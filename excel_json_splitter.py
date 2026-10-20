
from __future__ import annotations

import argparse
import asyncio
import base64
from collections import Counter, deque
import concurrent.futures
from contextlib import ExitStack, suppress
from datetime import datetime
import json
import os
from pathlib import Path
import re
import socket
import sys
import threading
import time
import tkinter as tk
from tkinter import ttk
from urllib.parse import urlsplit
from urllib.request import ProxyHandler, HTTPRedirectHandler, build_opener

from dotenv import dotenv_values
from playwright.sync_api import Error as PlaywrightErro, sync_playwright
from websockets.asyncio.client import connect

class ConfiguracaoErro(ValueError):
    pass


def configurar(env_path: Path) -> dict[str, str]:
    if not env_path.is_file():
        raise ConfiguracaoErro("Arquivo .env nao encontrado; informe --env com o caminho correto.")
    try:
        valores = dotenv_values(env_path, encoding="utf-8-sig", interpolate=False)
    except (OSError, UnicodeError):
        raise ConfiguracaoErro("Nao foi possivel ler o .env como UTF-8.") from None
    url = (valores.get("URL_SBK") or "").strip()
    identificador = (valores.get("ID_TESTE") or "").strip()
    try:
        partes = urlsplit(url)
        valido = (
            partes.scheme in {"http", "https"}
            and bool(partes.hostname)
            and partes.username is None
            and partes.password is None
            and not any(c.isspace() or ord(c) < 32 or ord(c) == 127 for c in url)
            and "\\" not in url
        )
        _ = partes.port
    except ValueError:
        valido = False
    if not valido:
        raise ConfiguracaoErro("URL_SBK ausente ou invalida: use endereco HTTP(S), sem credenciais embutidas.")
    if not identificador or len(identificador) > 256 or any(
        ord(c) < 32 or ord(c) == 127 for c in identificador
    ):
        raise ConfiguracaoErro("ID_TESTE ausente ou invalido: use de 1 a 256 caracteres, sem controles.")
    return {"URL_SBK": url, "ID_TESTE": identificador}


def numero_ou_none(value):
    value = str(value or "")
    return int(value) if re.fullmatch(r"[0-9]{1,18}", value) else None


"""Validação estrutural conservadora de um PDF já salvo em disco.

Não reescreve o documento, não renderiza e não chama get_data()/get_contents().
O pypdf pode ler bytes brutos de streams e decodificar estruturas internas
(por exemplo object streams) necessárias ao parser; conteúdo visual não é
interpretado. Streams comuns são descartados do cache após conferir seus
metadados; o pico ainda depende do maior stream e dos object streams/xref
internos, além dos metadados. Não há limite constante de RAM garantido.
Leituras integrais sem tamanho explícito são bloqueadas: o validador rejeita
documentos que levem o parser a esse caminho de reparo, mesmo se um visualizador
conseguir abri-los.
Uma estrutura válida não prova que o relatório contém todos os
registros. A contagem esperada, quando conhecida externamente, acrescenta uma
verificação de completude por número de páginas, sem validar seu conteúdo.
"""

import hashlib
import logging
import os
import warnings
from pathlib import Path

from pypdf import PdfReader
from pypdf.generic import ArrayObject, DictionaryObject, IndirectObject, StreamObject


class DocumentoInvalido(ValueError):
    """Falha de validação; as mensagens não incluem caminhos ou dados do PDF."""


class _ArquivoPdfLimitado:
    """Arquivo em disco com seek; bloqueia fallback de leitura integral.

    pypdf 6.10 pode usar read(-1) para procurar referências durante reparos,
    inclusive em strict=True. Leituras normais com tamanho positivo continuam
    disponíveis, inclusive streams individuais e estruturas internas grandes.
    """
    mode = "rb"

    def __init__(self, arquivo):
        self._arquivo = arquivo

    def read(self, tamanho=-1):
        if tamanho is None or tamanho < 0:
            raise DocumentoInvalido("PDF exige leitura integral ou reparo não permitido.")
        return self._arquivo.read(tamanho)

    def seek(self, deslocamento, origem=0):
        return self._arquivo.seek(deslocamento, origem)

    def tell(self):
        return self._arquivo.tell()


class _AvisosPdf(logging.Handler):
    def __init__(self):
        super().__init__(level=logging.WARNING)
        self.ocorreu = False

    def emit(self, record):
        self.ocorreu = True
        # Interrompe antes de propagar a mensagem original ao logger da aplicação.
        # O texto do parser pode incluir fragmentos do documento.
        raise DocumentoInvalido("PDF gerou avisos ou exigiu reparos de estrutura.")


def _objeto_pdf(objeto):
    return objeto.get_object() if isinstance(objeto, IndirectObject) else objeto


def _verificar_arvore_paginas(raiz_paginas):
    """Confere tipos, folhas únicas e /Count de cada nó da árvore."""
    pendentes = [(_objeto_pdf(raiz_paginas), False)]
    vistos = set()
    contagens = {}
    while pendentes:
        no, concluir = pendentes.pop()
        if not isinstance(no, DictionaryObject) or isinstance(no, StreamObject):
            raise DocumentoInvalido("Árvore de páginas inválida.")
        chave = id(no)
        tipo = no.get("/Type")
        if concluir:
            filhos = _objeto_pdf(no.get("/Kids"))
            total = sum(contagens[id(_objeto_pdf(filho))] for filho in filhos)
            declarado = _objeto_pdf(no.get("/Count"))
            if isinstance(declarado, bool) or not isinstance(declarado, int) or declarado != total:
                raise DocumentoInvalido("Contagem interna de páginas inconsistente.")
            contagens[chave] = total
            continue
        if chave in vistos:
            raise DocumentoInvalido("Árvore de páginas inválida.")
        vistos.add(chave)
        if tipo == "/Page":
            contagens[chave] = 1
        elif tipo == "/Pages":
            filhos = _objeto_pdf(no.get("/Kids"))
            if not isinstance(filhos, ArrayObject):
                raise DocumentoInvalido("Árvore de páginas inválida.")
            pendentes.append((no, True))
            pendentes.extend((_objeto_pdf(filho), False) for filho in reversed(filhos))
        else:
            raise DocumentoInvalido("Árvore de páginas inválida.")
    return contagens[id(_objeto_pdf(raiz_paginas))]


def _percorrer_estrutura_pdf(leitor):
    """Resolve referências alcançáveis sem decodificar streams de conteúdo.

    Inclui catálogo, metadados, páginas, recursos e anotações. Não percorre
    objetos órfãos da tabela xref nem interpreta operadores de desenho, fontes,
    imagens, assinaturas digitais ou o significado dos dados do relatório.
    Depois de enfileirar os metadados de cada stream comum, remove apenas esse
    stream do cache do leitor. Não altera bytes nem dicionários do documento.
    /ObjStm e /XRef permanecem sob controle do parser; podem reter bytes brutos
    e decodificados. Os dicionários/arrays de metadados permanecem retidos para
    evitar reuso de identidades durante a travessia e preservar referências.
    """
    pendentes = [leitor.trailer]
    referencias = set()
    objetos = {}
    while pendentes:
        objeto = pendentes.pop()
        referencia = None
        if isinstance(objeto, IndirectObject):
            chave = (objeto.idnum, objeto.generation)
            if chave in referencias:
                continue
            referencias.add(chave)
            referencia = objeto
            objeto = objeto.get_object()
        if isinstance(objeto, StreamObject):
            if referencia is None:
                # A especificação exige que streams sejam objetos indiretos.
                # Um stream direto ficaria retido no dicionário do pai.
                raise DocumentoInvalido("Stream PDF com referência inválida.")
            pendentes.extend(objeto.values())
            if objeto.get("/Type") not in ("/ObjStm", "/XRef"):
                chave_cache = (referencia.generation, referencia.idnum)
                if leitor.resolved_objects.get(chave_cache) is objeto:
                    del leitor.resolved_objects[chave_cache]
                # Libera antes de resolver o próximo stream, evitando sobrepor
                # dois conteúdos pela variável local da iteração anterior.
                objeto = None
            continue
        if isinstance(objeto, (DictionaryObject, ArrayObject)):
            chave = id(objeto)
            if chave in objetos:
                continue
            objetos[chave] = objeto
            if isinstance(objeto, DictionaryObject):
                # values() mantém referências indiretas; __getitem__ as resolveria.
                # StreamObject é um dicionário: seus bytes não são decodificados.
                pendentes.extend(objeto.values())
            else:
                pendentes.extend(objeto)


def validar_pdf(path: Path, paginas_esperadas: int | None = None) -> dict:
    """Retorna bytes, páginas e SHA-256 do arquivo original após validação.

    Rejeita criptografia, avisos/reparos do parser, referências alcançáveis
    inválidas, contagens incoerentes e ausência de assinatura/EOF. Sem uma
    contagem esperada obtida de fonte confiável, não confirma que todas as
    páginas pretendidas pelo sistema foram geradas ou transferidas.
    """
    if paginas_esperadas is not None and (
        isinstance(paginas_esperadas, bool)
        or not isinstance(paginas_esperadas, int)
        or paginas_esperadas <= 0
    ):
        raise DocumentoInvalido("Contagem esperada de páginas inválida.")
    avisos = _AvisosPdf()
    logger = logging.getLogger("pypdf")
    try:
        with Path(path).open("rb") as arquivo:
            estado_inicial = os.fstat(arquivo.fileno())
            tamanho = estado_inicial.st_size
            if arquivo.read(5) != b"%PDF-":
                raise DocumentoInvalido("Assinatura PDF ausente.")
            arquivo.seek(max(0, tamanho - 4096))
            cauda = arquivo.read(4096).rstrip(b" \t\r\n\f\x00")
            if not cauda.endswith(b"%%EOF"):
                raise DocumentoInvalido("Marcador final PDF ausente ou inválido.")
            arquivo.seek(0)
            logger.addHandler(avisos)
            try:
                with warnings.catch_warnings(record=True) as avisos_python:
                    warnings.simplefilter("always")
                    leitor = PdfReader(_ArquivoPdfLimitado(arquivo), strict=True)
                    if leitor.is_encrypted:
                        raise DocumentoInvalido("PDF criptografado não é aceito.")
                    raiz = _objeto_pdf(leitor.trailer.get("/Root"))
                    if not isinstance(raiz, DictionaryObject) or isinstance(raiz, StreamObject) or raiz.get("/Type") != "/Catalog":
                        raise DocumentoInvalido("Catálogo PDF inválido.")
                    raiz_paginas = _objeto_pdf(raiz.get("/Pages"))
                    if not isinstance(raiz_paginas, DictionaryObject) or isinstance(raiz_paginas, StreamObject) or raiz_paginas.get("/Type") != "/Pages":
                        raise DocumentoInvalido("Árvore de páginas inválida.")
                    paginas = _verificar_arvore_paginas(raiz_paginas)
                    if paginas <= 0 or len(leitor.pages) != paginas:
                        raise DocumentoInvalido("Contagem interna de páginas inconsistente.")
                    _percorrer_estrutura_pdf(leitor)
                    if avisos.ocorreu or avisos_python:
                        raise DocumentoInvalido("PDF gerou avisos ou exigiu reparos de estrutura.")
            finally:
                logger.removeHandler(avisos)
            if paginas_esperadas is not None and paginas != paginas_esperadas:
                raise DocumentoInvalido("PDF com quantidade de páginas diferente da esperada.")
            arquivo.seek(0)
            digest = hashlib.sha256()
            while bloco := arquivo.read(1024 * 1024):
                digest.update(bloco)
            estado_final = os.fstat(arquivo.fileno())
            if (estado_final.st_size, estado_final.st_mtime_ns) != (
                estado_inicial.st_size, estado_inicial.st_mtime_ns
            ):
                raise DocumentoInvalido("Arquivo alterado durante a validação.")
            return {"bytes": tamanho, "paginas": paginas, "sha256": digest.hexdigest()}
    except DocumentoInvalido:
        raise
    except Exception:
        raise DocumentoInvalido("PDF inválido ou estrutura inconsistente.") from None

def classificar_arquivo(path):
    tamanho = Path(path).stat().st_size
    with Path(path).open("rb") as handle:
        inicio = handle.read(1024)
    limpo = inicio.lstrip(b"\xef\xbb\xbf \t\r\n\x00")
    if not inicio:
        classe = "VAZIO"
    elif inicio.startswith(b"%PDF-"):
        classe = "PDF"
    elif b"%PDF-" in inicio:
        classe = "PDF_COM_PREFIXO"
    elif limpo.lower().startswith((b"<!doctype", b"<html", b"<head", b"<script", b"<?xml")):
        classe = "HTML_OU_XML"
    elif limpo.startswith((b"{", b"[")):
        classe = "JSON_POSSIVEL"
    elif limpo.startswith(b"JVBERi0"):
        classe = "BASE64_PDF_POSSIVEL"
    elif inicio.startswith(b"\x1f\x8b"):
        classe = "GZIP"
    elif inicio.startswith(b"PK\x03\x04"):
        classe = "ZIP"
    else:
        classe = "OUTRO"
    return {"bytes": tamanho, "classe_bytes": classe,
            "offset_assinatura": inicio.find(b"%PDF-")}


class ProtocoloErro(RuntimeError):
    pass


class CapturaOriginal:
    """Preserva corpo HTTP e converte apenas a apresentacao PDF em download.

    O Fetch pausa nos cabecalhos da resposta recebida; continueResponse troca
    somente Content-Disposition. Nao ha GET adicional, leitura do corpo pelo
    Python, impressao nem reconstrucao do PDF. A transferencia e nativa.
    """
    def __init__(self, monitor, modo='corpo', pasta=None, timeout_corpo=1200):
        self.monitor = monitor
        self.modo = modo                  # 'corpo' (padrao) ou 'download'
        self.pasta = Path(pasta) if pasta else None
        self.timeout_corpo = timeout_corpo
        self.corpos = deque()             # PDFs salvos pelo CDP (append/popleft sao atomicos)
        self.ws = None
        self.leitor = None
        self.sequencia = 0
        self.futuros = {}
        self.sessoes_futuras = {}
        self.sessoes = set()
        self.alvos = set()
        self.alvos_por_sessao = {}
        self.tarefas = set()
        self.ativo = False
        self.fechando = False
        self.ajustados = 0
        self.candidatos = 0

    def tarefa(self, coroutine):
        task = asyncio.create_task(coroutine)
        self.tarefas.add(task)
        def terminou(done):
            self.tarefas.discard(done)
            if not done.cancelled():
                erro = done.exception()
                if erro:
                    self.monitor.registrar('captura_observador_falhou', classe=type(erro).__name__)
        task.add_done_callback(terminou)
        return task

    async def comando(self, metodo, params=None, session=None, timeout=15):
        self.sequencia += 1
        identificador = self.sequencia
        future = asyncio.get_running_loop().create_future()
        self.futuros[identificador] = future
        self.sessoes_futuras[identificador] = session
        message = {'id': identificador, 'method': metodo, 'params': params or {}}
        if session:
            message['sessionId'] = session
        try:
            await self.ws.send(json.dumps(message))
            return await asyncio.wait_for(future, timeout)
        finally:
            self.futuros.pop(identificador, None)
            self.sessoes_futuras.pop(identificador, None)

    async def instalar(self, endpoint, contextos_esperados=None):
        # Endpoint criado exclusivamente pelo perfil temporario deste processo.
        # Conexao local sem proxy. O endpoint e os headers nunca sao registrados.
        self.ws = await connect(endpoint, proxy=None, compression=None,
            max_size=1024 * 1024 * 1024, max_queue=16, open_timeout=10, close_timeout=5)
        self.leitor = asyncio.create_task(self.receber())
        # Verificar identidade antes de observar alvos ou alterar respostas.
        if contextos_esperados is not None:
            encontrados = set((await self.comando('Target.getBrowserContexts')).get('browserContextIds', []))
            if not contextos_esperados or not set(contextos_esperados).issubset(encontrados):
                raise ProtocoloErro('NAVEGADOR_LOCAL_DIVERGENTE')
        await self.comando('Target.setAutoAttach', {'autoAttach': True,
            'waitForDebuggerOnStart': True, 'flatten': True,
            'filter': [{'type': 'page', 'exclude': False},
                       {'type': 'iframe', 'exclude': False}, {'exclude': True}]})
        for _ in range(100):
            if self.sessoes:
                break
            await asyncio.sleep(.02)
        if self.tarefas:
            await asyncio.gather(*list(self.tarefas), return_exceptions=True)
        if not self.sessoes:
            raise ProtocoloErro('CAPTURA_SEM_ALVO_PRONTO')
        self.monitor.registrar('captura_original_instalada', sessoes=len(self.sessoes))

    async def configurar_alvo(self, session, target):
        try:
            # Todas as respostas sao observadas, pois a classificacao pode ser
            # feita somente apos receber Content-Type. O corpo nunca e lido.
            await self.comando('Fetch.enable', {'patterns': [
                {'urlPattern': '*', 'requestStage': 'Response'}]}, session)
            await self.comando('Target.setAutoAttach', {'autoAttach': True,
                'waitForDebuggerOnStart': True, 'flatten': True,
                'filter': [{'type': 'iframe', 'exclude': False}, {'exclude': True}]}, session)
            self.sessoes.add(session)
            self.monitor.registrar('captura_alvo_pronta', numero=len(self.sessoes),
                tipo=target.get('type') if target.get('type') in {'page', 'iframe'} else 'outro')
        except Exception as erro:
            self.monitor.registrar('captura_alvo_indisponivel', classe=type(erro).__name__)
        finally:
            with suppress(Exception):
                await self.comando('Runtime.runIfWaitingForDebugger', session=session)

    async def receber(self):
        try:
            async for raw in self.ws:
                message = json.loads(raw)
                if 'id' in message:
                    future = self.futuros.get(message['id'])
                    if future is not None and not future.done():
                        if 'error' in message:
                            future.set_exception(ProtocoloErro('COMANDO_CDP_INDISPONIVEL'))
                        else:
                            future.set_result(message.get('result', {}))
                    continue
                method = message.get('method')
                params = message.get('params', {})
                if method == 'Target.attachedToTarget':
                    target = params.get('targetInfo', {})
                    session = params['sessionId']
                    if target.get('targetId') in self.alvos or self.fechando:
                        self.tarefa(self.comando('Runtime.runIfWaitingForDebugger', session=session))
                    else:
                        self.alvos.add(target.get('targetId'))
                        self.alvos_por_sessao[session] = target.get('targetId')
                        self.tarefa(self.configurar_alvo(session, target))
                elif method == 'Target.detachedFromTarget':
                    detached = params.get('sessionId')
                    self.sessoes.discard(detached)
                    alvo_removido = self.alvos_por_sessao.pop(detached, None)
                    if alvo_removido is not None:
                        self.alvos.discard(alvo_removido)
                    for identificador, sid in list(self.sessoes_futuras.items()):
                        future = self.futuros.get(identificador)
                        if sid == detached and future is not None and not future.done():
                            future.set_exception(ProtocoloErro('ALVO_CDP_FECHADO'))
                elif method == 'Fetch.requestPaused':
                    self.tarefa(self.resposta(message.get('sessionId'), params))
        except Exception as erro:
            if not self.fechando:
                self.monitor.registrar('canal_captura_falhou', classe=type(erro).__name__)
        finally:
            for future in list(self.futuros.values()):
                if not future.done():
                    future.set_exception(ProtocoloErro('CANAL_CDP_FECHADO'))

    async def salvar_corpo(self, session, request_id, status, h, numero):
        """Le o corpo da PROPRIA resposta pausada (sem 2o GET) e grava em disco."""
        destino = self.pasta / f'sbk_corpo_{numero:04d}.part'
        try:
            r = await self.comando('Fetch.getResponseBody', {'requestId': request_id},
                                   session, timeout=self.timeout_corpo)
            if not r.get('base64Encoded'):
                raise ProtocoloErro('CORPO_NAO_BINARIO')
            dados = base64.b64decode(r.get('body', ''))
            await asyncio.to_thread(destino.write_bytes, dados)
            self.corpos.append({'arquivo': str(destino), 'numero': numero, 'http': {
                'requisicao_id': f'C{numero:04d}', 'status': status, 'content_type': 'application/pdf',
                'content_length': numero_ou_none(h.get('content-length')),
                'content_encoding': h.get('content-encoding', '').strip().lower(),
                'tem_content_range': False}})
            self.monitor.registrar('corpo_pdf_salvo', numero=numero, bytes=len(dados))
        except Exception as erro:
            self.monitor.registrar('corpo_pdf_falhou', numero=numero, classe=type(erro).__name__)
        finally:
            # Sempre libera a resposta, inclusive em falha, para a pagina nao travar.
            with suppress(Exception):
                await self.comando('Fetch.continueRequest', {'requestId': request_id}, session)

    async def resposta(self, session, params):
        request_id = params['requestId']
        headers = params.get('responseHeaders') or []
        h = {str(i.get('name', '')).lower(): str(i.get('value', '')) for i in headers}
        tipo = h.get('content-type', '').split(';', 1)[0].strip().lower()
        status = params.get('responseStatusCode')
        url = str((params.get('request') or {}).get('url', '')).lower()
        servlet = 'showjasperreportpdfservlet' in url
        eh_pdf = tipo in {'application/pdf', 'application/x-pdf'} or (
            servlet and tipo in {'application/octet-stream', 'application/x-download',
                                 'binary/octet-stream'})
        if self.ativo and (servlet or eh_pdf):
            # Diagnostico sem URL: mostra o que o servidor realmente respondeu.
            disp = h.get('content-disposition', '').lower()
            self.monitor.registrar('resposta_relevante', servlet=servlet, status=status,
                content_type=tipo or 'ausente', tipo_recurso=params.get('resourceType'),
                disposition='attachment' if 'attachment' in disp else ('inline' if disp else 'ausente'),
                content_length=numero_ou_none(h.get('content-length')),
                tem_content_range='content-range' in h)
        alterar = (self.ativo and not self.fechando and status == 200 and eh_pdf
                   and 'content-range' not in h)
        if alterar:
            self.candidatos += 1
            if self.modo == 'corpo' and self.pasta is not None:
                await self.salvar_corpo(session, request_id, status, h, self.candidatos)
                return
            nome_local = f'sbk_original_{self.candidatos:04d}.pdf'
            associar = getattr(self.monitor, 'associar_http_download', None)
            if associar is not None:
                associar(nome_local, {'requisicao_id': f'C{self.candidatos:04d}',
                    'status': status, 'content_type': 'application/pdf',
                    'content_length': numero_ou_none(h.get('content-length')),
                    'content_encoding': h.get('content-encoding', '').strip().lower() if h.get('content-encoding', '').strip().lower() in {'', 'identity', 'gzip', 'br', 'deflate', 'zstd'} else 'outro',
                    'tem_content_range': False, 'disposition': 'attachment',
                    'origem_metadados': 'resposta_original_antes_visualizador'})
            novos_headers = [item for item in headers
                if str(item.get('name', '')).lower() != 'content-disposition']
            novos_headers.append({'name': 'Content-Disposition',
                                  'value': f'attachment; filename="{nome_local}"'})
            try:
                await self.comando('Fetch.continueResponse', {'requestId': request_id,
                    'responseCode': status, 'responseHeaders': novos_headers}, session)
                self.ajustados += 1
                self.monitor.registrar('cabecalho_download_ajustado', numero=self.ajustados,
                    status=status, content_type='application/pdf', corpo_alterado=False,
                    requisicao_repetida=False)
                return
            except Exception as erro:
                self.monitor.registrar('cabecalho_download_nao_ajustado', classe=type(erro).__name__)
        # Demais respostas (ADF/HTML, scripts, erros): segue sem alteracao.
        with suppress(Exception):
            await self.comando('Fetch.continueRequest', {'requestId': request_id}, session)

    async def fechar(self):
        self.fechando = True
        self.ativo = False
        if self.tarefas:
            await asyncio.gather(*list(self.tarefas), return_exceptions=True)
        if self.ws:
            for session in list(self.sessoes):
                with suppress(Exception):
                    await self.comando('Fetch.disable', session=session, timeout=5)
            with suppress(Exception):
                await self.comando('Target.setAutoAttach', {'autoAttach': False,
                    'waitForDebuggerOnStart': False, 'flatten': True}, timeout=5)
            await self.ws.close()
        if self.leitor:
            with suppress(Exception):
                await self.leitor
        if self.tarefas:
            await asyncio.gather(*list(self.tarefas), return_exceptions=True)

"""Controller SYNC para CapturaOriginal: Playwright fica na thread principal.

Montagem: este helper usa CapturaOriginal definido antes dele no mesmo modulo.
Imports necessarios: asyncio, concurrent.futures, json, re, threading, time,
Path, suppress e connect (websockets.asyncio.client).

Contrato de monitor: registrar(evento, **dados), opcionalmente
associar_http_download(nome, metadados). Estes metodos e seus consumidores na
thread principal devem usar o mesmo RLock monitor.trava_threads. O proxy abaixo
protege todas as chamadas feitas pela thread CDP. Nenhum objeto Playwright e
usado ou armazenado nessa thread.
"""


class CapturaInicializacaoErro(RuntimeError):
    pass


class _MonitorDaCaptura:
    def __init__(self, monitor, trava):
        self._monitor = monitor
        self._trava = trava

    def registrar(self, evento, **dados):
        with self._trava:
            self._monitor.registrar(evento, **dados)

    def associar_http_download(self, nome, metadados):
        with self._trava:
            associar = getattr(self._monitor, 'associar_http_download', None)
            if associar is not None:
                associar(nome, metadados)


def reservar_porta_local():
    # O socket e liberado antes do launch. A identidade CDP e conferida depois
    # para rejeitar outro processo que eventualmente ocupe esta porta.
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as servidor:
        servidor.bind(('127.0.0.1', 0))
        return servidor.getsockname()[1]


class _SemRedirecionamentoLocal(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def endpoint_na_porta_local(porta, timeout=6):
    if isinstance(porta, bool) or not isinstance(porta, int) or not 1 <= porta <= 65535:
        raise CapturaInicializacaoErro('CDP_PORTA_INVALIDA')
    # Ignorar proxy corporativo apenas nesta consulta a 127.0.0.1.
    # Nao alterar o proxy usado pelo Edge para acessar o SBK.
    cliente = build_opener(ProxyHandler({}), _SemRedirecionamentoLocal())
    prazo = time.monotonic() + timeout
    ultimo = 'SEM_RESPOSTA'
    while time.monotonic() < prazo:
        try:
            with cliente.open(f'http://127.0.0.1:{porta}/json/version',
                              timeout=max(.05, min(1, prazo - time.monotonic()))) as resposta:
                dados = resposta.read(65537)
            if len(dados) > 65536:
                raise ValueError('RESPOSTA_LOCAL_EXCESSIVA')
            endpoint = json.loads(dados)['webSocketDebuggerUrl']
            esperado = rf'ws://127\.0\.0\.1:{porta}/devtools/browser/[A-Za-z0-9-]+'
            if not isinstance(endpoint, str) or not re.fullmatch(esperado, endpoint):
                raise ValueError('ENDPOINT_LOCAL_INVALIDO')
            return endpoint
        except Exception as erro:
            # Somente classe; mensagens podem conter caminhos/dados do ambiente.
            ultimo = type(erro).__name__
            time.sleep(min(.1, max(0, prazo - time.monotonic())))
    raise CapturaInicializacaoErro(
        'CDP_LOCAL_SEM_RESPOSTA (' + ultimo + '). O Edge iniciou, mas a conexao '
        'local de captura nao ficou disponivel. Isso ainda nao confirma bloqueio '
        'corporativo; se persistir, envie somente este codigo de erro.'
    )


class CapturaEmSegundoPlano:
    """Loop CDP independente, inclusive durante Tk.mainloop e save_as SYNC."""
    def __init__(self, monitor, porta_cdp=None, modo='corpo', pasta=None, timeout_corpo=1200):
        self._modo = modo
        self._pasta = pasta
        self._timeout_corpo = timeout_corpo
        self._porta_cdp = porta_cdp
        self._contextos_esperados = None
        trava = getattr(monitor, 'trava_threads', None)
        if trava is None:
            trava = threading.RLock()
            monitor.trava_threads = trava
        self.monitor = _MonitorDaCaptura(monitor, trava)
        self.pronta = threading.Event()
        self._expirou = threading.Event()
        self._thread = None
        self._loop = None
        self._sair = None
        self._captura = None
        self._watchdog = None
        self._erro = None
        self._fechada = False

    @property
    def expirou(self):
        return self._expirou.is_set()

    @staticmethod
    def descobrir_endpoint(browser):
        # Metodo chamado somente pela thread principal. O perfil e o endpoint
        # pertencem ao Browser recebido; nao procura navegadores do usuario.
        sessao = None
        try:
            sessao = browser.new_browser_cdp_session()
            argumentos = sessao.send('Browser.getBrowserCommandLine')['arguments']
            perfis = []
            for indice, argumento in enumerate(argumentos):
                if argumento.startswith('--user-data-dir='):
                    perfis.append(argumento.split('=', 1)[1])
                elif argumento == '--user-data-dir' and indice + 1 < len(argumentos):
                    perfis.append(argumentos[indice + 1])
            if len(perfis) != 1:
                raise ValueError('PERFIL_NAO_IDENTIFICADO')
            linhas = (Path(perfis[0]) / 'DevToolsActivePort').read_text(encoding='utf-8').splitlines()
            if len(linhas) < 2:
                raise ValueError('ENDPOINT_INCOMPLETO')
            porta, caminho = linhas[:2]
            if not porta.isdecimal() or not 1 <= int(porta) <= 65535:
                raise ValueError('PORTA_INVALIDA')
            if not re.fullmatch(r'/devtools/browser/[A-Za-z0-9-]+', caminho):
                raise ValueError('CAMINHO_CDP_INVALIDO')
            return f'ws://127.0.0.1:{int(porta)}{caminho}'
        except Exception:
            raise CapturaInicializacaoErro(
                'Nao foi possivel preparar a captura local do navegador iniciado. '
                'Confira as duas flags remote-debugging e se o Edge permite depuracao local.'
            ) from None
        finally:
            if sessao is not None:
                with suppress(Exception):
                    sessao.detach()

    def iniciar(self, browser):
        # Chamar apos context.new_page(), antes de navegar ou exportar.
        if self._thread is not None:
            raise CapturaInicializacaoErro('A captura ja foi iniciada.')
        if self._porta_cdp is None:
            # Compatibilidade com chamadas antigas e fixtures locais.
            endpoint = self.descobrir_endpoint(browser)
        else:
            sessao = None
            try:
                sessao = browser.new_browser_cdp_session()
                self._contextos_esperados = set(sessao.send('Target.getBrowserContexts')['browserContextIds'])
                if not self._contextos_esperados:
                    raise ValueError('CONTEXTO_AUSENTE')
            except Exception as erro:
                raise CapturaInicializacaoErro(
                    'CDP_IDENTIDADE_INDISPONIVEL (' + type(erro).__name__ + ')'
                ) from None
            finally:
                if sessao is not None:
                    with suppress(Exception):
                        sessao.detach()
            endpoint = endpoint_na_porta_local(self._porta_cdp)
        self._thread = threading.Thread(target=self._rodar,
            args=(endpoint,), name='sbk-cdp-local', daemon=True)
        self._thread.start()
        if not self.pronta.wait(35):
            self.fechar()
            raise CapturaInicializacaoErro('A captura local nao ficou pronta no prazo de 35 segundos.')
        if self._erro is not None:
            self.fechar()
            raise CapturaInicializacaoErro(
                'CDP_CAPTURA_NAO_INSTALADA (' + self._erro + ').'
            ) from None

    def _rodar(self, endpoint):
        try:
            asyncio.run(self._executar(endpoint))
        except Exception as erro:
            self._erro = (str(erro) if isinstance(erro, ProtocoloErro) else type(erro).__name__)
            self.monitor.registrar('captura_thread_falhou', classe=self._erro)
        finally:
            self.pronta.set()

    async def _executar(self, endpoint):
        self._loop = asyncio.get_running_loop()
        self._sair = asyncio.Event()
        self._captura = CapturaOriginal(self.monitor, self._modo, self._pasta, self._timeout_corpo)
        try:
            await self._captura.instalar(endpoint, self._contextos_esperados)
            self.pronta.set()
            await self._sair.wait()
        finally:
            await self._cancelar_prazo_async()
            try:
                await asyncio.wait_for(self._captura.fechar(), 20)
            except Exception:
                if self._captura.ws is not None:
                    with suppress(Exception):
                        await self._captura.ws.close()

    def _chamar(self, coroutine, timeout=10):
        if self._loop is None or self._thread is None or not self._thread.is_alive() or self._fechada:
            coroutine.close()
            raise CapturaInicializacaoErro('A captura local nao esta disponivel.')
        futuro = asyncio.run_coroutine_threadsafe(coroutine, self._loop)
        try:
            return futuro.result(timeout)
        except concurrent.futures.TimeoutError:
            futuro.cancel()
            raise CapturaInicializacaoErro('A captura local nao confirmou a operacao no prazo.') from None

    async def _armar_async(self):
        self._captura.ativo = True
        self.monitor.registrar('captura_original_armada')

    def armar(self):
        self._chamar(self._armar_async())

    def proximo_corpo(self):
        try:
            return self._captura.corpos.popleft()
        except (IndexError, AttributeError):
            return None

    async def _cancelar_prazo_async(self):
        tarefa = self._watchdog
        self._watchdog = None
        if tarefa is not None and tarefa is not asyncio.current_task():
            tarefa.cancel()
            with suppress(asyncio.CancelledError):
                await tarefa

    async def _iniciar_prazo_async(self, prazo_final):
        await self._cancelar_prazo_async()
        self._expirou.clear()
        self._watchdog = asyncio.create_task(self._vigiar(prazo_final))

    def iniciar_prazo(self, segundos):
        if not isinstance(segundos, (int, float)) or segundos <= 0:
            raise ValueError('O prazo da transferencia deve ser positivo.')
        self._chamar(self._iniciar_prazo_async(time.monotonic() + segundos))

    async def _vigiar(self, prazo_final):
        await asyncio.sleep(max(0, prazo_final - time.monotonic()))
        self._expirou.set()
        self.monitor.registrar('prazo_download_excedido', acao='encerrar_navegador_da_automacao')
        # Somente o browser proprio do endpoint descoberto em iniciar().
        # Interrompe inclusive save_as bloqueante, sem chamar Playwright aqui.
        with suppress(Exception):
            await self._captura.comando('Browser.close', timeout=5)

    def cancelar_prazo(self):
        if self._thread is not None and self._thread.is_alive() and not self._fechada:
            with suppress(Exception):
                self._chamar(self._cancelar_prazo_async(), timeout=6)

    def fechar(self):
        if self._fechada:
            return
        self.cancelar_prazo()
        self._fechada = True
        if self._loop is not None and self._sair is not None:
            with suppress(RuntimeError):
                self._loop.call_soon_threadsafe(self._sair.set)
        if self._thread is not None and self._thread is not threading.current_thread():
            self._thread.join(timeout=30)
            if self._thread.is_alive():
                self.monitor.registrar('captura_thread_nao_encerrou_no_prazo')

class ErroDownload(RuntimeError):
    """Erro controlado, sem dados do documento ou credenciais."""


class RegistroExecucao:
    def __init__(self, pasta, paginas_esperadas=None):
        self.pasta = Path(pasta)
        self.pasta.mkdir(parents=True, exist_ok=True)
        self.arquivo = (self.pasta / "eventos.jsonl").open("x", encoding="utf-8", buffering=1)
        self.trava_threads = threading.RLock()
        self.trava = self.trava_threads
        self.http_por_nome = {}
        self.disparos_download = deque()
        self.resultado = {}
        self.paginas_esperadas = paginas_esperadas
        self.armado = False
        self.fechado = False
        self.inicio = time.monotonic()
        self.contagens = Counter()
        self.paginas = set()

    def registrar(self, evento, **dados):
        with self.trava_threads:
            if self.fechado:
                return
            self.contagens[evento] += 1
            self.arquivo.write(json.dumps({"segundos": round(time.monotonic() - self.inicio, 3),
                "evento": evento, **dados}, ensure_ascii=True) + "\n")

    def associar_http_download(self, nome, dados):
        with self.trava_threads:
            self.http_por_nome[nome] = dict(dados)

    def instalar(self, context):
        # Todas as chamadas Playwright, inclusive callbacks, ficam na thread
        # principal. A thread auxiliar usa apenas CDP e metadados protegidos.
        def nova_pagina(page):
            if page in self.paginas:
                return
            self.paginas.add(page)
            self.registrar("pagina_detectada", numero=len(self.paginas))

            def download_iniciado(download):
                with self.trava_threads:
                    if self.armado:
                        self.disparos_download.append(download)
                        self.registrar("download_iniciado")

            page.on("download", download_iniciado)

        context.on("page", nova_pagina)
        for page in context.pages:
            nova_pagina(page)

    def gravar_resumo(self):
        with self.trava_threads:
            r = self.resultado
            h = r.get("http") or {}
            linhas = ["SBK_APP2_CORRIGIDO",
                "BASE=APP2; CAPTURA=RESPOSTA_ORIGINAL; SEM_REQUISICAO_EXTRA",
                f"DOWNLOADS_INICIADOS={self.contagens['download_iniciado']}; CORPOS_SALVOS={self.contagens['corpo_pdf_salvo']}; RESPOSTAS_RELEVANTES={self.contagens['resposta_relevante']}",
                f"RESPOSTAS_AJUSTADAS={self.contagens['cabecalho_download_ajustado']}",
                f"RESULTADO={r.get('motivo', 'EXECUCAO_NAO_CONCLUIDA')}",
                f"HTTP={h.get('status', 'NAO_OBSERVADO')}; MIME={h.get('content_type', 'NAO_OBSERVADO')}",
                f"CLASSE_BYTES={r.get('classe_bytes', 'NAO_MEDIDA')}; OFFSET_PDF={r.get('offset_assinatura')}",
                f"PDF_VALIDADO_ESTRUTURA={'SIM' if r.get('ok') else 'NAO'}",
                f"BYTES={r.get('bytes')}; PAGINAS={r.get('paginas')}; ESPERADAS={self.paginas_esperadas}",
                f"SHA256={r.get('sha256')}",
                f"ARQUIVO={r.get('arquivo', 'NAO_SALVO')}",
                f"PARCIAIS_RESTANTES={len(list(self.pasta.glob('*.part')))}"]
            (self.pasta / "resumo.txt").write_text("\n".join(linhas) + "\n", encoding="utf-8")

    def fechar(self):
        with self.trava_threads:
            if not self.fechado:
                self.gravar_resumo()
                self.fechado = True
                self.arquivo.close()


def baixar_pdf_original(page, context, monitor, captura, botao, timeout=1200):
    """Um clique e um download nativo; nenhuma consulta adicional ao servlet."""
    if timeout <= 0:
        raise ValueError("Prazo de download deve ser positivo.")
    parte = monitor.pasta / "documento.part"
    destino = monitor.pasta / "documento.pdf"
    r = {"ok": False, "motivo": "NAO_CONCLUIDO", "bytes": None, "paginas": None,
         "sha256": None, "http": None, "classe_bytes": None, "offset_assinatura": None}
    try:
        if parte.exists() or destino.exists():
            raise ErroDownload("DESTINO_JA_EXISTE")
        monitor.armado = True
        captura.armar()
        botao.scroll_into_view_if_needed()
        captura.iniciar_prazo(timeout)
        prazo = time.monotonic() + timeout
        monitor.registrar("exportacao_automatica_disparada")
        # Nao aguardar navegacao aqui: a geracao e a transferencia possuem seu
        # proprio prazo, e o resultado pode ser download direto ou pop-up.
        botao.click(no_wait_after=True)
        download = None
        while time.monotonic() < prazo:
            if captura.expirou:
                raise ErroDownload("TIMEOUT_DOWNLOAD")
            with monitor.trava_threads:
                if monitor.disparos_download:
                    download = monitor.disparos_download.popleft()
                    break
            # Pump da API SYNC: time.sleep impediria receber os eventos.
            page.wait_for_timeout(200)
        if download is None:
            raise ErroDownload("TIMEOUT_AGUARDANDO_DOWNLOAD")
        with monitor.trava_threads:
            h = monitor.http_por_nome.get(download.suggested_filename)
            r["http"] = dict(h) if h else None
        print("Download original iniciado. Aguardando a transferencia terminar...")
        # O navegador transfere para disco. O watchdog CDP fecha somente este
        # Browser temporario se save_as ficar bloqueado alem do prazo.
        download.save_as(parte)
        if download.failure():
            raise ErroDownload("DOWNLOAD_NATIVO_FALHOU")
        captura.cancelar_prazo()
        r.update(classificar_arquivo(parte))
        if h:
            if h["status"] in {401, 403}:
                raise ErroDownload("HTTP_AUTENTICACAO_NEGADA")
            if h["status"] != 200 or h.get("tem_content_range"):
                raise ErroDownload("HTTP_NAO_INTEGRAL")
            if h["content_type"] in {"text/html", "application/json", "text/json"}:
                raise ErroDownload("HTTP_NAO_PDF")
            if h.get("content_length") is not None and h.get("content_encoding", "") in {"", "identity"}:
                if r["bytes"] != h["content_length"]:
                    raise ErroDownload("TAMANHO_HTTP_DIVERGENTE")
        with parte.open("r+b") as handle:
            handle.flush()
            os.fsync(handle.fileno())
        r.update(validar_pdf(parte, monitor.paginas_esperadas))
        os.replace(parte, destino)
        r.update(ok=True, motivo="PDF_ORIGINAL_VALIDADO", arquivo=destino.name)
        print(f"PDF original salvo e validado: {destino.name} | {r['paginas']} paginas | {r['bytes']} bytes")
        return destino
    except DocumentoInvalido as erro:
        r["motivo"] = str(erro)
        raise ErroDownload(r["motivo"]) from None
    except ErroDownload as erro:
        r["motivo"] = str(erro)
        raise
    except PlaywrightErro as erro:
        if captura.expirou:
            r["motivo"] = "TIMEOUT_DOWNLOAD"
        else:
            codigo = re.search(r"\bnet::ERR_[A-Z_0-9]+\b", str(erro))
            r["motivo"] = codigo.group(0) if codigo else "DOWNLOAD_NATIVO_FALHOU"
        raise ErroDownload(r["motivo"]) from None
    except OSError as erro:
        r["motivo"] = f"ERRO_DISCO_{erro.errno}"
        raise ErroDownload(r["motivo"]) from None
    except Exception as erro:
        r["motivo"] = "FALHA_DOWNLOAD_" + type(erro).__name__
        raise ErroDownload(r["motivo"]) from None
    finally:
        with suppress(Exception):
            captura.cancelar_prazo()
        if not r["ok"]:
            # save_as ja terminou/falhou; nenhum escritor Python permanece ativo.
            with suppress(OSError):
                parte.unlink(missing_ok=True)
        with monitor.trava_threads:
            monitor.resultado = r
        monitor.registrar("download_resultado", **r)
        monitor.gravar_resumo()

def baixar_pdf_corpo(page, monitor, captura, botao, timeout=1200):
    """Um clique; o PDF e gravado a partir da propria resposta (CDP), sem novo GET."""
    if timeout <= 0:
        raise ValueError("Prazo de download deve ser positivo.")
    destino = monitor.pasta / "documento.pdf"
    r = {"ok": False, "motivo": "NAO_CONCLUIDO", "bytes": None, "paginas": None,
         "sha256": None, "http": None, "classe_bytes": None, "offset_assinatura": None}
    try:
        if destino.exists():
            raise ErroDownload("DESTINO_JA_EXISTE")
        captura.armar()
        botao.scroll_into_view_if_needed()
        captura.iniciar_prazo(timeout)
        prazo = time.monotonic() + timeout
        monitor.registrar("exportacao_automatica_disparada")
        botao.click(no_wait_after=True)
        ultimo_erro, limite_extra = None, None
        while True:
            agora = time.monotonic()
            if captura.expirou or agora >= prazo:
                raise ErroDownload(ultimo_erro or "TIMEOUT_AGUARDANDO_PDF")
            if ultimo_erro and agora >= limite_extra:
                raise ErroDownload(ultimo_erro)
            cand = captura.proximo_corpo()
            if cand is None:
                page.wait_for_timeout(200)   # mantem o Playwright processando eventos
                continue
            parte = Path(cand["arquivo"])
            h = cand["http"]
            try:
                r["http"] = dict(h)
                r.update(classificar_arquivo(parte))
                if h.get("content_length") is not None and h.get("content_encoding", "") in {"", "identity"}:
                    if r["bytes"] != h["content_length"]:
                        raise ErroDownload("TAMANHO_HTTP_DIVERGENTE")
                r.update(validar_pdf(parte, monitor.paginas_esperadas))
                os.replace(parte, destino)
                r.update(ok=True, motivo="PDF_ORIGINAL_VALIDADO", arquivo=destino.name)
                print(f"PDF original salvo e validado: {destino.name} | {r['paginas']} paginas | {r['bytes']} bytes")
                return destino
            except (DocumentoInvalido, ErroDownload) as erro:
                ultimo_erro = str(erro)
                limite_extra = time.monotonic() + 30   # espera outro candidato
                monitor.registrar("candidato_pdf_rejeitado", motivo=ultimo_erro)
    except ErroDownload as erro:
        r["motivo"] = str(erro)
        raise
    except PlaywrightErro as erro:
        r["motivo"] = "TIMEOUT_DOWNLOAD" if captura.expirou else "FALHA_PLAYWRIGHT"
        raise ErroDownload(r["motivo"]) from None
    except OSError as erro:
        r["motivo"] = f"ERRO_DISCO_{erro.errno}"
        raise ErroDownload(r["motivo"]) from None
    except Exception as erro:
        r["motivo"] = "FALHA_DOWNLOAD_" + type(erro).__name__
        raise ErroDownload(r["motivo"]) from None
    finally:
        with suppress(Exception):
            captura.cancelar_prazo()
        # Candidatos nao escolhidos ficam como .extra (nao contam como parciais).
        for sobra in monitor.pasta.glob("sbk_corpo_*.part"):
            with suppress(OSError):
                sobra.rename(sobra.with_suffix(".extra"))
        with monitor.trava_threads:
            monitor.resultado = r
        monitor.registrar("download_resultado", **{k: v for k, v in r.items() if k != "http"})
        monitor.gravar_resumo()


def esperar_rede(alvo, timeout=15000):
    """networkidle e opcional: no ADF pode nunca ficar ocioso; nao derruba o fluxo."""
    try:
        alvo.wait_for_load_state("networkidle", timeout=timeout)
    except PlaywrightErro:
        pass


def solicitar_token():
  token = {"valor": ""}

  def confirmar():
    token["valor"] = entrada.get().strip()
    janela.destroy()

  janela = tk.Tk()
  janela.title("SBK - Dupla Autenticação")
  janela.geometry("500x220")
  janela.resizable(False, False)

  titulo = tk.Label(
      janela, text="Dupla Autenticação", font=("Segoe UI", 12, "bold")
  )
  titulo.pack(pady=(20, 10))

  texto = tk.Label(
      janela,
      text="Digite o token recebido por e-mail para continuar.",
      wraplength=450,
  )
  texto.pack()

  entrada = ttk.Entry(janela, width=35, justify="center")
  entrada.pack(pady=15)
  entrada.focus()

  ttk.Button(janela, text="Confirmar", command=confirmar).pack()
  janela.bind("<Return>", lambda e: confirmar())
  janela.mainloop()

  return token["valor"]


def fechar_browser_seguro(browser):
  with suppress(Exception):
    if browser.is_connected():
      browser.close()


def executar_automacao(config=None, timeout_download=1200, paginas_esperadas=None, modo="corpo"):
  if config is None:
    config = configurar(Path(__file__).with_name(".env"))
  URL_SBK = config["URL_SBK"]
  ID_TESTE = config["ID_TESTE"]
  pasta = Path(__file__).with_name(datetime.now().strftime("execucao_app2_%Y%m%d_%H%M%S_%f"))
  with sync_playwright() as p, ExitStack() as recursos:
    porta_cdp = reservar_porta_local()
    # Lançamento do navegador Chromium (Edge) com desativação de bloqueios de pop-ups
    browser = p.chromium.launch(
        channel="msedge",
        headless=False,
        args=[
            "--disable-popup-blocking",
            "--allow-popups-during-page-unload",
            f"--remote-debugging-port={porta_cdp}",
            "--remote-debugging-address=127.0.0.1",
        ],
    )

    recursos.callback(fechar_browser_seguro, browser)

    # Configuração do contexto ideal para navegação legítima de frames no ADF
    context = browser.new_context(
        accept_downloads=True,
        ignore_https_errors=False,
    )

    monitor = RegistroExecucao(pasta, paginas_esperadas)
    recursos.callback(monitor.fechar)
    monitor.instalar(context)
    captura = CapturaEmSegundoPlano(monitor, porta_cdp=porta_cdp, modo=modo,
        pasta=pasta, timeout_corpo=timeout_download)
    recursos.callback(captura.fechar)

    page = context.new_page()
    print("Captura local: revisao 2026-10-20 (conexao direta).")
    captura.iniciar(browser)

    print("Abrindo SBK...")
    page.goto(URL_SBK)

    print("Realize o login normalmente.")
    print("Aguardando tela de token...")
    page.wait_for_selector("#duplaAutenticacao\\:\\:\\:content", timeout=120000)

    print("Campo de token localizado.")
    token = solicitar_token()
    if not token:
      raise ConfiguracaoErro("Token nao informado; autenticacao cancelada.")

    page.fill("#duplaAutenticacao\\:\\:\\:content", token)
    print("Token preenchido.")

    try:
      page.locator("#b4 a").click()
    except:
      page.get_by_text("Autenticar").click()

    print("Botão autenticar acionado.")
    esperar_rede(page, 30000)
    print("Autenticação concluída.")

    # ==========================================
    # CONSULTA IMAGEM
    # ==========================================
    print("Abrindo Consulta Imagem...")
    page.click("#pt1\\:pt_1ConsultaDeImagem\\:\\:text")
    page.wait_for_timeout(5000)

    page.wait_for_timeout(5000)

    dialog_frame = None
    for frame in page.frames:
      if "adf.dialog-request" in frame.url:
        dialog_frame = frame
        break

    if dialog_frame is None:
      raise Exception(
          "Não foi possível localizar o frame da Consulta Imagem."
      )

    print("Frame localizado com sucesso.")

    # ==========================================
    # TIPO DOCUMENTO
    # ==========================================
    print("Selecionando CONTABIL BRADESCO-189...")
    dialog_frame.select_option(
        "#pt1\\:socTipoDocumento\\:\\:\\:content",
        label="CONTABIL BRADESCO-189",
    )
    dialog_frame.wait_for_timeout(2000)

    # ==========================================
    # CLIENTE
    # ==========================================
    print("Selecionando Cliente...")
    dialog_frame.click("#pt1\\:\\:sorTipoPesquisa\\:\\:_1")
    dialog_frame.wait_for_timeout(1000)

    # ==========================================
    # ID
    # ==========================================
    print("Preenchendo o ID configurado no .env...")
    dialog_frame.fill("#pt1\\:\\:itTipoPesquisaItem\\:\\:\\:content", ID_TESTE)
    dialog_frame.wait_for_timeout(1000)

    # ==========================================
    # PESQUISAR
    # ==========================================
    print("Clicando em Pesquisar Documento...")
    dialog_frame.click("#pt1\\:\\:btPesquisarDocumento")
    dialog_frame.wait_for_timeout(5000)
    print("Pesquisa enviada.")

    # ==========================================
    # SELEÇÃO DOS FILTROS E CHECKBOXES (Continuação)
    # ==========================================

    # 1. Marcar o checkbox SelectAllDoc
    print("Marcando a primeira checkbox (Selecionar Todos)...")
    seletor_chk1 = "#pt1\\:\\:pc1\\:\\:t1\\:\\:sbcSelectAllDoc\\:\\:\\:content"
    dialog_frame.wait_for_selector(seletor_chk1, timeout=15000)
    dialog_frame.wait_for_timeout(2000)
    dialog_frame.locator(seletor_chk1).set_checked(True)

    # 2. Clique em Confirmar Filtro
    print("Clicando em Confirmar Filtro...")
    dialog_frame.wait_for_timeout(2000)
    seletor_btn1 = "#pt1\\:\\:pc1\\:\\:btConfirmarFiltro > a"
    dialog_frame.wait_for_selector(seletor_btn1, timeout=15000)
    dialog_frame.click(seletor_btn1)

    esperar_rede(dialog_frame)

    # 3. Marcar a outra checkbox SelectAllDocDet
    print("Marcando a segunda checkbox (Selecionar Detalhes)...")
    seletor_chk2 = (
        "#pt1\\:\\:pcIPD\\:\\:t3\\:\\:sbcSelectAllDocDet\\:\\:\\:content"
    )
    dialog_frame.wait_for_selector(seletor_chk2, timeout=15000)
    dialog_frame.wait_for_timeout(2000)
    dialog_frame.locator(seletor_chk2).set_checked(True)

    print("Aguardando o sistema processar a seleção das imagens...")
    esperar_rede(dialog_frame)
    dialog_frame.wait_for_timeout(3000)

    # ==========================================
    # 4. DOWNLOAD ORIGINAL: apresentar como attachment antes do visualizador
    # ==========================================
    print("Aguardando botão Exportar Imagens estar totalmente pronto...")
    seletor_btn2 = "#pt1\\:\\:pcIPD\\:\\:btDownloadImgSelect > a"
    dialog_frame.wait_for_selector(seletor_btn2, timeout=15000)
    dialog_frame.wait_for_timeout(3000)

    nome_arquivo = monitor.pasta / "documento.pdf"
    erro_download = None
    try:
      if modo == "corpo":
        baixar_pdf_corpo(page, monitor, captura, dialog_frame.locator(seletor_btn2),
                         timeout=timeout_download)
      else:
        monitor.armado = True
        baixar_pdf_original(
            page, context, monitor, captura, dialog_frame.locator(seletor_btn2),
            timeout=timeout_download,
        )
      print(f"Arquivo validado: {nome_arquivo.name}")
    except ErroDownload as erro:
      erro_download = erro
      print(f"Download nao concluido: {erro}")
    finally:
      captura.fechar()
      monitor.gravar_resumo()

    print(f"Resumo e resultado locais na pasta: {monitor.pasta.name}")
    try:
      input("\nPressione ENTER aqui para encerrar o Edge de testes...")
    except EOFError:
      pass
    fechar_browser_seguro(browser)
    if erro_download is not None:
      raise erro_download


def main():
  parser = argparse.ArgumentParser(description="App2 original com .env e download nativo validado.")
  parser.add_argument("--env", type=Path, default=Path(__file__).with_name(".env"))
  parser.add_argument("--timeout-download", type=int, default=1200)
  parser.add_argument("--paginas-esperadas", type=int)
  parser.add_argument("--modo", choices=["corpo", "download"], default="corpo",
                      help="corpo: grava a resposta PDF via CDP (padrao). download: forca attachment.")
  args = parser.parse_args()
  if not 10 <= args.timeout_download <= 7200:
    parser.error("--timeout-download deve estar entre 10 e 7200 segundos.")
  if args.paginas_esperadas is not None and args.paginas_esperadas <= 0:
    parser.error("--paginas-esperadas deve ser positivo.")
  try:
    config = configurar(args.env)
    executar_automacao(config, args.timeout_download, args.paginas_esperadas, args.modo)
    return 0
  except ConfiguracaoErro as erro:
    print(f"Configuracao: {erro}", file=sys.stderr)
    return 2
  except ErroDownload as erro:
    print(f"Falha: {erro}", file=sys.stderr)
    return 1
  except CapturaInicializacaoErro as erro:
    print(f"Captura: {erro}", file=sys.stderr)
    return 1
  except KeyboardInterrupt:
    print("Execucao interrompida pelo usuario.", file=sys.stderr)
    return 1
  except Exception as erro:
    # Erros Playwright podem incluir URL, tokens ou valores preenchidos.
    print(f"A automacao parou ({type(erro).__name__}). Confira a ultima etapa exibida e o resumo local.", file=sys.stderr)
    return 1


if __name__ == "__main__":
  raise SystemExit(main())
