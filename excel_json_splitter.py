"""SBK: automacao completa com Tkinter e download nativo do PDF original.

Configuracao local obrigatoria: URL_SBK e ID_TESTE no .env.
Login manual no Edge; token na janela Tkinter; navegacao/exportacao automaticas.
Instale: python -m pip install playwright python-dotenv "pypdf==6.10.0" "websockets==16.1.1"
Execute: python app_corrigido.py
Nenhum endereco real ou credencial foi incorporado neste arquivo.
"""
from __future__ import annotations

import argparse
import asyncio
from collections import Counter
from contextlib import suppress
from datetime import datetime
from importlib.metadata import version
import json
import os
from pathlib import Path
import re
import sys
import time
from urllib.parse import urljoin, urlsplit

from dotenv import dotenv_values
from playwright.async_api import Error as PlaywrightErro, async_playwright

import base64
import tempfile
import threading
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


class Sanitizador:
    """Permite apenas termos estaticos conhecidos; todo o resto recebe alias."""

    CAMINHOS = {"jdoc", "faces", "showjasperreportpdfservlet", "adf", "login"}
    PARAMETROS = {"_rtrId", "_afrPage", "_afrLoop", "_afrWindowId", "_afrWindowMode"}

    def __init__(self):
        self.origens = {}
        self.recursos = {}

    def url(self, value: str | None) -> dict:
        value = value or ""
        recurso = self.recursos.setdefault(value, f"R{len(self.recursos) + 1:04d}")
        try:
            partes = urlsplit(value)
            esquema = partes.scheme.lower()
            if esquema not in {"http", "https", "blob", "data", "about", "chrome-extension", "edge"}:
                esquema = "outro"
            origem = None
            caminho = "[oculto]"
            parametros = []
            if esquema in {"http", "https"}:
                chave = (partes.scheme.lower(), partes.hostname, partes.port)
                origem = self.origens.setdefault(chave, f"O{len(self.origens) + 1:03d}")
                segmentos = [s.lower() if s.lower() in self.CAMINHOS else "*"
                             for s in partes.path.split("/") if s]
                caminho = "/" + "/".join(segmentos[:12])
                if len(segmentos) > 12:
                    caminho += "/..."
                parametros = sorted({p.split("=", 1)[0] for p in partes.query.split("&")}
                                    & self.PARAMETROS)
            endereco = f"{esquema}://{origem or '[oculto]'}{caminho}"
            return {"url": endereco, "esquema": esquema, "origem_id": origem,
                    "recurso_id": recurso, "parametros_adf": parametros,
                    "tem_query": bool(partes.query), "tem_fragmento": bool(partes.fragment)}
        except (ValueError, TypeError):
            return {"url": "[url_oculta]", "esquema": "outro", "origem_id": None,
                    "recurso_id": recurso, "parametros_adf": [],
                    "tem_query": False, "tem_fragmento": False}


def numero(value):
    value = str(value or "")
    return int(value) if re.fullmatch(r"[0-9]{1,18}", value) else None


def intervalo(value):
    value = str(value or "").strip().lower()
    return value if re.fullmatch(r"bytes(?:=\d*-\d*(?:,\s*\d*-\d*)*| (?:\d+-\d+|\*)/(?:\d+|\*))", value) else None


def mime(value):
    value = str(value or "").split(";", 1)[0].strip().lower()
    permitidos = {"application/pdf", "application/octet-stream", "text/html",
                  "application/json", "text/json", "text/plain", "application/xml",
                  "text/xml", "text/javascript", "application/javascript"}
    return value if value in permitidos else ("outro" if value else "ausente")



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

class Monitor:
    """Observacao manual; downloads nativos sao preservados antes de fechar."""

    def __init__(self, pasta, timeout_download=1200, paginas_esperadas=None):
        self.pasta = Path(pasta)
        self.pasta.mkdir(parents=True, exist_ok=True)
        self.log = (self.pasta / "eventos.jsonl").open("x", encoding="utf-8", buffering=1)
        self.sanitizador = Sanitizador()
        self.inicio = time.monotonic()
        self.timeout_download = timeout_download
        self.paginas_esperadas = paginas_esperadas
        self.paginas = {}
        self.requisicoes = {}
        self.respostas = {}
        self.respostas_por_id = {}
        self.ultimas_requisicoes = {}
        self.tarefas = set()
        self.copias = set()
        self.transferencias = set()
        self.validacoes = set()
        self.trava_validacao = asyncio.Lock()
        self.partes = set()
        self.resultados = []
        self.contagens = Counter()
        self.aceitar_downloads = True
        self.rede_ativa = True
        self.fechado = False
        self.linhas = 0
        self.ultimo_download = None
        self.motivo = "em_execucao"

    def registrar(self, evento, **dados):
        if self.fechado:
            return
        self.contagens[evento] += 1
        if self.linhas >= 30000 and evento not in {"fim", "falha", "download_resultado"}:
            if self.linhas == 30000:
                self.log.write('{"evento":"limite_eventos","limite":30000}\n')
                self.linhas += 1
            return
        self.log.write(json.dumps({"segundos": round(time.monotonic() - self.inicio, 3),
                                   "evento": evento, **dados}, ensure_ascii=True) + "\n")
        self.linhas += 1

    def tarefa(self, coroutine, grupo=None):
        task = asyncio.create_task(coroutine)
        self.tarefas.add(task)
        if grupo is not None:
            grupo.add(task)

        def terminou(completed):
            self.tarefas.discard(completed)
            if grupo is not None:
                grupo.discard(completed)
            if not completed.cancelled():
                erro = completed.exception()
                if erro:
                    self.registrar("observador_falhou", classe=type(erro).__name__)

        task.add_done_callback(terminou)
        return task

    def pagina_id(self, page):
        return self.paginas.setdefault(page, f"P{len(self.paginas) + 1:03d}")

    def observar_pagina(self, page):
        if page in self.paginas:
            return
        pid = self.pagina_id(page)
        # Instalar listener antes de qualquer await, inclusive em pop-ups.
        page.on("download", self.receber_download)
        page.on("framenavigated", lambda frame: self.registrar(
            "frame_navegou", pagina_id=pid, principal=frame == page.main_frame,
            endereco=self.sanitizador.url(frame.url)))
        page.on("crash", lambda: self.registrar("pagina_crash", pagina_id=pid))
        page.on("close", lambda: self.registrar("pagina_fechada", pagina_id=pid))
        self.registrar("pagina", pagina_id=pid, endereco=self.sanitizador.url(page.url))

    def instalar(self, context):
        self.context = context
        context.on("page", self.observar_pagina)
        for page in context.pages:
            self.observar_pagina(page)
        context.on("request", self.requisicao)
        context.on("response", self.resposta)
        context.on("requestfinished", lambda request: self.tarefa(self.concluida(request)) if self.rede_ativa else None)
        context.on("requestfailed", self.falhou)
        self.registrar("captura_iniciada", modo="automatico", antes_de_abrir_site=True)

    def requisicao(self, request):
        if not self.rede_ativa or request in self.requisicoes:
            return
        if len(self.requisicoes) >= 10000:
            if not self.contagens["limite_requisicoes"]:
                self.registrar("limite_requisicoes", limite=10000)
            return
        rid = f"Q{len(self.requisicoes) + 1:05d}"
        self.requisicoes[request] = rid
        self.ultimas_requisicoes[request.url] = rid
        # Registrar antes do await de headers para manter a correlacao cronologica.
        self.registrar("requisicao", requisicao_id=rid, metodo=request.method,
                       tipo=request.resource_type, endereco=self.sanitizador.url(request.url),
                       redirecionada_de=self.requisicoes.get(request.redirected_from))
        self.tarefa(self.cabecalhos(request, rid))

    async def cabecalhos(self, request, rid):
        try:
            h = await request.all_headers()
            self.registrar("cabecalhos_requisicao", requisicao_id=rid,
                cookie_presente=bool(h.get("cookie")),
                authorization_presente=bool(h.get("authorization")),
                csrf_presente=any(k in h for k in ("x-csrf-token", "x-xsrf-token", "csrf-token")),
                referer=self.sanitizador.url(h["referer"]) if h.get("referer") else None,
                range=intervalo(h.get("range")))
        except PlaywrightErro:
            self.registrar("cabecalhos_indisponiveis", requisicao_id=rid)

    def resposta(self, response):
        if not self.rede_ativa:
            return
        request = response.request
        if request not in self.requisicoes:
            self.requisicao(request)
        h = response.headers
        encoding = h.get("content-encoding", "").strip().lower()
        disposition = h.get("content-disposition", "").split(";", 1)[0].strip().lower()
        dados = {"requisicao_id": self.requisicoes.get(request),
                 "status": response.status, "content_type": mime(h.get("content-type")),
                 "content_length": numero(h.get("content-length")),
                 "content_range": intervalo(h.get("content-range")),
                 "tem_content_range": bool(h.get("content-range")),
                 "content_encoding": encoding if encoding in {"", "identity", "gzip", "br", "deflate", "zstd"} else "outro",
                 "disposition": disposition if disposition in {"inline", "attachment"} else "ausente_ou_outro",
                 "via_service_worker": bool(response.from_service_worker)}
        if len(self.respostas) < 10000 or response.url in self.respostas:
            self.respostas[response.url] = dados
        if dados["requisicao_id"]:
            self.respostas_por_id[dados["requisicao_id"]] = dados
        self.registrar("resposta",
                       endereco=self.sanitizador.url(response.url),
                       location=self.sanitizador.url(urljoin(response.url, h["location"])) if h.get("location") else None,
                       **dados)

    async def concluida(self, request):
        rid = self.requisicoes.get(request)
        if not rid:
            return
        try:
            tamanho = (await request.sizes()).get("responseBodySize")
        except PlaywrightErro:
            tamanho = None
        self.registrar("requisicao_concluida", requisicao_id=rid, bytes_codificados=tamanho)

    def falhou(self, request):
        if not self.rede_ativa:
            return
        failure = request.failure or ""
        codigo = failure if re.fullmatch(r"net::ERR_[A-Z_0-9]+", failure) else "omitido"
        self.registrar("requisicao_falhou", requisicao_id=self.requisicoes.get(request), codigo=codigo)

    def receber_download(self, download):
        self.contagens["downloads_recebidos"] += 1
        did = self.contagens["downloads_recebidos"]
        self.registrar("download_iniciado", download_id=did, pagina_id=self.pagina_id(download.page),
                       endereco=self.sanitizador.url(download.url))
        self.ultimo_download = time.monotonic()
        if not self.aceitar_downloads or did > 5:
            self.registrar("download_recusado", download_id=did, motivo="limite_ou_encerramento")
            self.tarefa(download.cancel())
            return
        # Fixar o request no instante do evento. Uma nova consulta ADF ao mesmo
        # URL nao pode substituir os cabecalhos deste download enquanto ele baixa.
        requisicao_id = self.ultimas_requisicoes.get(download.url)
        self.tarefa(self.preservar(download, did, requisicao_id), self.transferencias)

    async def preservar(self, download, did, requisicao_id=None):
        parte = self.pasta / f"documento_{did:03d}.part"
        final = self.pasta / f"documento_{did:03d}.pdf"
        self.partes.add(parte)
        resultado = {"download_id": did, "ok": False, "motivo": "nao_concluido",
                     "http": None, "bytes": None, "paginas": None, "sha256": None}
        copia = asyncio.create_task(download.save_as(parte))
        self.copias.add(copia)
        copia.add_done_callback(lambda task: task.exception() if not task.cancelled() else None)
        tarefa_validacao = None
        try:
            # wait nao cancela a chamada Playwright em andamento por timeout e
            # nao deixa futures intermediarios de shield imprimirem erros brutos.
            concluidas, _ = await asyncio.wait({copia}, timeout=self.timeout_download)
            if not concluidas:
                raise asyncio.TimeoutError
            copia.result()
            resultado.update(classificar_arquivo(parte))
            falha = await asyncio.wait_for(download.failure(), 15)
            if falha:
                raise DocumentoInvalido("DOWNLOAD_NATIVO_FALHOU")
            # Dar uma volta ao dispatcher para receber cabecalhos ja emitidos.
            await asyncio.sleep(0)
            http = self.respostas_por_id.get(requisicao_id)
            resultado["http"] = http
            if http:
                if http["status"] in {401, 403}:
                    raise DocumentoInvalido("HTTP_AUTENTICACAO_NEGADA")
                if http["status"] >= 400:
                    raise DocumentoInvalido("HTTP_ERRO")
                if http["status"] == 206 or http["tem_content_range"]:
                    raise DocumentoInvalido("HTTP_PARCIAL_REQUER_INVESTIGACAO")
                if http["content_type"] in {"text/html", "application/json", "text/json", "application/xml", "text/xml"}:
                    raise DocumentoInvalido("HTTP_NAO_PDF")
                if http["content_length"] is not None and http["content_encoding"] in {"", "identity"}:
                    if parte.stat().st_size != http["content_length"]:
                        raise DocumentoInvalido("TAMANHO_HTTP_DIVERGENTE")
            if final.exists():
                raise DocumentoInvalido("DESTINO_JA_EXISTE")
            with parte.open("r+b") as handle:
                handle.flush()
                os.fsync(handle.fileno())
            async def validar_em_fila():
                # O logger pypdf e global; serializar validacoes evita misturar
                # avisos de dois documentos, mantendo a tarefa viva no cleanup.
                async with self.trava_validacao:
                    return await asyncio.to_thread(validar_pdf, parte, self.paginas_esperadas)

            tarefa_validacao = asyncio.create_task(validar_em_fila())
            self.validacoes.add(tarefa_validacao)
            await asyncio.wait({tarefa_validacao})
            validacao = tarefa_validacao.result()
            self.validacoes.discard(tarefa_validacao)
            # Mesmo diretorio/volume: promover somente depois de concluir e validar.
            os.replace(parte, final)
            self.partes.discard(parte)
            resultado.update(validacao, ok=True, motivo="PDF_ESTRUTURA_VALIDADA", arquivo=final.name)
            print(f"PDF salvo e validado: {final.name}; paginas={validacao['paginas']}; bytes={validacao['bytes']}", flush=True)
        except asyncio.TimeoutError:
            resultado["motivo"] = "TIMEOUT_DOWNLOAD"
            with suppress(PlaywrightErro, asyncio.TimeoutError):
                await asyncio.wait_for(download.cancel(), 10)
            with suppress(Exception):
                concluidas, _ = await asyncio.wait({copia}, timeout=10)
                if concluidas:
                    copia.result()
        except DocumentoInvalido as erro:
            # As mensagens desta classe sao codigos fixos, nunca valores do PDF.
            resultado["motivo"] = str(erro)
        except PlaywrightErro as erro:
            texto = str(erro)
            codigo = re.search(r"\bnet::ERR_[A-Z_0-9]+\b", texto)
            resultado["motivo"] = (codigo.group(0) if codigo else
                "DOWNLOAD_CANCELADO" if "canceled" in texto.lower() or "cancelled" in texto.lower()
                else "DOWNLOAD_NATIVO_FALHOU")
        except OSError as erro:
            resultado["motivo"] = f"FALHA_DISCO_ERRNO_{erro.errno}"
        except asyncio.CancelledError:
            resultado["motivo"] = "INTERROMPIDO"
            with suppress(PlaywrightErro, asyncio.TimeoutError):
                await asyncio.wait_for(download.cancel(), 5)
            raise
        except Exception as erro:
            resultado["motivo"] = "FALHA_LOCAL_" + type(erro).__name__
        finally:
            if copia.done():
                self.copias.discard(copia)
                if not copia.cancelled():
                    # Recuperar a excecao sem imprimir texto ou traceback.
                    copia.exception()
                if not resultado["ok"] and (tarefa_validacao is None or tarefa_validacao.done()):
                    with suppress(OSError):
                        parte.unlink(missing_ok=True)
                    if not parte.exists():
                        self.partes.discard(parte)
            self.resultados.append(resultado)
            self.registrar("download_resultado", **resultado)

    async def aguardar(self, browser, espera):
        limite = time.monotonic() + espera
        proximo_aviso = 0
        while browser.is_connected() and self.context.pages:
            agora = time.monotonic()
            # Um download iniciado dentro do prazo pode terminar depois dele.
            if agora >= limite and not self.transferencias:
                return "PRAZO_OBSERVACAO"
            if self.resultados and not self.transferencias and agora - self.ultimo_download >= 2:
                return "DOWNLOAD_PROCESSADO"
            if agora >= proximo_aviso:
                print(f"Observando: respostas={self.contagens['resposta']}; downloads={self.contagens['downloads_recebidos']}. "
                      "Login, token e navegacao sao manuais neste diagnostico.", flush=True)
                proximo_aviso = agora + 30
            await asyncio.sleep(0.2)
        # O usuario pode ter fechado a pagina que iniciou a transferencia.
        if self.transferencias:
            await asyncio.gather(*list(self.transferencias), return_exceptions=True)
        return "NAVEGADOR_FECHADO"

    async def encerrar(self, browser):
        self.aceitar_downloads = False
        self.rede_ativa = False
        for task in list(self.transferencias):
            task.cancel()
        if self.transferencias:
            with suppress(asyncio.TimeoutError):
                await asyncio.wait_for(asyncio.gather(*list(self.transferencias), return_exceptions=True), 20)
        if browser is not None:
            with suppress(PlaywrightErro, asyncio.TimeoutError):
                await asyncio.wait_for(browser.close(), 20)
        if self.copias:
            with suppress(asyncio.TimeoutError):
                await asyncio.wait_for(asyncio.gather(*list(self.copias), return_exceptions=True), 5)
        # Cancelar to_thread nao para o parser. Esperar terminar antes de apagar
        # qualquer arquivo que ele possa ainda estar lendo, especialmente Windows.
        if self.validacoes:
            await asyncio.gather(*list(self.validacoes), return_exceptions=True)
            self.validacoes.clear()
        # Limpar parciais somente depois de encerrar as gravacoes do navegador.
        for parte in self.partes:
            with suppress(OSError):
                parte.unlink(missing_ok=True)
        for task in list(self.tarefas):
            if not task.done():
                task.cancel()
        if self.tarefas:
            await asyncio.gather(*list(self.tarefas), return_exceptions=True)

    def resumo(self):
        escolhido = next((r for r in self.resultados if r["ok"]),
                         self.resultados[-1] if self.resultados else {})
        http = escolhido.get("http") or {}
        linhas = ["DIAGNOSTICO_SBK_V2",
            "MODO=MANUAL; CAPTURA=DESDE_INICIO",
            f"ENCERRAMENTO={self.motivo}",
            f"PAGINAS_NAVEGADOR={len(self.paginas)}; RESPOSTAS_HTTP={self.contagens['resposta']}",
            f"DOWNLOADS_INICIADOS={self.contagens['downloads_recebidos']}",
            f"HTTP_DOWNLOAD={http.get('status', 'NAO_OBSERVADO')}",
            f"MIME_DOWNLOAD={http.get('content_type', 'NAO_OBSERVADO')}",
            f"CONTENT_LENGTH={http.get('content_length')}",
            f"RESULTADO={escolhido.get('motivo', 'NENHUM_DOWNLOAD')}",
            f"PDF_VALIDADO_ESTRUTURA={'SIM' if escolhido.get('ok') else 'NAO'}",
            f"BYTES={escolhido.get('bytes')}; PAGINAS_PDF={escolhido.get('paginas')}",
            f"PAGINAS_ESPERADAS={self.paginas_esperadas}",
            f"SHA256={escolhido.get('sha256')}",
            f"ARQUIVO={escolhido.get('arquivo', 'NAO_SALVO')}",
            f"PARCIAIS_RESTANTES={sum(p.exists() for p in self.partes)}",
            "SEM_REQUISICAO_EXTRA; SEM_IMPRESSAO; SEM_RECONSTRUCAO"]
        texto = "\n".join(linhas) + "\n"
        (self.pasta / "resumo.txt").write_text(texto, encoding="utf-8")
        print("\n" + texto, flush=True)
        self.registrar("fim", motivo=self.motivo, resultados=self.resultados)
        self.fechado = True
        self.log.close()
        return any(r["ok"] for r in self.resultados)


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
    def __init__(self, monitor):
        self.monitor = monitor
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

    async def instalar(self, endpoint):
        # Endpoint criado exclusivamente pelo perfil temporario deste processo.
        # Conexao local sem proxy. O endpoint e os headers nunca sao registrados.
        self.ws = await connect(endpoint, proxy=None, compression=None,
            max_size=4 * 1024 * 1024, max_queue=16, open_timeout=10, close_timeout=5)
        self.leitor = asyncio.create_task(self.receber())
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

    async def resposta(self, session, params):
        request_id = params['requestId']
        headers = params.get('responseHeaders') or []
        tipo = next((str(item.get('value', '')).split(';', 1)[0].strip().lower()
            for item in headers if str(item.get('name', '')).lower() == 'content-type'), '')
        status = params.get('responseStatusCode')
        alterar = (self.ativo and not self.fechando and status == 200
                   and tipo == 'application/pdf'
                   and not any(str(item.get('name', '')).lower() == 'content-range'
                               for item in headers))
        if alterar:
            self.candidatos += 1
            nome_local = f'sbk_original_{self.candidatos:04d}.pdf'
            associar = getattr(self.monitor, 'associar_http_download', None)
            if associar is not None:
                h = {str(item.get('name', '')).lower(): str(item.get('value', '')) for item in headers}
                associar(nome_local, {'requisicao_id': f'C{self.candidatos:04d}',
                    'status': status, 'content_type': 'application/pdf',
                    'content_length': numero(h.get('content-length')),
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
        # Inclusive respostas ADF/HTML, erros e falhas do comando experimental.
        # continueRequest na fase Response preserva corpo e cabecalhos recebidos.
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

from playwright.async_api import Error as ErroPlaywright


# Literais conferidos com o valor runtime dos seletores no app.py original.
SBK_IDS = {
    "token": "duplaAutenticacao:::content",
    "cliente": "pt1::sorTipoPesquisa::_1",
    "identificador": "pt1::itTipoPesquisaItem:::content",
    "pesquisar": "pt1::btPesquisarDocumento",
    "selecionar_documentos": "pt1::pc1::t1::sbcSelectAllDoc:::content",
    "confirmar_filtro": "pt1::pc1::btConfirmarFiltro",
    "selecionar_detalhes": "pt1::pcIPD::t3::sbcSelectAllDocDet:::content",
    "exportar": "pt1::pcIPD::btDownloadImgSelect",
}


class FalhaAutomacao(RuntimeError):
    """Falha com mensagem controlada, sem dados de campos ou respostas."""


class ElementoAmbiguo(FalhaAutomacao):
    pass


class TempoAutomacao(FalhaAutomacao):
    pass


class TokenCancelado(FalhaAutomacao):
    pass


def seletor_id(chave):
    return "[id='" + SBK_IDS[chave] + "']"


async def solicitar_token_tk(ao_abrir=None):
    """Abre Tk na thread principal e bombeia eventos sem bloquear o asyncio.

    O token fica apenas em memoria e no campo do site, nunca em print ou log.
    """
    if threading.current_thread() is not threading.main_thread():
        raise FalhaAutomacao("A janela de token precisa executar na thread principal.")
    import tkinter as tk
    from tkinter import ttk

    janela = None
    resposta = asyncio.get_running_loop().create_future()
    try:
        janela = tk.Tk()
        janela.title("SBK - Dupla Autenticacao")
        janela.geometry("500x250")
        janela.resizable(False, False)
        tk.Label(janela, text="Dupla Autenticacao", font=("Segoe UI", 12, "bold")).pack(pady=(20, 10))
        tk.Label(janela, text="Digite o codigo recebido por e-mail para continuar.", wraplength=450).pack()
        entrada = ttk.Entry(janela, width=35, justify="center", show="*")
        entrada.pack(pady=15)
        aviso = tk.Label(janela, text="")
        aviso.pack()

        def confirmar(event=None):
            valor = entrada.get().strip()
            if not valor:
                aviso.config(text="Informe o codigo antes de confirmar.")
                return
            if not resposta.done():
                resposta.set_result(valor)

        def cancelar():
            if not resposta.done():
                resposta.set_result(None)

        ttk.Button(janela, text="Confirmar", command=confirmar).pack()
        janela.bind("<Return>", confirmar)
        janela.protocol("WM_DELETE_WINDOW", cancelar)
        janela.lift()
        janela.attributes("-topmost", True)
        janela.after(500, lambda: janela.attributes("-topmost", False))
        entrada.focus_force()
        janela.update_idletasks()
        if ao_abrir is not None:
            ao_abrir()
        # Nao usar mainloop()/wait_window(): bloqueariam os eventos Playwright.
        while not resposta.done():
            janela.update_idletasks()
            janela.update()
            await asyncio.sleep(0.05)
        valor = resposta.result()
        if valor is None:
            raise TokenCancelado("Entrada do codigo cancelada. Automacao encerrada.")
        return valor
    except tk.TclError:
        raise FalhaAutomacao("Nao foi possivel abrir o Tkinter. Verifique a instalacao Tcl/Tk do Python usado para executar o aplicativo.") from None
    finally:
        if janela is not None:
            with suppress(Exception):
                janela.destroy()


def _frames_html(page):
    # page.frames ja inclui o frame principal e todos os descendentes.
    # Nao pesquisa outras abas ou frames do visualizador PDF do navegador.
    for frame in list(page.frames):
        if frame.is_detached():
            continue
        esquema = urlsplit(frame.url).scheme.lower()
        if esquema in {"http", "https"} or frame.url in {"about:blank", "about:srcdoc", ""}:
            yield frame


async def _visiveis(page, seletor=None, *, texto=None):
    encontrados = []
    for frame in _frames_html(page):
        try:
            grupo = frame.locator(seletor) if seletor is not None else frame.get_by_text(texto, exact=True)
            for indice in range(await grupo.count()):
                elemento = grupo.nth(indice)
                if await elemento.is_visible():
                    encontrados.append(elemento)
        except ErroPlaywright:
            # Um frame pode ter sido substituido por uma resposta parcial ADF.
            continue
    return encontrados


def _unico(encontrados, etapa):
    if len(encontrados) > 1:
        raise ElementoAmbiguo("Mais de um elemento visivel na etapa " + etapa + ". Nenhum clique realizado.")
    return encontrados[0] if encontrados else None


async def _esperar_unico(page, seletor, timeout, etapa):
    prazo = time.monotonic() + timeout
    while time.monotonic() < prazo:
        if page.is_closed():
            raise FalhaAutomacao("A pagina foi fechada durante a etapa " + etapa + ".")
        elemento = _unico(await _visiveis(page, seletor), etapa)
        if elemento is not None:
            try:
                if await elemento.is_enabled():
                    return elemento, max(1, int((prazo - time.monotonic()) * 1000))
            except ErroPlaywright:
                pass
        await asyncio.sleep(0.1)
    raise TempoAutomacao("Tempo esgotado na etapa " + etapa + ".")


async def _estado_login(page, timeout):
    prazo = time.monotonic() + timeout
    while time.monotonic() < prazo:
        if page.is_closed():
            raise FalhaAutomacao("A pagina foi fechada durante o login.")
        token = _unico(await _visiveis(page, seletor_id("token")), "localizar_token")
        try:
            if token is not None and await token.is_enabled():
                return "token"
        except ErroPlaywright:
            continue
        cliente = _unico(await _visiveis(page, seletor_id("cliente")), "localizar_cliente")
        try:
            if cliente is not None and await cliente.is_enabled():
                return "autenticado"
        except ErroPlaywright:
            continue
        await asyncio.sleep(0.1)
    raise TempoAutomacao("Tempo esgotado aguardando login e campo de codigo ou tela de consulta.")


async def _botao_autenticar(page, timeout):
    prazo = time.monotonic() + timeout
    while time.monotonic() < prazo:
        candidatos = await _visiveis(page, "[id='b4'] a")
        # Alternativa preservada do app.py: nome visivel exato, nunca parcial.
        if not candidatos:
            candidatos = await _visiveis(page, texto="Autenticar")
        elemento = _unico(candidatos, "autenticar")
        try:
            if elemento is not None and await elemento.is_enabled():
                return elemento, max(1, int((prazo - time.monotonic()) * 1000))
        except ErroPlaywright:
            continue
        await asyncio.sleep(0.1)
    raise TempoAutomacao("Tempo esgotado aguardando o botao Autenticar.")


async def _aguardar_adf(page, timeout):
    """Consulta API publica ADF, quando disponivel, sem mudar seu estado."""
    prazo = time.monotonic() + timeout
    estavel_desde = None
    while time.monotonic() < prazo:
        ocupado = False
        for frame in _frames_html(page):
            try:
                estado = await frame.evaluate("""() => {
                    const p = window.AdfPage && window.AdfPage.PAGE;
                    if (!p || typeof p.isSynchronizedWithServer !== 'function') return null;
                    const pronto = p.isSynchronizedWithServer();
                    return typeof pronto === 'boolean' ? pronto : null;
                }""")
                if estado is False:
                    ocupado = True
            except ErroPlaywright:
                ocupado = True
        if ocupado:
            estavel_desde = None
        elif estavel_desde is None:
            estavel_desde = time.monotonic()
        elif time.monotonic() - estavel_desde >= 0.3:
            return
        await asyncio.sleep(0.1)
    raise TempoAutomacao("Tempo esgotado aguardando o processamento da selecao pelo sistema.")


async def executar_fluxo(page, config, monitor, timeout_etapa=120, timeout_login=300,
                         solicitar_token=solicitar_token_tk):
    """Recebe pagina ja aberta; retorna depois do clique automatico em Exportar.

    O chamador instala o monitor antes da navegacao e aguarda a captura do PDF
    apos o retorno. Nenhum request, reload ou reenvio de autenticacao e criado.
    """
    if timeout_etapa <= 0 or timeout_login <= 0:
        raise ValueError("Os tempos limite precisam ser positivos.")
    etapa = "aguardar_login"

    def iniciar(nome, mensagem):
        nonlocal etapa
        etapa = nome
        print(mensagem, flush=True)
        monitor.registrar("automacao_etapa", etapa=nome, estado="iniciada")

    def concluir():
        monitor.registrar("automacao_etapa", etapa=etapa, estado="concluida")

    async def clicar(chave, nome, mensagem, *, ancora=False, checkbox=False):
        iniciar(nome, mensagem)
        seletor = seletor_id(chave) + (" > a" if ancora else "")
        elemento, restante_ms = await _esperar_unico(page, seletor, timeout_etapa, nome)
        if chave == "exportar":
            autorizar_pdf = getattr(monitor, "autorizar_pdf", None)
            if autorizar_pdf is not None:
                autorizar_pdf()
        if checkbox:
            await elemento.check(timeout=restante_ms)
        else:
            await elemento.click(timeout=restante_ms)
        if chave != "exportar":
            await _aguardar_adf(page, timeout_etapa)
        concluir()

    try:
        iniciar("aguardar_login", "Realize o login no navegador. Quando o campo de codigo aparecer, a janela Tkinter sera aberta automaticamente.")
        estado = await _estado_login(page, timeout_login)
        concluir()
        if estado == "token":
            iniciar("solicitar_token", "Campo de codigo localizado. Informe o codigo na janela SBK - Dupla Autenticacao.")
            token = await solicitar_token()
            if not isinstance(token, str) or not token.strip():
                raise TokenCancelado("Nenhum codigo foi informado. Automacao encerrada.")
            concluir()
            iniciar("preencher_token", "Preenchendo o codigo de autenticacao...")
            try:
                campo, restante_ms = await _esperar_unico(page, seletor_id("token"), timeout_etapa, etapa)
                await campo.fill(token.strip(), timeout=restante_ms)
            finally:
                token = ""
            concluir()
            iniciar("autenticar", "Clicando em Autenticar...")
            botao, restante_ms = await _botao_autenticar(page, timeout_etapa)
            await botao.click(timeout=restante_ms)
            concluir()
            iniciar("confirmar_autenticacao", "Aguardando a tela de consulta apos a autenticacao...")
            await _esperar_unico(page, seletor_id("cliente"), timeout_etapa, etapa)
            concluir()
        else:
            monitor.registrar("autenticacao_ja_concluida", origem="tela_de_consulta")
            print("Tela de consulta localizada; continuando a navegacao automatica.", flush=True)

        await clicar("cliente", "selecionar_cliente", "Selecionando Cliente...")
        iniciar("preencher_identificador", "Preenchendo o identificador configurado no .env...")
        campo, restante_ms = await _esperar_unico(page, seletor_id("identificador"), timeout_etapa, etapa)
        await campo.fill(config["ID_TESTE"], timeout=restante_ms)
        # Blur dispara o change usado pelos campos ADF antes da pesquisa.
        await campo.press("Tab", timeout=max(1, restante_ms))
        await _aguardar_adf(page, timeout_etapa)
        concluir()
        await clicar("pesquisar", "pesquisar_documento", "Clicando em Pesquisar Documento...")
        await clicar("selecionar_documentos", "selecionar_documentos", "Marcando Selecionar Todos dos documentos...", checkbox=True)
        await clicar("confirmar_filtro", "confirmar_filtro", "Clicando em Confirmar Filtro...", ancora=True)
        await clicar("selecionar_detalhes", "selecionar_detalhes", "Marcando Selecionar Detalhes...", checkbox=True)
        await clicar("exportar", "exportar_imagens", "Clicando em Exportar Imagens. Aguarde a captura do PDF original...", ancora=True)
        monitor.registrar("automacao_exportacao_disparada")
        return True
    except Exception as erro:
        monitor.registrar("automacao_falhou", etapa=etapa, classe=type(erro).__name__)
        print("A automacao parou na etapa: " + etapa + ". Consulte o resumo local.", flush=True)
        if isinstance(erro, FalhaAutomacao):
            raise
        # Erros Playwright podem incluir valores de fill(). Nunca propagar texto
        # bruto nem traceback encadeado com codigo/identificador do usuario.
        raise FalhaAutomacao("Falha na etapa " + etapa + " (" + type(erro).__name__ + ").") from None

class Aplicacao(Monitor):
    def __init__(self, pasta, timeout_download=1200, paginas_esperadas=None):
        super().__init__(pasta, timeout_download, paginas_esperadas)
        self.captura = None
        self.ultima_etapa = "inicializacao"
        self.falha_automacao = None
        self.tk_aberto = False
        self.exportou = False
        self.armada = False
        self.http_por_nome = {}

    def registrar(self, evento, **dados):
        if evento == "automacao_etapa":
            self.ultima_etapa = dados.get("etapa", self.ultima_etapa)
        elif evento == "automacao_falhou":
            self.falha_automacao = dados.get("classe", "FALHA")
        elif evento == "janela_token_aberta":
            self.tk_aberto = True
        elif evento == "automacao_exportacao_disparada":
            self.exportou = True
        super().registrar(evento, **dados)

    def autorizar_pdf(self):
        self.armada = True
        if self.captura is not None:
            self.captura.ativo = True
        self.registrar("captura_exportacao_armada")

    def associar_http_download(self, nome_local, dados):
        # Nome gerado pelo proprio app no Content-Disposition: correlacao
        # exata sem usar a ultima resposta mutavel de um servlet de sessao.
        self.http_por_nome[nome_local] = dict(dados)

    async def preservar(self, download, did, requisicao_id=None):
        dados = self.http_por_nome.get(download.suggested_filename)
        if dados is not None:
            requisicao_id = dados["requisicao_id"]
            self.respostas_por_id[requisicao_id] = dict(dados)
        return await super().preservar(download, did, requisicao_id)

    def receber_download(self, download):
        if not self.armada:
            self.registrar("download_fora_da_exportacao_ignorado")
            return
        super().receber_download(download)

    async def aguardar(self, browser, espera):
        limite = time.monotonic() + espera
        proximo_aviso = 0
        while browser.is_connected() and self.context.pages:
            agora = time.monotonic()
            if self.resultados and not self.transferencias and self.ultimo_download is not None:
                if agora - self.ultimo_download >= 2:
                    return "PDF_VALIDADO" if any(r["ok"] for r in self.resultados) else "DOWNLOAD_REJEITADO"
            if agora >= limite and not self.transferencias:
                return "TEMPO_ESGOTADO_AGUARDANDO_DOWNLOAD"
            if agora >= proximo_aviso:
                print(f"Exportacao automatica enviada. Downloads iniciados: {self.contagens['downloads_recebidos']}. Aguarde...", flush=True)
                proximo_aviso = agora + 30
            await asyncio.sleep(0.2)
        if self.transferencias:
            await asyncio.gather(*list(self.transferencias), return_exceptions=True)
        return "NAVEGADOR_FECHADO"

    def resumo(self):
        escolhido = next((r for r in self.resultados if r["ok"]), self.resultados[-1] if self.resultados else {})
        http = escolhido.get("http") or {}
        linhas = ["SBK_APP_CORRIGIDO_V3",
            "MODO=AUTOMATICO_APOS_LOGIN_MANUAL",
            f"ENCERRAMENTO={self.motivo}",
            f"ULTIMA_ETAPA={self.ultima_etapa}; FALHA_AUTOMACAO={self.falha_automacao}",
            f"TKINTER_ABERTO={'SIM' if self.tk_aberto else 'NAO'}; EXPORTACAO_AUTOMATICA={'SIM' if self.exportou else 'NAO'}",
            f"RESPOSTAS_AJUSTADAS_PARA_DOWNLOAD={self.contagens['cabecalho_download_ajustado']}",
            f"DOWNLOADS_INICIADOS={self.contagens['downloads_recebidos']}",
            f"HTTP_DOWNLOAD={http.get('status', 'NAO_OBSERVADO')}; MIME={http.get('content_type', 'NAO_OBSERVADO')}",
            f"RESULTADO={escolhido.get('motivo', 'NENHUM_DOWNLOAD')}",
            f"CLASSE_BYTES={escolhido.get('classe_bytes', 'NAO_MEDIDA')}; OFFSET_PDF={escolhido.get('offset_assinatura')}",
            f"PDF_VALIDADO_ESTRUTURA={'SIM' if escolhido.get('ok') else 'NAO'}",
            f"BYTES={escolhido.get('bytes')}; PAGINAS_PDF={escolhido.get('paginas')}; PAGINAS_ESPERADAS={self.paginas_esperadas}",
            f"ARQUIVO={escolhido.get('arquivo', 'NAO_SALVO')}",
            f"PARCIAIS_RESTANTES={sum(p.exists() for p in self.partes)}"]
        texto = "\n".join(linhas) + "\n"
        (self.pasta / "resumo.txt").write_text(texto, encoding="utf-8")
        print("\n" + texto, flush=True)
        self.registrar("fim", motivo=self.motivo, resultados=self.resultados)
        self.fechado = True
        self.log.close()
        return any(r["ok"] for r in self.resultados) and self.falha_automacao is None


async def executar_app(config, app, timeout_login=300, timeout_etapa=120, espera=900):
    async with async_playwright() as p:
        # Perfil novo e exclusivo, sem reutilizar o perfil corporativo do usuario.
        with tempfile.TemporaryDirectory(prefix="sbk_automacao_") as perfil:
            browser = None
            captura = None
            try:
                context = await p.chromium.launch_persistent_context(
                    perfil, channel="msedge", headless=False, accept_downloads=True,
                    args=["--disable-popup-blocking", "--allow-popups-during-page-unload",
                          "--remote-debugging-port=0", "--remote-debugging-address=127.0.0.1"])
                browser = context.browser
                app.instalar(context)
                app.registrar("ambiente", versao_script="3.0", python=sys.version.split()[0],
                    playwright=version("playwright"), navegador=browser.version,
                    tls_verificado=True, modo="automatico", conexao_cdp="loopback_temporario")
                arquivo_porta = Path(perfil) / "DevToolsActivePort"
                partes_endpoint = arquivo_porta.read_text(encoding="utf-8").splitlines()
                if len(partes_endpoint) < 2 or not partes_endpoint[0].isdigit() or not partes_endpoint[1].startswith("/devtools/browser/"):
                    raise FalhaAutomacao("Nao foi possivel iniciar a captura original do navegador.")
                endpoint = f"ws://127.0.0.1:{int(partes_endpoint[0])}{partes_endpoint[1]}"
                captura = CapturaOriginal(app)
                app.captura = captura
                await captura.instalar(endpoint)
                page = context.pages[0] if context.pages else await context.new_page()
                try:
                    await page.goto(config["URL_SBK"], wait_until="domcontentloaded", timeout=60000)
                except ErroPlaywright as erro:
                    app.registrar("navegacao_inicial_incompleta", classe=type(erro).__name__)

                async def dialogo():
                    return await solicitar_token_tk(ao_abrir=lambda: app.registrar("janela_token_aberta"))

                await executar_fluxo(page, config, app, timeout_etapa=timeout_etapa,
                                     timeout_login=timeout_login, solicitar_token=dialogo)
                app.motivo = await app.aguardar(browser, espera)
            except asyncio.CancelledError:
                app.motivo = "INTERROMPIDO_MANUALMENTE"
            except FalhaAutomacao as erro:
                app.motivo = "FALHA_AUTOMACAO"
                print(str(erro), flush=True)
            except Exception as erro:
                app.motivo = "FALHA_" + type(erro).__name__
                app.registrar("falha", classe=type(erro).__name__)
            finally:
                if captura is not None:
                    with suppress(Exception):
                        await captura.fechar()
                await app.encerrar(browser)


def main():
    parser = argparse.ArgumentParser(description="SBK: login manual, token Tkinter, cliques automaticos e PDF original validado.")
    parser.add_argument("--env", type=Path, default=Path(__file__).with_name(".env"))
    parser.add_argument("--timeout-login", type=int, default=300)
    parser.add_argument("--timeout-etapa", type=int, default=120)
    parser.add_argument("--espera", type=int, default=900)
    parser.add_argument("--timeout-download", type=int, default=1200)
    parser.add_argument("--paginas-esperadas", type=int)
    args = parser.parse_args()
    if any(not 10 <= value <= 7200 for value in (args.timeout_login, args.timeout_etapa, args.espera, args.timeout_download)):
        parser.error("Os prazos precisam estar entre 10 e 7200 segundos.")
    if args.paginas_esperadas is not None and args.paginas_esperadas <= 0:
        parser.error("--paginas-esperadas deve ser positivo.")
    try:
        config = configurar(args.env)
    except ConfiguracaoErro as erro:
        print("Configuracao: " + str(erro), file=sys.stderr)
        return 2
    pasta = Path(__file__).with_name(datetime.now().strftime("execucao_sbk_%Y%m%d_%H%M%S_%f"))
    try:
        app = Aplicacao(pasta, args.timeout_download, args.paginas_esperadas)
    except OSError:
        print("Nao foi possivel criar os arquivos locais. Use uma pasta com permissao de escrita.", file=sys.stderr)
        return 2
    try:
        asyncio.run(executar_app(config, app, args.timeout_login, args.timeout_etapa, args.espera))
    except KeyboardInterrupt:
        app.motivo = "INTERROMPIDO_MANUALMENTE"
    except Exception as erro:
        app.motivo = "FALHA_INICIAL_" + type(erro).__name__
        app.registrar("falha", classe=type(erro).__name__)
    finally:
        ok = app.resumo()
    print(f"Resultado local em: {pasta.name}. Se necessario, transcreva somente resumo.txt.", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
