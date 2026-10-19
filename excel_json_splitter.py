"""Diagnostico de uma exportacao SBK. Nao salva copia final nem valida o PDF.

Mantem o login manual e os seletores do app.py recebido. Observa metadados,
sem route.fetch(), repetir URLs, ler corpos HTTP ou gravar credenciais.
"""

from __future__ import annotations

import argparse
from datetime import datetime
from importlib.metadata import version
import json
from pathlib import Path
import re
import sys
import time
import tkinter as tk
from tkinter import ttk
from urllib.parse import urljoin, urlsplit

from dotenv import dotenv_values
from playwright.sync_api import Error as PlaywrightErro
from playwright.sync_api import TimeoutError as PlaywrightTimeout
from playwright.sync_api import sync_playwright


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


class Coletor:
    def __init__(self, log_path: Path):
        # Modo exclusivo: um log anterior nunca e sobrescrito.
        self.arquivo = log_path.open("x", encoding="utf-8", buffering=1)
        self.sanitizador = Sanitizador()
        self.inicio = time.monotonic()
        self.ativo = False
        self.paginas = {}
        self.frames = {}
        self.requisicoes = {}
        self.pendentes = set()
        self.ultimos_dom = {}
        self.mimes_frames = {}
        self.dom_omitidos = set()
        self.contagens = {}
        self.linhas = 0
        self.limitado = False
        self.context = None
        self.encerrado = False
        self.etapa = "inicializacao"

    def registrar(self, evento, **dados):
        if self.encerrado:
            return
        self.contagens[evento] = self.contagens.get(evento, 0) + 1
        if evento == "javascript_erro" and self.contagens[evento] > 50:
            if self.contagens[evento] == 51:
                self.registrar("limite_eventos_javascript", limite=50)
            return
        if self.linhas >= 30000 and evento not in {"fim_diagnostico", "falha", "observacao_encerrada"}:
            if not self.limitado:
                self.limitado = True
                self.arquivo.write(json.dumps({"evento": "limite_total_eventos", "limite": 30000}) + "\n")
            return
        linha = {"segundos": round(time.monotonic() - self.inicio, 3),
                 "evento": evento, **dados}
        self.arquivo.write(json.dumps(linha, ensure_ascii=True) + "\n")
        self.linhas += 1

    def marcar(self, etapa):
        self.etapa = etapa
        self.registrar("etapa", nome=etapa)
        print(f"Etapa: {etapa}", flush=True)

    def proteger(self, nome, funcao):
        def callback(*args):
            try:
                funcao(*args)
            except Exception as erro:
                # Excecoes Playwright podem conter URLs, valores e trechos HTML.
                self.registrar("observador_indisponivel", observador=nome,
                               classe=type(erro).__name__)
        return callback

    def frame_id(self, frame):
        if frame is None:
            return None
        return self.frames.setdefault(frame, f"F{len(self.frames) + 1:03d}")

    def pagina_id(self, page):
        return self.paginas.setdefault(page, f"P{len(self.paginas) + 1:03d}")

    def observar_frame(self, evento, frame):
        self.registrar(evento, frame_id=self.frame_id(frame),
                       pagina_id=self.pagina_id(frame.page),
                       pai_id=self.frame_id(frame.parent_frame),
                       endereco=self.sanitizador.url(frame.url))

    def observar_pagina(self, page):
        if page in self.paginas:
            return
        pagina_id = self.pagina_id(page)
        opener = page.opener()
        self.registrar("pagina", pagina_id=pagina_id,
                       origem_pagina_id=self.pagina_id(opener) if opener else None,
                       endereco=self.sanitizador.url(page.url))
        for evento in ("frameattached", "framenavigated", "framedetached"):
            page.on(evento, self.proteger(evento, lambda frame, ev=evento: self.observar_frame(ev, frame)))
        page.on("download", self.proteger("download", lambda download: self.registrar(
            "download_iniciado", pagina_id=pagina_id,
            endereco=self.sanitizador.url(download.url))))
        page.on("close", lambda: self.registrar("pagina_fechada", pagina_id=pagina_id))
        page.on("pageerror", lambda _erro: self.registrar("javascript_erro", pagina_id=pagina_id))
        page.on("crash", lambda: self.registrar("pagina_crash", pagina_id=pagina_id))
        for frame in page.frames:
            self.observar_frame("frame_inicial", frame)

    def instalar(self, context):
        self.context = context
        context.on("page", self.proteger("page", self.observar_pagina))
        for page in context.pages:
            self.observar_pagina(page)
        for evento, handler in (("request", self.requisicao), ("response", self.resposta),
                                ("requestfinished", self.finalizada), ("requestfailed", self.falhou)):
            context.on(evento, self.proteger(evento, handler))

    def iniciar_exportacao(self):
        self.ativo = True
        self.registrar("inicio_captura_rede", limite_requisicoes=10000)
        self.marcar("exportacao")

    def requisicao(self, request):
        if not self.ativo or request in self.requisicoes:
            return
        if len(self.requisicoes) >= 10000:
            if not self.contagens.get("limite_requisicoes"):
                self.registrar("limite_requisicoes", limite=10000)
            return
        rid = f"Q{len(self.requisicoes) + 1:05d}"
        self.requisicoes[request] = rid
        self.pendentes.add(rid)
        try:
            frame = request.frame
        except PlaywrightErro:
            frame = None
        # Estes valores existem apenas transitoriamente; o log recebe allowlist.
        headers = request.all_headers()
        self.registrar("requisicao", requisicao_id=rid, metodo=request.method,
                       tipo=request.resource_type, navegacao=request.is_navigation_request(),
                       frame_id=self.frame_id(frame),
                       pagina_id=self.pagina_id(frame.page) if frame else None,
                       endereco=self.sanitizador.url(request.url),
                       redirecionada_de=self.requisicoes.get(request.redirected_from),
                       cookie_presente=bool(headers.get("cookie")),
                       authorization_presente=bool(headers.get("authorization")),
                       csrf_header_presente=any(k in headers for k in ("x-csrf-token", "x-xsrf-token", "csrf-token")),
                       referer=self.sanitizador.url(headers["referer"]) if headers.get("referer") else None,
                       range=intervalo(headers.get("range")))

    def resposta(self, response):
        request = response.request
        h = response.headers
        # Guardar apenas MIME da navegacao, inclusive durante o login. Nao avaliar
        # DOM de renderer PDF/visualizador: pode nunca responder a evaluate().
        if request.resource_type == "document":
            try:
                self.mimes_frames[request.frame] = mime(h.get("content-type"))
            except PlaywrightErro:
                pass
        if not self.ativo:
            return
        if request not in self.requisicoes:
            self.requisicao(request)
        rid = self.requisicoes.get(request)
        if not rid:
            return
        disposition = h.get("content-disposition", "").split(";", 1)[0].strip().lower()
        encoding = h.get("content-encoding", "").strip().lower()
        self.registrar("resposta", requisicao_id=rid, status=response.status,
                       endereco=self.sanitizador.url(response.url),
                       content_type=mime(h.get("content-type")),
                       content_length=numero(h.get("content-length")),
                       content_range=intervalo(h.get("content-range")),
                       accept_ranges=h.get("accept-ranges", "").lower() == "bytes",
                       content_encoding=encoding if encoding in {"", "identity", "gzip", "br", "deflate", "zstd"} else "outro",
                       transfer_chunked="chunked" in h.get("transfer-encoding", "").lower(),
                       disposition=disposition if disposition in {"inline", "attachment"} else "ausente_ou_outro",
                       filename_presente="filename" in h.get("content-disposition", "").lower(),
                       location=self.sanitizador.url(urljoin(response.url, h["location"])) if h.get("location") else None,
                       via_service_worker=bool(response.from_service_worker))

    def finalizada(self, request):
        if not self.ativo:
            return
        rid = self.requisicoes.get(request)
        if not rid:
            return
        self.pendentes.discard(rid)
        try:
            tamanhos = request.sizes()
        except PlaywrightErro:
            tamanhos = {}
        self.registrar("requisicao_concluida", requisicao_id=rid,
                       bytes_resposta_codificados=tamanhos.get("responseBodySize"),
                       bytes_requisicao=tamanhos.get("requestBodySize"))

    def falhou(self, request):
        if not self.ativo:
            return
        rid = self.requisicoes.get(request)
        if not rid:
            return
        self.pendentes.discard(rid)
        failure = request.failure or ""
        # Somente codigos Chromium, nunca o texto livre de uma excecao.
        codigo = failure if re.fullmatch(r"net::ERR_[A-Z_0-9]+", failure) else "erro_omitido"
        self.registrar("requisicao_falhou", requisicao_id=rid, codigo=codigo)

    def inspecionar_dom(self):
        for page in list(self.context.pages):
            for frame in list(page.frames):
                if (self.mimes_frames.get(frame) != "text/html"
                        or not frame.url.startswith(("http://", "https://"))):
                    if frame not in self.dom_omitidos:
                        self.dom_omitidos.add(frame)
                        self.registrar("inspecao_dom_omitida", frame_id=self.frame_id(frame),
                                       pagina_id=self.pagina_id(page),
                                       motivo="frame_sem_navegacao_html_observada", endereco=self.sanitizador.url(frame.url))
                    continue
                try:
                    dados = frame.evaluate("""() => ({
                        frameset: !!document.querySelector('frameset'),
                        adf_loopback: typeof window.AdfLoopbackUtils !== 'undefined',
                        janela_nomeada: !!window.name,
                        elementos: Array.from(document.querySelectorAll('frame,iframe,embed,object'))
                            .slice(0, 50).map(e => ({tag: e.tagName.toLowerCase(),
                                url: e.tagName === 'OBJECT' ? e.data : e.src}))
                    })""")
                    seguro = {"frame_id": self.frame_id(frame),
                              "pagina_id": self.pagina_id(page),
                              "pai_id": self.frame_id(frame.parent_frame),
                              "frameset": dados["frameset"],
                              "adf_loopback": dados["adf_loopback"], "janela_nomeada": dados["janela_nomeada"],
                              "endereco": self.sanitizador.url(frame.url),
                              "elementos": [{"tag": e["tag"], "endereco": self.sanitizador.url(e["url"])}
                                            for e in dados["elementos"]]}
                    chave = json.dumps(seguro, sort_keys=True)
                    if self.ultimos_dom.get(frame) != chave:
                        self.ultimos_dom[frame] = chave
                        self.registrar("estrutura_visualizador", **seguro)
                except PlaywrightErro:
                    pass  # Frame pode navegar/fechar durante a observacao.

    def fechar(self, motivo):
        if self.encerrado:
            return
        self.registrar("fim_diagnostico", motivo=motivo, etapa=self.etapa,
                       requisicoes_pendentes=sorted(self.pendentes),
                       contagens=dict(self.contagens), pdf_validado=False)
        self.encerrado = True
        self.arquivo.close()


def solicitar_token():
    resultado = {"valor": ""}
    janela = tk.Tk()
    janela.title("SBK - Dupla Autenticacao")
    janela.geometry("500x220")
    janela.resizable(False, False)
    tk.Label(janela, text="Dupla Autenticacao", font=("Segoe UI", 12, "bold")).pack(pady=(20, 10))
    tk.Label(janela, text="Digite o token recebido por e-mail para continuar.", wraplength=450).pack()
    entrada = ttk.Entry(janela, width=35, justify="center", show="*")
    entrada.pack(pady=15)
    entrada.focus()

    def confirmar():
        valor = entrada.get().strip()
        if valor:
            resultado["valor"] = valor
            janela.destroy()

    ttk.Button(janela, text="Confirmar", command=confirmar).pack()
    janela.bind("<Return>", lambda _event: confirmar())
    janela.mainloop()
    if not resultado["valor"]:
        raise ConfiguracaoErro("Entrada do token cancelada.")
    return resultado["valor"]


def executar(config, coletor, espera):
    with sync_playwright() as p:
        browser = p.chromium.launch(channel="msedge", headless=False,
            args=["--disable-popup-blocking", "--allow-popups-during-page-unload"])
        browser.on("disconnected", lambda: coletor.registrar("navegador_desconectado"))
        try:
            coletor.registrar("ambiente", python=sys.version.split()[0],
                               playwright=version("playwright"), navegador=browser.version,
                               tls_verificado=True, interceptacao=False)
            context = browser.new_context(accept_downloads=True)
            context.set_default_timeout(30000)
            context.set_default_navigation_timeout(120000)
            coletor.instalar(context)
            page = context.new_page()
            coletor.marcar("abrir_site_login_manual")
            page.goto(config["URL_SBK"], wait_until="domcontentloaded")
            print("Realize o login normalmente. Aguarde a janela para informar o token.", flush=True)
            page.wait_for_selector("#duplaAutenticacao\\:\\:\\:content", timeout=120000)
            token = solicitar_token()
            page.fill("#duplaAutenticacao\\:\\:\\:content", token)
            del token
            autenticar = page.locator("#b4 a")
            if autenticar.count() and autenticar.first.is_visible():
                autenticar.first.click()
            else:
                page.get_by_text("Autenticar", exact=True).click()
            # A tela seguinte confirma que o fluxo avancou; networkidle nao prova login.
            coletor.marcar("selecionar_cliente")
            page.locator("#pt1\\:\\:sorTipoPesquisa\\:\\:_1").click(timeout=120000)
            page.wait_for_timeout(1000)
            coletor.marcar("preencher_identificador")
            page.fill("#pt1\\:\\:itTipoPesquisaItem\\:\\:\\:content", config["ID_TESTE"])
            page.wait_for_timeout(1000)
            coletor.marcar("pesquisar_documento")
            page.click("#pt1\\:\\:btPesquisarDocumento")
            page.wait_for_timeout(5000)
            coletor.marcar("selecionar_documentos")
            chk1 = "#pt1\\:\\:pc1\\:\\:t1\\:\\:sbcSelectAllDoc\\:\\:\\:content"
            page.wait_for_selector(chk1, timeout=15000)
            page.wait_for_timeout(2000)
            page.locator(chk1).set_checked(True)
            page.wait_for_timeout(2000)
            coletor.marcar("confirmar_filtro")
            page.locator("#pt1\\:\\:pc1\\:\\:btConfirmarFiltro > a").click(timeout=15000)
            coletor.marcar("selecionar_detalhes")
            chk2 = "#pt1\\:\\:pcIPD\\:\\:t3\\:\\:sbcSelectAllDocDet\\:\\:\\:content"
            page.wait_for_selector(chk2, timeout=15000)
            page.wait_for_timeout(2000)
            page.locator(chk2).set_checked(True)
            page.wait_for_timeout(3000)
            exportar = page.locator("#pt1\\:\\:pcIPD\\:\\:btDownloadImgSelect > a")
            exportar.wait_for(timeout=15000)
            page.wait_for_timeout(3000)
            exportar.scroll_into_view_if_needed()
            coletor.iniciar_exportacao()
            inicio_exportacao = time.monotonic()
            exportar.click(no_wait_after=True)
            print("Observando a exportacao. Nao clique novamente em Exportar.", flush=True)
            print("Apos o PDF carregar, voce pode encerrar com Ctrl+C neste terminal.", flush=True)
            proximo_dom = 0
            proximo_aviso = 0
            while time.monotonic() - inicio_exportacao < espera:
                decorrido = time.monotonic() - inicio_exportacao
                if decorrido >= proximo_dom:
                    coletor.inspecionar_dom()
                    proximo_dom = decorrido + 5
                if decorrido >= proximo_aviso:
                    print(f"Observacao: {int(decorrido)}s; respostas: {coletor.contagens.get('resposta', 0)}; "
                          f"downloads iniciados: {coletor.contagens.get('download_iniciado', 0)}", flush=True)
                    proximo_aviso = decorrido + 30
                if not browser.is_connected() or not context.pages:
                    return "navegador_fechado"
                # Espera diagnostica: entrega controle ao dispatcher sync do Playwright.
                context.pages[0].wait_for_timeout(250)
            return "prazo_observacao_encerrado"
        finally:
            # Snapshot antes do fechamento. O chamador ainda precisa registrar
            # eventuais excecoes e o motivo real antes de fechar o arquivo.
            coletor.registrar("observacao_encerrada", etapa=coletor.etapa,
                               requisicoes_pendentes=sorted(coletor.pendentes))
            coletor.ativo = False
            try:
                browser.close()
            except PlaywrightErro:
                pass


def main():
    parser = argparse.ArgumentParser(description="Observa uma exportacao SBK sem ler corpos nem validar o PDF.")
    parser.add_argument("--env", type=Path, default=Path(__file__).with_name(".env"))
    parser.add_argument("--espera", type=int, default=600, help="Segundos de observacao apos exportar (30 a 3600).")
    args = parser.parse_args()
    if not 30 <= args.espera <= 3600:
        parser.error("--espera deve estar entre 30 e 3600 segundos.")
    try:
        config = configurar(args.env)
    except ConfiguracaoErro as erro:
        print(f"Configuracao: {erro}", file=sys.stderr)
        return 2
    destino = Path(__file__).with_name(datetime.now().strftime("diagnostico_sbk_%Y%m%d_%H%M%S_%f.jsonl"))
    try:
        coletor = Coletor(destino)
    except OSError:
        print("Nao foi possivel criar o log; extraia o pacote em uma pasta com permissao de escrita.", file=sys.stderr)
        return 2
    codigo = 0
    try:
        motivo = executar(config, coletor, args.espera)
    except KeyboardInterrupt:
        motivo = "interrupcao_manual"
    except Exception as erro:
        # Nao imprimir str(erro), pois pode conter URL, token, identificador ou HTML.
        coletor.registrar("falha", etapa=coletor.etapa, classe=type(erro).__name__,
                           timeout=isinstance(erro, PlaywrightTimeout))
        print(f"Diagnostico interrompido na etapa {coletor.etapa} ({type(erro).__name__}).", flush=True)
        motivo = "falha"
        codigo = 1
    finally:
        coletor.fechar(locals().get("motivo", "fim"))
    print(f"Log sanitizado: {destino.name}", flush=True)
    print("Coleta encerrada. A integridade e o download do PDF ainda NAO foram comprovados.", flush=True)
    return codigo


if __name__ == "__main__":
    raise SystemExit(main())
