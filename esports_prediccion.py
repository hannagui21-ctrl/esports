"""
Pronósticos ESportsBattle Football: todas las ligas del día, en segundo plano
============================================================================
Qué hace
  - Sigue TODAS las ligas del día a la vez (unas 58), con el navegador oculto y prioridad
    baja para no estorbar el resto del computador.
  - Lee los datos por la API interna del sitio (la misma que usa la página). La descubre
    sola abriendo una liga una vez; si no la encuentra, lee el HTML de cada liga.
  - Si arrancas tarde (por ejemplo de noche), primero se pone al día con todo lo jugado:
    cada partido terminado se "pronostica" como si fuera antes de jugarse, usando solo lo
    que había pasado hasta esa hora, y se verifica contra el resultado real.
  - 13 modelos compiten y se combinan: Poisson, Maher, Dixon-Coles, Poisson bivariado,
    Binomial negativa, Jugador + equipo, Elo + logit ordenado, Pi-ratings, Glicko-2,
    Bradley-Terry, Massey, Promedio simple y Ensamble bayesiano (BMA).
  - Además del 1X2 calcula más/menos goles, ambos marcan y marcador más probable.
  - Panel web liviano que se abre desde cualquier dispositivo: en tu red local y, si tienes
    cloudflared instalado, con un enlace público https protegido por clave.
  - Análisis del día: desde qué liga y con cuánto historial los pronósticos son más
    confiables, calibración, equipos, jugadores y patrones (fatiga, revancha, hora, etc.).

Uso
  python esports_prediccion.py                 # en vivo, todas las ligas de hoy
  python esports_prediccion.py --solo-html     # sin API, leyendo cada página
  python esports_prediccion.py --archivo a.html b.html   # backtest con páginas guardadas
  python esports_prediccion.py --nueva         # ignora lo ya guardado de hoy
  python esports_prediccion.py --ver-navegador # muestra el navegador (para depurar)

Requisitos
  pip install playwright beautifulsoup4 openpyxl
  playwright install chromium
  Enlace público (opcional): scoop install cloudflared

Marcadores: el PRIMERO son goles y el SEGUNDO tiros de esquina. El resultado se decide solo
por goles (3/1/0). Desempate: diferencia de goles y goles a favor.
"""
import argparse
import atexit
import bisect
import gzip
import json
import math
import os
import platform
import queue
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor, as_completed
import random
import re
import secrets
import shutil
import socket
import sqlite3
import subprocess
import sys
import threading
import time
import urllib.request
import webbrowser
from collections import OrderedDict, defaultdict
from datetime import date, datetime, timedelta
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urljoin, urlparse

from bs4 import BeautifulSoup
from openpyxl import Workbook
from openpyxl.styles import Font

# ---------------- CONFIGURACIÓN ----------------
URL_HOME = os.environ.get("URL_SITIO", "https://football.esportsbattle.com/")
URL_SCHEDULE = URL_HOME + "en/schedule"
URL_API_TORNEOS = URL_HOME + "api/tournaments?page={pagina}&dateFrom={desde}&dateTo={hasta}"
TORNEO_BUSCADO = None          # None = todas. Ej.: "International" filtra por nombre
ZONA_HORARIA = "America/Bogota"
REFRESCO_SEG = 15              # sin API: cada cuánto se leen las páginas de las ligas en juego
VIGIA_SEG = 5                  # con API: cada cuánto se revisan los marcadores en vivo
HILOS_HTTP = 16                # descargas simultáneas
UMBRAL_ACIERTO = 0.70          # 'alta confianza' = rango donde el historial acierta al menos esto
REFRESCO_LISTA_MIN = 3         # cada cuánto se relee la lista de ligas del día
DURACION_PARTIDO_MIN = 15      # un partido de otra liga cuenta como jugado si empezó hace esto
VIDA_MEDIA_HORAS = 24.0        # el peso de un partido viejo se reduce a la mitad cada 24 h (se autoajusta)
PESO_OTRA_LIGA = 0.7           # peso base de un partido de otra liga (el de la liga actual pesa 1)
F_OTRO_EQUIPO = 0.6            # si el jugador usaba otro equipo, ese partido pesa esto
MAX_HIST_JUGADOR = 80          # partidos previos por jugador que se usan como máximo
DIAS_HISTORIAL = int(os.environ.get("DIAS_HISTORIAL", "30"))           # días anteriores que se descargan y usan en los pronósticos
AUTOAJUSTE = True              # ajustar parámetros con los resultados reales (una vez al día)
PRIOR = 2.0                    # partidos "promedio" que suavizan muestras pequeñas
MAX_GOLES = 30
MIN_ELECCION = 30              # pronósticos verificados antes de confiar en el ranking de modelos
VENTANA_RANKING = 300          # el ranking de modelos mira los últimos N pronósticos
ETA_BMA = 0.3                  # qué tan rápido el ensamble premia al modelo que va mejor
SIM_PANEL = 1500               # Monte Carlo para "probabilidad de campeón" en ligas en juego
SIN_CAMBIOS_MAX_MIN = 75       # liga empezada sin cambios este tiempo = se deja de consultar
FIN_DIA_SIN_LIGAS_MIN = 45     # sin ligas por jugar este tiempo = terminó el día
PUERTO_PANEL = int(os.environ.get("PORT", "8765"))
CARPETA_SALIDA = os.environ.get("CARPETA_DATOS", "salidas")
VERSION_SESION = 3
MAX_PAGINAS_SCHEDULE = 10
EXCEL_CADA_MIN = 30
# -----------------------------------------------

AHORA = datetime.now    # se puede fijar en pruebas


# ================= FECHAS =================
MESES = {"jan": 1, "feb": 2, "mar": 3, "apr": 4, "may": 5, "jun": 6, "jul": 7, "aug": 8,
         "sep": 9, "oct": 10, "nov": 11, "dec": 12, "ene": 1, "abr": 4, "ago": 8, "dic": 12}


def _fecha(a, m, d):
    try:
        return date(a, m, d)
    except ValueError:
        return None


def leer_fecha_hora(texto, base):
    """Lee 'HH:MM' con o sin fecha (2026-11-09, 09.11, 09/11/2026, 9 Nov, Nov 9, Tomorrow)."""
    t = " ".join((texto or "").split())
    hm = re.search(r"(\d{1,2}):(\d{2})", t)
    if not hm:
        return None, False
    h, mi = int(hm.group(1)), int(hm.group(2))
    if h > 23 or mi > 59:
        return None, False
    resto = (t[:hm.start()] + " " + t[hm.end():]).lower()
    d = None
    m = re.search(r"(\d{4})-(\d{1,2})-(\d{1,2})", resto)
    if m:
        d = _fecha(int(m.group(1)), int(m.group(2)), int(m.group(3)))
    if d is None:
        m = re.search(r"(?<!\d)(\d{1,2})[./](\d{1,2})(?:[./](\d{2,4}))?(?!\d)", resto)
        if m:
            x, y = int(m.group(1)), int(m.group(2))
            anio = int(m.group(3)) if m.group(3) else base.year
            anio += 2000 if anio < 100 else 0
            d = _fecha(anio, y, x) if y <= 12 else _fecha(anio, x, y)
    if d is None:
        for patron, orden in ((r"(?<!\d)(\d{1,2})\s+([a-zé]{3,})\.?,?(?:\s+(\d{4}))?", "dm"),
                              (r"([a-zé]{3,})\.?\s+(\d{1,2})(?!\d)(?:,?\s+(\d{4}))?", "md")):
            for m in re.finditer(patron, resto):
                dia, mes = (m.group(1), m.group(2)) if orden == "dm" else (m.group(2), m.group(1))
                mes = MESES.get(mes[:3])
                if mes:
                    d = _fecha(int(m.group(3)) if m.group(3) else base.year, mes, int(dia))
                    if d:
                        break
            if d:
                break
    if d is None:
        if "tomorrow" in resto or "mañana" in resto:
            d = base + timedelta(days=1)
        elif "yesterday" in resto or "ayer" in resto:
            d = base - timedelta(days=1)
    con_fecha = d is not None
    d = d or base
    return datetime(d.year, d.month, d.day, h, mi), con_fecha


def asignar_fechas(partidos, base):
    """Fecha cada partido; si solo hay hora y 'retrocede' más de 12 h, cruzó la medianoche."""
    previo = None
    for p in partidos:
        if p.get("dt"):
            previo = p["dt"]
            continue
        dt, con_fecha = leer_fecha_hora(p.get("hora", ""), base)
        if dt and not con_fecha and previo and dt < previo - timedelta(hours=12):
            dt += timedelta(days=1)
        p["dt"] = dt
        if dt:
            previo = dt


def a_local(valor, offset_min=0):
    """Fecha de la API (ISO con o sin zona, o epoch) a hora local sin zona."""
    dt = None
    if isinstance(valor, (int, float)) and valor > 1e9:
        dt = datetime.fromtimestamp(valor / 1000 if valor > 1e12 else valor)
    elif isinstance(valor, str) and valor.strip():
        s = valor.strip()
        if s.isdigit():
            return a_local(int(s), offset_min)
        if re.match(r"^\d{4}-\d{2}-\d{2}", s):
            s = s.replace("Z", "+00:00")
            if len(s) > 10 and s[10] == " ":
                s = s[:10] + "T" + s[11:]
            try:
                dt = datetime.fromisoformat(s)
            except ValueError:
                try:
                    dt = datetime.fromisoformat(s[:19])
                except ValueError:
                    dt = None
            if dt and dt.tzinfo:
                dt = dt.astimezone().replace(tzinfo=None)
    if dt is None:
        return None
    return (dt + timedelta(minutes=offset_min)).replace(second=0, microsecond=0)


def orden_crono(p):
    return (p.get("dt") is None, p.get("dt") or datetime.min, p.get("idx", 10 ** 6))


def iso(dt):
    return dt.isoformat(timespec="minutes") if isinstance(dt, datetime) else dt


def desde_iso(x):
    if isinstance(x, str) and x:
        try:
            return datetime.fromisoformat(x)
        except ValueError:
            return None
    return x if isinstance(x, datetime) else None


PALABRAS_FIN = ("finish", "complete", "ended", "closed")
PALABRAS_ANULADO = ("cancel", "postpon", "annul", "abandon", "technical")
PALABRAS_VIVO = ("live", "progress", "running", "started", "playing")


# ================= LECTURA DEL HTML =================
def partidos_desde_html(html, base):
    """Partidos de la página de una liga, con el formato común del script."""
    soup = BeautifulSoup(html, "html.parser")
    etiqueta = soup.select_one(".tournament-title-label")
    nombre = etiqueta.get_text(strip=True) if etiqueta else ""
    out = []
    for fila in soup.select(".tournament-matches-row"):
        bloques = fila.select("div.participant-photo-logo")
        if len(bloques) != 2:
            continue
        jug, eqs = [], []
        for b in bloques:
            j = b.select_one("a.text-link")
            e = b.select_one(".participant-photo-logo-team")
            jug.append(j.get_text(strip=True) if j else "?")
            eqs.append(e.get_text(strip=True) if e else "")
        est = fila.select_one(".tournament-matches-cell-status .subcaption-1")
        estado = est.get_text(strip=True) if est else ""
        hora = fila.select_one(".tournament-matches-date")
        consola = fila.select_one(".console-match-icon")
        marc = []
        for m in fila.select(".match-scores"):
            nums = re.findall(r"\d+", m.get_text(" ", strip=True))
            if len(nums) == 2:
                marc.append((int(nums[0]), int(nums[1])))
        goles = marc[0] if marc else None
        esq = marc[1] if len(marc) > 1 else (None, None)
        el = estado.lower()
        anulado = any(w in el for w in PALABRAS_ANULADO)
        terminado = (not anulado) and "finish" in el and goles is not None
        vivo = (not terminado) and any(w in el for w in PALABRAS_VIVO)
        out.append({"idx": len(out), "a": jug[0], "b": jug[1], "eq_a": eqs[0], "eq_b": eqs[1],
                    "hora": hora.get_text(" ", strip=True) if hora else "", "dt": None,
                    "estado": estado, "terminado": terminado, "anulado": anulado, "en_vivo": vivo,
                    "vivo": list(goles) if (vivo and goles) else None,
                    "ga": goles[0] if terminado else None, "gb": goles[1] if terminado else None,
                    "ca": esq[0] if terminado else None, "cb": esq[1] if terminado else None,
                    "consola": consola.get_text(strip=True) if consola else ""})
    asignar_fechas(out, base)
    return nombre, out


# ================= LECTURA GENÉRICA DE JSON =================
CLAVES_NICK = ("nickname", "nick", "nickName", "login", "username", "gamertag")
CLAVES_NOMBRE = ("name", "title", "token_international", "token")
CLAVES_EQUIPO = ("token_international", "name", "title", "token", "short_name", "shortName")
CLAVES_FECHA = ("date", "start_date", "startDate", "date_start", "dateStart", "begin_at", "beginAt",
                "start_time", "startTime", "scheduled_at", "scheduledAt", "datetime", "time", "start")
CLAVES_ESTADO = ("status", "status_id", "statusId", "state", "match_status")
PARES_PART = (("participant1", "participant2"), ("home", "away"), ("player1", "player2"),
              ("team1", "team2"), ("first", "second"), ("opponent1", "opponent2"))
LISTAS_PART = ("participants", "opponents", "players", "competitors")


def _texto(d, claves):
    for k in claves:
        v = d.get(k)
        if isinstance(v, str) and v.strip():
            return v.strip()
    return None


def _nombre_part(p):
    t = _texto(p, CLAVES_NICK)
    if t:
        return t
    for k in ("participant", "player", "user", "gamer"):
        v = p.get(k)
        if isinstance(v, dict):
            t = _texto(v, CLAVES_NICK) or _texto(v, CLAVES_NOMBRE)
            if t:
                return t
    return _texto(p, ("name", "title"))


def _equipo_part(p):
    for k in ("team", "club", "squad"):
        v = p.get(k)
        if isinstance(v, dict):
            t = _texto(v, CLAVES_EQUIPO)
            if t:
                return t
        elif isinstance(v, str) and v.strip():
            return v.strip()
    for k in ("participant", "player"):
        v = p.get(k)
        if isinstance(v, dict) and isinstance(v.get("team"), dict):
            t = _texto(v["team"], CLAVES_EQUIPO)
            if t:
                return t
    return _texto(p, ("team_name", "teamName", "club_name")) or ""


def _num(v):
    if isinstance(v, bool):
        return None
    if isinstance(v, (int, float)):
        return int(v)
    if isinstance(v, str) and v.strip().isdigit():
        return int(v.strip())
    return None


def _goles_part(p):
    for k in ("score", "goals", "result", "points"):
        n = _num(p.get(k))
        if n is not None:
            return n
    return None


def _esquinas_part(p):
    for k, v in p.items():
        if "corner" in str(k).lower():
            n = _num(v)
            if n is not None:
                return n
    return None


def _estado(m):
    for k in CLAVES_ESTADO:
        v = m.get(k)
        if isinstance(v, dict):
            v = _texto(v, ("name", "title", "code", "slug")) or v.get("id")
        if v is not None and v != "":
            return str(v)
    return ""


def _participantes(m):
    for k1, k2 in PARES_PART:
        if isinstance(m.get(k1), dict) and isinstance(m.get(k2), dict):
            return m[k1], m[k2], k1
    for k in LISTAS_PART:
        v = m.get(k)
        if isinstance(v, list) and len(v) == 2 and all(isinstance(x, dict) for x in v):
            return v[0], v[1], k
    return None


def extraer_partidos_json(data):
    """Busca partidos en cualquier JSON: objetos con dos participantes con nombre."""
    out = []

    def visitar(x, prof):
        if prof > 7:
            return
        if isinstance(x, dict):
            ps = _participantes(x)
            if ps:
                p1, p2, _ = ps
                a, b = _nombre_part(p1), _nombre_part(p2)
                if a and b:
                    ga, gb = _goles_part(p1), _goles_part(p2)
                    if ga is None or gb is None:
                        for k1, k2 in (("score1", "score2"), ("home_score", "away_score"),
                                       ("homeScore", "awayScore"), ("goals1", "goals2")):
                            if _num(x.get(k1)) is not None and _num(x.get(k2)) is not None:
                                ga, gb = _num(x.get(k1)), _num(x.get(k2))
                                break
                    fecha = None
                    for k in CLAVES_FECHA:
                        if x.get(k) not in (None, ""):
                            fecha = x.get(k)
                            break
                    out.append({"id": x.get("id"), "a": a, "b": b, "eq_a": _equipo_part(p1),
                                "eq_b": _equipo_part(p2), "ga": ga, "gb": gb,
                                "ca": _esquinas_part(p1), "cb": _esquinas_part(p2),
                                "fecha_raw": fecha, "estado": _estado(x),
                                "consola": _texto(x, ("console", "location", "stream", "table")) or ""})
                    return
            for v in x.values():
                visitar(v, prof + 1)
        elif isinstance(x, list):
            for v in x:
                visitar(v, prof + 1)

    visitar(data, 0)
    return out


def extraer_torneos_json(data):
    """Torneos en el JSON de la lista: objetos con id, nombre y fecha, sin participantes."""
    out, vistos = [], set()

    def visitar(x, prof):
        if prof > 6:
            return
        if isinstance(x, dict):
            if "id" in x and _participantes(x) is None:
                nombre = _texto(x, ("token_international", "name", "title", "token"))
                fecha = next((x[k] for k in CLAVES_FECHA if x.get(k) not in (None, "")), None)
                if nombre and fecha is not None and str(x["id"]) not in vistos:
                    vistos.add(str(x["id"]))
                    out.append({"id": str(x["id"]), "nombre": nombre, "fecha_raw": fecha,
                                "estado_api": _estado(x)})
                    return
            for v in x.values():
                visitar(v, prof + 1)
        elif isinstance(x, list):
            for v in x:
                visitar(v, prof + 1)

    visitar(data, 0)
    return out


def total_paginas(data):
    if isinstance(data, dict):
        for k in ("totalPages", "total_pages", "pages", "last_page", "lastPage", "pageCount"):
            n = _num(data.get(k))
            if n:
                return n
        for k in ("meta", "pagination", "paging"):
            if isinstance(data.get(k), dict):
                n = total_paginas(data[k])
                if n:
                    return n
    return None


# ================= EXTRACCIÓN EN VIVO (navegador oculto) =================
def bajar_prioridad():
    """Prioridad baja para este proceso y sus hijos (el navegador hereda la prioridad)."""
    try:
        if os.name == "nt":
            import ctypes
            k = ctypes.windll.kernel32
            k.SetPriorityClass(k.GetCurrentProcess(), 0x00004000)   # BELOW_NORMAL
        else:
            os.nice(5)
    except Exception:
        pass


def cerrar_avisos(page):
    for texto in ("Accept all", "Accept", "I agree", "Agree", "Got it", "OK"):
        try:
            b = page.get_by_role("button", name=re.compile(rf"^{texto}$", re.I))
            if b.count() and b.first.is_visible():
                b.first.click(timeout=2000)
                return
        except Exception:
            pass


def id_de_href(href):
    nums = re.findall(r"\d+", urlparse(href).path)
    return nums[-1] if nums else None


def reemplazar_ultimo(texto, viejo, nuevo):
    i = texto.rfind(viejo)
    return texto if i < 0 else texto[:i] + nuevo + texto[i + len(viejo):]


class ClienteHTTP:
    """Peticiones JSON directas (sin abrir páginas), en paralelo. Usa las cookies del navegador oculto."""

    def __init__(self):
        self.headers = {"Accept": "application/json, text/plain, */*", "Accept-Language": "en-US,en;q=0.9",
                        "Accept-Encoding": "gzip", "Referer": URL_HOME, "Cache-Control": "no-cache",
                        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                                      "(KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36"}

    def configurar(self, ua, cookies):
        self.headers["User-Agent"] = ua
        if cookies:
            self.headers["Cookie"] = "; ".join(f"{c['name']}={c['value']}" for c in cookies)

    def json(self, url, timeout=15):
        try:
            sep = "&" if "?" in url else "?"
            req = urllib.request.Request(f"{url}{sep}_={int(time.time() * 1000)}", headers=self.headers)
            with urllib.request.urlopen(req, timeout=timeout) as r:
                datos = r.read()
                if r.headers.get("Content-Encoding") == "gzip":
                    datos = gzip.decompress(datos)
            return json.loads(datos.decode("utf-8"))
        except Exception:
            return None

    def muchos(self, urls, hilos=HILOS_HTTP):
        out = {}
        with ThreadPoolExecutor(max_workers=max(1, min(hilos, len(urls)))) as ex:
            futuros = {ex.submit(self.json, u): u for u in urls}
            for f in as_completed(futuros):
                out[futuros[f]] = f.result()
        return out


class Extractor:
    """Lee el sitio con Chrome/Edge oculto. Aprende la API interna; si no puede, usa el HTML."""

    def __init__(self, panel, fecha, solo_html=False, visible=False):
        self.panel, self.fecha = panel, fecha
        self.solo_html, self.visible = solo_html, visible
        self.pw = self.browser = self.ctx = self.page = None
        self.patron_api = self.patron_pagina = None
        self.codigos_fin, self.codigos_no_fin = set(), set()
        self.offset_min = 0
        self.api_lista = None            # None = sin probar, True/False
        self.aprendido = False
        self.diag = {}
        self.http = ClienteHTTP()
        self.http_ok = None      # None = sin probar; True = la API responde sin navegador

    # ---- navegador ----
    def abrir(self):
        from playwright.sync_api import sync_playwright
        self.pw = sync_playwright().start()
        args = ["--disable-blink-features=AutomationControlled", "--disable-gpu", "--mute-audio",
                "--disable-extensions", "--no-first-run", "--disable-background-networking",
                "--renderer-process-limit=2", "--js-flags=--max-old-space-size=256"]
        opciones = dict(headless=not self.visible, args=args)
        for canal in ("chrome", "msedge", None):
            try:
                self.browser = (self.pw.chromium.launch(channel=canal, **opciones) if canal
                                else self.pw.chromium.launch(**opciones))
                break
            except Exception:
                continue
        if self.browser is None:
            raise SystemExit("No pude abrir Chrome, Edge ni Chromium. Ejecuta: playwright install chromium")
        version = self.browser.version.split(".")[0]
        ua = (f"Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
              f"Chrome/{version}.0.0.0 Safari/537.36")
        self.ctx = self.browser.new_context(viewport={"width": 1280, "height": 800}, locale="en-US",
                                            timezone_id=ZONA_HORARIA, user_agent=ua)
        self.ctx.route("**/*", lambda r: r.abort() if r.request.resource_type in
                       ("image", "media", "font") else r.continue_())
        self.page = self.ctx.new_page()
        try:
            self.page.goto(URL_HOME, wait_until="domcontentloaded", timeout=60000)
            self.page.wait_for_timeout(2000)
            cerrar_avisos(self.page)
        except Exception as e:
            self.panel.avisar(f"La página principal tardó en cargar ({type(e).__name__}); sigo.")
        try:
            self.http.configurar(ua, self.ctx.cookies())
        except Exception:
            pass

    def cerrar(self):
        for f in (lambda: self.browser.close(), lambda: self.pw.stop()):
            try:
                f()
            except Exception:
                pass

    def _json(self, url):
        if self.http_ok is not False:
            d = self.http.json(url)
            if d is not None:
                if not self.http_ok:
                    self.http_ok = True
                return d
        try:
            r = self.ctx.request.get(url, headers={"Accept": "application/json"}, timeout=30000)
            if r.ok and self.http_ok is None:
                self.http_ok = False     # solo responde dentro del navegador: sin lectura paralela
            if not r.ok:
                return None
            return r.json()
        except Exception:
            return None

    def _ir(self, url, selector, espera=45000):
        try:
            self.page.goto(url, wait_until="domcontentloaded", timeout=60000)
            self.page.wait_for_selector(selector, timeout=espera)
            self.page.wait_for_timeout(800)
            return True
        except Exception:
            return False

    # ---- lista de ligas ----
    def listar(self):
        torneos = {}
        if not self.solo_html and self.api_lista is not False:
            api = self._listar_api()
            if api:
                if self.api_lista is None:
                    self.panel.avisar(f"Lista de ligas por API: {len(api)} ligas hoy (incluye las ya jugadas).")
                self.api_lista = True
                for t in api:
                    torneos[t["id"]] = t
            elif self.api_lista is None:
                self.api_lista = False
                self.panel.avisar("La API de la lista no respondió; uso la página Schedule "
                                  "(solo muestra ligas próximas o en juego).")
        if not self.api_lista or not self.patron_pagina:
            for t in self._listar_html():
                torneos.setdefault(t["id"], t).update({k: v for k, v in t.items() if v})
        for t in torneos.values():
            if not t.get("url") and self.patron_pagina:
                t["url"] = self.patron_pagina.replace("{id}", t["id"])
        return list(torneos.values())

    def descargar_dia(self, dia, avisar_cada=None):
        """Resultados reales de un día anterior (solo si la API está disponible)."""
        if not (self.api_lista and self.patron_api):
            return None
        torneos = self._listar_api(dia)
        if not torneos:
            return None
        nombres, todos = {}, []
        for t, data in self._datos_ligas(torneos).items():
            if not data:
                continue
            lista = [self._normalizar(m, k) for k, m in enumerate(extraer_partidos_json(data))]
            asignar_claves(t, lista)
            nombres[t] = next(x["nombre"] for x in torneos if x["id"] == t)
            todos += [p for p in lista if p["terminado"]]
        return nombres, todos

    def _datos_ligas(self, ligas):
        """JSON de varias ligas: en paralelo si la API responde sin navegador."""
        urls = {L["id"]: self.patron_api.replace("{id}", L["id"]) for L in ligas}
        if self.http_ok:
            res = self.http.muchos(list(urls.values()))
            return {i: res.get(u) for i, u in urls.items()}
        return {i: self._json(u) for i, u in urls.items()}

    def puede_vigilar(self):
        return bool(self.patron_api and self.http_ok and not self.solo_html)

    def partidos_varios(self, ligas, progreso=None):
        """{id: (lista, nombre)} de varias ligas; con API va en paralelo."""
        out = {}
        if self.patron_api and not self.solo_html and ligas:
            for i, data in self._datos_ligas(ligas).items():
                lst = extraer_partidos_json(data) if data else []
                if lst:
                    out[i] = ([self._normalizar(m, k) for k, m in enumerate(lst)], None)
        resto = [L for L in ligas if L["id"] not in out]
        for n, L in enumerate(resto, 1):
            out[L["id"]] = self.partidos(L)
            if progreso:
                progreso(n, len(resto))
        return out

    def _listar_api(self, fecha=None):
        fecha = fecha or self.fecha
        desde, hasta = fecha.isoformat(), (fecha + timedelta(days=1)).isoformat()
        out, pagina = [], 1
        while pagina <= 40:
            data = self._json(URL_API_TORNEOS.format(pagina=pagina, desde=desde, hasta=hasta))
            if data is None:
                break
            lst = extraer_torneos_json(data)
            out += lst
            tot = total_paginas(data)
            if not lst or not tot or pagina >= tot:
                break
            pagina += 1
        res = []
        for t in out:
            t["dt"] = a_local(t.pop("fecha_raw"), self.offset_min)
            if t["dt"] is None or t["dt"].date() == fecha:
                res.append(t)
        return res

    def _listar_html(self):
        """Lee todas las páginas del Schedule (?page=1, ?page=2, ...)."""
        out, vistos = [], set()
        pagina, ultima = 1, 1
        while pagina <= min(ultima, MAX_PAGINAS_SCHEDULE):
            if not self._ir(f"{URL_SCHEDULE}?page={pagina}", "li.tournaments-schedule-row"):
                break
            if pagina == 1:
                cerrar_avisos(self.page)
            try:
                nums = self.page.eval_on_selector_all(
                    ".pagination a[data-page]", "els => els.map(e => parseInt(e.dataset.page) || 0)")
                ultima = max([ultima] + nums)
            except Exception:
                pass
            nuevos = [t for t in self._filas_schedule() if t["id"] not in vistos]
            if not nuevos:
                break
            for t in nuevos:
                vistos.add(t["id"])
            out += nuevos
            pagina += 1
        return out

    def _filas_schedule(self):
        out = []
        filas = self.page.locator("li.tournaments-schedule-row")
        for i in range(filas.count()):
            fila = filas.nth(i)
            try:
                nombre = fila.locator(".tournament-title-label").first.inner_text().strip()
                href = fila.locator(".tournaments-cell-details a.icon-link").first.get_attribute("href")
                texto = fila.inner_text()
            except Exception:
                continue
            tid = id_de_href(href or "")
            if not tid:
                continue
            url = urljoin(URL_HOME, href)
            if not self.patron_pagina:
                self.patron_pagina = reemplazar_ultimo(url, tid, "{id}")
            dt, _ = leer_fecha_hora(texto, self.fecha)
            out.append({"id": tid, "nombre": nombre, "url": url, "dt": dt})
        return out

    # ---- aprender la API de partidos ----
    def aprender(self, ligas):
        if self.solo_html or self.aprendido:
            return
        ahora = AHORA()
        cand = [L for L in ligas if L.get("url") and L.get("dt") and L["dt"] < ahora - timedelta(minutes=20)]
        cand.sort(key=lambda L: L["dt"], reverse=True)
        cand += [L for L in ligas if L.get("url") and L not in cand]
        for L in cand[:3]:
            if self._aprender_de(L):
                break
        self.aprendido = True
        if not self.patron_api:
            self.panel.avisar("No encontré la API de partidos; leo cada liga desde su página (más lento).")

    def _aprender_de(self, L):
        capt = []

        def al_responder(r):
            try:
                if r.request.resource_type in ("xhr", "fetch") and "json" in (r.headers.get("content-type") or ""):
                    capt.append(r)
            except Exception:
                pass

        self.page.on("response", al_responder)
        ok = self._ir(L["url"], ".tournament-matches-row")
        self.page.wait_for_timeout(1500)
        try:
            self.page.remove_listener("response", al_responder)
        except Exception:
            pass
        if not ok:
            return False
        _, filas = partidos_desde_html(self.page.content(), self.fecha)
        mejor = None
        for r in capt:
            try:
                data = r.json()
            except Exception:
                continue
            api = extraer_partidos_json(data)
            if len(api) < 3:
                continue
            res = comparar_fuentes(api, filas)
            if res["iguales"] >= 3 and res["iguales"] >= 0.8 * max(res["comparables"], 1):
                if mejor is None or res["iguales"] > mejor[1]["iguales"]:
                    mejor = (r.url, res)
        self.diag["respuestas_json"] = [r.url for r in capt][:30]
        if not mejor:
            return False
        url, res = mejor
        if L["id"] not in url:
            self.diag["api_sin_id"] = url
            return False
        self.patron_api = reemplazar_ultimo(url, L["id"], "{id}")
        self.codigos_fin, self.codigos_no_fin = res["fin"] - res["no_fin"], res["no_fin"]
        self.offset_min = res["offset"]
        self.diag.update({"patron_api": self.patron_api, "codigos_fin": sorted(self.codigos_fin),
                          "codigos_no_fin": sorted(self.codigos_no_fin), "offset_min": self.offset_min})
        self.panel.avisar("Encontré la API de partidos del sitio: lectura rápida activada.")
        return True

    # ---- partidos de una liga ----
    def partidos(self, L):
        if self.patron_api and not self.solo_html:
            data = self._json(self.patron_api.replace("{id}", L["id"]))
            if data is not None:
                lst = extraer_partidos_json(data)
                if lst:
                    return [self._normalizar(m, i) for i, m in enumerate(lst)], None
        if not L.get("url"):
            return None, None
        if not self._ir(L["url"], ".tournament-matches-row", espera=20000):
            return None, None
        nombre, lst = partidos_desde_html(self.page.content(), (L.get("dt") or AHORA()).date())
        return lst, nombre

    def _normalizar(self, m, i):
        dt = a_local(m["fecha_raw"], self.offset_min)
        st = m["estado"]
        sl = st.lower()
        ahora = AHORA()
        anulado = any(w in sl for w in PALABRAS_ANULADO)
        hay_goles = m["ga"] is not None and m["gb"] is not None
        if anulado:
            fin = False
        elif any(w in sl for w in PALABRAS_FIN):
            fin = hay_goles
        elif self.codigos_fin or self.codigos_no_fin:
            fin = hay_goles and st in self.codigos_fin
        else:
            fin = hay_goles and dt is not None and ahora > dt + timedelta(minutes=DURACION_PARTIDO_MIN)
        vivo = (not fin and not anulado and
                (any(w in sl for w in PALABRAS_VIVO) or st in getattr(self, "codigos_vivo", ()) or
                 (dt is not None and dt <= ahora < dt + timedelta(minutes=DURACION_PARTIDO_MIN + 10))))
        return {"idx": i, "a": m["a"], "b": m["b"], "eq_a": m["eq_a"], "eq_b": m["eq_b"], "hora": "",
                "dt": dt, "estado": st, "terminado": fin, "anulado": anulado, "en_vivo": vivo,
                "vivo": [m["ga"], m["gb"]] if (vivo and hay_goles) else None,
                "ga": m["ga"] if fin else None, "gb": m["gb"] if fin else None,
                "ca": m["ca"] if fin else None, "cb": m["cb"] if fin else None, "consola": m["consola"]}


def comparar_fuentes(api, filas):
    """Empareja partidos de la API con los del HTML para validar goles, estados y hora."""
    por_par = defaultdict(list)
    for f in filas:
        por_par[(f["a"], f["b"])].append(f)
    usados = defaultdict(int)
    iguales = comparables = 0
    fin, no_fin, difs = set(), set(), []
    for m in api:
        lst = por_par.get((m["a"], m["b"]))
        if not lst:
            continue
        f = lst[min(usados[(m["a"], m["b"])], len(lst) - 1)]
        usados[(m["a"], m["b"])] += 1
        (fin if f["terminado"] else no_fin).add(m["estado"])
        if f["terminado"]:
            comparables += 1
            iguales += (m["ga"], m["gb"]) == (f["ga"], f["gb"])
        dt = a_local(m["fecha_raw"])
        if dt and f.get("dt"):
            difs.append((f["dt"] - dt).total_seconds() / 60)
    offset = 0
    if difs:
        difs.sort()
        offset = int(round(difs[len(difs) // 2] / 15.0) * 15)
    return {"iguales": iguales, "comparables": comparables, "fin": fin, "no_fin": no_fin, "offset": offset}


class Vigia:
    """Hilo que revisa cada pocos segundos las ligas en juego y entrega los cambios al instante."""

    def __init__(self, ext):
        self.ext = ext
        self.cola = queue.Queue()
        self.lock = threading.Lock()
        self.ligas = []
        self.activo = True
        threading.Thread(target=self._bucle, daemon=True).start()

    def fijar(self, ligas):
        with self.lock:
            self.ligas = [{"id": L["id"]} for L in ligas]

    def _bucle(self):
        while self.activo:
            t0 = time.time()
            with self.lock:
                ligas = list(self.ligas)
            if ligas:
                try:
                    for i, data in self.ext._datos_ligas(ligas).items():
                        lst = extraer_partidos_json(data) if data else []
                        if lst:
                            self.cola.put((i, [self.ext._normalizar(m, k) for k, m in enumerate(lst)]))
                except Exception:
                    pass
            time.sleep(max(0.5, VIGIA_SEG - (time.time() - t0)))


class ExtractorHTTP(Extractor):
    """Versión sin navegador: usa directamente la API del sitio (la que encontró el diagnóstico).
    Consume muy poca memoria; es la que corre en el servidor en la nube."""

    def __init__(self, panel, fecha):
        super().__init__(panel, fecha)
        self.patron_api = URL_HOME + "api/tournaments/{id}/matches"
        self.codigos_fin, self.codigos_no_fin = {"3"}, {"1"}
        self.codigos_vivo = {"2"}
        self.http_ok = True
        self.aprendido = True
        self.diag = {"modo": "solo API (sin navegador)", "patron_api": self.patron_api}

    def abrir(self):
        if self.http.json(URL_HOME + "api/statuses") is None:
            self.panel.avisar("La API del sitio no respondió al iniciar; reintento en cada ciclo.")

    def cerrar(self):
        pass

    def aprender(self, ligas):
        pass

    def _json(self, url):
        return self.http.json(url)

    def _listar_html(self):
        """Respaldo: Schedule leído como HTML simple (todas sus páginas)."""
        out, vistos = [], set()
        for pagina in range(1, MAX_PAGINAS_SCHEDULE + 1):
            try:
                req = urllib.request.Request(f"{URL_SCHEDULE}?page={pagina}",
                                             headers={"User-Agent": self.http.headers["User-Agent"]})
                with urllib.request.urlopen(req, timeout=20) as r:
                    soup = BeautifulSoup(r.read().decode("utf-8", "replace"), "html.parser")
            except Exception:
                break
            nuevos = 0
            for fila in soup.select("li.tournaments-schedule-row"):
                a = fila.select_one(".tournaments-cell-details a.icon-link")
                tit = fila.select_one(".tournament-title-label")
                tid = id_de_href(a.get("href", "")) if a else None
                if not tid or tid in vistos:
                    continue
                vistos.add(tid)
                nuevos += 1
                dt, _ = leer_fecha_hora(fila.get_text(" ", strip=True), self.fecha)
                out.append({"id": tid, "nombre": tit.get_text(strip=True) if tit else tid,
                            "url": urljoin(URL_HOME, a["href"]), "dt": dt})
            if not nuevos:
                break
        return out

    def partidos(self, L):
        data = self._json(self.patron_api.replace("{id}", L["id"]))
        lst = extraer_partidos_json(data) if data else []
        if not lst:
            return None, None
        return [self._normalizar(m, i) for i, m in enumerate(lst)], None


class FuenteArchivos:
    """Backtest con páginas HTML guardadas: cada archivo es una liga."""

    def __init__(self, rutas, fecha):
        self.rutas, self.fecha = rutas, fecha
        self.diag = {}

    def abrir(self):
        pass

    def cerrar(self):
        pass

    def aprender(self, ligas):
        pass

    def listar(self):
        out = []
        for r in self.rutas:
            nombre, lst = partidos_desde_html(Path(r).read_text(encoding="utf-8"), self.fecha)
            dts = [p["dt"] for p in lst if p["dt"]]
            out.append({"id": f"{self.fecha:%Y%m%d}-{Path(r).stem}", "nombre": nombre or Path(r).stem, "url": str(r),
                        "dt": min(dts) if dts else None})
        return out

    def partidos(self, L):
        nombre, lst = partidos_desde_html(Path(L["url"]).read_text(encoding="utf-8"), self.fecha)
        return lst, nombre

    def partidos_varios(self, ligas, progreso=None):
        return {L["id"]: self.partidos(L) for L in ligas}

    def puede_vigilar(self):
        return False


# ================= ALMACÉN DEL DÍA =================
def asignar_claves(liga_id, lista):
    """Clave estable de cada partido: liga, jugadores y número de cruce (sirve con API o HTML)."""
    lista.sort(key=orden_crono)
    cuenta = defaultdict(int)
    for i, p in enumerate(lista):
        par = (p["a"], p["b"])
        p["key"] = f"{liga_id}|{p['a']}|{p['b']}|{cuenta[par]}"
        cuenta[par] += 1
        p["liga"] = liga_id
        p["idx"] = i
    return lista


class Almacen:
    """Todas las ligas, partidos y pronósticos verificados del día."""

    def __init__(self, fecha):
        self.fecha = fecha
        self.ligas = {}          # id -> liga
        self.partidos = {}       # key -> partido
        self.registros = {}      # key -> pronóstico verificado
        self._indice = None
        self._recs = None
        self.cambios = 0
        self.hist_ligas = {}     # ligas de días anteriores: id -> partidos
        self.hist_lista = []
        self.previos = []        # pronósticos verificados de días anteriores

    def cargar_historial(self, partidos, registros):
        self.hist_ligas = defaultdict(list)
        for p in partidos:
            if p["liga"] in self.ligas:
                continue
            p.update(terminado=True, anulado=False, en_vivo=False, vivo=None, estado="Finished")
            self.hist_ligas[p["liga"]].append(p)
        for lst in self.hist_ligas.values():
            lst.sort(key=orden_crono)
        self.hist_lista = [p for lst in self.hist_ligas.values() for p in lst]
        self.previos = sorted((r for r in registros if r["key"] not in self.registros),
                              key=lambda r: (r["dt"] or "", r["key"]))
        self._indice = None
        self._recs = None

    def partidos_liga(self, liga_id):
        if liga_id in self.ligas:
            return self.partidos_de(liga_id)
        return self.hist_ligas.get(liga_id, [])

    # ---- ligas ----
    def registrar_ligas(self, torneos):
        nuevas = 0
        for t in torneos:
            if TORNEO_BUSCADO and TORNEO_BUSCADO.lower() not in t["nombre"].lower():
                continue
            L = self.ligas.get(t["id"])
            if L is None:
                self.ligas[t["id"]] = L = {"id": t["id"], "nombre": t["nombre"], "dt": t.get("dt"),
                                           "url": t.get("url"), "estado": "próxima", "partidos": [],
                                           "firma": None, "ult_cambio": None, "consultada": False}
                nuevas += 1
            else:
                for k in ("url", "dt", "nombre"):
                    if t.get(k) and not L.get(k):
                        L[k] = t[k]
        self.numerar()
        return nuevas

    def numerar(self):
        for i, L in enumerate(self.ligas_ordenadas(), 1):
            L["num"] = i

    def ligas_ordenadas(self):
        return sorted(self.ligas.values(), key=lambda L: (L.get("dt") is None, L.get("dt") or datetime.max, L["id"]))

    def partidos_de(self, liga_id):
        return [self.partidos[k] for k in self.ligas[liga_id]["partidos"] if k in self.partidos]

    def actualizar(self, liga_id, lista, nombre=None):
        L = self.ligas[liga_id]
        L["consultada"] = True
        if nombre and (not L["nombre"] or L["nombre"] == liga_id):
            L["nombre"] = nombre
        lista = asignar_claves(liga_id, lista)
        firma = tuple((p["key"], p["terminado"], p["ga"], p["gb"], iso(p["dt"]), p["en_vivo"],
                       tuple(p["vivo"] or ()), p["anulado"]) for p in lista)
        if firma == L["firma"]:
            return False
        fin_antes = sum(1 for k in L["partidos"] if self.partidos.get(k, {}).get("terminado"))
        for k in L["partidos"]:
            self.partidos.pop(k, None)
        for p in lista:
            self.partidos[p["key"]] = p
        L["partidos"] = [p["key"] for p in lista]
        L["firma"] = firma
        L["ult_cambio"] = time.time()
        if lista and not L.get("dt"):
            dts = [p["dt"] for p in lista if p["dt"]]
            L["dt"] = min(dts) if dts else None
            self.numerar()
        validos = [p for p in lista if not p["anulado"]]
        if validos and all(p["terminado"] for p in validos):
            L["estado"] = "terminada"
        elif any(p["terminado"] or p["en_vivo"] for p in lista):
            L["estado"] = "en juego"
        if sum(1 for p in lista if p["terminado"]) != fin_antes:
            self._indice = None
        self.cambios += 1
        return True

    # ---- índices ----
    def indice(self, jugador):
        if self._indice is None:
            idx = defaultdict(list)
            for p in list(self.partidos.values()) + [h for h in self.hist_lista if h["key"] not in self.partidos]:
                if p["terminado"]:
                    idx[p["a"]].append(p)
                    idx[p["b"]].append(p)
            self._indice = {}
            for j, lst in idx.items():
                lst.sort(key=orden_crono)
                self._indice[j] = (lst, [p["dt"] or datetime.min for p in lst])
        return self._indice.get(jugador, ([], []))

    def agregar_registro(self, rec):
        self.registros[rec["key"]] = rec
        self._recs = None

    def registros_ordenados(self):
        if self._recs is None:
            self._recs = self.previos + sorted(self.registros.values(), key=lambda r: (r["dt"] or "", r["key"]))
            self._recs_dt = [r["dt"] or "" for r in self._recs]
        return self._recs

    def registros_hoy(self):
        return [r for r in self.registros_ordenados() if r["key"] in self.registros]

    def registros_antes(self, dt):
        recs = self.registros_ordenados()
        if dt is None:
            return recs
        return recs[:bisect.bisect_left(self._recs_dt, iso(dt))]


# ================= CONTEXTO "HASTA ESA HORA" =================
def _antes(p, m):
    if p.get("dt") and m.get("dt"):
        return (p["dt"], p["idx"]) < (m["dt"], m["idx"])
    return p["idx"] < m["idx"]


def contexto(alm, liga_id, objetivo=None):
    """Todo lo que se sabía justo antes de 'objetivo' (o ahora, si no hay objetivo)."""
    ps = sorted(alm.partidos_liga(liga_id), key=orden_crono)
    if objetivo is not None:
        corte = objetivo["dt"]
        conocidos = [p for p in ps if p["terminado"] and p is not objetivo and _antes(p, objetivo)]
    else:
        corte = AHORA()
        conocidos = [p for p in ps if p["terminado"]]
    ids_con = {p["key"] for p in conocidos}
    jugadores = list(OrderedDict.fromkeys([p["a"] for p in ps] + [p["b"] for p in ps]))
    equipo = {}
    for p in ps:
        equipo.setdefault(p["a"], p["eq_a"])
        equipo.setdefault(p["b"], p["eq_b"])
    pendientes = [p for p in ps if not p["anulado"] and p["key"] not in ids_con
                  and (objetivo is not None or not p["terminado"])]
    existentes = {(p["a"], p["b"]) for p in ps}
    for a in jugadores:                       # cruces que la página todavía no muestra
        for b in jugadores:
            if a != b and (a, b) not in existentes:
                pendientes.append({"key": f"{liga_id}|{a}|{b}|x", "a": a, "b": b, "eq_a": equipo[a],
                                   "eq_b": equipo[b], "dt": None, "idx": 999, "terminado": False,
                                   "anulado": False, "sintetico": True})

    # historia de otras ligas: solo partidos ya terminados antes del corte
    limite = (corte - timedelta(minutes=DURACION_PARTIDO_MIN)) if corte else None
    vistos, hist = set(), []
    for j in jugadores:
        lst, dts = alm.indice(j)
        hi = bisect.bisect_right(dts, limite) if limite else len(lst)
        for p in lst[max(0, hi - MAX_HIST_JUGADOR * 2):hi]:
            if p["liga"] == liga_id or p["key"] in vistos:
                continue
            vistos.add(p["key"])
            hist.append(p)
    obs = []
    for p in sorted(hist, key=orden_crono):
        horas = (corte - p["dt"]).total_seconds() / 3600 if (corte and p["dt"]) else 0.0
        fs = [1.0 if eq == equipo[j] else F_OTRO_EQUIPO
              for j, eq in ((p["a"], p["eq_a"]), (p["b"], p["eq_b"])) if j in equipo]
        w = PESO_OTRA_LIGA * 0.5 ** (max(horas, 0) / VIDA_MEDIA_HORAS) * sum(fs) / len(fs)
        if w < 0.02:
            continue
        obs.append({"a": p["a"], "b": p["b"], "ga": p["ga"], "gb": p["gb"], "eq_a": p["eq_a"],
                    "eq_b": p["eq_b"], "w": w, "h": True})
    obs += [{"a": p["a"], "b": p["b"], "ga": p["ga"], "gb": p["gb"], "eq_a": p["eq_a"], "eq_b": p["eq_b"],
             "w": 1.0, "h": False} for p in conocidos]
    eq_prev = defaultdict(set)
    hist_cnt = defaultdict(int)
    for o in obs:
        if o["h"]:
            eq_prev[o["a"]].add(o["eq_a"])
            eq_prev[o["b"]].add(o["eq_b"])
            hist_cnt[o["a"]] += 1
            hist_cnt[o["b"]] += 1
    jug_modelo = list(OrderedDict.fromkeys(jugadores + [o["a"] for o in obs] + [o["b"] for o in obs]))
    adj = {j: [] for j in jug_modelo}
    for o in obs:
        adj[o["a"]].append((o["b"], o["ga"], o["gb"], o["w"]))
        adj[o["b"]].append((o["a"], o["gb"], o["ga"], o["w"]))
    sw = sum(o["w"] for o in obs)
    mu = max(sum(o["w"] * (o["ga"] + o["gb"]) for o in obs) / (2 * sw), 0.5) if sw > 0 else 2.5
    gf, gc, pj = defaultdict(float), defaultdict(float), defaultdict(float)
    for o in obs:
        gf[o["a"]] += o["w"] * o["ga"]
        gc[o["a"]] += o["w"] * o["gb"]
        pj[o["a"]] += o["w"]
        gf[o["b"]] += o["w"] * o["gb"]
        gc[o["b"]] += o["w"] * o["ga"]
        pj[o["b"]] += o["w"]
    atq = {j: ((gf[j] + PRIOR * mu) / (pj[j] + PRIOR)) / mu for j in jug_modelo}
    dfn = {j: ((gc[j] + PRIOR * mu) / (pj[j] + PRIOR)) / mu for j in jug_modelo}
    tabla = tabla_vacia(jugadores)
    for p in conocidos:
        aplicar(tabla, p["a"], p["b"], p["ga"], p["gb"])
    return {"liga": liga_id, "jugadores": jugadores, "equipo": equipo, "conocidos": conocidos,
            "pendientes": pendientes, "obs": obs, "jug_modelo": jug_modelo, "adj": adj, "mu": mu,
            "atq": atq, "dfn": dfn, "tabla": tabla, "hist_cnt": hist_cnt, "eq_prev": eq_prev,
            "n_hist": sum(1 for o in obs if o["h"])}


# ================= TABLA =================
def tabla_vacia(jugadores):
    return {j: {"PJ": 0, "G": 0, "E": 0, "P": 0, "GF": 0, "GC": 0, "Pts": 0} for j in jugadores}


def aplicar(tabla, a, b, ga, gb):
    pa, pb = (3, 0) if ga > gb else (1, 1) if ga == gb else (0, 3)
    for j, f, c, pts in ((a, ga, gb, pa), (b, gb, ga, pb)):
        t = tabla[j]
        t["PJ"] += 1
        t["GF"] += f
        t["GC"] += c
        t["Pts"] += pts
        t["G" if pts == 3 else "E" if pts == 1 else "P"] += 1


def ordenar(tabla):
    return sorted(tabla, key=lambda j: (tabla[j]["Pts"], tabla[j]["GF"] - tabla[j]["GC"], tabla[j]["GF"]),
                  reverse=True)


# ================= PROBABILIDAD =================
def pmf(lam):
    p = [math.exp(-lam)]
    for k in range(1, MAX_GOLES + 1):
        p.append(p[-1] * lam / k)
    return p


def pmf_nb(lam, r):
    out = [(r / (r + lam)) ** r]
    q = lam / (r + lam)
    for k in range(1, MAX_GOLES + 1):
        out.append(out[-1] * (k - 1 + r) / k * q)
    return out


def probs_desde_pmf(fa, fb):
    gana = empata = acum = 0.0
    for i, x in enumerate(fa):
        gana += x * acum
        empata += x * fb[i]
        acum += fb[i]
    tot = sum(fa) * sum(fb)
    gana, empata = gana / tot, empata / tot
    return gana, empata, max(0.0, 1 - gana - empata)


def armar(la, lb, probs=None, r=None):
    la, lb = max(la, 0.05), max(lb, 0.05)
    fa, fb = (pmf_nb(la, r), pmf_nb(lb, r)) if r else (pmf(la), pmf(lb))
    if probs is None:
        probs = probs_desde_pmf(fa, fb)
    return {"la": la, "lb": lb, "pa": probs[0], "pe": probs[1], "pb": probs[2], "fa": fa, "fb": fb}


def escala_goles(obs):
    """Tasa de empates y cuántos goles de diferencia hay entre favorito y no favorito."""
    sw = sum(o["w"] for o in obs)
    emp = sum(o["w"] for o in obs if o["ga"] == o["gb"])
    dif = sum(o["w"] * abs(o["ga"] - o["gb"]) for o in obs)
    return min(0.45, (emp + 1) / (sw + 4)), 2.0 * (dif + 1.5) / (sw + 1)


def desde_probs(pa, pe, pb, mu, k):
    g = (pa - pb) * k
    return armar(max(0.3, mu + g / 2), max(0.3, mu - g / 2), probs=(pa, pe, pb))


def desde_we(we, mu, dr, k):
    we = min(max(we, 0.02), 0.98)
    pe = dr * 4 * we * (1 - we)
    return desde_probs(we - pe / 2, pe, 1 - we - pe / 2, mu, k)


def resultado_de(ga, gb):
    return "A" if ga > gb else "E" if ga == gb else "B"


def sigm(z):
    if z < -35:
        return 0.0
    if z > 35:
        return 1.0
    return 1 / (1 + math.exp(-z))


def ajustar_logit(feats, iters=80):
    """Logit ordenado (B gana < empate < A gana) sobre una sola variable x.
    feats = [(x, y, w)] con y en {0: gana B, 1: empate, 2: gana A}."""
    n = sum(w for _, _, w in feats)
    if n < 3:
        return None
    if _np is not None:
        return _logit_np(feats, iters)
    mx = sum(w * x for x, _, w in feats) / n
    sx = math.sqrt(sum(w * (x - mx) ** 2 for x, _, w in feats) / n) or 1.0
    pb = (sum(w for _, y, w in feats if y == 0) + 1) / (n + 3)
    pbe = (sum(w for _, y, w in feats if y <= 1) + 2) / (n + 3)
    t1 = math.log(pb / (1 - pb))
    d = math.log(max(math.log(pbe / (1 - pbe)) - t1, 0.05))
    b = 1.0
    lam = 1.0                                   # prior suave (en partidos)
    for _ in range(iters):
        gb_ = gt = gd = 0.0
        ed = math.exp(d)
        for x, y, w in feats:
            x /= sx
            s1, s2 = sigm(t1 - b * x), sigm(t1 + ed - b * x)
            if y == 0:
                g1, g2 = 1 - s1, 0.0
            elif y == 2:
                g1, g2 = 0.0, -s2
            else:
                p = max(s2 - s1, 1e-9)
                g1, g2 = -s1 * (1 - s1) / p, s2 * (1 - s2) / p
            gt += w * (g1 + g2)
            gd += w * g2 * ed
            gb_ += w * -x * (g1 + g2)
        gb_ -= lam * (b - 1.0)
        paso = 1.5 / (n + lam)
        b += paso * gb_
        t1 += paso * gt
        d += paso * gd
    return b / sx, t1, t1 + math.exp(d)


try:
    import numpy as _np
except ImportError:
    _np = None


def _logit_np(feats, iters=80):
    """Mismo logit ordenado, vectorizado con numpy (unas 20 veces más rápido)."""
    np = _np
    X = np.array([f[0] for f in feats], dtype=float)
    Y = np.array([f[1] for f in feats])
    W = np.array([f[2] for f in feats], dtype=float)
    n = W.sum()
    mx = (W * X).sum() / n
    sx = math.sqrt((W * (X - mx) ** 2).sum() / n) or 1.0
    X = X / sx
    pb = (W[Y == 0].sum() + 1) / (n + 3)
    pbe = (W[Y <= 1].sum() + 2) / (n + 3)
    t1 = math.log(pb / (1 - pb))
    d = math.log(max(math.log(pbe / (1 - pbe)) - t1, 0.05))
    b, lam = 1.0, 1.0
    e0, e2 = Y == 0, Y == 2
    for _ in range(iters):
        ed = math.exp(d)
        s1 = 1 / (1 + np.exp(-np.clip(t1 - b * X, -35, 35)))
        s2 = 1 / (1 + np.exp(-np.clip(t1 + ed - b * X, -35, 35)))
        p = np.maximum(s2 - s1, 1e-9)
        g1 = np.where(e0, 1 - s1, np.where(e2, 0.0, -s1 * (1 - s1) / p))
        g2 = np.where(e0, 0.0, np.where(e2, -s2, s2 * (1 - s2) / p))
        gt = (W * (g1 + g2)).sum()
        gd = (W * g2).sum() * ed
        gb_ = (W * -X * (g1 + g2)).sum() - lam * (b - 1.0)
        paso = 1.5 / (n + lam)
        b += paso * gb_
        t1 += paso * gt
        d += paso * gd
    return b / sx, t1, t1 + math.exp(d)


def probs_logit(par, x):
    b, t1, t2 = par
    s1, s2 = sigm(t1 - b * x), sigm(t2 - b * x)
    return 1 - s2, max(s2 - s1, 0.0), s1


def y_de(o):
    return 2 if o["ga"] > o["gb"] else 1 if o["ga"] == o["gb"] else 0


# ================= MODELOS =================
def m_poisson(ctx):
    mu, atq, dfn = ctx["mu"], ctx["atq"], ctx["dfn"]
    return lambda a, b: armar(mu * atq[a] * dfn[b], mu * atq[b] * dfn[a])


def maher(ctx, k=1.0, iters=30):
    if "_maher" in ctx:
        return ctx["_maher"]
    jug, mu, adj = ctx["jug_modelo"], ctx["mu"], ctx["adj"]
    atq = {j: 1.0 for j in jug}
    dfn = {j: 1.0 for j in jug}
    for _ in range(iters):
        for j in jug:
            f = e = 0.0
            for r, gf, gc, w in adj[j]:
                f += w * gf
                e += w * mu * dfn[r]
            atq[j] = (f + k) / (e + k)
        for j in jug:
            c = e = 0.0
            for r, gf, gc, w in adj[j]:
                c += w * gc
                e += w * mu * atq[r]
            dfn[j] = (c + k) / (e + k)
        ma, md = sum(atq.values()) / len(atq), sum(dfn.values()) / len(dfn)
        for j in jug:
            atq[j] /= ma
            dfn[j] /= md
    ctx["_maher"] = (atq, dfn)
    return atq, dfn


def m_maher(ctx):
    atq, dfn = maher(ctx)
    mu = ctx["mu"]
    return lambda a, b: armar(mu * atq[a] * dfn[b], mu * atq[b] * dfn[a])


def tau(i, j, la, lb, rho):
    if i == 0 and j == 0:
        t = 1 - la * lb * rho
    elif i == 0 and j == 1:
        t = 1 + la * rho
    elif i == 1 and j == 0:
        t = 1 + lb * rho
    elif i == 1 and j == 1:
        t = 1 - rho
    else:
        t = 1.0
    return max(t, 0.01)


def m_dixon_coles(ctx):
    atq, dfn = maher(ctx)
    mu = ctx["mu"]

    def lam(a, b):
        return mu * atq[a] * dfn[b], mu * atq[b] * dfn[a]

    mejor, rho = -1e18, 0.0
    for rc in (0.0, -0.03, -0.06, -0.1, -0.15, 0.03, 0.06):
        s = 0.0
        for o in ctx["obs"]:
            if o["ga"] <= 1 and o["gb"] <= 1:
                la, lb = lam(o["a"], o["b"])
                s += o["w"] * math.log(tau(o["ga"], o["gb"], la, lb, rc))
        if s > mejor:
            mejor, rho = s, rc

    def pred(a, b):
        la, lb = lam(a, b)
        fa, fb = pmf(la), pmf(lb)
        gana = emp = tot = 0.0
        for i in range(21):
            for j in range(21):
                q = fa[i] * fb[j] * (tau(i, j, la, lb, rho) if i < 2 and j < 2 else 1.0)
                tot += q
                if i > j:
                    gana += q
                elif i == j:
                    emp += q
        return armar(la, lb, probs=(gana / tot, emp / tot, max(0.0, 1 - (gana + emp) / tot)))
    return pred


def m_bivariada(ctx):
    """Poisson bivariado (Karlis y Ntzoufras): los goles de ambos pueden ir correlacionados."""
    atq, dfn = maher(ctx)
    mu = ctx["mu"]

    def marg(a, b):
        return mu * atq[a] * dfn[b], mu * atq[b] * dfn[a]

    def logp(x, y, l1, l2, l3):
        base = -(l1 + l2 + l3) + x * math.log(l1) - math.lgamma(x + 1) + y * math.log(l2) - math.lgamma(y + 1)
        if l3 <= 0:
            return base
        r, term, tot = l3 / (l1 * l2), 1.0, 1.0
        for k in range(1, min(x, y) + 1):
            term *= (x - k + 1) * (y - k + 1) / k * r
            tot += term
        return base + math.log(tot)

    mejor, c = -1e18, 0.0
    for cc in (0.0, 0.05, 0.1, 0.2, 0.3):
        s = 0.0
        for o in ctx["obs"]:
            ma, mb = marg(o["a"], o["b"])
            l3 = cc * min(ma, mb)
            s += o["w"] * logp(o["ga"], o["gb"], ma - l3, mb - l3, l3)
        if s > mejor:
            mejor, c = s, cc

    def pred(a, b):
        ma, mb = marg(a, b)
        l3 = c * min(ma, mb)
        l1, l2 = max(ma - l3, 0.02), max(mb - l3, 0.02)
        gana = emp = tot = 0.0
        for i in range(17):
            for j in range(17):
                q = math.exp(logp(i, j, l1, l2, l3))
                tot += q
                if i > j:
                    gana += q
                elif i == j:
                    emp += q
        return armar(ma, mb, probs=(gana / tot, emp / tot, max(0.0, 1 - (gana + emp) / tot)))
    return pred


def m_binomial_negativa(ctx):
    mu, atq, dfn, obs = ctx["mu"], ctx["atq"], ctx["dfn"], ctx["obs"]
    r = 200.0
    sw = 2 * sum(o["w"] for o in obs)
    if len(obs) >= 2 and sw >= 4:
        m = sum(o["w"] * (o["ga"] + o["gb"]) for o in obs) / sw
        v = sum(o["w"] * ((o["ga"] - m) ** 2 + (o["gb"] - m) ** 2) for o in obs) / max(sw - 1, 1)
        if v > m * 1.05:
            r = m * m / (v - m)
    r = min(max(r, 3.0), 200.0)
    return lambda a, b: armar(mu * atq[a] * dfn[b], mu * atq[b] * dfn[a], r=r)


def m_jugador_equipo(ctx, iters=25):
    """Poisson con fuerza del jugador y del equipo que eligió (el mismo jugador rinde distinto
    según el equipo)."""
    obs, mu = ctx["obs"], ctx["mu"]
    jug = ctx["jug_modelo"]
    eqs = sorted({o["eq_a"] for o in obs} | {o["eq_b"] for o in obs} | set(ctx["equipo"].values()))
    ap, dp = {j: 1.0 for j in jug}, {j: 1.0 for j in jug}
    at, dt = {e: 1.0 for e in eqs}, {e: 1.0 for e in eqs}
    kj, ke = 1.0, 3.0
    filas = []
    for o in obs:
        filas.append((o["a"], o["eq_a"], o["b"], o["eq_b"], o["ga"], o["w"]))
        filas.append((o["b"], o["eq_b"], o["a"], o["eq_a"], o["gb"], o["w"]))
    for _ in range(iters):
        for tabla_f, k, sel in ((ap, kj, 0), (at, ke, 1), (dp, kj, 2), (dt, ke, 3)):
            num, den = defaultdict(float), defaultdict(float)
            for j, e, r, er, g, w in filas:
                ex = mu * ap[j] * at[e] * dp[r] * dt[er]
                clave = (j, e, r, er)[sel]
                num[clave] += w * g
                den[clave] += w * ex / tabla_f[clave]
            for clave in tabla_f:
                tabla_f[clave] = (num[clave] + k) / (den[clave] + k)
            m = sum(tabla_f.values()) / len(tabla_f)
            for clave in tabla_f:
                tabla_f[clave] /= m
    eq = ctx["equipo"]

    def pred(a, b):
        ea, eb = eq.get(a, ""), eq.get(b, "")
        return armar(mu * ap[a] * at.get(ea, 1) * dp[b] * dt.get(eb, 1),
                     mu * ap[b] * at.get(eb, 1) * dp[a] * dt.get(ea, 1))
    return pred


def m_elo_logit(ctx):
    """Elo con peso por diferencia de goles + logit ordenado (Hvattum y Arntzen)."""
    rating = defaultdict(lambda: 1500.0)
    feats = []
    for o in ctx["obs"]:
        a, b = o["a"], o["b"]
        x = (rating[a] - rating[b]) / 100
        feats.append((x, y_de(o), o["w"]))
        we = 1 / (1 + 10 ** (-x / 4))
        s = 1.0 if o["ga"] > o["gb"] else 0.5 if o["ga"] == o["gb"] else 0.0
        d = 40 * o["w"] * (1 + math.log(1 + abs(o["ga"] - o["gb"]))) * (s - we)
        rating[a] += d
        rating[b] -= d
    par = ajustar_logit(feats)
    dr, k = escala_goles(ctx["obs"])
    mu = ctx["mu"]

    def pred(a, b):
        x = (rating[a] - rating[b]) / 100
        if par:
            return desde_probs(*probs_logit(par, x), mu, k)
        return desde_we(1 / (1 + 10 ** (-x / 4)), mu, dr, k)
    return pred


def m_pi_ratings(ctx, c=3.0, lam=0.05):
    """Pi-ratings (Constantinou y Fenton): ratings en escala de diferencia de goles."""
    R = defaultdict(float)

    def gd(r):
        return math.copysign(10 ** (abs(r) / c) - 1, r)

    feats = []
    for o in ctx["obs"]:
        a, b = o["a"], o["b"]
        esp = gd(R[a]) - gd(R[b])
        feats.append((esp, y_de(o), o["w"]))
        real = o["ga"] - o["gb"]
        psi = c * math.log10(1 + abs(real - esp))
        s = 1 if real > esp else -1
        R[a] += s * psi * lam * o["w"]
        R[b] -= s * psi * lam * o["w"]
    par = ajustar_logit(feats)
    dr, k = escala_goles(ctx["obs"])
    mu = ctx["mu"]

    def pred(a, b):
        x = gd(R[a]) - gd(R[b])
        la, lb = max(0.3, mu + x / 2), max(0.3, mu - x / 2)
        if par:
            return armar(la, lb, probs=probs_logit(par, x))
        return armar(la, lb)
    return pred


def _volatilidad(sig, phi, v, delta, tau_=0.5):
    a = math.log(sig ** 2)

    def f(x):
        ex = math.exp(x)
        return ex * (delta ** 2 - phi ** 2 - v - ex) / (2 * (phi ** 2 + v + ex) ** 2) - (x - a) / tau_ ** 2

    A = a
    if delta ** 2 > phi ** 2 + v:
        B = math.log(delta ** 2 - phi ** 2 - v)
    else:
        k = 1
        while f(a - k * tau_) < 0 and k < 50:
            k += 1
        B = a - k * tau_
    fA, fB = f(A), f(B)
    for _ in range(40):
        if abs(B - A) <= 1e-6 or fB == fA:
            break
        C = A + (A - B) * fA / (fB - fA)
        fC = f(C)
        if fC * fB <= 0:
            A, fA = B, fB
        else:
            fA /= 2
        B, fB = C, fC
    return math.exp(A / 2)


def m_glicko2(ctx):
    """Glicko-2 (Glickman): rating con incertidumbre; el desconocido se mueve más rápido."""
    st = defaultdict(lambda: [0.0, 350 / 173.7178, 0.06])

    def g(phi):
        return 1 / math.sqrt(1 + 3 * phi * phi / math.pi ** 2)

    feats = []
    for o in ctx["obs"]:
        a, b, w = o["a"], o["b"], o["w"]
        (ma, pa_, sa), (mb, pb_, sb) = list(st[a]), list(st[b])
        feats.append((g(math.sqrt(pa_ ** 2 + pb_ ** 2)) * (ma - mb), y_de(o), w))
        s = 1.0 if o["ga"] > o["gb"] else 0.5 if o["ga"] == o["gb"] else 0.0
        for j, (m, ph, sg), (mo, pho), sj in ((a, (ma, pa_, sa), (mb, pb_), s), (b, (mb, pb_, sb), (ma, pa_), 1 - s)):
            gg = g(pho)
            e = 1 / (1 + math.exp(-gg * (m - mo)))
            v = 1 / max(w * gg * gg * e * (1 - e), 1e-9)
            delta = v * w * gg * (sj - e)
            sg2 = _volatilidad(sg, ph, v, delta)
            phs = math.sqrt(ph * ph + sg2 * sg2)
            ph2 = 1 / math.sqrt(1 / phs ** 2 + 1 / v)
            st[j] = [m + ph2 * ph2 * w * gg * (sj - e), ph2, sg2]
    par = ajustar_logit(feats)
    dr, k = escala_goles(ctx["obs"])
    mu = ctx["mu"]

    def pred(a, b):
        (ma, pa_, _), (mb, pb_, _) = st[a], st[b]
        x = g(math.sqrt(pa_ ** 2 + pb_ ** 2)) * (ma - mb)
        if par:
            return desde_probs(*probs_logit(par, x), mu, k)
        return desde_we(1 / (1 + math.exp(-x)), mu, dr, k)
    return pred


def m_bradley_terry(ctx):
    jug, adj, mu = ctx["jug_modelo"], ctx["adj"], ctx["mu"]
    w = {j: 1.0 for j in jug}
    for j in jug:
        for r, f, c, wt in adj[j]:
            w[j] += wt * (1.0 if f > c else 0.5 if f == c else 0.0)
    pi = {j: 1.0 for j in jug}
    for _ in range(60):
        nuevo = {}
        for j in jug:
            den = 2 / (pi[j] + 1)
            for r, f, c, wt in adj[j]:
                den += wt / (pi[j] + pi[r])
            nuevo[j] = w[j] / den
        gm = math.exp(sum(math.log(v) for v in nuevo.values()) / len(nuevo))
        cambio = max(abs(nuevo[j] / gm - pi[j]) for j in jug)
        pi = {j: v / gm for j, v in nuevo.items()}
        if cambio < 1e-5:
            break
    dr, k = escala_goles(ctx["obs"])
    return lambda a, b: desde_we(pi[a] / (pi[a] + pi[b]), mu, dr, k)


def m_massey(ctx):
    jug, adj, mu = ctx["jug_modelo"], ctx["adj"], ctx["mu"]
    rt = {j: 0.0 for j in jug}
    for _ in range(120):
        cambio = 0.0
        for j in jug:
            s = n = 0.0
            for r, f, c, wt in adj[j]:
                s += wt * ((f - c) + rt[r])
                n += wt
            nuevo = s / (n + 1.0)
            cambio = max(cambio, abs(nuevo - rt[j]))
            rt[j] = nuevo
        if cambio < 1e-4:
            break

    def pred(a, b):
        d = rt[a] - rt[b]
        return armar(max(0.3, mu + d / 2), max(0.3, mu - d / 2))
    return pred


PROMEDIO = "Promedio simple"
ENSAMBLE = "Ensamble bayesiano"
MODELOS = OrderedDict([
    ("Poisson suavizado", m_poisson),
    ("Poisson Maher", m_maher),
    ("Dixon-Coles", m_dixon_coles),
    ("Poisson bivariado", m_bivariada),
    ("Binomial negativa", m_binomial_negativa),
    ("Jugador + equipo", m_jugador_equipo),
    ("Elo + logit ordenado", m_elo_logit),
    ("Pi-ratings", m_pi_ratings),
    ("Glicko-2", m_glicko2),
    ("Bradley-Terry", m_bradley_terry),
    ("Massey", m_massey),
])
CALIBRADO = "Ensamble calibrado"
META = "Meta-modelo (stacking)"
TODOS = list(MODELOS) + [PROMEDIO, ENSAMBLE, CALIBRADO, META]
NOMBRES_RASGOS = ["log(local/visita)", "log(empate)", "dif. goles esperados", "goles esperados",
                  "forma reciente", "cara a cara", "partidos cara a cara", "dif. historial", "historial mínimo",
                  "dif. puntos por partido en la liga", "mismo equipo de siempre", "desacuerdo entre modelos"]


def rasgos(ctx, a, b, r_ens, rs_base):
    """Variables para el meta-modelo: lo que dicen los modelos + forma, cara a cara, historial y liga."""
    obs = ctx["obs"]

    def forma(j):
        pts = []
        for o in reversed(obs):
            if o["a"] == j:
                pts.append(3 if o["ga"] > o["gb"] else 1 if o["ga"] == o["gb"] else 0)
            elif o["b"] == j:
                pts.append(3 if o["gb"] > o["ga"] else 1 if o["ga"] == o["gb"] else 0)
            if len(pts) >= 6:
                break
        return sum(pts) / len(pts) if pts else 1.35

    s_h = n_h = 0.0
    for o in obs:
        if o["a"] == a and o["b"] == b:
            s_h += o["w"] * (o["ga"] - o["gb"])
            n_h += o["w"]
        elif o["a"] == b and o["b"] == a:
            s_h += o["w"] * (o["gb"] - o["ga"])
            n_h += o["w"]
    t = ctx["tabla"]

    def ppg(j):
        return t[j]["Pts"] / t[j]["PJ"] if j in t and t[j]["PJ"] else 1.35
    hc = ctx["hist_cnt"]
    mismo = lambda j: 1.0 if ctx["equipo"].get(j) in ctx["eq_prev"].get(j, set()) else 0.0
    pas = [x["pa"] - x["pb"] for x in rs_base] or [0.0]
    mpas = sum(pas) / len(pas)
    disp = math.sqrt(sum((x - mpas) ** 2 for x in pas) / len(pas))
    pa, pe, pb = max(r_ens["pa"], 1e-4), max(r_ens["pe"], 1e-4), max(r_ens["pb"], 1e-4)
    v = [math.log(pa / pb), math.log(pe), r_ens["la"] - r_ens["lb"], r_ens["la"] + r_ens["lb"],
         forma(a) - forma(b), s_h / n_h if n_h else 0.0, math.log1p(n_h),
         math.log1p(hc.get(a, 0)) - math.log1p(hc.get(b, 0)), math.log1p(min(hc.get(a, 0), hc.get(b, 0))),
         ppg(a) - ppg(b), mismo(a) - mismo(b), disp]
    return [round(x, 4) for x in v]


class MetaModelo:
    """Regresión logística multinomial (stacking) entrenada con los pronósticos ya verificados.
    Aprende cuándo cada señal (modelos, forma, cara a cara, historial) acierta de verdad."""

    def __init__(self):
        self.W = self.mu = self.sd = None
        self.info = {}

    @property
    def ok(self):
        return self.W is not None

    def _datos(self, recs):
        return [(r["f"], {"A": 0, "E": 1, "B": 2}[r["salida"]], r["m"][ENSAMBLE][:3])
                for r in recs if r.get("f") and len(r["f"]) == len(NOMBRES_RASGOS) and ENSAMBLE in r["m"]]

    def _ajustar(self, datos, iters=300, lam=1e-3):
        d = len(datos[0][0])
        try:
            import numpy as np
            X = np.array([x for x, _, _ in datos], dtype=float)
            y = np.array([c for _, c, _ in datos])
            mu, sd = X.mean(0), X.std(0) + 1e-6
            Xs = np.hstack([(X - mu) / sd, np.ones((len(X), 1))])
            Y = np.eye(3)[y]
            W = np.zeros((d + 1, 3))
            for _ in range(iters):
                Z = Xs @ W
                Z -= Z.max(1, keepdims=True)
                P = np.exp(Z)
                P /= P.sum(1, keepdims=True)
                W -= 0.5 * (Xs.T @ (P - Y) / len(Xs) + lam * W)
            return W.tolist(), mu.tolist(), sd.tolist()
        except ImportError:
            datos = datos[-3000:]
            n = len(datos)
            mu = [sum(x[i] for x, _, _ in datos) / n for i in range(d)]
            sd = [math.sqrt(sum((x[i] - mu[i]) ** 2 for x, _, _ in datos) / n) + 1e-6 for i in range(d)]
            Xs = [[(x[i] - mu[i]) / sd[i] for i in range(d)] + [1.0] for x, _, _ in datos]
            W = [[0.0] * 3 for _ in range(d + 1)]
            for _ in range(150):
                G = [[0.0] * 3 for _ in range(d + 1)]
                for xr, (_, c, _) in zip(Xs, datos):
                    z = [sum(xr[i] * W[i][k] for i in range(d + 1)) for k in range(3)]
                    m = max(z)
                    e = [math.exp(v - m) for v in z]
                    t = sum(e)
                    for k in range(3):
                        g = e[k] / t - (1 if k == c else 0)
                        for i in range(d + 1):
                            G[i][k] += xr[i] * g
                for i in range(d + 1):
                    for k in range(3):
                        W[i][k] -= 0.5 * (G[i][k] / n + lam * W[i][k])
            return W, mu, sd

    def prob(self, f, W=None, mu=None, sd=None):
        W, mu, sd = W or self.W, mu or self.mu, sd or self.sd
        x = [(f[i] - mu[i]) / sd[i] for i in range(len(f))] + [1.0]
        z = [sum(x[i] * W[i][k] for i in range(len(x))) for k in range(3)]
        m = max(z)
        e = [math.exp(v - m) for v in z]
        t = sum(e)
        return tuple(v / t for v in e)

    def entrenar(self, recs):
        datos = self._datos(recs)[-30000:]
        if len(datos) < 400:
            self.info = {"estado": f"esperando datos ({len(datos)} de 400 pronósticos verificados)"}
            return False
        corte = int(len(datos) * 0.8)
        W, mu, sd = self._ajustar(datos[:corte])
        ll_m = ll_e = 0.0
        for f, c, pe in datos[corte:]:
            ll_m -= math.log(max(self.prob(f, W, mu, sd)[c], 1e-9))
            ll_e -= math.log(max(pe[c], 1e-9))
        n = len(datos) - corte
        self.W, self.mu, self.sd = self._ajustar(datos)
        self.info = {"estado": "activo", "entrenado_con": len(datos), "logloss_meta": round(ll_m / n, 4),
                     "logloss_ensamble": round(ll_e / n, 4), "mejora": round((ll_e - ll_m) / n, 4)}
        return True


MERCADOS = (("1", "Gana {a}"), ("X", "Empate"), ("2", "Gana {b}"), ("1X", "{a} o empate"), ("X2", "{b} o empate"),
            ("12", "No hay empate"), ("O", "Más de {l} goles"), ("U", "Menos de {l} goles"),
            ("BTTS", "Ambos marcan"), ("NBTTS", "No marcan ambos"))


def opciones_mercado(p, mk):
    pa, pe, pb = p["pa"], p["pe"], p["pb"]
    v = {"1": pa, "X": pe, "2": pb, "1X": pa + pe, "X2": pe + pb, "12": pa + pb}
    if mk:
        v.update({"O": mk["over"], "U": 1 - mk["over"], "BTTS": mk["btts"], "NBTTS": 1 - mk["btts"]})
    return v


def mejor_mercado(p, mk, a, b, excluir=("12",)):
    """Mercado con mayor probabilidad (se omite 'no hay empate' por ser casi siempre trivial)."""
    v = {k: x for k, x in opciones_mercado(p, mk).items() if k not in excluir}
    k = max(v, key=v.get)
    texto = dict(MERCADOS)[k].format(a=a, b=b, l=mk["linea"] if mk else "")
    return {"cod": k, "texto": texto, "p": round(v[k], 4)}


def cumple(cod, ga, gb, linea):
    return {"1": ga > gb, "X": ga == gb, "2": ga < gb, "1X": ga >= gb, "X2": ga <= gb, "12": ga != gb,
            "O": ga + gb > linea, "U": ga + gb < linea, "BTTS": ga > 0 and gb > 0,
            "NBTTS": not (ga > 0 and gb > 0)}[cod]


def temperado(probs, T):
    ps = [max(p, 1e-9) ** (1 / T) for p in probs]
    s = sum(ps)
    return tuple(p / s for p in ps)


def memo(f):
    cache = {}

    def g(a, b):
        if (a, b) not in cache:
            cache[(a, b)] = f(a, b)
        return cache[(a, b)]
    return g


def combinar(preds, pesos):
    def pred(a, b):
        rs, ws = [], []
        for n, f in preds.items():
            try:
                rs.append(f(a, b))
                ws.append(pesos.get(n, 0.0) if pesos else 1.0)
            except Exception:
                pass
        tot = sum(ws) or 1.0
        ws = [w / tot for w in ws]
        la = sum(w * r["la"] for w, r in zip(ws, rs))
        lb = sum(w * r["lb"] for w, r in zip(ws, rs))
        probs = tuple(sum(w * r[k] for w, r in zip(ws, rs)) for k in ("pa", "pe", "pb"))
        return armar(la, lb, probs=probs)
    return pred


def construir_predictores(ctx, pesos=None, solo=None, temp=1.0, meta=None):
    base = OrderedDict()
    combinados = (None, PROMEDIO, ENSAMBLE, CALIBRADO, META)
    nombres = list(MODELOS) if solo in combinados else [solo]
    for n in nombres:
        try:
            base[n] = memo(MODELOS[n](ctx))
        except Exception:
            continue
    preds = OrderedDict(base)
    if solo in combinados and base:
        preds[PROMEDIO] = memo(combinar(base, None))
        ens = memo(combinar(base, pesos or {n: 1.0 for n in base}))
        preds[ENSAMBLE] = ens

        def calibrado(a, b):
            r = ens(a, b)
            return armar(r["la"], r["lb"], probs=temperado((r["pa"], r["pe"], r["pb"]), temp))
        preds[CALIBRADO] = memo(calibrado)
        if meta is not None and meta.ok:
            def meta_pred(a, b):
                r = ens(a, b)
                rs = [f(a, b) for f in base.values()]
                return armar(r["la"], r["lb"], probs=meta.prob(rasgos(ctx, a, b, r, rs)))
            preds[META] = memo(meta_pred)
    return preds


def mercados(r, mu):
    """Más/menos goles, ambos marcan y marcador más probable a partir de las curvas de goles."""
    fa, fb = r["fa"], r["fb"]
    linea = math.floor(2 * mu) + 0.5
    hasta = int(linea)
    acum_b, menos = [], 0.0
    s = 0.0
    for x in fb:
        s += x
        acum_b.append(s)
    for i in range(0, hasta + 1):
        menos += fa[i] * acum_b[hasta - i]
    mejor, marc = 0.0, "0-0"
    for i in range(13):
        for j in range(13):
            q = fa[i] * fb[j]
            if q > mejor:
                mejor, marc = q, f"{i}-{j}"
    return {"linea": linea, "over": round(1 - menos, 4), "btts": round((1 - fa[0]) * (1 - fb[0]), 4),
            "marcador": marc, "p_marcador": round(mejor, 4)}


# ================= MOTOR: PRONOSTICAR Y VERIFICAR =================
def logloss_rec(rec, nombre):
    m = rec["m"].get(nombre)
    if not m:
        return None
    return -math.log(max(m[{"A": 0, "E": 1, "B": 2}[rec["salida"]]], 1e-6))


def mejor_de(m):
    return max((m[0], "A"), (m[1], "E"), (m[2], "B"))[1]


class Motor:
    def __init__(self, alm):
        self.alm = alm
        self.meta = MetaModelo()
        self._n_meta = 0

    def entrenar_meta(self):
        recs = self.alm.registros_ordenados()
        self.meta.entrenar(recs)
        self._n_meta = len(recs)
        return self.meta.info

    def confianza(self):
        """Desde qué probabilidad el pronóstico 1X2 acierta al menos UMBRAL_ACIERTO en el historial."""
        recs = self.alm.registros_ordenados()[-5000:]
        if len(recs) < 80:
            return None
        tops = [(max(r["m"][r["usado"]][:3]), mejor_de(r["m"][r["usado"]]) == r["salida"]) for r in recs]
        mejor = None
        for i in range(10, 19):
            t = i * 0.05
            sel = [ok for p, ok in tops if p >= t]
            if len(sel) >= 40:
                acc = sum(sel) / len(sel)
                cand = {"umbral": round(t, 2), "acierto": round(acc, 3), "n": len(sel),
                        "cobertura": round(len(sel) / len(tops), 3)}
                if acc >= UMBRAL_ACIERTO:
                    return cand
                if mejor is None or acc > mejor["acierto"]:
                    mejor = cand
        return mejor

    def _cache(self, nombre, dt, cada, calcular):
        """Recalcula como mucho cada 'cada' pronósticos nuevos (ahorra tiempo al ponerse al día)."""
        n = len(self.alm.registros_antes(dt))
        c = self.__dict__.setdefault("_caches", {})
        if nombre in c and c[nombre][0] == n // cada:
            return c[nombre][1]
        v = calcular()
        c[nombre] = (n // cada, v)
        return v

    def pesos(self, dt):
        return self._cache("pesos", dt, 10, lambda: self._pesos(dt))

    def _pesos(self, dt):
        """Pesos del ensamble bayesiano: exp(-η · log-loss acumulada reciente)."""
        recs = self.alm.registros_antes(dt)[-VENTANA_RANKING:]
        if not recs:
            return None
        L = {}
        for n in MODELOS:
            vals = [logloss_rec(r, n) for r in recs]
            vals = [v for v in vals if v is not None]
            if vals:
                L[n] = sum(vals) / len(vals) * len(recs)
        if not L:
            return None
        mn = min(L.values())
        return {n: math.exp(-ETA_BMA * (v - mn)) for n, v in L.items()}

    def temperatura(self, dt):
        return self._cache("temp", dt, 50, lambda: self._temperatura(dt))

    def _temperatura(self, dt):
        """Temperatura que mejor calibra el ensamble con los resultados reales previos."""
        recs = [r for r in self.alm.registros_antes(dt)[-600:] if ENSAMBLE in r["m"]]
        if len(recs) < 60:
            return 1.0
        mejor, mejor_t = 1e18, 1.0
        for i in range(21):
            T = 0.6 + 0.05 * i
            ll = 0.0
            for r in recs:
                p = temperado(r["m"][ENSAMBLE][:3], T)
                ll -= math.log(max(p[{"A": 0, "E": 1, "B": 2}[r["salida"]]], 1e-9))
            if ll < mejor:
                mejor, mejor_t = ll, T
        return mejor_t

    def modelo_en_uso(self, dt=None):
        return self._cache("modelo", dt, 10, lambda: self._modelo_en_uso(dt))

    def _modelo_en_uso(self, dt=None):
        recs = self.alm.registros_antes(dt)[-VENTANA_RANKING:]
        if len(recs) < MIN_ELECCION:
            return ENSAMBLE
        mejor, mejor_v = ENSAMBLE, 1e9
        for n in TODOS:
            vals = [logloss_rec(r, n) for r in recs]
            vals = [v for v in vals if v is not None]
            if len(vals) >= 0.9 * len(recs):
                v = sum(vals) / len(vals)
                if v < mejor_v:
                    mejor, mejor_v = n, v
        return mejor

    def registrar(self, M):
        ctx = contexto(self.alm, M["liga"], M)
        usado = self.modelo_en_uso(M["dt"])
        preds = construir_predictores(ctx, self.pesos(M["dt"]), temp=self.temperatura(M["dt"]), meta=self.meta)
        a, b = M["a"], M["b"]
        m, r_usado, base_rs, r_ens = {}, None, [], None
        for n, f in preds.items():
            try:
                r = f(a, b)
            except Exception:
                continue
            m[n] = [round(r["pa"], 4), round(r["pe"], 4), round(r["pb"], 4), round(r["la"], 3), round(r["lb"], 3)]
            if n in MODELOS:
                base_rs.append(r)
            if n == ENSAMBLE:
                r_ens = r
            if n == usado:
                r_usado = r
        if not m:
            return None
        if r_usado is None:
            usado = ENSAMBLE if ENSAMBLE in m else next(iter(m))
            r_usado = preds[usado](a, b)

        def tipo(j):
            if not ctx["hist_cnt"].get(j):
                return "sin historial"
            return "mismo equipo" if ctx["equipo"][j] in ctx["eq_prev"].get(j, set()) else "otro equipo"
        ta, tb = tipo(a), tipo(b)
        cat = ("sin historial" if ta == tb == "sin historial" else
               "algún jugador cambió de equipo" if "otro equipo" in (ta, tb) else "con historial y mismo equipo")
        L = self.alm.ligas.get(M["liga"], {})
        rec = {"key": M["key"], "liga": M["liga"], "num": L.get("num"), "dt": iso(M["dt"]),
               "a": a, "b": b, "eq_a": M["eq_a"], "eq_b": M["eq_b"], "ga": M["ga"], "gb": M["gb"],
               "salida": resultado_de(M["ga"], M["gb"]), "hist_a": ctx["hist_cnt"].get(a, 0),
               "hist_b": ctx["hist_cnt"].get(b, 0), "n_liga": len(ctx["conocidos"]), "cat": cat,
               "consola": M.get("consola", ""), "usado": usado, "m": m, "mk": mercados(r_usado, ctx["mu"])}
        rec["pick"] = mejor_mercado(r_usado, rec["mk"], a, b)
        rec["pick_ok"] = cumple(rec["pick"]["cod"], M["ga"], M["gb"], rec["mk"]["linea"])
        if r_ens is not None:
            rec["f"] = rasgos(ctx, a, b, r_ens, base_rs)
        self.alm.agregar_registro(rec)
        return rec

    def verificar(self, progreso=None):
        faltan = sorted((p for p in self.alm.partidos.values()
                         if p["terminado"] and p["key"] not in self.alm.registros), key=orden_crono)
        hechos = []
        for i, M in enumerate(faltan):
            try:
                rec = self.registrar(M)
            except Exception as e:
                print(f"No pude pronosticar {M['a']} vs {M['b']}: {type(e).__name__}: {e}")
                rec = None
            if rec:
                hechos.append(rec)
            if progreso and (i % 10 == 9 or i == len(faltan) - 1):
                progreso(i + 1, len(faltan))
        return hechos


# ================= VISTAS PARA EL PANEL =================
def pron_dict(v):
    return {"pa": v[0], "pe": v[1], "pb": v[2], "la": v[3], "lb": v[4]}


def monte_carlo(ctx, pred, sims):
    jug, tabla = ctx["jugadores"], ctx["tabla"]
    pend = []
    for p in ctx["pendientes"]:
        r = pred(p["a"], p["b"])
        ca, cb, s = [], [], 0.0
        for x in r["fa"]:
            s += x
            ca.append(s)
        s = 0.0
        for x in r["fb"]:
            s += x
            cb.append(s)
        pend.append((p["a"], p["b"], ca, cb))
    campeon = defaultdict(int)
    rnd = random.Random(2026)
    for _ in range(sims):
        pts = {j: tabla[j]["Pts"] for j in jug}
        dg = {j: tabla[j]["GF"] - tabla[j]["GC"] for j in jug}
        gf = {j: tabla[j]["GF"] for j in jug}
        for a, b, ca, cb in pend:
            x, y = bisect.bisect_left(ca, rnd.random()), bisect.bisect_left(cb, rnd.random())
            if x > y:
                pts[a] += 3
            elif x == y:
                pts[a] += 1
                pts[b] += 1
            else:
                pts[b] += 3
            dg[a] += x - y
            dg[b] += y - x
            gf[a] += x
            gf[b] += y
        campeon[max(jug, key=lambda j: (pts[j], dg[j], gf[j], rnd.random()))] += 1
    return {j: campeon[j] / max(sims, 1) for j in jug}


def validar_fechas(L, ps):
    alertas = []
    ahora = AHORA()
    if any(p["dt"] is None for p in ps):
        alertas.append("Hay partidos sin hora legible: se ordenan por su posición.")
    for p in ps:
        if p["dt"] and p["terminado"] and p["dt"] > ahora + timedelta(minutes=5):
            alertas.append(f"{p['a']} vs {p['b']} figura terminado con hora futura ({p['dt']:%H:%M}): revisa la zona horaria.")
        if p["dt"] and not p["terminado"] and not p["anulado"] and p["dt"] < ahora - timedelta(minutes=45):
            alertas.append(f"{p['a']} vs {p['b']} ({p['dt']:%H:%M}) lleva más de 45 min sin resultado.")
    dts = [p["dt"] for p in ps if p["dt"]]
    if dts and max(dts).date() != min(dts).date():
        alertas.append("La liga cruza la medianoche; los partidos después de las 00:00 van al día siguiente.")
    anul = sum(1 for p in ps if p["anulado"])
    if anul:
        alertas.append(f"{anul} partidos cancelados o aplazados quedan fuera del análisis.")
    return alertas[:8]


def foto_liga(alm, motor, liga_id):
    L = alm.ligas[liga_id]
    ps = sorted(alm.partidos_de(liga_id), key=orden_crono)
    modelo = motor.modelo_en_uso()
    ctx = pred = None
    if L["estado"] != "terminada" and ps:
        ctx = contexto(alm, liga_id)
        preds = construir_predictores(ctx, motor.pesos(None), solo=modelo, temp=motor.temperatura(None),
                                      meta=motor.meta)
        pred = preds.get(modelo) or next(iter(preds.values()), None)
    filas = []
    aciertos = evaluados = 0
    for p in ps:
        f = {"hora": p["dt"].strftime("%H:%M") if p["dt"] else (p.get("hora") or ""), "a": p["a"], "b": p["b"],
             "eq_a": p["eq_a"], "eq_b": p["eq_b"], "estado": p["estado"], "fin": p["terminado"],
             "anulado": p["anulado"], "vivo": p["en_vivo"], "marcador_vivo": p["vivo"],
             "ga": p["ga"], "gb": p["gb"], "ca": p["ca"], "cb": p["cb"]}
        rec = alm.registros.get(p["key"])
        if rec and rec["usado"] in rec["m"]:
            v = rec["m"][rec["usado"]]
            f["pron"] = pron_dict(v)
            f["ok"] = mejor_de(v) == rec["salida"]
            f["mk"] = rec["mk"]
            f["hist"] = [rec["hist_a"], rec["hist_b"]]
            if rec.get("pick"):
                f["pick"] = dict(rec["pick"], ok=rec.get("pick_ok"))
            evaluados += 1
            aciertos += f["ok"]
        elif pred and not p["terminado"] and not p["anulado"]:
            try:
                r = pred(p["a"], p["b"])
                f["pron"] = {k: round(r[k], 4) for k in ("pa", "pe", "pb", "la", "lb")}
                f["mk"] = mercados(r, ctx["mu"])
                f["hist"] = [ctx["hist_cnt"].get(p["a"], 0), ctx["hist_cnt"].get(p["b"], 0)]
                f["pick"] = mejor_mercado(f["pron"], f["mk"], p["a"], p["b"])
            except Exception:
                pass
        filas.append(f)
    jugadores = list(OrderedDict.fromkeys([p["a"] for p in ps] + [p["b"] for p in ps]))
    t = tabla_vacia(jugadores)
    equipo = {}
    for p in ps:
        equipo.setdefault(p["a"], p["eq_a"])
        equipo.setdefault(p["b"], p["eq_b"])
        if p["terminado"]:
            aplicar(t, p["a"], p["b"], p["ga"], p["gb"])
    tabla = [{"j": j, "eq": equipo.get(j, ""), **t[j]} for j in ordenar(t)]
    campeon = None
    if ctx and pred and ctx["pendientes"]:
        try:
            pc = monte_carlo(ctx, pred, SIM_PANEL)
            campeon = [{"j": j, "p": round(pc[j], 4)} for j in sorted(pc, key=lambda j: -pc[j])]
        except Exception:
            campeon = None
    validos = [p for p in ps if not p["anulado"]]
    return {"id": liga_id, "num": L.get("num"), "nombre": L["nombre"], "estado": L["estado"],
            "hora": L["dt"].strftime("%H:%M") if L.get("dt") else "", "modelo": modelo,
            "filas": filas, "tabla": tabla, "campeon": campeon, "evaluados": evaluados, "aciertos": aciertos,
            "n_fin": sum(1 for p in validos if p["terminado"]), "n_total": len(validos),
            "con_hist": sum(1 for j in jugadores if ctx and ctx["hist_cnt"].get(j)) if ctx else None,
            "alertas": validar_fechas(L, ps)}


def resumen(alm, motor, fotos, fase, url_publica):
    ahora = AHORA()
    ligas = []
    for L in alm.ligas_ordenadas():
        f = fotos.get(L["id"])
        recs = [r for r in alm.registros.values() if r["liga"] == L["id"]]
        ok = sum(1 for r in recs if mejor_de(r["m"][r["usado"]]) == r["salida"])
        lider = f["tabla"][0]["j"] if f and f["tabla"] and f["n_fin"] else ""
        ligas.append({"id": L["id"], "num": L.get("num"), "nombre": L["nombre"], "estado": L["estado"],
                      "hora": L["dt"].strftime("%H:%M") if L.get("dt") else "", "lider": lider,
                      "n_fin": f["n_fin"] if f else 0, "n_total": f["n_total"] if f else 0,
                      "acierto": round(ok / len(recs), 3) if recs else None, "n_ver": len(recs)})
    en_vivo, proximos = [], []
    for L in alm.ligas_ordenadas():
        f = fotos.get(L["id"])
        if not f or L["estado"] == "terminada":
            continue
        for x in f["filas"]:
            if x["fin"] or x["anulado"] or not x.get("pron"):
                continue
            item = dict(x, liga=L["id"], liga_nombre=L["nombre"], num=L.get("num"))
            (en_vivo if x["vivo"] else proximos).append(item)
    proximos.sort(key=lambda x: (x["hora"] or "99"))
    recs = alm.registros_hoy()
    recientes = []
    for r in recs[-12:][::-1]:
        v = r["m"][r["usado"]]
        recientes.append({"hora": r["dt"][11:16] if r["dt"] else "", "a": r["a"], "b": r["b"],
                          "eq_a": r["eq_a"], "eq_b": r["eq_b"], "ga": r["ga"], "gb": r["gb"],
                          "pron": pron_dict(v), "ok": mejor_de(v) == r["salida"],
                          "liga": r["liga"], "num": r["num"], "liga_nombre": alm.ligas[r["liga"]]["nombre"]})
    ok = sum(1 for r in recs if mejor_de(r["m"][r["usado"]]) == r["salida"])
    conf = motor.confianza()
    alta = []
    if conf:
        for x in en_vivo + proximos:
            top = max(x["pron"]["pa"], x["pron"]["pe"], x["pron"]["pb"])
            if top >= conf["umbral"]:
                alta.append(x)
    picks = [r for r in recs if r.get("pick")]
    estados = defaultdict(int)
    for L in alm.ligas.values():
        estados[L["estado"]] += 1
    return {"fecha": alm.fecha.strftime("%d/%m/%Y"), "fase": fase, "hora": ahora.strftime("%H:%M:%S"),
            "url_publica": url_publica, "modelo": motor.modelo_en_uso(),
            "kpi": {"ligas": len(alm.ligas), "terminadas": estados["terminada"], "en_juego": estados["en juego"],
                    "proximas": estados["próxima"], "verificados": len(recs),
                    "acierto": round(ok / len(recs), 3) if recs else None},
            "ligas": ligas, "en_vivo": en_vivo[:24], "proximos": proximos[:15], "recientes": recientes,
            "confianza": conf, "alta": alta[:12], "meta": motor.meta.info,
            "acierto_pick": round(sum(1 for r in picks if r.get("pick_ok")) / len(picks), 3) if picks else None}


# ================= ANÁLISIS DEL DÍA =================
def _acc(recs, n=None):
    vals = [mejor_de(r["m"][n or r["usado"]]) == r["salida"] for r in recs if (n or r["usado"]) in r["m"]]
    return sum(vals) / len(vals) if vals else None


def _ll(recs, n=None):
    vals = [logloss_rec(r, n or r["usado"]) for r in recs]
    vals = [v for v in vals if v is not None]
    return sum(vals) / len(vals) if vals else None


def _rps(recs, n):
    tot = k = 0
    for r in recs:
        m = r["m"].get(n)
        if not m:
            continue
        oa, oe = int(r["salida"] == "A"), int(r["salida"] == "E")
        tot += ((m[0] - oa) ** 2 + (m[0] + m[1] - oa - oe) ** 2) / 2
        k += 1
    return tot / k if k else None


def p_dos_prop(k1, n1, k2, n2):
    if not n1 or not n2:
        return 1.0
    p = (k1 + k2) / (n1 + n2)
    se = math.sqrt(p * (1 - p) * (1 / n1 + 1 / n2))
    return 1.0 if se == 0 else math.erfc(abs((k1 / n1 - k2 / n2) / se) / math.sqrt(2))


def grupo(recs, clave, orden=None):
    g = defaultdict(list)
    for r in recs:
        g[clave(r)].append(r)
    claves = orden or sorted(g)
    return [{"grupo": c, "n": len(g[c]), "acierto": _acc(g[c]), "logloss": _ll(g[c])} for c in claves if g.get(c)]


def tramo_hist(r):
    x = (r["hist_a"] + r["hist_b"]) / 2
    return ("sin historial" if x == 0 else "1 a 5 previos" if x <= 5 else "6 a 15 previos" if x <= 15
            else "16 a 30 previos" if x <= 30 else "más de 30 previos")


TRAMOS = ["sin historial", "1 a 5 previos", "6 a 15 previos", "16 a 30 previos", "más de 30 previos"]


def analisis_dia(alm, motor):
    recs = alm.registros_hoy()
    out = {"n": len(recs), "conclusiones": [], "modelos": [], "por_bloque": [], "por_hora": [],
           "por_hist": [], "por_equipo": [], "calibracion": [], "mercados": {}, "equipos": [],
           "jugadores": [], "patrones": [], "umbral": None}
    equipos_jugadores(alm, out)
    if not recs:
        out["conclusiones"].append("Aún no hay pronósticos verificados.")
        return out
    for n in TODOS:
        sub = [r for r in recs if n in r["m"]]
        if sub:
            out["modelos"].append({"modelo": n, "n": len(sub), "acierto": _acc(sub, n), "logloss": _ll(sub, n),
                                   "rps": _rps(sub, n)})
    out["modelos"].sort(key=lambda x: x["logloss"])
    ultimos = recs[-VENTANA_RANKING:]
    reciente = min((n for n in TODOS if any(n in r["m"] for r in ultimos)), key=lambda n: _ll(ultimos, n) or 9)
    out["por_bloque"] = grupo(recs, lambda r: f"{((r['num'] or 1) - 1) // 5 * 5 + 1:02d} a {((r['num'] or 1) - 1) // 5 * 5 + 5:02d}")
    out["por_hora"] = grupo(recs, lambda r: (r["dt"] or "")[11:13] + ":00" if r["dt"] else "sin hora")
    out["por_hist"] = grupo(recs, tramo_hist, TRAMOS)
    out["por_equipo"] = grupo(recs, lambda r: r["cat"], ["sin historial", "con historial y mismo equipo",
                                                          "algún jugador cambió de equipo"])
    # calibración: ¿cuando dice 60%, pasa el 60% de las veces?
    bins = defaultdict(lambda: [0.0, 0, 0])
    for r in recs:
        v = r["m"][r["usado"]]
        for prob, sal in ((v[0], "A"), (v[1], "E"), (v[2], "B")):
            b = min(int(prob * 10), 9)
            bins[b][0] += prob
            bins[b][1] += r["salida"] == sal
            bins[b][2] += 1
    out["calibracion"] = [{"rango": f"{b * 10}–{b * 10 + 10}%", "predicho": bins[b][0] / bins[b][2],
                           "real": bins[b][1] / bins[b][2], "n": bins[b][2]} for b in sorted(bins) if bins[b][2]]
    ov = [((r["ga"] + r["gb"]) > r["mk"]["linea"]) == (r["mk"]["over"] > 0.5) for r in recs]
    bt = [((r["ga"] > 0 and r["gb"] > 0) == (r["mk"]["btts"] > 0.5)) for r in recs]
    mc = [r["mk"]["marcador"] == f"{r['ga']}-{r['gb']}" for r in recs]
    pk = [r["pick_ok"] for r in recs if r.get("pick")]
    dc = [mejor_de(r["m"][r["usado"]]) in ("A", "E") and r["salida"] in ("A", "E") or
          mejor_de(r["m"][r["usado"]]) in ("B", "E") and r["salida"] in ("B", "E") for r in recs]
    out["mercados"] = {"over": sum(ov) / len(ov), "btts": sum(bt) / len(bt), "marcador": sum(mc) / len(mc),
                       "goles_medios": sum(r["ga"] + r["gb"] for r in recs) / len(recs),
                       "pick": sum(pk) / len(pk) if pk else None, "doble": sum(dc) / len(dc)}
    historico = alm.registros_ordenados()
    out["por_confianza"] = []
    for i in range(7, 19):
        t = i * 0.05
        sel_h = [mejor_de(r["m"][r["usado"]]) == r["salida"] for r in historico if max(r["m"][r["usado"]][:3]) >= t]
        sel_d = [mejor_de(r["m"][r["usado"]]) == r["salida"] for r in recs if max(r["m"][r["usado"]][:3]) >= t]
        if sel_h:
            out["por_confianza"].append({"desde": f"{t:.0%}", "n_hist": len(sel_h), "acierto_hist": sum(sel_h) / len(sel_h),
                                         "n_hoy": len(sel_d), "acierto_hoy": sum(sel_d) / len(sel_d) if sel_d else None})
    out["meta"] = motor.meta.info
    # ¿desde qué liga se predice mejor?
    nums = sorted({r["num"] for r in recs if r["num"]})
    mejor_u = None
    for L in nums[1:]:
        antes = [r for r in recs if r["num"] and r["num"] < L]
        desp = [r for r in recs if r["num"] and r["num"] >= L]
        if len(antes) < 30 or len(desp) < 30:
            continue
        aa, ad = _acc(antes), _acc(desp)
        p = p_dos_prop(round(ad * len(desp)), len(desp), round(aa * len(antes)), len(antes))
        if mejor_u is None or ad - aa > mejor_u["dif"]:
            mejor_u = {"liga": L, "dif": ad - aa, "antes": aa, "despues": ad, "na": len(antes), "nd": len(desp), "p": p}
    out["umbral"] = mejor_u
    con = out["conclusiones"]
    con.append(f"{len(recs)} pronósticos verificados; el modelo en uso acertó {_acc(recs):.0%} del 1X2.")
    con.append(f"Mejor modelo en los últimos {len(ultimos)} partidos: {reciente} "
               f"(log-loss {_ll(ultimos, reciente):.3f}; menor es mejor).")
    if mejor_u and mejor_u["dif"] > 0.03:
        txt = (f"Desde la liga {mejor_u['liga']} el acierto sube a {mejor_u['despues']:.0%}, frente a "
               f"{mejor_u['antes']:.0%} antes ({mejor_u['nd']} vs {mejor_u['na']} partidos, p = {mejor_u['p']:.2f}). ")
        con.append(txt + ("Diferencia sólida." if mejor_u["p"] < 0.05 else "Aún puede ser azar."))
    elif len(nums) > 1:
        con.append("Todavía no se ve una liga a partir de la cual el acierto mejore claramente.")
    ph = [x for x in out["por_hist"] if x["n"] >= 20]
    if len(ph) >= 2:
        b = max(ph, key=lambda x: x["acierto"])
        con.append(f"Se acierta más cuando los jugadores traen {b['grupo']} ({b['acierto']:.0%} en {b['n']} partidos).")
    pe = {x["grupo"]: x for x in out["por_equipo"]}
    m1, m2 = pe.get("con historial y mismo equipo"), pe.get("algún jugador cambió de equipo")
    if m1 and m2 and m1["n"] >= 15 and m2["n"] >= 15:
        con.append(f"Mismo equipo de antes: {m1['acierto']:.0%} de acierto; con cambio de equipo: {m2['acierto']:.0%}.")
    mk = out["mercados"]
    con.append(f"Más/menos goles acertó {mk['over']:.0%}, ambos marcan {mk['btts']:.0%} y el marcador exacto "
               f"{mk['marcador']:.0%}. Media de {mk['goles_medios']:.1f} goles por partido.")
    if mk.get("pick") is not None:
        con.append(f"El 'mercado más seguro' de cada partido acertó {mk['pick']:.0%}; la doble oportunidad "
                   f"del favorito (gana o empata), {mk['doble']:.0%}.")
    conf = motor.confianza()
    if conf:
        con.append(f"Con todo el historial: cuando el 1X2 da {conf['umbral']:.0%} o más, acierta {conf['acierto']:.0%} "
                   f"({conf['n']} partidos, {conf['cobertura']:.0%} del total).")
    if motor.meta.info.get("estado") == "activo":
        i = motor.meta.info
        con.append(f"Meta-modelo entrenado con {i['entrenado_con']} partidos reales: log-loss {i['logloss_meta']:.3f} "
                   f"frente a {i['logloss_ensamble']:.3f} del ensamble en partidos que no vio.")
    if out["equipos"]:
        e = out["equipos"][0]
        con.append(f"Equipo más rentable del día: {e['equipo']} ({e['pts_pj']:.2f} pts por partido en {e['PJ']}).")
    out["patrones"] = patrones_dia(alm, recs)
    sig = [p["nombre"] for p in out["patrones"] if p["veredicto"] == "significativo"]
    pos = [p["nombre"] for p in out["patrones"] if p["veredicto"] == "posible"]
    if sig:
        con.append("Patrones con evidencia sólida: " + "; ".join(sig) + ".")
    if pos:
        con.append("Patrones por confirmar (pueden ser azar): " + "; ".join(pos) + ".")
    return out


def equipos_jugadores(alm, out):
    eq = defaultdict(lambda: {"PJ": 0, "G": 0, "E": 0, "P": 0, "GF": 0, "GC": 0, "jug": set()})
    jug = defaultdict(lambda: {"PJ": 0, "G": 0, "E": 0, "P": 0, "GF": 0, "GC": 0, "Pts": 0, "ligas": set(),
                               "eqs": defaultdict(lambda: [0, 0])})
    for p in alm.partidos.values():
        if not p["terminado"]:
            continue
        for j, e, f, c in ((p["a"], p["eq_a"] or "?", p["ga"], p["gb"]), (p["b"], p["eq_b"] or "?", p["gb"], p["ga"])):
            r = "G" if f > c else "E" if f == c else "P"
            pts = {"G": 3, "E": 1, "P": 0}[r]
            for d in (eq[e], jug[j]):
                d["PJ"] += 1
                d[r] += 1
                d["GF"] += f
                d["GC"] += c
            eq[e]["jug"].add(j)
            jug[j]["Pts"] += pts
            jug[j]["ligas"].add(p["liga"])
            jug[j]["eqs"][e][0] += 1
            jug[j]["eqs"][e][1] += pts
    out["equipos"] = sorted(({"equipo": e, "PJ": d["PJ"], "G": d["G"], "E": d["E"], "P": d["P"], "DG": d["GF"] - d["GC"],
                              "pct": d["G"] / d["PJ"], "pts_pj": (3 * d["G"] + d["E"]) / d["PJ"],
                              "jugadores": sorted(d["jug"])[:6]} for e, d in eq.items()),
                            key=lambda x: (x["PJ"] >= 5, x["pts_pj"]), reverse=True)[:40]
    lst = []
    for j, d in jug.items():
        mej = sorted(d["eqs"].items(), key=lambda kv: (kv[1][0] >= 3, kv[1][1] / kv[1][0]), reverse=True)
        lst.append({"jugador": j, "ligas": len(d["ligas"]), "PJ": d["PJ"], "G": d["G"], "E": d["E"], "P": d["P"],
                    "DG": d["GF"] - d["GC"], "pts_pj": d["Pts"] / d["PJ"], "mejor_equipo": mej[0][0] if mej else "",
                    "equipos": [f"{e} ({v[0]})" for e, v in sorted(d["eqs"].items(), key=lambda kv: -kv[1][0])][:4]})
    out["jugadores"] = sorted(lst, key=lambda x: (x["PJ"] >= 5, x["pts_pj"]), reverse=True)[:80]


# ================= PATRONES =================
def p_binomial(k, n, p0=0.5):
    if n == 0:
        return 1.0
    p0 = min(max(p0, 1e-9), 1 - 1e-9)
    lp = lambda i: math.lgamma(n + 1) - math.lgamma(i + 1) - math.lgamma(n - i + 1) + i * math.log(p0) + (n - i) * math.log(1 - p0)
    pk = lp(k)
    return min(1.0, sum(math.exp(lp(i)) for i in range(n + 1) if lp(i) <= pk + 1e-9))


def correlacion(x, y):
    n = len(x)
    if n < 3:
        return 0.0
    mx, my = sum(x) / n, sum(y) / n
    sx = sum((a - mx) ** 2 for a in x)
    sy = sum((b - my) ** 2 for b in y)
    if sx == 0 or sy == 0:
        return 0.0
    return sum((a - mx) * (b - my) for a, b in zip(x, y)) / math.sqrt(sx * sy)


def p_perm(x, y, rnd, rep=200):
    obs = abs(correlacion(x, y))
    y2 = list(y)
    c = 0
    for _ in range(rep):
        rnd.shuffle(y2)
        c += abs(correlacion(x, y2)) >= obs - 1e-12
    return (c + 1) / (rep + 1)


def p_signo(vals, rnd, rep=1000):
    if len(vals) < 5:
        return 1.0
    obs = abs(sum(vals) / len(vals))
    c = 0
    for _ in range(rep):
        c += abs(sum(v if rnd.random() < 0.5 else -v for v in vals) / len(vals)) >= obs - 1e-12
    return (c + 1) / (rep + 1)


def patrones_dia(alm, recs):
    fin = sorted((p for p in alm.partidos.values() if p["terminado"]), key=orden_crono)
    if len(fin) < 20:
        return []
    rnd = random.Random(7)
    res = []

    def add(nombre, detalle, p):
        res.append({"nombre": nombre, "detalle": detalle, "p": round(p, 4)})

    n = len(fin)
    gl = sum(p["ga"] > p["gb"] for p in fin)
    gv = sum(p["ga"] < p["gb"] for p in fin)
    add("Ventaja del jugador listado primero", f"gana el 1.º {gl} veces y el 2.º {gv}", p_binomial(gl, gl + gv))
    if recs:
        esp = sum(r["m"][r["usado"]][1] for r in recs)
        var = sum(r["m"][r["usado"]][1] * (1 - r["m"][r["usado"]][1]) for r in recs) or 1
        obs = sum(r["salida"] == "E" for r in recs)
        add("Empates frente a lo esperado", f"{obs} empates; el modelo esperaba {esp:.0f}",
            math.erfc(abs(obs - esp) / math.sqrt(2 * var)))
    goles = [g for p in fin for g in (p["ga"], p["gb"])]
    m = sum(goles) / len(goles)
    v = sum((g - m) ** 2 for g in goles) / (len(goles) - 1)
    if m > 0 and v > 0:
        df = len(goles) - 1
        z = ((v / m) ** (1 / 3) - (1 - 2 / (9 * df))) / math.sqrt(2 / (9 * df))
        add("Dispersión de goles", f"varianza/media = {v / m:.2f} (1.0 sería Poisson puro)", math.erfc(abs(z) / math.sqrt(2)))
    con_hora = [p for p in fin if p["dt"]]
    if len(con_hora) >= 20:
        add("Goles según la hora del día", f"r = {correlacion([p['dt'].hour + p['dt'].minute / 60 for p in con_hora], [p['ga'] + p['gb'] for p in con_hora]):+.2f}",
            p_perm([p["dt"].hour + p["dt"].minute / 60 for p in con_hora], [p["ga"] + p["gb"] for p in con_hora], rnd))
    esq = [p for p in fin if p["ca"] is not None and p["cb"] is not None and p["ca"] + p["cb"] > 0]
    if len(esq) >= 20:
        x, y = [p["ca"] - p["cb"] for p in esq], [p["ga"] - p["gb"] for p in esq]
        add("Esquinas y goles", f"r = {correlacion(x, y):+.2f} entre diferencia de esquinas y de goles", p_perm(x, y, rnd))
    cons = defaultdict(list)
    for p in fin:
        if p.get("consola"):
            cons[p["consola"]].append(p["ga"] + p["gb"])
    cons = {k: v for k, v in cons.items() if len(v) >= 10}
    if len(cons) >= 2:
        etq = [k for k, v in cons.items() for _ in v]
        tot = [g for v in cons.values() for g in v]

        def rango(t):
            med = defaultdict(list)
            for e, g in zip(etq, t):
                med[e].append(g)
            ms = [sum(v) / len(v) for v in med.values()]
            return max(ms) - min(ms)
        o = rango(tot)
        t2 = list(tot)
        c = 0
        for _ in range(400):
            rnd.shuffle(t2)
            c += rango(t2) >= o - 1e-12
        add("Estadio o consola", f"diferencia de {o:.2f} goles por partido entre estadios", (c + 1) / 401)
    if recs:
        # Residuo = puntos reales - puntos esperados por el modelo en uso
        cuenta, previo = defaultdict(int), {}
        idx_x, idx_y, mom_x, mom_y = [], [], [], []
        primeras = {}
        rev = []
        for r in recs:
            v = r["m"][r["usado"]]
            for j, pts, esp, lado in ((r["a"], 3 if r["salida"] == "A" else 1 if r["salida"] == "E" else 0, 3 * v[0] + v[1], "a"),
                                      (r["b"], 3 if r["salida"] == "B" else 1 if r["salida"] == "E" else 0, 3 * v[2] + v[1], "b")):
                res_ = pts - esp
                idx_x.append(cuenta[j])
                idx_y.append(res_)
                cuenta[j] += 1
                if j in previo:
                    mom_x.append(previo[j])
                    mom_y.append(res_)
                previo[j] = 1 if pts == 3 else 0
            par = (r["liga"], frozenset((r["a"], r["b"])))
            if par in primeras:
                perdedor = primeras[par]
                if perdedor:
                    v = r["m"][r["usado"]]
                    if perdedor == r["a"]:
                        rev.append((3 if r["salida"] == "A" else 1 if r["salida"] == "E" else 0) - (3 * v[0] + v[1]))
                    else:
                        rev.append((3 if r["salida"] == "B" else 1 if r["salida"] == "E" else 0) - (3 * v[2] + v[1]))
            else:
                primeras[par] = r["b"] if r["salida"] == "A" else r["a"] if r["salida"] == "B" else None
        if len(idx_x) >= 40:
            add("Fatiga durante el día", f"r = {correlacion(idx_x, idx_y):+.2f} entre partidos ya jugados y rendimiento sobre lo esperado",
                p_perm(idx_x, idx_y, rnd))
        if len(mom_x) >= 40:
            add("Racha (ganar el partido anterior)", f"r = {correlacion(mom_x, mom_y):+.2f} con el rendimiento sobre lo esperado",
                p_perm(mom_x, mom_y, rnd))
        if len(rev) >= 10:
            add("Revancha en la vuelta", f"quien perdió la ida rinde {sum(rev) / len(rev):+.2f} pts sobre lo esperado ({len(rev)} casos)",
                p_signo(rev, rnd))
    alfa = 0.05 / max(len(res), 1)
    for r in res:
        r["veredicto"] = "significativo" if r["p"] < alfa else "posible" if r["p"] < 0.05 else "sin evidencia"
    return res


# ================= HISTORIAL DE TODOS LOS DÍAS (SQLite) =================
class Historial:
    """Base local con todos los resultados reales y pronósticos verificados de cada día."""

    def __init__(self, ruta):
        Path(ruta).parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(str(ruta))
        self.db.executescript("""
            CREATE TABLE IF NOT EXISTS partidos(key TEXT PRIMARY KEY, fecha TEXT, liga TEXT, liga_nombre TEXT,
                dt TEXT, idx INT, a TEXT, b TEXT, eq_a TEXT, eq_b TEXT, ga INT, gb INT, ca INT, cb INT, consola TEXT);
            CREATE INDEX IF NOT EXISTS ix_partidos_fecha ON partidos(fecha);
            CREATE TABLE IF NOT EXISTS registros(key TEXT PRIMARY KEY, fecha TEXT, dt TEXT, datos TEXT);
            CREATE INDEX IF NOT EXISTS ix_registros_dt ON registros(dt);
            CREATE TABLE IF NOT EXISTS dias(fecha TEXT PRIMARY KEY, ligas INT, partidos INT, completo INT);
        """)

    def guardar_partidos(self, fecha, nombres, partidos):
        filas = [(p["key"], fecha.isoformat(), p["liga"], nombres.get(p["liga"], ""), iso(p["dt"]), p["idx"],
                  p["a"], p["b"], p["eq_a"], p["eq_b"], p["ga"], p["gb"], p.get("ca"), p.get("cb"), p.get("consola", ""))
                 for p in partidos if p["terminado"]]
        self.db.executemany("INSERT OR REPLACE INTO partidos VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", filas)
        self.db.commit()

    def guardar_registros(self, fecha, recs):
        self.db.executemany("INSERT OR REPLACE INTO registros VALUES (?,?,?,?)",
                            [(r["key"], fecha.isoformat(), r["dt"], json.dumps(r, ensure_ascii=False)) for r in recs])
        self.db.commit()

    def marcar_dia(self, fecha, ligas, partidos):
        self.db.execute("INSERT OR REPLACE INTO dias VALUES (?,?,?,1)", (fecha.isoformat(), ligas, partidos))
        self.db.commit()

    def dia_completo(self, fecha):
        return self.db.execute("SELECT 1 FROM dias WHERE fecha=? AND completo=1", (fecha.isoformat(),)).fetchone() is not None

    def cargar_partidos(self, desde, hasta):
        cur = self.db.execute("SELECT key,liga,dt,idx,a,b,eq_a,eq_b,ga,gb,ca,cb,consola FROM partidos "
                              "WHERE fecha>=? AND fecha<?", (desde.isoformat(), hasta.isoformat()))
        cols = ("key", "liga", "dt", "idx", "a", "b", "eq_a", "eq_b", "ga", "gb", "ca", "cb", "consola")
        out = []
        for fila in cur:
            p = dict(zip(cols, fila))
            p["dt"] = desde_iso(p["dt"])
            out.append(p)
        return out

    def cargar_registros(self, desde, hasta, limite=40000):
        cur = self.db.execute("SELECT datos FROM registros WHERE fecha>=? AND fecha<? ORDER BY dt DESC LIMIT ?",
                              (desde.isoformat(), hasta.isoformat(), limite))
        return [json.loads(f[0]) for f in cur][::-1]

    def dias_sin_analizar(self, antes_de):
        p = dict(self.db.execute("SELECT fecha, COUNT(*) FROM partidos WHERE fecha<? GROUP BY fecha",
                                 (antes_de.isoformat(),)).fetchall())
        r = dict(self.db.execute("SELECT fecha, COUNT(*) FROM registros GROUP BY fecha").fetchall())
        return sorted(f for f, n in p.items() if r.get(f, 0) < 0.9 * n)

    def cargar_dia(self, fecha):
        cur = self.db.execute("SELECT key,liga,liga_nombre,dt,idx,a,b,eq_a,eq_b,ga,gb,ca,cb,consola FROM partidos "
                              "WHERE fecha=?", (fecha.isoformat(),))
        cols = ("key", "liga", "liga_nombre", "dt", "idx", "a", "b", "eq_a", "eq_b", "ga", "gb", "ca", "cb", "consola")
        out = []
        for fila in cur:
            q = dict(zip(cols, fila))
            q["dt"] = desde_iso(q["dt"])
            out.append(q)
        return out

    def totales(self):
        n = self.db.execute("SELECT COUNT(*), COUNT(DISTINCT fecha) FROM partidos").fetchone()
        return {"partidos": n[0], "dias": n[1]}


def analizar_dia_pasado(args):
    """Proceso aparte: pronostica y verifica todos los partidos de un día anterior
    (cada día en un núcleo distinto del procesador)."""
    fecha_iso, ruta_db, dias, params = args
    globals().update(params)
    bajar_prioridad()
    fecha = date.fromisoformat(fecha_iso)
    h = Historial(ruta_db)
    alm = Almacen(fecha)
    for q in h.cargar_dia(fecha):
        L = alm.ligas.setdefault(q["liga"], {"id": q["liga"], "nombre": q.pop("liga_nombre") or q["liga"], "dt": None,
                                             "url": None, "estado": "terminada", "partidos": [], "firma": None,
                                             "ult_cambio": None, "consultada": True})
        q.pop("liga_nombre", None)
        q.update(terminado=True, anulado=False, en_vivo=False, vivo=None, estado="Finished")
        alm.partidos[q["key"]] = q
        L["partidos"].append(q["key"])
        if q["dt"] and (L["dt"] is None or q["dt"] < L["dt"]):
            L["dt"] = q["dt"]
    alm.numerar()
    alm.cargar_historial(h.cargar_partidos(fecha - timedelta(days=dias), fecha), [])
    recs = Motor(alm).verificar()
    h.guardar_registros(fecha, recs)
    return fecha_iso, len(recs)


def analizar_dias_pasados(historial, ruta_db, fecha, dias, panel, procesos=None):
    pendientes = [f for f in historial.dias_sin_analizar(fecha) if f >= (fecha - timedelta(days=dias)).isoformat()]
    if not pendientes:
        return 0
    n = procesos or max(1, min(6, (os.cpu_count() or 2) - 1))
    params = {k: globals()[k] for k in PARAMETROS}
    panel.avisar(f"Analizando {len(pendientes)} días anteriores en {n} procesos en paralelo...")
    hechos = 0
    with ProcessPoolExecutor(max_workers=n) as ex:
        futuros = [ex.submit(analizar_dia_pasado, (f, str(ruta_db), dias, params)) for f in pendientes]
        for i, fut in enumerate(as_completed(futuros), 1):
            try:
                f, k = fut.result()
                hechos += k
                panel.fase = f"Analizando días anteriores: {i} de {len(pendientes)} listos"
            except Exception as e:
                panel.avisar(f"Un día no se pudo analizar ({type(e).__name__}: {e}).")
    panel.avisar(f"Historial analizado: {hechos} pronósticos verificados de días anteriores.")
    return hechos


PARAMETROS = {"VIDA_MEDIA_HORAS": [6.0, 24.0, 72.0, 240.0], "PESO_OTRA_LIGA": [0.4, 0.7, 1.0],
              "F_OTRO_EQUIPO": [0.4, 0.7, 1.0], "PRIOR": [1.0, 2.0, 4.0]}


def autoajustar(alm, panel, fecha):
    """Elige los parámetros que mejor habrían pronosticado los resultados reales recientes
    (búsqueda por coordenadas sobre una muestra; se hace una vez al día y se guarda)."""
    ruta = Path(CARPETA_SALIDA) / "parametros.json"
    try:
        guardado = json.loads(ruta.read_text(encoding="utf-8"))
    except Exception:
        guardado = None
    if guardado and guardado.get("fecha") == fecha.isoformat():
        globals().update(guardado["valores"])
        panel.avisar(f"Parámetros ajustados hoy: {guardado['valores']}")
        return guardado
    cand = sorted([p for p in alm.hist_lista] +
                  [p for p in alm.partidos.values() if p["terminado"]], key=orden_crono)
    if not cand or cand[0]["dt"] is None:
        return guardado
    inicio = cand[0]["dt"] + timedelta(hours=3)        # los primeros no tienen historia
    cand = [p for p in cand if p["dt"] and p["dt"] >= inicio][-900:]
    if len(cand) < 150:
        if guardado:
            globals().update(guardado["valores"])
        return guardado
    muestra = cand[::max(1, len(cand) // 150)][:150]

    def evaluar():
        tot = 0.0
        for M in muestra:
            ctx = contexto(alm, M["liga"], M)
            r = m_maher(ctx)(M["a"], M["b"])
            tot -= math.log(max({"A": r["pa"], "E": r["pe"], "B": r["pb"]}[resultado_de(M["ga"], M["gb"])], 1e-6))
        return tot / len(muestra)

    panel.fase = "Ajustando parámetros con los resultados reales"
    base = evaluar()
    mejor = base
    for nombre, valores in PARAMETROS.items():
        for v in valores:
            viejo = globals()[nombre]
            if v == viejo:
                continue
            globals()[nombre] = v
            s = evaluar()
            if s < mejor - 1e-4:
                mejor = s
            else:
                globals()[nombre] = viejo
    valores = {k: globals()[k] for k in PARAMETROS}
    datos = {"fecha": fecha.isoformat(), "valores": valores, "logloss_antes": round(base, 4),
             "logloss_despues": round(mejor, 4), "muestra": len(muestra)}
    ruta.parent.mkdir(parents=True, exist_ok=True)
    ruta.write_text(json.dumps(datos, indent=1), encoding="utf-8")
    panel.avisar(f"Parámetros ajustados con {len(muestra)} partidos reales: {valores} "
                 f"(log-loss {base:.3f} -> {mejor:.3f}).")
    return datos


# ================= SESIÓN DEL DÍA =================
def _json_default(x):
    if isinstance(x, (datetime, date)):
        return x.isoformat()
    if isinstance(x, (set, tuple)):
        return list(x)
    return str(x)


def carpeta_dia(fecha):
    return Path(CARPETA_SALIDA) / fecha.isoformat()


def guardar_sesion(alm):
    ruta = carpeta_dia(alm.fecha) / "sesion.json"
    ruta.parent.mkdir(parents=True, exist_ok=True)
    ligas = {k: {kk: vv for kk, vv in L.items() if kk != "firma"} for k, L in alm.ligas.items()}
    datos = {"version": VERSION_SESION, "fecha": alm.fecha.isoformat(), "ligas": ligas, "partidos": list(alm.partidos.values()),
             "registros": list(alm.registros.values())}
    tmp = ruta.with_suffix(".tmp")
    tmp.write_text(json.dumps(datos, default=_json_default, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
    os.replace(tmp, ruta)


def cargar_sesion(fecha, nueva=False):
    alm = Almacen(fecha)
    ruta = carpeta_dia(fecha) / "sesion.json"
    if nueva or not ruta.exists():
        return alm
    try:
        d = json.loads(ruta.read_text(encoding="utf-8"))
        if not isinstance(d, dict) or d.get("version") != VERSION_SESION:
            raise ValueError("formato de una versión anterior del script")
        for k, L in d["ligas"].items():
            L["dt"] = desde_iso(L.get("dt"))
            L["firma"] = None
            alm.ligas[k] = L
        for p in d["partidos"]:
            p["dt"] = desde_iso(p.get("dt"))
            alm.partidos[p["key"]] = p
        for r in d["registros"]:
            alm.registros[r["key"]] = r
    except Exception as e:
        respaldo = ruta.with_name(f"sesion_anterior_{int(time.time())}.json")
        try:
            os.replace(ruta, respaldo)
        except OSError:
            pass
        print(f"La sesión guardada no sirve ({e}); la guardé como {respaldo.name} y empiezo de cero.")
        return Almacen(fecha)
    print(f"Sesión de hoy recuperada: {len(alm.ligas)} ligas, {len(alm.registros)} pronósticos verificados.")
    return alm


def guardar_excel(alm, dia, ruta):
    negrita = Font(bold=True)
    wb = Workbook()
    ws = wb.active
    ws.title = "Conclusiones"
    ws.append(["Conclusiones del día"])
    ws["A1"].font = negrita
    for c in dia["conclusiones"]:
        ws.append([c])
    ws.column_dimensions["A"].width = 130

    def hoja(nombre, cab, filas):
        h = wb.create_sheet(nombre)
        h.append(cab)
        for c in h[1]:
            c.font = negrita
        for f in filas:
            h.append([round(x, 4) if isinstance(x, float) else x for x in f])
        for i in range(1, len(cab) + 1):
            h.column_dimensions[h.cell(1, i).column_letter].width = 18
        h.freeze_panes = "A2"

    hoja("Modelos", ["Modelo", "Partidos", "Acierto", "Log-loss", "RPS"],
         [[m["modelo"], m["n"], m["acierto"], m["logloss"], m["rps"]] for m in dia["modelos"]])
    for nombre, clave in (("Por bloque de ligas", "por_bloque"), ("Por hora", "por_hora"),
                          ("Por historial", "por_hist"), ("Por equipo usado", "por_equipo")):
        hoja(nombre, ["Grupo", "Partidos", "Acierto", "Log-loss"],
             [[g["grupo"], g["n"], g["acierto"], g["logloss"]] for g in dia[clave]])
    hoja("Calibración", ["Rango", "Probabilidad media", "Frecuencia real", "Casos"],
         [[c["rango"], c["predicho"], c["real"], c["n"]] for c in dia["calibracion"]])
    hoja("Ligas", ["N.º", "Liga", "Hora", "Estado", "Partidos", "Verificados"],
         [[L.get("num"), L["nombre"], L["dt"].strftime("%H:%M") if L.get("dt") else "", L["estado"],
           len(L["partidos"]), sum(1 for r in alm.registros.values() if r["liga"] == L["id"])]
          for L in alm.ligas_ordenadas()])
    filas = []
    for r in alm.registros_hoy():
        v = r["m"][r["usado"]]
        filas.append([r["num"], alm.ligas[r["liga"]]["nombre"], r["dt"], r["a"], r["eq_a"], r["b"], r["eq_b"],
                      v[0], v[1], v[2], {"A": r["a"], "B": r["b"], "E": "Empate"}[mejor_de(v)],
                      f"{r['ga']}-{r['gb']}", "Sí" if mejor_de(v) == r["salida"] else "No", r["usado"],
                      r["mk"]["linea"], r["mk"]["over"], r["mk"]["btts"], r["mk"]["marcador"],
                      r["hist_a"], r["hist_b"], r["cat"]])
    hoja("Pronósticos", ["Liga", "Nombre", "Fecha y hora", "Local", "Equipo local", "Visita", "Equipo visita",
                         "% Local", "% Empate", "% Visita", "Pronóstico", "Real", "Acierto", "Modelo",
                         "Línea goles", "P(más)", "P(ambos marcan)", "Marcador probable", "Historial local",
                         "Historial visita", "Situación de equipos"], filas)
    hoja("Equipos", ["Equipo", "PJ", "G", "E", "P", "DG", "% victorias", "Pts por partido", "Jugadores"],
         [[e["equipo"], e["PJ"], e["G"], e["E"], e["P"], e["DG"], e["pct"], e["pts_pj"], ", ".join(e["jugadores"])]
          for e in dia["equipos"]])
    hoja("Jugadores", ["Jugador", "Ligas", "PJ", "G", "E", "P", "DG", "Pts por partido", "Mejor equipo", "Equipos"],
         [[j["jugador"], j["ligas"], j["PJ"], j["G"], j["E"], j["P"], j["DG"], j["pts_pj"], j["mejor_equipo"],
           ", ".join(j["equipos"])] for j in dia["jugadores"]])
    hoja("Patrones", ["Patrón", "Detalle", "p-valor", "Veredicto"],
         [[p["nombre"], p["detalle"], p["p"], p["veredicto"]] for p in dia["patrones"]])
    ruta.parent.mkdir(parents=True, exist_ok=True)
    wb.save(ruta)


# ================= PANEL WEB =================
class Panel:
    """Guarda cada recurso ya convertido a JSON (y comprimido) con un número de versión."""

    def __init__(self):
        self.lock = threading.Lock()
        self.recursos = {}
        self.log = []
        self.fase = "Iniciando"
        self.url_publica = None
        self.carpeta = None      # modo estático: cada recurso se guarda como archivo .json

    def _escribir(self, nombre, crudo):
        ruta = Path(self.carpeta) / "api" / f"{nombre}.json"
        ruta.parent.mkdir(parents=True, exist_ok=True)
        ruta.write_bytes(crudo)

    def publicar(self, nombre, obj):
        crudo = json.dumps(obj, default=_json_default, ensure_ascii=False, separators=(",", ":")).encode("utf-8")
        with self.lock:
            v = self.recursos.get(nombre, (0,))[0] + 1
            self.recursos[nombre] = (v, crudo, gzip.compress(crudo, 6))
        if self.carpeta:
            self._escribir(nombre, crudo)

    def obtener(self, nombre):
        with self.lock:
            return self.recursos.get(nombre)

    def avisar(self, msg):
        linea = f"{AHORA():%H:%M:%S}  {msg}"
        print(linea)
        with self.lock:
            self.log = (self.log + [linea])[-40:]
        if self.carpeta:
            self._escribir("log", json.dumps(self.log, ensure_ascii=False).encode("utf-8"))


def clave_panel():
    if os.environ.get("CLAVE_PANEL"):
        return os.environ["CLAVE_PANEL"].strip()
    ruta = Path(CARPETA_SALIDA) / "clave_panel.txt"
    if ruta.exists():
        c = ruta.read_text(encoding="utf-8").strip()
        if c:
            return c
    ruta.parent.mkdir(parents=True, exist_ok=True)
    c = secrets.token_urlsafe(9)
    ruta.write_text(c, encoding="utf-8")
    return c


def ip_local():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except Exception:
        return "127.0.0.1"


def iniciar_servidor(panel, puerto, clave):
    class Manejador(BaseHTTPRequestHandler):
        protocol_version = "HTTP/1.1"

        def _enviar(self, codigo, cuerpo=b"", tipo="application/json; charset=utf-8", extra=None):
            gz = False
            if cuerpo and len(cuerpo) > 800 and "gzip" in (self.headers.get("Accept-Encoding") or ""):
                if not isinstance(cuerpo, tuple):
                    cuerpo = (cuerpo, gzip.compress(cuerpo, 6))
            if isinstance(cuerpo, tuple):
                gz = "gzip" in (self.headers.get("Accept-Encoding") or "")
                cuerpo = cuerpo[1] if gz else cuerpo[0]
            try:
                self.send_response(codigo)
                self.send_header("Content-Type", tipo)
                self.send_header("Content-Length", str(len(cuerpo)))
                self.send_header("Cache-Control", "no-store")
                if gz:
                    self.send_header("Content-Encoding", "gzip")
                for k, v in (extra or {}).items():
                    self.send_header(k, v)
                self.end_headers()
                if cuerpo:
                    self.wfile.write(cuerpo)
            except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError):
                pass

        def do_GET(self):
            u = urlparse(self.path)
            q = parse_qs(u.query)
            if u.path == "/salud":            # para servicios que mantienen despierto el servidor
                self._enviar(200, b"ok", "text/plain")
                return
            cookie = self.headers.get("Cookie") or ""
            autorizado = f"k={clave}" in cookie
            if q.get("k", [""])[0] == clave:
                self._enviar(302, b"", "text/plain", {"Location": "/", "Set-Cookie":
                             f"k={clave}; Path=/; Max-Age=31536000; SameSite=Lax"})
                return
            if not autorizado:
                self._enviar(401, PAGINA_CLAVE, "text/html; charset=utf-8")
                return
            if u.path in ("/", "/index.html"):
                self._enviar(200, PANEL_HTML_BYTES, "text/html; charset=utf-8")
                return
            if u.path.startswith("/api/"):
                nombre = u.path[5:]
                if nombre == "log":
                    with panel.lock:
                        self._enviar(200, json.dumps(panel.log, ensure_ascii=False).encode("utf-8"))
                    return
                r = panel.obtener(nombre)
                if r is None:
                    self._enviar(404, b"{}")
                    return
                if q.get("v", [""])[0] == str(r[0]):
                    self._enviar(304)
                    return
                self._enviar(200, (r[1], r[2]), extra={"X-Version": str(r[0])})
                return
            self._enviar(404, b"")

        def log_message(self, *a):
            pass

    srv = None
    for p in range(puerto, puerto + 10):
        try:
            srv = ThreadingHTTPServer(("0.0.0.0", p), Manejador)
            break
        except OSError:
            continue
    if srv is None:
        raise SystemExit(f"No pude abrir el panel en los puertos {puerto}-{puerto + 9}.")
    srv.daemon_threads = True
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return srv.server_address[1]


def tema_ntfy():
    ruta = Path(CARPETA_SALIDA) / "ntfy_tema.txt"
    if ruta.exists() and ruta.read_text(encoding="utf-8").strip():
        return ruta.read_text(encoding="utf-8").strip()
    ruta.parent.mkdir(parents=True, exist_ok=True)
    tema = "esports-" + secrets.token_hex(6)
    ruta.write_text(tema, encoding="utf-8")
    return tema


def enviar_ntfy(tema, enlace):
    """Manda el enlace al celular (app gratuita ntfy, suscrita al tema)."""
    try:
        req = urllib.request.Request(f"https://ntfy.sh/{tema}", data=enlace.encode("utf-8"), method="POST",
                                     headers={"Title": "Panel de pronosticos listo", "Click": enlace, "Tags": "soccer"})
        urllib.request.urlopen(req, timeout=15).read()
    except Exception:
        pass


def obtener_cloudflared(panel):
    exe = shutil.which("cloudflared")
    if exe:
        return exe
    sistema, maq = platform.system(), platform.machine().lower()
    arm = "arm" in maq or "aarch" in maq
    if sistema == "Windows":
        nombre, archivo = "cloudflared.exe", "cloudflared-windows-amd64.exe"
    elif sistema == "Linux":
        nombre, archivo = "cloudflared", "cloudflared-linux-arm64" if arm else "cloudflared-linux-amd64"
    else:
        return None
    destino = Path(CARPETA_SALIDA) / "bin" / nombre
    if destino.exists() and destino.stat().st_size > 1_000_000:
        return str(destino)
    destino.parent.mkdir(parents=True, exist_ok=True)
    url = f"https://github.com/cloudflare/cloudflared/releases/latest/download/{archivo}"
    panel.avisar("Descargando cloudflared para el enlace público (solo la primera vez, unos 30 MB)...")
    try:
        tmp = destino.with_suffix(".part")
        urllib.request.urlretrieve(url, str(tmp))
        os.replace(tmp, destino)
        if os.name != "nt":
            os.chmod(destino, 0o755)
        return str(destino)
    except Exception as e:
        panel.avisar(f"No pude descargar cloudflared ({type(e).__name__}); probaré otra vía.")
        return None


class Tunel:
    """Enlace público https que se mantiene solo: cloudflared (descarga automática) y, si falla,
    localhost.run por ssh. Si se cae, se reconecta y manda el nuevo enlace al celular."""

    def __init__(self, puerto, clave, panel, tema):
        self.puerto, self.clave, self.panel, self.tema = puerto, clave, panel, tema
        self.proc = None
        self.activo = True
        self.exe = None
        atexit.register(self.cerrar)
        threading.Thread(target=self._bucle, daemon=True).start()

    def cerrar(self):
        self.activo = False
        try:
            if self.proc:
                self.proc.terminate()
        except Exception:
            pass

    def _bucle(self):
        fallos_cf = fallos = 0
        while self.activo:
            if self.exe is None and fallos_cf < 3:
                self.exe = obtener_cloudflared(self.panel) or False
            if self.exe and fallos_cf < 3:
                ok = self._correr([self.exe, "tunnel", "--url", f"http://127.0.0.1:{self.puerto}", "--no-autoupdate"],
                                  r"https://[a-z0-9]+(?:-[a-z0-9]+)+\.trycloudflare\.com")
                fallos_cf = 0 if ok else fallos_cf + 1
            elif shutil.which("ssh"):
                ok = self._correr(["ssh", "-T", "-o", "StrictHostKeyChecking=no", "-o", "ServerAliveInterval=30",
                                   "-o", "ExitOnForwardFailure=yes", "-R", f"80:127.0.0.1:{self.puerto}",
                                   "nokey@localhost.run"], r"https://[a-z0-9-]+\.(?:lhr\.life|localhost\.run)")
                fallos_cf = 0 if ok else fallos_cf    # tras un éxito, vuelve a probar cloudflared
            else:
                self.panel.avisar("No pude crear el enlace público (cloudflared no conecta y no hay ssh); "
                                  "reintento en 10 minutos. El panel sigue funcionando en tu wifi.")
                for _ in range(600):
                    if not self.activo:
                        return
                    time.sleep(1)
                fallos_cf, self.exe = 0, None
                continue
            fallos = 0 if ok else fallos + 1
            if fallos >= 8:
                self.panel.avisar("El enlace público falló varias veces; reviso de nuevo en 10 minutos.")
                for _ in range(600):
                    if not self.activo:
                        return
                    time.sleep(1)
                fallos, fallos_cf = 0, 0
            time.sleep(10)

    def _correr(self, cmd, patron):
        flags = 0x08000000 if os.name == "nt" else 0
        try:
            self.proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                         text=True, encoding="utf-8", errors="replace", creationflags=flags)
        except Exception:
            return False
        encontrado = False
        for linea in self.proc.stdout:
            m = re.search(patron, linea)
            if m and not encontrado:
                encontrado = True
                enlace = f"{m.group(0)}/?k={self.clave}"
                self.panel.url_publica = enlace
                (Path(CARPETA_SALIDA) / "enlace_publico.txt").write_text(enlace, encoding="utf-8")
                self.panel.avisar(f"Enlace público (cualquier red): {enlace}")
                enviar_ntfy(self.tema, enlace)
            if not self.activo:
                break
        try:
            self.proc.wait(timeout=5)
        except Exception:
            pass
        if encontrado and self.activo:
            self.panel.url_publica = None
            self.panel.avisar("Se cayó el enlace público; creando uno nuevo...")
        return encontrado


# ================= BUCLE PRINCIPAL =================
_PANEL = None


def correr(args):
    global AHORA
    try:
        import sys
        sys.stdout.reconfigure(errors="replace")
    except Exception:
        pass
    bajar_prioridad()
    fecha = date.fromisoformat(args.fecha) if args.fecha else AHORA().date()
    if args.archivo:                  # en un backtest, "ahora" es el final de ese día
        fin_dia = datetime(fecha.year, fecha.month, fecha.day) + timedelta(days=1, hours=6)
        AHORA = lambda: fin_dia
    alm = cargar_sesion(fecha, args.nueva)
    historial = Historial(Path(CARPETA_SALIDA) / "historial.sqlite")
    if alm.registros:
        historial.guardar_registros(fecha, list(alm.registros.values()))

    def cargar_hist():
        desde = fecha - timedelta(days=args.dias_historial)
        alm.cargar_historial(historial.cargar_partidos(desde, fecha), historial.cargar_registros(desde, fecha))
    cargar_hist()
    motor = Motor(alm)
    global _PANEL
    if args.estatico:
        panel, clave, puerto = Panel(), "", None
        panel.carpeta = args.estatico
        Path(args.estatico).mkdir(parents=True, exist_ok=True)
        html = PANEL_HTML.replace("const ESTATICO = false;", "const ESTATICO = true;")
        html = html.replace('<meta name="theme-color" content="#1E4D3A">',
                            '<meta name="theme-color" content="#1E4D3A"><meta name="robots" content="noindex">')
        (Path(args.estatico) / "index.html").write_text(html, encoding="utf-8")
        (Path(args.estatico) / ".nojekyll").write_text("", encoding="utf-8")
        nuevo_panel = False
    elif _PANEL is None:
        panel = Panel()
        clave = clave_panel()
        puerto = iniciar_servidor(panel, args.puerto, clave)
        _PANEL = (panel, clave, puerto)
        nuevo_panel = True
    else:
        panel, clave, puerto = _PANEL
        nuevo_panel = False
    url_local = f"http://localhost:{puerto}/?k={clave}"
    if args.estatico:
        print(f"Modo estático: el panel se genera en la carpeta {args.estatico}.")
    elif args.servidor:
        if nuevo_panel:
            print(f"Panel escuchando en el puerto {puerto}. Ábrelo con la dirección pública del servidor.")
    else:
        print("\nPanel:")
        print(f"  En este computador:     {url_local}")
        print(f"  En tu wifi (celular):   http://{ip_local()}:{puerto}/?k={clave}")
    tema = tema_ntfy()
    panel.ntfy = tema
    if not args.sin_tunel and not args.archivo and not args.servidor and not args.estatico:
        Tunel(puerto, clave, panel, tema)
        panel.tunel = True
        print("  Desde cualquier red:    el enlace aparece en unos segundos aquí, en el panel y en")
        print(f"                          salidas/enlace_publico.txt. Para recibirlo en el celular instala la app")
        print(f"                          ntfy y suscríbete al tema  {tema}  (o abre https://ntfy.sh/{tema}).")
    print()
    if not args.sin_abrir and not args.servidor and not args.estatico:
        webbrowser.open(url_local)

    fotos = {}
    ultimo = {"dia": 0.0, "excel": time.time(), "regs_dia": -1, "regs_excel": len(alm.registros)}

    def fase(texto):
        panel.fase = texto

    def publicar(forzar_dia=False):
        r = resumen(alm, motor, fotos, panel.fase, panel.url_publica)
        r["ntfy"] = getattr(panel, "ntfy", None) if getattr(panel, "tunel", False) else None
        r["tunel"] = getattr(panel, "tunel", False)
        r["historial"] = dict(historial.totales(), cargados=len(alm.hist_lista))
        panel.publicar("resumen", r)
        n = len(alm.registros)
        if forzar_dia or (n != ultimo["regs_dia"] and time.time() - ultimo["dia"] > 60):
            panel.publicar("dia", analisis_dia(alm, motor))
            ultimo["dia"], ultimo["regs_dia"] = time.time(), n

    def refrescar_fotos(ids):
        for i in ids:
            if alm.ligas[i]["partidos"]:
                fotos[i] = foto_liga(alm, motor, i)
                panel.publicar("liga/" + i, fotos[i])

    if alm.ligas:
        fase("Cargando lo guardado de hoy")
        refrescar_fotos(list(alm.ligas))
        publicar(forzar_dia=True)

    if args.archivo:
        fuente = FuenteArchivos(args.archivo, fecha)
    elif args.servidor or args.sin_navegador or args.estatico:
        fuente = ExtractorHTTP(panel, fecha)
    else:
        fuente = Extractor(panel, fecha, solo_html=args.solo_html, visible=args.ver_navegador)
    ruta_db = Path(CARPETA_SALIDA) / "historial.sqlite"
    fase("Abriendo el sitio en segundo plano")
    publicar()
    fuente.abrir()
    vigia = None
    try:
        # ---- 1) lista de ligas y aprendizaje de la API ----
        fase("Leyendo la lista de ligas del día")
        publicar()
        nuevas = alm.registrar_ligas(fuente.listar())
        ultimo_listado = time.time()
        panel.avisar(f"{len(alm.ligas)} ligas en la lista de hoy.")
        fuente.aprender(alm.ligas_ordenadas())
        if getattr(fuente, "diag", None):
            ruta = carpeta_dia(fecha) / "diagnostico.json"
            ruta.parent.mkdir(parents=True, exist_ok=True)
            ruta.write_text(json.dumps(dict(fuente.diag, http_directo=getattr(fuente, "http_ok", None)),
                                       ensure_ascii=False, indent=1, default=str), encoding="utf-8")

        # ---- 2) historial: descargar días que falten (en paralelo) ----
        if hasattr(fuente, "descargar_dia") and args.dias_historial > 0:
            t_h, bajados = time.time(), 0
            faltan = [fecha - timedelta(days=d) for d in range(args.dias_historial, 0, -1)
                      if not historial.dia_completo(fecha - timedelta(days=d))]
            for n, dia in enumerate(faltan, 1):
                fase(f"Descargando resultados reales: día {n} de {len(faltan)} ({dia:%d/%m})")
                publicar()
                res = fuente.descargar_dia(dia)
                if res is None:
                    panel.avisar("Los días anteriores no se pueden descargar sin la API; "
                                 "el historial se irá llenando con cada día que corras el script.")
                    break
                historial.guardar_partidos(dia, res[0], res[1])
                historial.marcar_dia(dia, len(res[0]), len(res[1]))
                bajados += len(res[1])
            if bajados:
                panel.avisar(f"Historial: {bajados} resultados de {len(faltan)} días descargados en {time.time() - t_h:.0f} s.")
        cargar_hist()

        # ---- 3) ajustar parámetros y analizar días anteriores en varios núcleos ----
        if AUTOAJUSTE and not args.sin_autoajuste:
            autoajustar(alm, panel, fecha)
        if not args.sin_analisis_historial:
            fase("Analizando días anteriores en paralelo")
            publicar()
            t_a = time.time()
            if analizar_dias_pasados(historial, ruta_db, fecha, args.dias_historial, panel, args.procesos):
                panel.avisar(f"Análisis del historial terminado en {time.time() - t_a:.0f} s.")
                cargar_hist()
        info = motor.entrenar_meta()
        panel.avisar(f"Meta-modelo: {info.get('estado')}"
                     + (f" (mejora de log-loss {info['mejora']:+.3f} frente al ensamble)" if info.get("mejora") is not None else ""))

        # ---- 4) seguimiento en vivo ----
        fin_desde, primera = None, True
        ultimo_barrido = ultimo_otras = 0.0
        if fuente.puede_vigilar() and not args.archivo and not args.estatico:
            vigia = Vigia(fuente)
            panel.avisar(f"Marcadores en vivo cada {VIGIA_SEG} s (lectura directa de la API).")
        elif not args.archivo and not args.estatico:
            panel.avisar(f"Sin API directa: las ligas en juego se leen cada {REFRESCO_SEG} s.")
        while True:
            ahora = AHORA()
            if time.time() - ultimo_listado > REFRESCO_LISTA_MIN * 60:
                nuevas = alm.registrar_ligas(fuente.listar())
                ultimo_listado = time.time()
                if nuevas:
                    panel.avisar(f"{nuevas} ligas nuevas en la lista (total {len(alm.ligas)}).")

            # qué ligas seguir
            objetivo, sin_leer = [], []
            for L in alm.ligas_ordenadas():
                if L["estado"] in ("terminada", "incompleta"):
                    continue
                if not L["consultada"]:
                    if L.get("dt") is None or L["dt"] <= ahora + timedelta(hours=3):
                        sin_leer.append(L)
                    continue
                if L.get("dt") is None or L["dt"] <= ahora + timedelta(minutes=10):
                    if (L["dt"] and L["dt"] < ahora - timedelta(minutes=30) and L.get("ult_cambio")
                            and time.time() - L["ult_cambio"] > SIN_CAMBIOS_MAX_MIN * 60):
                        L["estado"] = "incompleta"
                        panel.avisar(f"Liga {L.get('num')} ({L['nombre']}) sin cambios hace {SIN_CAMBIOS_MAX_MIN} min: dejo de consultarla.")
                        continue
                    objetivo.append(L)
            a_leer = list(sin_leer)
            if vigia:
                vigia.fijar(objetivo)
                if time.time() - ultimo_barrido > 60:          # barrido de seguridad cada minuto
                    a_leer += objetivo
                    ultimo_barrido = time.time()
            elif time.time() - ultimo_barrido >= REFRESCO_SEG or primera:
                a_leer += objetivo
                ultimo_barrido = time.time()

            cambiadas = set()
            if a_leer:
                if len(a_leer) > 3:
                    fase(f"Leyendo {len(a_leer)} ligas")
                    publicar()

                def prog_lectura(n, tot):
                    fase(f"Leyendo ligas: {n} de {tot}")
                    if n % 5 == 0:
                        publicar()
                for lid, (lista, nombre) in fuente.partidos_varios(a_leer, prog_lectura).items():
                    if lista is None:
                        continue
                    L = alm.ligas[lid]
                    if L.get("ult_cambio") is None:
                        L["ult_cambio"] = time.time()
                    if alm.actualizar(lid, lista, nombre):
                        cambiadas.add(lid)
            if vigia:
                while True:
                    try:
                        lid, lista = vigia.cola.get_nowait()
                    except queue.Empty:
                        break
                    if lid in alm.ligas and alm.actualizar(lid, lista):
                        cambiadas.add(lid)

            nuevos = []
            if cambiadas or primera:
                def progreso(i, n):
                    fase(f"Poniéndose al día: {i} de {n} partidos verificados")
                    if i % 50 == 0 or i == n:
                        publicar()
                nuevos = motor.verificar(progreso)
                if nuevos:
                    historial.guardar_registros(fecha, nuevos)
                    ok = sum(1 for r in nuevos if mejor_de(r["m"][r["usado"]]) == r["salida"])
                    panel.avisar(f"{len(nuevos)} resultados nuevos verificados ({ok} acertados en 1X2).")
                    cambiadas |= {r["liga"] for r in nuevos}
                if cambiadas:
                    historial.guardar_partidos(fecha, {i: alm.ligas[i]["nombre"] for i in cambiadas},
                                               [p for i in cambiadas for p in alm.partidos_de(i)])
                if len(alm.registros_ordenados()) - motor._n_meta >= 300:
                    motor.entrenar_meta()
                # primero la liga que cambió (rápido); las demás, como mucho una vez por minuto
                refrescar_fotos(cambiadas)
                if nuevos and time.time() - ultimo_otras > 60:
                    refrescar_fotos({L["id"] for L in alm.ligas.values() if L["estado"] in ("en juego", "próxima")
                                     and L["consultada"] and L["id"] not in cambiadas})
                    ultimo_otras = time.time()
                en_juego = sum(1 for L in alm.ligas.values() if L["estado"] == "en juego")
                if args.estatico:
                    fase(f"{en_juego} ligas en juego. Se actualiza cada 10 a 15 minutos.")
                else:
                    fase(f"En vivo: {en_juego} ligas en juego." if not args.archivo else "Backtest terminado")
                publicar(forzar_dia=primera or len(nuevos) > 20)
                guardar_sesion(alm)
            elif int(time.time()) % 15 == 0:
                publicar()       # mantener la hora del panel al día
            if (len(alm.registros) != ultimo["regs_excel"] and time.time() - ultimo["excel"] > EXCEL_CADA_MIN * 60):
                try:
                    guardar_excel(alm, analisis_dia(alm, motor), carpeta_dia(fecha) / "resumen_dia.xlsx")
                    ultimo["excel"], ultimo["regs_excel"] = time.time(), len(alm.registros)
                except PermissionError:
                    panel.avisar("No pude actualizar resumen_dia.xlsx: ciérralo en Excel.")
            primera = False
            if args.archivo or args.estatico:
                break
            pendientes = [L for L in alm.ligas.values() if L["estado"] not in ("terminada", "incompleta")]
            if args.servidor:
                if AHORA().date() > fecha and not pendientes:
                    historial.marcar_dia(fecha, len(alm.ligas), sum(1 for p in alm.partidos.values() if p["terminado"]))
                    panel.avisar("Terminó el día; paso al siguiente.")
                    break
                if AHORA().date() > fecha + timedelta(days=1):
                    break
            elif pendientes:
                fin_desde = None
            else:
                fin_desde = fin_desde or time.time()
                if time.time() - fin_desde > FIN_DIA_SIN_LIGAS_MIN * 60:
                    historial.marcar_dia(fecha, len(alm.ligas), sum(1 for p in alm.partidos.values() if p["terminado"]))
                    panel.avisar("No quedan ligas por jugar: terminó el día.")
                    break
            time.sleep(1)
    except KeyboardInterrupt:
        panel.avisar("Detenido. Lo analizado queda guardado; al volver a abrirlo hoy sigue desde aquí.")
        if args.servidor:
            raise
    finally:
        if vigia:
            vigia.activo = False
        fuente.cerrar()
        guardar_sesion(alm)

    dia = analisis_dia(alm, motor)
    panel.publicar("dia", dia)
    if args.estatico:
        en_juego = sum(1 for L in alm.ligas.values() if L["estado"] == "en juego")
        fase(f"{en_juego} ligas en juego. Se actualiza cada 10 a 15 minutos.")
    else:
        fase("Día terminado. Puedes revisar todas las ligas.")
    publicar()
    try:
        guardar_excel(alm, dia, carpeta_dia(fecha) / "resumen_dia.xlsx")
        print(f"Excel del día: {carpeta_dia(fecha) / 'resumen_dia.xlsx'}")
        if args.estatico:
            shutil.copy(carpeta_dia(fecha) / "resumen_dia.xlsx", Path(args.estatico) / "resumen_dia.xlsx")
    except PermissionError:
        print("No pude guardar resumen_dia.xlsx: ciérralo en Excel.")
    print("\nConclusiones del día:")
    for c in dia["conclusiones"]:
        print(" -", c)
    if args.servidor or args.estatico:
        return
    if not args.salir_al_final:
        print(f"\nEl panel sigue disponible ({url_local}). Ctrl+C para salir.")
        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            pass


def main():
    ap = argparse.ArgumentParser(description="Pronósticos de todas las ligas del día de ESportsBattle Football")
    ap.add_argument("--archivo", nargs="+", help="páginas HTML guardadas, una por liga (backtest)")
    ap.add_argument("--fecha", help="día a analizar AAAA-MM-DD (por defecto hoy)")
    ap.add_argument("--puerto", type=int, default=PUERTO_PANEL)
    ap.add_argument("--nueva", action="store_true", help="ignora lo guardado de hoy")
    ap.add_argument("--solo-html", action="store_true", help="no usar la API; leer cada página")
    ap.add_argument("--ver-navegador", action="store_true", help="mostrar el navegador (depuración)")
    ap.add_argument("--sin-tunel", action="store_true", help="no crear enlace público")
    ap.add_argument("--sin-abrir", action="store_true", help="no abrir el panel al iniciar")
    ap.add_argument("--salir-al-final", action="store_true", help="cerrar el panel al terminar")
    ap.add_argument("--dias-historial", type=int, default=DIAS_HISTORIAL,
                    help="días anteriores de resultados reales que se usan (por defecto 14)")
    ap.add_argument("--sin-autoajuste", action="store_true", help="no ajustar parámetros automáticamente")
    ap.add_argument("--sin-analisis-historial", action="store_true", help="no analizar los días anteriores")
    ap.add_argument("--procesos", type=int, default=None, help="núcleos para analizar el historial")
    ap.add_argument("--sin-navegador", action="store_true", help="usar solo la API (sin Chrome)")
    ap.add_argument("--estatico", metavar="CARPETA",
                    help="una pasada y genera el panel como página estática en CARPETA (GitHub Pages)")
    ap.add_argument("--servidor", action="store_true",
                    help="modo servidor en la nube: sin navegador, sin túnel, corre todos los días sin parar")
    args = ap.parse_args()
    if os.environ.get("MODO_SERVIDOR") == "1":
        args.servidor = True
    if not args.servidor:
        correr(args)
        return
    while True:                      # un día tras otro, sin detenerse
        try:
            args.fecha, args.nueva = None, False
            correr(args)
        except KeyboardInterrupt:
            break
        except Exception as e:
            print(f"Error inesperado: {type(e).__name__}: {e}. Reintento en 60 s.")
            time.sleep(60)


PANEL_HTML = r"""<!doctype html>
<html lang="es">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#1E4D3A">
<title>Pronósticos ESportsBattle</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Barlow+Condensed:wght@500;600;700&family=Barlow:wght@400;500;600&display=swap" rel="stylesheet">
<style>
:root{--fondo:#E8ECE4;--hoja:#F6F8F2;--tinta:#1B2A2F;--suave:#56656A;--linea:#CBD3C8;--cesped:#1E4D3A;
 --sobre:#F1F4EC;--ambar:#E3A72F;--local:#2F6F8E;--visita:#9A5B2E;--empate:#7C8794;--txtbarra:#fff;
 --bien:#2C7A4E;--mal:#B04436;color-scheme:light}
@media (prefers-color-scheme:dark){:root{--fondo:#141D1A;--hoja:#1B2723;--tinta:#E3E9E2;--suave:#9AA9A2;
 --linea:#2E3E38;--cesped:#0F3326;--sobre:#E3E9E2;--ambar:#F2B847;--local:#6FB0CF;--visita:#D9975F;
 --empate:#8B96A1;--txtbarra:#0F1A16;--bien:#5DBB86;--mal:#E07B6C;color-scheme:dark}}
*{box-sizing:border-box}
body{margin:0;background:var(--fondo);color:var(--tinta);font:15px/1.5 'Barlow',system-ui,sans-serif;
 padding-bottom:env(safe-area-inset-bottom)}
h1,h2,h3,th,.cifra,.tab,.kpi b{font-family:'Barlow Condensed','Arial Narrow',sans-serif}
header{background:var(--cesped);color:var(--sobre);padding:14px clamp(14px,4vw,36px) 12px;
 padding-top:max(14px,env(safe-area-inset-top));
 background-image:repeating-linear-gradient(90deg,transparent 0 90px,rgba(255,255,255,.035) 90px 180px)}
h1{margin:0;font-size:1.4rem;font-weight:600}
.fase{margin:2px 0 0;opacity:.85;font-size:.92rem}
.kpis{display:flex;flex-wrap:wrap;gap:4px 22px;margin-top:10px}
.kpi{display:flex;flex-direction:column}.kpi b{font-size:1.45rem;color:var(--ambar);line-height:1.1;font-weight:700}
.kpi span{font-size:.8rem;opacity:.85}
.enlace{margin-top:8px;font-size:.85rem;opacity:.9;word-break:break-all}
.enlace button{font:inherit;margin-left:6px;padding:2px 10px;border-radius:4px;border:1px solid var(--ambar);
 background:transparent;color:var(--sobre);cursor:pointer}
nav{position:sticky;top:0;z-index:5;display:flex;background:var(--hoja);border-bottom:1px solid var(--linea)}
.tab{flex:1;text-align:center;padding:10px 6px;font-size:1.08rem;font-weight:600;color:var(--suave);text-decoration:none;
 border-bottom:3px solid transparent}
.tab.on{color:var(--tinta);border-bottom-color:var(--ambar)}
a:focus-visible,button:focus-visible,input:focus-visible{outline:3px solid var(--ambar);outline-offset:2px}
main{padding:14px clamp(12px,3vw,32px) 40px;max-width:1400px;margin:0 auto}
h2{font-size:1.25rem;margin:18px 0 8px;font-weight:600}
h2:first-child{margin-top:4px}
.nota{color:var(--suave);font-size:.85rem;margin:-4px 0 8px}
.bloque{background:var(--hoja);border:1px solid var(--linea);border-radius:8px;padding:12px 14px;margin-bottom:14px}
.rejilla{display:grid;grid-template-columns:repeat(auto-fill,minmax(300px,1fr));gap:12px}
.dos{display:grid;grid-template-columns:minmax(0,1.6fr) minmax(0,1fr);gap:14px;align-items:start}
@media (max-width:900px){.dos{grid-template-columns:minmax(0,1fr)}}
.tarjeta{background:var(--hoja);border:1px solid var(--linea);border-radius:8px;padding:10px 12px}
.tarjeta.viva{border-color:var(--ambar)}
.liga-et{font-size:.8rem;color:var(--suave);display:flex;justify-content:space-between;gap:8px}
.duelo{display:grid;grid-template-columns:1fr auto 1fr;gap:8px;align-items:center;margin:6px 0}
.duelo .der{text-align:right}
.jug{font-weight:600;overflow-wrap:anywhere}.eq{display:block;font-size:.8rem;color:var(--suave)}
.cifra{font-size:1.9rem;font-weight:700;color:var(--ambar);font-variant-numeric:tabular-nums;line-height:1}
.barra{display:flex;height:18px;border-radius:4px;overflow:hidden;font-size:.72rem;font-weight:600;color:var(--txtbarra);min-width:120px}
.barra span{display:flex;align-items:center;justify-content:center;white-space:nowrap}
.barra .l{background:var(--local)}.barra .e{background:var(--empate)}.barra .v{background:var(--visita)}
.extra{font-size:.82rem;color:var(--suave);margin-top:5px}
.desliza{overflow-x:auto}
table{border-collapse:collapse;width:100%;font-variant-numeric:tabular-nums}
th{font-weight:600;text-align:left;color:var(--suave);font-size:.9rem;padding:6px 7px;border-bottom:1px solid var(--linea);white-space:nowrap}
td{padding:6px 7px;border-bottom:1px solid var(--linea);vertical-align:middle}
td small{display:block;color:var(--suave);font-size:.76rem}
.n{text-align:right}
tr.hecho td{color:var(--suave)} tr.hecho td b{color:var(--tinta)}
tr.jugando{background:color-mix(in srgb,var(--ambar) 15%,transparent)}
tr.anulado td{text-decoration:line-through;color:var(--suave)}
.ok{color:var(--bien);font-weight:700}.no{color:var(--mal);font-weight:700}
.filtros{display:flex;flex-wrap:wrap;gap:6px;align-items:center;margin-bottom:10px}
.chip{font:inherit;padding:5px 12px;border-radius:16px;border:1px solid var(--linea);background:var(--hoja);color:var(--tinta);cursor:pointer}
.chip.on{background:var(--cesped);color:var(--sobre);border-color:var(--cesped)}
.buscar{flex:1;min-width:160px;font:inherit;padding:6px 10px;border-radius:6px;border:1px solid var(--linea);background:var(--hoja);color:var(--tinta)}
.lista-ligas{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:8px}
.fila-liga{display:grid;grid-template-columns:3.2rem 1fr auto;gap:8px;align-items:center;padding:8px 10px;
 background:var(--hoja);border:1px solid var(--linea);border-radius:8px;color:inherit;text-decoration:none}
.fila-liga:hover{border-color:var(--suave)}
.fila-liga .h{font-family:'Barlow Condensed',sans-serif;font-size:1.15rem;font-weight:600}
.fila-liga .nom{font-weight:600;line-height:1.2;overflow-wrap:anywhere}
.fila-liga small{display:block;color:var(--suave);font-size:.78rem}
.estado{font-size:.75rem;padding:2px 8px;border-radius:10px;border:1px solid var(--linea);white-space:nowrap}
.estado.en.juego,.estado.vivo{border-color:var(--ambar);color:var(--tinta);background:color-mix(in srgb,var(--ambar) 20%,transparent)}
.estado.terminada{color:var(--suave)}
.volver{display:inline-block;margin-bottom:6px;color:var(--suave)}
.cab-liga h2{margin:0}.cab-liga p{margin:2px 0 10px;color:var(--suave)}
.prob{display:grid;grid-template-columns:minmax(5rem,8rem) 1fr 3rem;gap:8px;align-items:center;margin:4px 0}
.riel{background:var(--linea);border-radius:3px;height:9px}.riel i{display:block;height:9px;background:var(--ambar);border-radius:3px}
ul.lista{margin:0;padding-left:1.1rem}ul.lista li{margin:4px 0}
.vacio{color:var(--suave)}
.pick{display:block;margin-top:4px;font-size:.82rem;color:var(--tinta)}
.pick b{color:var(--bien)}
.prox{display:grid;grid-template-columns:3rem 1fr auto;gap:4px 8px;align-items:center;padding:8px 10px;background:var(--hoja);
 border:1px solid var(--linea);border-radius:8px;color:inherit;text-decoration:none}
.prox .h{font-family:'Barlow Condensed',sans-serif;font-size:1.1rem;font-weight:600}
.prox small{display:block;color:var(--suave);font-size:.76rem}.prox .b{grid-column:1/-1}
#estado-red{color:var(--mal);font-weight:600}
footer{max-width:1400px;margin:0 auto;padding:0 clamp(12px,3vw,32px) 30px;color:var(--suave);font-size:.84rem}
@media (prefers-reduced-motion:no-preference){.tarjeta.viva .cifra{animation:lat 2.4s ease-in-out infinite}}
@keyframes lat{50%{opacity:.6}}
</style>
</head>
<body>
<header>
 <h1>Pronósticos ESportsBattle</h1>
 <p class="fase"><span id="fase">Conectando…</span> <span id="estado-red"></span></p>
 <div class="kpis" id="kpis"></div>
 <div class="enlace" id="enlace"></div>
</header>
<nav aria-label="Secciones">
 <a class="tab" href="#ahora" data-v="ahora">Ahora</a>
 <a class="tab" href="#ligas" data-v="ligas">Ligas</a>
 <a class="tab" href="#dia" data-v="dia">Día</a>
</nav>
<main id="vista"><p class="vacio">Cargando…</p></main>
<footer><details><summary>Actividad del script</summary><ol id="log"></ol></details></footer>
<script>
const $ = s => document.querySelector(s);
const S = {vista: "ahora", liga: null, filtro: "todas", q: "", v: {}, d: {}};
const pct = x => x == null ? "–" : Math.round(x * 100) + "%";
const num = (x, d = 2) => x == null ? "–" : Number(x).toFixed(d);
const esc = s => String(s ?? "").replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const quien = (f, p) => { const m = Math.max(p.pa, p.pe, p.pb); return m === p.pa ? f.a : m === p.pb ? f.b : "Empate"; };

function leerHash() {
  const h = decodeURIComponent(location.hash.slice(1));
  if (h.startsWith("liga/")) { S.vista = "liga"; S.liga = h.slice(5); }
  else S.vista = ["ahora", "ligas", "dia"].includes(h) ? h : "ahora";
}
const ESTATICO = false;
async function traer(n) {
  if (ESTATICO) {
    const r = await fetch("api/" + n + ".json?t=" + Date.now(), {cache: "no-store"});
    if (!r.ok) throw new Error(r.status);
    const t = await r.text();
    if (S.v[n] === t.length + ":" + t.slice(-40)) return false;
    S.v[n] = t.length + ":" + t.slice(-40); S.d[n] = JSON.parse(t); return true;
  }
  const r = await fetch("/api/" + n + "?v=" + (S.v[n] || ""), {cache: "no-store"});
  if (r.status === 304) return false;
  if (!r.ok) throw new Error(r.status);
  S.d[n] = await r.json(); S.v[n] = r.headers.get("X-Version"); return true;
}
let ocupado = false;
async function ciclo(forzar) {
  if (ocupado || (document.hidden && !forzar)) return;
  ocupado = true;
  try {
    let c = await traer("resumen");
    if (S.vista === "liga" && S.liga) c = (await traer("liga/" + S.liga).catch(() => false)) || c;
    if (S.vista === "dia") c = (await traer("dia").catch(() => false)) || c;
    $("#estado-red").textContent = "";
    if (c || forzar) pintar();
  } catch (e) { $("#estado-red").textContent = "Sin conexión con el script."; }
  ocupado = false;
}
setInterval(ciclo, ESTATICO ? 60000 : 5000);
document.addEventListener("visibilitychange", () => { if (!document.hidden) ciclo(true); });
addEventListener("hashchange", () => { leerHash(); pintar(); ciclo(true); });
leerHash(); ciclo(true);
setInterval(async () => {
  if (document.hidden || !$("#log").closest("details").open) return;
  try { const l = await (await fetch(ESTATICO ? "api/log.json?t=" + Date.now() : "/api/log")).json(); $("#log").innerHTML = l.slice().reverse().map(x => `<li>${esc(x)}</li>`).join(""); } catch (e) {}
}, 6000);

function barra(p) {
  const t = x => x >= .15 ? pct(x) : "";
  return `<div class="barra" role="img" aria-label="Local ${pct(p.pa)}, empate ${pct(p.pe)}, visita ${pct(p.pb)}"><span class="l" style="width:${p.pa*100}%">${t(p.pa)}</span><span class="e" style="width:${p.pe*100}%">${t(p.pe)}</span><span class="v" style="width:${p.pb*100}%">${t(p.pb)}</span></div>`;
}
function pick(pk, conOk) {
  if (!pk) return "";
  const ok = conOk && pk.ok != null ? (pk.ok ? ' <span class="ok" aria-label="acierto">✓</span>' : ' <span class="no" aria-label="fallo">✗</span>') : "";
  return `<span class="pick">Más seguro: <b>${esc(pk.texto)}</b> ${pct(pk.p)}${ok}</span>`;
}
function mercado(mk) {
  if (!mk) return "";
  return `Más de ${mk.linea} goles ${pct(mk.over)}. Ambos marcan ${pct(mk.btts)}. Marcador probable ${esc(mk.marcador)}.`;
}

function pintar() {
  const R = S.d.resumen;
  document.querySelectorAll(".tab").forEach(t => t.classList.toggle("on", t.dataset.v === S.vista || (S.vista === "liga" && t.dataset.v === "ligas")));
  if (!R) return;
  $("#fase").textContent = R.fase + " Actualizado a las " + R.hora + ".";
  const k = R.kpi;
  $("#kpis").innerHTML = `<div class="kpi"><b>${k.terminadas}/${k.ligas}</b><span>ligas terminadas</span></div>
    <div class="kpi"><b>${k.en_juego}</b><span>en juego</span></div>
    <div class="kpi"><b>${pct(k.acierto)}</b><span>acierto en ${k.verificados} partidos</span></div>
    <div class="kpi"><b>${esc(R.modelo)}</b><span>modelo en uso</span></div>
    ${R.acierto_pick != null ? `<div class="kpi"><b>${pct(R.acierto_pick)}</b><span>acierto del mercado más seguro hoy</span></div>` : ""}
    ${R.historial ? `<div class="kpi"><b>${R.historial.partidos}</b><span>resultados reales en el historial (${R.historial.dias} días)</span></div>` : ""}`;
  $("#enlace").innerHTML = (R.url_publica ? `Enlace para cualquier red: ${esc(R.url_publica)} <button type="button" id="copiar">Copiar</button>` : (R.tunel ? "Creando el enlace para cualquier red…" : ""))
    + (R.ntfy ? `<br>Recibe el enlace en el celular: app ntfy, tema <b>${esc(R.ntfy)}</b>.` : "");
  const bc = $("#copiar"); if (bc) bc.onclick = () => navigator.clipboard.writeText(R.url_publica).then(() => bc.textContent = "Copiado");
  if (S.vista === "ahora") $("#vista").innerHTML = vistaAhora(R);
  else if (S.vista === "ligas") vistaLigas(R);
  else if (S.vista === "liga") $("#vista").innerHTML = S.d["liga/" + S.liga] ? vistaLiga(S.d["liga/" + S.liga]) : '<p class="vacio">Cargando la liga…</p>';
  else $("#vista").innerHTML = S.d.dia ? vistaDia(S.d.dia) : '<p class="vacio">Calculando el resumen…</p>';
}

function tarjeta(x) {
  const p = x.pron;
  return `<article class="tarjeta ${x.vivo ? "viva" : ""}">
    <div class="liga-et"><a href="#liga/${encodeURIComponent(x.liga)}">Liga ${x.num ?? ""}: ${esc(x.liga_nombre)}</a><span>${x.vivo ? "En juego" : esc(x.hora)}</span></div>
    <div class="duelo"><div><span class="jug">${esc(x.a)}</span><span class="eq">${esc(x.eq_a)}</span></div>
      <div class="cifra">${x.marcador_vivo ? x.marcador_vivo[0] + "–" + x.marcador_vivo[1] : "vs"}</div>
      <div class="der"><span class="jug">${esc(x.b)}</span><span class="eq">${esc(x.eq_b)}</span></div></div>
    ${barra(p)}
    <div class="extra">Pronóstico 1X2: <b>${esc(quien(x, p))}</b>, goles esperados ${num(p.la, 1)} a ${num(p.lb, 1)}. ${mercado(x.mk)}</div>
    ${pick(x.pick)}
  </article>`;
}

function vistaAhora(R) {
  let h = "";
  const c = R.confianza;
  if (c) {
    h += `<h2>Alta confianza</h2><p class="nota">En todo el historial, cuando el 1X2 da ${pct(c.umbral)} o más, acertó ${pct(c.acierto)} (${c.n} partidos).</p>`
      + (R.alta.length ? `<div class="rejilla">${R.alta.map(tarjeta).join("")}</div>` : `<p class="vacio">Ningún partido próximo llega a ese nivel de confianza ahora mismo.</p>`);
  }
  h += `<h2>En juego</h2>` + (R.en_vivo.length ? `<div class="rejilla">${R.en_vivo.map(tarjeta).join("")}</div>`
       : `<p class="vacio">No hay partidos en juego en este momento.</p>`);
  h += `<h2>Próximos partidos</h2>` + (R.proximos.length ? `<div class="rejilla">${R.proximos.map(x => `<a class="prox" href="#liga/${encodeURIComponent(x.liga)}">
      <span class="h">${esc(x.hora)}</span><span><b>${esc(x.a)}</b> vs <b>${esc(x.b)}</b><small>Liga ${x.num ?? ""}: ${esc(x.liga_nombre)}</small></span>
      <span class="n"><b>${esc(quien(x, x.pron))}</b><small>${x.mk ? "+" + x.mk.linea + ": " + pct(x.mk.over) : ""}</small></span>
      <span class="b">${barra(x.pron)}${pick(x.pick)}</span></a>`).join("")}</div>` : `<p class="vacio">Sin partidos programados por ahora.</p>`);
  h += `<h2>Últimos resultados</h2>` + (R.recientes.length ? `<div class="bloque desliza"><table><thead><tr><th>Hora</th><th>Partido</th><th>Pronóstico</th><th>Resultado</th></tr></thead><tbody>
    ${R.recientes.map(x => `<tr><td>${esc(x.hora)}</td><td><b>${esc(x.a)}</b> vs <b>${esc(x.b)}</b><small>Liga ${x.num ?? ""}: ${esc(x.liga_nombre)}</small></td>
      <td>${esc(quien(x, x.pron))}<small>${pct(Math.max(x.pron.pa, x.pron.pe, x.pron.pb))}</small></td>
      <td><b>${x.ga}–${x.gb}</b> ${x.ok ? '<span class="ok" aria-label="acierto">✓</span>' : '<span class="no" aria-label="fallo">✗</span>'}</td></tr>`).join("")}
    </tbody></table></div>` : `<p class="vacio">Aún no hay partidos verificados.</p>`);
  return h;
}

function vistaLigas(R) {
  if (!$("#lista-ligas")) {
    $("#vista").innerHTML = `<div class="filtros" role="group" aria-label="Filtrar ligas">
      ${[["todas","Todas"],["en juego","En juego"],["próxima","Próximas"],["terminada","Terminadas"]].map(([v,t]) =>
        `<button type="button" class="chip ${S.filtro === v ? "on" : ""}" data-f="${v}">${t}</button>`).join("")}
      <input class="buscar" type="search" placeholder="Buscar liga o jugador" aria-label="Buscar liga o jugador" value="${esc(S.q)}">
    </div><div id="lista-ligas" class="lista-ligas"></div>`;
    document.querySelectorAll(".chip").forEach(b => b.onclick = () => {
      S.filtro = b.dataset.f; document.querySelectorAll(".chip").forEach(c => c.classList.toggle("on", c === b)); listaLigas();
    });
    $(".buscar").oninput = e => { S.q = e.target.value; listaLigas(); };
  }
  listaLigas();
}
function listaLigas() {
  const R = S.d.resumen; if (!R) return;
  const q = S.q.trim().toLowerCase();
  let ls = R.ligas.filter(l => S.filtro === "todas" || l.estado === S.filtro || (S.filtro === "terminada" && l.estado === "incompleta"));
  if (q) ls = ls.filter(l => (l.nombre + " " + l.lider).toLowerCase().includes(q));
  const rango = {"en juego": 0, "próxima": 1, "terminada": 2, "incompleta": 2};
  if (S.filtro === "terminada") ls = ls.slice().reverse();
  else if (S.filtro === "todas") ls = ls.slice().sort((x, y) => (rango[x.estado] - rango[y.estado]) || (x.estado === "terminada" ? (y.num - x.num) : (x.num - y.num)));
  $("#lista-ligas").innerHTML = ls.length ? ls.map(l => `<a class="fila-liga" href="#liga/${encodeURIComponent(l.id)}">
      <span class="h">${esc(l.hora || "–")}</span>
      <span><span class="nom">${l.num ?? ""}. ${esc(l.nombre)}</span>
        <small>${l.n_fin}/${l.n_total} jugados${l.lider ? (l.estado === "terminada" ? ". Campeón: " : ". Líder: ") + esc(l.lider) : ""}${l.n_ver ? ". Acierto " + pct(l.acierto) : ""}</small></span>
      <span class="estado ${l.estado}">${esc(l.estado)}</span></a>`).join("") : '<p class="vacio">Ninguna liga coincide con el filtro.</p>';
}

function filaPartido(f) {
  const cls = f.anulado ? "anulado" : f.vivo ? "jugando" : f.fin ? "hecho" : "";
  let res = "";
  if (f.fin) res = `<b>${f.ga}–${f.gb}</b> ${f.ok === true ? '<span class="ok" aria-label="acierto">✓</span>' : f.ok === false ? '<span class="no" aria-label="fallo">✗</span>' : ""}${f.ca != null ? `<small>esquinas ${f.ca}–${f.cb}</small>` : ""}`;
  else if (f.vivo) res = `En juego${f.marcador_vivo ? " " + f.marcador_vivo[0] + "–" + f.marcador_vivo[1] : ""}`;
  else if (f.anulado) res = esc(f.estado);
  const p = f.pron;
  return `<tr class="${cls}"><td>${esc(f.hora)}</td><td><b>${esc(f.a)}</b><small>${esc(f.eq_a)}</small></td><td><b>${esc(f.b)}</b><small>${esc(f.eq_b)}</small></td>
    <td>${p ? barra(p) : '<small>sin pronóstico</small>'}</td>
    <td>${p ? esc(quien(f, p)) + `<small>${num(p.la, 1)}–${num(p.lb, 1)}${f.mk ? ", +" + f.mk.linea + ": " + pct(f.mk.over) : ""}</small>` : ""}${pick(f.pick, true)}</td><td>${res}</td></tr>`;
}

function vistaLiga(L) {
  const top = L.tabla[0];
  const sub = L.estado === "terminada" && top ? `Campeón: ${esc(top.j)} con ${top.Pts} puntos (${esc(top.eq)}).`
    : `${L.n_fin} de ${L.n_total} partidos jugados.`;
  let h = `<a class="volver" href="#ligas">Volver a la lista de ligas</a>
   <div class="cab-liga"><h2>Liga ${L.num ?? ""}: ${esc(L.nombre)}</h2><p>${esc(L.hora)}. ${sub} Acierto ${L.evaluados ? pct(L.aciertos / L.evaluados) + " en " + L.evaluados + " partidos" : "sin datos aún"}. Modelo: ${esc(L.modelo)}.</p></div>`;
  h += `<div class="dos"><section class="bloque"><h2>Partidos</h2><p class="nota">Cada pronóstico usa solo lo jugado antes de su hora.</p>
    <div class="desliza"><table><thead><tr><th>Hora</th><th>Local</th><th>Visita</th><th>Local, empate, visita</th><th>Pronóstico</th><th>Resultado</th></tr></thead>
    <tbody>${L.filas.map(filaPartido).join("")}</tbody></table></div></section><div>`;
  h += `<section class="bloque"><h2>Clasificación</h2><div class="desliza"><table><thead><tr><th class="n">#</th><th>Jugador</th><th class="n">PJ</th><th class="n">G</th><th class="n">E</th><th class="n">P</th><th class="n">DG</th><th class="n">Pts</th></tr></thead><tbody>
    ${L.tabla.map((t, i) => `<tr><td class="n">${i + 1}</td><td><b>${esc(t.j)}</b><small>${esc(t.eq)}</small></td><td class="n">${t.PJ}</td><td class="n">${t.G}</td><td class="n">${t.E}</td><td class="n">${t.P}</td><td class="n">${t.GF - t.GC}</td><td class="n"><b>${t.Pts}</b></td></tr>`).join("")}
    </tbody></table></div></section>`;
  if (L.campeon) h += `<section class="bloque"><h2>Probabilidad de ser campeón</h2>${L.campeon.map(c => `<div class="prob"><span>${esc(c.j)}</span><div class="riel"><i style="width:${c.p * 100}%"></i></div><span class="n">${pct(c.p)}</span></div>`).join("")}</section>`;
  h += `<section class="bloque"><h2>Validación de fechas</h2>${L.alertas.length ? `<ul class="lista">${L.alertas.map(a => `<li>${esc(a)}</li>`).join("")}</ul>` : '<p class="vacio">Horas coherentes.</p>'}</section></div></div>`;
  return h;
}

function tabla(cab, filas) {
  return `<div class="desliza"><table><thead><tr>${cab.map(c => `<th class="${c[1] || ""}">${c[0]}</th>`).join("")}</tr></thead><tbody>
    ${filas.map(f => `<tr>${f.map((v, i) => `<td class="${cab[i][1] || ""}">${v}</td>`).join("")}</tr>`).join("")}</tbody></table></div>`;
}
function grupos(lst) {
  return tabla([["Grupo"], ["Partidos", "n"], ["Acierto", "n"], ["", ""], ["Log-loss", "n"]],
    lst.map(g => [esc(g.grupo), g.n, pct(g.acierto), `<div class="riel" style="min-width:80px"><i style="width:${(g.acierto || 0) * 100}%"></i></div>`, num(g.logloss, 3)]));
}
function vistaDia(D) {
  let h = `<section class="bloque"><h2>Conclusiones</h2><ul class="lista">${D.conclusiones.map(c => `<li>${esc(c)}</li>`).join("")}</ul></section>`;
  if (!D.n) return h;
  h += `<div class="dos"><div>`;
  h += `<section class="bloque"><h2>Modelos</h2><p class="nota">Ordenados por log-loss (menor es mejor; mide qué tan buenas son las probabilidades).</p>
    ${tabla([["Modelo"], ["Partidos", "n"], ["Acierto", "n"], ["Log-loss", "n"], ["RPS", "n"]], D.modelos.map(m => [esc(m.modelo), m.n, pct(m.acierto), num(m.logloss, 3), num(m.rps, 3)]))}</section>`;
  h += `<section class="bloque"><h2>Precisión por bloque de ligas</h2><p class="nota">Ligas numeradas por hora de inicio.</p>${grupos(D.por_bloque)}</section>`;
  h += `<section class="bloque"><h2>Precisión por hora</h2>${grupos(D.por_hora)}</section>`;
  h += `<section class="bloque"><h2>Equipos del día</h2>${tabla([["Equipo"], ["PJ", "n"], ["G", "n"], ["E", "n"], ["P", "n"], ["DG", "n"], ["Pts/PJ", "n"]],
    D.equipos.slice(0, 25).map(e => [`<b>${esc(e.equipo)}</b><small>${esc(e.jugadores.join(", "))}</small>`, e.PJ, e.G, e.E, e.P, e.DG, num(e.pts_pj)]))}</section>`;
  h += `</div><div>`;
  h += `<section class="bloque"><h2>Según historial de los jugadores</h2>${grupos(D.por_hist)}</section>`;
  h += `<section class="bloque"><h2>Según el equipo usado</h2>${grupos(D.por_equipo)}</section>`;
  const mk = D.mercados;
  if (D.por_confianza && D.por_confianza.length) h += `<section class="bloque"><h2>Acierto según la confianza</h2><p class="nota">Partidos cuyo 1X2 más probable supera cada nivel.</p>
    ${tabla([["Confianza"], ["Historial", "n"], ["Acierto", "n"], ["Hoy", "n"], ["Acierto hoy", "n"]], D.por_confianza.map(c => [c.desde, c.n_hist, pct(c.acierto_hist), c.n_hoy, pct(c.acierto_hoy)]))}</section>`;
  h += `<section class="bloque"><h2>Otros mercados</h2><ul class="lista"><li>Mercado más seguro de cada partido: ${pct(mk.pick)}</li><li>Doble oportunidad del favorito: ${pct(mk.doble)}</li><li>Más/menos goles: ${pct(mk.over)} de acierto</li><li>Ambos marcan: ${pct(mk.btts)}</li><li>Marcador exacto: ${pct(mk.marcador)}</li><li>Media de goles por partido: ${num(mk.goles_medios, 1)}</li></ul></section>`;
  h += `<section class="bloque"><h2>Calibración</h2><p class="nota">Si el modelo está bien calibrado, las dos columnas se parecen.</p>
    ${tabla([["Probabilidad dada"], ["Media", "n"], ["Ocurrió", "n"], ["Casos", "n"]], D.calibracion.map(c => [c.rango, pct(c.predicho), pct(c.real), c.n]))}</section>`;
  h += `<section class="bloque"><h2>Patrones</h2>${D.patrones.length ? `<ul class="lista">${D.patrones.map(p => `<li><b>${esc(p.nombre)}</b>: ${esc(p.detalle)} (p = ${num(p.p, 3)}, ${esc(p.veredicto)})</li>`).join("")}</ul>` : '<p class="vacio">Hacen falta al menos 20 partidos.</p>'}</section>`;
  h += `<section class="bloque"><h2>Jugadores del día</h2>${tabla([["Jugador"], ["Ligas", "n"], ["PJ", "n"], ["Pts/PJ", "n"], ["Mejor equipo"]],
    D.jugadores.slice(0, 40).map(j => [`<b>${esc(j.jugador)}</b><small>${esc(j.equipos.join(", "))}</small>`, j.ligas, j.PJ, num(j.pts_pj), esc(j.mejor_equipo)]))}</section>`;
  return h + `</div></div>`;
}
</script>
</body>
</html>
"""
PAGINA_CLAVE = """<!doctype html><html lang="es"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1"><title>Pronósticos ESportsBattle</title>
<style>body{margin:0;min-height:100vh;display:grid;place-items:center;background:#1E4D3A;color:#F1F4EC;
font:16px/1.5 system-ui,sans-serif}form{display:flex;flex-direction:column;gap:10px;width:min(90vw,320px)}
h1{font-size:1.3rem;margin:0 0 6px}input,button{font:inherit;padding:10px 12px;border-radius:6px;border:1px solid #E3A72F}
input{background:#0F3326;color:#F1F4EC}button{background:#E3A72F;color:#1B2A2F;font-weight:600;cursor:pointer}
</style></head><body><form method="get" action="/"><h1>Pronósticos ESportsBattle</h1>
<label for="k">Clave del panel</label><input id="k" name="k" type="password" autocomplete="current-password" required>
<button type="submit">Entrar</button></form></body></html>""".encode("utf-8")
_HTML_CRUDO = PANEL_HTML.encode("utf-8")
PANEL_HTML_BYTES = (_HTML_CRUDO, gzip.compress(_HTML_CRUDO, 9))


if __name__ == "__main__":
    main()
