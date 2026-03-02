#!/usr/bin/env python3
"""
WhisperFlow — персональный голосовой ввод для macOS.
Ctrl+Shift+Space → диктовка → текст вставляется в любое поле ввода.
Groq API (Whisper + Llama) через sing-box прокси.
"""

import base64
import collections
import ctypes
import ctypes.util
import io
import json
import math
import os
import re
import subprocess
import threading
import time
import urllib.parse
import urllib.request
import wave
from pathlib import Path

import numpy as np
import objc
import sounddevice as sd
from AppKit import (
    NSAlert,
    NSAlertFirstButtonReturn,
    NSAnimationContext,
    NSApp,
    NSApplication,
    NSBackingStoreBuffered,
    NSBezierPath,
    NSColor,
    NSEvent,
    NSEventMaskKeyDown,
    NSMakeRect,
    NSMakePoint,
    NSObject,
    NSScreen,
    NSTextField,
    NSView,
    NSWindow,
    NSWindowCollectionBehaviorCanJoinAllSpaces,
    NSWindowCollectionBehaviorStationary,
    NSWindowStyleMaskBorderless,
)
from Foundation import NSLog, NSTimer
import Quartz
from groq import Groq

# ── Constants ───────────────────────────────────────────────────────

CONFIG_DIR = Path.home() / ".config" / "whisperflow"
CONFIG_FILE = CONFIG_DIR / "config.json"
SINGBOX_CONFIG = CONFIG_DIR / "singbox.json"
SAMPLE_RATE = 16000
MIN_DURATION_SEC = 0.5
SPACE_KEYCODE = 49
ESCAPE_KEYCODE = 53
MOD_FN = 1 << 23
LOCAL_PROXY_PORT = 10808

NUM_BARS = 28
IDLE_W, IDLE_H = 54, 5
REC_W, REC_H = 210, 38
CIRCLE_D = 36
BOTTOM_Y = 85

DEFAULT_CONFIG = {
    "groq_api_key": "",
    "proxy_sub_url": "",
    "language": "ru",
    "post_processing": True,
}

CLEANUP_SYSTEM_PROMPT = (
    "You are a text cleanup assistant. You receive raw speech transcriptions "
    "and clean them up: fix punctuation, capitalization, remove filler words "
    "(um, uh, like, you know, ну, типа, вот, короче, как бы, это самое, э, эм). "
    "Keep the original meaning and language. Output ONLY the cleaned text."
)


# ── Config ──────────────────────────────────────────────────────────

def load_config():
    cfg = dict(DEFAULT_CONFIG)
    if CONFIG_FILE.exists():
        with open(CONFIG_FILE) as f:
            cfg.update(json.load(f))
    return cfg


def save_config(cfg):
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    with open(CONFIG_FILE, "w") as f:
        json.dump(cfg, f, indent=2, ensure_ascii=False)


# ── Proxy (sing-box) ───────────────────────────────────────────────

def decode_subscription(url):
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "WhisperFlow/1.0"})
        with urllib.request.urlopen(req, timeout=10) as resp:
            raw = resp.read()
        decoded = base64.b64decode(raw).decode("utf-8", errors="ignore")
        return [l.strip() for l in decoded.splitlines() if l.strip()]
    except Exception as e:
        NSLog(f"WhisperFlow: sub decode error: {e}")
        return []


def parse_proxy_uri(uri):
    if uri.startswith("ss://"):
        return _parse_ss(uri)
    if uri.startswith("trojan://"):
        return _parse_trojan(uri)
    if uri.startswith("vless://"):
        return _parse_vless(uri)
    if uri.startswith("vmess://"):
        return _parse_vmess(uri)
    return None


def _parse_ss(uri):
    uri = uri.replace("ss://", "", 1)
    tag_name = ""
    if "#" in uri:
        uri, tag_name = uri.rsplit("#", 1)
        tag_name = urllib.parse.unquote(tag_name)
    if "@" in uri:
        userinfo, server_part = uri.split("@", 1)
        try:
            userinfo = base64.b64decode(userinfo + "==").decode()
        except Exception:
            pass
        method, password = userinfo.split(":", 1)
        host, port = server_part.rsplit(":", 1)
    else:
        try:
            decoded = base64.b64decode(uri + "==").decode()
        except Exception:
            return None
        method_pass, server_part = decoded.rsplit("@", 1)
        method, password = method_pass.split(":", 1)
        host, port = server_part.rsplit(":", 1)
    return {
        "type": "shadowsocks", "tag": tag_name or "proxy",
        "server": host, "server_port": int(port),
        "method": method, "password": password,
    }


def _parse_trojan(uri):
    uri = uri.replace("trojan://", "", 1)
    tag_name = ""
    if "#" in uri:
        uri, tag_name = uri.rsplit("#", 1)
        tag_name = urllib.parse.unquote(tag_name)
    password, rest = uri.split("@", 1)
    server_part = rest.split("?")[0]
    host, port = server_part.rsplit(":", 1)
    params = {}
    if "?" in rest:
        params = dict(urllib.parse.parse_qsl(rest.split("?", 1)[1]))
    return {
        "type": "trojan", "tag": tag_name or "proxy",
        "server": host, "server_port": int(port),
        "password": password,
        "tls": {"enabled": True, "server_name": params.get("sni", host)},
    }


def _parse_vless(uri):
    uri = uri.replace("vless://", "", 1)
    tag_name = ""
    if "#" in uri:
        uri, tag_name = uri.rsplit("#", 1)
        tag_name = urllib.parse.unquote(tag_name)
    uuid, rest = uri.split("@", 1)
    server_part = rest.split("?")[0]
    host, port = server_part.rsplit(":", 1)
    params = {}
    if "?" in rest:
        params = dict(urllib.parse.parse_qsl(rest.split("?", 1)[1]))
    out = {
        "type": "vless", "tag": tag_name or "proxy",
        "server": host, "server_port": int(port),
        "uuid": uuid,
        "tls": {"enabled": True, "server_name": params.get("sni", host)},
    }
    flow = params.get("flow")
    if flow:
        out["flow"] = flow
    transport_type = params.get("type")
    if transport_type and transport_type != "tcp":
        transport = {"type": transport_type}
        if transport_type == "ws":
            transport["path"] = params.get("path", "/")
            h = params.get("host")
            if h:
                transport["headers"] = {"Host": h}
        elif transport_type == "grpc":
            sn = params.get("serviceName")
            if sn:
                transport["service_name"] = sn
        out["transport"] = transport
    security = params.get("security", "")
    if security == "reality":
        out["tls"]["reality"] = {
            "enabled": True,
            "public_key": params.get("pbk", ""),
            "short_id": params.get("sid", ""),
        }
        out["tls"]["utls"] = {"enabled": True, "fingerprint": params.get("fp", "chrome")}
    return out


def _parse_vmess(uri):
    uri = uri.replace("vmess://", "", 1)
    try:
        raw = base64.b64decode(uri + "==").decode()
        cfg = json.loads(raw)
    except Exception:
        return None
    out = {
        "type": "vmess", "tag": cfg.get("ps", "proxy"),
        "server": cfg["add"], "server_port": int(cfg["port"]),
        "uuid": cfg["id"], "alter_id": int(cfg.get("aid", 0)),
        "security": cfg.get("scy", "auto"),
    }
    net = cfg.get("net", "tcp")
    if net and net != "tcp":
        transport = {"type": net}
        if net == "ws":
            transport["path"] = cfg.get("path", "/")
            h = cfg.get("host")
            if h:
                transport["headers"] = {"Host": h}
        out["transport"] = transport
    tls = cfg.get("tls", "")
    if tls == "tls":
        out["tls"] = {"enabled": True, "server_name": cfg.get("sni", cfg["add"])}
    return out


def write_singbox_config(outbound):
    config = {
        "log": {"level": "warn"},
        "inbounds": [{
            "type": "mixed", "tag": "mixed-in",
            "listen": "127.0.0.1", "listen_port": LOCAL_PROXY_PORT,
        }],
        "outbounds": [outbound, {"type": "direct", "tag": "direct"}],
    }
    CONFIG_DIR.mkdir(parents=True, exist_ok=True)
    with open(SINGBOX_CONFIG, "w") as f:
        json.dump(config, f, indent=2)
    NSLog(f"WhisperFlow: sing-box config → {outbound.get('type')} @ {outbound.get('server')}")


_singbox_process = None


def start_singbox():
    global _singbox_process
    if _singbox_process and _singbox_process.poll() is None:
        return True
    if not SINGBOX_CONFIG.exists():
        return False
    try:
        _singbox_process = subprocess.Popen(
            ["sing-box", "run", "--config", str(SINGBOX_CONFIG)],
            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
        )
        time.sleep(1.5)
        if _singbox_process.poll() is not None:
            err = _singbox_process.stderr.read().decode()[:200]
            NSLog(f"WhisperFlow: sing-box failed: {err}")
            return False
        NSLog(f"WhisperFlow: sing-box started on 127.0.0.1:{LOCAL_PROXY_PORT}")
        return True
    except Exception as e:
        NSLog(f"WhisperFlow: sing-box start error: {e}")
        return False


def stop_singbox():
    global _singbox_process
    if _singbox_process and _singbox_process.poll() is None:
        _singbox_process.terminate()
        try:
            _singbox_process.wait(timeout=3)
        except subprocess.TimeoutExpired:
            _singbox_process.kill()
        NSLog("WhisperFlow: sing-box stopped")


def enable_proxy():
    proxy = f"http://127.0.0.1:{LOCAL_PROXY_PORT}"
    os.environ["HTTP_PROXY"] = proxy
    os.environ["HTTPS_PROXY"] = proxy
    os.environ["ALL_PROXY"] = proxy
    NSLog(f"WhisperFlow: proxy enabled → {proxy}")


# ── Accessibility ───────────────────────────────────────────────────

def is_accessibility_granted():
    try:
        lib = ctypes.cdll.LoadLibrary(
            "/System/Library/Frameworks/ApplicationServices.framework/ApplicationServices"
        )
        lib.AXIsProcessTrusted.restype = ctypes.c_bool
        return lib.AXIsProcessTrusted()
    except Exception:
        return False


def request_accessibility():
    alert = NSAlert.alloc().init()
    alert.setMessageText_("WhisperFlow — нужен доступ Accessibility")
    alert.setInformativeText_(
        "Без этого разрешения горячая клавиша и вставка текста не работают.\n\n"
        "1. Нажмите 'Открыть настройки'\n"
        "2. Найдите Python и включите тумблер\n"
        "3. Перезапустите WhisperFlow"
    )
    alert.addButtonWithTitle_("Открыть настройки")
    alert.addButtonWithTitle_("Продолжить")
    if alert.runModal() == NSAlertFirstButtonReturn:
        subprocess.run(["open",
            "x-apple.systempreferences:com.apple.preference.security?Privacy_Accessibility"])


# ── Audio Recorder ──────────────────────────────────────────────────

class Recorder:
    def __init__(self):
        self._frames = []
        self._stream = None
        self._lock = threading.Lock()
        self._recording = False
        self._start_time = 0.0
        self._level_history = collections.deque(maxlen=NUM_BARS)

    @property
    def is_recording(self):
        return self._recording

    @property
    def levels(self):
        result = list(self._level_history)
        while len(result) < NUM_BARS:
            result.insert(0, 0.0)
        return result

    def start(self):
        with self._lock:
            self._frames.clear()
            self._level_history.clear()
            self._recording = True
            self._start_time = time.monotonic()
            self._stream = sd.InputStream(
                samplerate=SAMPLE_RATE, channels=1, dtype="int16",
                callback=self._callback, blocksize=1024,
            )
            self._stream.start()

    def stop(self):
        with self._lock:
            self._recording = False
            duration = time.monotonic() - self._start_time
            if self._stream:
                self._stream.stop()
                self._stream.close()
                self._stream = None
            if not self._frames or duration < MIN_DURATION_SEC:
                self._frames.clear()
                return None
            pcm = np.concatenate(self._frames)
            self._frames.clear()

        buf = io.BytesIO()
        with wave.open(buf, "wb") as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(SAMPLE_RATE)
            wf.writeframes(pcm.tobytes())
        buf.seek(0)
        return buf

    def _callback(self, data, frames, time_info, status):
        if self._recording:
            self._frames.append(data.copy())
            rms = np.sqrt(np.mean(data.astype(np.float32) ** 2)) / 32768.0
            level = min(1.0, rms * 18.0)
            level = math.pow(level, 0.5)
            self._level_history.append(level)


# ── Transcription (Groq) ───────────────────────────────────────────

class Transcriber:
    def __init__(self, api_key, language="ru"):
        self.client = Groq(api_key=api_key)
        self.language = language

    def transcribe(self, audio, clean=False):
        lang = self.language if self.language != "auto" else None
        transcription = self.client.audio.transcriptions.create(
            file=("audio.wav", audio),
            model="whisper-large-v3-turbo",
            language=lang, response_format="text",
        )
        text = transcription.strip()
        if not text or not clean:
            return text

        response = self.client.chat.completions.create(
            model="llama-3.3-70b-versatile",
            messages=[
                {"role": "system", "content": CLEANUP_SYSTEM_PROMPT},
                {"role": "user", "content": text},
            ],
            temperature=0, max_tokens=2000,
        )
        return response.choices[0].message.content.strip()


# ── Helpers ─────────────────────────────────────────────────────────

def inject_text(text):
    old = subprocess.run(["pbpaste"], capture_output=True, text=True).stdout
    subprocess.run(["pbcopy"], input=text, text=True, check=True)
    time.sleep(0.1)
    _simulate_paste()
    threading.Timer(0.5, lambda: subprocess.run(["pbcopy"], input=old, text=True)).start()


def _simulate_paste():
    v_keycode = 0x09
    source = Quartz.CGEventSourceCreate(Quartz.kCGEventSourceStateHIDSystemState)
    cmd_down = Quartz.CGEventCreateKeyboardEvent(source, v_keycode, True)
    Quartz.CGEventSetFlags(cmd_down, Quartz.kCGEventFlagMaskCommand)
    Quartz.CGEventPost(Quartz.kCGAnnotatedSessionEventTap, cmd_down)
    cmd_up = Quartz.CGEventCreateKeyboardEvent(source, v_keycode, False)
    Quartz.CGEventSetFlags(cmd_up, Quartz.kCGEventFlagMaskCommand)
    Quartz.CGEventPost(Quartz.kCGAnnotatedSessionEventTap, cmd_up)


def ask_text(title, message, placeholder=""):
    alert = NSAlert.alloc().init()
    alert.setMessageText_(title)
    alert.setInformativeText_(message)
    alert.addButtonWithTitle_("Сохранить")
    alert.addButtonWithTitle_("Пропустить")
    field = NSTextField.alloc().initWithFrame_(NSMakeRect(0, 0, 350, 24))
    field.setPlaceholderString_(placeholder)
    alert.setAccessoryView_(field)
    if alert.runModal() == NSAlertFirstButtonReturn:
        return str(field.stringValue()).strip()
    return ""


# ── Status View (custom drawing) ───────────────────────────────────

def _make_status_view_class():
    class _StatusView(NSView):
        _mode = "idle"
        _levels = None
        _click_callback = None

        def initWithFrame_(self, frame):
            self = objc.super(_StatusView, self).initWithFrame_(frame)
            if self is not None:
                self._levels = [0.0] * NUM_BARS
                self._mode = "idle"
            return self

        def setMode_(self, mode):
            self._mode = mode
            self.setNeedsDisplay_(True)

        def setLevels_(self, levels):
            self._levels = levels
            self.setNeedsDisplay_(True)

        def setClickCallback_(self, cb):
            self._click_callback = cb

        def acceptsFirstMouse_(self, event):
            return True

        def mouseDown_(self, event):
            if self._click_callback:
                self._click_callback()

        def drawRect_(self, rect):
            bounds = self.bounds()
            mode = self._mode

            if mode == "idle":
                NSColor.colorWithRed_green_blue_alpha_(0.25, 0.25, 0.25, 0.65).set()
                pill = NSBezierPath.bezierPathWithRoundedRect_xRadius_yRadius_(
                    bounds, bounds.size.height / 2, bounds.size.height / 2)
                pill.fill()
                return

            # Expanded states
            if mode == "recording":
                bg = NSColor.colorWithRed_green_blue_alpha_(0.10, 0.10, 0.10, 0.94)
            elif mode == "processing":
                bg = NSColor.colorWithRed_green_blue_alpha_(0.08, 0.08, 0.15, 0.94)
            elif mode == "done":
                bg = NSColor.colorWithRed_green_blue_alpha_(0.08, 0.40, 0.18, 0.94)
            elif mode == "cancelled":
                bg = NSColor.colorWithRed_green_blue_alpha_(0.55, 0.08, 0.08, 0.94)
            else:
                bg = NSColor.colorWithRed_green_blue_alpha_(0.50, 0.12, 0.05, 0.94)

            bg.set()
            NSBezierPath.bezierPathWithRoundedRect_xRadius_yRadius_(
                bounds, 14, 14).fill()

            if mode == "cancelled":
                cx = bounds.size.width / 2
                cy = bounds.size.height / 2
                d = min(bounds.size.width, bounds.size.height)
                NSBezierPath.bezierPathWithOvalInRect_(
                    NSMakeRect(cx - d/2, cy - d/2, d, d)).fill()
                NSColor.colorWithRed_green_blue_alpha_(1, 1, 1, 0.95).set()
                # Trash lid
                NSBezierPath.bezierPathWithRoundedRect_xRadius_yRadius_(
                    NSMakeRect(cx - 7, cy + 2, 14, 1.8), 0.9, 0.9).fill()
                # Trash handle
                NSBezierPath.bezierPathWithRoundedRect_xRadius_yRadius_(
                    NSMakeRect(cx - 2.8, cy + 3.8, 5.6, 2.5), 1.3, 1.3).fill()
                # Trash body
                tbody = NSBezierPath.bezierPath()
                tbody.moveToPoint_(NSMakePoint(cx - 6, cy + 1.5))
                tbody.lineToPoint_(NSMakePoint(cx - 4.8, cy - 8))
                tbody.lineToPoint_(NSMakePoint(cx + 4.8, cy - 8))
                tbody.lineToPoint_(NSMakePoint(cx + 6, cy + 1.5))
                tbody.closePath()
                tbody.fill()
                # Slits
                NSColor.colorWithRed_green_blue_alpha_(0.55, 0.08, 0.08, 1.0).set()
                for off in [-2.4, 0, 2.4]:
                    NSBezierPath.bezierPathWithRoundedRect_xRadius_yRadius_(
                        NSMakeRect(cx + off - 0.4, cy - 6, 0.8, 6.5), 0.4, 0.4).fill()
                return

            if mode == "done":
                cx = bounds.size.width / 2
                cy = bounds.size.height / 2
                d = min(bounds.size.width, bounds.size.height)
                NSBezierPath.bezierPathWithOvalInRect_(
                    NSMakeRect(cx - d/2, cy - d/2, d, d)).fill()
                # Checkmark
                NSColor.whiteColor().set()
                check = NSBezierPath.bezierPath()
                check.setLineWidth_(2.5)
                check.setLineCapStyle_(1)  # round
                check.setLineJoinStyle_(1)  # round
                check.moveToPoint_(NSMakePoint(cx - 5.5, cy - 0.5))
                check.lineToPoint_(NSMakePoint(cx - 1.5, cy - 5))
                check.lineToPoint_(NSMakePoint(cx + 6, cy + 4.5))
                check.stroke()
                return

            if mode == "error":
                return

            # ── Waveform bars ───────────────────────────────────────
            levels = self._levels or [0.0] * NUM_BARS
            bar_w = 2.5
            gap = 1.8
            stop_btn_d = 26.0
            pad_l = 14.0
            pad_r = 10.0
            btn_gap = 10.0

            bar_area_w = bounds.size.width - pad_l - btn_gap - stop_btn_d - pad_r
            max_bars = int(bar_area_w / (bar_w + gap))
            n = min(max_bars, len(levels))
            total_bars_w = n * (bar_w + gap) - gap
            start_x = pad_l + (bar_area_w - total_bars_w) / 2

            max_h = bounds.size.height - 10
            if mode == "recording":
                bar_color = NSColor.colorWithRed_green_blue_alpha_(1, 1, 1, 0.88)
            else:
                bar_color = NSColor.colorWithRed_green_blue_alpha_(0.65, 0.7, 1.0, 0.8)
            bar_color.set()

            display_levels = levels[-n:] if len(levels) >= n else ([0.0] * (n - len(levels))) + levels
            for i, lv in enumerate(display_levels):
                h = max(3.0, lv * max_h)
                x = start_x + i * (bar_w + gap)
                y = (bounds.size.height - h) / 2
                NSBezierPath.bezierPathWithRoundedRect_xRadius_yRadius_(
                    NSMakeRect(x, y, bar_w, h), 1.25, 1.25).fill()

            # ── Stop button ─────────────────────────────────────────
            btn_x = bounds.size.width - stop_btn_d - pad_r
            btn_y = (bounds.size.height - stop_btn_d) / 2

            NSColor.colorWithRed_green_blue_alpha_(0.85, 0.18, 0.18, 1.0).set()
            NSBezierPath.bezierPathWithOvalInRect_(
                NSMakeRect(btn_x, btn_y, stop_btn_d, stop_btn_d)).fill()

            sq = stop_btn_d * 0.36
            sq_x = btn_x + (stop_btn_d - sq) / 2
            sq_y = btn_y + (stop_btn_d - sq) / 2
            NSColor.whiteColor().set()
            NSBezierPath.bezierPathWithRoundedRect_xRadius_yRadius_(
                NSMakeRect(sq_x, sq_y, sq, sq), 2, 2).fill()

    return _StatusView


StatusViewClass = _make_status_view_class()


# ── Floating Status Window ──────────────────────────────────────────

class StatusWindow:
    def __init__(self, click_callback=None):
        self._click_callback = click_callback
        screen = NSScreen.mainScreen().frame()
        x = (screen.size.width - IDLE_W) / 2
        self.window = NSWindow.alloc().initWithContentRect_styleMask_backing_defer_(
            NSMakeRect(x, BOTTOM_Y, IDLE_W, IDLE_H),
            NSWindowStyleMaskBorderless,
            NSBackingStoreBuffered,
            False,
        )
        self.window.setLevel_(25)
        self.window.setOpaque_(False)
        self.window.setBackgroundColor_(NSColor.clearColor())
        self.window.setIgnoresMouseEvents_(False)
        self.window.setCollectionBehavior_(
            NSWindowCollectionBehaviorCanJoinAllSpaces
            | NSWindowCollectionBehaviorStationary
        )
        self.window.setHasShadow_(True)

        self.view = StatusViewClass.alloc().initWithFrame_(
            NSMakeRect(0, 0, IDLE_W, IDLE_H))
        if click_callback:
            self.view.setClickCallback_(click_callback)
        self.view.setWantsLayer_(True)
        self.window.setContentView_(self.view)

    def _animate_to(self, w, h, duration=0.25):
        screen = NSScreen.mainScreen().frame()
        x = (screen.size.width - w) / 2
        new_frame = NSMakeRect(x, BOTTOM_Y, w, h)
        NSAnimationContext.beginGrouping()
        NSAnimationContext.currentContext().setDuration_(duration)
        NSAnimationContext.currentContext().setTimingFunction_(
            __import__("Quartz").CAMediaTimingFunction.functionWithName_("easeInEaseOut"))
        self.window.animator().setFrame_display_(new_frame, True)
        self.window.animator().setAlphaValue_(1.0)
        NSAnimationContext.endGrouping()

    def show_idle(self):
        self.window.setAlphaValue_(1.0)
        self.view.setMode_("idle")
        self._animate_to(IDLE_W, IDLE_H, 0.25)
        self.window.orderFront_(None)

    def show_recording(self):
        self.view.setMode_("recording")
        self._animate_to(REC_W, REC_H, 0.2)
        self.window.orderFront_(None)

    def show_processing(self):
        self.view.setMode_("processing")
        self.window.orderFront_(None)

    def shrink_to_circle(self, mode):
        """Shrink from expanded bar to a circle with icon (done/cancelled)."""
        self.view.setMode_(mode)
        self._animate_to(CIRCLE_D, CIRCLE_D, 0.25)
        self.window.orderFront_(None)

    def slide_down_and_hide(self):
        """Slide the circle down and fade out."""
        frame = self.window.frame()
        cx = frame.origin.x + frame.size.width / 2
        target = NSMakeRect(cx - CIRCLE_D / 2, BOTTOM_Y - 40, CIRCLE_D, CIRCLE_D)
        NSAnimationContext.beginGrouping()
        ctx = NSAnimationContext.currentContext()
        ctx.setDuration_(0.3)
        ctx.setTimingFunction_(
            __import__("Quartz").CAMediaTimingFunction.functionWithName_("easeIn"))
        self.window.animator().setFrame_display_(target, True)
        self.window.animator().setAlphaValue_(0.0)
        NSAnimationContext.endGrouping()

    def show_error(self):
        self.view.setMode_("error")
        self.window.orderFront_(None)

    def update_levels(self, levels):
        self.view.setLevels_(levels)


# ── App Delegate ────────────────────────────────────────────────────

class AppDelegate(NSObject):

    def init(self):
        self = objc.super(AppDelegate, self).init()
        if self is None:
            return None
        self.recorder = Recorder()
        self.transcriber = None
        self._processing = False
        self.cfg = load_config()
        self.status_window = None
        self._anim_timer = None
        self._last_toggle = 0.0
        return self

    def applicationDidFinishLaunching_(self, notification):
        NSLog("WhisperFlow: starting")
        NSApp.setActivationPolicy_(1)

        if not is_accessibility_granted():
            NSLog("WhisperFlow: accessibility not granted")
            request_accessibility()
        else:
            NSLog("WhisperFlow: accessibility OK")

        # ── Proxy ───────────────────────────────────────────────────
        proxy_url = self.cfg.get("proxy_sub_url", "")
        if not proxy_url:
            proxy_url = ask_text(
                "WhisperFlow — Прокси",
                "Вставьте ссылку подписки (Shadowrocket/V2Ray)\n"
                "или прямую ссылку прокси.\n\n"
                "Groq API заблокирован в РФ — нужен прокси.",
                "https://... или ss://...",
            )
            if proxy_url:
                self.cfg["proxy_sub_url"] = proxy_url
                save_config(self.cfg)
        if proxy_url:
            self._setupProxy(proxy_url)

        # ── API key ─────────────────────────────────────────────────
        api_key = self.cfg.get("groq_api_key", "") or os.environ.get("GROQ_API_KEY", "")
        if not api_key:
            api_key = ask_text(
                "WhisperFlow — API ключ",
                "Введите Groq API ключ.\n"
                "Получить бесплатно: console.groq.com → API Keys",
                "gsk_...",
            )
            if not api_key:
                NSApp.terminate_(None)
                return
            self.cfg["groq_api_key"] = api_key
            save_config(self.cfg)

        try:
            self.transcriber = Transcriber(api_key, self.cfg["language"])
        except Exception as e:
            NSLog(f"WhisperFlow: init error: {e}")
            alert = NSAlert.alloc().init()
            alert.setMessageText_("Ошибка Groq API")
            alert.setInformativeText_(str(e))
            alert.runModal()
            NSApp.terminate_(None)
            return

        # ── UI + Hotkey ─────────────────────────────────────────────
        self.status_window = StatusWindow(
            click_callback=lambda: self.toggleRecording_(None))
        self.status_window.show_idle()

        self._setupHotkey()
        NSLog("WhisperFlow: ready")

    @objc.python_method
    def _setupProxy(self, url):
        if re.match(r"^(ss|vmess|vless|trojan)://", url):
            uris = [url]
        else:
            NSLog("WhisperFlow: fetching subscription...")
            uris = decode_subscription(url)
        if not uris:
            NSLog("WhisperFlow: no proxies found")
            return
        outbound = None
        for uri in uris:
            outbound = parse_proxy_uri(uri)
            if outbound:
                break
        if not outbound:
            NSLog("WhisperFlow: could not parse any proxy")
            return
        write_singbox_config(outbound)
        if start_singbox():
            enable_proxy()
        else:
            NSLog("WhisperFlow: sing-box failed to start")

    def applicationWillTerminate_(self, notification):
        stop_singbox()

    # ── Animation Timer ─────────────────────────────────────────────

    def startAnimTimer(self):
        if self._anim_timer:
            return
        self._anim_timer = NSTimer.scheduledTimerWithTimeInterval_target_selector_userInfo_repeats_(
            0.045, self, "animTick", None, True)

    def stopAnimTimer(self):
        if self._anim_timer:
            self._anim_timer.invalidate()
            self._anim_timer = None

    def animTick(self):
        if not self.status_window:
            return
        if self.recorder.is_recording:
            self.status_window.update_levels(self.recorder.levels)
        elif self._processing:
            t = time.time()
            levels = [
                abs(math.sin(t * 3.5 + i * 0.35)) * 0.35 + 0.12
                for i in range(NUM_BARS)
            ]
            self.status_window.update_levels(levels)

    # ── Hotkey (CGEventTap — intercepts Fn+Space at system level) ──

    @objc.python_method
    def _setupHotkey(self):
        delegate = self

        def tap_callback(proxy, event_type, event, refcon):
            try:
                if event_type not in (Quartz.kCGEventKeyDown, Quartz.kCGEventKeyUp):
                    if event_type == 0xFFFFFFFE:
                        Quartz.CGEventTapEnable(delegate._event_tap, True)
                    return event

                keycode = Quartz.CGEventGetIntegerValueField(
                    event, Quartz.kCGKeyboardEventKeycode)
                flags = Quartz.CGEventGetFlags(event)
                fn_bit = bool(int(flags) & MOD_FN)

                if int(keycode) == SPACE_KEYCODE and fn_bit:
                    if event_type == Quartz.kCGEventKeyDown:
                        delegate.toggleRecording_(None)
                    return None
                if int(keycode) == ESCAPE_KEYCODE and delegate.recorder.is_recording:
                    if event_type == Quartz.kCGEventKeyDown:
                        delegate.cancelRecording_(None)
                    return None
            except Exception as e:
                NSLog(f"WhisperFlow: tap error: {e}")
            return event

        mask = (Quartz.CGEventMaskBit(Quartz.kCGEventKeyDown)
                | Quartz.CGEventMaskBit(Quartz.kCGEventKeyUp))

        self._event_tap = Quartz.CGEventTapCreate(
            Quartz.kCGSessionEventTap,
            Quartz.kCGHeadInsertEventTap,
            Quartz.kCGEventTapOptionDefault,
            mask,
            tap_callback,
            None,
        )

        if self._event_tap:
            source = Quartz.CFMachPortCreateRunLoopSource(None, self._event_tap, 0)
            Quartz.CFRunLoopAddSource(
                Quartz.CFRunLoopGetMain(), source, Quartz.kCFRunLoopCommonModes)
            Quartz.CGEventTapEnable(self._event_tap, True)
            NSLog("WhisperFlow: hotkey Fn+Space (CGEventTap)")
        else:
            NSLog("WhisperFlow: CGEventTap failed — fallback to NSEvent")
            NSEvent.addGlobalMonitorForEventsMatchingMask_handler_(
                NSEventMaskKeyDown, self._fallbackKey_)

    def _fallbackKey_(self, event):
        flags = event.modifierFlags()
        if event.keyCode() == SPACE_KEYCODE and (flags & MOD_FN):
            self.toggleRecording_(None)

    # ── Recording ───────────────────────────────────────────────────

    def cancelRecording_(self, sender):
        if not self.recorder.is_recording:
            return
        now = time.monotonic()
        if now - self._last_toggle < 0.4:
            return
        self._last_toggle = now
        self.recorder.stop()
        self.stopAnimTimer()
        NSLog("WhisperFlow: recording cancelled")
        self._animateCircleExit("cancelled")

    @objc.python_method
    def _animateCircleExit(self, mode):
        """Shrink to circle icon, pause, slide down and hide, then reset to idle."""
        if self.status_window:
            self.status_window.shrink_to_circle(mode)
        threading.Timer(0.35, lambda: self.performSelectorOnMainThread_withObject_waitUntilDone_(
            "slideDownAndHide", None, False)).start()

    def slideDownAndHide(self):
        if self.status_window:
            self.status_window.slide_down_and_hide()
        threading.Timer(0.4, lambda: self.performSelectorOnMainThread_withObject_waitUntilDone_(
            "showIdle", None, False)).start()

    def toggleRecording_(self, sender):
        now = time.monotonic()
        if now - self._last_toggle < 0.4:
            return
        self._last_toggle = now
        if self._processing:
            return
        if self.recorder.is_recording:
            self._stopRecording()
        else:
            self._startRecording()

    @objc.python_method
    def _startRecording(self):
        if not self.transcriber:
            return
        try:
            self.recorder.start()
        except Exception as e:
            NSLog(f"WhisperFlow: mic error: {e}")
            return
        if self.status_window:
            self.status_window.show_recording()
        self.startAnimTimer()
        NSLog("WhisperFlow: recording started")

    @objc.python_method
    def _stopRecording(self):
        audio = self.recorder.stop()
        if not audio:
            self.stopAnimTimer()
            if self.status_window:
                self.status_window.show_idle()
            return
        self._processing = True
        if self.status_window:
            self.status_window.show_processing()
        NSLog("WhisperFlow: processing audio")
        threading.Thread(target=self._process, args=(audio,), daemon=True).start()

    @objc.python_method
    def _process(self, audio):
        try:
            clean = self.cfg.get("post_processing", True)
            text = self.transcriber.transcribe(audio, clean=clean)
            if text:
                inject_text(text)
                NSLog(f"WhisperFlow: injected {len(text)} chars")
                self.performSelectorOnMainThread_withObject_waitUntilDone_(
                    "showDone", None, False)
            else:
                NSLog("WhisperFlow: empty result")
                self.performSelectorOnMainThread_withObject_waitUntilDone_(
                    "showIdle", None, False)
        except Exception as e:
            NSLog(f"WhisperFlow: error: {e}")
            self.performSelectorOnMainThread_withObject_waitUntilDone_(
                "showErrorState", None, False)
        finally:
            self._processing = False

    def showDone(self):
        self.stopAnimTimer()
        self._animateCircleExit("done")

    def showIdle(self):
        self.stopAnimTimer()
        if self.status_window:
            self.status_window.show_idle()

    def showErrorState(self):
        self.stopAnimTimer()
        if self.status_window:
            self.status_window.show_error()
        threading.Timer(3.0, lambda: self.performSelectorOnMainThread_withObject_waitUntilDone_(
            "showIdle", None, False)).start()


# ── Entry Point ─────────────────────────────────────────────────────

def main():
    app = NSApplication.sharedApplication()
    delegate = AppDelegate.alloc().init()
    app.setDelegate_(delegate)
    NSLog("WhisperFlow: launching")
    app.run()


if __name__ == "__main__":
    main()
