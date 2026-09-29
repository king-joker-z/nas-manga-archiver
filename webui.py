#!/usr/bin/env python3
"""Local control panel for targeted manga and folder archiving."""
import base64
import hmac
import html
import json
import logging
import os
import secrets
import threading
import time
from collections import deque
from datetime import datetime
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from urllib.parse import parse_qs, urlencode, urlsplit

from archiver import (
    Config, Suwayomi, available_folders, chapter_fingerprint,
    collect_chapter_units, find_manga_dir, load_policies, load_state,
    resolve_completed, resolve_folder, run_once, safe_name, build_folder_index,
    optimize_existing_book, resolve_library_book, optimization_signature, book_paths, save_state,
)

log = logging.getLogger("manga-archiver.web")
CONFIG_DIR = Path(os.environ.get("CONFIG_DIR", "/config"))
SETTINGS_FILE = CONFIG_DIR / "settings.json"
MANUAL_FILE = CONFIG_DIR / "manual_completed.txt"
POLICIES_FILE = CONFIG_DIR / "policies.json"
PASSWORD = os.environ.get("WEBUI_PASSWORD", "")
TOKEN = secrets.token_urlsafe(32)
SCRIPT_NONCE = secrets.token_urlsafe(24)
LOCK = threading.RLock()
HISTORY = deque(maxlen=50)
RUNNING = False
PROGRESS = {"status": "idle", "label": "", "stage": "尚无任务", "title": "",
            "pages_done": 0, "pages_total": 0, "volume": 0, "started_at": None, "message": ""}
LAST_RUN = None
NEXT_RUN = None
MAX_BODY = 65536

FIELDS = {
    "suwayomi_url": ("Suwayomi 地址", "text"),
    "suwayomi_user": ("Basic Auth 用户", "text"),
    "suwayomi_pass": ("Basic Auth 密码（留空保持不变）", "password"),
    "interval_seconds": ("自动扫描间隔 / 秒（0 = 关闭）", "number"),
    "completed_statuses": ("自动识别的完结状态", "text"),
    "completed_category": ("完结分类名", "text"),
    "manga_mode": ("ComicInfo 阅读方向", "text"),
    "output_name_template": ("输出文件模板", "text"),
    "request_timeout": ("API 超时 / 秒", "number"),
    "max_zip_entry_mb": ("单页限制 / MB", "number"),
    "optimize_images": ("图片缩放及压缩（仅当新图更小时替换）", "checkbox"),
    "image_max_width": ("最大宽度 / 像素", "number"),
    "image_max_height": ("最大高度 / 像素", "number"),
    "image_quality": ("JPEG 质量（1–95）", "number"),
    "pages_per_book": ("每册最多页数（0 = 不拆分）", "number"),
    "move_source": ("归档后删除源章节（高风险）", "checkbox"),
    "dry_run": ("自动任务只预演", "checkbox"),
}


def escape(value):
    return html.escape(str(value), quote=True)


def load_settings():
    try:
        data = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except FileNotFoundError:
        return {}
    except (OSError, ValueError) as exc:
        log.error("无法读取配置：%s", exc)
        return {}


def save_text(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_name(path.name + ".tmp")
    try:
        fd = os.open(temp, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, "w", encoding="utf-8") as fp:
            fp.write(text)
        os.replace(temp, path)
    finally:
        temp.unlink(missing_ok=True)


def configured():
    cfg = Config()
    for key, value in load_settings().items():
        if key not in FIELDS:
            continue
        if key == "completed_statuses":
            value = {s.strip().upper() for s in value.split(",") if s.strip()}
        setattr(cfg, key, value)
    return cfg


def form_settings(form):
    settings = {}
    for key, (_, kind) in FIELDS.items():
        value = form.get(key, [""])[0].strip()
        if kind == "checkbox":
            settings[key] = key in form
        elif key == "suwayomi_pass" and not value:
            settings[key] = load_settings().get(key, os.environ.get("SUWAYOMI_PASS", ""))
        elif kind == "number":
            number = int(value)
            if number < (0 if key in ("interval_seconds", "pages_per_book") else 1) or number > 864000:
                raise ValueError(f"{key} 超出允许范围")
            if key == "image_quality" and number > 95:
                raise ValueError(f"{key} 超出允许范围")
            settings[key] = number
        else:
            if len(value) > 1000:
                raise ValueError(f"{key} 太长")
            settings[key] = value
    if not settings["suwayomi_url"].startswith(("http://", "https://")):
        raise ValueError("Suwayomi 地址必须以 http:// 或 https:// 开头")
    template = settings["output_name_template"]
    if template.count("{series}") != 1 or "{" in template.replace("{series}", "") or "}" in template.replace("{series}", ""):
        raise ValueError("输出模板必须且只能包含一个 {series}")
    if "/" in template or "\\" in template or ".." in template or not template.lower().endswith(".cbz"):
        raise ValueError("输出模板只能是单个 .cbz 文件名")
    if settings["move_source"] and not form.get("confirm_delete"):
        raise ValueError("启用删除源章节前请勾选二次确认")
    return settings


def manga_list(cfg):
    try:
        return Suwayomi(cfg).get_library_mangas(), None
    except Exception as exc:
        return [], str(exc)


def folder_list(cfg):
    if not cfg.download_dir.is_dir():
        return [], f"下载目录不可用：{cfg.download_dir}"
    try:
        return available_folders(cfg.download_dir), None
    except OSError as exc:
        return [], str(exc)


def folder_details(cfg, relative):
    path = resolve_folder(cfg.download_dir, relative)
    units = collect_chapter_units(path)
    return path, units


def report_progress(**updates):
    with LOCK:
        PROGRESS.update(updates)


def progress_snapshot():
    with LOCK:
        data = PROGRESS.copy()
        data["running"] = RUNNING
    data["elapsed_seconds"] = max(0, int(time.time() - data["started_at"])) if data["started_at"] else 0
    total = data["pages_total"]
    data["percent"] = min(100, int(data["pages_done"] * 100 / total)) if total else None
    return data


def run_job(dry_run=False, target=None, folder=None, force=False, library_book=None):
    global RUNNING, LAST_RUN
    label = f"库内文件 {library_book}" if library_book else (f"漫画 #{target}" if target is not None else (f"文件夹 {folder}" if folder else "自动巡检"))
    succeeded = False
    try:
        cfg = configured()
        if target is not None or folder is not None or library_book:
            cfg.dry_run = dry_run
        if library_book:
            stats = optimize_existing_book(cfg, library_book, dry_run=dry_run,
                                           progress=report_progress)
            if not dry_run:
                state = load_state(cfg.state_file)
                source = str(cfg.komga_library / library_book)
                for record in state.values():
                    if isinstance(record, dict) and record.get("output") == source:
                        record["outputs"] = [str(p) for p in book_paths(Path(source), stats["books"])]
                        record["optimization"] = optimization_signature(cfg)
                save_state(cfg.state_file, state)
        else:
            stats = run_once(cfg, target=target, folder=folder, force=force,
                             progress=report_progress)
        succeeded = not stats.get("failed", 0)
        message = f"{datetime.now():%m-%d %H:%M} · {label} · {'预演' if cfg.dry_run else '归档'} · {stats}"
    except Exception as exc:
        log.exception("归档任务失败")
        message = f"{datetime.now():%m-%d %H:%M} · {label} · 失败：{exc}"
    with LOCK:
        HISTORY.appendleft(message)
        LAST_RUN = datetime.now()
        RUNNING = False
        PROGRESS.update(status="completed" if succeeded else "failed",
                        stage="已完成" if succeeded else "任务失败", message=message)


def start_job(dry_run=False, target=None, folder=None, force=False, library_book=None):
    global RUNNING
    with LOCK:
        if RUNNING:
            return False
        RUNNING = True
        PROGRESS.update(status="running", label=(f"库内文件 {library_book}" if library_book else
                        f"漫画 #{target}" if target is not None else
                        f"文件夹 {folder}" if folder else "自动巡检"),
                        stage="等待任务启动", title="", pages_done=0, pages_total=0,
                        volume=0, started_at=time.time(), message="")
    threading.Thread(target=run_job, args=(dry_run, target, folder, force, library_book), daemon=True).start()
    return True


def scheduler():
    global NEXT_RUN
    # Deliberately no automatic startup run; wait one full interval.
    while True:
        interval = configured().interval_seconds
        if interval <= 0:
            NEXT_RUN = None
            time.sleep(5)
            continue
        NEXT_RUN = time.monotonic() + interval
        while time.monotonic() < NEXT_RUN:
            time.sleep(min(5, max(.1, NEXT_RUN - time.monotonic())))
            if configured().interval_seconds != interval:
                break
        else:
            start_job()


STYLE = """
:root{font-family:Inter,system-ui,-apple-system,sans-serif;color:#eaf0fb;background:#0c1220}*{box-sizing:border-box}body{margin:0}a{color:inherit;text-decoration:none}.shell{min-height:100vh;display:flex}aside{width:224px;background:#10192a;border-right:1px solid #24334b;padding:32px 16px;position:sticky;top:0;height:100vh}aside strong{display:block;font-size:20px;margin:0 12px 10px}aside small{display:block;margin:0 12px 42px;color:#8294b3}nav a{display:block;color:#aebbd0;padding:13px 15px;border-radius:11px;margin:4px 0}nav a.active,nav a:hover{color:#fff;background:#253751}main{max-width:1180px;width:100%;margin:0 auto;padding:34px 36px 80px}header{display:flex;justify-content:space-between;align-items:center;gap:16px;margin-bottom:26px}h1{margin:0;font-size:30px;letter-spacing:-.04em}h2{font-size:19px;margin:0 0 16px}h3{font-size:15px;margin:0 0 12px}p,small{color:#9daec8;line-height:1.6}.eyebrow{font-size:12px;letter-spacing:.12em;color:#83d9b3;text-transform:uppercase;font-weight:700}.badge{border-radius:99px;padding:7px 12px;font-size:12px;background:#173c37;color:#91eac1;white-space:nowrap}.muted{color:#9baac1}.card{background:#151f31;border:1px solid #2b3b52;border-radius:16px;padding:22px;margin:18px 0}.grid{display:grid;grid-template-columns:repeat(3,1fr);gap:16px}.grid .card{margin:0}.metric{font-size:30px;font-weight:750;margin-top:6px}.notice{background:#183f38;color:#c5ffdf;border:1px solid #377a67;border-radius:12px;padding:14px;margin-bottom:20px}.warning{background:#4a3422;color:#ffe6ba;border-color:#80633a}.row{display:flex;gap:12px;align-items:center;flex-wrap:wrap}.spaced{justify-content:space-between}.button,button{background:#83dfae;color:#08211a;display:inline-block;border:0;border-radius:9px;padding:9px 15px;font:inherit;font-weight:700;cursor:pointer}.button.secondary,button.secondary{background:#273b56;color:#e8f0ff}.button.danger,button.danger{background:#4a303a;color:#ffdce0}form.inline{display:inline-block;margin-right:6px}input,select,textarea{background:#0d1626;color:#eef4ff;border:1px solid #40546e;border-radius:8px;padding:10px;font:inherit;max-width:100%}input[type=checkbox]{width:18px;height:18px;accent-color:#83dfae}input[type=search]{width:320px}textarea{width:100%;min-height:145px;resize:vertical}label.field{display:flex;justify-content:space-between;align-items:center;gap:12px;border-bottom:1px solid #26374b;padding:13px 0}label.field input:not([type=checkbox]),label.field select{width:50%}.table-wrap{overflow:auto}table{width:100%;border-collapse:collapse}th{text-align:left;color:#8296b5;font-size:12px;font-weight:600}td,th{padding:14px 11px;border-bottom:1px solid #29374a;vertical-align:middle}td.actions{white-space:nowrap}code{color:#b3d4ef;overflow-wrap:anywhere}ul{padding-left:20px;line-height:1.9}.chip{background:#27364c;color:#b4c4db;border-radius:7px;padding:4px 8px;font-size:12px}.section-title{display:flex;justify-content:space-between;align-items:center;margin-bottom:18px}.empty{padding:32px;text-align:center;color:#9baac1}.detail{display:grid;grid-template-columns:1fr 1fr;gap:18px}.detail .card{margin:0}.breadcrumbs{color:#9baac1;margin-bottom:17px;display:block}.danger-note{color:#ffc5a1}@media(max-width:800px){.shell{display:block}aside{width:auto;height:auto;position:static;padding:16px}aside small{margin-bottom:14px}nav{display:flex;overflow:auto}nav a{white-space:nowrap}main{padding:24px 16px}.grid,.detail{grid-template-columns:1fr}header{align-items:flex-start}label.field{display:block}label.field input:not([type=checkbox]),label.field select{width:100%;margin-top:8px}}
"""

PROGRESS_SCRIPT = """
const panel = document.getElementById('job-progress');
const meter = document.getElementById('job-meter');
const details = document.getElementById('job-details');
const summary = document.getElementById('job-summary');
async function refreshProgress() {
  try {
    const response = await fetch('/progress', {cache: 'no-store'});
    if (!response.ok) throw new Error('无法读取任务状态');
    const state = await response.json();
    panel.hidden = state.status === 'idle';
    if (panel.hidden) return;
    const label = state.title || state.label;
    const pages = state.pages_total ? ` · ${state.pages_done} / ${state.pages_total} 页 (${state.percent}%)` : '';
    const volume = state.volume ? ` · 第 ${state.volume} 册` : '';
    details.textContent = `${label} · ${state.stage}${pages}${volume} · 已用 ${state.elapsed_seconds} 秒`;
    summary.textContent = state.running ? '正在处理，请勿重复提交任务' : state.message;
    if (state.pages_total) {
      meter.value = state.pages_done;
      meter.max = state.pages_total;
    } else {
      meter.removeAttribute('value');
    }
  } catch (error) {
    details.textContent = `进度获取失败：${error.message}`;
  }
}
refreshProgress();
setInterval(refreshProgress, 1500);
"""


def post_form(action, label, fields=None, style="secondary", confirm=""):
    hidden = f'<input type="hidden" name="csrf" value="{TOKEN}">'
    for key, value in (fields or {}).items():
        hidden += f'<input type="hidden" name="{escape(key)}" value="{escape(value)}">'
    if confirm:
        hidden += f'<label class="danger-note"><input type="checkbox" name="confirm" required> {escape(confirm)}</label>'
    return f'<form class="inline" method="post" action="{escape(action)}">{hidden}<button class="{style}">{escape(label)}</button></form>'


def nav_link(path, label, current):
    return f'<a href="{path}" class="{"active" if current == path else ""}">{label}</a>'


def layout(title, section, body, message="", warning=False):
    notice = f'<div class="notice {"warning" if warning else ""}">{escape(message)}</div>' if message else ""
    with LOCK:
        running = RUNNING
    return f'''<!doctype html><html lang="zh-CN"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>{escape(title)} · Manga Archiver</title><style>{STYLE}</style></head><body><div class="shell"><aside><strong>◈ Manga Archive</strong><small>Suwayomi → Komga</small><nav>{nav_link('/', '◫　控制台', section)}{nav_link('/mangas', '▤　漫画管理', section)}{nav_link('/folders', '▥　文件夹管理', section)}{nav_link('/library', '▧　已合并优化', section)}{nav_link('/settings', '⚙　功能配置', section)}</nav></aside><main><header><div><div class="eyebrow">LIBRARY CONTROL CENTER</div><h1>{escape(title)}</h1></div><span class="badge">{'● 正在执行' if running else '● 系统空闲'}</span></header>{notice}<section id="job-progress" class="card" hidden><h2>任务进度</h2><p id="job-details" role="status" aria-live="polite">正在读取进度…</p><progress id="job-meter" style="width:100%;height:18px;accent-color:#83dfae"></progress><p id="job-summary"></p></section>{body}</main></div><script nonce="{SCRIPT_NONCE}">{PROGRESS_SCRIPT}</script></body></html>'''


class Handler(BaseHTTPRequestHandler):
    def authorized(self):
        try:
            scheme, encoded = self.headers.get("Authorization", "").split(" ", 1)
            user, supplied = base64.b64decode(encoded, validate=True).decode().split(":", 1)
            return scheme.lower() == "basic" and hmac.compare_digest(user, "admin") and hmac.compare_digest(supplied, PASSWORD)
        except (ValueError, UnicodeError):
            return False

    def respond(self, status, body, content_type="text/html; charset=utf-8"):
        payload = body.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(payload)))
        self.send_header("Cache-Control", "no-store")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Security-Policy", f"default-src 'none'; connect-src 'self'; script-src 'nonce-{SCRIPT_NONCE}'; style-src 'unsafe-inline'; form-action 'self'; base-uri 'none'; frame-ancestors 'none'")
        self.end_headers()
        self.wfile.write(payload)

    def check_auth(self):
        if self.authorized():
            return True
        self.send_response(401)
        self.send_header("WWW-Authenticate", 'Basic realm="Manga Archiver"')
        self.send_header("Content-Length", "0")
        self.end_headers()
        return False

    def do_GET(self):
        if not self.check_auth():
            return
        url = urlsplit(self.path)
        params = parse_qs(url.query)
        message = params.get("message", [""])[0]
        try:
            if url.path == "/healthz":
                self.respond(200, "ok", "text/plain; charset=utf-8")
                return
            if url.path == "/progress":
                self.respond(200, json.dumps(progress_snapshot(), ensure_ascii=False),
                             "application/json; charset=utf-8")
                return
            pages = {"/": self.dashboard, "/mangas": self.mangas, "/folders": self.folders,
                     "/manga": self.manga_detail, "/folder": self.folder_detail, "/settings": self.settings,
                     "/library": self.library_books}
            page = pages.get(url.path)
            if not page:
                self.respond(404, "页面不存在")
                return
            self.respond(200, page(params, message))
        except (ValueError, OSError) as exc:
            self.respond(400, layout("请求无效", "/", "<p>请返回列表重新选择。</p>", str(exc), True))

    def do_POST(self):
        if not self.check_auth():
            return
        url = urlsplit(self.path)
        length = self.headers.get("Content-Length", "")
        if url.path not in ("/settings", "/manual", "/policy", "/run", "/optimize") or not length.isdigit() or int(length) > MAX_BODY:
            self.respond(400, "无效请求")
            return
        form = parse_qs(self.rfile.read(int(length)).decode("utf-8", "replace"), keep_blank_values=True)
        if not hmac.compare_digest(form.get("csrf", [""])[0], TOKEN):
            self.respond(403, "请求校验失败")
            return
        destination = "/settings" if url.path in ("/settings", "/manual") else ("/library" if url.path == "/optimize" else ("/mangas" if form.get("kind") == ["manga"] else "/folders"))
        try:
            if url.path == "/settings":
                save_text(SETTINGS_FILE, json.dumps(form_settings(form), ensure_ascii=False, indent=2))
                message = "功能配置已保存；下一轮任务生效"
            elif url.path == "/manual":
                save_text(MANUAL_FILE, form.get("manual", [""])[0])
                message = "手动完结清单已保存"
            elif url.path == "/policy":
                destination, message = self.save_policy(form)
            elif url.path == "/optimize":
                relative = form.get("book", [""])[0]
                resolve_library_book(configured(), relative)
                operation = form.get("operation", [""])[0]
                if operation not in ("preview", "optimize"):
                    raise ValueError("无效操作")
                if operation == "optimize" and form.get("confirm") != ["on"]:
                    raise ValueError("重处理需要确认")
                started = start_job(dry_run=operation == "preview", library_book=relative)
                message = "已开始预演" if started and operation == "preview" else ("已开始重处理" if started else "已有任务正在执行")
            else:
                destination, message = self.run_target(form)
        except (ValueError, OSError) as exc:
            message = f"操作失败：{exc}"
        self.send_response(303)
        self.send_header("Location", destination + "?" + urlencode({"message": message}))
        self.send_header("Content-Length", "0")
        self.end_headers()

    def save_policy(self, form):
        cfg = configured()
        kind = form.get("kind", [""])[0]
        identifier = form.get("id", [""])[0]
        mode = form.get("mode", [""])[0]
        if mode not in ("auto", "manual", "skip"):
            raise ValueError("无效处理模式")
        if kind == "manga":
            matches = [m for m in Suwayomi(cfg).get_library_mangas() if str(m.get("id")) == identifier]
            if not matches:
                raise ValueError("漫画不存在")
            folder = form.get("folder", [""])[0]
            if folder:
                resolve_folder(cfg.download_dir, folder)
            record = {"mode": mode, "folder": folder}
            destination = "/manga?" + urlencode({"id": identifier})
            bucket = "manga"
        elif kind == "folder":
            path, _ = folder_details(cfg, identifier)
            title = form.get("title", [""])[0].strip() or path.name
            if len(title) > 180:
                raise ValueError("标题过长")
            safe_name(title)
            record = {"mode": mode, "title": title}
            destination = "/folder?" + urlencode({"path": identifier})
            bucket = "folders"
        else:
            raise ValueError("无效目标")
        with LOCK:
            data = load_policies(cfg)
            data.setdefault(bucket, {})[identifier] = record
            save_text(POLICIES_FILE, json.dumps(data, ensure_ascii=False, indent=2))
        return destination, "单项策略已保存"

    def run_target(self, form):
        cfg = configured()
        kind = form.get("kind", [""])[0]
        identifier = form.get("id", [""])[0]
        operation = form.get("operation", [""])[0]
        if operation not in ("preview", "archive", "force"):
            raise ValueError("无效操作")
        if kind == "manga":
            mangas, error = manga_list(cfg)
            if error or not any(str(m.get("id")) == identifier for m in mangas):
                raise ValueError("无法校验漫画 ID，请检查 Suwayomi 连接")
            target, folder = identifier, None
            destination = "/manga?" + urlencode({"id": identifier})
        elif kind == "folder":
            folder_details(cfg, identifier)
            target, folder = None, identifier
            destination = "/folder?" + urlencode({"path": identifier})
        else:
            raise ValueError("必须指定漫画或文件夹，不允许无目标全量执行")
        if operation == "force" and form.get("confirm") != ["on"]:
            raise ValueError("强制重建需要确认")
        started = start_job(dry_run=operation == "preview", target=target, folder=folder, force=operation == "force")
        return destination, ("已开始单项预演" if operation == "preview" else "已开始单项归档") if started else "已有任务正在执行"

    def dashboard(self, params, message):
        cfg = configured()
        state = load_state(cfg.state_file)
        policies = load_policies(cfg)
        with LOCK:
            history, running, last_run = list(HISTORY), RUNNING, LAST_RUN
        counts = [len(state), len(policies.get("manga", {})), len(policies.get("folders", {}))]
        metrics = "".join(f'<div class="card"><div class="muted">{label}</div><div class="metric">{value}</div></div>' for label, value in zip(("已归档记录", "漫画独立策略", "文件夹独立策略"), counts))
        entries = "".join(f'<li>{escape(item)}</li>' for item in history) or '<li class="muted">尚无任务。前往漫画或文件夹详情执行单项操作。</li>'
        body = f'''<p>一个入口，精准管理每一部作品。自动任务仅处理符合完结规则且未被设为「仅手动」或「忽略」的项目。</p><div class="grid">{metrics}</div><div class="card"><div class="section-title"><h2>归档控制</h2><span class="badge">{'任务运行中' if running else '等待指令'}</span></div><p>自动扫描：{'已关闭' if cfg.interval_seconds == 0 else f'每 {cfg.interval_seconds} 秒'} · 最近运行：{escape(last_run.strftime('%Y-%m-%d %H:%M') if last_run else '暂无')}</p><div class="row"><a class="button" href="/mangas">选择漫画 →</a><a class="button secondary" href="/folders">选择文件夹 →</a></div><p>出于安全考虑，控制台不提供一键全库归档。请先查看章节与输出路径再执行。</p></div><div class="card"><h2>最近任务</h2><ul>{entries}</ul></div>'''
        return layout("控制台", "/", body, message)

    def mangas(self, params, message):
        cfg = configured()
        mangas, error = manga_list(cfg)
        policies = load_policies(cfg).get("manga", {})
        query = params.get("q", [""])[0].strip()[:100].lower()
        completed = {str(mid): reason for mid, _, reason in resolve_completed(cfg)} if not error else {}
        rows = []
        for manga in mangas:
            title = str(manga.get("title") or "")
            mid = str(manga.get("id"))
            if query and query not in title.lower() and query not in mid:
                continue
            policy = policies.get(mid, {})
            mode = {"auto": "自动", "manual": "仅手动", "skip": "忽略"}.get(policy.get("mode"), "继承完结规则")
            link = "/manga?" + urlencode({"id": mid})
            rows.append(f'<tr><td><a href="{link}"><strong>{escape(title)}</strong></a><br><small>#{escape(mid)}</small></td><td>{escape(manga.get("status") or "未知")}</td><td>{escape(mode)}</td><td>{"已命中" if mid in completed else "未命中"}</td><td><a class="button secondary" href="{link}">管理 →</a></td></tr>')
        warning = f'<div class="notice warning">连接 Suwayomi 失败：{escape(error)}。可先在「文件夹管理」中直接操作本地文件夹。</div>' if error else ''
        body = f'''<p>按 Suwayomi 漫画 ID 精确匹配。可为单部作品绑定下载文件夹并覆盖自动归档策略。</p>{warning}<div class="card"><form method="get" action="/mangas" class="row"><input type="search" name="q" value="{escape(query)}" placeholder="搜索标题或漫画 ID"><button>搜索</button><a class="button secondary" href="/mangas">清空</a></form></div><div class="card table-wrap"><table><thead><tr><th>漫画</th><th>源站状态</th><th>处理策略</th><th>完结规则</th><th>操作</th></tr></thead><tbody>{''.join(rows)}</tbody></table>{'<div class="empty">暂无匹配漫画。检查 Suwayomi 连接或尝试文件夹管理。</div>' if not rows else ''}</div>'''
        return layout("漫画管理", "/mangas", body, message)

    def manga_detail(self, params, message):
        cfg = configured()
        mid = params.get("id", [""])[0]
        mangas, error = manga_list(cfg)
        manga = next((m for m in mangas if str(m.get("id")) == mid), None)
        if not manga:
            raise ValueError(error or "漫画 ID 不存在")
        title = str(manga.get("title") or "")
        policy = load_policies(cfg).get("manga", {}).get(mid, {})
        folders, folder_error = folder_list(cfg)
        index = build_folder_index(cfg.download_dir)
        matched = find_manga_dir(index, title)
        suggested = matched.relative_to(cfg.download_dir).as_posix() if matched else ""
        selected = policy.get("folder", "") or suggested
        options = '<option value="">自动匹配（仅唯一匹配时）</option>' + ''.join(f'<option value="{escape(f["path"])}" {"selected" if selected == f["path"] else ""}>{escape(f["path"])} · {f["chapters"]} 话</option>' for f in folders)
        units = []
        if selected:
            try:
                _, units = folder_details(cfg, selected)
            except ValueError:
                pass
        state = load_state(cfg.state_file).get(mid, {})
        output = cfg.komga_library / safe_name(title) / cfg.output_name_template.format(series=safe_name(title))
        mode = policy.get("mode", "auto")
        mode_options = ''.join(f'<option value="{value}" {"selected" if mode == value else ""}>{label}</option>' for value, label in (("auto", "自动（遵循完结识别）"), ("manual", "仅手动"), ("skip", "忽略自动处理")))
        chapters = ''.join(f'<li>{escape(u.name)}</li>' for u in units[:60]) or '<li>尚未找到章节，请绑定正确文件夹。</li>'
        if len(units) > 60:
            chapters += f'<li>……其余 {len(units) - 60} 个章节</li>'
        controls = ''.join(post_form('/run', label, {"kind": "manga", "id": mid, "operation": op}, style, confirm) for op, label, style, confirm in (("preview", "预演本书", "secondary", ""), ("archive", "归档本书", "", ""), ("force", "强制重建", "danger", "我确认覆盖已有输出")))
        body = f'''<a class="breadcrumbs" href="/mangas">← 返回漫画管理</a><div class="detail"><div class="card"><h2>{escape(title)}</h2><p>Suwayomi ID：{escape(mid)} · 状态：{escape(manga.get('status') or '未知')}</p><p>预计输出：<code>{escape(output)}</code></p><p>历史归档：{escape(state.get('merged_at') or '暂无')} · {escape(state.get('pages') or 0)} 页</p><p>匹配文件夹：<code>{escape(selected or '未找到唯一匹配')}</code></p></div><div class="card"><h2>单书策略</h2><form method="post" action="/policy"><input type="hidden" name="csrf" value="{TOKEN}"><input type="hidden" name="kind" value="manga"><input type="hidden" name="id" value="{escape(mid)}"><label class="field">处理方式 <select name="mode">{mode_options}</select></label><label class="field">下载文件夹 <select name="folder">{options}</select></label><button>保存本书策略</button></form><small>绑定只影响此漫画，不改变其他作品。</small></div></div><div class="card"><h2>章节清单 · {len(units)} 话</h2>{f'<p class="danger-note">{escape(folder_error)}</p>' if folder_error else ''}<ul>{chapters}</ul></div><div class="card"><h2>定向操作</h2><p>只处理漫画 #{escape(mid)}，不会操作其他漫画；强制重建会覆盖原有 CBZ。</p>{controls}</div>'''
        return layout("单书管理", "/mangas", body, message)

    def folders(self, params, message):
        cfg = configured()
        folders, error = folder_list(cfg)
        policies = load_policies(cfg).get("folders", {})
        query = params.get("q", [""])[0].strip()[:100].lower()
        rows = []
        for folder in folders:
            path = folder["path"]
            if query and query not in path.lower():
                continue
            link = "/folder?" + urlencode({"path": path})
            mode = {"auto": "自动", "manual": "仅手动", "skip": "忽略"}.get(policies.get(path, {}).get("mode"), "仅手动")
            rows.append(f'<tr><td><a href="{link}"><strong>{escape(folder["name"])}</strong></a><br><small>{escape(path)}</small></td><td>{folder["chapters"]} 话</td><td>{mode}</td><td><a class="button secondary" href="{link}">管理 →</a></td></tr>')
        body = f'''<p>不依赖 Suwayomi：直接扫描已挂载的下载目录，按实际相对路径精确选择。</p>{f'<div class="notice warning">{escape(error)}</div>' if error else ''}<div class="card"><form method="get" action="/folders" class="row"><input type="search" name="q" value="{escape(query)}" placeholder="搜索文件夹名称或路径"><button>搜索</button><a class="button secondary" href="/folders">清空</a></form></div><div class="card table-wrap"><table><thead><tr><th>源文件夹</th><th>章节</th><th>处理策略</th><th>操作</th></tr></thead><tbody>{''.join(rows)}</tbody></table>{'<div class="empty">没有发现包含 CBZ / 图片章节的漫画文件夹。请检查下载目录挂载。</div>' if not rows else ''}</div>'''
        return layout("文件夹管理", "/folders", body, message)

    def folder_detail(self, params, message):
        cfg = configured()
        relative = params.get("path", [""])[0]
        path, units = folder_details(cfg, relative)
        policy = load_policies(cfg).get("folders", {}).get(relative, {})
        title = policy.get("title") or path.name
        mode = policy.get("mode", "manual")
        modes = ''.join(f'<option value="{value}" {"selected" if value == mode else ""}>{label}</option>' for value, label in (("manual", "仅手动（默认）"), ("auto", "自动处理"), ("skip", "忽略自动处理")))
        state = load_state(cfg.state_file).get("folder:" + relative, {})
        chapters = ''.join(f'<li>{escape(unit.name)}</li>' for unit in units[:80]) or '<li>该文件夹暂无章节。</li>'
        if len(units) > 80:
            chapters += f'<li>……其余 {len(units) - 80} 个章节</li>'
        controls = ''.join(post_form('/run', label, {"kind": "folder", "id": relative, "operation": op}, style, confirm) for op, label, style, confirm in (("preview", "预演此文件夹", "secondary", ""), ("archive", "归档此文件夹", "", ""), ("force", "强制重建", "danger", "我确认覆盖已有输出")))
        output = cfg.komga_library / safe_name(title) / cfg.output_name_template.format(series=safe_name(title))
        body = f'''<a class="breadcrumbs" href="/folders">← 返回文件夹管理</a><div class="detail"><div class="card"><h2>{escape(path.name)}</h2><p>源目录：<code>{escape(path)}</code></p><p>预计输出：<code>{escape(output)}</code></p><p>上次归档：{escape(state.get('merged_at') or '暂无')} · {escape(state.get('pages') or 0)} 页</p></div><div class="card"><h2>文件夹策略</h2><form method="post" action="/policy"><input type="hidden" name="csrf" value="{TOKEN}"><input type="hidden" name="kind" value="folder"><input type="hidden" name="id" value="{escape(relative)}"><label class="field">归档标题 <input name="title" value="{escape(title)}" required maxlength="180"></label><label class="field">处理方式 <select name="mode">{modes}</select></label><button>保存文件夹策略</button></form></div></div><div class="card"><h2>章节清单 · {len(units)} 话</h2><ul>{chapters}</ul></div><div class="card"><h2>定向操作</h2><p>操作只读取此文件夹；仅归档标题决定输出目录和 CBZ 名称。</p>{controls}</div>'''
        return layout("文件夹详情", "/folders", body, message)

    def library_books(self, params, message):
        cfg = configured()
        query = params.get("q", [""])[0].strip()[:100].lower()
        rows = []
        if cfg.komga_library.is_dir():
            for root, dirs, files in os.walk(cfg.komga_library, followlinks=False):
                dirs[:] = [d for d in dirs if not (Path(root) / d).is_symlink()]
                for name in sorted(files):
                    if not name.lower().endswith(".cbz"):
                        continue
                    path = Path(root) / name
                    relative = path.relative_to(cfg.komga_library).as_posix()
                    if query and query not in relative.lower():
                        continue
                    if path.is_symlink():
                        continue
                    controls = post_form('/optimize', '预演', {'book': relative, 'operation': 'preview'}) + post_form('/optimize', '优化此书', {'book': relative, 'operation': 'optimize'}, 'danger', '确认重处理此 CBZ；请先备份')
                    rows.append(f'<tr><td><code>{escape(relative)}</code></td><td>{path.stat().st_size / 1048576:.1f} MB</td><td>{controls}</td></tr>')
                    if len(rows) >= 200:
                        break
                if len(rows) >= 200:
                    break
        body = f'''<p>仅处理选中的单个原始 CBZ，不批量修改库。建议先备份原文件并预演；分册后请到 Komga 重新扫描。已有分册请从源章节强制重建。</p><p>当前设置：压缩{'开启' if cfg.optimize_images else '关闭'}，最长边约 {cfg.image_max_width}×{cfg.image_max_height}，JPEG 质量 {cfg.image_quality}，每册 {cfg.pages_per_book or '不限'} 页。修改请前往<a href="/settings">功能配置</a>。</p><div class="card"><form method="get" action="/library" class="row"><input name="q" type="search" value="{escape(query)}" placeholder="搜索 CBZ 文件名"><button>搜索</button></form></div><div class="card table-wrap"><table><thead><tr><th>库内文件</th><th>大小</th><th>操作</th></tr></thead><tbody>{''.join(rows)}</tbody></table>{'<div class="empty">暂无匹配的 CBZ。</div>' if not rows else ''}</div>'''
        return layout("已合并优化", "/library", body, message)

    def settings(self, params, message):
        cfg = configured()
        fields = []
        for key, (label, kind) in FIELDS.items():
            value = getattr(cfg, key)
            if key == "suwayomi_pass":
                value = ""
            if key == "completed_statuses":
                value = ",".join(sorted(value))
            if kind == "checkbox":
                control = f'<input type="checkbox" name="{key}" {"checked" if value else ""}>'
            else:
                control = f'<input type="{kind}" name="{key}" value="{escape(value)}" {"min=0" if kind == "number" else ""}>'
            fields.append(f'<label class="field">{escape(label)} {control}</label>')
        try:
            manual = MANUAL_FILE.read_text(encoding="utf-8")
        except FileNotFoundError:
            manual = ""
        body = f'''<p>这里仅管理全局规则和连接参数。单书控制请前往「漫画管理」或「文件夹管理」。</p><div class="card"><h2>连接与归档规则</h2><p>输入：<code>{escape(cfg.download_dir)}</code> · 输出：<code>{escape(cfg.komga_library)}</code> · 持久化：<code>{escape(cfg.config_dir)}</code></p><form method="post" action="/settings"><input type="hidden" name="csrf" value="{TOKEN}">{''.join(fields)}<label class="field danger-note">我确认启用后删除源章节 <input type="checkbox" name="confirm_delete"></label><button>保存全局配置</button></form></div><div class="card"><h2>手动完结清单</h2><p>每行一个漫画标题或数字 ID；仅影响自动完结识别。推荐在漫画详情中管理单书策略。</p><form method="post" action="/manual"><input type="hidden" name="csrf" value="{TOKEN}"><textarea name="manual">{escape(manual)}</textarea><button>保存清单</button></form></div>'''
        return layout("功能配置", "/settings", body, message)


if __name__ == "__main__":
    if not PASSWORD:
        raise SystemExit("必须设置非空的 WEBUI_PASSWORD 才能启动管理界面")
    threading.Thread(target=scheduler, daemon=True).start()
    server = ThreadingHTTPServer((os.environ.get("WEBUI_HOST", "0.0.0.0"), int(os.environ.get("WEBUI_PORT", "8765"))), Handler)
    log.info("管理界面监听 %s:%s", *server.server_address)
    server.serve_forever()
