#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
NAS 漫画归档器 / Manga Archiver
================================

把 Suwayomi 已下载（DOWNLOAD_AS_CBZ=true）的「已完结」漫画，按顺序合并为
「整本」CBZ，并投递到 Komga 漫画库目录。Komga 扫描后即为「一个系列、一本书」。

完结判定（两种方式，可同时使用）：
  1. 自动：查询 Suwayomi GraphQL，manga.status 属于 COMPLETED_STATUSES 的漫画。
  2. 手动：
     a) 在 CONFIG_DIR/manual_completed.txt 中逐行写「漫画标题」或「Suwayomi manga id」；
     b) 在 Suwayomi 里把漫画加入名为 COMPLETED_CATEGORY 的分类（默认「已完结」）。

用法：
  python archiver.py            # 按 INTERVAL_SECONDS 循环运行（Docker 默认）
  python archiver.py --once     # 只跑一次
  python archiver.py --dry-run  # 只打印将要做什么，不写任何文件

合并逻辑：
  - 找到该漫画在下载目录中的文件夹（按标题归一化匹配）。
  - 收集章节单元（每话一个 .cbz，或每话一个图片文件夹），按文件名自然排序。
  - 逐话读取图片（不解码、不重新压缩，原样搬运），统一按全局序号重命名，
    写入一个新的 CBZ；再写入 ComicInfo.xml（Series/Number/Volume/PageCount）。
  - 幂等：state.json 记录章节指纹，章节无变化则跳过；新增章节会自动重新合并。

注意：本脚本只读取 Suwayomi 下载目录、只写入 Komga 库目录。默认不删除源文件。
"""

import os
import re
import sys
import json
import time
import shutil
import zipfile
import logging
import hashlib
import unicodedata
from io import BytesIO
import xml.sax.saxutils as saxutils
import xml.etree.ElementTree as ET
from PIL import Image, ImageOps, UnidentifiedImageError
from pathlib import Path
from datetime import datetime

try:
    import requests
except Exception:  # pragma: no cover
    requests = None


# ---------------------------------------------------------------------------
# 配置
# ---------------------------------------------------------------------------
def env_bool(name, default=False):
    v = os.environ.get(name)
    if v is None:
        return default
    return str(v).strip().lower() in ("1", "true", "yes", "y", "on")


def env_int(name, default):
    try:
        return int(os.environ.get(name, default))
    except Exception:
        return default


class Config:
    def __init__(self):
        self.suwayomi_url = os.environ.get("SUWAYOMI_URL", "http://suwayomi:4567").rstrip("/")
        self.suwayomi_user = os.environ.get("SUWAYOMI_USER", "")
        self.suwayomi_pass = os.environ.get("SUWAYOMI_PASS", "")
        self.download_dir = Path(os.environ.get("DOWNLOAD_DIR", "/downloads"))
        self.komga_library = Path(os.environ.get("KOMGA_LIBRARY", "/komga-library"))
        self.config_dir = Path(os.environ.get("CONFIG_DIR", "/config"))
        self.interval_seconds = env_int("INTERVAL_SECONDS", 21600)  # 默认 6 小时
        self.completed_statuses = {
            s.strip().upper()
            for s in os.environ.get("COMPLETED_STATUSES", "COMPLETED,PUBLISHING_FINISHED").split(",")
            if s.strip()
        }
        self.completed_category = os.environ.get("COMPLETED_CATEGORY", "已完结").strip()
        self.manga_mode = os.environ.get("MANGA_MODE", "YesAndRightToLeft").strip()
        self.move_source = env_bool("MOVE_SOURCE", False)
        self.dry_run = env_bool("DRY_RUN", False)
        self.output_name_template = os.environ.get("OUTPUT_NAME_TEMPLATE", "{series}.cbz")
        self.request_timeout = env_int("REQUEST_TIMEOUT", 30)
        self.max_zip_entry_mb = env_int("MAX_ZIP_ENTRY_MB", 200)  # 单页安全上限
        self.optimize_images = env_bool("OPTIMIZE_IMAGES", False)
        self.image_max_width = env_int("IMAGE_MAX_WIDTH", 1600)
        self.image_max_height = env_int("IMAGE_MAX_HEIGHT", 2400)
        self.image_quality = env_int("IMAGE_QUALITY", 82)
        self.pages_per_book = env_int("PAGES_PER_BOOK", 0)  # 0 表示不拆分
        if not (1 <= self.image_quality <= 95 and self.image_max_width > 0 and
                self.image_max_height > 0 and self.pages_per_book >= 0):
            raise ValueError("图片质量、尺寸或分册页数配置无效")

    @property
    def state_file(self) -> Path:
        return self.config_dir / "state.json"

    @property
    def manual_file(self) -> Path:
        return self.config_dir / "manual_completed.txt"


# ---------------------------------------------------------------------------
# 日志
# ---------------------------------------------------------------------------
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
    stream=sys.stdout,
)
log = logging.getLogger("manga-archiver")


# ---------------------------------------------------------------------------
# 工具函数
# ---------------------------------------------------------------------------
IMG_EXTS = {".jpg", ".jpeg", ".png", ".webp", ".gif", ".bmp", ".avif", ".jxl", ".tif", ".tiff"}


def normalize(s: str) -> str:
    """归一化名称，用于标题与文件夹名匹配（保留中日韩文字与字母数字）。"""
    if s is None:
        return ""
    s = str(s).lower()
    # 去掉常见分隔/标点与空白
    s = re.sub(r"[\s\-_\.\[\]\(\)（）【】,，。:：;；!！?？~～'\"`·、/\\|+&]+", "", s)
    return s


def natural_key(s: str):
    """自然排序 key：'第9话' 排在 '第10话' 前面。"""
    parts = re.split(r"(\d+)", str(s))
    key = []
    for p in parts:
        if p.isdigit():
            key.append((1, int(p)))
        else:
            key.append((0, p.lower()))
    return key


def sha1_of(text: str) -> str:
    return hashlib.sha1(text.encode("utf-8", "ignore")).hexdigest()


def safe_name(value: str) -> str:
    """Make an API-supplied title safe as one filesystem path component."""
    value = unicodedata.normalize("NFKC", str(value))
    value = "".join("_" if c in '/\\<>:\"|?*' or ord(c) < 32 or ord(c) == 127 else c for c in value).strip(" .")
    if value in ("", ".", ".."):
        raise ValueError("漫画标题不能用作文件名")
    return value[:180].rstrip(" .")


# ---------------------------------------------------------------------------
# Suwayomi API 客户端
# ---------------------------------------------------------------------------
class Suwayomi:
    def __init__(self, cfg: Config):
        self.cfg = cfg
        self.endpoint = f"{cfg.suwayomi_url}/api/graphql"
        self.auth = None
        if cfg.suwayomi_user:
            self.auth = (cfg.suwayomi_user, cfg.suwayomi_pass)

    def graphql(self, query: str, variables=None):
        if requests is None:
            raise RuntimeError("未安装 requests 库")
        payload = {"query": query}
        if variables:
            payload["variables"] = variables
        r = requests.post(
            self.endpoint,
            json=payload,
            auth=self.auth,
            timeout=self.cfg.request_timeout,
        )
        r.raise_for_status()
        data = r.json()
        if data.get("errors"):
            raise RuntimeError(f"GraphQL 错误: {data['errors']}")
        return data.get("data", {})

    def get_library_mangas(self):
        """返回库中漫画列表 [{id,title,status}]。多套查询依次尝试，兼容不同版本。"""
        candidate_queries = [
            """
            query {
              mangas(condition: {inLibrary: true}) {
                nodes { id title status sourceId inLibrary }
              }
            }
            """,
            """
            query {
              mangas(filter: {inLibrary: true}) {
                nodes { id title status sourceId inLibrary }
              }
            }
            """,
            """
            query {
              mangas {
                nodes { id title status sourceId }
              }
            }
            """,
        ]
        last_err = None
        for q in candidate_queries:
            try:
                data = self.graphql(q)
                nodes = (((data or {}).get("mangas") or {}).get("nodes")) or []
                if nodes:
                    return nodes
                # 查询成功但为空，可能是筛选条件不匹配，继续尝试下一套
                last_err = "空结果"
            except Exception as e:  # noqa
                last_err = str(e)
                continue
        if last_err:
            log.warning("查询 Suwayomi 漫画库失败或为空：%s", last_err)
        return []

    def get_categories(self):
        try:
            data = self.graphql("query { categories { nodes { id name } } }")
            return (((data or {}).get("categories") or {}).get("nodes")) or []
        except Exception as e:  # noqa
            log.debug("查询分类失败：%s", e)
            return []

    def get_mangas_in_category(self, category_id):
        try:
            data = self.graphql(
                "query($cid: Int!) { mangas(condition: {categoryId: $cid}) { nodes { id title } } }",
                {"cid": category_id},
            )
            return (((data or {}).get("mangas") or {}).get("nodes")) or []
        except Exception as e:  # noqa
            log.debug("按分类查询漫画失败：%s", e)
            return []


# ---------------------------------------------------------------------------
# 完结判定
# ---------------------------------------------------------------------------
def read_manual_list(path: Path):
    """读取手动标注清单，返回 (titles:set, ids:set)。# 开头为注释。"""
    titles, ids = set(), set()
    if not path.exists():
        return titles, ids
    try:
        for line in path.read_text(encoding="utf-8").splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if re.fullmatch(r"\d+", line):
                ids.add(int(line))
            else:
                titles.add(line)
    except Exception as e:  # noqa
        log.warning("读取手动清单失败：%s", e)
    return titles, ids


def resolve_completed(cfg: Config):
    """
    返回已完结漫画集合：[(manga_id, title, reason)]
    reason ∈ {auto-status, manual-file, manual-category}
    """
    completed = {}  # key: (id or None, normalized title) -> (id, title, reason)

    # 1) 自动：状态
    api = Suwayomi(cfg)
    mangas = api.get_library_mangas()
    for m in mangas:
        status = str(m.get("status") or "").upper()
        if status in cfg.completed_statuses:
            title = m.get("title") or ""
            completed[(m.get("id"), normalize(title))] = (m.get("id"), title, f"auto-status={status}")
    log.info("自动识别完结（状态）：%d 部", sum(1 for v in completed.values() if v[2].startswith("auto")))

    # 2) 手动：分类
    if cfg.completed_category:
        cats = api.get_categories()
        target = None
        for c in cats:
            if (c.get("name") or "").strip() == cfg.completed_category:
                target = c
                break
        if target:
            for m in api.get_mangas_in_category(target["id"]):
                title = m.get("title") or ""
                key = (m.get("id"), normalize(title))
                if key not in completed:
                    completed[key] = (m.get("id"), title, f"manual-category={cfg.completed_category}")
            log.info("手动识别完结（分类「%s」）：已并入", cfg.completed_category)
        else:
            log.debug("未找到名为「%s」的分类", cfg.completed_category)

    # 3) 手动：文本清单（优先级最高，可覆盖状态判定）
    man_titles, man_ids = read_manual_list(cfg.manual_file)
    if man_titles or man_ids:
        log.info("手动清单：%d 个标题 / %d 个 id", len(man_titles), len(man_ids))
        # 与已知库漫画做匹配
        by_id = {m.get("id"): m for m in mangas}
        for mid in man_ids:
            m = by_id.get(mid)
            title = (m or {}).get("title") or f"manga_{mid}"
            completed[(mid, normalize(title))] = (mid, title, "manual-file(id)")
        for t in man_titles:
            nt = normalize(t)
            matched = False
            for m in mangas:
                if normalize(m.get("title")) == nt:
                    mid = m.get("id")
                    completed[(mid, nt)] = (mid, m.get("title") or t, "manual-file(title)")
                    matched = True
            if not matched:
                # 清单里的标题可能不在库中，也允许按标题匹配磁盘文件夹
                completed[(None, nt)] = (None, t, "manual-file(title)")

    return list(completed.values())


# ---------------------------------------------------------------------------
# 下载目录扫描与合并
# ---------------------------------------------------------------------------
def build_folder_index(download_dir: Path):
    """扫描下载目录，返回 {归一化文件夹名: [Path,...]}，仅收录含图片/压缩包的文件夹。"""
    index = {}
    if not download_dir.exists():
        return index
    for root, dirs, files in os.walk(download_dir):
        p = Path(root)
        lower_files = [f.lower() for f in files]
        has_cbz = any(f.endswith(".cbz") for f in lower_files)
        has_img = any(os.path.splitext(f)[1] in IMG_EXTS for f in lower_files)
        if has_cbz or has_img:
            index.setdefault(normalize(p.name), []).append(p)
    return index


def find_manga_dir(index, title: str):
    nt = normalize(title)
    if not nt:
        return None
    candidates = {candidate for paths in index.values() for p in paths
                  for candidate in (p, p.parent) if normalize(candidate.name) == nt}
    # Never silently choose a different work when titles normalize to the same name.
    return next(iter(candidates)) if len(candidates) == 1 else None


def resolve_folder(download_dir: Path, relative: str) -> Path:
    """Accept only a real folder below DOWNLOAD_DIR, never a symlink or absolute path."""
    if not relative or Path(relative).is_absolute() or "\\" in relative:
        raise ValueError("无效的下载文件夹")
    root = download_dir.resolve()
    candidate = download_dir / relative
    try:
        if candidate.resolve().relative_to(root) == Path("."):
            raise ValueError("不能选择下载根目录")
        candidate.resolve().relative_to(root)
    except ValueError as exc:
        raise ValueError("文件夹不在下载目录内") from exc
    if any(part in (".", "..") for part in Path(relative).parts):
        raise ValueError("无效的文件夹路径")
    current = download_dir
    for part in Path(relative).parts:
        current = current / part
        if current.is_symlink():
            raise ValueError("不允许符号链接")
    if not candidate.is_dir():
        raise ValueError("文件夹不存在")
    return candidate


def available_folders(download_dir: Path):
    """Find manga-sized folders and their chapter counts without modifying the disk."""
    index = build_folder_index(download_dir)
    candidates = set()
    for paths in index.values():
        for path in paths:
            if path.is_symlink():
                continue
            # Image chapters belong to their containing manga; CBZ files are
            # already stored directly in the manga directory.
            if any(p.is_file() and p.suffix.lower() in IMG_EXTS for p in path.iterdir()):
                parent = path.parent
                candidates.add(parent if parent != download_dir and path in collect_chapter_units(parent) else path)
            else:
                candidates.add(path)
    folders = []
    for path in sorted(candidates, key=str):
        try:
            relative = path.relative_to(download_dir).as_posix()
            units = collect_chapter_units(resolve_folder(download_dir, relative))
            if units:
                folders.append({"path": relative, "name": path.name, "chapters": len(units)})
        except (ValueError, OSError):
            continue
    return folders


def load_policies(cfg: Config):
    path = cfg.config_dir / "policies.json"
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        return data if isinstance(data, dict) else {}
    except FileNotFoundError:
        return {}
    except (OSError, ValueError) as exc:
        log.warning("读取单项策略失败：%s", exc)
        return {}


def collect_chapter_units(manga_dir: Path):
    """返回按自然顺序排序的章节单元列表（.cbz 文件或图片文件夹）。"""
    units = []
    if any(p.is_file() and p.suffix.lower() in IMG_EXTS for p in manga_dir.iterdir()):
        return [manga_dir]
    for entry in manga_dir.iterdir():
        if entry.is_file() and entry.suffix.lower() in (".cbz", ".zip"):
            units.append(entry)
        elif entry.is_dir():
            try:
                if any(os.path.splitext(f.name)[1].lower() in IMG_EXTS for f in entry.iterdir() if f.is_file()):
                    units.append(entry)
            except Exception:
                pass
    # 若当前层没有单元，尝试下钻一层（兼容 source/title/chapter/... 结构）
    if not units:
        for sub in manga_dir.iterdir():
            if sub.is_dir():
                for entry in sub.iterdir():
                    if entry.is_file() and entry.suffix.lower() in (".cbz", ".zip"):
                        units.append(entry)
                    elif entry.is_dir():
                        try:
                            if any(os.path.splitext(f.name)[1].lower() in IMG_EXTS for f in entry.iterdir() if f.is_file()):
                                units.append(entry)
                        except Exception:
                            pass
    units.sort(key=lambda p: natural_key(p.name))
    return units


def iter_pages(unit: Path, max_bytes: int):
    """迭代一个章节单元中的页面，产出 (原始页名, bytes)。按自然顺序。"""
    if unit.is_file():
        with zipfile.ZipFile(unit, "r") as zf:
            names = [
                n for n in zf.namelist()
                if not n.endswith("/") and os.path.splitext(n)[1].lower() in IMG_EXTS
            ]
            names.sort(key=natural_key)
            for n in names:
                if zf.getinfo(n).file_size > max_bytes:
                    raise ValueError(f"图片超过单页大小限制：{n}")
                with zf.open(n) as image:
                    data = image.read(max_bytes + 1)
                if len(data) > max_bytes:
                    raise ValueError(f"图片超过单页大小限制：{n}")
                yield os.path.basename(n), data
    else:
        files = [f for f in unit.iterdir() if f.is_file() and f.suffix.lower() in IMG_EXTS]
        files.sort(key=lambda p: natural_key(p.name))
        for f in files:
            if f.stat().st_size > max_bytes:
                raise ValueError(f"图片超过单页大小限制：{f}")
            with f.open("rb") as image:
                data = image.read(max_bytes + 1)
            if len(data) > max_bytes:
                raise ValueError(f"图片超过单页大小限制：{f}")
            yield f.name, data


def build_comicinfo(meta, page_count):
    if meta.get("comicinfo") is not None:
        root = ET.fromstring(meta["comicinfo"])
        for tag, value in (("Number", meta.get("volume", 1)),
                           ("Volume", meta.get("volume", 1)), ("PageCount", page_count)):
            node = root.find(tag)
            if node is None:
                node = ET.SubElement(root, tag)
            node.text = str(value)
        return ET.tostring(root, encoding="utf-8", xml_declaration=True)

    def e(v):
        return saxutils.escape(str(v)) if v not in (None, "") else ""

    lines = [
        '<?xml version="1.0" encoding="utf-8"?>',
        '<ComicInfo xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" '
        'xmlns:xsd="http://www.w3.org/2001/XMLSchema">',
        f"  <Title>{e(meta.get('title'))}</Title>",
        f"  <Series>{e(meta.get('series'))}</Series>",
        f"  <Number>{int(meta.get('volume', 1))}</Number>",
        f"  <Volume>{int(meta.get('volume', 1))}</Volume>",
        f"  <Count>{int(meta.get('count', 1))}</Count>",
        f"  <PageCount>{page_count}</PageCount>",
    ]
    if meta.get("writer"):
        lines.append(f"  <Writer>{e(meta.get('writer'))}</Writer>")
    if meta.get("summary"):
        lines.append(f"  <Summary>{e(meta.get('summary'))}</Summary>")
    if meta.get("manga_mode"):
        lines.append(f"  <Manga>{e(meta.get('manga_mode'))}</Manga>")
    lines.append("  <Notes>merged by manga-archiver</Notes>")
    lines.append("</ComicInfo>")
    return "\n".join(lines)


def chapter_fingerprint(units):
    """章节集合指纹：任一章节文件名/大小/修改时间变化都会改变。"""
    items = []
    for u in units:
        try:
            st = u.stat()
            items.append(f"{u}|{st.st_size}|{st.st_mtime_ns}")
            if u.is_dir():
                for image in sorted(u.iterdir()):
                    if image.is_file() and image.suffix.lower() in IMG_EXTS:
                        img_stat = image.stat()
                        items.append(f"{image.name}|{img_stat.st_size}|{img_stat.st_mtime_ns}")
        except OSError:
            items.append(u.name)
    return sha1_of("\n".join(items))


def optimization_signature(cfg):
    return [cfg.optimize_images, cfg.image_max_width, cfg.image_max_height,
            cfg.image_quality, cfg.pages_per_book]


def optimize_page(name, data, cfg):
    """只在输出更小时采用 JPEG；动图和无法识别的格式保持原样。"""
    if not cfg.optimize_images or Path(name).suffix.lower() == ".gif":
        return name, data
    try:
        with Image.open(BytesIO(data)) as source:
            source.load()
            if getattr(source, "is_animated", False):
                return name, data
            image = ImageOps.exif_transpose(source)
            image.thumbnail((cfg.image_max_width, cfg.image_max_height), Image.Resampling.LANCZOS)
            if image.mode in ("RGBA", "LA") or (image.mode == "P" and "transparency" in image.info):
                background = Image.new("RGB", image.size, "white")
                background.paste(image.convert("RGBA"), mask=image.convert("RGBA").getchannel("A"))
                image = background
            else:
                image = image.convert("RGB")
            buffer = BytesIO()
            image.save(buffer, format="JPEG", quality=cfg.image_quality, optimize=True)
            encoded = buffer.getvalue()
            if len(encoded) < len(data):
                return str(Path(name).with_suffix(".jpg")), encoded
    except (UnidentifiedImageError, OSError, ValueError, Image.DecompressionBombError) as exc:
        log.warning("图片 %s 无法重编码，保留原图：%s", name, exc)
    return name, data


def book_paths(out_path, count):
    return [out_path] if count == 1 else [out_path.with_name(f"{out_path.stem} - {n:03d}{out_path.suffix}")
                                           for n in range(1, count + 1)]


def count_pages(units):
    """只读取章节目录和 ZIP 索引，不读取图片内容。"""
    total = 0
    for unit in units:
        if unit.is_file():
            with zipfile.ZipFile(unit) as zf:
                total += sum(not info.is_dir() and Path(info.filename).suffix.lower() in IMG_EXTS
                             for info in zf.infolist())
        else:
            total += sum(p.is_file() and p.suffix.lower() in IMG_EXTS for p in unit.iterdir())
    return total


def merge_book(units, out_path: Path, meta, cfg: Config, old_paths=(), progress=None, total_pages=None):
    """分卷流式写入临时文件，全部生成成功后再发布。返回页数与文件路径。"""
    out_path.parent.mkdir(parents=True, exist_ok=True)
    if progress:
        progress(stage="统计页数", pages_done=0, pages_total=0)
        if total_pages is None:
            total_pages = count_pages(units)
        progress(stage="压缩并写入", pages_done=0, pages_total=total_pages, volume=0)
    staged = []
    zout = None
    count = 0
    volume_pages = 0
    try:
        for unit in units:
            for orig_name, data in iter_pages(unit, cfg.max_zip_entry_mb * 1024 * 1024):
                if zout is None or (cfg.pages_per_book and volume_pages >= cfg.pages_per_book):
                    if zout:
                        zout.writestr("ComicInfo.xml", build_comicinfo(dict(meta, volume=len(staged)), volume_pages))
                        zout.close()
                    temp = out_path.with_name(f".{out_path.name}.part-{len(staged) + 1:03d}.tmp")
                    if temp.exists():
                        raise ValueError(f"存在未完成的临时文件：{temp}，请检查后移走")
                    zout = zipfile.ZipFile(temp, "w", zipfile.ZIP_STORED, allowZip64=True)
                    staged.append(temp)
                    volume_pages = 0
                name, data = optimize_page(orig_name, data, cfg)
                count += 1
                volume_pages += 1
                zout.writestr(f"{volume_pages:05d}{Path(name).suffix.lower() or '.jpg'}", data)
                if progress:
                    progress(stage="压缩并写入", pages_done=count, pages_total=total_pages,
                             volume=len(staged))
        if zout:
            zout.writestr("ComicInfo.xml", build_comicinfo(dict(meta, volume=len(staged)), volume_pages))
            zout.close()
            zout = None
        if not count:
            raise ValueError("未找到图片，拒绝创建空归档")
        paths = book_paths(out_path, len(staged))
        owned = set(old_paths)
        for path in paths:
            if path.is_symlink() or (path.exists() and path not in owned):
                raise ValueError(f"已有非本任务文件，拒绝覆盖：{path}")
        for path in owned:
            if path.is_symlink():
                raise ValueError(f"旧输出是符号链接，拒绝覆盖：{path}")
        if progress:
            progress(stage="发布文件", pages_done=count, pages_total=total_pages, volume=len(staged))
        # 保留旧文件作回滚，成功发布后再清理；失败时还原旧文件。
        backups = []
        published = []
        try:
            for path in owned:
                if path.exists():
                    backup = path.with_name(f".{path.name}.archive-backup")
                    if backup.exists():
                        raise ValueError(f"存在待恢复备份：{backup}")
                    os.replace(path, backup)
                    backups.append((path, backup))
            for temp, path in zip(staged, paths):
                os.replace(temp, path)
                published.append(path)
        except Exception:
            for path in published:
                path.unlink(missing_ok=True)
            for path, backup in backups:
                os.replace(backup, path)
            raise
        for _, backup in backups:
            backup.unlink()
        return count, paths
    finally:
        if zout:
            zout.close()
        for temp in staged:
            temp.unlink(missing_ok=True)


def resolve_library_book(cfg, relative):
    """仅允许处理 Komga 库下的普通 CBZ 文件。"""
    if not relative or Path(relative).is_absolute() or "\\" in relative or any(
        p in (".", "..") for p in Path(relative).parts
    ):
        raise ValueError("无效的漫画文件路径")
    root = cfg.komga_library.resolve()
    path = cfg.komga_library / relative
    path.resolve().relative_to(root)
    current = cfg.komga_library
    for part in Path(relative).parts:
        current = current / part
        if current.is_symlink():
            raise ValueError("不允许符号链接")
    if not path.is_file() or path.suffix.lower() != ".cbz":
        raise ValueError("只能选择库中的 CBZ 文件")
    return path


def optimize_existing_book(cfg, relative, dry_run=False, progress=None):
    source = resolve_library_book(cfg, relative)
    if progress:
        progress(stage="读取 CBZ 目录", pages_done=0, pages_total=0, volume=0)
    with zipfile.ZipFile(source) as zf:
        names = sorted((n for n in zf.namelist() if Path(n).suffix.lower() in IMG_EXTS
                        and not n.endswith("/")), key=natural_key)
        if not names:
            raise ValueError("CBZ 中没有图片")
        count = len(names)
        comicinfo = next((n for n in zf.namelist() if n.lower() == "comicinfo.xml"), None)
        original_meta = zf.read(comicinfo) if comicinfo and zf.getinfo(comicinfo).file_size < 1048576 else None
        if original_meta is not None:
            ET.fromstring(original_meta)
    if progress:
        progress(stage="目录统计完成" if dry_run else "准备优化", pages_done=0,
                 pages_total=count, volume=0)
    if dry_run:
        return {"pages": count, "books": (count - 1) // cfg.pages_per_book + 1 if cfg.pages_per_book else 1,
                "source_mb": round(source.stat().st_size / 1048576, 1)}
    # 只重处理单本，不能将已有的分册当成整本；分册用原始章节强制重建。
    if source.name.rsplit(" - ", 1)[-1].replace(".cbz", "").isdigit():
        raise ValueError("此文件可能是分册，请从下载章节重新归档，而非处理单个分册")
    original_size = source.stat().st_size
    meta = {"series": source.parent.name, "title": source.parent.name,
            "manga_mode": cfg.manga_mode, "comicinfo": original_meta}
    count, paths = merge_book([source], source, meta, cfg, old_paths=[source],
                              progress=progress, total_pages=count)
    return {"pages": count, "books": len(paths), "source_mb": round(original_size / 1048576, 1),
            "output_mb": round(sum(p.stat().st_size for p in paths) / 1048576, 1)}


# ---------------------------------------------------------------------------
# 状态
# ---------------------------------------------------------------------------
def load_state(path: Path):
    if path.exists():
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except Exception:
            log.warning("state.json 解析失败，重新开始")
    return {}


def save_state(path: Path, state):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")
    os.replace(tmp, path)


# ---------------------------------------------------------------------------
# 主流程
# ---------------------------------------------------------------------------
def run_once(cfg: Config, target=None, folder=None, force=False, progress=None) -> dict:
    stats = {"completed": 0, "merged": 0, "skipped": 0, "failed": 0}
    log.info("=" * 60)
    log.info("漫画归档器开始运行  dry_run=%s  move_source=%s", cfg.dry_run, cfg.move_source)
    if progress:
        progress(stage="扫描下载目录", pages_done=0, pages_total=0, volume=0)

    if not cfg.download_dir.exists():
        log.error("下载目录不存在：%s", cfg.download_dir)
        return stats

    policies = load_policies(cfg)
    manga_policies = policies.get("manga", {})
    folder_policies = policies.get("folders", {})
    completed = resolve_completed(cfg) if target is None and folder is None else []
    if target is not None:
        matches = [m for m in Suwayomi(cfg).get_library_mangas() if str(m.get("id")) == str(target)]
        if not matches:
            raise ValueError("未找到指定漫画 ID；请检查 Suwayomi 连接")
        manga = matches[0]
        completed = [(manga.get("id"), manga.get("title"), "manual-manga")]
    if folder is not None:
        manga_dir = resolve_folder(cfg.download_dir, folder)
        entry = folder_policies.get(folder, {})
        completed = [(None, entry.get("title") or manga_dir.name, "manual-folder")]
    if target is None and folder is None:
        for rel, entry in folder_policies.items():
            if entry.get("mode") == "auto" and not entry.get("manga_id"):
                try:
                    manga_dir = resolve_folder(cfg.download_dir, rel)
                    completed.append((None, entry.get("title") or manga_dir.name, f"auto-folder:{rel}"))
                except ValueError:
                    log.warning("自动文件夹已失效：%s", rel)
    stats["completed"] = len(completed)
    if not completed:
        log.info("没有需要归档的漫画")
        return stats

    index = build_folder_index(cfg.download_dir)
    state = load_state(cfg.state_file)
    state_changed = False

    handled_folders = set()
    for manga_id, title, reason in completed:
        if progress:
            progress(stage="检查归档任务", title=title or "未知作品", pages_done=0,
                     pages_total=0, volume=0)
        if not title:
            continue
        entry = manga_policies.get(str(manga_id), {}) if manga_id is not None else {}
        if target is None and folder is None and entry.get("mode") in ("manual", "skip"):
            stats["skipped"] += 1
            continue
        relative = folder if folder is not None else (reason.split(":", 1)[1] if reason.startswith("auto-folder:") else entry.get("folder"))
        try:
            manga_dir = resolve_folder(cfg.download_dir, relative) if relative else find_manga_dir(index, title)
        except ValueError as exc:
            log.warning("「%s」绑定的文件夹无效：%s", title, exc)
            stats["failed"] += 1
            continue
        if not manga_dir:
            log.warning("未能唯一匹配「%s」的下载文件夹，请在漫画详情中手动绑定", title)
            stats["skipped"] += 1
            continue
        relative = manga_dir.relative_to(cfg.download_dir).as_posix()
        if target is None and folder is None and relative in handled_folders:
            log.warning("同一文件夹被多个自动任务引用，跳过重复项：%s", relative)
            stats["skipped"] += 1
            continue
        folder_entry = folder_policies.get(relative, {})
        if target is None and folder is None and folder_entry.get("mode") in ("manual", "skip"):
            stats["skipped"] += 1
            continue
        if target is None and folder is None and reason.startswith("auto-folder:") and any(
            other_id is not None and other_title and normalize(other_title) == normalize(title)
            for other_id, other_title, _ in completed
        ):
            log.info("文件夹 %s 已由漫画 ID 管理，跳过文件夹自动任务", relative)
            continue
        if folder is not None or reason.startswith("auto-folder:"):
            manga_id = None

        units = collect_chapter_units(manga_dir)
        if not units:
            log.warning("「%s」目录下没有可用章节，跳过", title)
            continue
        handled_folders.add(relative)

        fp = chapter_fingerprint(units)
        key = str(manga_id) if manga_id is not None else f"folder:{relative}"
        try:
            safe_title = safe_name(title)
            out_name = cfg.output_name_template.format(series=safe_title)
            if Path(out_name).name != out_name or not out_name.lower().endswith(".cbz") or ".." in out_name:
                raise ValueError("非法的输出文件名模板")
            out_path = cfg.komga_library / safe_title / out_name
        except (ValueError, KeyError) as exc:
            log.error("输出路径无效：%s", exc)
            stats["failed"] += 1
            continue

        prev = state.get(key)
        if any(other_key != key and (record.get("output") == str(out_path) or
                str(out_path) in record.get("outputs", []))
               for other_key, record in state.items() if isinstance(record, dict)):
            log.error("输出 %s 已归属另一个漫画或文件夹，拒绝覆盖；请修改文件夹归档标题", out_path)
            stats["failed"] += 1
            continue
        old_paths = [Path(p) for p in prev.get("outputs", [prev.get("output", "")]) if p] if prev else []
        if any(p.parent != out_path.parent or p.suffix.lower() != ".cbz" for p in old_paths):
            log.error("记录中的旧输出路径无效，拒绝覆盖：%s", old_paths)
            stats["failed"] += 1
            continue
        if out_path.exists() and out_path not in old_paths:
            log.error("输出 %s 已存在但没有匹配的归档记录，拒绝覆盖", out_path)
            stats["failed"] += 1
            continue
        if not force and prev and prev.get("fingerprint") == fp and prev.get("optimization") == optimization_signature(cfg) and all(p.exists() for p in old_paths):
            log.info("「%s」无变化，跳过（%d 话）", title, len(units))
            stats["skipped"] += 1
            continue

        log.info(
            "合并「%s」：%d 话，%s → %s",
            title, len(units), reason, out_path,
        )
        if cfg.dry_run:
            if progress:
                progress(stage="预演完成", pages_done=0, pages_total=0, volume=0)
            stats["merged"] += 1
            continue

        meta = {
            "series": title,
            "title": f"{title}（全 1 卷）",
            "summary": f"由 {len(units)} 话合并（{units[0].name} … {units[-1].name}）",
            "manga_mode": cfg.manga_mode,
        }
        try:
            pages, outputs = merge_book(units, out_path, meta, cfg, old_paths, progress=progress)
        except Exception as e:  # noqa
            log.exception("合并失败：%s", e)
            stats["failed"] += 1
            continue

        if cfg.move_source:
            for u in units:
                try:
                    if u == manga_dir:
                        for image in u.iterdir():
                            if image.is_file() and image.suffix.lower() in IMG_EXTS:
                                image.unlink()
                    elif u.is_dir():
                        shutil.rmtree(u)
                    else:
                        u.unlink()
                except Exception as e:  # noqa
                    log.warning("删除源章节失败 %s：%s", u, e)

        state[key] = {
            "title": title,
            "chapters": len(units),
            "pages": pages,
            "output": str(out_path),
            "outputs": [str(p) for p in outputs],
            "optimization": optimization_signature(cfg),
            "fingerprint": fp,
            "reason": reason,
            "merged_at": datetime.now().isoformat(timespec="seconds"),
        }
        state_changed = True
        stats["merged"] += 1
        log.info("完成：「%s」→ %d 页，%d 话", title, pages, len(units))

    if state_changed and not cfg.dry_run:
        save_state(cfg.state_file, state)

    log.info(
        "本轮结束：完结 %d，合并 %d，跳过 %d，失败 %d",
        stats["completed"], stats["merged"], stats["skipped"], stats["failed"],
    )
    return stats


def main():
    cfg = Config()
    once = "--once" in sys.argv
    if "--dry-run" in sys.argv:
        cfg.dry_run = True

    if once:
        run_once(cfg)
        return

    if cfg.interval_seconds <= 0:
        run_once(cfg)
        return

    log.info("进入循环模式，间隔 %d 秒", cfg.interval_seconds)
    while True:
        try:
            run_once(cfg)
        except Exception as e:  # noqa
            log.exception("运行异常：%s", e)
        time.sleep(cfg.interval_seconds)


if __name__ == "__main__":
    main()
