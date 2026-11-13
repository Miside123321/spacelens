# -*- coding: utf-8 -*-
"""空间透镜 · WebView 版

思路：**Python 扫描引擎完全不动，只把界面层换成浏览器渲染。**
    Python 起本地 HTTP 服务 → 用 Edge 的「应用窗口」打开 → 界面是 HTML/CSS/JS

这样「毛玻璃(backdrop-filter) / 抗锯齿 / 丝滑动画」全是浏览器原生能力，
不用再像 Tk 那样手工算圆弧、超采样贴图、逐帧重画。

数据全部来自现成的 disk_surface_scan（优先读 7 天缓存，秒开）。
慢活儿（清理解析 / 软件统计 / 全盘搜索索引 / 软件图标）一律后台线程 + 轮询，
绝不阻塞界面 —— 这是 Tk 版踩过的坑。

接口一览：
    GET  /                     界面
    GET  /api/state            顶栏：目标盘 / 磁盘列表 / 总量 / 进度 / 状态
    GET  /api/rank?path=       文件夹排行（某一层的直接子目录）
    GET  /api/type?group=      类型分布（group 为空=图例，有值=该类型的最大文件）
    GET  /api/clean            清理建议（后台解析 + 轮询）
    GET  /api/soft             软件占用（后台解析 + 轮询）
    GET  /api/search?q=        全电脑搜索（后台建索引 + 轮询）
    GET  /api/icon?i=N         软件图标 PNG
    GET  /api/act?act=&arg=    动作：open/del/cleanall/uninstall/setdrive/rescan
"""
import ctypes
from ctypes import wintypes      # COM 取缩略图那段要用（原来只在函数里局部 import 过）
import json
import os
import socket
import string
import subprocess
import sys
import threading
import time
import urllib.parse
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import disk_surface_scan as core                     # noqa: E402

# 打包成 onefile 后 web/ 会被解到 _MEIPASS 里
ROOT = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
WEB = os.path.join(ROOT, "web")
PROFILE = os.path.join(os.environ.get("LOCALAPPDATA", os.path.expanduser("~")),
                       "DiskSurfaceScan", "webview")

CLEAN_BUDGET = 6.0        # 单个清理位置最多统计几秒
SOFT_DEADLINE = 150.0     # 软件统计总预算（秒）
SEARCH_MAX = 5000         # 搜索结果上限。普通查询（几百条）就是全量；
                          # 只有像 steam 这种命中几万条的才截断，并按相关度截
RANK_FILE_MAX = 2000      # 排行页每个目录最多列多少个文件。
                          # ★ 这个数就是"一个文件夹里最多能看到多少个文件"，
                          #   缩略图的上限只是跟着它走。视频文件夹动辄上千个，
                          #   400 太小了；2000 够覆盖绝大多数目录，
                          #   再大的目录（四万个文件那种）仍然只列最大的 2000 个
ICON_SIZE = 28            # 图标像素尺寸（浏览器里按 20px 显示，留点余量）
THUMB_DIR = os.path.join(core.CONFIG_DIR, "thumbs")
THUMB_SIZE = 256          # ★ 用 256：系统缩略图缓存的档位是 32/96/256/1024。
                          #   注意：**并不是**"非档位尺寸就取不到缓存"（v2.54.0 实测
                          #   128/160/192/256 的耗时没有差别，解码才是瓶颈），
                          #   选 256 是为了高 DPI 下够清楚 —— 显示时缩到 ~146px。
                          #   代价只是 PNG 体积：256 约 22KB、128 约 7KB。
THUMB_MAX = 2000          # 一次最多生成几张，跟着 RANK_FILE_MAX 走。
                          # 图片单个 1~10ms、视频 30~100ms（4 线程并行），
                          # 2000 个视频大约十几秒，而且是分批出的，边生成边显示
THUMB_SRC_MAX = 40 * 1024 * 1024   # 老路（PowerShell 读整张图解码）的上限
THUMB_COM_MAX = 32 * 1024 * 1024 * 1024   # Windows 缩略图接口的上限：它不读整份文件，
                                         # 视频动辄几百 MB~几 GB，40MB 那道闸对它没意义
                                         # （只留个大得离谱的上限防意外）
THUMB_EXT = {".jpg", ".jpeg", ".png", ".gif", ".bmp", ".tif", ".tiff",
             ".webp", ".heic", ".heif", ".avif", ".jxr", ".hdp",
             # 视频：Windows 的缩略图接口能给出一帧画面
             ".mp4", ".mkv", ".avi", ".mov", ".wmv", ".webm", ".m4v",
             ".mpg", ".mpeg", ".flv", ".ts", ".m2ts", ".3gp", ".rmvb"}
THUMB_COM = True          # 用 Windows 缩略图接口（快 + 认识视频）；失败自动退回 PowerShell
# 取图是 CPU + 磁盘的活，和 GPU 没关系（系统编解码器走 CPU）。
# 线程数按核心数走，上限 24：再多也不会更快（shell 缩略图缓存写入是串行的）。
THUMB_WORKERS = min(24, os.cpu_count() or 8)
# 一批缩略图最多等这么久（秒）。超时的条目当失败，别拖住整批。
THUMB_BATCH_TIMEOUT = 20
# 缩略图缓存上限（字节）。超了就按"最久没访问"删到 80%，避免无限长大。
# 一张 256px 的 PNG 约 20~80KB，512MB 大概能放 1~2 万张。
THUMB_CACHE_MAX = 1024 * 1024 * 1024         # 并行取图的线程数。★ v2.54.0 实测：图片 1→4 线程有效
                          #   （24 张 698→367ms），但 4→8 几乎不再涨；**视频不能加**
                          #   （8/16 线程会让成功率从 22/24 崩到 4/24、11/24）——
                          #   那条路内部是串行的，加线程只是制造争用。
THUMB_MINI = 32           # 小图档位。★ v2.54.0 起不再用：实测 32px 的解码不会被
                          #   256px 复用（缓存按尺寸档位存），等于每格解码两遍，
                          #   整屏 860→387ms。只为兼容老缓存里的 _t.png 保留。

LOCK = threading.RLock()
ST = {
    "target": "C:\\",
    "scan": None,          # 当前扫描结果（Scanner 或 CachedScan）
    "busy": False,         # 正在读缓存 / 扫描
    "phase": "",           # "" | "cache" | "scan"
    "prog": "",            # 扫描进度文字
    "msg": "",             # 出错信息
    "scanned_at": "",
    # 慢任务的缓存（都带 state: idle|running|done|error）
    "clean": {"state": "idle", "rows": [], "safe": 0, "caut": 0, "msg": "", "ts": 0},
    "soft": {"state": "idle", "rows": [], "third": 0, "sysv": 0, "msg": "",
             "ts": 0, "icons": False},
    "search": {"state": "idle", "q": "", "rows": [], "note": "", "ts": 0},
}
JOBS = {"clean": False, "soft": False, "icons": False, "index": False,
        "thumbs": False, "dup": False}

DUP_MIN = 256 * 1024                 # 小于这个的不看（小文件一堆，收益也低）
DUP_MARGIN = 64 * 1024               # 头/尾各取这么多字节做快速比对
DUP_VERIFY_BUDGET = 1536 * 1024 * 1024   # 全量复核的总预算（字节）
# 图片 + 视频。只找媒体文件时用这个白名单（默认就看这些）
DUP_MEDIA_EXT = {
    # 图片
    ".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp", ".tif", ".tiff",
    ".heic", ".heif", ".avif", ".raw", ".cr2", ".cr3", ".nef", ".arw", ".dng",
    # 视频
    ".mp4", ".mkv", ".avi", ".mov", ".wmv", ".flv", ".webm", ".m4v",
    ".mpg", ".mpeg", ".ts", ".m2ts", ".rmvb", ".3gp", ".vob",
}

DUP = {"state": "idle", "ms": "", "ts": 0, "groups": [], "n": 0,
       "files": 0, "cand": 0, "can": 0, "err": ""}

# ---------------------------------------------------------------- 界面偏好
# ★ 不能放浏览器 localStorage：服务端口每次启动都是随机的，而 localStorage
#   按 origin（含端口）隔离，换个端口就读不到 —— 设置等于每次都得重设。
#   所以落到 %LOCALAPPDATA%\DiskSurfaceScan\ui.json（跟扫描缓存同一个目录）。
PREFS_FILE = os.path.join(core.CONFIG_DIR, "ui.json")
PREFS = {"dupMediaOnly": True,        # 重复识别只找图片和视频（默认开）
         "animPress": True,            # 按下回弹
         "animRipple": True,           # 点击波纹
         "loadSweep": True,            # 缩略图占位的扫光：生成期间要有反馈
         "tileAnim": True,             # 卡片入场：错开时机的 spring 飞入（关掉=整体滑入）
         "bgAnim": True,               # 动态背景（光斑）
         "dupAnim": True,              # 查重展开动画（关掉瞬间展开）
         "searchFold": True,           # 搜索时把"命中文件夹的内容"折叠进文件夹
         "dupPic": True,               # 查重页要不要显示缩略图
         "filePic": True,              # 图片/视频文件要不要缩略图（独立开关）
         "folderPic": True,           # 文件夹用内容缩略图当门面（只对以文件为主的目录）
         "hideTopPic": True,          # 最外层文件夹不给缩略图（怕无意中露出隐私内容）
         "oneClick": True,            # 单击直接打开；关掉则是"先选中、双击才打开"
         "viewMode": "list",         # list = 卡片列表（默认）；grid = 方块平铺
         "barScale": "gamma",        # gamma = 压缩刻度（默认）；linear = 真实比例
         "memPage": False,            # 内存卡片页：默认关（它要每秒采样，关掉就零开销）
         "theme": "auto"}             # 外观：auto = 跟随系统（默认）；dark / light


def _load_prefs():
    try:
        with open(PREFS_FILE, encoding="utf-8") as f:
            d = json.load(f)
        if isinstance(d, dict):
            for k, v in d.items():
                if k in PREFS:
                    PREFS[k] = v
    except Exception:      # noqa: BLE001 文件不存在 / 坏了都走默认值
        pass


def _save_prefs():
    try:
        os.makedirs(core.CONFIG_DIR, exist_ok=True)
        with open(PREFS_FILE, "w", encoding="utf-8") as f:
            json.dump(PREFS, f, ensure_ascii=False, indent=1)
    except Exception:      # noqa: BLE001
        pass


def p_prefs():
    with LOCK:
        return dict(PREFS)


def do_setpref(kv):
    """arg 形如 barScale=linear"""
    if "=" not in (kv or ""):
        return "设置参数格式不对"
    k, v = [x.strip() for x in kv.split("=", 1)]
    if k not in PREFS:
        return "没有这个设置项：%s" % k
    if k == "barScale" and v not in ("gamma", "linear"):
        return "条形刻度只能是 gamma 或 linear"
    if k == "memPage":
        v = (v == "on")
    if k in ("folderPic", "hideTopPic", "oneClick", "dupMediaOnly",
             "animPress", "animRipple", "loadSweep", "tileAnim", "filePic", "dupPic",
             "dupAnim", "bgAnim", "searchFold"):
        v = (v == "1")
    if k == "dupMediaOnly":
        # 换了范围，之前那份结果就不作数了
        with LOCK:
            DUP.update(state="idle", ms="范围变了，重新扫一遍",
                       groups=[], n=0, can=0, files=0, cand=0)
    if k == "viewMode" and v not in ("list", "grid"):
        return "视图只能是 list 或 grid"
    if k == "theme" and v not in ("auto", "dark", "light"):
        return "外观只能是 auto / dark / light"
    with LOCK:
        PREFS[k] = v
    _save_prefs()
    return "设置已保存"


_load_prefs()

# ---------------------------------------------------------------- 存活判定
# ★ 绝对不能用「Edge 启动进程退出」来判断窗口关了：
#   同一个 --user-data-dir 第二次启动 msedge 时，启动进程会在 0.3 秒内把命令
#   交接给已有的浏览器进程然后自己退出，proc.wait() 立刻返回 —— 于是服务器
#   被关掉，而新开的那个窗口指向一个已经死掉的端口，永远停在
#   ERR_CONNECTION_REFUSED。真正的存活依据只能是「页面还在不在心跳」。
START = time.time()
ALIVE = {"last": 0.0, "ever": False, "bye": 0.0}
# 宽限期可以用环境变量覆盖，方便单独把看门狗测掉（不影响正常使用）
# ★ 12 秒太短：挂机/息屏/系统睡眠时浏览器会把后台定时器降频，
#   心跳断十几秒就被判成“窗口已关”——后端自己退出（就是用户碰到的“挂机就挂”）。
#   真正关窗口走的是 bye 那条路（BYE_GRACE=3 秒），不受这个影响。
PING_GRACE = float(os.environ.get("SPACELENS_PING_GRACE", "180"))   # 心跳断多久算窗口关了
BYE_GRACE = float(os.environ.get("SPACELENS_BYE_GRACE", "3"))      # 收到 bye 后的宽限
NO_PAGE_LIMIT = float(os.environ.get("SPACELENS_NOPAGE", "90"))    # 一直没页面连上就退出


def _touch():
    ALIVE["last"] = time.time()
    ALIVE["ever"] = True
    ALIVE["bye"] = 0.0


def _watchdog():
    while True:
        time.sleep(1.0)
        now = time.time()
        if ALIVE["bye"] and now - ALIVE["bye"] > BYE_GRACE:
            os._exit(0)
        if ALIVE["ever"] and now - ALIVE["last"] > PING_GRACE:
            os._exit(0)
        if not ALIVE["ever"] and now - START > NO_PAGE_LIMIT:
            os._exit(0)


# ---------------------------------------------------------------- 基础
def human(n):
    try:
        return core.human_size(n)
    except Exception:      # noqa: BLE001
        return "-"


def drives():
    """所有存在的盘符，形如 ['C:\\\\', ...]。"""
    out = []
    for ch in string.ascii_uppercase:
        d = ch + ":\\"
        if os.path.exists(d):
            out.append(d)
    return out


def drive_free(d):
    try:
        u = __import__("shutil").disk_usage(d)
        return u.free, u.total
    except OSError:
        return None, None


IMG_EXT = (".jpg", ".jpeg", ".png", ".gif", ".bmp", ".webp")
# ★ v1.0：文件夹门面也认视频了——以前只认 IMG_EXT，纯视频文件夹拿不到门面，
#   前端就会退回系统的黄色文件夹图标。视频走 COM 接口能给一帧画面。
FOLDER_MEDIA_EXT = IMG_EXT + (".mp4", ".mkv", ".avi", ".mov", ".wmv", ".webm",
                              ".m4v", ".mpg", ".mpeg", ".flv", ".ts", ".m2ts",
                              ".3gp", ".rmvb", ".heic", ".heif", ".avif")
FOLDER_PICK_MIN_FILES = 4      # 文件夹里至少这么多文件才值得拿一张图当门面


FOLDER_PICK_MAX = 8 * 1024 * 1024   # 门面图不用超过这个大小的


# 门面图的大小区间：太小的是图标（放大到格子里一片糊），太大解码慢（门面只要 256px）
FOLDER_PICK_MIN = 8 * 1024
# 这些格式解码快，同样合格时优先用（png 往往是大截图，最慢）
FOLDER_PICK_FAST = (".jpg", ".jpeg", ".jfif", ".webp", ".bmp")


def _pick_dir_image(children):
    """在一个目录的直属子项里挑一张图/视频，当这个文件夹的门面。

    ★ v1.0：从只认图片扩展到也认视频（FOLDER_MEDIA_EXT）。
      纯视频文件夹以前拿不到门面，前端会退回黄色文件夹图标。
      优先"还小但能看清"的那张：jpg 比 png 解码快得多，而门面只是 256px
      的小方块，用不着大图。达标区间 [FOLDER_PICK_MIN, FOLDER_PICK_MAX]
      里取最小的、jpg 优先；一个都不在区间里就退回"所有媒体里最小的那张"。
    """
    cand, small = [], None
    for it in children:
        try:
            nm, sz, is_dir = it[0], it[1], it[2]
        except (IndexError, TypeError):
            continue
        if is_dir or sz <= 0:
            continue
        ext = os.path.splitext(nm)[1].lower()
        if ext not in FOLDER_MEDIA_EXT:
            continue
        if small is None or sz < small[1]:
            small = (nm, sz)
        if FOLDER_PICK_MIN <= sz <= FOLDER_PICK_MAX:
            # 图片优先于视频（视频抽帧慢一点），快格式优先于慢格式
            is_img = 0 if ext in IMG_EXT else 1
            is_fast = 0 if ext in FOLDER_PICK_FAST else 1
            cand.append((is_img, is_fast, sz, nm))
    if cand:
        cand.sort()
        return cand[0][3]
    return small[0] if small else ""


def _pick_dir_media_list(children, max_n=4):
    """取文件夹里最多 max_n 个媒体文件（图片+视频），用于 2×2 合成门面。

    ★ v1.0 新增。返回文件名列表，按"图片优先、小文件优先"排序。
      单个媒体时直接用单图封面；2~4 个时合成 2×2；没有时返回空列表。
    """
    items = []
    for it in children:
        try:
            nm, sz, is_dir = it[0], it[1], it[2]
        except (IndexError, TypeError):
            continue
        if is_dir or sz <= 0:
            continue
        ext = os.path.splitext(nm)[1].lower()
        if ext not in FOLDER_MEDIA_EXT:
            continue
        is_img = 0 if ext in IMG_EXT else 1
        items.append((is_img, sz, nm))
    items.sort()
    return [it[2] for it in items[:max_n]]


def _dir_has_media(path):
    """这个目录的**直属子项**里有没有图/视频。

    ★ 用来决定"要不要给它做文件夹缩略图"。系统那张文件夹缩略图是
      "文件夹图形打底 + 内容叠上去"；目录里没有图/视频时，系统只能退化成
      一张纯文件夹图标（黄色那张）—— 那还不如直接显示 App 自己的图标。
      实测 90 个目录里 88% 都没有媒体，正是用户看到的一排黄文件夹。
    """
    try:
        with os.scandir(path) as it:
            for e in it:
                try:
                    if e.is_dir():
                        continue
                    if os.path.splitext(e.name)[1].lower() in THUMB_EXT:
                        return True
                except OSError:
                    pass
    except OSError:
        pass
    return False


def children_of(sc, path):
    """某个目录的直接子目录，按占用降序。

    ★ 坑：父目录 children 里子目录那一项的 size 恒为 0（只有文件才带大小），
      子目录的真实 size / nfiles 必须再查它自己的记录，否则整列都是 0 B。
    """
    try:
        rec = sc.folders.get(path)
    except Exception:      # noqa: BLE001
        return []
    if not rec:
        return []
    out = []
    for item in rec.get("children", []):
        nm, is_dir = item[0], item[2]
        if not is_dir:
            continue
        cp = os.path.join(path, nm)
        crec = sc.folders.get(cp) or {}
        row = {"size": crec.get("size", 0), "path": cp, "name": nm,
               "files": crec.get("nfiles", 0)}
        # ★ 有没有图/视频 —— 前端靠它决定"要不要向系统要文件夹缩略图"。
        #   没有的话要回来也是那张黄文件夹图标，不如直接显示 App 的图标。
        row["hasv"] = 0
        # ★ 只有"这个子目录本身就以文件为主"时才给它挑一张代表图。
        #   像 C:\Users 这种装着几十个子目录的，拿里面某一张图当门面毫无意义；
        #   而 Screenshots 这种 285 个文件、0 个子目录的，一张图就能代表它。
        cn = crec.get("children") or []
        # ★ 有没有图/视频，直接看扫描时就已经拿到的这份子项列表 ——
        #   原来这里 _dir_has_media(cp) 会再 os.scandir 一遍，整盘上千个文件夹
        #   就是白白多扫上千次目录。
        row["hasv"] = 1 if any(
            (not it[2]) and os.path.splitext(it[0])[1].lower() in THUMB_EXT
            for it in cn) else 0
        cnd = sum(1 for it in cn if it[2])          # 它自己有几个子目录
        cnf = crec.get("nfiles", 0)
        # 标出"这是扫描根目录的直接子目录" —— 界面上默认不给这一层缩略图（隐私）
        rt = os.path.normcase(os.path.normpath(getattr(sc, "root", "") or ""))
        pp = os.path.normcase(os.path.normpath(os.path.dirname(cp)))
        if pp == rt:
            row["top"] = 1
        # ★ 只要里面有一张图就给门面（用户明确说：随便找一张就行，不要求清晰）。
        #   以前这里还要求"文件数够多、且文件远多于子目录"，结果大量文件夹没有门面。
        pk = _pick_dir_image(cn)
        if pk:
            row["pick"] = os.path.join(cp, pk)
        out.append(row)
    out.sort(key=lambda r: -r["size"])
    return out


def child_files(sc, path, limit=200):
    """某个目录下的直接文件，按大小降序（要 <=0 字节的空文件直接跳过）。"""
    try:
        rec = sc.folders.get(path)
    except Exception:      # noqa: BLE001
        return []
    if not rec:
        return []
    out = []
    for item in rec.get("children", []):
        nm, sz, is_dir, g = item[0], item[1], item[2], item[3]
        if is_dir or sz <= 0:
            continue
        gi = g if isinstance(g, int) and 0 <= g < len(core.TYPE_GROUPS) \
            else len(core.TYPE_GROUPS) - 1
        out.append({"size": sz, "path": os.path.join(path, nm), "name": nm,
                    "kind": core.TYPE_GROUPS[gi][0], "g": gi,
                    "color": core.TYPE_GROUPS[gi][1]})
    out.sort(key=lambda r: -r["size"])
    return out[:limit]


# ---------------------------------------------------------------- 扫描
def _do_scan(force=False):
    """后台线程：先试缓存，没有就真扫。始终在锁外做重活。"""
    with LOCK:
        if ST["busy"]:
            # ★ 别直接丢掉。扫描正忙时点「重新扫描 / 切换磁盘」以前是直接 return，
            #   于是那次请求永远没人做，界面就一直停在"正在切换磁盘…" ——
            #   表现就是"点了重扫卡了好久、也没有任何进度"。
            #   这里记一笔，等这一轮跑完立刻再来一次。
            ST["want_scan"] = True
            return
        target = ST["target"]
        ST["busy"] = True
        ST["phase"] = "cache"
        ST["prog"] = "正在读取缓存…"
        ST["msg"] = ""
    try:
        # ★ 先把上次的结果读出来：一是正常启动直接用，二是重扫时拿它的
        #   total_files 当进度分母（不然百分比没有分母，只能干转圈）。
        prev = core.load_scan_cache(target)
        sc = None if force else prev
        if sc is None:
            with LOCK:
                ST["phase"] = "scan"
                ST["prog"] = "正在扫描…"
            sc = core.Scanner(target)
            stop = threading.Event()

            # 分母：上次扫描的总文件数。同一次扫描里它是固定的，
            # 所以百分比只会往上涨，不会忽大忽小。
            try:
                denom = int(getattr(prev.stats, "total_files", 0)) if prev else 0
            except Exception:      # noqa: BLE001
                denom = 0

            def poll():
                while not stop.is_set():
                    st = sc.stats
                    pct = -1
                    if denom > 0:
                        # 留 1% 给"收尾"（存缓存还要一点时间），到 99 就不再涨
                        pct = int(min(99, st.files * 100.0 / denom))
                    with LOCK:
                        ST["prog"] = "已扫描 %s 个文件 · %s%s" % (
                            "{:,}".format(st.files), human(st.bytes),
                            "" if pct < 0 else " · %d%%" % pct)
                    stop.wait(0.4)

            th = threading.Thread(target=poll, daemon=True)
            th.start()
            try:
                sc.scan()
            finally:
                stop.set()
            try:
                core.save_scan_cache(sc)
            except Exception:      # noqa: BLE001
                pass
            # 换了数据源 → 缓存失效
            with LOCK:
                ST["clean"] = {"state": "idle", "rows": [], "safe": 0, "caut": 0,
                               "msg": "", "ts": 0}
                ST["soft"] = {"state": "idle", "rows": [], "third": 0, "sysv": 0,
                              "msg": "", "ts": 0, "icons": False}
                ST["search"] = {"state": "idle", "q": "", "rows": [], "note": "", "ts": 0}
        with LOCK:
            ST["scan"] = sc
            ST["scanned_at"] = getattr(sc, "scanned_at", "")
            ST["prog"] = ""
        _MT_CACHE.clear()          # 换了数据源，修改时间的缓存作废
    except Exception as e:      # noqa: BLE001
        with LOCK:
            ST["msg"] = "扫描失败：%s" % e
    finally:
        with LOCK:
            ST["busy"] = False
            ST["phase"] = ""
            _ok = ST["scan"] is not None
            again = bool(ST.pop("want_scan", False))
        if _ok:
            _prewarm()
        if again:
            # 扫描期间被点过「重扫 / 切盘」：换完数据源立刻补跑一次
            _do_scan(True)


def _prewarm():
    """扫描一就绪，就**提前**把清理和软件的统计跑掉。

    这两个原本是按需触发的（第一次点进去才开始算），于是点「清理」还得先看
    几秒钟滚动条。反正这会儿是闲着的，开程序时就先算好，点进去直接出结果。
    跑在后台线程里，不影响扫描、也不影响界面（界面在 Edge 里）。
    """
    for fn in (p_clean, p_soft):
        try:
            fn()
        except Exception:      # noqa: BLE001
            pass


def kick_scan(force=False):
    threading.Thread(target=_do_scan, kwargs={"force": force}, daemon=True).start()


def _snapshot():
    with LOCK:
        return (ST["scan"], ST["target"], ST["busy"], ST["phase"],
                ST["prog"], ST["msg"], ST["scanned_at"])


# ---------------------------------------------------------------- 页面数据
def p_state():
    sc, target, busy, phase, prog, msg, sat = _snapshot()
    ds = []
    for d in drives():
        free, total = drive_free(d)
        ds.append({"letter": d, "free": free or 0, "total": total or 0,
                   "freeText": human(free) if free else "?",
                   "totalText": human(total) if total else "?",
                   "current": (d == target)})
    d = {"ready": sc is not None, "busy": busy, "phase": phase, "prog": prog,
         "msg": msg, "target": target, "drives": ds, "scannedAt": sat,
         "ver": core.APP_VERSION}
    if sc is not None:
        st = sc.stats
        free, _total = drive_free(target)
        d["stats"] = {
            "total": getattr(st, "total", 0),
            "totalText": human(getattr(st, "total", 0)),
            "files": getattr(st, "total_files", 0),
            "dirs": getattr(st, "total_dirs", 0),
            "freeText": human(free) if free else "?",
        }
        d["sub"] = "%s  ·  %s  ·  %s 个文件  ·  可用 %s" % (
            target, human(getattr(st, "total", 0)),
            "{:,}".format(getattr(st, "total_files", 0)),
            human(free) if free else "?")
    else:
        d["stats"] = {"total": 0, "totalText": "—", "files": 0, "dirs": 0,
                      "freeText": "?"}
        d["sub"] = prog or "正在准备…"
    return d


_MT_CACHE = {}


def _mtime_text(path):
    """最后修改时间。取不到就返回空串。

    排行页每翻一层目录都要给几十上百行取时间，所以带缓存；
    扫描结果本身是静态快照，重扫时统一清掉（见 _do_scan）。
    """
    if path in _MT_CACHE:
        return _MT_CACHE[path]
    try:
        t = time.strftime("%Y-%m-%d %H:%M", time.localtime(os.stat(path).st_mtime))
    except OSError:
        t = ""
    if len(_MT_CACHE) > 20000:      # 逛了很多目录就整个丢掉，别无限涨
        _MT_CACHE.clear()
    _MT_CACHE[path] = t
    return t


# 一次 /api/rank 里最多顺手捎回多少张已缓存的缩略图。
# 24 张 ≈ 1360x900 首屏（约 17 格）+ 下一排；一张 JPEG 约 12 KB，
# 加起来 300 KB 左右，走本地回环几乎不花时间。
RANK_THUMBS = 24
RANK_THUMB_SCAN = 80      # 最多往前找 80 行（每行一次 stat，再多就拖慢开目录）


def p_rank(path):
    sc = _snapshot()[0]
    if sc is None:
        return {"ready": False, "rows": [], "crumb": ""}
    cur = path or ST["target"]
    dirs = children_of(sc, cur)
    for r in dirs:
        r["isDir"] = True
    # ★ 只列子目录的话，点到最后一级会出现「这个文件夹下面是空的」，
    #   而用户想看的恰恰是哪些**文件**占地方。这里把文件也并进来：
    #   先子目录、后文件，各自按占用降序（和 Tk 版一致）。
    files = child_files(sc, cur, RANK_FILE_MAX)
    for r in files:
        r["isDir"] = False
        r["files"] = 0
    rows = dirs + files
    mx = max([r["size"] for r in rows] or [1])
    for i, r in enumerate(rows):
        r["i"] = i + 1
        r["sizeText"] = human(r["size"])
        r["frac"] = (r["size"] / float(mx or 1))
        # 修改时间：文件夹也有（内容一变它就变），跟资源管理器一致
    # 面包屑：从盘符往下逐级
    # ★ 修改时间每个文件要一次 os.stat —— 2000 行实测 511ms，是打开目录的大头
    #   （取数据本身只要 26ms）。os.stat 是系统调用、会释放 GIL，所以多线程是真并行。
    # ★ 不再逐个 os.stat：用 os.scandir 一次把目录列出来，DirEntry 的 stat 信息是同一次
    #   目录枚举里带回来的（Windows 上就是 FindFirstFile/FindNextFile 的返回值），不用再
    #   逐个开文件。实测 2000 行：逐个 os.stat 要 511ms，开 16 个线程也省不掉（慢在
    #   系统调用总额上）；scandir 一次走完只要几十毫秒。
    mt_of = {}
    try:
        with os.scandir(cur) as _it:
            for _e in _it:
                try:
                    mt_of[_e.name] = _e.stat(follow_symlinks=False).st_mtime
                except OSError:
                    pass
    except OSError:
        mt_of = {}
    for _r in rows:
        _mt = mt_of.get(_r.get("name"))
        if _mt is None:
            _r["mtimeText"] = _mtime_text(_r["path"])
        else:
            _r["mtimeText"] = time.strftime("%Y-%m-%d %H:%M", time.localtime(_mt))

    root = os.path.abspath(ST["target"])
    cur_abs = os.path.abspath(cur)
    # ★ v1.0.8 修复：不能 rstrip("\\/")！C:\ 会变成 C:，os.path.join("C:", "Users")
    #   在 Windows 上不会自动加反斜杠，结果是相对路径 C:Users，前端点面包屑
    #   就会拼到当前路径后面（C:\Users\wan\Desktop\Users\wan），卡死在空目录。
    crumbs = [{"name": ST["target"], "path": ""}]
    if cur_abs.lower() != root.lower():
        rel = cur_abs[len(root):].strip("\\/")
        acc = root
        for part in [p for p in rel.split(os.sep) if p]:
            acc = os.path.join(acc, part)
            crumbs.append({"name": part, "path": acc})
    # ★ 首屏提速：把**已经缓存好的**前几十张直接塞进这次响应。
    #   代价是每行一次 stat + 一次读文件，200 KB 出头；省下的是一整轮
    #   "渲染 → IntersectionObserver → 排队 → /api/thumbs 往返"（实测 375→180 ms）。
    #   没有缓存的（第一次看这个目录）这里什么也不加，照旧走后面的队列。
    _nt = 0
    for _r in rows[:RANK_THUMB_SCAN]:
        if _nt >= RANK_THUMBS:
            break
        _u = _data_big(_r["path"])
        if _u:
            _r["t"] = _u
            _nt += 1
    return {"ready": True, "rows": rows, "path": cur, "crumb": crumbs,
            "canUp": cur_abs.lower() != root.lower(),
            "nDirs": len(dirs), "nFiles": len(files),
            "truncated": len(files) >= RANK_FILE_MAX}


TYPE_SLICE_MAX = 10      # 二/三级最多画几个扇形，尾巴合并成「其他 N 项」
TYPE_MIN_FRAC = 0.012    # ★ 占比小于 1.2% 的直接并进「其他」。
                         #   只按名次切不够：0.01% 的项也会单独占一个扇形，
                         #   图上是一根看不见的丝，却还拖着一条引线和一个 0.0% 标注。


def _ext_group(e):
    """扩展名 → 类型下标（和 Scanner.type_stats 的算法保持一致）。"""
    return core.EXT_TO_GROUP.get(e.lstrip(".").lower(), len(core.TYPE_GROUPS) - 1)


def _with_colors(raw):
    """raw: [(name, bytes, count)] 已按大小降序 → 带颜色的扇形项。

    扩展名和文件夹没有固定配色，用黄金角旋转生成色相，相邻扇形颜色拉得开。

    选取规则（两个条件都要满足才单独成扇形）：
      · 排在前 TYPE_SLICE_MAX 名之内
      · 占比 >= TYPE_MIN_FRAC
    剩下的全并成「其他 N 项」。只按名次切的话，0.01% 的项也会单独占一格，
    图上是一根看不见的丝、却还拖着引线和 "0.0%" 标注。
    """
    total = sum(t[1] for t in raw) or 1
    head, tail = [], []
    for t in raw:
        if len(head) < TYPE_SLICE_MAX and t[1] / total >= TYPE_MIN_FRAC:
            head.append(t)
        else:
            tail.append(t)
    if not head and raw:            # 全都太小 → 至少留最大的那个，
        head, tail = raw[:1], raw[1:]   # 免得整张图只剩一个「其他」
    items = []
    for i, (n, b, c) in enumerate(head):
        items.append({"name": n, "bytes": b, "count": c,
                      "color": core.rank_color(i, 0.60), "key": n, "drill": True})
    if tail:
        items.append({"name": "其他 %d 项" % len(tail),
                      "bytes": sum(t[1] for t in tail),
                      "count": sum(t[2] for t in tail),
                      "color": core.rank_color(len(head), 0.40),
                      "key": None, "drill": False})
    return items


def _folder_breakdown(sc, group, ext):
    """某个 (类型, 扩展名) 的文件，按**所在文件夹**聚合，降序。

    用 all_items：它是惰性构建 + 之后缓存的，第一次要一秒左右。
    但这跑在 HTTP 工作线程里，浏览器那头完全不受影响（这正是 Web 版的好处）。
    """
    try:
        items = sc.all_items
    except Exception:      # noqa: BLE001
        return []
    root = getattr(sc, "root", None) or ST["target"]
    agg = {}
    for rec in items:
        try:
            full, _name, size, is_dir, g = rec[0], rec[1], rec[2], rec[3], rec[4]
        except (IndexError, TypeError):
            continue
        if is_dir or size <= 0 or g != group:
            continue
        if os.path.splitext(full)[1].lower() != ext:
            continue
        k = _top_key(os.path.dirname(full), root)
        cur = agg.get(k)
        if cur is None:
            agg[k] = [size, 1]
        else:
            cur[0] += size
            cur[1] += 1
    out = [(d, b, c) for d, (b, c) in agg.items()]
    out.sort(key=lambda r: -r[1])
    return out


def _top_key(path, root):
    r"""把「文件所在目录」归到 **盘根 + 前两级目录**。

    ★ 直接用直接父目录会碎得没法看：.dll 散在 27232 个文件夹里，最大的一项
      只占 5%，扇形图 80% 被一个「其他」吃掉，等于没有信息。归到前两级之后，
      粒度才看得出东西堆在哪（Windows\System32、Windows\WinSxS、Program Files…）。
    """
    try:
        rel = os.path.relpath(path, root)
    except ValueError:
        return path
    if rel.startswith(".."):
        return path
    parts = [p for p in rel.split(os.sep) if p and p != "."][:2]
    return os.path.join(root, *parts) if parts else root


def p_type(group, ext=None):
    """类型分布。group=None → 一级（按类型）；给了 group → 二级（按扩展名）；
    再给 ext → 三级（按所在文件夹）。每级都是一张扇形图。"""
    sc = _snapshot()[0]
    empty = {"ready": False, "level": 1, "items": [], "crumb": [], "total": 0,
             "totalText": "—"}
    if sc is None:
        return empty
    # 面包屑只放**下钻路径**：标题已经写着「类型分布」了，再加一段就重复显示
    crumb = []

    if group is None or not (0 <= group < len(core.TYPE_GROUPS)):
        ts = sc.type_stats()
        raw = [(b, c, i) for i, (b, c) in enumerate(ts) if b > 0]
        raw.sort(reverse=True)
        total = sum(t[0] for t in raw) or 1
        items = [{"name": core.TYPE_GROUPS[i][0], "bytes": b, "count": c,
                  "color": core.TYPE_GROUPS[i][1], "key": i, "drill": True}
                 for b, c, i in raw]
        level = 1
        title = "类型分布"
        hint = "点扇形或图例继续往下分"

    elif not ext:
        raw = []
        for e, (b, c) in (sc.ext_stats or {}).items():
            if b <= 0 or _ext_group(e) != group:
                continue
            raw.append((e.lower() or "(无扩展名)", b, c))
        raw.sort(key=lambda r: -r[1])
        total = sum(r[1] for r in raw) or 1
        items = _with_colors(raw)
        gname = core.TYPE_GROUPS[group][0]
        crumb.append({"name": gname, "group": group, "ext": None})
        level = 2
        title = "类型分布"
        hint = "点扇形看这类文件都在哪些文件夹"

    else:
        raw = _folder_breakdown(sc, group, ext)
        total = sum(r[1] for r in raw) or 1
        items = _with_colors(raw)
        gname = core.TYPE_GROUPS[group][0]
        crumb.append({"name": gname, "group": group, "ext": None})
        crumb.append({"name": ext, "group": group, "ext": ext})
        level = 3
        title = "类型分布"
        hint = "点扇形打开所在文件夹"

    for i, it in enumerate(items):
        it["idx"] = i
        it["bytesText"] = human(it["bytes"])
        it["frac"] = it["bytes"] / float(total or 1)
    return {"ready": True, "level": level, "title": title, "hint": hint,
            "items": items, "crumb": crumb, "total": total,
            "totalText": human(total), "group": group, "ext": ext}


def _clean_worker():
    rows = []
    for name, raw, risk, advice in core.CLEAN_TARGETS:
        try:
            p = os.path.expandvars(raw)
            if not os.path.exists(p):
                continue
            sz = core.path_size(p, CLEAN_BUDGET)
        except OSError:
            continue
        if sz > 0:
            label, col = core.CLEAN_RISK.get(risk, ("", "#7F8FA3"))
            rows.append({"name": name, "path": p, "risk": risk,
                         "riskText": label, "riskColor": col,
                         "advice": advice, "size": sz, "sizeText": human(sz)})
    rows.sort(key=lambda r: -r["size"])
    mx = rows[0]["size"] if rows else 1
    for i, r in enumerate(rows):
        r["i"] = i + 1
        r["frac"] = r["size"] / float(mx or 1)
    safe = sum(r["size"] for r in rows if r["risk"] == "safe")
    caut = sum(r["size"] for r in rows if r["risk"] == "caution")
    with LOCK:
        ST["clean"] = {"state": "done", "rows": rows, "safe": safe, "caut": caut,
                       "msg": "" if rows else "没找到可清理的位置（可能都被占用，或路径不存在）",
                       "ts": time.time()}
        JOBS["clean"] = False


def p_clean():
    with LOCK:
        c = ST["clean"]
        if c["state"] in ("idle", "error") and not JOBS["clean"]:
            JOBS["clean"] = True
            ST["clean"] = dict(c, state="running", msg="")
            threading.Thread(target=_clean_worker, daemon=True).start()
        c = ST["clean"]
    return {"state": c["state"], "rows": c["rows"], "msg": c["msg"],
            "safeText": human(c["safe"]), "cautText": human(c["caut"])}


# ---- 软件 ----
def _hit(nm, toks):
    """词命中判断。★ 必须是"整词"，不能是子串。

    子串匹配的后果：名字里的 "man" 会撞上 "installmanager"，
    发行商里的 "games" 会撞上所有游戏公司的目录 —— 一个软件能认领 20 个目录。
    英文按字母/数字边界判断；中文没有词边界，仍按子串。
    """
    for t in toks:
        if any("\u4e00" <= ch <= "\u9fff" for ch in t):
            if t in nm:
                return True
            continue
        i = nm.find(t)
        while i >= 0:
            before = nm[i - 1] if i > 0 else ""
            j = i + len(t)
            after = nm[j] if j < len(nm) else ""
            if not before.isalnum() and not after.isalnum():
                return True
            i = nm.find(t, i + 1)
    return False


def _match_in(base, toks, pub):
    res = []
    try:
        if not os.path.isdir(base):
            return res
        with os.scandir(base) as it:
            for e in it:
                try:
                    if not e.is_dir(follow_symlinks=False):
                        continue
                except OSError:
                    continue
                nm = e.name.lower()
                if _hit(nm, toks) or (pub and _hit(nm, pub)):
                    res.append(e.path)
    except OSError:
        pass
    return res


def _cands(app, drives_, name_roots):
    out_ = []
    loc = app.get("loc") or ""
    if loc and os.path.isdir(loc):
        out_.append(os.path.normpath(loc))
    toks = core.norm_tokens(app["name"])
    if not toks:
        return out_
    pub = core.norm_tokens(app.get("publisher") or "")
    for raw in name_roots:
        out_.extend(_match_in(os.path.expandvars(raw), toks, pub))
    for d in drives_:
        for sub in ("Program Files", "Program Files (x86)", "Programs"):
            out_.extend(_match_in(os.path.join(d, sub), toks, pub))
    uniq = []
    for p in out_:
        if p not in uniq:
            uniq.append(p)
    uniq.sort(key=len)
    kept = []
    for p in uniq:
        if not any(p == q or p.startswith(q + os.sep) for q in kept):
            kept.append(p)
    return kept


def soft_kind(app, dirs):
    """系统组件还是自己装的第三方软件（和 Tk 版判定一致）。"""
    name = (app.get("name") or "").lower()
    pub = (app.get("publisher") or "").lower()
    loc = (app.get("loc") or "").lower()
    if "microsoft" in pub or "windows" in pub:
        return "系统"
    for kw in ("驱动程序包", "update for", "hotfix", "redistributable", "runtime",
               "visual c++", "framework", "sdk", "language pack", "windows "):
        if kw in name:
            return "系统"
    if loc.startswith("c:\\windows") or any(
            d.lower().startswith("c:\\windows") for d in dirs):
        return "系统"
    return "第三方"


def _soft_worker():
    ds = drives()
    deadline = time.time() + SOFT_DEADLINE
    try:
        apps = core.read_installed_apps()
    except Exception as e:      # noqa: BLE001
        with LOCK:
            ST["soft"] = {"state": "error", "rows": [], "third": 0, "sysv": 0,
                          "msg": "读注册表失败：%s（试试以管理员身份运行）" % e,
                          "ts": time.time(), "icons": False}
            JOBS["soft"] = False
        return

    # ★ 一个目录只能算给一个软件。
    #   以前每个注册表条目各扫各的：Autodesk 装了十几个组件，全都认领同一个
    #   C:\Program Files\Autodesk，于是十几行都写 1.1 GB —— 同一份磁盘被数了十几遍。
    #   现在先收集所有"认领"，再按强度排他分配，最后把父目录里已经算给别人的
    #   子目录扣掉（父目录的大小本来就包含子目录）。
    import re as _re
    size_cache = {}

    def size_of(p):
        if p not in size_cache:
            try:
                size_cache[p] = core.path_size(p, core.SOFT_SIZE_BUDGET)
            except OSError:
                size_cache[p] = 0
        return size_cache[p]

    n = len(apps)
    claims = []                 # (强度, 目录深度, 名字, app, 目录)
    for idx, app in enumerate(apps):
        if time.time() > deadline:
            break
        with LOCK:
            ST["soft"] = dict(ST["soft"], state="running",
                              msg="正在统计 %d / %d：%s" % (idx + 1, n, app["name"]))
        loc = (app.get("loc") or "").strip()
        try:
            loc_n = (os.path.normcase(os.path.normpath(loc))
                     if loc and os.path.isdir(loc) else "")
        except (OSError, ValueError):
            loc_n = ""
        toks = core.norm_tokens(app["name"])
        pub = core.norm_tokens(app.get("publisher") or "")
        # 完整软件名（去掉空格标点）：目录名里含有它，说明这个目录几乎肯定就是它
        full = _re.sub(r"[^0-9a-z\u4e00-\u9fff]", "", app["name"].lower())
        for d in _cands(app, ds, core.SOFT_NAME_ROOTS):
            nd = os.path.normcase(os.path.normpath(d))
            if loc_n and nd == loc_n:
                s = 100                 # 注册表里直接写着的安装位置，最高优先级
            else:
                base = os.path.basename(nd)
                base_n = _re.sub(r"[^0-9a-z\u4e00-\u9fff]", "", base)
                if len(full) >= 4 and full in base_n:
                    s = 80              # 目录名里就是完整软件名，最可信
                elif toks and _hit(base, toks):
                    s = 60              # 目录名整词命中软件名
                elif pub and _hit(base, pub):
                    s = 25              # 只命中发行商
                else:
                    s = 10
            claims.append((s, nd.count(os.sep), app["name"].lower(), app, nd))

    # 排他分配：强度高的先占，同强度时深的目录先占（越具体越可信）
    claims.sort(key=lambda c: (-c[0], -c[1], c[2], c[4]))
    owner = {}                  # 归一化目录 -> (名字 key, app, 目录)
    for s, _dep, k, app, nd in claims:
        if nd in owner:
            continue
        if size_of(nd) <= 0:
            continue
        owner[nd] = (k, app, nd)

    def under(child, parent):
        c = os.path.normcase(child)
        p = os.path.normcase(parent).rstrip("\\")
        return c != p and c.startswith(p + "\\")

    mine = {}
    for nd, (k, app, path) in owner.items():
        mine.setdefault(k, {"app": app, "dirs": []})["dirs"].append(nd)

    items_raw = []
    for k, v in mine.items():
        app = v["app"]
        # 自己名下互相嵌套的目录只留最外层（父目录已经包含子目录）
        outer = [p for p in v["dirs"] if not any(under(p, q) for q in v["dirs"])]
        used = []
        for p in outer:
            res = size_of(p)
            for nd2, (k2, _a2, p2) in owner.items():
                if k2 != k and under(p2, p):
                    res -= size_of(p2)      # 这块已经算给别的软件了，扣掉
            if res > 0:
                used.append((p, res))
        total = sum(x[1] for x in used)
        if total <= 0:
            continue                        # 全是别人的，那这一条就是重复项
        items_raw.append((total, app, used))

    items = sorted(items_raw, key=lambda r: -r[0])
    rows = []
    for i, (total, app, used) in enumerate(items):
        uniq, seen = [], set()
        for d, v in used:
            if d not in seen:
                seen.add(d)
                uniq.append((d, v))
        dv = {}
        for d, v in uniq:
            dr = os.path.splitdrive(os.path.abspath(d))[0].upper()
            if dr:
                dv[dr] = dv.get(dr, 0) + v
        disks = [{"letter": k, "sizeText": human(v)} for k, v in
                 sorted(dv.items(), key=lambda kv: -kv[1])]
        kind = soft_kind(app, [d for d, _v in uniq])
        # ★ 右键菜单用：每个盘只留**最大的那个**目录。
        #   按名字模糊匹配会把一堆无关目录也算进来（实测某游戏 dirList 有 20 条），
        #   一目录一条会变成 20 项的菜单；用户要的其实是"每个盘挑一个打开"。
        _best = {}
        for _d, _v in uniq:
            _dr = os.path.splitdrive(os.path.abspath(_d))[0].upper() or ""
            if _dr not in _best or _v > _best[_dr][1]:
                _best[_dr] = (_d, _v)
        # ★ 标签上的数字要和卡片一致（卡片是该盘**合计**），
        #   路径仍然用该盘最大的那个目录 —— 否则会出现
        #   "卡片写 C: 3.0 GB、菜单写 C: 1.1 GB" 这种对不上的情况。
        _cnt = {}
        for _d, _v in uniq:
            _dr = os.path.splitdrive(os.path.abspath(_d))[0].upper() or ""
            _cnt[_dr] = _cnt.get(_dr, 0) + 1
        menu_dirs = [{"letter": _k or "目录", "path": _p,
                      "sizeText": human(dv.get(_k, _v)),
                      "dirs": _cnt.get(_k, 1)}
                     for _k, (_p, _v) in sorted(_best.items(), key=lambda kv: -kv[1][1])]
        rows.append({"i": i + 1, "name": app["name"], "kind": kind,
                     "size": total, "sizeText": human(total),
                     "dirs": len(uniq), "disks": disks, "menuDirs": menu_dirs,
                     "dirList": [d for d, _v in uniq],
                     "publisher": app.get("publisher") or "—",
                     "openPath": app.get("loc") or (uniq[0][0] if uniq else ""),
                     "uninst": bool((app.get("uninst") or "").strip()),
                     "icon": i < core.SOFT_ICON_MAX})
    mx = rows[0]["size"] if rows else 1
    for r in rows:
        r["frac"] = r["size"] / float(mx or 1)
    third = sum(r["size"] for r in rows if r["kind"] == "第三方")
    grand = sum(r["size"] for r in rows)
    with LOCK:
        ST["soft"] = {"state": "done", "rows": rows, "third": third,
                      "sysv": grand - third,
                      "msg": "" if rows else "没有统计到软件占用（注册表里没读到已装软件）",
                      "ts": time.time(), "icons": False}
        JOBS["soft"] = False
    _icons_worker(rows)


def p_soft():
    with LOCK:
        c = ST["soft"]
        if c["state"] in ("idle", "error") and not JOBS["soft"]:
            JOBS["soft"] = True
            ST["soft"] = dict(c, state="running", msg="正在读取注册表并统计各软件占用…")
            threading.Thread(target=_soft_worker, daemon=True).start()
        c = ST["soft"]
    return {"state": c["state"], "rows": c["rows"], "msg": c["msg"],
            "thirdText": human(c["third"]), "sysText": human(c["sysv"]),
            "icons": c["icons"]}


# ---- 软件图标 ----
def _norm_name(s):
    """软件名归一化：只留字母数字和汉字，用来做宽松匹配。"""
    import re
    return re.sub(r"[^0-9a-z\u4e00-\u9fff]+", "", (s or "").lower())


def _clean_icon_path(raw):
    """把 DisplayIcon 洗成一个真实存在的可执行文件路径。

    ★ 顺序很关键：**先**展开环境变量、去引号、砍掉 ",索引"，**再**判断文件存在。
      原来判断在前、清理在后，等于白写 —— 带索引的值 100% 拿不到图标。
    """
    p = (raw or "").strip()
    if not p:
        return ""
    if p.startswith('"') and p.endswith('"') and len(p) > 1:
        p = p[1:-1]
    p = os.path.expandvars(p.strip().strip('"')).strip()
    if "," in p:                       # "xxx.exe",0  /  yyy.exe,-101
        head, tail = p.rsplit(",", 1)
        if tail.strip().lstrip("-").isdigit():
            p = head
    p = p.strip().strip('"').strip()
    if os.path.isfile(p):
        return p
    if os.path.isdir(p):               # 有的直接登记目录
        try:
            for f in sorted(os.listdir(p)):
                if f.lower().endswith(".exe"):
                    return os.path.join(p, f)
        except OSError:
            pass
    return ""


def _is_msi_icon(p):
    """MSI 缓存里的图标（C:\\WINDOWS\\Installer\\{GUID}\\...）。
    ExtractAssociatedIcon 对它经常抽出空白或通用图标，所以优先级要低。"""
    s = (p or "").lower()
    return "\\installer\\{" in s or s.startswith("c:\\windows\\installer")


def _pick_icon(name, by_exact, by_norm):
    """三级匹配：精确 -> 归一化 -> 互相包含。都不中再回落到目录里找 exe。"""
    src = by_exact.get(name or "")
    if src:
        return src
    n = _norm_name(name)
    if not n:
        return ""
    src = by_norm.get(n)
    if src:
        return src
    if len(n) >= 4:
        for kn, ksrc in by_norm.items():
            if len(kn) >= 4 and (kn in n or n in kn):
                return ksrc
    return ""


# ---------------------------------------------------------------- Windows 缩略图接口
# IDE 里搜不到这些名字是正常的：全是 ctypes 直调 shell32 / gdiplus。
class _GUID(ctypes.Structure):
    _fields_ = [("Data1", ctypes.c_ulong), ("Data2", ctypes.c_ushort),
                ("Data3", ctypes.c_ushort), ("Data4", ctypes.c_ubyte * 8)]

    def __init__(self, v=None):
        super(_GUID, self).__init__()
        if v:
            self.Data1, self.Data2, self.Data3 = v[0], v[1], v[2]
            for i, b in enumerate(v[3]):
                self.Data4[i] = b


class _SIZE(ctypes.Structure):
    _fields_ = [("cx", ctypes.c_long), ("cy", ctypes.c_long)]


class _GPInput(ctypes.Structure):
    _fields_ = [("GdiplusVersion", ctypes.c_uint32),
                ("DebugEventCallback", ctypes.c_void_p),
                ("SuppressBackgroundThread", ctypes.c_int),
                ("SuppressExternalCodecs", ctypes.c_int)]


# {557CF406-...} GDI+ 的 PNG 编码器（现在用它）
_CLSID_PNG = _GUID((0x557CF406, 0x1A04, 0x11D3,
                    (0x9A, 0x73, 0x00, 0x00, 0xF8, 0x1E, 0xF3, 0x2E)))
# {557CF401-...} GDI+ 的 JPEG 编码器（照片用 JPEG 存小 5~8 倍）
_CLSID_JPEG = _GUID((0x557CF401, 0x1A04, 0x11D3,
                     (0x9A, 0x73, 0x00, 0x00, 0xF8, 0x1E, 0xF3, 0x2E)))
# {1D5BE4B5-...} "Quality" 参数
_GUID_QUALITY = _GUID((0x1D5BE4B5, 0xFA4A, 0x452D,
                       (0x9C, 0xDD, 0x5D, 0xB3, 0x51, 0x05, 0xE7, 0xEB)))
THUMB_QUALITY = 82        # JPEG 质量（82 肉眼看不出和原图缩略的差别，体积却很省）


class _EncParam(ctypes.Structure):
    _fields_ = [("Guid", _GUID), ("NumberOfValues", ctypes.c_ulong),
                ("Type", ctypes.c_ulong), ("Value", ctypes.c_void_p)]


class _EncParams(ctypes.Structure):
    _fields_ = [("Count", ctypes.c_uint), ("Parameter", _EncParam * 1)]
_IID_ISIIF = _GUID((0xBCC18B79, 0xBA16, 0x442F,
                    (0x80, 0xC4, 0x8A, 0x59, 0xC3, 0x0C, 0x46, 0x3B)))
_COM_STATE = {"gp": False}
_COM_LOCK = threading.Lock()


def _com_start():
    """GDI+ 全局只起一次（有锁）；COM 每个线程各初始化一次。

    并发取图时每个工作线程都会调它 —— 所以 GDI+ 那段落锁，CoInitializeEx 放锁外。
    """
    if not THUMB_COM:
        return False
    with _COM_LOCK:
        if not _COM_STATE["gp"]:
            try:
                import ctypes as _c
                shell32 = _c.oledll.shell32
                gdiplus = _c.windll.gdiplus
                shell32.SHCreateItemFromParsingName.argtypes = [
                    wintypes.LPCWSTR, _c.c_void_p, _c.POINTER(_GUID),
                    _c.POINTER(_c.c_void_p)]
                shell32.SHCreateItemFromParsingName.restype = _c.c_long
                gdiplus.GdiplusStartup.argtypes = [
                    _c.POINTER(_c.c_void_p), _c.POINTER(_GPInput), _c.c_void_p]
                gdiplus.GdipCreateBitmapFromHBITMAP.argtypes = [
                    wintypes.HBITMAP, wintypes.HPALETTE, _c.POINTER(_c.c_void_p)]
                gdiplus.GdipSaveImageToFile.argtypes = [
                    _c.c_void_p, wintypes.LPCWSTR, _c.POINTER(_GUID),
                    _c.POINTER(_EncParams)]
                gdiplus.GdipDisposeImage.argtypes = [_c.c_void_p]
                # 缩图用：GdipGetImageThumbnail 按"塞进 size×size"等比缩。
                # ★ 必须声明 argtypes：64 位下不声明，byref 的指针会被当成 int 截断。
                gdiplus.GdipGetImageThumbnail.argtypes = [
                    _c.c_void_p, _c.c_uint, _c.c_uint,
                    _c.POINTER(_c.c_void_p), _c.c_void_p, _c.c_void_p]
                # ★ v1.0：文件夹 2×2 合成需要的 GDI+ 函数
                gdiplus.GdipCreateBitmapFromFile.argtypes = [
                    wintypes.LPCWSTR, _c.POINTER(_c.c_void_p)]
                gdiplus.GdipGetImageGraphicsContext.argtypes = [
                    _c.c_void_p, _c.POINTER(_c.c_void_p)]
                gdiplus.GdipDrawImageRectI.argtypes = [
                    _c.c_void_p, _c.c_void_p, _c.c_int, _c.c_int,
                    _c.c_int, _c.c_int]
                gdiplus.GdipDeleteGraphics.argtypes = [_c.c_void_p]
                gdiplus.GdipCreateSolidFill.argtypes = [
                    _c.c_uint, _c.POINTER(_c.c_void_p)]
                gdiplus.GdipFillRectangle.argtypes = [
                    _c.c_void_p, _c.c_void_p, _c.c_float, _c.c_float,
                    _c.c_float, _c.c_float]
                gdiplus.GdipDeleteBrush.argtypes = [_c.c_void_p]
                # ★ v1.0.1：合成时保持比例需要的尺寸查询
                gdiplus.GdipGetImageWidth.argtypes = [
                    _c.c_void_p, _c.POINTER(_c.c_uint)]
                gdiplus.GdipGetImageHeight.argtypes = [
                    _c.c_void_p, _c.POINTER(_c.c_uint)]
                tok = _c.c_void_p()
                gi = _GPInput(1, None, 0, 0)
                if gdiplus.GdiplusStartup(_c.byref(tok),
                                          _c.byref(gi), None) != 0:
                    return False
                _COM_STATE["gp"] = True
            except Exception:      # noqa: BLE001
                return False
    try:
        ctypes.oledll.ole32.CoInitializeEx(None, 2)   # APARTMENTTHREADED
    except Exception:      # noqa: BLE001
        pass
    return _COM_STATE["gp"]


# ★ 方案3：图片直接用 Pillow 解码，跳过 COM Shell 层
_DIRECT_IMAGE_EXT = {".jpg", ".jpeg", ".png", ".gif", ".bmp", ".tif", ".tiff", ".webp"}

def _direct_image_thumb(src, size, dst):
    """直接用 Pillow 解码图片做 cover 缩略图，不走 COM。少一层 Shell 调用更快。"""
    try:
        from PIL import Image as PILImage
        with PILImage.open(src) as im:
            im = im.convert("RGB")
            w, h = im.size
            if w <= 0 or h <= 0:
                return False
            scale = max(size / w, size / h)
            nw = max(1, int(w * scale))
            nh = max(1, int(h * scale))
            im = im.resize((nw, nh), PILImage.LANCZOS)
            left = (nw - size) // 2
            top = (nh - size) // 2
            im = im.crop((left, top, left + size, top + size))
            tmp = dst + ".tmp"
            im.save(tmp, "JPEG", quality=THUMB_QUALITY)
            os.replace(tmp, dst)
            return os.path.getsize(dst) > 0
    except Exception:      # noqa: BLE001
        try:
            if os.path.isfile(dst):
                os.remove(dst)
        except OSError:
            pass
        return False


def _com_thumb(src, size, dst, folder=False):
    """取一张缩略图存成 PNG。成功返回 True。

    走 Explorer 那套（IShellItemImageFactory）：不用起进程，
    而且它认识视频（给一帧画面）、PDF —— PowerShell 的 System.Drawing 都不认识。
    ★ 方案3：图片文件直接走 _direct_image_thumb，跳过 COM。
    """
    if not folder:
        ext = os.path.splitext(src)[1].lower()
        if ext in _DIRECT_IMAGE_EXT:
            return _direct_image_thumb(src, size, dst)
    if not _COM_STATE["gp"]:
        return False
    c = ctypes
    try:
        p = c.c_void_p()
        hr = c.oledll.shell32.SHCreateItemFromParsingName(
            src, None, c.byref(_IID_ISIIF), c.byref(p))
        if hr != 0 or not p:
            return False
        vt = c.cast(p, c.POINTER(c.POINTER(c.c_void_p))).contents
        proto = c.WINFUNCTYPE(c.c_long, c.c_void_p, _SIZE, c.c_int,
                              c.POINTER(wintypes.HBITMAP))
        hbm = wintypes.HBITMAP()
        # 8 = SIIGBF_THUMBNAILONLY：只要真缩略图，不要退化成图标
        # 文件：8 = THUMBNAILONLY（只要真图，不要退化成文件类型图标）
        #       | 1 = BIGGERSIZEOK（缓存里有更大的就拿来用）
        # 文件夹：**不能**带 THUMBNAILONLY —— 实测对有些目录直接返回
        #       0x8004B200（失败）。系统给文件夹的缩略图本来就可能退化成图标，
        #       这正是资源管理器的行为：有多少给多少。
        # ★ 文件夹用 0：实测 0 才会真去生成缩略图（首次约 190ms），
        #   而 BIGGERSIZEOK(1) 会返回成功但没有位图（hr=0、HBITMAP 为空），
        #   看着像成功其实什么都没有。
        flags = 0 if folder else (8 | 1)
        hr = proto(vt[3])(p, _SIZE(size, size), flags, c.byref(hbm))
        c.WINFUNCTYPE(c.c_ulong, c.c_void_p)(vt[2])(p)      # Release
        if hr != 0 or not hbm.value:
            return False
        bmp = c.c_void_p()
        ok = False
        try:
            if c.windll.gdiplus.GdipCreateBitmapFromHBITMAP(
                    hbm, None, c.byref(bmp)) == 0:
                # 先写临时文件、成功后原子替换：中途被强杀也不会在缓存里
                # 留下半张图（那会让这一格永远破图且永不重做）
                #
                # ★ v3.37.0：缩到 size 见方 + JPEG(q82)。
                #   系统带 BIGGERSIZEOK 时经常回一张 960x1280 / 1280x720 的现成图，
                #   旧代码原样存 PNG —— 平均 263 KB（最大 2.5 MB）。整屏 17 张
                #   就是 4.4 MB 塞进一条 JSON，前端光传就要 86 ms，还要解 17 张大 PNG。
                #   缩完存 JPEG：263 KB → 12 KB，同一条请求 86 ms → 8 ms。
                tmp = dst + ".tmp"
                jpg = dst.lower().endswith(".jpg")
                # ★ v1.0.7：改用 Pillow 做 cover 裁剪，完全绕过 GDI+ 绘制。
                #   GDI+ 在多线程下直接 DrawImage 偶发重影/双画面；先 GetImageThumbnail
                #   再画又会被 contain 模式坑（横图压缩）。Pillow 单线程图像处理
                #   稳定，cover 逻辑简单可控。流程：COM 给的 HBITMAP → GDI+ 存临时
                #   PNG → Pillow 打开 → cover 裁到 size×size → 存最终 JPEG。
                raw_png = dst + "._raw.png"
                ok = c.windll.gdiplus.GdipSaveImageToFile(
                    bmp, raw_png, c.byref(_CLSID_PNG), None) == 0
                if ok:
                    try:
                        from PIL import Image as PILImage
                        with PILImage.open(raw_png) as im:
                            im = im.convert("RGB")
                            w, h = im.size
                            if w > 0 and h > 0:
                                scale = max(size / w, size / h)
                                nw = max(1, int(w * scale))
                                nh = max(1, int(h * scale))
                                im = im.resize((nw, nh), PILImage.LANCZOS)
                                left = (nw - size) // 2
                                top = (nh - size) // 2
                                im = im.crop((left, top, left + size, top + size))
                                if jpg:
                                    im.save(tmp, "JPEG", quality=THUMB_QUALITY)
                                else:
                                    im.save(tmp, "PNG")
                                ok = True
                            else:
                                ok = False
                    except Exception:      # noqa: BLE001
                        ok = False
                    finally:
                        try:
                            os.remove(raw_png)
                        except OSError:
                            pass
                if ok:
                    try:
                        os.replace(tmp, dst)
                    except OSError:
                        ok = False
        finally:
            if bmp:
                c.windll.gdiplus.GdipDisposeImage(bmp)
            c.windll.gdi32.DeleteObject(hbm)
        # ★ 护栏：文件不存在、或者 0 字节，都不算成功，并且把它删掉。
        #   不然 0 字节的缓存会被后面的 isfile 当成"已经有了"，
        #   那一格永远显示破图，还再也不会重新生成。
        if ok:
            try:
                if os.path.getsize(dst) > 0:
                    return True
            except OSError:
                pass
        try:
            if os.path.isfile(dst):
                os.remove(dst)
        except OSError:
            pass
        return False
    except Exception:      # noqa: BLE001
        return False


def _draw_image_cover(gdiplus, graphics, img, dx, dy, dw, dh):
    """把 img 等比缩放后居中裁剪填满 (dx,dy,dw,dh) 格子，不拉伸变形。

    ★ v1.0.1 新增。cover 模式：scale = max(dw/w, dh/h)，超出格子的部分裁掉。
    横图裁左右、竖图裁上下，视觉上和手机相册/资源管理器的缩略图一致。
    """
    c = ctypes
    w = c.c_uint()
    h = c.c_uint()
    if gdiplus.GdipGetImageWidth(img, c.byref(w)) != 0:
        return
    if gdiplus.GdipGetImageHeight(img, c.byref(h)) != 0:
        return
    iw, ih = w.value, h.value
    if iw <= 0 or ih <= 0:
        return
    scale = max(dw / iw, dh / ih)
    tw = int(iw * scale)
    th = int(ih * scale)
    tx = dx + (dw - tw) // 2
    ty = dy + (dh - th) // 2
    gdiplus.GdipDrawImageRectI(graphics, img, tx, ty, tw, th)


def _compose_folder_thumb(src_files, size, dst):
    """把最多 4 张缩略图合成 2×2 门面图，存到 dst（JPEG）。成功返回 True。

    ★ v1.0 新增。文件夹有多个媒体文件时，不再只拿一张当门面，
      而是合成 2×2 预览，和资源管理器的文件夹缩略图视觉一致，
      但用的是真实内容（系统对普通文件夹只给黄色图标）。
      单张时直接铺满，2~4 张时 2×2 排列。
    """
    if not _COM_STATE["gp"] or not src_files:
        return False
    c = ctypes
    gdiplus = c.windll.gdiplus
    imgs = []
    bmp = c.c_void_p()
    g = c.c_void_p()
    hbm = None
    try:
        # 加载每张缩略图
        for sf in src_files[:4]:
            try:
                img = c.c_void_p()
                if gdiplus.GdipCreateBitmapFromFile(sf, c.byref(img)) == 0 and img:
                    imgs.append(img)
            except Exception:      # noqa: BLE001
                pass
        if not imgs:
            return False
        # 创建目标位图：先建兼容 HBITMAP，再包成 GDI+ Bitmap
        hdc = c.windll.user32.GetDC(0)
        hbm = c.windll.gdi32.CreateCompatibleBitmap(hdc, size, size)
        c.windll.user32.ReleaseDC(0, hdc)
        if not hbm:
            return False
        if gdiplus.GdipCreateBitmapFromHBITMAP(hbm, None, c.byref(bmp)) != 0 or not bmp:
            return False
        # 获取 Graphics 并填深色背景（和 App 暗色主题一致）
        if gdiplus.GdipGetImageGraphicsContext(bmp, c.byref(g)) != 0 or not g:
            return False
        brush = c.c_void_p()
        if gdiplus.GdipCreateSolidFill(0xFF141428, c.byref(brush)) == 0 and brush:
            gdiplus.GdipFillRectangle(g, brush, 0.0, 0.0,
                                       float(size), float(size))
            gdiplus.GdipDeleteBrush(brush)
        # 绘制（★ v1.0.1：每张图保持宽高比，居中裁剪填满格子，不拉伸）
        n = len(imgs)
        if n == 1:
            _draw_image_cover(gdiplus, g, imgs[0], 0, 0, size, size)
        else:
            half = size // 2
            positions = [(0, 0), (half, 0), (0, half), (half, half)]
            for i, img in enumerate(imgs[:4]):
                x, y = positions[i]
                _draw_image_cover(gdiplus, g, img, x, y, half, half)
        # 保存为 JPEG（原子替换）
        tmp = dst + ".tmp"
        par = _EncParams()
        par.Count = 1
        c.memmove(c.byref(par.Parameter[0].Guid),
                   c.byref(_GUID_QUALITY), 16)
        par.Parameter[0].NumberOfValues = 1
        par.Parameter[0].Type = 4      # EncoderParameterValueTypeLong
        qv = c.c_ulong(THUMB_QUALITY)
        par.Parameter[0].Value = c.cast(c.byref(qv), c.c_void_p)
        ok = gdiplus.GdipSaveImageToFile(
            bmp, tmp, c.byref(_CLSID_JPEG), c.byref(par)) == 0
        if ok:
            try:
                os.replace(tmp, dst)
            except OSError:
                ok = False
        if ok:
            try:
                return os.path.getsize(dst) > 0
            except OSError:
                return False
        return False
    except Exception:      # noqa: BLE001
        return False
    finally:
        if g:
            gdiplus.GdipDeleteGraphics(g)
        if bmp:
            gdiplus.GdipDisposeImage(bmp)
        if hbm:
            c.windll.gdi32.DeleteObject(hbm)
        for img in imgs:
            gdiplus.GdipDisposeImage(img)
        try:
            if os.path.isfile(dst + ".tmp"):
                os.remove(dst + ".tmp")
        except OSError:
            pass


_PRUNE_STATE = {"t": 0.0}


def _old_png_key(nm):
    """老格式的大图缓存名：20 位十六进制 + .png。

    ★ v3.37.0 起大图改存 .jpg，这些再也不会被引用（小图是 *_t.png，不受影响）
    留着就是几百 MB 死数据，还会把缓存上限挤爆。
    """
    return (len(nm) == 24 and nm.endswith(".png")
            and all(ch in "0123456789abcdef" for ch in nm[:20]))


def _prune_thumbs():
    """缓存超过硬上限时，按"最久没被访问"删到 80%。

    为什么用 atime：缩略图是读的时候才算"用到"，扫描/预加载不会碰 atime，
    所以最久没看过的（可能整个文件夹都删了）会先被清掉。
    """
    try:
        if not os.path.isdir(THUMB_DIR):
            return 0
        items = []
        total = 0
        with os.scandir(THUMB_DIR) as it:
            for e in it:
                try:
                    if not e.is_file(follow_symlinks=False):
                        continue
                    st = e.stat(follow_symlinks=False)
                except OSError:
                    continue
                if _old_png_key(e.name):
                    try:
                        os.remove(e.path)
                        continue
                    except OSError:
                        pass
                total += st.st_size
                items.append((getattr(st, "st_atime", st.st_mtime), st.st_size, e.path))
        if total <= THUMB_CACHE_MAX:
            return 0
        target = int(THUMB_CACHE_MAX * 0.8)
        items.sort()                    # atime 小的在前 = 最久没看的先删
        freed = 0
        for _at, sz, p in items:
            if total - freed <= target:
                break
            try:
                os.remove(p)
                freed += sz
            except OSError:
                pass
        return freed
    except Exception:      # noqa: BLE001
        return 0


def _thumb_path(p):
    """缩略图缓存路径。带 mtime，原图改了自动换一张。"""
    import hashlib
    import stat as _stat
    try:
        st = os.stat(p)
        key = "%s|%d|%d" % (os.path.normcase(os.path.abspath(p)), int(st.st_mtime),
                            st.st_size)
        # ★ 文件夹的门面算法换过（系统文件夹图标 → 里面随便一张小图）。
        #   路径/mtime/大小 都没变，键也就没变 —— 于是老代码那张"黄文件夹壳"
        #   会被当成"已经有缓存"永远端出来。所以文件夹的键里带上算法版本号；
        #   图片/视频不动，它们的缓存一个都不用重做。
        if _stat.S_ISDIR(st.st_mode):
            key += "|cover2"
    except OSError:
        return ""
    # ★ v3.37.0：缓存从"原尺寸 PNG"改成"256 JPEG"，格式变了。键里带上版本，
    #   否则老 PNG 会被当成"已经有了"永远端出来（体积大 20 倍）。
    key += "|jpg2"   # ★ 方案3：版本号+1，清掉旧缓存避免重影图复用
    h = hashlib.sha1(key.encode("utf-8", "replace")).hexdigest()[:20]
    return os.path.join(THUMB_DIR, h + ".jpg")


def _thumb_mini_path(p):
    """和大图同一套键，只是换个后缀。"""
    f = _thumb_path(p)
    return (f[:-4] + "_t.png") if f else ""


def _thumb_url(p):
    """URL 用缓存文件名当键：文件名里含原图 mtime，图变了 URL 就变，
    所以可以给浏览器发 immutable 的永久缓存头。"""
    f = _thumb_path(p)
    return "/api/thumb?k=" + os.path.basename(f) if f else ""


def _clean_thumbs():
    """清掉 7 天没动过的缩略图（顺带控制目录大小）。"""
    try:
        if not os.path.isdir(THUMB_DIR):
            return
        now = time.time()
        with os.scandir(THUMB_DIR) as it:
            for e in it:
                try:
                    if now - e.stat(follow_symlinks=False).st_mtime > 7 * 24 * 3600:
                        os.remove(e.path)
                except OSError:
                    pass
    except OSError:
        pass


_CLEAN_STATE = {"t": 0.0, "busy": False}


def _clean_thumbs_async():
    """★ 缩略图清理必须离开请求路径。

    实测：缓存里有 31,786 个文件时，_clean_thumbs() 一次要 **10.1 秒**
    （每个文件一次 stat），而且绝大多数时候一个都删不掉。
    以前它挂在 _thumbs_worker 末尾 —— 也就是"只要这一批有图要生成"，
    那一条 /api/thumbs 就多等十几秒。用户看到的就是格子一直空着、图不来。
    现在丢到后台线程，并且一小时最多跑一次。
    """
    now = time.time()
    if _CLEAN_STATE["busy"] or now - _CLEAN_STATE["t"] < 3600:
        return
    _CLEAN_STATE["t"] = now

    def run():
        _CLEAN_STATE["busy"] = True
        try:
            _clean_thumbs()
        finally:
            _CLEAN_STATE["busy"] = False

    try:
        threading.Thread(target=run, daemon=True).start()
    except Exception:      # noqa: BLE001
        _CLEAN_STATE["busy"] = False


def _thumbs_worker(paths, mode="both"):
    """一次 PowerShell 把这一批图缩好。返回真正生成成功的路径列表。"""
    import tempfile
    work = []
    for p in paths[:THUMB_MAX]:
        # ★ 目录没有扩展名，不能拿扩展名去过滤它 —— 一过滤，下面所有
        #   "文件夹走系统缩略图"的分支就全成了死代码（w["dir"] 永远是 False）。
        _isd = os.path.isdir(p)
        if not _isd:
            ext = os.path.splitext(p)[1].lower()
            if ext not in THUMB_EXT:
                continue
        try:
            # ★ 目录的 size 是"目录项大小"（通常 0），不是里面内容的大小，
            #   拿它跟 THUMB_COM_MAX 比没有意义，直接跳过。
            sz = 0 if _isd else os.path.getsize(p)
        except OSError:
            continue
        if not _isd and sz > THUMB_COM_MAX:
            continue
        dst = _thumb_path(p)
        if not dst:
            continue
        # big = 太大，别交给 PowerShell 那条路（会整份读进内存）；COM 不受它限制
        work.append({"src": p, "dst": dst, "mini": _thumb_mini_path(p),
                     "ok": p, "big": False if _isd else (sz > THUMB_SRC_MAX),
                     "dir": _isd})
    def _ok_file(f):
        # ★ 只看"非空"不够：GdipSaveImageToFile 是原地写，进程被强杀会留下半截
        #   PNG —— 非空但解不开，于是那一格永远破图，而且因为"文件已存在"
        #   永远不会重做。所以顺带验一下 8 字节的 PNG 头。
        try:
            if os.path.getsize(f) < 16:
                return False
            with open(f, "rb") as fh:
                head = fh.read(8)
            # 大图是 JPEG、小图还是 PNG —— 两种头都认，别再"解不开但永不重做"
            if head[:4] == b"\x89PNG":
                return True
            return head[:3] == b"\xff\xd8\xff"
        except OSError:
            return False
    need_dst = mode in ("both", "big")
    need_mini = mode in ("both", "mini")

    def _ready(w):
        """这一趟要的东西到位了吗 —— 别拿大图去判断小图那一趟。"""
        if w.get("dir"):
            # 文件夹只做大图，也不参与"小图那一趟"
            return (not need_dst) or _ok_file(w["dst"])
        if need_dst and not _ok_file(w["dst"]):
            return False
        if need_mini and not _ok_file(w["mini"]):
            return False
        return True

    def _missing(w):
        if w.get("dir"):
            return need_dst and not _ok_file(w["dst"])
        if need_dst and not _ok_file(w["dst"]):
            return True
        if need_mini and not _ok_file(w["mini"]):
            return True
        return False
    todo = [w for w in work if _missing(w)]
    if not todo:
        return [w["ok"] for w in work if _ready(w)]
    try:
        os.makedirs(THUMB_DIR, exist_ok=True)
    except OSError:
        return []
    # 超过上限就按最久没访问的删，防止缓存无限长。
    # ★ 扫一次 31,000 个文件要 100 ms，每批都扫等于白送一次卡顿 —— 两分钟最多一次。
    _now_p = time.time()
    if _now_p - _PRUNE_STATE["t"] > 120:
        _PRUNE_STATE["t"] = _now_p
        _prune_thumbs()
    # ---- 先用 Windows 自己的缩略图接口：快得多，而且视频也有画面 ----
    # ★ 并行做。视频取一帧要 70~400ms（图片只要 1~10ms），串行的话一个视频文件夹
    #   的总耗时就是它们相加。4 个线程各做各的（COM 是按线程初始化的，
    #   所以每个线程里都要 CoInitializeEx 一次）。
    left = []
    if _com_start():
        def one(w):
            try:
                if not _com_start():        # 本线程的 COM 初始化
                    return w
                # ★ 小图先做：它把"解码原图"这笔开销付掉，之后系统缓存住了，
                #   大图再要就很快。所以第一趟只做小图，能最快把画面铺上。
                # ★ 文件夹门面：直接拿里面一张**小**图当门面 ——
                #   用户要的就是这个："随便找一张，不要求清晰，只要快"。
                #   写进的还是文件夹自己的缓存文件，所以前端不管按哪条路径要，
                #   回来的都是照片，不会又是那张黄文件夹图标。
                src0 = w["src"]
                isdir = os.path.isdir(src0)
                if isdir:
                    # ★ v1.0：文件夹门面全面改进
                    #   1. 支持视频（以前只认图片，纯视频文件夹拿不到门面）
                    #   2. 多个媒体文件时合成 2×2 预览（以前只拿一张）
                    #   3. 没有媒体时直接不出图，绝不回退系统的黄色文件夹图标
                    try:
                        kids = [(e.name, e.stat(follow_symlinks=False).st_size,
                                 e.is_dir(follow_symlinks=False))
                                for e in os.scandir(src0)]
                    except OSError:
                        kids = []
                    media = _pick_dir_media_list(kids, 4)
                    if not media:
                        # 里面一个媒体都没有：别退回黄色文件夹图标，直接不出图，
                        # 界面显示 App 自己的图标（好看得多）。
                        return None
                    if len(media) == 1:
                        # ★ v1.0.2：单媒体也走 cover 合成，不用 _com_thumb
                        #   （_com_thumb 内部 GdipGetImageThumbnail 是 contain，
                        #    竖屏视频/图片会留上下黑边，用户说"比例不对"）。
                        #   先生成一张临时缩略图，再用 _compose_folder_thumb
                        #   做 cover（保持比例、填满、居中裁切），和多图一致。
                        if need_dst and not _ok_file(w["dst"]):
                            tmp = w["dst"] + "._p0.jpg"
                            if _com_thumb(os.path.join(src0, media[0]),
                                          THUMB_SIZE, tmp, False):
                                _compose_folder_thumb([tmp], THUMB_SIZE, w["dst"])
                            try:
                                os.remove(tmp)
                            except OSError:
                                pass
                    else:
                        # 多媒体：先各生成一张半尺寸缩略图，再用 GDI+ 合成 2×2
                        if need_dst and not _ok_file(w["dst"]):
                            half = max(64, THUMB_SIZE // 2)
                            tmp_files = []
                            for i, m in enumerate(media):
                                tmp = w["dst"] + "._p%d.jpg" % i
                                if _com_thumb(os.path.join(src0, m), half, tmp, False):
                                    tmp_files.append(tmp)
                            if tmp_files:
                                _compose_folder_thumb(tmp_files, THUMB_SIZE, w["dst"])
                            for tf in tmp_files:
                                try:
                                    os.remove(tf)
                                except OSError:
                                    pass
                    # 文件夹只做大图，不做小图；做完直接判断返回
                    if not need_dst or _ok_file(w["dst"]):
                        return None
                    return w
                # ---- 以下是文件的正常缩略图逻辑 ----
                if (need_mini and not _ok_file(w["mini"])):
                    _com_thumb(src0, THUMB_MINI, w["mini"], False)
                if need_dst and not _ok_file(w["dst"]):
                    _com_thumb(src0, THUMB_SIZE, w["dst"], False)
                # ★ 和 _ready() 用同一套判断
                if (not need_dst or _ok_file(w["dst"])) and \
                        (not need_mini or _ok_file(w["mini"])):
                    return None
            except Exception as e:      # noqa: BLE001
                # 别再静默吞：这一轮就是被静默吞掉的 NameError 坑了
                _COM_STATE["err"] = repr(e)[:160]
            return w
        # ★ 不能等一批全部做完才返回：单个文件可能让系统的缩略图接口卡住很久
        #   （坏文件、网络盘、正在写的视频……）。以前是 ex.map 全等，一条卡住
        #   = 整个请求不返回 = 前端那条管线永久停摆（整屏只剩占位块）。
        #   现在设一个总时限，超时的当失败，先把做完的返回。
        from concurrent.futures import ThreadPoolExecutor, as_completed
        ex = ThreadPoolExecutor(max_workers=THUMB_WORKERS)
        try:
            futs = [ex.submit(one, w) for w in todo]
            stop = time.time() + THUMB_BATCH_TIMEOUT
            for fu in as_completed(futs, timeout=max(1.0, stop - time.time())):
                try:
                    r = fu.result()
                except Exception:      # noqa: BLE001
                    r = None
                if r is not None:
                    left.append(r)
            left.extend(w for w, fu in zip(todo, futs) if not fu.done())
        except Exception:      # noqa: BLE001
            left = todo
        finally:
            # 不等那几个卡住的线程（它们在后台自己会结束或一直挂着，都无所谓了）
            ex.shutdown(wait=False)
        try:
            ctypes.oledll.ole32.CoUninitialize()
        except Exception:      # noqa: BLE001
            pass
    else:
        left = todo
    if not left:
        _clean_thumbs()
        return [w["ok"] for w in work if _ready(w)]
    # ---- 剩下 COM 取不到的，交给老的 PowerShell（只认图片格式）----
    # 太大的就别给了：那条路会把整张图读进内存
    # ★ 这条 PowerShell 兜底实际上永远没活干：THUMB_EXT 里的类型（图片 + 视频）
    #   COM 全都认识，真正取不到的那些再交给 System.Drawing 也一样取不到。
    #   而它每次起步就要 350ms、缩一张 617ms —— 以前只要有一个文件没做成
    #   就会把它叫起来，等于白等。只留 COM 明确不处理的扩展名。
    _ps_ext = {".pdf", ".ico", ".svg"}
    todo = [w for w in left if (not w.get("big")) and
            os.path.splitext(w["src"])[1].lower() in _ps_ext]
    jf = os.path.join(tempfile.gettempdir(), "spacelens_thumbs.json")
    try:
        with open(jf, "w", encoding="utf-8") as f:
            json.dump([{"src": w["src"], "dst": w["dst"], "mini": w["mini"]}
                       for w in todo], f, ensure_ascii=False)
    except OSError:
        return []
    # 等比缩到长边 THUMB_SIZE，最大不放大（小图保持原样，免得糊）
    ps = ("Add-Type -AssemblyName System.Drawing; "
          "$items = Get-Content -Raw -Encoding UTF8 '%s' | ConvertFrom-Json; "
          "foreach ($it in $items) { try { "
          "$img = [System.Drawing.Image]::FromFile($it.src); "
          # 大图
          "$s = [Math]::Min(%d / $img.Width, %d / $img.Height); "
          "if ($s -gt 1) { $s = 1 }; "
          "$w = [int]($img.Width * $s); $h = [int]($img.Height * $s); "
          "if ($w -lt 1) { $w = 1 }; if ($h -lt 1) { $h = 1 }; "
          "$b = New-Object System.Drawing.Bitmap $w, $h; "
          "$g = [System.Drawing.Graphics]::FromImage($b); "
          "$g.InterpolationMode = [System.Drawing.Drawing2D.InterpolationMode]::HighQualityBicubic; "
          "$g.DrawImage($img, 0, 0, $w, $h); "
          "$b.Save($it.dst, [System.Drawing.Imaging.ImageFormat]::Jpeg); "
          "$g.Dispose(); $b.Dispose(); "
          # 同一张图顺手缩一张很小的，前端先铺它（先糊后清）
          "$ts = [Math]::Min(%d / $img.Width, %d / $img.Height); "
          "if ($ts -gt 1) { $ts = 1 }; "
          "$mw = [int]($img.Width * $ts); $mh = [int]($img.Height * $ts); "
          "if ($mw -lt 1) { $mw = 1 }; if ($mh -lt 1) { $mh = 1 }; "
          "$mb = New-Object System.Drawing.Bitmap $mw, $mh; "
          "$mg = [System.Drawing.Graphics]::FromImage($mb); "
          "$mg.InterpolationMode = [System.Drawing.Drawing2D.InterpolationMode]::HighQualityBicubic; "
          "$mg.DrawImage($img, 0, 0, $mw, $mh); "
          "$mb.Save($it.mini, [System.Drawing.Imaging.ImageFormat]::Png); "
          "$mg.Dispose(); $mb.Dispose(); $img.Dispose() "
          "} catch {} }") % (jf, THUMB_SIZE, THUMB_SIZE, THUMB_MINI, THUMB_MINI)
    try:
        subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", ps],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       timeout=120, creationflags=0x08000000)
    except Exception:      # noqa: BLE001
        pass
    # ★ 以前每次请求都扫一遍缓存目录（listdir + 几百次 getmtime），
    #   小批量请求也要付这份钱。改成条目数超过阈值时才清。
    _clean_thumbs_async()
    return [w["ok"] for w in work if _ready(w)]


def _data_big(p):
    """把 256px 大图也读成 data URI。

    ★ 为什么：前端原先拿到的是 URL，每个格子都要再发一条 HTTP 请求。
    HTTP/1.1 同域最多 6 条并发连接，285 张图就是 48 轮排队 ——
    这才是"一批批刷、十几秒"的真正原因（实测服务端单张只要 8~84ms）。
    塞进 JSON 里一次带回，整屏就一次请求。
    """
    import base64
    f = _thumb_path(p)
    try:
        if not (f and os.path.isfile(f)):
            return ""
        with open(f, "rb") as fh:
            return "data:image/jpeg;base64," + base64.b64encode(fh.read()).decode()
    except OSError:
        return ""


def _data_uri(p):
    """把小图读成 data URI。几十到几百字节，直接塞在 JSON 里省一次请求。"""
    import base64
    f = _thumb_mini_path(p)
    try:
        if not (f and os.path.isfile(f)):
            return ""
        with open(f, "rb") as fh:
            return "data:image/png;base64," + base64.b64encode(fh.read()).decode()
    except OSError:
        return ""


def p_thumbs(raw, mode="both"):

    """批量生成缩略图。raw 是 | 分隔的路径（Windows 路径里不会有 |）。

    返回 ok: [{p: 原图路径, u: 大图 URL, m: 模糊小图的 data URI}]
    """
    paths = [p for p in (raw or "").split("|") if p]
    if not paths:
        return {"ok": []}
    with LOCK:
        if JOBS.get("thumbs"):
            return {"ok": [], "busy": True}
        JOBS["thumbs"] = True
    try:
        ok = _thumbs_worker(paths, mode)
    finally:
        with LOCK:
            JOBS["thumbs"] = False
    return {"ok": [{"p": p, "u": _data_big(p) or _thumb_url(p), "m": _data_uri(p)}
            for p in ok],
            "n": len(ok)}


def _icons_worker(rows):
    """批量抽图标：一次 PowerShell 全搞定（和 Tk 版同一套做法）。"""
    if JOBS["icons"]:
        return
    JOBS["icons"] = True
    try:
        os.makedirs(core.SOFT_ICON_DIR, exist_ok=True)
        for f in os.listdir(core.SOFT_ICON_DIR):
            if f.endswith(".png"):
                try:
                    os.remove(os.path.join(core.SOFT_ICON_DIR, f))
                except OSError:
                    pass
    except OSError:
        JOBS["icons"] = False
        return
    # 注册表只读一次，做成 名字 -> 可执行文件 的两套索引
    # （之前每个软件都重读一遍注册表，慢得离谱）
    by_exact, by_norm = {}, {}
    try:
        for app in core.read_installed_apps():
            src = _clean_icon_path(app.get("icon"))
            if not src:
                continue
            nm = app.get("name") or ""
            by_exact.setdefault(nm, src)
            by_norm.setdefault(_norm_name(nm), src)
    except Exception:      # noqa: BLE001
        pass
    work = []
    for i, r in enumerate(rows[:core.SOFT_ICON_MAX]):
        p = r.get("openPath") or ""
        src = _pick_icon(r.get("name"), by_exact, by_norm)
        # 安装目录里的真 exe 比 Installer 缓存里的图标靠谱（后者常抽出空白图）
        real = ""
        if p and os.path.isfile(p) and p.lower().endswith(".exe"):
            real = p
        elif p and os.path.isdir(p):
            try:
                for f in sorted(os.listdir(p)):
                    if f.lower().endswith(".exe"):
                        real = os.path.join(p, f)
                        break
            except OSError:
                pass
        if real and (_is_msi_icon(src) or not src):
            src = real
        if src:
            work.append({"i": i, "src": src})
    if not work:
        JOBS["icons"] = False
        return
    import tempfile
    jf = os.path.join(tempfile.gettempdir(), "spacelens_icons.json")
    try:
        with open(jf, "w", encoding="utf-8") as f:
            json.dump(work, f, ensure_ascii=False)
    except OSError:
        JOBS["icons"] = False
        return
    ps = ("Add-Type -AssemblyName System.Drawing; "
          "$items = Get-Content -Raw -Encoding UTF8 '%s' | ConvertFrom-Json; "
          "foreach ($it in $items) { try { "
          "$ic = [System.Drawing.Icon]::ExtractAssociatedIcon($it.src); "
          "if ($ic) { $b = New-Object System.Drawing.Bitmap $ic, %d, %d; "
          "$b.Save((Join-Path '%s' ($it.i.ToString() + '.png')), "
          "[System.Drawing.Imaging.ImageFormat]::Png); $b.Dispose(); $ic.Dispose() } "
          "} catch {} }") % (jf, ICON_SIZE, ICON_SIZE, core.SOFT_ICON_DIR)
    try:
        subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", ps],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                       timeout=120, creationflags=0x08000000)
    except Exception:      # noqa: BLE001
        pass
    with LOCK:
        if ST["soft"]["state"] == "done":
            ST["soft"] = dict(ST["soft"], icons=True)
    JOBS["icons"] = False


# ---- 全电脑搜索 ----
def _index_worker():
    """把所有盘的落盘缓存索引并起来 —— 「全电脑搜索」要能搜到别的盘。

    索引只建一次，之后一直用；建索引本身很重（C 盘约百万条），所以放后台。
    """
    srcs = []
    for d in drives():
        try:
            sc = core.load_scan_cache(d)
        except Exception:      # noqa: BLE001
            sc = None
        if sc is None:
            continue
        try:
            items = sc.all_items
        except Exception:      # noqa: BLE001
            items = None
        if not items:
            continue
        # ★ 预先算好每条记录「所在目录的小写」。
        #   路径是共享的：同一个目录下的几万个文件指向**同一个字符串对象**，
        #   所以只多花十多万个目录串 + 每条一个指针；而查询阶段就零分配了。
        #   之前每次查询都要对全部路径 lower() 一遍，实测 1.1 秒/次。
        cache = {}
        dls = []
        # ★ 目录项的 sz 在扫描记录里恒为 0（只有文件才带大小），
        #   真正的"目录总占用"记在 folders[路径]["size"] 里 —— 这里补上，
        #   否则搜索结果里所有文件夹都是 0 B，排序也跟着错。
        folders = getattr(sc, "folders", None) or {}
        fixed = []
        for it in items:
            p = it[0]
            k = p[:p.rfind("\\")] if "\\" in p else p
            v = cache.get(k)
            if v is None:
                v = k.lower()
                cache[k] = v
            dls.append(v)
            if it[3]:                       # it[3] = is_dir
                rec = folders.get(p)
                if rec:
                    tot = rec.get("size") or 0
                    if tot and tot != it[2]:
                        it = (it[0], it[1], tot) + tuple(it[3:])
            fixed.append(it)
        srcs.append((sc.root, fixed, dls))
    with LOCK:
        ST.setdefault("_index", [])
        ST["_index"] = srcs
        JOBS["index"] = False
        ST["search"] = dict(ST["search"], state="ready")


def p_search(q):
    q = (q or "").strip().lower()
    with LOCK:
        idx = ST.get("_index")
        if idx is None and not JOBS["index"]:
            JOBS["index"] = True
            ST["search"] = dict(ST["search"], state="indexing", q=q, rows=[],
                                note="正在为全电脑建立搜索索引…")
            threading.Thread(target=_index_worker, daemon=True).start()
            idx = None
        if not q:
            return {"state": "idle", "rows": [], "note": "", "q": ""}
        if idx is None:
            return {"state": "indexing", "rows": [],
                    "note": "正在为全电脑建立搜索索引…", "q": q}
    toks = q.split()

    # ★ 关联度：0 最相关。同一条规则对单词和多词都适用。
    #   只看"关键词落在哪"，不看大小 —— 大小只做同级的次级排序。
    _WORDSTART = " -_.([{（【［"

    def _rel(nl, dlow):
        if q in nl:
            stem = nl.rsplit(".", 1)[0] if "." in nl[1:] else nl
            if nl == q or stem == q:
                return 0                    # 名字（去掉扩展名）就叫这个词
            if nl.startswith(q):
                return 1                    # 以关键词开头
            i = nl.find(q)
            while i >= 0:
                if i and nl[i - 1] in _WORDSTART:
                    return 2                # 落在词边界上
                i = nl.find(q, i + 1)
            return 3                        # 名字中间包含
        if all(t in nl for t in toks):
            return 3                        # 多词分散命中名字
        return 4                            # 只有目录命中

    hits = []
    # 命中 = 所有词都出现在**文件名**里，或者都出现在**所在目录**里。
    # （分词后不可能跨过路径分隔符，所以「名字 + 目录」等价于原来的「整条路径」，
    #   但这里不用再 lower()、也不用再拼字符串。）
    if len(toks) == 1:
        # ★ 单词查询是绝大多数情况（边打字边搜）。走直连比较：
        #   省掉 all(...) 生成器每条一次的函数调用开销 —— 实测 1153ms → 143ms。
        t = toks[0]
        for _root, items, dls in idx:
            for it, dlow in zip(items, dls):
                nl = it[1]
                if t in nl or t in dlow:
                    hits.append((_rel(nl, dlow), it[2], it[0], nl, it[3], it[4]))
    elif len(toks) == 2:
        a, b = toks
        for _root, items, dls in idx:
            for it, dlow in zip(items, dls):
                nl = it[1]
                if (a in nl and b in nl) or (a in dlow and b in dlow):
                    hits.append((_rel(nl, dlow), it[2], it[0], nl, it[3], it[4]))
    else:
        for _root, items, dls in idx:
            for it, dlow in zip(items, dls):
                nl = it[1]
                if all(t in nl for t in toks) or all(t in dlow for t in toks):
                    hits.append((_rel(nl, dlow), it[2], it[0], nl, it[3], it[4]))
    # ★ 折叠"命中文件夹的内容"：名字命中的目录 -> 它里面那些"只靠目录命中"的条目
    #   全都算它的内容，不再单独占一行。否则搜一个文件夹名，结果会被里面几百个
    #   文件灌满（它们只是路径里带了这个词）。
    dir_hits = set()
    if PREFS.get("searchFold", True):
        for _r, _sz, full, _nl, is_dir, _g in hits:
            if is_dir and _r <= 3:
                dir_hits.add(os.path.normcase(full))
    inner = {}
    kept = []
    for h in hits:
        if h[0] <= 3 or not dir_hits:
            kept.append(h)
            continue
        # 关联度 4：往上看有没有"名字命中的祖先目录"
        owner = None
        parent = os.path.dirname(h[2])
        while parent and len(parent) > 2:
            nc = os.path.normcase(parent)
            if nc in dir_hits:
                owner = nc
                break
            up = os.path.dirname(parent)
            if up == parent:
                break
            parent = up
        if owner is None:
            kept.append(h)
        else:
            inner[owner] = inner.get(owner, 0) + 1
    folded = len(hits) - len(kept)
    hits = kept

    # 先按关联度，再在同一级里按大小降序（大文件更可能是目标）
    hits.sort(key=lambda h: (h[0], -h[1]))
    rows = []
    nlast = len(core.TYPE_GROUPS) - 1
    for _rel_v, size, full, nl, is_dir, g in hits[:SEARCH_MAX]:
        gi = g if isinstance(g, int) and 0 <= g < len(core.TYPE_GROUPS) else nlast
        rows.append({"path": full, "name": os.path.basename(full) or full,
                     "dir": os.path.dirname(full), "size": size,
                     "sizeText": human(size), "isDir": bool(is_dir),
                     "inner": inner.get(os.path.normcase(full), 0),
                     "g": gi, "color": core.TYPE_GROUPS[gi][1]})
    note = "共 %d 个结果" % (len(hits) + folded)
    if folded:
        note += "（%d 个位于命中文件夹内的条目已折叠）" % folded
    if len(hits) > SEARCH_MAX:
        note += "（按相关度列出前 %d 个）" % SEARCH_MAX
    if not hits:
        note = "没找到匹配的文件夹或文件"
    return {"state": "done", "rows": rows, "note": note, "q": q,
            "sources": [os.path.basename(r.rstrip("\\/")) or r for r, _i, _d in
                        (idx or [])]}


# ---------------------------------------------------------------- 把窗口提到前台
# ★ Windows 有「前台锁定」：不是前台进程的进程调 SetForegroundWindow 会被忽略，
#   只在任务栏闪一下。我们的 HTTP 服务在后台线程里跑，所以点文件夹时
#   窗口开是开了，却总落在别的窗口后面。
#   标准绕法：先把自己线程的输入队列 AttachThreadInput 到当前前台窗口的线程上，
#   系统就认我们是前台了，这时 SetForegroundWindow 才生效。
_WIN32 = None


def _win32():
    global _WIN32
    if _WIN32 is None:
        try:
            import ctypes
            from ctypes import wintypes
            u = ctypes.windll.user32
            k = ctypes.windll.kernel32
            u.GetWindowThreadProcessId.argtypes = [wintypes.HWND,
                                                   ctypes.POINTER(wintypes.DWORD)]
            u.GetWindowThreadProcessId.restype = wintypes.DWORD
            _WIN32 = (ctypes, wintypes, u, k)
        except Exception:      # noqa: BLE001
            _WIN32 = False
    return _WIN32 or None


def _visible_windows():
    """当前所有可见、且有标题的顶层窗口，按 Z 序（最上层在最前）。"""
    c = _win32()
    if not c:
        return []
    ctypes, wintypes, u, _k = c
    out = []
    CB = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)

    def cb(hwnd, _l):
        try:
            if u.IsWindowVisible(hwnd):
                t = ctypes.create_unicode_buffer(256)
                u.GetWindowTextW(hwnd, t, 256)
                if t.value.strip():
                    out.append(int(hwnd))
        except Exception:      # noqa: BLE001
            pass
        return True

    try:
        u.EnumWindows(CB(cb), 0)
    except Exception:          # noqa: BLE001
        pass
    return out


def _raise_new_window(before, tries=20):
    """等"打开之后才出现"的窗口，并把它提到最前。

    打开文件用的是 os.startfile，具体哪个程序接手不知道，所以不能按名字找 ——
    只能对比打开前后的窗口集合。EnumWindows 按 Z 序返回，新的通常在最上面。
    """
    before = set(before or ())
    for _ in range(tries):
        time.sleep(0.12)
        try:
            now = _visible_windows()
        except Exception:      # noqa: BLE001
            return
        for h in now:
            if h not in before and _foreground(h):
                return


def _explorer_windows():
    """当前所有资源管理器文件夹窗口 [(hwnd, 标题)]，按 Z 序（最上层在最前）。"""
    c = _win32()
    if not c:
        return []
    ctypes, wintypes, u, _k = c
    out = []
    CB = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)

    def cb(hwnd, _l):
        try:
            b = ctypes.create_unicode_buffer(256)
            u.GetClassNameW(hwnd, b, 256)
            if b.value in ("CabinetWClass", "ExploreWClass"):
                t = ctypes.create_unicode_buffer(512)
                u.GetWindowTextW(hwnd, t, 512)
                out.append((hwnd, t.value))
        except Exception:      # noqa: BLE001
            pass
        return True

    try:
        u.EnumWindows(CB(cb), 0)
    except Exception:          # noqa: BLE001
        pass
    return out


def _foreground(hwnd):
    """把窗口强行提到前台（绕过前台锁定）。"""
    c = _win32()
    if not c:
        return False
    ctypes, _wintypes, u, k = c
    try:
        fg = u.GetForegroundWindow()
        tid_fg = u.GetWindowThreadProcessId(fg, None) if fg else 0
        tid_me = k.GetCurrentThreadId()
        attached = False
        if tid_fg and tid_fg != tid_me:
            attached = bool(u.AttachThreadInput(tid_me, tid_fg, True))
        u.ShowWindow(hwnd, 9)                 # SW_RESTORE
        u.BringWindowToTop(hwnd)
        u.SetForegroundWindow(hwnd)
        if attached:
            u.AttachThreadInput(tid_me, tid_fg, False)
        return True
    except Exception:          # noqa: BLE001
        return False


def _raise_explorer(name, tries=15):
    """等资源管理器窗口出现，然后把它提到前台。

    · 放在后台线程里：窗口不是立刻就有的，得等一两百毫秒
    · 用目录名匹配标题：EnumWindows 按 Z 序返回，第一个命中的就是刚被激活的那个
    · 匹配不上就兜底提最上面那个文件夹窗口（比如盘符根目录，标题里没有目录名）
    """
    key = (name or "").strip().lower()
    top = None
    for _ in range(tries):
        time.sleep(0.12)
        wins = _explorer_windows()
        if not wins:
            continue
        top = wins[0][0]
        if key:
            for hwnd, title in wins:
                if key in title.strip().lower():
                    return _foreground(hwnd)
    if top:
        return _foreground(top)
    return False


# ---------------------------------------------------------------- 内存采样
# 纯 ctypes，不加第三方依赖（psutil 之类的不引）。
_MEM_WIN = None
MEM = {
    "on": False,          # 采样线程是否在跑
    "sys": {},            # 系统总览
    "groups": [],         # 按进程名合并后的排行（按工作集降序）
    "nProc": 0,           # 真实进程数（合并前）
    "cats": [],           # 分类聚合
    "trend": [],          # [(时间戳, 已用字节)]，总用量曲线
    "rate": [],           # [(时间戳, 变化字节/秒)]，活动波形
    "ts": 0.0,
}
_mem_io = {}              # pid -> (ts, 读字节, 写字节)，用来算每秒速率
MEM_TREND_MAX = 150       # 系统趋势保留 150 个点（1 秒一个 ≈ 2.5 分钟）
MEM_HIST_MAX = 90         # 每个进程名留 90 个点（约 1.5 分钟），给迷你走势线用
_mem_hist = {}            # 进程名 -> [工作集, …]
_mem_prev = {}            # pid -> deque[(t, 工作集)]，用来算"最近涨了多少"
_mem_names = {}           # pid -> 进程名（缓存，省得每秒重查）

# 进程按用途分类。命中靠进程名小写后的子串匹配，顺序即优先级。
MEM_CATS = [
    ("浏览器",   ("chrome", "msedge", "firefox", "brave", "opera", "iexplore",
                  "360se", "360chrome", "qqbrowser", "sogouexplorer", "quark")),
    ("开发工具", ("code", "cursor", "trae", "windsurf", "devenv", "pycharm", "idea",
                  "webstorm", "goland", "clion", "rider", "sublime", "notepad++",
                  "node", "python", "pythonw", "java", "javaw", "docker", "git",
                  "wezterm", "windowsterminal", "powershell", "pwsh", "cmd")),
    ("游戏",     ("steam", "epicgames", "battle.net", "wegame", "riot", "ubisoft",
                  "origin", "ea desktop", "genshin", "yuanshen", "starrail",
                  "launcher", "game")),
    ("通讯",     ("wechat", "weixin", "qq", "tim", "telegram", "discord", "dingtalk",
                  "feishu", "lark", "slack", "zoom", "teams", "skype")),
    ("媒体",     ("potplayer", "vlc", "mpv", "spotify", "cloudmusic", "netease",
                  "foobar", "aimp", "obs", "audacity")),
]


def _mem_win32():
    global _MEM_WIN
    if _MEM_WIN is None:
        try:
            import ctypes
            from ctypes import wintypes

            class MEMORYSTATUSEX(ctypes.Structure):
                _fields_ = [("dwLength", wintypes.DWORD),
                            ("dwMemoryLoad", wintypes.DWORD),
                            ("ullTotalPhys", ctypes.c_ulonglong),
                            ("ullAvailPhys", ctypes.c_ulonglong),
                            ("ullTotalPageFile", ctypes.c_ulonglong),
                            ("ullAvailPageFile", ctypes.c_ulonglong),
                            ("ullTotalVirtual", ctypes.c_ulonglong),
                            ("ullAvailVirtual", ctypes.c_ulonglong),
                            ("ullAvailExtendedVirtual", ctypes.c_ulonglong)]

            # cb 给成 EX 的大小，函数就会填 PRIVATE_USAGE 那几个扩展字段
            class PMC_EX(ctypes.Structure):
                _fields_ = [("cb", wintypes.DWORD),
                            ("PageFaultCount", wintypes.DWORD),
                            ("PeakWorkingSetSize", ctypes.c_size_t),
                            ("WorkingSetSize", ctypes.c_size_t),
                            ("QuotaPeakPagedPoolUsage", ctypes.c_size_t),
                            ("QuotaPagedPoolUsage", ctypes.c_size_t),
                            ("QuotaPeakNonPagedPoolUsage", ctypes.c_size_t),
                            ("QuotaNonPagedPoolUsage", ctypes.c_size_t),
                            ("PagefileUsage", ctypes.c_size_t),
                            ("PeakPagefileUsage", ctypes.c_size_t),
                            ("PrivateUsage", ctypes.c_size_t)]

            # 每个进程的累计读写字节数（磁盘 + 设备 I/O 都算）
            class IO_COUNTERS(ctypes.Structure):
                _fields_ = [("ReadOperationCount", ctypes.c_ulonglong),
                            ("WriteOperationCount", ctypes.c_ulonglong),
                            ("OtherOperationCount", ctypes.c_ulonglong),
                            ("ReadTransferCount", ctypes.c_ulonglong),
                            ("WriteTransferCount", ctypes.c_ulonglong),
                            ("OtherTransferCount", ctypes.c_ulonglong)]

            u = ctypes.windll.user32
            k = ctypes.windll.kernel32
            p = ctypes.windll.psapi
            # HANDLE 是 64 位指针宽度，ctypes 默认按 C int 收返回值会截断 ——
            # 句柄值小的时候"碰巧"没事，大了就关错对象，必须显式声明。
            k.OpenProcess.restype = wintypes.HANDLE
            k.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
            k.CloseHandle.argtypes = [wintypes.HANDLE]
            k.QueryFullProcessImageNameW.argtypes = [
                wintypes.HANDLE, wintypes.DWORD,
                wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD)]
            p.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.c_void_p,
                                               wintypes.DWORD]
            k.GetProcessIoCounters.argtypes = [wintypes.HANDLE, ctypes.c_void_p]
            _MEM_WIN = (ctypes, wintypes, u, k, p, MEMORYSTATUSEX, PMC_EX, IO_COUNTERS)
        except Exception:      # noqa: BLE001
            import traceback
            MEM["err"] = "ctypes 初始化失败:\n" + traceback.format_exc()[-500:]
            _MEM_WIN = False
    return _MEM_WIN or None


def _cat_of(name, path):
    n = (name or "").lower()
    for cat, keys in MEM_CATS:
        for kw in keys:
            if kw in n:
                return cat
    if (path or "").lower().startswith("c:\\windows"):
        return "系统"
    return "其他"


def _mem_one_sample():
    c = _mem_win32()
    if not c:
        return None
    ctypes, wintypes, u, k, psapi, MSX, PMC, IOC = c

    ms = MSX()
    ms.dwLength = ctypes.sizeof(MSX)
    if not k.GlobalMemoryStatusEx(ctypes.byref(ms)):
        return None

    # 进程列表：先要 PID，再逐个开句柄查内存
    PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
    arr = (wintypes.DWORD * 8192)()
    need = wintypes.DWORD()
    if not psapi.EnumProcesses(ctypes.byref(arr), ctypes.sizeof(arr), ctypes.byref(need)):
        return None
    n = min(need.value // ctypes.sizeof(wintypes.DWORD), len(arr))

    now = time.time()
    procs = []
    alive = set()
    for i in range(n):
        pid = arr[i]
        if not pid:
            continue
        h = k.OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, False, pid)
        if not h:
            continue                      # 系统 / 受保护进程，跳过
        try:
            pmc = PMC()
            pmc.cb = ctypes.sizeof(PMC)
            if not psapi.GetProcessMemoryInfo(h, ctypes.byref(pmc), pmc.cb):
                continue
            ws = int(pmc.WorkingSetSize)
            if ws <= 0:
                continue
            nm = _mem_names.get(pid)
            if nm is None:
                buf = ctypes.create_unicode_buffer(520)
                sz = wintypes.DWORD(520)
                if k.QueryFullProcessImageNameW(h, 0, buf, ctypes.byref(sz)):
                    full = buf.value
                    nm = os.path.basename(full).rsplit(".", 1)[0]
                else:
                    full, nm = "", "pid-%d" % pid
                _mem_names[pid] = (nm, full)
            else:
                nm, full = nm
            # 累计 I/O。拿不到就当 0（受保护进程、伪句柄都可能失败）
            ioc = IOC()
            wio = rio = 0
            if k.GetProcessIoCounters(h, ctypes.byref(ioc)):
                wio, rio = int(ioc.WriteTransferCount), int(ioc.ReadTransferCount)
            alive.add(pid)
            procs.append({"pid": pid, "name": nm, "path": full, "ws": ws,
                          "priv": int(pmc.PrivateUsage),
                          "wio": wio, "rio": rio})
        except Exception:      # noqa: BLE001
            continue
        finally:
            try:
                k.CloseHandle(h)
            except Exception:      # noqa: BLE001
                pass

    # 算"最近涨了多少"：每个 pid 留一小段历史，取窗口首尾之差
    for p in procs:
        dq = _mem_prev.get(p["pid"])
        if dq is None:
            dq = _mem_prev[p["pid"]] = []
        dq.append((now, p["ws"]))
        del dq[:-15]                      # 只留最近 15 个采样
        span = dq[-1][0] - dq[0][0]
        p["grow"] = (p["ws"] - dq[0][1]) if span >= 8 else 0
    # ★ 磁盘活动：累计值求差。任务管理器只在"详细信息"里藏着一列，
    #   而这里要回答的是"到底是谁在写盘"，所以按秒算成速率直接显示。
    for p in procs:
        prev = _mem_io.get(p["pid"])
        _mem_io[p["pid"]] = (now, p["wio"], p["rio"])
        p["wps"] = p["rps"] = 0.0
        if prev:
            dt = now - prev[0]
            if 0.2 <= dt <= 10:
                p["wps"] = max(0.0, (p["wio"] - prev[1]) / dt)
                p["rps"] = max(0.0, (p["rio"] - prev[2]) / dt)
    for pid in list(_mem_prev):
        if pid not in alive:
            _mem_prev.pop(pid, None)
            _mem_names.pop(pid, None)
            _mem_io.pop(pid, None)

    procs.sort(key=lambda x: -x["ws"])

    # ★ 按进程名合并。任务管理器那张表最大的毛病就是 chrome 列 40 行、
    #   既看不出总量也看不出谁在涨；合并之后一行就是一个"东西"。
    grp = {}
    for p in procs:
        g = grp.get(p["name"])
        if g is None:
            g = grp[p["name"]] = {"name": p["name"], "ws": 0, "priv": 0, "n": 0,
                                  "wps": 0.0, "rps": 0.0,
                                  "cat": _cat_of(p["name"], p["path"])}
        g["ws"] += p["ws"]
        g["priv"] += p["priv"]
        g["wps"] += p["wps"]
        g["rps"] += p["rps"]
        g["n"] += 1

    # 每个名字各留一条历史（前端画迷你走势线 / 算增长）
    for name, g in grp.items():
        h = _mem_hist.setdefault(name, [])
        h.append(g["ws"])
        del h[:-MEM_HIST_MAX]
        span = min(len(h), 13)                 # 最近约 12 秒
        g["grow"] = (g["ws"] - h[-span]) if span > 4 else 0
        g["hist"] = list(h)
    for name in list(_mem_hist):
        if name not in grp:
            _mem_hist.pop(name, None)

    groups = sorted(grp.values(), key=lambda x: -x["ws"])

    # 分类聚合（按合并后的算，不然浏览器 40 个进程会把平均值带偏）
    agg = {}
    for g in groups:
        a = agg.get(g["cat"])
        if a is None:
            a = agg[g["cat"]] = {"name": g["cat"], "ws": 0, "n": 0}
        a["ws"] += g["ws"]
        a["n"] += g["n"]
    cats = sorted(agg.values(), key=lambda x: -x["ws"])

    return {
        "total": ms.ullTotalPhys, "avail": ms.ullAvailPhys,
        "pageTotal": ms.ullTotalPageFile, "pageAvail": ms.ullAvailPageFile,
        "load": ms.dwMemoryLoad, "procs": procs, "groups": groups,
        "cats": cats, "ts": now, "nProc": len(procs),
        "ioW": sum(p["wps"] for p in procs), "ioR": sum(p["rps"] for p in procs),
    }


def _mem_worker():
    """每秒采一次。设置里关掉就自己退出（这就是"默认零开销"的实现）。"""
    while True:
        with LOCK:
            if not PREFS.get("memPage"):
                MEM["on"] = False
                return
        try:
            d = _mem_one_sample()
        except Exception as _e:    # noqa: BLE001
            import traceback
            with LOCK:
                MEM["err"] = traceback.format_exc()[-400:]
            d = None
        if d:
            used = d["total"] - d["avail"]
            with LOCK:
                MEM["sys"] = {k: d[k] for k in
                              ("total", "avail", "pageTotal", "pageAvail", "load")}
                MEM["groups"] = d["groups"][:40]
                MEM["cats"] = d["cats"]
                MEM["ts"] = d["ts"]
                MEM["on"] = True
                MEM["nProc"] = d["nProc"]
                MEM["ioW"] = d["ioW"]
                MEM["ioR"] = d["ioR"]
                # 趋势存两份：总用量（看趋势）+ 每秒变化量（看"活动"）
                prev = MEM["trend"][-1][1] if MEM["trend"] else used
                MEM["trend"].append([round(d["ts"], 1), used])
                MEM["rate"].append([round(d["ts"], 1), used - prev])
                del MEM["trend"][:-MEM_TREND_MAX]
                del MEM["rate"][:-MEM_TREND_MAX]
        time.sleep(1.0)


def _dup_sig(path, size):
    """头部 + 尾部各 64KB 的哈希。"""
    import hashlib
    h = hashlib.sha1()
    with open(path, "rb") as f:
        h.update(f.read(DUP_MARGIN))
        if size > DUP_MARGIN * 2:
            f.seek(-DUP_MARGIN, os.SEEK_END)
            h.update(f.read(DUP_MARGIN))
    return h.hexdigest()


def _dup_full(path):
    """全量 SHA-1。只有走到这一步才真读整个文件。"""
    import hashlib
    h = hashlib.sha1()
    with open(path, "rb") as f:
        while True:
            b = f.read(1024 * 1024)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


def _dup_worker(scope=""):
    """后台跑：按目录树收集候选 -> 大小 -> 头尾 -> 全量。

    scope 为空 = 整块盘；给了路径 = 只在这个目录子树里找
    （"这一个文件夹里有没有重复文件"是最常用的用法）。
    """
    def say(msg):
        with LOCK:
            DUP["ms"] = msg

    try:
        with LOCK:
            sc = ST.get("scan")
        if sc is None:
            with LOCK:
                DUP.update(state="error", ms="还没扫描完，稍后再试")
            return
        with LOCK:
            media_only = bool(PREFS.get("dupMediaOnly", True))
        # 只在指定目录子树里找：先算好前缀，后面用它过滤文件夹路径
        base = (scope or "").rstrip("\\/")
        pre = (base + os.sep).lower() if base else ""
        say("正在列出候选文件…")
        cand = []
        for p, rec in sc.folders.items():
            if pre:
                lp = p.lower()
                if not (lp == base.lower() or lp.startswith(pre)):
                    continue
            # 大文件夹才可能装得下大文件 —— 先按目录大小剪枝，省掉全量遍历
            if rec.get("size", 0) < DUP_MIN:
                continue
            for name, sz, is_dir, _g, _fl in (rec.get("children") or ()):
                if is_dir or sz < DUP_MIN:
                    continue
                if media_only and os.path.splitext(name)[1].lower() not in DUP_MEDIA_EXT:
                    continue
                cand.append((os.path.join(p, name), sz))
        with LOCK:
            DUP["files"] = len(cand)
            DUP["mediaOnly"] = media_only
            DUP["scope"] = base
        say("候选 %d 个，正在按大小分组…" % len(cand))

        # ---- 1) 按大小 ----
        by_size = {}
        for p, sz in cand:
            by_size.setdefault(sz, []).append(p)
        groups = [v for v in by_size.values() if len(v) > 1]
        with LOCK:
            DUP["cand"] = sum(len(g) for g in groups)
        say("大小相同的组 %d 个，正在比对头尾…" % len(groups))

        # ---- 2) 头尾签名 ----
        by_sig = {}
        for g in groups:
            for p in g:
                try:
                    by_sig.setdefault((os.path.getsize(p), _dup_sig(p, os.path.getsize(p))),
                                      []).append(p)
                except OSError:
                    continue
        groups = [v for v in by_sig.values() if len(v) > 1]
        say("头尾一致的有 %d 组，正在复核…" % len(groups))

        # ---- 3) 全量复核（预算内） ----
        budget = DUP_VERIFY_BUDGET
        out = []
        for g in sorted(groups, key=lambda v: -os.path.getsize(v[0])):
            try:
                size = os.path.getsize(g[0])
            except OSError:
                continue
            if size * len(g) <= budget:
                budget -= size * len(g)
                by_hash = {}
                for p in g:
                    try:
                        by_hash.setdefault(_dup_full(p), []).append(p)
                    except OSError:
                        continue
                for v in by_hash.values():
                    if len(v) > 1:
                        out.append({"size": size, "files": v, "verified": True})
            else:
                out.append({"size": size, "files": g, "verified": False})
        out.sort(key=lambda d: -(d["size"] * (len(d["files"]) - 1)))
        can = sum(d["size"] * (len(d["files"]) - 1) for d in out)
        with LOCK:
            DUP.update(state="done", ts=time.time(), groups=out, n=len(out),
                       can=can, ms="扫描完成", scope=base)
    except Exception as e:      # noqa: BLE001
        import traceback
        with LOCK:
            DUP.update(state="error", ms="出错：%s" % e,
                       err=traceback.format_exc()[-400:])
    finally:
        with LOCK:
            JOBS["dup"] = False


def p_dup():
    with LOCK:
        d = dict(DUP)
        d["mediaOnly"] = bool(PREFS.get("dupMediaOnly", True))
    d["canText"] = human(d.get("can", 0))
    for g in d.get("groups", []):
        g["sizeText"] = human(g["size"])
        g["canText"] = human(g["size"] * (len(g["files"]) - 1))
    return d


def do_redup(scope=""):
    """跑一遍重复识别（后台）。scope 为空 = 整块盘，给了路径 = 只扫这个文件夹。"""
    with LOCK:
        if JOBS["dup"]:
            return "正在扫描中…"
        JOBS["dup"] = True
        DUP.update(state="running", ms="准备中…", err="", groups=[], n=0, can=0)
        t = threading.Thread(target=_dup_worker, args=(scope or "",), daemon=True)
        t.start()
    return "开始扫描重复文件"


def do_delmany(raw):
    """批量删除（重复文件页用）。raw 是 | 分隔的完整路径。

    ★ 只删**文件**：不递归、不删目录、不认识的一律跳过。
      每个都单独 try，一个失败不影响其它。
    """
    paths = [p for p in (raw or "").split("|") if p]
    if not paths:
        return "没有要删的文件"
    okn = fail = 0
    freed = 0
    for p in paths:
        try:
            if not os.path.isfile(p):
                fail += 1
                continue
            sz = os.path.getsize(p)
            os.remove(p)
            okn += 1
            freed += sz
        except OSError:
            fail += 1
    # 文件和刚才那份列表对不上了，作废掉，下次重新扫
    with LOCK:
        if DUP.get("state") == "done":
            DUP.update(state="idle", ms="文件有变动，重新扫一遍", groups=[], can=0)
    return "已删除 %d 个，释放 %s%s" % (okn, human(freed),
                                       ("（%d 个跳过）" % fail) if fail else "")


def _read_bytes(p, n, tail=False):
    """读头部（或尾部）n 字节。尾部用于 moov 在文件末尾的 mp4。"""
    try:
        sz = os.path.getsize(p)
        with open(p, "rb") as f:
            if tail:
                f.seek(max(0, sz - n))
            return f.read(n)
    except OSError:
        return b""


def _img_size(b):
    """从文件头取图片宽高。取不到返回 (0, 0)。"""
    import struct
    try:
        if len(b) >= 24 and b[:8] == b"\x89PNG\r\n\x1a\n":
            return struct.unpack(">II", b[16:24])
        if len(b) >= 10 and b[:3] == b"GIF":
            return struct.unpack("<HH", b[6:10])
        if len(b) >= 26 and b[:2] == b"BM":
            w, h = struct.unpack("<ii", b[18:26])
            return abs(w), abs(h)
        if len(b) >= 30 and b[:4] == b"RIFF" and b[8:12] == b"WEBP":
            tag = b[12:16]
            if tag == b"VP8X":
                return (1 + int.from_bytes(b[24:27], "little"),
                        1 + int.from_bytes(b[27:30], "little"))
            if tag == b"VP8 ":
                return (struct.unpack("<H", b[26:28])[0] & 0x3FFF,
                        struct.unpack("<H", b[28:30])[0] & 0x3FFF)
        if b[:2] == b"\xff\xd8":                     # JPEG：找 SOF 段
            i = 2
            while i + 9 < len(b):
                if b[i] != 0xFF:
                    i += 1
                    continue
                m = b[i + 1]
                if m in (0xD8, 0xD9, 0x01) or 0xD0 <= m <= 0xD7:
                    i += 2
                    continue
                ln = struct.unpack(">H", b[i + 2:i + 4])[0]
                if 0xC0 <= m <= 0xCF and m not in (0xC4, 0xC8, 0xCC):
                    h, w = struct.unpack(">HH", b[i + 5:i + 9])
                    return w, h
                i += 2 + ln
    except Exception:      # noqa: BLE001
        pass
    return 0, 0


def _mp4_size(p):
    """mp4/mov：在 moov→trak→tkhd 里取宽高（16.16 定点数）。"""
    import struct
    for blob in (_read_bytes(p, 2 * 1024 * 1024), _read_bytes(p, 2 * 1024 * 1024, True)):
        try:
            j = blob.rfind(b"tkhd")
            while j > 4:
                size = struct.unpack(">I", blob[j - 4:j])[0]
                end = j - 4 + size
                if 90 <= size and end <= len(blob):
                    w = struct.unpack(">I", blob[end - 8:end - 4])[0] >> 16
                    h = struct.unpack(">I", blob[end - 4:end])[0] >> 16
                    if w and h:
                        return w, h
                j = blob.rfind(b"tkhd", 0, j)
        except Exception:      # noqa: BLE001
            pass
    return 0, 0


def p_dupinfo(raw):
    """一次查一组副本：分辨率 / 大小 / 修改时间。只读文件头，几十毫秒。"""
    out = []
    for p in [x for x in (raw or "").split("|") if x][:40]:
        try:
            st = os.stat(p)
        except OSError:
            continue
        ext = os.path.splitext(p)[1].lower()
        w = h = 0
        try:
            if ext in (".mp4", ".m4v", ".mov", ".3gp"):
                w, h = _mp4_size(p)
            elif ext in (".mkv", ".webm", ".avi", ".wmv", ".flv"):
                w, h = 0, 0            # 容器太杂，先返回 0，前端显示 —
            else:
                w, h = _img_size(_read_bytes(p, 65536))
        except Exception:      # noqa: BLE001
            w, h = 0, 0
        out.append({"p": p, "w": w, "h": h, "size": st.st_size,
                    "mtimeText": time.strftime("%Y-%m-%d %H:%M",
                                               time.localtime(st.st_mtime))})
    return {"files": out}


def p_diff(scope=None):
    """「变化」页：拿最早和最新两份快照比。

    为什么用"最早 vs 最新"而不是"最近两次"：用户想知道的是"这段时间我的盘
    怎么了"，跨度越大越有信息量。跨度会一起返回，界面上直接写清楚"跟 X 天前比"。
    """
    with LOCK:
        sc = ST.get("scan")
        target = ST.get("target") or ""
    root = getattr(sc, "root", None) or target
    snaps = core._load_snaps(root)
    n = len(snaps)
    if n < 2:
        return {"ready": False, "n": n, "root": root,
                "firstText": (time.strftime("%m-%d %H:%M",
                                            time.localtime(snaps[0]["ts"])) if snaps else ""),
                "hint": "快照还不够两份，没法对比。"}
    d = core.diff_pair(snaps[0], snaps[-1], scope or None)
    d["ready"] = True
    d["n"] = n
    d["root"] = root
    d["prevText"] = time.strftime("%m-%d %H:%M", time.localtime(d["prev_ts"]))
    d["curText"] = time.strftime("%m-%d %H:%M", time.localtime(d["cur_ts"]))
    sp = d["span"]
    d["spanText"] = ("%d 天" % (sp / 86400) if sp >= 86400 else
                     ("%d 小时" % (sp / 3600) if sp >= 3600 else
                      ("%d 分钟" % max(1, sp / 60))))
    return d


WHY_TOP = 12          # 每一类列几个文件


def p_diffwhy(path):
    """某个目录里具体是哪些文件变了（变化页展开用）。"""
    with LOCK:
        sc = ST.get("scan")
        target = ST.get("target") or ""
    root = getattr(sc, "root", None) or target
    snaps = core._load_snaps(root)
    if len(snaps) < 2:
        return {"ok": False, "msg": "快照不够两份，没法比较"}
    dirp = (path or "").strip().rstrip("\\/")
    if not dirp:
        return {"ok": False, "msg": "没给目录"}
    prev, cur = snaps[0], snaps[-1]
    pf, cf = prev.get("files") or {}, cur.get("files") or {}
    pfx = dirp + "\\"
    low = pfx.lower()
    use_low = not pfx in "".join(list(cf)[:3000])

    def under(p):
        return p.lower().startswith(low) if use_low else p.startswith(pfx)

    new, grown, gone, byext = [], [], [], {}
    for p, sz in cf.items():
        if not under(p):
            continue
        o = pf.get(p)
        if o is None:
            if sz > 0:
                new.append((p, sz))
        elif sz - o > 0:
            grown.append((p, sz - o, sz))
    for p, sz in pf.items():
        if under(p) and p not in cf and sz > 0:
            gone.append((p, sz))
    new.sort(key=lambda t: -t[1])
    gone.sort(key=lambda t: -t[1])
    grown.sort(key=lambda t: -t[1])
    for p, sz in new:
        e = os.path.splitext(p)[1].lower() or "(无扩展名)"
        byext[e] = byext.get(e, 0) + sz
    for p, d, _now in grown:
        e = os.path.splitext(p)[1].lower() or "(无扩展名)"
        byext[e] = byext.get(e, 0) + d
    ext = sorted(byext.items(), key=lambda kv: -kv[1])[:6]
    return {
        "ok": True, "path": dirp,
        "new": [{"path": p, "name": os.path.basename(p), "size": sz,
                 "sizeText": human(sz)} for p, sz in new[:WHY_TOP]],
        "grown": [{"path": p, "name": os.path.basename(p), "delta": d,
                   "sizeText": human(d), "nowText": human(now)}
                  for p, d, now in grown[:WHY_TOP]],
        "gone": [{"path": p, "name": os.path.basename(p), "size": sz,
                  "sizeText": human(sz)} for p, sz in gone[:WHY_TOP]],
        "nNew": len(new), "nGrown": len(grown), "nGone": len(gone),
        "newSize": human(sum(x[1] for x in new)),
        "grownSize": human(sum(x[1] for x in grown)),
        "goneSize": human(sum(x[1] for x in gone)),
        "ext": [{"ext": e, "sizeText": human(v)} for e, v in ext],
    }


def p_mem():
    with LOCK:
        on = bool(PREFS.get("memPage"))
        if on and not MEM["on"]:
            MEM["on"] = True                       # 先置位，避免连开多个线程
            threading.Thread(target=_mem_worker, daemon=True).start()
        return {"ready": bool(MEM["sys"]), "on": on,
                "trend": list(MEM["trend"]), "rate": list(MEM["rate"]),
                "sys": dict(MEM["sys"]), "nProc": MEM["nProc"],
                "ioW": MEM.get("ioW", 0.0), "ioR": MEM.get("ioR", 0.0),
                "groups": [dict(g) for g in MEM["groups"]],
                "cats": [dict(c) for c in MEM["cats"]], "ts": MEM["ts"],
                "err": MEM.get("err", ""),
                "totalText": human(MEM["sys"].get("total", 0)) if MEM["sys"] else "—"}


# ---------------------------------------------------------------- 动作
def do_open(path):
    if not path or not os.path.exists(path):
        return "路径不存在：%s" % path
    p = os.path.normpath(path)
    if os.path.isdir(p):
        os.startfile(p)
        name = os.path.basename(p)
    else:
        # ★ 文件：直接用系统默认程序打开它。以前这里是 explorer /select
        #   （在资源管理器里选中），点一张图却弹出一个文件夹，很别扭。
        #   没装关联程序时 startfile 会抛 OSError，那就退回"选中它"。
        try:
            before = _visible_windows()
        except Exception:      # noqa: BLE001
            before = []
        try:
            os.startfile(p)
        except OSError:
            subprocess.Popen(["explorer", "/select,", p])
        # ★ 开出来还得提到最前：Edge 是 --app 窗口，经常把新窗口压在后面
        threading.Thread(target=_raise_new_window, args=(before,), daemon=True).start()
        return "已打开 %s" % path
        name = os.path.basename(os.path.dirname(p))
    # 开出来只是第一步 —— 还得把它提上来，否则会压在 Edge 窗口后面
    threading.Thread(target=_raise_explorer, args=(name,), daemon=True).start()
    return "已打开 %s" % path


def do_reveal(path):
    """在资源管理器里选中它（右键菜单「在资源管理器中显示」用）。"""
    if not path or not os.path.exists(path):
        return "路径不存在：%s" % path
    p = os.path.normpath(path)
    if os.path.isdir(p):
        os.startfile(p)
        name = os.path.basename(p)
    else:
        subprocess.Popen(["explorer", "/select,", p])
        name = os.path.basename(os.path.dirname(p))
    threading.Thread(target=_raise_explorer, args=(name,), daemon=True).start()
    return "已在资源管理器中显示 %s" % path


def do_del(path):
    """删这个位置的内容（目录本身保留），占用中 / 没权限的跳过。"""
    if not path or not os.path.exists(path):
        return "路径不存在：%s" % path
    freed = skipped = 0
    if os.path.isfile(path):
        try:
            n = os.path.getsize(path)
            os.remove(path)
            return "已释放 %s" % human(n)
        except OSError as e:
            return "删除失败：%s" % e
    for root, _dirs, files in os.walk(path):
        for fn in files:
            fp = os.path.join(root, fn)
            try:
                n = os.path.getsize(fp)
            except OSError:
                n = 0
            try:
                os.remove(fp)
                freed += n
            except OSError:
                skipped += 1
    return "已释放 %s，跳过 %d 个文件（占用中或没权限）" % (human(freed), skipped)


def do_cleanall():
    todo = []
    for name, raw, risk, advice in core.CLEAN_TARGETS:
        if risk != "safe":
            continue
        p = os.path.expandvars(raw)
        if os.path.exists(p):
            todo.append(p)
    freed = skipped = 0
    for p in todo:
        if os.path.isfile(p):
            try:
                n = os.path.getsize(p)
                os.remove(p)
                freed += n
            except OSError:
                skipped += 1
            continue
        for root, _dirs, files in os.walk(p):
            for fn in files:
                fp = os.path.join(root, fn)
                try:
                    n = os.path.getsize(fp)
                except OSError:
                    n = 0
                try:
                    os.remove(fp)
                    freed += n
                except OSError:
                    skipped += 1
    return "一键清理完成：释放 %s，跳过 %d 个文件" % (human(freed), skipped)


def _purge_files(path):
    """删掉目录里的文件（目录结构本身保留），返回 (释放字节, 跳过数)。"""
    if os.path.isfile(path):
        try:
            n = os.path.getsize(path)
            os.remove(path)
            return n, 0
        except OSError:
            return 0, 1
    freed = skipped = 0
    for root, _dirs, files in os.walk(path):
        for fn in files:
            fp = os.path.join(root, fn)
            try:
                n = os.path.getsize(fp)
            except OSError:
                n = 0
            try:
                os.remove(fp)
                freed += n
            except OSError:
                skipped += 1
    return freed, skipped


def do_delsoft(name):
    """删掉某个软件被统计到的那些目录里的文件。

    只删文件、保留目录结构；占用中/没权限的会跳过。
    删完把这个软件从缓存里去掉，界面刷新后它就不见了，不用重新分析一遍。
    """
    with LOCK:
        rows = list((ST["soft"].get("rows") or []))
    row = next((r for r in rows if r["name"] == name), None)
    if row is None:
        return "没找到这个软件（列表可能已经刷新过）"
    dirs = row.get("dirList") or []
    if not dirs:
        return "这个软件没有可删除的目录"
    freed = skipped = 0
    for d in dirs:
        f, sk = _purge_files(d)
        freed += f
        skipped += sk
    with LOCK:
        st = ST["soft"]
        st["rows"] = [r for r in st["rows"] if r["name"] != name]
        st["third"] = sum(r["size"] for r in st["rows"] if r["kind"] == "第三方")
        st["sysv"] = sum(r["size"] for r in st["rows"]) - st["third"]
    return "已删除「%s」的 %d 个目录：释放 %s，跳过 %d 个文件（占用中或没权限）" % (
        name, len(dirs), human(freed), skipped)


def do_uninstall(name):
    """调起软件**自己的**卸载程序（注册表里的 UninstallString）。

    ★ 卸载不是删目录：真正的卸载要清注册表、服务、开始菜单、计划任务……
      直接删目录会让"设置 → 应用"里留一个永远卸不掉的空条目。
      删目录只是兜底手段，放在右键菜单里（do_delsoft）。
    """
    try:
        apps = core.read_installed_apps()
    except Exception as e:      # noqa: BLE001
        return "读注册表失败：%s（试试以管理员身份运行）" % e
    # 同名条目可能有多条（HKLM / HKCU / WOW6432Node 各一份），优先用带卸载命令的
    hit = None
    for app in apps:
        if app["name"] == name and (app.get("uninst") or "").strip():
            hit = app
            break
    if hit is None:
        for app in apps:
            if app["name"] == name:
                hit = app
                break
    if hit is None:
        return "没找到「%s」（注册表里已经没有它了）" % name
    cmd = (hit.get("uninst") or "").strip()
    if not cmd:
        return ("「%s」没有登记卸载命令 —— 可以用右键「打开安装目录」自己处理，"
                "或用「直接删除目录内容」强删" % name)
    # MSI 的 UninstallString 常常写成 MsiExec.exe /I{GUID}：
    #   /I 打开的是"修改/修复/删除"三选一的对话框，/X 才是直接卸载。
    #   只在 msiexec 且参数就是 /I{GUID} 时替换，别的形态原样交给系统。
    import re as _re
    run = cmd
    if _re.search(r"msiexec", run, _re.I) and _re.search(r"/I\s*\{", run, _re.I):
        run = _re.sub(r"/I(\s*)\{", r"/X\1{", run, count=1, flags=_re.I)
    try:
        p = subprocess.Popen(run, shell=True)
    except Exception as e:      # noqa: BLE001
        return "调起卸载程序失败：%s" % e
    # 卸载程序退出后把列表标成"待重扫"，下次进这一页就是新的
    def _wait():
        try:
            p.wait(timeout=900)
        except Exception:      # noqa: BLE001
            return
        with LOCK:
            JOBS["soft"] = False
            ST["soft"] = dict(ST["soft"], state="idle", msg="")
    try:
        threading.Thread(target=_wait, daemon=True).start()
    except Exception:      # noqa: BLE001
        pass
    return "已调起「%s」的卸载程序（它自己的界面走完后，这一页会自动重扫）" % name


def do_setdrive(d):
    if not d or not os.path.exists(d):
        return "磁盘不存在：%s" % d
    with LOCK:
        ST["target"] = d
        ST["scan"] = None
        ST["scanned_at"] = ""
    kick_scan(False)
    return "正在切换到 %s…" % d


# ---------------------------------------------------------------- HTTP
class H(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, *_a):
        pass

    def _send(self, code, body, ctype):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        try:
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionAbortedError):
            pass

    def _json(self, obj):
        self._send(200, json.dumps(obj, ensure_ascii=False).encode("utf-8"),
                   "application/json; charset=utf-8")

    def do_GET(self):
        # ★ 只认本机、同源。这个服务能删目录、能起进程，而它监听的端口虽然随机，
        #   但任何网页都可以去扫本机端口然后提交请求（DNS rebinding 同理）。
        #   浏览器同源请求不带 Origin，跨源请求一定带 —— 所以带了且不是自己就拒绝。
        _h = (self.headers.get("Host") or "").lower()
        _o = (self.headers.get("Origin") or "").lower()
        if not _h.startswith("127.0.0.1:") or (_o and not _o.startswith("http://127.0.0.1:")):
            self._send(403, b"cross-origin blocked", "text/plain")
            return
        _touch()               # 任何一次请求都算「窗口还活着」
        u = urllib.parse.urlparse(self.path)
        q = urllib.parse.parse_qs(u.query)
        one = lambda k, d="": q.get(k, [d])[0]        # noqa: E731
        try:
            if u.path == "/api/ping":
                self._json({"ok": True})
                return
            if u.path == "/api/bye":
                ALIVE["bye"] = time.time()
                self._json({"ok": True})
                return
            if u.path in ("/", "/index.html"):
                p = os.path.join(WEB, "index.html")
                with open(p, "rb") as f:
                    html = f.read()
                # ★ 把外观偏好注入进页面：<head> 里那段脚本靠它决定第一帧的颜色。
                #   不这么做的话会先按默认色画一遍再切，眼睛能看见闪一下。
                try:
                    with LOCK:
                        th = PREFS.get("theme", "auto")
                    if th not in ("auto", "dark", "light"):
                        th = "auto"
                    html = html.replace(b"@@THEME@@", th.encode())
                except Exception:      # noqa: BLE001
                    pass
                self._send(200, html, "text/html; charset=utf-8")
                return
            if u.path == "/echarts.min.js":
                # 本地打包的 ECharts（1MB），不走 CDN —— 断网也能用。
                # 万一文件丢了就 404，页面会自动退回手写 SVG 扇形图。
                p = os.path.join(WEB, "echarts.min.js")
                if not os.path.exists(p):
                    self._send(404, b"no echarts", "text/plain")
                    return
                with open(p, "rb") as f:
                    self._send(200, f.read(),
                               "application/javascript; charset=utf-8")
                return
            if u.path == "/api/state":
                self._json(p_state())
                return
            if u.path == "/api/thumb":
                q = urllib.parse.parse_qs(u.query)
                k = (q.get("k") or [""])[0]
                # ★ 只认"纯文件名"：k 里带任何路径分隔都拒绝，防止越目录读文件
                if (not k or os.path.basename(k) != k or
                        not k.endswith((".jpg", ".png"))):
                    self._send(400, b"bad key", "text/plain")
                    return
                f = os.path.join(THUMB_DIR, k)
                if not os.path.isfile(f):
                    self._send(404, b"no thumb", "text/plain")
                    return
                with open(f, "rb") as fh:
                    data = fh.read()
                # 文件名里带着原图 mtime，图变了 URL 就变 —— 所以可以永久缓存
                self.send_response(200)
                self.send_header("Content-Type",
                                 "image/jpeg" if k.endswith(".jpg") else "image/png")
                self.send_header("Content-Length", str(len(data)))
                self.send_header("Cache-Control", "public, max-age=31536000, immutable")
                self.send_header("ETag", '"' + k + '"')
                self.end_headers()
                try:
                    self.wfile.write(data)
                except Exception:      # noqa: BLE001
                    pass
                return
            if u.path == "/api/thumbs":
                q = urllib.parse.parse_qs(u.query)
                md = (q.get("mode") or ["both"])[0]
                if md not in ("both", "mini", "big"):
                    md = "both"
                self._json(p_thumbs((q.get("p") or [""])[0], md))
                return
            if u.path == "/api/dup":
                self._json(p_dup())
                return
            if u.path == "/api/dupinfo":
                self._json(p_dupinfo(one("p")))
                return
            if u.path == "/api/diff":
                self._json(p_diff(one("scope") or None))
                return
            if u.path == "/api/diffwhy":
                self._json(p_diffwhy(one("path")))
                return
            if u.path == "/api/prefs":
                self._json(p_prefs())
                return
            if u.path == "/api/mem":
                self._json(p_mem())
                return
            if u.path == "/api/rank":
                self._json(p_rank(one("path")))
                return
            if u.path == "/api/type":
                g = one("group")
                self._json(p_type(int(g) if g.isdigit() else None,
                                  one("ext") or None))
                return
            if u.path == "/api/clean":
                self._json(p_clean())
                return
            if u.path == "/api/soft":
                self._json(p_soft())
                return
            if u.path == "/api/search":
                self._json(p_search(one("q")))
                return
            if u.path == "/api/icon":
                i = one("i", "-1")
                p = os.path.join(core.SOFT_ICON_DIR, "%s.png" % i)
                if i.isdigit() and os.path.isfile(p):
                    with open(p, "rb") as f:
                        self._send(200, f.read(), "image/png")
                else:
                    self._send(404, b"", "image/png")
                return
            if u.path == "/api/act":
                act, arg = one("act"), one("arg")
                self._json({"msg": self._act(act, arg)})
                return
        except (BrokenPipeError, ConnectionAbortedError):
            return
        except Exception as e:      # noqa: BLE001
            try:
                self._json({"error": "%s: %s" % (type(e).__name__, e)})
            except Exception:       # noqa: BLE001
                pass
            return
        self._send(404, b"not found", "text/plain")

    def do_POST(self):
        self.do_GET()

    @staticmethod
    def _act(act, arg):
        if act == "reveal":
            return do_reveal(arg)
        if act == "open":
            return do_open(arg)
        if act == "del":
            return do_del(arg)
        if act == "cleanall":
            return do_cleanall()
        if act == "uninstall":
            return do_uninstall(arg)
        if act == "delsoft":
            return do_delsoft(arg)
        if act == "setdrive":
            return do_setdrive(arg)
        if act == "redup":
            return do_redup(arg)
        if act == "delmany":
            return do_delmany(arg)
        if act == "setpref":
            return do_setpref(arg)
        if act == "rescan":
            kick_scan(True)
            return "正在重新扫描…"
        if act == "reclean":
            with LOCK:
                ST["clean"] = {"state": "idle", "rows": [], "safe": 0, "caut": 0,
                               "msg": "", "ts": 0}
                JOBS["clean"] = False
            return "正在重新分析可清理的位置…"
        if act == "resoft":
            with LOCK:
                ST["soft"] = {"state": "idle", "rows": [], "third": 0, "sysv": 0,
                              "msg": "", "ts": 0, "icons": False}
                JOBS["soft"] = False
            return "正在重新统计软件占用…"
        if act == "clearthumbs":
            # ★ v1.0.8：清理缩略图缓存。改了缩略图逻辑后，老缓存会被复用
            #   导致"改了没效果"，用户可以在设置里一键清掉。
            cnt = 0
            try:
                if os.path.isdir(THUMB_DIR):
                    for f in os.listdir(THUMB_DIR):
                        fp = os.path.join(THUMB_DIR, f)
                        try:
                            if os.path.isfile(fp):
                                os.remove(fp)
                                cnt += 1
                        except OSError:
                            pass
            except OSError:
                pass
            return {"ok": True, "cleared": cnt}
        if act == "killproc":
            # ★ v1.1.0：结束进程。arg 是进程名（不含 .exe 也可以），杀所有同名进程。
            name = (arg or "").strip()
            if not name:
                return "进程名不能为空"
            if not name.lower().endswith(".exe"):
                name += ".exe"
            # 只允许字母数字下划线点横线，防止命令注入
            if not all(c.isalnum() or c in "._-" for c in name):
                return "非法进程名"
            try:
                import subprocess
                r = subprocess.run(["taskkill", "/F", "/IM", name],
                                   capture_output=True, text=True, timeout=10)
                return {"ok": r.returncode == 0, "out": r.stdout.strip()[:200]}
            except Exception as e:      # noqa: BLE001
                return "结束失败：%s" % e
        return "未知动作：%s" % act


# ---------------------------------------------------------------- 启动期自救
# ★ 打包是 --windowed，没有控制台，print 出去的东西用户永远看不到。
#   于是"没找到 Edge / 端口起不来 / 打包漏了文件"在别人电脑上全都表现成
#   「双击没反应」—— 换台电脑打不开，就是撞在这里。所以下面每一条致命
#   错误都必须走「写日志 + 弹系统对话框」两条路，绝不能再静默挂起。
START_LOG = os.path.join(core.CONFIG_DIR, "start.log")


def _log(msg):
    """启动日志。换电脑出问题时，让对方把这个文件发回来就能定位。"""
    line = "%s  %s" % (time.strftime("%Y-%m-%d %H:%M:%S"), msg)
    try:
        os.makedirs(core.CONFIG_DIR, exist_ok=True)
        if os.path.isfile(START_LOG) and os.path.getsize(START_LOG) > 256 * 1024:
            try:
                os.replace(START_LOG, START_LOG + ".old")
            except Exception:      # noqa: BLE001
                pass
        with open(START_LOG, "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except Exception:      # noqa: BLE001
        pass
    try:
        print(line, flush=True)        # 从命令行跑的时候还能看见
    except Exception:      # noqa: BLE001
        pass


def _msgbox(text, title="空间透镜", icon=0x10):
    """0x10 = 错误图标。没有这个，用户在别的电脑上只能看到"没反应"。"""
    try:
        import ctypes
        ctypes.windll.user32.MessageBoxW(None, text, title, icon | 0x4000)
    except Exception:      # noqa: BLE001
        pass


def _fatal(what, detail="", url=None):
    """致命错误：记日志 + 弹窗。带 url 时说明服务其实活着，手动打开就能用。"""
    txt = what
    if detail:
        txt += "\n\n" + detail
    if url:
        txt += ("\n\n本地服务其实已经起来了，你也可以手动在浏览器里打开：\n" + url +
                "\n\n（把上面这个地址复制到浏览器地址栏即可）")
    txt += "\n\n详细信息已写入：\n" + START_LOG
    _log("致命错误：%s | %s" % (what, detail.replace("\n", " ")))
    _msgbox(txt)


def _console():
    """双击启动时没有控制台；--diag 时现开一个，好把自检信息打出来。"""
    try:
        import ctypes
        k = ctypes.windll.kernel32
        if k.GetConsoleWindow():
            return True
        if not k.AllocConsole():
            return False
        sys.stdout = open("CONOUT$", "w", encoding="utf-8", buffering=1)
        sys.stderr = open("CONOUT$", "w", encoding="utf-8", buffering=1)
        return True
    except Exception:      # noqa: BLE001
        return False


# Chromium 系都支持 --app= 这种没有地址栏的"应用窗口"。
# 换电脑最常见的坑：那台机器没装 Edge（或被精简版系统删了），
# 所以这里必须有后备 —— 至少退到系统默认浏览器，界面一样能用。
BROWSERS = [
    ("Edge", "msedge.exe", (
        r"%ProgramFiles(x86)%\Microsoft\Edge\Application\msedge.exe",
        r"%ProgramFiles%\Microsoft\Edge\Application\msedge.exe",
        r"%LOCALAPPDATA%\Microsoft\Edge\Application\msedge.exe")),
    ("Chrome", "chrome.exe", (
        r"%ProgramFiles%\Google\Chrome\Application\chrome.exe",
        r"%ProgramFiles(x86)%\Google\Chrome\Application\chrome.exe",
        r"%LOCALAPPDATA%\Google\Chrome\Application\chrome.exe")),
    ("Brave", "brave.exe", (
        r"%ProgramFiles%\BraveSoftware\Brave-Browser\Application\brave.exe",
        r"%ProgramFiles(x86)%\BraveSoftware\Brave-Browser\Application\brave.exe",
        r"%LOCALAPPDATA%\BraveSoftware\Brave-Browser\Application\brave.exe")),
]


def _reg_app_path(exe_name):
    """注册表里登记的安装位置，比猜目录靠谱（装到别的盘、绿色版、改过路径）。"""
    try:
        import winreg
    except Exception:      # noqa: BLE001
        return None
    key = r"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths" + "\\" + exe_name
    for root in (winreg.HKEY_CURRENT_USER, winreg.HKEY_LOCAL_MACHINE):
        try:
            with winreg.OpenKey(root, key) as k:
                p = winreg.QueryValueEx(k, "")[0]
            if p and os.path.isfile(p):
                return p
        except Exception:      # noqa: BLE001
            pass
    return None


def find_browser():
    """返回 (可执行文件, 名字)，找不到返回 (None, None)。"""
    for name, exe, guess in BROWSERS:
        p = _reg_app_path(exe)
        if p:
            return p, name
        for c in guess:
            c = os.path.expandvars(c)
            if os.path.isfile(c):
                return c, name
    return None, None


def diag_report():
    """自检：换电脑出问题时，这张表基本能直接指出原因。"""
    import platform
    L = ["空间透镜 · 启动自检", "=" * 40,
         "版本        " + core.APP_VERSION,
         "打包运行    " + ("是" if getattr(sys, "frozen", False) else "否（源码）"),
         "程序        " + sys.executable,
         "界面目录    " + WEB + ("  [存在]" if os.path.isfile(
             os.path.join(WEB, "index.html")) else "  [★ 缺 index.html，打包漏了]"),
         "系统        " + platform.platform(),
         "Python      " + sys.version.split()[0] + "  " + platform.machine(),
         "配置目录    " + core.CONFIG_DIR,
         "启动日志    " + START_LOG]
    for label, path in (("配置目录可写", core.CONFIG_DIR),
                        ("TEMP 可写", os.environ.get("TEMP", ""))):
        try:
            os.makedirs(path, exist_ok=True)
            t = os.path.join(path, "_w.tmp")
            open(t, "w").close()
            os.remove(t)
            L.append("%-11s 是  %s" % (label, path))
        except Exception as e:      # noqa: BLE001
            L.append("%-11s ★ 否 %s  (%s)" % (label, path, e))
    for name, exe, guess in BROWSERS:
        hits = [os.path.expandvars(c) for c in guess if os.path.isfile(os.path.expandvars(c))]
        reg = _reg_app_path(exe)
        L.append("%-11s %s%s" % (name, "找到 " + (reg or hits[0]) if (reg or hits) else "★ 没找到",
                                 "（注册表）" if reg else ""))
    p, nm = find_browser()
    L.append("-" * 40)
    L.append("将使用      " + (nm + "  " + p if p else "★ 没有 Chromium 浏览器，退到系统默认浏览器"))
    return "\n".join(L)


def free_port():
    s = socket.socket()
    s.bind(("127.0.0.1", 0))
    p = s.getsockname()[1]
    s.close()
    return p


def find_edge():                     # 旧名字保留（可能还有别处引用）
    return find_browser()[0]


def _style_window():
    """空实现 —— 保留函数名和调用点，但不再改窗口样式。

    为什么不动它（下面每一条都实测过）：
      · DWMWA_CAPTION_COLOR(35)/DWMWA_TEXT_COLOR(36)：调用返回 S_OK，
        但 Chromium 会自己重设标题栏颜色，反复设也压不住；
      · DWMWA_BORDER_COLOR(34)：反而把整条标题栏变成纯黑，更丑；
      · manifest 的 theme_color 和 <meta name=theme-color>：完全无效；
      · 去掉 WS_CAPTION：**Chromium 的 app 窗口标题栏是它自己画的**，
        不是 Windows 画的，去掉样式位照样显示（截图放大后能清楚看到
        Edge 的地球图标），只是白折腾；
      · manifest 的 display_override:[window-controls-overlay]（含
        --enable-features=WebAppWindowControlsOverlay）：只对「已安装的 PWA」
        生效，--app 窗口里 navigator.windowControlsOverlay.visible 恒为 false。

    结论：这条标题栏去不掉也染不了色，所以改成让页面顶部也从纯黑起步
    （见 web/index.html 里 .bg::after 的顶部压黑），两者自然融合。
    """
    return


def _hold_alive():
    """服务交给看门狗；主线程只需要别退出。"""
    while True:
        time.sleep(3600)


def main():
    _log("---- 启动 v%s  %s ----" % (core.APP_VERSION, sys.executable))
    _log("配置目录 %s" % core.CONFIG_DIR)

    # --diag：先开个控制台把自检打出来（双击运行也能看到）
    if "--diag" in sys.argv:
        rep = diag_report()
        _log("自检：\n" + rep)
        if not _console():
            _msgbox(rep, "空间透镜 · 启动自检", 0x40)     # 0x40 = 信息图标

    if not os.path.isfile(os.path.join(WEB, "index.html")):
        _fatal("界面的网页文件缺失", "找不到：%s\n说明打包时没把 web 目录带进去。"
              % os.path.join(WEB, "index.html"))
        return

    # 先用缓存把界面点亮（秒开），没有缓存才真扫
    try:
        kick_scan(False)
    except Exception:      # noqa: BLE001
        import traceback
        _log("预读缓存失败（不影响启动）：\n" + traceback.format_exc()[-600:])

    # 端口：随机端口极少撞车，但真撞了就换一个，别再挂在那儿
    srv = None
    port = 0
    for _ in range(10):
        port = free_port()
        try:
            srv = ThreadingHTTPServer(("127.0.0.1", port), H)
            break
        except OSError as e:
            _log("端口 %d 起不来：%s" % (port, e))
            srv = None
    if srv is None:
        _fatal("本地服务启动失败",
               "连续 10 个端口都绑定不上。\n通常是杀毒软件/安全软件拦了本机监听，"
               "或者系统端口被占满了。\n重启一次电脑多半就好了。")
        return
    srv.daemon_threads = True
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    url = "http://127.0.0.1:%d/" % port
    _log("服务已就绪 %s" % url)

    exe, bname = find_browser()
    proc = None
    if exe:
        _log("浏览器 %s  %s" % (bname, exe))
        # Edge 沿用老目录（保住老用户的窗口状态）；别的浏览器各用各的，互不干扰
        prof = PROFILE if bname == "Edge" else PROFILE + "-" + bname.lower()
        try:
            os.makedirs(prof, exist_ok=True)
        except Exception as e:      # noqa: BLE001
            _log("配置目录建不了（继续跑）：%s" % e)
        # ★ 清掉这个配置目录里的"自动填充历史"：Edge 会把文本框里输入过的词
        #   存进 Default\Web Data，下次聚焦任何输入框就弹出来 —— 搜「学习通」
        #   弹出一堆别的网站的词就是这么来的，和本软件的搜索没有任何关系。
        #   只删 Web Data（自动填充/表单历史），Cookie、登录态、缓存都不动。
        try:
            _def = os.path.join(prof, "Default")
            for _f in ("Web Data", "Web Data-journal"):
                _p = os.path.join(_def, _f)
                if os.path.isfile(_p):
                    os.remove(_p)
        except OSError:
            pass
        try:
            proc = subprocess.Popen([
                exe, "--app=" + url,
                "--window-size=1360,900",
                "--user-data-dir=" + prof,
                "--no-first-run", "--no-default-browser-check",
                # 别让浏览器关窗后还在后台驻留（驻留会让下次启动又被交接，生命周期更难判）
                "--disable-background-mode",
                "--disable-features=Translate,msEdgeSplitScreen",
            ])
        except Exception as e:      # noqa: BLE001
            _log("启动 %s 失败：%s" % (bname, e))
            exe, proc = None, None
    if proc is None:
        # ★ 兜底：没有 Chromium 系浏览器就交给系统默认浏览器。
        #   界面是网页，任何浏览器都能开，总比什么都不显示强。
        _log("没有可用的 Chromium 浏览器，改用系统默认浏览器")
        try:
            os.startfile(url)
        except Exception as e:      # noqa: BLE001
            _log("默认浏览器也开不了：%s" % e)
            _fatal("没找到能用的浏览器",
                   "这台电脑上没找到 Edge / Chrome / Brave，系统默认浏览器也打不开。\n"
                   "装一个浏览器（Edge 或 Chrome）就能用了。", url)
            _hold_alive()           # 服务留着，用户手动打开地址也能用
            return

    threading.Thread(target=_watchdog, daemon=True).start()
    threading.Thread(target=_style_window, daemon=True).start()
    if proc is not None:
        try:
            proc.wait()      # 浏览器真退出时会返回；被交接时会 0.3s 就返回
        except Exception:      # noqa: BLE001
            pass
    # ★ 这里**不能**关服务器：启动进程退出 ≠ 窗口关了（见上面 ALIVE 那段注释）。
    #   服务器由页面心跳决定生死，交给看门狗。
    _hold_alive()


if __name__ == "__main__":
    try:
        main()
    except Exception:      # noqa: BLE001
        # 最外层兜底：任何没预料到的异常也要弹出来，不能静默消失
        import traceback
        tb = traceback.format_exc()
        try:
            os.makedirs(core.CONFIG_DIR, exist_ok=True)
            with open(START_LOG, "a", encoding="utf-8") as f:
                f.write(tb + "\n")
        except Exception:      # noqa: BLE001
            pass
        _msgbox("程序启动时崩溃了，抱歉。\n\n" + tb[-800:] +
                "\n\n完整信息已写入：\n" + START_LOG, "空间透镜 · 启动失败")
