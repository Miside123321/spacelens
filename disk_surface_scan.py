# -*- coding: utf-8 -*-
"""
空间透镜 SpaceLens
图形化查看磁盘/文件夹空间占用：矩形树图、类型分布、大文件排行。
纯 Python 标准库（tkinter），Windows 10/11，Python 3.8+。

用法:
  python disk_surface_scan.py                      启动图形界面
  python disk_surface_scan.py --selftest 路径      命令行自测（扫描并输出摘要）
  python disk_surface_scan.py --render 路径 输出.png  渲染矩形树图示例图
  python disk_surface_scan.py --smoke              只验证界面能启动
"""

import os
import sys
import stat
import time
import math
import string
import threading
import queue
import heapq
import shutil
import subprocess
import json
import json
from collections import OrderedDict
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP_TITLE = "空间透镜 · SpaceLens"
APP_VERSION = "4.1.2"   # 修复缩略图偶发重影（put幂等）
# ★ 什么时候才加版本号：
#   加 —— 用户能感知的功能/行为变了（新功能、修好一个真影响使用的 bug、性能明显变化）
#   不加 —— 纯文案、样式微调、日志整理、只改注释；这种直接覆盖同版本号的包就行
DEFAULT_TOP_N = 300
SCAN_THREADS = 8
PRE_SCAN_THREADS = 2     # 启动时的后台预扫描只用 2 个线程，避免抢 CPU/IO
CACHE_MAX = 3           # 最多在内存中保留几个目标的扫描结果（避免重复扫描）
MERGE_RATIO = 0.04      # 布局时小于该比例（占当前视图总量）的项合并为「其他 N 项」拼图块，保证大块方块化、不出现细条
MERGED_FLAG = 4         # 合并块的标记位（叠加在隐藏=1/系统=2 之外）
RANK_MAX_ROWS = 100     # 排行榜标签页最多显示多少行，其余合并为「其他 N 项」
RANK_ANIM_MS = 1100      # 排行榜横条生长动画时长（毫秒）
RANK_FPS_MS = 8         # 排行榜动画帧间隔（约 120fps，更顺滑）
SEARCH_DEBOUNCE_MS = 200 # 搜索框输入后防抖延迟
SEARCH_MAX = 1000        # 搜索结果最多显示条数

# 全局主题：(窗口/面板背景, 主文字, 弱文字, 画布底, 排行榜底, 排行榜轨道, 排行榜悬停,
#           排行榜名称字, 排行榜副标题字, 树状图方块描边, 横条明度, 合并行灰)
THEMES = {
    "light": dict(app="#eef1f5", text="#1f2733", muted="#66717f", canvas="#fdfdfd",
                  rank_bg="#eceff4", track="#ffffff", hover="#dde5f0",
                  rname="#222b38", rsub="#788495", outline="#ffffff", bar_l=0.50,
                  merged="#9aa5b3", tab_bg="#e2e7ee", tab_sel="#fdfdfd",
                  tv_bg="#ffffff", tv_head="#e7ebf1", sb_trough="#e3e7ed",
                  bar="#2fa85c"),      # 排行榜横条统一色（参考电池续航榜那种单色条）
    "dark":  dict(app="#171c26", text="#e6ebf2", muted="#8b97a7", canvas="#1a1f29",
                  rank_bg="#13171f", track="#1e2632", hover="#2a3547",
                  rname="#eef2f7", rsub="#8b97a7", outline="#10151d", bar_l=0.58,
                  merged="#5b6675", tab_bg="#1f2733", tab_sel="#2a3444",
                  tv_bg="#1b222e", tv_head="#232c3a", sb_trough="#1b222e",
                  bar="#4ec87a"),
}
CONFIG_DIR = os.path.join(os.environ.get("LOCALAPPDATA", os.path.expanduser("~")),
                          "DiskSurfaceScan")
SETTINGS_FILE = os.path.join(CONFIG_DIR, "settings.json")


def load_settings():
    """纯本地设置文件（性能模式、树图配色等），换电脑拷过去即可。"""
    try:
        import json
        with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except Exception:
        return {}


def save_settings(d):
    try:
        import json
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(d, f, ensure_ascii=False, indent=2)
    except Exception:
        pass

# ---------------------------------------------------------------- 配色
# 「蓝 / 青 / 浅紫」低饱和色系（苹果风，通透干净）。
# 二级/三级的扩展名和文件夹颜色也从这里取，整个软件配色统一。
PALETTE = [
    "#68bcd9",   # 浅天青蓝
    "#6891d9",   # 鸭卵青蓝
    "#6b68d9",   # 靛蓝
    "#9a68d9",   # 浅紫
    "#c868d9",   # 兰紫
    "#d968b3",   # 玫粉
    "#d9687a",   # 珊瑚红
    "#d98d68",   # 暖橘
    "#d9b368",   # 琥珀
    "#68d9bc",   # 薄荷青
]


def _hsl_of(hexcolor):
    """#rrggbb -> (h 0-360, s 0-1, l 0-1)"""
    h = hexcolor.lstrip("#")
    r, g, b = (int(h[k:k + 2], 16) / 255.0 for k in (0, 2, 4))
    mx, mn = max(r, g, b), min(r, g, b)
    l = (mx + mn) / 2.0
    if mx == mn:
        return 0.0, 0.0, l
    d = mx - mn
    s = d / (2.0 - mx - mn) if l > 0.5 else d / (mx + mn)
    if mx == r:
        hh = ((g - b) / d + (6 if g < b else 0)) / 6.0
    elif mx == g:
        hh = ((b - r) / d + 2) / 6.0
    else:
        hh = ((r - g) / d + 4) / 6.0
    return hh * 360.0, s, l


def _hsl2hex(h, s, l):
    """HSL(0-360, 0-1, 0-1) -> #rrggbb。

    跟下面那个老的 _hsl() 是同一套算法，但那个定义在文件后面，
    而 TYPE_GROUPS 在模块加载时就要用到 lift()，所以这里自带一份。
    """
    h = (h % 360) / 360.0
    if s == 0:
        v = int(l * 255)
        return "#%02x%02x%02x" % (v, v, v)

    def hue(p, q, t):
        if t < 0:
            t += 1
        if t > 1:
            t -= 1
        if t < 1 / 6:
            return p + (q - p) * 6 * t
        if t < 1 / 2:
            return q
        if t < 2 / 3:
            return p + (q - p) * (2 / 3 - t) * 6
        return p

    q = l * (1 + s) if l < 0.5 else l + s - l * s
    p = 2 * l - q
    return "#%02x%02x%02x" % (int(hue(p, q, h + 1 / 3) * 255),
                              int(hue(p, q, h) * 255),
                              int(hue(p, q, h - 1 / 3) * 255))


def tone(hexcolor, dl=0.0, ds=0.0):
    """把调色板里的颜色整体提亮 / 压暗一点（dl 是 HSL 亮度增量）。"""
    h, s, l = _hsl_of(hexcolor)
    return _hsl2hex(h, max(0.0, min(1.0, s + ds)), max(0.0, min(1.0, l + dl)))


def lift(hexcolor, min_l=0.42, cap_s=0.66, only_below=0.36):
    """深色底上太暗的颜色才提亮，其它一律不动。

    #3A0CA3（深紫蓝）和 #073B4C（深青灰）本身很好看，但画在 #0D1117 的
    背景上跟"没有"一样。只有亮度低于 only_below 的才会被提亮到 min_l、
    顺便把饱和度压到 cap_s（用户要的是"低饱和通透"，纯色太扎眼）。
    ★ only_below 不能设大：调色板里 #118AB2 / #7209B7 / #B5179E 的亮度都在
      0.37~0.38，它们本身在深色底上完全看得见，一刀切会把整个调色板洗淡、
      而且互相越来越像。
    """
    h, s, l = _hsl_of(hexcolor)
    if l >= only_below:
        return hexcolor
    return _hsl2hex(h, min(s, cap_s), min_l)


# ---------------------------------------------------------------- 文件类型分组
# (名称, 颜色, 扩展名集合)。无扩展名/未列出的扩展名一律归入“其他”。
# 颜色按扇形相邻顺序挑的 —— 相邻两块在色相上尽量拉开。
TYPE_GROUPS = [
    ("视频",     PALETTE[7], {"mp4", "mkv", "avi", "mov", "wmv", "flv", "webm", "m4v", "ts", "m2ts",
                             "rmvb", "rm", "mpg", "mpeg", "3gp", "f4v", "vob", "mts", "ogv", "mxf",
                             "asf", "divx", "m3u8", "m2v", "wtv", "dvr-ms", "rec", "bik", "roq"}),
    ("音频",     PALETTE[9], {"mp3", "wav", "flac", "aac", "ogg", "m4a", "wma", "ape", "mid", "midi",
                             "opus", "aiff", "amr", "wv", "m4b", "m4r", "aif", "caf", "dsf", "dff",
                             "mod", "xm", "it", "s3m", "spx", "tak", "tta", "ac3", "dts", "wavpack"}),
    ("图片",     PALETTE[2], {"jpg", "jpeg", "png", "gif", "bmp", "webp", "tiff", "tif", "svg", "ico",
                             "heic", "heif", "raw", "cr2", "nef", "arw", "dng", "psd", "ai", "jfif",
                             "avif", "exr", "hdr", "tga", "dds", "icns", "jxl", "qoi", "apng",
                             "cr3", "orf", "rw2", "raf", "sr2", "xcf", "kra", "clip", "svgz"}),
    ("文档",     PALETTE[4], {"doc", "docx", "xls", "xlsx", "ppt", "pptx", "pdf", "txt", "md", "csv",
                             "rtf", "odt", "ods", "odp", "epub", "mobi", "wps", "et", "dps", "one",
                             "xmind", "eml", "pst", "html", "htm", "xml", "json", "jsonl", "yaml",
                             "yml", "toml", "ini", "js", "mjs", "cjs", "css", "scss", "sql",
                             "tex", "azw3", "djvu", "chm", "vsdx", "msg", "xps", "pages", "numbers",
                             "key", "ipynb", "rmd", "org", "nfo", "srt", "ass", "vtt", "lrc"}),
    ("压缩包",   PALETTE[8], {"zip", "rar", "7z", "tar", "gz", "bz2", "xz", "z", "iso", "cab",
                             "lz4", "zst", "lz", "jar", "tgz", "asar", "wxapkg", "crx", "xpi",
                             "lzma", "br", "txz", "tbz", "tbz2", "wim", "esd", "vhd", "vhdx",
                             "dmg", "sitx", "arj", "lzh", "apkg", "cpgz", "xar", "pak2", "001"}),
    ("应用安装", PALETTE[5], {"exe", "msi", "msp", "appx", "msix", "msu", "bat", "cmd", "com",
                             "apk", "ipa", "appimage", "snap", "flatpak", "xap", "deb", "rpm",
                             "apks", "xapk", "appxbundle", "msixbundle", "run", "bin2"}),
    ("系统程序", PALETTE[1], {"dll", "sys", "ocx", "drv", "bin", "dat", "cfg", "conf", "log",
                             "tmp", "bak", "old", "efi", "mui", "manifest", "cat", "inf",
                             "db", "db-wal", "db-shm", "sqlite", "sqlite3", "node", "onnx",
                             "o", "a", "obj", "lib", "so", "dylib", "pdb", "tlb", "ttf", "ttc",
                             "otf", "woff", "woff2", "fon", "fnt", "msstyles", "theme", "lnk",
                             "reg", "pol", "mui2", "nls", "pak0", "idx", "vhdmp"}),
    ("游戏资源", PALETTE[0], {"blk", "ucas", "utoc", "ubulk", "uexp", "uasset", "umap", "usm",
                             "pck", "pak", "bundle", "assets", "ress", "vpk", "wad", "arc",
                             "big", "rpa", "xp3", "nsp", "xci", "wbfs", "rvz", "sav", "vfs",
                             "mihoyobin", "cache2", "bank", "bnk", "fsb", "unity3d", "foz",
                             "tlg", "ftn", "hpw", "qqxlog", "sdf", "cdb", "mpk", "sav2",
                             "sprite", "atlas", "skel", "plist", "tmx", "tsx", "ldb", "sst"}),
    ("其他",     PALETTE[3], set()),
]
# 常见可清理位置。risk: safe=放心清理 / caution=看清再清 / danger=请勿乱动
CLEAN_TARGETS = [
    ("用户临时文件", "%TEMP%", "safe",
     "程序运行时产生的临时文件，可安全清理；正在使用的文件会自动跳过"),
    ("Windows 临时目录", r"C:\Windows\Temp", "safe", "系统级临时文件，可安全清理"),
    ("Windows 更新缓存", r"C:\Windows\SoftwareDistribution\Download", "safe",
     "已完成安装的更新包，删除不影响系统；系统将按需重新下载"),
    ("传递优化缓存", r"C:\Windows\ServiceProfiles\NetworkService\AppData\Local\Microsoft"
                     r"\Windows\DeliveryOptimization", "safe", "Windows 更新的 P2P 分发缓存"),
    ("错误报告归档", r"C:\ProgramData\Microsoft\Windows\WER", "safe",
     "程序崩溃报告文件，排查完成后无保留价值"),
    ("蓝屏转储(小)", r"C:\Windows\Minidump", "safe", "蓝屏时生成的小型转储文件"),
    ("蓝屏转储(完整)", r"C:\Windows\MEMORY.DMP", "safe", "蓝屏完整转储，通常为数 GB"),
    ("缩略图/图标缓存", r"%LOCALAPPDATA%\Microsoft\Windows\Explorer", "safe",
     "资源管理器缩略图数据库，删除后会自动重建"),
    ("Chrome 网页缓存", r"%LOCALAPPDATA%\Google\Chrome\User Data\Default\Cache", "safe",
     "仅为网页缓存，删除后首次访问网站略慢，不影响登录状态"),
    ("Edge 网页缓存", r"%LOCALAPPDATA%\Microsoft\Edge\User Data\Default\Cache", "safe",
     "仅为网页缓存，删除后首次访问网站略慢，不影响登录状态"),
    ("npm 包缓存", r"%LOCALAPPDATA%\npm-cache", "safe", "npm 包缓存，需要时会重新下载"),
    ("pip 包缓存", r"%LOCALAPPDATA%\pip\Cache", "safe",
     "Python 包的下载缓存，重装依赖时会自动重新下载"),
    ("Windows 旧系统备份", r"C:\Windows.old", "caution",
     "升级前的旧系统备份（通常十余 GB）。如需回退请保留；确定不回退可清理"),
    ("回收站", r"C:\$Recycle.Bin", "caution", "已删除但尚未清空的文件，清空前请自行确认"),
    ("休眠文件", r"C:\hiberfil.sys", "caution",
     "大小与物理内存相当。如不使用休眠，可用管理员权限执行 powercfg /h off 释放（请勿直接删除文件）"),
    ("微信聊天文件", r"%USERPROFILE%\Documents\WeChat Files", "caution",
     "聊天记录和收到的文件，建议先在微信「设置 → 存储空间」里管理"),
    ("QQ 文件", r"%USERPROFILE%\Documents\Tencent Files", "caution",
     "聊天记录和收到的文件，建议先在 QQ 的设置里管理"),
    ("NuGet 包缓存", r"%USERPROFILE%\.nuget\packages", "caution",
     "VS/.NET 包缓存，删除后项目首次还原会变慢"),
    ("Gradle 缓存", r"%USERPROFILE%\.gradle\caches", "caution",
     "Android/Gradle 构建缓存，删除后需重新构建"),
    ("Maven 本地仓库", r"%USERPROFILE%\.m2\repository", "caution",
     "Java 依赖包的本地仓库，删除后首次构建会重新下载"),
    ("页面文件", r"C:\pagefile.sys", "danger",
     "虚拟内存，不要手动删。要调整请到「系统属性 → 高级 → 性能设置 → 虚拟内存」"),
]
CLEAN_RISK = {"safe": ("放心清理", "#2f9e5c"), "caution": ("看清再清", "#d9a441"),
              "danger": ("请勿乱动", "#d9534f")}


def path_size(path, budget=5.0):
    """算一个文件/目录占多少字节；带时间预算，超时就返回已统计的部分。"""
    import time as _t
    t0 = _t.time()
    try:
        if os.path.isfile(path):
            return os.path.getsize(path)
    except OSError:
        return 0
    total = 0
    stack = [path]
    while stack:
        if _t.time() - t0 > budget:
            break
        d = stack.pop()
        try:
            with os.scandir(d) as it:
                for e in it:
                    try:
                        if e.is_dir(follow_symlinks=False):
                            stack.append(e.path)
                        else:
                            total += e.stat(follow_symlinks=False).st_size
                    except OSError:
                        pass
        except OSError:
            pass
    return total




def spacemap_exe_path():
    """找 SpaceMap.exe。

    优先用**打包进本程序**的那份（PyInstaller 会释放到临时目录），首次运行把它
    拷到 %LOCALAPPDATA%\\DiskSurfaceScan\\ 缓存下来 —— 之后直接从那启动，
    省得每次都从临时目录跑。都没有才退回桌面那份（开发时的兜底）。
    """
    cache = os.path.join(CONFIG_DIR, "SpaceMap.exe")
    src = None
    cands = []
    base = getattr(sys, "_MEIPASS", None)
    if base:
        cands.append(os.path.join(base, "SpaceMap.exe"))
    cands.append(os.path.join(os.path.dirname(os.path.abspath(__file__)), "SpaceMap.exe"))
    for c in cands:
        if os.path.isfile(c):
            src = c
            break
    if src:
        try:
            os.makedirs(CONFIG_DIR, exist_ok=True)
            # 已缓存且大小一致就不重复拷（88MB，每次拷会明显拖慢启动）
            if not (os.path.isfile(cache) and os.path.getsize(cache) == os.path.getsize(src)):
                shutil.copyfile(src, cache)
        except OSError:
            pass
        return cache if os.path.isfile(cache) else src
    # ★ 这里原本还有一个写死的桌面路径兜底（开发时用的），
    #   分享出去的版本本来就没打包 SpaceMap.exe，那个兜底永远命中不了，
    #   只会把作者的用户名泄出去 —— 已删。
    return ""
SPACEMAP_TITLES = ("SpaceMap - 磁盘空间树图", "SpaceMap")  # 按标题抓它的窗口
SOFT_ICON_DIR = os.path.join(CONFIG_DIR, "icons")
SOFT_ICON_MAX = 120        # 只给占用最大的这些软件抽图标，避免开一堆进程
SOFT_SIZE_BUDGET = 4.0     # 单个目录的遍历预算（秒），超时返回已统计部分
# 按名字去这些地方找"同一个软件"的数据目录
SOFT_NAME_ROOTS = ["%LOCALAPPDATA%", "%APPDATA%", "%PROGRAMDATA%",
                   "%USERPROFILE%\\Documents", "%USERPROFILE%\\AppData\\LocalLow"]


def norm_tokens(name):
    """把软件名拆成用于匹配的词，丢掉版本号、位数、常见后缀这类噪声。"""
    import re as _re
    t = name.lower()
    t = _re.sub(r"[（(].*?[)）]", " ", t)
    t = _re.sub(r"\b(x64|x86|64|32|bit|bit版)\b", " ", t)
    t = _re.sub(r"\b\d+(\.\d+)*\b", " ", t)
    t = _re.sub(r"[^0-9a-z\u4e00-\u9fff]+", " ", t)
    stop = {"microsoft", "windows", "update", "the", "for", "and", "with",
            "software", "app", "application", "driver", "runtime", "redistributable",
            "version", "edition", "professional", "ultimate", "setup", "installer",
            # ★ 公司名里的通用词：这些词拿去匹配目录，会把别人的目录也认领过来。
            #   实测 "Hello Games" 的 games 把 Rockstar / Epic / Riot / GameSir
            #   全算到《无人深空》头上（34.2 GB 里有 3 GB 是假的）。
            "game", "games", "studio", "studios", "entertainment", "interactive",
            "system", "systems", "technology", "technologies", "tech", "media",
            "digital", "group", "company", "corp", "corporation", "ltd", "limited",
            "gmbh", "labs", "lab", "network", "networks", "solution", "solutions",
            "service", "services", "global", "holdings", "international", "inc"}
    out = []
    for w in t.split():
        if len(w) >= 3 and w not in stop and w not in out:
            out.append(w)
    return out


_GENERIC_DIRS = {"application", "applications", "app", "bin", "current",
                 "app-64", "app-32", "program", "programs", "binaries"}


def _dir_from_cmd(cmd):
    """从卸载命令 / 图标路径里反推安装目录。认不出就返回空串。

    支持这些形态（注册表里都真实存在）：
        C:\\Program Files\\bilibili\\卸载哔哩哔哩.exe
        "C:\\Users\\wan\\AppData\\Local\\Doubao\\Application\\uninstall.exe"
        "C:\\xx\\app.exe" /currentuser
        "E:\\JianyingPro\\uninst.exe"
    """
    s = (cmd or "").strip()
    if not s:
        return ""
    # 去掉 ",索引"（DisplayIcon 常见写法 xxx.exe,0）
    if "," in s and not s.startswith('"'):
        head = s.rsplit(",", 1)[0]
        if s.rsplit(",", 1)[1].strip().lstrip("-").isdigit():
            s = head
    if s.startswith('"'):
        s = s[1:].split('"', 1)[0]
    else:
        # 没有引号：取前面第一段（到 .exe 为止）
        low = s.lower()
        k = low.find(".exe")
        s = s[:k + 4] if k > 0 else s.split(" ", 1)[0]
    s = os.path.expandvars(s.strip())
    if not s:
        return ""
    if os.path.isfile(s):
        d = os.path.dirname(s)
    elif os.path.isdir(s):
        d = s
    else:
        return ""
    # 落点是 Application / bin 这类通用目录时，再往上退一层
    try:
        if os.path.basename(d).lower() in _GENERIC_DIRS:
            up = os.path.dirname(d)
            if up and os.path.isdir(up):
                d = up
    except (OSError, ValueError):
        pass
    return d if os.path.isdir(d) else ""


def read_installed_apps():
    """读注册表 Uninstall 键，返回 [{name,publisher,loc,icon,est}]。"""
    import winreg
    roots = [
        (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\\Microsoft\\Windows\\CurrentVersion\\Uninstall"),
        (winreg.HKEY_LOCAL_MACHINE,
         r"SOFTWARE\\WOW6432Node\\Microsoft\\Windows\\CurrentVersion\\Uninstall"),
        (winreg.HKEY_CURRENT_USER, r"SOFTWARE\\Microsoft\\Windows\\CurrentVersion\\Uninstall"),
    ]
    apps, seen = [], set()
    for hive, sub_key in roots:
        try:
            key = winreg.OpenKey(hive, sub_key)
        except OSError:
            continue
        try:
            n = winreg.QueryInfoKey(key)[0]
        except OSError:
            n = 0
        for i in range(n):
            try:
                sk = winreg.EnumKey(key, i)
                k2 = winreg.OpenKey(key, sk)
            except OSError:
                continue
            vals = {}
            try:
                m = winreg.QueryInfoKey(k2)[1]
                for j in range(m):
                    try:
                        nm, val, _t = winreg.EnumValue(k2, j)
                        vals[nm] = val
                    except OSError:
                        pass
            except OSError:
                pass
            try:
                winreg.CloseKey(k2)
            except OSError:
                pass
            name = str(vals.get("DisplayName") or "").strip()
            if not name or vals.get("SystemComponent") == 1:
                continue
            if vals.get("ParentKeyName"):
                continue
            ico = str(vals.get("DisplayIcon") or "").strip().strip('"')
            if "," in ico:
                ico = ico.rsplit(",", 1)[0].strip().strip('"')
            loc = str(vals.get("InstallLocation") or "").strip().strip('"')
            # ★ InstallLocation 绝大多数第三方软件是空的（实测本机 44 个里 40 多个为空），
            #   只用它就等于"位置未知"，只能靠名字去猜目录 —— 中文名基本猜不中。
            if not loc or not os.path.isdir(os.path.expandvars(loc)):
                cand = (_dir_from_cmd(str(vals.get("UninstallString") or ""))
                        or _dir_from_cmd(str(vals.get("QuietUninstallString") or ""))
                        or _dir_from_cmd(ico))
                loc = cand or loc
            try:
                est = int(vals.get("EstimatedSize") or 0) * 1024
            except (TypeError, ValueError):
                est = 0
            k = name.lower()
            if k in seen:
                continue
            seen.add(k)
            apps.append({"name": name, "publisher": str(vals.get("Publisher") or "").strip(),
                         "loc": loc, "icon": ico, "est": est,
                         "uninst": str(vals.get("QuietUninstallString")
                                       or vals.get("UninstallString") or "").strip()})
        try:
            winreg.CloseKey(key)
        except OSError:
            pass
    return apps


SCAN_CACHE_DIR = os.path.join(CONFIG_DIR, "scans")
SCAN_CACHE_TTL = 7 * 24 * 3600      # 扫描结果落盘后保留 7 天
SCAN_CACHE_VER = 2      # 2 起只存纯数据，不再 pickle 类实例


class CachedScan(object):
    """从磁盘缓存恢复出来的扫描结果。

    只带数据和方法，和 Scanner 对外接口一致，所以界面代码不用改。
    """

    def __init__(self, root, stats, folders, ext_stats, top_files, ts):
        self.root = root
        self.stats = stats
        self.folders = folders
        self.ext_stats = ext_stats
        self.top_files = top_files
        self.scanned_at = time.strftime("%m-%d %H:%M", time.localtime(ts))
        # all_items（全量条目索引）是从 folders 推导出来的。
        # ★ 改成**惰性**：全量展开 C 盘约百万条、实测 1.4s，而它只被"搜索"用到。
        #   放在 __init__ 里会让每次切盘都白等 1.4s（切盘顿挫的主因之一）。
        self._all_items = None

    @property
    def all_items(self):
        """惰性构建全量条目索引（首次访问时才建，之后缓存）。"""
        if self._all_items is None:
            idx = []
            for fpath, frec in self.folders.items():
                for name, sz, is_dir, g, flags in frec["children"]:
                    idx.append((os.path.join(fpath, name), name.lower(),
                                sz, is_dir, g, flags))
            self._all_items = idx
        return self._all_items

    def folder_size(self, path):
        rec = self.folders.get(path)
        return rec["size"] if rec else 0

    def top_folders(self, n=300):
        items = [(rec["size"], path) for path, rec in self.folders.items()
                 if path != self.root]
        items.sort(key=lambda t: -t[0])
        out = []
        for size, path in items[:n]:
            rec = self.folders[path]
            out.append((size, path, os.path.basename(path), os.path.dirname(path),
                        _dominant_of(rec), rec["nfiles"]))
        return out

    def type_stats(self):
        ts = [[0, 0] for _ in TYPE_GROUPS]
        for ext, (b, c) in self.ext_stats.items():
            g = EXT_TO_GROUP.get(ext.lstrip("."), len(TYPE_GROUPS) - 1)
            ts[g][0] += b
            ts[g][1] += c
        return ts


# ---------------------------------------------------------------- 快照历史
# 「变化」页要回答的是"跟上一次比，什么变大了" —— 这需要两个时间点的数据，
# 而落盘缓存只留最新一份。所以额外存一串精简快照。
SNAP_DIR = os.path.join(CONFIG_DIR, "snaps")
SNAP_MIN = 1 * 1024 * 1024          # 文件夹：只记 >= 1MB 的
SNAP_FILE_MIN = 50 * 1024 * 1024    # 文件：只记 >= 50MB 的
SNAP_KEEP = 12                      # 每个目标最多留几份
SNAP_GAP = 120                      # 两次快照至少隔这么久（秒），免得反复重扫刷屏
DIFF_MIN = 20 * 1024 * 1024         # 差异小于这个的不报
DIFF_TOP = 60                       # 每类最多列几条
_SNAP_LOCK = threading.Lock()


def _snap_file(root):
    import hashlib
    key = os.path.normcase(os.path.normpath(root or ""))
    h = hashlib.sha1(key.encode("utf-8", "replace")).hexdigest()[:16]
    return os.path.join(SNAP_DIR, h + ".pkl")


def make_snapshot(folders, root, ts):
    """把一次扫描压成精简快照：{文件夹路径: 大小} + {大文件路径: 大小}。"""
    fs = {}
    for p, rec in folders.items():
        sz = rec.get("size", 0)
        if sz >= SNAP_MIN:
            fs[p] = sz
    files = {}
    for p, rec in folders.items():
        # 大文件必然待在大文件夹里 —— 先按文件夹大小剪枝，省掉全量遍历
        if rec.get("size", 0) < SNAP_FILE_MIN:
            continue
        for name, sz, is_dir, _g, _fl in (rec.get("children") or ()):
            if not is_dir and sz >= SNAP_FILE_MIN:
                files[os.path.join(p, name)] = sz
    return {"ts": float(ts or time.time()), "root": root,
            "folders": fs, "files": files}


def _load_snaps(root):
    import pickle
    try:
        f = _snap_file(root)
        if not os.path.isfile(f):
            return []
        with open(f, "rb") as fh:
            d = pickle.load(fh)
        return d if isinstance(d, list) else []
    except Exception:      # noqa: BLE001
        return []


def push_snapshot(folders, root, ts=None):
    """追加一份快照（太近的不重复记）。返回快照数量。"""
    import pickle
    if not root or not folders:
        return 0
    ts = float(ts or time.time())
    with _SNAP_LOCK:
        try:
            os.makedirs(SNAP_DIR, exist_ok=True)
            snaps = _load_snaps(root)
            if snaps and abs(ts - snaps[-1].get("ts", 0)) < 1.0:
                return len(snaps)      # 就是同一份（时间戳一模一样），别白写一次盘
            if snaps and abs(ts - snaps[-1].get("ts", 0)) < SNAP_GAP:
                snaps[-1] = make_snapshot(folders, root, ts)   # 同一轮的刷新，替换
            else:
                snaps.append(make_snapshot(folders, root, ts))
            snaps.sort(key=lambda x: x.get("ts", 0))
            del snaps[:-SNAP_KEEP]
            f = _snap_file(root)
            tmp = f + ".tmp"
            with open(tmp, "wb") as fh:
                pickle.dump(snaps, fh, protocol=4)
            os.replace(tmp, f)
            return len(snaps)
        except Exception:      # noqa: BLE001
            return 0


def diff_pair(prev, cur, scope=None):
    """两份快照的差异。prev 可以比 cur 老，也可以反过来（自动判断方向）。

    scope: 只看这个目录的**直属子项**（界面上点某个文件夹就往下钻一层）。
    """
    if prev.get("ts", 0) > cur.get("ts", 0):
        prev, cur = cur, prev
    pf, cf = prev.get("folders") or {}, cur.get("folders") or {}
    root = cur.get("root")
    sc = os.path.normcase(os.path.normpath(scope)).rstrip("\\/") if scope else ""

    def sel(p):
        """没给 scope 就全都要；给了就只留它的直属子项。"""
        if not sc:
            return True
        par = os.path.normcase(os.path.dirname(p.rstrip("\\/"))).rstrip("\\/")
        return par == sc

    grown, added = [], []
    for p, sz in cf.items():
        if p == root:          # 根目录自己必然"涨了全盘那么多"，卡头已经写了总量
            continue
        if not sel(p):
            continue
        o = pf.get(p)
        if o is None:
            if sz >= DIFF_MIN:
                added.append({"path": p, "size": sz})
        elif sz - o >= DIFF_MIN:
            grown.append({"path": p, "size": sz, "was": o, "delta": sz - o})
    gone = [{"path": p, "size": sz} for p, sz in pf.items()
            if p not in cf and p != root and sz >= DIFF_MIN and sel(p)]
    pfil, cfil = prev.get("files") or {}, cur.get("files") or {}
    newf = [{"path": p, "size": sz} for p, sz in cfil.items()
            if p not in pfil and sel(p)]
    delf = [{"path": p, "size": sz} for p, sz in pfil.items()
            if p not in cfil and sel(p)]
    k = lambda d: -d["size"]
    grown.sort(key=k); added.sort(key=k); gone.sort(key=k)
    newf.sort(key=k); delf.sort(key=k)
    return {
        "prev_ts": prev.get("ts", 0), "cur_ts": cur.get("ts", 0),
        "span": max(0.0, cur.get("ts", 0) - prev.get("ts", 0)),
        # ★ 只能取根目录那条：文件夹大小是自下而上累计的，全加起来会把
        #   父子路径重复计算（实测 112GB 的盘能加成 622GB）
        "prev_used": pf.get(prev.get("root"), 0),
        "cur_used": cf.get(cur.get("root"), 0),
        "grown": grown[:DIFF_TOP], "added": added[:DIFF_TOP],
        "gone": gone[:DIFF_TOP], "newf": newf[:DIFF_TOP], "delf": delf[:DIFF_TOP],
        "n_grown": len(grown), "n_added": len(added), "n_gone": len(gone),
        "n_newf": len(newf), "n_delf": len(delf),
        # 下钻用：这一层自己的起点/终点大小
        "scope": scope or "",
        "scope_prev": pf.get(scope, 0) if scope else pf.get(root, 0),
        "scope_cur": cf.get(scope, 0) if scope else cf.get(root, 0),
    }


def _scan_cache_file(path):
    import hashlib
    key = os.path.normcase(os.path.normpath(path))
    h = hashlib.sha1(key.encode("utf-8", "replace")).hexdigest()[:16]
    return os.path.join(SCAN_CACHE_DIR, h + ".pkl")


def save_scan_cache(scanner):
    """把一次扫描的结果落盘。失败就算了，不影响主流程。"""
    import pickle
    try:
        if not getattr(scanner, "root", None):
            return
        os.makedirs(SCAN_CACHE_DIR, exist_ok=True)
        # stats 只存纯 dict —— pickle 类实例会把模块名一起写进去（打包后是 __main__），
        # 换个上下文就反序列化失败，所以这里不存对象。
        # ScanStats 用了 __slots__，没有 __dict__，必须按 slots 逐个取
        blob = {"ver": SCAN_CACHE_VER, "ts": time.time(), "root": scanner.root,
                "stats": {k: getattr(scanner.stats, k, 0) for k in ScanStats.__slots__},
                "folders": scanner.folders,
                "ext_stats": scanner.ext_stats, "top_files": scanner.top_files}
        target = _scan_cache_file(scanner.root)
        # ★ 覆盖之前先把"上一次的扫描"存进历史。不这么做的话永远只有最新一份，
        #   「变化」页就没得比 —— 而这份旧缓存可能正好是几天前的，是现成的基线。
        try:
            if os.path.isfile(target):
                with open(target, "rb") as fh:
                    old = pickle.load(fh)
                if isinstance(old, dict) and old.get("ver") == SCAN_CACHE_VER:
                    push_snapshot(old.get("folders"), old.get("root"),
                                  old.get("ts") or 0)
        except Exception:      # noqa: BLE001
            pass
        tmp = target + ".tmp"
        with open(tmp, "wb") as f:
            pickle.dump(blob, f, protocol=4)
        os.replace(tmp, target)
        push_snapshot(scanner.folders, scanner.root, blob["ts"])
    except Exception:      # noqa: BLE001
        pass


def load_scan_cache(path):
    """读落盘的扫描结果；超过 7 天或格式不符就返回 None（会重新扫）。"""
    import pickle
    try:
        f = _scan_cache_file(path)
        if not os.path.isfile(f):
            return None
        if time.time() - os.path.getmtime(f) > SCAN_CACHE_TTL:
            return None
        with open(f, "rb") as fh:
            blob = pickle.load(fh)
        if not isinstance(blob, dict) or blob.get("ver") != SCAN_CACHE_VER:
            return None
        st = ScanStats()
        for _k, _v in (blob.get("stats") or {}).items():
            try:
                setattr(st, _k, _v)
            except Exception:      # noqa: BLE001
                pass
        # 顺手把这份缓存记进快照历史：这样「变化」页不用等到下次重扫就有基线。
        # 时间戳用缓存自己的，重复调用时上面那条"同一份不重写"会挡住。
        push_snapshot(blob["folders"], blob["root"], blob["ts"])
        return CachedScan(blob["root"], st, blob["folders"],
                          blob["ext_stats"], blob["top_files"], blob["ts"])
    except Exception:      # noqa: BLE001
        return None


def clean_scan_cache():
    """清掉过期的落盘缓存。"""
    try:
        if not os.path.isdir(SCAN_CACHE_DIR):
            return
        now = time.time()
        for n in os.listdir(SCAN_CACHE_DIR):
            p = os.path.join(SCAN_CACHE_DIR, n)
            try:
                if now - os.path.getmtime(p) > SCAN_CACHE_TTL:
                    os.remove(p)
            except OSError:
                pass
    except OSError:
        pass


EXT_TO_GROUP = {}
for _i, (_n, _c, _exts) in enumerate(TYPE_GROUPS):
    for _e in _exts:
        EXT_TO_GROUP[_e] = _i


def _load_user_ext_map():
    """用户自定义的扩展名映射（可选文件）：
        %LOCALAPPDATA%\\DiskSurfaceScan\\extmap.json
    内容形如 {"xyz": 7, "abc": 4}，值是上面 TYPE_GROUPS 的下标。
    纯本地文件、纯离线；换电脑时把这个 json 一起拷过去就行。
    """
    try:
        import json
        path = os.path.join(CONFIG_DIR, "extmap.json")
        with open(path, "r", encoding="utf-8") as f:
            raw = json.load(f)
    except Exception:
        return {}
    out = {}
    for k, v in raw.items():
        try:
            idx = int(v)
        except Exception:
            continue
        if 0 <= idx < len(TYPE_GROUPS):
            out[str(k).lstrip(".").lower()] = idx
    return out


# 内置表打底，用户表覆盖（这样"认不出来"的扩展名可以自己补，不用改代码）
USER_EXT_MAP = _load_user_ext_map()


def group_of(name):
    ext = os.path.splitext(name)[1].lstrip(".").lower()
    if ext in USER_EXT_MAP:
        return USER_EXT_MAP[ext]
    return EXT_TO_GROUP.get(ext, len(TYPE_GROUPS) - 1)


def write_user_ext_map_example():
    """首次运行时写一份空的映射文件，方便用户照格式自己加。"""
    try:
        import json
        path = os.path.join(CONFIG_DIR, "extmap.json")
        if os.path.exists(path):
            return
        os.makedirs(CONFIG_DIR, exist_ok=True)
        names = [g[0] for g in TYPE_GROUPS]
        with open(path, "w", encoding="utf-8") as f:
            json.dump({"__说明__": "扩展名(不带点) -> 分类下标；下标对应：%s" %
                       "、".join("%d=%s" % (i, n) for i, n in enumerate(names))},
                      f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def human_size(n):
    n = float(n)
    for unit in ("B", "KB", "MB", "GB", "TB", "PB"):
        if n < 1024 or unit == "PB":
            return ("%d B" % int(n)) if unit == "B" else ("%.1f %s" % (n, unit))
        n /= 1024.0
    return "%.1f PB" % n


def _clip(name, w):
    """按像素宽度截断文本，中文按双倍宽度估算。"""
    n = max(1, int(w / 14.5))
    if len(name) > n:
        return name[:max(1, n - 1)] + "…"
    return name


def _hsl(h, s, l):
    """HSL(0-360, 0-1, 0-1) -> #rrggbb"""
    h = (h % 360) / 360.0
    if s == 0:
        v = int(l * 255)
        return "#%02x%02x%02x" % (v, v, v)

    def hue(p, q, t):
        if t < 0:
            t += 1
        if t > 1:
            t -= 1
        if t < 1 / 6:
            return p + (q - p) * 6 * t
        if t < 1 / 2:
            return q
        if t < 2 / 3:
            return p + (q - p) * (2 / 3 - t) * 6
        return p

    q = l * (1 + s) if l < 0.5 else l + s - l * s
    p = 2 * l - q
    r = hue(p, q, h + 1 / 3)
    g = hue(p, q, h)
    b = hue(p, q, h - 1 / 3)
    return "#%02x%02x%02x" % (int(r * 255), int(g * 255), int(b * 255))


def rank_color(i, lightness=0.5):
    """第 i 行的颜色：在 PALETTE 里按 7 的步长跳着取。

    步长 7 和长度 10 互质，所以连着 10 行都不会撞色，而且颜色始终在这个
    色系里（原来是黄金角算色相，什么颜色都能冒出来，跟新配色不搭）。
    lightness 沿用旧签名：0.5 = 调色板原色，越大多越亮。
    """
    c = lift(PALETTE[(i * 7) % len(PALETTE)])
    if abs(lightness - 0.5) < 0.02:
        return c
    return tone(c, (lightness - 0.5) * 0.9)


def round_rect_points(x1, y1, x2, y2, r):
    """圆角矩形多边形点（配合 create_polygon(smooth=True)）。"""
    r = max(0, min(r, (x2 - x1) / 2.0, (y2 - y1) / 2.0))
    if r <= 0:
        return [x1, y1, x2, y1, x2, y2, x1, y2]
    return [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r,
            x2, y2 - r, x2, y2, x2 - r, y2, x1 + r, y2,
            x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]


def ring_points(cx, cy, r_out, r_in, a_start, a_end, step=2.0):
    """圆环上一段（角度制，逆时针，0° = 3 点钟方向）的闭合多边形点。

    不用 Tk 的 create_arc(style="arc", width=...)：它在 Windows 上画粗圆弧会有
    锯齿，相邻两段之间还会露缝。自己按 2° 采样出一圈点，稳得多也圆得多。
    """
    import math
    n = max(2, int(abs(a_end - a_start) / step) + 1)
    pts = []
    for i in range(n + 1):
        a = math.radians(a_start + (a_end - a_start) * i / float(n))
        pts.extend([cx + r_out * math.cos(a), cy - r_out * math.sin(a)])
    for i in range(n, -1, -1):
        a = math.radians(a_start + (a_end - a_start) * i / float(n))
        pts.extend([cx + r_in * math.cos(a), cy - r_in * math.sin(a)])
    return pts


SEL_BLUE = "#6cb6ff"   # 选中框主色：淡蓝


class RoundButton(tk.Canvas):
    """圆角按钮。

    ttk 的按钮在 Windows 上做不出圆角，所以用 Canvas 自己画一个。
    对外接口尽量和 ttk.Button 保持一致（text / state / command / config），
    这样替换调用点时不用改别的代码。
    """

    def __init__(self, master, text="", command=None, outer="#eef1f5",
                 bg="#e2e7ee", fg="#1f2733", hover=None, disabled_fg=None,
                 font=("Microsoft YaHei UI", 9), padx=16, height=30, **kw):
        self._text = text
        self._command = command
        self._outer = outer
        self._bg = bg
        self._fg = fg
        self._hover = hover or bg
        self._hovering = False
        self._state = "normal"
        self._font = font
        self._padx = padx
        self._height = height
        super().__init__(master, height=height, bd=0, highlightthickness=0,
                         bg=outer, **kw)
        self._btn_w = max(60, self._measure(text) + padx * 2)
        self.configure(width=self._btn_w)
        self._disabled_fg = disabled_fg or _blend(fg, 0.55, outer)
        self.bind("<Enter>", self._on_enter)
        self.bind("<Leave>", self._on_leave)
        self.bind("<Button-1>", self._on_press)
        self.bind("<ButtonRelease-1>", self._on_release)
        self._redraw()

    # --- 兼容 ttk.Button 的接口 ---
    def config(self, **kw):
        self.configure(**kw)

    def configure(self, **kw):
        redraw = False
        if "text" in kw:
            self._text = kw.pop("text")
            need = max(60, self._measure(self._text) + self._padx * 2)
            if need != self._btn_w:
                self._btn_w = need
                super().configure(width=need)
            redraw = True
        if "state" in kw:
            self._state = kw.pop("state")
            redraw = True
        if kw:
            super().configure(**kw)
        if redraw:
            self._redraw()

    def cget(self, key):
        if key == "text":
            return self._text
        if key == "state":
            return self._state
        return super().cget(key)

    def set_colors(self, outer, bg, fg, hover):
        self._outer = outer
        self._bg = bg
        self._fg = fg
        self._hover = hover
        self._disabled_fg = _blend(fg, 0.55, outer)
        super().configure(bg=outer)
        self._redraw()

    def _measure(self, text):
        item = self.create_text(0, 0, text=text, font=self._font, anchor="nw")
        box = self.bbox(item)
        self.delete(item)
        return (box[2] - box[0]) if box else 40

    def _redraw(self):
        self.delete("all")
        w, h = self._btn_w, self._height
        enabled = self._state != "disabled"
        bg = self._hover if (enabled and self._hovering) else self._bg
        fg = self._fg if enabled else self._disabled_fg
        self.create_polygon(round_rect_points(1, 1, w - 1, h - 1, (h - 2) / 2.0),
                            fill=bg, outline="", smooth=True)
        self.create_text(w / 2.0, h / 2.0, text=self._text, fill=fg, font=self._font)

    def _on_enter(self, _e):
        self._hovering = True
        if self._state != "disabled":
            self._redraw()

    def _on_leave(self, _e):
        self._hovering = False
        self._redraw()

    def _on_press(self, _e):
        if self._state != "disabled":
            self.configure(cursor="hand2")

    def _on_release(self, ev):
        if self._state == "disabled" or self._command is None:
            return
        if 0 <= ev.x <= self._btn_w and 0 <= ev.y <= self._height:
            self._command()

def draw_glow_selection(c, x1, y1, x2, y2, rad, bg, tag=None, core=SEL_BLUE):
    """淡蓝色圆角选中框 + 外扩光晕（多层半透明感描边模拟 blur）。
    bg 为所在画布底色，光晕颜色由主色向底色逐层混合。"""
    kw = {"fill": "", "smooth": True}
    if tag:
        kw["tags"] = tag
    # 从最外层（最淡）画到内层（最亮），宽描边互相叠加形成光晕
    for d, frac, w in ((5, 0.86, 6), (4, 0.74, 6), (3, 0.60, 5), (2, 0.44, 4), (1, 0.26, 3)):
        c.create_polygon(round_rect_points(x1 - d, y1 - d, x2 + d, y2 + d, rad + d),
                         outline=_blend(core, frac, bg), width=w, **kw)
    c.create_polygon(round_rect_points(x1, y1, x2, y2, rad),
                     outline=core, width=2, **kw)


# ---------------------------------------------------------------- 扫描引擎
class ScanStats(object):
    __slots__ = ("files", "dirs", "skipped", "bytes", "total", "total_files",
                 "total_dirs", "hidden_files", "hidden_bytes", "system_files",
                 "system_bytes", "start", "end", "cancelled", "last_path", "error")

    def __init__(self):
        self.files = 0
        self.dirs = 0
        self.skipped = 0
        self.bytes = 0
        self.total = 0
        self.total_files = 0
        self.total_dirs = 0
        self.hidden_files = 0
        self.hidden_bytes = 0
        self.system_files = 0
        self.system_bytes = 0
        self.start = 0.0
        self.end = 0.0
        self.cancelled = False
        self.last_path = ""
        self.error = ""


class Scanner(object):
    """多线程 scandir 全量遍历：统计每个文件夹大小、文件类型、最大文件。
    遍历结果存为 dict 树，扫描完成后自底向上汇总。"""

    def __init__(self, root, nthreads=SCAN_THREADS, top_n=DEFAULT_TOP_N):
        self.root = os.path.abspath(root)
        self.nthreads = nthreads
        self.top_n = top_n
        self.cancel = threading.Event()
        self.stats = ScanStats()
        self.folders = {}       # path -> record
        self.ext_stats = {}     # ext -> [bytes, count]
        self.top_files = []     # 最小堆 (size, path, name, group)
        self.all_items = []    # 全量条目 (fullpath, name_lower, size, is_dir, group, flags)，供即时搜索
        self._queue = queue.Queue()
        self._pending = 0
        self._lock = threading.Lock()
        self._ext_lock = threading.Lock()

    # ---- 内部 ----
    @staticmethod
    def _new_record():
        return {"children": [], "fbytes": 0,
                "groups": [0] * len(TYPE_GROUPS), "gcounts": [0] * len(TYPE_GROUPS),
                "size": 0, "nfiles": 0}

    def _push_top(self, sz, path, name, g, flags):
        if len(self.top_files) < self.top_n:
            heapq.heappush(self.top_files, (sz, path, name, g, flags))
        elif sz > self.top_files[0][0]:
            heapq.heapreplace(self.top_files, (sz, path, name, g, flags))

    def _worker(self):
        while not self.cancel.is_set():
            try:
                path = self._queue.get_nowait()
            except queue.Empty:
                with self._lock:
                    done = (self._pending == 0)
                if done:
                    return
                time.sleep(0.002)
                continue
            try:
                self._scan_folder(path)
            except Exception:
                pass
            finally:
                with self._lock:
                    self._pending -= 1
        with self._lock:
            self.stats.cancelled = True

    def _scan_folder(self, path):
        rec = self.folders[path]
        children = []
        fbytes = 0
        nfiles = 0
        groups = [0] * len(TYPE_GROUPS)
        gcounts = [0] * len(TYPE_GROUPS)
        try:
            it = os.scandir(path)
        except OSError:
            with self._lock:
                self.stats.skipped += 1
            rec["children"] = children
            return
        with it:
            for e in it:
                try:
                    # 一次 stat 拿齐大小+属性（Windows 下为缓存数据，无额外系统调用）
                    try:
                        srec = e.stat(follow_symlinks=False)
                        attrs = srec.st_file_attributes if srec else 0
                    except OSError:
                        attrs = 0
                        srec = None
                    flags = ((1 if attrs & stat.FILE_ATTRIBUTE_HIDDEN else 0) |
                             (2 if attrs & stat.FILE_ATTRIBUTE_SYSTEM else 0))
                    if e.is_dir(follow_symlinks=False):
                        # 跳过 junction/符号链接，避免循环和重复计数
                        if attrs & stat.FILE_ATTRIBUTE_REPARSE_POINT:
                            continue
                        cp = e.path
                        self.folders[cp] = self._new_record()
                        children.append([e.name, 0, True, -1, flags])
                        with self._lock:
                            self._pending += 1
                            self.stats.dirs += 1
                        self._queue.put(cp)
                    else:
                        sz = srec.st_size if srec else 0
                        g = group_of(e.name)
                        children.append([e.name, sz, False, g, flags])
                        fbytes += sz
                        nfiles += 1
                        groups[g] += sz
                        gcounts[g] += 1
                        if flags & 1:
                            with self._lock:
                                self.stats.hidden_files += 1
                                self.stats.hidden_bytes += sz
                        if flags & 2:
                            with self._lock:
                                self.stats.system_files += 1
                                self.stats.system_bytes += sz
                        ext = os.path.splitext(e.name)[1].lower()
                        with self._ext_lock:
                            es = self.ext_stats.get(ext)
                            if es is None:
                                self.ext_stats[ext] = [sz, 1]
                            else:
                                es[0] += sz
                                es[1] += 1
                        if sz > 0:
                            self._push_top(sz, e.path, e.name, g, flags)
                except OSError:
                    with self._lock:
                        self.stats.skipped += 1
        with self._lock:
            self.stats.files += nfiles
            self.stats.bytes += fbytes
            self.stats.last_path = path
        rec["children"] = children
        rec["fbytes"] = fbytes
        rec["groups"] = groups
        rec["gcounts"] = gcounts
        rec["nfiles"] = nfiles

    def _finalize(self):
        for path in reversed(list(self.folders.keys())):
            rec = self.folders[path]
            total = rec["fbytes"]
            nf = rec["nfiles"]
            groups = list(rec["groups"])
            gcounts = list(rec["gcounts"])
            for name, _sz, is_dir, _g, _fl in rec["children"]:
                if not is_dir:
                    continue
                crec = self.folders.get(os.path.join(path, name))
                if crec is None:
                    continue
                total += crec["size"]
                nf += crec["nfiles"]
                for i in range(len(groups)):
                    groups[i] += crec["groups"][i]
                    gcounts[i] += crec["gcounts"][i]
            rec["size"] = total
            rec["nfiles"] = nf
            rec["groups"] = groups
            rec["gcounts"] = gcounts
        # 扁平文件/文件夹索引（搜索框即时检索用）
        all_items = []
        for fpath, frec in self.folders.items():
            for name, sz, is_dir, g, flags in frec["children"]:
                all_items.append((os.path.join(fpath, name), name.lower(),
                                  sz, is_dir, g, flags))
        self.all_items = all_items
        root_rec = self.folders[self.root]
        self.stats.total = root_rec["size"]
        self.stats.total_files = root_rec["nfiles"]
        self.stats.total_dirs = len(self.folders)

    # ---- 对外 ----
    def scan(self):
        """同步扫描（应在后台线程调用）"""
        self.stats.start = time.time()
        self.stats.last_path = self.root
        self.folders[self.root] = self._new_record()
        self._pending = 1
        self._queue.put(self.root)
        workers = [threading.Thread(target=self._worker, daemon=True)
                   for _ in range(self.nthreads)]
        for w in workers:
            w.start()
        for w in workers:
            w.join()
        self._finalize()
        self.stats.end = time.time()

    def type_stats(self):
        """全扫描范围按类型分组统计: [(bytes, count), ...]"""
        ts = [[0, 0] for _ in TYPE_GROUPS]
        for ext, (b, c) in self.ext_stats.items():
            g = EXT_TO_GROUP.get(ext.lstrip("."), len(TYPE_GROUPS) - 1)
            ts[g][0] += b
            ts[g][1] += c
        return ts

    def folder_size(self, path):
        rec = self.folders.get(path)
        return rec["size"] if rec else 0

    def top_folders(self, n=300):
        """按文件夹大小排行（不含扫描根目录本身）"""
        items = [(rec["size"], path) for path, rec in self.folders.items()
                 if path != self.root]
        items.sort(key=lambda t: -t[0])
        out = []
        for size, path in items[:n]:
            rec = self.folders[path]
            out.append((size, path, os.path.basename(path) or path,
                        os.path.dirname(path), _dominant_of(rec), rec["nfiles"]))
        return out


# ---------------------------------------------------------------- 矩形树图布局
def _worst_ratio(total, mx, mn, side):
    """当前行在给定短边下的最差长宽比，越接近 1 越好。"""
    if total <= 0 or side <= 0 or mn <= 0:
        return float("inf")
    return max((side * side * mx) / (total * total),
               (total * total) / (side * side * mn))


def _dominant_of(rec):
    """目录内容占比最大的类型编号"""
    if rec is None:
        return len(TYPE_GROUPS) - 1
    gs = rec["groups"]
    m = max(gs)
    if m <= 0:
        return len(TYPE_GROUPS) - 1
    return gs.index(m)


def _blend(hexcolor, frac, target="#ffffff"):
    """把颜色往目标色混合（frac=0 原色，1 全目标色）。"""
    r = int(hexcolor[1:3], 16)
    g = int(hexcolor[3:5], 16)
    b = int(hexcolor[5:7], 16)
    tr, tg, tb = int(target[1:3], 16), int(target[3:5], 16), int(target[5:7], 16)
    r = int(r + (tr - r) * frac)
    g = int(g + (tg - g) * frac)
    b = int(b + (tb - b) * frac)
    return "#%02x%02x%02x" % (r, g, b)


# ============================================================ SpaceMap 树图
# v2.1.0 起，矩形树图换成 SpaceMap 引擎（Squarified 嵌套 + SpaceSniffer 视觉规格）。
# 原来的 flat_layout（单层平铺）已删除——它只铺一级、出图就是几条横带子。
#
# 视觉规格（对着原版 SpaceSniffer 截图逐像素反推出来的）：
#   · 面积严格正比字节数；squarify 让每块尽量方正
#   · 文件夹不画成实心块，而是画成"带标题带的地图框"，子项填充其内部，层层嵌套
#   · 每层四周内缩 1px，露出的父级底色就是网格线——那条线就是目录树
#   · 帧底色按深度走一条阶梯并在末位收敛（不循环），否则深层会变回一级色、满屏一个调
#   · 标题带高度固定 13px，粗体、左对齐距左 3px
#   · 叶子两行标签（名称 / 大小），矩形内水平+垂直居中，超宽直接截断不加省略号
# 界面缩放系数：由实际 DPI 决定（100% / 125% / 150% / 200%），App 启动时校准。
# 字体交给 Tk 的 scaling 处理，这里只管那些写死的像素尺寸。
UI_SCALE = 1.0

SM_HEADER_H = 13        # 帧标题带高度（原版实测每级都是 12~13px）
SM_PAD = 1.0            # 每层内缩：相邻两块之间露出 2px 父级底色
SM_MIN_FRAME_W = 54     # 帧小于此尺寸就不显示标题带
SM_MIN_FRAME_H = 30
SM_MIN_SPLIT = 8.0      # 小于此边长的矩形不再往下细分
SM_MIN_TILE = 1.2       # 小于此边长的块直接不画
SM_MAX_TILES = 4000     # 静态渲染的绘制预算（tkinter 画布项数上限）
SM_ANIM_TILES = 140      # 缩放动画中的低清预算（实测 140 时每帧约 70ms、只有 14 帧/秒，砍半提速）
SM_MAX_LABELS = 340      # 屏幕格子上最多标多少个字（Tk 的 create_text 约 0.5ms/个）
SM_ANIM_LABELS = 48      # 动画帧只标最大的这么多个，保住帧率
SM_MAX_CHILDREN = 220   # 单目录子项上限，超出部分合并为「其他 N 项」（防超宽目录卡顿）
TYPE_CHILD_MAX = 12     # 「类型分布」下钻到某一类型时，最多列几个构成项
TYPE_EXT_MAX = 10       # 「类型分布」下钻时，「按扩展名」最多列几个

# 帧底色阶梯：跟着 App 自身的深/浅主题走，保证与其它标签页同一套色感。
# 末位会一直沿用（收敛）。
#
# 【v2.1.2 起停用】树图配色已改回软件原本的「按内容占比最大的类型着色」
# （见 _folder_colors / TYPE_GROUPS），好和「类型分布」图例保持一致。
# 这套深度阶梯色保留在这里，想换回"层级配色"时把 _render_tree 里的 fill 换回来即可。
# 【树图配色】不跟底部的「按类型着色」图例走 —— 那套饱和色铺满整屏太吵。
# 改成：文件按类型取**低饱和**色，文件夹按**所在层级**取一条递进的底色阶梯
# （末位收敛不循环），不再细分的文件夹再把内容主类型色往本层底色里混一点。
# 这样层级一眼可辨，颜色又不抢戏。
# 【树图配色 · 帧底色】文件按类型上色，文件夹按**所在层级**换底色。
#
# 之前只用明度递进（每级差 7 左右），八层文件夹叠下来糊成一片 —— 就是截图里
# "miHoYo Launcher / games / Genshin Impact Game / ..." 那串分不清的楼梯。
# 现在改成**冷暖交替 + 明度递进**：0/2/4 层偏冷，1/3/5 层偏暖，相邻两层的
# 色相差足够一眼分开，明度仍然压在暗部，所以整体还是低饱和的夜色调。
SPACEMAP_FRAMES = {
    "dark":  ["#141a24", "#221d26", "#1b2531", "#2b2520", "#233040", "#332c23"],
    "light": ["#fbfcfe", "#f4eef4", "#ecf2fa", "#f6efe6", "#e2ebf8", "#efe6d8"],
}


def sm_frame_color(theme, depth):
    ladder = SPACEMAP_FRAMES.get(theme) or SPACEMAP_FRAMES["dark"]
    return ladder[min(depth, len(ladder) - 1)]


def sm_header_bg(theme, depth):
    """帧标题带的底色：比本层帧底色再亮/暗一点点，当成"标题栏"。
    这样每一层的"名字 + 内容"边界都是可见的，层数一眼能数出来。"""
    base = sm_frame_color(theme, depth)
    return _blend(base, 0.10, "#ffffff") if theme == "dark" else _blend(base, 0.06, "#000000")
# 下标同 TYPE_GROUPS：0 视频 1 音频 2 图片 3 文档 4 压缩包 5 应用安装 6 系统程序 7 游戏资源 8 其他
# 统一明度 55~62%、饱和度 50~62%，色相均匀拉开；「系统程序」「其他」是最大的两类，
# 做成低饱和中性色不抢眼，彩色的类型才跳得出来。深色主题是同一组色的压暗版。
SPACEMAP_FILES = {
    "dark":  ["#AD5359", "#7E5EAD", "#3B895D", "#3D70A7", "#A9933D", "#AF7131",
              "#626C7A", "#318B86", "#6F697D"],
    "light": ["#DE6B72", "#A178DE", "#4CB077", "#4E8FD6", "#D9BC4E", "#E0913F",
              "#7E8B9C", "#3FB2AC", "#8E86A0"],
}
# 「类型分布」下钻后列的是"子项"（不是类型），用这套同风格的分类色轮着上
SPACEMAP_CAT = {
    "dark":  ["#AD5359", "#3B895D", "#3D70A7", "#A9933D", "#7E5EAD", "#318B86",
              "#AF7131", "#6F697D", "#A55F7D", "#70884A", "#9D7D53", "#63839D"],
    "light": ["#DE6B72", "#4CB077", "#4E8FD6", "#D9BC4E", "#A178DE", "#3FB2AC",
              "#E0913F", "#8E86A0", "#D97AA6", "#8FAE5F", "#C9A06B", "#7FA8C9"],
}


def sm_frame_edge(theme, depth):
    """顶层帧的描边色：比本层底色亮一档，让一级目录互相分开。"""
    base = sm_frame_color(theme, depth)
    return _blend(base, 0.45, "#ffffff") if theme == "dark" else _blend(base, 0.35, "#000000")


def sm_cat_color(theme, i):
    palette = SPACEMAP_CAT.get(theme) or SPACEMAP_CAT["dark"]
    return palette[i % len(palette)]
SPACEMAP_LABEL = {"dark": "#dce3ec", "light": "#2b3542"}
SPACEMAP_HEADER = {"dark": "#f2f6fa", "light": "#18202b"}


def sm_file_color(theme, g):
    palette = SPACEMAP_FILES.get(theme) or SPACEMAP_FILES["dark"]
    return palette[g] if 0 <= g < len(palette) else palette[-1]


def sm_leaf_folder_color(theme, gd, depth):
    """没有再往下细分的文件夹：内容主类型色往本层帧底色里混。

    直接铺帧底色就是一块没信息量的苍白方块，和文件块也难分；
    混一点主类型色之后既看得出里面主要是什么，又明显区别于实心的文件块。
    """
    base = sm_file_color(theme, gd)
    target = sm_frame_color(theme, depth)
    return _blend(base, 0.55 if theme == "light" else 0.42, target)


def squarify(ids, sizes, x, y, w, h):
    """Squarified Treemap（Bruls / Huizing / van Wijk, 2000）。

    返回 [(id, (x, y, w, h)), ...]，面积严格正比 sizes，块尽量方正。

    关键点：贪心扩行时，只要「再加一块会让最差长宽比变坏」就收行。
    旧实现用的是「长宽比不超过 2.5 就继续塞」，那不是 squarified，
    结果是每行被塞到接近 2.5 的极端长宽比，出图就是一条条横带子。
    """
    pairs = [(i, s) for i, s in zip(ids, sizes) if s > 0]
    if not pairs or w <= 0 or h <= 0:
        return []
    pairs.sort(key=lambda p: -p[1])
    total = sum(s for _, s in pairs)
    if total <= 0:
        return []
    scale = (w * h) / total
    areas = [s * scale for _, s in pairs]

    out = []
    rx, ry, rw, rh = float(x), float(y), float(w), float(h)
    i, n = 0, len(areas)
    while i < n and rw > 1e-9 and rh > 1e-9:
        side = min(rw, rh)
        s = mx = 0.0
        mn = float("inf")
        best = float("inf")
        j = i
        while j < n:
            a = areas[j]
            ns = s + a
            nmx = a if a > mx else mx
            nmn = a if a < mn else mn
            ratio = _worst_ratio(ns, nmx, nmn, side)
            if j > i and ratio > best:
                break
            s, mx, mn, best = ns, nmx, nmn, ratio
            j += 1
        if rw >= rh:
            strip = s / rh if rh > 0 else 0.0
            oy = ry
            for k in range(i, j):
                hh = areas[k] / strip if strip > 0 else 0.0
                out.append((pairs[k][0], (rx, oy, strip, hh)))
                oy += hh
            rx += strip
            rw -= strip
        else:
            strip = s / rw if rw > 0 else 0.0
            ox = rx
            for k in range(i, j):
                ww = areas[k] / strip if strip > 0 else 0.0
                out.append((pairs[k][0], (ox, ry, ww, strip)))
                ox += ww
            ry += strip
            rh -= strip
        i = j
    return out


def nested_layout(folders, focus, x, y, w, h, budget=None):
    """SpaceSniffer 式递归布局。

    文件夹不再是一块实心方块，而是"带标题带的地图框"：框内继续切分子项，
    子项里还是文件夹的就再往下切，整屏一眼看全目录层级。

    返回 (path, name, size, is_dir, gd, flags, (x,y,w,h), depth, is_container) 列表。
    **列表顺序即绘制顺序**（父在前、子在后），所以命中测试从后往前扫就能拿到最深的那块。
    is_container=True 表示这是文件夹的地图框，框内还会被更深的块填充。
    """
    if budget is None:
        budget = [SM_MAX_TILES]
    out = []

    def children_of(path):
        rec = folders.get(path)
        if rec is None:
            return []
        items = []
        for name, sz, is_dir, g, flags in rec["children"]:
            cpath = os.path.join(path, name)
            crec = folders.get(cpath) if is_dir else None
            size = crec["size"] if crec else (sz if not is_dir else 0)
            if size > 0:
                items.append((cpath, name, size, is_dir, g, flags))
        if len(items) > SM_MAX_CHILDREN:
            # 超宽目录（node_modules 那种）：只铺最大的若干项，其余合并成一块，
            # 既不出碎条也不让 squarify 在几万个子项上耗时
            items.sort(key=lambda t: -t[2])
            rest = items[SM_MAX_CHILDREN - 1:]
            label = "其他 %d 项" % len(rest)
            items = items[:SM_MAX_CHILDREN - 1]
            items.append((os.path.join(path, label), label, sum(t[2] for t in rest),
                          False, len(TYPE_GROUPS) - 1, MERGED_FLAG))
        return items

    root_rec = folders.get(focus)
    if root_rec is None:
        return out
    box = (float(x), float(y), float(w), float(h))
    rootname = os.path.basename(focus.rstrip("\\/")) or focus
    out.append((focus, rootname, root_rec["size"], True, _dominant_of(root_rec), 0, box, 0, True))

    # 按"当前面积"从大到小展开（最大堆）。
    #
    # 之前是广度优先：整层整层地花预算，结果小分支把预算吃光，屏幕上面积最大的
    # 分支反而没来得及细分，留下一大片平的色块。按面积优先则预算永远花在眼睛
    # 真正看得到的地方。
    #
    # 注意绘制顺序依然合法：子块只有在父块被弹出时才生成，所以任何后代一定排在
    # 它的祖先之后 —— _hit 从后往前扫仍然能拿到最深的块。
    import heapq

    filled = set()
    seq = 0
    heap = [(-(box[2] * box[3]), seq, focus, box, 0)]
    while heap and budget[0] > 0:
        _neg, _s, path, rect, depth = heapq.heappop(heap)
        if budget[0] <= 0:
            break
        rx, ry, rw, rh = rect
        if rw < SM_MIN_TILE or rh < SM_MIN_TILE:
            continue
        items = children_of(path)
        if not items:
            continue
        header = SM_HEADER_H if (rw >= SM_MIN_FRAME_W and rh >= SM_MIN_FRAME_H) else 0
        inner = (rx + SM_PAD, ry + header, rw - SM_PAD * 2, rh - header - SM_PAD)
        if inner[2] <= 1 or inner[3] <= 1:
            continue
        placed = squarify(list(range(len(items))), [t[2] for t in items], *inner)
        for idx, r in placed:
            cw, chh = r[2], r[3]
            if cw < SM_MIN_TILE or chh < SM_MIN_TILE:
                continue
            budget[0] -= 1
            cpath, name, size, is_dir, g, flags = items[idx]
            gd = _dominant_of(folders.get(cpath)) if is_dir else g
            recurse = (is_dir and not (flags & MERGED_FLAG)
                       and cw >= SM_MIN_SPLIT and chh >= SM_MIN_SPLIT)
            out.append((cpath, name, size, is_dir, gd, flags, r, depth + 1, recurse))
            if recurse:
                seq += 1
                heapq.heappush(heap, (-(cw * chh), seq, cpath, r, depth + 1))
            filled.add(path)

    # 预算耗尽时，有些被标成"容器"的帧其实一个子块都没画进去。这种帧会变成
    # 一块没有任何信息的白板，所以降级成"叶子文件夹"——渲染时改用内容主类型色填充。
    return [(p, n, s, d, g, f, r, dp, (ic and p in filled))
            for (p, n, s, d, g, f, r, dp, ic) in out]


# ---------------------------------------------------------------- 简约滚动条
class MiniScrollbar(tk.Canvas):
    """胶囊形细滚动条：无箭头无防滑纹，滑块头尾全圆，悬停变粗变亮；
    整个条带都是点击/拖动热区（不只是滑块本身）。"""

    CANVAS_W = 15       # 固定画布宽（点击热区），与右边框留间隔由 pack padx 控制
    THUMB_W = 6         # 滑块视觉宽
    THUMB_W_HOVER = 10
    MIN_LEN = 28
    MAX_LEN = 88

    def __init__(self, master, command=None, **kw):
        super().__init__(master, width=self.CANVAS_W, highlightthickness=0, bd=0,
                         takefocus=0, **kw)
        self.cmd = command
        self.first, self.last = 0.0, 1.0
        self._bg = "#ffffff"
        self._thumb = "#c3cad6"
        self._hover_c = "#9aa6b8"
        self._drag_off = None
        self._hovering = False
        self._tw = self.THUMB_W
        self._wid_job = None
        self._thumb_id = self.create_polygon(0, 0, 0, 0, fill=self._thumb,
                                             outline="", smooth=True, state="hidden")
        self.bind("<Button-1>", self._on_press)
        self.bind("<B1-Motion>", self._on_drag)
        self.bind("<ButtonRelease-1>", self._on_release)
        self.bind("<Motion>", self._on_motion)
        self.bind("<Leave>", self._on_leave)
        self.bind("<Configure>", lambda e: self._draw())

    def set_colors(self, bg, thumb, hover):
        self._bg, self._thumb, self._hover_c = bg, thumb, hover
        self.configure(bg=bg)
        self._draw()

    def set(self, first, last):
        try:
            self.first, self.last = float(first), float(last)
        except (TypeError, ValueError):
            return
        self._draw()

    def _thumb_rect(self):
        w = self.CANVAS_W
        h = self.winfo_height()
        if h <= 1 or self.last - self.first >= 0.999:
            return None
        th = max(self.MIN_LEN, min(self.MAX_LEN, (self.last - self.first) * h))
        y0 = self.first * h
        y1 = min(y0 + th, h)
        x1 = (w - self._tw) / 2.0
        return (x1, y0, x1 + self._tw, y1, self._tw / 2.0)

    def _draw(self):
        r = self._thumb_rect()
        if r is None:
            self.itemconfigure(self._thumb_id, state="hidden")
            return
        x1, y1, x2, y2, rad = r
        col = self._hover_c if self._hovering else self._thumb
        self.itemconfigure(self._thumb_id, state="normal", fill=col)
        self.coords(self._thumb_id, *round_rect_points(x1, y1, x2, y2, rad))

    def _thumb_h(self, h):
        """当前滑块的实际像素高度（受 MIN/MAX_LEN 截断）。"""
        size = max(self.last - self.first, 0.02)
        return max(self.MIN_LEN, min(self.MAX_LEN, size * h))

    def _moveto_y(self, y):
        """点击轨道空白处：让滑块中心对准 y。用实际(截断后)的滑块高度居中。"""
        h = max(self.winfo_height(), 1)
        th = self._thumb_h(h)
        frac = max(0.0, min(1.0 - th / h, y / h - th / h / 2.0))
        if self.cmd:
            self.cmd("moveto", frac)

    def _drag_to_y(self, y_top):
        """拖动滑块：让滑块顶边对准 y_top（保持按下时的偏移）。"""
        h = max(self.winfo_height(), 1)
        th = self._thumb_h(h)
        frac = max(0.0, min(1.0 - th / h, y_top / h))
        if self.cmd:
            self.cmd("moveto", frac)

    def _band(self, y):
        """y 是否落在滑块所在的水平条带（x 不限制，整条宽度都是热区）"""
        r = self._thumb_rect()
        return bool(r and r[1] - 6 <= y <= r[3] + 6)

    def _on_press(self, e):
        r = self._thumb_rect()
        if r and self._band(e.y):
            self._drag_off = e.y - r[1]
        else:
            self._drag_off = 0
            self._moveto_y(e.y)
        self._hovering = True
        self._animate_w(self.THUMB_W_HOVER)

    def _on_drag(self, e):
        if self._drag_off is None:
            return
        # 拖动时保持按下点相对滑块顶边的位置，不再做居中
        self._drag_to_y(e.y - self._drag_off)

    def _on_release(self, e):
        self._drag_off = None
        self._on_motion(e)

    def _on_motion(self, e):
        hov = self._band(e.y) or self._drag_off is not None
        if hov != self._hovering:
            self._hovering = hov
            self._animate_w(self.THUMB_W_HOVER if hov else self.THUMB_W)
        self.configure(cursor="sb_v_double_arrow" if hov else "")
        self._draw()

    def _on_leave(self, _e):
        if self._drag_off is None and self._hovering:
            self._hovering = False
            self._animate_w(self.THUMB_W)
        self.configure(cursor="")
        self._draw()

    def _animate_w(self, target):
        if self._wid_job:
            self.after_cancel(self._wid_job)
            self._wid_job = None
        if self._tw == target:
            return

        def f():
            if self._tw == target:
                self._wid_job = None
                return
            self._tw += 1 if target > self._tw else -1
            self._draw()
            self._wid_job = self.after(10, f)
        f()


# ---------------------------------------------------------------- 图形界面
# ---------------------------------------------------------------- 图形界面
def _enable_dpi_awareness():
    try:
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass


class App(tk.Tk):
    def __init__(self):
        _enable_dpi_awareness()
        super().__init__()
        self._apply_dpi_scaling()
        self.title(APP_TITLE + "  v" + APP_VERSION + "    © wanghx")
        # 初始窗口跟着屏幕走：树图越宽越好看，所以尽量铺开，但留一圈桌面边距好拖动
        w, h = self._initial_geometry()
        self.geometry("%dx%d" % (w, h))
        self.after(100, self._center_window)
        self.minsize(960, 620)

        self.scanner = None
        self.scan_thread = None
        self._scan_active = False   # 以 Scanner 状态为准的"正在扫描"标记
        self._sync_pending = False
        self.result = None
        # 本地设置（性能模式 / 树图配色 / 主题模式）—— 必须赶在读主题之前就绪
        self.settings = load_settings()
        self.perf_mode = self.settings.get("perf_mode", "fast")          # lite / fast
        self.tree_color_mode = self.settings.get("tree_color", "depth")  # depth / type
        self.tree_anim = self.settings.get("tree_anim", "smooth")       # smooth / fast / off
        self._anim_ms = 220
        self._anim_t0 = None
        self.theme = self._load_theme()
        self.current_path = None
        self.target = ""
        self._draw_items = []   # 树图当前帧所有方块: (path,name,size,is_dir,gd,flags,lrect,crect,depth,is_container)
        self._selected_path = None
        self._child_map = {}    # child_tree iid -> (name, is_dir, flags)
        self._world = None      # 树图世界坐标 (wx,wy,ww,wh)，rest 时 = (0,0,cw,ch)
        self._animating = False
        self._big_mode = tk.StringVar(value="file")
        self._big_map = {}        # big_tree iid -> (path, is_dir)
        # 文件夹排行榜标签页
        self.rank_path = None         # 排行榜当前所在目录（独立于树图导航）
        self.rank_rows = []           # 命中/动画用的行数据
        self.rank_anim_after = None
        self.rank_animating = False
        self.rank_hover = -1
        self.rank_resize_after = None
        self._cache = OrderedDict()   # 目标路径 -> Scanner（避免重复扫描）
        self._cache_ts = {}           # 目标路径 -> 扫描时间字符串
        self.tooltip = None
        self._closed = False

        self._style()
        self._build_ui()
        self._load_drives()
        # 启动就让它在后台把当前目标预扫一遍（2 线程），用户点「开始扫描」时往往已经有结果了
        self.after(700, self._prequest)
        self.after(1500, self._poll_system_theme)   # 跟随系统模式：定时校对
        self.after(1100, self._maybe_welcome)       # 首次运行：欢迎 + 上手教程
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.after(120, self._poll_scan)
        self.after(150, lambda: self._set_dark_titlebar(self.theme == "dark"))

    # ---------------- 界面构建 ----------------
    def _style(self):
        st = ttk.Style(self)
        try:
            st.theme_use("clam")
        except tk.TclError:
            pass
        st.configure(".", font=("Microsoft YaHei UI", 9))
        st.configure("TButton", padding=4)
        st.configure("Treeview", rowheight=23, font=("Microsoft YaHei UI", 9))
        st.configure("Treeview.Heading", font=("Microsoft YaHei UI", 9, "bold"))

    # ---------------- 主题 ----------------
    @staticmethod
    def _system_is_dark():
        """读注册表判断 Windows 当前是深色还是浅色（读不到就当浅色）。"""
        try:
            import winreg
            k = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                               r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize")
            v, _ = winreg.QueryValueEx(k, "AppsUseLightTheme")
            winreg.CloseKey(k)
            return int(v) == 0
        except Exception:
            return False

    def _load_theme(self):
        """主题模式：light / dark / system。老版本存在 theme.txt，新版本存在 settings.json。"""
        mode = self.settings.get("theme_mode")
        if mode not in ("light", "dark", "system"):
            try:
                with open(os.path.join(CONFIG_DIR, "theme.txt"), "r", encoding="utf-8") as f:
                    t = f.read().strip()
                mode = t if t in ("light", "dark") else "system"
            except OSError:
                mode = "system"
        self.theme_mode = mode
        if mode == "system":
            return "dark" if self._system_is_dark() else "light"
        return mode

    def _save_theme(self):
        self.settings["theme_mode"] = self.theme_mode
        save_settings(self.settings)

    def _set_theme_mode(self, mode, announce=True):
        self.theme_mode = mode
        self.theme = ("dark" if self._system_is_dark() else "light") if mode == "system" else mode
        self._save_theme()
        self._apply_theme()
        self._repaint_all()
        self._set_dark_titlebar(self.theme == "dark")
        self._update_theme_button()
        if announce:
            name = {"light": "浅色", "dark": "深色", "system": "跟随系统"}[mode]
            extra = "（系统当前是%s）" % ("深色" if self.theme == "dark" else "浅色") \
                if mode == "system" else ""
            self.lbl_status.config(text="主题已切换为 %s%s" % (name, extra))

    def _update_theme_button(self):
        """按钮只显示「点一下会切成什么」，点了直接切；跟随系统在「设置」里调。

        顺带把所有圆角按钮和"安全保护"标签的颜色刷新一遍（_apply_theme 结尾会调到这里）。
        """
        p = self.t
        for _b in list(getattr(self, "_round_buttons", [])):
            try:
                _outer = p[getattr(_b, "_outer_key", "app")]
                if getattr(_b, "_role", "normal") == "primary":
                    _b.set_colors(_outer, "#2d6cdf", "#ffffff", "#3b7bf0")
                else:
                    _b.set_colors(_outer, p["tab_bg"], p["text"], p["hover"])
            except tk.TclError:
                self._round_buttons.remove(_b)      # 对话框里的按钮已被销毁
        if getattr(self, "lbl_safe", None) is not None:
            self.lbl_safe.configure(background=p["app"], foreground="#3fbf7f")
        # 嵌入的 SpaceMap 是独立进程，主题靠它的 settings.json；改了要重启才会套用
        if getattr(self, "sm_host", None) is not None:
            self.sm_host.configure(bg=p["canvas"])
            if getattr(self, "_sm_hwnd", 0):
                # 只写 settings.json，不重启 —— 重启会明显闪一下。
                # 新配色在下次启动 SpaceMap 时生效（切走再切回来会重启进程）
                self._spacemap_set_theme()
        if getattr(self, "btn_theme", None) is not None:
            self.btn_theme.config(text="浅色模式" if self.theme == "dark" else "深色模式")

    def _toggle_theme(self):
        """直接切深浅，不参与循环（跟随系统交给设置）"""
        self._set_theme_mode("light" if self.theme == "dark" else "dark")

    def _poll_system_theme(self):
        """跟随系统模式下，系统换深色时自动跟上（3 秒查一次注册表，开销可忽略）。"""
        if self._closed:
            return
        if getattr(self, "theme_mode", "light") == "system":
            want = "dark" if self._system_is_dark() else "light"
            if want != self.theme:
                self._set_theme_mode("system", announce=False)
        self.after(3000, self._poll_system_theme)

    def _update_prescan_label(self):
        """右上角显示后台预扫描进度：还有几个盘没就绪，一眼看到。"""
        lbl = getattr(self, "lbl_prescan", None)
        if lbl is None:
            return
        if self.perf_mode == "lite":
            lbl.config(text="省内存模式 · 只缓存当前盘")
            return
        total = getattr(self, "_prescan_total", 0)
        if not total:
            lbl.config(text="")
            return
        done = getattr(self, "_prescan_done", 0)
        thr = getattr(self, "_prescan_thread", None)
        if done >= total or (thr is not None and not thr.is_alive()):
            lbl.config(text="预扫描就绪 %d/%d · 所有磁盘均可直接切换" % (done, total))
        else:
            lbl.config(text="后台预扫描中 %d/%d …" % (done, total))

    def _maybe_welcome(self):
        """首次运行弹一次「欢迎 + 上手教程」，之后就只在「关于」里能翻到。"""
        if self.settings.get("welcomed"):
            return
        self.settings["welcomed"] = True
        save_settings(self.settings)
        self._show_welcome()

    def _show_welcome(self):
        dlg = tk.Toplevel(self)
        dlg.title("欢迎使用")
        dlg.transient(self)
        dlg.resizable(False, False)
        p = self.t
        dlg.configure(bg=p["app"])
        dlg.update_idletasks()
        w, h = 560, 480
        x = self.winfo_rootx() + (self.winfo_width() - w) // 2
        y = self.winfo_rooty() + (self.winfo_height() - h) // 2
        dlg.geometry("%dx%d+%d+%d" % (w, h, x, y))

        ttk.Label(dlg, text="感谢支持！", font=("Microsoft YaHei UI", 16, "bold"),
                  background=p["app"], foreground=p["text"]).pack(padx=22, pady=(20, 2), anchor="w")
        ttk.Label(dlg,
                  text="空间透镜  v%s      © wanghx\n"
                       "完全本地运行 · 不联网 · 不上传任何数据" % APP_VERSION,
                  background=p["app"], foreground=p["muted"],
                  font=("Microsoft YaHei UI", 9), justify="left").pack(padx=22, anchor="w")

        body = tk.Frame(dlg, bg=p["app"])
        body.pack(fill="both", expand=True, padx=22, pady=14)
        tips = [
            ("1", "选目标就能开工",
             "顶部选盘符，或点「选择文件夹…」。打开软件后会自动开始扫描当前盘，"
             "同时后台会预扫描其余磁盘，完成后切换磁盘无需等待。"),
            ("2", "四个页签随便逛",
             "文件夹排行（默认首页）· 类型分布 · 大文件/大目录排行 · 文件夹树图。"
             "树图里双击方块进入下一层、双击空白返回上级。"),
            ("3", "可以切换深色模式",
             "默认就是「跟随系统」——你在 Windows 里换深色，软件会自己跟着变。"
             "想固定住，就点右上角的「深色模式 / 浅色模式」按钮直接切；"
             "也可以在「设置 → 深色模式」里三选一。"),
            ("4", "设置与关于",
             "「设置」里能选性能模式（流畅＝预扫所有盘 / 省内存＝只缓存当前盘）和树图配色；"
             "「关于」里有从 v1.0 到现在的完整更新日志。"),
        ]
        for no, title, desc in tips:
            row = tk.Frame(body, bg=p["app"])
            row.pack(fill="x", pady=(0, 10))
            tk.Label(row, text=no, bg="#2d6cdf", fg="#ffffff", width=2, height=1,
                     font=("Microsoft YaHei UI", 10, "bold")).pack(side="left", anchor="n", pady=2)
            col = tk.Frame(row, bg=p["app"])
            col.pack(side="left", fill="x", expand=True, padx=(10, 0))
            tk.Label(col, text=title, bg=p["app"], fg=p["text"], anchor="w",
                     font=("Microsoft YaHei UI", 10, "bold")).pack(anchor="w")
            tk.Label(col, text=desc, bg=p["app"], fg=p["rsub"], anchor="w",
                     justify="left", wraplength=440,
                     font=("Microsoft YaHei UI", 9)).pack(anchor="w")

        btns = ttk.Frame(dlg)
        btns.pack(pady=(0, 16))
        self._mkbtn(btns, "开始使用", dlg.destroy, bg="#2d6cdf", fg="#ffffff").pack(side="left", padx=6)
        self._mkbtn(btns, "查看更新日志",
                    lambda: (dlg.destroy(), self._show_about())).pack(side="left", padx=6)
        dlg.bind("<Escape>", lambda e: dlg.destroy())
        try:
            import ctypes
            user32 = ctypes.windll.user32
            dhwnd = user32.GetAncestor(dlg.winfo_id(), 2)
            val = ctypes.c_int(1 if self.theme == "dark" else 0)
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                dhwnd, 20, ctypes.byref(val), ctypes.sizeof(val))
        except Exception:
            pass
        dlg.grab_set()
        dlg.focus_set()

    def _show_settings(self):
        """设置：性能模式 + 树图配色，改完立即生效并记住。"""
        dlg = tk.Toplevel(self)
        dlg.title("设置")
        dlg.transient(self)
        dlg.resizable(False, False)
        p = self.t
        dlg.configure(bg=p["app"])
        dlg.update_idletasks()
        w, h = 500, 560
        x = self.winfo_rootx() + (self.winfo_width() - w) // 2
        y = self.winfo_rooty() + (self.winfo_height() - h) // 2
        dlg.geometry("%dx%d+%d+%d" % (w, h, x, y))

        ttk.Label(dlg, text="设置", font=("Microsoft YaHei UI", 13, "bold"),
                  background=p["app"], foreground=p["text"]).pack(padx=20, pady=(16, 8), anchor="w")

        v_perf = tk.StringVar(value=self.perf_mode)
        v_tree = tk.StringVar(value=self.tree_color_mode)

        f1 = ttk.LabelFrame(dlg, text=" 性能模式 ", padding=10)
        f1.pack(fill="x", padx=16, pady=(0, 10))
        ttk.Radiobutton(f1, text="流畅（推荐）· 启动后预扫描所有磁盘，切换时无需等待；内存占用较高",
                        variable=v_perf, value="fast").pack(anchor="w")
        ttk.Radiobutton(f1, text="省内存 · 只缓存当前盘、不预扫其余盘；切盘需要现场扫描",
                        variable=v_perf, value="lite").pack(anchor="w", pady=(6, 0))

        f2 = ttk.LabelFrame(dlg, text=" 树图配色 ", padding=10)
        f2.pack(fill="x", padx=16, pady=(0, 10))
        ttk.Radiobutton(f2, text="按层级（推荐）· 底色逐层递进，层级清晰可辨",
                        variable=v_tree, value="depth").pack(anchor="w")
        ttk.Radiobutton(f2, text="按文件类型 · 和「类型分布」「圆环图」用同一套色",
                        variable=v_tree, value="type").pack(anchor="w", pady=(6, 0))

        v_anim = tk.StringVar(value=getattr(self, "tree_anim", "smooth"))
        f4 = ttk.LabelFrame(dlg, text=" 树图动画 ", padding=10)
        f4.pack(fill="x", padx=16, pady=(0, 10))
        row4 = ttk.Frame(f4)
        row4.pack(anchor="w")
        for _lbl, _val in (("跟随 SpaceMap 节奏", "smooth"), ("快速", "fast"), ("关闭", "off")):
            ttk.Radiobutton(row4, text=_lbl, variable=v_anim, value=_val).pack(side="left", padx=(0, 14))
        ttk.Label(f4, text="动画卡顿的话选「关闭」，双击直接跳转不做过渡",
                  foreground=p["muted"], font=("Microsoft YaHei UI", 8)).pack(anchor="w", pady=(4, 0))

        v_theme = tk.StringVar(value=self.theme_mode)
        f3 = ttk.LabelFrame(dlg, text=" 深色模式 ", padding=10)
        f3.pack(fill="x", padx=16, pady=(0, 10))
        row = ttk.Frame(f3)
        row.pack(anchor="w")
        ttk.Radiobutton(row, text="跟随系统", variable=v_theme, value="system").pack(side="left")
        ttk.Radiobutton(row, text="浅色", variable=v_theme, value="light").pack(side="left", padx=(14, 0))
        ttk.Radiobutton(row, text="深色", variable=v_theme, value="dark").pack(side="left", padx=(14, 0))
        ttk.Label(f3, text="选「跟随系统」后会跟着 Windows 的深浅色自动切换",
                  foreground=p["muted"], font=("Microsoft YaHei UI", 8)).pack(anchor="w", pady=(4, 0))

        def apply_now(*_a):
            self.perf_mode = v_perf.get()
            self.tree_color_mode = v_tree.get()
            self.settings["perf_mode"] = self.perf_mode
            self.settings["tree_color"] = self.tree_color_mode
            save_settings(self.settings)
            while len(self._cache) > self.cache_max:      # 切到省内存立即瘦身
                old = next(iter(self._cache))
                del self._cache[old]
                self._cache_ts.pop(old, None)
            self._update_prescan_label()
            self._render_tree()

        v_perf.trace_add("write", apply_now)
        v_tree.trace_add("write", apply_now)

        def apply_theme_now(*_a):
            self.settings["tree_color"] = self.tree_color_mode
            self._set_theme_mode(v_theme.get())

        v_theme.trace_add("write", apply_theme_now)

        def apply_anim_now(*_a):
            self.tree_anim = v_anim.get()
            self.settings["tree_anim"] = self.tree_anim
            save_settings(self.settings)

        v_anim.trace_add("write", apply_anim_now)

        # 只显示环境变量写法，不要把用户自己的绝对路径（含用户名）显示出来
        ttk.Label(dlg, text="改完立即生效并记住，存在：\n%LOCALAPPDATA%\\DiskSurfaceScan\\settings.json",
                  background=p["app"], foreground=p["muted"],
                  font=("Microsoft YaHei UI", 8), justify="left").pack(padx=20, anchor="w")
        self._mkbtn(dlg, "关闭", dlg.destroy).pack(pady=12)
        dlg.bind("<Escape>", lambda e: dlg.destroy())
        try:
            import ctypes
            user32 = ctypes.windll.user32
            dhwnd = user32.GetAncestor(dlg.winfo_id(), 2)
            val = ctypes.c_int(1 if self.theme == "dark" else 0)
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                dhwnd, 20, ctypes.byref(val), ctypes.sizeof(val))
        except Exception:
            pass
        dlg.grab_set()
        dlg.focus_set()

    def _show_about(self):
        """关于：作者署名 + 从 v1.0 到现在的简短更新日志。"""
        dlg = tk.Toplevel(self)
        dlg.title("关于")
        dlg.transient(self)
        dlg.resizable(False, False)
        p = self.t
        dlg.configure(bg=p["app"])
        # 居中到主窗口
        dlg.update_idletasks()
        w, h = 520, 460
        x = self.winfo_rootx() + (self.winfo_width() - w) // 2
        y = self.winfo_rooty() + (self.winfo_height() - h) // 2
        dlg.geometry("%dx%d+%d+%d" % (w, h, x, y))

        ttk.Label(dlg, text=APP_TITLE, font=("Microsoft YaHei UI", 14, "bold"),
                  background=p["app"], foreground=p["text"]).pack(padx=20, pady=(18, 2), anchor="w")
        ttk.Label(dlg, text="版本 v" + APP_VERSION + "    版权 © wanghx    本地运行 · 不上传任何数据",
                  background=p["app"], foreground=p["muted"]).pack(padx=20, anchor="w")
        ttk.Label(dlg, text="感谢支持！有问题或建议欢迎继续提。",
                  background=p["app"], foreground=p["muted"],
                  font=("Microsoft YaHei UI", 9)).pack(padx=20, pady=(2, 0), anchor="w")
        ttk.Label(dlg, text="联系邮箱：whx206916@outlook.com",
                  background=p["app"], foreground=p["muted"],
                  font=("Microsoft YaHei UI", 9)).pack(padx=20, anchor="w")

        box = tk.Frame(dlg, bg=p["app"])
        box.pack(fill="both", expand=True, padx=16, pady=10)
        txt = tk.Text(box, wrap="word", bg=p["tv_bg"], fg=p["text"],
                     relief="flat", bd=0, font=("Microsoft YaHei UI", 10),
                     padx=12, pady=10, highlightthickness=0)
        sb = MiniScrollbar(box, command=txt.yview)
        sb.pack(side="right", fill="y")
        txt.pack(side="left", fill="both", expand=True)
        sb.set_colors(p["tv_bg"], "#9aa6b8", "#66717f")
        txt.configure(yscrollcommand=sb.set)

        # 更新日志按「级别」分区：里程碑 / 功能迭代 / 修复优化
        # 每项是 (类型, 版本, 说明)；类型 sec 是分区标题
        log = [
            ("sec", "", "", "■ 重大更新 · 里程碑"),
            ("major", "09-23", "v2.1.0", "树图换成 SpaceMap 引擎：真正的 squarified 递归嵌套"),
            ("major", "09-22", "v2.0.0", "树图重写为 SpaceSniffer 式递归嵌套"),
            ("major", "早期", "v1.4.0", "新增文件夹排行横条榜"),
            ("major", "早期", "v1.3.0", "树图改单层方块拼图，小项合并为「其他 N 项」"),
            ("major", "早期", "v1.1.0", "新增扇形图与类型分布；隐藏/系统文件标记"),
            ("major", "早期", "v1.0.0", "首发：多线程扫描、树图、类型分布、大文件排行"),

            ("feat", "09-24", "v2.22.0", "搜索：输入框加大、加可点击的「搜索」按钮、范围扩到全电脑所有盘（用各盘的落盘缓存）"),
            ("feat", "09-25", "v2.23.0", "改名为「空间透镜 · SpaceLens」（标题栏 / 关于 / 欢迎页 / 预览图水印）"),
            ("sec", "", "", "■ 功能新增 · 体验迭代"),
            ("feat", "09-24", "v2.20.0", "清理建议加「一键清理」（只清清「放心清理」那一档）"),
            ("feat", "09-24", "v2.19.0", "扫描结果落盘缓存 7 天，重开软件不用重扫"),
            ("feat", "09-24", "v2.18.0", "SpaceMap 跟随软件的扫描目标"),
            ("feat", "09-24", "v2.17.0", "SpaceMap 打进 exe，分享一个文件对方也能用"),
            ("feat", "09-24", "v2.16.0", "嵌入窗口去掉标题栏与黑边；预热提前到开机"),
            ("feat", "09-24", "v2.15.0", "嵌入窗口贴边；默认窗口放大 10%；适配浅色"),
            ("feat", "09-24", "v2.14.0", "新增「SpaceMap 树图」标签页（直接嵌入它的窗口）"),
            ("feat", "09-24", "v2.13.0", "缩放动画期间也给大格子标字"),
            ("feat", "09-24", "v2.12.0", "动画做布局缓存，帧率 15 → 40+"),
            ("feat", "09-24", "v2.11.0", "动画改按真实时间驱动；设置里可调三档"),
            ("feat", "09-24", "v2.9.0", "新增软件占用分析；清理建议并入该页"),
            ("feat", "09-23", "v2.8.0", "新增「软件占用」标签页（读注册表 + 软件图标）"),
            ("feat", "09-23", "v2.7.0", "新增「清理建议」标签页（21 处常见可清理位置）"),
            ("feat", "09-23", "v2.6.1", "重配类型分布色板，九类色相拉开"),
            ("feat", "09-23", "v2.6.0", "适配 150% / 200% 分辨率缩放"),
            ("feat", "09-23", "v2.5.2", "深色模式默认改为跟随系统"),
            ("feat", "09-23", "v2.5.0", "按钮改圆角胶囊；加「安全保护」说明"),
            ("feat", "09-23", "v2.4.0", "深色模式可跟随系统；首次运行欢迎教程"),
            ("feat", "09-23", "v2.3.0", "新增「设置」：性能模式 / 树图配色 / 预扫进度"),
            ("feat", "09-23", "v2.2.0", "「关于」日志按级别分区；署名改为 wanghx"),
            ("feat", "09-23", "v2.1.9", "打开软件自动扫描 + 后台逐盘预扫"),
            ("feat", "09-23", "v2.1.8", "横条长度改按占比；圆环自绘消除锯齿"),
            ("feat", "09-23", "v2.1.7", "扇形改圆环；切目标即时同步；标签切换动画"),
            ("feat", "09-23", "v2.1.5", "分类扩到 310 个扩展名，新增「游戏资源」"),
            ("feat", "09-23", "v2.1.3", "「类型分布」支持逐级下钻"),
            ("feat", "09-22", "v2.0.2", "顶栏新增磁盘健康度（S.M.A.R.T.）"),
            ("feat", "早期", "v1.7.0", "即时搜索框；磁盘容量条；滚动条胶囊化"),
            ("feat", "早期", "v1.5.0", "全局深浅主题；排行榜设为默认首页"),
            ("feat", "早期", "v1.2.0", "树图双击进入/返回；同目标缓存不重复扫"),

            ("fix", "09-24", "v2.21.0", "更新日志重写：每条压成一行、并标上日期"),
            ("fix", "09-24", "v2.22.1", "修落盘缓存的 pickle 隐患：不再存类实例、只存纯数据（否则缓存换上下文就反序列化失败，表现为「缓存读不出来」）"),
            ("fix", "09-24", "v2.22.2", "补上一版：ScanStats 用了 __slots__，没有 __dict__，所以统计数字没存进去 —— 改成按 slots 逐个存取"),
            ("fix", "09-25", "v2.23.1", "修「打开软件又跳出 SpaceMap 窗口」：Edge 已在运行时 Chromium 会忽略 --window-position，所以窗口落在屏幕中间；现在预热后立刻盯着，一出现就藏起来，切到标签页才正式嵌入"),
            ("fix", "09-25", "v2.23.2", "界面措辞去口语化：统一用「预扫描」不用「扫盘」，「秒开」「切过去」「就没用了」这类口语改成书面表达"),
            ("fix", "09-26", "v2.23.3", "类型分布标注：字号 9→10，并把「按每字 14.5px 猜宽度」换成**实际量宽**，再用画布剩余空间决定截断，不再出现「系统程序 51.8 GB · 50…」这种被截掉的情况"),
            ("fix", "09-26", "v2.23.4", "修「没能抓到 SpaceMap 的窗口」：v2.23.1 为了让预热窗口不弹到桌面上主动把它藏了起来，而找窗口时又用 IsWindowVisible 过滤掉了不可见窗口 —— 藏起来就再也找不到。现在找窗口不再看可见性，清扫孤儿则把隐藏的也算进去"),
            ("sec", "", "", "■ 修复 · 细节优化"),
            ("fix", "09-24", "v2.20.1", "清理列表右键可直接删除该项内容"),
            ("fix", "09-24", "v2.19.2", "修搜索失效；搜索改用堆选择提速"),
            ("fix", "09-24", "v2.19.1", "修开机没查缓存、导致仍然重扫"),
            ("fix", "09-24", "v2.18.2", "修关闭后残留 SpaceMap 孤儿窗口"),
            ("fix", "09-24", "v2.18.1", "关闭时连浏览器窗口一起关掉"),
            ("fix", "09-24", "v2.17.2", "修需手动点才嵌入；标题栏/黑框自愈"),
            ("fix", "09-24", "v2.17.1", "预热提前到 1.2 秒；大文件释放挪后台"),
            ("fix", "09-24", "v2.14.1", "关软件时一并收掉它启动的 SpaceMap"),
            ("fix", "09-24", "v2.13.1", "静态渲染 482ms → 184ms（限制标字数量）"),
            ("fix", "09-24", "v2.12.2", "修悬停白框从左上角框满屏（残留重复定义）"),
            ("fix", "09-24", "v2.12.1", "去掉蓝色选中框；加白色悬停框；首帧也画字"),
            ("fix", "09-24", "v2.11.2", "修「返回上级」动画丢失（计时器没重置）"),
            ("fix", "09-24", "v2.11.1", "紧急修树图卡死（_e 未定义导致异常）"),
            ("fix", "09-24", "v2.10.2", "回退上一版无效的低清预算改动"),
            ("fix", "09-24", "v2.10.0", "修文字被误截断；动画帧数 8 → 16"),
            ("fix", "09-24", "v2.9.3", "树图撤掉悬停白框；字号压小、标签更全"),
            ("fix", "09-24", "v2.9.2", "修白框指错格子；软件列表第三方排前"),
            ("fix", "09-24", "v2.9.1", "修标签顺序错乱；软件右键可卸载"),
            ("fix", "09-23", "v2.7.0", "修树图缩放被拉伸；标签门槛放宽"),
            ("fix", "09-23", "v2.5.3", "设置窗口不再显示本机绝对路径"),
            ("fix", "09-23", "v2.5.1", "修浅色模式下按钮仍是深色底"),
            ("fix", "09-23", "v2.4.3", "更正联系邮箱拼写"),
            ("fix", "09-23", "v2.4.2", "修复扫描卡死（误判线程存活）"),
            ("fix", "09-23", "v2.4.1", "修深色下单选按钮白底白字；隐藏/系统徽章"),
            ("fix", "09-23", "v2.1.6", "树图帧冷暖交替；「其他」可看扩展名构成"),
            ("fix", "09-23", "v2.1.4", "修图例颜色没跟随树图配色"),
            ("fix", "09-23", "v2.1.2", "树图配色与「类型分布」图例统一"),
            ("fix", "09-23", "v2.1.1", "修扇形图被画成整圆（Tk 的 extent bug）"),
            ("fix", "09-22", "v2.0.4", "右侧「当前目录内容」列宽调整"),
            ("fix", "09-22", "v2.0.3", "健康度即时刷新；默认窗口调大并居中"),
            ("fix", "早期", "v1.9.0", "选中框改淡蓝圆角描边 + 外扩光晕"),
            ("fix", "早期", "v1.8.1", "修滚动条点击/拖动位置偏移"),
            ("feat", "早期", "v1.8.0", "标题栏加版权署名；新增「关于」窗口"),
            ("fix", "早期", "v1.6.0", "排行榜名称列加宽；滚动条改细圆角"),
            ("fix", "早期", "v1.2.1", "树图引入「拼图式合并」"),
        ]
        txt.insert("end", "更新日志\n", "h")
        txt.tag_config("h", font=("Microsoft YaHei UI", 12, "bold"),
                       foreground=p["text"], spacing1=2, spacing3=6)
        txt.tag_config("b_major", foreground="#d9534f", font=("Microsoft YaHei UI", 9, "bold"))
        txt.tag_config("b_feat", foreground="#2d6cdf", font=("Microsoft YaHei UI", 9, "bold"))
        txt.tag_config("b_fix", foreground="#2f9e5c", font=("Microsoft YaHei UI", 9, "bold"))
        txt.tag_config("v_major", foreground="#d9534f", font=("Microsoft YaHei UI", 10, "bold"))
        txt.tag_config("v_feat", foreground="#2d6cdf", font=("Microsoft YaHei UI", 10, "bold"))
        txt.tag_config("v_fix", foreground="#2f9e5c", font=("Microsoft YaHei UI", 10, "bold"))
        txt.tag_config("body", foreground=p["rsub"], spacing3=8)

        def _vkey(v):
            try:
                return tuple(int(x) for x in v.lstrip("v").split("."))
            except ValueError:
                return (0,)

        # 单一列表 + 严格按版本号降序。
        # 之前是按「级别分区」，每区内部虽然降序，但跨区读起来版本是乱的。
        items = [e for e in log if e[0] != "sec"]
        items.sort(key=lambda e: _vkey(e[2]), reverse=True)
        badge = {"major": "里程碑", "feat": "功能", "fix": "修复"}
        txt.tag_config("date", foreground=p["muted"], font=("Microsoft YaHei UI", 9))
        for kind, date, ver, body in items:
            txt.insert("end", "[%s] " % badge.get(kind, kind), "b_" + kind)
            txt.insert("end", "%-5s " % date, "date")
            txt.insert("end", ver + "  ", "v_" + kind)
            txt.insert("end", body + "\n", "body")
        txt.configure(state="disabled")

        self._mkbtn(dlg, "关闭", dlg.destroy).pack(pady=(0, 14))
        dlg.bind("<Escape>", lambda e: dlg.destroy())
        # 弹窗标题栏也跟随深色
        try:
            import ctypes
            user32 = ctypes.windll.user32
            dhwnd = user32.GetAncestor(dlg.winfo_id(), 2)
            val = ctypes.c_int(1 if self.theme == "dark" else 0)
            ctypes.windll.dwmapi.DwmSetWindowAttribute(
                dhwnd, 20, ctypes.byref(val), ctypes.sizeof(val))
        except Exception:
            pass
        dlg.grab_set()
        dlg.focus_set()

    def _set_dark_titlebar(self, dark):
        """Windows 10 2004+/11：让系统标题栏跟随深色模式（老系统静默忽略）。"""
        try:
            import ctypes
            user32 = ctypes.windll.user32
            # Tk 9 下 winfo_id() 是 TkChild 子窗口，DWM 属性必须设在 TkTopLevel 顶层窗口
            hwnd = user32.GetAncestor(self.winfo_id(), 2) or self.winfo_id()
            val = ctypes.c_int(1 if dark else 0)
            for attr in (20, 19):  # DWMWA_USE_IMMERSIVE_DARK_MODE
                hr = ctypes.windll.dwmapi.DwmSetWindowAttribute(
                    hwnd, attr, ctypes.byref(val), ctypes.sizeof(val))
                if hr == 0:
                    break
        except Exception:
            pass

    def _apply_theme(self):
        p = THEMES[self.theme]
        self.t = p
        self.configure(bg=p["app"])
        st = ttk.Style(self)
        st.configure(".", background=p["app"], foreground=p["text"])
        st.configure("TFrame", background=p["app"])
        st.configure("TLabel", background=p["app"], foreground=p["text"])
        st.configure("TButton", background=p["tab_bg"], foreground=p["text"],
                     bordercolor=p["tab_bg"], focuscolor=p["tab_bg"],
                     lightcolor=p["tab_bg"], darkcolor=p["tab_bg"], borderwidth=1)
        st.map("TButton",
               background=[("active", p["hover"]), ("pressed", p["hover"])],
               foreground=[("active", p["text"])])
        st.configure("Accent.TButton", background="#2d6cdf", foreground="#ffffff")
        st.map("Accent.TButton", background=[("active", "#3b7bf0")])
        st.configure("TCombobox", fieldbackground=p["tv_bg"], background=p["tab_bg"],
                     foreground=p["text"], arrowcolor=p["text"], bordercolor=p["tab_bg"],
                     lightcolor=p["tab_bg"], darkcolor=p["tab_bg"], selectbackground="#2d6cdf",
                     selectforeground="#ffffff")
        st.map("TCombobox",
               fieldbackground=[("readonly", p["tv_bg"]), ("!readonly", p["tv_bg"]),
                                ("disabled", p["tab_bg"])],
               foreground=[("readonly", p["text"]), ("!readonly", p["text"])],
               background=[("readonly", p["tab_bg"]), ("!readonly", p["tab_bg"])],
               bordercolor=[("focus", p["tab_bg"]), ("active", p["tab_bg"])],
               lightcolor=[("readonly", p["tab_bg"])], darkcolor=[("readonly", p["tab_bg"])],
               arrowcolor=[("active", p["text"])])
        self.option_add("*TCombobox*Listbox.background", p["tv_bg"])
        self.option_add("*TCombobox*Listbox.foreground", p["text"])
        self.option_add("*TCombobox*Listbox.selectBackground", "#2d6cdf")
        self.option_add("*TCombobox*Listbox.selectForeground", "#ffffff")
        st.configure("TProgressbar", troughcolor=p["sb_trough"], background="#2d6cdf",
                     bordercolor=p["sb_trough"])
        # 去掉 clam notebook 的外框元素，标签边框颜色全部压平，避免深色下白边
        st.layout("TNotebook", [("TNotebook.client", {"sticky": "nswe"})])
        st.configure("TNotebook", background=p["app"], borderwidth=0, tabmargins=0,
                     bordercolor=p["app"], lightcolor=p["app"], darkcolor=p["app"])
        st.configure("TNotebook.Tab", background=p["tab_bg"], foreground=p["muted"],
                     padding=(14, 6), borderwidth=0, focusthickness=0,
                     focuscolor=p["tab_sel"],
                     bordercolor=p["tab_bg"], lightcolor=p["tab_bg"], darkcolor=p["tab_bg"])
        st.map("TNotebook.Tab",
               background=[("selected", p["tab_sel"]), ("active", p["hover"])],
               foreground=[("selected", p["text"]), ("active", p["text"])],
               bordercolor=[("selected", p["tab_sel"]), ("active", p["hover"])],
               lightcolor=[("selected", p["tab_sel"]), ("active", p["hover"])],
               darkcolor=[("selected", p["tab_sel"]), ("active", p["hover"])])
        st.configure("Treeview", background=p["tv_bg"], fieldbackground=p["tv_bg"],
                     foreground=p["text"], bordercolor=p["tv_bg"], borderwidth=0, relief="flat",
                     lightcolor=p["tv_bg"], darkcolor=p["tv_bg"])
        st.map("Treeview",
               background=[("selected", "#2d6cdf")],
               foreground=[("selected", "#ffffff")])
        st.configure("Treeview.Heading", background=p["tv_head"], foreground=p["text"],
                     relief="flat", bordercolor=p["tv_head"],
                     lightcolor=p["tv_head"], darkcolor=p["tv_head"])
        st.map("Treeview.Heading", background=[("active", p["hover"])])
        st.configure("TScrollbar", background=p["tab_bg"], troughcolor=p["sb_trough"],
                     arrowcolor=p["text"], bordercolor=p["sb_trough"])
        if self.theme == "light":
            sb_thumb, sb_hover = "#c3cad6", "#9aa6b8"
        else:
            sb_thumb, sb_hover = "#3a4556", "#4d5c72"
        for _sb, _bg in ((self.rank_sb, p["rank_bg"]), (self.type_sb, p["canvas"]),
                         (self.big_sb, p["tv_bg"]), (self.child_sb, p["tv_bg"]),
                         (self.search_sb, p["tv_bg"])):
            _sb.set_colors(_bg, sb_thumb, sb_hover)
        if getattr(self, "_disk_pct", None) is not None:
            self._draw_disk_bar()
        self.paned.configure(bg=p["app"])
        st.configure("TEntry", fieldbackground=p["tv_bg"], foreground=p["text"],
                     insertcolor=p["text"], bordercolor=p["tab_bg"],
                     lightcolor=p["tab_bg"], darkcolor=p["tab_bg"])
        # 单选/复选/分组框：不配的话深色下会保留系统浅色底，出现"白框、字看不见"
        st.configure("TRadiobutton", background=p["app"], foreground=p["text"],
                     focuscolor=p["app"], indicatorcolor=p["tv_bg"],
                     bordercolor=p["tab_bg"], lightcolor=p["app"], darkcolor=p["app"])
        st.map("TRadiobutton",
               background=[("active", p["app"]), ("selected", p["app"]),
                           ("!selected", p["app"]), ("disabled", p["app"])],
               foreground=[("active", p["text"]), ("selected", p["text"]),
                           ("!selected", p["text"]), ("disabled", p["rsub"])],
               indicatorcolor=[("selected", "#2d6cdf"), ("!selected", p["tv_bg"])])
        st.configure("TCheckbutton", background=p["app"], foreground=p["text"],
                     focuscolor=p["app"], indicatorcolor=p["tv_bg"],
                     bordercolor=p["tab_bg"], lightcolor=p["app"], darkcolor=p["app"])
        st.map("TCheckbutton",
               background=[("active", p["app"]), ("selected", p["app"]), ("!selected", p["app"])],
               foreground=[("active", p["text"]), ("selected", p["text"]), ("!selected", p["text"])],
               indicatorcolor=[("selected", "#2d6cdf"), ("!selected", p["tv_bg"])])
        st.configure("TLabelframe", background=p["app"], bordercolor=p["tab_bg"],
                     lightcolor=p["app"], darkcolor=p["app"], relief="solid", borderwidth=1)
        st.configure("TLabelframe.Label", background=p["app"], foreground=p["text"])
        self.option_add("*TEntry*selectBackground", "#2d6cdf")
        self.option_add("*TEntry*selectForeground", "#ffffff")
        self.disk_bar.configure(bg=p["app"])
        # 画布底色
        self.tree_canvas.configure(bg=p["canvas"])
        self.type_canvas.configure(bg=p["canvas"])
        self.rank_canvas.configure(bg=p["rank_bg"])
        # 排行榜标签页里的 tk 原生控件
        tab_rank = self.rank_head.master
        tab_rank.configure(bg=p["rank_bg"])
        self.rank_head.configure(bg=p["rank_bg"])
        self.rank_body.configure(bg=p["rank_bg"])
        self.lbl_rank_path.configure(bg=p["rank_bg"], fg=p["rsub"])

        # 显式指定过颜色的标签
        self.lbl_disk.configure(background=p["app"], foreground=p["muted"])
        self.lbl_status.configure(background=p["app"], foreground=p["muted"])
        self.lbl_hint.configure(background=p["app"], foreground=p["muted"])
        self.lbl_scaninfo.configure(background=p["app"], foreground=p["muted"])
        self.lbl_right_head.configure(background=p["app"], foreground=p["text"])
        self.lbl_big_note.configure(background=p["app"], foreground=p["muted"])
        self.lbl_tree_note.configure(background=p["app"], foreground=p["muted"])
        # 树图底部图例的色块：必须和树图实际用的 sm_file_color 一致
        for _i, _sw in enumerate(getattr(self, "tree_legend_swatches", [])):
            _sw.configure(bg=sm_file_color(self.theme, _i))
        # 标签指示条也要跟着主题重画
        if getattr(self, "tab_ind", None) is not None:
            self.tab_ind.configure(bg=p["tab_bg"])
            try:
                self._move_tab_ind(self.nb.index(self.nb.select()), animate=False)
            except tk.TclError:
                pass
        # 树图 / 类型分布 自带的导航条
        for _head, _bg in ((self.tree_head, p["canvas"]), (self.type_head, p["canvas"])):
            _head.configure(bg=_bg)

        for _lbl, _fg in ((self.lbl_tree_path, p["muted"]), (self.lbl_tree_hint, p["muted"]),
                          (self.lbl_type_path, p["muted"]), (self.lbl_type_hint, p["muted"])):
            _lbl.configure(bg=p["canvas"], fg=_fg)
        self._update_theme_button()

    def _repaint_all(self):
        """切换主题后重绘所有画布内容。"""
        if self.rank_anim_after:
            self.after_cancel(self.rank_anim_after)
            self.rank_anim_after = None
            self.rank_animating = False
        self._render_tree()
        self._render_type_tab()
        if self.result and self.rank_path:
            self._rank_render(animate=False)
        else:
            self.rank_canvas.delete("all")
            self.rank_canvas.create_text(320, 220, text="选择目标后点击「开始扫描」",
                                         fill=self.t["rsub"],
                                         font=("Microsoft YaHei UI", 11))

    def _mkbtn(self, parent, text, command, bg=None, fg=None, outer=None,
               outer_key="app", **kw):
        """造一个圆角按钮并登记下来，方便切主题时统一刷新颜色。"""
        btns = getattr(self, "_round_buttons", None)
        if btns is None:
            btns = self._round_buttons = []
        # _build_ui 跑在 _apply_theme 之前，那时 self.t 还不存在，先按当前主题名兜底
        th = getattr(self, "t", None)
        if th is None:
            th = THEMES.get(getattr(self, "theme", "light"), THEMES["light"])
            self.t = th
        st = kw.pop("state", "normal")
        b = RoundButton(parent, text=text, command=command,
                        outer=outer or th["app"], bg=bg or th["tab_bg"],
                        fg=fg or th["text"], hover=th["hover"],
                        font=("Microsoft YaHei UI", 9), **kw)
        # 记住角色和所在背景：切主题时要按当前主题重新取色，
        # 不能沿用创建时的颜色（否则从深色启动再切浅色，按钮还是深底）
        b._role = "primary" if bg == "#2d6cdf" else "normal"
        b._outer_key = outer_key
        if st != "normal":
            b.configure(state=st)
        btns.append(b)
        return b

    def _build_ui(self):
        top = ttk.Frame(self, padding=(10, 8, 10, 4))
        top.pack(fill="x")
        ttk.Label(top, text="扫描目标:").pack(side="left")
        self.target_cb = ttk.Combobox(top, width=24, state="readonly")
        self.target_cb.pack(side="left", padx=(4, 6))
        self.target_cb.bind("<<ComboboxSelected>>",
                            lambda e: self._set_target(self.target_cb.get()))
        self.btn_folder = self._mkbtn(top, "选择文件夹…", self._pick_folder)
        self.btn_folder.pack(side="left", padx=(0, 6))
        self.btn_scan = self._mkbtn(top, "开始扫描", self._toggle_scan, bg="#2d6cdf", fg="#ffffff")
        self.btn_scan.pack(side="left")
        self.btn_up = self._mkbtn(top, "⬆ 上级", self._go_up, state="disabled")
        self.btn_up.pack(side="left", padx=(10, 0))
        ttk.Label(top, text="🔍 搜索:").pack(side="left", padx=(16, 3))
        self.var_search = tk.StringVar()
        self.ent_search = ttk.Entry(top, width=38, textvariable=self.var_search)
        self.ent_search.pack(side="left")
        self.ent_search.bind("<Return>", lambda e: self._do_search())
        self._search_after = None
        self.var_search.trace_add("write", lambda *a: self._on_search_input())
        self.btn_search = self._mkbtn(top, "搜索", self._do_search, bg="#2d6cdf", fg="#ffffff")
        self.btn_search.pack(side="left", padx=(6, 0))
        self.lbl_health = ttk.Label(top, text="磁盘健康 --", font=("Microsoft YaHei UI", 9, "bold"))
        self.lbl_health.pack(side="right", padx=(0, 12))
        self.lbl_health.bind("<Enter>", self._health_enter)
        self.lbl_health.bind("<Leave>", self._health_leave)
        self._health_tip = ""
        self.btn_about = self._mkbtn(top, "关于", self._show_about)
        self.btn_about.pack(side="right", padx=(0, 8))
        self.btn_settings = self._mkbtn(top, "设置", self._show_settings)
        self.btn_settings.pack(side="right", padx=(0, 8))
        self.btn_theme = self._mkbtn(top, "深色模式", self._toggle_theme)
        self.btn_theme.pack(side="right", padx=(0, 8))

        # 当前目标 + 后台预扫描进度 + 安全说明
        self.path_row = ttk.Frame(self)
        self.path_row.pack(fill="x")
        self.lbl_path = ttk.Label(self.path_row, text="尚未扫描", anchor="w", padding=(10, 2))
        self.lbl_path.pack(side="left")
        self.lbl_prescan = ttk.Label(self.path_row, text="", anchor="e", padding=(10, 2))
        self.lbl_prescan.pack(side="right")
        self.lbl_safe = ttk.Label(
            self.path_row, anchor="e", padding=(10, 2),
            text="🛡 安全保护：只读取文件名、大小和路径，不打开文件内容 · 不联网 · 不上传任何数据",
            foreground="#2f9e5c")
        self.lbl_safe.pack(side="right")

        prog = ttk.Frame(self, padding=(10, 0, 10, 4))
        prog.pack(fill="x")
        self.progress = ttk.Progressbar(prog, mode="indeterminate", length=240)
        self.progress.pack(side="left")
        self.lbl_status = ttk.Label(prog, text="就绪", anchor="w")
        self.lbl_status.pack(side="left", padx=10, fill="x", expand=True)

        diskrow = ttk.Frame(self, padding=(10, 0, 10, 4))
        diskrow.pack(fill="x")
        self.lbl_disk = ttk.Label(diskrow, text="", anchor="w", foreground="#555")
        self.lbl_disk.pack(side="left")
        self.disk_bar = tk.Canvas(diskrow, width=280, height=14, highlightthickness=0, bd=0)
        self.disk_bar.pack(side="left", padx=(14, 0), pady=2)

        paned = tk.PanedWindow(self, orient="horizontal", bd=0, sashwidth=4,
                               sashrelief="flat", sashpad=0,
                               bg=THEMES[self.theme]["app"])
        paned.pack(fill="both", expand=True, padx=10, pady=(0, 4))
        self.paned = paned

        left = ttk.Frame(paned)
        paned.add(left, minsize=420, stretch="always")
        self.nb = ttk.Notebook(left)
        self.nb.pack(fill="both", expand=True)
        # 标签栏下沿的滑动指示条：ttk 的标签本身没法做动画，
        # 就在标签行底部盖一条 3px 的细条，切换时从旧标签滑到新标签。
        self.tab_ind = tk.Canvas(self.nb, height=3, highlightthickness=0, bd=0)
        self.tab_ind.bind("<Button-1>", self._tab_ind_click)
        self._tab_ind_after = None
        self._tab_ind_cur = None
        self.after(500, self._place_tab_ind)

        # 标签页1: 文件夹树图
        tab_tree = ttk.Frame(self.nb)
        self.tab_tree = tab_tree
        self.nb.add(tab_tree, text="文件夹树图")

        # 标签页: SpaceMap 树图（把 SpaceMap.exe 的窗口嵌进来用，原树图不动）
        tab_sm = ttk.Frame(self.nb)
        self.tab_spacemap = tab_sm
        self.nb.add(tab_sm, text="SpaceMap 树图")
        smbar = ttk.Frame(tab_sm)
        smbar.pack(fill="x", padx=8, pady=(4, 3))
        self.lbl_sm = ttk.Label(
            smbar, anchor="w", font=("Microsoft YaHei UI", 9),
            text="SpaceMap 用浏览器画布渲染，动画最顺 —— 这里直接把它的窗口嵌进来，"
                 "跟着当前扫描目标走。原来的「文件夹树图」保持不变")
        self.lbl_sm.pack(side="left", fill="x", expand=True)
        self.btn_sm = self._mkbtn(smbar, "启动并嵌入", self._spacemap_start,
                                  bg="#2d6cdf", fg="#ffffff")
        self.btn_sm.pack(side="right")
        self.sm_host = tk.Frame(tab_sm, bg=self.t.get("canvas", "#1a1f29"),
                                highlightthickness=0, bd=0)
        self.sm_host.pack(fill="both", expand=True)      # 贴边，不留白边
        self.sm_host.bind("<Configure>", self._spacemap_resize)
        self._sm_hwnd = 0

        # 标签页4: 清理建议（只分析、只导航，绝不删东西）
        # 「清理建议」不再单独占一个标签：和「软件占用」合并成上下两栏
        tab_combo = ttk.Frame(self.nb)
        self.tab_combo = tab_combo
        self.nb.add(tab_combo, text="清理与软件")
        combo = ttk.PanedWindow(tab_combo, orient="vertical")
        combo.pack(fill="both", expand=True)
        self._combo_paned = combo
        tab_clean = ttk.Frame(combo)
        self.tab_clean = tab_clean

        # 标签页5: 软件占用（把散在多个目录的同一软件合并成一个条目）
        tab_soft = ttk.Frame(combo)
        self.tab_soft = tab_soft
        combo.add(tab_clean, weight=2)
        combo.add(tab_soft, weight=5)
        combo.configure(height=999)
        shead = ttk.Frame(tab_soft)
        shead.pack(fill="x", padx=8, pady=(6, 3))
        self.lbl_soft_sum = ttk.Label(
            shead, anchor="w", font=("Microsoft YaHei UI", 9),
            text="② 软件占用 —— 每个软件实际占了多少、分散在哪些盘。打开软件后自动分析，右键可打开目录或卸载")
        self.lbl_soft_sum.pack(side="left", fill="x", expand=True)
        self.btn_soft_go = self._mkbtn(shead, "分析软件占用", self._soft_scan,
                                       bg="#2d6cdf", fg="#ffffff")
        self.btn_soft_go.pack(side="right")
        # 行高加高：默认 23px 塞不下 24px 图标，图标会被裁掉
        st2 = ttk.Style(self)
        st2.configure("Soft.Treeview", rowheight=30, font=("Microsoft YaHei UI", 9),
                      borderwidth=0, relief="flat")
        self.soft_tree = ttk.Treeview(tab_soft,
                                      columns=("cat", "size", "gap", "disk", "dirs", "pub"),
                                      show="tree headings", style="Soft.Treeview")
        self.soft_tree.heading("#0", text="软件")
        self.soft_tree.column("#0", width=300, anchor="w", minwidth=220)
        for c, t, w, an in (("cat", "类别", 90, "center"), ("size", "总占用", 100, "e"),
                            ("gap", "", 46, "center"),
                            ("disk", "分布在哪些盘", 230, "w"), ("dirs", "目录", 60, "center"),
                            ("pub", "厂商", 170, "w")):
            self.soft_tree.heading(c, text=t)
            self.soft_tree.column(c, width=w, anchor=an)
        self.soft_tree.bind("<Double-1>", self._soft_open)
        self.soft_tree.bind("<Button-3>", self._soft_right)
        ssb = MiniScrollbar(tab_soft, command=self.soft_tree.yview)
        self.soft_tree.configure(yscrollcommand=ssb.set)
        self.soft_tree.pack(side="left", fill="both", expand=True)
        ssb.pack(side="right", fill="y", padx=(1, 6))
        ssb.set_colors(self.t["tv_bg"], "#9aa6b8", "#66717f")
        self._soft_sb = ssb
        ttk.Label(tab_soft,
                  text="占用 = 安装目录 + 匹配到的数据目录 · 双击打开主目录 · 右键可卸载",
                  foreground="#888", wraplength=760, justify="left").pack(
            side="bottom", fill="x", anchor="w", padx=10, pady=(0, 4))
        self._soft_icons = {}
        chead = ttk.Frame(tab_clean)
        chead.pack(fill="x", padx=8, pady=(6, 3))
        self.lbl_clean_sum = ttk.Label(
            chead, anchor="w", font=("Microsoft YaHei UI", 9),
            text="① 清理建议 —— 帮你找出可以安全释放的空间（21 处常见位置）。打开软件后自动分析，也可点右边重跑。本功能只分析，不会删除任何文件")
        self.lbl_clean_sum.pack(side="left", fill="x", expand=True)
        self.btn_clean_go = self._mkbtn(chead, "开始分析", self._clean_scan)
        self.btn_clean_go.pack(side="right")
        self.btn_clean_purge = self._mkbtn(chead, "一键清理", self._clean_all,
                                           bg="#2d6cdf", fg="#ffffff")
        self.btn_clean_purge.pack(side="right", padx=(0, 6))
        ccols = ("size", "risk", "name", "where", "advice")
        self.clean_tree = ttk.Treeview(tab_clean, columns=ccols, show="headings")
        for c, t, w, an in (("size", "占用", 90, "e"), ("risk", "风险", 76, "center"),
                            ("name", "项目", 150, "w"), ("where", "具体位置", 330, "w"),
                            ("advice", "说明与建议", 430, "w")):
            self.clean_tree.heading(c, text=t)
            self.clean_tree.column(c, width=w, anchor=an)
        self.clean_tree.tag_configure("odd", background=self.t.get("tv_head", "#eeeeee"))
        self.clean_tree.tag_configure("safe", foreground="#3fbf7f")
        self.clean_tree.tag_configure("caution", foreground="#d9a441")
        self.clean_tree.tag_configure("danger", foreground="#d9534f")
        self.clean_tree.bind("<Double-1>", self._clean_open)
        self.clean_tree.bind("<Button-3>", self._clean_right)
        csb = MiniScrollbar(tab_clean, command=self.clean_tree.yview)
        self.clean_tree.configure(yscrollcommand=csb.set)
        self.clean_tree.pack(side="left", fill="both", expand=True)
        csb.pack(side="right", fill="y", padx=(1, 6))
        csb.set_colors(self.t["tv_bg"], "#9aa6b8", "#66717f")
        self._clean_sb = csb
        ttk.Label(tab_clean, text="双击打开该位置 · 右键有更多操作",
                  foreground="#888", wraplength=760, justify="left").pack(
            side="bottom", fill="x", anchor="w", padx=10, pady=(0, 4))
        # 树图自带的导航条：返回上级的按钮就放在图的正上方，不用跑回顶部工具栏去点
        tree_head = tk.Frame(tab_tree)
        self.tree_head = tree_head
        tree_head.pack(fill="x", padx=8, pady=(6, 3))
        self.btn_tree_up = self._mkbtn(tree_head, "← 返回上级", self._go_up, outer_key="canvas")
        self.btn_tree_up.pack(side="left")
        self.lbl_tree_path = tk.Label(tree_head, text="", anchor="w",
                                      font=("Microsoft YaHei UI", 9))
        self.lbl_tree_path.pack(side="left", padx=10, fill="x", expand=True)
        self.lbl_tree_hint = tk.Label(tree_head, text="双击方块进入 · 双击空白返回",
                                      anchor="e", font=("Microsoft YaHei UI", 9))
        self.lbl_tree_hint.pack(side="right")

        self.tree_canvas = tk.Canvas(tab_tree, bg="#fdfdfd", highlightthickness=0)
        self.tree_canvas.pack(fill="both", expand=True)
        # 窗口拉大拉小要跟着重画（防抖，别在拖动过程中疯狂重绘）
        self.tree_canvas.bind("<Configure>", self._on_tree_configure)
        legend = ttk.Frame(tab_tree)
        legend.pack(fill="x", padx=6, pady=4)
        # 色块要跟树图实际用的配色一致（sm_file_color），并且随深浅主题变，
        # 所以把控件存下来，在 _apply_theme 里刷新颜色。
        # 分类加到 9 类之后一行放不下（实测要 798px，窄窗口会截断），改成网格自动换行。
        self.tree_legend_swatches = []
        COLS = 5
        for i, (_n, _color, _e) in enumerate(TYPE_GROUPS):
            cell = ttk.Frame(legend)
            cell.grid(row=i // COLS, column=i % COLS, sticky="w", padx=(0, 16), pady=1)
            f = tk.Frame(cell, width=12, height=12)
            f.pack(side="left")
            self.tree_legend_swatches.append(f)
            ttk.Label(cell, text=_n).pack(side="left", padx=(4, 0))
        self.lbl_tree_note = ttk.Label(legend, text="（文件按类型着色；文件夹底色按层级递进）")
        self.lbl_tree_note.grid(row=len(TYPE_GROUPS) // COLS, column=len(TYPE_GROUPS) % COLS,
                                sticky="w", padx=(0, 0), pady=1)

        # 标签页: 文件夹排行（横条排行榜，单击文件夹逐级进入）
        tab_rank = tk.Frame(self.nb)
        self.tab_rank = tab_rank
        self.nb.add(tab_rank, text="文件夹排行")
        self.rank_head = tk.Frame(tab_rank)
        self.rank_head.pack(fill="x", padx=10, pady=(8, 2))
        self.btn_rank_up = self._mkbtn(self.rank_head, "← 返回上级", self._rank_back, outer_key="rank_bg")
        self.btn_rank_up.pack(side="left")
        self.lbl_rank_path = tk.Label(self.rank_head, text="尚未扫描",
                                      font=("Microsoft YaHei UI", 9), anchor="w")
        self.lbl_rank_path.pack(side="left", padx=10, fill="x", expand=True)
        self.rank_body = tk.Frame(tab_rank)
        self.rank_body.pack(fill="both", expand=True)
        self.rank_canvas = tk.Canvas(self.rank_body, highlightthickness=0)
        self.rank_sb = MiniScrollbar(self.rank_body, command=self.rank_canvas.yview)
        self.rank_canvas.configure(yscrollcommand=self.rank_sb.set)
        self.rank_sb.pack(side="right", fill="y", padx=(1, 6))
        self.rank_canvas.pack(side="left", fill="both", expand=True)

        # 标签页: 搜索结果（默认隐藏，输入搜索词时出现）
        tab_search = ttk.Frame(self.nb)
        self.tab_search = tab_search
        self.nb.add(tab_search, text="搜索结果")
        self.search_info = ttk.Label(tab_search, text="", anchor="w")
        self.search_info.pack(fill="x", padx=6, pady=(4, 0))
        cols3 = ("size", "name", "type", "loc")
        self.search_tree = ttk.Treeview(tab_search, columns=cols3, show="headings")
        for c, t, w, an in (("size", "大小", 95, "e"), ("name", "名称", 240, "w"),
                            ("type", "类型", 80, "w"), ("loc", "位置", 360, "w")):
            self.search_tree.heading(c, text=t)
            self.search_tree.column(c, width=w, anchor=an)
        self.search_sb = MiniScrollbar(tab_search, command=self.search_tree.yview)
        self.search_tree.configure(yscrollcommand=self.search_sb.set)
        self.search_tree.pack(side="left", fill="both", expand=True)
        self.search_sb.pack(side="right", fill="y", padx=(1, 6))
        self._search_map = {}
        self._search_shown = False
        self.nb.hide(tab_search)
        self.search_tree.bind("<Double-1>", self._on_search_double)
        self.search_tree.bind("<Button-3>", self._on_search_right)

        # 标签页3: 类型分布
        tab_type = ttk.Frame(self.nb)
        self.tab_type = tab_type
        self.nb.add(tab_type, text="类型分布")
        # 类型分布也能逐级下钻，所以同样给一条导航条
        type_head = tk.Frame(tab_type)
        self.type_head = type_head
        type_head.pack(fill="x", padx=8, pady=(6, 3))
        self.btn_type_back = self._mkbtn(type_head, "← 返回上级", self._type_back, outer_key="canvas")
        self.btn_type_back.pack(side="left")
        self.lbl_type_path = tk.Label(type_head, text="", anchor="w",
                                      font=("Microsoft YaHei UI", 9))
        self.lbl_type_path.pack(side="left", padx=10, fill="x", expand=True)
        self.lbl_type_hint = tk.Label(type_head, text="点扇形或图例继续下钻",
                                      anchor="e", font=("Microsoft YaHei UI", 9))
        self.lbl_type_hint.pack(side="right")
        self.type_sb = MiniScrollbar(tab_type)
        self.type_canvas = tk.Canvas(tab_type, bg="#fdfdfd", highlightthickness=0,
                                     yscrollcommand=self.type_sb.set)
        self.type_sb.cmd = self.type_canvas.yview
        self.type_sb.pack(side="right", fill="y", padx=(1, 6))
        self.type_canvas.pack(side="left", fill="both", expand=True)
        self.type_canvas.bind("<MouseWheel>",
                              lambda e: self.type_canvas.yview_scroll(int(-e.delta / 120), "units"))
        self.type_canvas.bind("<Button-1>", self._on_type_click)

        # 标签页3: 大文件排行（可切换按文件/按文件夹）
        tab_big = ttk.Frame(self.nb)
        self.tab_big = tab_big
        self.nb.add(tab_big, text="大文件/大目录排行")
        bar = ttk.Frame(tab_big)
        bar.pack(fill="x", padx=6, pady=(4, 0))
        ttk.Radiobutton(bar, text="按文件", variable=self._big_mode, value="file",
                        command=self._fill_big_files).pack(side="left")
        ttk.Radiobutton(bar, text="按文件夹", variable=self._big_mode, value="folder",
                        command=self._fill_big_files).pack(side="left", padx=(10, 0))
        self.lbl_big_note = ttk.Label(bar, text="（按文件夹=哪些目录占用最大，可双击跳转）",
                                      foreground="#888")
        self.lbl_big_note.pack(side="left", padx=10)
        ttk.Label(bar, text="筛选:").pack(side="left", padx=(10, 3))
        self.var_bigfilter = tk.StringVar()
        self.ent_bigfilter = ttk.Entry(bar, width=16, textvariable=self.var_bigfilter)
        self.ent_bigfilter.pack(side="left")
        self.var_bigfilter.trace_add("write", lambda *a: self._fill_big_files())
        cols = ("size", "name", "type", "loc")
        self.big_tree = ttk.Treeview(tab_big, columns=cols, show="headings")
        for c, t, w, an in (("size", "大小", 95, "e"), ("name", "文件/文件夹", 220, "w"),
                            ("type", "类型", 80, "w"), ("loc", "位置", 320, "w")):
            self.big_tree.heading(c, text=t)
            self.big_tree.column(c, width=w, anchor=an)
        self.big_sb = MiniScrollbar(tab_big, command=self.big_tree.yview)
        self.big_tree.configure(yscrollcommand=self.big_sb.set)
        self.big_tree.pack(side="left", fill="both", expand=True)
        self.big_sb.pack(side="right", fill="y", padx=(1, 6))

        # 右侧: 当前目录内容
        right = ttk.Frame(paned, width=400)
        paned.add(right, minsize=280, stretch="never")
        self.lbl_right_head = ttk.Label(right, text="当前目录内容（按大小排序）",
                                        font=("Microsoft YaHei UI", 9, "bold"))
        self.lbl_right_head.pack(anchor="w", padx=6, pady=(4, 2))
        cols2 = ("name", "size", "pct", "type")
        self.child_tree = ttk.Treeview(right, columns=cols2, show="headings")
        for c, t, w, an in (("name", "名称", 140, "w"), ("size", "大小", 78, "e"),
                            ("pct", "占比", 58, "e"), ("type", "类型", 130, "w")):
            self.child_tree.heading(c, text=t)
            self.child_tree.column(c, width=w, anchor=an)
        self.child_sb = MiniScrollbar(right, command=self.child_tree.yview)
        self.child_tree.configure(yscrollcommand=self.child_sb.set)
        self.child_tree.pack(side="left", fill="both", expand=True, padx=(6, 0), pady=(0, 6))
        self.child_sb.pack(side="right", fill="y", pady=(0, 6), padx=(1, 6))

        status = ttk.Frame(self, padding=(10, 2, 10, 6))
        status.pack(fill="x")
        self.lbl_hint = ttk.Label(self, text="v%s · 排行榜: 单击文件夹逐级进入/双击文件直接打开/右键文件管理器 · 树图: 双击进入·双击空白返回 · 隐藏文件=黄框「隐」/系统文件=红框「系」" %
                                  APP_VERSION, foreground="#666")
        self.lbl_hint.pack(side="left")
        self.lbl_scaninfo = ttk.Label(self, text="", foreground="#666")
        self.lbl_scaninfo.pack(side="right")

        self.tree_canvas.bind("<Configure>", lambda e: self._render_tree())
        self.tree_canvas.bind("<Motion>", self._on_motion)
        self.tree_canvas.bind("<Button-1>", self._on_click)
        self.tree_canvas.bind("<Double-Button-1>", self._on_double)
        self.tree_canvas.bind("<Button-3>", self._on_tree_right)
        self.tree_canvas.bind("<Leave>", self._tree_leave)
        # 悬停就显示"会选中哪个"的白框（照 SpaceMap 那样，不用点）。
        # 用 add="+" 追加，不动原有的 tooltip 处理。
        self.child_tree.bind("<Double-1>", self._on_child_double)
        self.child_tree.bind("<Button-3>", self._on_child_right)
        self.big_tree.bind("<Double-1>", self._on_big_double)
        self.big_tree.bind("<Button-3>", self._on_big_right)
        # 文件夹排行榜
        self.rank_canvas.bind("<Button-1>", self._rank_click)
        self.rank_canvas.bind("<Double-Button-1>", self._rank_double)
        self.rank_canvas.bind("<Button-3>", self._rank_right)
        self.rank_canvas.bind("<Motion>", self._rank_motion)
        self.rank_canvas.bind("<Leave>", self._rank_leave)
        self.rank_canvas.bind("<MouseWheel>",
                              lambda e: self.rank_canvas.yview_scroll(int(-e.delta / 120), "units"))
        self.rank_canvas.bind("<Configure>", self._rank_on_configure)
        self.nb.bind("<<NotebookTabChanged>>", self._on_tab_changed)

        # 标签顺序：文件夹排行第一个并默认显示，类型/大文件居中，树图移到最后
        self.nb.insert(tab_rank, 0)
        self.nb.insert(tab_search, 1)
        self.nb.insert(tab_type, 2)
        self.nb.insert(tab_big, 3)
        self.nb.hide(tab_search)
        # 「清理建议」是后加的，挪到最后一个，绝不打乱原有标签顺序；
        # 默认页也显式指定成「文件夹排行」，不靠下标 0 碰运气
        self._apply_tab_order()
        self.nb.select(self.tab_rank)
        # 打开软件就把「清理建议 / 软件占用」在后台分析好，不用手动点
        self.after(2000, self._auto_combo)
        clean_scan_cache()                         # 清掉过期的落盘扫描缓存（>7天）
        self._spacemap_close_orphans()             # 先扫掉上次留下的孤儿窗口
        self.after(1200, self._spacemap_prestart)   # 开机就预热 SpaceMap，切过去就不用等
        self._apply_theme()
        self.rank_canvas.create_text(320, 220, text="选择目标后点击「开始扫描」",
                                     fill=self.t["rsub"],
                                     font=("Microsoft YaHei UI", 11))

    # ---------------- 目标选择 ----------------
    def _load_drives(self):
        drives = []
        for letter in string.ascii_uppercase:
            p = letter + ":\\"
            if os.path.exists(p):
                drives.append(p)
        self.target_cb["values"] = drives
        if drives:
            self.target_cb.current(0)
            # 启动时不在这里同步：交给 _prequest 用少量线程在后台预扫描
            self._set_target(drives[0], sync=False)

    def _set_target(self, path, sync=True):
        self.target = path
        self.lbl_path.config(text="目标: %s" % path)
        self._update_disk_info(path)
        self._refresh_health(path)
        # 让嵌入的 SpaceMap 跟着切到同一个目标
        try:
            self._spacemap_write_wanted(path)
        except Exception:      # noqa: BLE001
            pass
        if sync:
            # 切换目标后立刻把下面的四个界面同步过来：有缓存直接显示，没有就自动开扫
            self._sync_target()

    def _sync_target(self):
        """把界面切到当前 self.target：命中缓存就直接显示，否则自动开始扫描。"""
        target = (self.target or "").strip().strip('"')
        if not target or not os.path.exists(target):
            return
        if self._scan_active:
            # 还在扫别的目标：先请它停，扫完在 _poll_scan 里再同步一次
            if self.scanner:
                self.scanner.cancel.set()
            self._sync_pending = True
            return
        key = os.path.normcase(os.path.normpath(target))
        if self._apply_cached(key, target):
            return
        # 落盘缓存：7 天内扫过就直接用，完全不扫
        sc = load_scan_cache(target)
        if sc is not None:
            self._cache[key] = sc
            self._cache_ts[key] = getattr(sc, "scanned_at", "上次")
            self._cache.move_to_end(key)
            if self._apply_cached(key, target):
                return
        # 后台预扫描正好在扫这个盘 —— 直接把它接过来当当前扫描，
        # 别再起一个跟它抢磁盘（这就是"切盘还要重扫"的根源）
        if (getattr(self, "_prescan_key", None) == key
                and getattr(self, "_prescan_scanner", None) is not None):
            # 接管：扫描对象直接指向预扫描的那个 Scanner。
            # 注意**不要把 scan_thread 指向预扫描的工作线程** —— 它跨盘循环，
            # 会让界面永远以为"还在扫描"。
            self.scanner = self._prescan_scanner
            self.scan_thread = None
            self._scan_active = True
            self.result = None
            self.current_path = None
            self._clear_views()
            self.btn_scan.config(text="取消扫描", state="normal")
            self.progress.start(12)
            self.lbl_status.config(text="正在自动扫描 %s …" % target)
            return
        self._start_scan(target)

    @property
    def cache_max(self):
        """省内存模式只留 1 个目标的结果；流畅模式留 CACHE_MAX 个。"""
        return 1 if self.perf_mode == "lite" else CACHE_MAX

    def _scan_running(self):
        """当前这次扫描结束没有 —— **以 Scanner 自身的状态为准，不看线程死没死**。

        踩过的坑：后台预扫描的工作线程是**跨盘循环**的，一个盘扫完它还活着。
        如果按"线程 is_alive"判断，界面就会永远停在"正在扫描"，切目标也不生效。
        """
        if not getattr(self, "_scan_active", False):
            return False
        sc = self.scanner
        if sc is None:
            return False
        st = sc.stats
        if getattr(st, "end", 0) or getattr(st, "error", ""):
            return False
        return True

    def _finish_scan(self):
        self._scan_active = False
        self.scan_thread = None
        self.btn_scan.config(text="刷新", state="normal")
        self.progress.stop()

    def _apply_cached(self, key, target):
        """命中缓存就直接把界面刷出来。"""
        cached = self._cache.get(key)
        if cached is None:
            return False
        self.result = cached
        self.current_path = cached.root
        self._clear_views()
        self.btn_scan.config(text="刷新", state="normal")
        self.lbl_path.config(text="当前: %s" % self.current_path)
        self._update_disk_info(target)
        st = cached.stats
        self.lbl_status.config(text="已加载缓存结果（%s 扫描）· 点「刷新」可重新扫描" %
                               self._cache_ts.get(key, "上次"))
        self.lbl_scaninfo.config(
            text="共 %s 个文件 · %s 个目录 · 合计 %s    |    隐藏 %s 个/%s · 系统 %s 个/%s" %
                 ("{:,}".format(st.total_files), "{:,}".format(st.total_dirs), human_size(st.total),
                  "{:,}".format(st.hidden_files), human_size(st.hidden_bytes),
                  "{:,}".format(st.system_files), human_size(st.system_bytes)))
        self._refresh_views()
        self._rank_reset(animate=True)
        return True

    def _start_scan(self, target, nthreads=None):
        # 用户要扫了：让后台预扫描马上收手，别抢磁盘
        ps = getattr(self, "_prescan_scanner", None)
        if ps is not None:
            ps.cancel.set()
        self._scan_active = True
        self.result = None
        self.current_path = None
        self._clear_views()
        self.scanner = Scanner(target, nthreads=nthreads or SCAN_THREADS)
        self.scan_thread = threading.Thread(target=self._run_scan, daemon=True)
        self.btn_scan.config(text="取消扫描", state="normal")
        self.progress.start(12)
        self.scan_thread.start()

    def _drive_list(self):
        out = []
        for letter in string.ascii_uppercase:
            p = letter + ":\\"
            try:
                if os.path.exists(p):
                    out.append(p)
            except OSError:
                pass
        return out

    def _prequest(self):
        """启动时自动开工：

        1) 当前目标**立刻用正常线程数扫**，界面马上有进度、几十秒就出结果；
        2) 其余所有盘交给后台线程逐个预扫（每个只占 PRE_SCAN_THREADS 个线程），
           扫完写缓存，之后切到哪个盘都是秒开。
        """
        target = (self.target or "").strip().strip('"')
        if target and os.path.exists(target) and not self.result:
            key = os.path.normcase(os.path.normpath(target))
            if key not in self._cache:
                # 先看落盘缓存：7 天内扫过就直接用，开机不用再扫一遍
                sc = load_scan_cache(target)
                if sc is not None:
                    self._cache[key] = sc
                    self._cache_ts[key] = getattr(sc, "scanned_at", "上次")
            if key in self._cache:
                self._apply_cached(key, target)
            elif not (self.scan_thread and self.scan_thread.is_alive()):
                self.lbl_status.config(text="正在自动扫描 %s …" % target)
                self._start_scan(target)
        self._start_prescan_others()

    def _start_prescan_others(self):
        """后台把"还没扫过的盘"逐个预扫一遍（跳过当前目标）。

        省内存模式下不预扫其余盘：只保留当前目标，代价是切盘要现场扫。
        """
        if self.perf_mode == "lite":
            self._update_prescan_label()
            return
        t = getattr(self, "_prescan_thread", None)
        if t is not None and t.is_alive():
            return
        cur = ""
        if self.target:
            try:
                cur = os.path.normcase(os.path.normpath(self.target.strip().strip('"')))
            except OSError:
                cur = ""
        drives = [d for d in self._drive_list()
                  if os.path.normcase(os.path.normpath(d)) != cur]
        if not drives:
            return
        self._prescan_results = []
        self._prescan_total = len(drives)
        self._prescan_done = sum(
            1 for d in drives
            if os.path.normcase(os.path.normpath(d)) in self._cache)
        self._update_prescan_label()
        pending = [d for d in drives
                   if os.path.normcase(os.path.normpath(d)) not in self._cache]
        if not pending:
            return
        if not self.result:
            self.lbl_status.config(text="同时后台预扫描其余磁盘…（每个只占 %d 个线程）"
                                   % PRE_SCAN_THREADS)

        def worker():
            for d in pending:
                if self._closed:
                    return
                # 用户自己在扫：让路，别抢磁盘
                while self.scan_thread and self.scan_thread.is_alive() and not self._closed:
                    time.sleep(0.5)
                if self._closed:
                    return
                key = os.path.normcase(os.path.normpath(d))
                if key in self._cache:
                    continue
                cached = load_scan_cache(d)      # 7 天内有落盘缓存就不重扫
                if cached is not None:
                    self._prescan_results.append((key, cached))
                    for _ in range(600):
                        if self._closed:
                            return
                        if not any(k == key for k, _s in self._prescan_results):
                            break
                        time.sleep(0.1)
                    continue
                sc = Scanner(d, nthreads=PRE_SCAN_THREADS)
                self._prescan_scanner = sc
                self._prescan_key = key
                try:
                    sc.scan()
                except Exception:      # noqa: BLE001
                    continue
                finally:
                    self._prescan_scanner = None
                    self._prescan_key = None
                if sc.stats.cancelled:
                    continue          # 用户插进来扫了，这盘作废，看下一盘
                self._prescan_results.append((key, sc))
                for _ in range(600):
                    if self._closed:
                        return
                    if not any(k == key for k, _s in self._prescan_results):
                        break
                    time.sleep(0.1)

        self._prescan_thread = threading.Thread(target=worker, daemon=True)
        self._prescan_thread.start()

    def _apply_dpi_scaling(self):
        """按实际 DPI 校准字体与像素尺寸，兼容 125% / 150% / 200% 缩放。

        字体：把 Tk 的 scaling 设成 dpi/72，之后所有以「点」为单位的字号自动放大；
        像素：那些写死的尺寸（标题带 13px、圆环半径、横条高度等）按同一比例放大，
              否则字变大了框没变，文字会被裁掉。
        """
        global UI_SCALE, SM_HEADER_H, SM_PAD, SM_MIN_FRAME_W, SM_MIN_FRAME_H, SM_MIN_SPLIT
        try:
            self.update_idletasks()
            dpi = float(self.winfo_fpixels("1i"))
        except Exception:
            dpi = 96.0
        if dpi <= 0:
            dpi = 96.0
        try:
            self.tk.call("tk", "scaling", dpi / 72.0)
        except Exception:
            pass
        UI_SCALE = max(1.0, min(dpi / 96.0, 2.5))
        SM_PAD = round(1.0 * UI_SCALE, 2)
        SM_HEADER_H = int(round(13 * UI_SCALE))
        SM_MIN_FRAME_W = int(round(54 * UI_SCALE))
        SM_MIN_FRAME_H = int(round(30 * UI_SCALE))
        SM_MIN_SPLIT = round(8.0 * UI_SCALE, 1)

    def _initial_geometry(self):
        """初始窗口尺寸：屏幕工作区的 86%，再夹到合理区间。

        树图的观感跟画布面积强相关，但铺太满也不好拖动、也挡桌面，
        所以取 86% 并封顶 1680x1040。
        """
        sw = self.winfo_screenwidth()
        sh = self.winfo_screenheight()
        w = max(1200, min(int(sw * 0.92), 1860))
        h = max(760, min(int(sh * 0.92), 1140))
        return w, h

    def _center_window(self):
        self.update_idletasks()
        w, h = self.winfo_width(), self.winfo_height()
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        self.geometry("+%d+%d" % ((sw - w) // 2, max(0, (sh - h) // 2 - 20)))

    def _update_disk_info(self, path):
        try:
            d = os.path.splitdrive(os.path.abspath(path))[0] + "\\"
            u = shutil.disk_usage(d)
            pct = u.used / u.total * 100.0
            self.lbl_disk.config(text="%s  总 %s · 已用 %s（%.1f%%）· 可用 %s" %
                                (d, human_size(u.total), human_size(u.used), pct,
                                 human_size(u.free)))
            self._disk_pct = pct
            self._disk_free_pct = u.free / u.total
            self._draw_disk_bar()
        except OSError:
            self.lbl_disk.config(text="")
            self._disk_pct = None
            self.disk_bar.delete("all")

    def _draw_disk_bar(self):
        cv = self.disk_bar
        cv.delete("all")
        if getattr(self, "_disk_pct", None) is None:
            return
        w, h = 280, 14
        x1, y1, x2, y2 = 2.0, 2.0, w - 2.0, h - 2.0
        low = self._disk_free_pct < 0.10
        fill = "#e74c3c" if low else "#2d6cdf"
        cv.create_polygon(round_rect_points(x1, y1, x2, y2, (y2 - y1) / 2),
                          fill=self.t["sb_trough"], outline="", smooth=True)
        fw = max((y2 - y1), (x2 - x1) * min(self._disk_pct, 100.0) / 100.0)
        cv.create_polygon(round_rect_points(x1, y1, x1 + fw, y2, (y2 - y1) / 2),
                          fill=fill, outline="", smooth=True)

    def _pick_folder(self):
        p = filedialog.askdirectory(title="选择要扫描的文件夹（也可以选整个盘）",
                                    initialdir=self.target or "C:\\")
        if p:
            self.target_cb.set(p)
            self._set_target(p)

    # ---------------- 扫描控制 ----------------
    def _toggle_scan(self):
        if self._scan_running():
            if self.scanner:
                self.scanner.cancel.set()
            self.btn_scan.config(state="disabled", text="正在取消…")
            return
        target = self.target.strip().strip('"')
        if not target:
            messagebox.showwarning("提示", "请先选择要扫描的盘符或文件夹")
            return
        if not os.path.exists(target):
            messagebox.showerror("错误", "路径不存在:\n%s" % target)
            return
        # 按钮现在就是「刷新」：直接重新扫一遍，不走缓存。
        # 切目标时的自动加载走 _sync_target / _apply_cached。
        self.lbl_status.config(text="正在重新扫描…")
        self.lbl_scaninfo.config(text="")
        self._start_scan(target)

    def _drain_prescan(self):
        """把后台预扫描线程产出的结果收进缓存（必须在主线程做）。"""
        pending = getattr(self, "_prescan_results", None)
        while pending:
            key, sc = pending.pop(0)
            self._cache[key] = sc
            self._cache_ts[key] = time.strftime("%H:%M:%S")
            self._cache.move_to_end(key)
            while len(self._cache) > self.cache_max:
                old = next(iter(self._cache))
                del self._cache[old]
                self._cache_ts.pop(old, None)
            self._prescan_done = getattr(self, "_prescan_done", 0) + 1
            self._update_prescan_label()
            if type(sc) is Scanner:
                save_scan_cache(sc)                # 落盘，关掉软件也不丢
            self.lbl_status.config(text="预扫描完成：%s（%s）· 结果已写入缓存"
                                   % (key, human_size(sc.stats.total)))
            # 当前目标正是它、而界面还空着 —— 直接显示出来
            if not self.result and self.target:
                try:
                    if os.path.normcase(os.path.normpath(self.target)) == key:
                        self._apply_cached(key, self.target)
                except OSError:
                    pass

    def _run_scan(self):
        try:
            self.scanner.scan()
        except Exception as e:  # noqa: BLE001
            self.scanner.stats.error = str(e)
            import traceback
            traceback.print_exc()

    def _clear_views(self):
        self.tree_canvas.delete("all")
        self.type_canvas.delete("all")
        self.rank_canvas.delete("all")
        if self.rank_anim_after:
            self.after_cancel(self.rank_anim_after)
            self.rank_anim_after = None
        self.rank_animating = False
        self.rank_rows = []
        self.rank_hover = -1
        self.rank_path = None
        self.big_tree.delete(*self.big_tree.get_children())
        self.child_tree.delete(*self.child_tree.get_children())
        self._draw_items = []
        self._selected_path = None
        self._hover_idx = None
        self._world = None
        self._child_map = {}

    def _poll_scan(self):
        if self._closed:
            return
        # 先收后台预扫描的成果（放最前面：用户自己在扫的时候也要能收）
        self._drain_prescan()
        try:
            if self._scan_running():
                st = self.scanner.stats
                self.lbl_status.config(
                    text="已扫描 %s 个文件 / %s 个目录 · %s · 跳过 %s 个(权限) · 当前: %s" %
                    ("{:,}".format(st.files), "{:,}".format(st.dirs), human_size(st.bytes),
                     st.skipped, st.last_path[:90]))
                return
            if getattr(self, "_scan_active", False):
                self._finish_scan()
                st = self.scanner.stats
                if st.error:
                    self.lbl_status.config(text="扫描失败: %s" % st.error)
                    return
                if st.cancelled:
                    self.lbl_status.config(text="已取消（显示部分结果）· 用时 %.1f s · 跳过 %s 个目录(权限不足)" %
                                           (st.end - st.start, st.skipped))
                else:
                    self.lbl_status.config(text="扫描完成 · 用时 %.1f s · 隐藏 %s 个/%s · 系统 %s 个/%s · 跳过 %s 个目录(权限不足，可管理员运行)" %
                                           (st.end - st.start,
                                            "{:,}".format(st.hidden_files), human_size(st.hidden_bytes),
                                            "{:,}".format(st.system_files), human_size(st.system_bytes),
                                            st.skipped))
                    # 写入缓存：之后切回该目标不再重新扫描
                    if not st.error:
                        self._search_index = None          # 有新数据了，搜索索引要重建
                        save_scan_cache(self.scanner)      # 同时落盘，关掉软件也不丢
                        key = os.path.normcase(os.path.normpath(self.scanner.root))
                        self._cache[key] = self.scanner
                        self._cache_ts[key] = time.strftime("%H:%M:%S")
                        self._cache.move_to_end(key)
                        while len(self._cache) > self.cache_max:
                            old = next(iter(self._cache))
                            del self._cache[old]
                            self._cache_ts.pop(old, None)
                self.result = self.scanner
                self.current_path = self.scanner.root
                self.btn_up.config(state="disabled")
                self.lbl_path.config(text="当前: %s" % self.current_path)
                self.lbl_scaninfo.config(text="共 %s 个文件 · %s 个目录 · 合计 %s    |    隐藏 %s 个/%s · 系统 %s 个/%s" %
                                         ("{:,}".format(st.total_files), "{:,}".format(st.total_dirs),
                                          human_size(st.total),
                                          "{:,}".format(st.hidden_files), human_size(st.hidden_bytes),
                                          "{:,}".format(st.system_files), human_size(st.system_bytes)))
                self._refresh_views()
                self._rank_reset(animate=True)
                self._refresh_health()
                # 扫描期间用户切过目标：这边一停就立刻同步过去
                if getattr(self, "_sync_pending", False):
                    self._sync_pending = False
                    self.after(60, self._sync_target)
        finally:
            self.after(120, self._poll_scan)

    # ---------------- 磁盘健康（S.M.A.R.T. / Storage 健康度） ----------------
    def _refresh_health(self, root=None):
        if root is None:
            sc = getattr(self, "scanner", None)
            root = sc.root if sc else None
        if not root:
            return
        self._health_pending = True
        def work():
            self._health_result = self._read_health_blocking(root)
        threading.Thread(target=work, daemon=True).start()
        self._poll_health()

    def _poll_health(self):
        if getattr(self, "_health_pending", False) and hasattr(self, "_health_result"):
            self._health_pending = False
            self._apply_health(self._health_result)
            del self._health_result
            return
        if getattr(self, "_health_pending", False):
            self.after(400, self._poll_health)

    def _read_health_blocking(self, root):
        letter = os.path.splitdrive(root)[0].rstrip(":")
        if not letter:
            return None
        ps = (
            "$d='%s'; try {"
            "$part = Get-Partition -DriveLetter $d -ErrorAction Stop; "
            "$pd = Get-PhysicalDisk | Where-Object DeviceID -eq $part.DiskNumber; "
            "$rc = $pd | Get-StorageReliabilityCounter -ErrorAction SilentlyContinue; "
            "[PSCustomObject]@{Name=$pd.FriendlyName; Media=$pd.MediaType; Health=$pd.HealthStatus; "
            "Size=$pd.Size; Wear=$rc.Wear; Temp=$rc.Temperature; POH=$rc.PowerOnHours} | ConvertTo-Json -Compress"
            "} catch { '' }"
        ) % letter
        try:
            out = subprocess.run(["powershell", "-NoProfile", "-Command", ps],
                                 capture_output=True, text=True, timeout=15,
                                 creationflags=0x08000000)
            txt = (out.stdout or "").strip()
            if not txt:
                return None
            data = json.loads(txt)
            wear = data.get("Wear")
            health = str(data.get("Health", "")).lower()
            if "unhealthy" in health:
                pct = 0
            elif "warning" in health:
                pct = 40
            elif wear is not None:
                try:
                    pct = max(0, 100 - int(wear))
                except (TypeError, ValueError):
                    pct = 100
            else:
                pct = 100
            return {"pct": pct, "name": str(data.get("Name", "")),
                    "media": str(data.get("Media", "")),
                    "temp": data.get("Temp"), "poh": data.get("POH"), "wear": wear}
        except Exception:
            return None

    def _apply_health(self, info):
        if not info:
            self.lbl_health.config(text="磁盘健康 --")
            self._health_tip = "无法读取磁盘健康信息（可能需要管理员权限）"
            return
        pct = info["pct"]
        color = "#27ae60" if pct >= 90 else ("#e6a23c" if pct >= 60 else "#e74c3c")
        t = info.get("temp")
        ttxt = "" if t in (None, "") else " · %s°C" % t
        self.lbl_health.config(text="磁盘健康 %d%%%s" % (pct, ttxt), foreground=color)
        tip = "%s\u000a类型: %s\u000a健康度: %d%%" % (info["name"], info["media"], pct)
        if info["temp"] not in (None, ""):
            tip += "\u000a温度: %s\u00b0C" % info["temp"]
        if info["poh"] not in (None, ""):
            tip += "\u000a通电时间: %s 小时" % info["poh"]
        if info["wear"] not in (None, ""):
            tip += "\u000aSSD 磨损: %s%%" % info["wear"]
        self._health_tip = tip

    def _health_enter(self, ev):
        if not self._health_tip:
            return
        if self.tooltip is None:
            self.tooltip = tk.Toplevel(self)
            self.tooltip.wm_overrideredirect(True)
            self.tooltip.wm_attributes("-topmost", True)
            self._tip_lbl = tk.Label(self.tooltip, text="", justify="left", bg="#2c3e50",
                                     fg="white", font=("Microsoft YaHei UI", 9),
                                     padx=8, pady=6, wraplength=360)
            self._tip_lbl.pack()
        self._tip_lbl.config(text=self._health_tip)
        px, py = ev.x_root + 12, ev.y_root + 12
        self.tooltip.geometry("+%d+%d" % (px, py))
        self.tooltip.deiconify()

    def _health_leave(self, ev):
        if self.tooltip is not None:
            self.tooltip.withdraw()

    # ---------------- 磁盘健康（S.M.A.R.T. / Storage 健康度） ----------------

    def _on_tree_configure(self, _ev):
        """画布尺寸变了就重画（防抖 150ms，别在拖窗口的过程中疯狂重绘）。"""
        after = getattr(self, "_tree_resize_after", None)
        if after:
            self.after_cancel(after)
        self._tree_resize_after = self.after(150, self._render_tree)

    def _refresh_views(self):
        self._render_tree()
        self._fill_child_tree()
        self._render_type_tab()
        self._fill_big_files()

    # ---------------- 树图 ----------------
    def _folder_colors(self, gd):
        """仅剩右侧列表/排行等旧调用点在用；树图已改用 _folder_colors / TYPE_GROUPS。"""
        color = TYPE_GROUPS[gd][1]
        if self.theme == "dark":
            return _blend(color, 0.58, self.t["canvas"]), _blend(color, 0.32)
        return _blend(color, 0.86), color

    def _dominant(self, rec):
        gs = rec["groups"]
        m = max(gs)
        if m <= 0:
            return len(TYPE_GROUPS) - 1
        return gs.index(m)

    def _children_with_size(self, path, rec):
        """返回 [(child_index, name, size, is_dir, group, flags)]，目录大小取已汇总值"""
        out = []
        for i, ch in enumerate(rec["children"]):
            name, sz, is_dir, g, flags = ch
            if is_dir:
                crec = self.result.folders.get(os.path.join(path, name))
                size = crec["size"] if crec else 0
            else:
                size = sz
            out.append((i, name, size, is_dir, g, flags))
        return out

    def _render_tree(self):
        c = self.tree_canvas
        c.delete("all")
        self._draw_items = []
        if not self.result or not self.current_path:
            c.create_text(max(c.winfo_width() // 2, 60), max(c.winfo_height() // 2, 30),
                          text="选择目标后点击「开始扫描」", fill=self.t["muted"])
            return
        if self.result.folders.get(self.current_path) is None:
            return
        cw, ch = self._canvas_size()
        # 画布在未显示标签页里时只有兜底尺寸 50x50；真正显示后要重置世界坐标，
        # 否则旧坐标会把所有方块放大到屏外（只剩一个块）
        # 画布尺寸变了要把"视窗"一起处理好，否则内容会被拉伸放大而不是显示更多：
        #   原来就是全视图 -> 直接扩成新尺寸（窗口变大 = 看到更多）
        #   原来是放大过的 -> 按比例跟着缩放（保持相对视野）
        prev = getattr(self, "_world_canvas", None)
        if prev and (abs(prev[0] - cw) > 1 or abs(prev[1] - ch) > 1):
            w = self._world
            was_full = (w is None or (abs(w[0]) < 0.5 and abs(w[1]) < 0.5
                                      and abs(w[2] - prev[0]) < 1 and abs(w[3] - prev[1]) < 1))
            if was_full:
                self._world = (0.0, 0.0, float(cw), float(ch))
            else:
                sx = cw / float(prev[0] or 1)
                sy = ch / float(prev[1] or 1)
                self._world = (w[0] * sx, w[1] * sy, w[2] * sx, w[3] * sy)
        self._world_canvas = (cw, ch)
        if self._world is None or (self._world[2] <= 50.5 and cw > 50):
            self._world = (0.0, 0.0, float(cw), float(ch))
        wx, wy, ww, wh = self._world
        if ww <= 0 or wh <= 0:
            return

        theme = self.theme
        animating = self._animating
        # 文字**始终**要画：否则动画期间一片空白（就是"打开文件夹一瞬间没有字"）。
        # 但动画帧只给够大的格子画 —— Tk 的 create_text 约 0.5ms/个，
        # 全画要 145ms(≈7帧/秒)，只标大格子既看得见字又保得住帧率。
        big_only = animating and not getattr(self, "_anim_first", False)
        draw_labels = True
        # 动画中降到低保真、而且**不画文字**：create_text 占了大头，
        # 12 帧全量重画会掉到十几帧。动画结束后会再用完整预算重绘一次。
        budget = [SM_ANIM_TILES if animating else SM_MAX_TILES]
        # 布局只算一次：缩放动画期间 current_path / cw / ch / animating 都不变，
        # nested_layout 的结果逐帧完全相同，变的只有 _world（观察窗口）。
        # 之前每帧重算 squarify 约 68ms，缓存后动画帧只剩"画矩形"，帧率能上到几十。
        # 缓存是单槽的，key 含 current_path 和 animating，所以切目录/动画结束都会自动换 key 重算。
        _ck = (self.current_path, cw, ch, animating)
        _lc = getattr(self, "_layout_cache", None)
        if _lc is not None and _lc[0] == _ck:
            boxes = _lc[1]
        else:
            boxes = nested_layout(self.result.folders, self.current_path, 0, 0, cw, ch, budget)
            self._layout_cache = (_ck, boxes)
        scale = cw / ww
        # 字号压小一档、下限放到 6：这样小格子也能容下字，不再大片空白
        fs = max(6, min(16, int(8 * scale)))
        fs_sub = max(6, fs - 1)
        fname = "Microsoft YaHei UI"
        # 按**实际像素宽度**决定截不截，而不是按每个字 14.5px 猜。
        # 原来英文名被严重高估（"JetBrains" 实测约 50px，却被算成 130px），
        # 所以格子明明放得下也照样出省略号。
        try:
            import tkinter.font as _tkfont
            _fnt = _tkfont.Font(family=fname, size=fs)
            _fnt_s = _tkfont.Font(family=fname, size=fs_sub)
        except Exception:      # noqa: BLE001
            _fnt = _fnt_s = None

        def fit(txt, fnt, maxpx):
            """放得下就原样返回（不加省略号）；放不下才按实际宽度二分截断。"""
            if fnt is None:
                return _clip(txt, maxpx)
            if maxpx <= 4:
                return ""
            if fnt.measure(txt) <= maxpx:
                return txt
            lo, hi = 0, len(txt)
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if fnt.measure(txt[:mid] + "…") <= maxpx:
                    lo = mid
                else:
                    hi = mid - 1
            return (txt[:lo] + "…") if lo > 0 else ""
        # 按面积挑出"要标字"的格子，只标最大的 N 个。
        # Tk 的 create_text 约 0.5ms/个：System32 这种规模下"凡是够大的都标"会有 900+ 个、
        # 单帧 480ms（画面就是"有框没字"）。按面积取前 N 个，保证标出来的都是看得清的大格子，
        # 渲染时间按比例下降。
        _max_lab = SM_ANIM_LABELS if big_only else SM_MAX_LABELS
        _order = sorted(range(len(boxes)),
                        key=lambda i: -(boxes[i][6][2] * boxes[i][6][3]))
        label_set = set()
        for _i in _order:
            if len(label_set) >= _max_lab:
                break
            _bw, _bh = boxes[_i][6][2], boxes[_i][6][3]
            if _bw >= 26 and _bh >= 15:
                label_set.add(_i)
        label_fg = SPACEMAP_LABEL.get(theme) or SPACEMAP_LABEL["dark"]
        head_fg = SPACEMAP_HEADER.get(theme) or SPACEMAP_HEADER["dark"]
        use_type = getattr(self, "tree_color_mode", "depth") == "type"
        badges = []          # 隐藏/系统的整格描边，最后统一画，免得被子块盖住
        self._draw_items = []

        for _bi, (path, name, size, is_dir, gd, flags, (lx, ly, lw, lh), depth, container) in enumerate(boxes):
            x = (lx - wx) / ww * cw
            y = (ly - wy) / wh * ch
            w = lw / ww * cw
            h = lh / wh * ch
            if w < SM_MIN_TILE or h < SM_MIN_TILE:
                continue
            # 每层内缩 0.5px（相邻两块共 1px），露出的父级底色就是网格线
            inset = 0.0 if depth == 0 else SM_PAD / 2.0
            x1, y1 = x + inset, y + inset
            x2, y2 = x + w - inset, y + h - inset
            if x2 - x1 < 0.6 or y2 - y1 < 0.6:
                continue

            if is_dir:
                if use_type:
                    # 「按文件类型」：文件夹铺内容主类型色（和圆环图/图例同一套）
                    fill, bcol = self._folder_colors(gd)
                    c.create_rectangle(x1, y1, x2, y2, fill=fill, outline="")
                    if draw_labels and _bi in label_set and container and lw >= SM_MIN_FRAME_W and lh >= SM_MIN_FRAME_H:
                        c.create_text(x1 + 4, y1 + SM_HEADER_H / 2.0,
                                      text=fit(name, _fnt, w - 12), anchor="w", fill=bcol,
                                      font=(fname, fs, "bold"))
                    elif not container:
                        c.create_rectangle(x1 + 0.5, y1 + 0.5, x2 - 0.5, y2 - 0.5, outline=bcol)
                else:
                    # 「按层级」：底色逐层递进；不再细分的用内容主类型色混一点进来
                    if container:
                        # 顶层帧给一圈更亮的描边，一级目录之间一眼能分开
                        edge = sm_frame_edge(theme, depth) if depth <= 1 else ""
                        c.create_rectangle(x1, y1, x2, y2,
                                           fill=sm_frame_color(theme, depth),
                                           outline=edge, width=2 if depth <= 1 else 1)
                        if draw_labels and _bi in label_set and lw >= SM_MIN_FRAME_W and lh >= SM_MIN_FRAME_H:
                            # 标题带单独铺一层底色，像窗口标题栏：
                            # 每层"名字 + 内容"的边界就看得见了，层数一眼能数出来
                            c.create_rectangle(x1, y1, x2, y1 + SM_HEADER_H,
                                               fill=sm_header_bg(theme, depth), outline="")
                            c.create_text(x1 + 4, y1 + SM_HEADER_H / 2.0,
                                          text=fit(name, _fnt, w - 12), anchor="w", fill=head_fg,
                                          font=(fname, fs, "bold"))
                    else:
                        c.create_rectangle(x1, y1, x2, y2,
                                           fill=sm_leaf_folder_color(theme, gd, depth), outline="")
            else:
                if use_type:
                    c.create_rectangle(x1, y1, x2, y2, fill=TYPE_GROUPS[gd][1], outline="")
                    tfg = "white"
                else:
                    c.create_rectangle(x1, y1, x2, y2, fill=sm_file_color(theme, gd), outline="")
                    tfg = label_fg
                cx, cy = (x1 + x2) / 2.0, (y1 + y2) / 2.0
                if draw_labels and _bi in label_set and w >= 22 and h >= 18:
                    c.create_text(cx, cy - 7, text=fit(name, _fnt, w - 6),
                                  fill=tfg, font=(fname, fs))
                    c.create_text(cx, cy + 7, text=fit(human_size(size), _fnt_s, w - 6),
                                  fill=tfg, font=(fname, fs_sub))
                elif draw_labels and _bi in label_set and w >= 8 and h >= 10:
                    c.create_text(cx, cy, text=fit(name, _fnt, w - 4),
                                  fill=tfg, font=(fname, fs))

            # 隐藏=黄 / 系统=红 / 两者都有=橙。整格描边比原来的 7px 小圆点显眼得多
            if flags & 3:
                bcol2 = "#e67e22" if (flags & 3) == 3 else ("#f1c40f" if flags & 1 else "#e74c3c")
                badges.append((x1, y1, x2, y2, bcol2, flags))
            self._draw_items.append((path, name, size, is_dir, gd, flags,
                                     (lx, ly, lw, lh), (x, y, w, h), depth, container))
        # 隐藏/系统：整格描边 + 右上角「隐」「系」徽章。放最后画，保证不被子块盖掉
        for bx1, by1, bx2, by2, bcol2, bflags in badges:
            c.create_rectangle(bx1 + 1, by1 + 1, bx2 - 1, by2 - 1,
                               outline=bcol2, width=2)
            if draw_labels and not big_only and (bx2 - bx1) >= 26 and (by2 - by1) >= 17:
                tx = bx2 - 4
                for bit, ch, bgc, fgc in ((2, "系", "#e74c3c", "#ffffff"),
                                          (1, "隐", "#f1c40f", "#1a1a1a")):
                    if bflags & bit:
                        tx -= 15
                        c.create_rectangle(tx, by1 + 4, tx + 13, by1 + 17,
                                           fill=bgc, outline="")
                        c.create_text(tx + 6.5, by1 + 10.5, text=ch, fill=fgc,
                                      font=(fname, 7, "bold"))

        # 树图导航条
        if getattr(self, "lbl_tree_path", None) is not None:
            self.lbl_tree_path.config(text="当前：%s" % (self.current_path or ""))
            can_up = bool(self.result and self.current_path
                          and self.current_path != self.result.root)
            self.btn_tree_up.config(state="normal" if can_up else "disabled")
            self.lbl_tree_hint.config(text="双击方块进入 · 双击空白返回")

        # 白色悬停框：常驻一个矩形项，鼠标移动时**只改坐标、不重绘整帧**，所以是实时的。
        # 用白色描边（不是点击那种蓝色光晕），鼠标到哪框哪。
        try:
            self._hover_rect = c.create_rectangle(0, 0, 0, 0, outline="#ffffff",
                                                  width=2, state="hidden")
            c.tag_raise(self._hover_rect)
        except tk.TclError:
            self._hover_rect = None
        self._set_hover(getattr(self, "_hover_idx", None))

    def _set_hover(self, idx):
        """把白色悬停框挪到第 idx 个方块上。

        这个 idx 必须和 tooltip 用的是**同一个**（都在 _show_tooltip 里算），
        否则两者会指向不同格子 —— 之前就是这么错的。
        """
        rid = getattr(self, "_hover_rect", None)
        if rid is None:
            return
        if idx is None or not (0 <= idx < len(self._draw_items)):
            try:
                self.tree_canvas.itemconfigure(rid, state="hidden")
            except tk.TclError:
                pass
            return
        x, y, w, h = self._draw_items[idx][7]
        try:
            self.tree_canvas.coords(rid, x + 1, y + 1, x + w - 1, y + h - 1)
            self.tree_canvas.itemconfigure(rid, state="normal")
            self.tree_canvas.tag_raise(rid)
        except tk.TclError:
            pass

    def _hit(self, ev):
        """命中当前帧最深的方块，返回 self._draw_items 下标。

        嵌套布局下文件夹内部会被子块铺满，只靠标题带进下一层太难点。
        所以额外给文件夹框加一圈 3px 的"边框热区"：落点贴着哪一层框的边，
        就认那一层，双击它即可下钻（和 SpaceSniffer 点边框进下一层是一个意思）。
        """
        deepest = None
        for idx in range(len(self._draw_items) - 1, -1, -1):
            _p, _n, _s, _d, _g, _f, _lr, (x, y, w, h), _dp, _ic = self._draw_items[idx]
            if x <= ev.x <= x + w and y <= ev.y <= y + h:
                deepest = idx
                break
        if deepest is None:
            return None
        # 边框热区：从最外层往里找，第一个"边缘落在热区内"的文件夹框胜出。
        # 优先外层是符合直觉的——你贴着哪条边框，想抓的就是那个框；
        # 深度 0 的根框除外（它等同于"返回上级"，见 _on_double）。
        edge = 3.0
        for idx in range(len(self._draw_items)):
            _p, _n, _s, _d, _g, _f, _lr, (x, y, w, h), _dp, _ic = self._draw_items[idx]
            if not _ic or _dp == 0:
                continue
            if (x <= ev.x <= x + w and y <= ev.y <= y + h and
                    (ev.x - x <= edge or x + w - ev.x <= edge or
                     ev.y - y <= edge or y + h - ev.y <= edge)):
                return idx
        return deepest

    def _on_motion(self, ev):
        if self._animating:
            self._hide_tooltip()
            return
        self._show_tooltip(ev)

    def _tree_leave(self, _ev):
        self._hide_tooltip()
        self._hover_idx = None
        self._set_hover(None)

    def _show_tooltip(self, ev):
        idx = self._hit(ev)
        self._hover_idx = idx          # 记住给悬停框用
        self._set_hover(idx)
        if idx is None:
            self._hide_tooltip()
            return
        path, name, size, is_dir, g, flags, _lr, _cr, _dp, _ic = self._draw_items[idx]
        attr_txt = ""
        if flags & 1:
            attr_txt = "隐藏文件 · "
        if flags & 2:
            attr_txt = "系统文件 · "
        if flags & MERGED_FLAG:
            txt = "%s\n%s\n已合并 %s 个过小项（文件/小文件夹，拼图式显示）\n查看明细: 右侧「当前目录内容」或「大目录排行」\n%s" % (
                name, human_size(size), name.replace("其他 ", "").replace(" 项", ""), path)
        elif is_dir:
            crec = self.result.folders.get(path)
            if crec:
                gd = _dominant_of(crec)
                txt = ("%s\n%s\n%s%s 个文件 · 内容以「%s」为主\n%s" %
                       (name, human_size(size), attr_txt, "{:,}".format(crec["nfiles"]),
                        TYPE_GROUPS[gd][0], path))
            else:
                txt = "%s\n%s\n%s%s" % (name, human_size(size), attr_txt, path)
        else:
            ext = os.path.splitext(name)[1].lstrip(".").lower() or "无扩展名"
            txt = "%s\n%s\n%s类型: %s（.%s）\n%s" % (
                name, human_size(size), attr_txt, TYPE_GROUPS[g][0], ext, path)
        self._show_tooltip_at(txt, ev)

    def _show_tooltip_at(self, text, ev):
        if self.tooltip is None:
            self.tooltip = tk.Toplevel(self)
            self.tooltip.wm_overrideredirect(True)
            self.tooltip.wm_attributes("-topmost", True)
            self._tip_lbl = tk.Label(self.tooltip, text="", justify="left", bg="#2c3e50",
                                     fg="white", font=("Microsoft YaHei UI", 9),
                                     padx=8, pady=6, wraplength=460)
            self._tip_lbl.pack()
        self._tip_lbl.config(text=text)
        px, py = ev.x_root + 14, ev.y_root + 14
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        if px + 460 > sw:
            px = ev.x_root - 480
        if py + 240 > sh:
            py = ev.y_root - 260
        self.tooltip.geometry("+%d+%d" % (px, py))
        self.tooltip.deiconify()

    def _hide_tooltip(self):
        if self.tooltip is not None:
            self.tooltip.withdraw()

    def _canvas_size(self):
        c = self.tree_canvas
        return max(c.winfo_width(), 50), max(c.winfo_height(), 50)

    def _on_click(self, ev):
        idx = self._hit(ev)
        c = self.tree_canvas
        c.delete("sel")
        if idx is None:
            self._selected_path = None
            return
        path, name, size, is_dir, g, flags, _lr, (x, y, w, h), _dp, _ic = self._draw_items[idx]
        self._selected_path = path      # 只记状态，不再画蓝色选中框
        if flags & MERGED_FLAG:
            self.lbl_status.config(text="已合并块: %s 个小文件（合计 %s）· 查看明细请用右侧列表或大文件排行" %
                                   (name.replace("其他 ", "").replace(" 项", ""), human_size(size)))
            return
        kind = "文件夹" if is_dir else TYPE_GROUPS[g][0]
        attr = " · " + ("隐藏/系统" if flags == 3 else ("隐藏" if flags & 1 else "系统")) if flags else ""
        self.lbl_status.config(text="已选择: %s  （%s%s · %s）" % (path, kind, attr, human_size(size)))

    def _on_double(self, ev):
        if self._animating:
            return
        idx = self._hit(ev)
        # 嵌套布局下，根目录的"地图框"铺满整屏，任何一点都至少命中它。
        # 所以把"命中根框"等同于原来的"双击空白"——返回上级，
        # 否则双击空白返回这条路会被根框吃掉，只能靠按钮返回。
        if idx is None or self._draw_items[idx][8] == 0:
            self._go_up()
            return
        path, name, size, is_dir, g, flags, lrect, _cr, _dp, _ic = self._draw_items[idx]
        if is_dir:
            self._zoom_in(path, lrect)
        elif flags & MERGED_FLAG:
            self.lbl_status.config(text="合并块无法定位，请查看右侧列表或大文件排行")
        else:
            self._explorer_select(path)   # 双击文件 = 在文件管理器中定位（方便删除）

    # ---------------- 缩放导航（SpaceSniffer 式动画） ----------------
    def _safe_anim(self, fn):
        """包一层保险：动画帧里抛任何异常都强制收尾。

        上一版就是因为某个动画函数里有个 NameError，_animating 永远清不掉，
        整个树图再也点不动了。以后不管出什么错，最坏也只是动画中断，不会卡死。
        """
        try:
            return fn()
        except Exception:      # noqa: BLE001
            self._animating = False
            self._anim_t0 = None
            try:
                self._render_tree()
            except Exception:      # noqa: BLE001
                pass
            return None

    def _zoom_in(self, path, lrect):
        cw, ch = self._canvas_size()
        cur = self._world or (0.0, 0.0, float(cw), float(ch))
        target = tuple(float(v) for v in lrect)
        ani = getattr(self, "tree_anim", "smooth")
        if ani == "off":                      # 设置里关掉动画：直接跳过去
            self._world = target
            self._render_tree()
            return
        self._anim_ms = 110 if ani == "fast" else 220
        self._anim_t0 = None
        self._animating = True
        steps = 16
        def frame(i):
            if self._closed:
                return
            # 按真实经过时间算进度（不是按帧序号）：某帧渲染慢时总时长也不会被拖长，
            # 慢帧只是少画几帧 —— SpaceMap 就是这么做的
            if getattr(self, "_anim_t0", None) is None:
                self._anim_t0 = time.perf_counter()
            _e = min(1.0, (time.perf_counter() - self._anim_t0) * 1000.0
                     / max(getattr(self, "_anim_ms", 220), 1))
            t = (4 * _e * _e * _e) if _e < 0.5 else (1 - pow(-2 * _e + 2, 3) / 2.0)
            self._world = (cur[0] + (target[0] - cur[0]) * t,
                           cur[1] + (target[1] - cur[1]) * t,
                           cur[2] + (target[2] - cur[2]) * t,
                           cur[3] + (target[3] - cur[3]) * t)
            self._anim_first = (i == 0)
            self._safe_anim(self._render_tree)
            if _e < 1.0:
                self.after(1, lambda: frame(i + 1))   # 延迟是人为加的，去掉后帧率由渲染速度决定
            else:
                self._world = None
                self.current_path = path
                self._selected_path = None
                self.btn_up.config(state="normal")
                self.lbl_path.config(text="当前: %s" % path)
                # 必须先关掉动画标记再重绘！_render_tree 在 _animating 为真时只画低清版
                # （350 块、不画文字），之前 _animating=False 写在 _refresh_views() 之后，
                # 于是下钻完成后这张图永远停在低保真状态，只有重新扫描才会恢复。
                self._animating = False
                self._refresh_views()

        frame(0)

    def _zoom_out(self, path):
        """返回上级：从上级视图中定位当前目录，做反向缩放动画"""
        parent = os.path.dirname(path)
        if parent == path or parent not in self.result.folders:
            return False
        cw, ch = self._canvas_size()
        boxes = nested_layout(self.result.folders, parent, 0, 0, cw, ch)
        rect = None
        for b in boxes:
            if b[0] == path:
                rect = b[6]
                break
        if rect is None:
            return False
        ani = getattr(self, "tree_anim", "smooth")
        if ani == "off":                       # 关闭动画：返回也直接到位
            self.current_path = parent
            self._world = None
            self._selected_path = None
            self.btn_up.config(state="normal" if parent != self.result.root else "disabled")
            self.lbl_path.config(text="当前: %s" % parent)
            self._refresh_views()
            return True
        self._anim_ms = 110 if ani == "fast" else 220
        self._anim_t0 = None
        self._animating = True
        cur = tuple(float(v) for v in rect)
        target = (0.0, 0.0, float(cw), float(ch))
        steps = 16
        self.current_path = parent

        def frame(i):
            if self._closed:
                return
            # 按真实经过时间算进度（慢帧只少画几帧，不会把动画拖长）
            if getattr(self, "_anim_t0", None) is None:
                self._anim_t0 = time.perf_counter()
            _e = min(1.0, (time.perf_counter() - self._anim_t0) * 1000.0
                     / max(getattr(self, "_anim_ms", 220), 1))
            t = (4 * _e * _e * _e) if _e < 0.5 else (1 - pow(-2 * _e + 2, 3) / 2.0)
            self._world = (cur[0] + (target[0] - cur[0]) * t,
                           cur[1] + (target[1] - cur[1]) * t,
                           cur[2] + (target[2] - cur[2]) * t,
                           cur[3] + (target[3] - cur[3]) * t)
            self._anim_first = (i == 0)
            self._safe_anim(self._render_tree)
            if _e < 1.0:
                self.after(1, lambda: frame(i + 1))
            else:
                self._world = None
                self._selected_path = None
                self.btn_up.config(state="normal" if parent != self.result.root else "disabled")
                self.lbl_path.config(text="当前: %s" % parent)
                self._animating = False      # 同上：先解除低清模式再重绘
                self._refresh_views()

        frame(0)
        return True

    def _go_up(self):
        if not self.current_path or self._animating:
            return
        if not self._zoom_out(self.current_path):
            # 当前目录在上级视图中被合并或不存在时，回退到其直接上级
            parent = os.path.dirname(self.current_path)
            if parent != self.current_path and parent in self.result.folders:
                self.current_path = parent
                self.btn_up.config(state="normal" if parent != self.result.root else "disabled")
            else:
                self.current_path = self.result.root
                self.btn_up.config(state="disabled")
            self._world = None
            self._selected_path = None
            self.lbl_path.config(text="当前: %s" % self.current_path)
            self._refresh_views()

    def _enter(self, name):
        p = os.path.join(self.current_path, name)
        if self.result.folders.get(p) is None:
            return
        self.current_path = p
        self._world = None
        self._selected_path = None
        self.btn_up.config(state="normal")
        self._refresh_views()
        self.lbl_path.config(text="当前: %s" % p)

    # ---------------- 右侧列表 / 其他标签页 ----------------
    def _fill_child_tree(self):
        t = self.child_tree
        t.delete(*t.get_children())
        self._child_map = {}
        if not self.result or not self.current_path:
            return
        rec = self.result.folders.get(self.current_path)
        if rec is None:
            return
        total = rec["size"] or 1
        rows = self._children_with_size(self.current_path, rec)
        rows = [r for r in rows if r[2] > 0]
        rows.sort(key=lambda r: -r[2])
        for i, name, size, is_dir, g, flags in rows:
            marker = ""
            if flags & 1:
                marker += "·隐藏"
            if flags & 2:
                marker += "·系统"
            tname = ("文件夹" if is_dir else TYPE_GROUPS[g][0]) + marker
            iid = t.insert("", "end", values=(name, human_size(size),
                                              "%.1f%%" % (size / total * 100), tname))
            self._child_map[iid] = (name, is_dir, flags)

    # ---------------- 类型分布（可逐级下钻） ----------------
    #
    # 视图栈交替两种视图，于是能一路点下去：
    #   ("dir", path)        当前目录的「按类型」分布          → 点类型下钻
    #   ("bytype", path, gi) path 里「类型 gi」由哪些子项构成  → 点文件夹下钻
    # 例：C:\ → 视频 → Users → 视频 → …（以此类推）
    def _type_reset(self):
        if not hasattr(self, "type_stack"):
            self.type_stack = []
        base = self.type_stack[0][1] if self.type_stack else None
        if base != self.current_path:
            self.type_stack = [("dir", self.current_path)]

    def _type_back(self):
        stack = getattr(self, "type_stack", None)
        if stack and len(stack) > 1:
            stack.pop()
            self._render_type_tab()

    def _type_activate(self, payload):
        kind = payload[0]
        if kind == "type":
            self.type_stack.append(("bytype", self.type_stack[-1][1], payload[1]))
            self._render_type_tab()
        elif kind == "dir":
            self.type_stack.append(("dir", payload[1]))
            self._render_type_tab()
        elif kind == "file":
            self._explorer_select(payload[1])
        else:
            self.lbl_status.config(text="合并块：明细请看右侧「当前目录内容」或大文件排行")

    def _on_type_click(self, ev):
        # 先看图例行 / 条形（都是矩形热区），再看扇形
        for payload, (x1, y1, x2, y2) in getattr(self, "_type_boxes", []):
            if x1 <= ev.x <= x2 and y1 <= ev.y <= y2:
                self._type_activate(payload)
                return
        pie = getattr(self, "_type_pie", None)
        if pie and pie[4]:
            import math
            cx, cy, r, ring_w, slices = pie
            dx, dy = ev.x - cx, ev.y - cy
            dist2 = dx * dx + dy * dy
            # 圆环：只认环带上的点击，中心留白不算
            inner = max(r - ring_w / 2.0 - 3, 0)
            outer = r + ring_w / 2.0 + 3
            if inner * inner <= dist2 <= outer * outer:
                ang = math.degrees(math.atan2(-dy, dx)) % 360.0
                for start, span, payload in slices:
                    # 环段从 start 起顺时针 span 度
                    if (start - ang) % 360.0 <= span:
                        self._type_activate(payload)
                        return

    def _render_type_tab(self):
        cv = self.type_canvas
        after = getattr(self, "_type_anim_after", None)
        if after:                       # 上一轮的生长动画要先停掉，否则会往已删除的项上写坐标
            self.after_cancel(after)
            self._type_anim_after = None
        cv.delete("all")
        self._type_boxes = []
        self._type_pie = None
        if not self.result or not self.current_path:
            cv.create_text(max(cv.winfo_width() // 2, 60), max(cv.winfo_height() // 2, 30),
                           text="扫描后显示类型分布", fill=self.t["muted"])
            cv.configure(scrollregion=cv.bbox("all"))
            return
        self._type_reset()
        view = self.type_stack[-1]
        rec = self.result.folders.get(view[1])
        if rec is None:
            return

        # rows: (点击负载, 名称, 字节, 颜色, 副标题)
        rows = []
        if view[0] == "dir":
            total = rec["size"]
            gcounts = rec["gcounts"]
            for i, b in enumerate(rec["groups"]):
                if b > 0:
                    rows.append((("type", i), TYPE_GROUPS[i][0], b,
                                 sm_file_color(self.theme, i),
                                 "%s 个文件" % "{:,}".format(gcounts[i])))
            rows.sort(key=lambda r: -r[2])
            title = "类型分布 · %s" % (os.path.basename(view[1]) or view[1])
            nfiles = rec["nfiles"]
        else:
            gi = view[2]
            items = []
            for name, sz, is_dir, g, _flags in rec["children"]:
                cpath = os.path.join(view[1], name)
                if is_dir:
                    crec = self.result.folders.get(cpath)
                    b = crec["groups"][gi] if crec else 0
                else:
                    b = sz if g == gi else 0
                if b > 0:
                    items.append((cpath, name, b, is_dir))
            items.sort(key=lambda t: -t[2])
            keep, rest = items[:TYPE_CHILD_MAX], items[TYPE_CHILD_MAX:]
            for i, (cpath, name, b, is_dir) in enumerate(keep):
                rows.append((("dir", cpath) if is_dir else ("file", cpath), name, b,
                             sm_cat_color(self.theme, i), "文件夹" if is_dir else "文件"))
            if rest:
                rows.append((("merged", 0), "其他 %d 项" % len(rest),
                             sum(t[2] for t in rest), self.t["muted"], "已合并"))
            total = sum(t[2] for t in items)
            nfiles = len(items)
            title = "%s · %s 由什么构成" % (TYPE_GROUPS[gi][0],
                                            os.path.basename(view[1]) or view[1])

        # 导航条
        crumbs = []
        for v in self.type_stack:
            if v[0] == "dir":
                crumbs.append(os.path.basename(v[1]) or v[1])
            else:
                crumbs.append(TYPE_GROUPS[v[2]][0])
        self.lbl_type_path.config(text=" › ".join(crumbs))
        self.btn_type_back.config(state="normal" if len(self.type_stack) > 1 else "disabled")

        if not rows or total <= 0:
            cv.create_text(max(cv.winfo_width() // 2, 60), max(cv.winfo_height() // 2, 30),
                           text="这里没有内容", fill=self.t["muted"])
            cv.configure(scrollregion=cv.bbox("all"))
            return

        W = max(cv.winfo_width() - 40, 120)
        cv.create_text(20, 16, text=title, anchor="w", fill=self.t["text"],
                       font=("Microsoft YaHei UI", 10, "bold"))

        # ---- 圆环图 + 贴着圆放的标注（标注本身也是点击热区） ----
        import math
        avail = max(cv.winfo_width(), 720)
        pie_cx = min(max(avail * 0.5, 240), 470)
        pie_cy = int(178 * UI_SCALE)
        pie_r, ring_w = int(108 * UI_SCALE), int(30 * UI_SCALE)
        r_out = pie_r + ring_w / 2.0
        r_in = pie_r - ring_w / 2.0
        slices = []
        labels = []          # [右侧?, y, payload, 文本, 引线起点x, 引线起点y]
        a0 = 90.0
        for payload, name, b, color, _sub in rows:
            span = b / total * 360.0
            if span < 1.0:
                # 太细的段画不出来也看不见（Tk 上还容易被画成整圆），跳过
                a0 -= span
                continue
            a_end = a0 - span
            # 两端各让 0.25° 重叠，接缝处不会露出底色
            cv.create_polygon(ring_points(pie_cx, pie_cy, r_out, r_in, a0 + 0.25, a_end - 0.25),
                              fill=color, outline="", smooth=False)
            slices.append((a0, span, payload))

            rad = math.radians(a0 - span / 2.0)
            right = math.cos(rad) >= 0
            labels.append([right, pie_cy - (r_out + 12) * math.sin(rad), payload,
                           "%s  %s · %.1f%%" % (name, human_size(b), b / total * 100.0),
                           pie_cx + (r_out + 2) * math.cos(rad),
                           pie_cy - (r_out + 2) * math.sin(rad)])
            a0 -= span

        # 标注字号（跟着 DPI 缩放）+ 按**实际像素宽度**裁剪的辅助函数。
        # 原来的 _clip 是按「每字 14.5px」猜的，跟字号无关 —— 字号一调大就溢出被截；
        # 而且两侧写死 300/290px，窗口更宽也不多显示。
        _lsz = max(9, int(round(10 * UI_SCALE)))
        try:
            import tkinter.font as _tkfont
            _lf = _tkfont.Font(family="Microsoft YaHei UI", size=_lsz)
        except Exception:      # noqa: BLE001
            _lf = None

        def lfit(t2, maxpx):
            """放得下就原样返回（不加省略号）；放不下才按实际宽度二分截断。"""
            if maxpx <= 10:
                return ""
            if _lf is None:
                return _clip(t2, maxpx)
            try:
                if _lf.measure(t2) <= maxpx:
                    return t2
                lo, hi = 0, len(t2)
                while lo < hi:
                    mid = (lo + hi + 1) // 2
                    if _lf.measure(t2[:mid] + "…") <= maxpx:
                        lo = mid
                    else:
                        hi = mid - 1
                return (t2[:lo] + "…") if lo > 0 else ""
            except tk.TclError:
                return _clip(t2, maxpx)

        cv_w = max(cv.winfo_width(), 720)
        # 同一侧的标注按 y 排开，免得小切片挤成一团看不清（10pt 行高约 16，留 18）
        for side in (True, False):
            col = sorted((L for L in labels if L[0] == side), key=lambda L: L[1])
            gap = 18.0
            for i in range(1, len(col)):
                if col[i][1] - col[i - 1][1] < gap:
                    col[i][1] = col[i - 1][1] + gap
            for _side, ly, payload, txt, sx, sy in col:
                lx = pie_cx + r_out + 14 if side else pie_cx - r_out - 14
                # 折线改成平滑曲线：Tk 画斜直线是硬锯齿，弯一点既好看也不显毛边
                mx = (sx + lx) / 2.0
                cv.create_line(sx, sy, mx, sy, mx, ly, lx, ly,
                               fill=self.t["muted"], smooth=True, splinesteps=12)
                # 用画布的实际剩余宽度，而不是写死的 300 —— 窗口越宽显示越完整
                avail_px = (cv_w - lx - 16) if side else (lx - 12)
                item = cv.create_text(lx + (4 if side else -4), ly, anchor="w" if side else "e",
                                      text=lfit(txt, avail_px),
                                      fill=self.t["text"],
                                      font=("Microsoft YaHei UI", _lsz))
                self._type_boxes.append((payload, cv.bbox(item)))

        self._type_pie = (pie_cx, pie_cy, pie_r, ring_w, slices)
        cv.create_text(pie_cx, pie_cy - 6, text="合计", fill=self.t["muted"],
                       font=("Microsoft YaHei UI", 9))
        cv.create_text(pie_cx, pie_cy + 12, text=human_size(total), fill=self.t["text"],
                       font=("Microsoft YaHei UI", 9, "bold"))

        # ---- 条形图：直接套「文件夹排行」那套（浅色轨道 + 从左向右生长的胶囊条） ----
        y = max(pie_cy + pie_r + int(40 * UI_SCALE), int(320 * UI_SCALE))
        bar_h = int(30 * UI_SCALE)      # 比排行榜更粗，胶囊两端圆弧更明显
        track_x0 = 12.0
        track_x1 = max(cv.winfo_width() - 22.0, track_x0 + 160.0)
        maxb = rows[0][2]
        self._type_bars = []
        for payload, name, b, color, sub in rows:
            pct = b / total * 100 if total else 0.0
            cv.create_rectangle(20, y, 36, y + 16, fill=color, outline="")
            cv.create_text(44, y + 8, anchor="w", fill=self.t["text"],
                           text="%s  %s · %s · %.1f%%" % (name, human_size(b), sub, pct),
                           font=("Microsoft YaHei UI", 9))
            by0, by1 = y + 22.0 * UI_SCALE, y + 22.0 * UI_SCALE + bar_h
            rad = (by1 - by0) / 2.0
            cv.create_polygon(round_rect_points(track_x0, by0, track_x1, by1, rad),
                              fill=self.t["track"], outline="", smooth=True)
            # 条长 = 占总量的百分比，不是"相对最大值拉满" —— 48.6% 就该只有半条
            full = max((b / total) * (track_x1 - track_x0), 3.0)
            bar = cv.create_polygon(round_rect_points(track_x0, by0, track_x0 + 1, by1, rad),
                                    fill=color, outline="", smooth=True)
            self._type_bars.append({"bar": bar, "bx": track_x0, "by0": by0,
                                    "by1": by1, "w": full, "r": rad})
            self._type_boxes.append((payload, (10, y - 2, track_x1 + 60, by1 + 4)))
            y = by1 + 16 * UI_SCALE
        cv.create_text(20, y + 2, text="合计 %s（%s 个文件）" % (human_size(total),
                       "{:,}".format(nfiles)), anchor="w", fill=self.t["muted"],
                       font=("Microsoft YaHei UI", 9))
        cv.configure(scrollregion=cv.bbox("all"))
        self._type_bars_play()

        # 下钻视图再补一份「按扩展名」的构成 —— 「其他」这一类尤其需要：
        # 光看"其他 12.6 GB"没用，得一眼看出是被哪几个后缀吃掉的。
        if view[0] == "bytype":
            self._render_type_ext_section(cv, view[1], view[2], y + 30)

    def _ext_breakdown(self, path, gi):
        """某一类型在 path 子树里的「按扩展名」构成，按大小降序。

        结果缓存，避免每次重绘都递归遍历一遍整个子树。
        """
        cache = getattr(self, "_type_ext_cache", None)
        if cache is None:
            cache = self._type_ext_cache = {}
        key = (id(self.result), path, gi)
        hit = cache.get(key)
        if hit is not None:
            return hit
        agg = {}
        stack = [path]
        guard = 0
        while stack and guard < 400000:
            p = stack.pop()
            rec = self.result.folders.get(p)
            if rec is None:
                continue
            for name, sz, is_dir, g, _fl in rec["children"]:
                guard += 1
                if is_dir:
                    stack.append(os.path.join(p, name))
                elif g == gi and sz > 0:
                    ext = os.path.splitext(name)[1].lstrip(".").lower() or "(无扩展名)"
                    a = agg.get(ext)
                    if a is None:
                        agg[ext] = [sz, 1]
                    else:
                        a[0] += sz
                        a[1] += 1
        out = sorted(((e, v[0], v[1]) for e, v in agg.items()), key=lambda t: -t[1])
        cache[key] = out
        return out

    def _render_type_ext_section(self, cv, path, gi, y):
        exts = self._ext_breakdown(path, gi)
        if not exts:
            return
        W = max(cv.winfo_width() - 40, 120)
        cv.create_text(20, y, anchor="w", fill=self.t["text"],
                       text="按扩展名 · %s 这一类是被哪些后缀吃掉的" % TYPE_GROUPS[gi][0],
                       font=("Microsoft YaHei UI", 10, "bold"))
        y += 24
        shown = exts[:TYPE_EXT_MAX]
        tot = sum(e[1] for e in exts) or 1
        for i, (ext, b, cnt) in enumerate(shown):
            color = sm_cat_color(self.theme, i)
            label = ("." + ext) if ext != "(无扩展名)" else "无扩展名"
            cv.create_rectangle(20, y, 36, y + 16, fill=color, outline="")
            cv.create_text(44, y + 8, anchor="w", fill=self.t["text"],
                           text="%-16s %10s · %s 个文件 · %.1f%%" % (
                               label, human_size(b), "{:,}".format(cnt), b / tot * 100),
                           font=("Microsoft YaHei UI", 9))
            # 同样按占总量的比例画
            wb = max((b / tot) * W, 3)
            cv.create_polygon(round_rect_points(20, y + 22, 20 + wb, y + 22 + 24, 12),
                              fill=color, outline="", smooth=True)
            y += 22 + 24 + 12
        if len(exts) > len(shown):
            cv.create_text(20, y + 2, anchor="w", fill=self.t["muted"],
                           text="…另有 %d 种更小的扩展名" % (len(exts) - len(shown)),
                           font=("Microsoft YaHei UI", 9))

    def _type_bars_play(self):
        """条条从左向右生长：直接套排行榜那套（ease-out cubic + 逐行 20ms 延迟）。"""
        after = getattr(self, "_type_anim_after", None)
        if after:
            self.after_cancel(after)
            self._type_anim_after = None
        bars = getattr(self, "_type_bars", [])
        if not bars:
            return
        cv = self.type_canvas

        def put(w, width):
            cv.coords(w["bar"], *round_rect_points(w["bx"], w["by0"],
                                                   w["bx"] + max(width, 1.0), w["by1"], w["r"]))

        selected = False
        try:
            selected = "类型" in self.nb.tab(self.nb.select(), "text")
        except Exception:
            pass
        if not selected:
            # 标签页没在看，直接画到位；等切过来时 _on_tab_changed 会重画并放动画
            for w in bars:
                put(w, w["w"])
            return

        t0 = time.perf_counter()

        def tick():
            if self._closed:
                return
            now = (time.perf_counter() - t0) * 1000.0
            done = True
            for k, w in enumerate(bars):
                p = (now - min(k, 12) * 20.0) / RANK_ANIM_MS
                if p < 1:
                    done = False
                    p = max(p, 0.0)
                else:
                    p = 1.0
                ease = 1 - (1 - p) ** 3          # ease-out cubic
                put(w, w["w"] * ease)
            self._type_anim_after = None if done else self.after(RANK_FPS_MS, tick)

        tick()

    def _fill_big_files(self, animate=False):
        t = self.big_tree
        after = getattr(self, "_big_anim_after", None)
        if after:
            self.after_cancel(after)
            self._big_anim_after = None
        t.delete(*t.get_children())
        self._big_map = {}
        if not self.result:
            return
        items = []
        if self._big_mode.get() == "folder":
            # 按文件夹：占用最大的目录排行（可双击跳转）
            for size, path, name, parent, g, _nf in self.result.top_folders(DEFAULT_TOP_N):
                items.append(((human_size(size), name, "目录·" + TYPE_GROUPS[g][0], parent),
                              (path, True)))
        else:
            for size, path, name, g, flags in sorted(self.result.top_files, reverse=True):
                marker = ""
                if flags & 1:
                    marker += "·隐藏"
                if flags & 2:
                    marker += "·系统"
                items.append(((human_size(size), name, TYPE_GROUPS[g][0] + marker,
                               os.path.dirname(path)), (path, False)))
        if not items:
            t.insert("", "end", values=("", "（没有扫描结果）", "", ""))
            return
        # 筛选：按名称子串过滤（大小/位置不参与，避免误判）
        kw = getattr(self, "var_bigfilter", None)
        kw = kw.get().strip().lower() if kw is not None else ""
        if kw:
            items = [it for it in items if kw in str(it[0][1]).lower()]
            if not items:
                t.insert("", "end", values=("", "（没有匹配「%s」的项）" % kw, "", ""))
                return
        if not animate:
            for vals, info in items:
                self._big_map[t.insert("", "end", values=vals)] = info
            return
        # 逐批插入：比一次性灌进去更像"列表长出来"，大列表也不会卡一下
        chunk = max(1, len(items) // 12)
        pos = [0]

        def tick():
            if self._closed:
                return
            end = min(pos[0] + chunk, len(items))
            for k in range(pos[0], end):
                vals, info = items[k]
                self._big_map[t.insert("", "end", values=vals)] = info
            pos[0] = end
            self._big_anim_after = None if end >= len(items) else self.after(16, tick)

        tick()

    def _auto_combo(self):
        """启动后台把两个分析都跑一遍（都是线程，不挡界面）。"""
        try:
            if not getattr(self, "_clean_running", False):
                self._clean_scan()
            if not getattr(self, "_soft_running", False):
                self._soft_scan()
        except Exception:      # noqa: BLE001
            pass

    def _combo_hint(self, tree, lines):
        """空列表时给个说明，别让人打开就是两个空窗口不知道干啥的。"""
        if tree.get_children():
            return
        for ln in lines:
            tree.insert("", "end", text="", values=(ln, "", "", "", ""))

    # ---------------- SpaceMap 嵌入 ----------------
    @staticmethod
    def _spacemap_find():
        """找 SpaceMap 的窗口。

        不能用 FindWindowW 精确标题：SpaceMap 会把标题改成「D:\ - SpaceMap」，
        所以改成遍历顶层窗口、匹配标题里含 SpaceMap。
        """
        try:
            import ctypes
            from ctypes import wintypes
            u = ctypes.windll.user32
        except Exception:      # noqa: BLE001
            return 0
        hit = []

        def _cb(hwnd, _lp):
            try:
                # 注意：**不要**用 IsWindowVisible 过滤。
                # 预热时我们主动把窗口 SW_HIDE 了，加了可见性判断就再也找不到它，
                # 表现就是切到该标签页时报「没能抓到 SpaceMap 的窗口」。
                n = u.GetWindowTextLengthW(hwnd)
                if n <= 0:
                    return True
                buf = ctypes.create_unicode_buffer(n + 1)
                u.GetWindowTextW(hwnd, buf, n + 1)
                t = buf.value or ""
                if "SpaceMap" in t or t in SPACEMAP_TITLES:
                    hit.append(hwnd)
                    return False
            except Exception:      # noqa: BLE001
                pass
            return True

        try:
            u.EnumWindows(ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND,
                                             wintypes.LPARAM)(_cb), 0)
        except Exception:      # noqa: BLE001
            return 0
        return hit[0] if hit else 0

    def _spacemap_write_wanted(self, path=None):
        """告诉嵌入的 SpaceMap：现在该看哪个目录。

        写进 %LOCALAPPDATA%\\SpaceMap\\wanted.txt，SpaceMap 前端每 1.5 秒问一次
        （/wanted 路由），变了就原地切过去 —— 这样"软件扫哪个盘、树图就显示哪个盘"。
        """
        import json
        d = os.path.join(os.environ.get("LOCALAPPDATA", os.path.expanduser("~")), "SpaceMap")
        try:
            os.makedirs(d, exist_ok=True)
            with open(os.path.join(d, "wanted.txt"), "w", encoding="utf-8") as f:
                f.write((path if path is not None else (self.target or "")).strip().strip('"'))
        except OSError:
            pass
        _ = json

    @staticmethod
    def _spacemap_close_orphans():
        """开机清扫上一次留下的孤儿窗口。

        那个浏览器窗口是独立进程；如果关软件时没关掉它，就会一直留在屏幕外。
        只清**屏幕外**的 —— 用户自己打开的 SpaceMap 在屏幕内，不动。
        """
        try:
            import ctypes
            from ctypes import wintypes
            u = ctypes.windll.user32
        except Exception:      # noqa: BLE001
            return

        class RECT(ctypes.Structure):
            _fields_ = [("left", ctypes.c_long), ("top", ctypes.c_long),
                        ("right", ctypes.c_long), ("bottom", ctypes.c_long)]

        def _cb(hwnd, _lp):
            try:
                n = u.GetWindowTextLengthW(hwnd)
                if n <= 0:
                    return True
                b = ctypes.create_unicode_buffer(n + 1)
                u.GetWindowTextW(hwnd, b, n + 1)
                if "SpaceMap" not in (b.value or ""):
                    return True
                # 隐藏的（被我们预热时藏起来的）或挪到屏幕外的，都算我们留下的孤儿；
                # 用户自己开的那个是可见且在屏幕内的，不动。
                if u.IsWindowVisible(hwnd):
                    r = RECT()
                    u.GetWindowRect(hwnd, ctypes.byref(r))
                    if not (r.left < -5000 or r.top < -5000):
                        return True
                u.PostMessageW(hwnd, 0x0010, 0, 0)       # WM_CLOSE
            except Exception:      # noqa: BLE001
                pass
            return True

        try:
            u.EnumWindows(ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND,
                                             wintypes.LPARAM)(_cb), 0)
        except Exception:      # noqa: BLE001
            pass

    def _spacemap_set_theme(self):
        """把当前深浅色写进 SpaceMap 的 settings.json。

        它启动时会读这个文件（键名 theme），所以窗口一打开就是配套配色。
        深色 -> ink，浅色 -> mist（palette.ts 里 mist 的 dark: false）。
        """
        import json
        d = os.path.join(os.environ.get("LOCALAPPDATA", os.path.expanduser("~")), "SpaceMap")
        f = os.path.join(d, "settings.json")
        cur = {}
        try:
            os.makedirs(d, exist_ok=True)
            if os.path.isfile(f):
                try:
                    with open(f, "r", encoding="utf-8") as fh:
                        cur = json.load(fh)
                    if not isinstance(cur, dict):
                        cur = {}
                except Exception:      # noqa: BLE001
                    cur = {}
            cur["theme"] = "mist" if self.theme == "light" else "ink"
            with open(f, "w", encoding="utf-8") as fh:
                json.dump(cur, fh, ensure_ascii=False, indent=2)
        except OSError:
            pass

    def _spacemap_restart(self):
        """主题变了：把嵌入的 SpaceMap 重启一次，让它套用新配色。"""
        hwnd = getattr(self, "_sm_hwnd", 0)
        self._sm_hwnd = 0
        try:
            if hwnd:
                import ctypes
                ctypes.windll.user32.PostMessageW(hwnd, 0x0010, 0, 0)   # WM_CLOSE
        except Exception:      # noqa: BLE001
            pass
        self._sm_shutdown()
        if not getattr(self, "_closed", False):
            self.after(700, self._spacemap_start)

    def _spacemap_prestart(self):
        """开机就把 SpaceMap 拉起来（窗口开在屏幕外，用户看不到）。

        它启动要几秒（SEA 解包 + 起 HTTP 服务 + 开 Edge），提前预热后切到标签页通常已就绪。
        首次运行还要把内嵌的 88MB 释放到缓存 —— 整段放后台线程做，别卡住界面。
        """
        if getattr(self, "_sm_proc", None) is not None or getattr(self, "_sm_hwnd", 0):
            return
        if getattr(self, "_sm_prestarting", False):
            return
        self._sm_prestarting = True

        def work():
            # 这一段完全不碰 Tk：找 exe（首次要释放 88MB）、写主题、起进程
            import subprocess
            try:
                exe = spacemap_exe_path()
                if not exe:
                    return
                self._spacemap_set_theme()
                cmd = [exe]
                target = (self.target or "").strip().strip('"')
                if target and os.path.exists(target):
                    cmd.append(target)
                self._sm_proc = subprocess.Popen(
                    cmd, env={**os.environ, "SPACEMAP_EMBED": "1"})
                self.after(300, self._spacemap_hide_watch)   # 一出现就藏起来
            except Exception:      # noqa: BLE001
                pass
            finally:
                self._sm_prestarting = False

        threading.Thread(target=work, daemon=True).start()

    def _spacemap_hide_watch(self, tries=0):
        """预热之后盯着点：窗口一出现就藏起来，别让它在桌面上单独弹出来。

        SpaceMap 启动时带了 --window-position=-20000,-20000，但**如果 Edge 已经在跑**，
        新窗口会并入已有浏览器进程 —— 这时 Chromium 会忽略位置参数，窗口就出现在屏幕中。
        这里做兜底：只要发现窗口就直接藏掉，用户看不到；切到标签页再正式嵌进来。
        """
        if self._closed or getattr(self, "_sm_hwnd", 0):
            return
        hwnd = self._spacemap_find()
        if hwnd:
            try:
                import ctypes
                u = ctypes.windll.user32
                u.ShowWindow(hwnd, 0)                       # SW_HIDE
                u.SetWindowPos(hwnd, 0, -20000, -20000, 0, 0,
                               0x0001 | 0x0004)             # NOSIZE | NOZORDER
            except Exception:      # noqa: BLE001
                pass
            return
        if tries > 150:          # 约 30 秒还没出现就不盯了
            return
        self.after(200, lambda: self._spacemap_hide_watch(tries + 1))

    def _spacemap_start(self):
        """启动 SpaceMap 并等它的窗口出现，然后嵌进 sm_host。"""
        import subprocess
        exe = spacemap_exe_path()
        if not exe:
            messagebox.showwarning(
                "找不到 SpaceMap",
                "没找到 SpaceMap.exe。\n\n正常安装时它应该已打进本程序里；"
                "如果是开发环境，请把它放到程序目录或桌面。")
            return
        if getattr(self, "_sm_hwnd", 0):
            self._spacemap_resize()
            return
        if getattr(self, "_sm_prestarting", False) and getattr(self, "_sm_proc", None) is None:
            # 预热还在进行（首次运行要释放 88MB），等它一会儿，别又起一个
            n = getattr(self, "_sm_wait_n", 0)
            if n < 60:
                self._sm_wait_n = n + 1
                self.after(150, self._spacemap_start)
                return
            self._sm_wait_n = 0
        if getattr(self, "_sm_proc", None) is None:      # 预热过就不再重复启动
            self._spacemap_set_theme()                   # 先写好配色，再启动
            target = (self.target or "").strip().strip('"')
            cmd = [exe]
            if target and os.path.exists(target):
                cmd.append(target)                       # 让 SpaceMap 直接扫当前目标
            try:
                self._sm_proc = subprocess.Popen(
                    cmd, env={**os.environ, "SPACEMAP_EMBED": "1"})
            except OSError as e:
                messagebox.showerror("启动失败", str(e))
                return
        self.btn_sm.config(text="启动中…" if getattr(self, "_sm_proc", None) is None else "嵌入中…",
                           state="disabled")
        self.lbl_sm.config(text="正在启动 SpaceMap，等它的窗口出现…")
        self._spacemap_wait(0)

    def _spacemap_wait(self, tries):
        if self._closed:
            return
        hwnd = self._spacemap_find()
        if hwnd:
            self._spacemap_attach(hwnd)
            return
        if tries > 60:                  # 约 12 秒
            self.btn_sm.config(text="重新尝试", state="normal")
            self.lbl_sm.config(
                text="没能抓到 SpaceMap 的窗口。它可能已经作为独立窗口打开了（看看任务栏）；"
                     "把它关掉再点「重新尝试」")
            return
        self.after(200, lambda: self._spacemap_wait(tries + 1))

    def _spacemap_attach(self, hwnd):
        """去掉弹窗样式、加上子窗口样式，再 SetParent 到 sm_host。"""
        try:
            import ctypes
            u = ctypes.windll.user32
            u.ShowWindow(hwnd, 0)        # 先藏起来（SW_HIDE），嵌好再显示，双保险
            GWL_STYLE = -16
            WS_POPUP, WS_CHILD, WS_VISIBLE = 0x80000000, 0x40000000, 0x10000000
            # 除了去掉弹窗样式，还要清掉标题栏/粗细边框/普通边框/对话框边框，
            # 否则嵌进来的窗口上面会留一条带叉号的标题栏、四周还有一圈边。
            WS_CAPTION, WS_THICKFRAME = 0x00C00000, 0x00040000
            WS_BORDER, WS_DLGFRAME, WS_SYSMENU = 0x00800000, 0x00400000, 0x00080000
            try:
                st = u.GetWindowLongW(hwnd, GWL_STYLE)
                st = st & ~(WS_POPUP | WS_CAPTION | WS_THICKFRAME | WS_BORDER
                            | WS_DLGFRAME | WS_SYSMENU)
                u.SetWindowLongW(hwnd, GWL_STYLE, st | WS_CHILD | WS_VISIBLE)
                # 改完样式必须 SWP_FRAMECHANGED 才会重算非客户区，否则边框还在
                SWP = 0x0020 | 0x0002 | 0x0001 | 0x0004      # FRAMECHANGED|NOMOVE|NOSIZE|NOZORDER
                u.SetWindowPos(hwnd, 0, 0, 0, 0, 0, SWP)
            except Exception:      # noqa: BLE001
                pass
            u.SetParent(hwnd, self.sm_host.winfo_id())
        except Exception as e:      # noqa: BLE001
            self.btn_sm.config(text="重新尝试", state="normal")
            self.lbl_sm.config(text="嵌入失败：%s（可以把它当独立窗口用）" % e)
            return
        self._sm_hwnd = hwnd
        self.after(700, self._spacemap_selfheal)          # 开始自愈校对
        try:
            import ctypes
            ctypes.windll.user32.ShowWindow(hwnd, 5)     # SW_SHOW
        except Exception:      # noqa: BLE001
            pass
        self.btn_sm.config(text="已嵌入", state="disabled")
        self.lbl_sm.config(text="已嵌入 SpaceMap · 它的窗口会跟着这个标签页缩放（切换标签页时自动隐藏）")
        self._spacemap_resize()
        self.after(400, self._spacemap_resize)      # 布局稳定后再校一次

    def _spacemap_resize(self, _ev=None):
        """让嵌入窗口的**客户区**正好铺满 sm_host，并且不带标题栏/边框。

        每次调用都会**重新清一遍窗口样式**：Chromium 会重建自己的窗口框架，
        只清一次不保险。清理之后再做几何规避（把非客户区推到可视区外）兜底，
        所以即使样式没生效，标题栏和边框也不会露出来。
        """
        hwnd = getattr(self, "_sm_hwnd", 0)
        if not hwnd:
            return
        try:
            import ctypes
            u = ctypes.windll.user32

            class RECT(ctypes.Structure):
                _fields_ = [("left", ctypes.c_long), ("top", ctypes.c_long),
                            ("right", ctypes.c_long), ("bottom", ctypes.c_long)]

            class POINT(ctypes.Structure):
                _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]

            # 1) 再清一次边框样式（Chromium 可能又加回来了）
            GWL_STYLE = -16
            WS_POPUP, WS_CHILD, WS_VISIBLE = 0x80000000, 0x40000000, 0x10000000
            WS_CAPTION, WS_THICKFRAME = 0x00C00000, 0x00040000
            WS_BORDER, WS_DLGFRAME, WS_SYSMENU = 0x00800000, 0x00400000, 0x00080000
            st = u.GetWindowLongW(hwnd, GWL_STYLE)
            want = (st & ~(WS_POPUP | WS_CAPTION | WS_THICKFRAME | WS_BORDER
                           | WS_DLGFRAME | WS_SYSMENU)) | WS_CHILD | WS_VISIBLE
            if st != want:
                u.SetWindowLongW(hwnd, GWL_STYLE, want)
                u.SetWindowPos(hwnd, 0, 0, 0, 0, 0,
                               0x0020 | 0x0002 | 0x0001 | 0x0004)   # FRAMECHANGED|NOMOVE|NOSIZE|NOZORDER

            # 2) 几何规避：算出非客户区厚度，把它推到可视区外
            w = max(self.sm_host.winfo_width(), 1)
            h = max(self.sm_host.winfo_height(), 1)
            wr, cr, pt = RECT(), RECT(), POINT(0, 0)
            u.GetWindowRect(hwnd, ctypes.byref(wr))
            u.GetClientRect(hwnd, ctypes.byref(cr))
            u.ClientToScreen(hwnd, ctypes.byref(pt))
            left = max(pt.x - wr.left, 0)
            top = max(pt.y - wr.top, 0)
            right = max(wr.right - (pt.x + cr.right), 0)
            bottom = max(wr.bottom - (pt.y + cr.bottom), 0)
            u.MoveWindow(hwnd, -left, -top, w + left + right, h + top + bottom, True)
        except Exception:      # noqa: BLE001
            pass

    def _spacemap_selfheal(self):
        """嵌着的时候每 700ms 校对一次样式和位置。

        Chromium 会时不时重建自己的窗口框架，把标题栏又加回来；这里一直纠着，
        用户就不会看到标题栏或黑框。开销只有几个 Win32 调用。
        """
        if self._closed:
            return
        if getattr(self, "_sm_hwnd", 0):
            self._spacemap_resize()
            self.after(700, self._spacemap_selfheal)

    # ---------------- 软件占用 ----------------
    def _lookup_size(self, path):
        """优先从已经扫过的结果里查表（零成本），查不到返回 0。"""
        if not path:
            return 0
        cands = [path, path.rstrip("\\"), os.path.normpath(path)]
        try:
            cands.append(os.path.normcase(os.path.normpath(path)))
        except OSError:
            pass
        scs = []
        if self.result is not None:
            scs.append(self.result)
        drive = os.path.splitdrive(os.path.abspath(path))[0] + "\\"
        for sc in list(getattr(self, "_cache", {}).values()):
            if sc is not None and sc not in scs:
                scs.append(sc)
        for sc in scs:
            for cpath in cands:
                try:
                    v = sc.folder_size(cpath)
                except Exception:      # noqa: BLE001
                    v = 0
                if v:
                    return v
        return 0

    def _soft_candidates(self, app):
        """这个软件可能占了哪些目录。"""
        out = []
        loc = app.get("loc") or ""
        if loc and os.path.isdir(loc):
            out.append(os.path.normpath(loc))
        toks = norm_tokens(app["name"])
        if not toks:
            return out
        pub = norm_tokens(app.get("publisher") or "")
        for raw in SOFT_NAME_ROOTS:
            base = os.path.expandvars(raw)
            out.extend(self._match_in(base, toks, pub))
        # 各盘的 Program Files 也找一遍（软件不一定装在 C 盘）
        for d in self._drive_list():
            for sub2 in ("Program Files", "Program Files (x86)", "Programs"):
                out.extend(self._match_in(os.path.join(d, sub2), toks, pub))
        # 去掉重复 + 去掉互为父子（只留父，避免重复计算）
        uniq = []
        for p in out:
            if p not in uniq:
                uniq.append(p)
        uniq.sort(key=len)
        kept = []
        for p in uniq:
            if not any(p == q or p.startswith(q + os.sep) for q in kept):
                kept.append(p)
        return kept

    def _match_in(self, base, toks, pub):
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
                    if any(t in nm for t in toks) or (pub and any(t in nm for t in pub)):
                        res.append(e.path)
        except OSError:
            pass
        return res

    def _soft_scan(self):
        if getattr(self, "_soft_running", False):
            return
        self._soft_running = True
        self._soft_done = False
        self._soft_rows = []
        self.soft_tree.delete(*self.soft_tree.get_children())
        self.btn_soft_go.config(text="分析中…", state="disabled")
        self.lbl_soft_sum.config(text="正在读注册表并统计各软件占用…（已扫过的盘会直接查表）")
        threading.Thread(target=self._soft_worker, daemon=True).start()
        self.after(200, self._poll_soft)

    def _soft_worker(self):
        import time as _t
        deadline = _t.time() + 150      # 总时长上限，避免没扫过的盘拖太久
        try:
            apps = read_installed_apps()
            for app in apps:
                if _t.time() > deadline:
                    break
                dirs = self._soft_candidates(app)
                total = 0
                used = []          # [(目录, 体积), ...] —— 要按盘汇总体积
                for d in dirs:
                    v = self._lookup_size(d)
                    if not v:
                        try:
                            v = path_size(d, SOFT_SIZE_BUDGET)
                        except OSError:
                            v = 0
                    if v > 0:
                        total += v
                        used.append((d, v))
                self._soft_rows.append((total, app, used))
        except Exception:      # noqa: BLE001
            pass
        finally:
            self._soft_done = True

    def _poll_soft(self):
        if self._closed:
            return
        if not getattr(self, "_soft_done", False):
            self.after(200, self._poll_soft)
            return
        self._soft_running = False
        self.btn_soft_go.config(text="重新分析", state="normal")
        rows = [r for r in getattr(self, "_soft_rows", []) if r[0] > 0]
        # 同一个软件可能有多个注册表条目，按名字合并
        merged = {}
        for total, app, used in rows:
            k = app["name"].lower()
            if k in merged:
                merged[k][0] += total
                merged[k][2].extend(used)
            else:
                merged[k] = [total, app, list(used)]
        # 第三方软件集中按大小排在最前，系统组件排在后面 —— 一眼看清"我装的东西"占了多少
        items = sorted(merged.values(),
                       key=lambda r: (0 if self._soft_kind(r[1],
                                                           [d for d, _v in r[2]]) == "第三方"
                                      else 1, -r[0]))
        self._soft_paths = {}
        self._soft_uninst = {}
        self._soft_items = items
        for total, app, used in items:
            uniq = []
            seen = set()
            for d, v in used:
                if d not in seen:
                    seen.add(d)
                    uniq.append((d, v))
            iid = self.soft_tree.insert(
                "", "end", text="  " + app["name"], values=(
                    self._soft_kind(app, [d for d, _v in uniq]), human_size(total), "",
                    self._soft_disks(uniq), "%d" % len(uniq),
                    _clip(app.get("publisher") or "—", 150)))
            self._soft_paths[iid] = [d for d, _v in uniq]
            if app.get("uninst"):
                self._soft_uninst[iid] = app["uninst"]
            else:
                self._soft_uninst.pop(iid, None)
        if not items:
            self._combo_hint(self.soft_tree, [
                "（注册表里没读到已装软件 —— 试试以管理员身份运行）"])
        grand = sum(r[0] for r in items)
        third = sum(r[0] for r in items
                    if self._soft_kind(r[1], [d for d, _v in r[2]]) == "第三方")
        self.lbl_soft_sum.config(
            text="共 %d 个 · 合计 %s（第三方约 %s / 系统组件约 %s）"
                 "· 右键有更多操作 · 图标稍后加载"
                 % (len(items), human_size(grand), human_size(third),
                    human_size(grand - third)))
        self.after(80, self._soft_load_icons)

    def _soft_load_icons(self):
        """批量抽图标：只抽占用最大的若干个，一次 PowerShell 全搞定。"""
        items = list(getattr(self, "_soft_items", []))[:SOFT_ICON_MAX]
        if not items:
            return
        work = []
        for i, (_t, app, used) in enumerate(items):
            src = app.get("icon") or ""
            if not (src and os.path.isfile(src)):
                src = ""
                for d, _v in used:
                    try:
                        for f in os.listdir(d):
                            if f.lower().endswith(".exe"):
                                src = os.path.join(d, f)
                                break
                    except OSError:
                        pass
                    if src:
                        break
            if src:
                work.append({"i": i, "src": src})
        if not work:
            self.lbl_soft_sum.config(text=self.lbl_soft_sum.cget("text")
                                     .replace("· 图标稍后加载", ""))
            return
        try:
            os.makedirs(SOFT_ICON_DIR, exist_ok=True)
        except OSError:
            return
        import json
        import subprocess
        import tempfile
        jf = os.path.join(tempfile.gettempdir(), "dss_icons.json")
        try:
            with open(jf, "w", encoding="utf-8") as f:
                json.dump(work, f, ensure_ascii=False)
        except OSError:
            return
        ps = ("Add-Type -AssemblyName System.Drawing; "
              "$items = Get-Content -Raw -Encoding UTF8 '%s' | ConvertFrom-Json; "
              "foreach ($it in $items) { try { "
              "$ic = [System.Drawing.Icon]::ExtractAssociatedIcon($it.src); "
              "if ($ic) { $b = New-Object System.Drawing.Bitmap $ic, 24, 24; "
              "$b.Save((Join-Path '%s' ($it.i.ToString() + '.png')), "
              "[System.Drawing.Imaging.ImageFormat]::Png); $b.Dispose(); $ic.Dispose() } "
              "} catch {} }") % (jf, SOFT_ICON_DIR)
        try:
            subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", ps],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           timeout=90, creationflags=0x08000000)
        except Exception:      # noqa: BLE001
            return
        self._apply_soft_icons()

    def _apply_soft_icons(self):
        kids = self.soft_tree.get_children()
        got = 0
        for i, iid in enumerate(kids):
            p = os.path.join(SOFT_ICON_DIR, "%d.png" % i)
            if not os.path.isfile(p):
                continue
            try:
                img = tk.PhotoImage(file=p)
            except tk.TclError:
                continue
            self._soft_icons[iid] = img          # 必须留引用，否则被 GC 掉图就没了
            try:
                self.soft_tree.item(iid, image=img)
            except tk.TclError:
                pass
            got += 1
        self.lbl_soft_sum.config(
            text=self.lbl_soft_sum.cget("text").replace("· 图标稍后加载", "")
            + "· 已加载 %d 个图标" % got)

    @staticmethod
    def _soft_kind(app, dirs):
        """系统组件还是自己装的第三方软件。"""
        name = (app.get("name") or "").lower()
        pub = (app.get("publisher") or "").lower()
        loc = (app.get("loc") or "").lower()
        if "microsoft" in pub or "windows" in pub:
            return "系统"
        for kw in ("驱动程序包", "update for", "hotfix", "redistributable", "runtime",
                   "visual c++", "framework", "sdk", "language pack", "windows "):
            if kw in name:
                return "系统"
        if loc.startswith("c:\\windows") or any(d.lower().startswith("c:\\windows") for d in dirs):
            return "系统"
        return "第三方"

    @staticmethod
    def _soft_disks(pairs):
        """这个软件的空间分布在哪些盘、各占多少 —— 按体积汇总，不是数目录个数。"""
        import collections
        c = collections.OrderedDict()
        for d, v in pairs:
            try:
                drv = os.path.splitdrive(os.path.abspath(d))[0].upper()
            except OSError:
                continue
            if drv:
                c[drv] = c.get(drv, 0) + v
        if not c:
            return "—"
        items = sorted(c.items(), key=lambda kv: -kv[1])
        return "  ".join("%s %s" % (k, human_size(v)) for k, v in items)

    def _soft_right(self, ev):
        iid = self.soft_tree.identify_row(ev.y)
        if not iid:
            return
        self.soft_tree.selection_set(iid)
        self.soft_tree.focus(iid)
        dirs = getattr(self, "_soft_paths", {}).get(iid) or []
        m = tk.Menu(self, tearoff=0)
        uninstall = getattr(self, "_soft_uninst", {}).get(iid)
        if uninstall:
            m.add_command(label="卸载这个软件…", command=lambda: self._soft_uninstall(iid))
            m.add_separator()
        m.add_command(label="打开主目录", command=lambda: self._soft_open_path(dirs, 0))
        for k in range(1, min(len(dirs), 4)):
            d = dirs[k]
            short = d if len(d) <= 46 else "…" + d[-44:]
            m.add_command(label="打开：%s" % short,
                          command=lambda p=d: self._soft_open_path([p], 0))
        m.add_separator()
        m.add_command(label="复制全部路径",
                      command=lambda: self._copy_text("\n".join(dirs)))
        m.add_command(label="在文件夹树图里定位",
                      command=lambda: self._soft_locate(iid))
        try:
            m.tk_popup(ev.x_root, ev.y_root)
        finally:
            m.grab_release()

    def _soft_uninstall(self, iid):
        """调注册表里登记的卸载命令。删不删由用户在卸载程序里决定。"""
        cmd = getattr(self, "_soft_uninst", {}).get(iid)
        if not cmd:
            return
        if not messagebox.askyesno(
                "卸载确认",
                "将执行该软件自己的卸载程序：\n\n%s\n\n"
                "接着由那个卸载程序决定怎么删，本软件不会替你删任何文件。继续吗？" % cmd[:300]):
            return
        try:
            subprocess.Popen(cmd, shell=True)
            self.lbl_status.config(text="已调起卸载程序，请在弹出的窗口里完成卸载")
        except Exception as e:      # noqa: BLE001
            messagebox.showerror("无法启动卸载", str(e))

    def _soft_open_path(self, dirs, idx):
        try:
            if dirs:
                os.startfile(dirs[idx])
        except (OSError, IndexError):
            pass

    def _copy_text(self, text):
        try:
            self.clipboard_clear()
            self.clipboard_append(text)
            self.lbl_status.config(text="已复制 %d 个路径到剪贴板" % text.count("\n") + 1)
        except tk.TclError:
            pass

    def _soft_locate(self, iid):
        """在这个软件的主目录里打开树图（若该盘已扫过）。"""
        dirs = getattr(self, "_soft_paths", {}).get(iid) or []
        if not dirs:
            return
        p = dirs[0]
        key = os.path.normcase(os.path.normpath(os.path.splitdrive(p)[0] + "\\"))
        sc = self._cache.get(key)
        if sc is None:
            self.lbl_status.config(text="该目录所在磁盘尚未预扫描，请先在顶部扫描 %s"
                                   % os.path.splitdrive(p)[0])
            return
        self._rank_enter_path(p)

    def _soft_open(self, _ev):
        iid = self.soft_tree.focus()
        dirs = getattr(self, "_soft_paths", {}).get(iid) or []
        if not dirs:
            return
        try:
            os.startfile(dirs[0])
        except OSError:
            pass

    # ---------------- 清理建议 ----------------
    def _clean_scan(self):
        if getattr(self, "_clean_running", False):
            return
        self._clean_running = True
        self._clean_done = False
        self._clean_results = []
        self._clean_paths = {}
        self._clean_sizes = {}
        self.clean_tree.delete(*self.clean_tree.get_children())
        self.btn_clean_go.config(text="分析中…", state="disabled")
        self.lbl_clean_sum.config(text="正在分析常见可清理位置…（每个位置最多 5 秒）")
        threading.Thread(target=self._clean_worker, daemon=True).start()
        self.after(150, self._poll_clean)

    def _clean_worker(self):
        try:
            for name, raw, risk, advice in CLEAN_TARGETS:
                try:
                    path = os.path.expandvars(raw)
                    if not os.path.exists(path):
                        continue
                    size = path_size(path)
                except OSError:
                    continue
                if size > 0:
                    self._clean_results.append((size, name, risk, advice, path))
        finally:
            self._clean_done = True

    def _poll_clean(self):
        if self._closed:
            return
        res = getattr(self, "_clean_results", None)
        while res:
            size, name, risk, advice, path = res.pop(0)
            label = CLEAN_RISK.get(risk, ("", ""))[0]
            iid = self.clean_tree.insert("", "end", values=(
                human_size(size), label, name, _clip(path, 320), advice),
                tags=(risk, "odd" if len(self.clean_tree.get_children()) % 2 else ""))
            self._clean_paths[iid] = path
            self._clean_sizes[iid] = size
        if not getattr(self, "_clean_done", False):
            self.after(150, self._poll_clean)
            return
        self._clean_running = False
        self.btn_clean_go.config(text="重新分析", state="normal")
        # 分析是并发的、到达顺序不定，结束后按占用从大到小重排
        items = [(self._clean_sizes.get(i, 0), self.clean_tree.item(i, "values"),
                  self.clean_tree.item(i, "tags"), self._clean_paths.get(i, ""))
                 for i in self.clean_tree.get_children()]
        items.sort(key=lambda x: x[0], reverse=True)
        self.clean_tree.delete(*self.clean_tree.get_children())
        self._clean_paths, self._clean_sizes = {}, {}
        total_safe = total_caution = 0
        for size, vals, tags, path in items:
            iid = self.clean_tree.insert("", "end", values=vals, tags=tags)
            self._clean_paths[iid] = path
            self._clean_sizes[iid] = size
            if vals[1] == "放心清理":
                total_safe += size
            elif vals[1] == "看清再清":
                total_caution += size
        n = len(items)
        if n == 0:
            self._combo_hint(self.clean_tree, [
                "（这次没找到可清理的位置 —— 可能都被占用，或路径不存在）"])
        self.lbl_clean_sum.config(
            text="找到 %d 处可清理位置：放心清理约 %s · 需你确认约 %s"
                 "（只分析不删除，双击可打开所在文件夹）"
                 % (n, human_size(total_safe), human_size(total_caution)))

    def _clean_purge_one(self, iid):
        """右键删单条：删这个位置的内容（目录保留），复用一键清理那套逻辑。"""
        if getattr(self, "_clean_running", False) or getattr(self, "_clean_purging", False):
            return
        path = getattr(self, "_clean_paths", {}).get(iid)
        if not path or not os.path.isdir(path):
            return
        vals = self.clean_tree.item(iid, "values") or ()
        name = vals[2] if len(vals) > 2 else path
        risk = vals[1] if len(vals) > 1 else ""
        size = self._clean_sizes.get(iid, 0)
        if risk == CLEAN_RISK["danger"][0]:
            messagebox.showwarning(
                "这一项不要删",
                "「%s」标记为「请勿乱动」，直接删会影响系统功能。\n\n"
                "如果是空间不够，请用系统自带的方式调整，而不是删这个文件。" % name)
            return
        extra = ""
        if risk == CLEAN_RISK["caution"][0]:
            extra = "\n\n注意：这一项是「看清再清」，删之前请自己确认内容还有没有用。"
        if not messagebox.askyesno(
                "确认删除",
                "将删除「%s」的内容（约 %s，目录本身保留）：\n\n%s%s\n\n"
                "正在使用、没权限的文件会自动跳过。\n"
                "删除后无法从回收站找回，确定继续吗？" % (name, human_size(size), path, extra)):
            return
        self._clean_purging = True
        self._clean_purge_done = False
        self._clean_purge_result = [0, 0, 0]
        self.btn_clean_purge.config(state="disabled")
        self.btn_clean_go.config(state="disabled")
        self.lbl_clean_sum.config(text="正在清理「%s」…" % name)
        threading.Thread(target=self._clean_purge_worker,
                         args=([(path, name, size)],), daemon=True).start()
        self.after(200, self._poll_purge)

    def _clean_all(self):
        """一键清理：**只清「放心清理」那一档**。

        谨慎/危险的两档一律不碰 —— 那些要么涉及回退能力（Windows.old）、
        要么涉及系统功能（休眠文件、页面文件）。删文件不可逆，这里刻意保守。
        """
        if getattr(self, "_clean_running", False) or getattr(self, "_clean_purging", False):
            return
        safe_label = CLEAN_RISK["safe"][0]
        todo = []
        for iid in self.clean_tree.get_children():
            vals = self.clean_tree.item(iid, "values")
            if not vals or vals[1] != safe_label:
                continue
            p = getattr(self, "_clean_paths", {}).get(iid)
            if p and os.path.isdir(p):
                todo.append((p, vals[2], self._clean_sizes.get(iid, 0)))
        if not todo:
            messagebox.showinfo(
                "一键清理",
                "没有可「放心清理」的项目。\n\n"
                "「看清再清」和「请勿乱动」那两档需要你自己判断，这里不会碰。")
            return
        total = sum(t[2] for t in todo)
        lines = "\n".join("  · %s   %s" % (n, human_size(sz)) for _p, n, sz in todo[:12])
        if len(todo) > 12:
            lines += "\n  …另有 %d 项" % (len(todo) - 12)
        if not messagebox.askyesno(
                "确认一键清理",
                "将删除以下位置的**内容**（目录本身保留）：\n\n%s\n\n"
                "预计释放约 %s。\n\n"
                "正在使用、没权限的文件会自动跳过；\n"
                "「看清再清」和「请勿乱动」的项目不会被删。\n\n"
                "此操作不可恢复，确定继续吗？" % (lines, human_size(total))):
            return
        # 二次确认：删文件不可逆，值得多问一次
        if not messagebox.askyesno("再次确认",
                                   "真的要删吗？删除后无法从回收站找回。"):
            return
        self._clean_purging = True
        self._clean_purge_done = False
        self._clean_purge_result = [0, 0, 0]
        self.btn_clean_purge.config(text="清理中…", state="disabled")
        self.btn_clean_go.config(state="disabled")
        self.lbl_clean_sum.config(text="正在清理…")
        threading.Thread(target=self._clean_purge_worker, args=(todo,), daemon=True).start()
        self.after(200, self._poll_purge)

    def _clean_purge_worker(self, todo):
        nfiles = freed = skipped = 0
        for path, _name, _size in todo:
            try:
                walker = os.walk(path, topdown=False)
            except OSError:
                continue
            for root, _dirs, files in walker:
                for fn in files:
                    fp = os.path.join(root, fn)
                    try:
                        sz = os.path.getsize(fp)
                        os.remove(fp)          # 不是回收站，直接删
                        nfiles += 1
                        freed += sz
                    except OSError:
                        skipped += 1           # 正在使用 / 没权限 → 跳过，不强删
                if root != path:               # 顶层目录保留
                    try:
                        os.rmdir(root)
                    except OSError:
                        pass
            self._clean_purge_result = [nfiles, freed, skipped]
        self._clean_purge_done = True

    def _poll_purge(self):
        if self._closed:
            return
        n, freed, skipped = getattr(self, "_clean_purge_result", [0, 0, 0])
        self.lbl_clean_sum.config(
            text="正在清理… 已删 %s 个文件 · 释放 %s · 跳过 %s 个（占用中或没权限）"
                 % ("{:,}".format(n), human_size(freed), "{:,}".format(skipped)))
        if not getattr(self, "_clean_purge_done", False):
            self.after(200, self._poll_purge)
            return
        self._clean_purging = False
        self._clean_purge_done = False
        self.btn_clean_purge.config(text="一键清理", state="normal")
        self.btn_clean_go.config(state="normal")
        messagebox.showinfo(
            "清理完成",
            "删除 %s 个文件，释放约 %s。\n跳过 %s 个（正在使用或没权限）。"
            % ("{:,}".format(n), human_size(freed), "{:,}".format(skipped)))
        self._clean_scan()      # 重新分析，数字当场刷新

    def _clean_right(self, ev):
        iid = self.clean_tree.identify_row(ev.y)
        if not iid:
            return
        self.clean_tree.selection_set(iid)
        self.clean_tree.focus(iid)
        path = getattr(self, "_clean_paths", {}).get(iid)
        m = tk.Menu(self, tearoff=0)
        m.add_command(label="打开所在文件夹", command=lambda: self._clean_open(None))
        m.add_command(label="复制路径", command=lambda: self._copy_text(path or ""))
        has = bool(path) and os.path.isdir(path)
        m.add_separator()
        m.add_command(label="删除此项内容…", state="normal" if has else "disabled",
                      command=lambda: self._clean_purge_one(iid))
        m.add_command(label="在文件夹树图里定位", state="normal" if has else "disabled",
                      command=lambda: self._clean_locate(path))
        try:
            m.tk_popup(ev.x_root, ev.y_root)
        finally:
            m.grab_release()

    def _clean_locate(self, path):
        if not path:
            return
        key = os.path.normcase(os.path.normpath(os.path.splitdrive(path)[0] + "\\"))
        if self._cache.get(key) is None:
            self.lbl_status.config(text="该磁盘尚未预扫描，请先在顶部扫描 %s"
                                   % os.path.splitdrive(path)[0])
            return
        self._rank_enter_path(path)

    def _clean_open(self, _ev):
        iid = self.clean_tree.focus()
        path = getattr(self, "_clean_paths", {}).get(iid)
        if not path:
            return
        try:
            target = path if os.path.isdir(path) else os.path.dirname(path)
            os.startfile(target)
        except OSError:
            pass

    def _on_child_double(self, _ev):
        iid = self.child_tree.focus()
        info = self._child_map.get(iid)
        if info and info[1]:
            self._enter(info[0])

    def _on_big_double(self, _ev):
        iid = self.big_tree.focus()
        info = self._big_map.get(iid)
        if not info:
            return
        path, is_dir = info
        if is_dir:
            # 双击大目录：跳到该目录的树图视图
            self.current_path = path
            self._world = None
            self._selected_path = None
            self.btn_up.config(state="normal" if path != self.result.root else "disabled")
            self.lbl_path.config(text="当前: %s" % path)
            self._refresh_views()
            self.lbl_status.config(text="已跳转到目录: %s" % path)
        else:
            self.lbl_status.config(text="已选择: %s" % path)

    # ---------------- 文件夹排行榜（深色横条 + 生长动画） ----------------
    # ---------------- 标签切换动画 ----------------

    def _tab_range(self, idx):
        try:
            bb = self.nb.bbox(idx)
        except tk.TclError:
            return None
        if not bb:
            return None
        x, _y, w, _h = bb
        return float(x), float(x + w)

    def _place_tab_ind(self):
        """把指示条贴到标签行下沿（要等 notebook 真正布局完才拿得到 bbox）。"""
        if self._closed:
            return
        bb = None
        try:
            bb = self.nb.bbox(0)
        except tk.TclError:
            bb = None
        if not bb:
            if not self._closed:
                self.after(250, self._place_tab_ind)
            return
        _x, y, _w, h = bb
        self.tab_ind.place(x=0, y=max(y + h - 3, 0), relwidth=1.0, height=3)
        # Canvas 把 lift / tkraise 都重定义成"提升画布**项**"了，提升控件得直接走 Misc
        tk.Misc.tkraise(self.tab_ind)
        try:
            idx = self.nb.index(self.nb.select())
        except tk.TclError:
            idx = 0
        self._move_tab_ind(idx, animate=False)

    def _tab_ind_click(self, ev):
        """指示条盖在标签下沿 3px 上，点它也要能切标签。"""
        for i in range(self.nb.index("end")):
            rng = self._tab_range(i)
            if rng and rng[0] <= ev.x <= rng[1]:
                self.nb.select(i)
                return

    def _move_tab_ind(self, idx, animate=True):
        if getattr(self, "_closed", False):
            return
        rng = self._tab_range(idx)
        if rng is None:
            return
        after = getattr(self, "_tab_ind_after", None)
        if after:
            self.after_cancel(after)
            self._tab_ind_after = None
        cv = self.tab_ind
        cur = self._tab_ind_cur or rng
        sel = rng
        dur = 240.0
        t0 = time.perf_counter()

        def draw(x1, x2):
            cv.delete("all")
            w = cv.winfo_width() or 1
            cv.create_rectangle(0, 0, w, 3, fill=self.t["tab_bg"], outline="")
            cv.create_rectangle(sel[0], 0, sel[1], 3, fill=self.t["tab_sel"], outline="")
            cv.create_polygon(round_rect_points(x1 + 2, 0.0, x2 - 2, 3.0, 1.5),
                              fill=self.t["text"], outline="")

        if not animate:
            self._tab_ind_cur = rng
            draw(*rng)
            return

        def tick():
            if self._closed:
                return
            p = min((time.perf_counter() - t0) * 1000.0 / dur, 1.0)
            e = 1 - (1 - p) ** 3                 # ease-out cubic
            draw(cur[0] + (rng[0] - cur[0]) * e, cur[1] + (rng[1] - cur[1]) * e)
            if p < 1:
                self._tab_ind_after = self.after(12, tick)
            else:
                self._tab_ind_after = None
                self._tab_ind_cur = rng

        tick()

    def _tree_reveal(self):
        """切到树图时来一下轻微放大（约 0.2 秒），比硬切换顺眼。"""
        if self._animating or not self.result or not self.current_path:
            return
        cw, ch = self._canvas_size()
        full = (0.0, 0.0, float(cw), float(ch))
        start = (cw * 0.05, ch * 0.05, cw * 0.90, ch * 0.90)
        steps = 14

        def frame(i):
            if self._closed:
                return
            # 按真实经过时间算进度（慢帧只少画几帧，不会把动画拖长）
            if getattr(self, "_anim_t0", None) is None:
                self._anim_t0 = time.perf_counter()
            _e = min(1.0, (time.perf_counter() - self._anim_t0) * 1000.0
                     / max(getattr(self, "_anim_ms", 220), 1))
            t = (4 * _e * _e * _e) if _e < 0.5 else (1 - pow(-2 * _e + 2, 3) / 2.0)
            self._world = tuple(start[k] + (full[k] - start[k]) * t for k in range(4))
            self._anim_first = (i == 0)
            self._safe_anim(self._render_tree)
            if _e < 1.0:
                self.after(1, lambda: frame(i + 1))
            else:
                self._world = None
                self._animating = False      # 先解除低清模式，最后这一帧才是完整精度
                self._render_tree()

        self._anim_ms = 110 if getattr(self, "tree_anim", "smooth") == "fast" else 220
        self._anim_t0 = None
        self._animating = True
        frame(0)

    def _on_tab_changed(self, _ev):
        try:
            idx = self.nb.index(self.nb.select())
        except tk.TclError:
            return
        cur = self.nb.select()
        # 标签栏指示条滑过去
        self._move_tab_ind(idx)
        # 顺手把键盘焦点从 notebook 上挪走：否则选中的标签上会留一圈虚线焦点框
        self.after(10, self.focus_set)
        if cur == str(self.tab_rank) and self.result and self.rank_path:
            # 每次切过来都重放一次生长动画（原来只在首次渲染时才会动）
            self._rank_render(animate=True)
        elif cur == str(self.tab_tree):
            # 树图标签页首次显示时画布才拿到真实尺寸，重绘一次；再补一个入场动画
            self._world = None
            self._render_tree()
            if self.result and self.current_path:
                self._tree_reveal()
        elif cur == str(self.tab_type):
            # 切过来时重画一遍，条条会重新生长
            self._render_type_tab()
        elif cur == str(self.tab_big):
            self._fill_big_files(animate=True)
        elif getattr(self, "tab_spacemap", None) is not None and cur == str(self.tab_spacemap):
            # 只要还没抓到窗口就走 _spacemap_start（它会自动等窗口出现再嵌入）。
            # 原来写成"进程不存在才走它"是个 bug：预热已经把进程起来了，
            # 于是走了 resize 分支，窗口永远抓不到，用户就得自己点按钮。
            if not getattr(self, "_sm_hwnd", 0):
                self.after(120, self._spacemap_start)
            else:
                self.after(120, self._spacemap_resize)

    def _rank_on_configure(self, ev):
        if ev.width < 50:
            return
        if self.rank_resize_after:
            self.after_cancel(self.rank_resize_after)

        def _do():
            self.rank_resize_after = None
            if self.rank_animating:
                return
            if self.result and self.rank_path and ev.width != getattr(self, "rank_cw", -1):
                self._rank_render(animate=False)

        self.rank_resize_after = self.after(150, _do)

    def _rank_reset(self, animate=True):
        if not self.result:
            return
        self.rank_path = self.result.root
        self.rank_canvas.yview_moveto(0)
        self._rank_render(animate=animate)

    def _rank_back(self):
        if not self.rank_path or not self.result:
            return
        parent = os.path.dirname(self.rank_path)
        if parent == self.rank_path or parent not in self.result.folders:
            return
        self._rank_enter_path(parent)

    def _apply_tab_order(self):
        """把标签按固定顺序排好。

        原来有两套机制在打架：_build_ui 里用 nb.insert 定位，_set_search_tab 又用
        forget + add 把搜索页扔到最后，所以顺序会随调用时机变化。这里统一收口，
        所有会动标签的地方都调它一次。
        """
        want = [self.tab_rank, self.tab_type, self.tab_big, self.tab_tree]
        if getattr(self, "tab_spacemap", None) is not None:
            want.append(self.tab_spacemap)
        try:
            self.nb.index(self.tab_search)      # 搜索页在场才排进去
        except tk.TclError:
            pass
        else:
            want.insert(1, self.tab_search)
        want.append(self.tab_combo)
        for pos, tab in enumerate(want):
            try:
                self.nb.insert(pos, tab)
            except tk.TclError:
                pass

    def _set_search_tab(self, show):
        # 搜索页固定占第 2 个标签位：显示=add（恢复到原位），隐藏=hide，不移动任何标签
        if show and not self._search_shown:
            self.nb.add(self.tab_search)
            self._search_shown = True
        elif not show and self._search_shown:
            self.nb.hide(self.tab_search)
            self._search_shown = False
        self._apply_tab_order()

    def _on_search_input(self):
        if self._search_after:
            self.after_cancel(self._search_after)
        self._search_after = self.after(SEARCH_DEBOUNCE_MS, self._do_search)

    def _search_sources(self):
        """收集全电脑所有可搜的数据源：内存缓存 + 各盘的落盘缓存。

        之前只搜当前扫的那个目标，所以"全电脑搜索"其实搜不到别的盘。
        现在把每个盘的索引都并进来 —— 落盘缓存是现成的，读一次就一直用。
        """
        idx = getattr(self, "_search_index", None)
        if idx is not None:
            return idx
        srcs = []
        seen = set()
        for key, sc in list(self._cache.items()):
            items = getattr(sc, "all_items", None)
            if items:
                srcs.append((sc.root, items))
                seen.add(key)
        for d in self._drive_list():
            k = os.path.normcase(os.path.normpath(d))
            if k in seen:
                continue
            sc = load_scan_cache(d)          # 7 天内的落盘缓存
            if sc is not None and getattr(sc, "all_items", None):
                self._cache[k] = sc
                self._cache_ts[k] = getattr(sc, "scanned_at", "上次")
                seen.add(k)
                srcs.append((sc.root, sc.all_items))
        self._search_index = srcs
        return srcs

    def _do_search(self):
        q = self.var_search.get().strip().lower()
        t = self.search_tree
        t.delete(*t.get_children())
        self._search_map = {}
        if not q:
            self._set_search_tab(False)
            self.nb.select(self.tab_rank)
            return
        srcs = self._search_sources()
        if not srcs:
            self.search_info.config(
                text="尚无任何磁盘的扫描数据。请先在顶部选择一个磁盘扫描，"
                     "之后 7 天内都能用它做全电脑搜索。")
            self._set_search_tab(True)
            self.nb.select(self.tab_search)
            return
        toks = q.split()
        # 遍历所有盘的索引，命中里带上盘符，方便一眼看出在哪个盘
        hits = []
        for root, items in srcs:
            if len(toks) == 1:
                tok = toks[0]
                hits.extend([(it[0], it[1], it[2], it[3], it[4], it[5], root)
                             for it in items if tok in it[1]])
            else:
                hits.extend([(it[0], it[1], it[2], it[3], it[4], it[5], root)
                             for it in items if all(tok in it[1] for tok in toks)])
        total_n = len(hits)
        # 取占用最大的前 SEARCH_MAX 个。原来是把所有命中全排序再切片 ——
        # 命中几万条时光排序就要几百毫秒，用堆选择只保留前 N 个快得多。
        import heapq
        top = heapq.nlargest(SEARCH_MAX, hits, key=lambda r: r[2])
        drives_n = len(set(h[6] for h in hits))
        self.search_info.config(
            text="找到 %s 个（搜索范围：全电脑 %d 个盘）· 只显示占用最大的 %d 个"
                 % ("{:,}".format(total_n), drives_n, SEARCH_MAX))
        for full, low, sz, is_dir, g, flags, _root in top:
            marker = ""
            if flags & 1:
                marker += "·隐藏"
            if flags & 2:
                marker += "·系统"
            iid = t.insert("", "end", values=(human_size(sz), os.path.basename(full),
                                              ("文件夹" if is_dir else TYPE_GROUPS[g][0]) + marker,
                                              os.path.dirname(full)))
            self._search_map[iid] = (full, is_dir)
        self.search_info.config(
            text="在全电脑 %d 个盘里找到 %s 个%s · 双击文件夹进入排行榜 / 双击文件直接打开 · 右键文件管理器"
                 % (drives_n, "{:,}".format(total_n),
                    ("（只显示占用最大的 %d 个，可输入更具体的关键词）" % SEARCH_MAX)
                    if total_n > SEARCH_MAX else ""))
        self._set_search_tab(True)
        self.nb.select(self.tab_search)

    def _on_search_double(self, _ev):
        iid = self.search_tree.focus()
        info = self._search_map.get(iid)
        if not info:
            return
        path, is_dir = info
        if is_dir:
            self.nb.select(0)
            self._rank_enter_path(path)
        else:
            self._open_file(path)

    def _on_search_right(self, ev):
        iid = self.search_tree.identify_row(ev.y)
        info = self._search_map.get(iid)
        if info:
            self._popup_for_path(info[0], info[1], ev)

    def _rank_enter_path(self, path):
        if not self.result or self.result.folders.get(path) is None:
            return
        self.rank_path = path
        self.rank_canvas.yview_moveto(0)
        self._rank_render(animate=True)

    def _rank_render(self, animate=True):
        cv = self.rank_canvas
        if self.rank_anim_after:
            self.after_cancel(self.rank_anim_after)
            self.rank_anim_after = None
        self.rank_animating = False
        cv.delete("all")
        self.rank_rows = []
        self.rank_hover = -1
        fname = "Microsoft YaHei UI"
        if not self.result or not self.rank_path:
            cv.create_text(320, 220, text="选择目标后点击「开始扫描」", fill=self.t["rsub"],
                           font=(fname, 11))
            self.btn_rank_up.config(state="disabled")
            self.lbl_rank_path.config(text="尚未扫描")
            return
        rec = self.result.folders.get(self.rank_path)
        if rec is None:
            return
        mapped = cv.winfo_width() >= 50
        self.rank_pending_anim = bool(animate and not mapped)
        animate = bool(animate and mapped)
        at_root = (self.rank_path == self.result.root)
        self.btn_rank_up.config(state="disabled" if at_root else "normal")
        self.lbl_rank_path.config(text="%s   ·   合计 %s" % (self.rank_path, human_size(rec["size"])))

        rows = [r for r in self._children_with_size(self.rank_path, rec) if r[2] > 0]
        rows.sort(key=lambda r: -r[2])
        total = rec["size"] or 1
        if len(rows) > RANK_MAX_ROWS:
            rest = rows[RANK_MAX_ROWS:]
            merged = (-1, "其他 %d 项" % len(rest), sum(r[2] for r in rest),
                      False, len(TYPE_GROUPS) - 1, MERGED_FLAG)
            rows = rows[:RANK_MAX_ROWS] + [merged]
        if not rows:
            cv.create_text(320, 220, text="此文件夹为空（或因权限不足未读取）", fill=self.t["rsub"],
                           font=(fname, 11))
            cv.configure(scrollregion=(0, 0, 640, 400))
            return

        cw = max(cv.winfo_width(), 640)
        ch = max(cv.winfo_height(), 400)
        self.rank_cw = cv.winfo_width()
        rowh = int(50 * UI_SCALE)
        barh, top = int(22 * UI_SCALE), int(14 * UI_SCALE)
        name_x, bar_x = 56, 372
        maxbar = max(cw - bar_x - 104, 80)
        maxsz = rows[0][2]
        content_h = top + len(rows) * rowh + 20
        cv.configure(scrollregion=(0, 0, cw, max(content_h, ch)))
        TRACK, HOVER = self.t["track"], self.t["hover"]

        for k, (_i, name, size, is_dir, g, flags) in enumerate(rows):
            y0 = top + k * rowh + 2
            y1 = y0 + rowh - 8
            ym = (y0 + y1) / 2.0
            path = None if flags & MERGED_FLAG else os.path.join(self.rank_path, name)
            color = self.t["merged"] if flags & MERGED_FLAG else rank_color(k, self.t["bar_l"])
            # 轨道
            track = cv.create_polygon(round_rect_points(10, y0, cw - 14, y1, 16),
                                      fill=TRACK, outline="", smooth=True)
            # 名次
            rank_txt = "…" if flags & MERGED_FLAG else str(k + 1)
            cv.create_text(24, ym, text=rank_txt, anchor="w", fill=color,
                           font=(fname, 12, "bold"))
            # 隐藏/系统标记：直接写「隐」「系」小徽章，比黄红圆点一眼能认
            tx = name_x
            for bit, ch, bgc, fgc in ((1, "隐", "#f1c40f", "#1a1a1a"),
                                      (2, "系", "#e74c3c", "#ffffff")):
                if flags & bit:
                    cv.create_rectangle(tx, y0 + 10, tx + 18, y0 + 24,
                                        fill=bgc, outline="")
                    cv.create_text(tx + 9, y0 + 17, text=ch, fill=fgc,
                                   font=(fname, 8, "bold"))
                    tx += 22
            # 名称 + 副标题
            cv.create_text(tx, y0 + 13, text=_clip(name, bar_x - name_x - 14), anchor="w",
                           fill=self.t["rname"], font=(fname, 10, "bold"))
            pct = size / total * 100.0
            if flags & MERGED_FLAG:
                sub = "已合并 %d 个过小项 · %.1f%%" % (
                    int(name.replace("其他 ", "").replace(" 项", "")), pct)
            elif is_dir:
                crec = self.result.folders.get(path)
                nf = crec["nfiles"] if crec else 0
                sub = "文件夹 · {:,} 个文件 · {:.1f}%".format(nf, pct)
            else:
                ext = os.path.splitext(name)[1].lstrip(".").lower()
                sub = "%s%s · %.1f%%" % (TYPE_GROUPS[g][0],
                                         ("（.%s）" % ext) if ext else "（无扩展名）", pct)
            cv.create_text(tx, y0 + 31, text=sub, anchor="w", fill=self.t["rsub"],
                           font=(fname, 8))
            # 横条
            w = max(2.0, size / maxsz * maxbar)
            by0, by1 = ym - barh / 2.0, ym + barh / 2.0
            init_w = 1.0 if animate else w
            bar = cv.create_polygon(round_rect_points(bar_x, by0, bar_x + init_w, by1, barh / 2),
                                    fill=color, outline="", smooth=True)
            # 数值（条尾右侧）
            label = cv.create_text(bar_x + (w if not animate else 1) + 8, ym,
                                   text=human_size(size), anchor="w", fill=self.t["rname"],
                                   font=(fname, 9, "bold"))
            self.rank_rows.append({"path": path, "name": name, "size": size,
                                   "is_dir": is_dir, "flags": flags, "g": g, "track": track,
                                   "bar": bar, "label": label, "bx": bar_x, "by0": by0,
                                   "by1": by1, "w": w, "color": color, "y0": y0, "y1": y1,
                                   "rounded": True})

        if animate:
            self.rank_animating = True
            self.rank_pending_anim = False
            t0 = time.perf_counter()

            def tick():
                if self._closed:
                    return
                now = (time.perf_counter() - t0) * 1000.0
                all_done = True
                for k, r in enumerate(self.rank_rows):
                    delay = min(k, 12) * 20.0
                    p = (now - delay) / RANK_ANIM_MS
                    if p < 1:
                        all_done = False
                        p = max(p, 0.0)
                    else:
                        p = 1.0
                    e = 1 - (1 - p) ** 3      # ease-out cubic
                    w = r["w"] * e
                    x2 = r["bx"] + max(w, 1.0)
                    cv.coords(r["bar"], *round_rect_points(r["bx"], r["by0"], x2, r["by1"],
                                                           (r["by1"] - r["by0"]) / 2.0))
                    cv.coords(r["label"], x2 + 6, (r["by0"] + r["by1"]) / 2.0)
                if not all_done:
                    self.rank_anim_after = self.after(RANK_FPS_MS, tick)
                else:
                    self.rank_anim_after = None
                    self.rank_animating = False

            tick()

    def _rank_finalize_bars(self):
        """动画结束后把直角条替换为圆角条。"""
        cv = self.rank_canvas
        for r in self.rank_rows:
            if r["rounded"]:
                continue
            cv.delete(r["bar"])
            r["bar"] = cv.create_polygon(
                round_rect_points(r["bx"], r["by0"], r["bx"] + r["w"], r["by1"],
                                  (r["by1"] - r["by0"]) / 2.0),
                fill=r["color"], outline="", smooth=True)
            cv.tag_raise(r["bar"])
            cv.tag_raise(r["label"])
            r["rounded"] = True

    def _rank_hit(self, ev):
        cv = self.rank_canvas
        y = cv.canvasy(ev.y)
        if ev.x < 6 or ev.x > cv.winfo_width() - 6:
            return None
        for idx, r in enumerate(self.rank_rows):
            if r["y0"] <= y <= r["y1"]:
                return idx
        return None

    def _rank_click(self, ev):
        if self.rank_animating:
            return
        idx = self._rank_hit(ev)
        cv = self.rank_canvas
        cv.delete("ranksel")
        if idx is None:
            return
        r = self.rank_rows[idx]
        if r["flags"] & MERGED_FLAG:
            self.lbl_status.config(text="合并行 %s（合计 %s）：明细见右侧「当前目录内容」列表" %
                                   (r["name"], human_size(r["size"])))
            return
        if r["is_dir"]:
            self._rank_enter_path(r["path"])
            return
        # 文件：单击选中（双击才打开）——淡蓝光晕框
        draw_glow_selection(cv, 11, r["y0"] + 1, cv.winfo_width() - 15, r["y1"] - 1, 9,
                            self.t["rank_bg"], tag="ranksel")
        kind = "文件夹" if r["is_dir"] else TYPE_GROUPS[r["g"]][0]
        self.lbl_status.config(text="已选择: %s（%s · %s）· 双击打开文件，右键可在文件管理器中定位" %
                               (r["path"], kind, human_size(r["size"])))

    def _rank_double(self, ev):
        if self.rank_animating:
            return
        idx = self._rank_hit(ev)
        if idx is None:
            return
        r = self.rank_rows[idx]
        if r["flags"] & MERGED_FLAG:
            return
        if r["is_dir"]:
            self._rank_enter_path(r["path"])
        else:
            self._open_file(r["path"])

    def _rank_right(self, ev):
        if self.rank_animating:
            return
        idx = self._rank_hit(ev)
        if idx is None:
            return
        r = self.rank_rows[idx]
        if r["flags"] & MERGED_FLAG:
            return
        self._popup_for_path(r["path"], r["is_dir"], ev)

    def _rank_motion(self, ev):
        if self.rank_animating:
            return
        idx = self._rank_hit(ev)
        cur = self.rank_hover if isinstance(self.rank_hover, int) else -1
        if idx != cur:
            if 0 <= cur < len(self.rank_rows):
                self.rank_canvas.itemconfig(self.rank_rows[cur]["track"],
                                            fill=self.t["track"])
            self.rank_hover = idx if idx is not None else -1
            if idx is not None:
                self.rank_canvas.itemconfig(self.rank_rows[idx]["track"],
                                            fill=self.t["hover"])
        want_arrow = idx is not None and not (self.rank_rows[idx]["flags"] & MERGED_FLAG)
        self.rank_canvas.configure(cursor="hand2" if want_arrow else "")

    def _rank_leave(self, _ev):
        if 0 <= self.rank_hover < len(self.rank_rows):
            self.rank_canvas.itemconfig(self.rank_rows[self.rank_hover]["track"],
                                        fill=self.t["track"])
        self.rank_hover = -1
        self.rank_canvas.configure(cursor="")

    def _open_file(self, path):
        try:
            os.startfile(path)   # Windows：用默认程序直接打开文件
            self.lbl_status.config(text="已调用默认程序打开: %s" % path)
        except OSError as e:
            messagebox.showerror("无法打开", "无法打开文件:\n%s\n\n%s" % (path, e))

    # ---------------- 右键：文件管理器 / 复制路径 ----------------
    def _popup_for_path(self, path, is_dir, ev):
        m = tk.Menu(self, tearoff=0)
        if is_dir:
            m.add_command(label="在文件管理器中打开", command=lambda: self._explorer_open(path))
            m.add_command(label="在上级目录中定位", command=lambda: self._explorer_select(path))
        else:
            m.add_command(label="打开此文件（默认程序）", command=lambda: self._open_file(path))
            m.add_command(label="在文件管理器中定位（方便删除）",
                          command=lambda: self._explorer_select(path))
            m.add_command(label="打开所在文件夹", command=lambda: self._explorer_select(path))
        m.add_separator()
        m.add_command(label="复制完整路径", command=lambda: self._copy_path(path))
        try:
            m.tk_popup(ev.x_root, ev.y_root)
        finally:
            m.grab_release()

    def _on_tree_right(self, ev):
        idx = self._hit(ev)
        if idx is None:
            return
        path, _n, _s, is_dir, _g, flags, _lr, _cr, _dp, _ic = self._draw_items[idx]
        if flags & MERGED_FLAG:
            self.lbl_status.config(text="合并块由多个小文件组成，无法在文件管理器定位；请用右侧列表或大文件排行")
            return
        self._popup_for_path(path, is_dir, ev)

    def _on_child_right(self, ev):
        iid = self.child_tree.identify_row(ev.y)
        info = self._child_map.get(iid)
        if not info:
            return
        self._popup_for_path(os.path.join(self.current_path, info[0]), info[1], ev)

    def _on_big_right(self, ev):
        iid = self.big_tree.identify_row(ev.y)
        info = self._big_map.get(iid)
        if not info:
            return
        self._popup_for_path(info[0], info[1], ev)

    def _explorer_select(self, path):
        try:
            subprocess.Popen(["explorer.exe", "/select,", os.path.normpath(path)])
        except OSError as e:
            messagebox.showerror("错误", "无法打开文件管理器:\n%s" % e)

    def _explorer_open(self, path):
        try:
            subprocess.Popen(["explorer.exe", os.path.normpath(path)])
        except OSError as e:
            messagebox.showerror("错误", "无法打开文件管理器:\n%s" % e)

    def _copy_path(self, path):
        self.clipboard_clear()
        self.clipboard_append(path)
        self.lbl_status.config(text="已复制路径: %s" % path)

    def _sm_shutdown(self):
        """关掉我们自己启动的 SpaceMap（用户原本就打开着的不动）。

        必须**先关窗口再收进程**：那个浏览器窗口是 msedge.exe 的独立进程，
        只杀 SpaceMap.exe 这个服务器不会关掉它，会在桌面上留孤儿窗口。
        """
        hwnd = getattr(self, "_sm_hwnd", 0)
        if hwnd:
            try:
                import ctypes
                ctypes.windll.user32.PostMessageW(hwnd, 0x0010, 0, 0)   # WM_CLOSE
            except Exception:      # noqa: BLE001
                pass
            self._sm_hwnd = 0
        proc = getattr(self, "_sm_proc", None)
        if proc is None:
            return
        try:
            if proc.poll() is None:
                proc.terminate()
                try:
                    proc.wait(timeout=2)
                except Exception:      # noqa: BLE001
                    proc.kill()
        except Exception:      # noqa: BLE001
            pass
        self._sm_proc = None
        # 兜底：如果用户从没切到 SpaceMap 标签页，那个预热出来的窗口没被 SetParent 过，
        # 上面就没有 hwnd 可关 —— 屏幕外那些孤儿在这里统一清掉。
        try:
            self._spacemap_close_orphans()
        except Exception:      # noqa: BLE001
            pass

    def _on_close(self):
        self._closed = True
        try:
            if self.scanner:
                self.scanner.cancel.set()
        except Exception:
            pass
        self._sm_shutdown()
        self.destroy()


# ---------------------------------------------------------------- 命令行
def render_png(path, out):
    """把扫描结果的根目录矩形树图渲染成 PNG（用于演示/预览）"""
    from PIL import Image, ImageDraw, ImageFont
    s = Scanner(path)
    s.scan()
    st = s.stats
    W, H = 1280, 860
    img = Image.new("RGB", (W, H), "#ffffff")
    d = ImageDraw.Draw(img)
    try:
        f_bold = ImageFont.truetype("C:/Windows/Fonts/msyhbd.ttc", 18)
        f_norm = ImageFont.truetype("C:/Windows/Fonts/msyh.ttc", 15)
        f_small = ImageFont.truetype("C:/Windows/Fonts/msyh.ttc", 13)
    except Exception:
        f_bold = f_norm = f_small = ImageFont.load_default()

    d.text((20, 14), "空间透镜 · 矩形树图预览 · %s" % path, fill="#2c3e50", font=f_bold)
    d.text((20, 44), "总计 %s · %s 个文件 · %s 个目录 · 扫描用时 %.1fs" %
           (human_size(st.total), "{:,}".format(st.total_files),
            "{:,}".format(st.total_dirs), st.end - st.start), fill="#555", font=f_small)

    # 图例：文件块按类型着色（和 App 的「类型分布」图例同一套色）
    lx = 20
    ly = 78
    for i, (name, color, _e) in enumerate(TYPE_GROUPS):
        d.rectangle([lx, ly, lx + 14, ly + 14], fill=color)
        d.text((lx + 18, ly - 1), name, fill="#333", font=f_small)
        lx += 18 + len(name) * 15 + 24
        if lx > W - 180:
            lx = 20
            ly += 20

    # 树图区：SpaceSniffer 式嵌套布局，与 App 内画布共用同一套引擎
    tx, ty, tw, th = 20, 100, W - 40, H - 170
    boxes = nested_layout(s.folders, s.root, tx, ty, tw, th)
    for path, name, size, is_dir, gd, flags, (lx, ly, lw, lh), depth, container in boxes:
        if lw < SM_MIN_TILE or lh < SM_MIN_TILE:
            continue
        inset = 0.0 if depth == 0 else SM_PAD / 2.0
        x1, y1 = lx + inset, ly + inset
        x2, y2 = lx + lw - inset, ly + lh - inset
        if x2 - x1 < 0.8 or y2 - y1 < 0.8:
            continue
        if is_dir:
            # 文件夹：内容主类型色往白底混（与 App 浅色主题的配法一致）
            base = TYPE_GROUPS[gd][1]
            d.rectangle([x1, y1, x2, y2], fill=_blend(base, 0.86))
            if container and lw >= SM_MIN_FRAME_W and lh >= SM_MIN_FRAME_H:
                d.text((x1 + 4, y1 + SM_HEADER_H / 2.0), _clip(name, lw - 12),
                       fill=base, font=f_small, anchor="lm")
            elif not container:
                d.rectangle([x1, y1, x2, y2], outline=base)
        else:
            d.rectangle([x1, y1, x2, y2], fill=TYPE_GROUPS[gd][1])
            cx, cy = (x1 + x2) / 2.0, (y1 + y2) / 2.0
            if lw >= 52 and lh >= 34:
                d.text((cx, cy - 9), _clip(name, lw - 10), fill="white", font=f_norm, anchor="mm")
                d.text((cx, cy + 9), human_size(size), fill="white", font=f_small, anchor="mm")
            elif lw >= 34 and lh >= 18:
                d.text((cx, cy), _clip(name, lw - 8), fill="white", font=f_small, anchor="mm")
    d.text((20, H - 60),
           "注: 颜色 = 文件类型（与「类型分布」图例一致），文件夹取其中占比最大的类型；"
           "每层内缩 1px 露出的底色即层级网格线。有 %d 个目录因权限不足未读取。" % st.skipped,
           fill="#888", font=f_small)
    img.save(out, "PNG")


def main():
    write_user_ext_map_example()      # 首次运行生成一份空的扩展名映射，方便自己补
    args = sys.argv[1:]
    if args and args[0] == "--selftest" and len(args) >= 2:
        path = args[1]
        t0 = time.time()
        s = Scanner(path)
        s.scan()
        dt = time.time() - t0
        st = s.stats
        print("路径: %s" % path)
        print("耗时: %.1fs（%d 线程）" % (dt, s.nthreads))
        print("总计: %s  文件 %s 个  目录 %s 个  跳过(权限) %s 个" %
              (human_size(st.total), "{:,}".format(st.total_files),
               "{:,}".format(st.total_dirs), st.skipped))
        print("隐藏文件: %s 个 / %s    系统文件: %s 个 / %s" %
              ("{:,}".format(st.hidden_files), human_size(st.hidden_bytes),
               "{:,}".format(st.system_files), human_size(st.system_bytes)))
        print("类型分布:")
        for i, (b, c) in enumerate(s.type_stats()):
            if b > 0:
                print("  %-6s %10s  %5.1f%%  %s 个文件" %
                      (TYPE_GROUPS[i][0], human_size(b),
                       b / st.total * 100 if st.total else 0, "{:,}".format(c)))
        print("最大 15 个文件:")
        for size, path2, name, g, flags in sorted(s.top_files, reverse=True)[:15]:
            mark = " [隐藏]" if flags & 1 else (" [系统]" if flags & 2 else "")
            print("  %10s  %s%s" % (human_size(size), path2, mark))
        return
    if args and args[0] == "--render" and len(args) >= 3:
        render_png(args[1], args[2])
        print("已渲染: %s" % args[2])
        return
    if args and args[0] == "--smoke":
        app = App()
        app.after(1500, app.destroy)
        app.mainloop()
        print("GUI 启动正常")
        return
    app = App()
    app.mainloop()


if __name__ == "__main__":
    main()
