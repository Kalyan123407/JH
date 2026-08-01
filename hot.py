import json
import sys
import re
import random
import threading
from typing import Optional, List, Tuple
from urllib import request, parse
import os
from concurrent.futures import ThreadPoolExecutor, as_completed
from urllib.parse import urlparse, urlunparse, urlencode, parse_qs, unquote
import uuid
import time
import subprocess
from datetime import datetime

# =========================
# TERMUX COLOR CODES
# =========================

BLACK   = "\033[30m"
RED     = "\033[91m"
GREEN   = "\033[92m"
YELLOW  = "\033[93m"
BLUE    = "\033[94m"
MAGENTA = "\033[95m"
CYAN    = "\033[96m"
WHITE   = "\033[97m"

DARK_RED     = "\033[31m"
DARK_GREEN   = "\033[32m"
DARK_YELLOW  = "\033[33m"
DARK_BLUE    = "\033[34m"
DARK_MAGENTA = "\033[35m"
DARK_CYAN    = "\033[36m"
GRAY         = "\033[90m"

BOLD_RED     = "\033[1;91m"
BOLD_GREEN   = "\033[1;92m"
BOLD_YELLOW  = "\033[1;93m"
BOLD_BLUE    = "\033[1;94m"
BOLD_MAGENTA = "\033[1;95m"
BOLD_CYAN    = "\033[1;96m"
BOLD_WHITE   = "\033[1;97m"

UNDERLINE = "\033[4m"
RESET = "\033[0m"

API_TEMPLATE = "https://www.hotstar.com/api/internal/bff/v2/slugs/in/{slug_path}/watch"

TOKEN_FILE = "token.txt"

# Global override for multi-token rotation in auto-update mode
_ACTIVE_TOKEN_OVERRIDE: Optional[str] = None

LANGUAGES={
"eng":"ENGLISH",
"en":"ENGLISH",
"hin":"HINDI",
"hi":"HINDI",
"hd":"HINDI HD",
"mar":"MARATHI",
"mr":"MARATHI",
"ma":"MARATHI",
"guj":"GUJARATI",
"gu":"GUJARATI",
"bho":"BHOJPURI",
"bh":"BHOJPURI",
"bih":"BHOJPURI",
"pan":"PUNJABI",
"pun":"PUNJABI",
"pa":"PUNJABI",
"pu":"PUNJABI",
"har":"HARYANVI",
"hv":"HARYANVI",
"ha":"HARYANVI",
"tam":"TAMIL",
"ta":"TAMIL",
"tel":"TELUGU",
"te":"TELUGU",
"kan":"KANNADA",
"kn":"KANNADA",
"mal":"MALAYALAM",
"ml":"MALAYALAM",
"ben":"BENGALI",
"bn":"BENGALI",
"ori":"ORIYA",
"or":"ORIYA",
}

# ===================== UNIQUE_LANGUAGES =====================
# Har language ke liye sirf ek primary code — request count ~30 se 12 ho jaata hai
# LANGUAGES (aliases) lookup/detection ke liye waise hi rehta hai
_seen_lang_names = set()
_skip_lang_names = {"HINDI HD", "ORIYA"}
UNIQUE_LANGUAGES = {}
for _lc, _ln in LANGUAGES.items():
    if _ln in _skip_lang_names:
        continue
    if _ln not in _seen_lang_names:
        _seen_lang_names.add(_ln)
        UNIQUE_LANGUAGES[_lc] = _ln
del _seen_lang_names, _skip_lang_names, _lc, _ln

# ===================== BLACKLIST CDNs for Options 12 & 13 =====================
BLACKLIST_CDNS = {
    "live-cf.cdn.hotstar.com",
    "abc3qs2aaaaaaaamgeckebpooksaa.live-cf.cdn.hotstar.com",
}
def is_blacklisted_cdn(host: str) -> bool:
    if host in BLACKLIST_CDNS:
        return True
    if host.endswith(".live-cf.cdn.hotstar.com"):
        return True
    return False

# ===================== OPTION 5 – CDN HOST LIST & URL REWRITERS =====================
# Full list of clean Akamai hotstar CDN hosts (live01p–live99p).
CDN_HOSTS = [
    "live07p.hotstar.com", "live08p.hotstar.com", "live09p.hotstar.com",
    "live10p.hotstar.com", "live11p.hotstar.com", "live12p.hotstar.com",
    "live13p.hotstar.com", "live14p.hotstar.com", "live15p.hotstar.com",
    "live16p.hotstar.com", "live17p.hotstar.com", "live18p.hotstar.com",
    "live19p.hotstar.com", "live20p.hotstar.com", "live21p.hotstar.com",
    "live22p.hotstar.com", "live23p.hotstar.com", "live24p.hotstar.com",
]
CDN_HOSTS_SET = set(CDN_HOSTS)

# CloudFront params that are CF-only and useless on Akamai CDN → strip them
_CF_STRIP_PARAMS = {"Signature", "Expires", "Key-Pair-Id"}

def _extract_live_prefix(playback_host: str) -> str:
    """Extract 'live11p' style prefix from a pristine host string.
    Only matches the plain 'liveNNp-...' pattern (digits immediately followed by 'p').
    The 'liveNNmp-...' multi-package variant (used by Haryanvi/Telugu and similar) is a
    DIFFERENT backend that serves a different path namespace (/out/v1/...) — it is NOT
    reachable via liveNNp.hotstar.com, so this deliberately does NOT match it, which makes
    the caller skip the rewrite and leave those streams on their original working host."""
    m = re.match(r"(live\d+p)", playback_host)
    return m.group(1) if m else ""

def rewrite_url_to_clean_cdn(url: str) -> str:
    """
    Rewrite any Hotstar SSAI/CF URL to a clean liveXXp.hotstar.com URL.

    Steps:
      1. Read playback_host param  → extract live prefix (e.g. live11p)
      2. Build clean_host = live11p.hotstar.com, verify it's in CDN_HOSTS_SET
      3. Replace netloc with clean_host
      4. Strip CloudFront-only params (Signature, Expires, Key-Pair-Id)
         — done on the RAW query string to avoid double-encoding hdnea token.

    Works for BOTH flavours Hotstar returns:
      • Akamai SSAI  →  live11p-ssai-akt-mum.cdn.hotstar.com  → live11p.hotstar.com
      • CloudFront   →  abhl7x…live-ssai-cf-mum-ace.cdn.hotstar.com → live11p.hotstar.com
        (CF-only auth params also stripped; hdnea token kept as-is, no re-encoding)

    Returns the original URL unchanged on any error.
    """
    try:
        parsed = urlparse(url)
        raw_query = parsed.query  # e.g. "a=s&hdnea=exp%3D...~hmac%3D..."

        # 1. Extract playback_host from raw query to find live prefix
        ph_match = re.search(r'(?:^|&)playback_host=([^&]+)', raw_query)
        if not ph_match:
            return url
        playback_host_val = parse.unquote(ph_match.group(1))
        live_prefix = _extract_live_prefix(playback_host_val)
        if not live_prefix:
            return url

        clean_host = f"{live_prefix}.hotstar.com"
        if clean_host not in CDN_HOSTS_SET:
            return url

        # 2. Strip CF-only params from the raw query string (no re-encoding at all)
        #    Each param is "key=value" or "key=val%xx..." — split by & and filter.
        cf_strip_lower = {k.lower() for k in _CF_STRIP_PARAMS}
        kept_parts = []
        for part in raw_query.split("&"):
            if not part:
                continue
            key = part.split("=", 1)[0].strip()
            if key.lower() in cf_strip_lower:
                continue
            kept_parts.append(part)
        new_query = "&".join(kept_parts)

        # 3. Replace host, keep scheme/path/query exactly as-is
        rewritten = parsed._replace(netloc=clean_host, query=new_query)
        return urlunparse(rewritten)
    except Exception:
        return url

def extract_hdntl_from_url(url: str) -> str:
    """Extract hdntl cookie value from URL query parameters"""
    try:
        parsed = urlparse(url)
        params = parse_qs(parsed.query)
        if 'hdnea' in params and params['hdnea']:
            return params['hdnea'][0]
        if 'hdntl' in params and params['hdntl']:
            return params['hdntl'][0]
    except:
        pass
    return ""


HEADERS_BASE = {
    "User-Agent": "Hotstar;in.startv.hotstar.dplus.tv/26.05.10.2 (Android/14; tv)",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "en",
    "Connection": "keep-alive",
    "Sec-Fetch-Dest": "empty",
    "Sec-Fetch-Mode": "cors",
    "Sec-Fetch-Site": "same-origin",
    "x-hs-retry-count": "0",
    "X-HS-Platform": "androidtv",
    "X-Country-Code": "in",
    "X-HS-Accept-language": "eng",
    "x-hs-is-retry": "false",
    "X-HS-Client": "platform:androidtv;app_id:in.startv.hotstar.dplus.tv;app_version:26.05.10.2;os:Android;os_version:14;schema_version:0.0.1690",
    "x-hs-app": "260510002",
    "Alt-Used": "www.hotstar.com",
    "Pragma": "no-cache",
    "Cache-Control": "no-cache",
}

# ===================== UNLIMITED DEVICE POOL (5-HOUR COOLDOWN) =====================
# On-the-fly generation — combination space:
#   Year(24-26) × Month(1-12) × Day(1-28) × Build(0-9) = 10,080 app versions
#   × ATV OS(10-15)=6  +  Android OS(9-15)=7
#   = 60,480 ATV profiles + 70,560 Android profiles = 131,040 total unique profiles
# Each profile locked for 5 hours after use. Effectively unlimited for any real workload.

import threading as _dev_threading

DEVICE_COOLDOWN_SEC = 5 * 3600  # 5 hours

_device_last_used: dict = {}    # key (platform, os_ver, app_ver) → timestamp
_device_lock = _dev_threading.Lock()

def _gen_random_app_version():
    year  = random.randint(24, 26)
    month = random.randint(1, 12)
    day   = random.randint(1, 28)   # safe for all months
    build = random.randint(0, 9)
    ver   = f"{year}.{month:02d}.{day:02d}.{build}"
    code  = f"{year}{month:02d}{day:02d}{build:03d}"
    return ver, code

def _gen_random_os_version(platform: str) -> str:
    return str(random.randint(10, 15)) if platform == "androidtv" else str(random.randint(9, 15))

def _build_device_profile(platform: str, os_ver: str, app_ver: str, app_code: str) -> tuple:
    if platform == "androidtv":
        ua     = f"Hotstar;in.startv.hotstar.dplus.tv/{app_ver} (Android/{os_ver}; tv)"
        client = (f"platform:androidtv;app_id:in.startv.hotstar.dplus.tv;"
                  f"app_version:{app_ver};os:Android;os_version:{os_ver};schema_version:0.0.1690")
    else:
        ua     = f"Hotstar;in.startv.hotstar/{app_ver} (Android/{os_ver})"
        client = (f"platform:android;app_id:in.startv.hotstar;"
                  f"app_version:{app_ver};os:Android;os_version:{os_ver};schema_version:0.0.1690")
    return ua, client, app_code

def _get_device(platform: str) -> tuple:
    """
    Return (user_agent, client_string, app_code) for platform.
    Tries up to 200 random combos to find one outside the 5-hr cooldown.
    Falls back to LRU if all attempts fail (should never happen in practice).
    """
    now = time.time()
    for _ in range(200):
        app_ver, app_code = _gen_random_app_version()
        os_ver = _gen_random_os_version(platform)
        key = (platform, os_ver, app_ver)
        with _device_lock:
            if now - _device_last_used.get(key, 0) >= DEVICE_COOLDOWN_SEC:
                _device_last_used[key] = now
                return _build_device_profile(platform, os_ver, app_ver, app_code)
    # Fallback: pick LRU from what we've seen
    with _device_lock:
        if _device_last_used:
            oldest = min(_device_last_used, key=lambda k: _device_last_used[k])
            p, ov, av = oldest
            parts = av.split(".")
            ac = "".join(parts[:3]) + f"{int(parts[3]):03d}" if len(parts) == 4 else "260510002"
            _device_last_used[oldest] = now
            return _build_device_profile(p, ov, av, ac)
    return _build_device_profile(platform, "14", "26.05.10.2", "260510002")

def _get_atv_device() -> tuple:
    """Pick a fresh AndroidTV device profile (5-hr cooldown, 60K+ combos)."""
    return _get_device("androidtv")

def _get_android_device() -> tuple:
    """Pick a fresh Android phone device profile (5-hr cooldown, 70K+ combos)."""
    return _get_device("android")

# Legacy helpers kept for any remaining direct calls
def random_device_id() -> str:
    return str(uuid.uuid4())

def random_request_id() -> str:
    return str(uuid.uuid4())

# ---- Header builders (platform-strict) ----

def build_jhs_headers():
    """AndroidTV only — uses ATV device pool."""
    ua, cs, app_code = _get_atv_device()
    headers = HEADERS_BASE.copy()
    headers["User-Agent"]        = ua
    headers["X-HS-Client"]       = cs
    headers["X-HS-Platform"]     = "androidtv"
    headers["x-hs-app"]          = app_code
    headers["X-Request-Id"]      = str(uuid.uuid4())
    headers["x-hs-request-id"]   = str(uuid.uuid4())
    headers["x-hs-device-id"]    = str(uuid.uuid4())
    headers["x-hs-usertoken"]    = load_user_token()
    return headers

def build_jhs_headers_android():
    """Android phone only — uses Android device pool."""
    ua, cs, app_code = _get_android_device()
    headers = HEADERS_BASE.copy()
    headers.update({
        "User-Agent":           ua,
        "Accept":               "application/json, text/plain, */*",
        "Accept-Language":      "eng",
        "Referer":              "https://www.hotstar.com/in/explore?search_query=live",
        "Connection":           "keep-alive",
        "Sec-Fetch-Dest":       "empty",
        "Sec-Fetch-Mode":       "no-cors",
        "Sec-Fetch-Site":       "same-origin",
        "TE":                   "trailers",
        "x-hs-retry-count":     "0",
        "X-HS-Platform":        "android",
        "X-Country-Code":       "in",
        "X-HS-Accept-language": "eng",
        "X-Request-Id":         str(uuid.uuid4()),
        "x-hs-device-id":       str(uuid.uuid4()),
        "x-hs-is-retry":        "false",
        "x-hs-request-id":      str(uuid.uuid4()),
        "X-HS-Client":          cs,
        "x-hs-app":             app_code,
        "Alt-Used":             "www.hotstar.com",
        "Pragma":               "no-cache",
        "Cache-Control":        "no-cache",
        "Priority":             "u=4",
    })
    headers["x-hs-usertoken"] = load_user_token()
    return headers

def build_ott_url(stream_url, hdntl):
    clean_url = stream_url.split("?")[0]
    final = (
        f"{clean_url}?|"
        f"Cookie=hdntl={hdntl}"
        f"&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)"
        f"&Referer=https://www.hotstar.com/"
        f"&Origin=https://www.hotstar.com"
    )
    return final

def build_ott_drm_url(mpd_url: str, key_str: str) -> str:
    """Build OTT Navigator / pipe-format DRM URL for clearkey MPD streams."""
    # Decode percent-encoded chars (%2f→/ %3d→= %2a→* etc.) so OTT Navigator
    # can correctly pass the hdnea token to the CDN (movie URLs come pre-encoded)
    base, _, query = mpd_url.partition("?")
    decoded_url = f"{base}?{unquote(query)}" if query else base
    final = (
        f"{decoded_url}"
        f"|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)"
        f"&Referer=https://www.hotstar.com/"
        f"&Origin=https://www.hotstar.com"
        f"&drmScheme=clearkey"
        f"&drmLicense={key_str}"
    )
    return final

def build_ott_drm_url_direct(mpd_url: str, key_str: str = "", hdntl_cookie: str = "") -> str:
    """Build OTT Navigator / NS Player pipe-URL from a raw MPD URL with optional cookie + clearkey.
    Strips hdnea query entirely — auth is provided by the hdntl cookie instead."""
    base = mpd_url.partition("?")[0]  # strip all query params (hdnea etc.)
    parts = [
        f"{base}?",  # NS Player expects base?| format
        "|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)",
        "&Referer=https://www.hotstar.com/",
        "&Origin=https://www.hotstar.com",
    ]
    if hdntl_cookie:
        parts.append(f"&Cookie=hdntl={hdntl_cookie}")
    if key_str:
        parts.append("&drmScheme=clearkey")
        parts.append(f"&drmLicense={key_str}")
    return "".join(parts)

def load_user_token(token_path: str = TOKEN_FILE) -> str:
    global _ACTIVE_TOKEN_OVERRIDE
    if _ACTIVE_TOKEN_OVERRIDE is not None:
        return _ACTIVE_TOKEN_OVERRIDE
    try:
        with open(token_path, "r", encoding="utf-8") as token_file:
            token = token_file.read().strip()
            return token
    except:
        return ""

def check_token_valid(token: str, slug_path: str = "sports/cricket") -> bool:
    """HTTP check — returns False on 401/403 OR if response body shows auth failure.
    Hotstar returns 200 OK for expired tokens but with no 'success' key in body.
    Uses short connection+read timeout so it never hangs the main loop."""
    try:
        test_url = f"https://www.hotstar.com/api/internal/bff/v2/slugs/in/{slug_path}/watch"
        _h = HEADERS_BASE.copy()
        _h["x-hs-usertoken"] = token
        _h["X-Request-Id"] = str(uuid.uuid4())
        _h["x-hs-request-id"] = str(uuid.uuid4())
        _h["x-hs-device-id"] = str(uuid.uuid4())
        req = request.Request(test_url, headers=_h)
        with request.urlopen(req, timeout=10) as resp:
            body = resp.read(4096)  # read enough bytes to parse JSON response
        try:
            data = json.loads(body)
            # Valid tokens → Hotstar returns {"success": { ... }} with actual content
            # Expired/invalid tokens → "success" key missing or empty dict {}
            if "success" not in data or not data.get("success"):
                return False
        except Exception:
            pass  # JSON parse failed → can't determine from body, assume OK
        return True
    except Exception as _e:
        _code = getattr(_e, "code", None)
        if _code in (401, 403):
            return False
        # timeout / DNS / SSL / other network errors → assume token OK, don't mark expired
        return True

def build_headers() -> dict:
    """AndroidTV only — uses ATV device pool with 1-hr cooldown."""
    ua, cs, app_code = _get_atv_device()
    headers = HEADERS_BASE.copy()
    headers["User-Agent"]       = ua
    headers["X-HS-Client"]      = cs
    headers["X-HS-Platform"]    = "androidtv"
    headers["x-hs-app"]         = app_code
    headers["X-Request-Id"]     = str(uuid.uuid4())
    headers["x-hs-request-id"]  = str(uuid.uuid4())
    headers["x-hs-device-id"]   = str(uuid.uuid4())
    headers["x-hs-usertoken"]   = load_user_token()
    return headers

def extract_hdntl(url):
    parsed = urlparse(url)
    query = parse_qs(parsed.query)
    token = ""
    if "hdntl" in query:
        token = query["hdntl"][0]
    elif "hdnea" in query:
        token = query["hdnea"][0]
    if not token:
        return ""
    token = re.sub(r"st=\d+~", "", token)
    return token

def extract_slug_path(url: str) -> Optional[str]:
    value = url.strip()
    parsed = parse.urlparse(value)
    path = parsed.path if parsed.scheme else value
    segments = [s for s in path.split("/") if s]
    if not segments:
        return None
    if segments[0] == "in":
        segments = segments[1:]
    if segments and segments[-1] == "watch":
        segments = segments[:-1]
    return "/".join(segments)

def build_jhs_api_url(slug_path: str, lang: str, is_live: bool = False):
    if is_live:
        capabilities = {
            "ads": ["ssai"],
            "audio_channel": ["stereo"],
            "container": ["ts"],
            "dvr": ["short"],
            "dynamic_range": ["sdr"],
            "encryption": ["plain"],
            "ladder": ["phone"],
            "package": ["hls"],
            "resolution": ["hd", "fhd"],
            "video_codec": ["h264"]
        }
        drm = {"widevine_security_level": ["SW_SECURE_DECODE"]}
    else:
        capabilities = {
            "ads": ["non_ssai"],
            "audio_channel": ["stereo"],
            "container": ["fmp4", "fmp4br", "ts"],
            "dvr": ["short"],
            "dynamic_range": ["sdr"],
            "encryption": ["plain"],
            "ladder": ["web", "tv", "full", "phone"],
            "package": ["hls"],
            "resolution": ["sd", "hd", "fhd"],
            "video_codec": ["h264", "h265"],
            "video_codec_non_secure": ["h264", "h265"]
        }
        drm = {
            "hdcp_version": ["HDCP_V2_2"],
            "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"]
        }
    return (
        API_TEMPLATE.format(slug_path=slug_path)
        + "?search_query=live"
        + "&client_capabilities=" + parse.quote(json.dumps(capabilities, separators=(",", ":")))
        + "&drm_parameters=" + parse.quote(json.dumps(drm, separators=(",", ":")))
        + "&request_features=consent_supported"
        + "&lang=" + parse.quote(lang)
    )

def build_jhs_4k_api_url(slug_path: str, lang: str, is_live: bool = False):
    if is_live:
        capabilities = {
            "ads": ["ssai"],
            "audio_channel": ["stereo", "dolby51", "atmos"],
            "container": ["ts", "fmp4"],
            "dvr": ["short"],
            "dynamic_range": ["sdr", "hdr"],
            "encryption": ["plain"],
            "ladder": ["tv", "full"],
            "package": ["hls", "dash"],
            "resolution": ["hd", "fhd", "4k"],
            "true_resolution": ["hd", "4k"],
            "video_codec": ["h265", "h264"]
        }
        drm = {"widevine_security_level": ["SW_SECURE_DECODE"]}
    else:
        capabilities = {
            "ads": ["non_ssai"],
            "audio_channel": ["stereo", "dolby51", "atmos"],
            "container": ["fmp4", "fmp4br", "ts"],
            "dvr": ["short", "long"],
            "dynamic_range": ["sdr", "hdr"],
            "encryption": ["plain"],
            "ladder": ["tv", "full", "web", "phone"],
            "package": ["hls", "dash"],
            "resolution": ["sd", "hd", "fhd", "4k"],
            "true_resolution": ["hd", "4k"],
            "video_codec": ["h265", "h264"],
            "video_codec_non_secure": ["h265", "h264", "vp9"]
        }
        drm = {
            "hdcp_version": ["HDCP_V2_2"],
            "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"]
        }
    return (
        API_TEMPLATE.format(slug_path=slug_path)
        + "?search_query=live"
        + "&client_capabilities=" + parse.quote(json.dumps(capabilities, separators=(",", ":")))
        + "&drm_parameters=" + parse.quote(json.dumps(drm, separators=(",", ":")))
        + "&request_features=consent_supported"
        + "&lang=" + parse.quote(lang)
    )

def build_api_url(slug_path: str, lang: str, quality_choice: str) -> str:
    if quality_choice == "1":
        capabilities = {
            "ads": ["non_ssai"],
            "audio_channel": ["stereo", "dolby51", "atmos"],
            "container": ["fmp4", "fmp4br", "ts"],
            "dvr": ["short", "long"],
            "dynamic_range": ["sdr", "hdr"],
            "encryption": ["widevine", "plain"],
            "ladder": ["tv", "full"],
            "package": ["dash", "hls"],
            "resolution": ["sd", "hd", "fhd", "4k"],
            "true_resolution": ["hd", "4k"],
            "video_codec": ["h265", "h264"],
            "video_codec_non_secure": ["h265", "h264", "vp9"]
        }
    else:
        capabilities = {
            "ads": ["non_ssai", "ssai"],
            "audio_channel": ["stereo"],
            "container": ["fmp4", "fmp4br", "ts"],
            "dvr": ["short"],
            "dynamic_range": ["sdr"],
            "encryption": ["widevine", "plain"],
            "ladder": ["web", "tv", "phone"],
            "package": ["dash", "hls"],
            "resolution": ["sd", "hd", "fhd"],
            "video_codec": ["h264", "h265"],
            "video_codec_non_secure": ["h264", "h265"]
        }
    drm = {
        "hdcp_version": ["HDCP_V2_2"],
        "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"]
    }
    return (
        API_TEMPLATE.format(slug_path=slug_path)
        + "?search_query=live"
        + "&client_capabilities=" + parse.quote(json.dumps(capabilities, separators=(",", ":")))
        + "&drm_parameters=" + parse.quote(json.dumps(drm, separators=(",", ":")))
        + "&request_features=consent_supported"
        + "&lang=" + parse.quote(lang)
    )

def extract_match_title(url: str) -> Tuple[str, str]:
    slug = extract_slug_path(url)
    if not slug: return "HOTSTAR CONTENT", ""
    parts = slug.split('/')
    match_no = ""
    match_search = re.search(r'(match[-_]?\d+|\bm\d+\b)', slug.lower())
    if match_search:
        match_no = match_search.group(1).replace('match', 'MATCH-').replace('m', 'MATCH-').upper()
        match_no = re.sub(r'-+', '-', match_no)
    for p in parts:
        if any(x in p for x in ["tata-ipl", "-vs-", "highlights", "replay"]):
            clean_name = p.replace('-highlights', '').replace('-replay', '').replace('-video', '')
            clean_name = re.sub(r'match[-_]?\d+|m\d+', '', clean_name)
            return clean_name.strip('-').replace('-', ' ').upper(), match_no
    name = parts[1] if len(parts) > 1 else parts[0]
    return name.replace('-', ' ').upper(), match_no

def extract_stream_type(url: str) -> str:
    u = url.lower()
    if "replay" in u: return "REPLAY"
    if "highlights" in u: return "HIGHLIGHTS"
    if "clips" in u: return "CLIP"
    if "/movies/" in u: return "MOVIE"
    if "/sports/" in u and "/video/live/" in u: return "LIVE TV"
    if "/tv/" in u and "live" in u: return "LIVE TV"
    if "/shows/" in u: return "TV SHOW"
    return "STREAM"

def extract_best_stream(player_config: dict, input_url: str) -> Optional[str]:
    media_assets = []
    stype = extract_stream_type(input_url)
    for key in ["media_asset", "media_asset_v2"]:
        asset = player_config.get(key)
        if isinstance(asset, dict):
            media_assets.append(asset)
        elif isinstance(asset, list):
            media_assets.extend(asset)
    for asset in media_assets:
        for key in ["fallback", "primary"]:
            try:
                url = asset[key]["content_url"]
                if not url:
                    continue
                if ".m3u8" not in url and ".mpd" not in url:
                    continue
                base_url = url.split("?")[0]
                if ".mpd" in base_url:
                    return url
                candidates = [
                    base_url.replace("_fhd", "_fhd").replace("/fhd/", "/fhd/"),
                    base_url.replace("_fhd", "_hd").replace("/fhd/", "/hd/").replace("_hd", "_hd"),
                    base_url.replace("_fhd", "_sd").replace("/fhd/", "/sd/").replace("/hd/", "/sd/").replace("_hd", "_sd"),
                ]
                seen = set()
                candidates = [c for c in candidates if not (c in seen or seen.add(c))]
                final_url = candidates[0]
                if stype in ["LIVE TV", "MOVIE", "TV SHOW"]:
                    return url
                elif stype == "REPLAY":
                    clean = url.split("?")[0]
                    path = clean.rsplit("/", 1)[0]
                    return path + "/index_7.m3u8"
                elif stype in ["HIGHLIGHTS", "CLIP"]:
                    return final_url.split("?")[0]
                return final_url
            except:
                pass
    return None

def extract_4k_streams(player_config: dict):
    streams = []
    for key in ["media_asset", "media_asset_v2"]:
        assets = player_config.get(key)
        if not assets: continue
        if isinstance(assets, dict):
            assets = [assets]
        for asset in assets:
            for variant in ["fallback", "primary"]:
                item = asset.get(variant)
                if not isinstance(item, dict): continue
                url = item.get("content_url")
                if not url: continue
                tags = str(item.get("playback_tags", "")).lower()
                height = int(item.get("height") or 0)
                video_quality = str(item.get("video_quality", "")).lower()
                resolution = str(item.get("resolution", "")).lower()
                url_lower = url.lower()
                is_4k = (
                    "4k" in tags or height >= 2160 or "4k" in video_quality or
                    "4k" in resolution or "_4k" in url_lower or "/4k/" in url_lower
                )
                if is_4k:
                    streams.append({"url": url, "height": height, "type": variant.upper()})
    return streams

def extract_jhs_fallback_only(player_config):
    streams = []
    for key in ["media_asset", "media_asset_v2"]:
        assets = player_config.get(key)
        if not assets:
            continue
        if isinstance(assets, dict):
            assets = [assets]
        for asset in assets:
            for variant in ["fallback", "primary"]:
                item = asset.get(variant)
                if not isinstance(item, dict):
                    continue
                url = item.get("content_url")
                if url and (".m3u8" in url or ".mpd" in url):
                    streams.append({"content_url": url, "type": variant, "playback_tags": item.get("playback_tags", "")})
    return streams

def build_drm_api_url(slug_path: str, lang: str = "eng") -> str:
    capabilities = {
        "ads": ["non_ssai"],
        "audio_channel": ["stereo", "dolby51", "atmos"],
        "container": ["fmp4", "fmp4br", "ts"],
        "dvr": ["short", "long"],
        "dynamic_range": ["sdr", "hdr"],
        "encryption": ["widevine", "plain"],
        "ladder": ["tv", "full"],
        "package": ["dash", "hls"],
        "resolution": ["sd", "hd", "fhd", "4k"],
        "true_resolution": ["hd", "4k"],
        "video_codec": ["h265", "h264"],
        "video_codec_non_secure": ["h265", "h264", "vp9"]
    }
    drm = {
        "hdcp_version": ["HDCP_V2_2"],
        "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"]
    }
    return (
        API_TEMPLATE.format(slug_path=slug_path)
        + "?search_query=live"
        + "&client_capabilities=" + parse.quote(json.dumps(capabilities, separators=(",", ":")))
        + "&drm_parameters=" + parse.quote(json.dumps(drm, separators=(",", ":")))
        + "&request_features=consent_supported"
        + "&lang=" + parse.quote(lang)
    )

def extract_drm_info(player_config: dict) -> list:
    results = []
    seen = set()
    def find_license(obj, depth=0):
        if depth > 6 or not isinstance(obj, (dict, list)):
            return None
        if isinstance(obj, list):
            for item in obj:
                r = find_license(item, depth+1)
                if r: return r
        elif isinstance(obj, dict):
            for k in ["license_url", "licenseUrl", "widevine_license_url", "keyServerUrl", "key_server_url"]:
                if k in obj and obj[k]:
                    return str(obj[k])
            for v in obj.values():
                r = find_license(v, depth+1)
                if r: return r
        return None
    license_url = find_license(player_config)
    for key in ["media_asset", "media_asset_v2"]:
        assets = player_config.get(key)
        if not assets:
            continue
        if isinstance(assets, dict):
            assets = [assets]
        for asset in assets:
            for variant in ["primary", "fallback"]:
                item = asset.get(variant)
                if not isinstance(item, dict):
                    continue
                url = item.get("content_url", "")
                if not url or ".mpd" not in url:
                    continue
                base = url.split("?")[0]
                if base in seen:
                    continue
                seen.add(base)
                item_license = item.get("license_url") or item.get("licenseUrl") or license_url
                results.append({"mpd_url": url, "license_url": item_license, "variant": variant.upper()})
    return results

def _kids_from_pssh_b64(pssh_b64: str) -> list:
    """Extract KIDs from a Widevine PSSH base64 string.
    Supports v1 (KID list in box header) and v0 (protobuf field scan).
    Returns list of lowercase hex KID strings (32 chars each).
    """
    import base64 as _b64p
    kids = []
    try:
        data = _b64p.b64decode(pssh_b64 + "==")
        WV_SID = bytes.fromhex("edef8ba979d64acea3c827dcd51d21ed")
        pos = data.find(WV_SID)
        if pos == -1:
            return kids
        vf_pos = pos - 4          # version_flags field sits before system ID
        if vf_pos < 0:
            return kids
        version = data[vf_pos]    # first byte = PSSH version
        after_sid = pos + 16      # byte after system ID
        if version == 1:
            # v1: 4-byte KID count followed by N×16-byte KIDs
            if after_sid + 4 > len(data):
                return kids
            kid_count = int.from_bytes(data[after_sid:after_sid + 4], 'big')
            offset = after_sid + 4
            for _ in range(min(kid_count, 64)):
                if offset + 16 > len(data):
                    break
                kids.append(data[offset:offset + 16].hex())
                offset += 16
        else:
            # v0: scan protobuf payload for tag 0x12 0x10 (field 2, length 16 = key_id)
            if after_sid + 4 > len(data):
                return kids
            i = after_sid + 4     # skip data_size field
            while i < len(data) - 17:
                if data[i] == 0x12 and data[i + 1] == 0x10:
                    kids.append(data[i + 2:i + 18].hex())
                    i += 18
                else:
                    i += 1
    except Exception:
        pass
    return kids


def fetch_mpd_pssh(mpd_url: str) -> dict:
    try:
        req = request.Request(mpd_url, headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Referer": "https://www.hotstar.com/",
            "Origin": "https://www.hotstar.com",
            "Accept": "*/*",
        })
        with request.urlopen(req, timeout=15) as resp:
            mpd_text = resp.read().decode("utf-8", errors="replace")
        pssh = ""
        wv_block = re.search(r'(?:edef8ba9|EDEF8BA9).{0,200}?<cenc:pssh[^>]*>(.*?)</cenc:pssh>', mpd_text, re.DOTALL)
        if not wv_block:
            wv_block = re.search(r'<cenc:pssh[^>]*>(.*?)</cenc:pssh>', mpd_text, re.DOTALL)
        if wv_block:
            pssh = wv_block.group(1).strip()
        kid_patterns = [
            r'default_KID="([0-9a-fA-F\-]{32,36})"',
            r'cenc:default_KID="([0-9a-fA-F\-]{32,36})"',
            r'default_KID="\{([0-9a-fA-F\-]{32,36})\}"',
            r'cenc:default_KID="\{([0-9a-fA-F\-]{32,36})\}"',
            r'<ContentProtection[^>]+value="([0-9a-fA-F]{32})"',
            r'<ContentProtection[^>]+value="\{([0-9a-fA-F\-]{32,36})\}"',
        ]
        key_ids = []
        for pat in kid_patterns:
            for m in re.finditer(pat, mpd_text):
                kid = m.group(1).replace("-", "").lower()
                if len(kid) == 32 and kid not in key_ids:
                    key_ids.append(kid)

        # Also parse KIDs directly from PSSH binary — catches KIDs not in XML attrs
        if pssh:
            for kid in _kids_from_pssh_b64(pssh):
                kid = kid.lower()
                if len(kid) == 32 and kid not in key_ids:
                    key_ids.append(kid)
        # Scan ALL cenc:pssh blocks (MPD may have one per AdaptationSet)
        for pssh_b64_raw in re.findall(r'<cenc:pssh[^>]*>(.*?)</cenc:pssh>', mpd_text, re.DOTALL):
            for kid in _kids_from_pssh_b64(pssh_b64_raw.strip()):
                kid = kid.lower()
                if len(kid) == 32 and kid not in key_ids:
                    key_ids.append(kid)

        # PlayReady mspr:pro — base64 XML blob containing KID in little-endian GUID form
        import base64 as _b64pr
        for pro_b64 in re.findall(r'<(?:mspr:pro|[^>]*:pro)[^>]*>(.*?)</(?:mspr:pro|[^>]*:pro)>', mpd_text, re.DOTALL):
            try:
                pro_bytes = _b64pr.b64decode(pro_b64.strip() + "==")
                pr_xml = pro_bytes.decode("utf-16-le", errors="replace")
                for m in re.finditer(r'<KID[^>]+VALUE="([A-Za-z0-9+/=]{24,})"', pr_xml):
                    try:
                        raw = _b64pr.b64decode(m.group(1) + "==")
                        if len(raw) == 16:
                            # PlayReady stores GUID in mixed-endian: swap first 3 groups
                            kid_hex = (
                                raw[3::-1].hex() +          # first 4 bytes LE→BE
                                raw[5:3:-1].hex() +          # next 2 bytes LE→BE
                                raw[7:5:-1].hex() +          # next 2 bytes LE→BE
                                raw[8:].hex()                # last 8 bytes unchanged
                            )
                            if len(kid_hex) == 32 and kid_hex not in key_ids:
                                key_ids.append(kid_hex)
                    except Exception:
                        pass
            except Exception:
                pass
        has_clearkey = "1077efec" in mpd_text.lower() or "clearkey" in mpd_text.lower()
        return {"pssh": pssh, "key_ids": key_ids, "has_clearkey": has_clearkey, "raw_mpd": mpd_text, "error": None}
    except Exception as e:
        return {"pssh": "", "key_ids": [], "has_clearkey": False, "raw_mpd": "", "error": str(e)}

def extract_mpd_languages(mpd_url: str) -> list:
    """Parse MPD XML and return list of (lang_code, lang_name) from audio tracks.
    Returns all unique languages found in the MPD."""
    LANG_MAP = {
        "eng": "ENGLISH", "en": "ENGLISH",
        "hin": "HINDI",   "hi": "HINDI", "hd": "HINDI HD",
        "mar": "MARATHI", "mr": "MARATHI", "ma": "MARATHI",
        "tam": "TAMIL",   "ta": "TAMIL",
        "tel": "TELUGU",  "te": "TELUGU",
        "kan": "KANNADA", "kn": "KANNADA",
        "mal": "MALAYALAM","ml": "MALAYALAM",
        "ben": "BENGALI", "bn": "BENGALI",
        "guj": "GUJARATI","gu": "GUJARATI",
        "pan": "PUNJABI", "pa": "PUNJABI", "pun": "PUNJABI", "pu": "PUNJABI",
        "bho": "BHOJPURI","bih": "BHOJPURI","bh": "BHOJPURI",
        "har": "HARYANVI","hv": "HARYANVI","ha": "HARYANVI",
        "ori": "ORIYA",   "or": "ORIYA",
    }

    def langs_from_url(url: str) -> list:
        path = url.split("?")[0].lower()
        segments = path.replace("//", "/").split("/")
        found = []
        seen = set()
        for seg in segments:
            seg = seg.strip()
            if seg in LANG_MAP and seg not in seen:
                seen.add(seg)
                found.append((seg, LANG_MAP[seg]))
        return found

    try:
        req = request.Request(mpd_url, headers={
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Referer": "https://www.hotstar.com/",
            "Origin": "https://www.hotstar.com",
            "Accept": "*/*",
        })
        with request.urlopen(req, timeout=15) as resp:
            mpd_text = resp.read().decode("utf-8", errors="replace")

        seen = set()
        langs = []

        # Method 1: Find lang attributes inside AdaptationSet (audio)
        for match in re.finditer(r'<AdaptationSet[^>]*lang\s*=\s*["\']([a-z]{2,3})["\'][^>]*>', mpd_text, re.IGNORECASE):
            lc = match.group(1).lower()
            if lc in LANG_MAP and lc not in seen:
                seen.add(lc)
                langs.append((lc, LANG_MAP[lc]))

        # Method 2: Scan whole MPD for lang= attributes
        if not langs:
            for match in re.finditer(r'lang\s*=\s*["\']([a-z]{2,3})["\']', mpd_text, re.IGNORECASE):
                lc = match.group(1).lower()
                if lc in LANG_MAP and lc not in seen:
                    seen.add(lc)
                    langs.append((lc, LANG_MAP[lc]))

        # Method 3: Fallback to URL path
        if not langs:
            langs = langs_from_url(mpd_url)

        # Method 4: Look for representation IDs like "audio_eng", "audio_hin"
        if not langs and "audio" in mpd_text.lower():
            for match in re.finditer(r'id="[^"]*audio[_\-]([a-z]{2,3})[^"]*"', mpd_text, re.IGNORECASE):
                lc = match.group(1).lower()
                if lc in LANG_MAP and lc not in seen:
                    seen.add(lc)
                    langs.append((lc, LANG_MAP[lc]))

        return langs

    except Exception:
        return langs_from_url(mpd_url)

def try_clearkey_json(kid_list: list, license_url: str) -> list:
    import base64 as _b64
    if not kid_list or not license_url:
        return []
    try:
        b64_kids = [_b64.urlsafe_b64encode(bytes.fromhex(kid.replace("-", ""))).rstrip(b"=").decode() for kid in kid_list]
        body = json.dumps({"kids": b64_kids, "type": "temporary"}).encode()
        ck_req = request.Request(license_url, data=body, headers={
            "Content-Type": "application/json",
            "User-Agent": "Mozilla/5.0",
            "Referer": "https://www.hotstar.com/",
            "Origin": "https://www.hotstar.com",
        }, method="POST")
        with request.urlopen(ck_req, timeout=12) as resp:
            resp_json = json.loads(resp.read())
        keys = []
        for entry in resp_json.get("keys", []):
            k_b64 = entry.get("k", "")
            kd_b64 = entry.get("kid", "")
            if not k_b64:
                continue
            k_hex = _b64.urlsafe_b64decode(k_b64 + "==").hex()
            kd_hex = _b64.urlsafe_b64decode(kd_b64 + "==").hex() if kd_b64 else kid_list[0]
            keys.append(f"{kd_hex}:{k_hex}")
        return keys
    except Exception:
        return []

def fetch_drm_info_for_slug(slug_path: str) -> tuple:
    """Fetch DRM MPD streams + keys. Returns (drm_entries, global_license, global_keys, player_config)."""
    player_config = None
    # Primary: widevine-only DRM API
    try:
        api_url = build_drm_api_url(slug_path, "eng")
        req = request.Request(api_url, headers=build_headers())
        with request.urlopen(req, timeout=12) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        for sec in data.get("success", {}).get("page", {}).get("spaces", {}).values():
            for w in sec.get("widget_wrappers", []):
                d = w.get("widget", {}).get("data", {})
                if "player_config" in d:
                    player_config = d["player_config"]
                    break
            if player_config:
                break
    except Exception:
        pass
    # Fallback: 4K API which also returns widevine MPD for most content
    if not player_config:
        try:
            api_url2 = build_api_url(slug_path, "eng", "1")
            req2 = request.Request(api_url2, headers=build_headers())
            with request.urlopen(req2, timeout=12) as resp2:
                data2 = json.loads(resp2.read().decode("utf-8"))
            for sec in data2.get("success", {}).get("page", {}).get("spaces", {}).values():
                for w in sec.get("widget_wrappers", []):
                    d = w.get("widget", {}).get("data", {})
                    if "player_config" in d:
                        player_config = d["player_config"]
                        break
                if player_config:
                    break
        except Exception:
            pass
    if not player_config:
        return [], "", [], None
    drm_streams = extract_drm_info(player_config)
    if not drm_streams:
        return [], "", [], player_config
    global_license = ""
    for s in drm_streams:
        if s.get("license_url"):
            global_license = s["license_url"]
            break
    global_keys = []
    first_mpd = drm_streams[0]["mpd_url"] if drm_streams else ""
    if first_mpd and global_license:
        try:
            mpd_info0 = fetch_mpd_pssh(first_mpd)
            if mpd_info0 and mpd_info0.get("key_ids"):
                ck = try_clearkey_json(mpd_info0["key_ids"], global_license)
                if ck:
                    global_keys = ck
                elif mpd_info0.get("pssh"):
                    wv = fetch_widevine_keys(mpd_info0["pssh"], global_license)
                    if wv and not any(l.startswith("❌") for l in wv):
                        global_keys = wv
        except Exception:
            pass
    return drm_streams, global_license, global_keys, player_config

def fetch_widevine_keys(pssh_b64: str, license_url: str) -> list:
    try:
        from pywidevine.cdm import Cdm
        from pywidevine.device import Device
        from pywidevine.pssh import PSSH as WvPSSH
    except ImportError:
        return ["❌ pywidevine not installed → pip install pywidevine"]
    if not pssh_b64:
        return ["❌ No PSSH available"]
    script_dir = os.path.dirname(os.path.abspath(__file__))
    wvd_names = ["device.wvd", "wv.wvd", "chrome.wvd", "cdm.wvd"]
    device_path = None
    for name in wvd_names:
        for base in [script_dir, os.getcwd()]:
            p = os.path.join(base, name)
            if os.path.exists(p):
                device_path = p
                break
        if device_path:
            break
    if not device_path:
        return ["❌ No .wvd file found. Place device.wvd in script folder."]
    try:
        device = Device.load(device_path)
        cdm = Cdm.from_device(device)
        session_id = cdm.open()
        pssh_obj = WvPSSH(pssh_b64)
        challenge = cdm.get_license_challenge(session_id, pssh_obj)
        lic_req = request.Request(license_url, data=challenge, headers={
            "Content-Type": "application/octet-stream",
            "User-Agent": "Mozilla/5.0",
            "Referer": "https://www.hotstar.com/",
            "Origin": "https://www.hotstar.com",
        }, method="POST")
        with request.urlopen(lic_req, timeout=15) as resp:
            license_bytes = resp.read()
        cdm.parse_license(session_id, license_bytes)
        keys = [f"{k.kid.hex}:{k.key.hex()}" for k in cdm.get_keys(session_id) if k.type == "CONTENT"]
        cdm.close(session_id)
        return keys if keys else ["⚠ License OK but no CONTENT keys returned"]
    except Exception as e:
        return [f"❌ {str(e)}"]

def fetch_lang_stream(lang_code: str, lang_name: str, slug_path: str, input_url: str, quality_choice: str):
    try:
        api_url = build_api_url(slug_path, lang_code, quality_choice)
        # ---- RATE LIMIT (Patch 1): Token spam se bachao — 0.5-1.2s gap ----
        time.sleep(random.uniform(0.5, 1.2))
        req = request.Request(api_url, headers=build_headers())
        # ---- RATE LIMIT (Patch 3): Extra safety gap before HTTP request ----
        time.sleep(random.uniform(0.3, 0.8))
        with request.urlopen(req) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        player_config = None
        page_spaces = data.get("success", {}).get("page", {}).get("spaces", {})
        for s in page_spaces:
            for w in page_spaces[s].get("widget_wrappers", []):
                if "player_config" in w.get("widget", {}).get("data", {}):
                    player_config = w["widget"]["data"]["player_config"]
                    break
            if player_config:
                break
        if not player_config:
            return None
        clean_stream = extract_best_stream(player_config, input_url)
        if not clean_stream:
            return None
        audio_lang = ""
        try:
            # Primary: URL path segment match (most reliable) e.g. /eng/ /hin/ /tam/
            _url_segs = set(clean_stream.lower().split("?")[0].replace("https://","").split("/"))
            for code, name in LANGUAGES.items():
                if code.lower() in _url_segs:
                    audio_lang = name
                    break
            # Fallback: playback_tags "language:eng" style
            if not audio_lang:
                _ptags = str(player_config.get("playback_tags", "")).lower()
                for _tag in _ptags.split(";"):
                    if _tag.strip().startswith("language:"):
                        _detected = _tag.split(":")[1].strip()
                        audio_lang = LANGUAGES.get(_detected, "")
                        break
        except:
            pass
        is_hdr = False
        dynamic_range = player_config.get("dynamic_range", "").lower()
        if dynamic_range == "hdr":
            is_hdr = True
        elif "hdr" in str(player_config.get("playback_tags", "")).lower():
            is_hdr = True
        elif "hdr" in clean_stream.lower():
            is_hdr = True
        return {"lang_name": audio_lang or lang_name, "stream": clean_stream, "player_config": player_config, "is_hdr": is_hdr}
    except:
        return None

# ===================== OPTION 5 (PRIMARY ADSFREE) REPLACED WITH 4kads.py LOGIC =====================

# ---- constants from 4kads.py ----
LANG_MAP_4KADS = {
    "1": ["eng"],
    "2": ["hin", "hi", "hd"],
    "3": ["mar", "mr", "ma"],
    "4": ["guj", "gu"],
    "5": ["bih", "bho", "bh"],
    "6": ["pan", "pun", "pa", "pu"],
    "7": ["har", "hv", "ha"],
    "8": ["tam", "ta"],
    "9": ["tel", "te"],
    "10": ["kan", "kn"],
    "11": ["mal", "ml"],
    "12": ["ben", "bn"],
}

LANG_DISPLAY_4KADS = {
    "eng": "ENGLISH", "hin": "HINDI", "mar": "MARATHI", "guj": "GUJARATI",
    "bih": "BHOJPURI", "pan": "PUNJABI", "har": "HARYANVI", "tam": "TAMIL",
    "tel": "TELUGU", "kan": "KANNADA", "mal": "MALAYALAM", "ben": "BENGALI",
    "hi": "HINDI", "hd": "HINDI", "mr": "MARATHI", "ma": "MARATHI",
    "gu": "GUJARATI", "bho": "BHOJPURI", "bh": "BHOJPURI",
    "pun": "PUNJABI", "pa": "PUNJABI", "pu": "PUNJABI",
    "hv": "HARYANVI", "ha": "HARYANVI", "ta": "TAMIL",
    "te": "TELUGU", "kn": "KANNADA", "ml": "MALAYALAM", "bn": "BENGALI"
}

LANG_ORDER_4KADS = ["ENGLISH", "HINDI", "MARATHI", "GUJARATI", "BHOJPURI", "PUNJABI", "HARYANVI", "TAMIL", "TELUGU", "KANNADA", "MALAYALAM", "BENGALI"]

CDN_HOSTS_4KADS = [
    "live11p.hotstar.com", "live12p.hotstar.com", "live13p.hotstar.com",
    "live14p.hotstar.com", "live15p.hotstar.com", "live16p.hotstar.com",
    "live17p.hotstar.com", "live18p.hotstar.com", "live19p.hotstar.com",
    "live20p.hotstar.com",
]

HEADERS_BASE_4KADS = {
    "User-Agent": "Hotstar;in.startv.hotstar/26.03.30.2.11580 (Android/12)",
    "Accept": "application/json, text/plain, */*",
    "Accept-Language": "eng",
    "Referer": "https://www.hotstar.com/in/explore?search_query=live",
    "Connection": "keep-alive",
    "X-HS-Platform": "androidtv",
    "X-Country-Code": "in",
    "X-HS-Accept-language": "eng",
    "x-hs-is-retry": "false",
    "x-hs-retry-count": "0",
    "X-HS-Client": "platform:androidtv;app_id:in.startv.hotstar;app_version:26.03.06.0;os:Android;os_version:12;schema_version:0.0.1690",
    "x-hs-app": "260306000",
    "Pragma": "no-cache",
    "Cache-Control": "no-cache",
}

# ---- helper functions from 4kads.py ----
def build_headers_4kads() -> dict:
    """AndroidTV only — uses ATV device pool with 1-hr cooldown."""
    ua, cs, app_code = _get_atv_device()
    h = HEADERS_BASE_4KADS.copy()
    h["User-Agent"]      = ua
    h["X-HS-Client"]     = cs
    h["X-HS-Platform"]   = "androidtv"
    h["x-hs-app"]        = app_code
    h["x-hs-usertoken"]  = load_user_token()
    h["X-Request-Id"]    = str(uuid.uuid4())
    h["x-hs-request-id"] = str(uuid.uuid4())
    h["x-hs-device-id"]  = str(uuid.uuid4())
    return h

# -------------------- HDR BUILDER (original, keeps HDR10 + HDR + SDR) --------------------
def build_api_url_4kads(asset_id: str, lang: str, slug_path: str = "") -> str:
    """Original builder with HDR10, HDR, SDR support (returns HDR stream usually)."""
    if slug_path:
        base_url = API_TEMPLATE_4KADS.format(slug_path=slug_path)
    else:
        base_url = "https://www.hotstar.com/api/internal/bff/v2/slugs/in/news/news18-india/{id}/live/watch".format(id=asset_id)
    client_capabilities = {
        "ads": ["non_ssai", "ssai"],
        "audio_channel": ["stereo", "dolby51", "atmos"],
        "container": ["fmp4", "fmp4br", "ts"],
        "dvr": ["short", "long"],
        "dynamic_range": ["hdr10", "hdr", "sdr"],   # HDR + SDR
        "encryption": ["widevine", "plain"],
        "ladder": ["tv", "web", "phone", "4k"],
        "package": ["dash", "hls"],
        "resolution": ["4k", "fhd", "hd", "sd"],
        "video_codec": ["h265", "h264"],
        "video_codec_non_secure": ["h265", "h264", "vp9"]
    }
    drm_parameters = {
        "hdcp_version": ["HDCP_V2_2"],
        "widevine_security_level": ["HW_SECURE_ALL", "HW_SECURE_DECODE", "SW_SECURE_DECODE"]
    }
    return (
        base_url
        + '?'
        + '&client_capabilities=' + parse.quote(json.dumps(client_capabilities, separators=(',', ':')))
        + '&drm_parameters=' + parse.quote(json.dumps(drm_parameters, separators=(',', ':')))
        + '&request_features=consent_supported'
        + '&lang=' + parse.quote(lang, safe="")
    )

# -------------------- SDR BUILDER (only SDR, but keeps 4K) --------------------
def build_api_url_4kads_sdr(asset_id: str, lang: str, slug_path: str = "") -> str:
    """SDR‑only builder – forces SDR, keeps 4K resolution."""
    if slug_path:
        base_url = API_TEMPLATE_4KADS.format(slug_path=slug_path)
    else:
        base_url = "https://www.hotstar.com/api/internal/bff/v2/slugs/in/news/news18-india/{id}/live/watch".format(id=asset_id)
    client_capabilities = {
        "ads": ["non_ssai", "ssai"],
        "audio_channel": ["stereo", "dolby51", "atmos"],
        "container": ["fmp4", "fmp4br", "ts"],
        "dvr": ["short", "long"],
        "dynamic_range": ["sdr"],   # Only SDR
        "encryption": ["widevine", "plain"],
        "ladder": ["tv", "web", "phone", "4k"],   # 4K ladder
        "package": ["dash", "hls"],
        "resolution": ["4k", "fhd", "hd", "sd"],  # 4K resolution
        "video_codec": ["h265", "h264"],
        "video_codec_non_secure": ["h265", "h264", "vp9"]
    }
    drm_parameters = {
        "hdcp_version": ["HDCP_V2_2"],
        "widevine_security_level": ["HW_SECURE_ALL", "HW_SECURE_DECODE", "SW_SECURE_DECODE"]
    }
    return (
        base_url
        + '?'
        + '&client_capabilities=' + parse.quote(json.dumps(client_capabilities, separators=(',', ':')))
        + '&drm_parameters=' + parse.quote(json.dumps(drm_parameters, separators=(',', ':')))
        + '&request_features=consent_supported'
        + '&lang=' + parse.quote(lang, safe="")
    )

def build_api_url_4kads_dv(asset_id: str, lang: str, slug_path: str = "") -> str:
    """Dolby Vision builder — requests dolby_vision + hdr10 + hdr dynamic range."""
    if slug_path:
        base_url = API_TEMPLATE_4KADS.format(slug_path=slug_path)
    else:
        base_url = "https://www.hotstar.com/api/internal/bff/v2/slugs/in/news/news18-india/{id}/live/watch".format(id=asset_id)
    client_capabilities = {
        "ads": ["non_ssai", "ssai"],
        "audio_channel": ["stereo", "dolby51", "atmos"],
        "container": ["fmp4", "fmp4br", "ts"],
        "dvr": ["short", "long"],
        "dynamic_range": ["dolby_vision", "hdr10", "hdr", "sdr"],
        "encryption": ["widevine", "plain"],
        "ladder": ["tv", "web", "phone", "4k"],
        "package": ["dash", "hls"],
        "resolution": ["4k", "fhd", "hd", "sd"],
        "video_codec": ["h265", "h264"],
        "video_codec_non_secure": ["h265", "h264", "vp9"]
    }
    drm_parameters = {
        "hdcp_version": ["HDCP_V2_2"],
        "widevine_security_level": ["HW_SECURE_ALL", "HW_SECURE_DECODE", "SW_SECURE_DECODE"]
    }
    return (
        base_url
        + '?'
        + '&client_capabilities=' + parse.quote(json.dumps(client_capabilities, separators=(',', ':')))
        + '&drm_parameters=' + parse.quote(json.dumps(drm_parameters, separators=(',', ':')))
        + '&request_features=consent_supported'
        + '&lang=' + parse.quote(lang, safe="")
    )

def fetch_player_config_4kads(api_url: str) -> dict:
    req = request.Request(api_url, method="GET", headers=build_headers_4kads())
    with request.urlopen(req) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    # Try fixed path first (fast path)
    try:
        pc = data["success"]["page"]["spaces"]["player"]["widget_wrappers"][0]["widget"]["data"]["player_config"]
        if pc:
            return pc
    except Exception:
        pass
    # Fallback: search all spaces (same as other options)
    page_spaces = data.get("success", {}).get("page", {}).get("spaces", {})
    for sec in page_spaces.values():
        for w in sec.get("widget_wrappers", []):
            d = w.get("widget", {}).get("data", {})
            if "player_config" in d and d["player_config"]:
                return d["player_config"]
    raise ValueError("Could not find player_config")

def extract_all_streams_4kads(player_config: dict) -> list:
    streams = []
    media_assets = []
    for key in ["media_asset", "media_asset_v2", "media_assets"]:
        asset = player_config.get(key)
        if not asset:
            continue
        if isinstance(asset, dict):
            media_assets.append(asset)
        elif isinstance(asset, list):
            media_assets.extend(asset)
    for asset in media_assets:
        for stream_type in ["primary", "preview", "dash", "hls", "playback_url"]:
            item = asset.get(stream_type)
            if not isinstance(item, dict):
                continue
            content_url = (
                item.get("content_url")
                or item.get("url")
                or item.get("playback_url")
            )
            if not content_url:
                continue
            streams.append({
                "type": stream_type,
                "content_url": content_url,
                "playback_tags": str(item.get("playback_tags", "")).lower(),
                "width": item.get("width") or 0,
                "height": item.get("height") or 0,
            })
    unique_streams = []
    seen = set()
    for s in streams:
        url = s.get("content_url")
        if not url:
            continue
        clean = url.split("?")[0]
        if clean in seen:
            continue
        seen.add(clean)
        unique_streams.append(s)
    return unique_streams

def get_hdntl_token_4kads(url: str, retries=5) -> str:
    for attempt in range(retries):
        try:
            req = request.Request(url, headers={
                "User-Agent": HEADERS_BASE_4KADS["User-Agent"],
                "Referer": "https://www.hotstar.com/",
                "Origin": "https://www.hotstar.com",
                "Accept": "*/*"
            })
            with request.urlopen(req, timeout=15) as resp:
                set_cookie = resp.headers.get("Set-Cookie", "")
                if "hdntl=" in set_cookie:
                    for part in set_cookie.split(","):
                        if "hdntl=" in part:
                            return part.split("hdntl=")[1].split(";")[0].strip()
        except:
            pass
        time.sleep(0.5)
    # Fallback to hdnea param
    parsed = urlparse(url)
    params = parse_qs(parsed.query)
    if "hdnea" in params and params["hdnea"][0]:
        return params["hdnea"][0]
    if "hdntl" in params and params["hdntl"][0]:
        return params["hdntl"][0]
    return ""

def append_hdntl_to_url_4kads(base_url: str, token: str) -> str:
    if not token:
        return base_url
    if '?' in base_url:
        base_part, query_part = base_url.split('?', 1)
        params = query_part.split('&')
        new_params = [p for p in params if not (p.startswith('hdnea=') or p.startswith('hdntl=') or p.startswith('ttl=') or p.startswith('Expires=') or p.startswith('Signature=') or p.startswith('Key-Pair-Id='))]
        base_url = base_part + ('?' + '&'.join(new_params) if new_params else '')
    if '?' in base_url:
        return base_url + '&hdnea=' + token
    else:
        return base_url + '?hdnea=' + token

def is_working_url_4kads(url: str) -> bool:
    try:
        req = request.Request(url, headers={
            "User-Agent": HEADERS_BASE_4KADS["User-Agent"],
            "Referer": "https://www.hotstar.com/",
            "Origin": "https://www.hotstar.com",
        })
        with request.urlopen(req, timeout=15) as resp:
            data = resp.read(300).decode("utf-8", errors="ignore")
            if "#EXTM3U" in data or "mpegurl" in str(resp.headers.get("Content-Type", "")).lower():
                return True
    except:
        return False
    return False

def clean_stream_url_4kads(url: str) -> str:
    if '?' not in url:
        return url
    base, query = url.split('?', 1)
    params = query.split('&')
    keep = []
    for p in params:
        if p.startswith('ttl=') or p.startswith('Expires=') or p.startswith('Signature=') or p.startswith('Key-Pair-Id='):
            continue
        keep.append(p)
    clean_query = '&'.join(keep)
    return base + '?' + clean_query

def modify_bitrate_url_4kads(url: str) -> list:
    variants = []
    for old, new in [("master", "master_2160"), ("master", "master_1080"),
                     ("master", "master_720"), ("master", "master_high"), ("master", "master_hd")]:
        if old in url:
            variants.append(url.replace(old, new))
    variants.append(url)
    return list(dict.fromkeys(variants))

def generate_cdn_variants_4kads(url: str) -> list:
    parsed = urlparse(url)
    if not parsed.netloc:
        return [url]
    urls = []
    if parsed.netloc in CDN_HOSTS_4KADS:
        urls.append(url)
    for host in CDN_HOSTS_4KADS:
        new_url = parsed._replace(netloc=host).geturl()
        urls.append(new_url)
    seen = set()
    unique = []
    for u in urls:
        if u not in seen:
            seen.add(u)
            unique.append(u)
    return unique

def detect_language_from_url_4kads(url: str) -> str:
    lower = url.lower()
    for code, name in LANG_DISPLAY_4KADS.items():
        if f"/{code}/" in lower:
            return name
    return "OTHER"

def fetch_stream_for_language_4kads(asset_id: str, lang_codes: List[str], expected_lang: str, max_retries: int = 8) -> Optional[tuple]:
    for retry in range(max_retries):
        for lang_code in lang_codes:
            try:
                api_url = build_api_url_4kads(asset_id, lang_code)
                player_config = fetch_player_config_4kads(api_url)
                streams = extract_all_streams_4kads(player_config)
                if not streams:
                    continue
                candidate_urls = []
                for s in streams:
                    original_url = str(s.get("content_url", ""))
                    if not original_url:
                        continue
                    if str(s.get("type", "")).lower() != "primary":
                        continue
                    variants = generate_cdn_variants_4kads(original_url)
                    for v in variants:
                        candidate_urls.append((v, s))
                working = []
                with ThreadPoolExecutor(max_workers=20) as executor:
                    futures = {executor.submit(is_working_url_4kads, item[0]): item for item in candidate_urls}
                    for future in as_completed(futures):
                        result = future.result()
                        if result:
                            working.append(futures[future])
                for raw_url, s in working:
                    detected_lang = detect_language_from_url_4kads(raw_url)
                    if detected_lang.upper() != expected_lang.upper():
                        continue
                    token = get_hdntl_token_4kads(raw_url)
                    final_url = append_hdntl_to_url_4kads(raw_url, token)
                    return (detected_lang, final_url)
            except Exception:
                continue
        if retry < max_retries - 1:
            time.sleep(random.uniform(1, 3))
    return None

def parse_asset_id_4kads(url: str) -> Optional[str]:
    value = url.strip()
    if not value:
        return None
    parsed = urlparse(value)
    path = parsed.path if parsed.scheme else value
    segments = [segment for segment in path.split("/") if segment]
    if len(segments) >= 4 and segments[-1] == "watch" and segments[-3] == "video":
        return segments[-4]
    if len(segments) >= 3 and segments[-1] == "watch":
        return segments[-3]
    if len(segments) >= 2 and segments[-1] in ["live", "highlights", "replay", "clips"]:
        return segments[-2]
    return segments[-1]

def fetch_language_wrapper_4kads(asset_id: str, lang_num: str, lang_codes: List[str]) -> tuple:
    primary_code = lang_codes[0]
    expected_lang = LANG_DISPLAY_4KADS.get(primary_code, "ENGLISH")
    result = fetch_stream_for_language_4kads(asset_id, lang_codes, expected_lang, max_retries=8)
    if result:
        return (result[0], result[1])
    return (expected_lang, None)

def fetch_language_wrapper_4kads_sdr(asset_id: str, lang_num: str, lang_codes: List[str]) -> tuple:
    primary_code = lang_codes[0]
    expected_lang = LANG_DISPLAY_4KADS.get(primary_code, "ENGLISH")
    result = fetch_stream_for_language_4kads_sdr(asset_id, lang_codes, expected_lang, max_retries=8)
    if result:
        return (result[0], result[1])
    return (expected_lang, None)

def fetch_stream_for_language_4kads_sdr(asset_id: str, lang_codes: List[str], expected_lang: str, max_retries: int = 8) -> Optional[tuple]:
    """Same as fetch_stream_for_language_4kads but using SDR-only API."""
    for retry in range(max_retries):
        for lang_code in lang_codes:
            try:
                api_url = build_api_url_4kads_sdr(asset_id, lang_code)
                player_config = fetch_player_config_4kads(api_url)
                streams = extract_all_streams_4kads(player_config)
                if not streams:
                    continue
                candidate_urls = []
                for s in streams:
                    original_url = str(s.get("content_url", ""))
                    if not original_url:
                        continue
                    if str(s.get("type", "")).lower() != "primary":
                        continue
                    variants = generate_cdn_variants_4kads(original_url)
                    for v in variants:
                        candidate_urls.append((v, s))
                working = []
                with ThreadPoolExecutor(max_workers=20) as executor:
                    futures = {executor.submit(is_working_url_4kads, item[0]): item for item in candidate_urls}
                    for future in as_completed(futures):
                        result = future.result()
                        if result:
                            working.append(futures[future])
                for raw_url, s in working:
                    detected_lang = detect_language_from_url_4kads(raw_url)
                    if detected_lang.upper() != expected_lang.upper():
                        continue
                    token = get_hdntl_token_4kads(raw_url)
                    final_url = append_hdntl_to_url_4kads(raw_url, token)
                    return (detected_lang, final_url)
            except Exception:
                continue
        if retry < max_retries - 1:
            time.sleep(random.uniform(1, 3))
    return None

# ---- LOW-REQUEST helpers for OPTION 5 ----
# Goal: cut Option 5 down from ~15-25 requests/language to ~1 request/language
# (same ballpark as Options 1-4), by borrowing Option 14's "accept the CDN url
# the API already gave us" approach instead of testing 10-15 CDN host variants.
#
# Removed vs the original Option 5 path:
#   1) NO generate_cdn_variants_4kads()  -> no fan-out across live11p..live20p hosts
#   2) NO is_working_url_4kads() probing -> no extra HEAD/GET request per CDN host
#   3) NO get_hdntl_token_4kads() call   -> no extra request to read Set-Cookie hdntl
#   4) NO max_retries=8 loop             -> single pass per language code
#
# NOT borrowed from Option 14: its global-cookie step (get_global_hdntl_token),
# since that itself costs an extra request. The stream URL the API returns
# already carries its own valid signed token, so it's used as-is.

def is_cloudfront_url(url: str) -> bool:
    """Return True if this is a CloudFront-signed CDN URL (blocked for option 5)."""
    try:
        host = urlparse(url).netloc.lower()
        # CF signed URLs have Signature= or Key-Pair-Id= params
        if "Signature=" in url or "Key-Pair-Id=" in url:
            return True
        # CF CDN hosts (not the legacy blacklist, but modern CF SSAI hosts)
        if "live-ssai-cf" in host or "cloudfront.net" in host:
            return True
    except Exception:
        pass
    return False

def fetch_stream_4kads_lite(asset_id: str, lang_codes: List[str], expected_lang: str, use_sdr: bool = False, max_retries: int = 10, slug_path: str = "") -> Optional[tuple]:
    """Single-pass, low-request stream fetch for Option 5.
    
    - Akamai SSAI URLs (live11p-ssai-akt-mum.cdn.hotstar.com) → rewritten to live11p.hotstar.com ✓
    - CloudFront URLs (CF-signed, Signature=/Key-Pair-Id=) → BLOCKED, retry API call
    - Legacy blacklisted CDNs (.live-cf.cdn.hotstar.com) → BLOCKED, retry API call
    
    If API returns only CF/blacklisted URLs, retries up to max_retries times.
    """
    builder = build_api_url_4kads_sdr if use_sdr else build_api_url_4kads
    for attempt in range(max_retries):
        for lang_code in lang_codes:
            try:
                api_url = builder(asset_id, lang_code, slug_path=slug_path)
                player_config = fetch_player_config_4kads(api_url)
                streams = extract_all_streams_4kads(player_config)
                if not streams:
                    continue
                got_any = False
                for s in streams:
                    if str(s.get("type", "")).lower() != "primary":
                        continue
                    raw_url = str(s.get("content_url", "") or "")
                    if not raw_url:
                        continue
                    got_any = True
                    parsed_netloc = urlparse(raw_url).netloc

                    # Block legacy blacklisted CDN hosts
                    if is_blacklisted_cdn(parsed_netloc):
                        continue

                    # Block CloudFront signed URLs - retry API call
                    if is_cloudfront_url(raw_url):
                        continue

                    # Language check
                    detected_lang = detect_language_from_url_4kads(raw_url)
                    if detected_lang and detected_lang != "OTHER" and detected_lang.upper() != expected_lang.upper():
                        continue

                    # Rewrite Akamai SSAI host → clean liveXXp.hotstar.com
                    # Raw query kept as-is (no re-encoding) so hdnea token stays intact
                    final_url = rewrite_url_to_clean_cdn(raw_url)
                    return (expected_lang, final_url)

                # If we got URLs but all were CF/blacklisted, retry after short sleep
                if got_any and attempt < max_retries - 1:
                    time.sleep(random.uniform(0.5, 1.5))
            except Exception:
                continue
    return None

def fetch_language_wrapper_4kads_lite(asset_id: str, lang_num: str, lang_codes: List[str], use_sdr: bool = False, slug_path: str = "") -> tuple:
    primary_code = lang_codes[0]
    expected_lang = LANG_DISPLAY_4KADS.get(primary_code, "ENGLISH")
    result = fetch_stream_4kads_lite(asset_id, lang_codes, expected_lang, use_sdr=use_sdr, slug_path=slug_path)
    if result:
        return (result[0], result[1])
    return (expected_lang, None)

def option5_main(input_url: str):
    asset_id = parse_asset_id_4kads(input_url)
    if not asset_id:
        print(f"{RED}Error: could not parse asset id from URL{RESET}")
        return

    # Extract slug_path for correct API URL (e.g. sports/cricket/.../1540071854/video/live)
    slug_path = extract_slug_path(input_url) or ""

    # ---- Step 1: HDR streams for ENGLISH and HINDI only ----
    hdr_results = {}
    # English
    eng_codes = LANG_MAP_4KADS.get("1", ["eng"])
    eng_hdr = fetch_stream_4kads_lite(asset_id, eng_codes, "ENGLISH", use_sdr=False, slug_path=slug_path)
    if eng_hdr:
        hdr_results["ENGLISH HDR"] = eng_hdr[1]
    # Hindi
    hin_codes = LANG_MAP_4KADS.get("2", ["hin", "hi", "hd"])
    hin_hdr = fetch_stream_4kads_lite(asset_id, hin_codes, "HINDI", use_sdr=False, slug_path=slug_path)
    if hin_hdr:
        hdr_results["HINDI HDR"] = hin_hdr[1]

    # ---- Step 2: SDR streams for ALL languages (1 request/lang, no retries/CDN-probe) ----
    sdr_results = {}
    with ThreadPoolExecutor(max_workers=len(LANG_MAP_4KADS)) as executor:
        futures = {
            executor.submit(fetch_language_wrapper_4kads_lite, asset_id, lang_num, lang_codes, True, slug_path): (lang_num, lang_codes)
            for lang_num, lang_codes in LANG_MAP_4KADS.items()
        }
        for future in as_completed(futures):
            lang_name, url = future.result()
            if url:
                # For English/Hindi, label as SDR to avoid confusion with HDR
                if lang_name in ["ENGLISH", "HINDI"]:
                    sdr_results[f"{lang_name} SDR"] = url
                else:
                    sdr_results[lang_name] = url

    # ---- Step 3: Print & collect entries ----
    # Order: ENGLISH HDR → HINDI HDR → ENGLISH SDR → HINDI SDR → rest SDR languages
    entries = []

    # 1. ENGLISH HDR
    if "ENGLISH HDR" in hdr_results:
        print(f"{CYAN}ENGLISH HDR 4K ADSFREE{RESET}")
        print(hdr_results["ENGLISH HDR"])
        entries.append(("ENGLISH HDR", hdr_results["ENGLISH HDR"], True))

    # 2. HINDI HDR
    if "HINDI HDR" in hdr_results:
        print(f"{CYAN}HINDI HDR 4K ADSFREE{RESET}")
        print(hdr_results["HINDI HDR"])
        entries.append(("HINDI HDR", hdr_results["HINDI HDR"], True))

    # 3. ENGLISH SDR
    if "ENGLISH SDR" in sdr_results:
        print(f"{CYAN}ENGLISH SDR 4K ADSFREE{RESET}")
        print(sdr_results["ENGLISH SDR"])
        entries.append(("ENGLISH SDR", sdr_results["ENGLISH SDR"], False))

    # 4. HINDI SDR
    if "HINDI SDR" in sdr_results:
        print(f"{CYAN}HINDI SDR 4K ADSFREE{RESET}")
        print(sdr_results["HINDI SDR"])
        entries.append(("HINDI SDR", sdr_results["HINDI SDR"], False))

    # 5. Rest of SDR languages (skip ENGLISH and HINDI, already printed above)
    lang_order = LANG_ORDER_4KADS.copy()
    for lang in lang_order:
        if lang in ["ENGLISH", "HINDI"]:
            continue
        if lang in sdr_results:
            print(f"{CYAN}{lang} SDR 4K ADSFREE{RESET}")
            print(sdr_results[lang])
            entries.append((f"{lang} SDR", sdr_results[lang], False))

    total = len(hdr_results) + len(sdr_results)
    print(f"{GREEN}Total streams: HDR({len(hdr_results)}) + SDR({len(sdr_results)}) = {total}{RESET}")

    if entries:
        slug_path = extract_slug_path(input_url)
        title, match_no = extract_match_title(input_url)
        stream_type = extract_stream_type(input_url)
        logo_url = extract_logo_from_url(input_url)
        offer_m3u_creation(entries, title, match_no, stream_type, logo_url, is_adsfree_4k=True)


def _embed_hdntl_in_url(url: str) -> str:
    """Fetch hdntl token from stream URL via 1 GET (Set-Cookie) and embed it in the URL."""
    token = get_hdntl_token_4kads(url)
    if token:
        return append_hdntl_to_url_4kads(url, token)
    return url


def option6_heavy_main(input_url: str):
    """ADS-FREE 4K HEAVY (30 MINUTES) — option5 lite CDN path + option7 hdntl embed per stream."""
    asset_id = parse_asset_id_4kads(input_url)
    if not asset_id:
        print(f"{RED}Error: could not parse asset id from URL{RESET}")
        return

    slug_path = extract_slug_path(input_url) or ""

    # ---- Step 1: HDR streams for ENGLISH and HINDI only (option5 lite path) ----
    hdr_results = {}
    eng_codes = LANG_MAP_4KADS.get("1", ["eng"])
    eng_hdr = fetch_stream_4kads_lite(asset_id, eng_codes, "ENGLISH", use_sdr=False, slug_path=slug_path)
    if eng_hdr:
        hdr_results["ENGLISH HDR"] = eng_hdr[1]
    hin_codes = LANG_MAP_4KADS.get("2", ["hin", "hi", "hd"])
    hin_hdr = fetch_stream_4kads_lite(asset_id, hin_codes, "HINDI", use_sdr=False, slug_path=slug_path)
    if hin_hdr:
        hdr_results["HINDI HDR"] = hin_hdr[1]

    # ---- Step 2: SDR streams for ALL languages (option5 lite path) ----
    sdr_results = {}
    with ThreadPoolExecutor(max_workers=len(LANG_MAP_4KADS)) as executor:
        futures = {
            executor.submit(fetch_language_wrapper_4kads_lite, asset_id, lang_num, lang_codes, True, slug_path): (lang_num, lang_codes)
            for lang_num, lang_codes in LANG_MAP_4KADS.items()
        }
        for future in as_completed(futures):
            lang_name, url = future.result()
            if url:
                if lang_name in ["ENGLISH", "HINDI"]:
                    sdr_results[f"{lang_name} SDR"] = url
                else:
                    sdr_results[lang_name] = url

    # ---- Step 3: Embed hdntl token per URL (option7 style — 1 GET per stream via Set-Cookie) ----
    all_raw = {}
    all_raw.update(hdr_results)
    all_raw.update(sdr_results)
    with ThreadPoolExecutor(max_workers=len(all_raw)) as executor:
        embed_futures = {executor.submit(_embed_hdntl_in_url, url): lang for lang, url in all_raw.items()}
        embedded = {}
        for future in as_completed(embed_futures):
            lang = embed_futures[future]
            try:
                embedded[lang] = future.result()
            except Exception:
                embedded[lang] = all_raw[lang]

    # ---- Step 4: Print & collect entries ----
    entries = []

    if "ENGLISH HDR" in embedded:
        print(f"{CYAN}ENGLISH HDR 4K ADSFREE{RESET}")
        print(embedded["ENGLISH HDR"])
        entries.append(("ENGLISH HDR", embedded["ENGLISH HDR"], True))

    if "HINDI HDR" in embedded:
        print(f"{CYAN}HINDI HDR 4K ADSFREE{RESET}")
        print(embedded["HINDI HDR"])
        entries.append(("HINDI HDR", embedded["HINDI HDR"], True))

    if "ENGLISH SDR" in embedded:
        print(f"{CYAN}ENGLISH SDR 4K ADSFREE{RESET}")
        print(embedded["ENGLISH SDR"])
        entries.append(("ENGLISH SDR", embedded["ENGLISH SDR"], False))

    if "HINDI SDR" in embedded:
        print(f"{CYAN}HINDI SDR 4K ADSFREE{RESET}")
        print(embedded["HINDI SDR"])
        entries.append(("HINDI SDR", embedded["HINDI SDR"], False))

    lang_order = LANG_ORDER_4KADS.copy()
    for lang in lang_order:
        if lang in ["ENGLISH", "HINDI"]:
            continue
        if lang in embedded:
            print(f"{CYAN}{lang} SDR 4K ADSFREE{RESET}")
            print(embedded[lang])
            entries.append((f"{lang} SDR", embedded[lang], False))

    total = len(hdr_results) + len(sdr_results)
    print(f"{GREEN}Total streams: HDR({len(hdr_results)}) + SDR({len(sdr_results)}) = {total}{RESET}")

    if entries:
        slug_path = extract_slug_path(input_url)
        title, match_no = extract_match_title(input_url)
        stream_type = extract_stream_type(input_url)
        logo_url = extract_logo_from_url(input_url)
        offer_m3u_creation(entries, title, match_no, stream_type, logo_url, is_adsfree_4k=True)


def option_fhd_heavy_main(input_url: str):
    """NORMAL FHD (30 MINUTES) — fetch FHD streams per language via fetch_lang_stream,
    embed a 30-min IP-bound hdnea token per URL, then append the 24-hour global
    hdntl cookie + User-Agent/Referer/Origin headers after the pipe separator."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL!{RESET}")
        return
    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)
    print(f"{DARK_MAGENTA}FETCHING STREAMS... PLEASE WAIT{RESET}")

    # ── Step 1: Collect unique FHD streams per language ───────────────────────
    raw_entries: dict = {}   # lang_name -> (url, is_hdr)
    seen_bases: set = set()
    logo_url = ""
    logo_printed = False
    with ThreadPoolExecutor(max_workers=2) as executor:
        futures = {
            executor.submit(fetch_lang_stream, lc, ln, slug_path, input_url, "2"): ln
            for lc, ln in UNIQUE_LANGUAGES.items()
        }
        for future in as_completed(futures):
            result = future.result()
            if not result:
                continue
            lname = result["lang_name"] or futures[future]
            stream = result["stream"]
            base = stream.split("?")[0]
            if lname in raw_entries or base in seen_bases:
                continue
            seen_bases.add(base)
            raw_entries[lname] = (stream, result.get("is_hdr", False))
            if not logo_printed:
                pc = result["player_config"]
                img = pc.get("expanded_content_poster", {}).get("image", {}).get("src") or pc.get("cast_image", {}).get("src")
                if img:
                    logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                logo_printed = True

    if not raw_entries:
        print(f"{YELLOW}No streams found.{RESET}")
        return

    # ── Step 2: Embed 30-min IP-bound hdnea token per URL (parallel) ──────────
    with ThreadPoolExecutor(max_workers=len(raw_entries)) as executor:
        emb_futures = {
            executor.submit(_embed_hdntl_in_url, url): lname
            for lname, (url, _) in raw_entries.items()
        }
        embedded: dict = {}   # lang_name -> url with ?a=ns&hdnea=<30min-token>
        for future in as_completed(emb_futures):
            lname = emb_futures[future]
            try:
                embedded[lname] = future.result()
            except Exception:
                embedded[lname] = raw_entries[lname][0]

    _ua  = "Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)"
    _ref = "https://www.hotstar.com/"
    _ori = "https://www.hotstar.com"

    # ── Step 3: Print ─────────────────────────────────────────────────────────
    print(f"\n{BOLD_RED}LOGO{RESET}")
    if logo_url:
        print(logo_url)
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print(f"{BOLD_GREEN}{title}{RESET}")
    print(f"{BOLD_MAGENTA}{stream_type}{RESET}")

    entries = []
    first_cookie = ""
    for lname, (raw_url, is_hdr) in raw_entries.items():
        # URL already contains ?a=ns&hdnea=<30-min-ip-bound-token> from _embed_hdntl_in_url
        emb_url = embedded.get(lname, raw_url)
        # Extract per-URL hdntl cookie from the embedded URL (like option 2)
        per_url_cookie = extract_hdntl_from_url(emb_url)
        final_url = (f"{emb_url}"
                     f"|Cookie=hdntl={per_url_cookie}"
                     f"&User-Agent={_ua}&Referer={_ref}&Origin={_ori}")
        if not first_cookie and per_url_cookie:
            first_cookie = per_url_cookie
        htag = " HDR" if is_hdr else ""
        print(f"{BOLD_CYAN}{lname}{htag}{RESET}")
        print(f"{GREEN}{final_url}{RESET}")
        entries.append((lname, final_url, is_hdr))

    if first_cookie:
        print(f"\n{BOLD_GREEN}COOKIE : {RESET}{CYAN}hdntl={first_cookie}{RESET}")
    if entries:
        offer_m3u_creation(entries, title, match_no, stream_type, logo_url, auto_hdntl=first_cookie or None)


def option6_pri_main(input_url: str):
    """ADS-FREE 4K — HDR for English+Hindi, SDR for all languages.
    CDN finder kept. HDR + SDR run fully in parallel for speed."""
    asset_id = parse_asset_id_4kads(input_url)
    if not asset_id:
        print(f"{RED}Error: could not parse asset id from URL{RESET}")
        return

    hdr_results = {}
    sdr_results = {}

    # HDR wrapper (English + Hindi only)
    def _fetch_hdr(lang_num, lang_codes):
        lang_name, url = fetch_language_wrapper_4kads(asset_id, lang_num, lang_codes)
        return ("HDR", lang_name, url)

    # SDR wrapper (all 12 languages)
    def _fetch_sdr(lang_num, lang_codes):
        lang_name, url = fetch_language_wrapper_4kads_sdr(asset_id, lang_num, lang_codes)
        return ("SDR", lang_name, url)

    _hdr_langs = {"1": LANG_MAP_4KADS["1"], "2": LANG_MAP_4KADS["2"]}

    # All 14 tasks (2 HDR + 12 SDR) fire at the same time
    total_workers = 2 + len(LANG_MAP_4KADS)
    with ThreadPoolExecutor(max_workers=total_workers) as executor:
        futures = {}
        for ln, lc in _hdr_langs.items():
            futures[executor.submit(_fetch_hdr, ln, lc)] = None
        for ln, lc in LANG_MAP_4KADS.items():
            futures[executor.submit(_fetch_sdr, ln, lc)] = None

        for future in as_completed(futures):
            try:
                kind, lang_name, url = future.result()
                if not url:
                    continue
                if kind == "HDR":
                    hdr_results[lang_name] = url
                else:
                    if lang_name in ("ENGLISH", "HINDI"):
                        sdr_results[f"{lang_name} SDR"] = url
                    else:
                        sdr_results[lang_name] = url
            except Exception:
                pass

    # Print + build entries — HDR (Eng/Hin only) first, then SDR for all languages
    entries = []
    # HDR: English and Hindi
    for lang in ["ENGLISH", "HINDI"]:
        if lang in hdr_results:
            print(f"{CYAN}{lang} HDR 4K ADSFREE{RESET}")
            print(hdr_results[lang])
            entries.append((lang, hdr_results[lang], True))      # is_hdr → M3U label: "ENGLISH HDR"
    # SDR: English and Hindi
    for lang in ["ENGLISH SDR", "HINDI SDR"]:
        if lang in sdr_results:
            print(f"{CYAN}{lang} 4K ADSFREE{RESET}")
            print(sdr_results[lang])
            entries.append((lang, sdr_results[lang], False))     # M3U label: "ENGLISH SDR"
    # SDR: all other languages
    for lang in LANG_ORDER_4KADS:
        if lang not in ["ENGLISH", "HINDI"] and lang in sdr_results:
            print(f"{CYAN}{lang} SDR 4K ADSFREE{RESET}")
            print(sdr_results[lang])
            entries.append((f"{lang} SDR", sdr_results[lang], False))  # M3U label: "BHOJPURI SDR"

    print(f"{GREEN}Language found {len(entries)}{RESET}")

    if entries:
        title, match_no = extract_match_title(input_url)
        stream_type = extract_stream_type(input_url)
        logo_url = extract_logo_from_url(input_url)
        offer_m3u_creation(entries, title, match_no, stream_type, logo_url, is_adsfree_4k=True)


# ===================== M3U FUNCTIONS =====================
def extract_logo_from_url(url: str) -> str:
    slug_path = extract_slug_path(url)
    if not slug_path:
        return ""
    try:
        api_url = build_api_url(slug_path, "eng", "2")
        req = request.Request(api_url, headers=build_headers())
        with request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        player_config = None
        page_spaces = data.get("success", {}).get("page", {}).get("spaces", {})
        for s in page_spaces:
            for w in page_spaces[s].get("widget_wrappers", []):
                if "player_config" in w.get("widget", {}).get("data", {}):
                    player_config = w["widget"]["data"]["player_config"]
                    break
            if player_config:
                break
        if player_config:
            img = player_config.get("expanded_content_poster", {}).get("image", {}).get("src") or player_config.get("cast_image", {}).get("src")
            if img:
                return f"https://img10.hotstar.com/image/upload/f_auto/{img}"
    except:
        pass
    return ""

def create_m3u_file(entries: List[Tuple[str, str, bool]], title: str, match_no: str,
                    stream_type: str, filename: str = "hotstar_live.m3u", logo_url: str = "", hdntl_cookie: str = "", skip_http_headers: bool = False, force_no_cookie: bool = False, is_adsfree_4k: bool = False) -> bool:
    if not entries:
        print(f"{RED}No stream entries to save.{RESET}")
        return False
    try:
        with open(filename, "w", encoding="utf-8") as f:
            f.write("#EXTM3U\n")
            f.write(f"# JoinTg: @StreamFlex19\n")
            f.write(f"# Title: {title}\n")
            if match_no:
                f.write(f"# Match: {match_no}\n")
            f.write(f"# Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
            import hashlib
            for entry in entries:
                try:
                    if len(entry) == 3:
                        lang, url, is_hdr = entry
                    else:
                        lang, url = entry[0], entry[1]
                        is_hdr = False
                except Exception:
                    continue
                if lang == "__TITLE__":
                    continue  # episode title marker — skip in M3U
                tvg_id = str(int(hashlib.md5(url.encode()).hexdigest(), 16) % 9999999999)
                # Build smart label
                lang_upper = lang.upper()
                if is_adsfree_4k:
                    if "SDR" in lang_upper:
                        base_lang = lang.replace(" SDR", "").replace(" sdr", "").strip()
                        channel_label = f"{base_lang} 4K SDR ADSFREE"
                    elif is_hdr:
                        base_lang = lang.replace(" HDR", "").replace(" hdr", "").strip()
                        channel_label = f"{base_lang} 4K HDR ADSFREE"
                    else:
                        channel_label = f"{lang} 4K SDR ADSFREE"
                elif "SDR" in lang_upper:
                    base_lang = lang.replace(" SDR", "").replace(" sdr", "").strip()
                    channel_label = f"{base_lang} SDR"
                elif is_hdr:
                    channel_label = f"{lang} HDR"
                else:
                    channel_label = f"{lang}"
                
                # Determine token for this specific URL
                if hdntl_cookie:
                    token_to_use = hdntl_cookie
                else:
                    # Auto-extract token from the URL itself (from query params)
                    token_to_use = extract_hdntl_from_url(url) or ""
                
                if logo_url:
                    f.write(f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{lang}" tvg-logo="{logo_url}" group-title="{title}", {channel_label}\n')
                else:
                    f.write(f'#EXTINF:-1 tvg-id="{tvg_id}" tvg-name="{lang}" group-title="{title} ", {channel_label}\n')
                
                if not skip_http_headers:
                    _exthttp = '{"Origin":"https://www.hotstar.com","Referer":"https://www.hotstar.com/"'
                    if token_to_use and not force_no_cookie:
                        _exthttp += f',"Cookie":"hdntl={token_to_use}"'
                    _exthttp += '}'
                    f.write(f'#EXTHTTP:{_exthttp}\n')
                    f.write('#EXTVLCOPT:http-extra-headers=Origin: https://www.hotstar.com\n')
                    f.write('#EXTVLCOPT:http-referrer=https://www.hotstar.com/\n')
                f.write(f"{url}\n")
        print(f"{GREEN}✓ M3U playlist saved as: {filename}{RESET}")
        return True
    except Exception as e:
        print(f"{RED}Failed to create M3U: {e}{RESET}")
        return False

def create_txt_file(entries: List[Tuple[str, str, bool]], filename: str, hdntl_cookie: str = "") -> bool:
    """Save plain-text file: episode title headers + stream name + URL pairs."""
    if not entries:
        print(f"{RED}No stream entries to save.{RESET}")
        return False
    try:
        with open(filename, "w", encoding="utf-8") as f:
            f.write(f"# Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n\n")
            for entry in entries:
                try:
                    name = entry[0]
                    url  = entry[1]
                except Exception:
                    continue
                if name == "__TITLE__":
                    f.write(f"\n{'─'*50}\n{url}\n{'─'*50}\n")
                    continue
                # Embed token into URL if not already present
                final_url = url
                if hdntl_cookie and "hdntl=" not in url:
                    sep = "&" if "?" in url else "?"
                    final_url = url + sep + f"hdntl={hdntl_cookie}"
                f.write(f"\n{name}\n{final_url}\n")
        print(f"{GREEN}✓ Text file saved as: {filename}{RESET}")
        return True
    except Exception as e:
        print(f"{RED}Failed to create text file: {e}{RESET}")
        return False

def offer_m3u_creation(entries: List[Tuple[str, str, bool]], title: str,
                       match_no: str, stream_type: str, logo_url: str = "", auto_hdntl: str = "",
                       filename_override: str = "", is_adsfree_4k: bool = False):
    if not entries:
        return
    ans = input(f"\n{BOLD_CYAN}Save files? (y/n): {RESET}").strip().lower()
    if ans == 'y':
        # Derive base name (no extension)
        if filename_override:
            _base = filename_override.rsplit(".", 1)[0]
        else:
            _base = title.replace(' ', '_')
        _txt_name = _base + ".txt"
        _m3u_name = _base + ".m3u"

        hdntl_cookie = auto_hdntl
        if auto_hdntl:
            print(f"{GREEN}✓ Cookie auto-extracted, press Enter to use it or paste a new one:{RESET}")
            print(f"{GRAY}hdntl={auto_hdntl[:60]}...{RESET}")
        else:
            print(f"{YELLOW}Paste hdntl cookie (TamperDev/browser extension) or press Enter to skip:{RESET}")
            print(f"{GRAY}Format: hdntl=exp=...~hmac=...{RESET}")
        raw_cookie = input(f"{BOLD_CYAN}Cookie : {RESET}").strip()
        if raw_cookie:
            if raw_cookie.startswith("hdntl="):
                hdntl_cookie = raw_cookie[len("hdntl="):]
            else:
                import re as _rc
                _m = _rc.search(r'hdntl=([^\s;&|]+)', raw_cookie)
                hdntl_cookie = _m.group(1) if _m else raw_cookie

        create_txt_file(entries, _txt_name, hdntl_cookie=hdntl_cookie)
        create_m3u_file(entries, title, match_no, stream_type, _m3u_name, logo_url, hdntl_cookie=hdntl_cookie, is_adsfree_4k=is_adsfree_4k)

def git_push_m3u(filename: str, message: str = "Auto update M3U playlist") -> bool:
    if subprocess.run(["git", "--version"], capture_output=True).returncode != 0:
        print(f"{YELLOW}⚠ Git not installed. Skipping push.{RESET}")
        return False
    if not os.path.isdir(".git"):
        print(f"{YELLOW}⚠ Not a git repository (no .git folder). Skipping push.{RESET}")
        print(f"{YELLOW}   To enable auto-push, run: git init && git remote add origin <your-repo-url>{RESET}")
        return False
    try:
        subprocess.run(["git", "add", filename], check=True, capture_output=True)
        has_changes = subprocess.run(
            ["git", "diff", "--cached", "--quiet"], capture_output=True
        ).returncode != 0
        if not has_changes:
            print(f"{YELLOW}⚠ No changes to commit for {filename}. Skipping push.{RESET}")
            return True
        subprocess.run(["git", "commit", "-m", message], check=True, capture_output=True)
        print(f"{GREEN}✓ Committed changes for {filename}{RESET}")
        pull_result = subprocess.run(
            ["git", "pull", "origin", "main", "--no-rebase"],
            capture_output=True, text=True
        )
        if pull_result.returncode != 0:
            subprocess.run(["git", "merge", "--abort"], capture_output=True)
            subprocess.run(["git", "rebase", "--abort"], capture_output=True)
            print(f"{YELLOW}⚠ Git pull failed, but attempting force push? No, will retry later.{RESET}")
            return False
        subprocess.run(["git", "push"], check=True, capture_output=True)
        print(f"{GREEN}✓ Pushed to GitHub successfully{RESET}")
        return True
    except subprocess.CalledProcessError as e:
        if "push" in str(e.cmd) and e.returncode != 0:
            try:
                subprocess.run(["git", "push", "--force-with-lease"], check=True, capture_output=True)
                print(f"{GREEN}✓ Force-pushed to GitHub successfully (resolved divergence){RESET}")
                return True
            except:
                print(f"{RED}Git push failed even after force-with-lease: {e}{RESET}")
        else:
            print(f"{RED}Git operation failed: {e}{RESET}")
        return False

# ===================== CLOUDFLARE WORKERS PUSH =====================
CF_CONFIG_FILE = "cf_config.json"
def load_cf_config():
    try:
        with open(CF_CONFIG_FILE, "r") as f:
            return json.load(f)
    except:
        return None
def save_cf_config(worker_url, api_token):
    with open(CF_CONFIG_FILE, "w") as f:
        json.dump({"worker_url": worker_url, "api_token": api_token}, f)
def push_to_cloudflare(filename: str, worker_url: str, api_token: str, retries: int = 3) -> bool:
    import urllib.error
    try:
        with open(filename, "rb") as f:
            file_content = f.read()
    except Exception as e:
        print(f"{RED}Failed to read M3U file: {e}{RESET}")
        return False
    for attempt in range(1, retries + 1):
        try:
            headers = {
                "Authorization": f"Bearer {api_token}",
                "Content-Type": "text/plain",
                "X-File-Name": os.path.basename(filename),
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                "Content-Length": str(len(file_content)),
            }
            req = request.Request(worker_url, data=file_content, headers=headers, method="PUT")
            try:
                with request.urlopen(req, timeout=30) as resp:
                    status = resp.status
                    body = resp.read().decode("utf-8", errors="replace").strip()
                    if status == 200:
                        print(f"{GREEN}✓ Uploaded to Cloudflare Workers (attempt {attempt}){RESET}")
                        if body:
                            print(f"{CYAN}  CF Response: {body[:200]}{RESET}")
                        return True
                    else:
                        print(f"{RED}✗ Cloudflare returned HTTP {status} (attempt {attempt}){RESET}")
                        if body:
                            print(f"{YELLOW}  CF Response: {body[:300]}{RESET}")
            except urllib.error.HTTPError as e:
                body = e.read().decode("utf-8", errors="replace").strip()
                print(f"{RED}✗ Cloudflare HTTP {e.code} error (attempt {attempt}): {e.reason}{RESET}")
                if body:
                    print(f"{YELLOW}  CF Error body: {body[:300]}{RESET}")
                if e.code in [401, 403]:
                    print(f"{RED}  → Check your API Bearer Token in cf_config.json{RESET}")
                    return False  # Don't retry auth errors
            except urllib.error.URLError as e:
                print(f"{RED}✗ Network error (attempt {attempt}): {e.reason}{RESET}")
        except Exception as e:
            print(f"{RED}✗ Cloudflare push attempt {attempt}/{retries} failed: {e}{RESET}")
        if attempt < retries:
            print(f"{YELLOW}  Retrying in 3 seconds...{RESET}")
            time.sleep(3)
    print(f"{RED}✗ All {retries} Cloudflare push attempts failed.{RESET}")
    print(f"{YELLOW}  Tip: Check Worker URL and Bearer Token in cf_config.json{RESET}")
    return False


def fetch_existing_m3u(filename: str, cf_worker_url: str = None) -> list:
    """Read existing M3U from local file or fetch from Cloudflare.
    Returns list of (extinf_line, url, tvg_name) tuples.
    Skips #EXTHTTP/#EXTVLCOPT lines to find real URL."""
    import re as _re
    lines_src = None
    if os.path.isfile(filename):
        try:
            with open(filename, "r", encoding="utf-8") as f:
                lines_src = f.readlines()
        except Exception:
            pass
    if lines_src is None and cf_worker_url:
        try:
            _base = cf_worker_url.rstrip("/")
            if _base.endswith("/upload"):
                _base = _base[:-7]
            _get_url = f"{_base}/{os.path.basename(filename)}"
            _req = request.Request(_get_url, headers={"User-Agent": "Mozilla/5.0"})
            with request.urlopen(_req, timeout=10) as _r:
                lines_src = _r.read().decode("utf-8").splitlines(keepends=True)
            print(f"{GREEN}  ✓ Fetched existing file from Cloudflare{RESET}")
        except Exception as _e:
            print(f"{YELLOW}  ⚠ Could not fetch from CF ({_e}), starting fresh{RESET}")
    if not lines_src:
        return []
    entries = []
    seen_urls = set()
    seen_names = set()
    i = 0
    while i < len(lines_src):
        ln = lines_src[i].strip()
        if ln.startswith("#EXTINF"):
            extinf = ln
            nm = _re.search(r'tvg-name="([^"]+)"', extinf)
            tvg_name = nm.group(1).strip() if nm else ""
            # Fallback: use display name (after last comma) if tvg-name missing
            if not tvg_name:
                dn = _re.search(r',\s*(.+)$', extinf)
                tvg_name = dn.group(1).strip() if dn else ""
            j = i + 1
            found_url = ""
            while j < len(lines_src):
                nxt = lines_src[j].strip()
                if nxt and not nxt.startswith("#"):
                    found_url = nxt
                    break
                j += 1
            base = found_url.split("?")[0]
            # Deduplicate by both URL base AND tvg_name to prevent same-name duplicates
            if found_url and base not in seen_urls and tvg_name not in seen_names:
                entries.append((extinf, found_url, tvg_name))
                seen_urls.add(base)
                if tvg_name:
                    seen_names.add(tvg_name)
            i = j + 1
            continue
        i += 1
    return entries


# ===================== OPTION 12 & 13 – INDEPENDENT STREAM EXTRACTION =====================

def fetch_player_config_for_slug(slug_path: str, lang_code: str) -> dict:
    """Fetch player config for a given slug and language using a generic API (quality "2")."""
    api_url = build_api_url(slug_path, lang_code, "2")
    req = request.Request(api_url, headers=build_headers())
    with request.urlopen(req, timeout=12) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    for sec in data.get("success", {}).get("page", {}).get("spaces", {}).values():
        for w in sec.get("widget_wrappers", []):
            d = w.get("widget", {}).get("data", {})
            if "player_config" in d:
                return d["player_config"]
    raise ValueError("No player_config found")

def extract_all_streams_general(player_config: dict) -> List[dict]:
    """Extract all streams (primary, fallback) from player_config."""
    streams = []
    for key in ["media_asset", "media_asset_v2"]:
        assets = player_config.get(key)
        if not assets:
            continue
        if isinstance(assets, dict):
            assets = [assets]
        for asset in assets:
            for variant in ["primary", "fallback"]:
                item = asset.get(variant)
                if isinstance(item, dict) and item.get("content_url"):
                    streams.append({
                        "type": variant,
                        "url": item["content_url"],
                        "playback_tags": str(item.get("playback_tags", "")),
                        "height": item.get("height", 0)
                    })
    return streams

def build_final_24h_url(raw_url: str, global_token: str) -> Optional[str]:
    parsed = urlparse(raw_url)
    if is_blacklisted_cdn(parsed.netloc):
        return None
    base = parsed._replace(query="").geturl().split("?")[0]
    token_part = f"a=ns&ttl=86400&hdnea={global_token}|Cookie=hdntl={global_token}"
    headers_part = "&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com"
    return f"{base}?{token_part}{headers_part}"

def option12_fallback_24h(input_url: str):
    """Option 12 – Sirf FALLBACK streams, original CDN host, blacklisted CDN skip with retry."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL.{RESET}")
        return

    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)

    print(f"{BOLD_RED}24-HOURS FALLBACK STREAMS{RESET}\n")
    global_token = get_global_hdntl_token()
    if not global_token:
        print(f"{RED}Failed to get global token. Aborting.{RESET}")
        return
    exp_match = re.search(r"exp=(\d+)", global_token)
    if exp_match:
        exp_str = datetime.fromtimestamp(int(exp_match.group(1))).strftime("%Y-%m-%d %H:%M:%S")
        print(f"{GREEN}✓ Token fetched, expires at {exp_str}{RESET}")
    else:
        print(f"{GREEN}✓ Token fetched{RESET}")

    logo_url = extract_logo_from_url(input_url)
    if not logo_url:
        try:
            api_test = build_api_url(slug_path, "eng", "2")
            req_logo = request.Request(api_test, headers=build_headers())
            with request.urlopen(req_logo, timeout=10) as r:
                d = json.loads(r.read().decode("utf-8"))
            for sec in d.get("success", {}).get("page", {}).get("spaces", {}).values():
                for w in sec.get("widget_wrappers", []):
                    pc = w.get("widget", {}).get("data", {}).get("player_config")
                    if pc:
                        img = pc.get("expanded_content_poster", {}).get("image", {}).get("src") or pc.get("cast_image", {}).get("src")
                        if img:
                            logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                        break
                if logo_url:
                    break
        except:
            pass

    print(f"{BOLD_RED}LOGO{RESET}")
    if logo_url:
        print(logo_url)
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print(f"{BOLD_GREEN}{title}{RESET}")
    print(f"{BOLD_MAGENTA}{stream_type}{RESET}")

    results = {}
    lock = threading.Lock()

    def build_final_url(raw_url: str) -> Optional[str]:
        """No CDN replacement – only blacklist check and token append."""
        parsed = urlparse(raw_url)
        if is_blacklisted_cdn(parsed.netloc):
            return None
        base = parsed._replace(query="").geturl().split("?")[0]
        token_part = f"a=ns&ttl=86400&hdnea={global_token}|Cookie=hdntl={global_token}"
        headers_part = "&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com"
        return f"{base}?{token_part}{headers_part}"

    def process_lang(lang_code, lang_name):
        max_retries = 3
        for attempt in range(max_retries):
            try:
                pc = fetch_player_config_for_slug(slug_path, lang_code)
                streams = extract_all_streams_general(pc)
                fallback_urls = [s for s in streams if s["type"] == "fallback" and s.get("url")]
                if not fallback_urls:
                    continue
                # Try each fallback URL
                for s in fallback_urls:
                    raw_url = s["url"]
                    # Check blacklist on original host
                    if is_blacklisted_cdn(urlparse(raw_url).netloc):
                        continue
                    # Detect language
                    detected = detect_language_from_url_4kads(raw_url)
                    if not detected or detected == "OTHER":
                        tags = s.get("playback_tags", "")
                        for tag in tags.split(";"):
                            if tag.strip().startswith("language:"):
                                detected_code = tag.split(":")[1].strip().lower()
                                detected = LANGUAGES.get(detected_code, "")
                                break
                    if detected.upper() != lang_name.upper():
                        continue
                    final = build_final_url(raw_url)
                    if final:
                        with lock:
                            if lang_name not in results:
                                results[lang_name] = final
                        return  # success
            except Exception:
                if attempt < max_retries - 1:
                    time.sleep(1)
                continue
        # After retries, no valid non-blacklisted URL found
        pass

    with ThreadPoolExecutor(max_workers=4) as ex:
        futures = [ex.submit(process_lang, code, name) for code, name in UNIQUE_LANGUAGES.items()]
        for _ in as_completed(futures):
            pass

    if not results:
        print(f"{RED}No fallback streams found for any language (blacklisted CDNs skipped after retries).{RESET}")
        return

    entries = []
    lang_order = ["ENGLISH","HINDI","MARATHI","GUJARATI","BHOJPURI","PUNJABI",
                  "HARYANVI","TAMIL","TELUGU","KANNADA","MALAYALAM","BENGALI"]
    for lang in lang_order:
        if lang in results:
            print(f"{BOLD_CYAN}{lang}{RESET}")
            print(f"{GREEN}{results[lang]}{RESET}")
            entries.append((lang, results[lang], False))

    print(f"\n{BOLD_GREEN}GLOBAL COOKIE:{RESET}\n{CYAN}hdntl={global_token}{RESET}")
    if entries:
        offer_m3u_creation(entries, title, match_no, stream_type, logo_url, auto_hdntl=global_token)

def option13_primary_24h(input_url: str):
    """Option 13 – Sirf PRIMARY streams, original CDN host, blacklisted CDN skip with retry."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL.{RESET}")
        return

    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)

    print(f"{BOLD_RED}24-HOURS PRIMARY STREAMS{RESET}\n")
    global_token = get_global_hdntl_token()
    if not global_token:
        print(f"{RED}Failed to get global token. Aborting.{RESET}")
        return
    exp_match = re.search(r"exp=(\d+)", global_token)
    if exp_match:
        exp_str = datetime.fromtimestamp(int(exp_match.group(1))).strftime("%Y-%m-%d %H:%M:%S")
        print(f"{GREEN}✓ Token fetched, expires at {exp_str}{RESET}")
    else:
        print(f"{GREEN}✓ Token fetched{RESET}")

    logo_url = extract_logo_from_url(input_url)
    if not logo_url:
        try:
            api_test = build_api_url(slug_path, "eng", "1")
            req_logo = request.Request(api_test, headers=build_headers())
            with request.urlopen(req_logo, timeout=10) as r:
                d = json.loads(r.read().decode("utf-8"))
            for sec in d.get("success", {}).get("page", {}).get("spaces", {}).values():
                for w in sec.get("widget_wrappers", []):
                    pc = w.get("widget", {}).get("data", {}).get("player_config")
                    if pc:
                        img = pc.get("expanded_content_poster", {}).get("image", {}).get("src") or pc.get("cast_image", {}).get("src")
                        if img:
                            logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                        break
                if logo_url:
                    break
        except:
            pass

    print(f"{BOLD_RED}LOGO{RESET}")
    if logo_url:
        print(logo_url)
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print(f"{BOLD_GREEN}{title}{RESET}")
    print(f"{BOLD_MAGENTA}{stream_type}{RESET}")

    results = {}
    lock = threading.Lock()

    def build_final_url(raw_url: str) -> Optional[str]:
        parsed = urlparse(raw_url)
        if is_blacklisted_cdn(parsed.netloc):
            return None
        base = parsed._replace(query="").geturl().split("?")[0]
        token_part = f"a=ns&ttl=86400&hdnea={global_token}|Cookie=hdntl={global_token}"
        headers_part = "&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com"
        return f"{base}?{token_part}{headers_part}"

    def process_lang(lang_code, lang_name):
        max_retries = 3
        for attempt in range(max_retries):
            try:
                pc = fetch_player_config_for_slug(slug_path, lang_code)
                streams = extract_all_streams_general(pc)
                primary_urls = [s for s in streams if s["type"] == "primary" and s.get("url")]
                if not primary_urls:
                    continue
                for s in primary_urls:
                    raw_url = s["url"]
                    if is_blacklisted_cdn(urlparse(raw_url).netloc):
                        continue
                    detected = detect_language_from_url_4kads(raw_url)
                    if not detected or detected == "OTHER":
                        tags = s.get("playback_tags", "")
                        for tag in tags.split(";"):
                            if tag.strip().startswith("language:"):
                                detected_code = tag.split(":")[1].strip().lower()
                                detected = LANGUAGES.get(detected_code, "")
                                break
                    if detected.upper() != lang_name.upper():
                        continue
                    final = build_final_url(raw_url)
                    if final:
                        with lock:
                            if lang_name not in results:
                                results[lang_name] = final
                        return
            except Exception:
                if attempt < max_retries - 1:
                    time.sleep(1)
                continue

    with ThreadPoolExecutor(max_workers=4) as ex:
        futures = [ex.submit(process_lang, code, name) for code, name in UNIQUE_LANGUAGES.items()]
        for _ in as_completed(futures):
            pass

    if not results:
        print(f"{RED}No primary streams found for any language (blacklisted CDNs skipped after retries).{RESET}")
        return

    entries = []
    lang_order = ["ENGLISH","HINDI","MARATHI","GUJARATI","BHOJPURI","PUNJABI",
                  "HARYANVI","TAMIL","TELUGU","KANNADA","MALAYALAM","BENGALI"]
    for lang in lang_order:
        if lang in results:
            print(f"{BOLD_CYAN}{lang}{RESET}")
            print(f"{GREEN}{results[lang]}{RESET}")
            entries.append((lang, results[lang], False))

    print(f"\n{BOLD_GREEN}GLOBAL COOKIE:{RESET}\n{CYAN}hdntl={global_token}{RESET}")
    if entries:
        offer_m3u_creation(entries, title, match_no, stream_type, logo_url, auto_hdntl=global_token)

# ===================== OPTION 14 & 15 – 4K 24-HOUR LINKS =====================

def _fetch_4k_24h_streams(slug_path: str, variant_type: str, lang_order: list, global_token: str) -> dict:
    """
    Shared helper: fetch 4K streams (fallback or primary) for all languages.
    variant_type: 'fallback' or 'primary'
    Returns dict {lang_name: final_url}
    """
    results = {}
    lock = threading.Lock()

    def build_final_url_4k(raw_url: str) -> Optional[str]:
        parsed = urlparse(raw_url)
        if is_blacklisted_cdn(parsed.netloc):
            return None
        base = parsed._replace(query="").geturl().split("?")[0]
        token_part = f"a=ns&ttl=86400&hdnea={global_token}|Cookie=hdntl={global_token}"
        headers_part = "&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com"
        return f"{base}?{token_part}{headers_part}"

    def get_player_config_4k(lang_code: str, use_ssai: bool) -> Optional[dict]:
        try:
            api_url = build_jhs_4k_api_url(slug_path, lang_code, is_live=use_ssai)
            req = request.Request(api_url, headers=build_jhs_headers())
            with request.urlopen(req, timeout=12) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            for sec in data.get("success", {}).get("page", {}).get("spaces", {}).values():
                for w in sec.get("widget_wrappers", []):
                    d = w.get("widget", {}).get("data", {})
                    if "player_config" in d:
                        return d["player_config"]
        except Exception:
            pass
        return None

    def try_url(raw_url: str, lang_name: str) -> Optional[str]:
        """Check language match and return final URL if valid."""
        if not raw_url or is_blacklisted_cdn(urlparse(raw_url).netloc):
            return None
        detected = detect_language_from_url_4kads(raw_url)
        if not detected or detected == "OTHER":
            detected = lang_name
        if detected.upper() != lang_name.upper():
            return None
        return build_final_url_4k(raw_url)

    def process_lang_4k(lang_code, lang_name):
        for attempt in range(3):
            try:
                # Try SSAI=True first (live), then SSAI=False (non-live/VOD)
                for use_ssai in [True, False]:
                    player_config = get_player_config_4k(lang_code, use_ssai)
                    if not player_config:
                        continue

                    # --- Pass 1: Dedicated 4K streams, exact type ---
                    streams_4k = extract_4k_streams(player_config)
                    for s in streams_4k:
                        if s.get("type", "").upper() != variant_type.upper():
                            continue
                        final = try_url(s.get("url", ""), lang_name)
                        if final:
                            with lock:
                                if lang_name not in results:
                                    results[lang_name] = final
                            return

                    # --- Pass 2: For fallback, accept any 4K variant (primary too) ---
                    if variant_type == "fallback":
                        for s in streams_4k:
                            final = try_url(s.get("url", ""), lang_name)
                            if final:
                                with lock:
                                    if lang_name not in results:
                                        results[lang_name] = final
                                return

                    # --- Pass 3: General streams with 4K tag/resolution check ---
                    general_streams = extract_all_streams_general(player_config)
                    # For fallback: check both types; for primary: only primary
                    check_types = ["fallback", "primary"] if variant_type == "fallback" else ["primary"]
                    for check_type in check_types:
                        for s in general_streams:
                            if s.get("type", "").lower() != check_type:
                                continue
                            raw_url = s.get("url", "")
                            if not raw_url:
                                continue
                            tags = s.get("playback_tags", "").lower()
                            height = int(s.get("height") or 0)
                            is_4k = (
                                "4k" in tags or height >= 2160 or
                                "_4k" in raw_url.lower() or "/4k/" in raw_url.lower()
                            )
                            if not is_4k:
                                continue
                            # Detect lang from tags if URL doesn't have it
                            lang_detected = detect_language_from_url_4kads(raw_url)
                            if not lang_detected or lang_detected == "OTHER":
                                for tag in tags.split(";"):
                                    if tag.strip().startswith("language:"):
                                        dc = tag.split(":")[1].strip().lower()
                                        lang_detected = LANGUAGES.get(dc, lang_name)
                                        break
                            if not lang_detected or lang_detected.upper() != lang_name.upper():
                                continue
                            final = build_final_url_4k(raw_url)
                            if final:
                                with lock:
                                    if lang_name not in results:
                                        results[lang_name] = final
                                return

            except Exception:
                if attempt < 2:
                    time.sleep(1)
                continue

    with ThreadPoolExecutor(max_workers=4) as ex:
        futures = [ex.submit(process_lang_4k, code, name) for code, name in UNIQUE_LANGUAGES.items()]
        for _ in as_completed(futures):
            pass
    return results


def option14_fallback_4k_24h(input_url: str):
    """Option 14 – FALLBACK 4K streams with 24-hour token."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL.{RESET}")
        return

    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)

    print(f"{BOLD_RED}24-HOURS FALLBACK 4K STREAMS{RESET}\n")
    global_token = get_global_hdntl_token()
    if not global_token:
        print(f"{RED}Failed to get global token. Aborting.{RESET}")
        return
    exp_match = re.search(r"exp=(\d+)", global_token)
    if exp_match:
        exp_str = datetime.fromtimestamp(int(exp_match.group(1))).strftime("%Y-%m-%d %H:%M:%S")
        print(f"{GREEN}✓ Token fetched, expires at {exp_str}{RESET}")
    else:
        print(f"{GREEN}✓ Token fetched{RESET}")

    logo_url = extract_logo_from_url(input_url)
    print(f"{BOLD_RED}LOGO{RESET}")
    if logo_url:
        print(logo_url)
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print(f"{BOLD_GREEN}{title}{RESET}")
    print(f"{BOLD_MAGENTA}{stream_type}{RESET}")

    lang_order = ["ENGLISH","HINDI","MARATHI","GUJARATI","BHOJPURI","PUNJABI",
                  "HARYANVI","TAMIL","TELUGU","KANNADA","MALAYALAM","BENGALI"]
    results = _fetch_4k_24h_streams(slug_path, "fallback", lang_order, global_token)

    if not results:
        print(f"{RED}No 4K fallback streams found. (Site may not have 4K for this content){RESET}")
        return

    entries = []
    seen = set()
    for lang in lang_order:
        if lang in results:
            url = results[lang]
            base = url.split("?")[0]
            if base in seen:
                continue
            seen.add(base)
            print(f"{BOLD_CYAN}{lang} 4K{RESET}")
            print(f"{GREEN}{url}{RESET}")
            entries.append((lang, url, False))

    print(f"\n{BOLD_GREEN}GLOBAL COOKIE:{RESET}\n{CYAN}hdntl={global_token}{RESET}")
    if entries:
        offer_m3u_creation(entries, title, match_no, stream_type, logo_url, auto_hdntl=global_token)


def option15_primary_4k_24h(input_url: str):
    """Option 15 – PRIMARY 4K streams with 24-hour token."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL.{RESET}")
        return

    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)

    print(f"{BOLD_RED}24-HOURS PRIMARY 4K STREAMS{RESET}\n")
    global_token = get_global_hdntl_token()
    if not global_token:
        print(f"{RED}Failed to get global token. Aborting.{RESET}")
        return
    exp_match = re.search(r"exp=(\d+)", global_token)
    if exp_match:
        exp_str = datetime.fromtimestamp(int(exp_match.group(1))).strftime("%Y-%m-%d %H:%M:%S")
        print(f"{GREEN}✓ Token fetched, expires at {exp_str}{RESET}")
    else:
        print(f"{GREEN}✓ Token fetched{RESET}")

    logo_url = extract_logo_from_url(input_url)
    print(f"{BOLD_RED}LOGO{RESET}")
    if logo_url:
        print(logo_url)
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print(f"{BOLD_GREEN}{title}{RESET}")
    print(f"{BOLD_MAGENTA}{stream_type}{RESET}")

    lang_order = ["ENGLISH","HINDI","MARATHI","GUJARATI","BHOJPURI","PUNJABI",
                  "HARYANVI","TAMIL","TELUGU","KANNADA","MALAYALAM","BENGALI"]
    results = _fetch_4k_24h_streams(slug_path, "primary", lang_order, global_token)

    if not results:
        print(f"{RED}No 4K primary streams found. (Site may not have 4K for this content){RESET}")
        return

    entries = []
    seen = set()
    for lang in lang_order:
        if lang in results:
            url = results[lang]
            base = url.split("?")[0]
            if base in seen:
                continue
            seen.add(base)
            print(f"{BOLD_CYAN}{lang} 4K{RESET}")
            print(f"{GREEN}{url}{RESET}")
            entries.append((lang, url, False))

    print(f"\n{BOLD_GREEN}GLOBAL COOKIE:{RESET}\n{CYAN}hdntl={global_token}{RESET}")
    if entries:
        offer_m3u_creation(entries, title, match_no, stream_type, logo_url, auto_hdntl=global_token)



# ===================== M3U FUNCTIONS =====================

def option18_quick_multilang(input_url: str):
    """Option 18 – Quick fetch all available languages (FHD, no cookie needed for preview)."""
    print(f"{BOLD_CYAN}=== QUICK MULTI-LANG STREAM GRAB ==={RESET}\n")
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL.{RESET}")
        return

    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)
    print(f"{BOLD_GREEN}{title}{RESET} | {BOLD_MAGENTA}{stream_type}{RESET}\n")

    lang_order = ["ENGLISH","HINDI","MARATHI","GUJARATI","BHOJPURI","PUNJABI",
                  "HARYANVI","TAMIL","TELUGU","KANNADA","MALAYALAM","BENGALI"]
    results = {}
    lock = threading.Lock()

    def fetch_single(lang_code, lang_name):
        try:
            api_url = build_api_url(slug_path, lang_code, "2")
            req = request.Request(api_url, headers=build_headers())
            with request.urlopen(req, timeout=10) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            player_config = None
            for sec in data.get("success", {}).get("page", {}).get("spaces", {}).values():
                for w in sec.get("widget_wrappers", []):
                    d = w.get("widget", {}).get("data", {})
                    if "player_config" in d:
                        player_config = d["player_config"]
                        break
                if player_config:
                    break
            if not player_config:
                return
            streams = extract_all_streams_general(player_config)
            for s in streams:
                raw = s.get("url", "")
                if not raw or is_blacklisted_cdn(urlparse(raw).netloc):
                    continue
                detected = detect_language_from_url_4kads(raw)
                if not detected or detected == "OTHER":
                    tags = s.get("playback_tags", "")
                    for tag in tags.split(";"):
                        if tag.strip().startswith("language:"):
                            dc = tag.split(":")[1].strip().lower()
                            detected = LANGUAGES.get(dc, lang_name)
                            break
                if detected.upper() == lang_name.upper():
                    with lock:
                        if lang_name not in results:
                            results[lang_name] = raw.split("?")[0]
                    return
        except Exception:
            pass

    with ThreadPoolExecutor(max_workers=3) as ex:
        futures = [ex.submit(fetch_single, code, name) for code, name in UNIQUE_LANGUAGES.items()]
        for _ in as_completed(futures):
            pass

    if not results:
        print(f"{RED}No streams found.{RESET}")
        return

    entries = []
    seen = set()
    for lang in lang_order:
        if lang in results:
            url = results[lang]
            if url in seen:
                continue
            seen.add(url)
            print(f"{BOLD_CYAN}{lang}{RESET}")
            print(f"{GREEN}{url}{RESET}")
            entries.append((lang, url, False))

    print(f"\n{CYAN}Total: {len(entries)} languages found{RESET}")
    if entries:
        offer_m3u_creation(entries, title, match_no, stream_type, "")


# ===================== M3U FUNCTIONS =====================
CF_CONFIG_FILE = "cf_config.json"
def fetch_drm_for_lang(slug_path: str, lang_code: str, lang_name: str) -> List[Tuple[str, str, str, str]]:
    """
    Fetch DRM MPD + keys for a specific language.
    Returns list of (display_lang, variant, mpd_url, key_str)
    """
    results = []
    try:
        # Use the DRM‑specific API for this language
        api_url = build_drm_api_url(slug_path, lang_code)
        req = request.Request(api_url, headers=build_headers())
        with request.urlopen(req, timeout=12) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        player_config = None
        for sec in data.get("success", {}).get("page", {}).get("spaces", {}).values():
            for w in sec.get("widget_wrappers", []):
                d = w.get("widget", {}).get("data", {})
                if "player_config" in d:
                    player_config = d["player_config"]
                    break
            if player_config:
                break
        if not player_config:
            return results

        drm_streams = extract_drm_info(player_config)
        if not drm_streams:
            return results

        # Get global keys from first MPD
        global_keys = []
        global_license = ""
        for s in drm_streams:
            if s.get("license_url"):
                global_license = s["license_url"]
                break
        first_mpd = drm_streams[0]["mpd_url"] if drm_streams else ""
        if first_mpd and global_license:
            try:
                mpd_info = fetch_mpd_pssh(first_mpd)
                if mpd_info and mpd_info.get("key_ids"):
                    ck = try_clearkey_json(mpd_info["key_ids"], global_license)
                    if ck:
                        global_keys = ck
                    elif mpd_info.get("pssh"):
                        wv = fetch_widevine_keys(mpd_info["pssh"], global_license)
                        if wv and not any(l.startswith("❌") for l in wv):
                            global_keys = wv
            except Exception:
                pass
        key_str_global = ",".join(global_keys) if global_keys else global_license

        seen_mpds = set()
        for stream in drm_streams:
            mpd_url = stream["mpd_url"]
            mpd_base = mpd_url.split("?")[0]
            if mpd_base in seen_mpds:
                continue
            seen_mpds.add(mpd_base)
            variant = stream.get("variant", "PRIMARY")
            # Get available languages inside this MPD
            avail_langs = extract_mpd_languages(mpd_url)
            if not avail_langs:
                avail_langs = [(lang_code, lang_name)]
            for _, audio_lang_name in avail_langs:
                # Use audio language name for display
                display = f"{audio_lang_name} [{variant}]"
                key_str = key_str_global
                try:
                    mpd_info = fetch_mpd_pssh(mpd_url)
                    if mpd_info and mpd_info.get("key_ids") and stream.get("license_url"):
                        ck = try_clearkey_json(mpd_info["key_ids"], stream["license_url"])
                        if ck:
                            key_str = ",".join(ck)
                        elif mpd_info.get("pssh"):
                            wv = fetch_widevine_keys(mpd_info["pssh"], stream["license_url"])
                            if wv and not any(l.startswith("❌") for l in wv):
                                key_str = ",".join(wv)
                except Exception:
                    pass
                results.append((display, variant, mpd_url, key_str))
    except Exception as e:
        # Silently ignore – will fallback to M3U8
        pass
    return results

def option7_main(slug_path: str, title: str, match_no: str, stream_type: str, input_url: str = ""):
    """Option 7: DRM with keys, fallback HLS. No cookie for replay/highlights."""
    print(f"{BOLD_GREEN}=== DRM/M3U8 ==={RESET}\n")

    # Extract logo (same as before)
    logo_url = ""
    if input_url:
        try:
            logo_url = extract_logo_from_url(input_url)
        except Exception:
            pass
    if not logo_url:
        try:
            api_url_logo = build_drm_api_url(slug_path, "eng")
            req_logo = request.Request(api_url_logo, headers=build_headers())
            with request.urlopen(req_logo, timeout=10) as r:
                d = json.loads(r.read().decode("utf-8"))
            for sec in d.get("success", {}).get("page", {}).get("spaces", {}).values():
                for w in sec.get("widget_wrappers", []):
                    pc = w.get("widget", {}).get("data", {}).get("player_config")
                    if pc:
                        img = (pc.get("expanded_content_poster", {}).get("image", {}).get("src")
                               or pc.get("cast_image", {}).get("src"))
                        if img:
                            logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                        break
        except Exception:
            pass

    # All unique display names from LANGUAGES dict
    unique_lang_names = set()
    for code, name in LANGUAGES.items():
        unique_lang_names.add(name)

    lang_order = [
        "ENGLISH", "HINDI", "HINDI HD", "MARATHI", "GUJARATI",
        "BHOJPURI", "PUNJABI", "HARYANVI", "TAMIL", "TELUGU",
        "KANNADA", "MALAYALAM", "BENGALI", "ORIYA"
    ]
    for name in unique_lang_names:
        if name not in lang_order:
            lang_order.append(name)

    lang_path_map = {
        "ENGLISH": ["eng", "en"],
        "HINDI": ["hin", "hi"],
        "MARATHI": ["mar", "mr", "ma"],
        "GUJARATI": ["guj", "gu"],
        "BHOJPURI": ["bih", "bh", "bho"],
        "PUNJABI": ["pan", "pun", "pa", "pu"],
        "HARYANVI": ["har", "hv", "ha"],
        "TAMIL": ["tam", "ta"],
        "TELUGU": ["tel", "te"],
        "KANNADA": ["kan", "kn"],
        "MALAYALAM": ["mal", "ml"],
        "BENGALI": ["ben", "bn"],
    }
    unique_langs = {}
    for code, name in LANGUAGES.items():
        if name not in unique_langs:
            unique_langs[name] = code

    results = {}  # lang_name -> (url, key_str, variant)
    lock = threading.Lock()

    def fetch_one_lang_drm(lang_name, lang_code):
        expected_segments = lang_path_map.get(lang_name, [lang_code.lower()])
        try:
            api_url = build_drm_api_url(slug_path, lang_code)
            req = request.Request(api_url, headers=build_headers())
            with request.urlopen(req, timeout=12) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            player_config = None
            for sec in data.get("success", {}).get("page", {}).get("spaces", {}).values():
                for w in sec.get("widget_wrappers", []):
                    d = w.get("widget", {}).get("data", {})
                    if "player_config" in d:
                        player_config = d["player_config"]
                        break
                if player_config:
                    break
            if not player_config:
                return

            drm_streams = extract_drm_info(player_config)
            if not drm_streams:
                return

            # For each stream, get MPD and keys
            for stream in drm_streams:
                mpd_url = stream["mpd_url"]
                url_lower = mpd_url.lower()
                if not any(f"/{seg}/" in url_lower for seg in expected_segments):
                    continue
                variant = stream.get("variant", "PRIMARY")
                license_url = stream.get("license_url", "")

                # Fetch keys from license URL
                key_str = ""
                if license_url:
                    try:
                        mpd_info = fetch_mpd_pssh(mpd_url)
                        if mpd_info and mpd_info.get("key_ids"):
                            ck = try_clearkey_json(mpd_info["key_ids"], license_url)
                            if ck:
                                key_str = ",".join(ck)
                            elif mpd_info.get("pssh"):
                                wv = fetch_widevine_keys(mpd_info["pssh"], license_url)
                                if wv and not any(l.startswith("❌") for l in wv):
                                    key_str = ",".join(wv)
                    except Exception:
                        pass
                with lock:
                    if lang_name not in results or variant == "PRIMARY":
                        results[lang_name] = (mpd_url, key_str, variant)
        except Exception:
            pass

    # Try DRM
    with ThreadPoolExecutor(max_workers=6) as executor:
        futures = [executor.submit(fetch_one_lang_drm, name, code) for code, name in UNIQUE_LANGUAGES.items()]
        for future in as_completed(futures, timeout=60):
            try:
                future.result()
            except Exception:
                pass

    # If no DRM, fallback to HLS
    if not results:
        hls_results = {}
        def fetch_hls_lang(lang_name, lang_code):
            try:
                res = fetch_lang_stream(lang_code, lang_name, slug_path, input_url, "2")
                if res:
                    hls_results[lang_name] = res["stream"]
            except Exception:
                pass
        with ThreadPoolExecutor(max_workers=6) as executor:
            futures = [executor.submit(fetch_hls_lang, name, code) for code, name in UNIQUE_LANGUAGES.items()]
            for future in as_completed(futures, timeout=60):
                try:
                    future.result()
                except Exception:
                    pass
        if hls_results:
            for lang, url in hls_results.items():
                results[lang] = (url, "", "HLS")
        else:
            print(f"{RED}No HLS streams found either. Aborting.{RESET}")
            return

    # Output
    print(f"{BOLD_MAGENTA}LOGO{RESET}")
    if logo_url:
        print(f"{GREEN}{logo_url}{RESET}")
    else:
        print()
    print(f"{BOLD_CYAN}{title}{RESET}")
    print(f"{BOLD_YELLOW}{stream_type}{RESET}")

    for lang in lang_order:
        if lang in results:
            url, key_str, variant = results[lang]
            # For REPLAY/HIGHLIGHTS, no cookie
            if stream_type in ["REPLAY", "HIGHLIGHTS"]:
                hdntl_val = ""
            else:
                hdntl_val = get_hdntl_token_4kads(url) or extract_hdntl(url)

            if key_str:  # DRM
                ott_url = build_ott_drm_url_direct(url.split("?")[0], key_str, hdntl_val)
            else:        # HLS fallback
                if hdntl_val:
                    ott_url = f"{url}|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={hdntl_val}"
                else:
                    ott_url = f"{url}|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com"
            print(f"{BOLD_BLUE}{lang}{RESET}")
            print(f"{GREEN}{ott_url}{RESET}")

    # M3U creation
    m3u_entries = []
    for lang, (url, key_str, _) in results.items():
        if stream_type in ["REPLAY", "HIGHLIGHTS"]:
            hdntl_val = ""
        else:
            hdntl_val = get_hdntl_token_4kads(url) or extract_hdntl(url)
        if key_str:
            ott_url = build_ott_drm_url_direct(url.split("?")[0], key_str, hdntl_val)
        else:
            if hdntl_val:
                ott_url = f"{url}|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={hdntl_val}"
            else:
                ott_url = f"{url}|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com"
        m3u_entries.append((lang, ott_url, False))
    if m3u_entries:
        offer_m3u_creation(m3u_entries, title, match_no, stream_type, logo_url)
     
def option8_direct_mpd(slug_path: str, title: str, match_no: str, stream_type: str, input_url: str = ""):
    """Option 8: Show all DRM streams (primary, fallback, ssai/non_ssai) as NS Player URLs."""

    # Extract logo
    logo_url = ""
    if input_url:
        try:
            logo_url = extract_logo_from_url(input_url)
        except Exception:
            pass
    if not logo_url:
        try:
            api_url_logo = build_drm_api_url(slug_path, "eng")
            req_logo = request.Request(api_url_logo, headers=build_headers())
            with request.urlopen(req_logo, timeout=10) as r:
                d = json.loads(r.read().decode("utf-8"))
            for sec in d.get("success", {}).get("page", {}).get("spaces", {}).values():
                for w in sec.get("widget_wrappers", []):
                    pc = w.get("widget", {}).get("data", {}).get("player_config")
                    if pc:
                        img = (pc.get("expanded_content_poster", {}).get("image", {}).get("src")
                               or pc.get("cast_image", {}).get("src"))
                        if img:
                            logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                        break
        except Exception:
            pass

    print(f"\n{BOLD_RED}LOGO{RESET}")
    if logo_url:
        print(f"{GREEN}{logo_url}{RESET}")
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print(f"{BOLD_GREEN}{title}{RESET}")
    print(f"{BOLD_MAGENTA}{stream_type}{RESET}")

    # Get player config (any language, use eng)
    player_config = None
    try:
        api_url = build_drm_api_url(slug_path, "eng")
        req = request.Request(api_url, headers=build_headers())
        with request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        for sec in data.get("success", {}).get("page", {}).get("spaces", {}).values():
            for w in sec.get("widget_wrappers", []):
                d = w.get("widget", {}).get("data", {})
                if "player_config" in d:
                    player_config = d["player_config"]
                    break
            if player_config:
                break
    except Exception as e:
        print(f"{RED}Failed to fetch player config: {e}{RESET}")
        return

    if not player_config:
        print(f"{RED}No player config found.{RESET}")
        return

    # Extract all DRM streams (including fallback)
    drm_streams = extract_drm_info(player_config)
    if not drm_streams:
        print(f"{YELLOW}No DRM streams found. Falling back to HLS...{RESET}")
        # Fallback to HLS (same as option 2)
        entries = fetch_m3u8_streams(slug_path, input_url, "2")
        if entries:
            for lang, url, is_hdr in entries:
                hdr_tag = " HDR" if is_hdr else ""
                print(f"{BOLD_CYAN}{lang}{hdr_tag}{RESET}")
                print(f"{GREEN}{url}{RESET}")
            offer_m3u_creation(entries, title, match_no, stream_type, logo_url)
        else:
            print(f"{RED}No streams found.{RESET}")
        return

    # For each stream, get MPD URL, variant, playback_tags (to detect ssai/non_ssai), and keys
    all_results = []  # list of (display_name, mpd_url, key_str, variant, is_ads_free)
    for stream in drm_streams:
        mpd_url = stream["mpd_url"]
        variant = stream.get("variant", "PRIMARY")
        license_url = stream.get("license_url", "")
        playback_tags = stream.get("playback_tags", "")  # may contain "ssai" or "non_ssai"

        # Detect if ads-free (non_ssai) or not
        is_ads_free = "non_ssai" in str(playback_tags).lower()
        # Also try to get from player_config if needed
        if not is_ads_free:
            # Check if any playback_tags in the original player_config indicate non_ssai
            pc_tags = str(player_config.get("playback_tags", "")).lower()
            if "non_ssai" in pc_tags:
                is_ads_free = True

        # Fetch keys for this MPD (pro.py logic: fallback to license URL if no keys)
        key_str = ""
        if license_url:
            try:
                mpd_info = fetch_mpd_pssh(mpd_url)
                if mpd_info and mpd_info.get("key_ids"):
                    ck = try_clearkey_json(mpd_info["key_ids"], license_url)
                    if ck:
                        key_str = ",".join(ck)
                    elif mpd_info.get("pssh"):
                        wv = fetch_widevine_keys(mpd_info["pssh"], license_url)
                        if wv and not any(l.startswith("❌") for l in wv):
                            key_str = ",".join(wv)
            except Exception:
                pass
            if not key_str:
                key_str = license_url  # player fetches keys itself

        # Extract available languages from MPD (or fallback to URL)
        languages = extract_mpd_languages(mpd_url)
        if not languages:
            # Guess from URL path
            for code, name in LANGUAGES.items():
                if f"/{code}/" in mpd_url.lower():
                    languages = [(code, name)]
                    break
        if not languages:
            languages = [("eng", "ENGLISH")]

        for lang_code, lang_name in languages:
            display_name = f"{lang_name} [{variant}]"
            if not is_ads_free:
                display_name += " [SSAI]"
            else:
                display_name += " [ADSFREE]"
            all_results.append((display_name, mpd_url, key_str, variant, is_ads_free))

    # Deduplicate by display_name (keep first)
    seen = set()
    unique_results = []
    for res in all_results:
        if res[0] not in seen:
            seen.add(res[0])
            unique_results.append(res)

    if not unique_results:
        print(f"{RED}No DRM streams found.{RESET}")
        return

    # Output in NS Player format
    m3u_entries = []
    for display_name, mpd_url, key_str, variant, is_ads_free in unique_results:
        # For REPLAY/HIGHLIGHTS, no cookie
        if stream_type in ["REPLAY", "HIGHLIGHTS"]:
            hdntl_val = ""
        else:
            hdntl_val = get_hdntl_token_4kads(mpd_url) or extract_hdntl(mpd_url)
        ott_url = build_ott_drm_url_direct(mpd_url.split("?")[0], key_str, hdntl_val)
        print(f"{BOLD_CYAN}{display_name}{RESET}")
        print(f"{GREEN}{ott_url}{RESET}\n")
        m3u_entries.append((display_name, ott_url, False))

    # Offer M3U creation
    if m3u_entries:
        offer_m3u_creation(m3u_entries, title, match_no, stream_type, logo_url)

# ===================== OPTION 10 (MODIFIED) — DRM-TV 24-HOURS LINK 24-HOUR ENGLISH =====================

def option10_drm_tv_24h(
    input_url: str,
    _shared_token: Optional[str] = None,
    _batch_mode: bool = False,
    _show_logo: bool = True,
    _title_override: Optional[str] = None,
) -> Optional[list]:
    """
    Option 10 — DRM-TV 24-HOURS LINK with 24-HOUR token, English only.
    4K HDR : via 4KADS API (option-6 style, HLS — use_sdr=False)
    4K SDR : via 4KADS API (option-6 style, HLS — use_sdr=True)
    FHD    : via DRM API (MPD) with optional ClearKey keys embedded
    24-hour cookie same as options 14/15/18/19.
    TV Show/Web Series: saare episodes detect karke list karo.
    """
    # ── TV Show / Web Series detection ────────────────────────────────────────
    _show_slug_check = extract_slug_path(input_url)
    _url_path_lower = input_url.split("?")[0].lower().rstrip("/")
    _slug_parts = _show_slug_check.split("/") if _show_slug_check else []
    _has_episode_indicator = any(
        seg in _url_path_lower
        for seg in ["/video/", "/watch", "episode", "/e-", "/ep-", "/s-", "/season"]
    )
    _is_show_page = (
        "/shows/" in _url_path_lower
        and _show_slug_check is not None
        and len(_slug_parts) <= 3
        and not _has_episode_indicator
    )
    if _is_show_page:
        print(f"\n{BOLD_CYAN}📺 TV Show / Web Series detected — fetching episode list...{RESET}")
        _raw_eps = fetch_show_episodes(input_url)   # [(season_no, disp, url), ...]
        if not _raw_eps:
            print(f"{YELLOW}⚠ Could not fetch episodes. Processing show URL directly...{RESET}")
        else:
            # ── Group by season (preserve insertion order) ───────────────────────
            _seasons: dict = {}
            _season_order: list = []
            for _sno, _et, _eu in _raw_eps:
                if _sno not in _seasons:
                    _seasons[_sno] = []
                    _season_order.append(_sno)
                _seasons[_sno].append((_et, _eu))

            # ── Season selector ──────────────────────────────────────────────────
            if len(_season_order) == 1:
                _sel_seasons = _season_order[:]
            else:
                print(f"\n{BOLD_GREEN}Found {len(_season_order)} Season(s):{RESET}")
                for _si, _sk in enumerate(_season_order, 1):
                    _slabel = f"SEASON-{_sk}" if _sk else "SEASON (UNKNOWN)"
                    print(f"  {BOLD_GREEN}{{{_si}}}{RESET} {WHITE}{_slabel}{RESET}")
                print(f"\n{BOLD_YELLOW}Enter Season number(s) (e.g. 1 or 1.2.3) or {BOLD_CYAN}'all'{RESET}{BOLD_YELLOW} for all Seasons:{RESET}")
                _s_raw = input(f"{BOLD_CYAN}Choose ➤ {RESET}").strip()
                _sel_seasons = []
                if _s_raw.lower() == "all":
                    _sel_seasons = _season_order[:]
                else:
                    for _p in _s_raw.replace(".", ",").split(","):
                        if _p.strip().isdigit():
                            _sidx = int(_p.strip()) - 1
                            if 0 <= _sidx < len(_season_order):
                                _sel_seasons.append(_season_order[_sidx])
                if not _sel_seasons:
                    print(f"{RED}No seasons selected.{RESET}")
                    return None

            # ── Collect episodes for selected seasons ────────────────────────────
            _pool: list = []
            for _sk in _sel_seasons:
                for _et, _eu in _seasons[_sk]:
                    _pool.append((_et, _eu, _sk))   # (title, url, season_no)

            # ── Episode selector ─────────────────────────────────────────────────
            _selected: list = []
            if len(_pool) == 1:
                _selected = _pool[:]
            else:
                print(f"\n{BOLD_GREEN}Found {len(_pool)} episode(s):{RESET}")
                for _ei, _ep_item in enumerate(_pool, 1):
                    print(f"  {BOLD_GREEN}{{{_ei}}}{RESET} {WHITE}{_ep_item[0]}{RESET}")
                print(f"\n{BOLD_YELLOW}Enter episode number(s) (e.g. 1 or 1.2.3) or {BOLD_CYAN}'all'{RESET}{BOLD_YELLOW} for all episodes:{RESET}")
                _ep_raw = input(f"{BOLD_CYAN}Choose ➤ {RESET}").strip()
                if _ep_raw.lower() == "all":
                    _selected = _pool[:]
                else:
                    for _p in _ep_raw.replace(".", ",").split(","):
                        if _p.strip().isdigit():
                            _eidx = int(_p.strip()) - 1
                            if 0 <= _eidx < len(_pool):
                                _selected.append(_pool[_eidx])
                if not _selected:
                    print(f"{RED}No episodes selected.{RESET}")
                    return None

            # ── Process selected episodes ────────────────────────────────────────
            if len(_selected) == 1:
                input_url = _selected[0][1]
                print(f"\n{BOLD_GREEN}» {_selected[0][0]}{RESET}")
            else:
                # ── Token once for all episodes ──────────────────────────────────
                _batch_tok = get_global_hdntl_token()
                if not _batch_tok:
                    print(f"{RED}Failed to get 24-hour token.{RESET}")
                    return None
                _exp_m = re.search(r"exp=(\d+)", _batch_tok)
                if _exp_m:
                    _exp_str = datetime.fromtimestamp(
                        int(_exp_m.group(1))).strftime("%Y-%m-%d %H:%M:%S")
                    print(f"\n{GREEN}✓ Token fetched, expires at {_exp_str}{RESET}")
                else:
                    print(f"\n{GREEN}✓ Token fetched{RESET}")

                # Show name from slug (e.g. house-of-the-dragon → HOUSE OF THE DRAGON)
                _sname_pretty = (
                    (_slug_parts[1] if len(_slug_parts) >= 2 else "")
                    .replace("-", " ").title().upper()
                )
                _all_entries: list = []
                _is_first_ep = True
                for _ep_item in _selected:
                    _mt, _mu, _msk = _ep_item
                    _stitle = (f"{_sname_pretty} SEASON {_msk}"
                               if _msk else _sname_pretty)
                    print(f"\n{BOLD_CYAN}{_mt}{RESET}")
                    _ep_entries = option10_drm_tv_24h(
                        _mu,
                        _shared_token=_batch_tok,
                        _batch_mode=True,
                        _show_logo=_is_first_ep,
                        _title_override=_stitle,
                    )
                    if _ep_entries:
                        # inject episode title marker for TXT file
                        _all_entries.append(("__TITLE__", _mt, False))
                        _all_entries.extend(_ep_entries)
                    _is_first_ep = False

                print(f"\n{BOLD_YELLOW}ENJOY FOR 24 HOUR'S VALIDITY 😎{RESET}")
                _season_keys = sorted(set(
                    str(_e[2]) for _e in _selected if _e[2]
                ))
                _suf = ("_SEASON-" + "-".join(_season_keys)) if _season_keys else ""
                _fname = f"{_sname_pretty.replace(' ', '_')}{_suf}.txt"
                offer_m3u_creation(
                    _all_entries, _sname_pretty, "", "TV SHOW", "",
                    auto_hdntl=_batch_tok,
                    filename_override=_fname,
                )
                return None
    # ─────────────────────────────────────────────────────────────────────────

    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid Hotstar URL!{RESET}")
        return

    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)

    # ── Step 1: Global 24-hour token ─────────────────────────────────────────────
    if _shared_token:
        global_token = _shared_token
    else:
        global_token = get_global_hdntl_token()
        if not global_token:
            print(f"{RED}Failed to get 24-hour token. Aborting.{RESET}")
            return None
        exp_match = re.search(r"exp=(\d+)", global_token)
        if exp_match:
            exp_str = datetime.fromtimestamp(int(exp_match.group(1))).strftime("%Y-%m-%d %H:%M:%S")
            print(f"{GREEN}✓ Token fetched, expires at {exp_str}{RESET}")
        else:
            print(f"{GREEN}✓ Token fetched{RESET}")

    logo_url = extract_logo_from_url(input_url)

    # ── Step 2: 4K Dolby Vision, HDR & SDR streams — English only ───────────────
    asset_id   = parse_asset_id_4kads(input_url)
    eng_codes  = LANG_MAP_4KADS.get("1", ["eng"])
    dv_url     = None
    hdr_url    = None
    sdr_4k_url = None

    if asset_id:
        # Dolby Vision — try up to 3 times with DV builder
        for _attempt in range(3):
            for _lc in eng_codes:
                try:
                    _api = build_api_url_4kads_dv(asset_id, _lc, slug_path=slug_path)
                    _pc  = fetch_player_config_4kads(_api)
                    for _s in extract_all_streams_4kads(_pc):
                        if str(_s.get("type","")).lower() != "primary":
                            continue
                        _raw = str(_s.get("content_url","") or "")
                        if not _raw or is_cloudfront_url(_raw) or is_blacklisted_cdn(urlparse(_raw).netloc):
                            continue
                        dv_url = rewrite_url_to_clean_cdn(_raw)
                        break
                    if dv_url:
                        break
                except Exception:
                    continue
            if dv_url:
                break

        r_hdr = fetch_stream_4kads_lite(asset_id, eng_codes, "ENGLISH",
                                        use_sdr=False, slug_path=slug_path)
        if r_hdr:
            hdr_url = r_hdr[1]

        r_sdr = fetch_stream_4kads_lite(asset_id, eng_codes, "ENGLISH",
                                        use_sdr=True, slug_path=slug_path)
        if r_sdr:
            sdr_4k_url = r_sdr[1]

    # ── Step 3: FHD MPD streams from DRM API (FALLBACK + PRIMARY + keys) ─────────
    def _find_license(obj, depth=0):
        if depth > 8 or not isinstance(obj, (dict, list)):
            return None
        if isinstance(obj, list):
            for item in obj:
                r = _find_license(item, depth + 1)
                if r:
                    return r
        elif isinstance(obj, dict):
            for k in ["license_url", "licenseUrl", "widevine_license_url",
                       "keyServerUrl", "key_server_url", "keyserver_url",
                       "drm_license_url", "drmLicenseUrl"]:
                if k in obj and obj[k]:
                    return str(obj[k])
            for v in obj.values():
                r = _find_license(v, depth + 1)
                if r:
                    return r
        return None

    def _get_clearkeys(mpd_raw_url: str, license_url: str) -> str:
        if not license_url:
            return ""
        try:
            fetch_url = mpd_raw_url
            if "hdnea" not in mpd_raw_url and "hdntl" not in mpd_raw_url:
                sep = "&" if "?" in mpd_raw_url else "?"
                fetch_url = f"{mpd_raw_url}{sep}hdnea={global_token}"
            mpd_info = fetch_mpd_pssh(fetch_url)
            if not mpd_info or not mpd_info.get("key_ids"):
                mpd_info = fetch_mpd_pssh(mpd_raw_url)
            if mpd_info and mpd_info.get("key_ids"):
                ck = try_clearkey_json(mpd_info["key_ids"], license_url)
                if ck:
                    return ",".join(ck)
                elif mpd_info.get("pssh"):
                    wv = fetch_widevine_keys(mpd_info["pssh"], license_url)
                    if wv and not any(l.startswith("❌") for l in wv):
                        return ",".join(wv)
        except Exception:
            pass
        # Fallback (pro.py logic): license URL itself → player fetches keys automatically
        return license_url

    # Fetch FHD MPD streams — keep one FALLBACK + one PRIMARY
    fhd_streams: dict = {}
    try:
        api_url = build_drm_api_url(slug_path, "eng")
        req = request.Request(api_url, headers=build_headers())
        with request.urlopen(req, timeout=14) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        pc = None
        for sec in data.get("success", {}).get("page", {}).get("spaces", {}).values():
            for w in sec.get("widget_wrappers", []):
                d = w.get("widget", {}).get("data", {})
                if "player_config" in d:
                    pc = d["player_config"]
                    break
            if pc:
                break
        if pc:
            if not logo_url:
                img = (pc.get("expanded_content_poster", {}).get("image", {}).get("src")
                       or pc.get("cast_image", {}).get("src"))
                if img:
                    logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
            global_lic = _find_license(pc)
            seen_b: set = set()
            # Collect base URLs already shown as 4K — skip duplicates in FHD section
            already_4k_bases = {u.split("?")[0] for u in [dv_url, hdr_url, sdr_4k_url] if u}
            for key in ["media_asset", "media_asset_v2"]:
                assets = pc.get(key)
                if not assets:
                    continue
                if isinstance(assets, dict):
                    assets = [assets]
                for asset in assets:
                    for variant in ["primary", "fallback"]:
                        item = asset.get(variant)
                        if not isinstance(item, dict):
                            continue
                        url = item.get("content_url", "")
                        if not url or ".mpd" not in url:
                            continue
                        base = url.split("?")[0]
                        if base in seen_b or base in already_4k_bases:
                            continue
                        seen_b.add(base)
                        lic = (item.get("license_url") or item.get("licenseUrl")
                               or item.get("keyServerUrl") or item.get("key_server_url")
                               or global_lic or "")
                        v = variant.upper()
                        if v not in fhd_streams:
                            fhd_streams[v] = {"url": url, "base": base, "license_url": lic}
    except Exception:
        pass

    # ── Print header (only for first episode in batch, or single episode) ────────
    if _show_logo:
        print(f"\n{BOLD_RED}LOGO{RESET}")
        if logo_url:
            print(logo_url)
        if match_no:
            print(f"{GREEN}{match_no}{RESET}")
        print(f"{BOLD_GREEN}{_title_override or title}{RESET}")
        print(f"{BOLD_MAGENTA}{stream_type}{RESET}\n")

    # ── Step 3.5: HLS FALLBACK (5.97 Mbps) + PRIMARY (4.49 Mbps) ────────────────
    # Same logic as option 14 (FALLBACK) and option 15 (PRIMARY).
    # No language filter — take the first available FALLBACK and PRIMARY HLS stream
    # (matches like cricket may only broadcast in Hindi, not English).
    hls_fallback_url: Optional[str] = None
    hls_primary_url:  Optional[str] = None
    try:
        pc_hls = fetch_player_config_for_slug(slug_path, "eng")
        hls_streams = extract_all_streams_general(pc_hls)
        for s in hls_streams:
            raw = s.get("url", "")
            if not raw or ".m3u8" not in raw:
                continue
            if is_blacklisted_cdn(urlparse(raw).netloc):
                continue
            final_hls = build_final_24h_url(raw, global_token)
            if not final_hls:
                continue
            if s["type"] == "fallback" and hls_fallback_url is None:
                hls_fallback_url = final_hls
            elif s["type"] == "primary" and hls_primary_url is None:
                hls_primary_url = final_hls
    except Exception:
        pass

    # ── Step 4: URL builders ──────────────────────────────────────────────────────
    def _build_24h_hls(raw_url: str) -> str:
        """HLS stream from 4KADS: strip old auth → add 24h token."""
        base = raw_url.split("?")[0]
        return (f"{base}?a=ns&ttl=86400&hdnea={global_token}"
                f"|Cookie=hdntl={global_token}"
                f"&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)"
                f"&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com")

    def _build_24h_mpd(base_mpd: str, key_str: str) -> str:
        """MPD stream: 24h token + optional ClearKey."""
        drm = f"&drmScheme=clearkey&drmLicense={key_str}" if key_str else ""
        return (f"{base_mpd}?a=ns&ttl=86400&hdnea={global_token}"
                f"|Cookie=hdntl={global_token}"
                f"&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)"
                f"&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com{drm}")

    # ── Step 5: Collect ALL KIDs from ALL MPD streams → one license call ────────
    entries = []

    # Gather every MPD URL available (4K streams may also be MPD for movies)
    _all_mpd_sources = []
    for _u in [dv_url, hdr_url, sdr_4k_url]:
        if _u and ".mpd" in _u:
            _all_mpd_sources.append(_u)
    for _v in ["FALLBACK", "PRIMARY"]:
        if _v in fhd_streams:
            _all_mpd_sources.append(fhd_streams[_v]["url"])

    # ALSO add MPD URLs from DRM API (Widevine MPD) — these have ALL KIDs in XML
    # Pro.py approach: build_drm_api_url gives a different MPD with all 3 KIDs
    _master_lic = ""
    try:
        _drm_api_url = build_drm_api_url(slug_path, "eng")
        _drm_req = request.Request(_drm_api_url, headers=build_headers())
        with request.urlopen(_drm_req, timeout=12) as _drm_resp:
            _drm_data = json.loads(_drm_resp.read().decode("utf-8"))
        _drm_pc = None
        for _sec in _drm_data.get("success", {}).get("page", {}).get("spaces", {}).values():
            for _w in _sec.get("widget_wrappers", []):
                _d = _w.get("widget", {}).get("data", {})
                if "player_config" in _d:
                    _drm_pc = _d["player_config"]
                    break
            if _drm_pc:
                break
        if _drm_pc:
            _drm_streams = extract_drm_info(_drm_pc)
            for _ds in _drm_streams:
                _du = _ds.get("mpd_url", "")
                if _du and ".mpd" in _du and _du not in _all_mpd_sources:
                    _all_mpd_sources.append(_du)
                if not _master_lic and _ds.get("license_url"):
                    _master_lic = _ds["license_url"]
    except Exception:
        pass

    # Find best license URL (from fhd_streams first if DRM API didn't give one)
    if not _master_lic:
        for _v in ["PRIMARY", "FALLBACK"]:
            if _v in fhd_streams and fhd_streams[_v].get("license_url"):
                _master_lic = fhd_streams[_v]["license_url"]
                break

    # Collect ALL unique KIDs from every MPD file
    _all_kids: list = []
    _all_kids_seen: set = set()
    _pssh_fallback = ""
    for _mpd_url in _all_mpd_sources:
        try:
            _fu = _mpd_url
            if "hdnea" not in _mpd_url and "hdntl" not in _mpd_url:
                _sep = "&" if "?" in _mpd_url else "?"
                _fu = f"{_mpd_url}{_sep}hdnea={global_token}"
            _info = fetch_mpd_pssh(_fu)
            if not _info or not _info.get("key_ids"):
                _info = fetch_mpd_pssh(_mpd_url)
            if _info:
                for _kid in (_info.get("key_ids") or []):
                    _kc = _kid.replace("-", "").lower()
                    if len(_kc) == 32 and _kc not in _all_kids_seen:
                        _all_kids_seen.add(_kc)
                        _all_kids.append(_kc)
                if not _pssh_fallback and _info.get("pssh"):
                    _pssh_fallback = _info["pssh"]
        except Exception:
            pass

    # One license request for ALL KIDs → gives ALL keys including 4K-only ones
    all_keys_str = ""
    if _all_kids and _master_lic:
        _ck = try_clearkey_json(_all_kids, _master_lic)
        if _ck:
            all_keys_str = ",".join(_ck)
        elif _pssh_fallback:
            _wv = fetch_widevine_keys(_pssh_fallback, _master_lic)
            if _wv and not any(_l.startswith("❌") for _l in _wv):
                all_keys_str = ",".join(_wv)
    # Last resort: original per-stream fetch
    if not all_keys_str:
        for _v in ["PRIMARY", "FALLBACK"]:
            if _v in fhd_streams:
                _ks = _get_clearkeys(fhd_streams[_v]["url"], fhd_streams[_v]["license_url"])
                if _ks:
                    all_keys_str = _ks
                    break

    # Apply same complete key set to every stream variant
    fhd_keys = {_v: all_keys_str for _v in ["FALLBACK", "PRIMARY"] if _v in fhd_streams}
    primary_key_str = all_keys_str

    # ── 4K streams: deduplicate by base URL, label by actual lowest quality ──────
    # If DV/HDR API falls back to SDR (same base), only the SDR label is kept.
    _4k_unique: dict = {}  # base → (label, url) — first write (lowest quality) wins
    for _lbl, _u in [("4K SDR", sdr_4k_url), ("4K HDR", hdr_url), ("4K Dolby Vision", dv_url)]:
        if not _u:
            continue
        _b = _u.split("?")[0]
        if _b not in _4k_unique:
            _4k_unique[_b] = (_lbl, _u)

    # Display highest quality first (reverse label priority order)
    _quality_rank = {"4K Dolby Vision": 2, "4K HDR": 1, "4K SDR": 0}
    for _lbl, _u in sorted(_4k_unique.values(),
                            key=lambda x: _quality_rank.get(x[0], 0), reverse=True):
        final = _build_24h_hls(_u)
        if primary_key_str:
            final += f"&drmScheme=clearkey&drmLicense={primary_key_str}"
        print(f"{BOLD_CYAN}{_lbl} [PRIMARY]{RESET}")
        print(f"{GREEN}{final}{RESET}\n")
        entries.append((f"{_lbl} [PRIMARY]", final, True))

    # FHD FALLBACK + PRIMARY MPD (deduplicated — no 4K duplicates here)
    for variant in ["FALLBACK", "PRIMARY"]:
        if variant not in fhd_streams:
            continue
        s = fhd_streams[variant]
        key_str = fhd_keys.get(variant, "")
        final = _build_24h_mpd(s["base"], key_str)
        label = f"FHD [{variant}]"
        print(f"{BOLD_CYAN}{label}{RESET}")
        print(f"{GREEN}{final}{RESET}\n")
        entries.append((label, final, False))

    # ── HLS FALLBACK (5.97 Mbps) — same as Option 14 ─────────────────────────────
    if hls_fallback_url:
        label = "HLS ENGLISH [FALLBACK] [5.97 Mbps]"
        print(f"{BOLD_CYAN}{label}{RESET}")
        print(f"{GREEN}{hls_fallback_url}{RESET}\n")
        entries.append((label, hls_fallback_url, False))

    # ── HLS PRIMARY (4.49 Mbps) — same as Option 15 ──────────────────────────────
    if hls_primary_url:
        label = "HLS ENGLISH [PRIMARY] [4.49 Mbps]"
        print(f"{BOLD_CYAN}{label}{RESET}")
        print(f"{GREEN}{hls_primary_url}{RESET}\n")
        entries.append((label, hls_primary_url, False))

    if not entries:
        print(f"{RED}No English streams could be fetched.{RESET}")
        return

    if _batch_mode:
        return entries

    print(f"{BOLD_YELLOW}ENJOY FOR 24 HOUR'S VALIDITY 😎{RESET}")
    offer_m3u_creation(entries, title, match_no, stream_type, logo_url, auto_hdntl=global_token)
    return None

def build_final_url(raw_url: str) -> str:
    # Option 5 style: working CDN host find karo
    working_host = get_working_cdn_host(raw_url)
    parsed = urlparse(raw_url)
    # Host replace karo
    converted = parsed._replace(netloc=working_host).geturl()
    base = converted.split("?")[0]   # saare query params hatao
    token_part = f"a=ns&ttl=86400&hdnea={global_token}|Cookie=hdntl={global_token}"
    headers_part = f"&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com"
    return f"{base}?{token_part}{headers_part}"

def get_fallback_24h_entries(input_url: str) -> List[Tuple[str, str, bool]]:
    """Return entries for Option 12 (fallback) – same logic as option12_long_lived but returns list."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        return []
    global_token = get_global_hdntl_token()
    if not global_token:
        return []
    # Fetch all languages using quality "2"
    lang_streams = {}
    seen_bases = set()
    with ThreadPoolExecutor(max_workers=2) as ex:  # RATE LIMIT: 6→2
        futures = {
            ex.submit(fetch_lang_stream, code, name, slug_path, input_url, "2"): name
            for code, name in UNIQUE_LANGUAGES.items()
        }
        for future in as_completed(futures):
            res = future.result()
            if not res:
                continue
            lang_name = res["lang_name"]
            raw_url = res["stream"]
            base = raw_url.split("?")[0]
            if base in seen_bases:
                continue
            seen_bases.add(base)
            lang_streams[lang_name] = (raw_url, res.get("is_hdr", False))

    if not lang_streams:
        return []

    def build_final_url(raw_url: str) -> str:
        # Option 5 style: working CDN host find karo
        working_host = get_working_cdn_host(raw_url)
        parsed = urlparse(raw_url)
        # Host replace karo
        converted = parsed._replace(netloc=working_host).geturl()
        base = converted.split("?")[0]   # saare query params hatao
        token_part = f"a=ns&ttl=86400&hdnea={global_token}|Cookie=hdntl={global_token}"
        headers_part = f"&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com"
        return f"{base}?{token_part}{headers_part}"

    results = {}
    for lang_name, (raw_url, is_hdr) in lang_streams.items():
        url_path = raw_url.split("?")[0].lower()
        lang_codes = [code for code, name in LANGUAGES.items() if name == lang_name]
        if not any(f"/{c}/" in url_path for c in lang_codes):
            continue
        final_url = build_final_url(raw_url)
        results[lang_name] = (final_url, is_hdr)

    if not results:
        # fallback: show all without verification
        for lang_name, (raw_url, is_hdr) in lang_streams.items():
            results[lang_name] = (build_final_url(raw_url), is_hdr)

    entries = []
    lang_order = ["ENGLISH","HINDI","MARATHI","GUJARATI","BHOJPURI","PUNJABI",
                  "HARYANVI","TAMIL","TELUGU","KANNADA","MALAYALAM","BENGALI"]
    seen_base = set()
    for lang_name in lang_order:
        if lang_name not in results:
            continue
        url, is_hdr = results[lang_name]
        base = url.split("?")[0]
        if base in seen_base:
            continue
        seen_base.add(base)
        entries.append((lang_name, url, is_hdr))
    return entries

def get_primary_24h_entries(input_url: str) -> List[Tuple[str, str, bool]]:
    """Return entries for Option 13 (primary) – same logic as option13_primary_24h but returns list."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        return []
    global_token = get_global_hdntl_token()
    if not global_token:
        return []
    # Fetch all languages using quality "1"
    lang_streams = {}
    seen_bases = set()
    with ThreadPoolExecutor(max_workers=2) as ex:  # RATE LIMIT: 6→2
        futures = {
            ex.submit(fetch_lang_stream, code, name, slug_path, input_url, "1"): name
            for code, name in UNIQUE_LANGUAGES.items()
        }
        for future in as_completed(futures):
            res = future.result()
            if not res:
                continue
            lang_name = res["lang_name"]
            raw_url = res["stream"]
            base = raw_url.split("?")[0]
            if base in seen_bases:
                continue
            seen_bases.add(base)
            lang_streams[lang_name] = (raw_url, res.get("is_hdr", False))

    if not lang_streams:
        return []

    def build_final_url(raw_url: str) -> str:
        # Option 5 style: working CDN host find karo
        working_host = get_working_cdn_host(raw_url)
        parsed = urlparse(raw_url)
        # Host replace karo
        converted = parsed._replace(netloc=working_host).geturl()
        base = converted.split("?")[0]   # saare query params hatao
        token_part = f"a=ns&ttl=86400&hdnea={global_token}|Cookie=hdntl={global_token}"
        headers_part = f"&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com"
        return f"{base}?{token_part}{headers_part}"

    results = {}
    for lang_name, (raw_url, is_hdr) in lang_streams.items():
        url_path = raw_url.split("?")[0].lower()
        lang_codes = [code for code, name in LANGUAGES.items() if name == lang_name]
        if not any(f"/{c}/" in url_path for c in lang_codes):
            continue
        final_url = build_final_url(raw_url)
        results[lang_name] = (final_url, is_hdr)

    if not results:
        for lang_name, (raw_url, is_hdr) in lang_streams.items():
            results[lang_name] = (build_final_url(raw_url), is_hdr)

    entries = []
    lang_order = ["ENGLISH","HINDI","MARATHI","GUJARATI","BHOJPURI","PUNJABI",
                  "HARYANVI","TAMIL","TELUGU","KANNADA","MALAYALAM","BENGALI"]
    seen_base = set()
    for lang_name in lang_order:
        if lang_name not in results:
            continue
        url, is_hdr = results[lang_name]
        base = url.split("?")[0]
        if base in seen_base:
            continue
        seen_base.add(base)
        entries.append((lang_name, url, is_hdr))
    return entries

def get_fallback_4k_24h_entries(input_url: str) -> List[Tuple[str, str, bool]]:
    """Return entries for Option 14 (fallback 4K) – returns list instead of printing."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        return []
    global_token = get_global_hdntl_token()
    if not global_token:
        return []
    lang_order = ["ENGLISH","HINDI","MARATHI","GUJARATI","BHOJPURI","PUNJABI",
                  "HARYANVI","TAMIL","TELUGU","KANNADA","MALAYALAM","BENGALI"]
    results = _fetch_4k_24h_streams(slug_path, "fallback", lang_order, global_token)
    entries = []
    seen = set()
    for lang in lang_order:
        if lang in results:
            url = results[lang]
            base = url.split("?")[0]
            if base in seen:
                continue
            seen.add(base)
            entries.append((lang, url, False))
    return entries

def get_primary_4k_24h_entries(input_url: str) -> List[Tuple[str, str, bool]]:
    """Return entries for Option 15 (primary 4K) – returns list instead of printing."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        return []
    global_token = get_global_hdntl_token()
    if not global_token:
        return []
    lang_order = ["ENGLISH","HINDI","MARATHI","GUJARATI","BHOJPURI","PUNJABI",
                  "HARYANVI","TAMIL","TELUGU","KANNADA","MALAYALAM","BENGALI"]
    results = _fetch_4k_24h_streams(slug_path, "primary", lang_order, global_token)
    entries = []
    seen = set()
    for lang in lang_order:
        if lang in results:
            url = results[lang]
            base = url.split("?")[0]
            if base in seen:
                continue
            seen.add(base)
            entries.append((lang, url, False))
    return entries

def fetch_show_episodes(show_url: str) -> list:
    """
    Hotstar show/web-series ke saare episodes fetch karo.

    Strategy (in order):
      0. HAR-confirmed Episode Navigation Widget API (bff/v2/pages/978/spaces/1445/...)
         — seasons API se season IDs nikalo, phir har season ke episodes fetch karo
      1. Hotstar content API  (api.hotstar.com/o/v1/episodes) — offset pagination
      2. BFF slugs page       (bff/v2/slugs) — more_grid_items_url + _extract_title_and_slug
    Returns: [(display_title, episode_url), ...]
    """
    slug = extract_slug_path(show_url)
    if not slug:
        return []

    # The numeric content-id is the last segment of the slug
    # e.g. "shows/house-of-the-dragon/1971002877" → "1971002877"
    content_id = parse_asset_id_4kads(show_url) or slug.split("/")[-1]
    # Derive show name slug (2nd segment if present)
    slug_parts = slug.split("/")  # ["shows", "house-of-the-dragon", "1971002877"]
    show_name_slug = slug_parts[1] if len(slug_parts) >= 2 else ""

    episodes: list = []
    seen_ids: set = set()          # dedup by episode content-id or cleaned URL
    token = load_user_token()

    # ── Shared web headers (older API + BFF both need these) ──────────────────
    _WEB_HDRS = {
        "User-Agent": (
            "Mozilla/5.0 (Linux; Android 10; K) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/114.0.0.0 Mobile Safari/537.36"
        ),
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en-US,en;q=0.9",
        "x-country-code": "IN",
        "X-Country-Code": "in",
        "x-platform-code": "PCTV",
        "X-HS-Platform": "web",
        "x-hs-platform": "web",
        "X-HS-AppVersion": "6.72.1",
        "Referer": "https://www.hotstar.com/",
        "Origin": "https://www.hotstar.com",
    }
    if token:
        _WEB_HDRS["x-hs-usertoken"] = token

    # ── BFF Android-TV headers (same as fetch_live_events) ────────────────────
    _BFF_HDRS = {
        "User-Agent": "Hotstar;in.startv.hotstar.dplus.tv/26.05.10.2 (Android/14; tv)",
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en",
        "X-HS-Platform": "androidtv",
        "X-Country-Code": "in",
        "X-HS-Accept-language": "eng",
        "x-hs-app": "260510002",
        "x-hs-retry-count": "0",
        "x-hs-is-retry": "false",
        "X-HS-Client": (
            "platform:androidtv;app_id:in.startv.hotstar.dplus.tv;"
            "app_version:26.05.10.2;os:Android;os_version:14;schema_version:0.0.1690"
        ),
        "Referer": "https://www.hotstar.com/",
        "Origin": "https://www.hotstar.com",
    }
    if token:
        _BFF_HDRS["x-hs-usertoken"] = token

    # ── Helper: URL canonicalize (no in/in doubling) ──────────────────────────
    def _ep_url(raw: str) -> str:
        raw = (raw or "").strip().split("?")[0]  # strip query params from slug
        if raw.startswith("http"):
            return raw
        if raw.startswith("/in/"):
            return f"https://www.hotstar.com{raw}"
        if raw.startswith("/"):
            return f"https://www.hotstar.com{raw}"
        if raw.startswith("in/"):
            raw = raw[3:]
        return f"https://www.hotstar.com/in/{raw}"

    # ── Helper: add episode to list if not duplicate ──────────────────────────
    def _add(season_no: int, title: str, url: str, ep_num: str = "") -> bool:
        ep_clean = url.split("?")[0].rstrip("/")
        show_clean = show_url.split("?")[0].rstrip("/")
        # Must be deeper than the show URL (i.e. an episode, not the show root)
        if ep_clean == show_clean:
            return False
        if ep_clean in seen_ids:
            return False
        seen_ids.add(ep_clean)
        disp = f"EP{ep_num}: {title}" if ep_num else title
        episodes.append((season_no, disp, url))
        return True

    # ══════════════════════════════════════════════════════════════════════════
    # Strategy 0 — HAR-confirmed Episode Navigation Widget API
    #
    # HAR entry 23 exact API (uses WEB platform headers, not androidtv!):
    # GET bff/v2/pages/978/spaces/1445/widgets/3799/widgets/168
    #   ?content_id={show_id}&season_content_id={season_id}&season_id={season_id}
    #   &page_enum=detail&wti_name=EpisodeNavigation
    # Response: success.widget_wrapper.widget.data.items[].playable_content.data
    # ══════════════════════════════════════════════════════════════════════════

    # ── WEB platform headers — HAR entry 23 pe exactly yahi headers hain ──────
    # CRITICAL: ye API androidtv headers se kaam nahi karti, sirf web se
    _WEB_EP_HDRS = {
        "User-Agent": (
            "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
        ),
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "eng",
        "x-country-code": "in",
        "X-Country-Code": "in",
        "x-hs-accept-language": "eng",
        "x-hs-platform": "web",
        "X-HS-Platform": "web",
        "x-hs-app": "260618000",
        "x-hs-client": (
            "platform:web;app_version:26.06.18.0;browser:Chrome;"
            "schema_version:0.0.1756;os:Linux;os_version:x86_64;"
            "browser_version:124;network_data:4g"
        ),
        "x-hs-is-retry": "false",
        "x-hs-retry-count": "0",
        "x-request-id": str(uuid.uuid4()),
        "x-hs-request-id": str(uuid.uuid4()),
        "Referer": f"https://www.hotstar.com/in/shows/{show_name_slug}/{content_id}",
        "Origin": "https://www.hotstar.com",
    }
    if token:
        _WEB_EP_HDRS["x-hs-usertoken"] = token

    _EP_NAV_BASE = (
        "https://www.hotstar.com/api/internal/bff/v2/pages/978"
        "/spaces/1445/widgets/3799/widgets/168"
    )

    def _fetch_ep_nav_season(season_id: str) -> int:
        """Ek season ke saare episodes fetch karo via EpisodeNavigation widget.

        HAR-confirmed pagination:
          Page 1  → GET widgets/168?content_id=...&season_content_id=...&season_id=...
                     &page_enum=detail&wti_name=EpisodeNavigation
          Page 2+ → GET widgets/168/items?<same params>
                     &token={"pageNo":N,"pageSize":10,"sortOrder":"asc"}   (URL-encoded)
        Response: success.widget_wrapper.widget.data.items[]
        Stop when items list is empty or shorter than pageSize.
        """
        _PAGE_SIZE  = 10
        _MAX_PAGES  = 500   # safety cap
        _ITEMS_BASE = f"{_EP_NAV_BASE}/items"
        _COMMON_QS  = (
            f"content_id={content_id}"
            f"&season_content_id={season_id}&season_id={season_id}"
            f"&page_enum=detail&wti_name=EpisodeNavigation"
        )
        added = 0

        def _extract_items(data: dict) -> list:
            return (
                data.get("success", {})
                    .get("widget_wrapper", {})
                    .get("widget", {})
                    .get("data", {})
                    .get("items", [])
            )

        def _process_items(items: list) -> int:
            count = 0
            for _itm in items:
                _pc = (_itm.get("playable_content") or {}).get("data") or {}
                _title = (_pc.get("title") or "").strip()
                _ep_no, _ep_sno = "", 0
                for _tag in (_pc.get("tags") or []):
                    _tv = (_tag.get("value") or "").strip()
                    _m = re.match(r"S(\d+)\s*E(\d+)", _tv, re.IGNORECASE)
                    if _m:
                        _ep_sno = int(_m.group(1))
                        _ep_no  = _m.group(2)
                        break
                _slug = ""
                for _act in (_pc.get("actions", {}).get("on_click") or []):
                    _nav = _act.get("page_navigation") or {}
                    if _nav.get("page_slug"):
                        _slug = _nav["page_slug"]
                        break
                if _title and _slug:
                    if _add(_ep_sno, _title, _ep_url(_slug), _ep_no):
                        count += 1
            return count

        # ── Page 1: initial widget URL (no token) ────────────────────────────
        try:
            _url1 = f"{_EP_NAV_BASE}?{_COMMON_QS}"
            _req1 = request.Request(_url1, headers=_WEB_EP_HDRS)
            with request.urlopen(_req1, timeout=15) as _r1:
                _d1 = json.loads(_r1.read().decode("utf-8", errors="replace"))
            _items1 = _extract_items(_d1)
            added += _process_items(_items1)
            if len(_items1) < _PAGE_SIZE:
                return added   # All episodes fit in page 1
        except Exception:
            return added

        # ── Pages 2, 3, 4, … : /items endpoint with token param ──────────────
        for _page_no in range(2, _MAX_PAGES + 1):
            try:
                _tok = parse.quote(
                    json.dumps({"pageNo": _page_no, "pageSize": _PAGE_SIZE,
                                "sortOrder": "asc"}, separators=(",", ":"))
                )
                _url_n = f"{_ITEMS_BASE}?{_COMMON_QS}&token={_tok}"
                _req_n = request.Request(_url_n, headers=_WEB_EP_HDRS)
                with request.urlopen(_req_n, timeout=15) as _rn:
                    _dn = json.loads(_rn.read().decode("utf-8", errors="replace"))
                _items_n = _extract_items(_dn)
                if not _items_n:
                    break   # No more episodes
                added += _process_items(_items_n)
                if len(_items_n) < _PAGE_SIZE:
                    break   # Last page (partial) — done
            except Exception:
                break

        return added

    def _scan_json_for_season_ids(obj, found: list, show_cid: str):
        """JSON mein recursively walk karke season content IDs dhundho."""
        if isinstance(obj, dict):
            # season_content_id / season_id keys check karo
            for _k in ("season_content_id", "season_id", "seasonContentId", "seasonId"):
                _v = str(obj.get(_k) or "").strip()
                if _v and _v.isdigit() and _v != show_cid and _v not in found:
                    found.append(_v)
            # content_id jo show se alag ho aur season ke liye ho
            for _ck in ("content_id", "contentId"):
                _cv = str(obj.get(_ck) or "").strip()
                _type = str(obj.get("type") or obj.get("content_type") or "").lower()
                if (_cv and _cv.isdigit() and _cv != show_cid
                        and _cv not in found and "season" in _type):
                    found.append(_cv)
            for _v in obj.values():
                _scan_json_for_season_ids(_v, found, show_cid)
        elif isinstance(obj, list):
            for _item in obj:
                _scan_json_for_season_ids(_item, found, show_cid)

    # ── Season IDs discover karo ──────────────────────────────────────────────
    # IMPORTANT: BFF slugs endpoint with androidtv headers → JSON milta hai
    #            Web browser headers → HTML (Next.js SSR page) milta hai — JSON nahi!
    # Isliye season discovery ke liye _BFF_HDRS (androidtv) use karo.
    _season_ids: list = []

    try:
        _slugs_url = (
            f"https://www.hotstar.com/api/internal/bff/v2/slugs/in/{slug}"
            f"?client_capabilities={parse.quote(_LIVE_CAPABILITIES)}"
            f"&drm_parameters={parse.quote(_LIVE_DRM)}"
            f"&request_features=consent_supported&lang=eng"
        )
        _req_sl = request.Request(_slugs_url, headers=_BFF_HDRS)
        with request.urlopen(_req_sl, timeout=15) as _rsl:
            _sld = json.loads(_rsl.read().decode("utf-8", errors="replace"))
        # Full JSON scan for season_content_id / season_id keys
        _scan_json_for_season_ids(_sld, _season_ids, content_id)
        # Also look for items with page_slugs that have /s-N/ pattern
        _full_txt = json.dumps(_sld)
        for _sm in re.finditer(r'"page_slug"\s*:\s*"[^"]+/s-\d+/(\d{8,12})', _full_txt):
            _sid = _sm.group(1)
            if _sid and _sid != content_id and _sid not in _season_ids:
                _season_ids.append(_sid)
        # Also scan for season_content_id= in URL strings within the response
        for _sm in re.finditer(r'season_content_id=(\d{8,12})', _full_txt):
            _sid = _sm.group(1)
            if _sid and _sid != content_id and _sid not in _season_ids:
                _season_ids.append(_sid)
    except Exception:
        pass

    # Fallback: single-season show ya last resort — content_id ko hi season ID maano
    if not _season_ids:
        _season_ids = [content_id]

    # ── Har season ke episodes fetch karo ─────────────────────────────────────
    for _season_id in _season_ids:
        try:
            _fetch_ep_nav_season(_season_id)
        except Exception:
            pass

    if episodes:
        return episodes

    # ══════════════════════════════════════════════════════════════════════════
    # Strategy 1 — Hotstar content API: /o/v1/episodes?tvsId=...
    # ══════════════════════════════════════════════════════════════════════════
    try:
        _offset = 0
        _limit  = 100
        _max_pages = 20

        for _ in range(_max_pages):
            _ep_api = (
                f"https://api.hotstar.com/o/v1/episodes"
                f"?tvsId={content_id}&contentId={content_id}"
                f"&limit={_limit}&offset={_offset}"
                f"&lang=eng&client=web&clientVersion=6.72.1&region=IN"
            )
            _req_e = request.Request(_ep_api, headers=_WEB_HDRS)
            with request.urlopen(_req_e, timeout=12) as _re:
                _ep_data = json.loads(_re.read().decode("utf-8", errors="replace"))

            # Response shape: body.results.items  OR  body.results
            _body    = _ep_data.get("body") or _ep_data.get("data") or {}
            _results = _body.get("results") or _body
            _items   = _results.get("items") or _results.get("assets") or []

            if not _items:
                break

            for _ep in _items:
                if not isinstance(_ep, dict):
                    continue
                _title  = str(_ep.get("title") or _ep.get("name") or "").strip()
                _ep_no  = str(_ep.get("episodeNo") or _ep.get("episode_number") or
                              _ep.get("episodeNumber") or "").strip()
                _web    = (_ep.get("webUrl") or _ep.get("web_url") or
                           _ep.get("deeplink_url") or _ep.get("slug") or "")
                # Fallback URL: build from show slug + content id
                if not _web:
                    _ep_content_id = str(_ep.get("contentId") or _ep.get("id") or "")
                    if _ep_content_id and show_name_slug:
                        _season = str(_ep.get("seasonNo") or _ep.get("season_number") or "1")
                        _web = (
                            f"/in/shows/{show_name_slug}/{content_id}"
                            f"/s-{_season}/{_ep_content_id}"
                        )
                _sno_1 = int(_ep.get("seasonNo") or _ep.get("season_number")
                             or _ep.get("seasonNumber") or 0)
                if _title and _web:
                    _add(_sno_1, _title, _ep_url(_web), _ep_no)

            # Pagination
            _total    = int(_results.get("total") or _results.get("totalResults") or 0)
            _next_off = int(_results.get("nextOffset") or _results.get("next_offset") or 0)
            _offset  += len(_items)
            # Stop only when: fetched everything, got fewer than limit, or no total known
            if len(_items) < _limit:
                break
            if _total and _offset >= _total:
                break
            if _next_off:
                _offset = _next_off

    except Exception:
        pass  # Fall through to Strategy 2

    if episodes:
        return episodes

    # ══════════════════════════════════════════════════════════════════════════
    # Strategy 2 — BFF slugs page + more_grid_items_url pagination
    # (same pattern as fetch_best_in_sports / _collect_events_from_spaces)
    # ══════════════════════════════════════════════════════════════════════════
    try:
        _bff_base = (
            f"https://www.hotstar.com/api/internal/bff/v2/slugs/in/{slug}"
            f"?client_capabilities={parse.quote(_LIVE_CAPABILITIES)}"
            f"&drm_parameters={parse.quote(_LIVE_DRM)}"
            f"&request_features=consent_supported&lang=eng"
        )
        _BFF_SITE = "https://www.hotstar.com/api/internal/bff"

        def _ingest_spaces(spaces: dict) -> int:
            """Walk spaces; add episode items; return count added."""
            added = 0
            _ITEM_KEYS = ("items", "cards", "assets", "tray", "content", "data")
            for _sp in spaces.values():
                if not isinstance(_sp, dict):
                    continue
                for _wr in (_sp.get("widget_wrappers") or []):
                    if not isinstance(_wr, dict):
                        continue
                    _wd = (_wr.get("widget") or {}).get("data") or {}
                    _candidates: list = []
                    for _k in _ITEM_KEYS:
                        _v = _wd.get(_k)
                        if isinstance(_v, list):
                            _candidates.extend(_v)
                        elif isinstance(_v, dict):
                            for _kk in _ITEM_KEYS:
                                _sub = _v.get(_kk)
                                if isinstance(_sub, list):
                                    _candidates.extend(_sub)
                    for _itm in _candidates:
                        _t, _s = _extract_title_and_slug(_itm)
                        if not _t or not _s:
                            continue
                        _eu = _ep_url(_s)
                        _ec = _eu.split("?")[0].rstrip("/")
                        _sc = show_url.split("?")[0].rstrip("/")
                        # Must be deeper (episode) not show root
                        if (("/shows/" in _ec or "/episodes/" in _ec)
                                and _ec != _sc
                                and len(_ec) > len(_sc)):
                            _sno_2 = 0
                            _sm2 = re.search(r'/s-(\d+)/', _eu)
                            if _sm2:
                                _sno_2 = int(_sm2.group(1))
                            if _add(_sno_2, _t, _eu):
                                added += 1
            return added

        def _fetch_more(more_url: str) -> tuple:
            _full = _BFF_SITE + more_url if more_url.startswith("/") else more_url
            _rr = request.Request(_full, headers=_BFF_HDRS)
            with request.urlopen(_rr, timeout=15) as _r2:
                _d2 = json.loads(_r2.read().decode("utf-8", errors="replace"))
            _pay = _d2.get("data") or _d2.get("success") or {}
            return (_pay.get("items") or [], _pay.get("more_grid_items_url") or "")

        # First page
        _rq0 = request.Request(_bff_base, headers=_BFF_HDRS)
        with request.urlopen(_rq0, timeout=15) as _r0:
            _d0 = json.loads(_r0.read().decode("utf-8", errors="replace"))
        _spaces0 = (_d0.get("success") or {}).get("page", {}).get("spaces", {})
        _ingest_spaces(_spaces0)

        # Walk widgets for more_grid_items_url (up to 20 pages)
        _pages = 0
        for _sp0 in _spaces0.values():
            if not isinstance(_sp0, dict):
                continue
            for _wr0 in (_sp0.get("widget_wrappers") or []):
                _wg0   = _wr0.get("widget") or {}
                _wd0   = _wg0.get("data") or {}
                _init  = len(_wd0.get("items") or [])
                _murl  = (
                    _wd0.get("more_grid_items_url") or
                    _wg0.get("more_grid_items_url") or
                    _wr0.get("more_grid_items_url") or ""
                )
                _wid   = (_wg0.get("id") or _wg0.get("widget_id") or
                          _wd0.get("id") or _wd0.get("widget_id") or "")
                if not _murl and _init > 0 and _wid:
                    _murl = (
                        f"/api/internal/bff/v2/slugs/in/{slug}"
                        f"/widgets/{_wid}/items?size=10&offset={_init}"
                    )
                _off2 = _init + 10
                while _murl and _pages < 20:
                    _pages += 1
                    try:
                        _more_items, _murl = _fetch_more(_murl)
                        if not _more_items:
                            break
                        _fake = {"pg": {"widget_wrappers": [{"widget": {"data": {"items": _more_items}}}]}}
                        _ingest_spaces(_fake)
                        if not _murl and _wid:
                            _murl = (
                                f"/api/internal/bff/v2/slugs/in/{slug}"
                                f"/widgets/{_wid}/items?size=10&offset={_off2}"
                            )
                            _off2 += 10
                        if not _more_items:
                            break
                    except Exception:
                        break

    except Exception:
        pass

    return episodes


# ===================== AUTO-UPDATE MODE (MULTI-EVENT) =====================
def auto_update_mode_multi(event_list):
    """Auto-update M3U for multiple events — combined into one playlist per cycle."""
    global _ACTIVE_TOKEN_OVERRIDE
    print(f"{BOLD_GREEN}=== AUTO-UPDATE MODE (MULTI-EVENT: {len(event_list)} events) ==={RESET}")

    # Fetch logos upfront (once)
    logos = {}
    for evt_title, evt_url in event_list:
        logo = extract_logo_from_url(evt_url)
        logos[evt_url] = logo or ""
        if logo:
            print(f"{GREEN}✓ Logo found: {evt_title}{RESET}")
        else:
            print(f"{YELLOW}⚠ No logo: {evt_title}{RESET}")

    # Quality menu
    print(f"{BOLD_YELLOW}Available qualities:{RESET}")
    print(f"{BOLD_GREEN}{{1}} H.265 4K DV,HDR,SDR ADSFREE{RESET}")
    print(f"{BOLD_GREEN}{{2}} H.265 FHD DV,HDR,SDR{RESET}")
    print(f"{BOLD_GREEN}{{3}} H.265 AUTO DV,HDR,SDR ADSFREE{RESET}")
    print(f"{BOLD_YELLOW}{{4}} ADS-FREE JHS HD{RESET}")
    print(f"{BOLD_MAGENTA}{{5}} JHS 4K{RESET}")
    print(f"{BOLD_WHITE}{{6}} H.264 4K DV,HDR,SDR{RESET}")
    print(f"{BOLD_WHITE}{{7}} H.265 4K DV,HDR,SDR{RESET}")
    print(f"{BOLD_WHITE}{{8}} H.264 FHD DV,HDR,SDR{RESET}")
    print(f"{BOLD_WHITE}{{9}} H.265 FHD DV,HDR,SDR{RESET}")
    print(f"{BOLD_GREEN}{{10}} ADS-FREE 4K TattiJio & Chortel users{RESET}")
    print(f"{BOLD_GREEN}{{17}} FALLBACK 24-HOURS LINK{RESET}")
    print(f"{BOLD_BLUE}{{18}} PRIMARY 24-HOURS LINK{RESET}")
    print(f"{BOLD_GREEN}{{19}} FALLBACK 24-HOURS TattiJio & Chortel users{RESET}")
    print(f"{BOLD_BLUE}{{20}} PRIMARY 24-HOURS TattiJio & Chortel users{RESET}")
    print(f"{BOLD_YELLOW}{{21}} FALLBACK 4K 24-HOURS LINK{RESET}")
    print(f"{BOLD_MAGENTA}{{22}} PRIMARY 4K 24-HOURS LINK{RESET}")
    quality_raw = input(f"{BOLD_CYAN}Choose quality (e.g. 1 or 1,2): {RESET}").strip()
    quality_list = [q.strip() for q in quality_raw.replace(".", ",").split(",")
                    if q.strip() in ["1","2","3","4","5","6","7","8","9","10","17","18","19","20","21","22"]]
    if not quality_list:
        print(f"{RED}Invalid choice. Defaulting to 2.{RESET}")
        quality_list = ["2"]
    quality = quality_list[0]
    if len(quality_list) > 1:
        print(f"{GREEN}✓ Multi-quality mode: {', '.join(quality_list)}{RESET}")

    interval_raw = input(f"Update interval in minutes (default 25): ").strip()
    interval = int(interval_raw) if interval_raw.isdigit() else 25
    filename = input(f"M3U filename (default: hotstar_multi.m3u): ").strip()
    if not filename:
        filename = "hotstar_multi.m3u"

    # Token setup
    token_count_raw = input(f"{BOLD_CYAN}How Many Token Use Per Request Cycles (default 2): {RESET}").strip()
    token_count = int(token_count_raw) if token_count_raw.isdigit() and 1 <= int(token_count_raw) <= 99 else 2
    _home = os.path.expanduser("~")
    multi_token_list = []
    for _ti in range(1, token_count + 1):
        for _tp in [os.path.join(_home, f"token{_ti}.txt"), f"token{_ti}.txt"]:
            if os.path.isfile(_tp):
                try:
                    with open(_tp, "r", encoding="utf-8") as _tf:
                        _tok = _tf.read().strip()
                    if _tok:
                        multi_token_list.append((_ti, _tok, _tp))
                        break
                except Exception:
                    pass
    if not multi_token_list:
        print(f"{YELLOW}⚠ No token files found. Falling back to token.txt{RESET}")
        multi_token_list = [(0, load_user_token(), TOKEN_FILE)]
    else:
        print(f"{GREEN}✓ Loaded {len(multi_token_list)} token(s) for rotation{RESET}")
        for _tn, _tk, _tpath in multi_token_list:
            _preview = _tk[:20] + "..." if len(_tk) > 20 else _tk
            print(f"  {CYAN}token{_tn}.txt{RESET} → {GRAY}{_preview}{RESET}")
        _chk_slug = extract_slug_path(event_list[0][1]) or "sports/cricket"
        print(f"\n{BOLD_YELLOW}Checking all tokens...{RESET}")
        _pre_expired = []
        for _tn, _tk, _tpath in multi_token_list:
            _label = f"token{_tn}.txt"
            print(f"  Checking {_label}...", end=" ", flush=True)
            if check_token_valid(_tk, _chk_slug):
                print(f"{GREEN}✓ valid{RESET}")
            else:
                print(f"{RED}✗ EXPIRED!{RESET}")
                _pre_expired.append(_label)
        if _pre_expired:
            print(f"\n{RED}Expired: {', '.join(_pre_expired)}{RESET}")
            _cont = input(f"\n{BOLD_CYAN}Continue anyway? (y/n): {RESET}").strip().lower()
            if _cont != "y":
                return

    _token_cycle_idx = 0
    _expired_token_nums = set()

    # Push destination setup
    print(f"\n{BOLD_CYAN}Auto-push destination:{RESET}")
    print(f"  {BOLD_GREEN}1{RESET}) GitHub only")
    print(f"  {BOLD_YELLOW}2{RESET}) Cloudflare Workers only")
    print(f"  {BOLD_MAGENTA}3{RESET}) Both GitHub + Cloudflare")
    print(f"  {BOLD_WHITE}n{RESET}) No push (local only)")
    push_choice = input(f"{BOLD_CYAN}Choose (1/2/3/n): {RESET}").strip().lower()
    git_push_enabled = push_choice in ["1", "3"]
    use_cf = push_choice in ["2", "3"]
    cf_worker_url = None
    cf_api_token = None
    replace_m3u = True
    if use_cf:
        config = load_cf_config()
        config_valid = (config and config.get("worker_url", "").startswith("http") and config.get("api_token", ""))
        if config_valid:
            print(f"{GREEN}✓ Loaded Cloudflare config from cf_config.json{RESET}")
            print(f"{CYAN}  Worker URL: {config['worker_url']}{RESET}")
            use_existing = input(f"Use existing config? (y/n): ").strip().lower()
            if use_existing == 'y':
                cf_worker_url = config['worker_url']
                cf_api_token = config['api_token']
                print(f"{GREEN}✓ Using saved Worker URL and token{RESET}")
                _rep = input(f"{BOLD_CYAN}Replace Your M3U File? (y/n): {RESET}").strip().lower()
                replace_m3u = (_rep == 'y')
                if replace_m3u:
                    print(f"{YELLOW}  → Replace mode: full rewrite each cycle{RESET}")
                else:
                    print(f"{GREEN}  → Append mode: existing channels kept{RESET}")
            else:
                cf_worker_url = input("Enter Cloudflare Worker URL (https://...): ").strip()
                cf_api_token = input("Enter API Bearer Token: ").strip()
                save_cf_config(cf_worker_url, cf_api_token)
        else:
            if config and not config_valid:
                print(f"{YELLOW}⚠ Saved config invalid. Re-entering.{RESET}")
            cf_worker_url = input("Enter Cloudflare Worker URL (https://...): ").strip()
            cf_api_token = input("Enter API Bearer Token: ").strip()
            save_cf_config(cf_worker_url, cf_api_token)
        if not cf_worker_url or not cf_worker_url.startswith("http"):
            print(f"{RED}✗ Invalid Worker URL! Disabling CF push.{RESET}")
            use_cf = False
        elif not cf_api_token:
            print(f"{RED}✗ Empty API token! Disabling CF push.{RESET}")
            use_cf = False
        else:
            print(f"{GREEN}✓ Cloudflare Workers configured{RESET}")
            print(f"{CYAN}  URL: {cf_worker_url}{RESET}")
    if git_push_enabled and not use_cf:
        _rep = input(f"{BOLD_CYAN}Replace Your M3U File? (y/n): {RESET}").strip().lower()
        replace_m3u = (_rep == 'y')
        if replace_m3u:
            print(f"{YELLOW}  → Replace mode: full rewrite each cycle{RESET}")
        else:
            print(f"{GREEN}  → Append mode{RESET}")

    # Entry fetcher per event URL — quality numbers match the multi-event menu
    def _get_entries_for_url(q, evt_url):
        sp = extract_slug_path(evt_url)
        if not sp:
            return []
        if q == "1":
            # H.265 4K DV,HDR,SDR ADSFREE — hdntl 30-min embed
            _dv_entries = [(lbl, su, False) for _, lbl, su in collect_dv_hdr_sdr_entries(sp, "h265", "ssai")]
            if not _dv_entries:
                return []
            _all_raw_q1 = {lbl: su for lbl, su, _ in _dv_entries}
            _embedded_q1 = {}
            with ThreadPoolExecutor(max_workers=len(_all_raw_q1) or 1) as _emb_ex:
                _emb_futs = {_emb_ex.submit(_embed_hdntl_in_url, _u): _l for _l, _u in _all_raw_q1.items()}
                for _emb_f in as_completed(_emb_futs):
                    _l = _emb_futs[_emb_f]
                    try:
                        _embedded_q1[_l] = _emb_f.result()
                    except Exception:
                        _embedded_q1[_l] = _all_raw_q1[_l]
            return [(_l, _embedded_q1.get(_l, _su), False) for _l, _su, _ in _dv_entries]
        elif q == "2":
            # H.265 FHD DV,HDR,SDR + 30-min hdntl cookie embedded
            _fhd_ents2 = [(lbl, su, False) for _, lbl, su in collect_fhd_dv_hdr_sdr_entries(sp, "h265", "ssai")]
            if not _fhd_ents2:
                return []
            _raw_fhd2 = {lbl: su for lbl, su, _ in _fhd_ents2}
            _emb_fhd2 = {}
            with ThreadPoolExecutor(max_workers=len(_raw_fhd2) or 1) as _ex_fhd2:
                _futs_fhd2 = {_ex_fhd2.submit(_embed_hdntl_in_url, _u): _l for _l, _u in _raw_fhd2.items()}
                for _f_fhd2 in as_completed(_futs_fhd2):
                    _l2 = _futs_fhd2[_f_fhd2]
                    try:
                        _emb_fhd2[_l2] = _f_fhd2.result()
                    except Exception:
                        _emb_fhd2[_l2] = _raw_fhd2[_l2]
            return [(_l, _emb_fhd2.get(_l, _su), False) for _l, _su, _ in _fhd_ents2]
        elif q == "3":
            # H.265 AUTO DV,HDR,SDR ADSFREE + 30-min hdntl cookie embedded
            _auto_ents_q3m = list(collect_auto_dv_hdr_sdr_entries(sp))
            if not _auto_ents_q3m:
                return []
            _raw_q3m = {lbl: su for _, lbl, su in _auto_ents_q3m}
            _emb_q3m = {}
            with ThreadPoolExecutor(max_workers=len(_raw_q3m) or 1) as _ex_q3m:
                _futs_q3m = {_ex_q3m.submit(_embed_hdntl_in_url, _u): _l for _l, _u in _raw_q3m.items()}
                for _f_q3m in as_completed(_futs_q3m):
                    _l_q3m = _futs_q3m[_f_q3m]
                    try:
                        _emb_q3m[_l_q3m] = _f_q3m.result()
                    except Exception:
                        _emb_q3m[_l_q3m] = _raw_q3m[_l_q3m]
            return [(lbl, _emb_q3m.get(lbl, su), False) for _, lbl, su in _auto_ents_q3m]
        elif q == "6":
            # H.264 4K DV,HDR,SDR
            return [(lbl, su, False) for _, lbl, su in collect_dv_hdr_sdr_entries(sp, "h264", "non_ssai")]
        elif q == "7":
            # H.265 4K DV,HDR,SDR
            return [(lbl, su, False) for _, lbl, su in collect_dv_hdr_sdr_entries(sp, "h265", "non_ssai")]
        elif q == "8":
            # H.264 FHD DV,HDR,SDR
            return [(lbl, su, False) for _, lbl, su in collect_fhd_dv_hdr_sdr_entries(sp, "h264", "non_ssai")]
        elif q == "9":
            # H.265 FHD DV,HDR,SDR
            return [(lbl, su, False) for _, lbl, su in collect_fhd_dv_hdr_sdr_entries(sp, "h265", "non_ssai")]
        elif q in ["4", "5"]:
            # JHS HD (4) / JHS 4K (5)
            _raw = []
            _lk = __import__("threading").Lock()
            def _fe(lc, ln):
                try:
                    res = fetch_lang_stream(lc, ln, sp, evt_url, q)
                    if not res:
                        return
                    su = res["stream"]
                    is_hdr = res.get("is_hdr", False)
                    with _lk:
                        _raw.append((res["lang_name"], su, is_hdr))
                except Exception:
                    pass
            with ThreadPoolExecutor(max_workers=2) as _ex:
                _futs = [_ex.submit(_fe, lc, ln) for lc, ln in UNIQUE_LANGUAGES.items()]
                for _f in as_completed(_futs, timeout=120):
                    try: _f.result()
                    except: pass
            _seen = set()
            _out = []
            for _item in _raw:
                _b = _item[1].split("?")[0]
                if _b not in _seen:
                    _seen.add(_b)
                    _out.append(_item)
            return _out
        elif q == "10":
            # ADS-FREE 4K TattiJio & Chortel
            _pri_entries = []
            try:
                _pri_entries = list(get_primary_4k_24h_entries(evt_url))
            except Exception:
                pass
            return _pri_entries
        elif q == "17":
            # FALLBACK 24-HOURS LINK
            return get_fallback_24h_entries(evt_url)
        elif q == "18":
            # PRIMARY 24-HOURS LINK
            return get_primary_24h_entries(evt_url)
        elif q == "19":
            # FALLBACK 24-HOURS TattiJio & Chortel users
            return get_fallback_24h_entries(evt_url)
        elif q == "20":
            # PRIMARY 24-HOURS TattiJio & Chortel users
            return get_primary_24h_entries(evt_url)
        elif q == "21":
            # FALLBACK 4K 24-HOURS LINK
            return get_fallback_4k_24h_entries(evt_url)
        elif q == "22":
            # PRIMARY 4K 24-HOURS LINK
            return get_primary_4k_24h_entries(evt_url)
        return []

    # ── MAIN UPDATE LOOP ──────────────────────────────────────────────────────
    while True:
        try:
            _working_tokens = [t for t in multi_token_list if t[0] not in _expired_token_nums]
            if not _working_tokens:
                print(f"\n{BOLD_RED}ALL TOKENS EXPIRED! Auto-update stopped.{RESET}")
                _ACTIVE_TOKEN_OVERRIDE = None
                return

            _tok_entry = _working_tokens[_token_cycle_idx % len(_working_tokens)]
            _tok_num, _tok_str, _tok_path = _tok_entry
            _tok_label = f"token{_tok_num}.txt" if _tok_num > 0 else "token.txt"

            _chk_sp = extract_slug_path(event_list[0][1]) or "sports/cricket"
            print(f"\n{BOLD_YELLOW}[{datetime.now().strftime('%H:%M:%S')}] Updating M3U...{RESET} {CYAN}(Using: {_tok_label}){RESET}")
            print(f"{GRAY}  Validating token...{RESET}", end="", flush=True)
            if not check_token_valid(_tok_str, _chk_sp):
                print(f"\r{RED}  ✗ {_tok_label} is EXPIRED! — skipping, trying next token...{RESET}                ")
                _expired_token_nums.add(_tok_num)
                _exp_names_cur = [f"token{n}.txt" for n in sorted(_expired_token_nums) if n > 0]
                print(f"{RED}  Expired: {', '.join(_exp_names_cur)}{RESET}")
                continue
            else:
                print(f"\r{GREEN}  ✓ {_tok_label} is valid{RESET}                  ")
            _token_cycle_idx += 1

            _ACTIVE_TOKEN_OVERRIDE = _tok_str
            _cycle_start = time.time()

            # Build combined M3U for all events — fetch ALL events in parallel
            all_lines = [
                "#EXTM3U",
                f"# Multi-Event Playlist ({len(event_list)} events)",
                f"# Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
                "",
            ]
            total_entries = 0

            _QL_MAP = {
                "1":"H265-DV-HDR-SDR-ADSFREE","2":"H265-FHD-DV-HDR-SDR",
                "3":"H265-AUTO-DV-HDR-SDR-ADSFREE","4":"JHS-FHD","5":"JHS-4K",
                "6":"H264-4K-DV-HDR-SDR","7":"H265-4K-DV-HDR-SDR",
                "8":"H264-FHD-DV-HDR-SDR","9":"H265-FHD-DV-HDR-SDR",
                "10":"ADSFREE-4K-TATTI",
                "17":"FALLBACK-24H","18":"PRIMARY-24H",
                "19":"FALLBACK-24H-JIO","20":"PRIMARY-24H-JIO",
                "21":"FALLBACK-4K-24H","22":"PRIMARY-4K-24H",
            }

            def _fetch_one_event(evt_title, evt_url):
                """Fetch all stream entries for one event (parallel-safe)."""
                _logo_e = logos[evt_url]
                if len(quality_list) > 1:
                    # Fetch each quality in parallel too
                    _q_results: dict = {}
                    with ThreadPoolExecutor(max_workers=len(quality_list)) as _qex:
                        _qfuts = {_qex.submit(_get_entries_for_url, _q, evt_url): _q
                                  for _q in quality_list}
                        for _qf in as_completed(_qfuts):
                            _qq = _qfuts[_qf]
                            try:
                                _q_results[_qq] = _qf.result()
                            except Exception:
                                _q_results[_qq] = []
                    _entries = []
                    _seen_bases: set = set()
                    for _q in quality_list:          # preserve quality order
                        _q_tag = _QL_MAP.get(_q, f"Q{_q}")
                        for _lang, _su, _hdr in _q_results.get(_q, []):
                            _base = _su.split("?")[0]
                            if _base not in _seen_bases:
                                _seen_bases.add(_base)
                                _entries.append((f"{_lang} [{_q_tag}]", _su, _hdr))
                else:
                    _entries = _get_entries_for_url(quality, evt_url)
                return evt_title, evt_url, _logo_e, _entries

            # ── Parallel fetch: all events at once ────────────────────────────
            _n_evt = len(event_list)
            _parallel_workers = min(_n_evt, 8)   # cap at 8 to avoid hammering API
            _ordered_results: dict = {}           # idx → result tuple
            print(f"{CYAN}  Fetching {_n_evt} event(s) in parallel...{RESET}")
            with ThreadPoolExecutor(max_workers=_parallel_workers) as _evpool:
                _ev_futs = {
                    _evpool.submit(_fetch_one_event, t, u): i
                    for i, (t, u) in enumerate(event_list)
                }
                for _ef in as_completed(_ev_futs):
                    _eidx = _ev_futs[_ef]
                    _etitle = event_list[_eidx][0]
                    try:
                        _ordered_results[_eidx] = _ef.result()
                        _cnt = len(_ordered_results[_eidx][3])
                        _status = f"{GREEN}✓ {_cnt} stream(s){RESET}" if _cnt else f"{YELLOW}⚠ no streams{RESET}"
                        print(f"  [{_eidx+1}/{_n_evt}] {_etitle} — {_status}")
                    except Exception as _ee:
                        print(f"  [{_eidx+1}/{_n_evt}] {_etitle} — {RED}error: {_ee}{RESET}")
                        _ordered_results[_eidx] = (_etitle, event_list[_eidx][1], "", [])

            # Assemble M3U in original event order
            for _eidx in range(_n_evt):
                evt_title, evt_url, _logo, _evt_entries = _ordered_results.get(
                    _eidx, (event_list[_eidx][0], event_list[_eidx][1], "", []))
                _group = evt_title
                if not _evt_entries:
                    continue
                for _lang, _su, _hdr in _evt_entries:
                    _hdr_tag = " HDR" if _hdr else ""
                    _ch_name = f"{_lang}{_hdr_tag}"
                    all_lines.append(f'#EXTINF:-1 tvg-name="{_ch_name}" tvg-logo="{_logo}" group-title="{_group}", {_ch_name}')
                    all_lines.append('#EXTHTTP:{"Origin":"https://www.hotstar.com","Referer":"https://www.hotstar.com/"}')
                    all_lines.append('#EXTVLCOPT:http-extra-headers=Origin: https://www.hotstar.com')
                    all_lines.append('#EXTVLCOPT:http-referrer=https://www.hotstar.com/')
                    all_lines.append(_su)
                    all_lines.append("")
                    total_entries += 1

            if total_entries == 0:
                print(f"{YELLOW}  ⚠ No streams found for any event this cycle.{RESET}")
            else:
                _m3u_text = "\n".join(all_lines)
                try:
                    with open(filename, "w", encoding="utf-8") as _fw:
                        _fw.write(_m3u_text)
                    print(f"{GREEN}✓ M3U saved: {filename} ({total_entries} entries across {len(event_list)} events){RESET}")
                except Exception as _we:
                    print(f"{RED}Failed to write M3U: {_we}{RESET}")
                if git_push_enabled:
                    git_push_m3u(filename, f"Auto update multi {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
                if use_cf and cf_worker_url and cf_api_token:
                    push_to_cloudflare(filename, cf_worker_url, cf_api_token)

            _elapsed = int(time.time() - _cycle_start)
            _wait_sec = max(5, interval * 60 - _elapsed)
            _next_hms = datetime.fromtimestamp(time.time() + _wait_sec).strftime("%H:%M:%S")
            print(f"Next update at {_next_hms} — waiting {_wait_sec // 60}m {_wait_sec % 60}s (took {_elapsed}s update)... (Ctrl+C to stop)")
            time.sleep(_wait_sec)

        except KeyboardInterrupt:
            print(f"\n{BOLD_YELLOW}Auto-update stopped by user.{RESET}")
            _ACTIVE_TOKEN_OVERRIDE = None
            return
        except Exception as _ce:
            print(f"{RED}Cycle error: {_ce}{RESET}")
            time.sleep(30)


# ===================== AUTO-UPDATE MODE =====================
def auto_update_mode(input_url: str):
    print(f"{BOLD_GREEN}=== AUTO-UPDATE MODE ==={RESET}")
    url = input_url
    print(f"{CYAN}Fetching logo image...{RESET}")
    logo_url = extract_logo_from_url(url)
    if logo_url:
        print(f"{GREEN}✓ Logo found: {logo_url}{RESET}")
    else:
        print(f"{YELLOW}⚠ No logo found, will create M3U without tvg-logo.{RESET}")
    print(f"{BOLD_YELLOW}Available qualities:{RESET}")
    print(f"{BOLD_GREEN}{{1}} H.265 4K DV,HDR,SDR ADSFREE{RESET}")
    print(f"{BOLD_GREEN}{{2}} H.265 FHD DV,HDR,SDR{RESET}")
    print(f"{BOLD_GREEN}{{3}} H.265 AUTO DV,HDR,SDR ADSFREE{RESET}")
    print(f"{BOLD_YELLOW}{{4}} ADS-FREE JHS HD{RESET}")
    print(f"{BOLD_MAGENTA}{{5}} JHS 4K{RESET}")
    print(f"{BOLD_WHITE}{{6}} H.264 4K DV,HDR,SDR{RESET}")
    print(f"{BOLD_WHITE}{{7}} H.265 4K DV,HDR,SDR{RESET}")
    print(f"{BOLD_WHITE}{{8}} H.264 FHD DV,HDR,SDR{RESET}")
    print(f"{BOLD_WHITE}{{9}} H.265 FHD DV,HDR,SDR{RESET}")
    print(f"{BOLD_GREEN}{{10}} ADS-FREE 4K TattiJio & Chortel users{RESET}")
    print(f"{BOLD_RED}{{11}} DRM MPD + CLEARKEY / PSSH{RESET}")
    print(f"{BOLD_YELLOW}{{12}} NORMAL HD (720p) ALL LANGUAGES{RESET}")
    print(f"{BOLD_GREEN}{{13}} DRM-TV 24-HOURS LINK{RESET}")
    print(f"{BOLD_YELLOW}{{14}} JHS ALL CHANNELS{RESET}")
    print(f"{BOLD_GREEN}{{17}} FALLBACK 24-HOURS LINK{RESET}")
    print(f"{BOLD_BLUE}{{18}} PRIMARY 24-HOURS LINK{RESET}")
    print(f"{BOLD_GREEN}{{19}} FALLBACK 24-HOURS TattiJio & Chortel users{RESET}")
    print(f"{BOLD_BLUE}{{20}} PRIMARY 24-HOURS TattiJio & Chortel users{RESET}")
    print(f"{BOLD_YELLOW}{{21}} FALLBACK 4K 24-HOURS LINK{RESET}")
    print(f"{BOLD_MAGENTA}{{22}} PRIMARY 4K 24-HOURS LINK{RESET}")
    quality_raw = input(f"{BOLD_CYAN}Choose quality (1-10 or multiple like 1,2 or 1.2): {RESET}").strip()
    # Support comma or dot separated multiple choices e.g. "1,2" or "1.2"
    quality_list = [q.strip() for q in quality_raw.replace(".", ",").split(",") if q.strip() in ["1","2","3","4","5","6","7","8","9","10","11","12","13","14","17","18","19","20","21","22"]]
    if not quality_list:
        print(f"{RED}Invalid choice. Defaulting to 2.{RESET}")
        quality_list = ["2"]
    quality = quality_list[0]  # primary quality (used for single-quality paths)
    if len(quality_list) > 1:
        print(f"{GREEN}✓ Multi-quality mode: {', '.join(quality_list)}{RESET}")
    interval = input(f"Update interval in minutes (default 25): ").strip()
    interval = int(interval) if interval.isdigit() else 25
    filename = input(f"M3U filename (default: hotstar_auto.m3u): ").strip()
    if not filename:
        filename = "hotstar_auto.m3u"

    # ── MULTI-TOKEN ROTATION SETUP ────────────────────────────────────────────
    token_count_raw = input(f"{BOLD_CYAN}How Many Token Use Per Request Cycles (default 2): {RESET}").strip()
    if token_count_raw.isdigit() and 1 <= int(token_count_raw) <= 99:
        token_count = int(token_count_raw)
    else:
        token_count = 2

    _home = os.path.expanduser("~")
    multi_token_list = []  # list of (token_number, token_str, file_path)
    for _ti in range(1, token_count + 1):
        _paths_to_try = [
            os.path.join(_home, f"token{_ti}.txt"),
            f"token{_ti}.txt",
        ]
        for _tp in _paths_to_try:
            if os.path.isfile(_tp):
                try:
                    with open(_tp, "r", encoding="utf-8") as _tf:
                        _tok = _tf.read().strip()
                    if _tok:
                        multi_token_list.append((_ti, _tok, _tp))
                        break
                except Exception:
                    pass

    if not multi_token_list:
        print(f"{YELLOW}⚠ No token files found (token1.txt–token{token_count}.txt). Falling back to token.txt{RESET}")
        _fallback_tok = load_user_token()
        multi_token_list = [(0, _fallback_tok, TOKEN_FILE)]
    else:
        print(f"{GREEN}✓ Loaded {len(multi_token_list)} token(s) for rotation{RESET}")
        for _tn, _tk, _tpath in multi_token_list:
            _preview = _tk[:20] + "..." if len(_tk) > 20 else _tk
            print(f"  {CYAN}token{_tn}.txt{RESET} → {GRAY}{_preview}{RESET}")

        # ── Upfront token validity check ─────────────────────────────────────
        _chk_slug = extract_slug_path(url) or "sports/cricket"
        print(f"\n{BOLD_YELLOW}Checking all tokens...{RESET}")
        _pre_expired = []
        for _tn, _tk, _tpath in multi_token_list:
            _label = f"token{_tn}.txt"
            print(f"  Checking {_label}...", end=" ", flush=True)
            if check_token_valid(_tk, _chk_slug):
                print(f"{GREEN}✓ valid{RESET}")
            else:
                print(f"{RED}✗ EXPIRED!{RESET}")
                _pre_expired.append(_label)

        if _pre_expired:
            print(f"\n{RED}Expired token files:{RESET}")
            for _el in _pre_expired:
                print(f"  {RED}✗ {_el}{RESET}")
            print(f"\n{YELLOW}↑ These tokens are expired — add fresh tokens in these files{RESET}")
            _cont = input(f"\n{BOLD_CYAN}Continue auto-update anyway? (y/n): {RESET}").strip().lower()
            if _cont != "y":
                return
        # ───────────────────────────────────────  �─────────────────────────────

    _token_cycle_idx = 0
    _expired_token_nums = set()  # set of token numbers confirmed expired
    _token_empty_cycles = {}     # token_num → consecutive empty-cycle count
    # ─────────────────────────────────────────────────────────────────────────

    print(f"\n{BOLD_CYAN}Auto-push destination:{RESET}")
    print(f"  {BOLD_GREEN}1{RESET}) GitHub only")
    print(f"  {BOLD_YELLOW}2{RESET}) Cloudflare Workers only")
    print(f"  {BOLD_MAGENTA}3{RESET}) Both GitHub + Cloudflare")
    print(f"  {BOLD_WHITE}n{RESET}) No push (local only)")
    push_choice = input(f"{BOLD_CYAN}Choose (1/2/3/n): {RESET}").strip().lower()
    git_push_enabled = push_choice in ["1", "3"]
    use_cf = push_choice in ["2", "3"]
    cf_worker_url = None
    cf_api_token = None
    replace_m3u = True  # default: replace
    if use_cf:
        config = load_cf_config()
        # Validate saved config - worker_url must start with http and token must exist
        config_valid = (
            config and
            config.get("worker_url", "").startswith("http") and
            config.get("api_token", "")
        )
        if config_valid:
            print(f"{GREEN}✓ Loaded Cloudflare config from {CF_CONFIG_FILE}{RESET}")
            print(f"{CYAN}  Worker URL: {config['worker_url']}{RESET}")
            use_existing = input(f"Use existing config? (y/n): ").strip().lower()
            if use_existing == 'y':
                cf_worker_url = config['worker_url']
                cf_api_token = config['api_token']
                print(f"{GREEN}✓ Using saved Worker URL and token{RESET}")
                _rep = input(f"{BOLD_CYAN}Replace Your M3U File? (y/n): {RESET}").strip().lower()
                replace_m3u = (_rep == 'y')
                if replace_m3u:
                    print(f"{YELLOW}  → Replace mode: full rewrite each cycle{RESET}")
                else:
                    print(f"{GREEN}  → Append mode: existing channels kept, tokens refreshed{RESET}")
            else:
                cf_worker_url = input("Enter Cloudflare Worker URL (https://...): ").strip()
                cf_api_token = input("Enter API Bearer Token: ").strip()
                save_cf_config(cf_worker_url, cf_api_token)
        else:
            if config and not config_valid:
                print(f"{YELLOW}⚠ Saved config is invalid (bad URL or missing token). Re-entering.{RESET}")
            cf_worker_url = input("Enter Cloudflare Worker URL (https://...): ").strip()
            cf_api_token = input("Enter API Bearer Token: ").strip()
            save_cf_config(cf_worker_url, cf_api_token)
        # Final validation
        if not cf_worker_url or not cf_worker_url.startswith("http"):
            print(f"{RED}✗ Invalid Worker URL! Must start with https://. Disabling CF push.{RESET}")
            use_cf = False
        elif not cf_api_token:
            print(f"{RED}✗ API token is empty! Disabling CF push.{RESET}")
            use_cf = False
        else:
            print(f"{GREEN}✓ Cloudflare Workers configured{RESET}")
            print(f"{CYAN}  URL: {cf_worker_url}{RESET}")
    if git_push_enabled:
        if not use_cf:
            _rep = input(f"{BOLD_CYAN}Replace Your M3U File? (y/n): {RESET}").strip().lower()
            replace_m3u = (_rep == 'y')
            if replace_m3u:
                print(f"{YELLOW}  → Replace mode: full rewrite each cycle{RESET}")
            else:
                print(f"{GREEN}  → Append mode: existing channels kept, tokens refreshed{RESET}")
        print(f"{GREEN}✓ GitHub auto-push enabled{RESET}")
    if not git_push_enabled and not use_cf:
        print(f"{YELLOW}No push destination. M3U will be saved locally only.{RESET}")
    slug_path = extract_slug_path(url)
    if not slug_path:
        print(f"{RED}Invalid URL!{RESET}")
        return

    def add_hdr_sdr_variants(entries):
        """For ALL languages: if HDR stream found, also add SDR variant."""
        final = []
        seen_urls = set()
        for lang, url, is_hdr in entries:
            if url not in seen_urls:
                seen_urls.add(url)
                final.append((lang, url, is_hdr))
            # Add SDR variant for ALL languages that have HDR
            if is_hdr:
                sdr_url = url.replace("hdr", "sdr").replace("HDR", "sdr").replace("Hdr", "sdr")
                if sdr_url != url and sdr_url not in seen_urls:
                    seen_urls.add(sdr_url)
                    final.append((f"{lang} SDR", sdr_url, False))
        return final

    def get_entries(quality, url, slug_path):
        def collect_option9_entries(url):
            _asset_id = parse_asset_id_4kads(url)
            _slug_path = extract_slug_path(url) or ""
            if not _asset_id:
                return []
            _lang_groups = [
                ("eng", ["eng"], "ENGLISH"),
                ("hin", ["hin", "hi", "hd"], "HINDI"),
                ("mar", ["mar", "mr", "ma"], "MARATHI"),
                ("guj", ["guj", "gu"], "GUJARATI"),
                ("bih", ["bih", "bho", "bh"], "BHOJPURI"),
                ("pan", ["pan", "pun", "pa", "pu"], "PUNJABI"),
                ("har", ["har", "hv", "ha"], "HARYANVI"),
                ("tam", ["tam", "ta"], "TAMIL"),
                ("tel", ["tel", "te"], "TELUGU"),
                ("kan", ["kan", "kn"], "KANNADA"),
                ("mal", ["mal", "ml"], "MALAYALAM"),
                ("ben", ["ben", "bn"], "BENGALI"),
            ]
            _collected = []
            _seen_langs = set()
            _lock = __import__("threading").Lock()

            def _fetch_one(primary, codes, lang_name):
                for lang_code in codes:
                    for attempt in range(3):
                        try:
                            api_url = build_api_url_4kads(_asset_id, lang_code, slug_path=_slug_path)
                            pc = fetch_player_config_4kads(api_url)
                            streams = extract_all_streams_4kads(pc)
                            if not streams:
                                continue
                            candidates = []
                            for s in streams:
                                orig = str(s.get("content_url", ""))
                                if not orig or str(s.get("type", "")).lower() != "primary":
                                    continue
                                for v in generate_cdn_variants_4kads(orig):
                                    candidates.append((v, s))
                            if not candidates:
                                continue
                            lang_candidates = []
                            for raw_url, s in candidates:
                                path_parts = set(raw_url.split("?")[0].replace("https://","").replace("http://","").split("/"))
                                if lang_code in path_parts:
                                    lang_candidates.append((raw_url, s))
                            if not lang_candidates:
                                lang_candidates = candidates
                            for raw_url, s in lang_candidates:
                                try:
                                    if not is_working_url_4kads(raw_url):
                                        continue
                                    token = get_hdntl_token_4kads(raw_url)
                                    final_url = append_hdntl_to_url_4kads(raw_url, token)
                                    is_hdr = "hdr" in raw_url.lower()
                                    label = f"{lang_name} 4K ADSFREE"
                                    with _lock:
                                        if lang_name not in _seen_langs:
                                            _seen_langs.add(lang_name)
                                            _collected.append((label, final_url, is_hdr))
                                    return
                                except Exception:
                                    continue
                        except Exception:
                            if attempt < 2:
                                time.sleep(1)
                            continue

            _LANG_ORDER = [
                "HINDI","ENGLISH","TELUGU","TAMIL","KANNADA","MALAYALAM",
                "BENGALI","MARATHI","GUJARATI","PUNJABI","BHOJPURI","HARYANVI",
            ]

            with ThreadPoolExecutor(max_workers=5) as pool:
                futs = [pool.submit(_fetch_one, p, codes, name) for p, codes, name in _lang_groups]
                for f in as_completed(futs, timeout=300):
                    try:
                        f.result()
                    except Exception:
                        pass
            _collected.sort(key=lambda x: _LANG_ORDER.index(x[0].split()[0]) if x[0].split()[0] in _LANG_ORDER else 99)
            return _collected

        if quality == "1":
            # H.265 4K DV,HDR,SDR ADSFREE + 30-min hdntl cookie embedded in URL
            _dv_entries_q1 = [(lbl, su, False) for _, lbl, su in collect_dv_hdr_sdr_entries(slug_path, "h265", "ssai")]
            if not _dv_entries_q1:
                return []
            _raw_q1 = {lbl: su for lbl, su, _ in _dv_entries_q1}
            _emb_q1 = {}
            with ThreadPoolExecutor(max_workers=len(_raw_q1) or 1) as _ex_q1:
                _futs_q1 = {_ex_q1.submit(_embed_hdntl_in_url, _u): _l for _l, _u in _raw_q1.items()}
                for _f_q1 in as_completed(_futs_q1):
                    _l_q1 = _futs_q1[_f_q1]
                    try:
                        _emb_q1[_l_q1] = _f_q1.result()
                    except Exception:
                        _emb_q1[_l_q1] = _raw_q1[_l_q1]
            return [(_l, _emb_q1.get(_l, _su), False) for _l, _su, _ in _dv_entries_q1]
        elif quality == "2":
            # H.265 FHD DV,HDR,SDR + 30-min hdntl cookie embedded in URL
            _dv_ents_q2 = [(lbl, su, False) for _, lbl, su in collect_fhd_dv_hdr_sdr_entries(slug_path, "h265", "ssai")]
            if not _dv_ents_q2:
                return []
            _raw_q2 = {lbl: su for lbl, su, _ in _dv_ents_q2}
            _emb_q2 = {}
            with ThreadPoolExecutor(max_workers=len(_raw_q2) or 1) as _ex_q2:
                _futs_q2 = {_ex_q2.submit(_embed_hdntl_in_url, _u): _l for _l, _u in _raw_q2.items()}
                for _f_q2 in as_completed(_futs_q2):
                    _l_q2 = _futs_q2[_f_q2]
                    try:
                        _emb_q2[_l_q2] = _f_q2.result()
                    except Exception:
                        _emb_q2[_l_q2] = _raw_q2[_l_q2]
            return [(_l, _emb_q2.get(_l, _su), False) for _l, _su, _ in _dv_ents_q2]
        elif quality == "3":
            # H.265 AUTO DV,HDR,SDR ADSFREE + 30-min hdntl cookie embedded
            _auto_ents_q3 = list(collect_auto_dv_hdr_sdr_entries(slug_path))
            if not _auto_ents_q3:
                return []
            _raw_q3 = {lbl: su for _, lbl, su in _auto_ents_q3}
            _emb_q3 = {}
            with ThreadPoolExecutor(max_workers=len(_raw_q3) or 1) as _ex_q3:
                _futs_q3 = {_ex_q3.submit(_embed_hdntl_in_url, _u): _l for _l, _u in _raw_q3.items()}
                for _f_q3 in as_completed(_futs_q3):
                    _l_q3 = _futs_q3[_f_q3]
                    try:
                        _emb_q3[_l_q3] = _f_q3.result()
                    except Exception:
                        _emb_q3[_l_q3] = _raw_q3[_l_q3]
            return [(lbl, _emb_q3.get(lbl, su), False) for _, lbl, su in _auto_ents_q3]
        elif quality == "4":
            def collect_jhs_entries(url, slug_path):
                LANG_CODES = [
                    ("eng","ENGLISH"), ("en","ENGLISH"),
                    ("hin","HINDI"), ("hi","HINDI"), ("hd","HINDI HD"),
                    ("mar","MARATHI"), ("mr","MARATHI"), ("ma","MARATHI"),
                    ("guj","GUJARATI"), ("gu","GUJARATI"),
                    ("bih","BHOJPURI"), ("bho","BHOJPURI"), ("bh","BHOJPURI"),
                    ("pan","PUNJABI"), ("pun","PUNJABI"), ("pa","PUNJABI"), ("pu","PUNJABI"),
                    ("har","HARYANVI"), ("hv","HARYANVI"), ("ha","HARYANVI"),
                    ("tam","TAMIL"), ("ta","TAMIL"),
                    ("tel","TELUGU"), ("te","TELUGU"),
                    ("kan","KANNADA"), ("kn","KANNADA"),
                    ("mal","MALAYALAM"), ("ml","MALAYALAM"),
                    ("ben","BENGALI"), ("bn","BENGALI"),
                    ("ori","ORIYA"), ("or","ORIYA"),
                ]
                _seen_names = set()
                _unique_codes = []
                for _code, _name in LANG_CODES:
                    if _name not in _seen_names:
                        _seen_names.add(_name)
                        _unique_codes.append((_code, _name))
                LANG_CODES = _unique_codes
                FALLBACKS = {
                    "eng":["en"], "hin":["hi","hd"], "mar":["mr","ma"],
                    "guj":["gu"], "bih":["bho","bh"], "pan":["pun","pa","pu"],
                    "har":["hv","ha"], "tam":["ta"], "tel":["te"],
                    "kan":["kn"], "mal":["ml"], "ben":["bn"], "ori":["or"],
                }
                is_live = extract_stream_type(url) == "LIVE TV"
                seen_lang = set()
                seen_url = set()
                res_list = []
                lock = __import__("threading").Lock()

                def fetch_jhs_lang(lang_code, lang_name):
                    all_codes = [lang_code] + FALLBACKS.get(lang_code, [])
                    for code in all_codes:
                        try:
                            api_url = build_jhs_api_url(slug_path, code, is_live=is_live)
                            req = request.Request(api_url, headers=build_jhs_headers_android())
                            with request.urlopen(req, timeout=10) as resp:
                                data = json.loads(resp.read().decode("utf-8"))
                            player_config = None
                            for sec in data.get("success",{}).get("page",{}).get("spaces",{}).values():
                                for w in sec.get("widget_wrappers",[]):
                                    d = w.get("widget",{}).get("data",{})
                                    if "player_config" in d:
                                        player_config = d["player_config"]; break
                                if player_config: break
                            if not player_config: continue
                            streams = extract_jhs_fallback_only(player_config)
                            for s in streams:
                                u = s.get("content_url")
                                if not u: continue
                                base_url = u.split("?")[0]
                                if is_live:
                                    tags = s.get("playback_tags","") or ""
                                    detected = ""
                                    for tag in tags.split(";"):
                                        if tag.startswith("language:"):
                                            detected = tag.split(":")[1].strip().lower(); break
                                    if detected and detected != code.lower(): continue
                                    display = LANGUAGES.get(detected, lang_name) if detected else lang_name
                                else:
                                    display = lang_name
                                    if extract_stream_type(url) not in ["MOVIE","TV SHOW"]:
                                        path_set = set(base_url.replace("https://","").split("/"))
                                        if not any(c in path_set for c in [lang_code]+FALLBACKS.get(lang_code,[])):
                                            continue
                                clean = u.split("?")[0] if extract_stream_type(url) in ["HIGHLIGHTS","CLIP"] else u
                                is_hdr = "hdr" in u.lower() or "hdr" in str(s.get("playback_tags","")).lower()
                                with lock:
                                    if display not in seen_lang and clean not in seen_url:
                                        seen_lang.add(display)
                                        seen_url.add(clean)
                                        res_list.append((display, clean, is_hdr))
                                return
                        except: continue

                with ThreadPoolExecutor(max_workers=2) as ex:  # RATE LIMIT: 6→2 (JHS quality 3)
                    futs = [ex.submit(fetch_jhs_lang, code, name) for code,name in LANG_CODES]
                    for f in as_completed(futs, timeout=90):
                        try: f.result()
                        except: pass
                order = [name for _,name in LANG_CODES]
                res_list.sort(key=lambda x: order.index(x[0]) if x[0] in order else 99)
                return res_list
            return add_hdr_sdr_variants(collect_jhs_entries(url, slug_path))
        elif quality == "5":
            def collect_jhs4k_entries(url, slug_path):
                LANG_CODES = [
                    ("eng","ENGLISH"), ("en","ENGLISH"),
                    ("hin","HINDI"), ("hi","HINDI"), ("hd","HINDI HD"),
                    ("mar","MARATHI"), ("mr","MARATHI"), ("ma","MARATHI"),
                    ("guj","GUJARATI"), ("gu","GUJARATI"),
                    ("bih","BHOJPURI"), ("bho","BHOJPURI"), ("bh","BHOJPURI"),
                    ("pan","PUNJABI"), ("pun","PUNJABI"), ("pa","PUNJABI"), ("pu","PUNJABI"),
                    ("har","HARYANVI"), ("hv","HARYANVI"), ("ha","HARYANVI"),
                    ("tam","TAMIL"), ("ta","TAMIL"),
                    ("tel","TELUGU"), ("te","TELUGU"),
                    ("kan","KANNADA"), ("kn","KANNADA"),
                    ("mal","MALAYALAM"), ("ml","MALAYALAM"),
                    ("ben","BENGALI"), ("bn","BENGALI"),
                    ("ori","ORIYA"), ("or","ORIYA"),
                ]
                _seen_names = set()
                _unique_codes = []
                for _code, _name in LANG_CODES:
                    if _name not in _seen_names:
                        _seen_names.add(_name)
                        _unique_codes.append((_code, _name))
                LANG_CODES = _unique_codes
                FALLBACKS = {
                    "eng":["en"], "hin":["hi","hd"], "mar":["mr","ma"],
                    "guj":["gu"], "bih":["bho","bh"], "pan":["pun","pa","pu"],
                    "har":["hv","ha"], "tam":["ta"], "tel":["te"],
                    "kan":["kn"], "mal":["ml"], "ben":["bn"], "ori":["or"],
                }
                is_live = extract_stream_type(url) == "LIVE TV"
                seen_lang = set()
                seen_url = set()
                results = {}
                lock = __import__("threading").Lock()

                def fetch_jhs4k_single(lang_code, lang_name):
                    all_codes = [lang_code] + FALLBACKS.get(lang_code, [])
                    for code in all_codes:
                        try:
                            api_url = build_jhs_4k_api_url(slug_path, code, is_live=is_live)
                            req = request.Request(api_url, headers=build_jhs_headers())
                            with request.urlopen(req, timeout=5) as resp:
                                data = json.loads(resp.read().decode("utf-8"))
                            player_config = None
                            for sec in data.get("success",{}).get("page",{}).get("spaces",{}).values():
                                for w in sec.get("widget_wrappers",[]):
                                    d = w.get("widget",{}).get("data",{})
                                    if "player_config" in d:
                                        player_config = d["player_config"]; break
                                if player_config: break
                            if not player_config: continue
                            streams_4k = extract_4k_streams(player_config)
                            if streams_4k:
                                u = streams_4k[0]["url"]
                                clean = u if extract_stream_type(url) not in ["HIGHLIGHTS","CLIP"] else u.split("?")[0]
                                is_hdr = "hdr" in u.lower() or "hdr" in str(streams_4k[0].get("playback_tags","")).lower()
                                with lock:
                                    if lang_name not in seen_lang and clean not in seen_url:
                                        seen_lang.add(lang_name)
                                        seen_url.add(clean)
                                        results[lang_name] = (clean, is_hdr)
                                return
                            for s in extract_jhs_fallback_only(player_config):
                                u = s.get("content_url")
                                if not u: continue
                                base = u.split("?")[0]
                                if is_live:
                                    tags = s.get("playback_tags","") or ""
                                    detected = ""
                                    for tag in tags.split(";"):
                                        if tag.startswith("language:"):
                                            detected = tag.split(":")[1].strip().lower(); break
                                    if detected and detected != code.lower(): continue
                                    display = LANGUAGES.get(detected, lang_name) if detected else lang_name
                                else:
                                    display = lang_name
                                    if extract_stream_type(url) not in ["MOVIE","TV SHOW"]:
                                        path_set = set(base.replace("https://","").split("/"))
                                        if not any(c in path_set for c in [lang_code]+FALLBACKS.get(lang_code,[])):
                                            continue
                                clean = u.split("?")[0] if extract_stream_type(url) in ["HIGHLIGHTS","CLIP"] else u
                                is_hdr = "hdr" in u.lower() or "hdr" in str(s.get("playback_tags","")).lower()
                                with lock:
                                    if display not in seen_lang and clean not in seen_url:
                                        seen_lang.add(display)
                                        seen_url.add(clean)
                                        results[display] = (clean, is_hdr)
                                return
                        except: continue

                with ThreadPoolExecutor(max_workers=2) as ex:  # RATE LIMIT: 6→2 (JHS-4K quality 4)
                    futs = [ex.submit(fetch_jhs4k_single, code, name) for code,name in LANG_CODES]
                    for f in as_completed(futs, timeout=90):
                        try: f.result()
                        except: pass
                order = [name for _,name in LANG_CODES]
                entries = [(name, results[name][0], results[name][1]) for name in order if name in results]
                return entries
            return add_hdr_sdr_variants(collect_jhs4k_entries(url, slug_path))
        elif quality == "8":
            # H.264 FHD DV,HDR,SDR
            return [(lbl, su, False) for _, lbl, su in collect_fhd_dv_hdr_sdr_entries(slug_path, "h264", "non_ssai")]
        elif quality == "9":
            # H.265 FHD DV,HDR,SDR
            return [(lbl, su, False) for _, lbl, su in collect_fhd_dv_hdr_sdr_entries(slug_path, "h265", "non_ssai")]
        elif quality == "10":
            # ADS-FREE 4K TattiJio & Chortel — lite path + hdntl embed per URL (30-min token)
            asset_id = parse_asset_id_4kads(url)
            if not asset_id:
                return []
            _slug6 = extract_slug_path(url) or ""
            # HDR: English and Hindi only
            _hdr6 = {}
            _hdr_langs6 = {"1": LANG_MAP_4KADS["1"], "2": LANG_MAP_4KADS["2"]}
            with ThreadPoolExecutor(max_workers=2) as executor:
                futures = {
                    executor.submit(fetch_language_wrapper_4kads_lite, asset_id, lang_num, lang_codes, False, _slug6): (lang_num, lang_codes)
                    for lang_num, lang_codes in _hdr_langs6.items()
                }
                for future in as_completed(futures):
                    try:
                        lang_name, url_res = future.result()
                        if url_res:
                            _hdr6[lang_name] = url_res
                    except Exception:
                        pass
            # SDR: all languages
            _sdr6 = {}
            with ThreadPoolExecutor(max_workers=len(LANG_MAP_4KADS)) as executor:
                futures = {
                    executor.submit(fetch_language_wrapper_4kads_lite, asset_id, lang_num, lang_codes, True, _slug6): (lang_num, lang_codes)
                    for lang_num, lang_codes in LANG_MAP_4KADS.items()
                }
                for future in as_completed(futures):
                    try:
                        lang_name, url_res = future.result()
                        if url_res:
                            _sdr6[lang_name] = url_res
                    except Exception:
                        pass
            # Build combined raw dict — HDR under plain keys, SDR under "LANG SDR" keys for Eng/Hin
            _all_7_raw = {}
            for _ln, _lu in _hdr6.items():
                _all_7_raw[_ln] = _lu                    # "ENGLISH", "HINDI"  (HDR)
            for _ln, _lu in _sdr6.items():
                _lkey = f"{_ln} SDR" if _ln in ("ENGLISH", "HINDI") else _ln
                _all_7_raw[_lkey] = _lu                  # "ENGLISH SDR", "HINDI SDR", others plain
            # Embed hdntl (30-min token) per URL in parallel
            _embedded_7 = {}
            with ThreadPoolExecutor(max_workers=len(_all_7_raw) or 1) as executor:
                _ef7 = {executor.submit(_embed_hdntl_in_url, _u): _l for _l, _u in _all_7_raw.items()}
                for _f in as_completed(_ef7):
                    _l = _ef7[_f]
                    try:
                        _embedded_7[_l] = _f.result()
                    except Exception:
                        _embedded_7[_l] = _all_7_raw[_l]
            entries_6 = []
            # HDR: English and Hindi only
            for lang in ["ENGLISH", "HINDI"]:
                if lang in _embedded_7:
                    entries_6.append((lang, _embedded_7[lang], True))          # is_hdr=True → "ENGLISH HDR"
            # SDR: English SDR and Hindi SDR
            for lang in ["ENGLISH SDR", "HINDI SDR"]:
                if lang in _embedded_7:
                    entries_6.append((lang, _embedded_7[lang], False))         # "ENGLISH SDR"
            # SDR: all remaining languages
            for lang in LANG_ORDER_4KADS:
                if lang not in ("ENGLISH", "HINDI") and lang in _embedded_7:
                    entries_6.append((f"{lang} SDR", _embedded_7[lang], False))
            return entries_6
        elif quality == "11":
            def collect_option6_drm(url, slug_path):
                try:
                    drm_streams, global_license, global_keys, _ = fetch_drm_info_for_slug(slug_path)
                    if not drm_streams:
                        print(f"{YELLOW}  [DRM] No MPD streams found from API.{RESET}")
                        return []
                    key_str_global = ",".join(global_keys) if global_keys else global_license
                    result = []
                    seen_mpds = set()
                    ordered = sorted(drm_streams, key=lambda s: 0 if s["variant"] == "PRIMARY" else 1)
                    for stream in ordered:
                        mpd_url = stream["mpd_url"]
                        mpd_base = mpd_url.split("?")[0]
                        if mpd_base in seen_mpds:
                            continue
                        seen_mpds.add(mpd_base)
                        license_url = stream.get("license_url") or global_license
                        variant = stream["variant"]
                        avail_langs = extract_mpd_languages(mpd_url)
                        if not avail_langs:
                            avail_langs = [("unk", "STREAM")]
                        key_str = key_str_global
                        try:
                            mpd_info = fetch_mpd_pssh(mpd_url)
                            if mpd_info and mpd_info.get("key_ids") and license_url:
                                ck = try_clearkey_json(mpd_info["key_ids"], license_url)
                                if ck:
                                    key_str = ",".join(ck)
                                elif mpd_info.get("pssh"):
                                    wv = fetch_widevine_keys(mpd_info["pssh"], license_url)
                                    if wv and not any(l.startswith("❌") for l in wv):
                                        key_str = ",".join(wv)
                        except Exception:
                            pass
                        for _, lang_name in avail_langs:
                            result.append((lang_name, variant, mpd_url, license_url, key_str))
                    return result
                except Exception as e:
                    print(f"{YELLOW}  [DRM] collect error: {e}{RESET}")
                    return []
            drm_entries = collect_option6_drm(url, slug_path)
            if not drm_entries:
                print(f"{RED}No DRM streams found.{RESET}")
                return []
            title_m3u, _ = extract_match_title(url)
            group = title_m3u or "Cricket"
            logo = logo_url or ""
            lines = ["#EXTM3U", f"# Title: {group}", f"", f"# Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}", ""]
            for lang_name, variant, mpd_url, license_url, key_str in drm_entries:
                entry_title = f"{lang_name} [{variant}]"
                ott_url = build_ott_drm_url(mpd_url, key_str) if key_str else mpd_url
                lines.append(f'#EXTINF:-1 tvg-id="" tvg-logo="{logo}" group-title="{group}", {entry_title}')
                lines.append(ott_url)
                lines.append("")
            m3u_text = "\n".join(lines)
            total_entries = len([l for l in lines if l.startswith("#EXTINF")])
            try:
                with open(filename, "w", encoding="utf-8") as fw:
                    fw.write(m3u_text)
                print(f"{GREEN}✓ DRM M3U saved: {filename} ({total_entries} entries — PRIMARY + FALLBACK){RESET}")
            except Exception as e:
                print(f"{RED}Failed to write M3U: {e}{RESET}")
            if os.path.isfile(filename):
                if git_push_enabled:
                    git_push_m3u(filename, f"Auto update DRM {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
                if use_cf and cf_worker_url and cf_api_token:
                    push_to_cloudflare(filename, cf_worker_url, cf_api_token)
            return None
        elif quality == "13":
            def collect_option7_plain_entries(slug_path):
                try:
                    drm_streams, _, _, _ = fetch_drm_info_for_slug(slug_path)
                    if not drm_streams:
                        return []
                    result = []
                    seen_mpds = set()
                    ordered = sorted(drm_streams, key=lambda s: 0 if s["variant"] == "PRIMARY" else 1)
                    for stream in ordered:
                        mpd_url = stream["mpd_url"]
                        mpd_base = mpd_url.split("?")[0]
                        if mpd_base in seen_mpds:
                            continue
                        seen_mpds.add(mpd_base)
                        variant = stream["variant"]
                        avail_langs = extract_mpd_languages(mpd_url)
                        if not avail_langs:
                            avail_langs = [("unk", "STREAM")]
                        for _, lang_name in avail_langs:
                            result.append((f"{lang_name} {variant}", mpd_url, False))
                    return result
                except Exception as e:
                    print(f"{RED}Option 7 plain error: {e}{RESET}")
                    return []
            plain_entries = collect_option7_plain_entries(slug_path)
            if not plain_entries:
                print(f"{RED}No DRM streams found.{RESET}")
                return []
            title_p, _ = extract_match_title(url)
            group_p = title_p or "Cricket"
            logo_p = logo_url or ""
            lines_p = ["#EXTM3U", f"# Title: {group_p}", f"", f"# Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}", ""]
            for lang_name, mpd_url, _ in plain_entries:
                lines_p.append(f'#EXTINF:-1 tvg-id="" tvg-logo="{logo_p}" group-title="{group_p}", {lang_name}')
                lines_p.append(mpd_url)
                lines_p.append("")
            total_p = len([l for l in lines_p if l.startswith("#EXTINF")])
            try:
                with open(filename, "w", encoding="utf-8") as fw:
                    fw.write("\n".join(lines_p))
                print(f"{GREEN}✓ DRM plain M3U saved: {filename} ({total_p} entries){RESET}")
            except Exception as e:
                print(f"{RED}Failed to write M3U: {e}{RESET}")
            if os.path.isfile(filename):
                if git_push_enabled:
                    git_push_m3u(filename, f"Auto update DRM plain {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
                if use_cf and cf_worker_url and cf_api_token:
                    push_to_cloudflare(filename, cf_worker_url, cf_api_token)
            return None
        elif quality == "13":
            def collect_live_tv_entries(url, slug_path):
                drm_streams, global_license, global_keys, _ = fetch_drm_info_for_slug(slug_path)
                if not drm_streams:
                    return []
                result = []
                seen_mpds = set()
                for stream in drm_streams:
                    mpd_url = stream["mpd_url"]
                    mpd_base = mpd_url.split("?")[0]
                    if mpd_base in seen_mpds:
                        continue
                    seen_mpds.add(mpd_base)
                    variant = stream.get("variant", "PRIMARY")
                    hdntl_val = get_hdntl_token_4kads(mpd_url) or extract_hdntl(mpd_url)
                    key_str = ""
                    license_url = stream.get("license_url") or global_license
                    if license_url:
                        try:
                            mpd_info = fetch_mpd_pssh(mpd_url)
                            if mpd_info and mpd_info.get("key_ids"):
                                ck = try_clearkey_json(mpd_info["key_ids"], license_url)
                                if ck:
                                    key_str = ",".join(ck)
                        except:
                            pass
                    ott_url = build_ott_drm_url_direct(mpd_base, key_str, hdntl_val)
                    result.append((f"LIVE TV [{variant}]", ott_url, False))
                return result
            entries = collect_live_tv_entries(url, slug_path)
            return entries
        elif quality == "14":
            print(f"{CYAN}  → Fetching fresh JHS cookie...{RESET}")
            try:
                _fixed_url = "https://www.hotstar.com/in/tv/star-sports-hindi-1/1260000025/live/watch"
                _slug = extract_slug_path(_fixed_url)
                _hdntl = ""
                # Try DRM fetch first
                try:
                    _drm_streams, _, _, _ = fetch_drm_info_for_slug(_slug)
                    for _s in _drm_streams:
                        _mpd = _s.get("mpd_url", "")
                        if _mpd:
                            _hdntl = get_hdntl_token_4kads(_mpd) or extract_hdntl(_mpd)
                            if _hdntl:
                                break
                except Exception:
                    pass
                # Fallback: JHS API
                if not _hdntl:
                    try:
                        _jhs_api = build_jhs_api_url(_slug, "hin", is_live=True)
                        _jhs_req = request.Request(_jhs_api, headers=build_jhs_headers_android())
                        with request.urlopen(_jhs_req, timeout=10) as _r:
                            _jhs_data = json.loads(_r.read().decode("utf-8"))
                        for _sec in _jhs_data.get("success", {}).get("page", {}).get("spaces", {}).values():
                            for _ww in _sec.get("widget_wrappers", []):
                                _pc = _ww.get("widget", {}).get("data", {}).get("player_config")
                                if _pc:
                                    for _st in extract_jhs_fallback_only(_pc):
                                        _u = _st.get("content_url", "")
                                        if _u:
                                            _hdntl = get_hdntl_token_4kads(_u) or extract_hdntl(_u)
                                            if _hdntl:
                                                break
                                if _hdntl:
                                    break
                            if _hdntl:
                                break
                    except Exception:
                        pass
                if not _hdntl:
                    print(f"{RED}  Could not fetch hdntl cookie for JHS.{RESET}")
                    return []
                import re as _re
                _exp = _re.search(r"exp=(\d+)", _hdntl)
                if _exp:
                    import datetime as _dt
                    _exp_str = _dt.datetime.fromtimestamp(int(_exp.group(1))).strftime("%H:%M:%S")
                    print(f"{GREEN}  ✓ JHS cookie fetched (expires {_exp_str}){RESET}")
                else:
                    print(f"{GREEN}  ✓ JHS cookie fetched{RESET}")
                # Build fresh JHS entries with new token
                _jhs_by_name = {}
                for _ch in JHS_CHANNELS:
                    _final_url = _ch["url_template"].replace("{HDNTL}", _hdntl)
                    _ch_logo = _ch.get("logo", "")
                    _extinf = f'#EXTINF:-1 tvg-name="{_ch["name"]}" tvg-logo="{_ch_logo}" group-title="JioHotstar Live Channels", {_ch["name"]}'
                    _jhs_by_name[_ch["name"]] = (_extinf, _final_url)

                if not replace_m3u:
                    # Append mode: refresh JHS tokens, keep non-JHS entries
                    _cf_get = cf_worker_url if use_cf else None
                    _existing = fetch_existing_m3u(filename, _cf_get)
                    _m3u_lines = [
                        "#EXTM3U",
                        f"# Updated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
                        f"",
                        ""
                    ]
                    _refreshed = 0; _kept = 0; _added = 0
                    _written = set()
                    for _ex_inf, _ex_url, _ex_name in _existing:
                        if _ex_name in _jhs_by_name:
                            _new_inf, _new_url = _jhs_by_name[_ex_name]
                            _m3u_lines += [_new_inf, _new_url, ""]
                            _refreshed += 1
                        else:
                            _m3u_lines += [_ex_inf, _ex_url, ""]
                            _kept += 1
                        _written.add(_ex_name)
                    for _ch_name, (_ni, _nu) in _jhs_by_name.items():
                        if _ch_name not in _written:
                            _m3u_lines += [_ni, _nu, ""]
                            _added += 1
                    _total = _refreshed + _kept + _added
                    _msg = f"Append: {_refreshed} JHS refreshed + {_kept} kept + {_added} new = {_total} total"
                else:
                    # Replace mode: only JHS channels
                    _m3u_lines = [
                        "#EXTM3U",
                        f"# JioHotstar LiveTv— Auto-Updated {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
                        ""
                    ]
                    for _ni, _nu in _jhs_by_name.values():
                        _m3u_lines += [_ni, _nu, ""]
                    _msg = f"Replace: {len(_jhs_by_name)} JHS channels"

                try:
                    with open(filename, "w", encoding="utf-8") as _fw:
                        _fw.write("\n".join(_m3u_lines))
                    _total = len([_l for _l in _m3u_lines if _l.startswith("#EXTINF")])
                    print(f"{GREEN}  ✓ JHS M3U saved: {filename} ({_total} channels) [{_msg}]{RESET}")
                except Exception as _e:
                    print(f"{RED}  Failed to write JHS M3U: {_e}{RESET}")
                if os.path.isfile(filename):
                    if git_push_enabled:
                        git_push_m3u(filename, f"JHS auto update {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
                    if use_cf and cf_worker_url and cf_api_token:
                        push_to_cloudflare(filename, cf_worker_url, cf_api_token)
                return None
            except Exception as e:
                print(f"{RED}  JHS update failed: {e}{RESET}")
                return []
        elif quality == "17":
            return get_fallback_24h_entries(url)
        elif quality == "21":
            return get_fallback_4k_24h_entries(url)
        elif quality == "22":
            return get_primary_4k_24h_entries(url)
        else:
            return []

    while True:
        try:
            # ── TOKEN ROTATION ────────────────────────────────────────────────
            global _ACTIVE_TOKEN_OVERRIDE
            _working_tokens = [t for t in multi_token_list if t[0] not in _expired_token_nums]

            if not _working_tokens:
                # All tokens expired — show report and ask user
                print(f"\n{BOLD_RED}╔══════════════════════════════════════╗{RESET}")
                print(f"{BOLD_RED}║    ⚠  ALL TOKENS EXPIRED!            ║{RESET}")
                print(f"{BOLD_RED}╚══════════════════════════════════════╝{RESET}")
                _exp_names = [f"token{n}.txt" for n in sorted(_expired_token_nums) if n > 0]
                if _exp_names:
                    print(f"\n{RED}Expired token files:{RESET}")
                    for _en in _exp_names:
                        print(f"  {BOLD_RED}✗ {_en}{RESET}")
                    print(f"\n{YELLOW}↑ These tokens are expired — add fresh tokens in these files{RESET}")
                _ACTIVE_TOKEN_OVERRIDE = None
                _ans = input(f"\n{BOLD_CYAN}Previous Menu (Any Key To Yes) [N]: {RESET}").strip()
                if _ans.upper() != "N":
                    return
                else:
                    print(f"{RED}No working tokens available. Auto-update stopped.{RESET}")
                    return

            # Pick next token round-robin from working tokens only
            _tok_entry = _working_tokens[_token_cycle_idx % len(_working_tokens)]
            _tok_num, _tok_str, _tok_path = _tok_entry
            _tok_label = f"token{_tok_num}.txt" if _tok_num > 0 else "token.txt"

            # Validate token before using it
            print(f"\n{BOLD_YELLOW}[{datetime.now().strftime('%H:%M:%S')}] Updating M3U...{RESET} {CYAN}(Using: {_tok_label}){RESET}")
            print(f"{GRAY}  Validating token...{RESET}", end="", flush=True)
            if not check_token_valid(_tok_str, slug_path):
                print(f"\r{RED}  ✗ {_tok_label} is EXPIRED! — skipping, trying next token...{RESET}                ")
                _expired_token_nums.add(_tok_num)
                _exp_names_cur = [f"token{n}.txt" for n in sorted(_expired_token_nums) if n > 0]
                print(f"{RED}  Expired: {', '.join(_exp_names_cur)}{RESET}")
                continue
            else:
                print(f"\r{GREEN}  ✓ {_tok_label} is valid{RESET}                  ")
            _token_cycle_idx += 1

            _ACTIVE_TOKEN_OVERRIDE = _tok_str
            # ─────────────────────────────────────────────────────────────────
            _cycle_start_time = time.time()  # track how long the update itself takes

            # Multi-quality: collect entries from all selected qualities and merge
            if len(quality_list) > 1:
                merged_entries = []
                seen_merge_urls = set()
                seen_merge_labels = set()
                for q_idx, q in enumerate(quality_list):
                    q_label_map = {"1":"H265-DV-HDR-SDR-ADSFREE","2":"H265-FHD-DV-HDR-SDR","3":"H265-AUTO-DV-HDR-SDR-ADSFREE","4":"JHS-FHD","5":"JHS-4K","6":"H264-DV-HDR-SDR","7":"H265-DV-HDR-SDR","8":"H264-FHD-DV-HDR-SDR","9":"H265-FHD-DV-HDR-SDR","10":"PRI-4K","11":"DRM-OTT","12":"DRM-NS","13":"DRM-TV","14":"JHS-CHANNELS","17":"FALLBACK-24H","18":"PRIMARY-24H","19":"FALLBACK-24H-JIO","20":"PRIMARY-24H-JIO","21":"FALLBACK-4K-24H","22":"PRIMARY-4K-24H"}
                    q_tag = q_label_map.get(q, f"Q{q}")
                    print(f"{CYAN}  → Fetching quality {q} ({q_tag})...{RESET}")
                    q_entries = get_entries(q, url, slug_path)
                    if q_entries is None or not q_entries:
                        continue
                    for entry in q_entries:
                        if len(entry) == 2:
                            lang_n, entry_url = entry; is_hdr = False
                        else:
                            lang_n, entry_url, is_hdr = entry
                        entry_url_base = entry_url.split("?")[0]
                        # Tag label with quality if multiple qualities
                        tagged_label = f"{lang_n} [{q_tag}]"
                        if entry_url_base not in seen_merge_urls and tagged_label not in seen_merge_labels:
                            seen_merge_urls.add(entry_url_base)
                            seen_merge_labels.add(tagged_label)
                            merged_entries.append((tagged_label, entry_url, is_hdr))
                entries = merged_entries if merged_entries else []
            else:
                # ── RETRY LOOP: up to 5 attempts with exponential backoff ──────
                _max_retries = 5
                _retry_base_delay = 3  # seconds (delays: 3, 6, 12, 24, 48)
                entries = None
                for _attempt in range(_max_retries):
                    if _attempt > 0:
                        _wait_time = _retry_base_delay * (2 ** (_attempt - 1))
                        print(f"{YELLOW}  Retry {_attempt}/{_max_retries - 1} for {_tok_label} in {_wait_time}s...{RESET}")
                        time.sleep(_wait_time)
                    entries = get_entries(quality, url, slug_path)
                    if entries:
                        break
                    elif entries is None:
                        # DRM option (7/8): handled inside get_entries — stop retrying
                        break
            if entries is None:
                pass  # option 7/8 DRM: already handled inside get_entries
            elif entries:
                # ── Stream found → reset empty-cycle counter for this token ──
                _token_empty_cycles[_tok_num] = 0
                title, match_no = extract_match_title(url)
                stype = extract_stream_type(url)
                # Normalize entries - handle both (lang, url) and (lang, url, is_hdr) tuples
                normalized = []
                for entry in entries:
                    if len(entry) == 2:
                        normalized.append((entry[0], entry[1], False))
                    else:
                        normalized.append(entry)
                # ── Auto-extract hdntl cookie — skip for options 1-7 (URLs already carry token)
                _au_hdntl = ""
                if quality not in ["1","2","3","4","5","6","7","8","9","10"]:
                    for _en, _eu, _eh in normalized:
                        try:
                            _tok = get_hdntl_token_4kads(_eu)
                            if _tok:
                                _au_hdntl = _tok
                                break
                        except Exception:
                            pass

                if not replace_m3u:
                    # ── APPEND MODE ─────────────────────────────────────────
                    # Recently refreshed/new channels TOP pe, kept (old) channels BOTTOM pe
                    import re as _re
                    _new_by_name = {}
                    for _n, _u, _h in normalized:
                        _new_by_name[_n.strip()] = (_n, _u, _h)
                    # Fetch existing entries (local file or CF)
                    _cf_get = cf_worker_url if use_cf else None
                    _existing = fetch_existing_m3u(filename, _cf_get)

                    _refreshed = 0
                    _kept = 0
                    _added = 0
                    _written_names = set()

                    # --- Separate refreshed vs kept from existing ---
                    _refreshed_lines = []   # existing entries that got new token (top)
                    _kept_lines = []        # existing entries with no new match (bottom)

                    _skip_hdrs_append = False  # always add Origin+Referer headers

                    def _exthttp_line(ck):
                        if ck and quality not in ["1","2","3","4","5","6","7","8","9","10"]:
                            return f'#EXTHTTP:{{"Origin":"https://www.hotstar.com","Referer":"https://www.hotstar.com/","Cookie":"hdntl={ck}"}}' 
                        return '#EXTHTTP:{"Origin":"https://www.hotstar.com","Referer":"https://www.hotstar.com/"}'

                    for _extinf, _old_url, _tvg in _existing:
                        if _tvg in _new_by_name:
                            # Refresh URL with new token, keep EXTINF header
                            _, _new_url, _new_h = _new_by_name[_tvg]
                            _refreshed_lines.append(_extinf)
                            if not _skip_hdrs_append:
                                _refreshed_lines.append(_exthttp_line(_au_hdntl))
                                _refreshed_lines.append('#EXTVLCOPT:http-extra-headers=Origin: https://www.hotstar.com')
                                _refreshed_lines.append('#EXTVLCOPT:http-referrer=https://www.hotstar.com/')
                            _refreshed_lines.append(_new_url)
                            _refreshed_lines.append("")
                            _refreshed += 1
                        else:
                            # Keep as-is (JHS channel or other source)
                            _kept_lines.append(_extinf)
                            _kept_lines.append(_old_url)
                            _kept_lines.append("")
                            _kept += 1
                        _written_names.add(_tvg)

                    # --- Truly new entries not seen before ---
                    _new_lines = []
                    for _n, _u, _h in normalized:
                        if _n.strip() not in _written_names:
                            if quality in ["7", "8", "9"]:
                                _n_upper = _n.upper()
                                if "SDR" in _n_upper:
                                    _base = _n.replace(" SDR", "").replace(" sdr", "").strip()
                                    _display = f"{_base} 4K SDR ADSFREE"
                                elif _h:
                                    _base = _n.replace(" HDR", "").replace(" hdr", "").strip()
                                    _display = f"{_base} 4K HDR ADSFREE"
                                else:
                                    _display = f"{_n} 4K SDR ADSFREE"
                            else:
                                _tag = " [HDR]" if _h else ""
                                _display = f"{_n}{_tag}"
                            _new_lines.append(f'#EXTINF:-1 tvg-id="" tvg-logo="{logo_url}" group-title="{title}", {_display}')
                            if not _skip_hdrs_append:
                                _new_lines.append(_exthttp_line(_au_hdntl))
                                _new_lines.append('#EXTVLCOPT:http-extra-headers=Origin: https://www.hotstar.com')
                                _new_lines.append('#EXTVLCOPT:http-referrer=https://www.hotstar.com/')
                            _new_lines.append(_u)
                            _new_lines.append("")
                            _added += 1

                    # --- Build final M3U: header → refreshed → new → kept ---
                    _merged = [
                        "#EXTM3U",
                        f"# Title: {title}",
                        f"# Updated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}",
                        ""
                    ]
                    _merged += _refreshed_lines   # recently refreshed → TOP
                    _merged += _new_lines          # brand new channels → after refreshed
                    _merged += _kept_lines         # old/JHS channels → BOTTOM

                    try:
                        with open(filename, "w", encoding="utf-8") as _fw:
                            _fw.write("\n".join(_merged))
                        print(f"{GREEN}✓ Append: {_refreshed} refreshed + {_added} new [TOP] + {_kept} kept [BOTTOM] = {_refreshed+_kept+_added} total → {filename}{RESET}")
                    except Exception as _we:
                        print(f"{YELLOW}⚠ Write failed ({_we}), falling back to replace{RESET}")
                        create_m3u_file(normalized, title, match_no, stype, filename, logo_url, skip_http_headers=False, force_no_cookie=(quality in ["1","2","3","4","5","6","7","8","9","10"]), is_adsfree_4k=(quality in ["10"]))
                else:
    # ── REPLACE MODE (default) ───────────────────────────────
                    create_m3u_file(normalized, title, match_no, stype, filename, logo_url, hdntl_cookie=None, skip_http_headers=False, force_no_cookie=(quality in ["1","2","3","4","5","6","7","8","9","10"]), is_adsfree_4k=(quality in ["10"]))
                # ── Push ─────────────────────────────────────────────────────
                file_exists = os.path.isfile(filename)
                if git_push_enabled and file_exists:
                    git_push_m3u(filename, f"Auto update {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
                if use_cf and cf_worker_url and cf_api_token and file_exists:
                    push_to_cloudflare(filename, cf_worker_url, cf_api_token)
                elif use_cf and cf_worker_url and cf_api_token and not file_exists:
                    print(f"{RED}✗ M3U file not found on disk, cannot push to Cloudflare.{RESET}")
            else:
                # ── No streams → track consecutive empty cycles per token ──
                _token_empty_cycles[_tok_num] = _token_empty_cycles.get(_tok_num, 0) + 1
                _empty_count = _token_empty_cycles[_tok_num]
                if _empty_count >= 2:
                    # 2 consecutive empty cycles = treat as expired (Hotstar gives 200 but no data)
                    print(f"{RED}No streams found this cycle.{RESET}")
                    print(f"{BOLD_RED}  ⚠ {_tok_label} returned empty streams {_empty_count}x in a row — marking as EXPIRED!{RESET}")
                    _expired_token_nums.add(_tok_num)
                    _exp_names_cur = [f"token{n}.txt" for n in sorted(_expired_token_nums) if n > 0]
                    print(f"\n{RED}Expired token files:{RESET}")
                    for _en in _exp_names_cur:
                        print(f"  {BOLD_RED}✗ {_en}{RESET}")
                    print(f"\n{YELLOW}↑ Ye tokens expire ho gaye — inhe fresh tokens se replace karo{RESET}")
                    _ans = input(f"\n{BOLD_CYAN}Previous Menu (Any Key To Yes) [N]: {RESET}").strip()
                    if _ans.upper() != "N":
                        _ACTIVE_TOKEN_OVERRIDE = None
                        return
                    else:
                        print(f"{YELLOW}Skipping expired token, trying next...{RESET}")
                        continue
                else:
                    print(f"{RED}No streams found this cycle.{RESET} {YELLOW}(empty cycle {_empty_count}/2 for {_tok_label}){RESET}")
                # ⚡ FAST SKIP: retries exhausted — jump to next token without full interval sleep
                print(f"{YELLOW}  → Skipping to next token immediately (no streams after {_max_retries} retries)...{RESET}")
                continue
            # ── Chunked sleep with countdown (avoids long blocking sleep) ──
            # Subtract time already spent on the update so total cycle = interval minutes
            _update_took = time.time() - _cycle_start_time
            _total_secs = max(0, interval * 60 - int(_update_took))
            _next_time = datetime.fromtimestamp(time.time() + _total_secs).strftime('%H:%M:%S')
            _took_str = f"{int(_update_took)}s update" if _update_took >= 1 else ""
            print(f"{CYAN}Next update at {_next_time} — waiting {_total_secs//60}m {_total_secs%60}s{f' (took {_took_str})' if _took_str else ''}... (Ctrl+C to stop){RESET}")
            _elapsed = 0
            _chunk = 30  # sleep in 30-second chunks
            while _elapsed < _total_secs:
                _sleep_now = min(_chunk, _total_secs - _elapsed)
                time.sleep(_sleep_now)
                _elapsed += _sleep_now
                _remaining = (_total_secs - _elapsed) // 60
                if _elapsed < _total_secs and _remaining > 0:
                    print(f"{GRAY}  ⏳ {_remaining} min remaining...{RESET}", end="\r", flush=True)
            print(f"                                    ", end="\r")  # clear countdown line
        except KeyboardInterrupt:
            print(f"\n{YELLOW}Auto-update stopped by user.{RESET}")
            _ACTIVE_TOKEN_OVERRIDE = None
            break
        except Exception as e:
            print(f"{RED}ERROR in update loop: {type(e).__name__}: {e}{RESET}")
            import traceback
            traceback.print_exc()
            _total_secs_retry = interval * 60
            print(f"{YELLOW}Retrying in {interval} minutes...{RESET}")
            _elapsed_r = 0
            while _elapsed_r < _total_secs_retry:
                _sleep_now_r = min(30, _total_secs_retry - _elapsed_r)
                time.sleep(_sleep_now_r)
                _elapsed_r += _sleep_now_r
    _ACTIVE_TOKEN_OVERRIDE = None


# ===================== OPTION 9 (4K ADS-FREE PRIMARY CDN - SINGLE LANGUAGE) =====================
API_TEMPLATE_4KADS = "https://www.hotstar.com/api/internal/bff/v2/slugs/in/{slug_path}/watch"

LANG_MAP_4KADS = {
    "1": ["eng"],
    "2": ["hin", "hi", "hd"],
    "3": ["mar", "mr", "ma"],
    "4": ["guj", "gu"],
    "5": ["bih", "bho", "bh"],
    "6": ["pan", "pun", "pa", "pu"],
    "7": ["har", "hv", "ha"],
    "8": ["tam", "ta"],
    "9": ["tel", "te"],
    "10": ["kan", "kn"],
    "11": ["mal", "ml"],
    "12": ["ben", "bn"],
}

def print_streams_4kads(streams: list, expected_lang: str):
    if not streams:
        return None
    candidate_urls = []
    for s in streams:
        original_url = str(s.get("content_url", ""))
        if not original_url:
            continue
        if str(s.get("type", "")).lower() != "primary":
            continue
        variants = generate_cdn_variants_4kads(original_url)
        for v in variants:
            candidate_urls.append((v, s))
    working = []
    with ThreadPoolExecutor(max_workers=12) as executor:
        futures = {executor.submit(is_working_url_4kads, item[0]): item for item in candidate_urls}
        for future in as_completed(futures):
            result = future.result()
            if result:
                working.append(futures[future])
    shown = set()
    for raw_url, s in working:
        clean = raw_url.split("?")[0]
        if clean in shown:
            continue
        shown.add(clean)
        detected_lang = detect_language_from_url_4kads(raw_url)
        if detected_lang.upper() != expected_lang.upper():
            continue
        token = get_hdntl_token_4kads(raw_url)
        final_url = append_hdntl_to_url_4kads(raw_url, token)
        lower = raw_url.lower()
        stype = str(s.get("type", "")).upper()
        extra = f" {GREEN}ADSFREE{RESET}" if ("non_ssai" in lower or "ssai" not in lower) else ""
        if "2160" in lower or "4k" in lower:
            extra += f" {MAGENTA}4K{RESET}"
        elif "1080" in lower:
            extra += f" {CYAN}1080P{RESET}"
        elif "720" in lower:
            extra += f" {BLUE}720P{RESET}"
        print(f"{YELLOW}WORKING PRIMARY CDN | {detected_lang} | {stype}{extra}{RESET}")
        print(f"{final_url}\n")
        return final_url
    return None

def clean_stream_url(url: str) -> str:
    """Remove ttl, Expires, Signature, Key-Pair-Id parameters, keep original hdnea."""
    if '?' not in url:
        return url
    base, query = url.split('?', 1)
    params = query.split('&')
    keep = []
    for p in params:
        # Drop these parameters
        if p.startswith('ttl=') or p.startswith('Expires=') or p.startswith('Signature=') or p.startswith('Key-Pair-Id='):
            continue
        keep.append(p)
    clean_query = '&'.join(keep)
    return base + '?' + clean_query

def get_option5_entries(input_url: str):
    """Reusable version of option5_main that returns (lang, url, is_hdr) entries.
    Fast path: no CDN probing, no hdntl fetch. HDR only for ENGLISH and HINDI.
    """
    asset_id = parse_asset_id_4kads(input_url)
    if not asset_id:
        return []

    slug_path_5 = extract_slug_path(input_url) or ""

    # Step 1: HDR for ENGLISH and HINDI only (Hotstar only serves HDR for these two)
    hdr_results = {}
    eng_hdr = fetch_stream_4kads_lite(asset_id, LANG_MAP_4KADS["1"], "ENGLISH", use_sdr=False, slug_path=slug_path_5)
    if eng_hdr:
        hdr_results["ENGLISH"] = eng_hdr[1]
    hin_hdr = fetch_stream_4kads_lite(asset_id, LANG_MAP_4KADS["2"], "HINDI", use_sdr=False, slug_path=slug_path_5)
    if hin_hdr:
        hdr_results["HINDI"] = hin_hdr[1]

    # Step 2: SDR for ALL languages — fast lite path, parallel
    sdr_results = {}
    with ThreadPoolExecutor(max_workers=len(LANG_MAP_4KADS)) as executor:
        futures = {
            executor.submit(fetch_language_wrapper_4kads_lite, asset_id, lang_num, lang_codes, True, slug_path_5): lang_num
            for lang_num, lang_codes in LANG_MAP_4KADS.items()
        }
        for future in as_completed(futures):
            try:
                lang_name, url_res = future.result()
                if url_res:
                    if lang_name in ["ENGLISH", "HINDI"]:
                        sdr_results[f"{lang_name} SDR"] = url_res
                    else:
                        sdr_results[lang_name] = url_res
            except Exception:
                pass

    # Step 3: Build entries — HDR first, then SDR in order
    entries = []
    for lang in ["ENGLISH", "HINDI"]:
        if lang in hdr_results:
            entries.append((lang, hdr_results[lang], True))
    for lang in ["ENGLISH SDR", "HINDI SDR"]:
        if lang in sdr_results:
            entries.append((lang, sdr_results[lang], False))
    for lang in LANG_ORDER_4KADS:
        if lang not in ["ENGLISH", "HINDI"] and lang in sdr_results:
            entries.append((lang, sdr_results[lang], False))
    return entries

def option9_main(input_url: str):
    import threading
    asset_id = parse_asset_id_4kads(input_url)
    slug_path = extract_slug_path(input_url) or ""
    if not asset_id:
        print(f"{RED}Error: could not parse asset id from URL{RESET}")
        return

    print(f"\n{GREEN}=== PRIMARY ADSFREE STREAM FINDER (ALL LANGUAGES) ==={RESET}\n")
    print(f"{YELLOW}Checking all languages in parallel...{RESET}\n")

    # All unique language groups to try (primary code + fallbacks)
    lang_groups = [
        ("eng", ["eng"], "ENGLISH"),
        ("hin", ["hin", "hi", "hd"], "HINDI"),
        ("mar", ["mar", "mr", "ma"], "MARATHI"),
        ("guj", ["guj", "gu"], "GUJARATI"),
        ("bih", ["bih", "bho", "bh"], "BHOJPURI"),
        ("pan", ["pan", "pun", "pa", "pu"], "PUNJABI"),
        ("har", ["har", "hv", "ha"], "HARYANVI"),
        ("tam", ["tam", "ta"], "TAMIL"),
        ("tel", ["tel", "te"], "TELUGU"),
        ("kan", ["kan", "kn"], "KANNADA"),
        ("mal", ["mal", "ml"], "MALAYALAM"),
        ("ben", ["ben", "bn"], "BENGALI"),
    ]

    collected = []
    lock = threading.Lock()

    def fetch_one_lang(primary, codes, lang_name):
        for lang_code in codes:
            for attempt in range(2):
                try:
                    api_url = build_api_url_4kads(asset_id, lang_code, slug_path=slug_path)
                    player_config = fetch_player_config_4kads(api_url)
                    streams = extract_all_streams_4kads(player_config)
                    if not streams:
                        continue
                    # Build CDN candidate list
                    candidate_urls = []
                    for s in streams:
                        orig = str(s.get("content_url", ""))
                        if not orig:
                            continue
                        if str(s.get("type", "")).lower() != "primary":
                            continue
                        for v in generate_cdn_variants_4kads(orig):
                            candidate_urls.append((v, s))
                    if not candidate_urls:
                        continue
                    # Check working URLs in parallel
                    working = []
                    with ThreadPoolExecutor(max_workers=12) as ex:
                        futs = {ex.submit(is_working_url_4kads, item[0]): item for item in candidate_urls}
                        for fut in as_completed(futs):
                            if fut.result():
                                working.append(futs[fut])
                    shown = set()
                    for raw_url, s in working:
                        clean = raw_url.split("?")[0]
                        if clean in shown:
                            continue
                        shown.add(clean)
                        detected = detect_language_from_url_4kads(raw_url)
                        if detected.upper() != lang_name.upper():
                            continue
                        token = get_hdntl_token_4kads(raw_url)
                        final_url = append_hdntl_to_url_4kads(raw_url, token)
                        lower = raw_url.lower()
                        extra = " ADSFREE" if ("non_ssai" in lower or "ssai" not in lower) else ""
                        if "2160" in lower or "4k" in lower:
                            extra += " 4K"
                        elif "1080" in lower:
                            extra += " 1080P"
                        elif "720" in lower:
                            extra += " 720P"
                        with lock:
                            if lang_name not in [c[0] for c in collected]:
                                collected.append((lang_name, final_url, extra.strip()))
                        return
                except Exception:
                    if attempt == 0:
                        time.sleep(0.5)
                    continue

    with ThreadPoolExecutor(max_workers=6) as pool:
        futs = [pool.submit(fetch_one_lang, p, codes, name) for p, codes, name in lang_groups]
        for f in as_completed(futs):
            try:
                f.result()
            except Exception:
                pass

    if not collected:
        print(f"{RED}No working primary streams found for any language.{RESET}")
        print(f"{YELLOW}Check token/network.{RESET}")
        return

    print(f"{BOLD_GREEN}=== FOUND {len(collected)} LANGUAGE(S) ==={RESET}\n")
    for lang_name, final_url, tags in collected:
        lower_url = final_url.lower()
        label = f"{lang_name} 4K ADSFREE"
        print(f"{BOLD_CYAN}{label}{RESET}")
        print(f"{GREEN}{final_url}{RESET}\n")

    if os.name == "nt":
        os.system("pause")
    else:
        input(f"\nPress Enter to exit and copy URLs...")

# ===================== OPTION 10 (REFRESH TOKENS IN M3U) =====================
def option9_refresh_tokens():
    print(f"\n{BOLD_GREEN}=== AUTO REFRESH TOKENS IN M3U ==={RESET}")
    filename = input(f"Enter M3U filename to refresh (e.g. hotstar_auto.m3u): ").strip()
    if not filename:
        print(f"{RED}No filename entered.{RESET}")
        return
    if not os.path.isfile(filename):
        print(f"{RED}File not found: {filename}{RESET}")
        return

    interval_raw = input(f"Refresh interval in minutes (default 20): ").strip()
    interval = int(interval_raw) if interval_raw.isdigit() else 20

    print(f"\n{BOLD_CYAN}Auto-push destination:{RESET}")
    print(f"  {BOLD_GREEN}1{RESET}) GitHub only")
    print(f"  {BOLD_YELLOW}2{RESET}) Cloudflare Workers only")
    print(f"  {BOLD_MAGENTA}3{RESET}) Both GitHub + Cloudflare")
    print(f"  {BOLD_WHITE}n{RESET}) No push (local only)")
    push_choice = input(f"{BOLD_CYAN}Choose (1/2/3/n): {RESET}").strip().lower()
    git_push_enabled = push_choice in ["1", "3"]
    use_cf = push_choice in ["2", "3"]
    cf_worker_url = None
    cf_api_token = None
    if use_cf:
        config = load_cf_config()
        config_valid = (
            config and
            config.get("worker_url", "").startswith("http") and
            config.get("api_token", "")
        )
        if config_valid:
            print(f"{GREEN}✓ Loaded Cloudflare config from {CF_CONFIG_FILE}{RESET}")
            use_existing = input(f"Use existing config? (y/n): ").strip().lower()
            if use_existing == 'y':
                cf_worker_url = config['worker_url']
                cf_api_token = config['api_token']
            else:
                cf_worker_url = input("Enter Cloudflare Worker URL (https://...): ").strip()
                cf_api_token = input("Enter API Bearer Token: ").strip()
                save_cf_config(cf_worker_url, cf_api_token)
        else:
            cf_worker_url = input("Enter Cloudflare Worker URL (https://...): ").strip()
            cf_api_token = input("Enter API Bearer Token: ").strip()
            save_cf_config(cf_worker_url, cf_api_token)
        if not cf_worker_url or not cf_worker_url.startswith("http"):
            print(f"{RED}✗ Invalid Worker URL! Disabling CF push.{RESET}")
            use_cf = False
        elif not cf_api_token:
            print(f"{RED}✗ API token empty! Disabling CF push.{RESET}")
            use_cf = False
    if git_push_enabled:
        print(f"{GREEN}✓ GitHub auto-push enabled{RESET}")
    if not git_push_enabled and not use_cf:
        print(f"{YELLOW}No push destination. File will be saved locally only.{RESET}")

    def do_refresh():
        with open(filename, "r", encoding="utf-8") as f:
            lines = f.readlines()

        updated = 0
        failed = 0
        i = 0

        while i < len(lines):
            line = lines[i].strip()

            # Only refresh the hdnea/hdntl token already present in the stream URL.
            # Do NOT touch #EXTHTTP, #EXTVLCOPT, or any other directive lines.
            if line.startswith("http") and "hotstar.com" in line and ("hdnea=" in line or "hdntl=" in line):
                old_url = line
                try:
                    new_token = get_hdntl_token_4kads(old_url)
                    if not new_token:
                        failed += 1
                    else:
                        new_url = append_hdntl_to_url_4kads(old_url, new_token)
                        lines[i] = new_url + "\n"
                        updated += 1
                except Exception:
                    failed += 1
            i += 1

        # Update the "Generated:" timestamp if present
        for idx, line in enumerate(lines):
            if line.startswith("# Generated:"):
                lines[idx] = f"# Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
                break

        # Write back to file
        with open(filename, "w", encoding="utf-8") as f:
            f.writelines(lines)

        return updated, failed

    print(f"{GREEN}✓ Starting auto-refresh every {interval} minute(s) — Ctrl+C to stop{RESET}")
    while True:
        try:
            print(f"\n{BOLD_YELLOW}[{datetime.now().strftime('%H:%M:%S')}] Refreshing tokens...{RESET}")
            ok, fail = do_refresh()
            print(f"{GREEN}✓ {ok} token(s) refreshed (URL + Cookie), {fail} failed → {filename}{RESET}")
            if git_push_enabled:
                git_push_m3u(filename, f"Token refresh {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
            if use_cf and cf_worker_url and cf_api_token:
                push_to_cloudflare(filename, cf_worker_url, cf_api_token)
            print(f"{CYAN}Waiting {interval} minutes...{RESET}")
            time.sleep(interval * 60)
        except KeyboardInterrupt:
            print(f"\n{YELLOW}Stopped.{RESET}")
            break


# ===================== OPTION 11 (UPDATE JHS.TXT COOKIES) =====================

# ── Embedded JHS channel list (from jhs.txt) ──────────────────────────────────
JHS_CHANNELS = [
    # ════════════════════════════════════════
    # ✅ VERIFIED WORKING CHANNELS (auto-merged)
    # ════════════════════════════════════════
    {
        "logo": 'https://i.ibb.co/YBMBDWtd/SS2HD-HINDI.jpg',
        "name": 'STAR SPORTS 2 Hindi HD',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/f0e3e64ae415771d8e460317ce97aa5e/Fallback/f0e3e64ae415771d8e460317ce97aa5e.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'f0e3e64ae415771d8e460317ce97aa5e'
    },
    {
        "logo": 'https://i.ibb.co/cXNb5Y9t/SS2-TAMIL.jpg',
        "name": 'STAR SPORTS 2 Tamil',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/4db6f833701e78ae4443cb268020f03b/Fallback/4db6f833701e78ae4443cb268020f03b.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": '4db6f833701e78ae4443cb268020f03b'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_960,h_540/v3Storage/assets/colors-cineplex-superhit%2016x9-1648793655358.jpg',
        "name": 'Colors Cineplex Superhits',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsCineplexSuperhit/JCHLS/JC_ColorsCineplexSuperhit.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsCineplexSuperhit'
    },
    {
        "logo": 'https://i.ibb.co/bM7qT3NC/SS2-TELUGU.jpg',
        "name": 'STAR SPORTS 2 Telugu',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/034d1fb94cae87294a06f4dc266084b9/Fallback/034d1fb94cae87294a06f4dc266084b9.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": '034d1fb94cae87294a06f4dc266084b9'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/cineplex-1713963820848.jpeg',
        "name": 'Colors Cineplex Bollywood',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsCineplexBollywood/JCHLS/JC_ColorsCineplexBollywood.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsCineplexBollywood'
    },
    {
        "logo": 'https://img1.hotstarext.com/image/upload/f_auto/sources/r1/cms/prod/7226/597226-h.jpg',
        "name": 'STAR SPORTS 1 SELECT HD',
        "url_template": 'https://livetv.hotstar.com/mp2/gec-india-1540065791/8bb5cd7a8e274186977473a6771d9352/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=1f64a24b3950468497390155c4880000:68f788aced6c4ecb89108f22fe9ee087',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540065791'
    },
    {
        "logo": 'https://i.ibb.co/x8739M8d/SS2HD.jpg',
        "name": 'STAR SPORTS 2 HD',
        "url_template": 'https://livetv.hotstar.com/mp2/gec-india-1540065785/a00717b1324f45eb814eec9e48a12db8/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=9dacc80134404c34ba184022c28d0000:982183fb4d9449c995859b7cff512092',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540065785'
    },
    {
        "logo": 'https://i.ibb.co/pmVQWFZ/SS1HD.jpg',
        "name": 'STAR SPORTS 1 HD',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540065782/fce958099ca84fc3b980e651a4a668a8/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=b7cdde012ce04e90a08b90622e020000:13603245acab444faef6cab5198de55f',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540065782'
    },
    {
        "logo": 'https://i.ibb.co/B5Mnd89k/SS2-HINDI.jpg',
        "name": 'STAR SPORTS 2 Hindi',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/2c7182c8e6a22cfa6ebc02bbc9ed6dd0/Fallback/2c7182c8e6a22cfa6ebc02bbc9ed6dd0.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": '2c7182c8e6a22cfa6ebc02bbc9ed6dd0'
    },
    {
        "logo": 'https://img1.hotstarext.com/image/upload/f_auto/sources/r1/cms/prod/7227/597227-h.jpg',
        "name": 'STAR SPORTS 2 SELECT HD',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540065794/e2408fbafb9d4a5ab23775b69e5737d7/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=2effd2e98f95492cb7418857bf610000:f0e42f1c91fb4b59bf6684cb4478d82e',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540065794'
    },
    {
        "logo": "https://img10.hotstar.com/image/upload/f_auto/sources/r1/cms/prod/8763/1739203338763-a.jpg",
        "name": "TATA IPL TV",
        "url_template": "https://jcevents.hotstar.com/bpk-tv/e03bbf7688f4b14faa3782e78851c3d9_CTV/Fallback/index2.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}",
        "type": "m3u8_lcookie",
        "stream_id": "e03bbf7688f4b14faa3782e78851c3d9_CTV",
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/ct-1644165913136.jpg',
        "name": 'Colors Tamil HD',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsTamilHD/JCHLS/JC_ColorsTamilHD.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsTamilHD'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_1090,h_613/v3Storage/assets/colors-hindi--16x9-1714557869344.jpg',
        "name": 'Colors HD',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsHD/JCHLS/JC_ColorsHD.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsHD'
    },
    {
        "logo": 'https://img.media.jio.com/tvpimages/5/6/301982_1749665314605_l_medium.jpg',
        "name": 'STAR SPORTS 1 Hindi HD',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540065788/fa6a4f0005ef4f90ab24484d165b0aaf/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=81872faa1d6b45fa9045cdeb2e310000:9b88168e61274587a471962c46b94675',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540065788'
    },
    {
        "logo": "https://img10.hotstar.com/image/upload/f_auto,q_90,w_384/sources/r1/cms/prod/1199/1752742701199-h",
        "name": "STAR VIJAY SUPER SINGER",
        "url_template": "https://livetv.hotstar.com/out/v1/llg-tv-mum/1540066005_tamil_7d12a83c/gec-india_hls_unencrypted/master-ap-1080-4.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}",
        "type": "m3u8_cookie",
        "stream_id": "691"
    },
    {
        "logo": "https://img10.hotstar.com/image/upload/f_auto,q_90,w_256/sources/r1/cms/prod/7405/1752743467405-h",
        "name": "STAR VIJAY CLASSIC",
        "url_template": "https://livetv.hotstar.com/out/v1/llg-tv-mum/1540065993_tamil_0fe06fa1/gec-india_hls_unencrypted/master-ap-1080-4.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}",
        "type": "m3u8_cookie",
        "stream_id": "961"
    },
    {
        "logo": "https://img10.hotstar.com/image/upload/f_auto,q_90,w_256/sources/r1/cms/prod/4044/1752743564044-h",
        "name": "STAR VIJAY MOVIE TIME",
        "url_template": "https://livetv.hotstar.com/out/v1/llg-tv-mum/1540066002_tamil_de83b1db/gec-india_hls_unencrypted/master-ap-1080-4.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}",
        "type": "m3u8_cookie",
        "stream_id": "169"
    },
    {
        "logo": "https://img10.hotstar.com/image/upload/f_auto,q_90,w_256/sources/r1/cms/prod/8708/1752743198708-h",
        "name": "STAR VIJAY KALAKKAL COMEDY",
        "url_template": "https://livetv.hotstar.com/out/v1/llg-tv-mum/1540065999_tamil_9be72647/gec-india_hls_unencrypted/master-ap-1080-4.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}",
        "type": "m3u8_cookie",
        "stream_id": "320"
    },
    {
        "logo": "https://img10.hotstar.com/image/upload/f_auto,q_90,w_256/sources/r1/cms/prod/3380/1752743343380-h",
        "name": "STAR VIJAY FUN GAMES",
        "url_template": "https://livetv.hotstar.com/out/v1/llg-tv-mum/1540065996_tamil_e5e5a418/gec-india_hls_unencrypted/master-ap-1080-4.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}",
        "type": "m3u8_cookie",
        "stream_id": "405"
    },
    {
        "logo": "https://img10.hotstar.com/image/upload/f_auto,q_90,w_384/sources/r1/cms/prod/2214/1750777602214-h",
        "name": "IPL 24/7",
        "url_template": "https://livetv.hotstar.com/out/v1/llg-tv-mum/1540065990_hindi_38333ea5/gec-india_hls_unencrypted/master-ap-1080-4.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}",
        "type": "m3u8_cookie",
        "stream_id": "741"
    },
    {
        "logo": "https://img10.hotstar.com/image/upload/f_auto,q_90,w_384/sources/r1/cms/prod/5745/1750779565745-h",
        "name": "STAR SPORTS CRICKET CLASSIC",
        "url_template": "https://livetv.hotstar.com/out/v1/llg-tv-mum/1540065984_hindi_786cf674/gec-india_hls_unencrypted/master-ap-1080-4.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}",
        "type": "m3u8_cookie",
        "stream_id": "213"
    },
    {
        "logo": "https://img10.hotstar.com/image/upload/f_auto,q_90,w_384/sources/r1/cms/prod/3639/1756796893639-h",
        "name": "T20s TV",
        "url_template": "https://livetv.hotstar.com/mp2/gec-india/60b51adb7eae4ae492e6ba6c156a1efe/index_7.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}",
        "type": "m3u8_cookie",
        "stream_id": "784"
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/colors-super-live-channels-16x9-4-1642744939924.jpg',
        "name": 'Colors Super',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsSuperKannada/JCHLS/JC_ColorsSuperKannada.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsSuperKannada'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/collors-rishtey-live-channels-16x9-3-1642676080416-1674198105431-1697532377978.jpg',
        "name": 'Colors Rishtey',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsRishtey/JCHLS/JC_ColorsRishtey.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsRishtey'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/colors-gujarati-16x9-1713269620328.jpg',
        "name": 'Colors Gujarati',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsGujarati/JCHLS/JC_ColorsGujarati.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsGujarati'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/colors-kannada-16x9-1677754085834.jpg',
        "name": 'Colors Kannada HD',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsKannadaHD/JCHLS/JC_ColorsKannadaHD.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsKannadaHD'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/Live-Tv-Channels-colors-cineplex-1607514413063.jpg',
        "name": 'Colors Cineplex HD',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsCineplexHD/JCHLS/JC_ColorsCineplexHD.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsCineplexHD'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/colors-infinity-live-channels-16x9-1642496946057.jpg',
        "name": 'Colors Infinity HD',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsInfinityHD/JCHLS/JC_ColorsInfinityHD.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsInfinityHD'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/colors-bangla-new-16x9-4-1649659533344.jpg',
        "name": 'Colors Bangla HD',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsBanglaHD/JCHLS/JC_ColorsBanglaHD.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsBanglaHD'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/colors-marathi-live-channels-16x9-4-6-apr-1649257093359.jpg',
        "name": 'Colors Marathi HD',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsMarathiHD/JCHLS/JC_ColorsMarathiHD.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsMarathiHD'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets//16x9-1719554242246.jpg',
        "name": 'Nick',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_NickSD/JCHLS/JC_NickSD.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_NickSD'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/colors-kannada-cinema-16x9-1713963481807.jpg',
        "name": 'Colors Kannada Cinema',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_ColorsKannadaCinema/JCHLS/JC_ColorsKannadaCinema.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_ColorsKannadaCinema'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/mtv-16x9-1714316345624.jpg',
        "name": 'MTV HD',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_MTVHD/JCHLS/JC_MTVHD.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_MTVHD'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/nick-jr-16x9-2-1626708077243.jpg',
        "name": 'Nick Jr',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_NickJr/JCHLS/JC_NickJr.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_NickJr'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_450,h_253/v3Storage/assets/sonic-16x9-2-1626707025539.jpg',
        "name": 'Sonic',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_SonicNick/JCHLS/JC_SonicNick.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_SonicNick'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_1090,h_613/v3Storage/assets/nick-hd-plus-live-channels-16x9-4-1642585145139.jpg',
        "name": 'Nick HD+',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/JC_NickHD/JCHLS/JC_NickHD.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'JC_NickHD'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_1090,h_613/v3Storage/assets/cnbc-awaaz-16x9-1702387934761.jpg',
        "name": 'CNBC Awaaz',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/CNBC_Awaaz_voot_MOB/Fallback/CNBC_Awaaz_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'CNBC_Awaaz_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/ETV_Kannada_News.png',
        "name": 'News18 Kannada',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Kannada_voot_MOB/Fallback/News18_Kannada_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Kannada_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/CNN_NEWS_18.png',
        "name": 'CNN News18',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/CNN_News18_voot_MOB/Fallback/CNN_News18_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'CNN_News18_voot_MOB'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_1090,h_613/v3Storage/assets/cnbc18-shereen-bhan-16x9-2-1693479472079.jpg',
        "name": 'CNBC TV18',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/CNBC_TV18_voot_MOB/Fallback/CNBC_TV18_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'CNBC_TV18_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/IBN_7.png',
        "name": 'News18 India',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_India_voot_MOB/Fallback/News18_India_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_India_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/ETV_Haryana_and_HP_News.png',
        "name": 'News18 Punjab Haryana',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Punjab_Haryana_HP_voot_MOB/Fallback/News18_Punjab_Haryana_HP_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Punjab_Haryana_HP_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/IBN_Lokmat.png',
        "name": 'News18 Lokmat',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Lokmat_voot_MOB/Fallback/News18_Lokmat_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Lokmat_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/News_18_Tamilnadu.png',
        "name": 'News 18 Tamilnadu',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Tamil_Nadu_voot_MOB/Fallback/News18_Tamil_Nadu_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Tamil_Nadu_voot_MOB'
    },
    {
        "logo": 'https://v3img.voot.com/resizeMedium,w_1090,h_613/v3Storage/assets/whatsapp16x9-1693491956187.jpg',
        "name": 'CNBC Bazaar',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/CNBC_Bazaar_voot_MOB/Fallback/CNBC_Bazaar_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'CNBC_Bazaar_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/ETV_Bangla_News.png',
        "name": 'News18 Bangla',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Bangla_voot_MOB/Fallback/News18_Bangla_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Bangla_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/ETV_BIHAR.png',
        "name": 'News18 Bihar Jharkhand',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Bihar_Jharkhand_voot_MOB/Fallback/News18_Bihar_Jharkhand_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Bihar_Jharkhand_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/ETV_News_Gujarati.png',
        "name": 'News18 Gujarati',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Gujarati_voot_MOB/Fallback/News18_Gujarati_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Gujarati_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/ETV_News_Oriya.png',
        "name": 'News18 Odia',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Odia_voot_MOB/Fallback/News18_Odia_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Odia_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/News_18_Assam.png',
        "name": 'News18 Assam North East',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Assam_North_East_voot_MOB/Fallback/News18_Assam_North_East_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Assam_North_East_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/ETV_Urdu.png',
        "name": 'News18 JKLH',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Urdu_voot_MOB/Fallback/News18_Urdu_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Urdu_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/ETV_RAJASTHAN.png',
        "name": 'News18 Rajasthan',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Rajasthan_voot_MOB/Fallback/News18_Rajasthan_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Rajasthan_voot_MOB'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7429/567429-h',
        "name": 'Star Suvarna',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540057075/57ae0b6fa2b64281984574d406f9a696/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=786fe347f558460398b9e42e1db50000:d630fb6469c3457e9d7c4bb863e1fef1',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057075'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/ETV_MP.png',
        "name": 'News18 MP Chhattisgarh',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_MP_Chhattisgarh_voot_MOB/Fallback/News18_MP_Chhattisgarh_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_MP_Chhattisgarh_voot_MOB'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/5868/595868-h',
        "name": 'Star Pravah',
        "url_template": 'https://livetv.hotstar.com/mp2/gec-india-1540057063/03a27d0f3ce347f0a3b4af1f6e62d4cc/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=9d300f38d30d4829b2e525a037560000:706572c4aac0420f90a778e22116b320',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057063'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/News_18_Kerala.png',
        "name": 'News18 Kerala',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_Kerala_voot_MOB/Fallback/News18_Kerala_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_Kerala_voot_MOB'
    },
    {
        "logo": 'http://jiotv.catchup.cdn.jio.com/dare_images/images/ETV_UP.png',
        "name": 'News18 UP Uttarakhand',
        "url_template": 'https://jcevents.hotstar.com/bpk-tv/News18_UP_Uttarakhand_voot_MOB/Fallback/News18_UP_Uttarakhand_voot_MOB.m3u8?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}',
        "type": 'm3u8_cookie',
        "stream_id": 'News18_UP_Uttarakhand_voot_MOB'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7424/567424-h',
        "name": 'Asianet Plus',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540057042/65edc0359d4b49f7a42d06d4dfe8457b/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=5f1a41f1f8c04e209dfcdfff2fdc0000:e0a5f3aa6afe414b902d6b729dd9b11b',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057042'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7419/567419-h',
        "name": 'Star Jalsha',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540057072/61b6b96b069d42f9821b6ed85b51388e/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=94b8e23444db4af3b81dc2840c930000:d7c43050ca6d4e1ab3a296c91a4bb38e',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057072'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7421/567421-h',
        "name": 'Star Maa Movies',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540057036/9b002b1b2a3748b7a80a8512aef0bb8d/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=18b7ece05d094614a3839978b9330000:267ba7674fbd4076bbf797eaa1dd16d0',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057036'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7420/567420-h',
        "name": 'Asianet',
        "url_template": 'https://livetv.hotstar.com/mp2/gec-india-1540057084/6569043a1d874fb49fc2cf2f273fe097/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=1dd2d0a48be14cc3a9666d861dd60000:24e889ab81444af0bceb8f8b9a530b18',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057084'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7415/567415-h',
        "name": 'StarPlus',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540057045/a73567ab8abd4680bc8206dd0c625cb0/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=17a6e6ef02f74d9bbce4640371d40000:7a89315d2ec84875901dce2d3044556c',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057045'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7409/567409-h',
        "name": 'Star Vijay',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540057060/15ef978ea9f449a2a8c97f7c05e618c5/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=652811d06b3545a3a1f20c1b03700000:d3db194166ee44b3b5c9c719aa9cdd63',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057060'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7407/567407-h',
        "name": 'Star Utsav',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540057078/6a9d9dbd5cd84dd3ba89856288c589b3/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=88f55cce9ba94df6b009f2433ef90000:6f33ae9e6fa24f95b82e538563b1cbaf',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057078'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7418/567418-h',
        "name": 'Star Maa',
        "url_template": 'https://livetv.hotstar.com/mp2/gec-india-1540057087/136d113eec07474e8836d7dc3dd0533b/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=b13dd22b45644e798457508fcdf70000:2c965c36ef5242f68a878952f993a591',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057087'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7406/567406-h',
        "name": 'Star Bharat',
        "url_template": 'https://livetv.hotstar.com/mp2/gec-india-1540057051/aa1fac3acfc244b4bbed73575a4a42da/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=4271050207424ba8b3e65c602d7e0000:8fdd910f634b40fdb5bfde551e08fd6c',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057051'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7403/567403-h',
        "name": 'Star Gold',
        "url_template": 'https://livetv.hotstar.com/mp2/gec-india-1540057030/0bbcb34798fd454a81c3502fb652911e/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=c3c8fd55071348e9992be759ceab0000:b894ad9ee2ad483fb2a5b71db0434bfc',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057030'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7404/567404-h',
        "name": 'Jalsha Movies',
        "url_template": 'https://livetv.hotstar.com/mp2/gec-india-1540057027/39127b380adb405e8de434e10e20c3a6/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=a515368ea6bc4d76a1aebc22f4660000:e46451b6cdae433ab6e719f39dcc449e',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057027'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7400/567400-h',
        "name": 'Asianet Movies',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540057039/96454b89b9cd49df822108b6975a1a60/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=53e552bf422a4feeb017e38ba43e0000:9cf91549836b4ce98e9d8137591dd38e',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057039'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7408/567408-h',
        "name": 'Maa Gold',
        "url_template": 'https://livetv.hotstar.com/mp1/gec-india-1540057033/9680ef02a23e4d05a7d6afab10805ec4/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=ab4cba34a7084eddbd6edf6a16460000:fd1cb8f19b2e42838d4ace714427ec76',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057033'
    },
    {
        "logo": 'https://img10.hotstar.com/image/upload/f_auto,q_90,w_1920/sources/r1/cms/prod/7399/567399-h',
        "name": 'Star Suvarna Plus',
        "url_template": 'https://livetv.hotstar.com/mp2/gec-india-1540057081/5c13f17d142c4963a1c7bd54fcd421d5/index.mpd?|User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com&Cookie=hdntl={HDNTL}&drmScheme=clearkey&drmLicense=ffcedf61e9544d1da7db98277a290000:cea7c92c93f04c6daaf31e2fda5e6809',
        "type": 'mpd_cookie',
        "stream_id": 'gec-india-1540057081'
    },
]


def option11_update_jhs(input_url: str = ""):
    """Option 11: Fetch fresh hdntl cookie from any Hotstar Live URL and
    regenerate all JHS channels with the updated cookie, then print and save."""
    # ── Step 1: Get URL if not provided ─────────────────── "�──────────
    if not input_url:
        input_url = input(f"{BOLD_CYAN}Enter any Hotstar Live TV URL (to fetch fresh cookie): {RESET}").strip()
    if not input_url:
        print(f"{RED}No URL provided. Aborting.{RESET}")
        return

    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid Hotstar URL!{RESET}")
        return

    # ── Step 2: Fetch fresh hdntl via DRM stream fetch ───────────────
    hdntl_new = ""

    try:
        drm_streams, _, _, _ = fetch_drm_info_for_slug(slug_path)
        for stream in drm_streams:
            mpd_url = stream.get("mpd_url", "")
            if mpd_url:
                hdntl_new = get_hdntl_token_4kads(mpd_url)
                if hdntl_new:
                    break
                hdntl_new = extract_hdntl(mpd_url)
                if hdntl_new:
                    break
    except Exception as e:
        print(f"{YELLOW}Warning: DRM fetch failed ({e}), trying direct token fetch...{RESET}")

    # Fallback: try JHS API
    if not hdntl_new:
        try:
            jhs_api = build_jhs_api_url(slug_path, "hin", is_live=True)
            jhs_req = request.Request(jhs_api, headers=build_jhs_headers_android())
            with request.urlopen(jhs_req, timeout=10) as r:
                jhs_data = json.loads(r.read().decode("utf-8"))
            for sec in jhs_data.get("success", {}).get("page", {}).get("spaces", {}).values():
                for ww in sec.get("widget_wrappers", []):
                    pc = ww.get("widget", {}).get("data", {}).get("player_config")
                    if pc:
                        streams = extract_jhs_fallback_only(pc)
                        for s in streams:
                            url = s.get("content_url", "")
                            if url:
                                hdntl_new = get_hdntl_token_4kads(url) or extract_hdntl(url)
                                if hdntl_new:
                                    break
                    if hdntl_new:
                        break
                if hdntl_new:
                    break
        except Exception as e:
            print(f"{YELLOW}JHS API fallback also failed: {e}{RESET}")

    if not hdntl_new:
        print(f"{RED}Could not fetch fresh hdntl cookie. Aborting.{RESET}")
        return

    # Show expiry from token
    exp_match = re.search(r"exp=(\d+)", hdntl_new)
    if exp_match:
        import datetime as _dt
        exp_ts = int(exp_match.group(1))
        exp_str = _dt.datetime.fromtimestamp(exp_ts).strftime("%Y-%m-%d %H:%M:%S")
        print(f"{GREEN}✓ Fresh cookie fetched! Expires: {exp_str}{RESET}")
    else:
        print(f"{GREEN}✓ Fresh cookie fetched!{RESET}")

    # ── Step 3: Build updated channel list lines ──────────────────────
    lines = []
    for ch in JHS_CHANNELS:
        final_url = ch["url_template"].replace("{HDNTL}", hdntl_new)
        lines.append("LOGO")
        lines.append(ch["logo"])
        lines.append(ch["name"])
        lines.append(final_url)
        lines.append("")

    output = "\n".join(lines).rstrip() + "\n"

    # ── Print all channels directly ───────────────────────────────────
    print(f"{BOLD_CYAN}ALL JHS CHANNELS{RESET}\n")
    for ch in JHS_CHANNELS:
        final_url = ch["url_template"].replace("{HDNTL}", hdntl_new)
        print(f"{BOLD_RED}LOGO{RESET}\n{ch['logo']}")
        print(f"{BOLD_GREEN}{ch['name']}{RESET}")
        print(f"{WHITE}{final_url}{RESET}")

    # ── Step 4: Ask to save jhs.txt at the end ────────────────────────
    save_ans = input(f"\n{BOLD_YELLOW}Save jhs.txt? (y/n): {RESET}").strip().lower()
    if save_ans == "y":
        out_file = input(f"Filename (default: jhs.txt): ").strip()
        if not out_file:
            out_file = "jhs.txt"
        try:
            with open(out_file, "w", encoding="utf-8") as fw:
                fw.write(output)
            print(f"{GREEN}✓ Saved {len(JHS_CHANNELS)} channels to: {out_file}{RESET}")
        except Exception as e:
            print(f"{RED}Failed to save: {e}{RESET}")

def get_global_hdntl_token() -> str:
    """
    Fetch token using the exact same method as Option 9.
    Uses the same default URL that Option 9 uses internally.
    Returns wide-scope token (acl=%2f*) or empty string.
    """
    # Option 9's default URL (same as in main menu)
    default_url = "https://www.hotstar.com/in/tv/star-sports-hindi-1/1260000025/live/watch"
    slug_path = extract_slug_path(default_url)
    if not slug_path:
        return ""
    
    # Use the same DRM fetch that Option 9 uses via option11_update_jhs
    try:
        drm_streams, _, _, _ = fetch_drm_info_for_slug(slug_path)
        for stream in drm_streams:
            mpd_url = stream.get("mpd_url", "")
            if not mpd_url:
                continue
            token = get_hdntl_token_4kads(mpd_url)
            if token:
                return token
            token = extract_hdntl(mpd_url)
            if token:
                return token
    except Exception as e:
        print(f"{YELLOW}DRM fetch error: {e}{RESET}")
    
    # Fallback: try to get token from any JHS channel (like option 9 fallback)
    try:
        jhs_api = build_jhs_api_url(slug_path, "hin", is_live=True)
        jhs_req = request.Request(jhs_api, headers=build_jhs_headers_android())
        with request.urlopen(jhs_req, timeout=10) as r:
            jhs_data = json.loads(r.read().decode("utf-8"))
        for sec in jhs_data.get("success", {}).get("page", {}).get("spaces", {}).values():
            for ww in sec.get("widget_wrappers", []):
                pc = ww.get("widget", {}).get("data", {}).get("player_config")
                if pc:
                    streams = extract_jhs_fallback_only(pc)
                    for s in streams:
                        url = s.get("content_url", "")
                        if url:
                            token = get_hdntl_token_4kads(url) or extract_hdntl(url)
                            if token:
                                return token
    except Exception as e:
        print(f"{YELLOW}JHS fallback error: {e}{RESET}")
    
    return ""

def append_headers_to_url(base_url: str, token: str) -> str:
    """Append User-Agent, Referer, Origin to the URL."""
    ua = "User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)"
    ref = "Referer=https://www.hotstar.com/"
    org = "Origin=https://www.hotstar.com"
    # Check if already has '?' or we need to add
    if '?' in base_url:
        return f"{base_url}&{ua}&{ref}&{org}"
    else:
        return f"{base_url}?{ua}&{ref}&{org}"

DESIRED_CDN_HOSTS = [f"live{i:02d}.hotstar.com" for i in range(1, 100)]

def get_working_cdn_host(raw_url: str) -> str:
    """
    Option 5 ke logic se working liveXX.hotstar.com host find karega.
    Returns: hostname like 'live07.hotstar.com'
    """
    parsed = urlparse(raw_url)
    for host in DESIRED_CDN_HOSTS:
        test_url = parsed._replace(netloc=host).geturl()
        if is_working_url_4kads(test_url):   # Option 5 ka working check
            return host
    # Agar koi bhi kaam nahi kiya to default live07
    return "live07.hotstar.com"

def option14_jio_fallback_24h(input_url: str):
    """Option 14: TattiJio & Chortel users FALLBACK – saari languages fetch (jaise Option 2), phir global token + working CDN + headers."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL.{RESET}")
        return

    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)

    print(f"{BOLD_RED}24-HOURS STREAMS LINKS{RESET}\n")
    global_token = get_global_hdntl_token()
    if not global_token:
        print(f"{RED}Failed to get global token. Aborting.{RESET}")
        return
    exp_match = re.search(r"exp=(\d+)", global_token)
    if exp_match:
        exp_str = datetime.fromtimestamp(int(exp_match.group(1))).strftime("%Y-%m-%d %H:%M:%S")
        print(f"{GREEN}✓ Token fetched, expires at {exp_str}{RESET}")
    else:
        print(f"{GREEN}✓ Token fetched{RESET}")

    # ---- Logo fetch ----
    logo_url = ""
    try:
        api_test = build_api_url(slug_path, "eng", "2")
        req_logo = request.Request(api_test, headers=build_headers())
        with request.urlopen(req_logo, timeout=10) as r:
            d = json.loads(r.read().decode("utf-8"))
        for sec in d.get("success", {}).get("page", {}).get("spaces", {}).values():
            for w in sec.get("widget_wrappers", []):
                pc = w.get("widget", {}).get("data", {}).get("player_config")
                if pc:
                    img = pc.get("expanded_content_poster", {}).get("image", {}).get("src") or pc.get("cast_image", {}).get("src")
                    if img:
                        logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                    break
            if logo_url:
                break
    except:
        pass

    print(f"{BOLD_RED}LOGO{RESET}")
    if logo_url:
        print(logo_url)
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print(f"{BOLD_GREEN}{title}{RESET}")
    print(f"{BOLD_MAGENTA}{stream_type}{RESET}")

    # ---- Saari languages fetch karo (quality "2") ----
    lang_streams = {}
    seen_bases = set()
    with ThreadPoolExecutor(max_workers=2) as ex:  # RATE LIMIT: 6→2
        futures = {
            ex.submit(fetch_lang_stream, code, name, slug_path, input_url, "2"): name
            for code, name in UNIQUE_LANGUAGES.items()
        }
        for future in as_completed(futures):
            res = future.result()
            if not res:
                continue
            lang_name = res["lang_name"]
            raw_url = res["stream"]
            base = raw_url.split("?")[0]
            if base in seen_bases:
                continue
            seen_bases.add(base)
            lang_streams[lang_name] = (raw_url, res.get("is_hdr", False))

    if not lang_streams:
        print(f"{RED}No streams found via normal API.{RESET}")
        return

    # ---- CDN replace, token attach, and headers add ----
    results = {}
    lock = threading.Lock()

    def build_final_url(raw_url: str) -> str:
        # Option 5 style: working CDN host find karo
        working_host = get_working_cdn_host(raw_url)
        parsed = urlparse(raw_url)
        # Host replace karo
        converted = parsed._replace(netloc=working_host).geturl()
        base = converted.split("?")[0]   # saare query params hatao
        token_part = f"a=ns&ttl=86400&hdnea={global_token}|Cookie=hdntl={global_token}"
        headers_part = f"&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com"
        return f"{base}?{token_part}{headers_part}"

    # Language verification
    for lang_name, (raw_url, is_hdr) in lang_streams.items():
        url_path = raw_url.split("?")[0].lower()
        lang_codes = [code for code, name in LANGUAGES.items() if name == lang_name]
        if not any(f"/{c}/" in url_path for c in lang_codes):
            continue
        final_url = build_final_url(raw_url)
        results[lang_name] = (final_url, is_hdr)

    if not results:
        for lang_name, (raw_url, is_hdr) in lang_streams.items():
            results[lang_name] = (build_final_url(raw_url), is_hdr)

    # Output
    entries = []
    seen_base = set()
    lang_order = ["ENGLISH","HINDI","MARATHI","GUJARATI","BHOJPURI","PUNJABI",
                  "HARYANVI","TAMIL","TELUGU","KANNADA","MALAYALAM","BENGALI"]
    for lang_name in lang_order:
        if lang_name not in results:
            continue
        url, is_hdr = results[lang_name]
        base = url.split("?")[0]
        if base in seen_base:
            continue
        seen_base.add(base)
        hdr_tag = " HDR" if is_hdr else ""
        print(f"{BOLD_CYAN}{lang_name}{hdr_tag}{RESET}")
        print(f"{GREEN}{url}{RESET}")
        entries.append((lang_name, url, is_hdr))

    print(f"\n{BOLD_GREEN}GLOBAL COOKIE:{RESET}\n{CYAN}hdntl={global_token}{RESET}")
    offer_m3u_creation(entries, title, match_no, stream_type, logo_url, auto_hdntl=global_token)

def option15_jio_primary_24h(input_url: str):
    """Option 15: TattiJio & Chortel users PRIMARY – Option-9 style global token + working CDN + headers."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL.{RESET}")
        return

    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)

    print(f"{BOLD_RED}24-HOURS STREAMS LINKS{RESET}\n")
    global_token = get_global_hdntl_token()
    if not global_token:
        print(f"{RED}Failed to get global token. Aborting.{RESET}")
        return
    exp_match = re.search(r"exp=(\d+)", global_token)
    if exp_match:
        exp_str = datetime.fromtimestamp(int(exp_match.group(1))).strftime("%Y-%m-%d %H:%M:%S")
        print(f"{GREEN}✓ Token fetched, expires at {exp_str}{RESET}")
    else:
        print(f"{GREEN}✓ Token fetched{RESET}")

    print(f"\n{BOLD_BLUE}=== OPTION 15: PRIMARY 24-HOURS TattiJio & Chortel users ==={RESET}\n")

    # Logo fetch
    logo_url = ""
    try:
        api_test = build_api_url(slug_path, "eng", "1")
        req_logo = request.Request(api_test, headers=build_headers())
        with request.urlopen(req_logo, timeout=10) as r:
            d = json.loads(r.read().decode("utf-8"))
        for sec in d.get("success", {}).get("page", {}).get("spaces", {}).values():
            for w in sec.get("widget_wrappers", []):
                pc = w.get("widget", {}).get("data", {}).get("player_config")
                if pc:
                    img = pc.get("expanded_content_poster", {}).get("image", {}).get("src") or pc.get("cast_image", {}).get("src")
                    if img:
                        logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                    break
            if logo_url:
                break
    except:
        pass

    print(f"{BOLD_RED}LOGO{RESET}")
    if logo_url:
        print(logo_url)
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print(f"{BOLD_GREEN}{title}{RESET}")
    print(f"{BOLD_MAGENTA}{stream_type}{RESET}")

    # Fetch primary streams (quality "1")
    lang_streams = {}
    seen_bases = set()
    with ThreadPoolExecutor(max_workers=2) as ex:  # RATE LIMIT: 6→2
        futures = {
            ex.submit(fetch_lang_stream, code, name, slug_path, input_url, "1"): name
            for code, name in UNIQUE_LANGUAGES.items()
        }
        for future in as_completed(futures):
            res = future.result()
            if not res:
                continue
            lang_name = res["lang_name"]
            raw_url = res["stream"]
            base = raw_url.split("?")[0]
            if base in seen_bases:
                continue
            seen_bases.add(base)
            lang_streams[lang_name] = (raw_url, res.get("is_hdr", False))

    if not lang_streams:
        print(f"{RED}No primary streams found. Try Option 14 (fallback).{RESET}")
        return

    results = {}
    lock = threading.Lock()

    def build_final_url(raw_url: str) -> str:
        # Option 5 style: working CDN host find karo
        working_host = get_working_cdn_host(raw_url)
        parsed = urlparse(raw_url)
        # Host replace karo
        converted = parsed._replace(netloc=working_host).geturl()
        base = converted.split("?")[0]   # saare query params hatao
        token_part = f"a=ns&ttl=86400&hdnea={global_token}|Cookie=hdntl={global_token}"
        headers_part = f"&User-Agent=Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)&Referer=https://www.hotstar.com/&Origin=https://www.hotstar.com"
        return f"{base}?{token_part}{headers_part}"

    for lang_name, (raw_url, is_hdr) in lang_streams.items():
        url_path = raw_url.split("?")[0].lower()
        lang_codes = [code for code, name in LANGUAGES.items() if name == lang_name]
        if not any(f"/{c}/" in url_path for c in lang_codes):
            continue
        final_url = build_final_url(raw_url)
        results[lang_name] = (final_url, is_hdr)

    if not results:
        for lang_name, (raw_url, is_hdr) in lang_streams.items():
            results[lang_name] = (build_final_url(raw_url), is_hdr)

    entries = []
    seen_base = set()
    lang_order = ["ENGLISH","HINDI","MARATHI","GUJARATI","BHOJPURI","PUNJABI",
                  "HARYANVI","TAMIL","TELUGU","KANNADA","MALAYALAM","BENGALI"]
    for lang_name in lang_order:
        if lang_name not in results:
            continue
        url, is_hdr = results[lang_name]
        base = url.split("?")[0]
        if base in seen_base:
            continue
        seen_base.add(base)
        hdr_tag = " HDR" if is_hdr else ""
        print(f"{BOLD_CYAN}{lang_name}{hdr_tag}{RESET}")
        print(f"{GREEN}{url}{RESET}")
        entries.append((lang_name, url, is_hdr))

    print(f"\n{BOLD_GREEN}GLOBAL COOKIE:{RESET}\n{CYAN}hdntl={global_token}{RESET}")
    offer_m3u_creation(entries, title, match_no, stream_type, logo_url, auto_hdntl=global_token)


# ===================== HOTSTAR COOKIES CHECKER (FAST EDITION) =====================

import asyncio
import base64 as _b64
import zipfile
import tarfile
import shutil

# ── Token extractors ──────────────────────────────────────────────────────────

# Cookie names that hold the Hotstar auth token in browser-exported JSON cookie files
_HS_AUTH_COOKIE_NAMES = {
    "userup", "sessionuserup",
    "usertoken", "x-hs-usertoken", "hs-token",
    "sub", "ut",
}

def _extract_from_browser_cookie_list(items: list) -> list:
    """
    Handle browser-exported cookie arrays: [{name, value, domain, ...}, ...]
    Only extract 'value' when 'name' is a known Hotstar auth cookie name.
    Returns [] if the list doesn't look like browser cookie objects.
    """
    tokens = []
    is_browser_format = any(
        isinstance(item, dict) and "name" in item and "value" in item
        for item in items
    )
    if not is_browser_format:
        return []
    for item in items:
        if not isinstance(item, dict):
            continue
        cname = str(item.get("name", "")).lower()
        cval = item.get("value", "")
        if cname in _HS_AUTH_COOKIE_NAMES and isinstance(cval, str) and len(cval) > 20:
            tokens.append(cval.strip())
    return tokens

def _extract_tokens_from_text(text: str) -> list:
    tokens = []

    # First: try to parse the whole content as JSON (handles .txt files that
    # actually contain a JSON array of browser-exported cookie objects)
    stripped = text.strip()
    if stripped.startswith("[") or stripped.startswith("{"):
        try:
            json_tokens = _extract_tokens_from_json(stripped)
            if json_tokens:
                return json_tokens
        except Exception:
            pass

    # Fallback: line-by-line scan
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("{"):
            try:
                obj = json.loads(line)
                for k in ("usertoken", "x-hs-usertoken", "token", "cookie", "ut", "value"):
                    if k in obj and isinstance(obj[k], str) and len(obj[k]) > 20:
                        tokens.append(obj[k].strip())
                        break
            except Exception:
                pass
            continue
        if "\t" in line:
            parts = line.split("\t")
            if len(parts) >= 7:
                name = parts[5].strip().lower()
                value = parts[6].strip()
                if name in ("usertoken", "hs-usertoken", "sub", "ut") and len(value) > 20:
                    tokens.append(value)
                    continue
            last = parts[-1].strip()
            if len(last) > 80:
                tokens.append(last)
            continue
        if len(line) > 20 and " " not in line:
            tokens.append(line)
    return tokens

def _extract_tokens_from_json(text: str) -> list:
    tokens = []
    try:
        obj = json.loads(text)
        if isinstance(obj, list):
            # Try browser-cookie-array format first (name+value objects)
            browser_toks = _extract_from_browser_cookie_list(obj)
            if browser_toks:
                return browser_toks
            # Plain list of strings or generic dicts
            for item in obj:
                if isinstance(item, str) and len(item) > 20:
                    tokens.append(item.strip())
                elif isinstance(item, dict):
                    for k in ("usertoken", "x-hs-usertoken", "token", "cookie", "ut", "value"):
                        v = item.get(k, "")
                        if isinstance(v, str) and len(v) > 20:
                            tokens.append(v.strip())
                            break
        elif isinstance(obj, dict):
            for k in ("usertoken", "x-hs-usertoken", "token", "cookie", "ut"):
                v = obj.get(k, "")
                if isinstance(v, str) and len(v) > 20:
                    tokens.append(v.strip())
                    break
            for k, v in obj.items():
                if isinstance(v, list):
                    # Nested browser cookie list?
                    browser_toks = _extract_from_browser_cookie_list(v)
                    if browser_toks:
                        tokens.extend(browser_toks)
                        continue
                    for item in v:
                        if isinstance(item, str) and len(item) > 20:
                            tokens.append(item.strip())
                        elif isinstance(item, dict):
                            for ck in ("usertoken", "token", "cookie", "value", "ut"):
                                cv = item.get(ck, "")
                                if isinstance(cv, str) and len(cv) > 20:
                                    tokens.append(cv.strip())
                                    break
    except Exception:
        pass
    return tokens

def _process_file_for_tokens(fpath: str, tokens_out: list):
    ext = os.path.splitext(fpath)[1].lower()
    try:
        if ext == ".zip":
            with zipfile.ZipFile(fpath, "r") as zf:
                for name in zf.namelist():
                    ne = os.path.splitext(name)[1].lower()
                    if ne in (".txt", ".json", ""):
                        try:
                            content = zf.read(name).decode("utf-8", errors="ignore")
                            if ne == ".json":
                                tokens_out.extend(_extract_tokens_from_json(content))
                            else:
                                tokens_out.extend(_extract_tokens_from_text(content))
                        except Exception:
                            pass
        elif ext in (".tar", ".gz", ".bz2", ".xz"):
            try:
                with tarfile.open(fpath, "r:*") as tf:
                    for member in tf.getmembers():
                        ne = os.path.splitext(member.name)[1].lower()
                        if ne in (".txt", ".json", ""):
                            try:
                                f = tf.extractfile(member)
                                if f:
                                    content = f.read().decode("utf-8", errors="ignore")
                                    if ne == ".json":
                                        tokens_out.extend(_extract_tokens_from_json(content))
                                    else:
                                        tokens_out.extend(_extract_tokens_from_text(content))
                            except Exception:
                                pass
            except Exception:
                pass
        elif ext in (".7z", ".rar"):
            tmpdir = f"/tmp/hs_ck_{uuid.uuid4().hex[:8]}"
            os.makedirs(tmpdir, exist_ok=True)
            try:
                if ext == ".7z":
                    cmd = ["7z", "e", fpath, f"-o{tmpdir}", "-y", "-bd"]
                else:
                    cmd = ["unrar", "e", "-y", fpath, tmpdir + "/"]
                subprocess.run(cmd, capture_output=True, timeout=60)
                for root, _, files in os.walk(tmpdir):
                    for fname in files:
                        _process_file_for_tokens(os.path.join(root, fname), tokens_out)
            except Exception:
                pass
            finally:
                shutil.rmtree(tmpdir, ignore_errors=True)
        elif ext == ".json":
            with open(fpath, "r", encoding="utf-8", errors="ignore") as f:
                tokens_out.extend(_extract_tokens_from_json(f.read()))
        else:
            with open(fpath, "r", encoding="utf-8", errors="ignore") as f:
                tokens_out.extend(_extract_tokens_from_text(f.read()))
    except Exception:
        pass

def _collect_tokens_from_path(path: str, raw_count_out: list = None) -> list:
    tokens = []
    SUPPORTED_EXTS = {".txt", ".json", ".zip", ".7z", ".rar", ".tar", ".gz", ".bz2", ""}
    if os.path.isdir(path):
        for root, _, files in os.walk(path):
            for fname in files:
                ext = os.path.splitext(fname)[1].lower()
                if ext in SUPPORTED_EXTS:
                    _process_file_for_tokens(os.path.join(root, fname), tokens)
    else:
        _process_file_for_tokens(path, tokens)
    if raw_count_out is not None:
        raw_count_out.append(len(tokens))
    seen = set()
    result = []
    for t in tokens:
        if t and t not in seen:
            seen.add(t)
            result.append(t)
    return result

# ── Plan-type extraction from filename & folder-aware token collection ─────────

# Maps raw plan strings (lowercase) from filenames → clean folder names
_PLAN_FOLDER_MAP = {
    "hotstar bundle": "HotstarBundle",
    "hotstar_bundle": "HotstarBundle",
    "hotstarbundle": "HotstarBundle",
    "hotstar super": "HotstarSuper",
    "hotstar_super": "HotstarSuper",
    "hotstarsuper": "HotstarSuper",
    "jhsmobilelite": "JHSMobileLite",
    "jhs mobile lite": "JHSMobileLite",
    "jhs_mobile_lite": "JHSMobileLite",
    "mobile plan": "MobilePlan",
    "mobile_plan": "MobilePlan",
    "mobileplan": "MobilePlan",
    "premium annual plan": "Premium_Annual_Plan",
    "premium_annual_plan": "Premium_Annual_Plan",
    "premiumannualplan": "Premium_Annual_Plan",
    "hotstar premium": "Premium_Annual_Plan",
    "hotstar_premium": "Premium_Annual_Plan",
    "hotstar premiumsmp": "Premium_Annual_Plan",
    "hotstar_premiumsmp": "Premium_Annual_Plan",
    "hotstarpremiungsmp": "Premium_Annual_Plan",
    "hotstarpremiumsmp": "Premium_Annual_Plan",
    "hotstar premiersmp": "Premium_Annual_Plan",
    "hotstar premieresmp": "Premium_Annual_Plan",
    "hotstarpremiersmp": "Premium_Annual_Plan",
    "single device": "Single_Device_Plan",
    "single_device": "Single_Device_Plan",
    "singledevice": "Single_Device_Plan",
    "single device plan": "Single_Device_Plan",
    "single_device_plan": "Single_Device_Plan",
    "singledeviceplan": "Single_Device_Plan",
}

def _normalize_plan_folder(raw: str) -> str:
    """Map raw plan name from filename to a clean folder name."""
    if not raw:
        return "Other"
    key = raw.lower().strip()
    return _PLAN_FOLDER_MAP.get(key, raw)

def _extract_plan_from_filename(fname: str) -> str:
    """
    Extract plan type from Hotstar cookie filename.
    Expected pattern: [Name]-[PlanType]-[Date]...
    Returns the second bracket value, e.g. 'JHSMobileLite', 'HotstarSuper'.
    """
    basename = os.path.basename(fname)
    parts = re.findall(r'\[([^\]]+)\]', basename)
    if len(parts) >= 2:
        return parts[1].strip()
    return ""

def _collect_tokens_with_plans(path: str) -> dict:
    """
    Walk path (file or folder/zip/rar/7z) and return {token: plan_folder_name}.
    Plan priority:
      1. Bracket pattern in the individual file's name: [Name]-[PlanType]-[Date]
      2. Bracket pattern in the parent zip/folder name (same pattern)
      3. The zip/folder/file's own basename (no extension) — used as-is
    Tokens whose source name truly has no usable label go to 'Other'.
    """
    token_plan = {}
    SUPPORTED_EXTS = {".txt", ".json", ".zip", ".7z", ".rar", ".tar", ".gz", ".bz2", ""}

    def _path_fallback(fpath: str) -> str:
        """Best-effort plan name: bracket pattern first, then bare basename."""
        from_bracket = _extract_plan_from_filename(fpath)
        if from_bracket:
            return from_bracket
        base = os.path.splitext(os.path.basename(fpath.rstrip("/\\")))[0]
        return base if base else ""

    def _add(toks, plan_raw):
        folder = _normalize_plan_folder(plan_raw) if plan_raw else "Other"
        for t in toks:
            if t and t not in token_plan:
                token_plan[t] = folder

    def _handle_zip(fpath, fallback_plan=""):
        try:
            with zipfile.ZipFile(fpath, "r") as zf:
                for zname in zf.namelist():
                    ne = os.path.splitext(zname)[1].lower()
                    if ne in (".txt", ".json", ""):
                        zplan = _extract_plan_from_filename(zname) or fallback_plan
                        try:
                            content = zf.read(zname).decode("utf-8", errors="ignore")
                            toks = (_extract_tokens_from_json(content) if ne == ".json"
                                    else _extract_tokens_from_text(content))
                            _add(toks, zplan)
                        except Exception:
                            pass
        except Exception:
            toks = []
            _process_file_for_tokens(fpath, toks)
            _add(toks, fallback_plan)

    def _handle_archive(fpath, fallback_plan=""):
        ext = os.path.splitext(fpath)[1].lower()
        tmpdir = f"/tmp/hs_plan_{uuid.uuid4().hex[:8]}"
        os.makedirs(tmpdir, exist_ok=True)
        try:
            if ext == ".7z":
                cmd = ["7z", "e", fpath, f"-o{tmpdir}", "-y", "-bd"]
            else:
                cmd = ["unrar", "e", "-y", fpath, tmpdir + "/"]
            subprocess.run(cmd, capture_output=True, timeout=60)
            for r, _, files in os.walk(tmpdir):
                for fname in files:
                    fp = os.path.join(r, fname)
                    plan = _extract_plan_from_filename(fname) or fallback_plan
                    toks = []
                    _process_file_for_tokens(fp, toks)
                    _add(toks, plan)
        except Exception:
            pass
        finally:
            shutil.rmtree(tmpdir, ignore_errors=True)

    if os.path.isdir(path):
        dir_fallback = _path_fallback(path)
        for root, _, files in os.walk(path):
            for fname in sorted(files):
                ext = os.path.splitext(fname)[1].lower()
                if ext not in SUPPORTED_EXTS:
                    continue
                fpath = os.path.join(root, fname)
                plan = _extract_plan_from_filename(fname) or dir_fallback
                if ext == ".zip":
                    _handle_zip(fpath, plan or _path_fallback(fpath))
                elif ext in (".7z", ".rar"):
                    _handle_archive(fpath, plan or _path_fallback(fpath))
                else:
                    toks = []
                    _process_file_for_tokens(fpath, toks)
                    _add(toks, plan)
    else:
        ext = os.path.splitext(path)[1].lower()
        base_plan = _path_fallback(path)
        if ext == ".zip":
            _handle_zip(path, base_plan)
        elif ext in (".7z", ".rar"):
            _handle_archive(path, base_plan)
        else:
            toks = []
            _process_file_for_tokens(path, toks)
            _add(toks, base_plan)

    return token_plan

# ── JWT instant check (no HTTP) ───────────────────────────────────────────────

def _decode_jwt_payload(token: str) -> dict:
    """Decode JWT payload without verifying signature. Returns {} on failure."""
    try:
        parts = token.split(".")
        if len(parts) != 3:
            return {}
        payload_b64 = parts[1]
        payload_b64 += "=" * (-len(payload_b64) % 4)
        return json.loads(_b64.urlsafe_b64decode(payload_b64).decode("utf-8"))
    except Exception:
        return {}

def _jwt_instant_check(token: str):
    """Returns (is_valid, plan) for a Hotstar JWT, or None if not a Hotstar JWT.

    Returns None for:
      - Non-eyJ tokens
      - Tokens whose payload can't be decoded
      - Tokens that look like Firebase/Google JWTs (no Hotstar uid/sub fields)
    These fall through to HTTP check.
    """
    if not token.startswith("eyJ"):
        return None
    payload = _decode_jwt_payload(token)
    if not payload:
        return None  # undecodable → HTTP check

    # Must be a Hotstar user token: needs uid or a sub with Hotstar fields
    uid = payload.get("uid") or payload.get("userId") or payload.get("user_id")
    sub_raw = payload.get("sub", "")
    sub_data: dict = {}
    if isinstance(sub_raw, str):
        try:
            sub_data = json.loads(sub_raw)
        except Exception:
            pass
    elif isinstance(sub_raw, dict):
        sub_data = sub_raw

    # Check if this is actually a Hotstar token
    iss = str(payload.get("iss", "")).lower()
    is_hotstar = bool(
        uid or
        sub_data.get("uid") or sub_data.get("subscriptionType") or
        sub_data.get("ut") or sub_data.get("userType") or
        "hotstar" in iss or iss in ("hs", "hotstar")
    )
    if not is_hotstar:
        return None  # Firebase/Google/other JWT → HTTP check

    # Check expiry
    exp = payload.get("exp", 0)
    if exp and int(exp) < int(time.time()):
        return (False, "EXPIRED")

    ut = (sub_data.get("subscriptionType") or sub_data.get("ut") or
          sub_data.get("userType") or sub_data.get("subscription_type") or
          payload.get("subscriptionType") or "")
    return (True, str(ut).upper() if ut else "FREE")

# ── Async checker (aiohttp) ───────────────────────────────────────────────────
#
# Check strategy:
#  1. JWT instant (no HTTP) — Hotstar-specific JWTs only
#  2. Home page API (PRIMARY — most reliable, definitive 401/200)
#  3. Subscriptions endpoint (for plan label, if home page confirmed valid)
#  4. Live event watch API (only if slug available, for PAID detection)
#
# Concurrency = 10; token sent as BOTH x-hs-usertoken AND Cookie header

_CK_SUBS_URL  = "https://www.hotstar.com/api/internal/bff/v2/user/subscriptions"
_CK_HOME_URL  = "https://www.hotstar.com/api/internal/bff/v2/pages/home?lang=eng"
_CK_PROF_URL  = "https://www.hotstar.com/api/internal/bff/v2/pages/profile?lang=eng"

# Populated at runtime by _calibrate_check_url()
_CALIBRATED_URL: list = [None]

def _make_check_headers(token: str) -> dict:
    """Build request headers that work for both app-style and web-style auth."""
    hdrs = HEADERS_BASE.copy()
    # Send token as both the app header AND a web cookie — Hotstar checks either
    hdrs["x-hs-usertoken"] = token
    hdrs["Cookie"] = f"usertoken={token}"
    return hdrs

async def _calibrate_check_url(session) -> str:
    """
    Try candidate URLs with a FAKE token. The first one returning 401/403
    is reliable for auth checking. Returns "" if none work (all public).
    """
    import aiohttp
    DUMMY = "invalid_hotstar_token_calibrate_xyz_12345"
    TO = aiohttp.ClientTimeout(total=6)
    candidates = [_CK_SUBS_URL, _CK_PROF_URL, _CK_HOME_URL]
    test_hdrs = _make_check_headers(DUMMY)
    for url in candidates:
        try:
            async with session.get(url, headers=test_hdrs, timeout=TO, ssl=False) as resp:
                if resp.status in (401, 403):
                    return url
        except Exception:
            pass
    return ""  # no URL returns 401 for fake token

def _extract_plan_from_json(data: dict) -> str:
    """Pull subscription/plan type out of any Hotstar API JSON response."""
    for root in (data.get("success") or {}, data.get("data") or {}, data):
        if not isinstance(root, dict):
            continue
        plan = (root.get("subscriptionType") or root.get("planName") or
                root.get("userType") or root.get("ut") or "")
        if plan:
            return str(plan).upper()
        sub_list = root.get("subscriptions") or root.get("items") or []
        if isinstance(sub_list, list) and sub_list:
            first = sub_list[0] if isinstance(sub_list[0], dict) else {}
            plan = first.get("subscriptionType") or first.get("planName") or ""
            if plan:
                return str(plan).upper()
    return ""

# Plan type map — normalize raw JWT/API values to readable labels
_PLAN_MAP = {
    "svod": "PREMIUM", "paid": "PREMIUM", "premium": "PREMIUM",
    "annual": "PREMIUM", "monthly": "PREMIUM",
    "avod": "FREE", "free": "FREE", "anonymous": "FREE",
    "mvpd": "TV PROVIDER", "tvprovider": "TV PROVIDER",
    "trial": "TRIAL",
}

def _plan_from_token(token: str, api_plan: str = "") -> str:
    """
    Get the best plan label for a WORKING cookie.
    Priority: API response plan > JWT payload > api_plan fallback.
    """
    # If API already gave us something meaningful (not just "VALID")
    if api_plan and api_plan not in ("VALID", ""):
        mapped = _PLAN_MAP.get(api_plan.lower(), api_plan.upper())
        return mapped

    # Try decoding JWT payload
    if token.startswith("eyJ"):
        try:
            payload = _decode_jwt_payload(token)
            if payload:
                # Try sub JSON field
                sub_raw = payload.get("sub", "")
                sub_d: dict = {}
                if isinstance(sub_raw, str):
                    try:
                        sub_d = json.loads(sub_raw)
                    except Exception:
                        pass
                elif isinstance(sub_raw, dict):
                    sub_d = sub_raw

                raw = (sub_d.get("subscriptionType") or sub_d.get("ut") or
                       sub_d.get("userType") or sub_d.get("subscription_type") or
                       payload.get("subscriptionType") or payload.get("ut") or
                       payload.get("userType") or "")
                if raw:
                    mapped = _PLAN_MAP.get(str(raw).lower(), str(raw).upper())
                    return mapped
        except Exception:
            pass

    return api_plan if api_plan else "VALID"

async def _async_check_one_ck(session, token: str, semaphore, test_slug_val: str) -> tuple:
    """Async single-cookie check. Returns (orig, is_valid, plan).

    Strategy (most-reliable-first):
      1. JWT instant check (no HTTP) — Hotstar JWTs only
      2. Home page (PRIMARY) — definitive 401/403=invalid, 200+success=valid
      3. Subscriptions endpoint — extract plan label when home confirms valid
      4. Live event watch API — detect PAID plan when slug available
    """
    import aiohttp
    orig = token
    if "%" in token:
        token = unquote(token)

    if "=" in token and not token.startswith("eyJ"):
        for cn in ("usertoken", "x-hs-usertoken", "hs-token", "sub", "ut"):
            if token.lower().startswith(cn + "="):
                token = token.split("=", 1)[1]
                break

    # ── 1. Hotstar JWT instant (no HTTP) ─────────────────────────────────────
    jwt = _jwt_instant_check(token)
    if jwt is not None:
        return (orig, jwt[0], jwt[1])

    hdrs = _make_check_headers(token)
    TO = aiohttp.ClientTimeout(total=12)

    async with semaphore:
        # ── 2. Home page (PRIMARY — most reliable) ────────────────────────────
        # This is the definitive check. 401/403 = definitely invalid.
        # 200+success = definitely valid. 429/timeout = uncertain (retry).
        try:
            async with session.get(_CK_HOME_URL, headers=hdrs, timeout=TO, ssl=False) as resp:
                hp_status = resp.status
                if hp_status in (401, 403):
                    return (orig, False, "")          # definitely invalid
                if hp_status in (429, 500, 502, 503, 504):
                    return (orig, None, "")           # rate-limited → retry
                if hp_status != 200:
                    return (orig, None, "")           # unknown → retry
                try:
                    hp_data = await resp.json(content_type=None)
                except Exception:
                    hp_data = json.loads((await resp.read()).decode("utf-8", errors="ignore"))
        except asyncio.CancelledError:
            raise
        except Exception:
            return (orig, None, "")  # timeout/network → retry

        hp_success = hp_data.get("success")
        if not hp_success:
            return (orig, False, "")  # 200 but no success payload → invalid

        # Home page confirmed valid — try to get a better plan label
        plan = _extract_plan_from_json(hp_data) or "VALID"

        # ── 3. Subscriptions endpoint (plan label enrichment) ─────────────────
        subs_url = _CALIBRATED_URL[0] or _CK_SUBS_URL
        try:
            async with session.get(subs_url, headers=hdrs, timeout=TO, ssl=False) as resp:
                if resp.status == 200:
                    try:
                        subs_data = await resp.json(content_type=None)
                    except Exception:
                        subs_data = json.loads((await resp.read()).decode("utf-8", errors="ignore"))
                    subs_plan = _extract_plan_from_json(subs_data)
                    if subs_plan:
                        plan = subs_plan
        except asyncio.CancelledError:
            raise
        except Exception:
            pass  # enrichment failed — keep home page plan label

        # ── 4. Live event watch API (PAID detection) ──────────────────────────
        if test_slug_val:
            try:
                api_url = build_jhs_api_url(test_slug_val, "eng", is_live=True)
                async with session.get(api_url, headers=hdrs, timeout=TO, ssl=False) as resp:
                    if resp.status == 200:
                        try:
                            le_data = await resp.json(content_type=None)
                        except Exception:
                            le_data = json.loads((await resp.read()).decode("utf-8", errors="ignore"))
                        spaces = (le_data.get("success") or {}).get("page", {}).get("spaces", {})
                        for space in spaces.values():
                            for wrapper in (space.get("widget_wrappers") or []):
                                pc = (wrapper.get("widget") or {}).get("data", {}).get("player_config")
                                if pc:
                                    plan = "PAID"
                                    break
            except asyncio.CancelledError:
                raise
            except Exception:
                pass  # live event check optional — ignore errors

        return (orig, True, plan)

async def _run_async_ck(tokens: list, test_slug_val: str, total: int,
                        working: list, lock_obj, start_time: float):
    import aiohttp

    # Low concurrency = fewer rate-limits = more cookies correctly detected
    CONCURRENCY = 10

    connector = aiohttp.TCPConnector(
        limit=CONCURRENCY * 2, limit_per_host=CONCURRENCY * 2,
        enable_cleanup_closed=True, ttl_dns_cache=300,
    )

    async def _run_pass(session, pass_tokens: list, pass_num: int,
                        sem_size: int, pass_label: str) -> list:
        """Run one checking pass. Returns list of still-uncertain tokens."""
        sem = asyncio.Semaphore(sem_size)
        uncertain: list = []
        pass_total = len(pass_tokens)
        checked_n = [0]

        tasks = [
            asyncio.create_task(
                _async_check_one_ck(session, tok, sem, test_slug_val)
            )
            for tok in pass_tokens
        ]
        for coro in asyncio.as_completed(tasks):
            try:
                result = await coro
            except asyncio.CancelledError:
                break
            except Exception:
                result = ("", None, "")
            async with lock_obj:
                checked_n[0] += 1
                cnt = checked_n[0]
                elapsed = time.time() - start_time
                speed = cnt / elapsed if elapsed > 0 else 0
                tok_, valid, plan = result
                if valid is True and tok_:
                    working.append(result)
                    short = tok_[:55] + "..." if len(tok_) > 55 else tok_
                    print(f"{GREEN}[{pass_label} {cnt}/{pass_total}] ✅ WORKING | {plan:<14} | {speed:.0f}/s | {short}{RESET}")
                elif valid is None and tok_:
                    uncertain.append(tok_)
                elif cnt % 50 == 0 or (pass_num > 1 and cnt % 25 == 0):
                    print(f"{GRAY}[{pass_label} {cnt}/{pass_total}] checking... {speed:.0f}/s{RESET}")
        return uncertain

    async with aiohttp.ClientSession(connector=connector) as session:
        # Self-calibrate: find which endpoint returns 401 for fake token
        cal = await _calibrate_check_url(session)
        _CALIBRATED_URL[0] = cal
        if cal:
            print(f"{CYAN}ℹ  Auth endpoint confirmed: {cal.split('/')[-1]}{RESET}")
        else:
            print(f"{YELLOW}⚠ No calibrated endpoint — using home page as primary check{RESET}")

        # ── Pass 1: all tokens, concurrency 10 ───────────────────────────────
        print(f"{CYAN}⏳ Pass 1/4 — checking all {total} cookies (concurrency={CONCURRENCY})...{RESET}")
        uncertain = await _run_pass(session, tokens, 1, CONCURRENCY, "P1")
        print(f"{CYAN}ℹ  Pass 1 done — {len(working)} working, {len(uncertain)} uncertain (rate-limited/timeout){RESET}")

        # ── Pass 2: retry uncertain after 5s cooldown, concurrency 8 ─────────
        if uncertain:
            print(f"\n{YELLOW}⏳ Pass 2/4 — retrying {len(uncertain)} uncertain cookies (5s cooldown)...{RESET}")
            await asyncio.sleep(5)
            before = len(working)
            uncertain = await _run_pass(session, uncertain, 2, 8, "P2")
            print(f"{CYAN}ℹ  Pass 2 done — +{len(working)-before} found, {len(uncertain)} still uncertain{RESET}")

        # ── Pass 3: retry after 10s cooldown, concurrency 5 ──────────────────
        if uncertain:
            print(f"\n{YELLOW}⏳ Pass 3/4 — retrying {len(uncertain)} uncertain cookies (10s cooldown)...{RESET}")
            await asyncio.sleep(10)
            before = len(working)
            uncertain = await _run_pass(session, uncertain, 3, 5, "P3")
            print(f"{CYAN}ℹ  Pass 3 done — +{len(working)-before} found, {len(uncertain)} still uncertain{RESET}")

        # ── Pass 4: final retry after 20s cooldown, concurrency 3 ────────────
        if uncertain:
            print(f"\n{YELLOW}⏳ Pass 4/4 — final retry {len(uncertain)} cookies (20s cooldown)...{RESET}")
            await asyncio.sleep(20)
            before = len(working)
            uncertain = await _run_pass(session, uncertain, 4, 3, "P4")
            print(f"{CYAN}ℹ  Pass 4 done — +{len(working)-before} found{RESET}")
            if uncertain:
                print(f"{YELLOW}⚠ {len(uncertain)} cookies still uncertain after all passes (network issues) — skipped{RESET}")

# ── Sync fallback checker (urllib threads — no extra deps) ────────────────────

def _check_single_cookie(token: str, _test_slug: list = None,
                         _check_url: list = None) -> tuple:
    """Sync fallback single-cookie check (urllib). Returns (orig, is_valid, plan)."""
    import urllib.error as _ue
    orig = token
    if "%" in token:
        token = unquote(token)

    # Handle "name=value" format
    if "=" in token and not token.startswith("eyJ"):
        for cn in ("usertoken", "x-hs-usertoken", "hs-token", "sub", "ut"):
            if token.lower().startswith(cn + "="):
                token = token.split("=", 1)[1]
                break

    # 1. Hotstar JWT instant (no HTTP)
    jwt = _jwt_instant_check(token)
    if jwt is not None:
        return (orig, jwt[0], jwt[1])

    hdrs = _make_check_headers(token)

    # 2. Home page (PRIMARY — most reliable, definitive result)
    try:
        req = request.Request(_CK_HOME_URL, headers=hdrs)
        with request.urlopen(req, timeout=12) as resp:
            hp_data = json.loads(resp.read().decode("utf-8", errors="ignore"))
        hp_success = hp_data.get("success")
        if not hp_success:
            return orig, False, ""
        plan = _extract_plan_from_json(hp_data) or "VALID"
    except _ue.HTTPError as he:
        if he.code in (401, 403):
            return orig, False, ""
        return orig, None, ""   # 429/5xx → uncertain, retry
    except Exception:
        return orig, None, ""   # timeout → uncertain, retry

    # 3. Subscriptions endpoint (plan label enrichment — home page already confirmed valid)
    check_url = (_check_url[0] if _check_url and _check_url[0] else _CK_SUBS_URL)
    try:
        req = request.Request(check_url, headers=hdrs)
        with request.urlopen(req, timeout=10) as resp:
            subs_data = json.loads(resp.read().decode("utf-8", errors="ignore"))
        subs_plan = _extract_plan_from_json(subs_data)
        if subs_plan:
            plan = subs_plan
    except Exception:
        pass  # enrichment failed — keep home page plan label

    # 4. Live event watch API (PAID detection — optional)
    if _test_slug and _test_slug[0]:
        try:
            api_url = build_jhs_api_url(_test_slug[0], "eng", is_live=True)
            req = request.Request(api_url, headers=hdrs)
            with request.urlopen(req, timeout=8) as resp:
                le_data = json.loads(resp.read().decode("utf-8", errors="ignore"))
            spaces = (le_data.get("success") or {}).get("page", {}).get("spaces", {})
            for space in spaces.values():
                for wrapper in (space.get("widget_wrappers") or []):
                    pc = (wrapper.get("widget") or {}).get("data", {}).get("player_config")
                    if pc:
                        plan = "PAID"
                        break
        except Exception:
            pass  # live event check optional — ignore errors

    return orig, True, plan

def _try_install_aiohttp() -> bool:
    try:
        import aiohttp  # noqa: F401
        return True
    except ImportError:
        pass
    print(f"{YELLOW}⏳ aiohttp not found, installing for max speed...{RESET}", flush=True)
    try:
        subprocess.run(
            [sys.executable, "-m", "pip", "install", "aiohttp", "-q"],
            timeout=60, check=True, capture_output=True
        )
        import aiohttp  # noqa: F401
        print(f"{GREEN}✅ aiohttp installed — async mode active{RESET}")
        return True
    except Exception:
        print(f"{YELLOW}⚠ aiohttp unavailable — using threaded mode{RESET}")
        return False

# ── Main cookies checker (called from menu) ───────────────────────────────────

def hotstar_cookies_checker():
    """Bulk Hotstar cookies checker — async fast mode (500-600/sec), auto-fallback to threads."""
    print(f"\n{BOLD_CYAN}╔══════════════════════════════════════════╗{RESET}")
    print(f"{BOLD_CYAN}║   🍪  HOTSTAR COOKIES CHECKER  FAST     ║{RESET}")
    print(f"{BOLD_CYAN}╚══════════════════════════════════════════╝{RESET}")
    print(f"{YELLOW}Supported: txt, json, folder, zip, 7z, rar{RESET}\n")

    path = input(f"{BOLD_CYAN}Enter cookies local file path: {RESET}").strip().strip('"').strip("'")
    if not path or not os.path.exists(path):
        print(f"{RED}❌ Path not found: {path}{RESET}")
        return

    print(f"{YELLOW}⏳ Loading cookies...{RESET}")
    _raw_count = []
    tokens = _collect_tokens_from_path(path, _raw_count)
    if not tokens:
        print(f"{RED}❌ No cookies/tokens found!{RESET}")
        return

    total = len(tokens)
    _raw_total = _raw_count[0] if _raw_count else total
    if _raw_total > total:
        print(f"{YELLOW}ℹ  {_raw_total} total files found — {_raw_total - total} duplicate tokens removed → {total} unique{RESET}")

    # Pre-scan: classify tokens correctly
    hs_jwt_valid   = 0   # Hotstar JWT, not expired
    hs_jwt_expired = 0   # Hotstar JWT, expired
    other_jwt      = 0   # eyJ... but NOT a Hotstar JWT (Firebase, Google, etc.)
    non_jwt        = 0   # no eyJ prefix → opaque session tokens
    now_ts         = int(time.time())
    for t in tokens:
        if not t.startswith("eyJ"):
            non_jwt += 1
            continue
        p = _decode_jwt_payload(t)
        if not p:
            other_jwt += 1  # undecodable
            continue
        uid  = p.get("uid") or p.get("userId") or p.get("user_id")
        sub_raw = p.get("sub", "")
        sub_d: dict = {}
        if isinstance(sub_raw, str):
            try:
                sub_d = json.loads(sub_raw)
            except Exception:
                pass
        elif isinstance(sub_raw, dict):
            sub_d = sub_raw
        iss = str(p.get("iss", "")).lower()
        is_hs = bool(
            uid or sub_d.get("uid") or sub_d.get("subscriptionType") or
            sub_d.get("ut") or sub_d.get("userType") or
            "hotstar" in iss or iss in ("hs", "hotstar")
        )
        if not is_hs:
            other_jwt += 1
            continue
        exp = p.get("exp", 0)
        if exp and exp < now_ts:
            hs_jwt_expired += 1
        else:
            hs_jwt_valid += 1

    print(f"{GREEN}✅ Found {total} unique tokens{RESET}")
    print(f"{CYAN}ℹ  Hotstar JWTs : ✅ {hs_jwt_valid} valid  ❌ {hs_jwt_expired} expired{RESET}")
    print(f"{CYAN}ℹ  Other JWTs   : {other_jwt} (non-Hotstar, checked via API){RESET}")
    print(f"{CYAN}ℹ  Session tokens: {non_jwt} (checked via API){RESET}")

    # Try to get a live event slug for more accurate PAID detection
    test_slug: list = [None]
    print(f"{YELLOW}⏳ Fetching live test event...{RESET}", end="", flush=True)
    try:
        live_ev, _ = fetch_live_events()
        if live_ev:
            _, ev_url = live_ev[0]
            sl = extract_slug_path(ev_url)
            if sl:
                test_slug[0] = sl
                print(f"\r{GREEN}✅ Test event: {live_ev[0][0][:40]}{RESET}        ")
            else:
                print(f"\r{YELLOW}⚠ No live slug — using subscription endpoint check{RESET}    ")
        else:
            print(f"\r{YELLOW}⚠ No live events — using subscription endpoint check{RESET}")
    except Exception:
        print(f"\r{YELLOW}⚠ Couldn't fetch live event — using subscription endpoint check{RESET}")

    print(f"{YELLOW}⏳ Checking {total} cookies... concurrency=75 (WORKING shown live){RESET}\n")

    working = []
    start_time = time.time()
    has_aiohttp = _try_install_aiohttp()

    if has_aiohttp:
        # ── ASYNC MODE: 500-600 cookies/sec ──────────────────────────────────
        lock_obj = asyncio.Lock()
        try:
            async def _run():
                nonlocal lock_obj
                lock_obj = asyncio.Lock()
                await _run_async_ck(
                    tokens, test_slug[0] or "", total,
                    working, lock_obj, start_time
                )
            asyncio.run(_run())
        except KeyboardInterrupt:
            print(f"\n{YELLOW}⚠ Interrupted — showing results so far.{RESET}")
    else:
        # ── THREADED FALLBACK: ~150-200 cookies/sec ───────────────────────────
        checked_count = [0]
        lock = threading.Lock()
        stop_flag = threading.Event()

        uncertain_list: list = []

        def check_one(tok):
            if stop_flag.is_set():
                return
            result = _check_single_cookie(tok, _test_slug=test_slug,
                                           _check_url=_CALIBRATED_URL)
            with lock:
                checked_count[0] += 1
                cnt = checked_count[0]
                elapsed = time.time() - start_time
                speed = cnt / elapsed if elapsed > 0 else 0
                orig_tok, valid, plan = result
                if valid is True:
                    working.append(result)
                    short = tok[:55] + "..." if len(tok) > 55 else tok
                    print(f"{GREEN}[{cnt}/{total}] ✅ WORKING | {plan:<14} | {speed:.0f}/s | {short}{RESET}")
                elif valid is None:
                    uncertain_list.append(tok)   # retry later
                elif cnt % 100 == 0:
                    print(f"{GRAY}[{cnt}/{total}] checking... {speed:.0f}/sec{RESET}")

        max_workers = min(200, max(50, total))
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            futures = {executor.submit(check_one, tok): tok for tok in tokens}
            try:
                for fut in as_completed(futures):
                    try:
                        fut.result()
                    except Exception:
                        pass
            except KeyboardInterrupt:
                stop_flag.set()
                print(f"\n{YELLOW}⚠ Interrupted — showing results so far.{RESET}")

        # Retry uncertain (rate-limited / timed-out) cookies at lower concurrency
        if uncertain_list and not stop_flag.is_set():
            import time as _t
            print(f"\n{YELLOW}⏳ Retrying {len(uncertain_list)} uncertain cookies...{RESET}")
            _t.sleep(2)
            retry_lock = threading.Lock()
            r_idx = [0]
            r_total = len(uncertain_list)

            def check_retry(tok):
                result = _check_single_cookie(tok, _test_slug=test_slug,
                                               _check_url=_CALIBRATED_URL)
                with retry_lock:
                    r_idx[0] += 1
                    orig_tok, valid, plan = result
                    if valid is True:
                        working.append(result)
                        short = tok[:55] + "..." if len(tok) > 55 else tok
                        print(f"{GREEN}[retry {r_idx[0]}/{r_total}] ✅ WORKING | {plan:<14} | {short}{RESET}")

            with ThreadPoolExecutor(max_workers=30) as retry_exec:
                for fut in as_completed({retry_exec.submit(check_retry, t): t
                                         for t in uncertain_list}):
                    try:
                        fut.result()
                    except Exception:
                        pass
            print(f"{CYAN}ℹ  Retry pass done{RESET}")

    elapsed = time.time() - start_time
    speed_final = total / elapsed if elapsed > 0 else 0

    print(f"\n{BOLD_GREEN}══════════════════════════════════════════{RESET}")
    print(f"{BOLD_GREEN}  RESULT: {len(working)} / {total} WORKING  ({elapsed:.1f}s, {speed_final:.0f}/s)  {RESET}")
    print(f"{BOLD_GREEN}══════════════════════════════════════════{RESET}")

    if not working:
        print(f"{RED}No working cookies found.{RESET}\n")
        return

    # Enrich plan labels from JWT payload (API often just returns "VALID")
    working = [(tok, ok, _plan_from_token(tok, plan)) for tok, ok, plan in working]

    # Plan breakdown
    from collections import Counter
    plan_counts = Counter(plan for _, _, plan in working)
    print(f"\n{BOLD_CYAN}Plan breakdown:{RESET}")
    for plan, cnt in plan_counts.most_common():
        print(f"  {GREEN}{plan:<16}{RESET} {cnt}")

    # ── Build token → source plan mapping (from filenames) ────────────────────
    print(f"{YELLOW}⏳ Mapping cookies to plan folders...{RESET}", end="", flush=True)
    token_plan_map = _collect_tokens_with_plans(path)
    print(f"\r{GREEN}✅ Plan folder mapping done.{RESET}          ")

    # ── Determine root output folder (named after the input path) ─────────────
    if os.path.isdir(path):
        input_basename = os.path.basename(path.rstrip("/\\"))
    else:
        input_basename = os.path.splitext(os.path.basename(path))[0]
    safe_name = "".join(c if c not in r'\/:*?"<>|' else "_" for c in input_basename)
    if not safe_name:
        safe_name = "hotstar_working"

    # Try Android Download folder first, fall back to Termux home
    dl_root = "/storage/emulated/0/Download"
    if os.path.isdir(dl_root) and os.access(dl_root, os.W_OK):
        output_root = os.path.join(dl_root, safe_name)
    else:
        output_root = os.path.join(os.path.expanduser("~"), "check_cookies", safe_name)

    os.makedirs(output_root, exist_ok=True)

    # ── Save one .txt per working cookie into its plan subfolder ──────────────
    # plan_idx tracks per-folder counter so files are numbered within each folder
    plan_idx: dict = {}
    saved = 0
    failed = 0
    folder_saved: dict = {}   # plan_folder → count (for summary)

    for tok, _, _api_plan in working:
        # Prefer plan from source filename; fall back to API-detected plan
        src_plan = token_plan_map.get(tok, "")
        plan_folder = src_plan if src_plan else _normalize_plan_folder("")
        # Sanitize plan folder name
        safe_plan = "".join(c if c not in r'\/:*?"<>|' else "_" for c in plan_folder)
        if not safe_plan:
            safe_plan = "Other"

        sub_dir = os.path.join(output_root, safe_plan)
        try:
            os.makedirs(sub_dir, exist_ok=True)
        except Exception:
            sub_dir = output_root  # fallback: flat

        plan_idx[safe_plan] = plan_idx.get(safe_plan, 0) + 1
        fname = os.path.join(sub_dir, f"token{plan_idx[safe_plan]}.txt")
        try:
            with open(fname, "w", encoding="utf-8") as f:
                f.write(tok + "\n")
            saved += 1
            folder_saved[safe_plan] = folder_saved.get(safe_plan, 0) + 1
        except Exception:
            failed += 1

    print(f"\n{BOLD_GREEN}✅ Working cookies sorted into plan folders:{RESET}")
    print(f"{CYAN}{output_root}{RESET}")
    for pf, cnt in sorted(folder_saved.items()):
        print(f"  {GREEN}├─ {pf:<24}{RESET} {cnt} cookie{'s' if cnt != 1 else ''}")
    print(f"{BOLD_YELLOW}Total: {saved} files / {total} checked{RESET}")
    if failed:
        print(f"{RED}⚠ {failed} files could not be saved{RESET}")
    print()

# ===================== HOTSTAR QUALITY CHECKER =====================

_QUALITY_DEFAULT_URL  = "https://www.hotstar.com/in/sports/cricket/england-vs-india-5th-t20i-highlights/1540072912/video/highlights/watch"
_QUALITY_DEFAULT_SLUG = "cricket/england-vs-india-5th-t20i-highlights/1540072912"

def _detect_quality_from_player_config(pc: dict) -> str:
    """
    Inspect player_config and return the best quality tier served:
    '4K_HDR', '4K_SDR', 'FHD', or 'SD'.
    """
    dynamic_range = str(pc.get("dynamic_range", "")).lower()
    ptags         = str(pc.get("playback_tags", "")).lower()
    is_hdr        = "hdr" in dynamic_range or "hdr" in ptags

    has_4k  = False
    has_fhd = False

    for key in ("media_asset", "media_asset_v2"):
        assets = pc.get(key)
        if not assets:
            continue
        if isinstance(assets, dict):
            assets = [assets]
        for asset in assets:
            for variant in ("primary", "fallback"):
                item = asset.get(variant)
                if not isinstance(item, dict):
                    continue
                url    = str(item.get("content_url", "")).lower()
                tags   = str(item.get("playback_tags", "")).lower()
                height = int(item.get("height") or 0)
                res    = str(item.get("resolution", "")).lower()
                vq     = str(item.get("video_quality", "")).lower()

                if (height >= 2160 or "4k" in tags or "4k" in res or
                        "4k" in vq or "_4k" in url or "/4k/" in url or
                        "uhd" in tags or "uhd" in vq):
                    has_4k = True
                    if "hdr" in tags or "hdr" in url:
                        is_hdr = True
                elif (height >= 1080 or "fhd" in tags or "fhd" in res or
                          "fhd" in vq or "_fhd" in url or "/fhd/" in url or
                          height == 1080):
                    has_fhd = True

    if not is_hdr and "hdr" in json.dumps(pc).lower():
        is_hdr = True

    if has_4k:
        return "4K_HDR" if is_hdr else "4K_SDR"
    if has_fhd:
        return "FHD"
    return "SD"


def _check_token_quality_sync(token: str, api_url: str):
    """
    Sync urllib quality check for one token.
    Returns quality string ('4K_HDR','4K_SDR','FHD','SD'),
    '' if token is invalid/no stream, or None on timeout/network error (retry).
    """
    try:
        hdrs = _make_check_headers(token)
        req  = request.Request(api_url, headers=hdrs)
        with request.urlopen(req, timeout=15) as resp:
            if resp.status != 200:
                return ""
            data = json.loads(resp.read().decode("utf-8", errors="ignore"))
        spaces = (data.get("success") or {}).get("page", {}).get("spaces", {})
        pc = None
        for space in spaces.values():
            for wrapper in (space.get("widget_wrappers") or []):
                _pc = (wrapper.get("widget") or {}).get("data", {}).get("player_config")
                if _pc:
                    pc = _pc
                    break
            if pc:
                break
        if not pc:
            return ""
        return _detect_quality_from_player_config(pc)
    except OSError:
        return None
    except Exception:
        return ""


async def _async_check_quality_one(session, token: str, semaphore, api_url: str) -> tuple:
    """
    Async quality check for one token.
    Returns (token, quality_str) where quality_str may be:
      '4K_HDR'/'4K_SDR'/'FHD'/'SD' — success
      '' — invalid / no stream
      None — timeout / rate-limit → retry
    """
    import aiohttp
    hdrs = _make_check_headers(token)
    TO   = aiohttp.ClientTimeout(total=15)
    async with semaphore:
        try:
            async with session.get(api_url, headers=hdrs, timeout=TO, ssl=False) as resp:
                if resp.status in (429, 500, 502, 503, 504):
                    return (token, None)
                if resp.status != 200:
                    return (token, "")
                try:
                    data = await resp.json(content_type=None)
                except Exception:
                    data = json.loads((await resp.read()).decode("utf-8", errors="ignore"))
        except asyncio.CancelledError:
            raise
        except Exception:
            return (token, None)

    spaces = (data.get("success") or {}).get("page", {}).get("spaces", {})
    pc = None
    for space in spaces.values():
        for wrapper in (space.get("widget_wrappers") or []):
            _pc = (wrapper.get("widget") or {}).get("data", {}).get("player_config")
            if _pc:
                pc = _pc
                break
        if pc:
            break
    if not pc:
        return (token, "")
    return (token, _detect_quality_from_player_config(pc))


async def _run_async_quality(tokens: list, api_url: str, total: int,
                              results: list, lock_obj, start_time: float):
    import aiohttp
    CONCURRENCY = 8

    connector = aiohttp.TCPConnector(
        limit=CONCURRENCY * 2, limit_per_host=CONCURRENCY * 2,
        enable_cleanup_closed=True, ttl_dns_cache=300,
    )

    async def _run_pass(session, pass_tokens: list, pass_label: str, sem_size: int) -> list:
        sem       = asyncio.Semaphore(sem_size)
        uncertain: list = []
        checked_n = [0]
        pass_total = len(pass_tokens)
        tasks = [
            asyncio.create_task(_async_check_quality_one(session, tok, sem, api_url))
            for tok in pass_tokens
        ]
        for coro in asyncio.as_completed(tasks):
            try:
                tok_, quality = await coro
            except asyncio.CancelledError:
                break
            except Exception:
                tok_, quality = ("", "")
            async with lock_obj:
                checked_n[0] += 1
                cnt     = checked_n[0]
                elapsed = time.time() - start_time
                speed   = cnt / elapsed if elapsed > 0 else 0
                if quality is None:
                    if tok_:
                        uncertain.append(tok_)
                    if cnt % 25 == 0:
                        print(f"{GRAY}[{pass_label} {cnt}/{pass_total}] checking... {speed:.0f}/s{RESET}")
                elif quality and tok_:
                    results.append((tok_, quality))
                    short = tok_[:50] + "..." if len(tok_) > 50 else tok_
                    color = (BOLD_MAGENTA if "4K" in quality
                             else (BOLD_GREEN if quality == "FHD" else YELLOW))
                    print(f"{color}[{pass_label} {cnt}/{pass_total}] ✅ {quality:<8} | {speed:.0f}/s | {short}{RESET}")
                else:
                    if cnt % 25 == 0:
                        print(f"{GRAY}[{pass_label} {cnt}/{pass_total}] checking... {speed:.0f}/s{RESET}")
        return uncertain

    async with aiohttp.ClientSession(connector=connector) as session:
        print(f"{CYAN}⏳ Pass 1/3 — checking all {total} tokens (concurrency={CONCURRENCY})...{RESET}")
        uncertain = await _run_pass(session, tokens, "P1", CONCURRENCY)
        print(f"{CYAN}ℹ  Pass 1 done — {len(results)} quality-detected, {len(uncertain)} uncertain{RESET}")

        if uncertain:
            print(f"\n{YELLOW}⏳ Pass 2/3 — retrying {len(uncertain)} uncertain tokens (8s cooldown)...{RESET}")
            await asyncio.sleep(8)
            before = len(results)
            uncertain = await _run_pass(session, uncertain, "P2", 5)
            print(f"{CYAN}ℹ  Pass 2 done — +{len(results)-before} resolved, {len(uncertain)} still uncertain{RESET}")

        if uncertain:
            print(f"\n{YELLOW}⏳ Pass 3/3 — final retry {len(uncertain)} tokens (15s cooldown)...{RESET}")
            await asyncio.sleep(15)
            before = len(results)
            uncertain = await _run_pass(session, uncertain, "P3", 3)
            print(f"{CYAN}ℹ  Pass 3 done — +{len(results)-before} found{RESET}")
            if uncertain:
                print(f"{YELLOW}⚠ {len(uncertain)} tokens still uncertain — counted as not_working{RESET}")


def hotstar_quality_checker():
    """Check stream quality (4K HDR / 4K SDR / FHD / SD) for a batch of tokens."""
    print(f"\n{BOLD_MAGENTA}╔══════════════════════════════════════════╗{RESET}")
    print(f"{BOLD_MAGENTA}║    🎬  HOTSTAR QUALITY CHECKER           ║{RESET}")
    print(f"{BOLD_MAGENTA}╚══════════════════════════════════════════╝{RESET}")
    print(f"{YELLOW}Supported: txt, json, folder, zip, 7z, rar{RESET}\n")

    path = input(f"{BOLD_CYAN}Enter tokens folder/file path: {RESET}").strip().strip('"').strip("'")
    if not path or not os.path.exists(path):
        print(f"{RED}❌ Path not found: {path}{RESET}")
        return

    print(f"{YELLOW}⏳ Loading tokens...{RESET}")
    _raw_count: list = []
    tokens = _collect_tokens_from_path(path, _raw_count)
    if not tokens:
        print(f"{RED}❌ No tokens found!{RESET}")
        return

    total      = len(tokens)
    _raw_total = _raw_count[0] if _raw_count else total
    if _raw_total > total:
        print(f"{YELLOW}ℹ  {_raw_total} total files found — {_raw_total - total} duplicate tokens removed → {total} unique{RESET}")
    print(f"{GREEN}✅ Found {total} unique tokens{RESET}")

    url_in = input(f"{BOLD_CYAN}Quality check URL (Enter = 4K Highlights default): {RESET}").strip()
    if not url_in:
        url_in = _QUALITY_DEFAULT_URL
    slug    = extract_slug_path(url_in) or _QUALITY_DEFAULT_SLUG
    api_url = build_api_url(slug, "eng", "1")
    print(f"{CYAN}ℹ  Slug: {slug}{RESET}")
    print(f"\n{YELLOW}⏳ Checking quality for {total} tokens... (4K/FHD shown live){RESET}\n")

    results: list = []   # [(token, quality_str), ...]
    start_time = time.time()
    has_aiohttp = _try_install_aiohttp()

    if has_aiohttp:
        lock_obj = asyncio.Lock()
        try:
            async def _run():
                nonlocal lock_obj
                lock_obj = asyncio.Lock()
                await _run_async_quality(tokens, api_url, total, results, lock_obj, start_time)
            asyncio.run(_run())
        except KeyboardInterrupt:
            print(f"\n{YELLOW}⚠ Interrupted — showing results so far.{RESET}")
    else:
        checked_count = [0]
        lock      = threading.Lock()
        stop_flag = threading.Event()
        uncertain_list: list = []

        def _check_one_q(tok):
            if stop_flag.is_set():
                return
            quality = _check_token_quality_sync(tok, api_url)
            with lock:
                checked_count[0] += 1
                cnt     = checked_count[0]
                elapsed = time.time() - start_time
                speed   = cnt / elapsed if elapsed > 0 else 0
                if quality is None:
                    uncertain_list.append(tok)
                    return
                if quality:
                    results.append((tok, quality))
                    short = tok[:50] + "..." if len(tok) > 50 else tok
                    color = (BOLD_MAGENTA if "4K" in quality
                             else (BOLD_GREEN if quality == "FHD" else YELLOW))
                    print(f"{color}[{cnt}/{total}] ✅ {quality:<8} | {speed:.0f}/s | {short}{RESET}")
                elif cnt % 25 == 0:
                    print(f"{GRAY}[{cnt}/{total}] checking... {speed:.0f}/s{RESET}")

        with ThreadPoolExecutor(max_workers=min(30, max(10, total))) as ex:
            futs = {ex.submit(_check_one_q, tok): tok for tok in tokens}
            try:
                for fut in as_completed(futs):
                    try:
                        fut.result()
                    except Exception:
                        pass
            except KeyboardInterrupt:
                stop_flag.set()
                print(f"\n{YELLOW}⚠ Interrupted.{RESET}")

        if uncertain_list and not stop_flag.is_set():
            print(f"\n{YELLOW}⏳ Retrying {len(uncertain_list)} uncertain tokens...{RESET}")
            time.sleep(5)
            for tok in uncertain_list:
                quality = _check_token_quality_sync(tok, api_url)
                if quality:
                    results.append((tok, quality))

    elapsed = time.time() - start_time
    print(f"\n{BOLD_MAGENTA}══════════════════════════════════════════{RESET}")
    print(f"{BOLD_MAGENTA}  RESULT: {len(results)} / {total} quality-detected  ({elapsed:.1f}s)  {RESET}")
    print(f"{BOLD_MAGENTA}══════════════════════════════════════════{RESET}")

    from collections import Counter as _QCounter
    q_counts = _QCounter(q for _, q in results)
    print(f"\n{BOLD_CYAN}Quality breakdown:{RESET}")
    for q in ("4K_HDR", "4K_SDR", "FHD", "SD"):
        cnt = q_counts.get(q, 0)
        if cnt:
            color = (BOLD_MAGENTA if "4K" in q
                     else (BOLD_GREEN if q == "FHD" else YELLOW))
            print(f"  {color}{q:<10}{RESET} {cnt}")
    not_working_count = total - len(results)
    if not_working_count:
        print(f"  {RED}not_working{RESET} {not_working_count}")

    # ── Determine output root ─────────────────────────────────────────────────
    if os.path.isdir(path):
        input_basename = os.path.basename(path.rstrip("/\\"))
    else:
        input_basename = os.path.splitext(os.path.basename(path))[0]
    safe_name = "".join(c if c not in r'\/:*?"<>|' else "_" for c in input_basename)
    if not safe_name:
        safe_name = "quality_results"

    dl_root = "/storage/emulated/0/Download"
    if os.path.isdir(dl_root) and os.access(dl_root, os.W_OK):
        output_root = os.path.join(dl_root, safe_name + "_quality")
    else:
        output_root = os.path.join(os.path.expanduser("~"), "quality_check", safe_name)
    os.makedirs(output_root, exist_ok=True)

    # ── Save tokens into quality subfolders ──────────────────────────────────
    q_idx:        dict = {}
    folder_saved: dict = {}
    saved  = 0
    failed = 0

    for tok, quality in results:
        sub_dir = os.path.join(output_root, quality)
        try:
            os.makedirs(sub_dir, exist_ok=True)
        except Exception:
            sub_dir = output_root
        q_idx[quality] = q_idx.get(quality, 0) + 1
        fname = os.path.join(sub_dir, f"token{q_idx[quality]}.txt")
        try:
            with open(fname, "w", encoding="utf-8") as f:
                f.write(tok + "\n")
            saved += 1
            folder_saved[quality] = folder_saved.get(quality, 0) + 1
        except Exception:
            failed += 1

    # Save not_working tokens
    working_set = {tok for tok, _ in results}
    nw_dir = os.path.join(output_root, "not_working")
    nw_idx = 0
    for tok in tokens:
        if tok not in working_set:
            try:
                os.makedirs(nw_dir, exist_ok=True)
                nw_idx += 1
                with open(os.path.join(nw_dir, f"token{nw_idx}.txt"), "w", encoding="utf-8") as f:
                    f.write(tok + "\n")
            except Exception:
                pass

    print(f"\n{BOLD_MAGENTA}✅ Tokens sorted by quality into:{RESET}")
    print(f"{CYAN}{output_root}{RESET}")
    for q in ("4K_HDR", "4K_SDR", "FHD", "SD"):
        cnt = folder_saved.get(q, 0)
        if cnt:
            color = (BOLD_MAGENTA if "4K" in q
                     else (BOLD_GREEN if q == "FHD" else YELLOW))
            print(f"  {color}├─ {q:<14}{RESET} {cnt} token{'s' if cnt != 1 else ''}")
    if nw_idx:
        print(f"  {RED}├─ not_working  {RESET} {nw_idx} token{'s' if nw_idx != 1 else ''}")
    print(f"{BOLD_YELLOW}Total: {saved} saved / {total} checked{RESET}")
    if failed:
        print(f"{RED}⚠ {failed} files could not be saved{RESET}")
    print()


# ===================== LIVE EVENTS FETCHER =====================
LIVE_EVENTS_HTML_URL = "https://www.hotstar.com/in/browse/editorial/live-now/1271392364"

# Slugs API — fetches the editorial live-now page directly as JSON (no profile gate)
_LIVE_SLUGS_API = (
    "https://www.hotstar.com/api/internal/bff/v2/slugs"
    "/in/browse/editorial/live-now/1271392364"
)

# Slugs API — fetches the best-in-sports editorial page
_SPORTS_SLUGS_API = (
    "https://www.hotstar.com/api/internal/bff/v2/slugs"
    "/in/browse/editorial/best-in-sports/6517"
)

# client_capabilities for the live editorial page fetch
_LIVE_CAPABILITIES = json.dumps({
    "ads": ["non_ssai"],
    "audio_channel": ["stereo"],
    "container": ["fmp4", "fmp4br", "ts"],
    "dvr": ["short"],
    "dynamic_range": ["sdr"],
    "encryption": ["plain"],
    "ladder": ["phone", "web"],
    "package": ["hls", "dash"],
    "resolution": ["sd", "hd", "fhd"],
    "video_codec": ["h264"],
    "video_codec_non_secure": ["h265", "h264"]
}, separators=(",", ":"))

_LIVE_DRM = json.dumps({
    "hdcp_version": ["HDCP_V2_2"],
    "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"]
}, separators=(",", ":"))


def _extract_title_and_slug(item: dict) -> tuple:
    """
    Extract (title, slug) from a BFF content item.
    Handles multiple card shapes Hotstar returns:
      - horizontal_content_card / vertical_content_card
      - standard item dict with title + web_url / deeplink_url
    Returns ("", "") when nothing useful found.
    """
    if not isinstance(item, dict):
        return "", ""

    # ── Shape 1: wrapped card (horizontal_content_card / vertical_content_card) ──
    for card_key in ("horizontal_content_card", "vertical_content_card",
                     "content_card", "card"):
        card = item.get(card_key)
        if not isinstance(card, dict):
            continue
        d = card.get("data") or card
        title = ""
        for fk in ("footer", "header", "body"):
            fnode = d.get(fk)
            if isinstance(fnode, dict):
                title = (fnode.get("title") or fnode.get("subtitle") or
                         fnode.get("name") or "")
                if title:
                    break
        if not title:
            title = (d.get("title") or d.get("name") or "")

        slug = ""
        # actions.on_click[].page_navigation.page_slug
        actions = d.get("actions") or {}
        for action in (actions.get("on_click") or []):
            nav = action.get("page_navigation") or {}
            if nav.get("page_slug"):
                slug = nav["page_slug"]
                break
        # fallback: web_url / deeplink_url in card data
        if not slug:
            slug = (d.get("web_url") or d.get("deeplink_url") or
                    d.get("share_url") or d.get("slug") or "")

        if title and slug:
            return title.strip(), slug

    # ── Shape 2: plain item dict ──────────────────────────────────────────────
    title = (item.get("title") or item.get("name") or
             item.get("show_name") or item.get("series_name") or "")
    if not title:
        b = item.get("body") or {}
        title = (b.get("title") or b.get("name") or "") if isinstance(b, dict) else ""

    slug = (item.get("web_url") or item.get("slug") or
            item.get("share_url") or item.get("deeplink_url") or "")
    if not slug:
        b = item.get("body") or {}
        slug = (b.get("web_url") or b.get("slug") or "") if isinstance(b, dict) else ""

    return title.strip(), slug


def _collect_events_from_spaces(spaces: dict) -> list:
    """Walk ALL spaces → widget_wrappers and collect (title, url) event tuples."""
    seen: set = set()
    events: list = []

    ITEM_KEYS = ("items", "cards", "assets", "tray", "content", "data")

    for space_name, space in spaces.items():
        if not isinstance(space, dict):
            continue
        for wrapper in (space.get("widget_wrappers") or []):
            if not isinstance(wrapper, dict):
                continue
            w_data = (wrapper.get("widget") or {}).get("data") or {}

            candidates: list = []
            for k in ITEM_KEYS:
                v = w_data.get(k)
                if isinstance(v, list):
                    candidates.extend(v)
                elif isinstance(v, dict):
                    for kk in ITEM_KEYS:
                        sub = v.get(kk)
                        if isinstance(sub, list):
                            candidates.extend(sub)

            for item in candidates:
                title, slug = _extract_title_and_slug(item)
                if not title or not slug:
                    continue
                dedup_key = slug  # slug is unique per event
                if dedup_key in seen:
                    continue
                seen.add(dedup_key)
                if slug.startswith("http"):
                    url = slug
                elif slug.startswith("/"):
                    url = f"https://www.hotstar.com{slug}"
                else:
                    url = f"https://www.hotstar.com/in/{slug}"
                events.append((title, url))

    return events


def _extract_title_slug_and_type(item: dict) -> tuple:
    """
    Extract (title, slug, content_type) from a BFF content item.
    content_type can be LIVE, HIGHLIGHT, VIDEO, etc.
    Returns ("", "", "") when nothing useful found.
    """
    if not isinstance(item, dict):
        return "", "", ""

    content_type = ""

    LIVE_TYPES = {"LIVE", "LIVE_TV", "LIVETV", "SPORT_LIVE"}
    HIGHLIGHT_TYPES = {"HIGHLIGHT", "HIGHLIGHTS", "CLIP", "CLIPS", "SHORTS"}

    def _detect_ctype(d: dict) -> str:
        for ct_key in ("content_type", "asset_type", "type", "content_sub_type"):
            ct = d.get(ct_key) or ""
            if ct:
                return str(ct).upper()
        badge = d.get("badge") or {}
        if isinstance(badge, dict):
            badge_text = (badge.get("text") or badge.get("label") or "").upper()
            if "LIVE" in badge_text:
                return "LIVE"
        return ""

    for card_key in ("horizontal_content_card", "vertical_content_card",
                     "content_card", "card"):
        card = item.get(card_key)
        if not isinstance(card, dict):
            continue
        d = card.get("data") or card
        title = ""
        for fk in ("footer", "header", "body"):
            fnode = d.get(fk)
            if isinstance(fnode, dict):
                title = (fnode.get("title") or fnode.get("subtitle") or
                         fnode.get("name") or "")
                if title:
                    break
        if not title:
            title = (d.get("title") or d.get("name") or "")

        content_type = _detect_ctype(d)

        slug = ""
        actions = d.get("actions") or {}
        for action in (actions.get("on_click") or []):
            nav = action.get("page_navigation") or {}
            if nav.get("page_slug"):
                slug = nav["page_slug"]
                break
        if not slug:
            slug = (d.get("web_url") or d.get("deeplink_url") or
                    d.get("share_url") or d.get("slug") or "")
        if title and slug:
            return title.strip(), slug, content_type

    title = (item.get("title") or item.get("name") or
             item.get("show_name") or item.get("series_name") or "")
    if not title:
        b = item.get("body") or {}
        title = (b.get("title") or b.get("name") or "") if isinstance(b, dict) else ""

    content_type = _detect_ctype(item)

    slug = (item.get("web_url") or item.get("slug") or
            item.get("share_url") or item.get("deeplink_url") or "")
    if not slug:
        b = item.get("body") or {}
        slug = (b.get("web_url") or b.get("slug") or "") if isinstance(b, dict) else ""

    return title.strip(), slug, content_type


def _collect_sports_from_spaces(spaces: dict, content_filter: str = "ALL") -> list:
    """
    Walk spaces and collect (title, url) based on content_filter:
      "LIVE"       — only live streams
      "HIGHLIGHTS" — only highlights/clips
      "OTHER"      — everything except live and highlights
      "ALL"        — everything
    """
    seen: set = set()
    events: list = []

    ITEM_KEYS = ("items", "cards", "assets", "tray", "content", "data")
    LIVE_TYPES = {"LIVE", "LIVE_TV", "LIVETV", "SPORT_LIVE"}
    HIGHLIGHT_TYPES = {"HIGHLIGHT", "HIGHLIGHTS", "CLIP", "CLIPS", "SHORTS"}

    for space_name, space in spaces.items():
        if not isinstance(space, dict):
            continue
        for wrapper in (space.get("widget_wrappers") or []):
            if not isinstance(wrapper, dict):
                continue
            w_data = (wrapper.get("widget") or {}).get("data") or {}

            candidates: list = []
            for k in ITEM_KEYS:
                v = w_data.get(k)
                if isinstance(v, list):
                    candidates.extend(v)
                elif isinstance(v, dict):
                    for kk in ITEM_KEYS:
                        sub = v.get(kk)
                        if isinstance(sub, list):
                            candidates.extend(sub)

            for item in candidates:
                title, slug, ctype = _extract_title_slug_and_type(item)
                if not title or not slug:
                    continue

                is_live = (
                    ctype in LIVE_TYPES or
                    "LIVE" in ctype or
                    "/live/" in slug.lower()
                )
                is_highlight = (
                    ctype in HIGHLIGHT_TYPES or
                    "HIGHLIGHT" in ctype or
                    "CLIP" in ctype or
                    "/highlights/" in slug.lower() or
                    "/clip" in slug.lower()
                )

                if content_filter == "LIVE" and not is_live:
                    continue
                elif content_filter == "HIGHLIGHTS" and not is_highlight:
                    continue
                elif content_filter == "OTHER" and (is_live or is_highlight):
                    continue

                dedup_key = slug
                if dedup_key in seen:
                    continue
                seen.add(dedup_key)

                if slug.startswith("http"):
                    url = slug
                elif slug.startswith("/"):
                    url = f"https://www.hotstar.com{slug}"
                else:
                    url = f"https://www.hotstar.com/in/{slug}"
                events.append((title, url))

    return events


def _extract_sports_items_from_data(widget_data: dict) -> tuple:
    """
    Extract (items_list, more_url) from a GridWidget data dict.
    """
    items = widget_data.get("items") or []
    more_url = widget_data.get("more_grid_items_url") or ""
    return items, more_url


def _parse_sports_item(item: dict) -> tuple:
    """
    Parse one horizontal_content_card item.
    Returns (title, slug) or ("", "").
    """
    hcc = item.get("horizontal_content_card") or {}
    data = hcc.get("data") or {}

    title = (
        (data.get("footer") or {}).get("title") or
        (data.get("header") or {}).get("title") or
        (data.get("body") or {}).get("title") or
        data.get("title") or ""
    )

    slug = ""
    for act in (data.get("actions") or {}).get("on_click") or []:
        nav = act.get("page_navigation") or {}
        if nav.get("page_slug"):
            slug = nav["page_slug"]
            break
    if not slug:
        slug = data.get("web_url") or data.get("slug") or ""

    return title.strip(), slug


def fetch_best_in_sports(content_filter: str = "ALL") -> tuple:
    """
    Fetch content from Hotstar best-in-sports editorial page.
    Uses GET /api/internal/bff/v2/slugs/in/browse/editorial/best-in-sports/6517
    — same slugs API pattern as fetch_live_events (confirmed working).
    content_filter: "LIVE", "HIGHLIGHTS", "OTHER", "ALL"
    Returns (list of (title, url) tuples, error_string).

    Pagination strategy (tries all three in order):
      1. Follow more_grid_items_url found at any level in the widget tree.
      2. Construct widget-id based grid items URL if widget id is found.
      3. Fallback: re-fetch the same sports URL with &offset=N&size=10 appended.
    """
    events: list = []
    token = load_user_token()

    # ── Android TV headers — same stack as fetch_live_events (confirmed working) ─
    hdrs = {
        "User-Agent": "Hotstar;in.startv.hotstar.dplus.tv/26.05.10.2 (Android/14; tv)",
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en",
        "X-HS-Platform": "androidtv",
        "X-Country-Code": "in",
        "X-HS-Accept-language": "eng",
        "x-hs-app": "260510002",
        "x-hs-retry-count": "0",
        "x-hs-is-retry": "false",
        "X-HS-Client": (
            "platform:androidtv;app_id:in.startv.hotstar.dplus.tv;"
            "app_version:26.05.10.2;os:Android;os_version:14;schema_version:0.0.1690"
        ),
        "Referer": "https://www.hotstar.com/in/browse/editorial/best-in-sports/6517",
        "Origin": "https://www.hotstar.com",
        "Pragma": "no-cache",
        "Cache-Control": "no-cache",
    }
    if token:
        hdrs["x-hs-usertoken"] = token

    sports_url_base = (
        _SPORTS_SLUGS_API
        + "?client_capabilities=" + parse.quote(_LIVE_CAPABILITIES)
        + "&drm_parameters=" + parse.quote(_LIVE_DRM)
        + "&request_features=consent_supported"
        + "&lang=eng"
    )

    _BFF_BASE = "https://www.hotstar.com/api/internal/bff"

    def _fetch_more_url(more_url: str) -> tuple:
        """Fetch a more_grid_items_url and return (items, next_more_url)."""
        full = _BFF_BASE + more_url if more_url.startswith("/") else more_url
        req_m = request.Request(full, headers=hdrs, method="GET")
        with request.urlopen(req_m, timeout=15) as r:
            d = json.loads(r.read().decode("utf-8", errors="replace"))
        payload = d.get("data") or d.get("success") or {}
        items    = payload.get("items") or []
        next_url = payload.get("more_grid_items_url") or ""
        return items, next_url

    def _ingest(items: list, seen: set) -> int:
        """Parse items into events; return count of new ones added."""
        fake_spaces = {
            "pg": {
                "widget_wrappers": [{
                    "widget": {"data": {"items": items}}
                }]
            }
        }
        added = 0
        for ev in _collect_sports_from_spaces(fake_spaces, content_filter):
            if ev[1] not in seen:
                seen.add(ev[1])
                events.append(ev)
                added += 1
        return added

    try:
        req = request.Request(sports_url_base, headers=hdrs, method="GET")
        with request.urlopen(req, timeout=15) as resp:
            data = json.loads(resp.read().decode("utf-8", errors="replace"))

        spaces = (data.get("success") or {}).get("page", {}).get("spaces", {})
        events = _collect_sports_from_spaces(spaces, content_filter)
        seen_urls = {url for _, url in events}

        # ── Strategy 1 & 2: walk each widget; find more_grid_items_url at any
        #    level OR build it from the widget id ─────────────────────────────
        _pages_fetched = 0
        _MAX_PAGES = 20

        for space in spaces.values():
            if not isinstance(space, dict):
                continue
            for wrapper in (space.get("widget_wrappers") or []):
                widget  = wrapper.get("widget") or {}
                w_data  = widget.get("data") or {}
                initial_items_count = len(w_data.get("items") or [])

                # Check more_grid_items_url at every nesting level
                more_url = (
                    w_data.get("more_grid_items_url") or
                    widget.get("more_grid_items_url") or
                    wrapper.get("more_grid_items_url") or
                    ""
                )

                # Always resolve widget_id (used in Strategy 2 fallback inside loop)
                widget_id = (
                    widget.get("id") or widget.get("widget_id") or
                    w_data.get("id") or w_data.get("widget_id") or ""
                )

                # Strategy 2: build from widget id if no URL found
                if not more_url and initial_items_count > 0 and widget_id:
                    more_url = (
                        f"/api/internal/bff/v2/pages/in/browse/editorial"
                        f"/best-in-sports/6517/widgets/{widget_id}/items"
                        f"?size=10&offset={initial_items_count}"
                    )

                offset_for_built_url = initial_items_count + 10
                while more_url and _pages_fetched < _MAX_PAGES:
                    _pages_fetched += 1
                    try:
                        more_items, more_url = _fetch_more_url(more_url)
                        if not more_items:
                            break
                        added = _ingest(more_items, seen_urls)
                        # If URL was built from widget_id, advance offset manually
                        if more_url == "" and widget_id and added > 0:
                            more_url = (
                                f"/api/internal/bff/v2/pages/in/browse/editorial"
                                f"/best-in-sports/6517/widgets/{widget_id}/items"
                                f"?size=10&offset={offset_for_built_url}"
                            )
                            offset_for_built_url += 10
                        if added == 0:
                            break
                    except Exception:
                        break

        # ── Strategy 3: offset fallback on the main sports URL ───────────────
        # Only runs if the widget-level strategies found nothing new
        if len(events) <= 10 and _pages_fetched == 0:
            offset = 10
            while _pages_fetched < _MAX_PAGES:
                _pages_fetched += 1
                try:
                    fallback_url = sports_url_base + f"&offset={offset}&size=10"
                    req_f = request.Request(fallback_url, headers=hdrs, method="GET")
                    with request.urlopen(req_f, timeout=15) as resp_f:
                        data_f = json.loads(resp_f.read().decode("utf-8", errors="replace"))
                    spaces_f = (data_f.get("success") or {}).get("page", {}).get("spaces", {})
                    if not spaces_f:
                        break
                    added = 0
                    for ev in _collect_sports_from_spaces(spaces_f, content_filter):
                        if ev[1] not in seen_urls:
                            seen_urls.add(ev[1])
                            events.append(ev)
                            added += 1
                    if added == 0:
                        break
                    offset += 10
                except Exception:
                    break

    except Exception as exc:
        return events, str(exc)

    return events, ""


def _show_sports_submenu(content_filter: str, label: str) -> Optional[str]:
    """
    Fetch best-in-sports content, show numbered list (10 per page) with N/P navigation.
    Supports single selection (returns URL) and multi-select via '1.2.3' or 'all'
    (handles full quality menu inline, returns None after processing).
    """
    PAGE_SIZE = 10

    print(f"{DARK_MAGENTA}Fetching {label}...{RESET}", end="", flush=True)
    sports_evts, _serr = fetch_best_in_sports(content_filter)
    print(f"\r{' ' * 50}\r", end="", flush=True)

    if not sports_evts:
        print(f"{YELLOW}No content found for {label}.{RESET}")
        return None

    total = len(sports_evts)
    page = 0
    prev_draw_lines = 0

    while True:
        start = page * PAGE_SIZE
        end = min(start + PAGE_SIZE, total)
        page_items = sports_evts[start:end]
        has_next = end < total
        has_prev = page > 0

        draw_lines = 1 + 3 + len(page_items) + int(has_next) + int(has_prev) + 2 + 1

        if prev_draw_lines > 0:
            sys.stdout.write(f"\033[{prev_draw_lines}A\r")
            sys.stdout.flush()

        print(f"\033[2K")
        print(f"\033[2K{BOLD_CYAN}┌──────────────────────────────────────────┐{RESET}")
        print(f"\033[2K{BOLD_CYAN}│  {label:<43}│{RESET}")
        print(f"\033[2K{BOLD_CYAN}└──────────────────────────────────────────┘{RESET}")

        for i, (ev_title, _) in enumerate(page_items, start + 1):
            print(f"\033[2K{BOLD_GREEN}{{{i}}}{RESET} {WHITE}{ev_title}{RESET}")

        if has_next:
            print(f"\033[2K{BOLD_YELLOW}{{N}}{RESET} {YELLOW}For Next Page 📄{RESET}")
        if has_prev:
            print(f"\033[2K{BOLD_MAGENTA}{{P}}{RESET} {MAGENTA}For Previous Page 📄{RESET}")

        print(f"\033[2K{BOLD_YELLOW}(Use 1.2.3 or 'all' to select multiple){RESET}")
        print(f"\033[2K")

        prev_draw_lines = draw_lines

        _pick_raw = input(f"\033[2K{BOLD_CYAN}Enter number ➤ {RESET}").strip()
        _pick_lower = _pick_raw.lower()

        if _pick_lower == "n" and has_next:
            page += 1
            continue
        elif _pick_lower == "p" and has_prev:
            page -= 1
            continue

        # ── Multi-select: 'all' or '1.2.3' or '1,2,3' ──────────────────────
        _parts = [p.strip() for p in _pick_raw.replace(".", ",").split(",") if p.strip()]
        _selected_events: list = []
        _seen_idx: set = set()

        if _pick_lower == "all":
            _selected_events = list(sports_evts)
        else:
            for _pt in _parts:
                if _pt.isdigit():
                    _idx = int(_pt)
                    if 1 <= _idx <= total and _idx not in _seen_idx:
                        _seen_idx.add(_idx)
                        _selected_events.append(sports_evts[_idx - 1])

        if not _selected_events:
            print(f"{RED}Invalid choice.{RESET}")
            return None

        # ── Single selection — return URL directly ───────────────────────────
        if len(_selected_events) == 1:
            _ev_title, _selected_url = _selected_events[0]
            print(f"\n{BOLD_GREEN}» {_ev_title}{RESET}")
            return _selected_url

        # ── Multi-selection — run the full quality menu inline ───────────────
        print(f"\n{BOLD_CYAN}✓ {len(_selected_events)} items selected:{RESET}")
        for _mi, (_mt, _) in enumerate(_selected_events, 1):
            print(f"  {BOLD_GREEN}{_mi}.{RESET} {WHITE}{_mt}{RESET}")
        print()
        print(f"{BOLD_GREEN}{{1}} NORMAL 4K{RESET}")
        print(f"{BOLD_BLUE}{{2}} NORMAL FHD{RESET}")
        print(f"{BOLD_CYAN}{{3}} NORMAL FHD (30 MINUTES){RESET}")
        print(f"{BOLD_YELLOW}{{4}} ADS-FREE JHS HD{RESET}")
        print(f"{BOLD_MAGENTA}{{5}} JHS 4K{RESET}")
        print(f"{BOLD_CYAN}{{6}} ADS-FREE 4K LITE (7 MINUTES){RESET}")
        print(f"{BOLD_CYAN}{{7}} ADS-FREE 4K HEAVY (30 MINUTES){RESET}")
        print(f"{BOLD_GREEN}{{8}} H.265 4K DV,HDR,SDR ADSFREE{RESET}")
        print(f"{BOLD_GREEN}{{9}} H.265 FHD DV,HDR,SDR{RESET}")
        print(f"{BOLD_GREEN}{{10}} H.265 AUTO DV,HDR,SDR ADSFREE{RESET}")
        print(f"{BOLD_GREEN}{{11}} ADS-FREE 4K TattiJio & Chortel users{RESET}")
        print(f"{BOLD_WHITE}{{12}} H.264 4K DV,HDR,SDR{RESET}")
        print(f"{BOLD_WHITE}{{13}} H.265 4K DV,HDR,SDR{RESET}")
        print(f"{BOLD_WHITE}{{14}} H.264 FHD DV,HDR,SDR{RESET}")
        print(f"{BOLD_WHITE}{{15}} H.265 FHD DV,HDR,SDR{RESET}")
        print(f"{BOLD_RED}{{16}} DRM MPD + CLEARKEY / PSSH{RESET}")
        print(f"{BOLD_YELLOW}{{17}} NORMAL HD (720p) ALL LANGUAGES{RESET}")
        print(f"{BOLD_GREEN}{{18}} DRM-TV 24-HOURS LINK{RESET}")
        print(f"{BOLD_MAGENTA}{{21}} AUTO-UPDATE M3U (EVERY MINUTES){RESET}")
        print(f"{BOLD_GREEN}{{22}} FALLBACK 24-HOURS LINK{RESET}")
        print(f"{BOLD_BLUE}{{23}} PRIMARY 24-HOURS LINK{RESET}")
        print(f"{BOLD_GREEN}{{24}} FALLBACK 24-HOURS TattiJio & Chortel users{RESET}")
        print(f"{BOLD_BLUE}{{25}} PRIMARY 24-HOURS TattiJio & Chortel users{RESET}")
        _mq = input(f"{BOLD_CYAN}Enter number ➤ {RESET}").strip()

        _MULTI_FN_MAP = {
            "3":  option_fhd_heavy_main,
            "6":  option5_main,
            "7":  option6_heavy_main,
            "8":  lambda u: option_dv_hdr_sdr(u, "h265", ads_mode="ssai"),
            "9":  lambda u: option_fhd_dv_hdr_sdr(u, "h265", ads_mode="ssai"),
            "10": option_auto_dv_hdr_sdr,
            "11": option6_pri_main,
            "12": lambda u: option_dv_hdr_sdr(u, "h264"),
            "13": lambda u: option_dv_hdr_sdr(u, "h265"),
            "14": lambda u: option_fhd_dv_hdr_sdr(u, "h264"),
            "15": lambda u: option_fhd_dv_hdr_sdr(u, "h265"),
            "17": option20_normal_hd,
            "18": option10_drm_tv_24h,
            "22": option12_fallback_24h,
            "23": option13_primary_24h,
            "24": option14_jio_fallback_24h,
            "25": option15_jio_primary_24h,
        }

        if _mq == "21":
            auto_update_mode_multi(_selected_events)
        elif _mq in _MULTI_FN_MAP:
            _mfn = _MULTI_FN_MAP[_mq]
            for _mi, (_mt, _mu) in enumerate(_selected_events, 1):
                print(f"\n{BOLD_CYAN}{'─'*44}{RESET}")
                print(f"{BOLD_CYAN}[{_mi}/{len(_selected_events)}] {_mt}{RESET}")
                print(f"{BOLD_CYAN}{'─'*44}{RESET}")
                _mfn(_mu)
        elif _mq == "16":
            for _mi, (_mt, _mu) in enumerate(_selected_events, 1):
                print(f"\n{BOLD_CYAN}{'─'*44}{RESET}")
                print(f"{BOLD_CYAN}[{_mi}/{len(_selected_events)}] {_mt}{RESET}")
                print(f"{BOLD_CYAN}{'─'*44}{RESET}")
                _msp = extract_slug_path(_mu)
                _mtt, _mmn = extract_match_title(_mu)
                _mst = extract_stream_type(_mu)
                option7_main(_msp, _mtt, _mmn, _mst, _mu)
        elif _mq in ["1", "2", "4", "5"]:
            for _mi, (_mt, _mu) in enumerate(_selected_events, 1):
                print(f"\n{BOLD_CYAN}{'─'*44}{RESET}")
                print(f"{BOLD_CYAN}[{_mi}/{len(_selected_events)}] {_mt}{RESET}")
                print(f"{BOLD_CYAN}{'─'*44}{RESET}")
                _msp = extract_slug_path(_mu)
                if not _msp:
                    print(f"{RED}Invalid URL, skipping.{RESET}")
                    continue
                _mtt, _mmn = extract_match_title(_mu)
                _mst = extract_stream_type(_mu)
                print(f"{DARK_MAGENTA}FETCHING STREAMS... PLEASE WAIT{RESET}")
                _m_entries = []
                _seen_bases: set = set()
                for _lc, _ln in UNIQUE_LANGUAGES.items():
                    try:
                        _mres = fetch_lang_stream(_lc, _ln, _msp, _mu, _mq_int)
                        if not _mres:
                            continue
                        _mpc = _mres["player_config"]
                        _is_hdr = _mres.get("is_hdr", False)
                        _clean_stream = _mres["stream"]
                        _lang_name = _mres["lang_name"] or _ln
                        if _mq_int == "1":
                            _ms4k = extract_4k_streams(_mpc)
                            if _ms4k:
                                _mu4k = _ms4k[0]["url"]
                                _base = _mu4k.split("?")[0]
                                if _base not in _seen_bases:
                                    _seen_bases.add(_base)
                                    _m_entries.append((_lang_name, _mu4k, _is_hdr))
                            else:
                                _base = _clean_stream.split("?")[0]
                                if _base not in _seen_bases:
                                    _seen_bases.add(_base)
                                    _m_entries.append((_lang_name, _clean_stream, _is_hdr))
                        else:
                            _base = _clean_stream.split("?")[0]
                            if _base not in _seen_bases:
                                _seen_bases.add(_base)
                                _m_entries.append((_lang_name, _clean_stream, _is_hdr))
                    except Exception:
                        continue
                if _m_entries:
                    for _mln, _mfu, _mhdr in _m_entries:
                        _htag = " HDR" if _mhdr else ""
                        print(f"\n{BOLD_CYAN}{_mln}{_htag}{RESET}")
                        print(f"{GREEN}{_mfu}{RESET}")
                else:
                    print(f"{YELLOW}No streams found for this event.{RESET}")
        else:
            print(f"{YELLOW}Invalid choice for multi-event mode.{RESET}")
        return None


# ===================== OPTIONS 5 & 6: H.264/H.265 4K DV+HDR+SDR (dv.py style) =====================

def _build_api_url_dv_style(slug_path: str, lang: str, dynamic_range: str, video_codec: str,
                             ads_mode: str = "non_ssai") -> str:
    """Build 4K API URL with specific dynamic range + codec (mirrors dv.py build_api_url).
    ads_mode: 'non_ssai' (clean ad-free URL, used by options 5/6) or 'ssai' (server-side-ad-insertion
    CDN pipeline — returns the playback_host/asn_id/si_match_id-style cookie URL, used by option 1)."""
    if dynamic_range == "dv":
        vc_list = ["dvh265", "h265"]
    else:
        vc_list = [video_codec]
    capabilities = {
        "ads": [ads_mode],
        "audio_channel": ["stereo", "dolby51", "atmos"],
        "container": ["fmp4", "fmp4br", "ts"],
        "dvr": ["short", "long"],
        "encryption": ["widevine", "plain"],
        "ladder": ["tv", "full"],
        "package": ["dash", "hls"],
        "resolution": ["sd", "hd", "fhd", "4k"],
        "true_resolution": ["4k"],
        "dynamic_range": [dynamic_range],
        "video_codec": vc_list,
        "video_codec_non_secure": vc_list + ["vp9"]
    }
    drm = {
        "hdcp_version": ["HDCP_V2_2"],
        "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"]
    }
    return (
        API_TEMPLATE.format(slug_path=slug_path)
        + "?search_query=live"
        + "&client_capabilities=" + parse.quote(json.dumps(capabilities, separators=(",", ":")))
        + "&drm_parameters=" + parse.quote(json.dumps(drm, separators=(",", ":")))
        + "&request_features=consent_supported"
        + "&lang=" + parse.quote(lang, safe="")
    )


def _extract_dv_assets(player_config: dict) -> list:
    """Extract assets with DR/codec detection (mirrors dv.py extract_all_assets)."""
    assets = []
    for key in ["media_asset", "media_asset_v2"]:
        asset_list = player_config.get(key)
        if not asset_list:
            continue
        if isinstance(asset_list, dict):
            asset_list = [asset_list]
        for asset in asset_list:
            for variant in ["primary", "fallback"]:
                item = asset.get(variant)
                if not isinstance(item, dict):
                    continue
                url = item.get("content_url")
                if not url:
                    continue
                codec = item.get("video_codec", "").lower()
                tags = str(item.get("playback_tags", "")).lower()
                if not codec:
                    if "h265" in tags or "hevc" in tags:
                        codec = "h265"
                    elif "h264" in tags or "avc" in tags:
                        codec = "h264"
                dr = "sdr"
                if codec in ("dvh265", "dvhe", "dvh1"):
                    dr = "dv"
                elif any(x in tags for x in ("dolby_vision", "dolbyvision", "dvh265")):
                    dr = "dv"
                elif any(x in tags for x in ("hdr10", "hdr_", "hdr10plus")) or "hdr10" in url.lower():
                    dr = "hdr10"
                elif any(x == "hdr" for x in re.split(r"[,\s]+", tags)):
                    dr = "hdr10"
                res = item.get("resolution", "").lower()
                height = int(item.get("height") or 0)
                assets.append({"url": url, "codec": codec, "dr": dr, "resolution": res, "height": height})
    return assets


def _select_dv_stream(assets: list, requested_dr: str, requested_codec: str) -> Optional[dict]:
    """Pick best resolution stream matching DR + codec."""
    res_order = {"4k": 3, "fhd": 2, "hd": 1, "sd": 0}
    def best(pool):
        if not pool:
            return None
        pool.sort(key=lambda x: (res_order.get(x["resolution"], 0), x["height"]), reverse=True)
        return pool[0]
    exact = [a for a in assets if a["dr"] == requested_dr and a["codec"] == requested_codec]
    if exact:
        return best(exact)
    dr_match = [a for a in assets if a["dr"] == requested_dr]
    if dr_match:
        return best(dr_match)
    return None


def _detect_real_lang_code(url: str) -> Optional[str]:
    """
    Detect the actual language code embedded in a stream URL's path segments
    (e.g. '.../inallow-indveng-2026/tel/...' → 'tel'). This is the only reliable
    signal for what language a Hotstar CDN stream really carries — the
    mediaselector API happily returns a fallback/default-language player_config
    for a lang= code it doesn't actually have, so the requested code alone
    cannot be trusted.
    """
    try:
        path_segs = set(url.split("?")[0].replace("https://", "").split("/"))
    except Exception:
        return None
    for seg in path_segs:
        seg_l = seg.lower()
        if seg_l in LANGUAGES:
            return seg_l
    return None


def _fetch_lang_dv_style(lang_code: str, lang_name: str, slug_path: str,
                          requested_dr: str, requested_codec: str,
                          lang_aliases: Optional[List[str]] = None,
                          ads_mode: str = "non_ssai") -> Optional[dict]:
    """
    Fetch one language stream with specific DR+codec using dv.py API style.
    Verifies the stream actually carries the requested language before
    returning it — Hotstar sometimes serves a different language's track as a
    fallback for an unsupported lang= code, which would otherwise show up as a
    fake/mislabeled duplicate. Any such mismatch is rejected here.
    """
    try:
        api_url = _build_api_url_dv_style(slug_path, lang_code, requested_dr, requested_codec, ads_mode=ads_mode)
        req = request.Request(api_url, headers=build_headers())
        with request.urlopen(req, timeout=15) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        player_config = None
        spaces = data.get("success", {}).get("page", {}).get("spaces", {})
        for s in spaces:
            for w in spaces[s].get("widget_wrappers", []):
                widget = w.get("widget", {})
                if "player_config" in widget.get("data", {}):
                    player_config = widget["data"]["player_config"]
                    break
            if player_config:
                break
        if not player_config:
            def _find_pc(obj):
                if isinstance(obj, dict):
                    if "player_config" in obj:
                        return obj["player_config"]
                    for v in obj.values():
                        r = _find_pc(v)
                        if r:
                            return r
                elif isinstance(obj, list):
                    for item in obj:
                        r = _find_pc(item)
                        if r:
                            return r
                return None
            player_config = _find_pc(data)
        if not player_config:
            return None
        assets = _extract_dv_assets(player_config)
        if not assets:
            return None
        selected = _select_dv_stream(assets, requested_dr, requested_codec)
        if not selected:
            return None
        real_code = _detect_real_lang_code(selected["url"])
        allowed_codes = {c.lower() for c in (lang_aliases or [lang_code])}
        if real_code and real_code not in allowed_codes:
            return None  # different language's track was served — reject as fake
        return {"lang_name": lang_name, "stream": selected["url"],
                "player_config": player_config, "actual_codec": selected["codec"]}
    except Exception:
        return None


def _find_license_url_dv(player_config: dict) -> Optional[str]:
    """Recursively search player_config for a license URL."""
    def _search(obj, depth=0):
        if depth > 6 or not isinstance(obj, (dict, list)):
            return None
        if isinstance(obj, list):
            for item in obj:
                r = _search(item, depth + 1)
                if r:
                    return r
        elif isinstance(obj, dict):
            for k in ["license_url", "licenseUrl", "widevine_license_url", "keyServerUrl", "key_server_url"]:
                if k in obj and obj[k]:
                    return str(obj[k])
            for v in obj.values():
                r = _search(v, depth + 1)
                if r:
                    return r
        return None
    return _search(player_config)


def collect_dv_hdr_sdr_entries(slug_path: str, requested_codec: str = "h265", ads_mode: str = "ssai") -> list:
    """
    Shared collector for the 4K DV/HDR10/SDR all-languages extractor used by
    option {1} (H.265 ADSFREE)/{5} (H.264)/{6} (H.265), and by AUTO-UPDATE MODE's
    quality {22} (H.265 4K ADSFREE DV,HDR,SDR) so the periodic refresh cycle gets
    the exact same per-language streams — including the liveNNmp- fallback to
    non_ssai for Haryanvi/Telugu, and the clean-CDN rewrite for everyone else.

    requested_codec: "h264" or "h265" (used for the SDR bucket only)
    ads_mode: "non_ssai" (clean a=ns&hdnea=... URL) or "ssai" (cookie-style
              a=s&asn_id=...&playback_host=... URL, with ADSFREE label suffix)

    Returns a flat list of (dr_key, label, stream_url) tuples, dr_key one of
    "hdr10"/"dv"/"sdr", deduplicated by base URL within each DR bucket.
    """
    lang_list = [
        ("ENGLISH",   ["eng", "en"]),
        ("HINDI",     ["hin", "hi", "hd"]),
        ("MARATHI",   ["mar", "mr", "ma"]),
        ("GUJARATI",  ["guj", "gu"]),
        ("BHOJPURI",  ["bih", "bho", "bh"]),
        ("PUNJABI",   ["pan", "pun", "pa", "pu"]),
        ("HARYANVI",  ["har", "hv", "ha"]),
        ("TAMIL",     ["tam", "ta"]),
        ("TELUGU",    ["tel", "te"]),
        ("KANNADA",   ["kan", "kn"]),
        ("MALAYALAM", ["mal", "ml"]),
        ("BENGALI",   ["ben", "bn"]),
    ]

    # DR order: HDR10 → Dolby Vision → SDR
    # HDR10 always uses h265 (same as dv.py); DV always dvh265; SDR uses requested_codec
    dr_configs = [
        ("hdr10", "h265",          "HDR10"),
        ("dv",    "dvh265",        "DOLBY VISION"),
        ("sdr",   requested_codec, "SDR"),
    ]

    # results[dr_key] = [(label, stream_url), ...]
    # Deduplicate within each DR bucket by base URL (path before '?') so that
    # languages sharing the same CDN stream aren't listed multiple times.
    seen_base: dict = {dr: set() for dr, _, _ in dr_configs}
    flat_entries: list = []

    for lang_name, lang_codes in lang_list:
        for req_dr, req_codec, dr_label in dr_configs:
            result = None
            for code in lang_codes:
                result = _fetch_lang_dv_style(code, lang_name, slug_path, req_dr, req_codec,
                                               lang_aliases=lang_codes, ads_mode=ads_mode)
                if result:
                    break
            if not result:
                continue
            stream_url = result["stream"]
            if ads_mode == "ssai":
                _host = urlparse(stream_url).hostname or ""
                if re.match(r"live\d+mp-", _host):
                    # This language's SSAI stream lives on the "liveNNmp-..." multi-package
                    # backend, which has no liveNNp.hotstar.com clean-CDN equivalent (different
                    # path namespace, /out/v1/...). The cookie-style URL doesn't work here, so
                    # fall back to the plain non-SSAI clean link (a=ns&hdnea=...) for this
                    # language/DR/codec instead, matching what worked before.
                    fallback_result = None
                    for code in lang_codes:
                        fallback_result = _fetch_lang_dv_style(code, lang_name, slug_path, req_dr, req_codec,
                                                                lang_aliases=lang_codes, ads_mode="non_ssai")
                        if fallback_result:
                            break
                    if fallback_result:
                        stream_url = fallback_result["stream"]
                    # else: keep the original (still-working-in-app) liveNNmp-ssai-... URL as last resort
                else:
                    # Rewrite the SSAI CDN host (e.g. live12p-ssai-akt-mum.cdn.hotstar.com) to the
                    # clean liveXXp.hotstar.com host, keeping all query params (asn_id, playback_host,
                    # si_match_id, hdnea, etc.) exactly as returned.
                    stream_url = rewrite_url_to_clean_cdn(stream_url)
            base_url = stream_url.split("?")[0]
            if base_url in seen_base[req_dr]:
                continue                          # duplicate CDN path → skip
            seen_base[req_dr].add(base_url)
            label = f"{lang_name} 4K {dr_label}"
            flat_entries.append((req_dr, label, stream_url))

    return flat_entries



def format_url_with_headers(url: str) -> str:
    """Append |Cookie=hdntl=...&User-Agent=...&Referer=...&Origin=... to a stream URL.
    Extracts hdnea token from URL query string and uses it as hdntl cookie value.
    Live stream URLs (hostname starts with 'live') are returned as-is without headers.
    """
    from urllib.parse import urlparse, parse_qs
    parsed = urlparse(url)
    # Live streams — return URL unchanged, no headers needed
    hostname = parsed.hostname or ""
    if hostname.startswith("live"):
        return url
    _UA  = "Hotstar;in.startv.hotstar/25.02.24.8.11169 (Android/15)"
    _REF = "https://www.hotstar.com/"
    _ORI = "https://www.hotstar.com"
    qs = parse_qs(parsed.query, keep_blank_values=True)
    hdnea = qs.get("hdnea", [None])[0]
    if hdnea:
        return f"{url}|Cookie=hdntl={hdnea}&User-Agent={_UA}&Referer={_REF}&Origin={_ORI}"
    else:
        return f"{url}|User-Agent={_UA}&Referer={_REF}&Origin={_ORI}"


def option_dv_hdr_sdr(input_url: str, requested_codec: str, ads_mode: str = "non_ssai") -> None:
    """
    Option {5} (H.264) / Option {6} (H.265) / Option {1} (H.265 ADSFREE, ssai cookie-style URLs):
    Fetches 4K streams for all languages across HDR10 → Dolby Vision → SDR.
    Prints a clean summary block (labels only) then a URL block (label + stream URL),
    both grouped by DR.  No hdntl/DRM/command noise.
    requested_codec: "h264" or "h265"
    ads_mode: "non_ssai" (default, options 5/6 — clean ad-free URL) or "ssai"
              (option 1 — returns the playback_host/asn_id/si_match_id cookie-style URL)
    """
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL.{RESET}")
        return

    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)

    # DR order: HDR10 → Dolby Vision → SDR (kept here to drive the print grouping below)
    dr_configs = [
        ("hdr10", "h265",          "HDR10"),
        ("dv",    "dvh265",        "DOLBY VISION"),
        ("sdr",   requested_codec, "SDR"),
    ]

    codec_label = requested_codec.upper()
    print(f"\n{BOLD_GREEN}=== HOTSTAR 4K DV/HDR/SDR EXTRACTOR [{codec_label}] ==={RESET}")
    print(f"{BOLD_YELLOW}Fetching all languages... please wait{RESET}\n")

    # ── Collect phase ──────────────────────────────────────────────────────────
    results: dict = {dr: [] for dr, _, _ in dr_configs}
    raw_collected = list(collect_dv_hdr_sdr_entries(slug_path, requested_codec, ads_mode))
    for req_dr, label, stream_url in raw_collected:
        results[req_dr].append((label, stream_url))

    # ── Embed 30-min hdntl cookie in URL (only for ssai / option 1 ADSFREE) ──
    if ads_mode == "ssai":
        _all_labels_urls = {}
        for req_dr, label, stream_url in raw_collected:
            _all_labels_urls[label] = stream_url
        _embedded_dv = {}
        with ThreadPoolExecutor(max_workers=len(_all_labels_urls) or 1) as _emb_ex_dv:
            _emb_futs_dv = {_emb_ex_dv.submit(_embed_hdntl_in_url, _u): _l for _l, _u in _all_labels_urls.items()}
            for _emb_f_dv in as_completed(_emb_futs_dv):
                _l_dv = _emb_futs_dv[_emb_f_dv]
                try:
                    _embedded_dv[_l_dv] = _emb_f_dv.result()
                except Exception:
                    _embedded_dv[_l_dv] = _all_labels_urls[_l_dv]
        # Replace results with hdntl-embedded URLs
        results = {dr: [] for dr, _, _ in dr_configs}
        for req_dr, label, stream_url in raw_collected:
            results[req_dr].append((label, _embedded_dv.get(label, stream_url)))

    # ── Header ────────────────────────────────────────────────────────────────
    print(f"{BOLD_GREEN}{title}{RESET}")
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print()

    # ── URL block (label + stream URL, grouped by DR) ─────────────────────────
    for req_dr, _, dr_label in dr_configs:
        for label, stream_url in results[req_dr]:
            print(f"{BOLD_CYAN}{label}{RESET}")
            print(format_url_with_headers(stream_url))

    print(f"{BOLD_GREEN}Done.{RESET}")


# ===================== OPTION 3: H.265 AUTO ADSFREE DV+HDR+SDR (4K first, FHD fallback) =====================

def collect_auto_dv_hdr_sdr_entries(slug_path: str) -> list:
    """
    Option {3}: per language+DR, tries 4K (H.265 ssai) first; if no 4K stream found
    falls back to FHD (H.265 ssai). Applies same CDN rewrite as options {1}/{2}.
    Returns flat list of (dr_key, label, stream_url) — hdntl NOT yet embedded.
    """
    lang_list = [
        ("ENGLISH",   ["eng", "en"]),
        ("HINDI",     ["hin", "hi", "hd"]),
        ("MARATHI",   ["mar", "mr", "ma"]),
        ("GUJARATI",  ["guj", "gu"]),
        ("BHOJPURI",  ["bih", "bho", "bh"]),
        ("PUNJABI",   ["pan", "pun", "pa", "pu"]),
        ("HARYANVI",  ["har", "hv", "ha"]),
        ("TAMIL",     ["tam", "ta"]),
        ("TELUGU",    ["tel", "te"]),
        ("KANNADA",   ["kan", "kn"]),
        ("MALAYALAM", ["mal", "ml"]),
        ("BENGALI",   ["ben", "bn"]),
    ]
    dr_configs = [
        ("hdr10", "h265",   "HDR10"),
        ("dv",    "dvh265", "DOLBY VISION"),
        ("sdr",   "h265",   "SDR"),
    ]
    seen_base: dict = {dr: set() for dr, _, _ in dr_configs}
    flat_entries: list = []

    for lang_name, lang_codes in lang_list:
        for req_dr, req_codec, dr_label in dr_configs:
            # ── 1. Try 4K first ──
            result_4k = None
            for code in lang_codes:
                result_4k = _fetch_lang_dv_style(code, lang_name, slug_path, req_dr, req_codec,
                                                  lang_aliases=lang_codes, ads_mode="ssai")
                if result_4k:
                    break
            if result_4k:
                stream_url = result_4k["stream"]
                _h4k = urlparse(stream_url).hostname or ""
                if re.match(r"live\d+mp-", _h4k):
                    _fb4k = None
                    for code in lang_codes:
                        _fb4k = _fetch_lang_dv_style(code, lang_name, slug_path, req_dr, req_codec,
                                                      lang_aliases=lang_codes, ads_mode="non_ssai")
                        if _fb4k:
                            break
                    if _fb4k:
                        stream_url = _fb4k["stream"]
                else:
                    stream_url = rewrite_url_to_clean_cdn(stream_url)
                base_url = stream_url.split("?")[0]
                if base_url in seen_base[req_dr]:
                    continue
                seen_base[req_dr].add(base_url)
                flat_entries.append((req_dr, f"{lang_name} 4K {dr_label} ADSFREE", stream_url))
                continue

            # ── 2. 4K not found → try FHD ──
            result_fhd = None
            for code in lang_codes:
                result_fhd = _fetch_lang_fhd_style(code, lang_name, slug_path, req_dr, req_codec,
                                                    lang_aliases=lang_codes, ads_mode="ssai")
                if result_fhd:
                    break
            if not result_fhd:
                continue
            stream_url = result_fhd["stream"]
            _hfhd = urlparse(stream_url).hostname or ""
            if re.match(r"live\d+mp-", _hfhd):
                _fb_fhd = None
                for code in lang_codes:
                    _fb_fhd = _fetch_lang_fhd_style(code, lang_name, slug_path, req_dr, req_codec,
                                                     lang_aliases=lang_codes, ads_mode="non_ssai")
                    if _fb_fhd:
                        break
                if _fb_fhd:
                    stream_url = _fb_fhd["stream"]
            else:
                stream_url = rewrite_url_to_clean_cdn(stream_url)
            base_url = stream_url.split("?")[0]
            if base_url in seen_base[req_dr]:
                continue
            seen_base[req_dr].add(base_url)
            flat_entries.append((req_dr, f"{lang_name} FHD {dr_label}", stream_url))

    return flat_entries


def option_auto_dv_hdr_sdr(input_url: str) -> None:
    """
    Option {3} — H.265 AUTO DV,HDR,SDR ADSFREE:
    Per language tries 4K first; falls back to FHD if 4K unavailable.
    Embeds 30-min hdntl cookie in every URL.
    """
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL.{RESET}")
        return
    title, match_no = extract_match_title(input_url)
    dr_configs = [
        ("hdr10", "h265",   "HDR10"),
        ("dv",    "dvh265", "DOLBY VISION"),
        ("sdr",   "h265",   "SDR"),
    ]
    print(f"\n{BOLD_GREEN}=== HOTSTAR AUTO DV/HDR/SDR EXTRACTOR [H265 | 4K→FHD] ==={RESET}")
    print(f"{BOLD_YELLOW}Fetching all languages... please wait{RESET}\n")

    raw_collected = list(collect_auto_dv_hdr_sdr_entries(slug_path))
    results: dict = {dr: [] for dr, _, _ in dr_configs}
    for req_dr, label, stream_url in raw_collected:
        results[req_dr].append((label, stream_url))

    # Embed 30-min hdntl cookie in every URL
    _all_auto = {label: su for _, label, su in raw_collected}
    _emb_auto = {}
    with ThreadPoolExecutor(max_workers=len(_all_auto) or 1) as _emb_a_ex:
        _emb_a_futs = {_emb_a_ex.submit(_embed_hdntl_in_url, _u): _l for _l, _u in _all_auto.items()}
        for _emb_a_f in as_completed(_emb_a_futs):
            _l_a = _emb_a_futs[_emb_a_f]
            try:
                _emb_auto[_l_a] = _emb_a_f.result()
            except Exception:
                _emb_auto[_l_a] = _all_auto[_l_a]

    results = {dr: [] for dr, _, _ in dr_configs}
    for req_dr, label, stream_url in raw_collected:
        results[req_dr].append((label, _emb_auto.get(label, stream_url)))

    print(f"{BOLD_GREEN}{title}{RESET}")
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print()

    # HLS FALLBACK for all languages — same embedded hdntl cookie style as option 3
    _fb3_lang_list = [
        ("ENGLISH",   ["eng", "en"]),
        ("HINDI",     ["hin", "hi", "hd"]),
        ("MARATHI",   ["mar", "mr", "ma"]),
        ("GUJARATI",  ["guj", "gu"]),
        ("BHOJPURI",  ["bih", "bho", "bh"]),
        ("PUNJABI",   ["pan", "pun", "pa", "pu"]),
        ("HARYANVI",  ["har", "hv", "ha"]),
        ("TAMIL",     ["tam", "ta"]),
        ("TELUGU",    ["tel", "te"]),
        ("KANNADA",   ["kan", "kn"]),
        ("MALAYALAM", ["mal", "ml"]),
        ("BENGALI",   ["ben", "bn"]),
    ]
    _fb3_raw = {}
    _fb3_lock = threading.Lock()

    def _fetch_fb3_lang(lang_name, lang_codes):
        for code in lang_codes:
            try:
                _pc3 = fetch_player_config_for_slug(slug_path, code)
                _sts3 = extract_all_streams_general(_pc3)
                for _s3 in _sts3:
                    _u3 = _s3.get("url", "")
                    if not _u3 or ".m3u8" not in _u3:
                        continue
                    if is_blacklisted_cdn(urlparse(_u3).netloc):
                        continue
                    if _s3["type"] == "fallback":
                        with _fb3_lock:
                            _fb3_raw[lang_name] = _u3
                        return
            except Exception:
                continue

    with ThreadPoolExecutor(max_workers=4) as _fb3_ex:
        _fb3_futs = [_fb3_ex.submit(_fetch_fb3_lang, ln, lc) for ln, lc in _fb3_lang_list]
        for _ff3 in as_completed(_fb3_futs):
            try: _ff3.result()
            except: pass

    _fb3_emb = {}
    if _fb3_raw:
        with ThreadPoolExecutor(max_workers=len(_fb3_raw)) as _fb3_emb_ex:
            _fb3_emb_futs = {_fb3_emb_ex.submit(_embed_hdntl_in_url, _u): _ln for _ln, _u in _fb3_raw.items()}
            for _fef3 in as_completed(_fb3_emb_futs):
                _ln3 = _fb3_emb_futs[_fef3]
                try:
                    _fb3_emb[_ln3] = _fef3.result()
                except Exception:
                    _fb3_emb[_ln3] = _fb3_raw[_ln3]

    _fb3_seen_raw = set()
    for _ln3, _lc3 in _fb3_lang_list:
        if _ln3 in _fb3_emb:
            _raw_base3 = _fb3_raw.get(_ln3, "").split("?")[0]
            if _raw_base3 and _raw_base3 in _fb3_seen_raw:
                continue
            if _raw_base3:
                _fb3_seen_raw.add(_raw_base3)
            print(f"{BOLD_CYAN}{_ln3} FHD SDR [FALLBACK]{RESET}")
            print(format_url_with_headers(_fb3_emb[_ln3]))

    print(f"{BOLD_GREEN}Done.{RESET}")


# ===================== OPTIONS 2, 7 & 8: FHD DV+HDR+SDR (dv.py FHD style) =====================

def _build_api_url_fhd_style(slug_path: str, lang: str, dynamic_range: str, video_codec: str,
                              ads_mode: str = "non_ssai") -> str:
    """Build FHD API URL with specific dynamic range + codec (mirrors dv.py FHD branch)."""
    if dynamic_range == "dv":
        vc_list = ["dvh265", "h265"]
    else:
        vc_list = [video_codec]
    capabilities = {
        "ads": ["non_ssai", "ssai"],
        "audio_channel": ["stereo"],
        "container": ["fmp4", "fmp4br", "ts"],
        "dvr": ["short"],
        "encryption": ["widevine", "plain"],
        "ladder": ["web", "tv", "phone"],
        "package": ["dash", "hls"],
        "resolution": ["sd", "hd", "fhd"],
        "true_resolution": ["fhd"],
        "dynamic_range": [dynamic_range],
        "video_codec": vc_list,
        "video_codec_non_secure": vc_list
    }
    drm = {
        "hdcp_version": ["HDCP_V2_2"],
        "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"]
    }
    return (
        API_TEMPLATE.format(slug_path=slug_path)
        + "?search_query=live"
        + "&client_capabilities=" + parse.quote(json.dumps(capabilities, separators=(",", ":")))
        + "&drm_parameters=" + parse.quote(json.dumps(drm, separators=(",", ":")))
        + "&request_features=consent_supported"
        + "&lang=" + parse.quote(lang, safe="")
    )


def _fetch_lang_fhd_style(lang_code: str, lang_name: str, slug_path: str,
                           requested_dr: str, requested_codec: str,
                           lang_aliases: Optional[List[str]] = None,
                           ads_mode: str = "non_ssai") -> Optional[dict]:
    """Fetch one FHD language stream with specific DR+codec (mirrors _fetch_lang_dv_style but FHD caps)."""
    try:
        api_url = _build_api_url_fhd_style(slug_path, lang_code, requested_dr, requested_codec, ads_mode=ads_mode)
        req = request.Request(api_url, headers=build_headers())
        with request.urlopen(req, timeout=15) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        player_config = None
        spaces = data.get("success", {}).get("page", {}).get("spaces", {})
        for s in spaces:
            for w in spaces[s].get("widget_wrappers", []):
                widget = w.get("widget", {})
                if "player_config" in widget.get("data", {}):
                    player_config = widget["data"]["player_config"]
                    break
            if player_config:
                break
        if not player_config:
            def _find_pc_fhd(obj):
                if isinstance(obj, dict):
                    if "player_config" in obj:
                        return obj["player_config"]
                    for v in obj.values():
                        r = _find_pc_fhd(v)
                        if r:
                            return r
                elif isinstance(obj, list):
                    for item in obj:
                        r = _find_pc_fhd(item)
                        if r:
                            return r
                return None
            player_config = _find_pc_fhd(data)
        if not player_config:
            return None
        assets = _extract_dv_assets(player_config)
        if not assets:
            return None
        selected = _select_dv_stream(assets, requested_dr, requested_codec)
        if not selected:
            return None
        real_code = _detect_real_lang_code(selected["url"])
        allowed_codes = {c.lower() for c in (lang_aliases or [lang_code])}
        if real_code and real_code not in allowed_codes:
            return None
        return {"lang_name": lang_name, "stream": selected["url"],
                "player_config": player_config, "actual_codec": selected["codec"]}
    except Exception:
        return None


def collect_fhd_dv_hdr_sdr_entries(slug_path: str, requested_codec: str = "h265", ads_mode: str = "non_ssai") -> list:
    """
    FHD version of collect_dv_hdr_sdr_entries.
    Used by option {2} (H.265 FHD ADSFREE), {7} (H.264 FHD), {8} (H.265 FHD).
    Returns a flat list of (dr_key, label, stream_url) tuples.
    """
    lang_list = [
        ("ENGLISH",   ["eng", "en"]),
        ("HINDI",     ["hin", "hi", "hd"]),
        ("MARATHI",   ["mar", "mr", "ma"]),
        ("GUJARATI",  ["guj", "gu"]),
        ("BHOJPURI",  ["bih", "bho", "bh"]),
        ("PUNJABI",   ["pan", "pun", "pa", "pu"]),
        ("HARYANVI",  ["har", "hv", "ha"]),
        ("TAMIL",     ["tam", "ta"]),
        ("TELUGU",    ["tel", "te"]),
        ("KANNADA",   ["kan", "kn"]),
        ("MALAYALAM", ["mal", "ml"]),
        ("BENGALI",   ["ben", "bn"]),
    ]
    dr_configs = [
        ("hdr10", "h265",          "HDR10"),
        ("dv",    "dvh265",        "DOLBY VISION"),
        ("sdr",   requested_codec, "SDR"),
    ]
    seen_base: dict = {dr: set() for dr, _, _ in dr_configs}
    flat_entries: list = []

    for lang_name, lang_codes in lang_list:
        for req_dr, req_codec, dr_label in dr_configs:
            result = None
            for code in lang_codes:
                result = _fetch_lang_fhd_style(code, lang_name, slug_path, req_dr, req_codec,
                                               lang_aliases=lang_codes, ads_mode=ads_mode)
                if result:
                    break
            if not result:
                continue
            stream_url = result["stream"]
            # CDN fallback — mirrors collect_dv_hdr_sdr_entries ssai logic
            if ads_mode == "ssai":
                _fhd_cdn_host = urlparse(stream_url).hostname or ""
                if re.match(r"live\d+mp-", _fhd_cdn_host):
                    # liveNNmp- multi-package backend has no clean-CDN equivalent — fallback to non_ssai
                    _fhd_fb = None
                    for code in lang_codes:
                        _fhd_fb = _fetch_lang_fhd_style(code, lang_name, slug_path, req_dr, req_codec,
                                                         lang_aliases=lang_codes, ads_mode="non_ssai")
                        if _fhd_fb:
                            break
                    if _fhd_fb:
                        stream_url = _fhd_fb["stream"]
                else:
                    stream_url = rewrite_url_to_clean_cdn(stream_url)
            base_url = stream_url.split("?")[0]
            if base_url in seen_base[req_dr]:
                continue
            seen_base[req_dr].add(base_url)
            label = f"{lang_name} FHD {dr_label}"
            flat_entries.append((req_dr, label, stream_url))

    return flat_entries


def option_fhd_dv_hdr_sdr(input_url: str, requested_codec: str, ads_mode: str = "non_ssai") -> None:
    """
    Option {2} (H.265 FHD DV,HDR,SDR) / Option {7} (H.264 FHD) / Option {8} (H.265 FHD):
    Fetches FHD streams for all languages across HDR10 → Dolby Vision → SDR.
    requested_codec: "h264" or "h265"
    ads_mode: "non_ssai" (options 7/8 — clean URLs) or "ssai" (option 2 — FHD + 30-min hdntl embed)
    """
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL.{RESET}")
        return

    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)

    dr_configs = [
        ("hdr10", "h265",          "HDR10"),
        ("dv",    "dvh265",        "DOLBY VISION"),
        ("sdr",   requested_codec, "SDR"),
    ]

    codec_label = requested_codec.upper()
    print(f"\n{BOLD_GREEN}=== HOTSTAR FHD DV/HDR/SDR EXTRACTOR [{codec_label}] ==={RESET}")
    print(f"{BOLD_YELLOW}Fetching all languages... please wait{RESET}\n")

    raw_collected = list(collect_fhd_dv_hdr_sdr_entries(slug_path, requested_codec, ads_mode))
    results: dict = {dr: [] for dr, _, _ in dr_configs}
    for req_dr, label, stream_url in raw_collected:
        results[req_dr].append((label, stream_url))

    # Embed 30-min hdntl cookie in URL (only for ssai / option 2 FHD)
    if ads_mode == "ssai":
        _all_fhd_lbl_url = {}
        for req_dr, label, stream_url in raw_collected:
            _all_fhd_lbl_url[label] = stream_url
        _embedded_fhd_op = {}
        with ThreadPoolExecutor(max_workers=len(_all_fhd_lbl_url) or 1) as _emb_ex_fhd:
            _emb_futs_fhd = {_emb_ex_fhd.submit(_embed_hdntl_in_url, _u): _l for _l, _u in _all_fhd_lbl_url.items()}
            for _emb_f_fhd in as_completed(_emb_futs_fhd):
                _l_fhd = _emb_futs_fhd[_emb_f_fhd]
                try:
                    _embedded_fhd_op[_l_fhd] = _emb_f_fhd.result()
                except Exception:
                    _embedded_fhd_op[_l_fhd] = _all_fhd_lbl_url[_l_fhd]
        results = {dr: [] for dr, _, _ in dr_configs}
        for req_dr, label, stream_url in raw_collected:
            results[req_dr].append((label, _embedded_fhd_op.get(label, stream_url)))

    print(f"{BOLD_GREEN}{title}{RESET}")
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print()

    # HLS FALLBACK for all languages — only for option 2 (ssai), same embedded hdntl cookie style
    if ads_mode == "ssai":
        _fb2_lang_list = [
            ("ENGLISH",   ["eng", "en"]),
            ("HINDI",     ["hin", "hi", "hd"]),
            ("MARATHI",   ["mar", "mr", "ma"]),
            ("GUJARATI",  ["guj", "gu"]),
            ("BHOJPURI",  ["bih", "bho", "bh"]),
            ("PUNJABI",   ["pan", "pun", "pa", "pu"]),
            ("HARYANVI",  ["har", "hv", "ha"]),
            ("TAMIL",     ["tam", "ta"]),
            ("TELUGU",    ["tel", "te"]),
            ("KANNADA",   ["kan", "kn"]),
            ("MALAYALAM", ["mal", "ml"]),
            ("BENGALI",   ["ben", "bn"]),
        ]
        _fb2_raw = {}
        _fb2_lock = threading.Lock()

        def _fetch_fb2_lang(lang_name, lang_codes):
            for code in lang_codes:
                try:
                    _pc2 = fetch_player_config_for_slug(slug_path, code)
                    _sts2 = extract_all_streams_general(_pc2)
                    for _s2 in _sts2:
                        _u2 = _s2.get("url", "")
                        if not _u2 or ".m3u8" not in _u2:
                            continue
                        if is_blacklisted_cdn(urlparse(_u2).netloc):
                            continue
                        if _s2["type"] == "fallback":
                            with _fb2_lock:
                                _fb2_raw[lang_name] = _u2
                            return
                except Exception:
                    continue

        with ThreadPoolExecutor(max_workers=4) as _fb2_ex:
            _fb2_futs = [_fb2_ex.submit(_fetch_fb2_lang, ln, lc) for ln, lc in _fb2_lang_list]
            for _ff2 in as_completed(_fb2_futs):
                try: _ff2.result()
                except: pass

        _fb2_emb = {}
        if _fb2_raw:
            with ThreadPoolExecutor(max_workers=len(_fb2_raw)) as _fb2_emb_ex:
                _fb2_emb_futs = {_fb2_emb_ex.submit(_embed_hdntl_in_url, _u): _ln for _ln, _u in _fb2_raw.items()}
                for _fef2 in as_completed(_fb2_emb_futs):
                    _ln2 = _fb2_emb_futs[_fef2]
                    try:
                        _fb2_emb[_ln2] = _fef2.result()
                    except Exception:
                        _fb2_emb[_ln2] = _fb2_raw[_ln2]

        _fb2_seen_raw = set()
        for _ln2, _lc2 in _fb2_lang_list:
            if _ln2 in _fb2_emb:
                _raw_base2 = _fb2_raw.get(_ln2, "").split("?")[0]
                if _raw_base2 and _raw_base2 in _fb2_seen_raw:
                    continue
                if _raw_base2:
                    _fb2_seen_raw.add(_raw_base2)
                print(f"{BOLD_CYAN}{_ln2} FHD SDR [FALLBACK]{RESET}")
                print(format_url_with_headers(_fb2_emb[_ln2]))

    print(f"{BOLD_GREEN}Done.{RESET}")


def fetch_live_events(debug: bool = False) -> tuple:
    """
    Fetch currently live events from the Hotstar live-now editorial page.

    Uses GET /api/internal/bff/v2/slugs/in/browse/editorial/live-now/1271392364
    — the same slugs API used for individual content pages, which returns the
    editorial tray directly without a profile-selection gate.

    Returns (list of (title, url) tuples, error_string).
    """
    events: list = []
    token = load_user_token()

    # ── Android TV headers (same stack that works for stream fetching) ─────────
    hdrs = {
        "User-Agent": "Hotstar;in.startv.hotstar.dplus.tv/26.05.10.2 (Android/14; tv)",
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en",
        "X-HS-Platform": "androidtv",
        "X-Country-Code": "in",
        "X-HS-Accept-language": "eng",
        "x-hs-app": "260510002",
        "x-hs-retry-count": "0",
        "x-hs-is-retry": "false",
        "X-HS-Client": (
            "platform:androidtv;app_id:in.startv.hotstar.dplus.tv;"
            "app_version:26.05.10.2;os:Android;os_version:14;schema_version:0.0.1690"
        ),
        "Referer": "https://www.hotstar.com/in/browse/editorial/live-now/1271392364",
        "Origin": "https://www.hotstar.com",
        "Pragma": "no-cache",
        "Cache-Control": "no-cache",
    }
    if token:
        hdrs["x-hs-usertoken"] = token

    # Build GET URL with capabilities
    live_url = (
        _LIVE_SLUGS_API
        + "?client_capabilities=" + parse.quote(_LIVE_CAPABILITIES)
        + "&drm_parameters=" + parse.quote(_LIVE_DRM)
        + "&request_features=consent_supported"
        + "&lang=eng"
    )

    _last_err = ""
    try:
        req = request.Request(live_url, headers=hdrs, method="GET")
        with request.urlopen(req, timeout=15) as resp:
            body_bytes = resp.read()
            status = resp.status
            ct = resp.headers.get("Content-Type", "")

        if debug:
            print(f"[LIVE] HTTP {status}  ct={ct[:30]}  len={len(body_bytes)}")

        try:
            data = json.loads(body_bytes.decode("utf-8", errors="replace"))
        except Exception as je:
            if debug:
                print(f"[LIVE] JSON parse fail: {je}  body[:120]={body_bytes[:120]}")
            return events, f"json:{je}"

        if debug:
            print(f"[LIVE] top keys: {list(data.keys())}")

        spaces = (data.get("success") or {}).get("page", {}).get("spaces", {})

        if debug:
            print(f"[LIVE] spaces keys: {list(spaces.keys())}")
            for sname, sval in spaces.items():
                if isinstance(sval, dict):
                    ww = sval.get("widget_wrappers") or []
                    print(f"[LIVE]   space={sname!r} widget_wrappers={len(ww)}")
                    for wi, wr in enumerate(ww[:3]):
                        w_data = (wr.get("widget") or {}).get("data") or {}
                        items = []
                        for k in ("items", "cards", "assets", "tray", "content"):
                            v = w_data.get(k)
                            if isinstance(v, list):
                                items = v
                                break
                        print(f"[LIVE]     wrapper[{wi}] data keys={list(w_data.keys())[:8]} items={len(items)}")

        events = _collect_events_from_spaces(spaces)

        if debug:
            print(f"[LIVE] events found: {len(events)}")

    except Exception as exc:
        import traceback as _tb
        _last_err = str(exc)
        if debug:
            print(f"[LIVE] exception type={type(exc).__name__} msg={exc}")
            _tb.print_exc()
        return events, _last_err

    return events, ""


def proxy_checker():
    """
    Proxy Checker — tests each proxy from a .txt file against JioHotstar.
    Working proxies saved to ok-proxy.txt with latency (ms).
    """
    DEFAULT_PATH = "/storage/emulated/0/Download/proxies.txt"
    TEST_URL = "https://www.hotstar.com/in"
    OUTPUT_FILE = "ok-proxy.txt"

    print(f"\n{BOLD_CYAN}╔══════════════════════════════════════════╗{RESET}")
    print(f"{BOLD_CYAN}║        🌐  PROXY CHECKER                 ║{RESET}")
    print(f"{BOLD_CYAN}║  Tests proxies against JioHotstar        ║{RESET}")
    print(f"{BOLD_CYAN}╚══════════════════════════════════════════╝{RESET}\n")

    # Ask for proxy file path
    path_input = input(
        f"{BOLD_CYAN}Proxy file path {GRAY}[default: {DEFAULT_PATH}]{RESET}\n"
        f"{BOLD_CYAN}➤ {RESET}"
    ).strip()
    proxy_file = path_input if path_input else DEFAULT_PATH

    if not os.path.isfile(proxy_file):
        print(f"{RED}✗ File not found: {proxy_file}{RESET}")
        return

    # Read proxies — support ip:port and http://ip:port
    raw_lines = []
    try:
        with open(proxy_file, "r", encoding="utf-8") as f:
            raw_lines = [l.strip() for l in f if l.strip() and not l.strip().startswith("#")]
    except Exception as e:
        print(f"{RED}✗ Cannot read file: {e}{RESET}")
        return

    proxies_list = []
    for line in raw_lines:
        # Normalize to "ip:port"
        if line.startswith("http://") or line.startswith("https://"):
            line = line.split("//", 1)[1]
        line = line.split("/")[0]  # strip any path
        if ":" in line:
            proxies_list.append(line)

    if not proxies_list:
        print(f"{RED}✗ No valid proxies found (expected ip:port per line){RESET}")
        return

    print(f"{GREEN}✓ Loaded {len(proxies_list)} proxies from {proxy_file}{RESET}")
    print(f"{BOLD_YELLOW}Checking against: {TEST_URL}{RESET}")
    print(f"{GRAY}Timeout: 10s per proxy  |  Parallel workers: 30{RESET}\n")

    working = []   # (proxy_str, latency_ms)
    failed  = []
    lock = threading.Lock()
    done_count = [0]

    def _check(proxy_str):
        proxy_dict = {
            "http":  f"http://{proxy_str}",
            "https": f"http://{proxy_str}",
        }
        t0 = time.time()
        try:
            import requests as _req
            resp = _req.get(
                TEST_URL,
                proxies=proxy_dict,
                timeout=10,
                allow_redirects=True,
                headers={"User-Agent": "Mozilla/5.0"},
                verify=False,
            )
            ms = int((time.time() - t0) * 1000)
            ok = resp.status_code in (200, 301, 302, 403)  # 403 = site reached, blocked login is fine
            with lock:
                done_count[0] += 1
                dc = done_count[0]
                total = len(proxies_list)
                if ok:
                    working.append((proxy_str, ms))
                    print(f"  {GREEN}✓{RESET} {WHITE}{proxy_str:<28}{RESET}  {GREEN}{ms} ms{RESET}  [{dc}/{total}]")
                else:
                    failed.append(proxy_str)
                    print(f"  {RED}✗{RESET} {GRAY}{proxy_str:<28}{RESET}  HTTP {resp.status_code}  [{dc}/{total}]")
        except Exception as e:
            ms = int((time.time() - t0) * 1000)
            with lock:
                done_count[0] += 1
                dc = done_count[0]
                total = len(proxies_list)
                failed.append(proxy_str)
                _emsg = str(e)[:50]
                print(f"  {RED}✗{RESET} {GRAY}{proxy_str:<28}{RESET}  {_emsg}  [{dc}/{total}]")

    t_start = time.time()
    with ThreadPoolExecutor(max_workers=min(30, len(proxies_list))) as ex:
        futs = [ex.submit(_check, p) for p in proxies_list]
        for f in as_completed(futs):
            pass
    elapsed = time.time() - t_start

    # Sort working by latency
    working.sort(key=lambda x: x[1])

    print(f"\n{BOLD_CYAN}{'─'*50}{RESET}")
    print(f"{BOLD_GREEN}✓ Working: {len(working)}/{len(proxies_list)}  ({elapsed:.1f}s){RESET}")
    print(f"{BOLD_RED}✗ Failed : {len(failed)}{RESET}")

    if working:
        try:
            with open(OUTPUT_FILE, "w", encoding="utf-8") as f:
                f.write(f"# Proxy check — {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
                f.write(f"# Test URL: {TEST_URL}\n")
                f.write(f"# Working: {len(working)}/{len(proxies_list)}\n\n")
                for proxy_str, ms in working:
                    f.write(f"{proxy_str}  # {ms} ms\n")
            print(f"\n{GREEN}✓ Saved to: {BOLD_WHITE}{OUTPUT_FILE}{RESET}")
            print(f"\n{BOLD_CYAN}Working proxies (sorted by speed):{RESET}")
            for proxy_str, ms in working:
                bar = "█" * min(int(ms / 100), 20)
                color = GREEN if ms < 500 else YELLOW if ms < 1500 else RED
                print(f"  {color}{proxy_str:<28}{RESET}  {color}{ms:>5} ms  {bar}{RESET}")
        except Exception as e:
            print(f"{RED}✗ Could not save output: {e}{RESET}")
    else:
        print(f"\n{YELLOW}⚠ No working proxies found.{RESET}")


def proxy_api_caller():
    """
    Proxy API Caller — reads working proxies from a .txt file, tests each one
    against a real Hotstar API endpoint.

    Auto-detects proxy type by port number:
      SOCKS ports  (1080,4153,4145,5678,9050,1085,9100,10808) → SOCKS4 first, then SOCKS5
      HTTP ports   (80,8080,3128,8888,8118,8123,8000,8118)    → HTTP only
      Unknown port → SOCKS4 → SOCKS5 → HTTP

    Requires PySocks for SOCKS support — auto-installs if missing.
    Only saves proxies that return genuine Hotstar API JSON (success key present).
    """
    import zipfile
    import warnings

    # ── Suppress SSL warnings ──────────────────────────────────────────────────
    try:
        import urllib3
        urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
    except Exception:
        pass

    # ── Auto-install PySocks (needed for socks4:// / socks5:// in requests) ───
    _socks_ok = False
    try:
        import socks  # noqa: F401
        _socks_ok = True
    except ImportError:
        print(f"{BOLD_YELLOW}⚙ PySocks not found — installing (needed for SOCKS proxies)...{RESET}")
        try:
            subprocess.run(
                [sys.executable, "-m", "pip", "install", "--quiet", "requests[socks]"],
                check=True, timeout=60,
            )
            import socks  # noqa: F401
            _socks_ok = True
            print(f"{GREEN}✓ PySocks installed OK{RESET}")
        except Exception as _e:
            print(f"{YELLOW}⚠ Could not install PySocks ({_e}). SOCKS proxies will be skipped.{RESET}")

    DEFAULT_PATH = "/storage/emulated/0/Download/ok-proxy.txt"
    OUTPUT_FILE  = "workingproxy.txt"
    OUTPUT_ZIP   = "workingproxy.zip"

    # Hotstar internal BFF — HTTPS only (plain HTTP is rejected by Hotstar)
    TEST_API_URL = (
        "https://www.hotstar.com/api/internal/bff/v2/slugs/in/browse/editorial/"
        "best-in-sports/6517?client_capabilities=%7B%22ads%22%3A%5B%22non_ssai%22%5D"
        "%2C%22audio_channel%22%3A%5B%22stereo%22%5D%2C%22container%22%3A%5B%22fmp4%22"
        "%2C%22fmp4br%22%2C%22ts%22%5D%2C%22dvr%22%3A%5B%22short%22%5D%2C%22dynamic_range"
        "%22%3A%5B%22sdr%22%5D%2C%22encryption%22%3A%5B%22plain%22%5D%2C%22ladder%22%3A"
        "%5B%22phone%22%2C%22web%22%5D%2C%22package%22%3A%5B%22hls%22%2C%22dash%22%5D"
        "%2C%22resolution%22%3A%5B%22sd%22%2C%22hd%22%2C%22fhd%22%5D%2C%22video_codec%22"
        "%3A%5B%22h264%22%5D%2C%22video_codec_non_secure%22%3A%5B%22h265%22%2C%22h264%22"
        "%5D%7D&drm_parameters=%7B%22hdcp_version%22%3A%5B%22HDCP_V2_2%22%5D%2C"
        "%22widevine_security_level%22%3A%5B%22SW_SECURE_DECODE%22%2C%22SW_SECURE_CRYPTO"
        "%22%5D%7D&request_features=consent_supported&lang=eng"
    )

    # ── Optional user token ───────────────────────────────────────────────────
    # Without a token Hotstar returns different JSON (no "success" key) so we
    # ask for the token file path here; skip with Enter to test without token.
    _token_str = ""
    _token_candidates = ["token1.txt", "token.txt",
                         "/storage/emulated/0/Download/token1.txt",
                         "/storage/emulated/0/Download/token.txt"]
    _auto_token = ""
    for _tc in _token_candidates:
        if os.path.isfile(_tc):
            try:
                _auto_token = open(_tc, encoding="utf-8").read().strip()
            except Exception:
                pass
            if _auto_token:
                break

    if _auto_token:
        print(f"{GREEN}✓ Auto-detected token from file ({len(_auto_token)} chars){RESET}")
        _token_str = _auto_token
    else:
        _tok_input = input(
            f"{BOLD_CYAN}Token file path {GRAY}(optional — press Enter to skip){RESET}\n"
            f"{BOLD_CYAN}➤ {RESET}"
        ).strip()
        if _tok_input and os.path.isfile(_tok_input):
            try:
                _token_str = open(_tok_input, encoding="utf-8").read().strip()
                print(f"{GREEN}✓ Token loaded ({len(_token_str)} chars){RESET}")
            except Exception as _te:
                print(f"{YELLOW}⚠ Could not read token file: {_te}{RESET}")
        elif _tok_input:
            print(f"{YELLOW}⚠ Token file not found — testing without token{RESET}")

    if not _token_str:
        print(f"{YELLOW}⚠ No token — Hotstar may return non-standard JSON for some proxies{RESET}")

    # Android TV headers — identical to the working curl command
    API_HEADERS = {
        "User-Agent": "Hotstar;in.startv.hotstar.dplus.tv/26.05.10.2 (Android/14; tv)",
        "Accept": "application/json, text/plain, */*",
        "Accept-Language": "en",
        "X-HS-Platform": "androidtv",
        "X-Country-Code": "in",
        "X-HS-Accept-language": "eng",
        "x-hs-app": "260510002",
        "x-hs-retry-count": "0",
        "x-hs-is-retry": "false",
        "X-HS-Client": (
            "platform:androidtv;app_id:in.startv.hotstar.dplus.tv;"
            "app_version:26.05.10.2;os:Android;os_version:14;schema_version:0.0.1690"
        ),
        "Referer": "https://www.hotstar.com/in/browse/editorial/best-in-sports/6517",
        "Origin": "https://www.hotstar.com",
        "Connection": "keep-alive",
        "Cache-Control": "no-cache",
    }
    if _token_str:
        API_HEADERS["x-hs-usertoken"] = _token_str

    # Well-known SOCKS and HTTP proxy ports for auto-detection
    _SOCKS_PORTS = {1080, 4153, 4145, 5678, 9050, 1085, 9100, 10808, 1081, 1082, 1083}
    _HTTP_PORTS  = {80, 8080, 3128, 8888, 8118, 8123, 8000, 8008, 8443, 3129, 9001}

    def _schemes_for(proxy_str: str) -> list:
        """Return ordered list of proxy schemes to try, based on port number."""
        try:
            port = int(proxy_str.rsplit(":", 1)[-1])
        except ValueError:
            port = 0
        if port in _SOCKS_PORTS:
            return (["socks4", "socks5"] if _socks_ok else [])
        if port in _HTTP_PORTS:
            return ["http"]
        # Unknown port — try SOCKS first (if available), then HTTP
        base = (["socks4", "socks5"] if _socks_ok else [])
        return base + ["http"]

    print(f"\n{BOLD_CYAN}╔══════════════════════════════════════════╗{RESET}")
    print(f"{BOLD_CYAN}║      📡  PROXY API CALLER                ║{RESET}")
    print(f"{BOLD_CYAN}║  Tests proxies against Hotstar API       ║{RESET}")
    socks_label = "SOCKS4/SOCKS5/HTTP" if _socks_ok else "HTTP only (PySocks missing)"
    print(f"{BOLD_CYAN}║  Mode: {socks_label:<34}║{RESET}")
    print(f"{BOLD_CYAN}╚══════════════════════════════════════════╝{RESET}\n")

    path_input = input(
        f"{BOLD_CYAN}Proxy file path {GRAY}[default: {DEFAULT_PATH}]{RESET}\n"
        f"{BOLD_CYAN}➤ {RESET}"
    ).strip()
    proxy_file = path_input if path_input else DEFAULT_PATH

    if not os.path.isfile(proxy_file):
        print(f"{RED}✗ File not found: {proxy_file}{RESET}")
        return

    # Read proxies — skip comment lines, strip inline comments
    raw_lines = []
    try:
        with open(proxy_file, "r", encoding="utf-8") as f:
            raw_lines = [l.strip() for l in f if l.strip() and not l.strip().startswith("#")]
    except Exception as e:
        print(f"{RED}✗ Cannot read file: {e}{RESET}")
        return

    proxies_list = []
    for line in raw_lines:
        # Strip inline comment: "1.2.3.4:8080  # 431 ms [SOCKS4]"
        line = line.split("#")[0].strip()
        # Strip any scheme prefix
        for _pfx in ("socks5://", "socks4://", "https://", "http://"):
            if line.lower().startswith(_pfx):
                line = line[len(_pfx):]
                break
        line = line.split("/")[0]
        if ":" in line and line:
            proxies_list.append(line)

    # Deduplicate while preserving order
    _seen_p: set = set()
    proxies_list = [p for p in proxies_list if not (p in _seen_p or _seen_p.add(p))]  # type: ignore[func-returns-value]

    if not proxies_list:
        print(f"{RED}✗ No valid proxies found (expected ip:port per line){RESET}")
        return

    print(f"{GREEN}✓ Loaded {len(proxies_list)} proxies from {proxy_file}{RESET}")
    print(f"{BOLD_YELLOW}Testing against: Hotstar BFF API{RESET}")
    print(f"{GRAY}Timeout: 12s per proxy  |  Parallel workers: 30{RESET}")
    print(f"{GRAY}Port-aware auto-detection: SOCKS ports vs HTTP ports{RESET}\n")

    working   = []   # (proxy_str, latency_ms, proto)
    failed    = []
    lock      = threading.Lock()
    done_count = [0]

    _with_token = bool(_token_str)

    def _classify_resp(resp):
        """
        Returns (tier, label) for a response:
          "api"  — real Hotstar BFF JSON (success key present)      → API ✅
          "conn" — HTTP 200 (proxy tunnel works, may be intercepted) → CONN 🌐
          "auth" — HTTP 401/403 from Hotstar (tunnel works, no token)→ AUTH 🔑
          None   — not working
        """
        sc = resp.status_code

        if sc == 200:
            tier, label = "conn", "CONN 🌐"
            try:
                ct = resp.headers.get("Content-Type", "")
                if "html" not in ct.lower():
                    data = resp.json()
                    if isinstance(data, dict) and "success" in data:
                        tier, label = "api", "API ✅"
            except Exception:
                pass
            return tier, label

        if sc in (401, 403):
            # 401 = Hotstar says "need auth" → tunnel worked, request reached Hotstar
            # 403 = Hotstar/proxy blocked this IP but tunnel was established
            return "auth", f"AUTH 🔑 ({sc})"

        return None, f"HTTP {sc}"

    def _try_one(proxy_str: str, scheme: str):
        """Single attempt. Raises on any connection/timeout failure."""
        import requests as _req
        proxy_url  = f"{scheme}://{proxy_str}"
        proxy_dict = {"http": proxy_url, "https": proxy_url}
        t0 = time.time()
        resp = _req.get(
            TEST_API_URL,
            proxies=proxy_dict,
            timeout=12,
            allow_redirects=False,
            headers=API_HEADERS,
            verify=False,
        )
        ms = int((time.time() - t0) * 1000)
        return resp, ms

    def _call_api(proxy_str):
        schemes = _schemes_for(proxy_str)
        if not schemes:
            with lock:
                done_count[0] += 1
                dc, total = done_count[0], len(proxies_list)
                failed.append(proxy_str)
                print(f"  {RED}✗{RESET} {GRAY}{proxy_str:<28}{RESET}  no scheme available  [{dc}/{total}]")
            return

        ok         = False
        tier_used  = ""
        label_used = ""
        proto_used = ""
        ms_used    = 0
        last_err   = ""

        for scheme in schemes:
            try:
                resp, ms = _try_one(proxy_str, scheme)
                tier, label = _classify_resp(resp)
                if tier:                          # any 200 = working
                    ok         = True
                    tier_used  = tier
                    label_used = label
                    proto_used = scheme.upper()
                    ms_used    = ms
                    break
                else:
                    last_err = label              # e.g. "HTTP 400"
                    if resp.status_code not in (501, 407, 405):
                        break                     # no point trying next scheme

            except Exception as e:
                _em = str(e)
                if ("SOCKS" in _em.upper() or "Missing" in _em
                        or "SOCKSHTTPSConnection" in _em
                        or "No connection adapters" in _em):
                    last_err = f"{scheme.upper()} unsupported"
                    continue   # try next scheme (SOCKS→HTTP)
                last_err = _em[:70]
                break

        with lock:
            done_count[0] += 1
            dc, total = done_count[0], len(proxies_list)
            if ok:
                working.append((proxy_str, ms_used, proto_used, tier_used))
                clr = GREEN if tier_used == "api" else BOLD_CYAN
                print(
                    f"  {GREEN}✓{RESET} {WHITE}{proxy_str:<28}{RESET}  "
                    f"{clr}{ms_used} ms  [{proto_used}]  {label_used}{RESET}  [{dc}/{total}]"
                )
            else:
                failed.append(proxy_str)
                print(
                    f"  {RED}✗{RESET} {GRAY}{proxy_str:<28}{RESET}  "
                    f"{last_err}  [{dc}/{total}]"
                )

    t_start = time.time()
    with ThreadPoolExecutor(max_workers=min(30, len(proxies_list))) as ex:
        futs = [ex.submit(_call_api, p) for p in proxies_list]
        for fut in as_completed(futs):
            pass
    elapsed = time.time() - t_start

    # Sort: API → CONN → AUTH, then by latency within each tier
    _tier_order = {"api": 0, "conn": 1, "auth": 2}
    working.sort(key=lambda x: (_tier_order.get(x[3], 9), x[1]))

    api_cnt  = sum(1 for w in working if w[3] == "api")
    conn_cnt = sum(1 for w in working if w[3] == "conn")
    auth_cnt = sum(1 for w in working if w[3] == "auth")

    print(f"\n{BOLD_CYAN}{'─'*50}{RESET}")
    print(f"{BOLD_GREEN}✓ Working     : {len(working)}/{len(proxies_list)}  ({elapsed:.1f}s){RESET}")
    if api_cnt:
        print(f"{GREEN}  ↳ API ✅     : {api_cnt}  (real Hotstar JSON — best){RESET}")
    if conn_cnt:
        print(f"{BOLD_CYAN}  ↳ CONN 🌐   : {conn_cnt}  (200 connected, tunnel works){RESET}")
    if auth_cnt:
        print(f"{YELLOW}  ↳ AUTH 🔑   : {auth_cnt}  (401/403 — reached Hotstar, needs token){RESET}")
    print(f"{BOLD_RED}✗ Failed      : {len(failed)}{RESET}")

    if working:
        try:
            with open(OUTPUT_FILE, "w", encoding="utf-8") as f:
                f.write(f"# Proxy check — {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
                f.write(f"# Working: {len(working)}/{len(proxies_list)}"
                        f"  (API:{api_cnt}  CONN:{conn_cnt}  AUTH:{auth_cnt})\n\n")
                if api_cnt:
                    f.write("# ── API ✅ (real Hotstar JSON — best quality) ──\n")
                    for proxy_str, ms, proto, tier in working:
                        if tier == "api":
                            f.write(f"{proxy_str}  # {ms} ms  [{proto}]  API\n")
                    f.write("\n")
                if conn_cnt:
                    f.write("# ── CONN 🌐 (tunnel works, 200 response) ──\n")
                    for proxy_str, ms, proto, tier in working:
                        if tier == "conn":
                            f.write(f"{proxy_str}  # {ms} ms  [{proto}]  CONN\n")
                    f.write("\n")
                if auth_cnt:
                    f.write("# ── AUTH 🔑 (reached Hotstar, 401/403 — try with valid token) ──\n")
                    for proxy_str, ms, proto, tier in working:
                        if tier == "auth":
                            f.write(f"{proxy_str}  # {ms} ms  [{proto}]  AUTH\n")
            print(f"\n{GREEN}✓ Saved to: {BOLD_WHITE}{OUTPUT_FILE}{RESET}")

            with zipfile.ZipFile(OUTPUT_ZIP, "w", zipfile.ZIP_DEFLATED) as zf:
                zf.write(OUTPUT_FILE, OUTPUT_FILE)
            print(f"{GREEN}✓ Zipped  : {BOLD_WHITE}{OUTPUT_ZIP}{RESET}")

            print(f"\n{BOLD_CYAN}Working proxies (API first → CONN → AUTH, by speed):{RESET}")
            _tier_colors = {"api": GREEN, "conn": BOLD_CYAN, "auth": YELLOW}
            _tier_labels = {"api": "API ✅", "conn": "CONN 🌐", "auth": "AUTH 🔑"}
            for proxy_str, ms, proto, tier in working:
                bar   = "█" * min(int(ms / 100), 20)
                color = _tier_colors.get(tier, WHITE)
                lbl   = _tier_labels.get(tier, tier)
                print(
                    f"  {GREEN}✓{RESET} {color}{proxy_str:<28}{RESET}  "
                    f"{color}{ms:>5} ms  [{proto}]  {lbl}  {bar}{RESET}"
                )
        except Exception as e:
            print(f"{RED}✗ Could not save output: {e}{RESET}")
    else:
        print(f"\n{YELLOW}⚠ No proxies connected. Proxy list may be dead/blocked.{RESET}")

    # ── Phase 2: One-by-one API test for CONN + AUTH proxies ─────────────────
    candidates = [(p, ms, proto, tier) for p, ms, proto, tier in working
                  if tier in ("conn", "auth")]

    if not candidates:
        return

    print(f"\n{BOLD_CYAN}{'─'*50}{RESET}")
    print(f"{BOLD_CYAN}Phase 2: Deep API test — {len(candidates)} proxies (CONN + AUTH){RESET}")
    cont = input(
        f"{BOLD_YELLOW}Continue API test one by one? (y/n): {RESET}"
    ).strip().lower()
    if cont != "y":
        return

    API_OUTPUT_FILE = "apiworking.txt"
    API_OUTPUT_ZIP  = "apiworking.zip"
    api_working = []  # (proxy_str, ms, proto_used)
    import requests as _rq2

    def _phase2_try(proxy_str, scheme):
        """Single attempt for Phase 2. Returns (resp, ms) or raises."""
        purl  = f"{scheme}://{proxy_str}"
        pd    = {"http": purl, "https": purl}
        t0    = time.time()
        resp  = _rq2.get(
            TEST_API_URL, proxies=pd, timeout=15,
            allow_redirects=False, headers=API_HEADERS, verify=False,
        )
        return resp, int((time.time() - t0) * 1000)

    def _is_api_ok(resp):
        if resp.status_code != 200:
            return False
        try:
            data = resp.json()
            return isinstance(data, dict) and "success" in data
        except Exception:
            return False

    for idx, (proxy_str, _, _proto, tier) in enumerate(candidates, 1):
        print(
            f"\n  [{idx}/{len(candidates)}] {BOLD_WHITE}{proxy_str}{RESET}  "
            f"[{tier.upper()}]",
            flush=True
        )

        found = False
        # Try SOCKS4 first, then HTTP — just like the two curl commands
        for scheme in (["socks4", "http"] if _socks_ok else ["http"]):
            print(f"    → {scheme.upper():<6} ... ", end="", flush=True)
            try:
                resp, ms2 = _phase2_try(proxy_str, scheme)
                if _is_api_ok(resp):
                    print(f"{GREEN}✓ API ✅  {ms2} ms{RESET}")
                    api_working.append((proxy_str, ms2, scheme.upper()))
                    found = True
                    break
                elif resp.status_code == 200:
                    print(f"{YELLOW}200 (intercepted — no success key){RESET}")
                    break  # 200 means connected; HTTP won't be different
                else:
                    print(f"{RED}HTTP {resp.status_code}{RESET}")
            except Exception as ex:
                em = str(ex)
                if ("SOCKS" in em.upper() or "Missing" in em
                        or "SOCKSHTTPSConnection" in em):
                    print(f"{GRAY}SOCKS unsupported — trying HTTP{RESET}")
                    continue
                print(f"{RED}{em[:60]}{RESET}")
                break

        if not found and scheme == "http":
            pass  # already printed error above

    print(f"\n{BOLD_CYAN}{'─'*50}{RESET}")
    print(f"{BOLD_GREEN}✓ API Confirmed : {len(api_working)}/{len(candidates)}{RESET}")

    if api_working:
        api_working.sort(key=lambda x: x[1])
        try:
            with open(API_OUTPUT_FILE, "w", encoding="utf-8") as f:
                f.write(f"# API-confirmed proxies — {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
                f.write(f"# These proxies returned real Hotstar BFF JSON (success key)\n")
                f.write(f"# Total: {len(api_working)}\n\n")
                for proxy_str, ms2, proto in api_working:
                    f.write(f"{proxy_str}  # {ms2} ms  [{proto}]  API\n")
            print(f"{GREEN}✓ Saved to: {BOLD_WHITE}{API_OUTPUT_FILE}{RESET}")

            with zipfile.ZipFile(API_OUTPUT_ZIP, "w", zipfile.ZIP_DEFLATED) as zf:
                zf.write(API_OUTPUT_FILE, API_OUTPUT_FILE)
            print(f"{GREEN}✓ Zipped  : {BOLD_WHITE}{API_OUTPUT_ZIP}{RESET}")

            print(f"\n{BOLD_GREEN}API-confirmed proxies (sorted by speed):{RESET}")
            for proxy_str, ms2, proto in api_working:
                bar   = "█" * min(int(ms2 / 100), 20)
                color = GREEN if ms2 < 1000 else YELLOW if ms2 < 3000 else RED
                print(
                    f"  {GREEN}✓{RESET} {WHITE}{proxy_str:<28}{RESET}  "
                    f"{color}{ms2:>6} ms  [{proto}]  API ✅  {bar}{RESET}"
                )
        except Exception as e:
            print(f"{RED}✗ Could not save: {e}{RESET}")
    else:
        print(f"{YELLOW}⚠ No proxies returned real Hotstar JSON in Phase 2.{RESET}")


def main():
    # ── Step 1: CLI arg shortcut ─────────────────────────────────────────────
    if len(sys.argv) > 1 and not sys.argv[1].startswith("--"):
        input_url = sys.argv[1]
        print(f"{CYAN}CLI Mode: Using provided URL{RESET}")
    else:
        # ── Step 1a: Fetch & display live events ─────────────────────────────
        _debug_live = "--debug" in sys.argv
        print(f"{DARK_MAGENTA}Fetching live events...{RESET}", end="", flush=True)
        live_events, _live_err = fetch_live_events(debug=_debug_live)
        # If live-now API failed, fallback to best-in-sports live filter
        if not live_events:
            try:
                _bs_events, _bs_err = fetch_best_in_sports("LIVE")
                if _bs_events:
                    live_events = _bs_events
                    _live_err = ""
            except Exception:
                pass
        # Clear the "Fetching..." line
        print(f"\r{' ' * 30}\r", end="", flush=True)

        _SPORTS_FILTER_MAP = {
            "1": ("LIVE",       "Only Live Streams 🛑"),
            "2": ("OTHER",      "Non-Stop Sports 🔥"),
            "3": ("HIGHLIGHTS", "All Sports Highlights ✅"),
        }

        if live_events:
            print(f"\n{BOLD_CYAN}┌──────────────────────────────────────┐{RESET}")
            print(f"{BOLD_CYAN}│        🔴  LIVE EVENTS NOW           │{RESET}")
            print(f"{BOLD_CYAN}└──────────────────────────────────────┘{RESET}")
            for i, (ev_title, _ev_url) in enumerate(live_events, 1):
                print(f"{BOLD_GREEN}{{{i}}}{RESET} {WHITE}{ev_title}{RESET}")
            sports_start = len(live_events) + 1
            checker_num  = len(live_events) + 4
            quality_num  = len(live_events) + 5
            proxy_num    = len(live_events) + 6
            print()
            print(f"{BOLD_RED}{{{sports_start}}}{RESET} {RED}Only Live Streams 🛑{RESET}")
            print(f"{BOLD_YELLOW}{{{sports_start+1}}}{RESET} {YELLOW}Non-Stop Sports 🔥{RESET}")
            print(f"{BOLD_GREEN}{{{sports_start+2}}}{RESET} {GREEN}All Sports Highlights ✅{RESET}")
            print(f"{BOLD_GREEN}{{{checker_num}}}{RESET} {GREEN}Hotstar Cookies checker ✅{RESET}")
            print(f"{BOLD_MAGENTA}{{{quality_num}}}{RESET} {MAGENTA}Quality Checker 🎬{RESET}")
            print(f"{BOLD_CYAN}{{{proxy_num}}}{RESET} {CYAN}Proxy Checker 🌐{RESET}")
            api_caller_num = len(live_events) + 7
            print(f"{BOLD_MAGENTA}{{{api_caller_num}}}{RESET} {MAGENTA}Proxy API Caller 📡{RESET}")
            print()
            print(f"{BOLD_YELLOW}(Use 1.2.3 / 'all' to multi-select — or paste URL directly){RESET}")
            print()
            event_raw = input(f"{BOLD_CYAN}Enter number / URL ➤ {RESET}").strip()

            # ── URL detection: if input looks like hotstar URL(s), treat directly ──
            _url_tokens = [t for t in event_raw.replace(",", " ").split()
                           if "hotstar" in t.lower() or t.startswith("http")]
            if _url_tokens:
                if len(_url_tokens) == 1:
                    # Single URL — fall through to quality picker below
                    input_url = _url_tokens[0]
                else:
                    # Multiple URLs — inline multi-event mode
                    _multi_events = [(f"URL {_i}", _u) for _i, _u in enumerate(_url_tokens, 1)]
                    print(f"\n{BOLD_CYAN}✓ {len(_multi_events)} URLs entered:{RESET}")
                    for _mi, (_mt, _mu) in enumerate(_multi_events, 1):
                        print(f"  {BOLD_GREEN}{_mi}.{RESET} {WHITE}{_mu}{RESET}")
                    print()
                    print(f"{BOLD_GREEN}{{1}} NORMAL 4K{RESET}")
                    print(f"{BOLD_BLUE}{{2}} NORMAL FHD{RESET}")
                    print(f"{BOLD_CYAN}{{3}} NORMAL FHD (30 MINUTES){RESET}")
                    print(f"{BOLD_YELLOW}{{4}} ADS-FREE JHS HD{RESET}")
                    print(f"{BOLD_MAGENTA}{{5}} JHS 4K{RESET}")
                    print(f"{BOLD_CYAN}{{6}} ADS-FREE 4K LITE (7 MINUTES){RESET}")
                    print(f"{BOLD_CYAN}{{7}} ADS-FREE 4K HEAVY (30 MINUTES){RESET}")
                    print(f"{BOLD_GREEN}{{8}} H.265 4K DV,HDR,SDR ADSFREE{RESET}")
                    print(f"{BOLD_GREEN}{{9}} H.265 FHD DV,HDR,SDR{RESET}")
                    print(f"{BOLD_GREEN}{{10}} H.265 AUTO DV,HDR,SDR ADSFREE{RESET}")
                    print(f"{BOLD_GREEN}{{11}} ADS-FREE 4K TattiJio & Chortel users{RESET}")
                    print(f"{BOLD_WHITE}{{12}} H.264 4K DV,HDR,SDR{RESET}")
                    print(f"{BOLD_WHITE}{{13}} H.265 4K DV,HDR,SDR{RESET}")
                    print(f"{BOLD_WHITE}{{14}} H.264 FHD DV,HDR,SDR{RESET}")
                    print(f"{BOLD_WHITE}{{15}} H.265 FHD DV,HDR,SDR{RESET}")
                    print(f"{BOLD_RED}{{16}} DRM MPD + CLEARKEY / PSSH{RESET}")
                    print(f"{BOLD_YELLOW}{{17}} NORMAL HD (720p) ALL LANGUAGES{RESET}")
                    print(f"{BOLD_GREEN}{{18}} DRM-TV 24-HOURS LINK{RESET}")
                    print(f"{BOLD_MAGENTA}{{21}} AUTO-UPDATE M3U (EVERY MINUTES){RESET}")
                    print(f"{BOLD_GREEN}{{22}} FALLBACK 24-HOURS LINK{RESET}")
                    print(f"{BOLD_BLUE}{{23}} PRIMARY 24-HOURS LINK{RESET}")
                    print(f"{BOLD_GREEN}{{24}} FALLBACK 24-HOURS TattiJio & Chortel users{RESET}")
                    print(f"{BOLD_BLUE}{{25}} PRIMARY 24-HOURS TattiJio & Chortel users{RESET}")
                    _mqu = input(f"{BOLD_CYAN}Enter number ➤ {RESET}").strip()
                    _MULTI_FN_MAPU = {
                        "3":  option_fhd_heavy_main,
                        "6":  option5_main,
                        "7":  option6_heavy_main,
                        "8":  lambda u: option_dv_hdr_sdr(u, "h265", ads_mode="ssai"),
                        "9":  lambda u: option_fhd_dv_hdr_sdr(u, "h265", ads_mode="ssai"),
                        "10": option_auto_dv_hdr_sdr,
                        "11": option6_pri_main,
                        "12": lambda u: option_dv_hdr_sdr(u, "h264"),
                        "13": lambda u: option_dv_hdr_sdr(u, "h265"),
                        "14": lambda u: option_fhd_dv_hdr_sdr(u, "h264"),
                        "15": lambda u: option_fhd_dv_hdr_sdr(u, "h265"),
                        "17": option20_normal_hd,
                        "18": option10_drm_tv_24h,
                        "22": option12_fallback_24h,
                        "23": option13_primary_24h,
                        "24": option14_jio_fallback_24h,
                        "25": option15_jio_primary_24h,
                    }
                    if _mqu == "21":
                        auto_update_mode_multi(_multi_events)
                    elif _mqu in _MULTI_FN_MAPU:
                        _mfnu = _MULTI_FN_MAPU[_mqu]
                        for _mi, (_mt, _mu) in enumerate(_multi_events, 1):
                            print(f"\n{BOLD_CYAN}{'─'*44}{RESET}")
                            print(f"{BOLD_CYAN}[{_mi}/{len(_multi_events)}] {_mu}{RESET}")
                            print(f"{BOLD_CYAN}{'─'*44}{RESET}")
                            _mfnu(_mu)
                    elif _mqu == "16":
                        for _mi, (_mt, _mu) in enumerate(_multi_events, 1):
                            print(f"\n{BOLD_CYAN}{'─'*44}{RESET}")
                            print(f"{BOLD_CYAN}[{_mi}/{len(_multi_events)}] {_mu}{RESET}")
                            print(f"{BOLD_CYAN}{'─'*44}{RESET}")
                            _mspu = extract_slug_path(_mu)
                            _mttu, _mmnu = extract_match_title(_mu)
                            _mstu = extract_stream_type(_mu)
                            option7_main(_mspu, _mttu, _mmnu, _mstu, _mu)
                    elif _mqu in ["1", "2", "4", "5"]:
                        _mqu_int = _mqu
                        for _mi, (_mt, _mu) in enumerate(_multi_events, 1):
                            print(f"\n{BOLD_CYAN}{'─'*44}{RESET}")
                            print(f"{BOLD_CYAN}[{_mi}/{len(_multi_events)}] {_mu}{RESET}")
                            print(f"{BOLD_CYAN}{'─'*44}{RESET}")
                            _mspu = extract_slug_path(_mu)
                            if not _mspu:
                                print(f"{RED}Invalid URL, skipping.{RESET}")
                                continue
                            _mttu, _mmnu = extract_match_title(_mu)
                            _mstu = extract_stream_type(_mu)
                            print(f"{DARK_MAGENTA}FETCHING STREAMS... PLEASE WAIT{RESET}")
                            _m_entriesy = []
                            _seen_basesy: set = set()
                            for _lcy, _lny in UNIQUE_LANGUAGES.items():
                                try:
                                    _mresy = fetch_lang_stream(_lcy, _lny, _mspu, _mu, _mqu_int)
                                    if not _mresy:
                                        continue
                                    _csy = _mresy["stream"]
                                    _lny2 = _mresy["lang_name"] or _lny
                                    _hdry = _mresy.get("is_hdr", False)
                                    _by = _csy.split("?")[0]
                                    if _by not in _seen_basesy:
                                        _seen_basesy.add(_by)
                                        _m_entriesy.append((_lny2, _csy, _hdry))
                                except Exception:
                                    continue
                            if _m_entriesy:
                                for _mlny, _mfuy, _mhdry in _m_entriesy:
                                    _htagy = " HDR" if _mhdry else ""
                                    print(f"\n{BOLD_CYAN}{_mlny}{_htagy}{RESET}")
                                    print(f"{GREEN}{_mfuy}{RESET}")
                            else:
                                print(f"{YELLOW}No streams found.{RESET}")
                    else:
                        print(f"{YELLOW}Invalid choice for multi-event mode.{RESET}")
                    return
            else:
                # ── Number / 'all' parsing ────────────────────────────────────
                _parsed_parts = [p.strip() for p in event_raw.replace(".", ",").split(",") if p.strip()]
                _valid_event_nums = []
                _seen_ev_set: set = set()
                if event_raw.strip().lower() == "all":
                    _valid_event_nums = list(range(1, len(live_events) + 1))
                else:
                    for _p in _parsed_parts:
                        if _p.isdigit():
                            _n = int(_p)
                            if 1 <= _n <= len(live_events) and _n not in _seen_ev_set:
                                _seen_ev_set.add(_n)
                                _valid_event_nums.append(_n)
                # ── Multi-event or single-event routing ──────────────────────
                if len(_valid_event_nums) > 1:
                    _multi_events = [(live_events[_n - 1][0], live_events[_n - 1][1]) for _n in _valid_event_nums]
                    print(f"\n{BOLD_CYAN}✓ {len(_multi_events)} events selected:{RESET}")
                    for _mi, (_mt, _) in enumerate(_multi_events, 1):
                        print(f"  {BOLD_GREEN}{_mi}.{RESET} {WHITE}{_mt}{RESET}")
                    print()
                    print(f"{BOLD_GREEN}{{1}} NORMAL 4K{RESET}")
                    print(f"{BOLD_BLUE}{{2}} NORMAL FHD{RESET}")
                    print(f"{BOLD_CYAN}{{3}} NORMAL FHD (30 MINUTES){RESET}")
                    print(f"{BOLD_YELLOW}{{4}} ADS-FREE JHS HD{RESET}")
                    print(f"{BOLD_MAGENTA}{{5}} JHS 4K{RESET}")
                    print(f"{BOLD_CYAN}{{6}} ADS-FREE 4K LITE (7 MINUTES){RESET}")
                    print(f"{BOLD_CYAN}{{7}} ADS-FREE 4K HEAVY (30 MINUTES){RESET}")
                    print(f"{BOLD_GREEN}{{8}} H.265 4K DV,HDR,SDR ADSFREE{RESET}")
                    print(f"{BOLD_GREEN}{{9}} H.265 FHD DV,HDR,SDR{RESET}")
                    print(f"{BOLD_GREEN}{{10}} H.265 AUTO DV,HDR,SDR ADSFREE{RESET}")
                    print(f"{BOLD_GREEN}{{11}} ADS-FREE 4K TattiJio & Chortel users{RESET}")
                    print(f"{BOLD_WHITE}{{12}} H.264 4K DV,HDR,SDR{RESET}")
                    print(f"{BOLD_WHITE}{{13}} H.265 4K DV,HDR,SDR{RESET}")
                    print(f"{BOLD_WHITE}{{14}} H.264 FHD DV,HDR,SDR{RESET}")
                    print(f"{BOLD_WHITE}{{15}} H.265 FHD DV,HDR,SDR{RESET}")
                    print(f"{BOLD_RED}{{16}} DRM MPD + CLEARKEY / PSSH{RESET}")
                    print(f"{BOLD_YELLOW}{{17}} NORMAL HD (720p) ALL LANGUAGES{RESET}")
                    print(f"{BOLD_GREEN}{{18}} DRM-TV 24-HOURS LINK{RESET}")
                    print(f"{BOLD_MAGENTA}{{21}} AUTO-UPDATE M3U (EVERY MINUTES){RESET}")
                    print(f"{BOLD_GREEN}{{22}} FALLBACK 24-HOURS LINK{RESET}")
                    print(f"{BOLD_BLUE}{{23}} PRIMARY 24-HOURS LINK{RESET}")
                    print(f"{BOLD_GREEN}{{24}} FALLBACK 24-HOURS TattiJio & Chortel users{RESET}")
                    print(f"{BOLD_BLUE}{{25}} PRIMARY 24-HOURS TattiJio & Chortel users{RESET}")
                    _mq = input(f"{BOLD_CYAN}Enter number ➤ {RESET}").strip()
                    _MULTI_FN_MAP = {
                        "3":  option_fhd_heavy_main,
                        "6":  option5_main,
                        "7":  option6_heavy_main,
                        "8":  lambda u: option_dv_hdr_sdr(u, "h265", ads_mode="ssai"),
                        "9":  lambda u: option_fhd_dv_hdr_sdr(u, "h265", ads_mode="ssai"),
                        "10": option_auto_dv_hdr_sdr,
                        "11": option6_pri_main,
                        "12": lambda u: option_dv_hdr_sdr(u, "h264"),
                        "13": lambda u: option_dv_hdr_sdr(u, "h265"),
                        "14": lambda u: option_fhd_dv_hdr_sdr(u, "h264"),
                        "15": lambda u: option_fhd_dv_hdr_sdr(u, "h265"),
                        "17": option20_normal_hd,
                        "18": option10_drm_tv_24h,
                        "22": option12_fallback_24h,
                        "23": option13_primary_24h,
                        "24": option14_jio_fallback_24h,
                        "25": option15_jio_primary_24h,
                    }
                    if _mq == "21":
                        auto_update_mode_multi(_multi_events)
                    elif _mq in _MULTI_FN_MAP:
                        _mfn = _MULTI_FN_MAP[_mq]
                        for _mi, (_mt, _mu) in enumerate(_multi_events, 1):
                            print(f"\n{BOLD_CYAN}{'─'*44}{RESET}")
                            print(f"{BOLD_CYAN}[{_mi}/{len(_multi_events)}] {_mt}{RESET}")
                            print(f"{BOLD_CYAN}{'─'*44}{RESET}")
                            _mfn(_mu)
                    elif _mq == "16":
                        for _mi, (_mt, _mu) in enumerate(_multi_events, 1):
                            print(f"\n{BOLD_CYAN}{'─'*44}{RESET}")
                            print(f"{BOLD_CYAN}[{_mi}/{len(_multi_events)}] {_mt}{RESET}")
                            print(f"{BOLD_CYAN}{'─'*44}{RESET}")
                            _msp = extract_slug_path(_mu)
                            _mtt, _mmn = extract_match_title(_mu)
                            _mst = extract_stream_type(_mu)
                            option7_main(_msp, _mtt, _mmn, _mst, _mu)
                    elif _mq in ["1", "2", "4", "5"]:
                        _mq_intl = _mq
                        for _mi, (_mt, _mu) in enumerate(_multi_events, 1):
                            print(f"\n{BOLD_CYAN}{'─'*44}{RESET}")
                            print(f"{BOLD_CYAN}[{_mi}/{len(_multi_events)}] {_mt}{RESET}")
                            print(f"{BOLD_CYAN}{'─'*44}{RESET}")
                            _msp = extract_slug_path(_mu)
                            if not _msp:
                                print(f"{RED}Invalid URL, skipping.{RESET}")
                                continue
                            _mtt, _mmn = extract_match_title(_mu)
                            _mst = extract_stream_type(_mu)
                            print(f"{DARK_MAGENTA}FETCHING STREAMS... PLEASE WAIT{RESET}")
                            _m_entries = []
                            _seen_bases: set = set()
                            for _lc, _ln in UNIQUE_LANGUAGES.items():
                                try:
                                    _mres = fetch_lang_stream(_lc, _ln, _msp, _mu, _mq_intl)
                                    if not _mres:
                                        continue
                                    _mpc = _mres["player_config"]
                                    _is_hdr = _mres.get("is_hdr", False)
                                    _clean_stream = _mres["stream"]
                                    _lang_name = _mres["lang_name"] or _ln
                                    _base = _clean_stream.split("?")[0]
                                    if _base not in _seen_bases:
                                        _seen_bases.add(_base)
                                        _m_entries.append((_lang_name, _clean_stream, _is_hdr))
                                except Exception:
                                    continue
                            if _m_entries:
                                for _mln, _mfu, _mhdr in _m_entries:
                                    _htag = " HDR" if _mhdr else ""
                                    print(f"\n{BOLD_CYAN}{_mln}{_htag}{RESET}")
                                    print(f"{GREEN}{_mfu}{RESET}")
                            else:
                                print(f"{YELLOW}No streams found for this event.{RESET}")
                    else:
                        print(f"{YELLOW}Invalid choice for multi-event mode.{RESET}")
                    return

                # ── Single-event routing ──────────────────────────────────────
                try:
                    event_idx = int(event_raw)
                except ValueError:
                    event_idx = -1

                if 1 <= event_idx <= len(live_events):
                    _ev_title, input_url = live_events[event_idx - 1]
                    print(f"\n{BOLD_GREEN}» {_ev_title}{RESET}")
                elif event_idx in (sports_start, sports_start + 1, sports_start + 2):
                    _offset = event_idx - sports_start + 1
                    _sf, _sl = _SPORTS_FILTER_MAP[str(_offset)]
                    _sel_url = _show_sports_submenu(_sf, _sl)
                    if _sel_url:
                        input_url = _sel_url
                    else:
                        return
                elif event_idx == checker_num:
                    hotstar_cookies_checker()
                    return
                elif event_idx == quality_num:
                    hotstar_quality_checker()
                    return
                elif event_idx == proxy_num:
                    proxy_checker()
                    return
                elif event_idx == api_caller_num:
                    proxy_api_caller()
                    return
                else:
                    print(f"{YELLOW}Invalid option. Paste a Hotstar URL directly at the main prompt.{RESET}")
                    return
        else:
            # No events fetched — show 3 sports options + cookies checker
            _err_hint = f" [{_live_err}]" if _live_err else ""
            print(f"{YELLOW}(Could not fetch live events{_err_hint}){RESET}")
            print(f"{BOLD_RED}{{1}}{RESET} {RED}Only Live Streams 🛑{RESET}")
            print(f"{BOLD_YELLOW}{{2}}{RESET} {YELLOW}Non-Stop Sports 🔥{RESET}")
            print(f"{BOLD_GREEN}{{3}}{RESET} {GREEN}All Sports Highlights ✅{RESET}")
            print(f"{BOLD_GREEN}{{4}}{RESET} {GREEN}Hotstar Cookies checker ✅{RESET}")
            print(f"{BOLD_MAGENTA}{{5}}{RESET} {MAGENTA}Quality Checker 🎬{RESET}")
            print(f"{BOLD_CYAN}{{6}}{RESET} {CYAN}Proxy Checker 🌐{RESET}")
            print(f"{BOLD_MAGENTA}{{7}}{RESET} {MAGENTA}Proxy API Caller 📡{RESET}")
            print()
            menu_raw = input(f"{BOLD_CYAN}Enter number / URL ➤ {RESET}").strip()
            if menu_raw in _SPORTS_FILTER_MAP:
                _sf, _sl = _SPORTS_FILTER_MAP[menu_raw]
                _sel_url = _show_sports_submenu(_sf, _sl)
                if _sel_url:
                    input_url = _sel_url
                else:
                    return
            elif menu_raw == "4":
                hotstar_cookies_checker()
                return
            elif menu_raw == "5":
                hotstar_quality_checker()
                return
            elif menu_raw == "6":
                proxy_checker()
                return
            elif menu_raw == "7":
                proxy_api_caller()
                return
            else:
                input_url = menu_raw

    # ── Step 2: Quality / option picker ──────────────────────────────────────
    print(f"{BOLD_GREEN}{{1}} NORMAL 4K{RESET}")
    print(f"{BOLD_BLUE}{{2}} NORMAL FHD{RESET}")
    print(f"{BOLD_CYAN}{{3}} NORMAL FHD (30 MINUTES){RESET}")
    print(f"{BOLD_YELLOW}{{4}} ADS-FREE JHS HD{RESET}")
    print(f"{BOLD_MAGENTA}{{5}} JHS 4K{RESET}")
    print(f"{BOLD_CYAN}{{6}} ADS-FREE 4K LITE (7 MINUTES){RESET}")
    print(f"{BOLD_CYAN}{{7}} ADS-FREE 4K HEAVY (30 MINUTES){RESET}")
    print(f"{BOLD_GREEN}{{8}} H.265 4K DV,HDR,SDR ADSFREE{RESET}")
    print(f"{BOLD_GREEN}{{9}} H.265 FHD DV,HDR,SDR{RESET}")
    print(f"{BOLD_GREEN}{{10}} H.265 AUTO DV,HDR,SDR ADSFREE{RESET}")
    print(f"{BOLD_GREEN}{{11}} ADS-FREE 4K TattiJio & Chortel users{RESET}")
    print(f"{BOLD_WHITE}{{12}} H.264 4K DV,HDR,SDR{RESET}")
    print(f"{BOLD_WHITE}{{13}} H.265 4K DV,HDR,SDR{RESET}")
    print(f"{BOLD_WHITE}{{14}} H.264 FHD DV,HDR,SDR{RESET}")
    print(f"{BOLD_WHITE}{{15}} H.265 FHD DV,HDR,SDR{RESET}")
    print(f"{BOLD_RED}{{16}} DRM MPD + CLEARKEY / PSSH{RESET}")
    print(f"{BOLD_YELLOW}{{17}} NORMAL HD (720p) ALL LANGUAGES{RESET}")
    print(f"{BOLD_GREEN}{{18}} DRM-TV 24-HOURS LINK{RESET}")
    print(f"{BOLD_YELLOW}{{19}} JHS ALL CHANNELS{RESET}")
    print(f"{BOLD_BLUE}{{20}} REFRESH TOKENS IN EXISTING M3U{RESET}")
    print(f"{BOLD_MAGENTA}{{21}} AUTO-UPDATE M3U (EVERY MINUTES){RESET}")
    print(f"{BOLD_GREEN}{{22}} FALLBACK 24-HOURS LINK{RESET}")
    print(f"{BOLD_BLUE}{{23}} PRIMARY 24-HOURS LINK{RESET}")
    print(f"{BOLD_GREEN}{{24}} FALLBACK 24-HOURS TattiJio & Chortel users{RESET}")
    print(f"{BOLD_BLUE}{{25}} PRIMARY 24-HOURS TattiJio & Chortel users{RESET}")
    quality_choice = input(f"{BOLD_CYAN}Enter number ➤ {RESET}").strip()
    if quality_choice == "3":
        option_fhd_heavy_main(input_url)
        return
    if quality_choice == "6":
        option5_main(input_url)
        return
    if quality_choice == "7":
        option6_heavy_main(input_url)
        return
    if quality_choice == "8":
        option_dv_hdr_sdr(input_url, "h265", ads_mode="ssai")
        return
    if quality_choice == "9":
        option_fhd_dv_hdr_sdr(input_url, "h265", ads_mode="ssai")
        return
    if quality_choice == "10":
        option_auto_dv_hdr_sdr(input_url)
        return
    if quality_choice == "12":
        option_dv_hdr_sdr(input_url, "h264")
        return
    if quality_choice == "13":
        option_dv_hdr_sdr(input_url, "h265")
        return
    if quality_choice == "14":
        option_fhd_dv_hdr_sdr(input_url, "h264")
        return
    if quality_choice == "15":
        option_fhd_dv_hdr_sdr(input_url, "h265")
        return
    if quality_choice == "11":
        option6_pri_main(input_url)
        return
    if quality_choice == "18":
        option10_drm_tv_24h(input_url)
        return
    if quality_choice == "19":
        default_url = "https://www.hotstar.com/in/tv/star-sports-hindi-1/1260000025/live/watch"
        option11_update_jhs(input_url=default_url)
        return
    if quality_choice == "20":
        option9_refresh_tokens()
        return
    if quality_choice == "22":
        option12_fallback_24h(input_url)
        return
    if quality_choice == "23":
        option13_primary_24h(input_url)
        return
    if quality_choice == "24":
        option14_jio_fallback_24h(input_url)
        return
    if quality_choice == "25":
        option15_jio_primary_24h(input_url)
        return
    if quality_choice == "17":
        option20_normal_hd(input_url)
        return
    if quality_choice == "21":
        auto_update_mode(input_url)
        return
    if quality_choice not in ["1", "2", "4", "5", "16"]:
        quality_choice = "2"
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid URL!{RESET}")
        return
    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)
    print(f"{DARK_MAGENTA}FETCHING STREAMS... PLEASE WAIT{RESET}")
    playlist_entries = []
    logo_url = ""
    if quality_choice == "16":
        option7_main(slug_path, title, match_no, stream_type, input_url)
        return
    if quality_choice == "11":
        print(f"\n{BOLD_RED}LOGO{RESET}")
        logo_url_drm = ""
        try:
            api_url_drm = build_drm_api_url(slug_path, "eng")
            req0 = request.Request(api_url_drm, headers=build_headers())
            with request.urlopen(req0) as r0:
                d0 = json.loads(r0.read().decode("utf-8"))
            for sec in d0.get("success",{}).get("page",{}).get("spaces",{}).values():
                for w in sec.get("widget_wrappers",[]):
                    pc = w.get("widget",{}).get("data",{}).get("player_config")
                    if pc:
                        img = pc.get("expanded_content_poster",{}).get("image",{}).get("src") or pc.get("cast_image",{}).get("src")
                        if img:
                            logo_url_drm = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                            print(logo_url_drm)
                        break
        except: pass
        if match_no: print(f"{GREEN}{match_no}{RESET}")
        print(f"{BOLD_GREEN}{title}{RESET}")
        print(f"{BOLD_MAGENTA}{stream_type}{RESET}")
        try:
            api_url_eng = build_drm_api_url(slug_path, "eng")
            req_eng = request.Request(api_url_eng, headers=build_headers())
            with request.urlopen(req_eng, timeout=10) as resp_eng:
                data_eng = json.loads(resp_eng.read().decode("utf-8"))
            player_config = None
            for sec in data_eng.get("success",{}).get("page",{}).get("spaces",{}).values():
                for w in sec.get("widget_wrappers",[]):
                    d = w.get("widget",{}).get("data",{})
                    if "player_config" in d:
                        player_config = d["player_config"]
                        break
                if player_config: break
            if not player_config:
                print(f"{RED}NO DRM STREAM FOUND ❌{RESET}")
                return
            drm_streams = extract_drm_info(player_config)
            if not drm_streams:
                print(f"{RED}NO DRM STREAM FOUND ❌{RESET}")
                return
            # ── Collect keys once (shared across PRIMARY/FALLBACK) ──────────────
            global_keys = []
            global_license = ""
            seen_mpds = set()
            for stream in drm_streams:
                lic = stream.get("license_url") or ""
                if lic:
                    global_license = lic
                    break
            # Try keys from first MPD
            first_mpd = drm_streams[0]["mpd_url"] if drm_streams else ""
            if first_mpd and global_license:
                try:
                    mpd_info0 = fetch_mpd_pssh(first_mpd)
                    if mpd_info0 and mpd_info0.get("key_ids"):
                        ck = try_clearkey_json(mpd_info0["key_ids"], global_license)
                        if ck:
                            global_keys = ck
                        elif mpd_info0.get("pssh"):
                            wv = fetch_widevine_keys(mpd_info0["pssh"], global_license)
                            if wv and not any(l.startswith("❌") for l in wv):
                                global_keys = wv
                except Exception:
                    pass
            key_str_global = ",".join(global_keys) if global_keys else global_license
            # ── Print PRIMARY then FALLBACK ─────────────────────────────────────
            m3u_lines = ["#EXTM3U", f"# Title: {title}", f"", f"# Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}", ""]
            # Order: PRIMARY first, FALLBACK second
            ordered_streams = sorted(drm_streams, key=lambda s: 0 if s["variant"] == "PRIMARY" else 1)
            for stream in ordered_streams:
                mpd_url = stream["mpd_url"]
                mpd_base = mpd_url.split("?")[0]
                if mpd_base in seen_mpds:
                    continue
                seen_mpds.add(mpd_base)
                license_url = stream.get("license_url") or global_license
                variant = stream.get("variant", "")
                print(f"\n{BOLD_CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━{RESET}")
                print(f"{BOLD_CYAN}[{variant}]{RESET}")
                print(f"{BOLD_YELLOW}MPD URL:{RESET}\n{GREEN}{mpd_url}{RESET}")
                if license_url:
                    print(f"{BOLD_YELLOW}LICENSE URL:{RESET}\n{CYAN}{license_url}{RESET}")
                else:
                    print(f"{BOLD_YELLOW}LICENSE URL:{RESET} {GRAY}not found{RESET}")
                # Detect available languages from this MPD
                print(f"{BOLD_YELLOW}Detecting languages...{RESET}", end=" ", flush=True)
                avail_langs = extract_mpd_languages(mpd_url)
                if avail_langs:
                    lang_names = ", ".join(n for _, n in avail_langs)
                    print(f"{GREEN}{lang_names}{RESET}")
                else:
                    # URL-based detection already tried inside extract_mpd_languages
                    avail_langs = [("unk", "STREAM")]
                    print(f"{YELLOW}Could not detect languages{RESET}")
                # Fetch PSSH/keys for this specific MPD
                print(f"{BOLD_YELLOW}Fetching MPD...{RESET}", end=" ", flush=True)
                mpd_info = fetch_mpd_pssh(mpd_url)
                if mpd_info["error"]:
                    print(f"{RED}Failed: {mpd_info['error']}{RESET}")
                    key_str = key_str_global
                else:
                    print(f"{GREEN}OK{RESET}")
                    if mpd_info["has_clearkey"]:
                        print(f"{BOLD_GREEN}⚡ ClearKey scheme detected!{RESET}")
                    if mpd_info["key_ids"]:
                        print(f"{BOLD_YELLOW}KEY IDs:{RESET}")
                        for kid in mpd_info["key_ids"]:
                            print(f"  {CYAN}{kid}{RESET}")
                    if mpd_info["pssh"]:
                        print(f"{BOLD_YELLOW}PSSH (Widevine):{RESET}\n  {CYAN}{mpd_info['pssh']}{RESET}")
                    # Try to get keys for this MPD
                    variant_keys = []
                    if license_url and mpd_info["key_ids"]:
                        print(f"{BOLD_YELLOW}Trying ClearKey...{RESET}", end=" ", flush=True)
                        ck_keys = try_clearkey_json(mpd_info["key_ids"], license_url)
                        if ck_keys:
                            variant_keys = ck_keys
                            print(f"{BOLD_GREEN}SUCCESS{RESET}")
                            print(f"{BOLD_GREEN}🔑 KEYS (kid:key):{RESET}")
                            for k in ck_keys:
                                print(f"  {BOLD_GREEN}{k}{RESET}")
                        else:
                            print(f"{YELLOW}No ClearKey response{RESET}")
                            if mpd_info["pssh"]:
                                print(f"{BOLD_YELLOW}Trying Widevine (pywidevine)...{RESET}", end=" ", flush=True)
                                wv_keys = fetch_widevine_keys(mpd_info["pssh"], license_url)
                                if any(l.startswith("❌") or l.startswith("⚠") for l in wv_keys):
                                    print(f"{RED}Failed{RESET}")
                                    for l in wv_keys:
                                        print(f"  {RED}{l}{RESET}")
                                else:
                                    variant_keys = wv_keys
                                    print(f"{BOLD_GREEN}SUCCESS{RESET}")
                                    print(f"{BOLD_GREEN}🔑 KEYS (kid:key):{RESET}")
                                    for k in wv_keys:
                                        print(f"  {BOLD_GREEN}{k}{RESET}")
                            else:
                                print(f"{YELLOW}⚠ No PSSH — cannot generate Widevine challenge{RESET}")
                    elif not license_url:
                        print(f"{YELLOW}⚠ No license URL{RESET}")
                    key_str = ",".join(variant_keys) if variant_keys else (key_str_global or license_url)
                    save_name = title.replace(" ", "_")
                    lic_part = " --key-text-file keys.txt --decryption-binary-path mp4decrypt" if license_url else ""
                    cmd = f'N_m3u8DL-RE "{mpd_url}" --auto-select --save-name "{save_name}"{lic_part}'
                    print(f"{BOLD_YELLOW}N_m3u8DL-RE Command:{RESET}\n  {DARK_CYAN}{cmd}{RESET}")
                # Build M3U entries — one per available language for this variant
                for _, lang_name in avail_langs:
                    entry_title = f"{lang_name} [{variant}] DRM"
                    m3u_lines.append(f'#EXTINF:-1 tvg-id="" tvg-logo="{logo_url_drm}" group-title="{title}", {entry_title}')
                    m3u_lines.append('#EXTHTTP:{"Origin":"https://www.hotstar.com","Referer":"https://www.hotstar.com/"}')
                    m3u_lines.append('#EXTVLCOPT:http-extra-headers=Origin: https://www.hotstar.com')
                    m3u_lines.append('#EXTVLCOPT:http-referrer=https://www.hotstar.com/')
                    m3u_lines.append('#KODIPROP:inputstream=inputstream.adaptive')
                    m3u_lines.append('#KODIPROP:inputstream.adaptive.manifest_type=mpd')
                    m3u_lines.append('#KODIPROP:inputstream.adaptive.license_type=com.widevine.alpha')
                    if key_str:
                        m3u_lines.append(f'#KODIPROP:inputstream.adaptive.license_key={key_str}')
                    m3u_lines.append(mpd_url)
                    m3u_lines.append("")
            # ── Build and offer OTT Navigator M3U ────────────────────────────────
            # Re-iterate drm_streams to build OTT lines (keys already fetched above; re-use key_str_global).
            ott_lines = ["#EXTM3U", f"# Title: {title}", f"", f"# Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}", ""]
            seen_ott = set()
            ordered_ott = sorted(drm_streams, key=lambda s: 0 if s["variant"] == "PRIMARY" else 1)
            for stream_ott in ordered_ott:
                mpd_url_ott = stream_ott["mpd_url"]
                mpd_base_ott = mpd_url_ott.split("?")[0]
                if mpd_base_ott in seen_ott:
                    continue
                seen_ott.add(mpd_base_ott)
                variant_ott = stream_ott.get("variant", "")
                license_url_ott = stream_ott.get("license_url") or global_license
                # Try to fetch keys for this MPD
                ks_ott = key_str_global
                try:
                    mi_ott = fetch_mpd_pssh(mpd_url_ott)
                    if mi_ott and mi_ott.get("key_ids") and license_url_ott:
                        ck_ott = try_clearkey_json(mi_ott["key_ids"], license_url_ott)
                        if ck_ott:
                            ks_ott = ",".join(ck_ott)
                        elif mi_ott.get("pssh"):
                            wv_ott = fetch_widevine_keys(mi_ott["pssh"], license_url_ott)
                            if wv_ott and not any(l.startswith("❌") for l in wv_ott):
                                ks_ott = ",".join(wv_ott)
                except Exception:
                    pass
                langs_ott = extract_mpd_languages(mpd_url_ott)
                if not langs_ott:
                    langs_ott = [("unk", "STREAM")]
                ott_url = build_ott_drm_url(mpd_url_ott, ks_ott)
                for _, lname_ott in langs_ott:
                    ott_entry = f"{lname_ott} [{variant_ott}] DRM"
                    ott_lines.append(f'#EXTINF:-1 tvg-id="" tvg-logo="{logo_url_drm}" group-title="{title}", {ott_entry}')
                    ott_lines.append(ott_url)
                    ott_lines.append("")
            if len(ott_lines) > 4:
                ott_fname = f"hotstar_ott_{title.replace(' ','_')}.m3u"
                ans_ott = input(f"\n{BOLD_CYAN}Save M3U? (y/n): {RESET}").strip().lower()
                if ans_ott == "y":
                    try:
                        with open(ott_fname, "w", encoding="utf-8") as fw:
                            fw.write("\n".join(ott_lines))
                        total_ott = len([l for l in ott_lines if l.startswith("#EXTINF")])
                        print(f"{GREEN}✓ M3U saved: {ott_fname} ({total_ott} entries){RESET}")
                    except Exception as e:
                        print(f"{RED}Failed to write M3U: {e}{RESET}")
        except Exception as e:
            print(f"{RED}Error: {e}{RESET}")
        return
    if quality_choice == "4":

        print(f"\n{BOLD_RED}LOGO{RESET}")
        try:
            first_api = build_jhs_api_url(slug_path, "eng")
            req0 = request.Request(first_api, headers=build_jhs_headers_android())
            with request.urlopen(req0) as r0:
                d0 = json.loads(r0.read().decode("utf-8"))
            for sec in d0.get("success", {}).get("page", {}).get("spaces", {}).values():
                for w in sec.get("widget_wrappers", []):
                    pc = w.get("widget", {}).get("data", {}).get("player_config")
                    if pc:
                        img = pc.get("expanded_content_poster", {}).get("image", {}).get("src") or pc.get("cast_image", {}).get("src")
                        if img:
                            logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                            print(f"https://img10.hotstar.com/image/upload/f_auto/{img}")
                        break
        except:
            pass
        if match_no:
            print(f"{GREEN}{match_no}{RESET}")
        print(f"{BOLD_GREEN}{title}{RESET}")
        print(f"{BOLD_MAGENTA}{stream_type}{RESET}")
        seen_urls = set()
        seen_lang_names = set()
        results_lock = __import__('threading').Lock()
        PRIMARY_CODES = [
            ("eng","ENGLISH"),("en","ENGLISH"),("hin","HINDI"),("hi","HINDI"),("hd","HINDI HD"),
            ("mar","MARATHI"),("mr","MARATHI"),("ma","MARATHI"),("guj","GUJARATI"),("gu","GUJARATI"),
            ("bho","BHOJPURI"),("bh","BHOJPURI"),("bih","BHOJPURI"),("pan","PUNJABI"),("pun","PUNJABI"),
            ("pa","PUNJABI"),("pu","PUNJABI"),("har","HARYANVI"),("hv","HARYANVI"),("ha","HARYANVI"),
            ("tam","TAMIL"),("ta","TAMIL"),("tel","TELUGU"),("te","TELUGU"),("kan","KANNADA"),("kn","KANNADA"),
            ("mal","MALAYALAM"),("ml","MALAYALAM"),("ben","BENGALI"),("bn","BENGALI"),("ori","ORIYA"),("or","ORIYA")
        ]
        FALLBACK_CODES = {
            "ENGLISH":["en","eng"],"HINDI":["hi","hd","hin"],"MARATHI":["mr","ma","mar"],"GUJARATI":["gu","guj"],
            "BHOJPURI":["bho","bh","bih"],"PUNJABI":["pan","pun","pa","pu"],"HARYANVI":["hv","ha","har"],
            "TAMIL":["ta","tam"],"TELUGU":["te","tel"],"KANNADA":["kn","kan"],"MALAYALAM":["ml","mal"],
            "BENGALI":["bn","ben"],"ORIYA":["or","ori"]
        }
        # Dedup PRIMARY_CODES by lang_name - keeps all variant codes in fallback map
        _seen_pc = set()
        PRIMARY_CODES_UNIQUE = [(_c,_n) for _c,_n in PRIMARY_CODES if not (_n in _seen_pc or _seen_pc.add(_n))]
        lang_codes_map = {name: [code] + FALLBACK_CODES.get(name, []) for code, name in PRIMARY_CODES_UNIQUE}
        def fetch_jhs_lang(lang_name, codes):
            is_live = stream_type == "LIVE TV"
            for lang_code in codes:
                try:
                    api_url = build_jhs_api_url(slug_path, lang_code, is_live=is_live)
                    req = request.Request(api_url, headers=build_jhs_headers_android())
                    with request.urlopen(req, timeout=10) as resp:
                        data = json.loads(resp.read().decode("utf-8"))
                    player_config = None
                    page_spaces = data.get("success", {}).get("page", {}).get("spaces", {})
                    for sec in page_spaces.values():
                        for w in sec.get("widget_wrappers", []):
                            d = w.get("widget", {}).get("data", {})
                            if "player_config" in d:
                                player_config = d["player_config"]
                                break
                        if player_config:
                            break
                    if not player_config:
                        continue
                    streams = extract_jhs_fallback_only(player_config)
                    for s in streams:
                        url = s.get("content_url")
                        if not url:
                            continue
                        base_url = url.split("?")[0]
                        if is_live:
                            tags = s.get("playback_tags", "") or ""
                            detected_lang = ""
                            for tag in tags.split(";"):
                                if tag.startswith("language:"):
                                    detected_lang = tag.split(":")[1].strip().lower()
                                    break
                            if detected_lang and detected_lang != lang_code.lower():
                                continue
                            display_lang = LANGUAGES.get(detected_lang, lang_name) if detected_lang else lang_name
                        else:
                            display_lang = lang_name
                            if stream_type not in ["MOVIE","TV SHOW"]:
                                path_set = set(base_url.replace("https://","").split("/"))
                                lang_in_url = any(c.lower() in path_set for c in codes)
                                if not lang_in_url:
                                    continue
                        clean_url = url.split("?")[0] if stream_type in ["HIGHLIGHTS","CLIP"] else url
                        is_hdr = "hdr" in url.lower() or "hdr" in str(s.get("playback_tags", "")).lower()
                        return (display_lang, clean_url, is_hdr)
                except:
                    continue
            return None
        with ThreadPoolExecutor(max_workers=2) as jhs_executor:
            jhs_futures = {jhs_executor.submit(fetch_jhs_lang, name, codes): name for name, codes in lang_codes_map.items()}
            for future in as_completed(jhs_futures):
                result = future.result()
                if not result:
                    continue
                lang_name, clean_url, is_hdr = result
                with results_lock:
                    if clean_url not in seen_urls and lang_name not in seen_lang_names:
                        seen_urls.add(clean_url)
                        seen_lang_names.add(lang_name)
                        hdr_tag = " HDR" if is_hdr else ""
                        print(f"{BOLD_CYAN}{lang_name}{hdr_tag} FHD ✓{RESET}")
                        print(f"{GREEN}{clean_url}{RESET}")
                        playlist_entries.append((lang_name, clean_url, is_hdr))
        if not seen_lang_names:
            print(f"{RED}NO ADSFREE STREAM FOUND ❌{RESET}")
        offer_m3u_creation(playlist_entries, title, match_no, stream_type, logo_url)
        print()
        return
    if quality_choice == "5":
        print(f"\n{BOLD_RED}LOGO{RESET}")
        try:
            first_api = build_jhs_4k_api_url(slug_path, "eng")
            req0 = request.Request(first_api, headers=build_jhs_headers())
            with request.urlopen(req0) as r0:
                d0 = json.loads(r0.read().decode("utf-8"))
            for sec in d0.get("success", {}).get("page", {}).get("spaces", {}).values():
                for w in sec.get("widget_wrappers", []):
                    pc = w.get("widget", {}).get("data", {}).get("player_config")
                    if pc:
                        img = pc.get("expanded_content_poster", {}).get("image", {}).get("src") or pc.get("cast_image", {}).get("src")
                        if img:
                            logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                            print(f"https://img10.hotstar.com/image/upload/f_auto/{img}")
                        break
        except:
            pass
        if match_no:
            print(f"{GREEN}{match_no}{RESET}")
        print(f"{BOLD_GREEN}{title}{RESET}")
        print(f"{BOLD_MAGENTA}{stream_type}{RESET}")
        seen_urls = set()
        seen_lang_names = set()
        results_lock = __import__('threading').Lock()
        ordered_results = {}
        PRIMARY_CODES = [
            ("eng","ENGLISH"),("en","ENGLISH"),("hin","HINDI"),("hi","HINDI"),("hd","HINDI HD"),
            ("mar","MARATHI"),("mr","MARATHI"),("ma","MARATHI"),("guj","GUJARATI"),("gu","GUJARATI"),
            ("bho","BHOJPURI"),("bh","BHOJPURI"),("bih","BHOJPURI"),("pan","PUNJABI"),("pun","PUNJABI"),
            ("pa","PUNJABI"),("pu","PUNJABI"),("har","HARYANVI"),("hv","HARYANVI"),("ha","HARYANVI"),
            ("tam","TAMIL"),("ta","TAMIL"),("tel","TELUGU"),("te","TELUGU"),("kan","KANNADA"),("kn","KANNADA"),
            ("mal","MALAYALAM"),("ml","MALAYALAM"),("ben","BENGALI"),("bn","BENGALI"),("ori","ORIYA"),("or","ORIYA")
        ]
        # Dedup by lang_name
        _seen_4k = set()
        PRIMARY_CODES = [(_c,_n) for _c,_n in PRIMARY_CODES if not (_n in _seen_4k or _seen_4k.add(_n))]
        FALLBACK_CODES_4K = {
            "ENGLISH":["en","eng"],"HINDI":["hi","hd","hin"],"MARATHI":["mr","ma","mar"],"GUJARATI":["gu","guj"],
            "BHOJPURI":["bho","bh","bih"],"PUNJABI":["pan","pun","pa","pu"],"HARYANVI":["hv","ha","har"],
            "TAMIL":["ta","tam"],"TELUGU":["te","tel"],"KANNADA":["kn","kan"],"MALAYALAM":["ml","mal"],
            "BENGALI":["bn","ben"],"ORIYA":["or","ori"]
        }
        lang_codes_map_4k = {name: [code] + FALLBACK_CODES_4K.get(name, []) for code, name in PRIMARY_CODES}
        def fetch_jhs4k_single(lang_name, codes):
            is_live = stream_type == "LIVE TV"
            for lang_code in codes:
                try:
                    api_url = build_jhs_4k_api_url(slug_path, lang_code, is_live=is_live)
                    req = request.Request(api_url, headers=build_jhs_headers())
                    with request.urlopen(req, timeout=10) as resp:
                        data = json.loads(resp.read().decode("utf-8"))
                    player_config = None
                    page_spaces = data.get("success", {}).get("page", {}).get("spaces", {})
                    for sec in page_spaces.values():
                        for w in sec.get("widget_wrappers", []):
                            d = w.get("widget", {}).get("data", {})
                            if "player_config" in d:
                                player_config = d["player_config"]
                                break
                        if player_config:
                            break
                    if not player_config:
                        continue
                    streams_4k = extract_4k_streams(player_config)
                    if streams_4k:
                        url = streams_4k[0]["url"]
                        base_url = url.split("?")[0]
                        if stream_type not in ["MOVIE", "TV SHOW"]:
                            path_set = set(base_url.replace("https://", "").split("/"))
                            lang_in_url = any(c.lower() in path_set for c in codes)
                            if not lang_in_url:
                                streams_4k = []
                        if streams_4k:
                            clean_url = url if stream_type not in ["HIGHLIGHTS","CLIP"] else base_url
                            is_hdr = "hdr" in url.lower() or "hdr" in str(streams_4k[0].get("playback_tags", "")).lower()
                            return (lang_name, clean_url, is_hdr, True)
                    streams = extract_jhs_fallback_only(player_config)
                    for s in streams:
                        url = s.get("content_url")
                        if not url:
                            continue
                        base_url = url.split("?")[0]
                        if is_live:
                            tags = s.get("playback_tags", "") or ""
                            detected_lang = ""
                            for tag in tags.split(";"):
                                if tag.startswith("language:"):
                                    detected_lang = tag.split(":")[1].strip().lower()
                                    break
                            if detected_lang and detected_lang != lang_code.lower():
                                continue
                            display_lang = LANGUAGES.get(detected_lang, lang_name) if detected_lang else lang_name
                        else:
                            display_lang = lang_name
                            if stream_type not in ["MOVIE","TV SHOW"]:
                                path_set = set(base_url.replace("https://","").split("/"))
                                lang_in_url = any(c.lower() in path_set for c in codes)
                                if not lang_in_url:
                                    continue
                        clean_url = url.split("?")[0] if stream_type in ["HIGHLIGHTS","CLIP"] else url
                        is_hdr = "hdr" in url.lower() or "hdr" in str(s.get("playback_tags", "")).lower()
                        return (display_lang, clean_url, is_hdr, False)
                except:
                    continue
            return None
        with ThreadPoolExecutor(max_workers=6) as jhs4k_executor:
            jhs4k_futures = {jhs4k_executor.submit(fetch_jhs4k_single, name, codes): name for name, codes in lang_codes_map_4k.items()}
            for future in as_completed(jhs4k_futures):
                result = future.result()
                if not result:
                    continue
                lang_name, clean_url, is_hdr, is_4k = result
                with results_lock:
                    if clean_url not in seen_urls and lang_name not in seen_lang_names:
                        seen_urls.add(clean_url)
                        seen_lang_names.add(lang_name)
                        ordered_results[lang_name] = (clean_url, is_hdr)
        printed_names = set()
        for code,name in LANGUAGES.items():
            if name in ordered_results and name not in printed_names:
                clean_url, is_hdr = ordered_results[name]
                hdr_tag = " HDR" if is_hdr else ""
                label = f"{BOLD_CYAN}{name}{hdr_tag}{RESET}" + f" {DARK_BLUE}4K{RESET}"
                print(label)
                print(f"{GREEN}{clean_url}{RESET}")
                printed_names.add(name)
                playlist_entries.append((name, clean_url, is_hdr))
        if not seen_lang_names:
            print(f"{RED}NO JHS 4K STREAM FOUND ❌{RESET}")
        offer_m3u_creation(playlist_entries, title, match_no, stream_type, logo_url)
        print()
        return
    # Options 1 & 2
    lang_streams = {}
    seen_stream_bases = set()
    logo_printed = False
    with ThreadPoolExecutor(max_workers=2) as executor:
        futures = {
            executor.submit(fetch_lang_stream, lang_code, lang_name, slug_path, input_url, quality_choice): lang_name
            for lang_code, lang_name in UNIQUE_LANGUAGES.items()
        }
        for future in as_completed(futures):
            result = future.result()
            if not result:
                continue
            lang_name = result["lang_name"]
            stream_base = result["stream"].split("?")[0]
            if lang_name in lang_streams or stream_base in seen_stream_bases:
                continue
            lang_streams[lang_name] = result
            seen_stream_bases.add(stream_base)
            if not logo_printed:
                first_config = result["player_config"]
                img = first_config.get("expanded_content_poster", {}).get("image", {}).get("src") or first_config.get("cast_image", {}).get("src")
                if img:
                    logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                print(f"\n{BOLD_RED}LOGO{RESET}")
                if img:
                    print(f"https://img10.hotstar.com/image/upload/f_auto/{img}")
                if match_no:
                    print(f"{GREEN}{match_no}{RESET}")
                print(f"{BOLD_GREEN}{title}{RESET}")
                print(f"{BOLD_MAGENTA}{stream_type}{RESET}")
                logo_printed = True
    for lang_name, res in lang_streams.items():
        clean_stream = res["stream"]
        is_hdr = res.get("is_hdr", False)
        hdr_tag = " HDR" if is_hdr else ""
        print(f"{BOLD_CYAN}{lang_name}{hdr_tag}{RESET}")
        playlist_entries.append((lang_name, clean_stream, is_hdr))
        if quality_choice == "1":
            streams_4k = extract_4k_streams(res["player_config"])
            if streams_4k:
                printed = set()
                for s in streams_4k:
                    clean_url = s["url"].split("?")[0]
                    if clean_url in printed:
                        continue
                    printed.add(clean_url)
                    url_to_print = s["url"]
                    if stream_type in ["HIGHLIGHTS","CLIP"]:
                        print(url_to_print.split("?")[0])
                    else:
                        if "star-sports-hindi-1" in input_url:
                            hdntl_token = extract_hdntl(url_to_print)
                            print(build_ott_url(url_to_print, hdntl_token))
                        else:
                            print(url_to_print)
            else:
                print(f"{BOLD_RED}FHD ✓{RESET}")
                if "star-sports-hindi-1" in input_url:
                    hdntl_token = extract_hdntl(clean_stream)
                    print(build_ott_url(clean_stream, hdntl_token))
                else:
                    print(clean_stream)
        else:
            if "star-sports-hindi-1" in input_url:
                hdntl_token = extract_hdntl(clean_stream)
                print(build_ott_url(clean_stream, hdntl_token))
            else:
                print(clean_stream)
    # Add SDR variants for English/Hindi if HDR exists
    sdr_entries = []
    for lang_name, url, is_hdr in playlist_entries:
        if lang_name in ["ENGLISH", "HINDI"] and is_hdr:
            sdr_url = url.replace("hdr", "sdr").replace("HDR", "sdr")
            if sdr_url != url:
                sdr_entries.append((f"{lang_name} (SDR)", sdr_url, False))
    playlist_entries.extend(sdr_entries)
    # ── Auto-extract hdntl cookie from stream URL (like Option 8) ──────
    _auto_hdntl = ""
    for _ln, _lu, _lh in playlist_entries:
        try:
            _tok = get_hdntl_token_4kads(_lu)
            if _tok:
                _auto_hdntl = _tok
                break
        except Exception:
            pass
    if _auto_hdntl:
        print(f"\n{BOLD_GREEN}COOKIE : {RESET}{CYAN}hdntl={_auto_hdntl}{RESET}")
    offer_m3u_creation(playlist_entries, title, match_no, stream_type, logo_url, auto_hdntl=_auto_hdntl)
    print()


# ===================== OPTION 20 – NORMAL HD (720p) ALL LANGUAGES =====================
def option20_normal_hd(input_url: str):
    """Option 20: NORMAL HD (720p) – Saari languages ke HLS streams, sirf HD quality."""
    slug_path = extract_slug_path(input_url)
    if not slug_path:
        print(f"{RED}Invalid Hotstar URL!{RESET}")
        return

    title, match_no = extract_match_title(input_url)
    stream_type = extract_stream_type(input_url)

    print(f"{BOLD_YELLOW}HD (720p) STREAMS — ALL LANGUAGES{RESET}\n")

    logo_url = ""
    try:
        api_test = build_api_url(slug_path, "eng", "2")
        req_logo = request.Request(api_test, headers=build_headers())
        with request.urlopen(req_logo, timeout=10) as r:
            d = json.loads(r.read().decode("utf-8"))
        for sec in d.get("success", {}).get("page", {}).get("spaces", {}).values():
            for w in sec.get("widget_wrappers", []):
                pc = w.get("widget", {}).get("data", {}).get("player_config")
                if pc:
                    img = pc.get("expanded_content_poster", {}).get("image", {}).get("src") or pc.get("cast_image", {}).get("src")
                    if img:
                        logo_url = f"https://img10.hotstar.com/image/upload/f_auto/{img}"
                    break
            if logo_url:
                break
    except:
        pass

    print(f"{BOLD_RED}LOGO{RESET}")
    if logo_url:
        print(logo_url)
    if match_no:
        print(f"{GREEN}{match_no}{RESET}")
    print(f"{BOLD_GREEN}{title}{RESET}")
    print(f"{BOLD_MAGENTA}{stream_type}{RESET}\n")

    # Fetch HD streams for all languages in parallel using quality "2" (FHD/HD)
    lang_results = {}
    seen_bases = set()
    with ThreadPoolExecutor(max_workers=6) as ex:
        futures = {
            ex.submit(fetch_lang_stream, code, name, slug_path, input_url, "2"): name
            for code, name in UNIQUE_LANGUAGES.items()
        }
        for future in as_completed(futures):
            res = future.result()
            if not res:
                continue
            lang_name = res["lang_name"]
            raw_url = res["stream"]
            base = raw_url.split("?")[0]
            if base in seen_bases:
                continue
            seen_bases.add(base)
            # Force HD (720p): replace resolution segment in URL path
            hd_url = re.sub(r'/(fhd|4k|uhd)/', '/hd/', raw_url, flags=re.IGNORECASE)
            lang_results[lang_name] = (hd_url, res.get("is_hdr", False))

    if not lang_results:
        print(f"{RED}No streams found!{RESET}")
        return

    entries = []
    lang_order = ["ENGLISH", "HINDI", "MARATHI", "GUJARATI", "BHOJPURI", "PUNJABI",
                  "HARYANVI", "TAMIL", "TELUGU", "KANNADA", "MALAYALAM", "BENGALI"]
    seen_base_out = set()
    for lang_name in lang_order:
        if lang_name not in lang_results:
            continue
        url, is_hdr = lang_results[lang_name]
        base = url.split("?")[0]
        if base in seen_base_out:
            continue
        seen_base_out.add(base)
        print(f"{BOLD_YELLOW}{lang_name} HD{RESET}")
        print(f"{GREEN}{url}{RESET}")
        entries.append((f"{lang_name} HD", url, False))

    # Remaining languages not in lang_order
    for lang_name, (url, is_hdr) in lang_results.items():
        if lang_name in lang_order:
            continue
        base = url.split("?")[0]
        if base in seen_base_out:
            continue
        seen_base_out.add(base)
        print(f"{BOLD_YELLOW}{lang_name} HD{RESET}")
        print(f"{GREEN}{url}{RESET}")
        entries.append((f"{lang_name} HD", url, False))

    print(f"\n{GREEN}Total HD streams: {len(entries)}{RESET}")

    if entries:
        offer_m3u_creation(entries, title, match_no, stream_type, logo_url)


# ===================== OPTION 21 – ADS-FREE FHD LITE (SDR ONLY) =====================
def build_api_url_4kads_fhd(asset_id: str, lang: str, slug_path: str = "") -> str:
    """FHD-only SDR builder – sirf FHD (1080p) SDR, ads-free (non_ssai+ssai)."""
    if slug_path:
        base_url = API_TEMPLATE_4KADS.format(slug_path=slug_path)
    else:
        base_url = "https://www.hotstar.com/api/internal/bff/v2/slugs/in/news/news18-india/{id}/live/watch".format(id=asset_id)
    client_capabilities = {
        "ads": ["non_ssai", "ssai"],
        "audio_channel": ["stereo", "dolby51", "atmos"],
        "container": ["fmp4", "fmp4br", "ts"],
        "dvr": ["short", "long"],
        "dynamic_range": ["sdr"],
        "encryption": ["widevine", "plain"],
        "ladder": ["tv", "web", "phone"],
        "package": ["dash", "hls"],
        "resolution": ["fhd", "hd", "sd"],   # max FHD, no 4K
        "video_codec": ["h264", "h265"],
        "video_codec_non_secure": ["h264", "h265", "vp9"]
    }
    drm_parameters = {
        "hdcp_version": ["HDCP_V2_2"],
        "widevine_security_level": ["SW_SECURE_DECODE", "SW_SECURE_CRYPTO"]
    }
    return (
        base_url
        + '?'
        + '&client_capabilities=' + parse.quote(json.dumps(client_capabilities, separators=(',', ':')))
        + '&drm_parameters=' + parse.quote(json.dumps(drm_parameters, separators=(',', ':')))
        + '&request_features=consent_supported'
        + '&lang=' + parse.quote(lang, safe="")
    )


def fetch_stream_4kads_fhd_lite(asset_id: str, lang_codes: List[str], expected_lang: str, max_retries: int = 10, slug_path: str = "") -> Optional[tuple]:
    """Option 5 jaisi fetch lekin FHD (1080p) SDR ke liye — clean Akamai CDN only."""
    for attempt in range(max_retries):
        for lang_code in lang_codes:
            try:
                api_url = build_api_url_4kads_fhd(asset_id, lang_code, slug_path=slug_path)
                player_config = fetch_player_config_4kads(api_url)
                streams = extract_all_streams_4kads(player_config)
                if not streams:
                    continue
                got_any = False
                for s in streams:
                    if str(s.get("type", "")).lower() != "primary":
                        continue
                    raw_url = str(s.get("content_url", "") or "")
                    if not raw_url:
                        continue
                    got_any = True
                    parsed_netloc = urlparse(raw_url).netloc
                    if is_blacklisted_cdn(parsed_netloc):
                        continue
                    if is_cloudfront_url(raw_url):
                        continue
                    detected_lang = detect_language_from_url_4kads(raw_url)
                    if detected_lang and detected_lang != "OTHER" and detected_lang.upper() != expected_lang.upper():
                        continue
                    final_url = rewrite_url_to_clean_cdn(raw_url)
                    return (expected_lang, final_url)
                if got_any and attempt < max_retries - 1:
                    time.sleep(random.uniform(0.5, 1.5))
            except Exception:
                continue
    return None


def option21_adsfree_fhd_lite(input_url: str):
    """Option 21: ADS-FREE FHD LITE – Option 5 jaisa lekin FHD (1080p) SDR only, saari languages."""
    asset_id = parse_asset_id_4kads(input_url)
    if not asset_id:
        print(f"{RED}Error: could not parse asset id from URL{RESET}")
        return

    slug_path = extract_slug_path(input_url) or ""

    print(f"{BOLD_CYAN}ADS-FREE FHD LITE (1080p SDR) — ALL LANGUAGES{RESET}\n")

    # FHD SDR streams for ALL languages in parallel
    fhd_results = {}
    with ThreadPoolExecutor(max_workers=len(LANG_MAP_4KADS)) as executor:
        futures = {
            executor.submit(
                fetch_stream_4kads_fhd_lite,
                asset_id,
                lang_codes,
                LANG_DISPLAY_4KADS.get(lang_codes[0], "ENGLISH"),
                10,
                slug_path
            ): lang_codes
            for lang_num, lang_codes in LANG_MAP_4KADS.items()
        }
        for future in as_completed(futures):
            result = future.result()
            if result:
                lang_name, url = result
                fhd_results[lang_name] = url

    entries = []
    seen_base = set()
    for lang_name in LANG_ORDER_4KADS:
        if lang_name not in fhd_results:
            continue
        url = fhd_results[lang_name]
        base = url.split("?")[0]
        if base in seen_base:
            continue
        seen_base.add(base)
        print(f"{BOLD_CYAN}{lang_name} FHD ADSFREE{RESET}")
        print(url)
        entries.append((f"{lang_name} FHD", url, False))

    print(f"\n{GREEN}Total FHD streams: {len(entries)}{RESET}")

    if entries:
        title, match_no = extract_match_title(input_url)
        stream_type = extract_stream_type(input_url)
        logo_url = extract_logo_from_url(input_url)
        offer_m3u_creation(entries, title, match_no, stream_type, logo_url)


if __name__ == "__main__":
    main()
