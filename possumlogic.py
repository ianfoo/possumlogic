#!/usr/bin/env python3
"""
possumlogic.py -- an archive of Phish performances, via the Phish.net API v5.

One call to /v5/setlists/showdate/<date>.json returns every song in the show
with its `gap` already computed, so there is no HTML parsing and no arithmetic.

    export PL_PHISHNET_API_KEY=...         # or ~/.config/possumlogic/keys.json
                                           # {"phish.net": "..."}
                                           # every PL_ var belongs to this program
    python3 possumlogic.py 2026-07-24 --html report.html --pdf report.pdf

Or keep a growing site of them, one page per show plus a searchable index:

    python3 possumlogic.py 2026-07-22 2026-07-24 --previous --site site
    python3 possumlogic.py --site site --rebuild    # re-render after a CSS edit

Each show lands in site/<date>.html, its data is archived in site/data, and
site/index.html is regenerated from that archive every run. Dates already in
the site are skipped unless --force, so runs are additive and cheap.

Requires: stdlib only for JSON/text output. `pip install weasyprint` for --pdf.
Responses are cached on disk; phish.net asks that clients cache rather than
re-request. Use --refresh to bypass.
"""

import argparse
import base64
import bisect
import contextlib
import collections
import datetime
import glob
import hashlib
import html
import json
import math
import os
import random
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
import urllib.parse
import urllib.request
import zoneinfo

API_ROOT = "https://api.phish.net/v5"
CACHE_TTL = 6 * 3600
# The new home, with the old one still read. A cache is disposable, but
# throwing one away silently means the next run re-fetches thousands of
# responses it already had, so the move is made without that cost.
_CACHE_NEW = os.path.expanduser("~/.cache/possumlogic")
_CACHE_OLD = os.path.expanduser("~/.cache/phishgap")
DEFAULT_CACHE = (_CACHE_OLD if os.path.isdir(_CACHE_OLD)
                 and not os.path.isdir(_CACHE_NEW) else _CACHE_NEW)

# Minimum spacing between live requests. Building a whole tour with --previous
# is a couple of hundred calls, and phish.net is a volunteer operation; the
# cache absorbs everything after the first pass, so the cost is once-only.
# 0.25s was enough to earn a 429, so pace it at well under two per second and
# back off when asked to.
MIN_INTERVAL = 0.6
MAX_TRIES = 5
_last_fetch = [0.0]

# How long a song count has to hold still before it is taken for the finished
# show. This is NOT the run interval: runs can be hourly and the quiet period
# still two. What it has to clear is the longest gap between two consecutive
# songs being entered -- a 45-minute jam, or a setbreak, plus the lag of
# whoever is typing. Call that 90 minutes and round up.
QUIET_HOURS = 2
# After an encore the band has said it is over, so the wait to call the
# show finished drops from two hours to this. Long enough for a second
# encore, which is the only thing that follows the first.
ENCORE_QUIET = datetime.timedelta(minutes=30)

# Backstop for when stability never settles, e.g. a setlist entered set by set
# and then abandoned overnight. Doors are never later than about 20:30 local and
# even a three-set night is done inside five hours, so 09:00 UTC the next day is
# past the latest plausible end for a Pacific show -- and for anywhere else on
# the continent by more. No venue time zone required, just the worst case.
LAST_END_UTC = datetime.time(9, 0)

# --catch-up re-fetches shows this recent even when they are already archived.
# There is no hour that is safely after both an east coast and a west coast
# show, so any schedule can catch a setlist mid-entry; without a recheck window
# that partial fill would be archived and then skipped for good. This also
# picks up phish.net corrections made in the days after a show.
RECHECK_DAYS = 3

# phish.net encodes sets as 1..4 then e / e2 / e3
SET_ORDER = {"1": 0, "2": 1, "3": 2, "4": 3, "e": 4, "e2": 5, "e3": 6}
SET_LABEL = {"1": "SET 1", "2": "SET 2", "3": "SET 3", "4": "SET 4",
             "e": "ENCORE", "e2": "ENCORE 2", "e3": "ENCORE 3"}
# The same sets in running prose. SET_LABEL is a column label and is set in
# caps; "Closed SET 1, before Tweezer" reads as shouting in the middle of a
# sentence, and "the encore" takes an article where "set 2" does not.
SET_PHRASE = {"1": "set 1", "2": "set 2", "3": "set 3", "4": "set 4",
              "e": "the encore", "e2": "the second encore",
              "e3": "the third encore"}
# Back the other way. A saved report stores the column label ("SET 1") where
# the running-order extract stores the key ("1"), and the years page reads
# both -- the extract for the career, a report for whichever show is too new
# to be in it. Derived rather than typed out, so the two cannot drift.
SET_SLUG = {v: k for k, v in SET_LABEL.items()}

# Everything a setlist walk decides about one performance. Cleared before the
# walk's answer is written rather than merged over the old one: `p.update(nb)`
# alone leaves a fossil the first time a rule changes -- a row recorded as a
# set closer, then re-walked under a rule that knows what stood across the
# break, would carry both answers and the renderer would show the older.
NB_KEYS = ("prev", "in", "next", "xprev", "xnext", "first", "last")
# The same, plus the flag saying the walk happened. Anything that rewrites a
# song's history from a song-history response must carry all of these forward:
# none of them is in that response, and each costs a setlist call to work out.
# Listed once, here, because the first four were added in one session and the
# list that copies them forward was in another function and was not updated --
# which would have dropped every new field on the next --previous run.
NB_CARRY = NB_KEYS + ("nb",)


# -------------------------------------------------------------------- api ---

class ApiError(RuntimeError):
    pass


# One file, one key per service, because a file called `apikey` holding a bare
# string does not say whose key it is -- and it stopped being true the moment a
# second service was worth asking. Keyed by the host the key authenticates
# against, so the name of the setting is checkable against the URL it is sent
# to rather than being a label we chose.
CONFIG_DIR = os.path.join(
    os.environ.get("XDG_CONFIG_HOME") or os.path.expanduser("~/.config"),
    "possumlogic")
CONFIG_FILE = os.path.join(CONFIG_DIR, "keys.json")
LEGACY_KEY_FILE = os.path.expanduser("~/.config/phishgap/apikey")

# The environment variable for each service names the service too. PHISHNET_API_KEY
# keeps its name: it is phish.net's key, not this program's, and rebranding
# someone else's credential would be the same mistake in the other direction.
# Everything this program reads from the environment is prefixed PL_, so it
# cannot collide with a variable some other tool owns and so a shell that has
# several of these in it says which belongs to what. The names are derived from
# the service key rather than listed, which is what keeps a third service from
# needing a decision: phish.net becomes PL_PHISH_NET_API_KEY on its own.
ENV_PREFIX = "PL_"

SERVICES = {
    "phish.net": {"signup": "https://phish.net/api"},
    "setlist.fm": {"signup": "https://www.setlist.fm/settings/api"},
}


# Every setting this program takes from the environment, prefixed or not, so a
# variable that is nearly right can be told from one that is simply unknown.
ENV_SETTINGS = ("GOATCOUNTER", "DOMAIN")


def env_all_names():
    """Every environment variable this program will read, prefixed and plain."""
    names = []
    for service in SERVICES:
        names.extend(env_names(service))
    for extra in ENV_SETTINGS:
        names.extend((ENV_PREFIX + extra, extra))
    return tuple(names)


# Reported once each, however many times a value is asked for.
_ENV_SAID = set()


def env_value(stem, quiet=False):
    """Read ENV_PREFIX+stem, falling back to stem, saying which one it used.

    Saying so is the point. A prefix typed slightly wrong -- PL_PHISNET_API_KEY
    -- sets a variable nothing reads, and the fallback then quietly serves
    whatever the unprefixed name happens to hold, which may be a key from a
    year ago. Silence there costs an afternoon. So a fallback announces itself,
    and a PL_ variable nobody recognizes is called out by name.
    """
    for name in (ENV_PREFIX + stem, stem):
        raw = os.environ.get(name)
        if raw and raw.strip():
            if not quiet and name not in _ENV_SAID:
                _ENV_SAID.add(name)
                if not name.startswith(ENV_PREFIX):
                    log("using %s (%s%s is not set)", name, ENV_PREFIX, stem)
                else:
                    log("using %s", name)
            return raw.strip()
    return None


def check_env():
    """Say what the environment is giving this run, and what it is not.

    Two things worth saying out loud. Which variable a value actually came
    from, because an unprefixed one is a value this program did not ask for by
    its own name and may be older than whoever set the prefixed one intended.
    And any PL_ variable nothing reads, because a prefixed name that is not one
    of ours is almost always a typo -- nothing else has a reason to use the
    prefix, and the fallback will hide the mistake by quietly working.
    """
    known = set(env_all_names())
    # One line naming where the configuration came from, not an inventory of
    # what is set. The only per-variable thing worth saying is when a value
    # arrived under a name this program did not ask for by, because that value
    # may be older than whoever set the prefixed one intended.
    plain = [n for n in env_all_names()
             if not n.startswith(ENV_PREFIX)
             and (os.environ.get(n) or "").strip()
             and not (os.environ.get(ENV_PREFIX + n) or "").strip()]
    sources = []
    if any((os.environ.get(n) or "").strip() for n in known):
        sources.append("environment")
    if _config_keys():
        sources.append(os.path.basename(CONFIG_FILE))
    if not sources and os.path.isfile(LEGACY_KEY_FILE):
        sources.append(LEGACY_KEY_FILE)
    if sources:
        log("config from %s", " and ".join(sources))
    for name in plain:
        log("config: %s came from the unprefixed %s -- %s%s is not set",
            name.split("_")[0].lower(), name, ENV_PREFIX, name)
    # Two kinds of near-miss. A wrong name under the right prefix -- and a
    # right name under the wrong prefix, which is the one that hides: PH_ for
    # PL_ sets a variable that starts with neither of our forms, so a check
    # that only looks at PL_ never sees it and the setting silently does
    # nothing. Anything ending in one of our stems is suspicious whatever it
    # begins with.
    stems = tuple(n for n in known if not n.startswith(ENV_PREFIX))
    stray = sorted(n for n in os.environ
                   if n not in known
                   and (n.startswith(ENV_PREFIX)
                        or any(n.endswith("_" + s) for s in stems)))
    for n in stray:
        near = [x for x in known
                if x.startswith(ENV_PREFIX) and n.endswith(x[len(ENV_PREFIX):])]
        log("env: warning -- %s is set but nothing reads it. %s",
            n, ("Did you mean %s?" % near[0]) if near else
            "This program reads %s"
            % ", ".join(sorted(x for x in known if x.startswith(ENV_PREFIX))))
    return stray


def env_names(service):
    """Environment variables to try for `service`, in order of precedence.

    The namespaced name, then the same name without the prefix. Separators in
    the service key are dropped rather than becoming underscores, which makes
    the unprefixed form come out as PHISHNET_API_KEY -- the name already in
    every existing shell and in the repository secret a scheduled job depends
    on tonight. So the fallback is not a compatibility shim bolted on; it is
    simply what these have always been called.
    """
    stem = re.sub(r"[^A-Z0-9]+", "", service.upper()) + "_API_KEY"
    return (ENV_PREFIX + stem, stem)


def _config_keys():
    """{service: key} from the config file, or {} if there is not one."""
    if not os.path.isfile(CONFIG_FILE):
        return {}
    try:
        with open(CONFIG_FILE, encoding="utf-8") as fh:
            data = json.load(fh)
    except ValueError as exc:
        raise ApiError("%s is not valid JSON: %s" % (CONFIG_FILE, exc))
    if not isinstance(data, dict):
        raise ApiError("%s should hold an object of service -> key" % CONFIG_FILE)
    return {k: v for k, v in data.items() if isinstance(v, str) and v.strip()}


def load_key(explicit=None, service="phish.net", required=True):
    """The key for one service: explicit, then environment, then config file.

    Returns None rather than raising when `required` is false, which is how an
    optional service -- one whose absence costs a feature rather than the run --
    asks whether it is configured.
    """
    if explicit:
        return explicit
    meta = SERVICES.get(service) or {}
    stem = env_names(service)[1]                 # the unprefixed form
    found = env_value(stem)
    if found:
        return found
    found = _config_keys().get(service)
    if found:
        return found
    # The old single-key file, which could only ever have been phish.net's.
    if service == "phish.net" and os.path.isfile(LEGACY_KEY_FILE):
        with open(LEGACY_KEY_FILE) as fh:
            legacy = fh.read().strip()
        if legacy:
            return legacy
    if not required:
        return None
    raise ApiError(
        "No %s API key. Set %s, or add it to %s as\n"
        '  {"%s": "..."}\n'
        "Request a key at %s"
        % (service, env_names(service)[0], CONFIG_FILE,
           service, meta.get("signup", "the service")))


def _http_json(url, label, cache_dir=DEFAULT_CACHE, refresh=False,
               ttl=CACHE_TTL, secret=None):
    """Fetch and parse one JSON URL, cached on disk, paced and backed off.

    `label` is what appears in errors, since a URL with a key in it must never
    be printed. `secret`, when given, is masked out of the cache key for the
    same reason. Shared by both APIs this reads, which is also why the pacing
    is global: politeness to one host should not be spent on the other.
    """
    blob = None
    if cache_dir:
        os.makedirs(cache_dir, exist_ok=True)
        # key on the URL minus the apikey so the key never lands on disk
        stable = url.replace(urllib.parse.quote(secret), "KEY") if secret else url
        cache_file = os.path.join(
            cache_dir, hashlib.sha256(stable.encode()).hexdigest()[:20] + ".json")
        if not refresh and os.path.isfile(cache_file):
            if time.time() - os.path.getmtime(cache_file) < ttl:
                with open(cache_file, encoding="utf-8") as fh:
                    blob = fh.read()

    if blob is None:
        req = urllib.request.Request(
            url, headers={"User-Agent": "possumlogic/1.0 (+personal use)",
                          "Accept": "application/json"})
        for attempt in range(1, MAX_TRIES + 1):
            wait = MIN_INTERVAL - (time.time() - _last_fetch[0])
            if wait > 0:
                time.sleep(wait)
            _last_fetch[0] = time.time()
            try:
                with urllib.request.urlopen(req, timeout=30) as resp:
                    blob = resp.read().decode("utf-8")
                break
            except urllib.error.HTTPError as exc:
                retryable = exc.code == 429 or 500 <= exc.code < 600
                if not retryable or attempt == MAX_TRIES:
                    raise ApiError("HTTP %s from %s" % (exc.code, label)) from None
                # Honor Retry-After when the server sends one, else back off.
                try:
                    pause = float(exc.headers.get("Retry-After") or 0)
                except ValueError:
                    pause = 0.0
                pause = pause or min(30.0, 2.0 ** attempt)
                log("HTTP %s from %s, retrying in %.0fs (%d/%d)",
                    exc.code, label, pause, attempt, MAX_TRIES)
                time.sleep(pause)
            except urllib.error.URLError as exc:
                # Wifi dropping out mid-run used to abandon a tour-length fetch
                # and leave half the histories unfilled, so this retries too.
                if attempt == MAX_TRIES:
                    raise ApiError("Could not reach %s: %s"
                                   % (urllib.parse.urlsplit(url).netloc,
                                      exc.reason)) from None
                pause = min(30.0, 2.0 ** attempt)
                log("%s, retrying in %.0fs (%d/%d)",
                    exc.reason, pause, attempt, MAX_TRIES)
                time.sleep(pause)
        if cache_dir:
            with open(cache_file, "w", encoding="utf-8") as fh:
                fh.write(blob)

    try:
        return json.loads(blob)
    except ValueError:
        raise ApiError("Non-JSON response from %s" % label) from None


def get(path, apikey, cache_dir=DEFAULT_CACHE, refresh=False, **params):
    """GET <API_ROOT>/<path>.json, cached on disk. -> list of row dicts."""
    params["apikey"] = apikey
    url = "%s/%s.json?%s" % (API_ROOT, path.strip("/"),
                             urllib.parse.urlencode(params))
    payload = _http_json(url, path, cache_dir=cache_dir, refresh=refresh,
                         secret=apikey)
    if payload.get("error"):
        raise ApiError(payload.get("error_message") or "API reported an error")
    return payload.get("data") or []


# fouldomain scores every circulating performance out of 100 and carries
# phish.net's own show rating besides, which phish.net's API does not expose --
# its /reviews rows have a `score`, but that is votes on the review, running
# 0-42 where the rating is out of 5. Recalculated nightly at their end, so a
# day's cache is as fresh as the data ever gets.
FOUL_ROOT = "https://fouldomain.com/api/public"
FOUL_TTL = 24 * 3600
BEST_LIMIT = 25

# "Top 25 versions" is only a distinction when a song has more than 25 to rank.
# Sparks has been played 15 times, so its whole history comes back as its own
# best, and a score of 35 would have been captioned "highly rated". The score
# is absolute across every Phish performance, so the caption goes by the score
# rather than by the rank: Tweezer's 25th is 86 and earns it, Sparks' second is
# 47 and does not, while both still carry the score and a way to hear them.
RATED_HIGH = 80

# Notes longer than this fold, so that one entry cannot take half the screen.
# Two lines at the width they are set to is about this many characters, and the
# median note is 178: roughly half of them fold, and the short ones are spared
# an affordance they do not need.
JAM_CLAMP = 200

# Grouping a song's history by year gives a heading every 7.9 rows across the
# archive -- but 16% of them head a single row, and on Weigh it is 76%. A year
# heading is the only thing on the page repeating what every row it heads
# already says, which is why it reads as furniture when it covers one row and
# as rhythm when it covers eighteen.
#
# Eras carry something no row does, and there are always three or four of them.
# Bounded by date rather than year because the hiatuses fall mid-year: the last
# show before the first was 2000-10-07, and 2.0 ended at Coventry.
ERAS = (
    ("1.0", "", "2000-10-07"),
    ("2.0", "2002-12-31", "2004-08-15"),
    ("3.0", "2009-03-06", "2020-02-23"),
    ("4.0", "2021-07-28", "9999"),
)


def era(iso):
    for label, start, end in ERAS:
        if start <= iso <= end:
            return label
    # A date in a hiatus belongs to whichever era it sits between; nothing in
    # the archive lands here, but a gap year should not go unlabeled.
    return next((l for l, s, _ in reversed(ERAS) if iso >= s), ERAS[0][0])


def foul(path, cache_dir=DEFAULT_CACHE, refresh=False, **params):
    """GET one fouldomain endpoint. -> parsed payload."""
    url = "%s/%s?%s" % (FOUL_ROOT, path.strip("/"),
                        urllib.parse.urlencode(params))
    return _http_json(url, "fouldomain/%s" % path, cache_dir=cache_dir,
                      refresh=refresh, ttl=FOUL_TTL)


# ---------------------------------------------------------------- fonts ---

# Bagnard, Sebastien Sanfilippo, SIL Open Font License 1.1. Self-hosted rather
# than served from Google: the point of changing face at all was to stop
# wearing the same two the whole internet wears, and the license ships beside
# it in font/OFL.txt as the OFL requires.
#
# One stylesheet for the site rather than the face inlined into every page --
# 13 KB inlined across 640 pages is 8 MB re-downloaded page to page, where one
# linked file is fetched once and cached for the whole visit. The single-file
# --html output keeps its own inlined fonts, since that one is still meant to
# survive being handed to somebody.
#: Everything the pages load that is not a page. The site root is for the
#: files that have to be there -- CNAME, robots.txt, sitemap.xml, .nojekyll --
#: and for the pages themselves; assets lie under here. The sheet, the face and
#: the paper texture are one group and they move as one, which is what makes
#: the relative url()s below work from any depth without a second thought.
STATIC_DIR = "static"
#: Relative to STATIC_DIR, because the @font-face url() resolves against the
#: sheet and both live in there.
FONT_DIR = "font"
DISPLAY_FACE = "Bagnard"
FONT_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                         "site", STATIC_DIR, FONT_DIR, "Bagnard.otf")
#: Not "fonts.css". It defines `body`, which a file named for the fonts has no
#: business doing -- Ian called that a smell and it was: the name described the
#: first thing put in it rather than what it is, which is the one stylesheet
#: every page links.
SITE_SHEET = "site.css"


def sheet_links(sheet):
    """The stylesheet link, and a head start on the face it is going to ask for.

    Without the preload the face cannot begin loading until the sheet has been
    fetched *and parsed*, because that is where its url() lives. Measured on
    localhost, where there is no latency to hide behind: the sheet starts at
    9.3ms and Bagnard.otf at 24.1ms, initiated by the stylesheet rather than by
    the document. On the live site that gap is a whole round trip, and
    `font-display:swap` spends it painting Georgia and then swapping -- which
    is the wordmark flicker, and it is not the inlined face, which no hosted
    page carries.

    `crossorigin` is required even though the font is same-origin: fonts are
    fetched in CORS mode, and a preload without it is discarded and refetched,
    which is slower than not preloading at all.
    """
    base = sheet.rsplit("/", 1)[0] if "/" in sheet else "."
    return ('<link rel="preload" href="%s/%s/%s.otf" as="font" '
            'type="font/otf" crossorigin>\n'
            '<link href="%s" rel="stylesheet">'
            % (base, FONT_DIR, DISPLAY_FACE, sheet))


def inline_font_css():
    """The face as a data URI, for output that has no stylesheet beside it.

    The hosted pages link one shared sheet, which is the whole reason for
    having a sheet. A file handed to somebody in a chat has no beside, so that
    one carries the face itself -- 13 KB of it -- or falls back to Georgia if
    the font is not where it should be.
    """
    try:
        with open(FONT_FILE, "rb") as fh:
            blob = base64.b64encode(fh.read()).decode()
    except OSError:
        return ""
    return ("<style>@font-face{font-family:'%s';font-weight:400;"
            "font-display:swap;src:url(data:font/otf;base64,%s) "
            "format('opentype')}</style>" % (DISPLAY_FACE, blob))
FONTS_CSS = """/* %(face)s -- Sebastien Sanfilippo, SIL Open Font License 1.1.
   License text: ./%(dir)s/OFL.txt */
@font-face{font-family:'%(face)s';src:url('./%(dir)s/Bagnard.otf') format('opentype');
  font-weight:400;font-style:normal;font-display:swap}
/* The paper's texture. It lives here rather than inline in every page for two
   reasons. It was an SVG feTurbulence data URI, which the browser has to run a
   filter over before it can paint -- about a quarter of a second, during which
   the page showed flat color and then visibly changed under the reader. A PNG
   decodes immediately. And as one cached file it costs 640 pages nothing,
   where a data URI large enough to look good would have been carried by each
   of them.

   url() in an external sheet resolves against the sheet, not the page, so this
   one line works from ./, ./show/ and ./song/ alike.

   The blend mode is the variable that has existed unused since the palettes
   were written: multiply on cream darkens the grain into the paper, screen on
   near-black lifts it, and neither shifts the paper color the way painting
   opaque noise over it did. */
body{background-image:var(--grain);background-blend-mode:soft-light}
""" % {"face": DISPLAY_FACE, "dir": FONT_DIR}

# Plex Mono is the only thing still coming from Google: it is doing real work
# at 10-14px and swapping it would cost legibility for no identity gain.
WEB_FONTS = ("https://fonts.googleapis.com/css2"
             "?family=IBM+Plex+Mono:wght@400;500;600"
             "&family=Literata:opsz,wght@7..72,400..500&display=swap")


# ------------------------------------------------------------------ share ---

# A donut with a bite out of it: near enough to Phish's own iconography to be
# recognized on a tab strip, far enough to be our own shape, and the bite is
# the thing the site is about. One path, so it survives being drawn at 16px.
FAVICON = (
    "<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 32 32'>"
    "<circle cx='16' cy='16' r='10.5' fill='none' stroke='#c8371b'"
    " stroke-width='8' stroke-dasharray='44 22' transform='rotate(-42 16 16)'/>"
    "</svg>")
# Fully percent-encoded, so the URI needs no HTML escaping on the way into an
# attribute -- escaping it turned every angle bracket into an entity.
FAVICON_HREF = "data:image/svg+xml,%s" % urllib.parse.quote(FAVICON, safe="/:=")

# Where the site lives, for the absolute URLs link previews require: og:image
# and og:url are fetched by a server that has no idea what page they came from,
# so a relative path is no path at all.
# The domain. In the source rather than only in the environment, because it is
# not a secret and because the alternative bites: GitHub Pages keeps serving a
# custom domain only while CNAME is on the branch, publishing replaces that
# branch wholesale, and a build that does not know the domain writes no CNAME.
# So with this in a repository variable alone, every publish from a laptop --
# where the variable does not exist -- would silently take the domain down
# until the next scheduled run put it back. PL_DOMAIN still overrides, which is
# what a move or a second deployment would use.
DOMAIN = env_value("DOMAIN", quiet=True) or "possumlogic.com"
SITE_URL = ("https://%s" % DOMAIN) if DOMAIN else "https://ianfoo.github.io/phishgap"

# GoatCounter: no cookies, no personal data, nothing stored about a visitor, so
# there is nothing for a consent banner to ask about. Set to the account code
# to switch it on; empty means the pages ask nothing of anyone, which is what
# they do until someone deliberately changes this line.
# Read quietly at import; check_env reports it with everything else, so a run
# gets one block about its environment rather than a line from wherever each
# value happened to be needed.
GOATCOUNTER = (env_value("GOATCOUNTER", quiet=True) or "")
ANALYTICS = ('<script data-goatcounter="https://%s.goatcounter.com/count" '
             'async src="//gc.zgo.at/count.js"></script>' % GOATCOUNTER
             if GOATCOUNTER else "")
#: Where the drawn cards go. Up here rather than with the drawing code,
#: because the share tags below name it and Python reads top to bottom.
CARD_DIR = "card"

#: The house card, for a page that has none of its own. It is `card/index.png`
#: rather than a committed og.png because that file was the one image on the
#: site drawn by nothing: hand-made once, tracked in git, outside card_print's
#: hashing and CARD_REVISION, and therefore unreachable by every fix that
#: corrected the other 1,304 cards. It ended up two names and 420 songs out of
#: date on six live pages. index.png is redrawn from the archive whenever the
#: archive moves, so the worst this fallback can now be is generic.
OG_IMAGE = "%s/index.png" % CARD_DIR


def share_meta(title, description, path="", image=OG_IMAGE, card=None):
    """The tags iMessage, Signal, Discord and the rest read off a link.

    All of them fall back to Open Graph, so that carries the weight; the
    twitter:card line is what makes the ones that look for it render a large
    image rather than a thumbnail. Without og:image the card is a line of gray
    text, which is a poor advertisement for a page of graphs.
    """
    url = "%s/%s" % (SITE_URL, path.lstrip("./")) if path else SITE_URL + "/"
    # A page's own card when one is being made for it, the house card when not
    # -- a preview naming the wrong show is worse than a generic one.
    if card:
        image = "%s/%s.png" % (CARD_DIR, card)
    return "".join((
        '<link rel="icon" href="%s">' % FAVICON_HREF,
        '<meta name="theme-color" content="#c8371b">',
        '<meta name="description" content="%s">' % description,
        '<meta property="og:site_name" content="Possum Logic">',
        '<meta property="og:title" content="%s">' % title,
        '<meta property="og:description" content="%s">' % description,
        '<meta property="og:url" content="%s">' % html.escape(url, quote=True),
        '<meta property="og:image" content="%s/%s">' % (SITE_URL, image),
        '<meta property="og:image:width" content="1200">',
        '<meta property="og:image:height" content="630">',
        '<meta property="og:image:alt" content="%s">' % description,
        '<meta name="twitter:card" content="summary_large_image">',
    ))


# ------------------------------------------------------------------ model ---

def build(showdate, apikey, artist="Phish", rows_out=None, **kw):
    """One show's report. `rows_out`, if given, is filled with the raw setlist.

    Handed back rather than hung on the report: the report is written to disk
    whole, by three separate callers, so a private key on it would have shipped
    to readers the first time one of them forgot to strip it. The rows are what
    the neighbor walk needs and they are already paid for here.
    """
    rows = get("setlists/showdate/%s" % showdate, apikey, **kw)
    if not rows:
        raise ApiError("No setlist found for %s" % showdate)
    if rows_out is not None:
        rows_out.extend(rows)

    artists = {r.get("artist_name") for r in rows if r.get("artist_name")}
    if artist and len(artists) > 1:
        rows = [r for r in rows if r.get("artist_name") == artist] or rows

    rows.sort(key=lambda r: (SET_ORDER.get(str(r.get("set")), 9),
                             int(r.get("position") or 0)))

    songs, seen = [], set()
    for r in rows:
        slug = r.get("slug") or r.get("song")
        if slug in seen:
            continue          # song repeated later in the same show
        seen.add(slug)
        songs.append({
            "set": SET_LABEL.get(str(r.get("set")), "SET %s" % r.get("set")),
            "song": r.get("song") or "",
            "slug": slug,
            "gap": _gap(r),
            "jamchart": str(r.get("isjamchart")) == "1",
            "prev_date": None,
            "prev_venue": None,
            "prev_place": None,
        })

    head = rows[0]
    report = {
        "date": head.get("showdate") or showdate,
        "venue": ", ".join(p for p in (head.get("venue"), head.get("city"),
                                       head.get("state")) if p),
        # Kept apart as well, because the index lays them out separately.
        "venue_name": head.get("venue") or "",
        "city": head.get("city") or "",
        "state": head.get("state") or "",
        "artist": head.get("artist_name") or artist,
        "tour": head.get("tourname") or "",
        "notes": (head.get("setlistnotes") or "").strip(),
        "permalink": head.get("permalink") or "",
        "songs": songs,
    }
    return report


def log(msg, *args):
    """One timestamped line to stderr.

    These are read in a GitHub Actions log days later, usually to answer "what
    did the run at 01:35 actually see" -- so every line carries the UTC time
    and says what was decided rather than what was written. A run that does
    nothing should say why in one line; a run during a show should be legible
    as a sequence of events without opening the archive.
    """
    stamp = _utcnow().strftime("%H:%M:%S")
    print("[%s] %s" % (stamp, msg % args if args else msg), file=sys.stderr)


def _utcnow():
    return datetime.datetime.now(datetime.timezone.utc)


def recent_shows(apikey, days, artist="Phish", **kw):
    """Dates of shows already played within the last `days`, oldest first.

    One call per calendar year touched by the window, which is how --catch-up
    stays cheap enough to run on a schedule: most days it finds nothing new.
    """
    today = _utcnow().date()
    start = today - datetime.timedelta(days=days)
    dates = set()
    # Every year the window touches, not just its two ends. A 21-day window
    # spans at most two calendar years and the set of both read correctly; a
    # backfill does not. Asking for 2020 and 2026 and calling it six years
    # returned 60 shows, all of them from 2020, and silently skipped four
    # years in the middle.
    for year in range(start.year, today.year + 1):
        for row in get("shows/showyear/%d" % year, apikey, **kw):
            if artist and row.get("artist_name") != artist:
                continue
            showdate = row.get("showdate") or ""
            if start.isoformat() <= showdate <= today.isoformat():
                dates.add(showdate)
    return sorted(dates)


def own_history(rows, artist):
    """One band's own performances of a song, oldest first.

    A song's history spans every band that has played it: /slug/ghost returns
    242 Phish rows, 81 Trey Anastasio and one Page McConnell. Unfiltered, the
    last performance of a Phish song came back as a Trey solo show at the
    Capitol Theatre. The same filter keeps the same-date lookup in
    add_previous from landing on another band's row, makes a debut mean the
    first time *this* band played it, and keeps song pages from listing TAB
    shows. Across the archive it drops 4,361 rows of 32,880.
    """
    rows = [r for r in rows if r.get("showdate")
            and (not artist or r.get("artist_name") == artist)]
    rows.sort(key=lambda r: (r["showdate"], int(r.get("position") or 0)))
    return rows


def remeasure(site_dir, artist="Phish"):
    """Recompute every archived report's derived fields from stored histories.

    Gaps, verdicts and previous performances are written into a report when it
    is fetched, so a change to how any of them is decided leaves every report
    already on disk stating the old answer. Re-fetching to correct that would
    be thousands of calls for data the archive already holds; this reads the
    song histories instead and costs nothing.

    Only songs whose stored history covers the show are touched. Anything else
    is left exactly as it was rather than guessed at.
    """
    changed = skipped = 0
    counting = set(load_calendar(site_dir))
    for path in sorted(glob.glob(os.path.join(show_data_dir(site_dir),
                                              "[12]*.json"))):
        with open(path, encoding="utf-8") as fh:
            report = json.load(fh)
        before = json.dumps(report, sort_keys=True)
        counts = report["date"] in counting
        for s in report.get("songs") or []:
            hist = archived_history(site_dir, s.get("slug") or "", report["date"])
            if hist is None:
                # No stored history to recompute from, but a verdict on an
                # event that is not a show is wrong whatever the history says,
                # so that much can still be withdrawn.
                if not counts:
                    for k in ("verdict", "gap_median", "gap_low", "gap_high",
                              "gap_away"):
                        s.pop(k, None)
                    s["verdict"] = None
                    # Nor is there a gap at an event that does not count.
                    s["gap"] = None
                skipped += 1
                continue
            # The verdict fields are rewritten wholesale, so a song that should
            # no longer carry one loses it rather than keeping a stale value.
            for k in ("gap", "verdict", "debut", "prev_date", "prev_venue",
                      "prev_place", "gap_median", "gap_mean", "gap_low",
                      "gap_high", "gap_away", "plays", "recent_plays", "out"):
                s.pop(k, None)
            _finish_song(s, hist, report["date"], counting)
        after = json.dumps(report, sort_keys=True)
        if after != before:
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(report, fh, indent=2)
            changed += 1
    log("remeasured: %d report%s rewritten, %d song rows had no stored history",
        changed, "" if changed == 1 else "s", skipped)
    return changed


def _finish_song(s, hist, date, counting=None):
    """Fill one song's gap, verdict and previous performance from its history.

    Split out so the archived path and the fetched path cannot drift: they
    differ in where the rows came from and in nothing else.

    `counting` is the set of show dates that count toward a gap. Performances
    at the others -- soundchecks, the Tonight Show, Tiny Desk -- are dropped
    before anything is decided, because they are not shows and must not stand
    as the performance before this one. Left in, Gone read as a bustout of
    1,468 whose previous performance was two months earlier: its first outing
    was the Festival 8 soundcheck, so its real debut did not look like one.
    Evolve pointed "last performed" at a Tiny Desk session four shows back that
    was not four shows back, or a show at all.

    The show being described always survives the filter, even when it is itself
    a soundcheck -- those reports still exist and still have to render.
    """
    if counting:
        hist = [h for h in hist
                if h["showdate"] in counting or h["showdate"] == date]
        hist = true_gaps(hist, counting)
    idx = next((i for i, h in enumerate(hist) if h["showdate"] == date), None)
    if idx is not None:
        # by_show has already found the night's real gap, wherever among the
        # repeats phish.net happened to file it.
        g = _gap(hist[idx])
        if g is not None:
            s["gap"] = g
    # remeasure pops the gap before calling, and a history that has none to
    # give -- see _gap -- would otherwise leave the key missing, where every
    # caller reads it by subscript.
    s.setdefault("gap", None)
    # What the song went into. phish.net files the mark on the earlier of the
    # two songs it joins, which is what makes it belong on this row: with a
    # band that segues as much as this one, "Tweezer ->" and "Tweezer" are
    # different facts about the night, and the report was printing them the
    # same. Absent for a set closer, which genuinely went into nothing.
    if idx is not None:
        s["out"] = hist[idx].get("out") or ""
    if idx == 0:
        s["debut"] = True              # this show IS the first performance
        # ...and a debut has no gap. A gap is the shows between a performance
        # and the one before it, so with nothing before it there is no gap to
        # state. phish.net files a number here anyway, and that number is the
        # count of every show the band had played up to that night: the
        # fourteen covers debuted on 2009-10-31 all carry 1,451, the nine on
        # 2016-10-31 all carry 1,747. Kept, it made 244 debuts read as bustouts
        # -- a song cannot come back from an absence it was never in -- and put
        # a debut at the top of the index as the longest gap on the site.
        s["gap"] = None
    # The history is already in hand for the previous-performance lookup, so
    # the song's own gap distribution costs nothing more. Shows before this one
    # only, and never the debut, which has no gap to speak of.
    # No verdict where the comparison would be meaningless. A soundcheck is not
    # a show, so calling something a bustout there says the band brought a song
    # back at an event that does not count as an occasion. And "Jam" is not a
    # composition -- it cannot be overdue or bust out, because there is no
    # particular thing to have been waiting for.
    judgeable = (not counting or counts_toward(counting, date)) \
        and (s.get("slug") or "") not in NOT_A_SONG
    if judgeable:
        s.update(_classify(s["gap"], hist[1:idx if idx else 0], date,
                           plays=None if idx is None else idx + 1,
                           played=hist[:idx] if idx else []))
    else:
        for k in ("verdict", "gap_median", "gap_mean", "gap_low", "gap_high",
                  "gap_away", "plays", "recent_plays"):
            s.pop(k, None)
        s["verdict"] = None
    prior = hist[idx - 1] if idx else (hist[-1] if idx is None and hist else None)
    # Always assigned, never conditionally. The renderers read these by
    # subscript because the report shape has always guaranteed them, so a debut
    # that simply omitted them turned into a KeyError three screens away.
    s["prev_date"] = prior.get("showdate") if prior else None
    s["prev_venue"] = (prior.get("venue") or "") if prior else ""
    s["prev_place"] = ", ".join(
        p for p in (prior.get("city"), prior.get("state")) if p) if prior else ""


def add_previous(report, apikey, site_dir=None, **kw):
    """Optional second pass: date/venue of each song's prior performance.

    Costs one call per song, so it is opt-in behind --previous.

    The response is the song's whole performance history, so with a site to
    write into, that history is archived on the way past. The refresh
    invariant falls out for free: a song's history only changes when the band
    plays it, and when they do, that show's fetch comes back through here.
    """
    missed = []
    artist = report.get("artist")
    counting = set(load_calendar(site_dir)) if site_dir else None
    for s in report["songs"]:
        # Free when the archive already covers this show, which during a
        # backfill is nearly always.
        hist = archived_history(site_dir, s["slug"], report["date"])
        if hist is not None:
            _finish_song(s, hist, report["date"], counting)
            continue
        try:
            hist = get("setlists/slug/%s" % s["slug"], apikey, **kw)
        except ApiError as exc:
            # Worth saying out loud: a rate limit here would otherwise just
            # render as a show whose songs quietly have no history.
            missed.append("%s (%s)" % (s["song"], exc))
            continue
        # One row per show from here down. The response has one row per setlist
        # slot, and a song can come round more than once a night -- five
        # Tweezers at Merriweather in 2014 -- which would otherwise count as
        # five plays, and file four gaps of 0 into the distribution that
        # decides whether tonight's gap is unusual.
        hist = by_show(own_history(hist, artist))
        if site_dir:
            save_song_history(site_dir, s["slug"], s["song"], hist, artist)
        _finish_song(s, hist, report["date"], counting)
    if missed:
        log("warning: no history for %d of %d songs in %s: %s",
            len(missed), len(report["songs"]), report["date"], "; ".join(missed))
    return report


# ----------------------------------------------------------------- render ---

def render_text(report):
    out = ["%s  --  %s" % (report["date"], report["venue"]), ""]
    width = max((len(s["song"]) for s in report["songs"]), default=10)
    current = None
    for s in report["songs"]:
        if s["set"] != current:
            current = s["set"]
            out += ["", current, "-" * (width + 24)]
        gap = "%6s" % ("{:,}".format(s["gap"]) if s["gap"] is not None else "?")
        tail = "  %s" % s["prev_date"] if s["prev_date"] else ""
        out.append("%s  %-*s%s" % (gap, width, s["song"], tail))
    gaps = [s["gap"] for s in report["songs"] if s["gap"] is not None]
    if gaps:
        out += ["", "%d songs | median %s | average %s | longest %s"
                % (len(report["songs"]), _stat(_median(gaps)),
                   _stat(sum(gaps) / len(gaps)), _stat(max(gaps)))]
    return "\n".join(out) + "\n"


LIGHT = {
    "paper": "#f2ece0", "ink": "#17150f", "ink-soft": "#413c31",
    "rule": "#c9bfa9", "rule-soft": "rgba(201,191,169,.45)",
    "hot": "#c8371b", "cool": "#4f6046", "dim": "#6b6456",
    # The accent reads at 4.44:1 on paper -- fine for a 36px figure, under the
    # bar for the 10px chips and verdicts it is also used on. Display keeps the
    # brighter one; anything small takes the darker.
    "hot-text": "#a92e14",
    "track": "rgba(23,21,15,.085)", "band": "#7d7360",
    # The band is the same graphic in both palettes and was the same opacity
    # in both, which is not the same *weight*: measured against its own paper
    # it read 3.09:1 here and 5.29:1 in the dark, so the dark bar shouted
    # where the light one spoke. Solved for the match rather than guessed --
    # .58 on the dark paper lands at 3.10:1.
    "band-opacity": ".85",
    "hover": "rgba(200,55,27,.055)", "edge": "#8d8676",
    "grain": "url(grain-light.png)",
}
DARK = {
    "paper": "#131210", "ink": "#ece5d5", "ink-soft": "#c4bcaa",
    "rule": "#413a30", "rule-soft": "rgba(236,229,213,.13)",
    "hot": "#ff6b45", "cool": "#93b184", "dim": "#9b9384",
    "hot-text": "#ff6b45",
    "track": "rgba(236,229,213,.1)", "band": "#a89c85",
    "band-opacity": ".58",
    "hover": "rgba(255,107,69,.07)", "edge": "#6b5f4f",
    "grain": "url(grain-dark.png)",
}


def _vars(palette):
    return "".join("--%s:%s;" % kv for kv in palette.items())


def _dark_under(root):
    """The dark rules, written against whichever :root selector applies.

    An explicit choice has to beat the system preference in both directions,
    which normally means two copies of the palette drifting apart. Emitting
    both from one dict instead: once for a dark system that has not been
    overridden, once for an explicit dark. Both stay inside `screen`, so print
    and PDF are never anything but paper stock.
    """
    return ("%(r)s{%(v)s}\n"
            # Favicons drawn as solid black on transparency vanish here.
            "%(r)s .badge img.flip{filter:invert(1)}\n"
            # Same icon, same problem, worn as a background by the song pages.
            "%(r)s .ext.i-pin::after{filter:invert(1)}\n"
            % {"r": root, "v": _vars(DARK)})


# Shared by the report pages and the index, so one palette edit moves both.
PALETTE_CSS = (
    ":root{color-scheme:light dark;%s}\n" % _vars(LIGHT)
    + ':root[data-theme="light"]{color-scheme:only light}\n'
    + ':root[data-theme="dark"]{color-scheme:only dark}\n'
    + "@media screen and (prefers-color-scheme:dark){\n%s}\n"
      % _dark_under(':root:not([data-theme="light"])')
    + "@media screen{\n%s}\n" % _dark_under(':root[data-theme="dark"]')
)

# Footer control. The buttons ship disabled and JavaScript enables them, so a
# page with scripting off offers nothing it cannot deliver.
THEME_CSS = """
.theme{display:inline-flex;gap:.3rem;align-items:center}
.theme button{font:inherit;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;padding:.28rem .45rem;border:1px solid var(--edge);
   background:transparent;color:var(--dim);cursor:pointer;border-radius:0}
.theme button:hover:not(:disabled):not(.on){color:var(--ink);
   border-color:var(--ink)}
.theme button.on{background:var(--ink);color:var(--paper);
   border-color:var(--ink)}
/* The selected one is already ink-on-paper reversed, so hovering it must not
   set the text to the color it is sitting on. It brightens its edge instead. */
.theme button.on:hover:not(:disabled){color:var(--paper);
   box-shadow:0 0 0 2px var(--hot)}
.theme button:disabled{opacity:.45;cursor:default}
.theme button:focus-visible{outline:2px solid var(--hot);outline-offset:1px}
@media print{.theme{display:none}}
"""

NEW_ROWS_JS = """<script>
/* Which rows arrived while this reader was away, so a setlist that grew does
   not have to be re-read from the top. The count is kept in this browser
   only; nothing is sent anywhere and nothing is stored server-side.

   The claim used to outlive the fact. The count was banked at page *load*,
   the tag was built once from it and then never touched again -- so "since
   you last looked" really meant "since this browser last loaded a document
   for this show", and the tag was a snapshot frozen at load time. Scrolling
   down to the new songs and back up left it still sitting there insisting
   they were new, because nothing re-evaluated it. Ian caught it doing exactly
   that, and asked the right question: how can it know when I last looked.

   It could not, and it was nearly invisible before, because the meta refresh
   it relied on never fired and the page therefore almost never reloaded.
   Making the reloads real made the false claim frequent.

   One rule makes the words true: **the stored count only ever advances to
   rows that have actually been in view.** So "since you last looked" means
   what it says -- since these rows were last in front of you -- and the tag
   retires itself the moment that becomes true, instead of asserting it for
   the life of the document.

   A first attempt also banked the count when the page was hidden or
   unloaded, to stop an unread page accumulating a claim. That was wrong in
   both directions and the first test caught it. A reload fires pagehide, so
   the count was banked from the document being torn down and the rows in the
   *next* one that the reader had still never seen were recorded as seen: two
   songs landing without a scroll in between reported "1 new", not 2.
   Accumulation is not the bug -- if you never look at the new songs they are
   still new, and saying so is the whole point. */
(function(){
  function start(){
    var live=document.querySelector('.live');
    if(!live||!window.localStorage) return;
    var rows=[].slice.call(document.querySelectorAll('tbody tr'));
    if(!rows.length) return;
    /* Keyed on the night, which the banner carries explicitly. It used to be
       derived from document.title -- but the title leads with the song count,
       "(20) 2026-07-27", so stripping non-digits gave "pl-seen-202026-07-" and
       a *different* key every time a song landed. seen was therefore always 0,
       the mark never fired once, and a key was left behind per song count. */
    var show=live.getAttribute('data-show');
    if(!show) return;
    var key='pl-seen-'+show;
    var seen=parseInt(localStorage.getItem(key)||'0',10);
    function bank(){ try{ localStorage.setItem(key,String(rows.length)); }catch(e){} }
    /* Banked here only when there is nothing new to show, where it is a
       no-op or a correction for a setlist that shrank. With something new it
       waits for the rows to be seen: writing the count at load is precisely
       what made the old claim false. */
    if(!(seen>0&&rows.length>seen)){ bank(); return; }
    var fresh=rows.slice(seen);
    fresh.forEach(function(r){ r.classList.add('fresh'); });
    /* The count is also the way there. Every song row already carries its
       slug as an id, so this is a real href to a real fragment rather than a
       scripted scroll -- which matters because a fragment jump is reversible
       with the Back button and a scroll is not, the same reasoning as the
       show row's landing spot in docs/TODO.md 2h. It points at the *first*
       new row, so the reader lands at the start of what they missed and
       reads down.

       tabindex="-1" so the jump moves focus as well as the viewport, and
       [tabindex="-1"]:focus already drops the ring for exactly this case: a
       landing spot is a place, not a control. */
    var target=fresh[0];
    var tag=document.createElement(target.id?'a':'span');
    tag.className='since-you';
    tag.textContent=(rows.length-seen)+' new since you last looked';
    if(target.id){
      target.setAttribute('tabindex','-1');
      tag.href='#'+target.id;
      /* Non-breaking, so the arrow can never be left on a line by itself. */
      tag.textContent+='\\u00a0\\u2193';
    }
    live.appendChild(tag);
    if(!window.IntersectionObserver){ bank(); return; }
    /* Retired once the last of those rows has held still in view for a
       second. One frame would retire it during a flick past the table, which
       is not looking at it; a second is long enough to mean a deliberate look
       and short enough that any real one counts. */
    var timer=null;
    var io=new IntersectionObserver(function(entries){
      entries.forEach(function(e){
        if(e.isIntersecting){
          if(!timer) timer=setTimeout(function(){
            io.disconnect();
            if(tag.parentNode) tag.parentNode.removeChild(tag);
            bank();
          },1000);
        } else if(timer){ clearTimeout(timer); timer=null; }
      });
    });
    io.observe(fresh[fresh.length-1]);
  }
  /* Same trap as the relative stamp beside it: this ships in the head, so it
     ran before .live or a single row existed and returned every time. */
  if(document.readyState==='loading')
    document.addEventListener('DOMContentLoaded', start);
  else start();
})();
</script>"""


LIVE_JS = """<script>
/* Watch tonight's report for a song landing, and reload when one does.
   Replaces <meta http-equiv="refresh">, which was present, well-formed and
   correctly placed, and did not fire. Two reasons, and it needed both fixed:
   Pages serves cache-control:max-age=600, so a reload inside ten minutes can
   be answered out of the browser's own cache with the same document; and
   browsers throttle or defer a meta refresh in a background tab for as long
   as they like. Hitting reload by hand during the 2026-07-29 show brought in
   five songs at once -- about 25 minutes of drift, well past the cache
   window, so it had not fired at all.

   The report JSON is what is watched rather than the page: it is a few KB
   against 60, and a changing query string puts each request on its own CDN
   cache key, which is what defeats both caches. The page reloads only when
   the song count actually moves, or when the show settles and the banner
   should go -- a timer that reloads regardless is what the meta refresh was.

   Nothing is polled while the tab is hidden. A background tab is exactly
   where a reader is not looking, and visibilitychange brings it up to date
   the moment they look back, which is sooner than any interval would. */
(function(){
  function start(){
    var el=document.querySelector('.live[data-show]');
    if(!el||!window.fetch) return;
    var show=el.getAttribute('data-show');
    var url='../data/shows/'+show+'.json';
    var seen=parseInt((el.querySelector('.n')||{}).textContent||'0',10);
    var key='pl-reloaded-'+show, busy=false;
    function look(){
      if(busy||document.hidden) return;
      busy=true;
      fetch(url+'?t='+Date.now(),{cache:'no-store'}).then(function(r){
        return r.ok?r.json():null;
      }).then(function(d){
        busy=false;
        if(!d||!d.songs) return;
        if(d.songs.length===seen&&d.provisional) return;
        /* One reload per change, remembered for this tab. A reload fetches
           the document fresh, but if a stale copy comes back anyway the
           count still would not match and this would reload on every pass
           for as long as the tab was open. */
        var mark=d.songs.length+(d.provisional?'':'-done');
        try{
          if(sessionStorage.getItem(key)===mark) return;
          sessionStorage.setItem(key,mark);
        }catch(e){}
        location.reload();
      }).catch(function(){ busy=false; });
    }
    setInterval(look,60000);
    document.addEventListener('visibilitychange',function(){
      if(!document.hidden) look();
    });
  }
  /* Ships in the head, so .live does not exist yet. The two scripts beside
     this one were each broken for weeks by exactly that. */
  if(document.readyState==='loading')
    document.addEventListener('DOMContentLoaded',start);
  else start();
})();
</script>"""


AGO_JS = """<script>
/* "4 minutes ago" rather than "01:47 UTC". A clock time on a page about dates
   reads like a server log, and the fact a reader wants is elapsed -- has this
   stalled? -- not the hour it happened. The stamp ships in datetime= so it is
   correct without JavaScript and correct after the tab has been open an hour;
   this only renders it. */
(function(){
  function say(sec){
    if(sec<45) return 'just now';
    var m=Math.round(sec/60);
    if(m<60) return m+' minute'+(m===1?'':'s')+' ago';
    var h=Math.round(m/60);
    return h+' hour'+(h===1?'':'s')+' ago';
  }
  function start(){
    var els=[].slice.call(document.querySelectorAll('time.ago'));
    if(!els.length) return;
    function tick(){
      var now=Date.now();
      els.forEach(function(e){
        var t=Date.parse(e.getAttribute('datetime'));
        if(!isNaN(t)) e.textContent=say((now-t)/1000);
      });
    }
    tick();
    setInterval(tick,20000);
  }
  /* This ships in the head, so on a first load it runs before the body it is
     looking for exists: querySelectorAll found nothing, the function returned,
     and every reader saw the bare 03:41 UTC fallback the markup carries for
     readers with no JavaScript at all. The stamp has been a clock reading on
     every live page since it was written. */
  if(document.readyState==='loading')
    document.addEventListener('DOMContentLoaded', start);
  else start();
})();
</script>"""


ROW_JS = """<script>
(function(){
  // On a phone the song title is a very small target for a link that is the
  // only one in its row, so the row follows it. Delegated rather than wrapped,
  // because an overlay covering the row would swallow the hover the gap
  // figure's tooltip needs. With scripting off the title still works.
  var t=document.querySelector('table');
  if(!t) return;
  document.addEventListener('click', function(e){
    if(e.target.closest('a')) return;
    var tr=e.target.closest('tr');
    if(!tr) return;
    // Two questions live in one row: "where does tonight's version sit in this
    // song's history" and "what else happened the last time they played it".
    // The whole row used to answer only the first, which swallowed the second
    // -- reaching for the previous show landed you on the current one.
    var last=e.target.closest('td.last');
    var a=(last && last.querySelector('a')) || tr.querySelector('td.song a');
    if(!a) return;
    var sel=window.getSelection();
    if(sel && !sel.isCollapsed) return;   // let people copy a venue name
    a.click();
  });
})();
</script>"""

THEME_UI = ("<span class='theme' role='group' aria-label='Color theme'>"
            + "".join("<button type='button' data-theme='%s' disabled>%s</button>"
                      % (v, v.title()) for v in ("auto", "light", "dark"))
            + "</span>")

# Runs in <head> so the stored choice is on the root element before first
# paint, otherwise a dark-mode reader gets a flash of paper. localStorage
# throws on a file:// page in some browsers, which is exactly how these get
# shared, hence the try blocks.
THEME_JS = """<script>
(function(){
  // Deliberately not renamed: this is a private key in a reader's own
  // browser, and changing it would silently reset the light/dark choice
  // of everyone who has ever set one, to rename a string nobody sees.
  var KEY='phishgap-theme', root=document.documentElement;
  function apply(v){
    if(v==='light'||v==='dark') root.setAttribute('data-theme',v);
    else root.removeAttribute('data-theme');
  }
  try{ apply(localStorage.getItem(KEY)); }catch(e){}
  document.addEventListener('DOMContentLoaded', function(){
    var box=document.querySelector('.theme');
    if(!box) return;
    var btns=[].slice.call(box.querySelectorAll('button'));
    function mark(){
      var cur=root.getAttribute('data-theme')||'auto';
      btns.forEach(function(b){
        var on=b.getAttribute('data-theme')===cur;
        b.classList.toggle('on',on);
        b.setAttribute('aria-pressed',on?'true':'false');
      });
    }
    btns.forEach(function(b){
      b.disabled=false;
      b.addEventListener('click',function(){
        var v=b.getAttribute('data-theme');
        apply(v);
        try{ v==='auto'?localStorage.removeItem(KEY):localStorage.setItem(KEY,v); }
        catch(e){}
        mark();
      });
    });
    mark();
  });
})();
</script>"""

# The jumping layer, on top of the accessibility floor: not being forced to
# reach for a pointer, rather than a keyboard interface that takes the site
# over. Three keys, and the page decides which of them it offers.
#
# The list in the overlay is read off the page rather than written down here,
# which is the same discipline the FAQ's contents block follows for the same
# reason: a help panel that names a key the page does not bind is worse than no
# help panel. A page with no search box does not claim "/" focuses one.
#
# <dialog> rather than a div: it brings the modal semantics, the Escape key,
# the focus move on open and the focus restore on close, and it does all of
# that in the browser rather than in a focus trap here that would be wrong on
# some platform nobody tested.
KEYS_JS = """<script>
(function(){
  function ready(fn){
    if(document.readyState!=='loading') fn();
    else document.addEventListener('DOMContentLoaded',fn);
  }
  ready(function(){
    var search=document.querySelector('input.search');
    var prev=document.querySelector('a[rel="prev"]');
    var next=document.querySelector('a[rel="next"]');
    var foot=document.querySelector('footer');
    if(!foot) return;
    // "Previous show, 2026-07-25" -> "Previous show". The pager already writes
    // a label saying what it steps through, so the overlay does not have to
    // guess whether this page is a list of shows or of anything else.
    function what(a,fallback){
      var s=(a&&a.getAttribute('aria-label'))||'';
      s=s.split(',')[0].trim();
      return s||fallback;
    }
    var rows=[];
    if(search){
      rows.push(['/','Jump to the search box']);
      rows.push(['Esc','Clear the search']);
    }
    if(prev) rows.push(['[  \\u2190', what(prev,'Previous')]);
    if(next) rows.push([']  \\u2192', what(next,'Next')]);
    rows.push(['?','This list']);
    var dlg=document.createElement('dialog');
    dlg.className='keys';
    dlg.setAttribute('aria-label','Keyboard shortcuts');
    dlg.innerHTML='<p class="cap">Keyboard</p><dl>'
      + rows.map(function(r){
          return '<div><dt><kbd>'+r[0].split('  ').join('</kbd> <kbd>')
                 +'</kbd></dt><dd>'+r[1]+'</dd></div>'; }).join('')
      + '</dl>'
      + (rows.length>1?'':'<p class="none">This page has nothing else to '
         + 'step through. The show and song lists have more.</p>')
      + '<form method="dialog"><button>Close</button></form>';
    document.body.appendChild(dlg);
    // A button as well as a key, because a shortcut nobody can find is a
    // shortcut nobody has. It carries the key it stands for.
    var hint=document.createElement('button');
    hint.type='button';
    hint.className='keyhint';
    hint.setAttribute('aria-haspopup','dialog');
    hint.innerHTML='Keys <kbd>?</kbd>';
    hint.addEventListener('click',function(){ dlg.showModal(); });
    foot.appendChild(hint);
    document.addEventListener('keydown',function(e){
      if(e.metaKey||e.ctrlKey||e.altKey||dlg.open) return;
      var t=e.target;
      // While typing, every one of these is a character somebody meant.
      if(t&&(t.tagName==='INPUT'||t.tagName==='TEXTAREA'
             ||t.tagName==='SELECT'||t.isContentEditable)) return;
      if(e.key==='?'){ e.preventDefault(); dlg.showModal(); return; }
      if(prev&&(e.key==='['||e.key==='ArrowLeft')){ e.preventDefault(); prev.click(); }
      if(next&&(e.key===']'||e.key==='ArrowRight')){ e.preventDefault(); next.click(); }
    });
  });
})();
</script>"""

# --------------------------------------------------------------------------
# The blocks every stylesheet shares.
#
# These used to be three copies of the same rule text, one per sheet, and the
# copies drifted: a nav that could not wrap, a footer link left in the browser
# default blue on seven page types of eight, a sticky-header hide out-specified
# by a modifier class, and tabular figures set on show pages only. Every one of
# those was invisible until a page leaned on it, and every one was found by a
# reader rather than by a check. A block named once cannot diverge from itself.
#
# Order is load-bearing: each sheet splices these in at the position its own
# copy occupied, so the cascade is unchanged. See docs/TODO.md 8e.
# --------------------------------------------------------------------------

#: Skip link, the site's own focus ring, the box model and tabular figures --
#: what every page type wants before it states anything of its own.
BASE_CSS = PALETTE_CSS + THEME_CSS + """
/* Off-screen until it is focused, then a real control in the corner. The
   index puts 691 rows between the search box and the footer, and a keyboard
   arriving on any page had to walk the whole navigation first. */
.skip{position:absolute;left:-9999px;top:0;z-index:10}
.skip:focus{left:.5rem;top:.5rem;background:var(--paper);color:var(--ink);
   padding:.5rem .7rem;border:2px solid var(--hot);font-size:.75rem;
   letter-spacing:.06em;text-transform:uppercase;text-decoration:none}
/* One focus ring for everything that takes focus, in the site's own accent.
   The controls -- search, sort, chips -- already had this; links, rows and
   hero cards fell through to the browser default, which is a 1px ring in
   Chrome blue. On cream paper and on charcoal that is both off-palette and
   thin, and rows and cards are the things a keyboard actually travels
   between. :focus-visible, so a pointer click does not draw it. */
a:focus-visible,button:focus-visible,select:focus-visible,input:focus-visible,
summary:focus-visible,[tabindex]:not([tabindex="-1"]):focus-visible{
  outline:2px solid var(--hot);outline-offset:2px}
/* The identity line under every h1, and any link inside it. It carried no link
   at all until the song page's debut date moved up into it on 2026-07-30, and
   there was no rule to catch it: it rendered #9E9EFF and underlined on all 589
   song pages, measured, while the best-version link two lines below it was
   site ink with no underline.
   **The fifth time a link here has shipped in the browser's default blue**,
   and the reason it is written into BASE_CSS rather than SONG_CSS is that
   `.show` is on every page type. Putting it in the one sheet that needs it
   today is precisely how the other four happened. */
.show a{color:var(--ink-soft);text-decoration:none;
   border-bottom:1px solid var(--rule)}
.show a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* The skip link's landing spot takes focus so the next Tab continues from
   the content rather than from the top of the page again -- but it is a
   place, not a control, so it does not wear the control's ring. */
[tabindex="-1"]:focus{outline:none}
/* A row is a wide, short target and the ring reads better tucked against it
   than floating two pixels off a full-width band. */
.reports a.row:focus-visible,.vn a.row:focus-visible,.due a.row:focus-visible,
a.card:focus-visible{outline-offset:-2px}
*{box-sizing:border-box}
/* The whole scale, pitched one step up from where it started.
   Ian: "the prose text feels small even by these standards... I feel this way
   on iPhone and on desktop." He was right, and the figures said so: body was
   .875rem against a 16px default, so running text set at 14px and the labels
   -- the size used more than any other on the site, 101 declarations of it --
   set at 10px.
   It is stated once, here, rather than as 300 edited declarations. Everything
   on this site is already sized in rem, so lifting the root lifts all of it in
   proportion and no two sizes can change their relationship to each other. It
   is also relative rather than absolute: a reader who has set their browser to
   20px gets 22.5, not 18.
   The top of the scale is held rather than lifted -- see the h1 clamps, whose
   rem endpoints are pulled back by exactly this factor. A wordmark at 64px was
   never the complaint; a scale should compress at the display end and open up
   at the reading end, and this one now does both. */
html{font-size:112.5%}
/* Every figure on this site sits in a column beside another figure. Tabular
   numerals are what makes that work. This lived in the show-page sheet only,
   so the index, songs, due, venues and every song page were setting their
   figures in proportional digits -- the fourth rule found in one sheet of
   three (see docs/TODO.md 8c), and invisible until somebody asked why a
   column of numbers with decimals in it would not line up. */
body{font-variant-numeric:tabular-nums}
/* The keyboard overlay and the button that opens it. In the block every sheet
   shares, because it is page furniture like the skip link above it and there
   is no page it does not belong on -- and because stating it three times is
   how four rules on this site came to disagree with themselves. */
.keyhint{font:inherit;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--dim);background:none;
   border:0;border-bottom:1px solid var(--rule);padding:0 0 .1rem;
   cursor:pointer;display:inline-flex;align-items:baseline;gap:.35rem}
.keyhint:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* Not on a touch device. It is a discovery aid for keys, and a phone has
   none -- so it sat in the footer of every page offering "[ and ] to step
   between shows" to a reader with no way to press either, and "Keys ?" is
   doubly meaningless when there is no ? to press. The footer is a flex row
   with gap and no separator characters, so this leaves nothing stranded
   behind it.

   The `?` handler stays bound either way: this hides a button, it does not
   remove the feature, so an iPad with a keyboard attached -- whose *primary*
   pointer is still coarse -- can open the same list. */
@media (hover:none) and (pointer:coarse){.keyhint{display:none}}
dialog.keys{border:1px solid var(--ink);background:var(--paper);
   color:var(--ink);padding:1.2rem 1.4rem 1rem;max-width:24rem;width:calc(100% - 2rem)}
dialog.keys::backdrop{background:rgba(0,0,0,.5)}
dialog.keys .cap{margin:0 0 .8rem;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--ink);font-weight:600}
dialog.keys dl{margin:0;display:grid;grid-template-columns:max-content 1fr;
   gap:.5rem .9rem}
/* display:contents so the two cells of a row land in the outer grid's columns
   -- otherwise every <div> is one grid item and the keys never form a column. */
dialog.keys dl > div{display:contents}
dialog.keys dt{margin:0}
dialog.keys dd{margin:0;font-size:.75rem;color:var(--ink-soft)}
dialog.keys .none{margin:.9rem 0 0;font-size:.75rem;color:var(--dim)}
kbd{font-family:'IBM Plex Mono',ui-monospace,monospace;font-size:.6875rem;
   line-height:1;padding:.25rem .4rem;border:1px solid var(--edge);
   color:var(--ink);background:var(--hover);white-space:nowrap}
dialog.keys form{margin:1rem 0 0;text-align:right}
dialog.keys button{font:inherit;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--dim);background:none;
   border:1px solid var(--rule);padding:.4rem .7rem;cursor:pointer}
dialog.keys button:hover{color:var(--hot-text);border-color:var(--hot-text)}
@media print{.keyhint,dialog.keys{display:none}}
"""

#: The page box and its measure.
#:
#: `background-color`, never the `background` shorthand. The shorthand resets
#: every background longhand it does not mention, `background-image` among
#: them, and the site sheet hangs the paper texture there one link earlier in
#: the same <head>. That single word switched the grain off for its entire
#: life -- generated, published, linked and never once painted, here or on
#: gh-pages. It is also invisible in a screenshot, because the page is the
#: right colour either way, just flat. tools/check_paper.py measures it now.
BODY_BOX_CSS = """body{margin:0;padding:clamp(1.4rem,4vw,3.5rem) clamp(1rem,5vw,3rem);
     background-color:var(--paper);color:var(--ink);
     font-family:'IBM Plex Mono',ui-monospace,SFMono-Regular,monospace;
     font-size:.875rem;line-height:1.55}
/* The measure in rem rather than px, so it travels with the type. Stated as
   960px it would have held still while the scale went up a step, which quietly
   shortens every line and tightens every column -- the same page with less room
   in it. 60rem is the 960px this has always been, at the root above. */
.wrap{max-width:60rem;margin:0 auto}
/* clip, not hidden, and the difference is the whole reason this is safe:
   overflow:hidden would make the body a scroll container and break every
   position:sticky header on the site, where clip does not.

   It is here because a hidden thing was still taking up room. The show pages'
   hover tooltip is position:absolute and white-space:nowrap, and it is hidden
   with visibility:hidden -- which still lays out. That was found once and fixed
   only for phones, by dropping the tooltip below 620px; above 620px every show
   page has been scrollable sideways ever since. Measured on the live build at
   1280px: 1,627px of scroll width, so the page slid 347px into nothing.
   The general shape is what earns a rule rather than a patch -- an off-screen
   or invisible decoration extends the scrollable area exactly as a visible one
   does, and the page it does it to looks completely normal.

   On html as well as body, and that is not belt and braces. An overflow set on
   body alone is *propagated* to the viewport, and body is then treated as
   visible -- so `body{overflow-x:clip}` by itself clips nothing, which is
   exactly what the first attempt at this measured: the rule shipped, the page
   still scrolled 347px. */
html,body{overflow-x:clip}
"""

#: The whole navigation strip. It used to be four near-identical `.crumb`
#: rules in four sheets plus a shared hit-area block, which is the arrangement
#: that has produced four bugs in this file -- a nav that could not wrap among
#: them. Show pages still lay theirs out differently, because they carry a
#: pager row the others do not, but everything about the strip itself is here.
#:
#: Two groups, not one list. Ian, 2026-07-30: "There's also a real mixture of
#: types of targets: shows, songs, years, venues, even due link to tabular
#: data. FAQ and How This Works are a different sort of target." They are: six
#: of them are the archive, two are about the archive. `.lists` is set one step
#: up and in reading ink, `.meta` stays at the old size in the dim, and on a
#: wide screen an auto margin pushes it to the far end of the row. No
#: separator glyph anywhere in it -- a middot between two groups stranded at
#: the end of a line the moment the strip wrapped, which it does at every
#: phone width.
NAV_CSS = """.crumb{display:flex;flex-wrap:wrap;align-items:baseline;
   gap:.55rem .9rem;margin-bottom:1.1rem;
   letter-spacing:.14em;text-transform:uppercase}
.crumb .lists,.crumb .meta{display:flex;flex-wrap:wrap;align-items:baseline;
   gap:.55rem .9rem}
.crumb .lists{font-size:.75rem}
.crumb .meta{font-size:.625rem;margin-left:auto}
/* Transparent rather than absent, so the strip does not move by a pixel when
   an item is hovered or when it is the page you are on. The hairline under
   every item went with it: seven of them under seven words set at 11px read
   as a row of fine print rather than as the way around the site, and in a nav
   landmark the underline is not carrying any meaning a body-text link needs
   it for. What tells you where you are is now the one item drawn in full ink
   with a rule under it. */
.crumb a{color:var(--ink-soft);text-decoration:none;white-space:nowrap;
   padding-bottom:.15rem;border-bottom:2px solid transparent}
.crumb .meta a{color:var(--dim)}
/* --hot-text, not --hot: these are 12px and 10px, so they want the 4.5 floor
   and --hot is 4.44 on paper. See the palette note. */
.crumb a:hover,.crumb a:focus-visible{color:var(--hot-text);
   border-bottom-color:var(--hot-text)}
.crumb a.here{color:var(--ink);border-bottom-color:var(--ink);cursor:default}
/* The site's name, not a link. It used to go where "Shows" goes, so the strip
   offered the same destination twice under two labels. */
.crumb .mark{color:var(--ink);border-bottom:0;cursor:default}
/* WCAG 2.5.8 asks for 24x24 and these measured 37x19, with "Due" only 22 wide.
   Padding is the obvious fix and the wrong one here: the border-bottom *is*
   the affordance, and padding-bottom would push that underline away from the
   word it underlines. So the ink stays exactly where it is and only the hit
   area grows -- a pseudo-element centered on the label, and never narrower
   than it is tall. It sits inside the anchor, so it is the same target. */
.crumb a{position:relative}
.crumb a::before{content:"";position:absolute;left:50%;top:50%;
   transform:translate(-50%,-50%);width:100%;min-width:24px;height:24px}
/* On a phone the strip is the whole of the navigation and 24px is the floor,
   not the target: Apple asks 44pt, Material 48dp, and WCAG's own AAA level
   agrees at 44. So the six destinations get 44px targets here.

   Which costs a row unless the labels are made to fit one, and they were not:
   at .75rem and .14em the six of them are 310px of ink in the 336px a 390px
   phone leaves, so "Venues" wrapped alone onto a second row and the strip came
   to 184px -- 22% of the screen, to say six words. Measured across the
   settings, .6875rem at .1em is 269px and fits, and it is still a size and a
   half up on the 11.25px this strip used to be set at. Under about 340px it
   goes back to two rows, which is why the row gap is what it is: 44px targets
   need 44px between their centers, and the gap is the only thing providing it.

   The meta pair keeps 24px, the AA floor. They are the two least-used links on
   the site and buying them 44px each costs another 20px of every phone screen.
   They also drop the auto margin and take a row of their own, rather than
   being pushed to a right edge a few characters away. */
@media (max-width:620px){
  .crumb{row-gap:1.5rem}
  .crumb .lists{font-size:.6875rem;letter-spacing:.1em;gap:1.5rem .7rem}
  .crumb .meta{margin-left:0;flex-basis:100%}
  .crumb .lists a::before{min-width:44px;height:44px}
}
/* The section a page sits in, which is not the page it is. A show page
   belongs under Shows and a song page under Songs, but neither *is* that
   page. Ian, 2026-07-30: "Considering 'show' part of 'shows' makes sense, but
   if we highlight it, then it makes it look like we're already there, and
   that definitely violates some sort of guideline." It does, and the
   guideline is aria-current: "page" is a claim that this is the document you
   are reading, and a show page saying it about the index is simply false --
   it would also take away the link, stranding the one route back to the list.

   So there are three states and not two: nothing, the section you are in
   (still a link, ink instead of soft ink, a rule in the edge color), and the
   page you are on (not a link, full ink, full rule). The markup says the same
   thing to a screen reader -- aria-current="page" for the page, plain "true"
   for the item in the set that contains it. */
.crumb a.sect{color:var(--ink);border-bottom-color:var(--edge)}
.crumb a.sect:hover,.crumb a.sect:focus-visible{color:var(--hot-text);
   border-bottom-color:var(--hot-text)}
@media print{.crumb .meta{display:none}}
"""


#: The filename of the page holding all three groups.
#:
#: It was `dormant.html` for the three days between that page shipping and the
#: night the split landed, and it stayed `dormant.html` for four more -- so the
#: page was titled *Out of rotation*, headed *Out of rotation*, linked as *out
#: of rotation*, and served from a URL naming one of the three things it keeps
#: apart. Ian: "the artifact name did not update with the conceptual shift."
#: Renaming a published URL is a thing to do once, so the name is a constant
#: this time rather than a string in seven places; `dormant.html` stays behind
#: as a forwarding page, since it is in the sitemap and on a preview card.
ROTATION_PAGE = "out-of-rotation.html"

#: The page for everything the band played that was not a show.
#:
#: Named for what unites the two kinds rather than for the larger one. Thirteen
#: of the twenty are soundchecks and seven are television or radio sessions, so
#: calling the page Soundchecks would be `dormant.html` again -- a filename
#: naming one of the things it holds. "Not a show" is also already this site's
#: phrase for it: it is what a song page prints in the gap column of one of
#: these rows, and what the songs index prints for a song that has only ever
#: been played at one.
NOT_A_SHOW_PAGE = "not-a-show.html"

#: A page's card is named for the page. Derived rather than written twice: the
#: name appears in the <meta og:image> of the page and in the filename the
#: shooter writes, and a card whose name has drifted from its page is a
#: preview that 404s -- which is exactly the failure og.png was papering over.
def card_name(page):
    return page[:-len(".html")] if page.endswith(".html") else page


ROTATION_CARD = card_name(ROTATION_PAGE)
NOT_A_SHOW_CARD = card_name(NOT_A_SHOW_PAGE)

#: The six lists that are the archive, then the two pages about it. Ian,
#: 2026-07-30, on the order: "songs should come before years. I feel like
#: Years and Venues go together. Due and Dormant go together as well."
#: The four ways into the archive, then the two pages about it.
#:
#: It held six until 2026-07-31, and the two that left are the reason this
#: comment exists. Ian: "we are starting to really crowd that nav bar… I don't
#: think the mobile widths could survive another addition." Measured at 390px
#: he was right with room to spare -- one line holds 336px, the six labels
#: came to 400px, and "Out of rotation" alone was 130px of it, more than
#: Shows, Songs and Years put together.
#:
#: The four that stayed are the ones that are *ways in*: every show, every
#: song, every year, every venue. What left -- Due, Out of rotation, Not a
#: show -- are questions asked *about* that archive, and each has a parent
#: that owns it: Due and Out of rotation are two rotation states of songs, so
#: they hang off the songs page; Not a show is the show calendar's own
#: boundary, so it hangs off the index. They are hero cards there, which is a
#: door this site already knows how to draw, and they mark their parent as
#: their section so a reader who arrives at one still sees where they are.
NAV_LISTS = (("Shows", "index.html"), ("Songs", "songs.html"),
             ("Years", "years.html"), ("Venues", "venues.html"))
NAV_META = (("FAQ", "faq.html"), ("How this works", "method.html"))

#: Who the data belongs to. Off the nav strip and in every footer instead --
#: the strip is four browse spines and adding a fifth is a decision about its
#: whole width, which the comment above measures. The footer is the older and
#: better place for a credit anyway, and it is the one element on every one of
#: the 1,311 pages.
ACK_PAGE = "acknowledgments.html"


def nav_strip(here=None, section=None, root="./", mark=False):
    """The navigation strip. Every page on this site gets it from here.

    It was nine copies of the same markup in nine shells, which is how the
    site came to be inconsistent about the one thing a nav has to be right
    about: eight pages marked themselves and the two biggest page types --
    every show and every song, 1,301 of the 1,309 pages -- marked nothing at
    all. No copy carried aria-current either. A reader could not tell where
    they were on the pages they were most likely to be on.

    `here` is the page you are on and `section` is the list it belongs to;
    passing both would be a contradiction and the first one wins, because a
    page cannot be inside itself.

    `mark` puts the wordmark in the strip. It belongs on pages whose <h1> is a
    page title rather than the site's name -- a show, a song, Due, Dormant,
    Years, Venues -- and not on the four whose <h1> already says Possum Logic.
    Venues and Years were missing it before this was one function, which is
    the same drift in a different column.
    """
    def item(label, page):
        if label == here:
            return '<a class="here" aria-current="page">%s</a>' % label
        mod = ' class="sect" aria-current="true"' if label == section else ''
        return '<a href="%s%s"%s>%s</a>' % (root, page, mod, label)
    return ('<nav class="crumb%s" aria-label="Sections">%s'
            '<span class="lists">%s</span><span class="meta">%s</span></nav>'
            % (" sections" if mark else "",
               '<span class="mark">Possum Logic</span>' if mark else "",
               "".join(item(*x) for x in NAV_LISTS),
               "".join(item(*x) for x in NAV_META)))

#: The two horizontal rules: the letterpress double, and the tear line.
RULE2_CSS = """
/* Letterpress: a thick rule with a hairline under it. Three to a page at most
   -- a double rule that turns up six times is wallpaper. */
.rule2{height:5px;margin:0 0 1rem;background:linear-gradient(to bottom,
   var(--ink) 0 3px,transparent 3px 4px,var(--ink) 4px 5px)}
/* The tear line between one set and the next. Never between rows. */
.perf{height:1px;margin:1.5rem 0 .6rem;background:repeating-linear-gradient(
   to right,var(--edge) 0 5px,transparent 5px 10px)}
"""

#: A hero figure's accent and its label.
FIGURE_CSS = """.num.hot{color:var(--hot)}
.lbl{font-size:.625rem;text-transform:uppercase;letter-spacing:.14em;
   color:var(--dim);margin-bottom:.35rem}
"""

#: A hero card that is also a link, in the three of these rules that do not
#: depend on where it goes. Named the moment a third sheet wanted it: the song
#: page's new Debuted card would have been an exact third copy of the show
#: page's block, which is the shape every stylesheet bug in this file has had.
#:
#: The fourth rule is deliberately *not* here. It carries the arrow, and the
#: arrow is the one thing that genuinely differs: the index points right,
#: because the card leaves for another page; the show and song pages point
#: down, because the card lands further down the page you are on. Kept at each
#: point of use so the glyph is readable beside the sheet it belongs to, rather
#: than parameterised into a token nobody can picture.
CARD_LINK_CSS = """a.card{text-decoration:none;color:inherit}
a.card:hover{background:var(--hover)}
a.card:hover .lbl,a.card:hover .lbl::after{color:var(--hot-text)}
"""

#: The standfirst. Two sheets stated this identically, which is how it comes to
#: be one block; and it is the one size that does not simply ride the root lift
#: above. A dek introduces the page's body text, so setting it *smaller* than
#: that text -- 13px over 14 -- had it apologizing for the thing it announces.
#: It is a step above body now. The optical size axis follows the point size,
#: which is what the axis is for.
DEK_CSS = """.dek{margin:.55rem 0 0;font-family:'Literata',Georgia,serif;
   font-size:.9375rem;line-height:1.5;font-variation-settings:'opsz' 16;
   color:var(--dim);max-width:56ch}
/* And its links, which is the fifth time a rule has been found living in one
   sheet of three. This one was in SONG_CSS alone, so the two links in the due
   page's standfirst -- "slipping" and "on the shelf", both pointing at sections
   of the page they introduce -- rendered in the browser's default link blue
   with a browser underline, on the one page on the site that has them. */
.dek a{color:var(--ink-soft);text-decoration:none;
   border-bottom:1px solid var(--rule)}
.dek a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
"""

#: Footer links, drawn the way every other link on the site is drawn.
# The footer's own box, and it sits immediately before FOOTER_LINK_CSS at all
# three call sites, so the two are always emitted together.
#
# Named late. CLAUDE.md listed footer{} for a long time as a near-miss that
# "differs by real amounts" and told sessions to leave it alone; measured on
# 2026-07-30 the three copies were identical once whitespace is normalized, so
# the note was protecting nothing. `.crumb` (four occurrences, four different)
# and `.hero` (flex in one sheet, grid in another) do still differ and stay
# where they are.
# The sort control, which is a native <select> and looked it: the one widget
# on the site drawn by the operating system rather than by this stylesheet,
# sitting beside era chips and a search field that are both drawn here. Ian
# spotted it on the song page and correctly said it was not that page's fault.
#
# `appearance:none` is what native styling turns on, and it is safe on a
# pre-rendered site -- no script and no framework involved. The caret is two
# 45-degree gradients rather than an SVG data URI, because gradients can use
# `currentColor` and so follow the theme; a data URI would have needed one copy
# per palette and would have been the next thing to drift.
#
# What this cannot do, and it is worth writing down before someone tries: the
# open dropdown is an OS menu, not part of the page, and no stylesheet reaches
# it. The `option` colors below help on Windows and Linux and are ignored on
# macOS. Chrome 135 has `appearance:base-select` for the popup as well, which
# is one browser and too new to build on.
#
# Named rather than copied because it was already in two sheets, identical, and
# it is about to be four times longer -- which is how the pairwise copies here
# start disagreeing with each other.
SELECT_CSS = """.sort{appearance:none;-webkit-appearance:none;
   font:inherit;font-size:.75rem;padding:.4rem 1.5rem .4rem .5rem;
   background-color:transparent;color:var(--ink);cursor:pointer;
   border:1px solid var(--edge);border-radius:0;
   background-image:linear-gradient(45deg,transparent 50%,currentColor 50%),
      linear-gradient(135deg,currentColor 50%,transparent 50%);
   background-position:calc(100% - .78rem) calc(50% + .05rem),
      calc(100% - .52rem) calc(50% + .05rem);
   background-size:.26rem .26rem,.26rem .26rem;background-repeat:no-repeat}
/* Matching the era chips beside it, which is the whole point of the exercise. */
.sort:hover{color:var(--ink);border-color:var(--ink-soft)}
/* It ships disabled and is enabled by script; without this the UA grays out
   text the reader can see for the split second before that happens. */
.sort:disabled{opacity:1;color:var(--ink)}
.sort option{background:var(--paper);color:var(--ink)}
"""

def footer_html(root="./", back=("How this works", "method.html"),
                right="{stamp}", here=None):
    """The footer. Every page on this site gets it from here.

    Written for the same reason `nav_strip` was: it was eleven hand-written
    copies of the same three cells across eleven shells, and the moment a
    twelfth cell was wanted -- the credit link below -- eleven was eleven
    chances to leave one page out. The chances are not hypothetical; the nav
    was in ten copies and 1,302 of 1,310 pages marked no location at all.

    `right` is whatever that page can honestly say about its own currency, and
    is a *format placeholder* on the nine pages that have a date: the shells
    are assembled here and formatted at render time, so `{stamp}` travels
    through this function as literal text and is filled in later by the caller
    that knows the date. The two prose pages have no such date and pass None,
    which drops the cell rather than printing an empty one.

    The credit cell is not conditional. What it credits is true of every page
    equally -- the setlists, the audio and the scores are three other
    projects' work -- so the page that thanks them is one click from all of
    them, rather than from the two that happened to carry a credit line
    before. `here` is that page saying so
    itself: the cell stays, because taking it out on one page of 1,311 is how
    a reader learns not to look for it, but it stops being a link to where
    they already are. `back` needs no such guard -- the method page is the one
    page that would have linked to itself and it passes All reports instead.
    """
    ack = ('<span aria-current="page">Acknowledgments</span>'
           if here == ACK_PAGE else
           '<span><a href="%s%s">Acknowledgments</a></span>' % (root, ACK_PAGE))
    cells = ['<span><a href="%s%s">%s</a></span>' % (root, back[1], back[0]),
             ack, "{theme_ui}"]
    if right:
        cells.append("<span>%s</span>" % right)
    return "<footer>%s</footer>" % "\n".join(cells)


FOOTER_BOX_CSS = """footer{margin-top:2.4rem;padding-top:.9rem;border-top:1px solid var(--rule);
   font-size:.75rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim);display:flex;justify-content:space-between;
   flex-wrap:wrap;align-items:center;gap:.4rem .9rem;padding-bottom:2.5rem}
"""
# The padding-bottom is the floating back-to-top's lane, and it is here rather
# than in TOTOP_CSS because the footer is what gets covered. `.totop` is
# position:fixed at the bottom right of the *viewport*, so the one piece of
# content it is guaranteed to sit on top of is the last row of the footer, at
# the one scroll position every reader reaches. It was a near miss before this
# change -- the theme control's row is full-width but its three buttons are all
# on the left, so the button covered empty space -- and adding a fourth cell
# reflowed Keys onto that row's right edge and under it, 42x24px of a 65x26px
# control. 2.5rem plus the body's own 1.575rem clears the 61px the button and
# its offset occupy at narrow widths, which is where the wrap is wide enough to
# reach under it at all; past 60rem the wrap stops short of the button and the
# padding is 40px of air at the very bottom of the page.
#
# Reserved rather than dodged: moving Keys out of the corner would have left
# the *next* cell to land there, and at 768px the sweep found the Dark button
# under it too. A fixed control needs a lane, not a list of exceptions.

FOOTER_LINK_CSS = """footer a{color:var(--dim);text-decoration:none;
   border-bottom:1px solid var(--rule)}
footer a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* 24px tall, without moving the ink -- the same trick `.backtop a` uses, and
   the same floor the nav links were held to. Measured at 19px before this: the
   nav got tap targets when it was audited and the footer did not, so every
   footer link on the site has been under the minimum since it was written. It
   is safe to grow them here because the row gap is .4rem: 2.5px of new box
   above and below against 3.2px of clearance, which the sweep over twelve page
   types at 320/390/430/600/768/1024/1280 confirms leaves no two footer targets
   overlapping. */
footer a{position:relative;display:inline-block}
footer a::before{content:"";position:absolute;left:50%;top:50%;
   transform:translate(-50%,-50%);width:100%;min-width:24px;height:24px}
"""

#: The way back to the navigation, for pages long enough to strand a reader.
#:
#: This was built for the song pages and stayed there for two days, which Ian
#: found from the other end -- reading the due page: "there's no way to get
#: back to the header without a long scroll to the top. We've talked about this
#: before, and it was agreed we'd have some functionality to warp a user back
#: to a navigation-dense area, but either it was applied to only one page, or
#: not at all." It was the first, and the page that had it is not the one that
#: needed it most: a song page runs to 629 rows at the outside, while the index
#: is 692, the song index 589 and out of rotation 281 as a matter of course.
#:
#: One block and one script rather than a copy per shell. Seven shells want it,
#: and the first paragraph of CLAUDE.md is about what a rule copied into three
#: sheets has cost this file.
#:
#: The nav is the top of every one of these pages, so #top is the address of
#: the navigation-dense area rather than merely of the beginning.
TOTOP_CSS = """.totop{position:fixed;right:clamp(.8rem,3vw,2rem);bottom:clamp(.8rem,3vw,2rem);
  z-index:19;width:2.6rem;height:2.6rem;display:flex;align-items:center;
  justify-content:center;background:var(--paper);border:1px solid var(--edge);
  color:var(--ink-soft);text-decoration:none;font-size:1rem}
/* --hot-text: this is 18px, under the 24px the display accent is cleared for,
   and --hot is 4.44:1 on paper. See the palette note. */
.totop:hover{color:var(--hot-text);border-color:var(--hot-text)}
/* And this line is the whole control. `hidden` hides an element by way of the
   browser's own `[hidden]{display:none}`, which is a *user-agent* rule -- so
   any author declaration of `display` beats it outright, whatever the
   specificity, and `display:flex` two lines up is one. The attribute has
   therefore never done anything: measured on the published song pages, where
   this button has been on screen since the day it shipped, pinned over a
   header it was written to appear only in the absence of. The script has been
   setting `.hidden` correctly the whole time and the page ignored it.
   `.totop[hidden]` is an author rule and wins on the ordinary rules.

   Same family as the four bugs listed at the top of CLAUDE.md and worth adding
   to the count: a control that hides itself needs its hidden state proved, not
   its visible one. */
.totop[hidden]{display:none}
@media print{.totop{display:none}}
"""

#: Hidden in the markup, so a reader with no JavaScript is never offered a
#: control that would take them nowhere they are not already -- and never shown
#: one pinned over the header it points at.
TOTOP_HTML = ('<a class="totop" id="totop" href="#top" hidden'
              ' aria-label="Back to the top">&uarr;</a>')

#: Watch the header rather than a scroll offset: no magic number, and it stays
#: right when the header wraps to more lines or a page grows a standfirst. The
#: song pages do this inline because the same observer also drives their
#: condensed header; these pages have nothing else to hang it on.
#:
#: The braces below are JavaScript's, and this string is passed to a shell's
#: .format() as an argument rather than concatenated into it -- a replacement
#: value is not re-scanned, so they need no doubling. Concatenating it would
#: have made `{rootMargin:...}` a format field and raised KeyError at import.
TOTOP_JS = TOTOP_HTML + """<script>
(function(){
  var b=document.getElementById('totop'), h=document.querySelector('header');
  if(!b||!h||!('IntersectionObserver' in window)) return;
  new IntersectionObserver(function(e){ b.hidden=e[0].isIntersecting; },
    {rootMargin:'-8px 0px 0px 0px'}).observe(h);
})();
</script>"""

CSS = BASE_CSS + """h1,h2,.title{text-wrap:balance}
""" + BODY_BOX_CSS + """/* The header is a grid so the tour, which lives in the show line where there
   is room for it, can be lifted out to ride the breadcrumb row where there is
   not -- see the max-width block. One element either way. */
header{padding-bottom:.9rem}
""" + NAV_CSS + """.crumb{margin:0 0 .5rem}
/* Two cells, not three. The middle one held an "All reports" link that the
   section row above already provides, and once that came out it was an empty
   grid cell on every page in the archive.

   The pager is its own strip and keeps the old size and the old hairline: it
   is two dates, not a set of destinations, and it is the one place where an
   underline is doing work -- the labels are bare dates, which do not read as
   links on their own the way a word like "Venues" does. */
.crumb.pager{display:grid;grid-template-columns:1fr 1fr;align-items:baseline;
       gap:.5rem;margin:0 0 1rem;font-size:.625rem;letter-spacing:.14em;
       text-transform:uppercase}
.crumb.pager a{color:var(--dim);border-bottom:1px solid var(--rule)}
.crumb.pager a:hover{border-bottom-color:var(--hot-text)}
.crumb .prev{grid-column:1;justify-self:start}
.crumb .next{grid-column:2;justify-self:end}
/* The date, not the wordmark. A report is one night, and the night's name is
   its date -- but the page led with the site's own name at 4rem while the date sat
   small beside a tour and an ordinal, so the one thing that identified the
   page was the least prominent thing on it. The wordmark is already in the nav
   above as a small mark, which is where a wordmark belongs on a page that is
   not the front door.
   Tabular figures because a date is eight digits: without them the 1s pull the
   whole string crooked at this size. */
/* Plex Mono, not the display face. A show's masthead is a date -- eight
   digits and two hyphens -- and the display face has no GSUB table at all, so
   font-variant-numeric here did nothing and its digits run 254 to 1151 units.
   Because the h1 sits in the grid's auto column, that spread moved the venue
   column by up to 45px depending on which digits the date happened to contain.
   The mono is already loaded, already tabular, and already sets every other
   date on the site. The display face keeps the wordmark, the song titles and
   the method page's headings -- words, which is what it is for. */
h1{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:clamp(1.5111rem,5vw,2.4444rem);line-height:1.1;margin:0 0 .25rem;
   letter-spacing:-.02em;font-variant-numeric:tabular-nums}
/* The day of the week, which the index has always shown and this page never
   did. Set against the date rather than under it: the masthead is already
   two blocks at width, and a third line would make it three. */
h1 .dow{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:400;
   font-size:.75rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim);margin-left:.7rem;vertical-align:.35em;
   white-space:nowrap}
/* Date and tour pair up: both short, so this line cannot wrap and the one
   separator on the page can be neither orphaned nor widowed. The venue is the
   variable-length part, so it gets a line to wrap inside, with no separator to
   strand at the break. */
.show{margin:0;display:flex;flex-wrap:wrap;align-items:baseline}
.show .date{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;font-size:1.5rem;
   line-height:1;color:var(--ink)}
.show .tour{font-size:1rem;font-weight:600;letter-spacing:0;
   text-transform:uppercase;color:var(--dim)}
/* Sits with the tour, not with the date: it is context for the night rather
   than part of naming it. Absent for 1.0, where it cannot be said honestly,
   and for anything phish.net does not count as a show. */
.show .nth{font-size:.75rem;font-weight:400;letter-spacing:0;color:var(--dim);
   text-transform:none;white-space:nowrap}
/* A dim middot, not a second hot bullet: this is an aside about the night, and
   a second hot bullet would give it the rank of the ones naming it.

   It is an element rather than a ::before on the ordinal, and that is the
   whole point. Attached to the ordinal it printed whenever the ordinal did --
   including on the 35 shows phish.net files as "Not Part of a Tour", where
   there is no tour for it to separate. Watkins Glen opened its masthead with
   "· 119th show of 3.0": a separator joining one thing to nothing. Now it is
   emitted only when there is something on each side of it. */
.show .sep{color:var(--dim);margin:0 .45rem;font-size:.75rem}
/* No leading bullet: the tour used to follow the date on this line and the
   bullet joined them. It leads now, and a separator with nothing before it is
   just a dot. The ordinal brings its own, which is the only join left. */
.where{margin:0 0 .45rem;font-size:1.125rem;font-weight:600;letter-spacing:0;
   text-transform:uppercase;color:var(--ink)}
/* The venue and the tour are links now -- to the index filtered to that room
   or that run -- and a masthead link is drawn differently from a link in
   prose. It keeps its own color and weight, because demoting it to --dim
   would demote the venue in the masthead, and takes only the hairline every
   other link on this site wears. Without this rule both came out in the
   browser's default blue with a browser underline, which is the fifth time
   that has happened here: a new link in a sheet with no rule for it. */
.where .v-name a,.show .tour a{color:inherit;text-decoration:none;
   border-bottom:1px solid var(--rule)}
.where .v-name a:hover,.show .tour a:hover{color:var(--hot-text);
   border-bottom-color:var(--hot-text)}
/* Two elements, so there is no separator to strand. The locality steps back
   rather than being joined by punctuation that has nowhere safe to break. */
.where .v-name{display:block}
.where .v-place{display:block;font-size:.875rem;color:var(--ink-soft)}
/* Below the stats rather than in the masthead: the header stays a tight block
   of identity, and the links get their own air on the first screen. */
.links{margin:1.1rem 0 0;display:flex;flex-wrap:wrap;gap:.4rem}
.badge{display:inline-flex;align-items:center;gap:.35rem;line-height:1;
   padding:.32rem .52rem;border:1px solid var(--rule);color:var(--dim);
   font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   text-decoration:none;white-space:nowrap}
.badge img{display:block;width:13px;height:13px}
.badge:hover{color:var(--ink);border-color:var(--ink-soft);
   background:var(--hover)}
""" + RULE2_CSS + """.hero{display:flex;flex-wrap:wrap;margin:.7rem 0 .3rem;
      border-bottom:1px solid var(--ink)}
.card{flex:1 1 0;padding:.85rem 1.1rem;border-left:1px solid var(--rule);
   display:flex;flex-direction:column}
.card:first-child{border-left:0;padding-left:0}
.num{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;font-size:2.25rem;line-height:1;
     letter-spacing:0;margin-top:auto;color:var(--ink)}
""" + FIGURE_CSS + """/* A tab struck in reverse, hung on a rule that runs out to the margin. Lighter
   on the page than slab caps, and it leaves the display face one job. */
h2{display:flex;align-items:center;gap:.6rem;margin:1.5rem 0 .3rem;padding:0;
   border:0;font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:.625rem;letter-spacing:.14em;text-transform:uppercase}
h2 .tab{background:var(--ink);color:var(--paper);padding:.25rem .55rem;
   print-color-adjust:exact;-webkit-print-color-adjust:exact}
h2::after{content:"";flex:1;border-bottom:1px solid var(--ink)}
table{width:100%;border-collapse:collapse;table-layout:fixed}
/* The gap column carries the number plus the song's typical figures under it,
   so it is wider than the number alone would need. */
/* Song, then where it last turned up, then the bar and the figure. The row
   leads with what it is about; the gap is an attribute of it. */
col.c-song{width:26%}
/* The bar takes six points off the "last performed" column. At 16% it was
   about 80px carrying a 32px band, so two rows whose numbers separate clearly
   put their marks two pixels apart -- a scale too short to resolve what it is
   drawing. The date and place it comes from wrap on their own terms and lose
   nothing by it. */
col.c-last{width:32%}
col.c-bar{width:22%}
col.c-gap{width:20%}
table.no-last col.c-song{width:36%}
table.no-last col.c-bar{width:44%}
th{font-size:.625rem;text-transform:uppercase;letter-spacing:.14em;
   color:var(--dim);font-weight:500;text-align:left;padding:.45rem .6rem;
   border-bottom:1px solid var(--rule)}
/* The column headers ride with their own set. Each table is its own containing
   block, so a header can only stay stuck while its own set is on screen: set
   1's is carried back off by the bottom edge of set 1's table just as set 2's
   arrives, and set 1's header is never left standing over set 2's rows. The
   hand-off is the containing block doing it, not script.

   Stuck on the cells rather than on <thead>: under border-collapse:collapse a
   border belongs to the table and not to the cell, so a stuck thead can leave
   its rule behind on the way up. The inset shadow draws it either way, and the
   border-bottom above still does the work when nothing is stuck. */
thead th{position:sticky;top:0;z-index:3;background:var(--paper);
   box-shadow:inset 0 -1px 0 var(--rule)}
/* A sticky strip at the top of the viewport is what makes an anchor land
   underneath one. Nothing on a show page is jumped to from inside it today
   except #main, so this costs nothing now and is here so that the first
   anchor somebody adds is not the one that discovers the problem. */
[id]{scroll-margin-top:2.6rem}
@media print{thead th{position:static;box-shadow:none}}
th.n,td.n{text-align:right;padding-right:1.1rem;white-space:nowrap}
.gap,.song,.last .date{line-height:1.35rem}
td{padding:.5rem .6rem;border-bottom:1px solid var(--rule-soft);
   vertical-align:middle;line-height:1.35rem}
.song{font-weight:600;font-size:1rem}
/* Outlined, not filled: a bustout is the headline of a night and gets the
   solid stamp, while this is an invitation to read something elsewhere. Inside
   the link, so the whole title-and-chip is one target and lights up together. */
/* The segue mark, which is a fact about the night rather than about the song:
   "Tweezer ->" and "Tweezer" are different entries in a setlist, and the report
   was printing them identically. Quiet, because it qualifies the title rather
   than competing with it. */
/* Only the two-glyph mark is tightened, and only slightly. At full monospace
   advance -> reads as a hyphen standing beside an angle bracket rather than as
   one mark; -.06em closes that without breaking the fixed advance the rest of
   the column depends on. A lone > has nothing to close up, so it is left on
   the grid. */
.seg.tight{letter-spacing:-.06em}
.seg{margin-left:.3rem;font-family:'IBM Plex Mono',ui-monospace,monospace;
   font-weight:600;color:var(--dim);white-space:nowrap}
/* One colour, not two. The border was --hot while the text was --hot-text,
   which is invisible at rest and becomes a lighter ring around a darker fill
   the moment the chip reverses. */
.jc-chip{display:inline-block;margin-left:.5rem;padding:.1rem .32rem;
   border:1px solid var(--hot-text);color:var(--hot-text);font-size:.625rem;
   font-weight:600;letter-spacing:.14em;text-transform:uppercase;
   line-height:1.15;vertical-align:.12em;white-space:nowrap}
a.jc-chip{text-decoration:none}
/* The selector this replaces was `td.song a:hover .jc-chip,a.jc-chip:hover`,
   and the first half of that was dead: the chip is a *sibling* of the title
   link, never a descendant of it, so that half had never matched anything.
   What it did do was make the hover look handled, while the half that does
   match -- a.jc-chip:hover, 0-2-1 -- lost the colour to `td.song a:hover` at
   0-2-2 further down this sheet. The chip therefore hovered to var(--hot) on
   var(--hot): 1.00:1, a solid red block where a word had been. Ian caught it.
   Fixed at the other end, by excluding the chip there rather than escalating
   here -- see the note on that rule. Same shape as .live span:not(.since-you),
   the sticky-header hide and .backtop: a modifier class losing to a descendant
   selector, four times now.

   The fill is --ink, not the accent, and that is a hierarchy decision rather
   than a contrast one. A red block of reversed 10px caps is the bustout's
   costume: it is the headline of a show and is struck twice and set two
   degrees off true to say so. This chip is a pointer to a paragraph on
   another page. Reversing it into the same red made the two marks read at the
   same weight one row apart -- Ian caught that too.

   It was never visible before. The chip has always been specified to fill on
   hover, and always with the accent, but the rule above it painted the text
   the colour of the fill, so what shipped was a featureless block. Making the
   word legible is what exposed the collision underneath it.

   Ink, specifically, because the site already reverses to ink for a state
   rather than a claim -- .yr h2 .tab and the tooltip both do. Red says
   something about the music; ink says the pointer is under your pointer.
   15.5:1 light, 14.9:1 dark, and it leaves the red stamp to the bustout
   alone, which is now the only filled red thing on a report. */
a.jc-chip:hover{background:var(--ink);border-color:var(--ink);
   color:var(--paper);
   print-color-adjust:exact;-webkit-print-color-adjust:exact}
.gap{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;font-size:1.5rem;line-height:1;
     white-space:nowrap}
.gap.big{color:var(--hot-text)}
.gap.small{color:var(--cool)}
/* The number carries the gap; these carry how the song usually behaves. Sized
   into the same family as the venue text under a date, which is the smallest
   thing on the page that is comfortably readable. */
.typ{display:block;margin-top:.25rem;font-size:.75rem;color:var(--dim);
   white-space:nowrap}
.typ .abbr{display:none}
.verdict{display:inline-block;margin-left:.5rem;vertical-align:.05em;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;white-space:nowrap}
.verdict.overdue{color:var(--hot-text)}
/* One of the pair shows at a time. Wide: under the figure, where the median
   it is judged against already is. Narrow: beside the title, because the
   gap column there is 3.7rem and the word is wider than that. */
.verdict.at-gap{display:block;margin:.1rem 0 0}
.verdict.premature{color:var(--cool)}
/* A bustout is the headline of a show, not a footnote to it: stamped rather
   than merely colored. print-color-adjust keeps the fill when a browser prints
   it; WeasyPrint keeps backgrounds anyway. */
/* A filled edge reads tighter than text does at the same distance, so the chip
   needs more room above it than the plain tags to sit on the same rhythm. */
/* Struck twice -- fill, a hairline of paper, then the outline again -- and set
   two degrees off true. The right margin buys the rotation its clearance. This
   is the only rotated thing on the site; the moment there are two, it reads as
   a theme rather than a stamp. */
/* --hot-text, like every other reversed stamp on the site. The palette note
   names this case exactly -- "the 10px chips and verdicts it is also used on"
   -- and this one had kept the display accent anyway: paper on --hot is
   4.44:1, and this is 10px. --hot-text lands at 5.79. Dark is unaffected; the
   two are the same colour there. */
.verdict.bustout{display:inline-block;margin:0 .6rem .1rem .5rem;
   background:var(--hot-text);color:var(--paper);padding:.16rem .4rem;
   font-size:.625rem;font-weight:600;letter-spacing:.14em;line-height:1.15;
   box-shadow:0 0 0 1.5px var(--paper),0 0 0 3px var(--hot-text);
   transform:rotate(-2deg);transform-origin:left center;
   print-color-adjust:exact;-webkit-print-color-adjust:exact}
/* Our own tooltip, because the browser's waits about a second before showing
   and this one exists to answer "what is that bar?" while the pointer is still
   on it. No delay, no JavaScript; hidden from print, where nothing hovers. */
@media screen{
  td[data-tip]{position:relative}
  /* max-content up to a limit, then wrap. It was nowrap, which is right for
     "9 shows; usually 5 to 13" and hopeless for the sentence a song with no
     range bar carries: 648px of unbreakable text hung off a cell four fifths
     of the way across the table, so on every viewport narrower than about
     1,600px the end of the explanation was somewhere off the side of the page.
     Two lines of tooltip is not a problem; a tooltip you have to scroll to is.
     line-height goes back to something a second line can live in. */
  td[data-tip]::after{content:attr(data-tip);position:absolute;left:.25rem;
    bottom:calc(100% - .35rem);z-index:5;
    width:max-content;max-width:min(24rem,calc(100vw - 3rem));
    padding:.3rem .5rem;background:var(--ink);color:var(--paper);
    font-size:.75rem;letter-spacing:0;line-height:1.35;
    opacity:0;visibility:hidden;transition:opacity .09s ease-out}
  td[data-tip]:hover::after,td[data-tip]:focus-visible::after{
    opacity:1;visibility:visible}
  /* The two right-hand columns hang their tips the other way, or they run off
     the edge -- and now that the page clips rather than scrolling, running off
     the edge means the words are simply gone rather than merely awkward. */
  td.bar[data-tip]::after,td.n[data-tip]::after{left:auto;right:1.2rem}
}
/* Visually hidden, still announced. Not display:none and not visibility:
   hidden -- both remove it from the accessibility tree, which is the opposite
   of the point. The 1px-clip form is the one that survives every screen
   reader worth supporting. */
.sr{position:absolute;width:1px;height:1px;margin:-1px;padding:0;
   overflow:hidden;clip:rect(0 0 0 0);clip-path:inset(50%);white-space:nowrap;
   border:0}
.bar{padding-right:1.2rem}
/* A position, not a length. The track is the whole range a gap can sit in for
   this song; the shaded middle is where it usually sits, the hairline is its
   median, and the mark is tonight. Nothing here is scaled to the show, so a
   bustout somewhere else on the bill cannot flatten this row. */
.bar .track{display:block;position:relative;width:100%;height:14px}
/* The line the mark sits on. Faint, but a real line -- without it a mark near
   the middle had nothing to be near. */
.bar .track::before{content:"";position:absolute;left:0;right:0;top:6px;
   height:2px;background:var(--rule)}
/* No band to draw, so no scale is drawn. A dash where the mark would have
   been, at the same height as the track, says the measurement was never
   possible -- the ghost scale that used to sit here read as a bar that had
   failed to render, and it was the emptiest graphic on the most interesting
   rows. `.bare` is gone with it. */
.bar .no-range{display:block;height:14px;line-height:14px;text-align:center;
   color:var(--dim);opacity:.65;font-size:.75rem}
/* Where this song usually lands, as a block rather than a tint. The previous
   version used --track, which is a 10% alpha meant for the inside of a
   progress bar, and against paper it was not there at all. */
.bar .band{position:absolute;left:30%;right:30%;top:3px;bottom:3px;
   background:var(--band);opacity:var(--band-opacity);border-radius:1px}
.bar .mid{position:absolute;left:50%;top:1px;bottom:1px;width:2px;
   background:var(--paper);opacity:.85}
/* Tonight. Full height and full-strength ink, with a paper halo so it reads
   wherever it lands -- including on top of the median line. This is the one
   thing in the row the eye is meant to find. */
.bar .at{position:absolute;left:50%;top:0;bottom:0;width:5px;
   transform:translateX(-50%);background:var(--ink);border-radius:1px;
   box-shadow:0 0 0 2px var(--paper)}
.bar .at.late{background:var(--hot)}
.bar .at.early{background:var(--cool)}
/* Inside its own band is the ordinary case and gets no color at all -- ink,
   like the figures. Two thirds of rows land here, and coloring them would
   spend the palette on "nothing to report". */
.bar .at.usual{background:var(--ink)}
.last{font-size:.875rem;overflow-wrap:anywhere;vertical-align:top}
.last .date{white-space:nowrap}
/* Named only where the column header is not doing it -- on a wide screen the
   thead says "Last performed" and a second label would be saying it twice. The
   gap cell's own label works the same way and for the same reason. */
.last .cap,td.n .cap{display:none}
/* A hero card that is also a way down the page. The index sheet has these
   rules for cards that lead to another page; this is the same affordance for a
   card that leads to a row of this one, which is why the mark is a down arrow
   rather than the index's right one. A right arrow inside a setlist is a claim
   about the music -- see the note on td.last's label. */
""" + CARD_LINK_CSS + """a.card .lbl::after{content:" \\2193";color:var(--dim);white-space:nowrap}
/* Where you landed. A jump into the middle of a forty-row setlist puts the
   reader somewhere with nothing to say they arrived, and the row they wanted
   looks exactly like the thirty-nine around it. The way back from here is the
   browser's, which a fragment navigation genuinely does restore -- unlike a
   scroll, which is why the other jump targets on this site carry a link. */
tbody tr:target td{background:var(--hover)}
tbody tr:target td:first-child{box-shadow:inset 3px 0 0 var(--hot)}
/* The date links when we hold that show. Underlined rather than colored, so
   a column of them does not turn the right-hand side of the table orange. */
.last .date a{color:inherit;text-decoration:none;
   border-bottom:1px solid var(--rule)}
.last .date a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* Stacked on wide layouts, run together on narrow ones -- see the
   max-width block, which puts these back inline with separators. */
.last .date,.last .venue,.last .place{display:block}
.venue{color:var(--dim);font-size:.75rem;line-height:1.2rem}
.rating{margin:.45rem 0 0;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--dim)}
.rating b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:1rem;color:var(--ink);letter-spacing:0;margin-left:.15rem}
.rating span{opacity:.75}
/* A show that is still happening. Marked, not decorated: the same field
   language as the rest of the masthead, with the state in the bold half and
   the detail in the quiet one. */
.live{margin:.7rem 0 0;display:flex;flex-wrap:wrap;align-items:baseline;
   gap:.2rem .6rem;font-size:.75rem}
/* A state, not a label. It used to be 10px tracked caps in the hot ink --
   character for character the same specification as every field label, every
   table head and every badge on the page -- so the one thing worth
   interrupting for was delivered in the site's most generic voice. */
.live{margin:.8rem 0 0;padding:.6rem 0 .6rem .9rem;
   border-left:4px solid var(--hot);display:block;max-width:62ch}
.live b{display:block;font-family:'Bagnard',Georgia,serif;font-weight:400;
   font-size:1.25rem;line-height:1.2;letter-spacing:0;text-transform:none;
   color:var(--ink)}
/* :not() rather than a bigger selector on .since-you. That chip is a span
   inside .live, so this rule reached it and won on specificity -- 0-1-1 over
   the chip's 0-1-0 -- handing it color:var(--dim) on a var(--hot) background:
   1.12:1 in the light palette, 1.08:1 in the dark, which is text you cannot
   read at all. It took display:block with it, so the bar also spanned the
   column instead of hugging its own text. Beating it back with .live
   .since-you would only move the race one round on; excluding the chip here
   means the two rules cannot both apply. Same shape as the sticky-header hide
   and .backtop before it: a modifier class losing to a descendant selector.
   The chip is an <a> now and this rule can no longer reach it either way; the
   :not() stays as the guard against the next span that lands in here. */
.live span:not(.since-you){display:block;margin-top:.15rem;font-size:.8125rem;
   color:var(--dim)}
.live span b.n{display:inline;font-family:'IBM Plex Mono',ui-monospace,monospace;
   font-weight:600;font-size:.9375rem;color:var(--ink)}
/* Added since this reader last looked. --hot-text, not --hot: paper on --hot
   is 4.44:1, and this is 10px uppercase, so it wants the 4.5 floor. The
   palette already carries the darker accent for exactly this ("anything small
   takes the darker") and it lands at 5.78:1. In the dark palette the two are
   the same color, so this is a no-op there and stays at 6.63:1. */
.since-you{display:inline-block;margin-top:.35rem;font-size:.625rem;
   letter-spacing:.14em;text-transform:uppercase;color:var(--paper);
   background:var(--hot-text);padding:.15rem .4rem}
/* It is an anchor now -- the count doubles as the jump to the first new row.
   text-decoration has to be said out loud: the color above already beats the
   UA link color, so this would not have come out browser blue, but it would
   have come out underlined, and four links on this site have shipped wearing
   a default the author sheet never overrode. The ring is not set here either;
   a:focus-visible in BASE_CSS already draws it in --hot. */
a.since-you{text-decoration:none}
a.since-you:hover{text-decoration:underline}
tr.fresh td{background:var(--hover)}
tr.fresh td.song{box-shadow:inset 3px 0 0 var(--hot)}
/* Same shape as the still-coming-in notice: state in the bold half, detail in
   the quiet one, set in the reading face because it is a sentence. */
.aside-note{margin:.7rem 0 0;padding-left:.8rem;border-left:2px solid var(--rule);
   max-width:62ch}
.aside-note b{display:block;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--dim);font-weight:400}
.aside-note span{font-family:'Literata',Georgia,serif;font-size:.9375rem;
   line-height:1.5;font-variation-settings:'opsz' 14;color:var(--ink-soft)}
/* The title carries the link to the song's own page; underlining every one of
   them would stripe the table, so it colors on hover instead. */
td.n,td.song{vertical-align:baseline}
td.song a{color:inherit;text-decoration:none}
/* :not(.jc-chip), because this cell holds two links and only one of them is a
   title. This rule is 0-2-2 and the chip's own hover is 0-2-1, so without the
   exclusion this one won and painted the chip's text the colour of its own
   fill. Excluding it here rather than escalating there is deliberate: a bigger
   selector on the chip would only move the race one round on. */
td.song a:not(.jc-chip):hover{color:var(--hot-text)}
.place{color:var(--dim);font-size:.75rem;line-height:1.2rem;white-space:nowrap}
.none{color:var(--dim);font-style:italic}
/* The show's own notes: the other block of real prose on the site, and set in
   the reading face for the same reason the song pages' are. */
.notes{margin:2.2rem 0 0;padding:1rem 1.1rem;border-left:3px solid var(--rule);
       font-family:'Literata',Georgia,serif;font-size:.9375rem;line-height:1.5;
       font-variation-settings:'opsz' 14;color:var(--ink-soft);max-width:68ch}
.notes a{color:var(--hot-text)}
""" + FOOTER_BOX_CSS + FOOTER_LINK_CSS + """@media screen{
  .bar .fill{animation:grow .7s cubic-bezier(.2,.8,.3,1) both}
  @keyframes grow{from{transform:scaleX(0);transform-origin:left}}
  tr:hover td{background:var(--hover)}
  /* The whole row leads to the song page on a phone, so it should look like
     it does. Desktop keeps the title as the target -- there the pointer is
     precise and a row-wide cursor over a table of figures reads as noise. */
  @media (max-width:620px){
    tbody tr:has(td.song a){cursor:pointer}
    /* The last-performed block is its own destination once the row stacks, so
       it gets its own edge rather than reading as more of the row above it. */
    td.last:has(a){padding-left:.55rem;border-left:2px solid var(--rule)}
    /* A 2px edge was the only thing saying this block goes somewhere else than
       the rest of the row -- tap the venue expecting the song page and you get
       the previous show instead. So the label carries a mark saying the block
       is a way in.

       The mark is a north-east arrow, and the arrow it replaces is why this
       comment is long. It was "\\2192", the same right arrow the hero cards use
       for "this is a way in" -- which is fine on the index and wrong here,
       because on a show page that glyph is already spoken for. A setlist uses
       arrows to say the band ran two songs together, so a decorative one
       sitting beside a date and a venue is not merely noise, it is a claim
       about the music. Ian caught it. "\\2197" makes no such claim: it is not
       setlist notation, and it says "leaves this row" rather than "runs into
       the next one". */
    td.last:has(a) .cap::after{content:" \\2197";color:var(--dim)}
  }
}
/* Narrow viewports: the four-column table becomes a list of stacked rows.
   A hidden `bar` cell used to leave the table's last column empty -- the
   cells shifted left into the colgroup widths while the 47% `last` column
   kept its space -- which is why the rules stopped short of the right edge.
   Dropping table layout altogether fixes that and buys room for the venue
   and city, which no longer have to be hidden to make the columns fit. */
@media screen and (max-width:620px){
  table,tbody,tr,td{display:block}
  colgroup,thead{display:none}
  /* Wide enough for a comma'd four-digit gap in the Georgia fallback. */
  .typ .full{display:none}
  .typ .abbr{display:inline}
  /* minmax(0,1fr) rather than 1fr, because a 1fr track still takes
     min-width:auto and a long unbreakable run would widen it. Not the cause of
     anything observed -- the tracks measure 267 + 59 against a 338 row -- but
     the row has no business being able to grow. */
  /* 4.6rem, not 3.7. The verdict lives in this cell at every width -- one
     element rather than a visible copy and a hidden one, which is what let an
     aria-hidden end up on the copy the phone actually shows. "premature" is
     the widest word it can hold, 63px at this size, so the track is sized for
     it: 73.6px. The song column gives up 0.9rem, which it can afford; the
     alternative costs a screen reader the verdict entirely. */
  tr{display:grid;grid-template-columns:minmax(0,1fr) 4.6rem;column-gap:.7rem;
     grid-template-areas:"song gap" "meta gap";
     padding:.5rem 0;border-bottom:1px solid var(--rule-soft)}
  /* And nothing inside may refuse to break, or the track has no smaller size
     to fall back to. */
  td.song,td.last{min-width:0;overflow-wrap:anywhere}
  td{border:0;padding:0}
  td.n{grid-area:gap;padding-right:0;align-self:start;padding-top:.1rem;
       text-align:right}
  td.song{grid-area:song}
  td.last{grid-area:meta}
  td.bar{display:none}
  /* The hover tooltip, gone. It is position:absolute and white-space:nowrap,
     and it was hidden with visibility:hidden -- which still takes part in
     layout. Every report page was therefore as wide as its longest tooltip:
     497px inside a 375px viewport, so every report scrolled sideways on a
     phone, with nothing visible out there to explain why. Measured: disabling
     this one rule takes the page from 497 to exactly 375.
     No loss here, because there is no hover on a touch screen to show it. */
  td[data-tip]::after{content:none}
  /* No bar here to carry the tick, so the words do all the work. */
  .typ{font-size:.75rem;margin-top:.2rem}
  .verdict{font-size:.625rem}
  .verdict.bustout{font-size:.625rem}
  .gap{font-size:1.25rem}
  .song{font-size:1rem;line-height:1.25rem}
  .last{font-size:.75rem;line-height:1.15rem}
  .last .cap,td.n .cap{display:block;font-size:.625rem;letter-spacing:.14em;
     text-transform:uppercase;color:var(--dim);margin-bottom:.15rem}
  .last .date,.last .venue,.last .place{display:inline}
  .last .place{white-space:normal}
  /* --dim rather than --rule. A hairline color is for hairlines: at #413a30
     on #131210 this separator was invisible on the dark palette. */
  .last .venue::before,.last .place::before{content:" · ";color:var(--dim);
    opacity:.7}
  /* Same two lines, scaled down: date and tour still pair on the first one
     even at 320px, and the masthead closes up so it reads as one block rather
     than a stack of separate announcements. */
  header{padding-bottom:.55rem}
  /* Two full dates have to share one line here, and at 320px they only just
     do, so the pager gives up some tracking rather than risk pushing the page
     sideways.

     `.crumb.pager`, not `.crumb`. It was written as the latter, which was
     harmless while both strips wanted the same geometry and stopped being so
     the moment the sections strip got 44px targets on a phone: `gap:.35rem`
     out-specified the shared block's row gap, the targets in the two rows
     overlapped, and it showed up on show pages only -- four overlapping pairs
     at 390px, none anywhere else on the site. The eighth instance of one sheet
     of several quietly answering for a rule that belongs to all of them. */
  .crumb.pager{margin-bottom:.7rem;gap:.35rem;font-size:.625rem;
     letter-spacing:.14em}
  .crumb.sections{margin-bottom:.7rem}
  h1{margin-bottom:.45rem}
  /* At this width the whole thing fits on one line, so it reads better joined
     -- and a middot cannot be orphaned the way a comma was, because it only
     exists when the two parts are already side by side. */
  .where .v-name,.where .v-place{display:inline}
  /* Margin rather than spaces inside content: a leading or trailing space in
     a generated string collapses, which left "GARDEN ·NEW YORK". */
  .where .v-place::before{content:"\\00B7";color:var(--dim);
     margin:0 .45rem 0 .55rem}
  .show .date{font-size:1.25rem}
  .show .tour{font-size:.625rem;font-weight:400;letter-spacing:.14em}
  .show .sep{margin:0 .35rem}
  .where{margin-top:.2rem;font-size:.75rem;letter-spacing:0}
  /* The buttons stand twice as tall as a line of footer text, so sharing a row
     with it inflated that row and opened a gap between the two text lines.
     They get their own row down here instead. */
  .theme{order:1;flex-basis:100%}
  /* All three badges have to hold one line down to a 320px phone. */
  .links{margin-top:.95rem;gap:.3rem}
  .badge{font-size:.625rem;letter-spacing:0;padding:.3rem .45rem;gap:.3rem}
  .badge img{width:12px;height:12px}
  .card{flex:1 1 45%;padding:.65rem .55rem}
  .card:nth-child(odd){border-left:0;padding-left:0}
  .card:nth-child(n+3){border-top:1px solid var(--rule)}
  .num{font-size:1.5rem}
  .lbl{font-size:.625rem;letter-spacing:.14em}
}
/* Wide layouts have a big empty corner to the right of the wordmark, and the
   show identity is about as tall as the wordmark is, so the two balance as
   columns. The masthead keeps the strongest position, top left; the show block
   gets the hard right edge of the page rather than being tucked into a corner,
   and the hero rule under both ties them together.

   Scoped to `screen`: a printed report wants its masthead stacked, and the
   page box measures 538pt, which would fall the wrong side of this threshold
   by unit accident rather than by intent. */
@media screen and (min-width:700px){
  /* The areas name the same order the markup is in. They used to name the
     opposite one -- the markup ran venue-then-context and this grid printed
     context-then-venue -- so the page read one way to a screen reader and in
     print, and the other way to everybody looking at it above 700px. The
     markup moved rather than the grid, because context-above-venue is the
     order that was on screen and the one that puts the venue nearest the
     setlist it introduces. */
  header{display:grid;grid-template-columns:auto 1fr;column-gap:2.5rem;
         align-items:start;
         grid-template-areas:"sections sections" "pager pager"
                             "title show" "title where"}
  .crumb.sections{grid-area:sections}
  .crumb.pager{grid-area:pager}
  h1{grid-area:title;margin-bottom:0}
  .show{grid-area:show;justify-content:flex-end;text-align:right}
  .where{grid-area:where;text-align:right;margin-top:.35rem}
}
@media (prefers-reduced-motion:reduce){.bar .fill{animation:none}}
@page{size:letter;margin:14mm 13mm 12mm}
@media print{
  body{padding:0;font-size:10.5pt;background:#fff}
  .crumb,.links{display:none}
  /* rem still resolves against the 16px root here while the body drops to
     10.5pt, so these do not shrink with the column and the widest of them ran
     into the song title. Sized in points to match the page. */
  .typ{font-size:7.5pt}
  .verdict{font-size:6.5pt}
  .verdict.bustout{font-size:7pt;padding:1pt 2.5pt}
  .wrap{max-width:none}
  h1{font-size:34pt}
  h2{margin-top:16pt;break-after:avoid}
  table{break-inside:auto}
  tr{break-inside:avoid}
  thead{display:table-header-group}
  footer{break-before:avoid}
}
"""

SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{titlestate}{date} &mdash; Possum Logic</title>
<meta property="og:type" content="article">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}{ago_js}{new_rows_js}{poll}</head><body><div class="wrap">
<a class="skip" href="#main">Skip to content</a>
<div class="rule2"></div>
<header>{crumb}<h1>{date}<span class="dow">{dow}</span></h1>
<p class="show">{tour}</p>
<p class="where">{venue}</p>{rating}{aside}{live}</header>
<section class="hero" id="main" tabindex="-1">{hero}</section>
<div class="rule2"></div>
<p class="links">{links}</p>
{sections}{notes}
""" + footer_html(root="../") + """
{analytics}
</div>{row_js}</body></html>
"""


# Site favicons, fetched once and inlined as 32px PNGs. Embedded rather than
# hotlinked for the same reason the fonts hurt: a page saved out of a chat has
# no network, and a badge with a broken image looks worse than no badge.
ICON_PNET = "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAJM0lEQVR42pWXe1BU1x3HP3ef7C4Lyy6wwAYUARVQAopR4yPWRC3SpJE4SZ2k0UmtSSeTadNJJo8/OomtZhIzJm1m0hgz0zhO6jimRuMQdEtsxuIDDI8QKhUBkYcLbFgey7LL7rK//gEB8d3fzJ07c+65v+/nnvO953eOIiLC/xk+n4+Ghgbq67/nyJEjGAxR1NTVsqAlwK+YhRoFADUKjYqXsgUG/nJoPz2ubqqqzvPlsS+pr/+O4WEfyt0AjI2N4fV66e3txel0cv78eXp6eli+fAUPrl7NkWNHOfTeHl4eTScLMxHGU2pQOKH08sVsIT//XiqrqujvcKEKR7BrjDjCOjR3Eu/v76eyspKqqira2tpwuVykpqby8ccfo9PrCQaD1NfVsyhoJoPoSXEAP2M0yiCXmlwEL7YzCyM/IYN0olGPKTQxdOcROHfuHJ999hmrVq0iKyuLoSEvu955m5jYGHRBP0OePqprv+OxPjurlQQ0okwihBFO0I2fMRZjxYEBDSrCRChX3FTda74zwOjoKD6fj6ioKOrr69m5cyelJ+uIRCK8kB7kpXQD34Z97G4KsOCKg4cj9sl3FRTCRFChoEJBEAKM8RXdjJQU8vIf/3DnKdDr9ej1er44coSD+/ZTW1MLiQ+BLpmDA19QovNQYrERws2brna0AYUoFDoYpVsfIj6o8HNJwYaeMEKZ0oOnaB5/emcHWRmZdwYAqKmr5R97/8a2hNk0xnjoVGZCVDK9ygY+uHSUaLuHVrcKc0aQi0lNxNus9PYL/zrjITMUy3pJwk+Y04qHr5NDvL3tGbIyMieMepPw+/14vV60Wi0Go5Hjh4/yG3MG2ZoYfKEoiE4ACYMqlrLuaDqHG1mxwc5HvywgLS2EzWajrGyQitMDJEai+Jwe2vHRpfERHoW3du7gq9LjPP74Yzd6wOPxsGPHDo4ePUpSUhJZWVn0dV5l56xlhMeC/PSf/8atz0eGW5hla6SkWGHTJgvzcqxotdrJPBcueHjvjcv8t6WPKFuElNQ0MmaqSb3Hx4ULag4fvkpv73UmjESEXbt2sX37m4yMjEwmMxiNzE9JIxKJUNPpQoWK5Us1/PZ30axbl47BoAfUgExc4yGDEa784CYmDqzWhIk+ABHOnm1m79726QB1dXWUlJRw+fLlO/oiOlqDw2Hg/vtDLF2WTE5eLAW5FoxGwzQIUE2KTg8hEAhNB3jxxRd5//330ev1iAjBYPCul+eUmbBovoVVSw2seSSF9PRYjEbttK8WEfz+EDqdFo1GRXPLFZCJaG1tlcLCQlEURUwmk+h0OgFFUlI0sn69RaxWs1wzxre8tGrEbtfIxo162bs3Xaqq8sXjKRCRdeL3Pyivvx4tBw9miMg6OXk4RyYBysvLxWaziVqtFq1WI4DMmGGWsrICGRxcLps3JwoodwUBiEaDGI3IjBnImjVqeemlGXLggF2WLFFk2TKzePofEBksmgJwOp0SFxc3mcBkQj74IFFE1opIkZSW5ktcnPauxDMyVPLuu3bZv98uOTkqASQ3F8nORkwmrcTGKnLqVKqIXAPQ2dkpa9asmUyyerUivb0LRGS9iKyXpqZ7paDgzuKJiRo5cGB8iEXWyUcfZUpCgiLHjlnk7Nn58sILZlEU5JVXZolIkfxoURwOB7t372bhwkKio7U880wWCQnxE+4VUlMNpKZG3daIigJPP53CE09kAgqgZsUKM+npQn+/gSVLUnn11TkUF0dx6VI/o6Mjk/8IAOXlX+NyXWXTJiMbN6Zd8wsJUVFx2O3JtwWw29U89VQCijKV1uEYw2qF6upoQEhJSWDbNgvunn6aLvZNB6ioOINOd5Xnn78HvV57g0Bm5iiaW1aPcfHcXOs164BgMBhRq/VcvTq1sM2ZY+GHbg1tTcoUwNmzZzl3rpKly2zk5SXcVGLpUjVm883li1fE8/utuWg06mntOp0Ng8HK8LCbwKgHAJstFa0pgarv2qcAWltbcfd1MDffgKJcv5qNf83ChRls3hyPxTI1DHPnwnPP2fnzJ4kkz9Fd6wh6e/u5dKmTwUE/oSGF0ODEXlEtmM0BGhoGp6qhSqWCSIQUy9gt59hoNPDGG/MoKhqmry+MSiXk5MC83DgU1Y/QCqDwn9peXnutnjZXkOZmWLvcQJR+/FkgEKKjI8xA8LpyrFJBdPTtbCbExhpYu9YwITTV/qN4MOinpdXNXz9ppqLSjFqjwT/iptPjp6W7m7mxOpzOJtxuL+0d1wEEAlBdo+eJX0QYt4fcFGL6fbKW0tJyhQ8/dFFePkRHJywsXElaWiptbW1cuFDDr7deISnpB6qq/KjVMTzy8KobNyT7/t5NfLKOLZvisSfF3kLs+lBx8WIfzz7bTnu7HbM5k4xZahyOFGJiYpg/fz5Wq5WamnpOn76MSJiSkofYs2fPVDXs6Ohg69atOJ1O9HoNhYVaiotjWbvWQmamA4Mhgk6nu6buRxgdDeHzqamp6WTXrkEqKoZ59NGfkZiYiIhw7V5HRBgZGaGnp4fGxkbC4TCFhYXTy7HL5WLLli04nc4Jt4LNpmP2bB0FBUFyclKwWm1otVrc7h6+/babM2fMBAJuZs4UGhoUZsxYzOLFi1CpVJMAiqLQ09NDbW0tGRkZxMfH4/V6uXz58o1bso6ODsrKyti+fTtdXV3k5Wl48skxBgZ0NFyA3kEzowMxiHjIzPSxaFEs993nID8fPv20i7fe8uFwzCEvLw+LxYKijJvV6/Vy5swZOjs7MZvN2O129Hr9rc8FTqeTQ4c+5+TJUh54wE1xcTqJiQqO1GgsMTYUJYJeH8FoVANaQMHlcrFhw0UqK31YLBays7PJysqaBAmFQjQ3N1NdXU1fXx8FBQW3P5iMjY1x/PgJSku/oqamApFWrHEhkpLjyc0dJTtbGBpS8HgidHVF0dIS5PvvzRQVPYparWbfvn1EIhHi4+NJS0sjMTERk8nEwMAA33zzDXl5eXd3OA0Gg3i9Xqqr6zh+/AQulwu9Pkwk4mNgYJjY2DhMJhuzZ89j1arl5OXlAXDq1ClKS0upqKigq6sLn8+HyWTCaDQiIqxcufLuAG4VIyN+hoaGSEhIQK1W3bJfS0sLzc3N9PX1EQgEAEhOTmbJkiX8Dy6oalTSw0WAAAAAAElFTkSuQmCC"
# phish.in's mark ships around half-transparent -- a mean alpha of 130 where
# phish.net's is fully opaque -- which reads as a gray smudge on cream and as
# nothing at all on near-black, whichever way it is inverted. Alpha is the one
# thing a CSS filter cannot raise, so the shape is made opaque here instead.
ICON_PIN = "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAACAUlEQVR42s2Xz2djURTHP0kqPMIwlBKGUoZQwlRWIausQukopaWmsuowZgyl/SO67X8xs+i2225a7bYMQyndtJTwCCFeN9/HdZv77n3pq9cvR17uPe/8vOfc86BkVIznGtAAFg1qAJH2psAYGAGPwD3wpLVC8BHoAkkgfQM+A/XXKu4AmzkU27QNLCtSIajbRicF0KGM8KEBNEVRkQakKXFFoQmsW/zrSmGwggOgDwwzeNry0kQEbDj4f+MQMpix3jWE9hwCh/LW9HzL49gLJasZ3qVY9kQhxYYvslUrXGOF2cYP1XyKGPjqyHck6gB/fafSNqAHHM/gO1PzMUupkSF3BbgI7QMhB9BGK4N3oAMbIrdFYHnZGHiqJUR5Ry3ey9i18tsqqG/sqwOz72E0O1y7wMaVAEkNuAIeFNZZ+C+v+8Cft7iSV4r2Kg9V0zyUOZAkZRpQLXskK9uAI15Zx90iDuE82AFOA/h++RgWHOt7uv2awImxvgucA7fGtZyF63kNuNbtVwfW1LNjYyQPze94XgNupRDgLuP9OGNv5Nl3VsH3kBeFR6XFZcCT5OUy4CbHYRxl5PlejlzmGUi2raHSh/Rz7osxBxxo5F7S/gdHuQ6BfgX4qVD+U75HwGSO0qynA4Yw0fekaWhkzJ4xMK0An8Qc63fyRl2vZv2f8h7wDEQBdexwLq8GAAAAAElFTkSuQmCC"
ICON_FOUL = "iVBORw0KGgoAAAANSUhEUgAAACAAAAAgCAYAAABzenr0AAAC7UlEQVR42u2Xz2tcVRTHP+e+Nz+a2MTa4Ewy0zSpq7ZiFwWhCEIRoxWULhztdBItRbKwW3fdduHfUBDFYIM/diq6cS2KoNAWwSyqTjLMpLVEW9PJzLv36yIabcvUZGZUhJztvfe8zz3nnvM9D7Zt27q0y6WD6dqLo/t79eO6Pbgrvv6qi6n0ChB3c+jq6ZGdfs3tBQ3+VHlgaLU10E7HraHc/HLjHwMQWKOcO+qJcoH4CwhDIN8meyyV1jWv1BHg3FYBbLMbGy+MHQ8Rz4I1cfKGG4TggYvIhkETmXT6tV1vfb/Stwg0KuOPBZIpF5Kvvdkxk9apxcAf6IYdwEkK0FxrTwHv9QXgyqmJrK21SxjDuMxuk0+tZ+LO1ChCLoIgRyj2rQqySfu5gHZuxZlwe+ozucG7IlkuHKmVi9ObArj2UrFQr4yedcGPb/U2QmlH/Iz+8rbqM7lJmZ1wCo83pguH7gmg2cOpJPEvI5sMcpNdFbbXU8snR6c2fPr4aUkxDieFE9VScUdHgKutH3dj0UO9NJYgLDj3qMA0eziFNPHnavRgKq0nOgIkSfp0X/p00D5KxezSzfpBYOSO1UMdAeIQdvRNLLJt5wjRXe/ElHQEaGfsvBS+6/Xbhi0w11hNx1EdY+224MC3HQEKb9aqKHwUgvmeFE66YaCRtxeXTNrojGb6OTL/2T3LcHS+ftlMK13dXCTAApH7ZCPkkRYAFGhK9lV+rvHr33dCs0+Rnse4CQxtnsBCfn7p9dty7t2HjjCcRO6D4juLi5sWo5WZvZPNVhhUlJxxFvsgP4AQWNNMGczZ72IEuAgFefi8cKH2Rl9a8f1zP1zJv1u95MwuAjhjtcPWWxJVgNh0ve9yrBJR1e3ZT5ZbUcvPOuw+M9pgERYyJt1wRtXLHs5fqL3S94HE3sdD9RLA8snCvBfTgo9BRw3yMvuyZXwD/pd/bRhdV7jxJ+uVsfONcvGR/2QqVomoUR47vv1/sG3/e/sNrEkrwQ1sbIcAAAAASUVORK5CYII="

# Last field flags an icon that is solid black on transparency, which needs
# inverting to survive the dark palette.
SHOW_LINKS = (
    ("phish.net", "https://phish.net/setlist/?d=%s", ICON_PNET, False),
    ("phish.in", "https://phish.in/%s", ICON_PIN, True),
    ("fouldomain", "https://fouldomain.com/shows/%s", ICON_FOUL, False),
)


def _badge(label, url, icon, flip):
    """One outbound chip, wearing the favicon of wherever it lands.

    The one copy of this markup. Show pages and song pages carry the same row
    of chips and built it from two copies until 2026-07-31, which is the shape
    that has cost this project five bugs elsewhere -- and the two had already
    drifted, in that neither escaped the href but only one was interpolating
    anything an escape would matter to. Escaped here, once.
    """
    return ("<a class='badge' href='%s' target='_blank' rel='noopener noreferrer'>"
            "<img class='%s' src='data:image/png;base64,%s' alt='' "
            "width='13' height='13'><span>%s</span></a>"
            % (html.escape(url, quote=True), "flip" if flip else "", icon, label))


def _show_links(date, on_phishin=None):
    """Badge links out to the sites that hold the rest of the story.

    phish.in only appears once they actually have the show. They post audio a
    while after the night, so the page most likely to be shared -- tonight's,
    while it is being played -- was the one guaranteed to link to a 404. When
    the catalog has not been fetched the link is shown as before, because a
    missing local file is not evidence of a missing recording.
    """
    return "".join(
        _badge(label, url % date, icon, flip)
        for label, url, icon, flip in SHOW_LINKS
        if label != "phish.in" or on_phishin is None or date in on_phishin)


# Below this many prior performances a song has no meaningful "typical", so it
# gets numbers but no verdict. A song played four times cannot be overdue.
MIN_HISTORY = 8

# At or below this many countable performances a song page stops being a list
# and becomes a statement, and the apparatus for reading a list is dropped:
# search, sort, era chips and the "n of n" counter. 134 of 589 songs are played
# exactly once, and on those the tools bar and three "n/a" cards were 367px of
# chrome on a phone in front of a single 257px row -- a search field over one
# searchable thing, a four-way sort that cannot reorder anything, and one era
# chip anchoring to the row directly beneath it.
#
# A constant rather than a literal because the line is Ian's to move; raising
# it is this one number. Every branch below tests `sparse`, never a count.
#
# Moved to 2 on 2026-07-30, on his call. It holds up on its own terms: a
# two-performance song has one interval, so the three gap cards printed the
# same figure three times -- Baby Lemonade read 1,312 / 1,312 / 1,312 across
# "median, last 10 years", "median, all-time" and "longest gap" -- and a
# four-way sort over two rows reorders nothing a reader cannot already see.
# 193 songs of 589.
SPARSE_HISTORY = 2

# The "typical" gap is measured over this many years before the show, never
# over all of history. Forty years of a working band is several different bands:
# the 1990s dominate any all-time figure, when they played far more shows a year
# out of a smaller catalog, so all-time gaps are much shorter and 59% of this
# archive came out overdue -- a word that means nothing if it fits three songs
# in five.
#
# Counting performances instead of years does not fix it, because a window of
# 20 performances is two years for a staple and twenty-four for a rarity: Kung's
# last 20 reach back to 1995, and every one of Big Ball Jam's is inside 1994.
# Their medians are true statements about a band that no longer exists. Bounding
# by time means a song has to have been in rotation lately to be judged at all.
RECENT_YEARS = 10

# Gaps outside the middle 70% of that window get a verdict. Over the 2026 tour
# quartiles called 37% of songs overdue, too many to carry weight; this yields
# 13% premature, 67% expected, 20% overdue, with 9% of songs unrated for want of
# recent performances -- which is the honest answer for a bustout.
BAND = (.15, .85)

# ...and the middle 70% is *measured* on a log scale, which is the whole of what
# `gap_band` does differently from reading two percentiles off the list. The band
# has to be earned rather than nominal: it says "usually", so it should contain
# the next gap about 70% of the time. Replaying all 32,605 rateable performances
# from the archive -- band built from prior gaps only, then checked against the
# gap that actually followed -- showed the percentile band did not, and missed in
# a pattern:
#
#   median gap    0-4    4-7   7-11  11-20  20-40    40+
#   percentiles   76%    70%    67%    63%    53%    44%
#   log scale     70%    69%    68%    67%    61%    49%
#
# Rare songs were the badly served ones, and note the direction: their bands
# were too *narrow*, landing inside barely half the time. Ian's read of a wild
# Esther row was right about the row and inverted about the cause -- the wide
# band belongs to songs whose spread is large relative to their own median,
# which is nearly independent of how rare they are. Scaling the width by rarity
# would have tightened the group already missing most often.
#
# Percentiles are not wrong here so much as the wrong shape. Two gaps and a
# straight line between them treats 5-to-8 and 68-to-71 as the same distance,
# and for a quantity that can be 5 or 112 but never negative, they are not: the
# honest unit is a ratio. Ordinary mean +/- SD is worse than either -- it covers
# 78% where it aims for 68% and puts the low end at or below zero on 38% of
# rows (Esther's is -0.5). A median-and-IQR version in log space resists
# outliers but undercovers at 62%, so it is not that either.
#
# K is the z-score matching BAND[1], so "the middle 70%" stays literally what is
# being computed rather than a leftover phrase. Overdue lands at 21.7% against
# the percentile band's 21.4%, which is what keeps the tuning note above intact;
# premature rises from 6.5% to 9.3%, nearer the 15% it always claimed.
BAND_K = statistics.NormalDist().inv_cdf(BAND[1])

# Ian, reading the live list: "the songs we *expect* to hear, but that haven't
# been played in a bit longer than we expect… I'm expecting due songs. I'm not
# expecting overdue songs." Two conditions come out of that, and measuring
# against the songs he named showed both are load-bearing.
#
# ONE: the band has to play it often enough to expect on a given night. His
# phrasing was "median gaps of about 10-20". Without this, Fuck Your Face
# qualifies -- gone 78 shows against a typical gap of 28.5, so only 2.7x late,
# but a song you wait 28 shows for even when it is on time is not one you are
# expecting tonight.
DUE_CADENCE = 20
#
# TWO: it has to be late, but not wildly so. Measured against the song's own
# *median* rather than the top of its usual range, which is what made the earlier
# version wrong: Mr. Completely sat 1.8x above that edge and looked mildly late,
# while being gone 98 shows against a typical gap of 15 -- 6.5x. The upper edge
# is pulled out by a song's few worst gaps and is the right gate for "is it late
# at all"; it is the wrong scale for "how late". (The 1.8x was measured when the
# edge was the 85th percentile of the gap list; `gap_band` computes it
# differently now, and the reasoning is about which figure to use, not which
# estimator produced it.)
#
# Every song Ian named lands between 1.8x and 3.2x its median: Golden Age 1.8,
# Hey Stranger 2.0, Kill Devil Falls 2.2, A Life Beyond The Dream 2.2, Martian
# Monster 2.4, 46 Days 2.5, Twist 3.2. Every song he pushed back on is well
# clear of it -- I Never Needed You Like This Before at 12.9x, Death Don't Hurt
# Very Long at 16.9x. The line sits above his examples and far below theirs.
DUE_MULTIPLE = 3.5

# A song out of rotation and gone this long is a bustout rather than an
# unrateable blank. It also has to have been played MIN_HISTORY times at some
# point: Sightless Escape at four plays ever, or Cream at one, are rare new
# songs, and calling their return a bustout would be nonsense. 100 sits where
# phish.net's own setlist notes use the word -- they called Kung at 258 and
# Sparks at 357 bustouts on 2026-07-24, and did not use it for Weigh at 88.
BUSTOUT_GAP = 100

# Above this many performances, a song that goes quiet was in rotation and left
# it. Below it, there was never a rotation to leave -- which is a different fact
# and was being published under the same word. Ian, reading the dormant page:
# "Dormancy implies that it was once not dormant, but many songs that get played
# once will never be played again."
#
# He is right, and the archive scores it. Every silence of BUSTOUT_GAP or more
# in the whole archive (774 of them), grouped by how many times the song had
# been played when it fell quiet, against whether it was ever played again:
#
#     1 play  28%   3 plays 62%   5-7  66%   16-40  85%
#     2 plays 33%   4 plays 68%   8-15 70%   41+    93%
#
# Conditioned on silences that already reached 300 shows -- which is where this
# page lives, its median row being gone 490 -- the same three bands read 20% /
# 43% / 75%. A one-play song is the only kind that is likelier to stay gone than
# to come back, so "dormant" was the one word it could not carry.
#
# Eight is MIN_HISTORY's value and not its meaning: that one counts *recent
# gaps* and gates a verdict, this one counts *plays ever* and picks a noun. They
# are related enough to share a number and separate enough that tuning one must
# not silently move the other, which is why this is its own constant.
#
# Raw plays beat every cleverer rule tried against the same outcome -- plays
# inside any 50- or 100- or 200-show window, and the span from first to last.
# Span was the worst of the eleven (34 points of separation against 49): whether
# a song was ever in rotation is answered by how many times they played it, not
# by how long they had it lying around.
ROTATION_PLAYS = 8


# And below this many, the song never got going at all. Ian, on the first cut:
# "We can't call two a 'one shot' ... but for most intents and purposes, they
# should probably be grouped with the one shots."
#
# The archive agrees, and by more than it agreed with the old line. Splitting
# 1 / 2-7 / 8+ the three groups ever came back 28% / 55% / 84%; splitting
# 1-2 / 3-7 / 8+ they come back 30% / 65% / 84%. Merging widens the bottom
# boundary from 27 points to 35 and costs nothing at the top -- a song played
# twice and then dropped is, on the evidence, the same object as a song played
# once and dropped.
FEW_PLAYS = 2

# Ian also asked whether the *spacing* of those plays separates "they did a bit
# for a minute and dropped it" from "a one-shot revived years later". It does,
# but not where he expected and not cleanly enough to draw a line:
#
#   - There are no two clusters to find. Shows-per-play across every song that
#     fell quiet at 2-7 plays is one hump with a long right tail; the 48
#     two-play songs on the page run 8 / 12 / 8 / 8 / 12 across the spacing
#     buckets. Any cut here would be a number this file invented.
#   - Among the 1-2 group it barely moves: clustered 36%, scattered 27%. They
#     are not coming back either way, which is the argument for merging them
#     rather than splitting them further.
#   - Among 3-7 it moves a lot: clustered (<=200 shows per play) 70%, scattered
#     38%. That is the real finding, and it belongs to the rarities.
#
# So it is described rather than modeled -- and the page was already printing
# it. The span on every row reads "2009" for a song played twice three shows
# apart and "1992-2021" for one played twice 1,308 apart. 13 of the 48 print a
# single year. Nothing pointed a reader at that column; the blurbs now do.

# Every English word that spells out FEW_PLAYS, in one table beside it. It was
# three loose strings for about an hour -- a section title, a song-page badge,
# and a phrase on the method page -- and none of them would have failed if the
# constant above moved: a FEW_PLAYS of 3 left a three-play song reading "played
# twice", quietly and on 174 pages. Ian's instinct, and it is the right one:
# "That way it should be noticed if ever it gets changed."
#
# Noticed is the weaker half. The title and the phrase are *built* from this
# table below, so they cannot fall out of step, and the guard under it turns
# the one case the table cannot cover into a build failure rather than wrong
# prose. Nothing here is a threshold -- move FEW_PLAYS, not these.
#
# Named rather than positional, because it was a three-tuple for one revision
# and dropping the unused field left `FEW_NAMES[plays][2]` reading off the end
# of a two-tuple. `.badge` cannot rot that way, and it says at every call site
# which of the two words is wanted.
FewName = collections.namedtuple("FewName", "times badge")
FEW_NAMES = {
    1: FewName("once", "one-off"),
    2: FewName("twice", "played twice"),
    3: FewName("three times", "played three times"),
    4: FewName("four times", "played four times"),
}

if FEW_PLAYS < 1 or FEW_PLAYS > max(FEW_NAMES):
    raise ValueError(
        "FEW_PLAYS is %d but FEW_NAMES only spells 1..%d. Add the words for "
        "every count up to the new value -- the section title, the song-page "
        "badge and the method page are all built from them, and none of the "
        "three can say a number this table does not hold."
        % (FEW_PLAYS, max(FEW_NAMES)))


def _join_clauses(parts, conj):
    """a / a <conj> b / a, b <conj> c -- one comma-list, written once.

    Two callers want this and they differ only in the conjunction: the heading
    is "once or twice", the tally under it is "126 played once and 48 played
    twice". Both grow a clause if FEW_PLAYS does, and neither should be the
    place that forgets to.
    """
    if not parts:
        return ""
    if len(parts) == 1:
        return parts[0]
    return "%s %s %s" % (", ".join(parts[:-1]), conj, parts[-1])


def few_phrase():
    """"once or twice" -- how often, for every count FEW_PLAYS covers.

    Built rather than written out so the heading, the badge and the two prose
    pages cannot disagree with the constant or with each other.
    """
    return _join_clauses([FEW_NAMES[n].times for n in range(1, FEW_PLAYS + 1)],
                         "or")


#: "Once or twice" -- the section heading, and the only name that fits a group
#: holding more than one play count.
#:
#: It read "One or two nights" first, which Ian caught: "I'm not sure where you
#: picked up the 'nights' lexicon. While it's true that most shows are at night,
#: this seems over-specific." He is right, and it was a word this site does not
#: otherwise use about its own subject -- the unit here is a *show*, counted as
#: such everywhere from BUSTOUT_GAP to shows_since, and a matinee or a festival
#: afternoon is no less one. The register was already sitting on the page: the
#: column these rows are counted in is headed "Times played". So the heading
#: says how many times, and nothing about when.
FEW_TITLE = few_phrase().capitalize()
#: The same fact inside a sentence, for running prose. One string, two cases:
#: the heading only differs by its capital.
FEW_TIMES = few_phrase()


def gap_band(recent):
    """Where this song's gaps usually land -- the one definition of "usually".

    -> (low, high), or (None, None) with too little history to say.

    Measured multiplicatively: the spread of log gaps, back-exponentiated, so
    the band is a ratio around the song's typical gap rather than a fixed number
    of shows either side of it. See the note on BAND_K for why, and for what the
    percentile version got wrong. The +1 is so a gap of 0 has a logarithm -- You
    Enjoy Myself has one, two shows in a row at Dick's.

    Shared by all four callers on purpose. The report row, the song page figure,
    that page's `data-high` and the due page each read two percentiles off the
    list themselves, which is four chances to disagree about what "usually"
    means -- and this file has already shipped that bug twice, once when the
    song page and its preview card computed longest-gap differently, and once
    when a card index and the published images disagreed about being current.
    """
    if len(recent) < MIN_HISTORY:
        return None, None
    logs = [math.log(g + 1) for g in recent]
    mid = statistics.mean(logs)
    spread = statistics.stdev(logs) if len(logs) > 1 else 0.0
    return (math.exp(mid - BAND_K * spread) - 1,
            math.exp(mid + BAND_K * spread) - 1)


# A break this size, above the median, is taken to separate two behaviors
# rather than to mark one long gap: the song's rotation, and the stretches it
# spent off the list entirely. Esther's recent gaps are 5 8 12 13 14 16 19 20 26
# 29 68 76 112 -- nine of one thing and three of another, and 29 -> 68 is the
# 2.3x that says so.
AWAY_JUMP = 2.0


def layoff_break(recent):
    """The gaps that are an absence rather than a longer wait, if any.

    -> the sorted layoff gaps, or [] where the record is one behavior.

    A band is a single range and cannot say "either a fortnight or two years",
    which is exactly what a song like Esther does. Rather than average the two
    into a range describing neither, the band keeps measuring the whole record
    and the row says the second thing in words.

    Four conditions, and each one is turning something down. A break of at least
    AWAY_JUMP, or there is only one behavior here. At least two gaps beyond it,
    because one is an outlier and naming it as a habit overstates it -- Mr.
    Completely's single 380 is its longest gap, which its own page already says.
    No more than a third of the record, or the "absences" are the behavior. And
    the break has to sit at twice the median at least, so this is a song that
    goes away rather than one that is merely uneven.

    Fires on 10.8% of rateable performances and 9 of the 214 songs rateable
    today, all nine of them visibly two clusters: Axilla 3-36 then 81 and 82,
    Contact 4-41 then 95 and 95, The Sloth 10-45 then 97 and 98.
    """
    if len(recent) < MIN_HISTORY:
        return []
    mid = _median(recent)
    ordered = sorted(recent)
    best = ()
    for i in range(len(ordered) - 1):
        if ordered[i] >= mid and ordered[i] > 0:
            best = max(best, (ordered[i + 1] / ordered[i], i + 1))
    if not best or best[0] < AWAY_JUMP:
        return []
    away = ordered[best[1]:]
    if len(away) < 2 or len(away) > len(recent) / 3 or not mid:
        return []
    return away if away[0] >= 2 * mid else []


def _years_before(iso, years):
    d = datetime.date.fromisoformat(iso)
    try:
        return d.replace(year=d.year - years).isoformat()
    except ValueError:                      # 29 February
        return d.replace(year=d.year - years, day=28).isoformat()


def recent_cutoff(counting, fallback=None):
    """Where the ten-year window starts for anything said about a song *now*.

    Anchored to the newest show the archive counts, so every song is judged
    over the same ten years. It used to be anchored to each song's own last
    performance, and a window that travels with the song is a window that can
    end long before today: Anything But Me was last played in 2011 and was
    measured on 2001-2011, where it had eleven gaps and a tidy norm of 21.5.
    So a song gone 564 shows read as a song running twenty-six times late, and
    led a page whose subject is songs that are merely due. It has none at all
    inside the real ten years, which is the honest answer and the one that
    keeps it off that page.

    `fallback` is used only when there is no calendar to anchor to -- a
    render with `counting` unset, which is the single-report path rather than
    the site build. Deliberately not a silent fallback to the old behavior
    for the ordinary case: that is the shape of bug this file keeps repeating.

    Note this is *not* the anchor a show page wants. A verdict printed on a
    2011 show has to be judged by the ten years before 2011, and `_classify`
    takes that date for exactly that reason.
    """
    latest = max(counting) if counting else fallback
    return _years_before(latest, RECENT_YEARS) if latest else ""


def _classify(gap, prior, on_date, plays=None, played=None):
    """Where this gap sits against how the song has behaved lately.

    `prior` is the song's performances before this one, each a row with a
    showdate and a gap. Only those within RECENT_YEARS of the show count, so
    the answer describes the rotation the band was in at the time rather than
    the one they were in decades earlier -- see the note on that constant.

    Percentiles rather than mean and standard deviation, because gap
    distributions are savagely right-skewed: a rotation staple with a median of
    6 carries a handful of 200s, and a standard deviation over that would call
    almost anything expected.

    A song without enough recent performances to judge gets no verdict, because
    there is no current norm to be early or late against. If it has also been
    gone a long time, that is a bustout, which is the more useful thing to say
    about it anyway.

    `played` is every performance before this one, the debut included, and is
    only counted. `prior` cannot stand in for it: it starts after the debut,
    because a debut has no gap, so counting it as plays printed "0 in 10 yr"
    under the second performance of every song -- Cream's, on 2026-07-12,
    seventeen shows after a debut well inside the window -- and one short
    under every song whose debut was in it.
    """
    cutoff = _years_before(on_date, RECENT_YEARS)
    recent = [_gap(h) for h in prior if h.get("showdate", "") >= cutoff]
    recent = [g for g in recent if g is not None]
    n_played = (len(recent) if played is None else
                sum(1 for h in played if h.get("showdate", "") >= cutoff))
    stats = {"plays": plays, "recent_plays": n_played, "gap_median": None,
             "gap_mean": None, "gap_low": None, "gap_high": None,
             "gap_away": None, "verdict": None}
    if len(recent) >= MIN_HISTORY:
        stats["gap_median"] = _median(recent)
        stats["gap_mean"] = sum(recent) / len(recent)
        stats["gap_low"], stats["gap_high"] = gap_band(recent)
        # Carried on the row because the renderer sees the row and not the
        # history it came from -- as [how many, from what], the two numbers the
        # sentence needs. Null rather than absent on the rows with nothing to
        # say, like gap_low and gap_mean beside it: the renderers read these by
        # subscript because the report shape has always guaranteed them, which
        # is the reason prev_date is assigned unconditionally further down.
        # The third figure is how many gaps that is out of, which is not
        # recent_plays: that counts performances, and a debut is one without
        # a gap.
        away = layoff_break(recent)
        if away:
            stats["gap_away"] = [len(away), away[0], len(recent)]
        if gap is not None:
            stats["verdict"] = (
                "premature" if gap < stats["gap_low"] else
                "overdue" if gap > stats["gap_high"] else "expected")
    elif gap is not None and gap >= BUSTOUT_GAP:
        # The gap alone decides it. This used also to require more than
        # MIN_HISTORY performances, meaning to screen out a new song whose
        # return is not a bustout because it never went anywhere -- but a gap
        # counts shows, so a gap of 485 already proves the song has been in the
        # catalog for 485 shows. Nothing new can reach the threshold: Cream's
        # largest gap ever is 17. All the test actually screened out was songs
        # that are *rare*, which is the whole population the word is for --
        # Back in the U.S.S.R., four plays between 1994 and 2026, returning
        # after 485 shows, was being called nothing at all.
        stats["verdict"] = "bustout"
    return stats


def _median(vals):
    ordered = sorted(vals)
    n = len(ordered)
    if not n:
        return None
    mid = n // 2
    return ordered[mid] if n % 2 else (ordered[mid - 1] + ordered[mid]) / 2


def _stat(value):
    """Thousands separators, and no trailing .0 on whole numbers."""
    if value is None:
        return "n/a"
    return ("{:,}".format(int(value)) if float(value).is_integer()
            else "{:,.1f}".format(value))


BAR_SCALES = ("linear", "sqrt", "log")


def _band_pos(gap, low, high):
    """Where this gap sits against the song's own band, as 0-100 across a track.

    The old bar drew each gap as a fraction of the longest gap in the show,
    which works until a bustout is in the room -- and on 168 of 690 shows the
    longest gap is at least twenty times the median, so about 95% of that
    night's bars collapse into one flat nub a couple of pixels long. A scale
    that one row can destroy for every other row is not a scale.

    So the bar stops measuring magnitude, which the printed number already
    gives exactly, and measures the only thing the number cannot: whether this
    was early or late *for this song*. Every row gets its own scale, which is
    the point -- Tweezer's 9 and Cold as Ice's 1,468 are both ordinary against
    their own histories, and both should read that way.

    The band [low, high] occupies the middle 40% of the track, so a gap inside
    it lands in the middle and one outside it visibly leaves. Beyond the band
    the mapping saturates rather than running off: at three times the high mark
    it reaches the end and stays there, because past a point "very late" is the
    whole of the message and a longer bar does not add to it.
    """
    if high is None or low is None or high <= 0:
        return None
    if gap <= low:
        return 30.0 * (gap / low) if low > 0 else 0.0
    if gap <= high:
        return 30.0 + 40.0 * (gap - low) / (high - low) if high > low else 50.0
    over = (gap - high) / (high * 2.0)
    return 70.0 + 30.0 * min(1.0, over)


def _bar_pct(gap, biggest, scale="linear"):
    """Bar length as a percentage of the longest gap in the show.

    Linear by default, because the bar's only job is comparing magnitudes.
    A log scale badly flatters mid-range values: against a 1,170 maximum it
    draws 531 at 89% of full width when the value is 45% of it, which makes
    the bars look arbitrary next to the numbers printed right beside them.
    """
    if not biggest or not gap:
        return 0.0
    if scale == "log":
        return math.log10(gap + 1) / math.log10(biggest + 1) * 100
    if scale == "sqrt":
        return math.sqrt(gap) / math.sqrt(biggest) * 100
    return gap / biggest * 100


def era_ordinal(dates, date):
    """"nth show of 3.0", or None where that cannot be said honestly.

    An absolute ordinal cannot: phish.net offers three defensible totals for
    how many shows Phish has played -- 2,239 rows, 2,114 that count toward
    statistics, 2,106 distinct dates -- and 1983-10-30, the show everyone calls
    their first, is flagged exclude_from_stats, so a stats-based count declares
    the second show to be number one. Any figure we printed would be
    confidently wrong against the one the reader already has.

    Inside an era it can, for three of the four. Six dates carry more than one
    counting show and all six are in 1.0, the earliest being 1985-02-25 -- so
    the drift is not confined to six shows, it is inherited by every show after
    them, roughly 1,350 of 1,361. 2.0, 3.0 and 4.0 are one show per date
    throughout, so the count is exact rather than approximately right.
    """
    label = era(date)
    if label == ERAS[0][0]:
        return None
    start = next((s for l, s, _ in ERAS if l == label), None)
    if not start:
        return None
    n = sum(1 for d in dates if start <= d <= date)
    return (n, label) if n else None


def _ordinal(n):
    """1 -> 1st. 11, 12 and 13 are the ones that break the naive rule."""
    suffix = "th" if 11 <= n % 100 <= 13 else {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")
    return "{:,}{}".format(n, suffix)


def render_html(report, bar_scale="linear", index_href=None,
                prev_date=None, next_date=None, songs=(), card=None,
                archived_show=(), sheet="../%s/%s" % (STATIC_DIR, SITE_SHEET), calendar=(),
                on_phishin=None, unlinkable_tours=()):
    # Whether this is a show at all. A soundcheck's songs are real and its
    # gaps are phish.net's, but nothing here feeds the rest of the site, and a
    # count of bustouts is a verdict wearing a number's clothes.
    counts = not calendar or report["date"] in set(calendar)
    allg = [s["gap"] for s in report["songs"] if s["gap"] is not None]
    biggest = max(allg) if allg else 0
    avg = _stat(sum(allg) / len(allg)) if allg else "n/a"
    med = _stat(_median(allg))
    longest = _stat(biggest) if allg else "n/a"
    show_last = any(s["prev_date"] for s in report["songs"])

    # An id per song row, so a row can be linked to at all. Nothing on a show
    # page could be until now -- which is why the LONGEST GAP card named a
    # figure sitting a few hundred pixels down its own page and offered no way
    # to it. The slug alone is not enough to be unique: a song can turn up twice
    # in a night (Mike's Song, or a reprise), and two elements with the same id
    # is not a near-miss, it is a document where half the links go to the wrong
    # place. Repeats are numbered.
    row_ids, seen_slugs = [], {}
    for s in report["songs"]:
        n = seen_slugs[s["slug"]] = seen_slugs.get(s["slug"], 0) + 1
        row_ids.append(s["slug"] if n == 1 else "%s-%d" % (s["slug"], n))
    # Which row the longest gap is actually on. First one wins a tie, which is
    # the one a reader scanning down the page reaches first.
    longest_id = None
    if allg:
        longest_id = next(rid for rid, s in zip(row_ids, report["songs"])
                          if s["gap"] == biggest)

    hero = hero_html([
        c for c in (
            (len(report["songs"]), "Songs Played", "", None),
            # The one href on this page that is an anchor rather than a URL.
            # It was written as "#%s" inside the copy of the builder that used
            # to live here, which is exactly the difference that made this a
            # fifth copy rather than a fifth caller.
            (longest, "Longest Gap", " hot",
             "#%s" % longest_id if longest_id else None),
            (med, "Median Gap", "", None),
            # Not the mean. A gap distribution with one 1,947 in it has a mean
            # that describes no song in the setlist -- across this archive it
            # runs to twice the median on 48% of shows and 253x on one of them.
            # The count of bustouts is the thing the mean was standing near.
            (sum(1 for s in report["songs"]
                 if (s["gap"] or 0) >= BUSTOUT_GAP), "Bustouts", "", None),
        ) if counts or c[1] != "Bustouts"])

    sections, rows, current = [], [], None

    def flush():
        if current is None:
            return
        # In the same order as the header below, which it was not: the last
        # column was emitted as c-last, so the widths came to 26 + 42 + 12 + 42
        # and the table was 122% of its container -- which is why a report
        # scrolled sideways on a phone. Without the Last Performed column it
        # was worse than wrong, it was misaligned: three cols against three
        # headers, but c-last landed on the bar and c-bar on the gap.
        cols = ("<colgroup><col class='c-song'>"
                + ("<col class='c-last'>" if show_last else "")
                + "<col class='c-bar'><col class='c-gap'></colgroup>")
        head = ("<th>Song</th>"
                + ("<th>Last Performed</th>" if show_last else "")
                + "<th></th><th class='n'>Gap</th>")
        sections.append("%s<h2><span class='tab'>%s</span></h2>\n"
                        "<table%s>%s<thead><tr>%s</tr></thead>"
                        "<tbody>\n%s\n</tbody></table>"
                        % ("<div class='perf'></div>" if sections else "",
                           html.escape(current),
                           "" if show_last else " class='no-last'",
                           cols, head, "\n".join(rows)))

    for s, row_id in zip(report["songs"], row_ids):
        if s["set"] != current:
            flush()
            current, rows = s["set"], []
        g = s["gap"]
        klass = "big" if (g or 0) >= 50 else "small"
        # How this song usually behaves: printed small under the number, and
        # marked on the bar so an overshoot is visible rather than arithmetic.
        # Free for anyone who hovers, no clutter for anyone who does not.
        # data-tip rather than title. The browser's own tooltip waits about a
        # second before it appears, which is far too long for a mark whose
        # whole job is answering "what is this?" -- by then the pointer has
        # moved on. aria-label carries the same words to a screen reader,
        # which title was doing incidentally.
        tip = ""
        if s.get("gap_low") is not None and g is not None:
            tip = ("%s show%s; usually %s to %s"
                   % (_stat(g), "" if g == 1 else "s",
                      _stat(round(s["gap_low"])), _stat(round(s["gap_high"]))))
            # A band is one range, and some songs do two things -- see
            # layoff_break. Where they do, the range alone reads as though the
            # song merely waits a long time, and "but" is doing the work: the
            # sentence has stopped describing one behavior and started naming
            # the second. Esther is the case that prompted it, and her range
            # tops out at 55 against three absences of 68, 76 and 112.
            if s.get("gap_away") and s.get("recent_plays"):
                away = s["gap_away"]
                tip += (", but %d of its last %d gaps ran %s or longer"
                        % (away[0], away[2] if len(away) > 2
                           else s["recent_plays"], _stat(away[1])))
        elif g is not None and s.get("recent_plays") is not None:
            # No band, so no bar -- and an empty column is the most confusing
            # thing on the row unless it says why it is empty. This is not a
            # bustout condition, which is how it was first written down: it is
            # any song with fewer than MIN_HISTORY plays inside the window.
            # Strange Design has six and is not a bustout, and looked identical
            # to Johnny B. Goode's nine hundred.
            n = s["recent_plays"]
            tip = ("%s in %d years, so there is no usual range to place this "
                   "gap against"
                   % ("not played" if not n
                      else "played %d time%s" % (n, "" if n == 1 else "s"),
                      RECENT_YEARS))
        # data-tip draws the hover; the same words reach a screen reader as a
        # visually-hidden span *inside* the gap cell rather than as an
        # aria-label *on* it. An aria-label on an element replaces everything
        # in it, so the cell announced "9 shows; usually 5 to 40" and the
        # figure, the median and the verdict -- the three things the cell is
        # for -- were never read out at all. The bar cell takes only the hover,
        # because it holds nothing to announce and would otherwise say the
        # sentence a second time.
        tip_attr = " data-tip='%s'" % html.escape(tip, quote=True) if tip else ""
        sr = "<span class='sr'>%s</span>" % html.escape(tip) if tip else ""

        typical = ""
        if s.get("gap_median") is not None:
            # The median alone. The mean sits within 20% of it for two thirds
            # of songs, so it earned its space rarely, and the band that
            # actually decides the verdict read as jargon on the page --
            # its ends are computed values that appear nowhere in the
            # song's real gaps. Both are still archived in the JSON.
            typical = "<span class='typ'>med %s</span>" % _stat(s["gap_median"])
        elif s.get("recent_plays") is not None:
            # No norm to compare against, so say why: this is how thin its
            # recent record is.
            # Spelled out where there is room, abbreviated where there is not:
            # at 390px "3 in 10 yr" is 72px against a 56px four-digit gap, so
            # the rarest thing in the column was setting its width.
            typical = ("<span class='typ'><span class='full'>%d in %d yr</span>"
                       "<span class='abbr'>%d/%dy</span></span>"
                       % (s["recent_plays"], RECENT_YEARS,
                          s["recent_plays"], RECENT_YEARS))
        # Where a verdict goes depends on what kind of thing it is. A bustout
        # is remarkable about the song -- it belongs against the title, next to
        # the jam chart chip, which is likewise about the song and not its
        # timing. Premature and overdue are judgments about the number, so
        # they belong against the number, under the median they are measured
        # from.
        #
        # At 390px "premature" is 63px against a 39px figure in a 3.7rem
        # column, so at that width the row's grid moves it out of the figure's
        # cell rather than letting it set the column's width -- see the narrow
        # rules, where it becomes its own line in the song area.
        tag = verdict = ""
        v = s.get("verdict")
        if v == "bustout":
            verdict = "<span class='verdict bustout'>bustout</span>"
        elif v in ("premature", "overdue"):
            # One span, not two. Shipping a copy in each cell and hiding one
            # with CSS meant the aria-hidden was baked into whichever copy the
            # markup called the spare -- so on a phone, where the layout shows
            # that one, the visible verdict was hidden from assistive
            # technology and the exposed one was display:none. No verdict was
            # announced at all on the width where it is the only one shown.
            # It lives in the gap cell and the narrow layout moves it.
            tag = "<span class='verdict %s at-gap'>%s</span>" % (v, v)
        if g is None:
            gap_cell = "<span class='gap none'>&mdash;</span>" + typical + tag
            bar = "<td class='bar'></td>"
        else:
            gap_cell = ("<span class='gap %s'>%s</span>%s%s"
                        % (klass, "{:,}".format(g), typical, tag))
            # Against the song's own band, not the show's longest gap. See
            # _band_pos: a bustout used to set a scale that flattened every
            # other row on the night into an identical nub.
            pos = _band_pos(g, s.get("gap_low"), s.get("gap_high"))
            if pos is None:
                # Too little history to have a norm, so there is nothing to be
                # early or late against. The ghost track that used to sit here
                # drew an empty scale at about 1.3:1 against the paper, which
                # read as a bar that had failed to render rather than as a
                # measurement that was never possible. A dash says the absence
                # out loud, in the one place a reader is already looking for
                # the mark, and the hover says why.
                bar = ("<td class='bar'%s><span class='no-range'"
                       " aria-hidden='true'>&mdash;</span></td>" % tip_attr)
            else:
                # The mark is colored by where it landed, not by how large
                # the number is. Those are different questions and they
                # disagree: a gap of 10 against a median of 5 sits right of the
                # band and is called overdue, but 10 is under the absolute
                # threshold, so the mark was drawn cool while its position and
                # the verdict beside it both said late. Position is what this
                # graphic encodes, so position is what it may color.
                where = ("early" if pos < 30 else
                         "late" if pos > 70 else "usual")
                bar = ("<td class='bar'%s><span class='track'>"
                       "<span class='band'></span><span class='mid'></span>"
                       "<span class='at %s' style='left:%.2f%%'></span>"
                       "</span></td>" % (tip_attr, where, pos))
        # Both statistics cells carry the explanation, so the hover target is
        # the whole of them rather than a range bar that can be five pixels wide.
        # The title is the way in to the song's own history, but only once that
        # page exists: a report archived before song pages did has songs the
        # band has not played since, and those get a page when they next come
        # round rather than a link to nowhere now.
        title = html.escape(typographic(s["song"]))
        href = ""
        if s["slug"] in songs:
            # Anchored at this very performance, so the link answers "where
            # does tonight's version sit against all the others" rather than
            # dropping you at the top of a six-hundred-row page to go looking.
            #
            # Only where that row exists. `songs` maps each slug to the dates
            # its page actually carries, because a show report and a song
            # history are two phish.net endpoints and they disagree once: the
            # 2020-08-11 Tonight Show lists I Never Needed You Like This
            # Before as a debut, and that song's own history begins in 2021.
            # One anchor of 14,126, and it landed at the top of the page --
            # which is what the anchor exists to avoid.
            rows_on = songs.get(s["slug"]) if hasattr(songs, "get") else None
            frag = ("#" + html.escape(report["date"], quote=True)
                    if rows_on is None or report["date"] in rows_on else "")
            href = "../song/%s.html%s" % (
                html.escape(s["slug"], quote=True), frag)
            title = "<a href='%s'>%s</a>" % (href, title)
        # phish.net wrote something about this one. The prose itself lives on
        # the song page, so this says so and points there rather than repeating
        # it here: a report is one night's gaps, and a paragraph per song would
        # bury them. A dot used to mark these, which told nobody anything.
        # Its own link rather than part of the title's, so the segue mark can
        # sit between them -- see below.
        chip = ""
        if s["jamchart"]:
            chip = ("<a class='jc-chip' href='%s'>Jam chart</a>" % href if href
                    else "<span class='jc-chip'>Jam chart</span>")
        # Outside the link, so the mark is not underlined with the title and
        # cannot be mistaken for part of the song's name.
        seg = ("<span class='seg%s'>%s</span>"
               % (" tight" if s["out"] == "->" else "", html.escape(s["out"]))
               if s.get("out") else "")
        # Song, then how it left, then everything said about it. The mark is
        # setlist notation and belongs against the title the way it is written
        # -- "Ether Edge >" -- not stranded past a chip, where it read as
        # punctuation belonging to the chip.
        cells = "<td class='song'>%s%s%s%s</td>" % (title, seg, chip, verdict)
        if show_last:
            if s["prev_date"]:
                # No <br>: the spans are blocks on wide layouts and inline on
                # narrow ones, so CSS alone decides how they stack. Empty ones
                # are dropped rather than left to grow a stray separator.
                # We very likely hold that show too -- 23 of 26 on a typical
                # report -- and "what else happened the last time they played
                # it" is the most natural click on the page. It was dead text.
                stamp = s["prev_date"]
                if stamp in archived_show:
                    stamp = ("<a href='./%s.html'>%s</a>"
                             % (html.escape(stamp, quote=True), stamp))
                bits = ["<span class='cap'>Last performed</span>",
                        "<span class='date'>%s</span>" % stamp]
                for cls, text in (("venue", s["prev_venue"]),
                                  ("place", s.get("prev_place"))):
                    if text:
                        bits.append("<span class='%s'>%s</span>"
                                    % (cls, html.escape(text)))
                cells += "<td class='last'>%s</td>" % "".join(bits)
            elif s.get("debut"):
                cells += ("<td class='last'><span class='cap'>Last performed"
                          "</span><span class='none'>debut</span></td>")
            else:
                cells += "<td class='last'></td>"
        # The bar and the figure close the row, which is where the song page
        # puts them too.
        #
        # The gap column names itself here, the way every other cell in the
        # stacked row does. Its label comes from the <th> on a wide screen, and
        # the <th> is hidden below 620px -- so on a phone the largest figure in
        # the row was the only thing on it that never said what it was, and a
        # reader had to infer it. Same mechanism as .last's own cap, hidden
        # wherever the header is doing the naming.
        cells += ("%s<td class='n'%s><span class='cap'>Gap</span>%s%s</td>"
                  % (bar, tip_attr, gap_cell, sr))
        rows.append("<tr id='%s'>%s</tr>"
                    % (html.escape(row_id, quote=True), cells))
    flush()

    notes = ""
    if report.get("notes"):
        notes = "<div class='notes'>%s</div>" % report["notes"]

    # Walking a tour without going back to the index. The first and last shows
    # the site knows about simply have one fewer link; the grid holds the
    # index link in the middle either way.
    crumb = ""
    if index_href:
        step = ("<a class='%s' rel='%s' href='./%s.html' "
                "aria-label='%s show, %s'>%s</a>")
        # Two rows, deliberately: the section links read the same as every
        # other page type, and the pager sits under them. Appending them to a
        # three-column pager grid left them wrapping into cells meant for
        # something else.
        # No "All reports" in the middle: the row above already has Shows,
        # pointing at the same page under the name the rest of the site uses
        # for it. The pager is for the two neighbors.
        #
        # The pager is built first and the strip concatenated after, rather
        # than interpolating both at once: nav_strip's output is markup this
        # function did not write, and running % over it would make any literal
        # percent sign in a future label a formatting error at render time.
        pager = ("<nav class='crumb pager'>%s%s</nav>" % (
            step % ("prev", "prev", prev_date, "Previous", prev_date,
                    "&larr; " + prev_date) if prev_date else "",
            step % ("next", "next", next_date, "Next", next_date,
                    next_date + " &rarr;") if next_date else ""))
        crumb = nav_strip(section="Shows", root="../", mark=True) + pager

    # What a chat client shows when someone drops the link in a thread. Plain
    # text, entities and all, because html.escape has the last word on it.
    # The share text must agree with the share image. The card for a show in
    # progress deliberately carries no figures, so a description asserting a
    # song count and a longest gap contradicts the picture above it -- and both
    # are frozen into somebody else's timeline the moment they paste the link.
    if report.get("provisional"):
        blurb = "%s \u00b7 being played now, setlist still coming in" % report["venue"]
        allg = []
    else:
        blurb = "%s \u00b7 %d songs" % (report["venue"], len(report["songs"]))
    if allg:
        blurb += " · longest gap %s (%s)" % (
            longest, next((s["song"] for s in report["songs"]
                           if s["gap"] == biggest), ""))

    # phish.net files one-offs under "Not Part of a Tour", which is not worth
    # saying out loud.
    name = report.get("tour") or ""
    name = (html.escape(name)
            if name and "not part of a tour" not in name.lower() else "")

    # Era-scoped, because an absolute one cannot be said honestly -- see
    # era_ordinal. Silent for 1.0 and for anything not on the calendar, which
    # is where the soundchecks and sessions land.
    place = era_ordinal(calendar, report["date"])
    nth = ("%s show of %s" % (_ordinal(place[0]), place[1])) if place else ""

    # The ordinal leads and the tour closes, so the weight in this block builds
    # towards the right edge the whole header is set against -- the two lines
    # under it put their heaviest type hard right, and this line used to run
    # the other way, opening on the boldest thing on it and trailing off into
    # the lightest.
    #
    # The separator belongs to the pair, not to either half. It used to be a
    # ::before on the ordinal, which meant a festival -- phish.net files those
    # as "Not Part of a Tour", so `name` is empty -- opened the line with a
    # dot attached to nothing. Watkins Glen read "· 119th show of 3.0".
    tour = ""
    if nth or name:
        tour = "<span class='nth'>%s</span>" % nth if nth else ""
        if name:
            tour += ("<span class='sep'>&middot;</span>" if nth else "")
            # The tour is a search, not a label. Every show of it is one click
            # away and the index already carries the tour name in each row's
            # haystack, so this needs no page of its own and nothing that can
            # fall out of step with the archive. Quoted, for the reason the
            # venue links are: unquoted words match loosely and "2026 Summer
            # Tour" would answer for any show with those words anywhere in it.
            #
            # Unless the name is inside another name, in which case even the
            # quoted phrase is not exact and the tour stays plain text. See
            # ambiguous_tours.
            tour += ("<span class='tour'>%s</span>" % name
                     if name in unlinkable_tours else
                     "<span class='tour'><a href='%s'>%s</a></span>"
                     % (search_href(name), name))

    # phish.net's own rating for the night, which their API does not expose --
    # fouldomain does, so it is theirs by way of someone else and says so.
    # Absent for a show played last night, which simply has no line.
    # Still coming in. Said plainly, with the two facts that make it useful:
    # how much is here, and when it last moved. The reload keeps a page open on
    # a phone in a parking lot current without anybody touching it.
    # Not a show. Its pages exist and its songs are real, but nothing on it
    # feeds a gap, a median or a verdict, and a reader who arrived from the
    # "Also on file" list should not have to infer that.
    aside = ""
    if not counts:
        aside = ("<p class='aside-note'><b>Not counted</b>"
                 "<span>phish.net does not count this toward a gap, so neither "
                 "do we. Nothing here feeds any figure on the rest of the "
                 "site.</span></p>")

    live = poll = ""
    if report.get("provisional"):
        # Two clocks, and the second is the one that matters. When the last
        # song arrived says how the show is going; when we last looked says
        # whether this page is still being fed. Without the second, a reader
        # cannot tell a gap between sets from a build that has stopped -- and
        # both look like a page that has not changed for forty minutes.
        since = report.get("count_since") or ""
        checked = _utcnow().isoformat(timespec="seconds")
        n = len(report["songs"])
        # One clock, and it is the one that says whether this page is still
        # being fed. When the last song arrived is on the row it arrived in;
        # repeating it up here as a second wall-clock time said nothing the
        # reader wanted and read like a server log.
        # data-show, so the "new since you last looked" mark can key its note
        # on the night rather than on the page title. The title begins with the
        # song count -- "(20) 2026-07-27" -- so a key derived from it changed
        # every time a song landed, which is precisely when the mark is meant
        # to fire, and it never once did.
        # "Last checked" was a claim about the server and this stamp cannot
        # make one: it is written at render time, so a document sitting in a
        # tab for an hour faithfully reports its own age and nothing else.
        # That was the one honest thing on a stale page and it read as the
        # opposite. It now says what it measures.
        # Three ideas, and the third is not about the show at all -- it is a
        # promise about the document. Run in with middots it wrapped after
        # "this", consistently, because that is simply where the measure ran
        # out: "... 1 minute ago * this / page refreshes itself". Its own line
        # cannot stall like that, and .live span:not(.since-you) already makes
        # every span here a block, so this costs no CSS.
        live = ("<p class='live' role='status' aria-live='polite'"
                " data-show='%s'>"
                "<b>This show is being played right now</b>"
                "<span><b class='n'>%d</b> song%s so far &middot; "
                "this page was built <time class='ago' datetime='%s'>%s</time>"
                "</span><span>It updates itself as songs land</span></p>"
                % (html.escape(report["date"], quote=True),
                   n, "" if n == 1 else "s",
                   html.escape(checked, quote=True), _clock(checked)))
        poll = LIVE_JS

    # The inlined display face, for output with no stylesheet beside it -- but
    # only when the page has a use for it. This sheet names Bagnard in exactly
    # one rule, `.live b` above, so a settled show's single-file output was
    # carrying 17 KB of font to paint nothing: 19% of a 91 KB file, measured
    # 2026-07-30. Deleting it outright is the obvious cure and the wrong one --
    # it drops that banner to Georgia, which no loaded page uses anywhere else
    # and which is precisely the generic voice `.live b` was written to escape.
    # Tying it to the one rule that asks for it costs the settled case nothing
    # and leaves the live case exactly as designed.
    face = inline_font_css() if report.get("provisional") else ""

    rating = ""
    if report.get("pnet_rating") is not None:
        rating = ("<p class='rating'>Phish.net rating <b>%.2f</b>"
                  "<span> via fouldomain</span></p>" % report["pnet_rating"])

    return SHELL.format(
        ago_js=AGO_JS,
        new_rows_js=NEW_ROWS_JS,
        analytics=ANALYTICS,
        css=CSS, theme_js=THEME_JS, keys_js=KEYS_JS, theme_ui=THEME_UI, fonts=WEB_FONTS,
        date=html.escape(report["date"]), crumb=crumb, tour=tour,
        dow=_full_weekday(report["date"]),
        # A tab left open all night should say what it is holding. Without
        # this the live show's tab is indistinguishable from any archived one.
        titlestate=("(%d) " % len(report["songs"])
                    if report.get("provisional") else ""),
        live=live, poll=poll, aside=aside,
        venue=_venue_lines(report), hero=hero, rating=rating,
        links=_show_links(report["date"], on_phishin), blurb=html.escape(blurb, quote=True),
        sections="\n".join(sections), notes=notes,
        sheet=(sheet_links(sheet) if sheet else face),
        row_js=ROW_JS,
        share=share_meta("%s%s &mdash; Possum Logic"
                         % ("Live: " if report.get("provisional") else "",
                            html.escape(report["date"])),
                         html.escape(blurb, quote=True),
                         "%s/%s.html" % (SHOW_DIR, report["date"]), card=card),
        # Dated by the report's own data, not by the clock. A build stamp made
        # every page differ from yesterday's copy of itself, so a nightly run
        # republished all of them to say nothing had happened. count_since is
        # when this setlist last actually moved; a report rendered outside a
        # site has none and falls back to the night it describes.
        stamp="Updated %s" % (report.get("count_since")
                              or report["date"])[:10])


# ------------------------------------------------------------------ index ---

INDEX_CSS = BASE_CSS + BODY_BOX_CSS + """/* Which of the two lists you are looking at, and the way to the other one.
   Above the wordmark because that is where a reader looks for it, and because
   the footer link that used to be the only route was found by nobody. */
/* Wrapping, with the same row gap the song pages use. This row did not wrap
   before, and did not need to at five sections: each label simply broke inside
   itself and the row stayed within the viewport. At six it stopped fitting and
   the due page ran 401px wide inside a 375px phone -- the whole page scrolling
   sideways for one nav item. Breaking between labels rather than inside them
   is what the song pages have always done; the two sheets disagreed only
   because nothing had ever pushed this one. */
""" + NAV_CSS + """h1{font-family:'Bagnard',Georgia,serif;font-weight:400;
   font-size:clamp(1.7778rem,7vw,3.5556rem);line-height:1.06;margin:0 0 .7rem;
   letter-spacing:-.01em}
h1 em{font-style:normal;color:var(--hot)}
/* The wordmark goes home, as a wordmark does, without looking like a link. */
h1 a{color:inherit;text-decoration:none}
h1 a:hover em{color:var(--ink)}
/* A hero card that is also a way in. Only some of them are. */
""" + CARD_LINK_CSS + """/* Some of the cards are links and some are not, so the ones that are need to
   say so -- but a rule under a letterspaced label reads as a stray underline
   rather than an affordance, and it was the one line in the hero not doing
   structural work. An arrow after the label carries the same message and
   disappears into the type. Right, not down: this card leaves for another
   page, where the show and song sheets' cards land further down their own. */
a.card .lbl::after{content:" →";color:var(--dim);white-space:nowrap}
/* Which song, or which night, the figure belongs to -- under the label and in
   the label's own small type, so the card still reads as one object. */
.lbl .of{display:block;margin-top:.2rem;letter-spacing:.14em;color:var(--ink-soft);
   text-transform:none;font-size:.75rem}
/* And on those cards the arrow moves down onto the name. The rule above
   appends to the end of the label, and the last thing in a label carrying a
   name is that display:block name -- so the arrow opened a line of its own and
   sat alone under it. On the name it is also the more honest target: the card
   goes to that song or that night, not to a page about longest gaps.

   `.named` is written by hero_html rather than inferred here with `:has(.of)`,
   because an unsupported selector is dropped in silence -- which would leave
   the arrow where it was *and* add a second one below it, on exactly the
   browsers nobody is testing. `.of` states its own color, so it does not
   inherit the label's hover and has to be named again. */
a.card.named .lbl::after{content:none}
a.card.named .lbl .of::after{content:" →";color:var(--dim);white-space:nowrap}
a.card.named:hover .lbl .of,
a.card.named:hover .lbl .of::after{color:var(--hot-text)}
header{padding-bottom:.9rem}
.show{margin:0;font-size:1rem;font-weight:600;letter-spacing:0;
      text-transform:uppercase;color:var(--ink-soft)}
""" + RULE2_CSS + """/* Six cards do not fit on one line, and a wrapping flex row gives the first
   card of the second line a left rule -- which then separates it from the page
   margin rather than from another card, and leaves its number indented out of
   line with the wordmark and every row below it. A grid ties both the rule and
   the flush left edge to a *column position* rather than to wherever the cards
   happen to wrap, so the stranded rule is impossible instead of relocated. The
   column count is written by whoever builds the hero, so it cannot disagree
   with the number of cards actually in it. */
/* The class names the column count rather than the card count, so a hero that
   gains or loses a card only has to say how many columns it now wants, and
   four cards on the song index and six here share one set of rules. The
   fallback is the four-across the hero had before any of this. */
.hero{display:grid;grid-template-columns:repeat(4,1fr);margin:.7rem 0 .3rem;
      border-bottom:1px solid var(--ink)}
.hero-c3{grid-template-columns:repeat(3,1fr)}
.hero-c4{grid-template-columns:repeat(4,1fr)}
.card{padding:.85rem 1.1rem;border-left:1px solid var(--rule);
   display:flex;flex-direction:column}
/* Only above the breakpoint. The narrow layout has always been two columns and
   already says which cards start a row down there; stating it twice meant the
   wide rule outranked the narrow one and left card 4 of a six indented half a
   space out of line with the cards above and below it. Each width states its
   own row-starts and neither has to undo the other. */
@media screen and (min-width:621px){
  .hero-c3>.card:nth-child(3n+1),
  .hero-c4>.card:nth-child(4n+1){border-left:0;padding-left:0}
  /* A second row of cards needs a rule over it, or the two rows read as one
     block with the numbers of the first sitting on the labels of the next. */
  .hero-c3>.card:nth-child(n+4),
  .hero-c4>.card:nth-child(n+5){border-top:1px solid var(--rule)}
}
.num{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;font-size:2.25rem;line-height:1;
     letter-spacing:0;margin-top:auto}
""" + FIGURE_CSS + """.tools{margin:1.9rem 0 .9rem}
/* Two rows rather than one wrapping run. The things you operate -- the search
   box and the sort -- sit together on the first; the filter chips are a
   different kind of control and get their own line instead of pushing sort to
   wherever the chips happen to stop. */
.tools-main{display:flex;flex-wrap:wrap;align-items:center;gap:.55rem .8rem}
.tools .chips{margin-top:.6rem}
.search{flex:1 1 15rem;min-width:0;font:inherit;font-size:.875rem;
        padding:.5rem .7rem;border:1px solid var(--edge);border-radius:0;
        background:transparent;color:var(--ink)}
.search::placeholder{color:var(--dim)}
.search:focus-visible,.chip:focus-visible,.sort:focus-visible{
  outline:2px solid var(--hot);outline-offset:1px}
/* Shown only once there is something to clear. The song page has carried this
   button for a while; the index only ever had the line of script that hides
   it, which is why that line referred to an element that was never here. */
.clear{font:inherit;font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   padding:.45rem .6rem;border:1px solid var(--edge);background:transparent;
   color:var(--dim);cursor:pointer}
.clear:hover{color:var(--hot-text);border-color:var(--hot-text)}
.clear:focus-visible{outline:2px solid var(--hot);outline-offset:1px}
.chips{display:flex;flex-wrap:wrap;gap:.3rem}
.chip{font:inherit;font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
      padding:.42rem .6rem;border:1px solid var(--edge);background:transparent;
      color:var(--dim);cursor:pointer}
.chip:hover{color:var(--ink)}
.chip.on{background:var(--ink);color:var(--paper);border-color:var(--ink)}
/* How many shows the era holds, so four chips carry the information the
   forty years did without the forty buttons. */
.chip-n{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   letter-spacing:0;color:var(--dim);margin-left:.3rem}
.chip.on .chip-n{color:var(--paper)}
""" + SELECT_CSS + """.count{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
       color:var(--dim);margin-left:auto}
.count b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
         font-size:1rem;color:var(--ink)}
.reports{list-style:none;margin:0;padding:0}
/* Geometry shared with the header below, chrome kept separate, so a column
   that moves moves in both at once rather than in whichever one was edited. */
.row,.lhead{display:grid;grid-template-columns:7.2rem 1fr 20.4rem;
     column-gap:1.1rem;align-items:baseline}
.row{padding:.7rem .25rem;text-decoration:none;
     color:inherit;border-bottom:1px solid var(--rule-soft)}
/* The column header these list pages never had, and it stays put.

   A grid rather than a <table>, because every row on these pages is one link
   and HTML does not let an <a> wrap a <tr>. Show pages get a real table for
   the opposite reason: their rows carry two destinations -- the song, and the
   night it was last played -- so the links live in cells and a <tr> is free.
   The tabular *look* is the same either way; only the markup differs, and it
   differs for a reason rather than by neglect.

   Opaque, because rows scroll under it. box-shadow rather than border-bottom:
   a border on a stuck element is drawn at its edge and can be clipped by the
   row arriving beneath it, and this way the rule never thins. */
.lhead{position:sticky;top:0;z-index:3;background:var(--paper);
   padding:.45rem .25rem;font-size:.625rem;text-transform:uppercase;
   letter-spacing:.14em;color:var(--dim);font-weight:500;
   box-shadow:inset 0 -1px 0 var(--rule)}
/* The figures column is its own sub-grid on the row, so the header's must be
   the same one or the labels sit over the wrong numbers. Taking .r-stats
   wholesale would bring its 12px reading size with it. */
.lhead .r-stats{font-size:inherit;color:inherit;line-height:inherit}
.lhead .end{text-align:right}
@media print{.lhead{position:static}}
/* A sticky strip at the top of the viewport is what puts an anchor target
   underneath it. Stated once for every id on these pages rather than per
   anchor, so a new one cannot be the thing that finds this out. */
[id]{scroll-margin-top:2.6rem}
/* Not the column header. It wears `.row head` because it needs the same grid
   as the performances beneath it, and so it inherited their hover: it lit up
   exactly like a row and did nothing when clicked, which is an affordance
   promising a target that was never there. Only the song pages carry a
   `.row head` today; the rule is written into both sheets that have `.row`
   so the two cannot drift apart the next time one gains a header. */
.row:not(.head):hover{background:var(--hover)}
/* Same rule, same reason: this is the one place the site still spoke two
   languages, since the song pages had already moved. */
/* Data in a column, so the mono: tabular by construction, which is what makes
   710 dates present one edge to the venue beside them rather than a soft
   ragged one. The display face keeps the mastheads, where a date is the name
   of the page rather than a value in a list. */
.r-date{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
        font-size:1rem;line-height:1.3rem;white-space:nowrap}
.r-venue{font-size:.875rem;font-weight:500;letter-spacing:0;
         line-height:1.3rem}
.r-place{display:block;color:var(--dim);font-size:.75rem;line-height:1.15rem}
/* Deliberately not a report row. These are on file, not on the bill: smaller,
   dimmer, no figures, and below the empty-search message so a search matching
   nothing cannot look as though it matched these. */
/* The due list. Same row grammar as the show index -- identity, context,
   figure -- so the two pages read as the same object seen from two sides. */
.onstage{display:flex;flex-wrap:wrap;align-items:baseline;gap:.3rem 1.1rem;
   margin:1.1rem 0 0;padding:.7rem .9rem;color:inherit;text-decoration:none;
   border-left:4px solid var(--hot);background:var(--hover)}
/* --hot-text and the left edge with it, so the reversed block is one colour
   rather than a 4px stripe of the display accent against a darker fill. Same
   4.44-at-10px argument as .jc-chip and .verdict.bustout. */
.onstage:hover{background:var(--hot-text);border-left-color:var(--hot-text);
   color:var(--paper)}
.onstage .k{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--hot-text);font-weight:600}
.onstage .w{font-size:1rem;font-weight:600;letter-spacing:0;text-transform:uppercase}
.onstage .p{display:block;font-size:.75rem;font-weight:400;color:var(--dim);
   text-transform:none;letter-spacing:0}
.onstage .n{margin-left:auto;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--dim)}
.onstage .n b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:1.125rem;letter-spacing:0;color:var(--ink)}
/* Everything inside a reversed block comes with it. This used to be a list of
   the three children that pin a colour -- .k, .n b, .p -- and the list was
   missing .n itself, whose own text is the words "songs so far". They stayed
   var(--dim) on the fill: 1.12:1 light, 1.08:1 dark, which is not dim, it is
   gone. Exactly the numbers the .live span bug produced, in the same week, on
   the banner that only ever appears while a show is being played -- so the
   one state nobody browsing the archive can stumble into.

   A list of children is a list a fourth child is not on; `*` cannot be
   incomplete.

   The class is doubled because the first attempt at this was `.onstage:hover
   *` and it did not work on all of them. `*` contributes *nothing* to
   specificity, so that selector is 0-2-0: it beat .k and .p at 0-2-0 on order
   alone and lost to .onstage .n b at 0-2-1, leaving the song count as var
   (--ink) on the fill, 2.68:1 light and 2.25:1 dark. Repeating .onstage buys
   the third class the element in `.n b` would otherwise win with, so this is
   0-3-0 and no descendant rule in the block can reach it -- and it does not
   have to be kept in any particular place in the sheet to stay true. */
.onstage:hover.onstage *{color:inherit}
/* Structural, and load-bearing rather than tidiness. Every list section on the
   due and out-of-rotation pages is wrapped in one of these so that its
   position:sticky column header is held by the section instead of by the page:
   sticky is bounded by the element's *parent*, so three headers sharing one
   parent each stayed pinned for the whole rest of the document, and the header
   of one list came to rest ruled across the heading of the next. Deliberately
   carries no visual property -- there is nothing to draw here, and anything
   added would land on both pages at once. `display:block` is a <section>'s own
   default and is written out so the class is findable in this sheet. */
.rot{display:block}
.due{list-style:none;margin:0;padding:0}
.due li{border-bottom:1px solid var(--rule-soft)}
.due .row,.lhead.due-h{display:grid;grid-template-columns:1fr 11rem 11rem;
   column-gap:1.1rem;align-items:baseline}
.due .row{padding:.6rem .25rem;color:inherit;text-decoration:none}
.due /* Not the column header. It wears `.row head` because it needs the same grid
   as the performances beneath it, and so it inherited their hover: it lit up
   exactly like a row and did nothing when clicked, which is an affordance
   promising a target that was never there. Only the song pages carry a
   `.row head` today; the rule is written into both sheets that have `.row`
   so the two cannot drift apart the next time one gains a header. */
.row:not(.head):hover{background:var(--hover)}
.d-song{font-size:1rem;font-weight:500}
.due .row:hover .d-song{color:var(--hot-text)}
.d-date{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:.875rem;white-space:nowrap}
.d-where{display:block;color:var(--dim);font-size:.75rem}
.d-n{text-align:right}
.d-n > b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:1.5rem;line-height:1;color:var(--hot-text);white-space:nowrap}
.d-n .typ{display:block;font-size:.75rem;color:var(--dim);margin-top:.15rem}
.d-n .typ span{display:block;white-space:nowrap}
/* Same rule the song pages carry, and it has to be stated here too because
   this sheet does not include theirs. It was missing entirely, so the due and
   venue standfirsts fell through to a bare <p>: mono, 16px, full measure,
   while the identical class on a song page was 12px and dim. One class, two
   appearances, by accident. */
""" + DEK_CSS + """
/* The measurement detail, folded away. Three paragraphs used to stand open
   here: 835px of a 1,147px front matter on a phone, 73% of it, before the
   first due song. And the FAQ already carries 2,930 characters on the same
   subject against their 1,189 -- so this page was not explaining itself, it
   was holding a shorter second copy of an answer that lives elsewhere, above
   its own content.
   What stays open is the one thing a reader cannot read the third column
   without: what 2x means. The rest is one click, and the click does not leave
   the page, which is the objection to sending it to the FAQ outright.
   Nothing is remembered per reader. A flag that says "you have read this"
   fails asymmetrically -- set wrongly it shows a first-time reader an
   unlabeled table of multipliers, unset wrongly it costs one line -- and a
   reference archive should not serve two different pages at one URL. The
   site's own precedent argues the same way: the last per-reader flag here
   shipped broken and stayed invisible for weeks.
   Same <details> idiom the show pages use for long notes: no JavaScript and
   keyboard-operable. It stays closed when printed, like every other one on
   the site -- forcing it open needs more than hiding the summary, and a
   half-done version that only removed the control would print a folded
   section with no sign it folds. */
details.how{margin:.7rem 0 0}
/* display:block, which is the shape details.jam and details.note already use
   on the song pages -- one idiom for disclosure on this site rather than two.
   width:max-content keeps the rule under the words instead of across the
   column.
   A caution for whoever measures this next: the accessibility inspector
   reports this summary as a plain "generic" node, and the site's existing
   shipped details reports exactly the same way, so that reading is the tool
   and not the markup. It was nearly written down here as a real defect. */
details.how > summary{display:block;width:max-content;
   font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim);border-bottom:1px solid var(--rule);cursor:pointer;
   padding:0 0 .1rem;list-style:none}
details.how > summary::-webkit-details-marker{display:none}
details.how > summary::after{content:" \\2193"}
details.how[open] > summary::after{content:" \\2191"}
details.how > summary:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* A section heading, under the due list. At 1.5rem it was barely larger than
   the 1rem song titles it headed, which made a new section read as another
   row. 2.125rem sits clearly between the page title and the data. */
.shelf-h{margin:3rem 0 .5rem;font-family:'Bagnard',Georgia,serif;
   font-weight:400;font-size:2.125rem;line-height:1.15;
   scroll-margin-top:2.6rem}
.shelf-h+.dek{margin-bottom:1.1rem}
/* The adjacent-sibling rule above reaches the *first* standfirst under a
   heading and no further, which was every case until a section blurb grew a
   second paragraph. `.dek` is margin-bottom:0 by default, so the trailing
   paragraph sat flush against the column header below it -- measured at 0px,
   against 19.8px for the one above it. Every `.dek` inside a section instead.
   A no-op on the due page, whose sections still carry one apiece. */
.rot .dek{margin-bottom:1.1rem}
/* The way back up. This is the fourth place it has been wanted -- the FAQ's
   answers, and now each section here -- so it is a house idiom rather than a
   page's own trick: jumping somewhere should never maroon a reader there, and
   these pages are long. Mono and small: a control, not a sentence. */
.backtop{margin:1rem 0 0;font-family:'IBM Plex Mono',ui-monospace,monospace;
   font-size:.625rem;letter-spacing:.14em;text-transform:uppercase}
.backtop a{color:var(--dim);text-decoration:none;
   border-bottom:1px solid var(--rule);position:relative;display:inline-block}
.backtop a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
.backtop a::before{content:"";position:absolute;left:50%;top:50%;
   transform:translate(-50%,-50%);width:100%;min-width:24px;height:24px}
@media print{.backtop{display:none}}
/* The venue list borrows the due page's three-column shape because it answers
   the same shape of question: a name, a when, and one figure worth ranking by.
   Its own class names, though -- .d-* means "due", and a venue row sharing
   them would make either page impossible to restyle without the other. */
.vn{list-style:none;margin:0;padding:0}
.vn li{border-bottom:1px solid var(--rule-soft)}
.vn .row,.lhead.vn-h{display:grid;grid-template-columns:1fr 12rem 7rem;
   column-gap:1.1rem;align-items:baseline}
.vn .row{padding:.6rem .25rem;color:inherit;text-decoration:none}
.vn /* Not the column header. It wears `.row head` because it needs the same grid
   as the performances beneath it, and so it inherited their hover: it lit up
   exactly like a row and did nothing when clicked, which is an affordance
   promising a target that was never there. Only the song pages carry a
   `.row head` today; the rule is written into both sheets that have `.row`
   so the two cannot drift apart the next time one gains a header. */
.row:not(.head):hover{background:var(--hover)}
.vn-venue{font-size:1rem;font-weight:500}
.vn .row:hover .vn-venue{color:var(--hot-text)}
.vn-place{display:block;color:var(--dim);font-size:.75rem;font-weight:400}
.vn-span{font-family:'IBM Plex Mono',ui-monospace,monospace;font-size:.875rem;
   color:var(--dim);white-space:nowrap}
.vn-n{text-align:right}
.vn-n b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:1.5rem;line-height:1;color:var(--ink)}
.vn-n .typ{display:block;font-size:.75rem;color:var(--dim);margin-top:.15rem;
   white-space:nowrap}
@media screen and (max-width:620px){
  /* "dates", not "span": grid-area:span would be parsed as the span keyword
     and drop the whole declaration. */
  /* max-content rather than 5.5rem, and it was the fixed figure that made this
     worth measuring. 5.5rem was cut to fit "longest 1,468" at the old scale and
     did not fit it at the new one -- 99px of column for 106px of label -- so
     the figures column was quietly overflowing its own track. A column asked to
     be exactly as wide as its content cannot be cut to fit anything. */
  .vn .row{grid-template-columns:1fr max-content;
     grid-template-areas:"venue n" "dates n";row-gap:.15rem}
  .vn-venue{grid-area:venue}
  .vn-span{grid-area:dates}
  .vn-n{grid-area:n}
  .vn-n b{font-size:1.25rem}
}
/* Below this the two columns cannot both be honest. The dates are a span --
   "2009-12-02 -> 2026-07-27", 23 characters of mono that must not break, since
   a date split across a line is unreadable and the arrow between them would be
   stranded -- so the left column has a hard floor of about 217px, and the
   figure wants another 106 beside it. At 320px there are 288 to share. The
   answer is the one this site already gives everywhere else: stack, and let the
   rules run the full width, rather than squeeze columns until something is
   clipped or pushed off the screen. */
@media screen and (max-width:400px){
  .vn .row{grid-template-columns:1fr;
     grid-template-areas:"venue" "dates" "n";row-gap:.2rem}
  .vn-n{text-align:left}
  .vn-n .typ{display:inline;margin-left:.5rem}
}
@media screen and (max-width:620px){
  /* 5.5rem held one number. It now holds that number and the multiple the
     list is ordered by, which wraps to two lines here rather than being
     dropped -- the order is the point of the page at any width. */
  .due .row{grid-template-columns:1fr 7rem;grid-template-areas:"song n" "last n";
     row-gap:.15rem}
  .d-song{grid-area:song}
  .d-last{grid-area:last}
  .d-n{grid-area:n}
  .d-n > b{font-size:1.25rem}
}
/* The pointer to the not-a-show page, where a list of twenty used to sit at
   the foot of 692 rows. Ian: "move the 'also on file' listings to a higher
   prominence home, or at least something that's not tacked onto the end of
   the show list." Under the hero, where a reader lands. */
.aside{margin:1.1rem 0 0;font-size:.75rem;color:var(--dim);max-width:68ch}
.aside b{color:var(--ink);font-weight:400}
.aside a{color:var(--ink);text-decoration:none;
   border-bottom:1px solid var(--rule)}
.aside a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* The list itself, which moved to a page of its own. Named rather than
   scoped to `.aside`, because it now has two homes and the version in this
   file has been the wrong shape twice for want of one name. */
.axlist{list-style:none;margin:0;padding:0}
.axlist li{display:flex;flex-wrap:wrap;align-items:baseline;gap:.5rem;
   padding:.3rem 0;border-bottom:1px solid var(--rule-soft);font-size:.75rem}
.ax-row{display:contents;color:inherit;text-decoration:none}
.ax-date{font-family:'Bagnard',Georgia,serif;font-size:.875rem;
   border-bottom:1px solid var(--rule)}
a.ax-row:hover .ax-date{color:var(--hot-text);border-bottom-color:var(--hot-text)}
.ax-kind{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--hot-text)}
.ax-venue{color:var(--dim)}
.ax-n{color:var(--dim);font-variant-numeric:tabular-nums}
/* phish.net's note, on its own line under the row. flex-basis:100% rather than
   a grid cell because the row above it is a wrapping flex line of four
   variable-width parts, and the note is the one thing that always wants the
   whole measure. Set in the reading face: it is the only prose in this list,
   and at 12px mono a 778-character note is a wall. */
.ax-note{flex-basis:100%;margin:.15rem 0 .1rem;max-width:74ch;
   font-family:'Literata',Georgia,serif;font-size:.8125rem;line-height:1.5;
   font-variation-settings:'opsz' 13;color:var(--ink-soft)}
.ax-note a{color:var(--ink-soft);border-bottom:1px solid var(--rule)}
.ax-note a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
.axlist .for{color:var(--dim)}
.axlist .for a{color:inherit}
/* A grid, not a right-aligned sentence. Right-alignment pins only the right
   edge; every figure to the left of it still moved row to row with the width
   of the numbers beside it. */
.r-stats{font-size:.75rem;color:var(--dim);line-height:1.3rem;
         display:grid;grid-template-columns:5.4rem 6.4rem 7.4rem;
         justify-items:end;column-gap:.6rem}
.r-stats .st{white-space:nowrap}
/* Tabular numerals do the aligning; the widths these used to be given by hand
   were a workaround for not having asked the face for them. */
.r-stats .st b{display:inline-block;text-align:right}
.r-stats b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
           font-size:1rem;color:var(--ink)}
.r-stats b.hot{color:var(--hot-text)}
/* A show still being played, said in the one place on the row where the
   number it qualifies already is: 24 songs means something different
   tonight than it will tomorrow. */
.live-tag{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--hot-text)}
/* The song that held the longest gap, under the figures it belongs to. Named
   for what it is: ".r-song" also means "the song this row is about" on the
   song index, which inherits this stylesheet, and one grid-column rule meant
   for this was enough to wreck that. */
.r-top{grid-column:1/-1;font-size:.75rem;color:var(--dim);text-align:right;
   white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.empty{margin:2rem 0;font-size:.875rem;color:var(--dim);font-style:italic}
""" + FOOTER_BOX_CSS + FOOTER_LINK_CSS + """@media screen{
}
/* Same lesson as the report tables: stack instead of squeezing columns, so
   the rules still run the full width and nothing has to be hidden. */
@media screen and (max-width:620px){
  /* Every list row stacks into one column here and the due and venue rows
     take a two-column area layout, so there are no columns left for a column
     header to label. It goes rather than pretending: a header standing over
     stacked rows is a claim about an alignment that is not there. The song
     pages already hide their .head below 820px for the same reason.

     All three selectors named, not just `.lhead`. The due and venue headers
     are matched by `.lhead.due-h` and `.lhead.vn-h`, two classes against one,
     so a bare `.lhead{display:none}` loses on specificity and both pages kept
     a three-column header over two-column rows. Measured, not assumed: the
     rule was written, the media query was active at 440px, and the computed
     display was still `grid`. */
  .lhead,.lhead.due-h,.lhead.vn-h{display:none}
  .row{grid-template-columns:1fr;column-gap:0;row-gap:.15rem;padding:.6rem 0}
  .r-stats{display:block;text-align:left;white-space:normal}
  .r-stats .st{display:inline;white-space:normal}
  /* Before each but the first, never after: the last .st is not the last
     child -- the song name follows it -- so a trailing separator was left
     stranded at the end of the line with the name wrapped beneath it. */
  .r-stats .st:empty{display:none}
  /* --dim, not --rule: rule is a hairline color and a glyph drawn in it is
     invisible on the dark paper, the way the separators were. */
  .r-stats .st:not(:empty) ~ .st:not(:empty)::before{content:"\\00b7";
    color:var(--dim);opacity:.7;margin:0 .4rem 0 .35rem}
  .r-stats .st b{min-width:0!important;text-align:left}
  /* white-space, and it is the reason this rule is three declarations rather
     than two. The wide layout gives .r-top a column of its own and clips the
     overflow with an ellipsis, so nowrap is right up there. Down here it is an
     inline run inside a paragraph, and nowrap made one row as wide as its
     longest song title: "She Caught the Katy and Left Me a Mule to Ride" is 45
     characters, which is 344px of mono at the old size and 389px at the new
     one. The index was six pixels from scrolling sideways at 375px before the
     scale went up a step, and 33 past it afterwards -- so the type change did
     not cause this, it collected on it. */
  .r-top{text-align:left;display:inline;white-space:normal}
  .r-top::before{content:" ("}
  .r-top::after{content:")"}
  /* Two across, whatever the wide layout asked for. The flex basis that used
     to be here stopped meaning anything when the hero became a grid. */
  .hero-c3,.hero-c4{grid-template-columns:repeat(2,1fr)}
  .card{padding:.65rem .55rem}
  .card:nth-child(odd){border-left:0;padding-left:0}
  .card:nth-child(n+3){border-top:1px solid var(--rule)}
  .num{font-size:1.5rem}
  .lbl{font-size:.625rem;letter-spacing:.14em}
  .show{font-size:.75rem;letter-spacing:0}
  .count{margin-left:0}
  .theme{order:1;flex-basis:100%}
}
""" + TOTOP_CSS

# Filtering is progressive enhancement: the rows are in the HTML, so the page
# is a complete list with JavaScript off. The haystack lives in a data
# attribute per row, which keeps the page one file with nothing to fetch.
INDEX_JS = """
(function(){
  var list=document.getElementById('list');
  if(!list) return;
  var rows=Array.prototype.slice.call(list.children);
  var q=document.getElementById('q'), sort=document.getElementById('sort'),
      shown=document.getElementById('shown'), empty=document.getElementById('empty'),
      clear=document.getElementById('clear'),
      chips=Array.prototype.slice.call(document.querySelectorAll('.chip')),
      era='';
  // Only the eras and the sorts the page actually offers. A hand-typed
  // ?era=90s matching no chip would otherwise hide every row at once, with
  // nothing on screen saying why and no lit chip to click back off.
  var eraOK={}, sortOK={};
  chips.forEach(function(c){ eraOK[c.getAttribute('data-era')]=1; });
  Array.prototype.forEach.call(sort.options, function(o){ sortOK[o.value]=1; });
  /* Terms are whitespace-separated, except inside double quotes, where the
     whole run is one term and has to appear together. Unquoted words are
     ANDed substrings and can match in any order and any field, which is what
     makes partial typing work -- and is also why "Key Arena" unquoted returns
     eight shows rather than the one played there, and why the two rooms named
     The Wharf Amphitheater and Amphitheater at the Wharf each answer for the
     other. A quoted phrase is the way to ask for a room by name. */
  function terms(s){
    var out=[], re=/"([^"]*)"|(\\S+)/g, m;
    while((m=re.exec(s))){
      var quoted=m[1]!==undefined, t=(quoted?m[1]:m[2]).toLowerCase().trim();
      if(t) out.push(matcher(t, quoted));
    }
    return out;
  }
  // A bare number means that number: searching 8 should find the 8th, not the
  // 18th. Inside quotes it is just text, because the reader has said so.
  function matcher(t, quoted){
    if(quoted||!/^\\d+$/.test(t)) return function(hay){ return hay.indexOf(t)>-1; };
    var re=new RegExp('(^|[^0-9])'+t+'([^0-9]|$)');
    return function(hay){ return re.test(hay); };
  }
  function apply(){
    var ts=terms(q.value), n=0;
    rows.forEach(function(r){
      var hay=r.getAttribute('data-search'), ok=ts.every(function(t){
        return t(hay);
      });
      if(ok&&era) ok=r.getAttribute('data-era')===era;
      r.hidden=!ok;
      if(ok) n++;
    });
    shown.textContent=n;
    empty.hidden=n>0;
    // The way out of a filter appears only once there is one to leave. This
    // line referred to an undeclared `clear` for as long as it has existed --
    // copied from the song page without the element or the declaration that
    // make it work there. Every keystroke threw a ReferenceError; nothing
    // showed because apply() had already done all its visible work by this
    // point, and there was nothing after it to lose.
    if(clear) clear.hidden=!q.value;
  }
  // The order the rows are actually in, so a page load in the order the server
  // already rendered does not re-append all 691 of them to prove it.
  var ordered='newest';
  function order(){
    var k=sort.value;
    if(k===ordered) return;
    // An absent rating sorts last rather than as zero: four shows have none,
    // and they are unrated, not badly rated.
    function num(r,attr){ var v=r.getAttribute(attr); return v===''?-1:+v; }
    rows.slice().sort(function(a,b){
      if(k==='gap') return num(b,'data-longest')-num(a,'data-longest');
      if(k==='songs') return num(b,'data-songs')-num(a,'data-songs');
      if(k==='rated') return num(b,'data-score')-num(a,'data-score');
      var x=a.getAttribute('data-date'), y=b.getAttribute('data-date');
      return k==='oldest' ? x.localeCompare(y) : y.localeCompare(x);
    }).forEach(function(r){ list.appendChild(r); });
    ordered=k;
  }

  /* The search is how this archive is read, and none of it was addressable:
     81 shows at MSG, 171 with a Tweezer, 33 in 2015 -- every one a state you
     can reach and cannot send to anybody. q, era and sort now ride in the
     query string.

     Typing replaces rather than pushes. One history entry per character would
     bury the back button -- eight presses to leave a search you typed once.
     A chip and the sort are each a single deliberate act, so those push, and
     back undoes them one at a time. */
  var HIST=!!(window.history&&window.history.replaceState);
  function write(push){
    if(!HIST) return;
    var p=[];
    if(q.value) p.push('q='+encodeURIComponent(q.value));
    if(era) p.push('era='+encodeURIComponent(era));
    if(sort.value!=='newest') p.push('sort='+encodeURIComponent(sort.value));
    // A bare path when nothing is filtered, so the front door keeps a clean
    // URL rather than growing ?q=&era=&sort= just from being looked at.
    var url=location.pathname+(p.length?'?'+p.join('&'):'')+location.hash;
    try{ window.history[push?'pushState':'replaceState'](null,'',url); }
    catch(e){}          // opaque origins (file://) refuse; the page still works
  }
  function read(){
    var out={};
    location.search.replace(/^\\?/,'').split('&').forEach(function(kv){
      if(!kv) return;
      var i=kv.indexOf('='), k=i<0?kv:kv.slice(0,i), v=i<0?'':kv.slice(i+1);
      try{ out[decodeURIComponent(k)]=decodeURIComponent(v.replace(/\\+/g,' ')); }
      catch(e){}        // a stray % is a bad query string, not a broken page
    });
    return out;
  }
  // The page follows the URL, rather than only ever writing to it -- which is
  // what makes both a pasted link and the back button land in the same state.
  function restore(){
    var st=read();
    q.value=st.q||'';
    era=st.era&&eraOK[st.era]?st.era:'';
    sort.value=st.sort&&sortOK[st.sort]?st.sort:'newest';
    chips.forEach(function(c){
      c.classList.toggle('on', c.getAttribute('data-era')===era);
    });
    order();
    apply();
  }

  /* Two timers, because the two jobs a keystroke starts want different delays.

     The filter is a style and layout recalc over every row: 22 ms at 690
     shows, and about 68 ms projected at the 2,100 the 1983 backfill would
     bring. At 80 ms it still reads as instant and a fast typist gets one pass
     per word rather than one per character.

     The URL write is a history entry replacement, which browsers rate limit --
     Safari allows roughly 100 in 30 seconds and throws once you pass it. It
     waits longer because nobody copies a URL mid-word, and coalescing a whole
     word into one entry keeps a long search well clear of the ceiling. */
  var filterT=0, urlT=0;
  function later(){
    clearTimeout(filterT); clearTimeout(urlT);
    filterT=setTimeout(apply, 80);
    urlT=setTimeout(function(){ write(false); }, 400);
  }
  // Clearing and landing are single acts, not typing: they take effect at
  // once, and cancel anything a half-typed word left pending.
  function now(){ clearTimeout(filterT); clearTimeout(urlT); apply(); write(false); }
  function setQuery(v){ q.value=v; now(); }
  q.addEventListener('input', later);
  sort.addEventListener('change', function(){ order(); write(true); });
  chips.forEach(function(c){
    c.addEventListener('click', function(){
      era = c.classList.contains('on') ? '' : c.getAttribute('data-era');
      chips.forEach(function(o){ o.classList.toggle('on', o.getAttribute('data-era')===era); });
      apply();
      write(true);
    });
  });
  if(clear) clear.addEventListener('click', function(){ setQuery(''); q.focus(); });
  document.addEventListener('keydown', function(e){
    if(e.key==='/' && document.activeElement!==q){ e.preventDefault(); q.focus(); }
    if(e.key==='Escape' && document.activeElement===q){ setQuery(''); q.blur(); }
  });
  window.addEventListener('popstate', restore);
  q.disabled=false; sort.disabled=false;
  chips.forEach(function(c){ c.disabled=false; });
  // Whatever the link asked for, before the first paint the reader sees.
  restore();
})();
"""

INDEX_SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Possum Logic</title>
<meta property="og:type" content="website">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}{ago_js}{new_rows_js}</head><body id="top"><div class="wrap">
<a class="skip" href="#main">Skip to content</a>
{crumb}
<div class="rule2"></div>
<header><h1>Possum <em>Logic</em></h1>
<p class="show">{subtitle}</p></header>
{onstage}
<section class="hero {hero_cls}">{hero}</section>
{aside}
<div class="rule2"></div>
<div class="tools" id="main" tabindex="-1">
<div class="tools-main">
<input id="q" class="search" type="search" autocomplete="off" disabled
       placeholder="Search date, venue, city, song, year&hellip;" aria-label="Search reports">
<button id="clear" class="clear" type="button" hidden>Clear</button>
<label class="count" for="sort">Sort
<select id="sort" class="sort" disabled>
<option value="newest">Newest</option><option value="oldest">Oldest</option>
<option value="gap">Longest gap</option><option value="songs">Most songs</option>
<option value="rated">Highest rated</option></select></label>
<span class="count"><b id="shown">{count}</b> of {count} shows</span>
</div>
<div class="chips">{years}</div>
</div>
<div class="lhead"><span>Date</span><span>Venue</span>
<span class="r-stats"><span>Songs</span><span>Median</span><span>Longest</span></span></div>
<ol class="reports" id="list">
{rows}
</ol>
<p class="empty" id="empty" hidden>No shows match that search.</p>
{totop}
""" + footer_html() + """
{analytics}
</div><script>{js}</script></body></html>
"""


def summarize(report):
    """The handful of fields the index needs out of a full report."""
    gaps = [s["gap"] for s in report["songs"] if s["gap"] is not None]
    longest = max(gaps) if gaps else None
    titles = [s["song"] for s in report["songs"]]
    venue, place = report.get("venue_name"), ", ".join(
        p for p in (report.get("city"), report.get("state")) if p)
    if not venue:
        # Reports saved before venue/city/state were split out on their own.
        parts = [p.strip() for p in (report.get("venue") or "").split(",")]
        venue, place = (parts[0] if parts else ""), ", ".join(parts[1:])
    return {
        "date": report["date"],
        "live": bool(report.get("provisional")),
        "venue": venue,
        "place": place,
        "tour": report.get("tour") or "",
        "songs": len(report["songs"]),
        "median": _median(gaps),
        "longest": longest,
        "longest_song": next((s["song"] for s in report["songs"]
                              if s["gap"] == longest), "") if gaps else "",
        "titles": titles,
        # phish.net's own score, by way of fouldomain. 707 of 711 shows carry
        # one, which is enough for it to be a way of ordering the archive.
        "rating": report.get("pnet_rating"),
    }


def _date_aliases(iso):
    """The other ways somebody might type a date into the search box.

    The archive only ever spells dates YYYY-MM-DD, so searching 7/24 or
    "july 24" would otherwise come up empty. Cheaper to widen the haystack
    than to teach the query parser about date formats.
    """
    try:
        d = datetime.date.fromisoformat(iso)
    except ValueError:
        return ""
    return " ".join((
        "%02d/%02d/%d" % (d.month, d.day, d.year),
        "%d/%d/%d" % (d.month, d.day, d.year),
        "%d/%d/%02d" % (d.month, d.day, d.year % 100),
        "%02d/%02d" % (d.month, d.day),
        "%d/%d" % (d.month, d.day),
        "%d-%d" % (d.month, d.day),
        # Both day spellings: "jul" still matches "july", and the unpadded one
        # is what lets a whole-number search for 8 find the 8th.
        d.strftime("%B %d %Y"),
        "%s %d" % (d.strftime("%B"), d.day),
        # The weekday is on the song pages anyway, and putting it in the
        # haystack makes "never miss a Sunday show" a search rather than a
        # saying. "sun" is a prefix of "sunday", so one spelling covers both.
        d.strftime("%A"),
    ))


def typographic(text):
    """A straight apostrophe becomes the right single quote.

    The display face has 149 codepoints and U+0027 is not among them, while
    U+2019 is -- so "Mike\u2019s Song" set in Bagnard drops the apostrophe or
    falls back to another face mid-word, visibly, on 35 of 587 song titles.
    U+2019 is the correct mark for an English apostrophe regardless of which
    face is in use, so this is worth doing even if the face changes.
    """
    return (text or "").replace("'", "\u2019")


def neighbors(perfs, counting=None, top=3):
    """What this song most often came out of and went into.

    Every row on a song page already names both, and nothing has ever added
    them up -- which is the question this audience asks most: what does Tweezer
    come out of? Counted over performances that count toward a gap, so a
    soundcheck pairing does not enter a statistic the rest of the site would
    not recognize.

    -> ([(song, n), ...] before, [(song, n), ...] after)
    """
    before, after = collections.Counter(), collections.Counter()
    for p in perfs:
        if counting and p.get("date") not in counting:
            continue
        if p.get("prev"):
            before[p["prev"]] += 1
        if p.get("next"):
            after[p["next"]] += 1
    # A pairing seen once says nothing; it is a coincidence with a name.
    keep = lambda c: [(s, n) for s, n in c.most_common(top) if n > 1]
    return keep(before), keep(after)


def _clock(iso):
    """A bare HH:MM fallback for a stamp that JavaScript will make relative."""
    return html.escape(iso[11:16]) if iso else ""


def ambiguous_tours(reports):
    """Tour names that are a substring of another tour name.

    A tour link is a quoted phrase search, and a quoted phrase is exact only if
    no other name contains it. Measured over the archive: **2011 NYE** is inside
    **2010/2011 NYE Run**, so linking it returned nine shows for a four-show
    run. One of sixty-two, and the only one -- but this is the failure §8b.4
    predicted for the venue links and it has now actually happened, on tours
    rather than on rooms.

    So the name is checked rather than trusted. A tour that cannot be searched
    for exactly is left as plain text, which is what it was yesterday: the site
    would rather say nothing than send a reader somewhere with the wrong shows
    in it.
    """
    names = {r.get("tour") or "" for r in reports}
    names.discard("")
    return {a for a in names if any(a != b and a in b for b in names)}


def search_href(phrase, root="../"):
    """The index, filtered to one exact phrase.

    Quoted, always. Measured on the venues page when these links were first
    built: unquoted, 6 of 153 venues returned somebody else's shows -- "Key
    Arena" matched eight, being any arena with a "key" anywhere in its setlist,
    and the two Wharf amphitheatres each answered for the other. The quoting is
    the whole correctness of this link, so it lives in one function rather than
    in every caller.
    """
    return "%sindex.html?q=%s" % (
        root, urllib.parse.quote('"%s"' % phrase, safe=""))


def _venue_lines(report):
    """The venue and its locality as two elements, with no comma between them.

    One flat string could not be made to wrap well. The masthead puts the date
    in an auto-sized grid column, so the venue's column is whatever is left --
    258px at 1280 and 187px at 1000, never more however wide the window. Long
    venues therefore always wrap, and the comma joining venue to city was
    stranded at the end of a line every time: "MADISON SQUARE GARDEN," above
    "NEW YORK, NY", and at 1000px a second orphan a line further up.

    No CSS can detect a wrap, so the separator has to stop existing. The index
    rows already solved this -- venue and place as two elements, no comma --
    and this is that pattern. Wide: two lines, the locality quieter. Narrow:
    one line joined by a middot, where the whole string fits anyway.
    """
    venue = report.get("venue_name") or ""
    place = ", ".join(p for p in (report.get("city"), report.get("state")) if p)
    if not venue:
        # Reports saved before venue/city/state were stored separately.
        parts = [p.strip() for p in (report.get("venue") or "").split(",")]
        venue, place = (parts[0] if parts else ""), ", ".join(parts[1:])
    # The venue is a search too -- the same link venues.html gives it, so a
    # reader who wants the other nights in this room does not have to go via a
    # third page to ask. The locality is not linked: it is context for the
    # venue rather than a thing to browse, and two links in a two-line block
    # would make the block read as a list of destinations.
    return ("<span class='v-name'><a href='%s'>%s</a></span>"
            "<span class='v-place'>%s</span>"
            % (search_href(venue, root="../"), html.escape(venue),
               html.escape(place)) if venue else
            "<span class='v-name'></span><span class='v-place'>%s</span>"
            % html.escape(place))


def _full_weekday(iso):
    """Saturday, Sunday... spelled out.

    The index abbreviates because it repeats the word 710 times down a column
    and the abbreviation is unambiguous there. A masthead says it once, so it
    can say it properly.
    """
    try:
        return datetime.date.fromisoformat(iso).strftime("%A")
    except ValueError:
        return ""


def weekday(iso):
    """Sun, Mon, Tue... for a date the archive spells YYYY-MM-DD."""
    try:
        return datetime.date.fromisoformat(iso).strftime("%a")
    except ValueError:
        return ""


def hero_cols(n):
    """How many columns a hero of n cards wants.

    Four across is the widest that keeps a five-figure number on one line at
    the page's measure, so anything past four goes to three and wraps.

    Three cards ask for three columns, not four. The old test only looked
    upward -- anything not past four got the four-column grid -- which was
    right for every hero that existed when it was written and wrong the moment
    one lost a card: three cards in a four-track grid leave a quarter of the
    row empty with the hero's bottom rule running on under nothing.
    """
    return "hero-c4" if n == 4 else "hero-c3"


def tied_with(rest):
    """The tail of a card's sub-label when a superlative is shared.

    "", ", tied with Gone", ", tied with 3 others". One function because two
    heroes need it and the whole point of stating a tie is that both pages
    state it the same way.
    """
    if not rest:
        return ""
    if len(rest) == 1:
        return ", tied with %s" % rest[0]
    return ", tied with %d others" % len(rest)


def hero_html(cards):
    """One hero, from (value, label, class, href[, sub-label]) per card.

    Five functions built this string from five copies of the same two lines,
    and they had already drifted: three escaped the href and two did not, on
    pages whose hrefs come from song slugs and venue names. One copy now.

    The fifth field is the name under the label -- which song, or which night,
    a superlative belongs to. It is passed rather than written into the label
    because a card that carries one has to say so in its markup: that is what
    moves the arrow off the end of the label and onto the name, where the link
    actually goes. Doing it in CSS instead would mean `:has(.of)`, and a
    selector a browser does not understand is dropped in silence -- leaving the
    old arrow where it was and adding a second one under it.
    """
    out = []
    for card in cards:
        val, lbl, cls, href = card[:4]
        of = card[4] if len(card) > 4 else ""
        klass = "card named" if of else "card"
        out.append(
            ("<a class='%s' href='%s'>" % (klass, html.escape(href, quote=True))
             if href else "<div class='%s'>" % klass)
            + "<div class='lbl'>%s%s</div><div class='num%s'>%s</div>"
            % (lbl, "<span class='of'>%s</span>" % html.escape(of) if of else "",
               cls, val)
            + ("</a>" if href else "</div>"))
    return "".join(out)


def render_index(reports, page_href="./show/%s.html", card=None, aside=(),
                 n_due=None):
    """A single self-contained index page over every saved report."""
    entries = sorted((summarize(r) for r in reports),
                     key=lambda e: e["date"], reverse=True)

    rows = []
    for e in entries:
        # Everything worth searching, flattened into one lowercase haystack.
        hay = " ".join([e["date"], _date_aliases(e["date"]),
                        e["venue"], e["place"], e["tour"]]
                       + e["titles"]).lower()
        # Each figure in its own cell rather than one right-aligned run of
        # text. Right-aligning the whole string only pins its right edge: with
        # 16 songs against 26, and a longest of 45 against 1,468, every other
        # number in the line sat at a different place on every row.
        stats = "<span class='st'><b>%d</b> songs%s</span>" % (
            e["songs"], " <span class='live-tag'>so far</span>" if e["live"] else "")
        if e["longest"] is not None:
            stats += ("<span class='st'>median <b>%s</b></span>"
                      "<span class='st'>longest <b class='hot'>%s</b></span>"
                      "<span class='r-top'>%s</span>"
                      % (_stat(e["median"]), _stat(e["longest"]),
                         html.escape(e["longest_song"])))
        rows.append(
            "<li data-date='%s' data-year='%s' data-era='%s' "
            "data-longest='%d' data-songs='%d' data-score='%s' "
            "data-search=\"%s\">"
            "<a class='row' href='%s'>"
            "<span class='r-date'>%s</span>"
            "<span class='r-where'><span class='r-venue'>%s</span>"
            "<span class='r-place'>%s</span></span>"
            "<span class='r-stats'>%s</span></a></li>"
            % (e["date"], e["date"][:4], era(e["date"]), e["longest"] or 0,
               e["songs"], "" if e["rating"] is None else e["rating"],
               html.escape(hay, quote=True),
               html.escape(page_href % e["date"], quote=True),
               e["date"], html.escape(e["venue"]), html.escape(e["place"]),
               stats))

    # Eras rather than years. A year chip per year was fine at six and is not
    # at eighteen; the full archive would put more than forty buttons above the
    # list, which is a wall rather than a filter. The eras are four, they are
    # the divisions the band's own audience uses, and the site already teaches
    # them on song pages. A year is still reachable -- typing it in the search
    # box filters to it, because the date is in the haystack.
    order = [label for label, _, _ in ERAS]
    present = sorted({era(e["date"]) for e in entries}, key=order.index)
    counts = collections.Counter(era(e["date"]) for e in entries)
    chips = "" if len(present) < 2 else "".join(
        "<button class='chip' type='button' disabled data-era='%s'>"
        "%s <span class='chip-n'>%d</span></button>" % (x, x, counts[x])
        for x in present)

    # A figure in the hero that cannot be followed is an advertisement for a
    # page that does not exist. The show holding the longest gap is a page the
    # site already builds, so the number points at it rather than just sitting
    # there being large.
    #
    # Every night holding it, not just one. This card was correct only by
    # accident: `max()` returns whichever tied entry it met first and states it
    # as the answer, and today exactly one of the 692 reports holds 1,468 --
    # Gone's 1,468 on 2009-12-30 is a song history rather than an archived
    # report, so it never reached this list. The songs index *is* tied, which
    # is how the shape was found there first; as the backfill runs, the same
    # tie arrives here. Fixed before it fires rather than after: the card names
    # the most recent night, links to it, and says how many others there are.
    #
    # Naming the night is also the answer to a second thing wrong with the
    # card, which is that it said "1,468" and pointed somewhere without saying
    # where. Most recent first among equals, because the ordering has to come
    # from the data and a date is the one thing every tied show differs on.
    top_gap = max((e["longest"] for e in entries if e["longest"]), default=None)
    holders = sorted((e for e in entries if e["longest"] == top_gap),
                     key=lambda e: e["date"], reverse=True) if top_gap else []
    peak = holders[0] if holders else None
    # The fullest night is deliberately *not* a hero card. It was one, and it
    # is the wrong thing for that slot: once the backfill reaches 1999-12-31 it
    # becomes Big Cypress and never moves again, so a permanently fixed number
    # would sit among five that change with every show. It is a fine fact and a
    # bad headline. It is reachable instead by sorting the archive on it, along
    # with the rating -- which answers the same kind of question and could not
    # be asked here at all before.
    #
    # There was a fifth card here, "Song Performances", and it went for two
    # reasons at once. The first is Ian's: five cards is a three-and-two hero,
    # which is the ugliest shape the grid makes, and this was the card the
    # page could most afford to lose. The second is worse and is why this one
    # went rather than another. It summed every song slot across the reports
    # *this page lists* -- 14,062 of them -- carried the same label as the
    # songs index and linked straight to it, and that page says 37,169,
    # because it counts every performance in every song's history across all
    # 2,108 counted shows rather than the 692 written up here. One label, two
    # populations, 2.6x apart, and a link from the smaller to the larger. It
    # is the "Songs Logged" bug from a year ago exactly: that one was fixed by
    # renaming the label, which left the two figures still disagreeing. A
    # number that contradicts the page it points at is worse than no number,
    # and the nav already carries a door to the songs index.
    cards = [
        (len(entries), "Reports", "", ""),
        (_stat(peak["longest"]) if peak else "n/a", "Longest Gap", " hot",
         page_href % peak["date"] if peak else "",
         (peak["date"] + tied_with([e["date"] for e in holders[1:]]))
         if peak else ""),
        # Was Venues, and went for the same reason the card above it names:
        # the nav carries a door to the venues page from every page on the
        # site, so a hero cell spending itself on that destination is spending
        # the widest row on the front page to repeat the strip above it. Not a
        # show has no nav entry at all now that the strip is four browse
        # spines -- this card and the note below it are its only two doors,
        # and it is the one destination here that needs one.
        (len(aside), "Not a Show", "", "./" + NOT_A_SHOW_PAGE),
    ]
    # What is overdue going into tonight, counted once by due_rows() and shown
    # here only if the due page was actually built -- a card offering a figure
    # and a link to a page that is not there is worse than no card.
    if n_due is not None:
        cards.append((n_due, "Songs Due", " hot", "./due.html"))
    hero = hero_html(cards)

    # Not concerts, and kept off the list above rather than out of the site:
    # the pages exist, the gap figures on them do not describe a show, and a
    # soundcheck's whole reason for existing is the concert it precedes.
    #
    # It was a twenty-row list at the foot of 692, which is where a reader who
    # has scrolled the entire archive finds it and nowhere else. Ian: "move the
    # 'also on file' listings to a higher prominence home, or at least
    # something that's not tacked onto the end of the show list." So the list
    # is a page now and this is one line under the hero, before the search box
    # rather than after everything -- and the page can say the things a tail
    # block could not, which is what it is for.
    aside_html = ""
    if aside:
        # The count, and the kinds named rather than counted. Counting them
        # here meant restating a breakdown that changes when phish.net files
        # something new -- and it published "0 television or radio sessions"
        # the first time the kinds were split, because it was reading a bucket
        # that had been emptied into three others.
        aside_html = (
            "<p class='aside'>Also on file: <b>%d</b> performances that were "
            "not shows &mdash; soundchecks, a tech rehearsal, television and "
            "radio tapings, one ceremony &mdash; which phish.net lists and "
            "does not count toward a gap, so neither does this site. "
            "<a href='./%s'>What was played at them</a>.</p>"
            % (len(aside), NOT_A_SHOW_PAGE))

    # A show being played is the reason to be here tonight, and a "so far"
    # tag on one row among 690 is not a way of saying so. The whole block is
    # the link, because the front door failing to reach the live page is the
    # failure this exists to fix.
    onstage = ""
    live_now = [e for e in entries if e.get("live")]
    if live_now:
        e = live_now[0]
        onstage = ("<a class='onstage' href='%s'>"
                   "<span class='k'>On stage now</span>"
                   "<span class='w'>%s<span class='p'>%s</span></span>"
                   "<span class='n'><b>%d</b> song%s so far</span></a>"
                   % (html.escape(page_href % e["date"], quote=True),
                      html.escape(e["venue"]), html.escape(e["place"]),
                      e["songs"], "" if e["songs"] == 1 else "s"))

    plural = "" if len(entries) == 1 else "s"
    if entries:
        span = ("%s &rarr; %s" % (entries[-1]["date"], entries[0]["date"])
                if len(entries) > 1 else entries[0]["date"])
        subtitle = "%d report%s &middot; %s" % (len(entries), plural, span)
        blurb = "Per-song gaps for %d Phish show%s, %s to %s." % (
            len(entries), plural, entries[-1]["date"], entries[0]["date"])
    else:
        subtitle, blurb = "No reports yet", "Per-song gaps for Phish shows."

    return INDEX_SHELL.format(
        crumb=nav_strip(here="Shows"),
        ago_js=AGO_JS,
        new_rows_js=NEW_ROWS_JS,
        analytics=ANALYTICS,
        css=INDEX_CSS, js=INDEX_JS, totop=TOTOP_JS, theme_js=THEME_JS, keys_js=KEYS_JS, theme_ui=THEME_UI,
        fonts=WEB_FONTS, sheet=sheet_links("./%s/%s" % (STATIC_DIR, SITE_SHEET)),
        hero=hero, hero_cls=hero_cols(len(cards)), years=chips,
        count=len(entries), rows="\n".join(rows) or "",
        aside=aside_html, subtitle=subtitle, onstage=onstage,
        share=share_meta("Possum Logic", html.escape(blurb, quote=True),
                         card=card),
        # The newest show it lists, for the same reason.
        stamp="Updated %s" % (entries[0]["date"] if entries else "&mdash;"))


# ------------------------------------------------------------------- song ---

# Alfa Slab One has one weight and it is a poster weight: right for a wordmark
# and for a bare number, too heavy for a date string, which has twice the
# characters and three pieces of punctuation. Aleo carries the dates and the
# song title; the gap figures and the hero numbers stay in the slab.
SONG_FONTS = WEB_FONTS

SONG_CSS = (BASE_CSS + BODY_BOX_CSS + NAV_CSS + """/* One of the three slots the display face is allowed: the wordmark, a show's
   date, and a song's name. Nowhere else. */
h1{font-family:'Bagnard',Georgia,serif;font-weight:400;
   font-size:clamp(1.7778rem,6.5vw,3.0222rem);line-height:1.14;margin:0 0 .5rem;
   letter-spacing:-.01em}
.show{margin:0;font-size:.75rem;font-weight:600;letter-spacing:0;
   text-transform:uppercase;color:var(--ink-soft)}
/* Two equal columns, not flex. Flex sized each card by its content, so the
   rule that strips the first card's left padding made that card 21px narrower
   than its siblings at every width -- correct under a grid, where the column
   stays 1fr and only the content moves flush left, and wrong here, where it
   moved the box. Measured 254 against 275 at 1280px, 174 against 195 at 860.
   Two columns also have no bad arrangement: the five cards this replaced went
   3+2 on the index's grid and onto one crammed line here. */
""" + RULE2_CSS + """.hero{display:grid;grid-template-columns:repeat(2,1fr);
   margin:.7rem 0 .3rem;border-bottom:1px solid var(--ink)}
/* A one- or two-performance song still gets the old pair of narrow cards. */
.hero.sparse{grid-template-columns:repeat(2,1fr)}
.card{padding:.85rem 1.1rem;border-left:1px solid var(--rule);
   display:flex;flex-direction:column;min-width:0}
.card:first-child{border-left:0;padding-left:0}
.num{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;font-size:2.25rem;line-height:1;
   letter-spacing:0;margin-top:auto}
/* The second half of each pair. It is the reason two cards can carry what five
   did: the medians are one statistic over two windows and the gaps are one
   distance at two moments, so the older reading belongs under the newer one
   rather than in a card of its own. Also what fills the measure a bare number
   left empty, which is what made two cards read as a hero and not as three
   missing ones. */
.card .sub{margin-top:.3rem;font-size:.6875rem;letter-spacing:.04em;
   color:var(--dim);text-transform:none;line-height:1.35}
.card .sub b{font-weight:600;color:var(--ink-soft)}
/* The debut card goes to the debut's own row. SONG_CSS had no `a.card` rules
   at all -- this is the one sheet where a card had never been a link -- and
   writing them out here would have made an exact third copy of the show
   sheet's block, so they were named instead. Down-arrow, not the index's
   right: the destination is on this page. */
""" + CARD_LINK_CSS + """a.card .lbl::after{content:" \\2193";color:var(--dim);white-space:nowrap}
/* A date rather than a count: ten characters where every other figure on this
   row is one to five, so it is set down a step. Only reachable on a
   one-performance page, where the hero is two cards and there is half the
   measure to spend on it -- five across it would wrap at 900, 1024 and 375. */
.num.when{font-size:1.75rem}
""" + FIGURE_CSS + """.lbl .abbr{display:none}
/* The best version gets a line rather than a fifth card: it is a date, a
   place, a score and two links, none of which fit a card built for one
   number. */
/* A stub, not a callout. The tinted panel with a colored left border was the
   one object on the site that looked like a framework component; it reads in
   the same field language as the row above it now -- label, value, no fill. */
.best{display:flex;flex-wrap:wrap;align-items:baseline;gap:.35rem 1.1rem;
   margin:.7rem 0 0;padding:0 0 .7rem;border-bottom:1px solid var(--rule);
   font-size:.875rem}
.best .cap{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim)}
/* One flowing line rather than a row of stacked label/value columns. .field
   is gone with the three captions that justified it; .v wraps as prose so a
   narrow screen breaks it between middots instead of stacking four boxes. */
.best .v{display:inline}
.best .when{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;font-size:1rem}
.best .score{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;color:var(--hot-text);
   font-size:1.25rem;line-height:1}
.best .where{color:var(--dim)}
.best a{color:var(--ink);text-decoration:none;border-bottom:1px solid var(--rule)}
.best a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* Up under the title, and captioned. These are links about the *song*, and
   they used to sit directly beneath the best-version block -- so Ian read them
   as being about that one performance and could not tell without clicking.
   Two things were wrong and both are fixed here: they were adjacent to the
   wrong thing, and they named no referent. Moving them alone would have cured
   only the instance. */
.links{margin:.55rem 0 0;display:flex;flex-wrap:wrap;align-items:center;
   gap:.4rem .55rem}
.links .cap{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim)}
.badge{display:inline-flex;align-items:center;gap:.35rem;line-height:1;
   padding:.35rem .5rem;border:1px solid var(--edge);color:var(--dim);
   text-decoration:none;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase}
.badge img{display:block;width:13px;height:13px}
.badge:hover{color:var(--ink);border-color:var(--ink-soft)}
/* Below the best version now, beside the list it summarizes: "most often out
   of / into" is a reading of the Before / after column, so it belongs next to
   that column rather than between the title and the figures. */
.pairs{margin:1.4rem 0 0}
.tools{display:flex;flex-wrap:wrap;align-items:center;gap:.55rem .8rem;
   margin:1.9rem 0 .9rem}
.search{flex:1 1 15rem;min-width:0;font:inherit;font-size:.875rem;
   padding:.5rem .7rem;border:1px solid var(--edge);border-radius:0;
   background:transparent;color:var(--ink)}
.search::placeholder{color:var(--dim)}
.search:focus-visible,.sort:focus-visible{outline:2px solid var(--hot);
   outline-offset:1px}
""" + SELECT_CSS + """.count{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim);margin-left:auto}
/* Jump to an era, with how many shows are in it. Anchors, so they work with
   scripting off and survive a reload. */
.eras{display:flex;flex-wrap:wrap;align-items:center;gap:.3rem}
/* Captioned, because "4.0 42" beside a sort control reads as a filter with an
   unexplained number, and nobody outside the fandom knows 4.0 is an era. */
.eras-cap{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim);margin-right:.15rem}
.era-chip{display:inline-flex;align-items:baseline;gap:.3rem;
   font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   padding:.42rem .55rem;border:1px solid var(--edge);color:var(--dim);
   text-decoration:none}
.era-chip b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:.875rem;letter-spacing:0;color:var(--ink-soft)}
.era-chip:hover{color:var(--ink);border-color:var(--ink-soft)}
.era-chip:hover b{color:var(--hot-text)}
/* Shown only once there is something to clear. */
.clear{font:inherit;font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   padding:.45rem .6rem;border:1px solid var(--edge);background:transparent;
   color:var(--dim);cursor:pointer}
.clear:hover{color:var(--hot-text);border-color:var(--hot-text)}
.clear:focus-visible{outline:2px solid var(--hot);outline-offset:1px}
/* A venue is a filter waiting to happen: click it to see every other night
   the song was played there. */
.r-venue{cursor:pointer}
.r-venue:hover{color:var(--hot-text)}
.count b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:1rem;color:var(--ink)}
.perfs{list-style:none;margin:0;padding:0;border-top:1px solid var(--rule)}
/* Anything a link can land on stops clear of the condensed header, which is
   fixed and 42px tall -- without this the browser puts the target's top edge
   at the top of the viewport, which is exactly where the header is, and the
   row you tapped to look at arrives half hidden underneath it. */
/* Clear of the sticky bar, which is not one height. Below 820px it carries the
   song and its counts and measures 42px; above, it also carries the column
   labels and measures 73px -- against the 57.6px this used to be, which put a
   jumped-to performance 16px underneath the bar meant to orient it. Measured
   at both widths rather than estimated, with room left over so the row has air
   above it rather than being flush to the edge. */
.perfs>li,.perfs>li.yr{scroll-margin-top:3.6rem}
@media screen and (min-width:821px){
  .perfs>li,.perfs>li.yr{scroll-margin-top:5.4rem}
}
.perfs>li{border-bottom:1px solid var(--rule-soft)}
.perfs>li.yr{border-bottom:0}
/* The same tab the set headings take, so a section boundary looks the same
   wherever it falls. */
.yr h2{display:flex;flex-wrap:wrap;align-items:center;gap:.2rem .7rem;
   font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   margin:1.6rem 0 .3rem;padding:0;border:0;color:var(--ink)}
.yr h2 .tab{background:var(--ink);color:var(--paper);padding:.25rem .55rem;
   letter-spacing:.14em;print-color-adjust:exact;-webkit-print-color-adjust:exact}
.yr h2::after{content:"";flex:1;border-bottom:1px solid var(--ink)}
.yr h2 span{font-family:'IBM Plex Mono',monospace;font-size:.625rem;
   letter-spacing:.14em;text-transform:uppercase;color:var(--dim)}
.yr:first-child h2{margin-top:.4rem}
/* Column labels. The date and the venue say what they are; the bar and the
   number on the far right did not, and were left to be guessed at. */
.head{padding-bottom:.35rem;border-bottom:1px solid var(--rule);
   font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim)}
.head .nhead{color:var(--dim)}
/* The marks set in the face the setlists print them in, so the label is a
   specimen of the thing it explains. Underlined like every other link here.

   Its own line, not the tail of the label's: this column is narrow enough that
   inline it wrapped anyway, and a wrap that was going to happen is better
   declared than discovered. `width:max-content` keeps the underline on the two
   marks rather than running the width of the column. */
.head .marks{display:block;width:max-content;margin-top:.15rem;
   font-family:'IBM Plex Mono',ui-monospace,monospace;
   letter-spacing:0;text-transform:none;color:var(--dim);text-decoration:none;
   border-bottom:1px solid var(--rule);white-space:nowrap}
.head .marks:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
.head .ghead{grid-column:4/-1;text-align:right}
/* Every row is its own grid, so an `auto` last column sizes to its own content
   and the gap figures stop lining up: "set 1" is 36px, "encore" 43, "set 2 -
   2x" 71, which put the numbers at three different left edges down the page.
   Fixed width, sized for the longest of them. */
.row{display:grid;grid-template-columns:8.4rem 1fr 9rem 5rem 6.4rem;
   column-gap:1.1rem;align-items:baseline;padding:.6rem .25rem}
/* Not the column header. It wears `.row head` because it needs the same grid
   as the performances beneath it, and so it inherited their hover: it lit up
   exactly like a row and did nothing when clicked, which is an affordance
   promising a target that was never there. Only the song pages carry a
   `.row head` today; the rule is written into both sheets that have `.row`
   so the two cannot drift apart the next time one gains a header. */
.row:not(.head):hover{background:var(--hover)}
/* The row's identifier, in the display face, same as the show index. It is
   the one thing in the row that is not the song. */
.r-date{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:1rem;line-height:1.3rem;white-space:nowrap}
.r-date a{color:inherit;text-decoration:none;
   border-bottom:1px solid var(--rule)}
.r-date a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* One copy of each favicon for the whole page, worn by class.
   No blanket opacity: these icons do not agree about their own. phish.net's is
   fully opaque, phish.in's averages an alpha of 130 and fouldomain's 137, so a
   single .65 on top of all three dimmed the translucent ones to about a third.
   Black at a third reads fine on cream and disappears on near-black, which is
   why phish.in's went missing in the dark and only in the dark. Each is dimmed
   to taste against what it actually ships, and 12px rather than 10 because
   they are detailed marks being drawn very small. */
.ext::after{content:"";display:inline-block;width:12px;height:12px;
   margin-left:.3rem;vertical-align:-1px;
   background-position:center;background-repeat:no-repeat;
   background-size:contain}
.i-pnet::after{opacity:.6}
.i-pin::after,.i-foul::after{opacity:.95}
.ext:hover::after{opacity:1}
.i-pnet::after{background-image:url("data:image/png;base64,__PNET__")}
.i-pin::after{background-image:url("data:image/png;base64,__PIN__")}
.i-foul::after{background-image:url("data:image/png;base64,__FOUL__")}
/* Literata, like every other run of prose on the site. This was mono for no
   reason anybody chose: `body` sets Plex Mono site-wide, and .jam, .note and
   the method page's .prose each opted out where reading matters. The dek never
   did, so a standfirst sat in the figure face. A shade larger than the .75rem
   it was set at, because the serif reads smaller at the same size. */
""" + DEK_CSS + """/* Said where the page explains itself, in the same voice as the gap note above
   it, but marked -- it is a correction to what the numbers appear to mean, not
   more description of them. */
/* What the song sits between, counted over its whole history. Two short rows
   rather than a table: this is context for the list below, not a finding of
   its own, and it earns its place only because the answer is usually
   surprising -- Harry Hood comes out of Hold Your Head Up 31 times. */
/* One grid for both rows, so the two lists start at the same place. As two
   independent flex rows they began wherever their own caption ended, and the
   captions are not the same length -- "out of" against "into" put the two
   lists 14.8px out of line at 760px. The caption column is max-content, so it
   fits the longer of the two and neither row states a width of its own. */
.pairs{margin:.7rem 0 0;display:grid;
   grid-template-columns:max-content minmax(0,1fr);gap:.25rem 1rem}
.pair{display:contents}
.pair .cap{grid-column:1}
/* 1.4rem between pairings rather than .7rem. At the old gap the row read as
   one run of alternating words and numbers -- the space between a song and
   its own count was very nearly the space between two songs. */
.pair .ps{grid-column:2;display:flex;flex-wrap:wrap;gap:.15rem 1.4rem}
.pair .cap{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim)}
.pair .p{font-size:.8125rem;color:var(--ink-soft);white-space:nowrap}
.pair .p b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:.75rem;color:var(--dim);margin-left:.3rem}
.caveat{margin:.6rem 0 0;padding-left:.8rem;border-left:2px solid var(--hot);
   font-family:'Literata',Georgia,serif;font-size:.9375rem;line-height:1.5;
   font-variation-settings:'opsz' 14;color:var(--ink-soft);max-width:58ch}

.dow{display:block;font-family:'IBM Plex Mono',monospace;font-weight:400;
   font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim);line-height:1.1rem}
/* Heavier than the show index's venue, deliberately. There the venue is the
   row's identity repeated 259 times and the weight accumulates into a wall.
   Here every row is the same song, so the venue is the only thing telling one
   performance from the next -- the weight is carrying the distinction rather
   than shouting. The date being in the display face is what keeps the two from
   competing at the same volume. */
.r-venue{font-size:.875rem;font-weight:600;letter-spacing:0;
   text-transform:uppercase;line-height:1.3rem}
.r-place{display:block;color:var(--dim);font-size:.75rem;line-height:1.15rem}
.r-gap{text-align:right;line-height:1.3rem}
/* The column header names this column, so the per-row label would be a second
   answer to a question already answered -- but the header is the first thing
   the narrow layout drops, and there the number was left to be guessed at.
   Shown exactly where the header is not. */
.glabel{display:none;font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim);margin-right:.4rem}
.gap{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;font-size:1rem}
/* The one card whose number arrives after the page does. Same shape as its
   four neighbors so its appearance is a card filling in, not the row
   reflowing around a new one. */
.card.since.over .num{color:var(--hot)}
/* The verdict rides in the label, which the hero can now afford to let wrap:
   the figures hang off a shared bottom edge, so a second line here moves this
   label and nothing else on the row. */
.card.since .v{display:block;text-transform:none;letter-spacing:0}
.card.since .v:not(:empty){margin-top:.1rem}
.card.since .v.quiet,.card.since .v.dim{color:var(--dim)}
.card.since.over .v{color:var(--hot-text);text-transform:uppercase;
   letter-spacing:.14em}
.card.since.dormant .num{color:var(--ink-soft)}
.gap.big{color:var(--hot-text)}
.gap.none{color:var(--dim)}
/* A soundcheck or a television session. It happened and it is listed,
   but phish.net does not count it toward a gap and neither do we, so
   the column says why it is empty rather than leaving a dash to be read
   as missing data. */
.gap.none{font-size:.75rem;letter-spacing:.14em;text-transform:uppercase}
.set{display:block;font-size:.625rem;letter-spacing:.14em;color:var(--dim);
   text-transform:uppercase}
/* What it followed and what it led into, stacked. Sized in ch so the column
   holds a couple of words of song title and truncates the rest rather than
   pushing the gap figures around. */
.nb{font-size:.75rem;line-height:1.25rem;color:var(--dim);min-width:0}
/* Named only where the column header is not doing it. */
.nb .cap{display:none}
/* Direct children only. These are the two lines -- what came before, what
   came after -- and each is its own line. The transition mark now lives in
   a span inside one of them, and a blanket rule here made that mark a
   block too, so a row read "->" and "Golden Age" on separate lines. */
/* Wraps rather than truncates. This track is a fixed 9rem, so `nowrap` plus
   an ellipsis meant a long title was cut at every viewport width and widening
   the window did nothing -- "A Song I Heard the Ocean Sing" was unreadable on
   a 27-inch screen, which is how Ian found it. The comment this replaces said
   the truncation kept the gap figures from being pushed around; it does not,
   because wrapping inside a fixed grid track cannot move the track. It only
   makes that one row taller, which the venue and the notes already do. The
   narrow layout had been overriding this back to `normal` all along, so the
   phone has been showing the full title while the desktop hid it. */
.nb>span{display:block}
/* Doubled backslashes: this is a Python string, and "\2190" is read as the
   octal escape \21 followed by "90", which reaches the browser as a control
   character and renders as a box. */
.nb-in::before{content:"\\2190\\00a0";opacity:.55}
.nb-out::before{content:"\\2192\\00a0";opacity:.55}
/* Where a transition mark is shown it points on its own; the plain arrow is
   only for rows that have none, so no line ever reads "-> ->". */
.nb .seg::before{content:none}
/* The set boundary, named. What is on the far side of a setbreak is a fact,
   so the words carry the ink and the song beside them stays dim -- the label
   is the answer, the song is the detail, and that order survives the column
   truncating. Not bold: this column sits under a gap figure and a bar, and a
   bold line here out-shouts both. */
.nb b{font-weight:400;color:var(--ink)}
/* These two wrap where every other line in the column truncates. The column
   is 162px at any desktop width, and a line of this shape is a sentence, not
   a title: 40 of Tweezer's 50 came out as "Opened set 3, af..." -- the cut
   landing inside "after" rather than inside a song name. Wrapping made 14 of
   that page's 418 rows taller and the page 0.7% longer, which is the whole
   cost. A title still truncates, because half a title is still readable and
   half a preposition is not. */
.nb .edge{white-space:normal}
/* No arrow on a show opener or closer: both name no song, so it would point
   at nothing. Hidden rather than removed, so the slot is still there and
   "Closed the show" starts where "Opened the encore, after ..." above it
   starts. Dropping the slot instead left the two lines of one cell on
   different left edges, which is visible on 3,821 rows. */
.nb .term::before{opacity:0}
/* Same -.06em as the report pages: enough to make -> one mark, not so
   much that it stops matching the > on the row above it. */
.nb .mk.tight{letter-spacing:-.06em}
.bar{align-self:center}
/* The same band the report pages use. This CSS is the half of that change I
   left out the first time: the markup emitted .band, .mid and .at while this
   sheet still described the old fill, so a song page drew an empty track with
   three unstyled spans inside it and looked like nothing at all. */
.bar .track{display:block;position:relative;width:100%;height:14px}
.bar .track::before{content:"";position:absolute;left:0;right:0;top:6px;
   height:2px;background:var(--rule)}
/* No band to draw, so no scale is drawn. A dash where the mark would have
   been, at the same height as the track, says the measurement was never
   possible -- the ghost scale that used to sit here read as a bar that had
   failed to render, and it was the emptiest graphic on the most interesting
   rows. `.bare` is gone with it. */
.bar .no-range{display:block;height:14px;line-height:14px;text-align:center;
   color:var(--dim);opacity:.65;font-size:.75rem}
.bar .band{position:absolute;left:30%;right:30%;top:3px;bottom:3px;
   background:var(--band);opacity:var(--band-opacity);border-radius:1px}
.bar .mid{position:absolute;left:50%;top:1px;bottom:1px;width:2px;
   background:var(--paper);opacity:.85}
.bar .at{position:absolute;left:50%;top:0;bottom:0;width:5px;
   transform:translateX(-50%);background:var(--ink);border-radius:1px;
   box-shadow:0 0 0 2px var(--paper)}
.bar .at.late{background:var(--hot)}
.bar .at.early{background:var(--cool)}
.bar .at.usual{background:var(--ink)}
/* Only the rated versions carry these, which is 25 rows out of however many
   hundred -- and only they are known to have audio, since a version cannot be
   scored until a recording of it circulates. */
.mark{display:block;margin-top:.3rem;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--dim)}
.mark b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:.875rem;color:var(--dim);letter-spacing:0}
.mark.high b{color:var(--hot-text)}
.mark a{color:var(--ink-soft);text-decoration:none;
   border-bottom:1px solid var(--rule)}
.mark a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* phish.net's note on the version, set under the venue rather than across the
   row: spanning every column put it against the page's left edge, where it
   read as something stuck on afterwards rather than as part of the entry.
   Roman, not italic -- these run to 950 characters at the long end, and a
   paragraph of italic prose is tiring well before that. */
/* The only real prose on the site, and the one job neither other face can do.
   The mono set it evenly and never argued with the figures, but 950 characters
   of monospace gives the eye nothing to return on, and the display face at
   text size is a display face at text size. Literata is drawn for reading and
   has the optical axis to be drawn differently here than at a headline, which
   is the whole argument for a third family rather than stretching a second.
   15px rather than 12: a proportional face sets far more into the same measure,
   and the old size was compensating for the mono's width. */
.jam,.note{margin:.45rem 0 0;font-family:'Literata',Georgia,serif;
   font-size:.9375rem;line-height:1.5;font-variation-settings:'opsz' 14;
   color:var(--ink-soft);max-width:62ch}
.jam a,.note a{color:inherit;text-decoration:none;
   border-bottom:1px solid var(--edge);word-break:break-word}
.jam a:hover,.note a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
.tag{display:inline-block;margin-right:.45rem;font-size:.625rem;
   letter-spacing:.14em;text-transform:uppercase;color:var(--dim)}
details.jam,details.note{cursor:pointer}
details.jam summary,details.note summary{display:block;list-style:none}
details.jam summary::-webkit-details-marker,
details.note summary::-webkit-details-marker{display:none}
.clip{display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;
   overflow:hidden}
details[open] .clip{-webkit-line-clamp:none;display:block}
/* The affordance sits outside the clamped box, or it would be clipped away by
   the very rule that makes it necessary. */
details.jam summary::after,
details.note summary::after{content:"More";display:inline-block;margin-top:.2rem;
   font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim);border-bottom:1px solid var(--rule)}
details.jam[open] summary::after,
details.note[open] summary::after{content:"Less"}
details.jam summary:hover::after,
details.note summary:hover::after{color:var(--hot-text);border-bottom-color:var(--hot-text)}
details.jam summary:focus-visible,
details.note summary:focus-visible{outline:2px solid var(--hot);outline-offset:2px}
.empty{margin:2rem 0;font-size:.875rem;color:var(--dim);font-style:italic}
/* The header a reader keeps once the real one has scrolled away. Landing on a
   row from a report's link otherwise drops you into an unlabeled list of
   dates with no way to tell what page you are on. It carries the song and the
   figure the page exists for, and nothing else. */
.stuck{position:fixed;top:0;left:0;right:0;z-index:20;
  background:var(--paper);border-bottom:1px solid var(--rule);
  transform:translateY(-101%);transition:transform .22s ease;
  padding:.5rem clamp(1rem,5vw,3rem)}
.stuck.on{transform:none}
/* 60rem, not 960px -- the same measure as .wrap and for the same reason given
   there. This was the one place the px-to-rem conversion was missed, so when
   the scale went up a step the content grew to 1080px and this bar held still
   at 960. It carries .cols, the column labels whose whole job is to sit over
   the columns they name, so the miss did not read as a narrow bar: it put
   every label 60px off its own column, and a long note in the venue cell then
   ran visibly past the "Before / after" label without ever touching that
   column. The header was wrong, not the note. */
.stuck .in{max-width:60rem;margin:0 auto;display:flex;align-items:baseline;
  gap:.7rem}
.stuck .name{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;font-size:1rem;
  white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.stuck .n{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
  color:var(--dim);margin-left:auto;white-space:nowrap}
.stuck .n b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
  font-size:.875rem;color:var(--ink);letter-spacing:0}
/* The column labels come along. A reader arriving from a report page lands
   mid-list, having never seen the header row, and the last column is a bare
   number: knowing it is a gap requires knowing the site already. Same markup
   and same grid as the real header, so the labels sit over their columns
   rather than near them. Dropped below 820px, where the row stops being
   columns at all and each field carries its own label instead. */
.stuck .cols{display:block;margin-top:.4rem}
.stuck .cols .head{border-bottom:0;padding-bottom:0}
@media screen and (max-width:820px){.stuck .cols{display:none}}
@media (prefers-reduced-motion:reduce){.stuck{transition:none}}
/* Where a link dropped you. Bright for a moment, then gone -- it answers
   "which row?" and then stops being ink on the page. */
@keyframes landed{from{background:var(--hover);box-shadow:inset 3px 0 0 var(--hot)}
  to{background:transparent;box-shadow:inset 3px 0 0 transparent}}
.perfs>li.landed{animation:landed 3.4s ease-out both}
@media (prefers-reduced-motion:reduce){
  .perfs>li.landed{animation:none;box-shadow:inset 3px 0 0 var(--hot)}}
""" + TOTOP_CSS + FOOTER_BOX_CSS + FOOTER_LINK_CSS + """@media screen{
}
/* Same lesson as the reports and the index: below this width the columns stop
   being columns, so nothing has to be squeezed or hidden. Higher than the 620
   the other pages use, because this row carries five columns to their three --
   at 760px the fixed four left the venue about 14rem and "Bethel Woods Center
   for the Arts" came out over four lines. */
@media screen and (max-width:820px){
  .head{display:none}
  /* The caption goes above its list rather than beside it, so the pairings get
     the whole measure. A pairing must not break -- the count belongs to the
     song it terminates, which is the point of setting it that way at all -- so
     "Bouncing Around the Room 24x" is one unbreakable 240px run, and beside a
     caption there was not 240px to give it at 375px. */
  .pairs{grid-template-columns:minmax(0,1fr)}
  .pair .cap,.pair .ps{grid-column:1}
  .pair .cap{margin-top:.35rem}
  .row{grid-template-columns:1fr;column-gap:0;row-gap:.15rem;padding:.55rem 0}
  .nb{margin-top:.35rem}
  .nb .cap{display:block;font-size:.625rem;letter-spacing:.14em;
     text-transform:uppercase;color:var(--dim);margin-bottom:.1rem}
  .r-date{display:flex;align-items:baseline;gap:.5rem}
  .dow{display:inline}
  .r-gap{text-align:left}
  .glabel{display:inline}
  .gap{font-size:1rem}
  .set{display:inline;margin-left:.5rem}
  .set::before{content:"\\00b7";margin-right:.5rem;color:var(--dim);opacity:.7}
  .bar{margin:.25rem 0}
  .card{flex:1 1 45%;padding:.65rem .55rem}
  .card:nth-child(odd){border-left:0;padding-left:0}
  .card:nth-child(n+3){border-top:1px solid var(--rule)}
  .num{font-size:1.5rem}
  /* Two columns here, so the date has a 45% card rather than half the row:
     1.5rem wants 162px against about 151px of it at 375. */
  .num.when{font-size:1.25rem}
  .lbl{font-size:.625rem;letter-spacing:.14em}
  /* "Median gap, last 10 years" is the clear label and the default one; the
     column is simply not wide enough for it here. */
  .lbl .full{display:none}
  .lbl .abbr{display:inline}
  .show{font-size:.75rem;letter-spacing:0}
  .count{margin-left:0}
  .theme{order:1;flex-basis:100%}
}
/* A one-performance hero is two cards and one of them is a ten-character date,
   which is a different problem from the five-card row: two cards share the
   width, so each gets about 124px at 320px and the date wants 135. Measured
   rather than guessed -- it is fine at 330 and wraps at 320, so the pair stack
   below 360 rather than at the edge of fitting, where a fallback face a little
   wider than IBM Plex Mono would put it back. Five cards already stack on a
   phone; these two just do it one breakpoint later. */
@media screen and (max-width:360px){
  .hero.sparse .card{flex:1 1 100%;border-left:0;padding-left:0}
  .hero.sparse .card+.card{border-top:1px solid var(--rule)}
  .hero.sparse .num.when{font-size:1.5rem}
}
""")
# After the sheet is composed, not inside its last segment: the placeholders sit
# near the top of it, and a .replace() hung off the closing literal would only
# ever see the text below the last shared block.
SONG_CSS = (SONG_CSS.replace("__PNET__", ICON_PNET)
                    .replace("__PIN__", ICON_PIN)
                    .replace("__FOUL__", ICON_FOUL))

SONG_JS = """
/* How long this song has been waiting, read from one small file rather than
   rendered into the page. It is the only figure here that moves when some
   *other* song is played, so baking it in would rewrite every song page after
   every show -- 48 MB pushed to publish one number that fits in 7 KB.

   The card no longer ships hidden. Hiding it meant a reader without
   JavaScript got a hero one card short with no sign the figure existed, and
   the label a reader saw depended on whether this file ran. It now carries
   its label and its longest-gap line from the start, and the big slot holds
   the same em-dash the bars use for a figure that is not available -- so a
   failed fetch leaves a card short of one number rather than no card, and
   only the number ever waits. */
(function(){
  var box=document.querySelector('.card.since');
  if(!box||!window.fetch) return;
  var slug=box.getAttribute('data-slug');
  fetch('../data/current.json').then(function(r){
    if(!r.ok) throw 0;
    return r.json();
  }).then(function(d){
    var n=d.since&&d.since[slug];
    if(typeof n!=='number') return;
    box.querySelector('.num').textContent=n.toLocaleString();
    /* The same two thresholds the report pages apply, in the same order: the
       upper edge of the song's usual range where it has enough history to have
       one, and the bustout line where it does not. Both are counted off the
       same calendar as this figure, so they compare like with like. */
    var high=parseFloat(box.getAttribute('data-high')),
        bust=parseFloat(box.getAttribute('data-bustout')),
        mult=parseFloat(box.getAttribute('data-mult'))||2,
        v=box.querySelector('.v');
    if(high>0){
      /* Past its norm AND past the bustout line is not "overdue" -- it is a
         song whose return would be the headline of the night. The due page
         draws the same line and files these under On the shelf, and the two
         must not disagree about the same song. */
      if(n>high&&n>=bust){ box.classList.add('dormant');
        if(v){ v.textContent='on the shelf'; v.className='v dim'; } }
      /* Due and overdue are different claims and the due page separates them,
         so this must too or the same song is called two things in two places.
         Past its norm but only just is the one a reader is expecting. */
      else if(n>=high*mult){ box.classList.add('over');
        if(v) v.textContent='overdue'; }
      else if(n>high){ box.classList.add('over'); if(v) v.textContent='due'; }
      // "line 10" was the site talking to itself: the reader has no way to
      // know which line, and the number is the one this song becomes overdue
      // at. Say that.
      else if(v){ v.textContent='due at '+Math.round(high); v.className='v quiet'; }
    }else if(n>=bust){
      /* The word arrives already chosen, in data-quiet, rather than being
         worked out here from thresholds. "Dormant" on a song played once was
         the claim the out-of-rotation page was rebuilt to stop making, and it
         was being made here too -- this box outlives any one list, so fixing
         only the page would have left the word loose on 174 song pages.

         Deciding it here meant this file spelling out the same two thresholds
         and the same four words the page uses, in a second language, where
         nothing would have caught them drifting apart. rotation_word() names
         it once in Python, from the constants and FEW_NAMES; the only thing
         left to do at this end is wait for the gap to prove it applies. */
      box.classList.add('dormant');
      var quiet=box.getAttribute('data-quiet');
      if(v&&quiet){ v.textContent=quiet; v.className='v dim'; }
    }
    box.title='Counted through '+d.as_of+', over '+d.shows.toLocaleString()+
            ' shows that count toward a gap';
    /* Nothing to reveal any more. Setting .num's textContent above already
       replaced the em-dash that stood in for the number, and a song missing
       from current.json returns before that and keeps the dash, which is the
       honest reading rather than a card that vanishes. */
  }).catch(function(){});
})();
(function(){
  var list=document.getElementById('list');
  if(!list) return;
  var kids=Array.prototype.slice.call(list.children),
      rows=kids.filter(function(n){ return !n.classList.contains('yr'); }),
      heads=kids.filter(function(n){ return n.classList.contains('yr'); }),
      q=document.getElementById('q'), sort=document.getElementById('sort'),
      shown=document.getElementById('shown'), empty=document.getElementById('empty');
  function matcher(t){
    if(!/^\\d+$/.test(t)) return function(hay){ return hay.indexOf(t)>-1; };
    var re=new RegExp('(^|[^0-9])'+t+'([^0-9]|$)');
    return function(hay){ return re.test(hay); };
  }
  function apply(){
    var terms=q.value.toLowerCase().split(/\\s+/).filter(Boolean).map(matcher),
        n=0, live={};
    rows.forEach(function(r){
      var hay=r.getAttribute('data-search'), ok=terms.every(function(t){
        return t(hay);
      });
      r.hidden=!ok;
      // A soundcheck row is shown but is not a show, so it is not counted.
      if(ok){ if(r.getAttribute('data-counted')!=='0') n++;
              live[r.getAttribute('data-era')]=1; }
    });
    // A year heading with nothing left under it is worse than no heading, so
    // it goes when its rows do -- and stays gone whenever the order is not
    // chronological, because then it is not describing what follows it.
    var byDate=sort.value==='newest'||sort.value==='oldest';
    heads.forEach(function(h){
      h.hidden=!byDate||!live[h.getAttribute('data-era')];
    });
    shown.textContent=n;
    empty.hidden=n>0;
    // The way out of a filter appears only once there is one to leave.
    if(clear) clear.hidden=!q.value;
  }
  var headFor={};
  heads.forEach(function(h){ headFor[h.getAttribute('data-era')]=h; });
  function order(){
    var k=sort.value;
    var sorted=rows.slice().sort(function(a,b){
      if(k==='rating') return (b.getAttribute('data-score')||-1)-(a.getAttribute('data-score')||-1);
      if(k==='gap') return (b.getAttribute('data-gap')||-1)-(a.getAttribute('data-gap')||-1);
      var x=a.getAttribute('data-date'), y=b.getAttribute('data-date');
      return k==='oldest' ? x.localeCompare(y) : y.localeCompare(x);
    });
    sorted.forEach(function(r){ list.appendChild(r); });
    if(k==='newest'||k==='oldest'){
      // Walk the list as it now runs and put each heading before the first row
      // of its era. Reading the era order off the original array instead put
      // every heading at the foot of its group when sorted oldest, because the
      // array is newest-first and never gets re-sorted itself.
      var placed={};
      sorted.forEach(function(r){
        var e=r.getAttribute('data-era');
        if(placed[e]) return;
        placed[e]=1;
        if(headFor[e]) list.insertBefore(headFor[e], r);
      });
    } else {
      // Hidden either way, but parked at the end rather than left stranded
      // between rows they no longer describe.
      heads.forEach(function(h){ list.appendChild(h); });
    }
    apply();
  }
  var clear=document.getElementById('clear');
  function setQuery(v){ q.value=v; apply(); }
  /* A one-performance page ships no tools bar at all, so every handler below
     is wired only where there is something to wire it to. Guarded here rather
     than by returning early: the sticky header and the deep-link landing at the
     foot of this function belong to every song page, and an early return took
     them out on the 134 pages that have one row -- which are exactly the pages
     a report links *into* by date. */
  if(q&&sort){
    q.addEventListener('input', apply);
    sort.addEventListener('change', order);
    // Clicking a venue asks the question you were about to type.
    list.addEventListener('click', function(e){
      var v=e.target.closest && e.target.closest('.r-venue');
      if(!v) return;
      setQuery(v.textContent.trim());
      q.scrollIntoView({block:'nearest'});
    });
    if(clear) clear.addEventListener('click', function(){ setQuery(''); q.focus(); });
    document.addEventListener('keydown', function(e){
      if(e.key==='/' && document.activeElement!==q){ e.preventDefault(); q.focus(); }
      if(e.key==='Escape' && q.value){ setQuery(''); q.blur(); }
    });
    q.disabled=false; sort.disabled=false;
    apply();
  }

  // The condensed header appears once the real one is off screen, and the
  // real one is the thing to watch rather than a scroll offset -- no
  // magic number, and it stays right when the header wraps to more lines.
  var stuck=document.getElementById('stuck'), head=document.querySelector('header'),
      totop=document.getElementById('totop');
  function perch(on){
    if(stuck) stuck.classList.toggle('on', on);
    if(totop) totop.hidden=!on;
  }
  if(head && 'IntersectionObserver' in window){
    new IntersectionObserver(function(e){ perch(!e[0].isIntersecting); },
      {rootMargin:'-8px 0px 0px 0px'}).observe(head);
  }

  // A link from a report lands on one row; say which, then stop saying it.
  function land(){
    var id=location.hash.slice(1);
    if(!id) return;
    var li=document.getElementById(id);
    if(!li || li.classList.contains('yr')) return;
    li.classList.remove('landed');
    void li.offsetWidth;            // restart the animation on a repeat visit
    li.classList.add('landed');
  }
  window.addEventListener('hashchange', land);
  land();
})();
"""

SONG_SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{song} &mdash; Possum Logic</title>
<meta property="og:type" content="article">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}{ago_js}{new_rows_js}</head><body id="top"><div class="wrap">
<a class="skip" href="{skip}">Skip to content</a>
{crumb}
<div class="stuck" id="stuck" aria-hidden="true"><div class="in">
<span class="name">{song}</span>
<span class="n">{stuckstat}</span></div>
<div class="in cols">{cols}</div></div>
<div class="rule2"></div>
<header><h1>{song}</h1>
<p class="show">{subtitle}</p>
<p class="links"><span class="cap">This song on</span>{links}</p>
{caveat}</header>
<section class="hero{herocls}">{hero}</section>
{best}
{pairs}
{tools}
{head}
<ol class="perfs" id="list"{listattrs}>
{rows}
</ol>
<p class="empty" id="empty" hidden>No performances match that search.</p>
<a class="totop" id="totop" href="#top" hidden aria-label="Back to the top">&uarr;</a>
""" + footer_html(root="../") + """
{analytics}
</div><script>{js}</script></body></html>
"""

# Lifted out of SONG_SHELL so that a page with nothing to search, sort or
# filter can leave it out entirely rather than ship it disabled. See
# SPARSE_HISTORY. Braces are the shell's own .format() vocabulary, so this stays
# a plain block with two fields and no CSS or script in it.
SONG_TOOLS = """<div class="tools" id="main" tabindex="-1">
<input id="q" class="search" type="search" autocomplete="off" disabled
       placeholder="Search venue, city, year, Sunday&hellip;" aria-label="Search performances">
<button id="clear" class="clear" type="button" hidden>Clear</button>
<span class="eras"><span class="eras-cap">Eras</span>{eras}</span>
<label class="count" for="sort">Sort
<select id="sort" class="sort" disabled>
<option value="newest">Newest</option><option value="oldest">Oldest</option>
<option value="rating">Highest rated</option><option value="gap">Longest gap</option>
</select></label>
<span class="count"><b id="shown">{count}</b> of {count} shows</span>
</div>"""

# Last field is which identifier the URL wants -- see foul_song_slug for why
# fouldomain cannot take the one the other two share.
SONG_LINKS = (
    ("phish.net", "https://phish.net/song/%s", ICON_PNET, False, "slug"),
    ("phish.in", "https://phish.in/songs/%s", ICON_PIN, True, "slug"),
    ("fouldomain", "https://fouldomain.com/songs/%s", ICON_FOUL, False, "foul"),
)


def foul_song_slug(title):
    """fouldomain's slug for a song, derived from its title.

    Not phish.net's slug, which is what every other identifier on this site
    keys on. Measured against all 589 songs here, phish.net's slug lands on
    fouldomain's "Song Not Found" for 13 of them: phish.net drops punctuation
    fouldomain keeps as a separator (AC/DC Bag is `acdc-bag` there and
    `ac-dc-bag` here, L.A. Woman `la-woman` against `l-a-woman`), carries
    disambiguation suffixes fouldomain has no need of (`gloria-branigan`,
    `invisible-2`, `timber-haunted`), and in one case has an `<em>` baked into
    it -- `theme-from-emnew-york-new-yorkem`.

    An apostrophe is *dropped* rather than separated on, and that is the whole
    of what a first pass got wrong: `mike-s-song` is a 404 where `mikes-song`
    is the page, and 24 songs turn on it. Derived this way all 589 resolve,
    and each lands on a page whose og:title is this song's exact title -- the
    check worth repeating if fouldomain ever changes its routing, because
    "the page exists" and "the page is about this song" are different claims
    and only the second one is the one being made here.
    """
    return re.sub(r"[^a-z0-9]+", "-", re.sub(r"['’]", "", title.lower())).strip("-")


# The one entry whose *title* is not the entry. phish.net files one-off and
# unlisted titles under `custom`, and this archive shows the page as Dog Log
# because Dog Log is one of the nine -- so a chip matched on title lands on
# fouldomain's page for the actual Dog Log and says the other eight are
# versions of it. The slug-matched chips beside it point at phish.net's own
# catch-all and keep the aggregate, which is why this is about fouldomain
# rather than about the page.
#
# Not NOT_A_SONG, which was the first gate here and was too wide by one: `jam`
# is the other page that is not a composition, but its title names the bucket
# rather than one of the things in it, and fouldomain files unnamed
# improvisation under the same word. Ian's call, and it holds -- the test is
# whether a title match lands on the same set, not whether the page is a song.
TITLE_NOT_THE_ENTRY = frozenset({"custom"})


def _song_links(doc):
    """The chips under a song's title, for the sites that hold the rest of it.

    fouldomain matches on title where the other two match on slug, so it is
    left off wherever those two disagree about what the page is -- see
    TITLE_NOT_THE_ENTRY, which is one page.
    """
    ids = {"slug": doc["slug"], "foul": foul_song_slug(doc["song"])}
    return "".join(
        _badge(label, url % ids[key], icon, flip)
        for label, url, icon, flip, key in SONG_LINKS
        if key != "foul" or doc["slug"] not in TITLE_NOT_THE_ENTRY)


def _ext(url, label, cls):
    """An outbound link, wearing the favicon of wherever it lands.

    The icon arrives by class rather than as an inlined <img>. It is the same
    2.5 KB of base64 either way, but on a page with a link on every one of You
    Enjoy Myself's 628 rows the difference is 2.6 MB against 240 KB.
    """
    return ("<a class='ext %s' href='%s' target='_blank'"
            " rel='noopener noreferrer'>%s</a>"
            % (cls, html.escape(url, quote=True), label))


# phish.net's prose occasionally carries a bare URL -- one in the archive so
# far, pointing at a YouTube clip of the version being described. It was being
# escaped and printed as text, which is the one place a reader would obviously
# want to click.
URL_IN_PROSE = re.compile(r"https?://[^\s<]+")


def linkify(escaped):
    """Turn bare URLs in already-escaped prose into links.

    Runs on escaped text, so an ampersand in a query string is already
    &amp; -- which is what an href wants anyway. Trailing punctuation belongs
    to the sentence rather than the address: the one live example ends
    ").", and a closing bracket only counts if the URL opened one.
    """
    def wrap(m):
        url = m.group(0)
        tail = ""
        while url and url[-1] in ".,;:!?":
            url, tail = url[:-1], url[-1] + tail
        while url.endswith(")") and url.count("(") < url.count(")"):
            url, tail = url[:-1], ")" + tail
        if not url:
            return m.group(0)
        return ("<a href='%s' target='_blank' rel='noopener noreferrer'>%s</a>%s"
                % (url, url, tail))
    return URL_IN_PROSE.sub(wrap, escaped)


def countable_gaps(doc, counting=None):
    """The performances and gaps a song's own figures are computed from.

    Two exclusions, and both matter. Anything the counting calendar does not
    hold is not a performance the rest of the site would recognize. And the
    debut's own gap is not a gap *between two performances of this song* -- it
    counts shows since the band's first show, so Johnny B. Goode's debut
    carries 954 where its real longest gap is 927.

    Shared because the song page and its preview card each did this arithmetic
    themselves and disagreed: the card had no longest-gap branch at all and
    printed an em-dash on 340 of 588 songs, and it counted every performance
    where the page counts only the countable ones. One reader, two numbers.

    -> (countable newest-first, debut date, gaps worth measuring)
    """
    perfs = list(reversed(doc.get("performances") or []))
    # Newest first, so the last countable row is the earliest one.
    countable = [p for p in perfs if not counting or p["date"] in counting]
    debut_date = countable[-1]["date"] if countable else None
    gaps = [p["gap"] for p in countable
            if p["gap"] is not None and p["date"] != debut_date]
    return countable, debut_date, gaps


def _debut_card(debut_date, sparse=False):
    """The hero card for when a song started, or nothing if it never counted.

    It takes the slot "Times Played" had, which was the same integer the page
    already printed three more times -- in the subtitle a dozen pixels above the
    card, in the "n of n shows" counter, and in the sticky bar -- while the
    debut was one small-caps phrase in that subtitle and its row was at the foot
    of a list up to 629 rows long. Every gap figure here is "n/a" on a quarter
    to a third of songs; the debut is missing on 9 of 589, which makes it the
    most widely available thing the hero was not showing.

    The figure is the **year**, and that is a measurement rather than a taste:
    five cards across leaves 117-160px inside each one between 900 and 1280px,
    and "1986-02-03" wants 243px at the .num size and still 162px shrunk to
    1.5rem. It wrapped to two lines at 900, 1024 and 375. Widening the card to
    fit starves the other four below 1024. So the exact date goes where there is
    room for it: the card is a link to the debut's own row, which is the sort
    reversal this card exists to save, and the row states the full date, the
    venue and the note.

    A one-performance page has two cards and half the row each, so there the
    full date fits and is printed -- and there is nothing to link to that is not
    already the only thing on the page.
    """
    if not debut_date:
        return ""
    if sparse:
        return ("<div class='card dbt'><div class='lbl'>Debuted</div>"
                "<div class='num when'>%s</div></div>" % debut_date)
    return ("<a class='card dbt' href='#%s' title='Debuted %s'>"
            "<div class='lbl'>Debuted</div>"
            "<div class='num'>%s</div></a>" % (debut_date, debut_date,
                                               debut_date[:4]))


def _sparse_gap_card(gaps):
    """The one gap figure a nearly-unplayed song actually has.

    At two performances there is exactly one interval, and it is the most
    interesting number on the page -- Baby Lemonade's two are 1,312 shows
    apart. The full hero said it three times, as "median, last 10 years",
    "median, all-time" and "longest gap", because with a single sample all
    three reduce to the same value. Said once, and named for what it is.

    Written to survive SPARSE_HISTORY being raised again: with more than one
    interval "shows between" would be a false description of a median, so the
    label changes with the arithmetic rather than assuming the threshold.
    """
    if not gaps:
        return ""
    val, lbl = ((gaps[0], "Shows Between") if len(gaps) == 1
                else (max(gaps), "Longest Gap"))
    return ("<div class='card'><div class='lbl'>%s</div>"
            "<div class='num hot'>%s</div></div>" % (lbl, _stat(val)))


def render_song(doc, archived=(), stamp=None, card=None, counting=None,
                kinds=None):
    """One song's whole performance history, newest first.

    The archive stores phish.net verbatim, so the corrections happen here.
    `counting` is the set of dates that count toward a gap; performances at the
    others are soundchecks and television sessions, and they are shown -- they
    happened -- but they are not the song's debut, they carry no gap, and they
    are kept out of every figure. Left in, Gone's debut was the Festival 8
    soundcheck, which made its real first performance render a gap of 1,468.
    """
    perfs = list(reversed(doc["performances"]))
    song = doc["song"]
    best = doc.get("best") or []
    rated = {v["date"]: v for v in best}
    countable, debut_date, gaps = countable_gaps(doc, counting)
    biggest = max(gaps) if gaps else 0

    # The all-time and recent medians sit side by side because they disagree so
    # often: You Enjoy Myself is 1 against 6, Llama 2 against 11. Showing only
    # the all-time figure would describe a band that stopped existing in 1999.
    # The same ten years the due page measures over, and the same ten for
    # every song -- see recent_cutoff. A window anchored to this song's own
    # last performance let a page say "median gap, last 10 years: 8" about a
    # song nobody has heard since 2011.
    cutoff = recent_cutoff(counting, perfs[0]["date"] if perfs else None)
    recent = [p["gap"] for p in countable
              if p["gap"] is not None and p["date"] >= cutoff
              and p["date"] != debut_date]
    lbl10 = ("Median Gap, <span class='full'>Last %d Years</span>"
             "<span class='abbr'>%d Yr</span>" % (RECENT_YEARS, RECENT_YEARS))
    # A song played once has one figure worth a card and it is not a gap: three
    # of the four below read "n/a", and the fourth restates the subtitle. What
    # it has instead is a date and a distance from now, so that is what it gets.
    sparse = len(countable) <= SPARSE_HISTORY
    # The debut card only survives where the hero would otherwise be thin: a
    # song with one or two performances has no median and no longest to pair,
    # so its date is the figure it has. Everywhere else the date has gone up
    # into the identity line, full rather than truncated to a year.
    hero = _debut_card(debut_date, sparse) if sparse else ""
    if sparse:
        hero += _sparse_gap_card(gaps)
    else:
        # Five cards were one date and one measure read at four moments, and
        # five across is the count that has no tidy arrangement: the grid lays
        # them 3+2 and the flex row crammed them onto one line at unequal
        # widths. They pair. The two medians are the same statistic over two
        # windows; the two gaps are the same distance at two moments. One card
        # each, the timelier reading in the big slot and the historical one
        # under it -- which is the same rule twice, not a per-card taste.
        #
        # The sub-line is also what fills the measure a bare number left empty,
        # so two cards read as a hero rather than as three missing ones.
        if recent:
            median_num, median_sub = (
                _stat(_median(recent)),
                "last %d years &middot; <b>%s</b> all-time"
                % (RECENT_YEARS, _stat(_median(gaps)) if gaps else "n/a"))
        else:
            # 51 songs have nothing in the window. Promoting the all-time
            # figure into the big slot retires an "n/a" card and says why.
            median_num, median_sub = (
                _stat(_median(gaps)) if gaps else "n/a",
                "all-time &middot; not played in the last %d years" % RECENT_YEARS)
        hero += ("<div class='card'><div class='lbl'>Median gap</div>"
                 "<div class='num'>%s</div><div class='sub'>%s</div></div>"
                 % (median_num, median_sub))
    # Filled in the browser from data/current.json; see SONG_JS. It carries the
    # thresholds rather than the verdict, because the count it has to be judged
    # against is the thing that is not known until the page is open. They are
    # the same two the report pages use -- the upper edge of `gap_band` where
    # there is enough history for one, the bustout line where there is not --
    # so a song called overdue here is overdue by the site's one rule.
    # Not `hidden`, and the label does not move. The card used to ship hidden
    # and be revealed by script, so a reader without JavaScript got a hero one
    # card short and never knew a figure existed. It now ships with the same
    # label it will always carry and the em-dash the bars already use for a
    # figure that is not available -- the mark that exists so an empty slot
    # reads as "never possible" rather than "failed".
    #
    # Ian asked why the label should differ between the two readers at all,
    # and the answer was that it should not: only the *number* is unknown
    # until the page is open, so only the number waits. The longest gap is
    # known at build time and sits under it, which also means this card says
    # something true before the fetch and something truer after.
    hero += ("<div class='card since' data-slug='%s' data-high='%s' "
             "data-bustout='%d' data-mult='%s' data-quiet='%s'>"
             "<div class='lbl'>Current gap<span class='v'></span></div>"
             "<div class='num'><span class='no-range' aria-hidden='true'>"
             "&mdash;</span></div>"
             "<div class='sub'>longest <b>%s</b></div></div>"
             % (html.escape(doc.get("slug") or ""),
                gap_band(recent)[1] if len(recent) >= MIN_HISTORY else "",
                BUSTOUT_GAP, DUE_MULTIPLE,
                # The word, not the numbers it is worked out from. Whether it
                # is used at all depends on the current gap, which is not known
                # until the page is open -- but which of the four words it
                # would be depends only on the play count, which is known here.
                html.escape(rotation_word(len(countable)), quote=True),
                _stat(biggest) if gaps else "n/a"))

    top = best[0] if best else ""
    if top:
        where = ", ".join(x for x in (top["venue"], top["city"]) if x)
        # The date is a link to its own row. Without it the only way to read
        # that version's notes was to remember the date, tap an era chip and
        # scroll for it.
        #
        # Unless there is no such row. The scores come from fouldomain and the
        # rows from phish.net's song history, and on twelve songs the two do
        # not agree about what exists: Joy's best version is dated 1995-12-09,
        # which is a night the band played but not one this archive holds a Joy
        # performance for -- likewise Rift, Axilla, Free, Sleep, Waves and six
        # more. The link went to a fragment no element carried, so it landed at
        # the top of the page: the exact behavior the comment above says it
        # was added to fix. Plain text when we cannot point at the row, which
        # is this file's rule everywhere else -- say less rather than say wrong.
        anchored = any(p["date"] == top["date"] for p in perfs)
        when = ("<a class='when' href='#%s'>%s</a>" % (top["date"], top["date"])
                if anchored else "<span class='when'>%s</span>" % top["date"])
        # One line, not four stacked label/value pairs. Three of those four
        # captions were naming a thing the reader can already identify: every
        # row below puts a venue in the same slot without labeling it, and
        # "Rated 83" is the phrasing the rows themselves use for a score. Only
        # "Best version" says something the values do not, so only it survives
        # as a caption. 170px of front matter on a phone for four words of
        # scaffolding.
        top = ("<p class='best'><span class='cap'>Best version</span>"
               "<span class='v'>%s"
               " &middot; <span class='where'>%s</span>"
               " &middot; Rated <span class='score'>%s</span>"
               " &middot; %s &middot; %s</span></p>"
               % (when, html.escape(where), top["score"],
                  _ext("https://phish.in/%s" % top["date"], "Listen", "i-pin"),
                  _ext(top["link"] or "https://fouldomain.com/", "Details", "i-foul")))

    # Each era heading counts its own shows, which is the thing a year heading
    # never told you: McGrupp reads 101 / 1 / 13 / 9 and you can watch the song
    # nearly die and come back.
    # Counted over what counts, so an era chip agrees with the rows under it
    # and with Times Played above it.
    tally = collections.Counter(era(p["date"]) for p in countable)
    span = {}
    for p in perfs:
        e = era(p["date"])
        lo, hi = span.get(e, (p["date"], p["date"]))
        span[e] = (min(lo, p["date"]), max(hi, p["date"]))

    # One band for the whole page: this is a single song, so "usually" is a
    # single answer rather than a per-row one.
    #
    # No layoff sentence here, though `layoff_break` would answer for this song
    # too. This page draws the band and never states it in words, so there is no
    # sentence to add the clause to -- only a new paragraph on all 588 pages, to
    # reach the nine it would say anything about. That is the mistake the marks
    # link below was moved to stop making.
    low, high = gap_band(recent)
    rows, seen_era = [], None
    for i, p in enumerate(perfs):
        date, g = p["date"], p["gap"]
        # The oldest row is the debut, and what phish.net files as its gap is
        # shows since the band's own first show -- Blaze On's 1,682 counts the
        # thirty years before it existed. A different measurement wearing the
        # same name: it does not belong in the column, in the song's longest
        # gap, or on a bar scaled to gaps that mean the other thing.
        # The earliest performance that counts, not the earliest row: a
        # soundcheck standing in front of it made the real debut look ordinary
        # and gave it phish.net's since-the-beginning figure as a gap.
        counted = not counting or date in counting
        debut = date == debut_date
        if not counted:
            g = None
        this = era(date)
        # A heading over one row says "3.0 - 1 show - 2010-2010", which is the
        # year that is in the row beneath it and the count that is in the
        # subtitle above it. There is nothing for it to divide.
        if this != seen_era and not sparse:
            seen_era = this
            lo, hi = span[this]
            rows.append(
                # The dot goes out of the id: "era-4.0" is a perfectly good
                # fragment but not a valid selector, where the dot reads as a
                # class -- querySelector throws on it and :target could never
                # match without escaping.
                "<li class='yr' id='era-%s' data-era='%s'>"
                "<h2><span class='tab'>%s</span>"
                "<span>%d show%s</span><span>%s&ndash;%s</span></h2></li>"
                % (this.replace(".", "-"), this, this, tally[this],
                   "" if tally[this] == 1 else "s", lo[:4], hi[:4]))
        note = p.get("note") or ""
        hay = " ".join([date, _date_aliases(date), p["venue"], p["city"],
                        p["state"], p.get("jam") or "",
                        p.get("note") or ""]).lower()
        # A performance we have a report for links to it; everything else goes
        # to phish.net, wearing their favicon so the trip off-site is visible
        # before it is taken rather than after.
        if date in archived:
            link = "<a href='../show/%s.html'>%s</a>" % (date, date)
        else:
            link = _ext("https://phish.net/setlist/?d=%s" % date, date, "i-pnet")
        place = ", ".join(x for x in (p["city"], p["state"]) if x)
        big = (g or 0) >= 50 and not debut
        # The same band the report pages use, and for the same reason: scaled
        # to the song's own longest gap, one bustout flattened every other row
        # on the page -- Back in the U.S.S.R. drew 485 and 689 at full width
        # and its 23 at three percent of one. The band is the same for every
        # row here, since every row is this song, so the marks line up down the
        # page and the shape of them is the song's history.
        # Same dash the report pages use, and for the same reason: a debut has
        # no gap and a song under MIN_HISTORY has no band, and in both cases an
        # empty scale reads as a bar that failed rather than one that was never
        # possible.
        bar = ("<span class='bar'><span class='no-range' aria-hidden='true'>"
               "&mdash;</span></span>")
        pos = _band_pos(g, low, high) if (g is not None and not debut) else None
        if pos is not None:
            # Colored by where it landed rather than by the size of the
            # number, so it cannot disagree with its own position.
            where = "early" if pos < 30 else "late" if pos > 70 else "usual"
            bar = ("<span class='bar'><span class='track'>"
                   "<span class='band'></span><span class='mid'></span>"
                   "<span class='at %s' style='left:%.2f%%'></span>"
                   "</span></span>" % (where, pos))
        mark = ""
        if date in rated:
            v = rated[date]
            mark = ("<span class='mark%s'>%s <b>%s</b> &middot; %s</span>"
                    % (" high" if v["score"] >= RATED_HIGH else "",
                       "Highly rated" if v["score"] >= RATED_HIGH else "Rated",
                       v["score"],
                       _ext("https://phish.in/%s" % date, "Listen", "i-pin")))
        # What it came out of and went into, reading the way a setlist reads:
        # the mark sits between the two songs it joins. Absent for a set opener
        # or closer, which genuinely has nothing on that side.
        # Always emitted, even empty: every row places the same number of grid
        # children, or a set opener with nothing before it shifts its own bar
        # and gap one column left of everybody else's.
        # One symbol per line. Where phish.net recorded a transition it stands
        # in setlist position and does the pointing itself -- "Everything's
        # Right ->" above, "-> Golden Age" below; a plain arrow only where
        # there was no mark to show. Both at once read as "-> ->".
        def _mk(mark):
            """The transition mark, wrapped so it can be set on its own."""
            return ("<span class='mk%s'>%s</span>"
                    % (" tight" if mark == "->" else "", html.escape(mark)))

        # A set boundary is named rather than left blank. Four states used to
        # render identically to each other and to "we never asked": opened the
        # set, closed the set, opened the show, closed the show. Only the last
        # two are true terminals -- a set opener and a set closer each have a
        # real song on the far side of a break -- so those two carry a song
        # and the terminals carry only the words.
        #
        # The song across a break never takes a mark, whatever phish.net
        # recorded, because a mark there would claim a segue across twenty
        # minutes of setbreak. Adjacency is not the same claim: an encore is
        # chosen in answer to how set 2 ended, and the blank cell threw that
        # away.
        # `or`, not a get() default: phish.net files the odd show under a set
        # key this table does not have, and "Opened set , after Harpua" is a
        # worse sentence than the one that does not name the set at all.
        where = SET_PHRASE.get(p["set"]) or "the set"
        bits = []
        if p.get("prev"):
            bits.append("<span class='nb-in%s'>%s%s</span>"
                        % (" seg" if p.get("in") else "",
                           html.escape(p["prev"]),
                           " %s" % _mk(p["in"]) if p.get("in") else ""))
        elif p.get("xprev"):
            bits.append("<span class='nb-in edge'><b>Opened %s</b>, after %s"
                        "</span>" % (where, html.escape(p["xprev"])))
        elif p.get("first"):
            bits.append("<span class='nb-in term'><b>Opened the show</b></span>")
        if p.get("next"):
            bits.append("<span class='nb-out%s'>%s%s</span>"
                        % (" seg" if p.get("out") else "",
                           "%s " % _mk(p["out"]) if p.get("out") else "",
                           html.escape(p["next"])))
        elif p.get("xnext"):
            bits.append("<span class='nb-out edge'><b>Closed %s</b>, before %s"
                        "</span>" % (where, html.escape(p["xnext"])))
        elif p.get("last"):
            bits.append("<span class='nb-out term'><b>Closed the show</b></span>")
        nb = ("<span class='nb'>%s%s</span>"
              % ("<span class='cap'>Before / after</span>" if bits else "",
                 "".join(bits)))
        times = ("<span class='set'>%s &middot; %d&times;</span>"
                 % (SET_LABEL.get(p["set"], "Set %s" % p["set"]), p["times"])
                 if p.get("times") else
                 "<span class='set'>%s</span>"
                 % SET_LABEL.get(p["set"], "Set %s" % p["set"]))
        # Folded only when long enough to be worth folding. <details> does the
        # work, so a note is still fully readable with scripting off -- and the
        # text is stored once, clamped by CSS rather than truncated in the
        # markup, so searching still reaches the hidden half.
        # phish.net's footnote first -- it is terse and about the performance --
        # then the jamchart prose, which is longer and about the playing. Each
        # labeled, because unlabeled they read as one run-on paragraph.
        jam = ""
        for cls, tag, text in (("note", "Note", p.get("note")),
                               ("jam", "Jam chart", p.get("jam"))):
            if not text:
                continue
            body = ("<span class='tag'>%s</span>%s"
                    % (tag, linkify(html.escape(html.unescape(text)))))
            jam += ("<details class='%s'><summary><span class='clip'>%s</span>"
                    "</summary></details>" % (cls, body)
                    if len(text) > JAM_CLAMP
                    else "<p class='%s'>%s</p>" % (cls, body))
        rows.append(
            "<li id='%s' data-date='%s' data-era='%s' data-gap='%s'"
            " data-score='%s'%s data-search=\"%s\"><div class='row'>"
            "<span class='r-date'>%s<span class='dow'>%s</span></span>"
            "<span><span class='r-venue'>%s</span>"
            "<span class='r-place'>%s</span>%s%s</span>%s%s"
            "<span class='r-gap'><span class='glabel'>Gap</span>"
            "<span class='gap%s'>%s</span>%s</span>"
            "</div></li>"
            % (date, date, this, -1 if (g is None or debut) else g,
               rated[date]["score"] if date in rated else "",
               "" if counted else " data-counted='0'",
               html.escape(hay, quote=True), link, weekday(date),
               html.escape(p["venue"]), html.escape(place), mark, jam, nb, bar,
               " none" if (g is None or debut) else (" big" if big else ""),
               "Debut" if debut else
               # Which kind of not-a-show, where the archive knows. It knows
               # for the twenty entries it holds a report for; the other
               # thirty-nine non-calendar dates are pre-2009 and have no report
               # to read a kind out of, so they keep the general word.
               (KIND_LABEL.get((kinds or {}).get(date), "Not a show")
                if not counted else
                "{:,}".format(g) if g is not None else "&mdash;"), times))

    # Every bar on this page is the same song against the same scale, so the
    # median sits at one position for all of them -- drawn as a gridline in the
    # track rather than as a tick repeated on six hundred rows, which is the
    # year-heading mistake in another costume. The report pages mark it per row
    # because there each row is a different song with a different norm.
    med = _median(gaps) if gaps else None
    medmark = ""
    # Only where there are bars for it to be a gridline on. Without a band no
    # row draws a track at all -- every one is the no-range dash -- so the
    # header was promising "mark at median 8" over a column that had no marks
    # in it. Rare while the ten-year window traveled with each song, because
    # a song's own last performance always fell inside its own window; with
    # the window anchored to the archive it is every song that has been away
    # for the whole ten years, which is 51 of them.
    if med and biggest and high is not None and _bar_pct(med, biggest) >= 2:
        medmark = ("<style>.perfs{--med:%.2f%%}</style>"
                   % _bar_pct(med, biggest))

    # One chip per era the song actually has, in page order. Anchors rather
    # than filters: "jump to 1.0" should land you there with the rest still
    # beneath you, which is what makes the spine worth having.
    seen_order, chips = [], ""
    for p in perfs:
        e = era(p["date"])
        if e not in seen_order:
            seen_order.append(e)
    chips = "".join(
        "<a class='era-chip' href='#era-%s'>%s<b>%d</b></a>"
        % (e.replace(".", "-"), e, tally[e])
        for e in seen_order)

    # The whole tools bar goes on a sparse page: a search field over one row, a
    # sort with four options that all produce the same page, a chip anchoring to
    # the row below it, and "1 of 1 shows". The bar carried `id="main"`, which
    # is what "Skip to content" skips *to*, so the skip link is re-pointed at
    # the list rather than left aiming at an element that is no longer rendered.
    # It aims at the id the list already has: a second `id` on the same <ol>
    # parses as a duplicate, only the first survives, and `#main` silently
    # resolved to nothing -- which is precisely the failure the skip link exists
    # to prevent, and it is invisible unless you tab into the page.
    tools = "" if sparse else SONG_TOOLS.format(eras=chips, count=len(countable))
    listattrs = ' tabindex="-1"' if sparse else ""
    skip = "#list" if sparse else "#main"
    # Named on the section because the pair of cards below wants a rule the
    # five-card row must not get: see `.hero.sparse` in SONG_CSS.
    herocls = " sparse" if sparse else ""

    # The labels alone, so the sticky bar can carry a second copy without
    # dragging the median's <style> block into a div with it.
    #
    # The marks link lives here rather than in the front matter, where it was
    # four lines of prose above the statistics on all 588 pages -- explaining
    # a notation to everybody in order to reach the few who wondered, and
    # wrapping awkwardly while it did. It sits in the header of the column the
    # marks are actually in, wearing the two marks as its label, so a reader
    # who wonders what `>` means is looking straight at the answer's door.
    cols = ("<div class='row head'><span>Date</span><span>Venue</span>"
            "<span class='nhead'>Before / after "
            "<a class='marks' href='../faq.html#segues'>&gt; and &#8211;&gt;</a>"
            "</span>"
            "<span class='ghead'>Gap%s</span></div>"
            % (" &middot; mark at median %s" % _stat(med) if medmark else ""))
    head = medmark + cols

    # Over the performances that count, so the debut named here is the one the
    # rows call the debut and the total matches Times Played.
    first = debut_date or ""
    last = countable[0]["date"] if countable else ""
    n = len(countable)
    # What it usually sits between. Counted from the same rows the page
    # already prints, so nothing new is fetched or stored.
    before, after = neighbors(perfs, counting)
    pairs = ""
    if before or after:
        def _side(label, items):
            if not items:
                return ""
            # The count carries a times sign so that it reads as a count and so
            # that each pairing ends in a glyph of its own. A middot between
            # items would have done the separating, but this block wraps at
            # every width the phone uses, and a separator that lives between
            # two items can land at the head of a wrapped line. A terminator
            # that belongs to the item cannot.
            return ("<div class='pair'><span class='cap'>%s</span>"
                    "<span class='ps'>%s</span></div>"
                    % (label, " ".join(
                        "<span class='p'>%s<b>%d&times;</b></span>"
                        % (html.escape(typographic(s)), n) for s, n in items)))
        # "Usually" overstated it and was wrong: Tweezer Reprise's top three
        # pairings sum to 58 of 331 performances. "Most often" is the claim the
        # counting actually supports; the denominator is the performance total
        # in the subtitle directly above.
        pairs = ("<div class='pairs'>%s%s</div>"
                 % (_side("Most often out of", before),
                    _side("Most often into", after)))

    caveat = NOT_A_SONG.get(doc.get("slug") or "")
    caveat = "<p class='caveat'>%s</p>" % html.escape(caveat) if caveat else ""
    # The debut is back, and it is here rather than in the hero because this
    # is where it fits. _debut_card had to print the *year* alone: five cards
    # across leaves 117-160px each, and "1986-02-03" wants 243px and wrapped
    # at 900, 1024 and 375. In a line of running text the full date fits, and
    # it keeps the link to its own row that was the card's real purpose -- the
    # sort-reversal a reader would otherwise have to do by hand. So this is
    # not the duplication that removed the clause before: the card is gone,
    # and what is here says more than the card could.
    subtitle = " &middot; ".join(x for x in (
        "Debuted <a href='#%s'>%s</a>" % (debut_date, debut_date)
        if debut_date else "",
        "Last played %s" % last if last and last != first else "",
        "%d performance%s" % (n, "" if n == 1 else "s"),
    ) if x)
    blurb = "Every Phish performance of %s: %d show%s" % (
        song, n, "" if n == 1 else "s")
    if first:
        blurb += ", %s to %s" % (first, last)
    if best:
        blurb += ". Best version %s (%s)" % (best[0]["date"], best[0]["score"])

    links = _song_links(doc)

    # `countable`, not `perfs`. The sticky bar counted every archived row where
    # the hero, the subtitle and the counter all count only the rows that count
    # toward a gap, so on 136 of 589 pages the bar contradicted the page it was
    # a condensed copy of: You Enjoy Myself read "629 shows" stuck to the top of
    # a page whose every other figure said 627. Same source as the rest now, and
    # pluralised, because a song played once was told it had "1 shows".
    stuckstat = ("<b>%d</b> show%s &middot; median gap <b>%s</b>"
                 % (n, "" if n == 1 else "s",
                    _stat(_median(gaps)) if gaps else "&mdash;"))

    return SONG_SHELL.format(
        crumb=nav_strip(section="Songs", root="../", mark=True),
        ago_js=AGO_JS,
        new_rows_js=NEW_ROWS_JS,
        analytics=ANALYTICS,
        css=SONG_CSS, js=SONG_JS, fonts=WEB_FONTS, sheet=sheet_links("../%s/%s" % (STATIC_DIR, SITE_SHEET)),
        cols=cols, caveat=caveat, pairs=pairs, theme_js=THEME_JS, keys_js=KEYS_JS,
        theme_ui=THEME_UI, song=html.escape(typographic(song)), subtitle=subtitle,
        hero=hero, best=top, links=links, tools=tools, listattrs=listattrs,
        skip=skip, herocls=herocls,
        share=share_meta(html.escape(typographic(song)),
                         html.escape(blurb, quote=True),
                         "song/%s.html" % doc["slug"], card=card),
        stuckstat=stuckstat,
        head=head,          # already carries medmark; see where it is built
        rows="\n".join(rows), blurb=html.escape(blurb, quote=True),
        # Dated by the data rather than by the clock. A build stamp changed
        # every page on every run, which is exactly the churn that made
        # rebuilds expensive -- and it was answering "when did this run?"
        # when the useful question is "how current is this?"
        stamp=stamp or ("Current through %s" % last if last else "No performances"))


# ------------------------------------------------------------- song index ---

# The show index's vocabulary, with the first column widened for titles and set
# in the same face the song pages use for theirs. One stylesheet's worth of
# rules rather than a second one drifting away from the first.
SONGS_CSS = INDEX_CSS + """
/* Fixed, not auto. Every row is its own grid, so a column sized to its own
   contents put "485 shows - median 2 - longest 31 - best 90" and "325 shows -
   median 3 - longest 202 - best 79" at different widths, and the last-played
   column shifted row to row down the page. */
.row,.lhead{grid-template-columns:1fr 8.5rem 23.5rem}
.r-stats,.lhead .r-stats{grid-template-columns:5.4rem 6.4rem 7.4rem 4.3rem}
.r-song{display:block;font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:1rem;line-height:1.3rem;color:inherit}
.r-when{font-size:.75rem;color:var(--dim);line-height:1.3rem;white-space:nowrap}
.r-when b{font-family:'IBM Plex Mono',monospace;font-weight:400;color:var(--ink-soft)}
.r-stats .score{color:var(--hot-text)}
/* `.lbl .of` and the arrow that rides it are on the sheet this one extends.
   They were here for half an hour, until the index wanted the same treatment
   for the same reason -- which is the shortest a rule has ever taken to want
   a second home in this file. */
@media screen and (max-width:620px){
  .row{grid-template-columns:1fr}
  .r-when{white-space:normal}
}
"""

SONGS_SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Songs &mdash; Possum Logic</title>
<meta property="og:type" content="website">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}{ago_js}{new_rows_js}</head><body id="top"><div class="wrap">
<a class="skip" href="#main">Skip to content</a>
{crumb}
<div class="rule2"></div>
<header><h1><a href="./index.html">Possum <em>Logic</em></a></h1>
<p class="show">{subtitle}</p></header>
<section class="hero {hero_cls}">{hero}</section>
<div class="rule2"></div>
<div class="tools" id="main" tabindex="-1">
<label class="count" for="sort">Sort
<select id="sort" class="sort" disabled>
<option value="played">Most played</option><option value="az">A&ndash;Z</option>
<option value="recent">Recently played</option><option value="gap">Longest gap</option>
<option value="rated">Highest rated</option></select></label>
<input id="q" class="search" type="search" autocomplete="off" disabled
       placeholder="Search songs&hellip;" aria-label="Search songs">
<span class="count"><b id="shown">{count}</b> of {count} songs</span>
</div>
<div class="lhead"><span>Song</span><span>Last played</span>
<span class="r-stats"><span>Shows</span><span>Median</span><span>Longest</span>
<span>Best</span></span></div>
<ol class="reports" id="list">
{rows}
</ol>
<p class="empty" id="empty" hidden>No songs match that search.</p>
{totop}
""" + footer_html() + """
{analytics}
</div><script>{js}</script></body></html>
"""

SONGS_JS = """
(function(){
  var list=document.getElementById('list');
  if(!list) return;
  var rows=Array.prototype.slice.call(list.children),
      q=document.getElementById('q'), sort=document.getElementById('sort'),
      shown=document.getElementById('shown'), empty=document.getElementById('empty');
  function matcher(t){
    if(!/^\\d+$/.test(t)) return function(hay){ return hay.indexOf(t)>-1; };
    var re=new RegExp('(^|[^0-9])'+t+'([^0-9]|$)');
    return function(hay){ return re.test(hay); };
  }
  function apply(){
    var terms=q.value.toLowerCase().split(/\\s+/).filter(Boolean).map(matcher), n=0;
    rows.forEach(function(r){
      var ok=terms.every(function(t){ return t(r.getAttribute('data-search')); });
      r.hidden=!ok; if(ok) n++;
    });
    shown.textContent=n; empty.hidden=n>0;
  }
  function num(r,k){ var v=r.getAttribute(k); return v===''?-1:+v; }
  function order(){
    var k=sort.value;
    rows.slice().sort(function(a,b){
      if(k==='az') return a.getAttribute('data-song').localeCompare(b.getAttribute('data-song'));
      if(k==='recent') return b.getAttribute('data-last').localeCompare(a.getAttribute('data-last'));
      if(k==='gap') return num(b,'data-longest')-num(a,'data-longest');
      if(k==='rated') return num(b,'data-score')-num(a,'data-score');
      return num(b,'data-played')-num(a,'data-played');
    }).forEach(function(r){ list.appendChild(r); });
  }
  q.addEventListener('input', apply);
  sort.addEventListener('change', order);
  document.addEventListener('keydown', function(e){
    if(e.key==='/' && document.activeElement!==q){ e.preventDefault(); q.focus(); }
    if(e.key==='Escape' && document.activeElement===q){ q.value=''; apply(); q.blur(); }
  });
  q.disabled=false; sort.disabled=false;
  apply();
})();
"""


DUE_SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>What&rsquo;s due &mdash; Possum Logic</title>
<meta property="og:type" content="website">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}{ago_js}{new_rows_js}</head><body id="top"><div class="wrap">
<a class="skip" href="#main">Skip to content</a>
{crumb}
<div class="rule2"></div>
<header><h1>What&rsquo;s due</h1>
<p class="show">{subtitle}</p>
<p class="dek">Songs you are expecting: ones the band plays often enough to
have a habit, which are now a little past it. Measured against each
song&rsquo;s own recent gaps rather than one number for the whole catalog
&mdash; a staple is late at eight shows and a rarity is not late at eighty.
The figure on the right is how far past: 2&times; means it has now been twice
this song&rsquo;s usual gap, which is printed under it.</p>
<details class="how"><summary>How these lists are measured</summary>
<p class="dek">Being late is not the same as being expected, and more late is
not more expected. A song at six times its usual gap is not one anybody is
waiting on &mdash; it is drifting out of rotation. So past {mult}&times; a song
is <a href="#slipping">slipping</a> rather than due, past {cap} shows it is
<a href="#shelf">on the shelf</a>, and with no recent habit at all it is
<a href="#rotation">out of rotation</a>. All four are below, though the fourth
is a count and a door rather than a list: there are more songs in it than in
the other three put together, so they have a page to themselves.</p>
<p class="dek">None of this knows what the band has planned. A themed night
overrides every figure here &mdash; the 2021 Halloween runs built around
numbers and animals, the elements nights of the first Sphere run, a run played
entirely out of one decade &mdash; and the theme is usually not public before
the show. On a night like that the list below is the wrong question.</p>
<p class="dek"><a href="./faq.html#due">The FAQ answers this at more
length</a>, including why a song gone for years is not on the list.</p>
</details></header>
<section class="hero {hero_cls}">{hero}</section>
<div class="rule2"></div>
<section class="rot">
<div class="lhead due-h"><span>Song</span>
<span>Last played</span><span class="end">How late</span></div>
<ol class="due" id="main" tabindex="-1">
{rows}
</ol>
</section>
{shelf}
{dormant}
{totop}
""" + footer_html() + """
{analytics}
</div></body></html>
"""


def due_rows(docs, counting, since):
    """Songs past their own norm, longest overdue first.

    Deliberately not every song that has been gone a while. A song with no
    recent habit that has not been played in 274 shows is not *due* -- nobody
    is expecting it, and calling it due would bury the fifty-five songs someone
    might actually shout for tonight under three hundred that nobody would.
    Dormant is a different fact and the song's own page says it.

    "Recent" is the same ten years for every song -- see recent_cutoff. Read
    per-song it was no filter at all: a song's own last performance always sits
    inside a window ending at its own last performance, so fifteen songs whose
    habit had stopped years ago were being ranked against habits that had
    stopped with them, and the most dormant song in the archive led the list.

    One selection, shared by the due page, its preview card and the index hero.
    It was written out twice before the hero wanted it, and a third copy is
    three chances for the number on the front page to disagree with the page
    it links to.

    Returns (due, overdue, shelved, dormant). Each row in the first three is
    (over, n, high, doc, last); a dormant row is (n, doc, played), because the
    three figures the others are ranked by are exactly what a dormant song does
    not have -- that is what makes it dormant. It used to be a bare count, and
    the count was all anybody could do with it: the dormant hero cell on the due
    page stated 283 and linked nowhere, because nothing in this file knew *which*
    283. All four are exclusive, and the question each answers is different:

      due      past its norm, but only just -- a song you are expecting
      overdue  well past it, still inside the bustout line: might come back,
               might be on its way out, and nobody is waiting on it tonight
      shelved  past its norm and past the bustout line; hearing it is an event
      dormant  no recent habit at all, and gone a bustout's worth
    """
    rows, dormant, calendar = [], [], None
    for doc in docs:
        slug = doc["slug"]
        n = since.get(slug)
        perfs = doc.get("performances") or []
        if n is None or not perfs or slug in NOT_A_SONG:
            continue
        played = [p for p in perfs if not counting or p["date"] in counting]
        if not played:
            continue
        cutoff = recent_cutoff(counting, played[-1]["date"])
        recent = [p["gap"] for p in played[1:]
                  if p.get("gap") is not None and p["date"] >= cutoff]
        if len(recent) < MIN_HISTORY:
            if n >= BUSTOUT_GAP:
                # `since` is computed from the song's raw last performance and
                # this list is keyed to its last *counted* one, which for two
                # songs in the archive are different dates -- both of them
                # phish.net catch-all entries with a stray uncounted row on the
                # end. Recomputed here from the date the row will actually
                # print, so the page cannot say "last played 1997" beside a
                # figure measured from 2009. See shows_since.
                gone = n
                if counting and played[-1]["date"] != perfs[-1]["date"]:
                    if calendar is None:
                        calendar = sorted(counting)
                    gone = shows_since(calendar, played[-1]["date"])
                # The whole counted history, not just its last row: a dormant
                # song is described by how many times it was played and over
                # what span, which are the only figures it has left.
                dormant.append((gone, doc, played))
            continue
        high = gap_band(recent)[1]
        if high is None or high <= 0 or n <= high:
            continue
        # The band's upper edge above is the gate -- past it, the song is later
        # than it usually is. The median below is the scale everything is then
        # measured and ranked on, because it is the gap a reader would call
        # this song's usual, and it is the one printed on the row.
        med = _median(recent)
        if not med:
            continue
        rows.append((n / med, n, med, doc, played[-1]))
    rows.sort(key=lambda r: -r[0])
    # Past its own norm is necessary and not sufficient. A multiple alone put
    # Rise/Come Together top of the list at 12.8x -- gone 184 shows and four
    # years, which nobody is expecting on any given night; meanwhile The
    # Howling, gone 36 shows after twenty-one performances in four years, sat
    # ninth. Both are correctly measured and only one of them is *due*.
    #
    # The cap is the site's existing bustout line rather than a new number,
    # because it already answers this exact question: a song whose return
    # phish.net would call a bustout is not merely late.
    #
    # The unit is shows, not days, and that is what keeps this honest as the
    # band's rate changes -- a gap of 36 shows is 36 chances to hear it whether
    # they took eight months or two years. The band played a mean of 94.7 shows
    # a year across 1990-2000 and 43.8 across 2021-2025, so 100 shows was about
    # 1.1 years then and is about 2.3 now. Counting in shows absorbs that;
    # counting in days would not. Note the decline is not ongoing: 3.0 averaged
    # 40.0 a year and 4.0 averages 43.8, and the last five complete years run
    # 36, 46, 49, 41, 47. The drop happened at the 2000 hiatus, not since.
    shelved = [r for r in rows if r[1] >= BUSTOUT_GAP]
    live = [r for r in rows if r[1] < BUSTOUT_GAP]
    # Both tests, and the cadence one matters as much as the multiple: a song
    # too rare to expect on any given night is not due however neatly its
    # multiple reads. Partitioned in one pass rather than by testing
    # membership of `due`, which would compare the archived documents inside
    # each row field by field.
    due, overdue = [], []
    for r in live:
        expected = r[2] <= DUE_CADENCE and r[0] < DUE_MULTIPLE
        (due if expected else overdue).append(r)
    return due, overdue, shelved, dormant


def rotation_split(dormant):
    """The fourth list, split by whether there was ever a rotation to leave.

    due_rows answers "is anyone expecting this tonight", and for all 281 of
    these the answer is no -- which is why they came back in one list. But no
    is not one fact. 126 of them have been played exactly once, ever, and 42 of
    those 126 were played on a Halloween night as part of a costume set: songs
    performed once by design, which never had a habit and so cannot have
    stopped. Filing them under a word that means "it used to be otherwise" was
    the page's largest single claim and it was false about nearly half its rows.

    Split on plays rather than on anything to do with the silence, because the
    silence is the same fact for all three and the plays are what differ -- see
    ROTATION_PLAYS and FEW_PLAYS for the two measurements that place the lines.

    Returns (stopped, rare, few), exclusive and in that order, each holding the
    same (gone, doc, played) rows due_rows built. One split, shared by the page
    and by the due page's hero cell above it, for the reason due_rows itself is
    shared: a second copy is a second chance for the two to disagree about how
    many songs are dormant, and this site has already paid for that once.
    """
    parts = ([], [], [])
    for row in dormant:
        parts[rotation_group(len(row[2]))].append(row)
    return parts


def rotation_group(plays):
    """Which of the three ROTATION_SECTIONS a song belongs to, as an index.

    The only place the two thresholds are ever compared against a count. The
    page groups with it and a song page's badge is named from it, so a song
    cannot be filed under one heading and stamped with another word -- which is
    the failure this file keeps paying for in other shapes, and the reason
    due_rows is one function rather than three.
    """
    if plays >= ROTATION_PLAYS:
        return 0
    return 2 if plays <= FEW_PLAYS else 1


def rotation_word(plays):
    """What a single song's own page calls itself once it has gone quiet.

    Sharper than the section heading where it can be. "Once or twice" is the
    only honest name for a group holding both, but a song page knows which of
    the two this song is, so it says "one-off" or "played twice" -- not a
    disagreement with the heading above it, a refinement of it. Every one of
    those words comes from FEW_NAMES; none is written out here.

    Empty for a song with no *counted* performances, which is nine of the 589:
    Day Tripper, My Sharona, Watcher of the Skies and six others exist in this
    archive only as soundchecks, and a soundcheck is not a night the band
    played. They have no play count to be named by, and the box that would
    carry the word simply says nothing -- the same answer this file gives
    everywhere else it cannot support a claim. Found by a KeyError on the first
    build after the words moved into a table: worth stating rather than
    silently guarding, because it is the one input the table cannot spell.
    """
    if plays < 1:
        return ""
    badge = ROTATION_SECTIONS[rotation_group(plays)][2]
    return badge or FEW_NAMES[plays].badge


def _due_row(over, n, high, doc, last):
    """One row, shared by the due list and the shelf under it.

    The list is ranked by how far past its own norm each song is, and it used
    to print only the two numbers that ratio is made of -- so the order looked
    like no order: not by date, not by gap, not by name.

    The ratio is the headline figure rather than a caption under the raw count,
    because the loudest number in a column is the one a reader takes the order
    from. Ranked by the ratio and headlined by the count, the column read 184,
    131, 176, 90 down the page and denied on sight that it was sorted at all.
    One decimal, because the difference between 12.8 and 12.1 is the difference
    between two adjacent rows.

    The figure printed is the song's median recent gap, which is the one a
    reader would call its usual, and the one the multiple beside it is computed
    against. It used to be the top of the song's usual range -- the gate for "is
    it late at all" -- and that was both harder to read and misleading as a
    scale: Show of Life's upper edge was 53.8 against a median of 29.5, and Mr.
    Completely looked mildly late at 1.8x that edge while being gone 98 shows
    against a typical gap of 15.
    """
    place = ", ".join(x for x in (last.get("city"), last.get("state")) if x)
    return ("<li><a class='row' href='./song/%s.html'>"
            "<span class='d-song'>%s</span>"
            "<span class='d-last'><span class='d-date'>%s</span>"
            "<span class='d-where'>%s</span></span>"
            "<span class='d-n'><b>%s&times;</b>"
            # Two lines by construction rather than by wrapping. As one run it
            # was thirty characters in an eleven-rem column and broke wherever
            # it broke -- "usually back" then a stranded "by 14.4". Each line
            # is now a whole statement: how long it has been, and what normal
            # is for this song.
            # "usually every 5.5" beside "93 shows" was two numbers arguing in
            # one row -- a song gone 93 shows is plainly not being played every
            # 5.5. It is a noun now, not a claim about the present: this is the
            # song's usual gap over the ten-year window, and the sections say
            # so where the two figures are far apart.
            "<span class='typ'><span>%s shows since</span>"
            "<span>usual gap %s</span></span>"
            "</span></a></li>"
            % (html.escape(doc["slug"], quote=True),
               html.escape(typographic(doc["song"])),
               last["date"], html.escape(place),
               _stat(over), "{:,}".format(n), _stat(high)))


def render_due(docs, counting, since, card=None):
    """The page listing what is overdue going into tonight."""
    due, overdue, shelved, dormant = due_rows(docs, counting, since)

    out = [_due_row(*r) for r in due]

    # Each list is shown rather than counted. The three say different things
    # about a song and a reader arriving at "what should I shout for" wants to
    # see the boundary, not be told a number on the far side of it.
    def section(anchor, title, blurb, rows):
        if not rows:
            return ""
        # Wrapped, for the reason render_dormant records at length: `.lhead` is
        # sticky at top:0 and a sticky element is held by its parent, so three
        # of them sharing one parent meant each stayed pinned for the rest of
        # the page and Slipping's column header sat ruled across the words "On
        # the shelf". Found on the out-of-rotation page, where 281 rows make it
        # obvious; it was here first, under 43.
        return ("<section class='rot'>"
                "<h2 class='shelf-h' id='%s'>%s</h2>"
                "<p class='dek'>%s</p>"
                "<div class='lhead due-h'><span>Song</span>"
                "<span>Last played</span><span class='end'>How late</span></div>"
                "<ol class='due'>%s</ol>"
                "<p class='backtop'><a href='#top'>&uarr; Back to top</a></p>"
                "</section>"
                % (anchor, title, blurb, "\n".join(_due_row(*r) for r in rows)))

    shelf = section(
        "slipping", "Slipping",
        # Trimmed to the two sentences that define the boundary a reader has
        # just crossed. What went is the naming rationale -- why "slipping"
        # and not "overdue" -- which is a question about the site's vocabulary
        # rather than about these songs, and which faq.html#due already
        # answers in full. A section blurb earns its space by saying what the
        # section is; it does not have to defend its own title.
        "Well past their usual gap rather than a little past it. These could "
        "turn up, and they could equally be on their way out of rotation "
        "&mdash; either way they are not what anybody is expecting tonight. "
        "The usual gap beside each one is measured over the last ten years of "
        "its performances, so for a song this far past it, read it as the "
        "schedule the song <em>was</em> on.",
        overdue)
    shelf += section(
        "shelf", "On the shelf",
        "Gone more than %d shows &mdash; long enough that the habit they are "
        "being measured against has probably stopped being true. Note this is "
        "not the same as saying their return would be a bustout: these songs "
        "all still have a recent record, and this site reserves that word for "
        "songs that do not." % BUSTOUT_GAP,
        shelved)

    # The same hero vocabulary the index uses, counting the four categories and
    # linking to all four. All four land on this page now, which is the point:
    # three of these cells took a reader to a section and the fourth left the
    # site's longest page for another one, so the hero was three doors and an
    # exit dressed the same.
    #
    # The fourth cell used to read "Dormant 54", and that was the figure being
    # careful while the label was not. It counted only the songs that were in
    # rotation and left it -- correct for the word, but it sat above a
    # paragraph about 281 songs and beside a link to a page titled *Out of
    # rotation*, so the one number on screen was the one nothing else on the
    # page was talking about. Under the umbrella term the count is the
    # umbrella's: 281, matching the section it now opens, which then hands off
    # to the page that separates the three.
    stopped, rare, few = rotation_split(dormant)
    cards = [(len(due), "Due", " hot", "#main"),
             (len(overdue), "Slipping", "", "#slipping"),
             (len(shelved), "On the shelf", "", "#shelf"),
             (len(dormant), "Out of rotation", "", "#rotation")]
    hero = hero_html(cards)

    n_due = len(due)
    subtitle = ("%d song%s you might reasonably expect tonight"
                % (n_due, "" if n_due == 1 else "s"))
    # The fourth group, promoted out of the trailing paragraph it had been
    # bolted to. It was the only one of this page's four with no heading, no
    # rule above it and no place in the hero -- so a reader who had scrolled
    # 38 rows of Slipping and On the shelf met the largest group on the page as
    # an unannounced sentence after the last list, or, far more likely, never
    # scrolled that far and never met it. Ian: "a reader would have to scroll
    # all the way down to the end to happen upon them. And then there's not
    # even a section heading to call out what they're about to read." Same
    # furniture as the two sections above it, so it reads as the fourth thing
    # rather than as a footnote about the third.
    #
    # Two copy repairs while it moved, both of them Ian's:
    #
    # "That page keeps them apart" -- a demonstrative with two candidate
    # referents and a stiff one at that, in the last sentence of the page. The
    # link now says where it goes and what is there, which is what the sentence
    # was reaching for.
    #
    # "%d turned up on %s" was grammatical when FEW_TITLE read "one or two
    # nights". It has read "once or twice" since Ian objected to the nights
    # lexicon, and the preposition was left behind: the published page says
    # "174 turned up on once or twice in the band's whole life". This is the
    # cost of interpolating a phrase whose grammar the sentence depends on --
    # the constant changed, every sentence built on it compiled fine, and one
    # of them stopped being English. It reads "were played once or twice" now,
    # which survives the phrase growing a third clause.
    tail = ""
    if dormant:
        tail = (
            "<section class='rot'>"
            "<h2 class='shelf-h' id='rotation'>Out of rotation</h2>"
            "<p class='dek'>Gone long enough that a return would be a "
            "bustout, and with no recent record left to be late against "
            "&mdash; so there is no lateness here to rank, and none of it is "
            "due. There are more of these than in the three lists above put "
            "together, and they are not one population: %d were in rotation "
            "and left it, %d were played a few times across the "
            "band&rsquo;s whole life and never became a habit, and %d were "
            "played %s and never again.</p>"
            "<p class='dek'><a href='./%s'>All %s, grouped by the year each "
            "was last heard</a></p>"
            "<p class='backtop'><a href='#top'>&uarr; Back to top</a></p>"
            "</section>"
            % (len(stopped), len(rare), len(few), FEW_TIMES,
               ROTATION_PAGE, "{:,}".format(len(dormant))))
    blurb = "Phish songs that are overdue, measured against their own habits."
    return DUE_SHELL.format(
        crumb=nav_strip(section="Songs", mark=True),
        analytics=ANALYTICS, ago_js=AGO_JS, new_rows_js=NEW_ROWS_JS,
        css=INDEX_CSS, totop=TOTOP_JS, fonts=WEB_FONTS, sheet=sheet_links("./%s/%s" % (STATIC_DIR, SITE_SHEET)),
        theme_js=THEME_JS, keys_js=KEYS_JS, theme_ui=THEME_UI, cap=BUSTOUT_GAP,
        mult=_stat(DUE_MULTIPLE), hero=hero, hero_cls=hero_cols(len(cards)),
        subtitle=subtitle, rows="\n".join(out), shelf=shelf, dormant=tail,
        share=share_meta("What's due &mdash; Possum Logic",
                         html.escape(blurb, quote=True), "due.html", card=card),
        stamp="Updated %s" % _utcnow().date().isoformat())


DUE_SHELL_END = None


#: The dormant list reuses the due page's row grid wholesale -- .d-song,
#: .d-last, .d-n and .typ, including how they stack on a phone -- so the only
#: rules here are the ones the due page has no use for: the year a song was
#: last heard, and the strip of years at the top.
# A strip of years across the top of a page, each carrying its own count,
# built from the same grouping the headings below it come from so it cannot
# offer a year the body does not hold.
#
# It was named on 2026-07-30 because two pages drew one, and by the time the
# branch merged it had one caller again: the dormant page was regrouped into
# three sections and dropped its strip, which eighteen years had needed and
# three sections did not. Kept as a block rather than folded back into
# YEARS_CSS -- it is the shape a second page wanted once and may want again,
# and a named block with one caller costs nothing while an inlined one has to
# be found and extracted a second time.
YEAR_STRIP_CSS = """/* The years, as a strip. Generated from the same grouping as the headings
   below, so it cannot offer a year the page does not hold. */
.years{margin:1.1rem 0 0;display:flex;flex-wrap:wrap;gap:.4rem}
.years a{font-family:'IBM Plex Mono',ui-monospace,monospace;font-size:.75rem;
   line-height:1;padding:.4rem .5rem;border:1px solid var(--edge);
   color:var(--ink-soft);text-decoration:none;white-space:nowrap}
.years a:hover{color:var(--hot-text);border-color:var(--hot-text)}
.years a b{font-weight:400;color:var(--dim);margin-left:.35rem}
"""


DORMANT_CSS = INDEX_CSS + """
/* One list with the years marked inside it, rather than eighteen lists. A
   heading that is a row of the same ordered list keeps one column header, one
   set of grid tracks, and one thing for a reader to scroll. */
.yr{display:flex;align-items:baseline;gap:.7rem;
   margin:1.8rem 0 .2rem;padding:0 .25rem .35rem;
   border-bottom:1px solid var(--ink)}
.yr:first-child{margin-top:.4rem}
.yr h2{margin:0;font-family:'Bagnard',Georgia,serif;font-weight:400;
   font-size:1.75rem;line-height:1;letter-spacing:-.01em;color:var(--ink)}
.yr .n{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim)}
/* Pushed to the right so the count and the way back sit at the two ends of the
   rule, and the year has the left edge to itself. */
.yr .up{margin-left:auto;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--dim);text-decoration:none;
   border-bottom:1px solid var(--rule);position:relative}
.yr .up::before{content:"";position:absolute;left:50%;top:50%;
   transform:translate(-50%,-50%);width:100%;min-width:24px;height:24px}
.yr .up:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* The strip of jump links that used to sit here is gone with the years it
   pointed at. Eighteen years needed a strip; three sections do not, and the
   hero directly under it already names all three, counts them and links to
   them -- so the two rows said the same three numbers a line apart. The hero
   is the bigger and clearer of the two, so the strip went rather than it. */
/* The span of a song's life, which is the one figure a dormant song has that a
   due song does not need: it was around from here to here, and then it was not. */
.d-n .span{font-variant-numeric:tabular-nums}
/* In ink, not in the accent. The due page sets its figure hot because it is
   the thing the page is sounding an alarm about and the order the list is in.
   Here the figure is neither: the list is ordered by year, and a play count is
   a description rather than a warning. A page of 281 rows all shouting in the
   accent color spends it on everything and therefore on nothing. */
.due.dormant .d-n > b{color:var(--ink)}
"""


DORMANT_SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Out of rotation &mdash; Possum Logic</title>
<meta property="og:type" content="website">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}{ago_js}{new_rows_js}</head><body id="top"><div class="wrap">
<a class="skip" href="#main">Skip to content</a>
{crumb}
<div class="rule2"></div>
<header><h1>Out of rotation</h1>
<p class="show">{subtitle}</p>
<p class="dek">The fourth list on <a href="./due.html">what&rsquo;s due</a>, and
the longest by some way. Every song here has been gone {cap} shows or more
<em>and</em> has fewer than {floor} performances inside the last {years_n}
years, so there is no habit left to be late against and nothing to rank it by.
That is the whole reason it needs a page rather than a place in a list: every
other song on this site is ordered by how far past its own norm it is, and
these have no norm.</p>
<p class="dek">They are not all the same thing, though, and calling them all
<em>dormant</em> said something false about nearly two thirds of them. Dormant
means it used to be otherwise. A song played once at a Halloween show never had
a rotation to fall out of &mdash; and in this archive, that difference is the
strongest thing we know about whether it is ever coming back. So the page is in
three parts, split on how many times the band ever played the song, and
<a href="./method.html#rotation">how this works</a> shows the measurement.</p>
<p class="dek">Inside each part they are ordered by when you last heard one,
newest first, and within a year by how often the band played it. None of it is
a prediction: a song coming back from here is a bustout, and the archive is
full of them &mdash; that is what makes this worth reading rather than a
graveyard.</p></header>
<section class="hero {hero_cls}" aria-label="Sections on this page">{hero}</section>
<div class="rule2"></div>
<div id="main" tabindex="-1">
{rows}
</div>
{totop}
""" + footer_html() + """
{analytics}
</div></body></html>
"""


def _dormant_row(gone, doc, played):
    """One dormant song.

    The same grid as a due row, because it is the same kind of object and the
    reader has just come from that page -- but the third column answers a
    different question. A due song's figure is how far past its norm it is; a
    dormant song has no norm, so the figure is how many times it was ever
    played, which is the one number that separates a staple that stopped from a
    cover played once at a Halloween show.
    """
    last = played[-1]
    place = ", ".join(x for x in (last.get("city"), last.get("state")) if x)
    first_yr, last_yr = played[0]["date"][:4], last["date"][:4]
    span = first_yr if first_yr == last_yr else "%s&ndash;%s" % (first_yr, last_yr)
    return ("<li><a class='row' id='%s' href='./song/%s.html'>"
            "<span class='d-song'>%s</span>"
            "<span class='d-last'><span class='d-date'>%s</span>"
            "<span class='d-where'>%s</span></span>"
            "<span class='d-n'><b>%s&times;</b>"
            "<span class='typ'><span>%s shows since</span>"
            "<span class='span'>%s</span></span>"
            "</span></a></li>"
            % (html.escape(doc["slug"], quote=True),
               html.escape(doc["slug"], quote=True),
               html.escape(typographic(doc["song"])),
               last["date"], html.escape(place),
               "{:,}".format(len(played)), "{:,}".format(gone), span))


#: The three parts of the page, in the order a reader meets them: the songs the
#: word "dormant" was always about first, then the two populations it was wrong
#: about. Each is (anchor, title, blurb). The anchors are also what the hero
#: cells above them link to, and what the due page's Dormant cell links to, so
#: renaming one moves three things.
#:
#: The third field is what a single song's page stamps on itself -- see
#: rotation_word. It is None for the last section because that one holds two
#: play counts and the sharper word depends on which; FEW_NAMES has them.
ROTATION_SECTIONS = (
    ("dormant", "Dormant", "dormant",
     "Played {floor} times or more, and then not at all. These had a rotation "
     "and left it, which is the only case where the word means what it says. "
     "They are also the likeliest to come back: of every long silence in this "
     "archive that began after {floor} or more performances, {rate}% has since "
     "been ended by another one."),
    ("rarities", "Rarities", "rarity",
     # "The band gave these a run and it did not take" went at Ian's reading:
     # it casts every performance as a trial aimed at sticking, and files the
     # outcome as a failure at something nobody said was being attempted. A
     # cover played twice on one tour was not an audition. What the archive
     # supports is the count and nothing about intent, which is what the clause
     # that survived already said.
     "More than {few} performances and fewer than {floor} &mdash; enough of a "
     "habit to notice, never enough to break. Some are covers taken out for "
     "one tour; some are originals that never found a place in a set. "
     "{rate}% have come back."
     "</p><p class='dek'>This is the one section where <em>when</em> the plays happened "
     "changes the answer. Read the years at the right of each row: a song "
     "whose handful of performances sat close together came back {tight}% of "
     "the time, and one whose were strewn across decades only {loose}%."),
    ("once-or-twice", FEW_TITLE, None,
     "{tally} &mdash; and then never "
     "again. These never had a rotation to fall out of, so <em>dormant</em> "
     "was never the word. A third of the single plays were a Halloween "
     "costume set, which is a song performed once by design. {rate}% ever "
     "return, the lowest figure on the page, and the honest reading of a row "
     "here is that you have already heard the whole story."
     "</p><p class='dek'>Two plays sit here with one because the archive says they are the "
     "same object: whether the pair was three shows apart or thirteen hundred, "
     "the song came back about as rarely either way. The years at the right of "
     "the row tell you which it was &mdash; a single year is a song they tried "
     "twice one summer, a range is a one-off someone revived a lifetime "
     "later."),
)

#: The return rates quoted in the blurbs above and on the method page. Measured
#: over every silence of BUSTOUT_GAP or more in the archive on 2026-07-30 --
#: 774 of them -- as the share that was ever ended by another performance. Held
#: as a constant rather than recomputed per build for the same reason the page
#: does not predict: it is a statement about the archive at a moment, and a
#: figure that drifts by a point every show reads as a forecast. See
#: ROTATION_PLAYS, and docs/TODO.md §2j for the scripts that produced it.
ROTATION_RETURN = {"dormant": 84, "rarities": 65, "once-or-twice": 30}

#: Within the rarities, the same figure split by how tightly the song's few
#: performances sat: at most 200 counting shows per play against more than
#: that. 70% and 38%, n=132 and n=21. The equivalent split on the once-or-twice
#: group is 36% against 27% -- close enough to be worth saying it does not
#: matter there, which is what that blurb says.
RARITY_TIGHT, RARITY_LOOSE = 70, 38


def _rotation_years(rows, anchor):
    """One section's rows, grouped by the year each song was last heard.

    Anchors carry the section, because a year appears in all three and an id
    has to be unique in a document -- #y2019 would have resolved to whichever
    of the three came first, which is the section a reader was least likely to
    want.
    """
    years = {}
    for row in rows:
        years.setdefault(row[2][-1]["date"][:4], []).append(row)
    body = []
    for year, group in sorted(years.items(), reverse=True):
        # Inside a year, most-played first: that is the order of "would I
        # remember this?", and there is no other order available -- none of
        # these songs has a usual range to be sorted on.
        group.sort(key=lambda r: (-len(r[2]), typographic(r[1]["song"])))
        body.append(
            "<li class='yr' id='%s-%s'><h2>%s</h2>"
            "<span class='n'>%d song%s</span>"
            "<a class='up' href='#top'>&uarr; Top</a></li>"
            % (anchor, year, year, len(group), "" if len(group) == 1 else "s"))
        body.extend(_dormant_row(*r) for r in group)
    return "\n".join(body)


def render_dormant(docs, counting, since, card=None):
    """Every song out of rotation, split by whether it ever had one."""
    parts = rotation_split(due_rows(docs, counting, since)[3])

    # Two of the blurbs quote the shape of their own section back at the
    # reader, so the figures come from the rows rather than from prose that
    # would go quietly stale the first time a song moved between sections.
    # "126 played once, 48 played twice", one clause per play count the last
    # section holds. Counted off the rows and worded from FEW_NAMES, because
    # written out it was a third place spelling FEW_PLAYS = 2 by hand -- the
    # same trap as the heading, in the sentence directly under it.
    counts = collections.Counter(len(r[2]) for r in parts[2])
    tally = _join_clauses(
        ["{:,} played {}".format(counts[n], FEW_NAMES[n].times)
         for n in range(1, FEW_PLAYS + 1) if counts[n]], "and")

    body = []
    for (anchor, title, _badge, blurb), rows in zip(ROTATION_SECTIONS, parts):
        if not rows:
            continue
        # The same furniture the due page puts above each of its lists -- the
        # heading, the note, the column header, the way back up -- because this
        # is the same object and the reader has just come from that page.
        #
        # Each part is wrapped, and the wrapper is load-bearing rather than
        # tidiness. `.lhead` is position:sticky, top:0, and a sticky element is
        # held by its *parent*: with all three headers sharing one parent, each
        # stayed pinned for the whole rest of the page, so scrolling into
        # Rarities showed the Dormant column header ruled straight across the
        # word "Rarities". A parent per part means a header lets go when its
        # own list ends. Measured, not reasoned: three .lhead, one containing
        # block, top:0 on all of them.
        body.append(
            "<section class='rot'>"
            "<h2 class='shelf-h' id='%s'>%s</h2><p class='dek'>%s</p>"
            "<div class='lhead due-h'><span>Song</span>"
            "<span>Last played</span><span class='end'>Times played</span></div>"
            "<ol class='due dormant'>%s</ol>"
            "<p class='backtop'><a href='#top'>&uarr; Back to top</a></p>"
            "</section>"
            % (anchor, title,
               blurb.format(floor=ROTATION_PLAYS, few=FEW_PLAYS,
                            rate=ROTATION_RETURN[anchor],
                            tight=RARITY_TIGHT, loose=RARITY_LOOSE,
                            tally=tally),
               _rotation_years(rows, anchor)))

    # Three counts and a row. The counts are the page's argument -- that these
    # are three populations and not one -- so they lead, and each links to the
    # section it counts. Longest gone keeps the fourth cell because it is the
    # one figure here that is a superlative rather than a total, and it is the
    # cell that found the Windora Bug anchoring bug. "Most played" gave up its
    # place: it is now the first row of the first section, three lines below.
    #
    # The third cell carries the section heading verbatim, which it could not
    # when that heading was three words long: a hero label is a caption set at
    # .625rem in caps, and the old "ONE OR TWO NIGHTS" wrapped to two lines at
    # every width the site supports while its three neighbors held one.
    # "ONCE OR TWICE" fits, so the cell and the heading it links to are now
    # one string rather than an abbreviation and its original.
    stopped, rare, few = parts
    dormant = stopped + rare + few
    longest = max(dormant, key=lambda r: r[0]) if dormant else None
    cards = [(len(stopped), "Dormant", "", "#dormant"),
             (len(rare), "Rarities", "", "#rarities"),
             (len(few), FEW_TITLE, "", "#" + ROTATION_SECTIONS[2][0]),
             ("{:,}".format(longest[0]) if longest else "n/a", "Longest gone",
              " hot", "#%s" % longest[1]["slug"] if longest else "")]
    hero = hero_html(cards)

    n = len(dormant)
    # "in three kinds" was Ian's: "'of three types,' or 'in three categories,'
    # maybe, but 'in three kinds' feels like an awkward phrase." It is -- kind
    # takes *of*, and the page's own furniture already had the plain word for
    # what these are, since the three things below this line are three groups
    # of rows.
    subtitle = ("%s song%s the band is not playing, in three groups"
                % ("{:,}".format(n), "" if n == 1 else "s"))
    blurb = ("Every Phish song that has dropped out of rotation, split by "
             "whether it ever had one.")
    return DORMANT_SHELL.format(
        crumb=nav_strip(section="Songs", mark=True),
        analytics=ANALYTICS, ago_js=AGO_JS, new_rows_js=NEW_ROWS_JS,
        css=DORMANT_CSS, totop=TOTOP_JS, fonts=WEB_FONTS, sheet=sheet_links("./%s/%s" % (STATIC_DIR, SITE_SHEET)),
        theme_js=THEME_JS, keys_js=KEYS_JS, theme_ui=THEME_UI, cap=BUSTOUT_GAP,
        floor=MIN_HISTORY, years_n=RECENT_YEARS,
        hero=hero, hero_cls=hero_cols(len(cards)), subtitle=subtitle,
        rows="\n".join(body),
        share=share_meta("Out of rotation &mdash; Possum Logic",
                         html.escape(blurb, quote=True), ROTATION_PAGE, card=card),
        stamp="Updated %s" % _utcnow().date().isoformat())


NOT_A_SHOW_SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Not a show &mdash; Possum Logic</title>
<meta property="og:type" content="website">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}{ago_js}{new_rows_js}</head><body id="top"><div class="wrap">
<a class="skip" href="#main">Skip to content</a>
{crumb}
<div class="rule2"></div>
<header><h1>Not a show</h1>
<p class="show">{subtitle}</p>
<p class="dek">Soundchecks, and television and radio sessions. phish.net lists
these and marks them as excluded from statistics, so they are absent from the
show calendar this site counts with &mdash; no gap here counts them, no
verdict is measured over them, and the figures on their own pages describe the
entry rather than a show the band played. They are kept because they happened:
five songs the band has otherwise never touched exist only here, and a handful
of these performances circulated well enough to be rated among the best
versions of their song.</p>
<p class="dek">The line is phish.net's rather than this site's, and they are
not consistent about it across their whole history &mdash; of the studio, TV
and radio sessions in the song histories, some count and some do not, split
roughly at 1999. This site defers to their flag rather than inventing a rule,
so where they disagree with themselves it disagrees in exactly the same
places, which is at least auditable.
<a href="./method.html#which-show-this-was">How this works</a> has the rest of
it, including why there is no honest total for how many shows the band has
played.</p></header>
<section class="hero {hero_cls}">{hero}</section>
<div class="rule2"></div>
<div id="main" tabindex="-1">{body}</div>
{totop}
""" + footer_html() + """
{analytics}
</div></body></html>
"""


def not_a_show_rows(aside, page_href):
    """The soundchecks and the sessions, each as a row that goes somewhere.

    With phish.net's note, which on these entries is the whole point and not
    decoration. All twenty carry one, they run 53 to 778 characters with a
    median of 253, and they are where the interesting thing about a soundcheck
    is recorded: that Magnaball's was a single 46-minute jam, that Festival 8's
    was two soundchecks in a day, and that the Bethel Woods tech rehearsal
    produced the Waves that got released on From the Archives. A rated-versions
    list cannot show any of that, because fouldomain scores almost none of
    these performances -- the Bethel Waves included.
    """
    out = {"before": [], "own": []}
    for a in sorted(aside, key=lambda a: a["report"]["date"], reverse=True):
        r, kind = a["report"], a["kind"]
        n = len(r.get("songs") or [])
        note = re.sub(r"<[^>]+>", "", html.unescape(str(r.get("notes") or ""))).strip()
        before = kind in BEFORE_A_SHOW
        # One of these exists because of the show after it, so it says which.
        # A taping or a ceremony does not -- it is its own occasion, and
        # pointing it at the next concert on the calendar would invent a
        # relationship out of nothing but the calendar's order.
        link = ("<span class='for'>before <a href='%s'>%s</a></span>"
                % (page_href % a["before"], a["before"])
                if before and a["before"] else "")
        out["before" if before else "own"].append(
            "<li><a class='ax-row' href='%s'><span class='ax-date'>%s</span>"
            "<span class='ax-kind'>%s</span>"
            "<span class='ax-venue'>%s</span>"
            "<span class='ax-n'>%d song%s</span></a>%s%s</li>"
            % (page_href % r["date"], r["date"],
               KIND_LABEL.get(kind, kind).lower(),
               html.escape(r.get("venue") or ""), n, "" if n == 1 else "s",
               link,
               "<span class='ax-note'>%s</span>" % linkify(html.escape(note))
               if note else ""))
    return out


def never_at_a_show(docs, counting):
    """Songs the band has played, but never at a show. -> rows, newest first.

    Nine of them, and five are one afternoon: a soundcheck at The Woodlands on
    2024-08-14 that produced five covers Phish has otherwise never touched.
    They are invisible everywhere else on the site -- `due_rows` drops any song
    with no counted performance before it classifies anything, so they are not
    on the due page or among the out-of-rotation three, and until this page
    they existed only as a row on the songs index reading "never at a show".
    """
    rows = []
    for doc in docs:
        perfs = doc.get("performances") or []
        if not perfs or any(p["date"] in counting for p in perfs):
            continue
        rows.append((perfs[-1]["date"], doc, perfs))
    rows.sort(key=lambda r: (r[0], typographic(r[1]["song"])), reverse=True)
    return rows


def rated_off_stage(docs, counting):
    """Rated versions that were not played at a show. -> rows, best first.

    Ian's: "in rare cases, they get circulated and gain favor." They do, and
    the archive can show it, because fouldomain scores every circulating
    performance rather than every show -- so a soundcheck that got out is
    scored beside the concerts. Fourteen of them, and one is the highest-rated
    version of its song.

    Not every piece of lore survives contact with this, and the limit is worth
    stating where it will be read: phish.net logs almost none of these
    setlists. The IT soundcheck is two songs in this archive, so the versions
    people actually argue about from that afternoon are not reachable here at
    all.
    """
    rows = []
    for doc in docs:
        best = doc.get("best") or []
        # 1-based, and the count of the list it sits in. A first pass at this
        # enumerated from zero and reported the ranks one too low, which turned
        # "My Soul's second-best version is a soundcheck" into "its best is" --
        # a claim about the whole archive resting on an index. The rank travels
        # with its denominator here so nothing downstream can restate it.
        for rank, b in enumerate(best, 1):
            if b.get("date") and b["date"] not in counting:
                rows.append((b["score"], rank, len(best), doc, b))
    rows.sort(key=lambda r: (-r[0], typographic(r[3]["song"])))
    return rows


def render_not_a_show(reports, docs, calendar, page_href="./show/%s.html",
                      card=None):
    """Everything the band played that was not a show, and what came of it."""
    counting = set(calendar)
    _, aside = split_archive(reports, calendar)
    lists = not_a_show_rows(aside, page_href)
    never = never_at_a_show(docs, counting)
    rated = rated_off_stage(docs, counting)
    kinds = {a["report"]["date"]: a["kind"] for a in aside}

    def section(anchor, title, blurb, body):
        return ("<section class='rot'>"
                "<h2 class='shelf-h' id='%s'>%s</h2><p class='dek'>%s</p>"
                "%s<p class='backtop'><a href='#top'>&uarr; Back to top</a></p>"
                "</section>" % (anchor, title, blurb, body))

    body = section(
        "before", "Before a show",
        "The band in the room before the doors, and each one names the show "
        "it came before &mdash; that is the whole reason it happened. Twelve "
        "are soundchecks. The thirteenth is the 2011 Bethel Woods <b>tech "
        "rehearsal</b>, which this site called a soundcheck until Ian pointed "
        "out that it is not one: a soundcheck is the afternoon of a concert, "
        "a rehearsal is for a run. phish.net&rsquo;s note says which, so the "
        "rows say which.",
        "<ol class='axlist'>%s</ol>" % "".join(lists["before"]))
    body += section(
        "own", "Occasions of their own",
        "Not attached to any concert: five television appearances, "
        "NPR&rsquo;s Tiny Desk, and the night in 2010 when Phish played two "
        "Genesis songs at the Waldorf Astoria and Trey made the case for "
        "inducting them into the Rock and Roll Hall of Fame. That last one "
        "was filed as a <em>session</em> until the same read-through, and a "
        "ceremony is not a session either.",
        "<ol class='axlist'>%s</ol>" % "".join(lists["own"]))
    if never:
        body += section(
            "never", "Never at a show",
            "%d songs the band has played, and never once at a concert. Five "
            "of them are a single afternoon &mdash; the covers soundcheck at "
            "The Woodlands on 2024-08-14. These are the only songs on this "
            "site with no gap, no median and no verdict, because every figure "
            "here is counted in shows and they have none."
            % len(never),
            "<ol class='axlist'>%s</ol>" % "".join(
                "<li><a class='ax-row' href='./song/%s.html'>"
                "<span class='ax-date'>%s</span>"
                "<span class='ax-kind'>%s</span>"
                "<span class='ax-venue'>%s</span></a>"
                "<span class='for'>%s</span></li>"
                % (html.escape(doc["slug"], quote=True),
                   html.escape(typographic(doc["song"])),
                   kinds.get(date, "not a show"),
                   html.escape(perfs[-1].get("venue") or ""), date)
                for date, doc, perfs in never))
    if rated:
        # The best-placed of them, computed rather than written down: whether
        # any of these ever beats every concert version of its song is exactly
        # the interesting question, and it is one a rebuild can change.
        top = min(rated, key=lambda r: r[1])
        claim = (
            "<b>%s</b> is rated above every concert version of itself."
            % html.escape(typographic(top[3]["song"])) if top[1] == 1 else
            "None of them is its song&rsquo;s best version. The closest is "
            "<b>%s</b>, at no.&nbsp;%d of the %d versions of it fouldomain "
            "rates highest."
            % (html.escape(typographic(top[3]["song"])), top[1], top[2]))
        body += section(
            "rated", "Rated away from the stage",
            "fouldomain scores every performance that circulates rather than "
            "every show, so a soundcheck that got out is scored beside the "
            "concerts. These are the %d that did. %s A rank here is within "
            "that song&rsquo;s own rated versions, which is the only honest "
            "way to read a score that is fouldomain&rsquo;s rather than this "
            "site&rsquo;s."
            "</p><p class='dek'>A score is not the only evidence that one of "
            "these got out, and on the strength of the notes above it is not "
            "the best. The Waves from the 2011 Bethel Woods tech rehearsal was "
            "released on Kevin Shapiro&rsquo;s <em>From the Archives</em> and "
            "phish.net calls it stunning &mdash; and fouldomain has no score "
            "for it, so it is not in this list. Read the notes for the ones "
            "that circulated; this list is only the ones that were also "
            "rated."
            % (len(rated), claim),
            "<ol class='axlist'>%s</ol>" % "".join(
                "<li><a class='ax-row' href='./song/%s.html#%s'>"
                "<span class='ax-date'>%s</span>"
                "<span class='ax-kind'>%s</span>"
                "<span class='ax-venue'>%s</span></a>"
                "<span class='for'>%s &middot; rated <b>%d</b>, "
                "no.&nbsp;%d of %d</span></li>"
                % (html.escape(doc["slug"], quote=True), b["date"],
                   html.escape(typographic(doc["song"])),
                   kinds.get(b["date"], "not a show"),
                   html.escape(b.get("venue") or ""), b["date"], score,
                   rank, of)
                for score, rank, of, doc, b in rated))

    n_b, n_o = len(lists["before"]), len(lists["own"])
    cards = [(n_b, "Before a show", "", "#before"),
             (n_o, "On their own", "", "#own"),
             (len(never), "Never at a show", " hot", "#never"),
             (len(rated), "Rated versions", "", "#rated")]
    # Counted off the rows rather than written out, and spelled from the same
    # labels the rows carry -- this line named two kinds when there were five.
    tally = collections.Counter(a["kind"] for a in aside)
    subtitle = ("%d entr%s &middot; %s"
                % (n_b + n_o, "y" if n_b + n_o == 1 else "ies",
                   _join_clauses(
                       ["%d %s" % (n, KIND_COUNTED[k][0 if n == 1 else 1])
                        for k, n in tally.most_common() if n], "and")))
    blurb = ("Every Phish soundcheck and session the archive holds, the songs "
             "that exist only there, and the versions that got out.")
    return NOT_A_SHOW_SHELL.format(
        crumb=nav_strip(section="Shows", mark=True),
        analytics=ANALYTICS, ago_js=AGO_JS, new_rows_js=NEW_ROWS_JS,
        css=INDEX_CSS, totop=TOTOP_JS, fonts=WEB_FONTS,
        sheet=sheet_links("./%s/%s" % (STATIC_DIR, SITE_SHEET)),
        theme_js=THEME_JS, keys_js=KEYS_JS, theme_ui=THEME_UI,
        hero=hero_html(cards), hero_cls=hero_cols(len(cards)),
        subtitle=subtitle, body=body,
        share=share_meta("Not a show &mdash; Possum Logic",
                         html.escape(blurb, quote=True), NOT_A_SHOW_PAGE, card=card),
        stamp="Updated %s" % _utcnow().date().isoformat())


VENUES_SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Venues &mdash; Possum Logic</title>
<meta property="og:type" content="website">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}{ago_js}{new_rows_js}</head><body id="top"><div class="wrap">
<a class="skip" href="#main">Skip to content</a>
{crumb}
<div class="rule2"></div>
<header><h1>Venues</h1>
<p class="show">{subtitle}</p>
<p class="dek">Every room the archive holds a report from, most nights first.
A venue opens the show list filtered to it rather than a page of its own: the
search is already that page, and one that cannot fall out of step with the
archive. What is here is what a search cannot tell you &mdash; how many nights,
over what span, and the longest gap the room has heard.</p></header>
<div class="rule2"></div>
<div class="lhead vn-h"><span>Venue</span>
<span>First to last</span><span class="end">Nights</span></div>
<ol class="vn" id="main" tabindex="-1">
{rows}
</ol>
{totop}
""" + footer_html() + """
{analytics}
</div></body></html>
"""


def render_venues(reports, card=None):
    """Every venue the archive holds a report from, most nights first.

    Deliberately not a page tree. The ruling was that URL-addressable search
    gets a reader to one venue's shows with no new build output and nothing to
    fall out of sync, and it does -- so each row here is a search, not a page.
    What this adds is the part a search cannot: the counts and the spans, in
    one place, ranked.
    """
    by_venue = {}
    for e in (summarize(r) for r in reports):
        if e["venue"]:
            by_venue.setdefault(e["venue"], []).append(e)

    rows = []
    for venue, shows in sorted(by_venue.items(),
                               key=lambda kv: (-len(kv[1]), kv[0])):
        shows.sort(key=lambda e: e["date"])
        # The most recent spelling of where the room is. Cities get renamed and
        # reports from the eighties spell them differently; the latest report
        # is the one to believe.
        place = next((e["place"] for e in reversed(shows) if e["place"]), "")
        span = ("%s &rarr; %s" % (shows[0]["date"], shows[-1]["date"])
                if len(shows) > 1 else shows[0]["date"])
        longest = max((e["longest"] for e in shows if e["longest"]), default=None)
        # Quoted, so the index matches the name as a phrase rather than as
        # loose words: unquoted, "Key Arena" answers with every arena that
        # also has a "key" somewhere in its setlist, and the two rooms called
        # The Wharf Amphitheater and Amphitheater at the Wharf each return the
        # other's nights. The name is not lowercased -- both sides are folded
        # before they meet, so the box can show the room as it is spelled.
        href = "./index.html?q=%s" % urllib.parse.quote('"%s"' % venue)
        rows.append(
            "<li><a class='row' href='%s'>"
            "<span class='vn-venue'>%s<span class='vn-place'>%s</span></span>"
            "<span class='vn-span'>%s</span>"
            "<span class='vn-n'><b>%d</b><span class='typ'>%s</span></span>"
            "</a></li>"
            % (html.escape(href, quote=True),
               html.escape(venue), html.escape(place), span, len(shows),
               # "longest", not "longest gap": the index rows already say it
               # that way, and the extra word wrapped the four-figure gaps onto
               # a second line while the three-figure ones stayed on one.
               ("longest %s" % _stat(longest)) if longest
               else "no gap on file"))

    n = len(by_venue)
    total = sum(len(s) for s in by_venue.values())
    subtitle = ("%d venue%s, %s night%s"
                % (n, "" if n == 1 else "s",
                   "{:,}".format(total), "" if total == 1 else "s"))
    blurb = ("Every venue in the archive: %d of them, over %s nights."
             % (n, "{:,}".format(total)))
    return VENUES_SHELL.format(
        crumb=nav_strip(here="Venues", mark=True),
        analytics=ANALYTICS, ago_js=AGO_JS, new_rows_js=NEW_ROWS_JS,
        css=INDEX_CSS, totop=TOTOP_JS, fonts=WEB_FONTS, sheet=sheet_links("./%s/%s" % (STATIC_DIR, SITE_SHEET)),
        theme_js=THEME_JS, keys_js=KEYS_JS, theme_ui=THEME_UI,
        subtitle=subtitle, rows="\n".join(rows),
        share=share_meta("Venues &mdash; Possum Logic",
                         html.escape(blurb, quote=True), "venues.html",
                         card=card),
        stamp="Updated %s" % (max((e["date"] for s in by_venue.values()
                                   for e in s), default="&mdash;")))


def due_card(docs, counting, since):
    """The due page's preview: how many, and the one furthest past its norm."""
    rows, _overdue, _shelved, _dormant = due_rows(docs, counting, since)
    # The head of the due list, which is the song furthest past its norm among
    # the ones still close enough to it to be expected. Not the furthest past
    # overall -- that song is under Overdue or on the shelf, and the card would
    # headline something the page it previews does not lead with.
    best = rows[0] if rows else None
    return card_markup(
        "Phish", "What&rsquo;s <em>due</em>", "Songs you might expect tonight",
        (("%d" % len(rows), "Songs due", ""),
         ("%s&times;" % _stat(best[0]) if best else "&mdash;",
          html.escape(typographic(best[3]["song"][:22])) if best else "Most due",
          "hot")),
        size=104)


def render_songs(docs, stamp=None, card=None, counting=None,
                 n_due=None, n_rotation=None):
    """One page listing every song the archive holds a history for.

    Every figure here counts *shows*, which is what the rest of the site
    counts and what this page did not. A soundcheck, a Tonight Show slot and a
    Tiny Desk are performances and they are in the archive, but they are not
    shows -- the index files them in a list of their own, `due_rows` leaves
    them out of every verdict, and each song's own page has always ignored
    them: My Sharona's page says "0 performances" while this page said it had
    been played once, and the two are one click apart.

    The order matters as much as the filter, and it is the order that was
    wrong. Drop the uncounted performances *first*, then drop the first of
    what is left -- because that first one carries phish.net's debut "gap",
    which is the number of shows the band played before the song existed
    rather than a silence. Skipping row 0 of the raw list skips the debut gap
    only when the song's first appearance was at a show; for the 45 songs that
    first turned up at a soundcheck the debut gap sat on row 1, untouched, and
    42 of them published it as their longest gap. Gone read 1,468 where the
    truth is 49.
    """
    rows, entries = [], []
    for doc in docs:
        perfs = doc.get("performances") or []
        if not perfs:
            continue
        played = [p for p in perfs if not counting or p["date"] in counting]
        # (gap, the night that gap ended) rather than the gap alone, because
        # the hero has to order the songs that tie on the figure -- see below.
        gaps = [(p["gap"], p["date"]) for p in played[1:] if p["gap"] is not None]
        best = (doc.get("best") or [None])[0]
        peak = max(gaps) if gaps else None
        entries.append({
            "song": doc["song"], "slug": doc["slug"], "played": len(played),
            # Nine songs have never been played at a show -- five of them at
            # one soundcheck at The Woodlands in 2024. They keep their rows:
            # dropping them would have this page say the band has never
            # touched Day Tripper, which is worse than saying it has played it
            # at no shows, and their pages exist and say the same thing.
            "last": played[-1]["date"] if played else "",
            "first": played[0]["date"] if played else "",
            "median": _median([g for g, _ in gaps]) if gaps else None,
            "longest": peak[0] if peak else None,
            "longest_on": peak[1] if peak else "",
            "score": best["score"] if best else None,
            "best_date": best["date"] if best else "",
        })
    entries.sort(key=lambda e: -e["played"])

    for e in entries:
        # One cell per figure, so the columns line up down the page rather than
        # drifting with the width of each row's numbers.
        stats = ("<span class='st'><b>%d</b> show%s</span>"
                 % (e["played"], "" if e["played"] == 1 else "s"))
        stats += ("<span class='st'>median <b>%s</b></span>" % _stat(e["median"])
                  if e["median"] is not None else "<span class='st'></span>")
        stats += ("<span class='st'>longest <b class='hot'>%s</b></span>"
                  % _stat(e["longest"]) if e["longest"] is not None
                  else "<span class='st'></span>")
        stats += ("<span class='st'>best <b class='score'>%s</b></span>" % e["score"]
                  if e["score"] is not None else "<span class='st'></span>")
        rows.append(
            "<li data-song=\"%s\" data-played='%d' data-last='%s'"
            " data-longest='%s' data-score='%s' data-search=\"%s\">"
            "<a class='row' href='./song/%s.html'>"
            "<span class='r-song'>%s</span>"
            "<span class='r-when'>%s</span>"
            "<span class='r-stats'>%s</span></a></li>"
            % (html.escape(e["song"], quote=True), e["played"], e["last"],
               e["longest"] if e["longest"] is not None else "",
               e["score"] if e["score"] is not None else "",
               html.escape(e["song"].lower(), quote=True),
               html.escape(e["slug"], quote=True), html.escape(e["song"]),
               # "last <date>" needs a date. A song with no show to its name
               # has none, and "last —" would read as a missing value rather
               # than as the fact itself. `data-last` stays empty, which sorts
               # these to the bottom of Recently played rather than the top.
               "last <b>%s</b>" % e["last"] if e["last"] else "never at a show",
               stats))

    total = sum(e["played"] for e in entries)
    # The song that holds the longest gap, so the figure can point at it. The
    # index has done this since it was built and says why: a figure in the hero
    # that cannot be followed is an advertisement for a page that does not
    # exist. This page had four such figures and no links at all -- the reader
    # was shown 1,468 and left to guess which of 589 songs it belonged to.
    #
    # Every song holding the record, not just one, because right now two do:
    # Cold as Ice came back after 1,468 shows on 2026-07-22 and Gone after
    # 1,468 on 2009-12-30. A bare `max()` would have named whichever sorted
    # first and stated it as *the* answer, and this site's rule is that a wrong
    # figure is worse than a missing one -- "Cold as Ice, 1,468" under the
    # words LONGEST GAP is a claim of uniqueness the archive does not support.
    # So the card names the most recent holder, links to it, and says how many
    # others there are. render_index does the same, off the same two helpers.
    #
    # Most recent first, because among equals it is the one a reader has a
    # chance of remembering, and because the ordering has to come from the
    # data rather than from where a song happens to sit in the list.
    top_gap = max((e["longest"] for e in entries if e["longest"]), default=None)
    holders = sorted((e for e in entries if e["longest"] == top_gap),
                     key=lambda e: e["longest_on"],
                     reverse=True) if top_gap else []
    peak = holders[0] if holders else None
    # "Performances" on a page listing songs can be read as the band's, and
    # 27,966 of those would be some tour. The count is of songs played, so it
    # says so.
    #
    # There was a fourth card, "Best Rated Version", and it is gone. Three
    # things were wrong with it and they are separable. It named a superlative
    # about one song on a page whose whole job is the other 588. Its phrasing
    # only parses if you already know it means "the best-rated version on the
    # site", which is a sentence this page never says. And the score is
    # fouldomain's, not this archive's -- a hero is where a site states what it
    # thinks, and that cell handed the largest type on the page to someone
    # else's judgment of one performance. None of that removes the fact from
    # the site: every row still carries its own best score, and "Highest rated"
    # is one of the five sorts directly below. A sort answers this for all 589
    # songs, which is the right shape for the question; a hero answered it for
    # one.
    # Four, and two of them are doors. This hero is how Due and Out of rotation
    # are reached now that the nav carries only the four ways into the archive,
    # so the room for them had to come from somewhere -- and it came from
    # "Song Performances", which was the one figure here that the line directly
    # above it already gives: the subtitle reads "589 songs, 36,958
    # performances between them". A hero cell that repeats the sentence over it
    # is spending the widest row on the page saying a number twice.
    #
    # Both doors are left out entirely when their figure is not known, rather
    # than drawn as a card with no number: a due page that did not get built is
    # a link to a page that is not there.
    cards = [
        (len(entries), "Songs", "", ""),
        (_stat(peak["longest"]) if peak else "n/a", "Longest Gap", " hot",
         "./song/%s.html" % peak["slug"] if peak else "",
         (peak["song"] + tied_with([e["song"] for e in holders[1:]]))
         if peak else ""),
    ]
    if n_due is not None:
        cards.append((n_due, "Due", "", "./due.html"))
    if n_rotation is not None:
        cards.append((n_rotation, "Out of Rotation", "", "./" + ROTATION_PAGE))
    hero = hero_html(cards)
    # "589 songs, played 37,169 times" attaches the verb to the nearest noun a
    # reader can find, and the nearest noun is singular: it reads as one song
    # played 37,169 times. The count is of performances across the catalog,
    # so it says performances, and "between them" puts the 589 back in charge
    # of the number.
    subtitle = ("%d song%s &middot; %s performance%s between them"
                % (len(entries), "" if len(entries) == 1 else "s",
                   "{:,}".format(total), "" if total == 1 else "s"))
    # Same correction as the subtitle, and it matters more here: this is the
    # line a link preview shows, with no page around it to disambiguate.
    blurb = ("Every song in the archive: %d of them, %s performances between "
             "them." % (len(entries), "{:,}".format(total)))
    return SONGS_SHELL.format(
        crumb=nav_strip(here="Songs"),
        ago_js=AGO_JS,
        new_rows_js=NEW_ROWS_JS,
        analytics=ANALYTICS,
        css=SONGS_CSS, js=SONGS_JS, totop=TOTOP_JS, fonts=WEB_FONTS, sheet=sheet_links("./%s/%s" % (STATIC_DIR, SITE_SHEET)), theme_js=THEME_JS, keys_js=KEYS_JS,
        theme_ui=THEME_UI, hero=hero, hero_cls=hero_cols(len(cards)),
        count=len(entries),
        rows="\n".join(rows), subtitle=subtitle,
        share=share_meta("Songs &mdash; Possum Logic",
                         html.escape(blurb, quote=True), "songs.html", card=card),
        stamp=stamp or "Updated %s" % max((e["last"] for e in entries), default=""))


# ------------------------------------------------------------------ years ---
#
# What a year sounded like, read off the running order rather than off the
# gaps. Every other list on this site is about one song's habits; this is the
# only one about the band's, and it is the only page whose input is the order
# the songs came in rather than the dates they fell on.

# Nights the repetition figure is stated over. See year_repeat for why a fixed
# number and not the year's own length; 20 is the largest round number that
# still lets 1987 (21 nights) and 2017 (28) answer.
YEARS_SAMPLE = 20
# A song is part of a year's sound if it turned up on at least this many of
# that year's nights, and on at least this share of them. Both, because three
# nights out of 124 is noise and three out of 21 is a habit.
YEARS_FLOOR = 3
YEARS_SHARE = .10
# And a move belongs to a year only if a quarter of every time it ever
# happened was that year.
YEARS_OWN = .25
# How many songs a fact line will name before it stops and says how many more
# there were.
YEARS_NAMED = 5


def year_order(order, counting, reports=()):
    """{date: rows} for every counting show whose running order is known.

    Two sources, because neither is complete on its own. The extract holds the
    whole career and is free to re-read, but it deliberately refuses a show
    whose report is still provisional -- so on the one night anyone would look
    hardest, the newest show is the one missing from it. The saved reports
    carry a running order too and go back only as far as the archive does.
    Extract first, then a report for anything the extract has not got.

    Filtered to the counting calendar throughout, so a year's shows here are
    the same shows the rest of the site counts. Nine of the archive's entries
    are soundchecks and radio sessions; a soundcheck is not a night.
    """
    known = {date: rows for date, rows in order.items() if date in counting}
    for report in reports:
        date = report["date"]
        if date in known or date not in counting:
            continue
        rows = [{"set": SET_SLUG.get(s.get("set"), ""), "position": i,
                 "slug": s["slug"], "song": s.get("song") or s["slug"],
                 "trans_mark": s.get("out") or ""}
                for i, s in enumerate(report.get("songs") or (), 1)
                if s.get("slug")]
        if rows:
            known[date] = rows
    return known


def year_songs(rows):
    """One show's songs in running order, minus the entries that are not songs.

    `jam` and `custom` are filed here for the same reason they carry a caveat
    on their own pages: neither is a composition, so counting either as the
    most-played song of a year answers a different question than the reader is
    asking. `custom` alone would have put nine different pieces of music into
    one row.
    """
    return [r for r in sorted(rows, key=lambda e: (SET_ORDER.get(e["set"], 9),
                                                   e["position"]))
            if r["slug"] not in NOT_A_SONG]


def year_moves(rows):
    """The song-to-song moves inside one show, as ordered pairs of slugs.

    Inside a set only. What follows the break is not what the band segued
    into, and treating it as one would make "Antelope, then Chalk Dust" the
    same object as "Antelope > Chalk Dust", which is the distinction the whole
    page is about.
    """
    songs = year_songs(rows)
    return [(a["slug"], b["slug"]) for a, b in zip(songs, songs[1:])
            if a["set"] == b["set"]]


def year_repeat(dates, order, sample=YEARS_SAMPLE):
    """The share of a year's moves that recur, stated over a fixed `sample`.

    The obvious figure -- what share of a year's moves happened more than once
    that year -- cannot be compared across years, and a page of years is
    nothing but a comparison. It climbs with the number of shows for purely
    arithmetic reasons: 124 nights give a pair 124 chances to turn up twice,
    28 nights give it 28. Measured, that is most of the distance between the
    two ends of this archive. Cut every year down to the same 29 nights and
    1991 falls from 68% to 39% -- while 2017, which already had 29, stays at
    1.4%. The ordering survives; the raw numbers do not deserve to.

    So what is published is the figure a reader who saw `sample` nights of
    that year would have seen, which every long-enough year can answer on the
    same terms. Exact rather than sampled: a move that appears on m of the
    year's n nights appears on X of a random `sample` of them, X being
    hypergeometric, and it reads as a repeat whenever X is 2 or more --

        E[repeats] = sum over moves of  E[X] - P(X = 1)

    Checked against 120 random draws of every year: no year moved by more than
    0.3 points, which is the difference between a statistic and a die roll.

    A move that happens twice in one night is a sandwich rather than a habit,
    so each move counts once per night. -> percent, or None below `sample`.
    """
    n = len(dates)
    if n < sample:
        return None
    nights = collections.Counter()
    for date in dates:
        nights.update(set(year_moves(order[date])))
    whole = math.comb(n, sample)
    alone, top, bottom = {}, 0.0, 0.0
    for m in nights.values():
        bottom += m * sample / n
        if m not in alone:
            alone[m] = (m * math.comb(n - m, sample - 1) / whole
                        if n - m >= sample - 1 else 0.0)
        top += m * sample / n - alone[m]
    return 100 * top / bottom if bottom else None


def year_profiles(order, counting, docs=()):
    """One profile per year of the band's career, newest first.

    `order` is what year_order returned, so everything here is already
    restricted to nights the site counts and whose running order is known.
    """
    by_year, played = {}, {}
    for date in order:
        by_year.setdefault(date[:4], []).append(date)
    for date in counting:
        played[date[:4]] = played.get(date[:4], 0) + 1

    # A song's debut, from the fullest source that has it. A song page holds
    # every performance phish.net knows of, which is better evidence than this
    # extract -- 100 shows before 1992 have no running order on file, so a
    # song first played at one of them looks younger here than it is. Only 589
    # songs have a page, though (a page exists for a song the archive's own
    # reports name, and those start in 2009), so the extract answers for the
    # rest and the earlier of the two answers wins.
    pages, debut, names = set(), {}, {}
    for doc in docs:
        pages.add(doc["slug"])
        first = next((p["date"] for p in doc.get("performances") or ()
                      if p["date"] in counting), None)
        if first:
            debut[doc["slug"]] = first[:4]

    plays, nights, moves = {}, {}, {}
    for year, dates in by_year.items():
        p, s, m = collections.Counter(), collections.Counter(), collections.Counter()
        for date in dates:
            songs = year_songs(order[date])
            for row in songs:
                p[row["slug"]] += 1
                names[row["slug"]] = row["song"]
            s.update({row["slug"] for row in songs})
            # Once a night. A move made twice in one show is a sandwich, and a
            # sandwich is a thing that happened once.
            m.update(set(year_moves(order[date])))
        plays[year], nights[year], moves[year] = p, s, m
        for slug in p:
            if slug not in debut or year < debut[slug]:
                debut[slug] = year

    anywhere, ever = collections.Counter(), collections.Counter()
    for year in by_year:
        anywhere += nights[year]
        ever += moves[year]
    everything = sum(len(dates) for dates in by_year.values())

    # A song nobody heard in any other year. Computed against every night the
    # archive holds an order for rather than against every night played, which
    # is the honest limit of the claim and is what the page says it is.
    lonely = {}
    for slug in names:
        seen = [year for year in by_year if plays[year].get(slug)]
        if len(seen) == 1:
            lonely.setdefault(seen[0], []).append(slug)

    def named(slugs, figure):
        return [(slug, names[slug], figure(slug)) for slug in slugs]

    out = []
    for year in sorted(by_year, reverse=True):
        dates = sorted(by_year[year])
        n = len(dates)
        p, s = plays[year], nights[year]
        performances = sum(p.values())

        # What made this year sound like itself rather than like the band:
        # how much of the year a song was in, weighed against how much of
        # every other year it was in. The log keeps a song that played twice
        # as often as usual on 60% of nights above one that played fifty times
        # as often on three -- rarity alone would fill every row with one-offs,
        # which is the next fact line down and a different question.
        rest = everything - n
        # Songs the band played only this year are left out of it, because the
        # line below says that about them and says it harder. In they went
        # first, and 1995 answered Acoustic Army, Taste That Surrounds and
        # Keyboard Army twice over -- the same three chips in two rows, where
        # the second row is the stronger claim. Out of this list, 1995 says
        # Strange Design, A Day in the Life and I'm Blue, I'm Lonesome, which
        # is what the year sounded like rather than what was unique to it.
        alone = set(lonely.get(year, ()))
        sound = []
        for slug, count in s.items():
            if slug in alone or count < YEARS_FLOOR or count < YEARS_SHARE * n:
                continue
            here = count / n
            elsewhere = (anywhere[slug] - count) / rest if rest else 0
            # Never anywhere else: a rate of zero has no logarithm, so it is
            # held at half a night rather than allowed to run to infinity.
            elsewhere = elsewhere or .5 / rest
            sound.append((here * math.log2(here / elsewhere), here, slug))
        sound.sort(reverse=True)

        # The move that was most this year's own, rather than the one it made
        # most often. Ranked on the raw count, nearly every year of the
        # archive answers with one of two pairs: The Horse into Silent in the
        # Morning is one piece of music filed as two rows, and Mike's Song
        # into I Am Hydrogen is a fixed sequence the band has played since
        # 1988. Both are true and neither is about a year. Weighed against how
        # often the pair ever happened, 1993 answers Big Ball Jam into Hold
        # Your Head Up -- 16 of the 22 nights it has ever happened, all of them
        # that year -- which is the thing worth knowing.
        habit, best = None, 0
        for pair, count in moves[year].items():
            # A quarter of every time it ever happened, at least, or the line
            # is not about this year and does not appear. Without the floor
            # 2021 answers Mike's Song into I Am Hydrogen on the strength of 3
            # nights out of 335 -- the best any 2021 pair could do, and still
            # a statement about 1988. Four years say nothing here instead.
            if count < YEARS_FLOOR or count < YEARS_OWN * ever[pair]:
                continue
            score = count * count / ever[pair]
            if score > best:
                habit, best = (names[pair[0]], names[pair[1]], count,
                               ever[pair]), score

        ages = sorted(int(year) - int(debut[slug])
                      for slug, count in p.items() for _ in range(count))
        only = sorted(lonely.get(year, ()), key=lambda x: (-p[x], names[x]))
        out.append({
            "year": year,
            "shows": played.get(year, n),
            "known": n,
            "songs": len(p),
            "performances": performances,
            "per_night": performances / n,
            "age": _median(ages),
            "repeat": year_repeat(dates, order),
            "most": named([slug for slug, _ in p.most_common(YEARS_NAMED)],
                          lambda slug: "%d" % p[slug]),
            "sound": named([slug for _, _, slug in sound[:YEARS_NAMED]],
                           lambda slug: "%.0f%%" % (100 * s[slug] / n)),
            "only": named(only[:YEARS_NAMED], lambda slug: "%d" % p[slug]),
            "only_n": len(only),
            "habit": habit,
        })
    return out


YEARS_CSS = INDEX_CSS + YEAR_STRIP_CSS + """
/* One block a year, and the year itself set the size the song titles are set
   on a show page -- this is a page of forty headings and the reader is
   scanning for one of them. */
.yb{margin:0 0 2.6rem}
.yb:first-of-type{margin-top:.4rem}
.yh{display:flex;align-items:baseline;gap:.7rem;margin:0 0 .7rem;
   padding:0 .25rem .35rem;border-bottom:1px solid var(--ink)}
.yh .y{font-family:'Bagnard',Georgia,serif;font-weight:400;font-size:1.75rem;
   line-height:1;letter-spacing:-.01em;color:var(--ink)}
.yh .n{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim)}
.yh .up{margin-left:auto;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--dim);text-decoration:none;
   border-bottom:1px solid var(--rule);position:relative}
.yh .up::before{content:"";position:absolute;left:50%;top:50%;
   transform:translate(-50%,-50%);width:100%;min-width:24px;height:24px}
.yh .up:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* The four figures, as a grid rather than a sentence with middots in it.
   Set as running text they stranded a separator at the end of every wrapped
   line; a grid cell cannot strand punctuation it does not carry. */
.shape{display:grid;grid-template-columns:repeat(4,1fr);gap:.6rem 1rem;
   margin:0 0 .9rem;padding:0 .25rem}
.shape dt{font-size:.625rem;letter-spacing:.14em;text-transform:uppercase;
   color:var(--dim);margin:0}
.shape dd{margin:.15rem 0 0;font-size:.9375rem;color:var(--ink-soft);
   font-variant-numeric:tabular-nums}
.shape dd b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   color:var(--ink)}
/* Said only where it is true, and it is true only before 1992. */
.part{margin:0 0 .9rem;padding:0 .25rem;font-family:'Literata',Georgia,serif;
   font-size:.875rem;line-height:1.5;font-variation-settings:'opsz' 14;
   color:var(--dim)}
.fact{display:grid;grid-template-columns:9.5rem 1fr;align-items:baseline;
   gap:.5rem .9rem;padding:.45rem .25rem;border-top:1px solid var(--rule-soft)}
.fact h3{margin:0;font-size:.625rem;letter-spacing:.14em;font-weight:400;
   text-transform:uppercase;color:var(--dim)}
/* Songs as chips, one size down from the year strip they echo. A run of
   titles set as text put its commas at the ends of lines; an enclosed item
   carries no punctuation to strand. */
.chips{display:flex;flex-wrap:wrap;gap:.35rem}
.chips a,.chips span{font-size:.8125rem;line-height:1.15;padding:.3rem .45rem;
   border:1px solid var(--edge);color:var(--ink-soft);text-decoration:none}
.chips a:hover{color:var(--hot-text);border-color:var(--hot-text)}
.chips b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:400;
   color:var(--dim);margin-left:.35rem;font-variant-numeric:tabular-nums}
.chips a:hover b{color:var(--hot-text)}
/* Not a chip: it is one sentence about two songs, and breaking it into two
   enclosures would hide the only thing it says, which is the arrow. */
.habit{margin:0;font-size:.8125rem;line-height:1.35;color:var(--ink-soft)}
.habit .to{color:var(--dim);margin:0 .3rem}
.habit .n{font-family:'IBM Plex Mono',ui-monospace,monospace;color:var(--dim);
   margin-left:.4rem;font-variant-numeric:tabular-nums}
.more{font-size:.75rem;color:var(--dim);align-self:center}
@media (max-width:620px){
  .shape{grid-template-columns:repeat(2,1fr)}
  .fact{grid-template-columns:1fr;gap:.3rem}
}
"""


YEARS_SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Years &mdash; Possum Logic</title>
<meta property="og:type" content="website">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}</head><body id="top"><div class="wrap">
<a class="skip" href="#main">Skip to content</a>
{crumb}
<div class="rule2"></div>
<header><h1>Years</h1>
<p class="show">{subtitle}</p>
<p class="dek">What a year sounded like, taken from the order the songs came
in rather than from how long the band went without them. Every other list here
is about one song&rsquo;s habits. This one is about the band&rsquo;s.</p>
<p class="dek"><b>Sounded like</b> is not the same list as <b>most played</b>,
and the difference is the point: Possum was played every year, so it says
nothing about any of them. A song earns a place in the first list by being a
bigger share of that year than of every other year put together.</p>
<p class="dek"><b>Moves that recur</b> is the share of a year&rsquo;s
song-to-song moves that turn up on more than one night &mdash; stated over a
fixed {sample} nights, because otherwise it is a count of how many shows the
band played. A long year gets more chances to repeat itself for reasons that
have nothing to do with how it sounded. Over the same {sample} nights, 1993
reads {high} and 2017 reads {low}.</p>
<p class="dek">Built from the running order of {read} nights. The archive has
no running order for {missing} of the shows the calendar counts, almost all of
them before 1992, so a year short of its own count says so under its figures
&mdash; and <b>only in</b> means only in the nights read here.</p>
<nav class="years" aria-label="Years on this page">{years}</nav></header>
<section class="hero {hero_cls}">{hero}</section>
<div class="rule2"></div>
<main id="main" tabindex="-1">
{blocks}
</main>
""" + footer_html() + """
{analytics}
</div></body></html>
"""


def _year_chips(items, pages, root="./"):
    """A run of songs, each with its figure, linked where the song has a page.

    Not every song does. A page exists for a song some saved report names, and
    the reports start in 2009 -- so Acoustic Army, 27 performances and all of
    them in 1995, is a name here and nothing more. Set as an unlinked chip
    rather than left out: what the page is saying about 1995 is that the song
    existed, and a missing page is not a reason to un-say it.
    """
    out = []
    for slug, song, figure in items:
        label = "%s<b>%s</b>" % (html.escape(typographic(song)),
                                 html.escape(figure))
        if slug in pages:
            out.append("<a href='%ssong/%s.html'>%s</a>"
                       % (root, html.escape(slug, quote=True), label))
        else:
            out.append("<span>%s</span>" % label)
    return "".join(out)


def _year_fact(label, body, more=""):
    return ("<div class='fact'><h3>%s</h3><div class='chips'>%s%s</div></div>"
            % (label, body,
               "<span class='more'>%s</span>" % more if more else ""))


def _year_block(profile, pages):
    """One year, as a heading, four figures and up to four fact lines."""
    year, n = profile["year"], profile["known"]
    age = profile["age"]
    figures = [
        ("A night", "<b>%.0f</b> songs" % profile["per_night"]),
        ("In rotation", "<b>%d</b> songs" % profile["songs"]),
        ("Median song", "new" if not age else
         "<b>%.0f</b> year%s old" % (age, "" if age == 1 else "s")),
        ("Moves that recur",
         "&mdash;" if profile["repeat"] is None
         else "<b>%.0f%%</b>" % profile["repeat"]),
    ]
    body = ["<section class='yb' id='y%s'>"
            "<h2 class='yh'><span class='y'>%s</span>"
            "<span class='n'>%s show%s</span>"
            "<a class='up' href='#top'>&uarr; Top</a></h2>"
            % (year, year, "{:,}".format(profile["shows"]),
               "" if profile["shows"] == 1 else "s"),
            "<dl class='shape'>%s</dl>"
            % "".join("<div><dt>%s</dt><dd>%s</dd></div>" % f for f in figures)]

    # Only when it is not the whole year, and it never is after 1991.
    if n < profile["shows"]:
        body.append("<p class='part'>Running order known for %d of these %d "
                    "nights; the figures above are what those %d hold.</p>"
                    % (n, profile["shows"], n))

    if profile["most"]:
        body.append(_year_fact("Most played",
                               _year_chips(profile["most"], pages)))
    if profile["sound"]:
        body.append(_year_fact("Sounded like",
                               _year_chips(profile["sound"], pages)))
    if profile["only"]:
        spare = profile["only_n"] - len(profile["only"])
        body.append(_year_fact(
            "Only in %s" % year, _year_chips(profile["only"], pages),
            "and %d more" % spare if spare else ""))
    if profile["habit"]:
        first, second, count, ever = profile["habit"]
        body.append(
            "<div class='fact'><h3>Ran together</h3>"
            "<p class='habit'>%s<span class='to'>&rarr;</span>%s"
            "<span class='n'>%d night%s, of %d ever</span></p></div>"
            % (html.escape(typographic(first)),
               html.escape(typographic(second)),
               count, "" if count == 1 else "s", ever))
    body.append("</section>")
    return "".join(body)


def render_years(profiles, missing, pages=(), card=None):
    """Forty years of this band, one block each, newest first."""
    read = sum(p["known"] for p in profiles)
    strip = "".join(
        "<a href='#y%s' aria-label='%s, %d show%s'>%s<b>%d</b></a>"
        % (p["year"], p["year"], p["shows"], "" if p["shows"] == 1 else "s",
           p["year"], p["shows"]) for p in profiles)

    rated = [p for p in profiles if p["repeat"] is not None]
    most = max(rated, key=lambda p: p["repeat"], default=None)
    least = min(rated, key=lambda p: p["repeat"], default=None)
    widest = max(profiles, key=lambda p: p["songs"], default=None)
    cards = [(len(profiles), "Years", "", ""),
             ("{:,}".format(read), "Nights read", "", ""),
             (most["year"] if most else "n/a", "Most habitual", " hot",
              "#y%s" % most["year"] if most else ""),
             (widest["year"] if widest else "n/a", "Widest rotation", "",
              "#y%s" % widest["year"] if widest else "")]
    hero = "".join(
        ("<a class='card' href='%s'>" % href if href else "<div class='card'>")
        + "<div class='lbl'>%s</div><div class='num%s'>%s</div>" % (lbl, cls, val)
        + ("</a>" if href else "</div>")
        for val, lbl, cls, href in cards)

    span = "%s&ndash;%s" % (profiles[-1]["year"], profiles[0]["year"]) if profiles else ""
    subtitle = "%d years of Phish, %s" % (len(profiles), span)
    blurb = ("What each year of Phish sounded like: the songs that were only "
             "that year's, and how much of the band's own running order they "
             "repeated.")
    return YEARS_SHELL.format(
        crumb=nav_strip(here="Years", mark=True),
        analytics=ANALYTICS, css=YEARS_CSS, fonts=WEB_FONTS,
        sheet=sheet_links("./%s/%s" % (STATIC_DIR, SITE_SHEET)), theme_js=THEME_JS, keys_js=KEYS_JS,
        theme_ui=THEME_UI, years=strip, hero=hero,
        hero_cls=hero_cols(len(cards)), subtitle=subtitle,
        sample=YEARS_SAMPLE, read="{:,}".format(read),
        missing="{:,}".format(missing),
        high="%.0f%%" % next((p["repeat"] for p in profiles
                              if p["year"] == "1993"), 0),
        low="%.0f%%" % next((p["repeat"] for p in profiles
                             if p["year"] == "2017"), 0),
        blocks="\n".join(_year_block(p, pages) for p in profiles),
        share=share_meta("Years &mdash; Possum Logic",
                         html.escape(blurb, quote=True), "years.html", card=card),
        stamp="Updated %s" % _utcnow().date().isoformat())


# ----------------------------------------------------------------- method ---

METHOD_CSS = INDEX_CSS + """
.prose{max-width:66ch;margin:0 0 2.4rem}
.prose h2{font-family:'Bagnard',Georgia,serif;font-weight:400;
   font-size:1.25rem;margin:2.2rem 0 .5rem;letter-spacing:0}
/* The page is almost nothing but prose -- 3.4 KB of it, eleven paragraphs --
   and it was the one place where setting everything in the mono was hardest to
   defend: this is the page that has to be read start to finish rather than
   scanned for a number. The reading face, at the measure it was already given.
   Figures inside a sentence stay mono, so a threshold quoted in the text looks
   like the same object it does on a report. */
.prose p{margin:0 0 1rem;font-family:'Literata',Georgia,serif;
   font-size:1rem;line-height:1.6;font-variation-settings:'opsz' 16;
   color:var(--ink-soft)}
.prose li{font-family:'Literata',Georgia,serif;font-size:1rem;line-height:1.6;
   font-variation-settings:'opsz' 16;color:var(--ink-soft)}
.prose b{color:var(--ink)}
.prose .verdict{display:inline-block;margin:0 .15rem;font-size:.625rem;
   letter-spacing:.14em;text-transform:uppercase}
/* The same two stamps the show pages carry, and they had drifted: there
   .verdict.overdue is --hot-text and here .overdue was still --hot, so the
   page that exists to explain the marks showed them in a different red from
   the marks themselves -- and at 4.44:1, under the floor for 10px caps. Both
   copies now say --hot-text. `.crumb` and `.hero` differ between sheets for
   real reasons; these two never did. */
.prose .overdue{color:var(--hot-text)}
.prose .premature{color:var(--cool)}
.prose .bust{background:var(--hot-text);color:var(--paper);padding:.1rem .3rem;
   font-weight:600;print-color-adjust:exact;-webkit-print-color-adjust:exact}
.prose .num{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;font-size:1rem;
   color:var(--ink)}
/* The one table on this page, and a real <table> rather than the grid the
   listing pages use: those are grids because every row is one link and an <a>
   cannot wrap a <tr>. Nothing here is a link, so the rows are rows.

   Figures in the mono with tabular numerals, which is what makes a column of
   percentages readable as a column -- this is the same lesson the show pages
   learned, and the reason it is stated again is that it was fixed there by a
   rule that lives on a sheet this page does not extend. Only on this sheet, so
   a plain search for `.figs` finds one match rather than three. */
.figs{max-width:66ch;width:100%;border-collapse:collapse;margin:0 0 1.4rem;
   font-family:'IBM Plex Mono',ui-monospace,monospace;font-size:.8125rem;
   font-variant-numeric:tabular-nums}
.figs th{font-weight:400;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--dim);text-align:left;
   padding:0 .6rem .4rem 0;border-bottom:1px solid var(--ink)}
.figs td{padding:.35rem .6rem .35rem 0;color:var(--ink-soft);
   border-bottom:1px solid var(--rule-soft)}
.figs tr:last-child td{border-bottom:0}
.figs .end{text-align:right;padding-right:0}
.figs td.end{color:var(--ink)}
/* Stated here rather than on the FAQ's sheet, because this page links out too
   and had no rule for a link in running prose -- the first one added to it
   would have come out in the browser's default blue. */
.prose a{color:var(--ink);text-decoration:none;
   border-bottom:1px solid var(--rule)}
.prose a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* Where a claim came from, set small and dim under the claim. It sat on the
   FAQ's sheet until the acknowledgments page wanted it, and the FAQ's sheet is
   built on this one, so leaving it there would have made it a rule the other
   two prose pages could not have -- the shape of every one-sheet-of-three bug
   in this file. Moved rather than copied.

   `.prose .src` as well as `.src`, and it is not belt and braces -- it is the
   same defect `.backtop` had, found the same way. These are <p> elements
   inside the prose, so `.prose p` is one class and one type against this
   rule's one class and wins outright, order be damned. Measured on the built
   page: the source line came out at 18px in Literata in --ink-soft, which is
   a body paragraph exactly, so the only thing this rule had ever done was
   the margin. It has been wrong on the FAQ's segues answer since that answer
   was written. */
/* The bottom margin is new with the second caller. On the FAQ this line is
   the last thing in an answer and had nothing under it to be crowded by; on
   the acknowledgments page it sits between a heading and the prose it
   introduces, and with no bottom margin the two ran together. Matched to
   `.prose p` so a source line spaces like the paragraph it stands in for. */
.src,.prose .src{margin:.4rem 0 1rem;font-size:.75rem;
   font-variation-settings:'opsz' 12;color:var(--dim)}
/* The contents block, shared by both prose pages. Generated from the same
   list the sections are, so it cannot name one the page does not have or miss
   one it does -- the FAQ has worked this way since it was built and the method
   page does now too.

   Stated here rather than on the FAQ's sheet because the FAQ's sheet is built
   on this one: a rule put there would have been a rule the method page could
   not have, which is the shape of every one-sheet-of-three bug in this file.

   It used to be a bare caption over eight hairline-separated lines set in the
   reading face, one size down from the h2 under it and in a softer ink -- so
   the whole block read as continuous prose and, in Ian's words, "sort of looks
   like the answer to the first question". Three things separate it now: it is
   enclosed rather than merely ruled, the entries are numbered, and the numbers
   are mono, which is this site's voice for a figure. A reader can tell an
   index from an answer before reading a word of either. */
.toc{max-width:66ch;margin:0 0 3rem;padding:1rem 1.2rem 1.1rem;
   border:1px solid var(--rule);background:var(--rule-soft)}
.toc .cap{display:block;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--ink);font-weight:600;margin:0 0 .6rem}
/* Counter rather than list-style:decimal, so the number is a column of its own
   and an entry that wraps aligns under itself instead of under its number. */
.toc ol{list-style:none;margin:0;padding:0;counter-reset:q}
.toc li{counter-increment:q;border-top:1px solid var(--rule-soft)}
.toc li:first-child{border-top:0}
.toc a{display:grid;grid-template-columns:1.6rem 1fr;align-items:baseline;
   padding:.4rem 0;font-family:'Literata',Georgia,serif;
   font-size:.9375rem;line-height:1.4;font-variation-settings:'opsz' 14;
   color:var(--ink-soft);text-decoration:none;border:0}
/* --ink-soft, not --dim. This is the one place on the site where --dim sits on
   something other than paper: the panel above carries a --rule-soft wash, which
   takes --dim from 4.98:1 on bare paper to 4.13:1 here, and 4.49:1 in the dark
   -- both under the floor for 12px. The mono face and the smaller size were
   always doing the work of separating the enumerator from the entry; being
   dimmer as well was belt and braces that cost the contrast. */
.toc a::before{content:counter(q);font-family:'IBM Plex Mono',ui-monospace,monospace;
   font-size:.75rem;font-weight:600;color:var(--ink-soft)}
.toc a:hover{color:var(--hot-text)}
.toc a:hover::before{color:var(--hot-text)}
/* The way back up. Every answer and every section gets one, because the point of an index is
   being able to pick a second question after the first -- and without this the
   only route was scrolling back yourself. Mono and small: it is a control, not
   a sentence, and it must not read as another paragraph of the answer. */
/* .prose .backtop as well as .backtop, and it is not belt and braces. Inside
   the prose these are <p> elements, so `.prose p` -- one class and one type --
   out-specifies a bare `.backtop`, and order cannot help because the two are
   not equal. The result was that this rule had never once been drawn: every
   "All questions" link on the FAQ has been set in Literata at the body size
   since the page was built, which is exactly the paragraph it was written not
   to look like. Verified against the published sheet, not just this one. */
.backtop,.prose .backtop{margin:.8rem 0 0;
   font-family:'IBM Plex Mono',ui-monospace,monospace;
   font-size:.625rem;letter-spacing:.14em;text-transform:uppercase}
.backtop a{color:var(--dim);text-decoration:none;
   border-bottom:1px solid var(--rule)}
.backtop a:hover{color:var(--hot-text);border-bottom-color:var(--hot-text)}
/* 24x24, the same floor the nav links were held to, without moving the ink. */
.backtop a{position:relative;display:inline-block}
.backtop a::before{content:"";position:absolute;left:50%;top:50%;
   transform:translate(-50%,-50%);width:100%;min-width:24px;height:24px}
@media print{.backtop{display:none}}
"""

METHOD_SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>How this is worked out &mdash; Possum Logic</title>
<meta property="og:type" content="article">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}{ago_js}{new_rows_js}</head><body id="top"><div class="wrap">
<a class="skip" href="#main">Skip to content</a>
{crumb}
<div class="rule2"></div>
<header><h1><a href="./index.html">Possum <em>Logic</em></a></h1>
<p class="show">How this is worked out</p></header>
<div class="rule2"></div>
<div class="prose" id="main" tabindex="-1">
<nav class="toc" id="sections" tabindex="-1" aria-label="Sections on this page"><span class="cap">Sections on this page</span>
<ol>{toc}</ol></nav>
{body}</div>
{totop}
""" + footer_html(back=("All reports", "index.html"), right=None) + """
{analytics}
</div></body></html>
"""


# (anchor, heading, body). One list, so the contents at the top of the page
# and the sections under it are the same thing rendered twice -- the FAQ has
# worked this way since it was built, and this page can no longer advertise a
# section it does not have.
#
# Order is the reading order. It used to run gap -> median -> verdict ->
# *segue notation* -> the bar, so the one paragraph that draws the verdict was
# separated from the three that define it by a section about something else.
# The bar now closes that argument and the notation follows it.
METHOD = (
    ('what-a-gap-is', 'What a gap is', """
<p>The number beside a song is how many shows the band played between this
performance and the one before it. A gap of <b class="num">0</b> means they
played it again the very next night; <b class="num">485</b> means four hundred
and eighty-five shows went by. It is counted here from the show calendar, not
taken from Phish.net, whose figure mostly counts the show itself and so reads
one higher.</p>"""),
    ('the-median-and-why-ten-years', 'The median, and why ten years', """
<p>Under each gap is that song's usual one &mdash; the median of its gaps over
the <b>ten years</b> before the show, not over all of history. Forty years of a
working band is several different bands. The 1990s dominate any all-time
figure, when they played far more shows a year out of a smaller catalog, so
all-time gaps run much shorter and better than half of everything came out
overdue &mdash; a word that means nothing if it fits three songs in five.</p>
<p>Counting a fixed number of past performances instead does not fix it: twenty
performances is two years for a staple and twenty-four for a rarity. Kung's
last twenty reach back to 1995. Bounding by time instead means a song has to
have been in rotation lately to be judged at all.</p>
<p>The median rather than the average, because gap distributions are savagely
right-skewed: a staple with a median of 6 carries a handful of 200s, and an
average over that would call almost anything ordinary.</p>"""),
    ('the-verdicts', 'The verdicts', """
<p>A gap outside the middle 70% of that ten-year window gets called. Below it,
<span class="verdict premature">premature</span>; above it,
<span class="verdict overdue">overdue</span>; inside, nothing is said, which is
most songs. The band's ends are computed values that appear nowhere in the
song's actual gaps, which is why they are not printed as numbers.</p>
<p>That middle 70% is measured as a <b>ratio</b> around the song's typical gap
rather than as a fixed number of shows either side of it. A gap can be 5 or 112
but never less than nothing, so a step from 5 to 8 and a step from 68 to 71 are
not the same distance, and reading two percentiles off the list treats them as
though they were. Checked against what actually happened next &mdash; band built
from a song's earlier gaps, then compared with the gap that followed, over
<span class="num">32,605</span> performances &mdash; percentiles held the next
gap <span class="num">76%</span> of the time for the staples and
<span class="num">44%</span> for the rarest songs, so the word
&ldquo;usually&rdquo; meant two different things depending on the row. On a
ratio scale it runs <span class="num">70%</span> to
<span class="num">49%</span>.</p>
<p>The band is wide enough that a verdict stays worth reading: roughly
<span class="num">9%</span> of performances come out premature,
<span class="num">69%</span> expected and <span class="num">22%</span>
overdue.</p>
<p>Some songs do two things rather than one &mdash; a fortnight's rotation, and
then a year away &mdash; and a single range describes neither. Where the record
breaks cleanly in two, the hover says so instead of averaging them: Esther's
range tops out under sixty shows, but three of her recent gaps ran
<span class="num">68</span> or longer.</p>"""),
    ('the-bar', 'The bar', """
<p>The bar is a <b>position, not a length</b>. Its shaded middle is the band
above &mdash; where this song usually lands &mdash; the hairline through it is
the median, and the mark is the performance being reported. Left of the shading
is sooner than usual for that song, right of it is later. Past three times the
upper edge the mark stops at the end and stays there, because beyond a point
&ldquo;very late&rdquo; is the whole of the message.</p>
<p>Every row is drawn against its own song rather than against the night, so
one bustout cannot flatten the rest of the bill &mdash; on
<span class="num">168</span> of <span class="num">690</span> shows the longest
gap is at least twenty times the median. It shows position rather than
magnitude because the number beside it already gives the magnitude exactly;
what the number cannot say is whether this was early or late
<em>for this song</em>.</p>
<p>A song with fewer than <b>eight</b> performances in the ten-year window has
no band to be measured against, so its track is drawn empty rather than
implying a comparison that was never made.</p>"""),
    ('before-and-after', 'What came before and after', """
<p>A song page shows what each performance sat between. A plain
<span class="num">&#8592;</span> or <span class="num">&#8594;</span> means only
that: the song before it, the song after it, played as separate songs with a
stop between them.</p>
<p>Where phish.net recorded that the band ran two songs together, its own mark
appears in place of the arrow &mdash; <span class="num">&gt;</span> or
<span class="num">&#8211;&gt;</span> &mdash; and it sits between the two songs
it joins, the way it does in a written setlist. So an arrow is the absence of a
segue rather than the presence of anything, which is worth saying because the
two look equally deliberate on the page.</p>
<p>The two marks are <em>not</em> the same claim.
<span class="num">&#8211;&gt;</span> is a real segue, one song jamming without
interruption into the next; <span class="num">&gt;</span> is everything else
that runs together, and is also used by convention between songs that are
simply always played as a set.
<a href="./faq.html#segues">The difference, in phish.net's own words.</a></p>"""),
    ('which-show-this-was', 'Which show this was', """
<p>A report says where the night sits inside its era &mdash; the
<span class="num">312th</span> show of 3.0 &mdash; and never where it sits
overall. There is no honest overall number to give. phish.net offers three
defensible totals for how many shows the band has played: <span
class="num">2,239</span> entries listed, <span class="num">2,114</span> that
count toward statistics, and <span class="num">2,106</span> distinct dates
among those. They differ by soundchecks, television and radio sessions,
canceled dates, and nights when two separate shows were played.</p>
<p>The disagreement reaches the beginning. <b>1983-10-30</b>, the show
generally called Phish's first, is one phish.net excludes from statistics, so a
count built on that flag declares the <em>second</em> show to be number one and
every figure after it inherits the error.</p>
<p>Inside an era the count is exact for three of the four. Six dates carry more
than one counting show, and all six fall in 1.0 &mdash; the earliest being
<b>1985-02-25</b>, close enough to the start that the drift is not confined to
six shows but is inherited by every show after them, roughly <span
class="num">1,350</span> of <span class="num">1,361</span>. 2.0, 3.0 and 4.0
run one show to a date throughout, so their ordinals are counted rather than
estimated. <b>1.0 shows carry no ordinal</b>, which is a decision and not an
oversight: the number could be produced, and it would be wrong by somewhere
between one and eight with no way to tell which from the date alone.</p>"""),
    ('songs-with-no-verdict', 'Songs with no verdict', """
<p>A song needs <b>eight</b> performances inside that ten-year window before
any of this is said about it. Below that there is no current norm to be early
or late against, so it gets its numbers and no adjective. Roughly one song in
eleven falls here, which is the honest answer for something the band has nearly
stopped playing.</p>"""),
    ('bustouts', 'Bustouts', """
<p>A <span class="verdict bust">bustout</span> is a song coming back that had
no recent record to be judged against, after a gap of <b class="num">100</b> or
more. A hundred sits where Phish.net's own setlist notes use the word.</p>
<p><b>It is not simply any gap over a hundred</b>, and this page said it was
for a long time. Where a song <em>does</em> have a recent record &mdash; the
eight-or-more performances the section above needs &mdash; that record decides
the verdict, and a long gap is marked <span class="verdict">overdue</span>
instead. Of the <b class="num">335</b> performances in this archive with a gap
of a hundred or more, <b class="num">293</b> are bustouts and
<b class="num">42</b> are not: Crowd Control came back after
<b class="num">122</b> shows and Nellie Kane after <b class="num">146</b>, and
both were overdue rather than bustouts, because both were still in the band's
rotation.</p>
<p>Within the bustout branch the gap alone decides it, with no test on how
often the song was ever played: a gap counts shows, so a large one already
proves the song has been in the catalog a long while, and nothing newly
written can reach the threshold.</p>"""),
    # The one section whose prose states the thresholds, so it is the one built
    # from them rather than written out. `.format` and not `%`: this text is a
    # quarter percent signs, and every one of them would have needed doubling.
    ('rotation', 'Dormant, rarity, %s' % FEW_TITLE.lower(), """
<p>Songs with no recent record that have been gone a hundred shows or more sit
<a href="./{page}">on their own page</a>, because there is nothing left
to rank them by. For a long time that page called all
<b class="num">281</b> of them <b>dormant</b>, and for
<b class="num">174</b> of them that was false. Dormant means a song used to be
otherwise. A song played once at a Halloween show, as part of a costume set,
never had a rotation to fall out of &mdash; and a third of the songs played
exactly once in this archive were played on a Halloween night.</p>
<p>So the page splits on how many times the band ever played the song:
<b class="num">{floor}</b> or more and it was in rotation and left, which is
<span class="verdict">dormant</span>; <b class="num">{lo}</b> to
<b class="num">{hi}</b> is a <b>rarity</b>, enough performances to notice and
never enough to become a habit; <b>{few_times}</b> and it never got going at
all.</p>
<p>The archive decides where that line goes rather than taste. Take every
silence of a hundred shows or more it holds &mdash; <b class="num">774</b> of
them &mdash; group them by how many times the song had been played when it fell
quiet, and ask how many were ever ended by another performance:</p>
<table class="figs"><thead><tr><th>Plays when it fell quiet</th>
<th class="end">Silences</th><th class="end">Ever came back</th></tr></thead>
<tbody>
<tr><td>1</td><td class="end">176</td><td class="end">28%</td></tr>
<tr><td>2</td><td class="end">72</td><td class="end">33%</td></tr>
<tr><td>3</td><td class="end">40</td><td class="end">62%</td></tr>
<tr><td>4</td><td class="end">37</td><td class="end">68%</td></tr>
<tr><td>5&ndash;7</td><td class="end">76</td><td class="end">66%</td></tr>
<tr><td>8&ndash;15</td><td class="end">104</td><td class="end">70%</td></tr>
<tr><td>16&ndash;40</td><td class="end">120</td><td class="end">85%</td></tr>
<tr><td>41 or more</td><td class="end">149</td><td class="end">93%</td></tr>
</tbody></table>
<p>Collapsed to the three groups above that is <b class="num">84%</b>,
<b class="num">65%</b> and <b class="num">30%</b>. A song that has been played
{few_times} is the only kind on that page likelier to stay gone than to come
back.</p>
<p><b>One and two are one group, and that is the second thing the table
decides.</b> The obvious line is under the one-offs, and it is the wrong one:
splitting <b>1 / 2&ndash;7 / 8+</b> the three groups return 28%, 55% and 84%,
while splitting <b>1&ndash;2 / 3&ndash;7 / 8+</b> they return 30%, 65% and 84%.
Merging widens the gap at the bottom boundary from 27 points to 35 and costs
nothing at the top. On the evidence, a song played twice and dropped is the
same object as a song played once and dropped &mdash; which is why one heading
covers both counts rather than a number naming either.</p>
<p><b>When those few plays happened matters too, but only for the rarities.</b>
Take how many shows passed per performance, and split at two hundred. A rarity
whose handful of plays sat close together came back <b class="num">70%</b> of
the time against <b class="num">38%</b> for one whose plays were strewn across
decades. Do the same to the {few_times} group and it is <b class="num">36%</b>
against <b class="num">27%</b> &mdash; those songs are not coming back whether
the pair was three shows apart or thirteen hundred, which is the other reason
they belong together.</p>
<p>There is no finer cut than that available, and the page does not pretend
there is. Shows-per-play is a single hump with a long tail rather than two
clusters &mdash; the forty-eight songs played exactly twice run 8, 12, 8, 8, 12
across the spacing buckets &mdash; so any threshold below the one above would
be a number this site made up. The years printed at the right of every row say
it exactly and without inventing anything: a single year is a song they tried
twice one summer, a range of decades is a one-off somebody revived.</p>
<p>Plays, and not something cleverer. Ten other rules were measured against the
same outcome &mdash; performances inside any fifty-, hundred- or two-hundred-show
window, and the span from a song's first performance to its last. None beat the
plain count, and span was the worst of them: whether a song was ever in rotation
is answered by how many times the band played it, not by how long they had it
lying around.</p>
<p>A song called back for one night after years away does not get a fourth
name. It is an event rather than a state, and the play count already carries
it: the song moves up by one, and a second performance has not moved it out of
the section it was already in. Whether it
sticks is not knowable on the night, but it is not a coin toss either. Of
returns from a silence of three hundred shows or more that have since had three
hundred shows of chance, the ones that had been played <b>once</b> before went
quiet again for good <b class="num">43%</b> of the time; those played two to
seven times, <b class="num">27%</b>; those played eight or more,
<b class="num">7%</b>.</p>""".format(
        floor=ROTATION_PLAYS, lo=FEW_PLAYS + 1, hi=ROTATION_PLAYS - 1,
        few_times=FEW_TIMES, few_title=FEW_TITLE.lower(),
        page=ROTATION_PAGE)),
    ('ratings-and-jam-charts', 'Ratings and jam charts', """
<p>Version scores and the Phish.net show rating both come by way of
<b>fouldomain</b>, which is the only place the latter is exposed
programmatically. Scores are computed from a mix of community signal and audio
analysis, so a version has none until a recording of it circulates &mdash;
days or weeks after the show, sometimes never. Jam chart entries are Phish.net's
own, written months after the fact. Both are treated as optional everywhere
they appear, which is why a report published the morning after a show carries
neither.</p>"""),
    ('when-a-report-appears', 'When a report appears', """
<p>A report is published while the show is still being played. Songs appear on
it as phish.net records them, the page says <b>setlist still coming in</b> with
how much is there and when it last moved, and it reloads itself every couple of
minutes. The index says <b>so far</b> next to the song count, because
<span class="num">24</span> songs means something different tonight than it
will tomorrow.</p>
<p>Knowing when it is <em>finished</em> is the harder half, and nothing in the
data says so. There is no show time to reason from, and the format is not
promised &mdash; a rained-out show can stop mid-second-set with no encore, so
counting sets proves nothing. Stability stands in for completeness instead:
once a song count has not moved for <b>two hours</b>, the show is taken to be
over and the report stops calling itself provisional.</p>
<p>Until that happens the figures are real but partial. A median gap over nine
songs is the median of those nine, not of the night, and the preview image
shared from that page deliberately carries no figures at all &mdash; only the
date, the venue, and that the setlist is still coming in &mdash; so a link
shared mid-show does not freeze a half-finished number into somebody else's
timeline.</p>"""),
)


def render_method(card=None):
    """The page the footers point at when a number wants explaining."""
    # The heading goes inside a span of its own, for the reason render_faq
    # records: .toc a is a two-column grid, and a grid container makes every
    # child a grid item, so any inline markup inside a heading would take a
    # cell of its own and break the entry across lines.
    toc = "".join(
        "<li><a href=\"#%s\"><span>%s</span></a></li>" % (anchor, head)
        for anchor, head, _ in METHOD)
    body = "\n".join(
        "<h2 id=\"%s\">%s</h2>\n%s\n"
        "<p class=\"backtop\"><a href=\"#sections\">&uarr; All sections</a></p>"
        % (anchor, head, text.strip())
        for anchor, head, text in METHOD)
    blurb = ("How the gaps, the medians and the verdicts on this site are "
             "worked out.")
    return METHOD_SHELL.format(
        crumb=nav_strip(here="How this works"),
        ago_js=AGO_JS,
        new_rows_js=NEW_ROWS_JS,
        analytics=ANALYTICS,
        css=METHOD_CSS, totop=TOTOP_JS, fonts=WEB_FONTS, sheet=sheet_links("./%s/%s" % (STATIC_DIR, SITE_SHEET)),
        theme_js=THEME_JS, keys_js=KEYS_JS, theme_ui=THEME_UI,
        toc=toc, body=body,
        share=share_meta("How this is worked out", html.escape(blurb, quote=True),
                         "method.html", card=card))


# -------------------------------------------------------------------- faq ---

# Built on the method page's sheet rather than beside it, so the two prose
# pages cannot drift and stripping INDEX_CSS out of METHOD_CSS later fixes both
# at once.
FAQ_CSS = METHOD_CSS + """
/* Questions are questions, so they are set in the reading face rather than in
   Bagnard like the method page's headings -- those are labels for sections,
   these are sentences somebody would say out loud. */
/* 500, not 600: Literata is requested across 400..500, so anything heavier
   clamps to 500. Measured -- the same string sets to an identical 297.89px at
   500, 600 and 700 -- so this is a declaration matching what is drawn rather
   than a fix to something visible. `.prose b` asks for 700 and gets 500 the
   same way, which is why bold prose on the method page is not faux-bolded. */
.prose h2{font-family:'Literata',Georgia,serif;font-size:1.0625rem;
   font-weight:500;font-variation-settings:'opsz' 16;margin:2.4rem 0 .6rem;
   color:var(--ink);scroll-margin-top:1rem}
.prose h2:first-child{margin-top:0}
/* A mark and what it means. The mark is mono because it is a mark -- the same
   glyph the setlists print -- and the gloss is prose. */
.defs{margin:0 0 1rem}
.defs dt{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;
   font-size:.9375rem;color:var(--ink);margin:.8rem 0 0}
.defs dd{margin:.15rem 0 0;font-family:'Literata',Georgia,serif;
   font-size:1rem;line-height:1.6;font-variation-settings:'opsz' 16;
   color:var(--ink-soft)}
"""

FAQ_SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>FAQ &mdash; Possum Logic</title>
<meta property="og:type" content="article">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}{ago_js}{new_rows_js}</head><body id="top"><div class="wrap">
<a class="skip" href="#main">Skip to content</a>
{crumb}
<div class="rule2"></div>
<header><h1><a href="./index.html">Possum <em>Logic</em></a></h1>
<p class="show">FAQ</p>
<p class="dek">What the numbers on this site mean, and what they deliberately
do not.</p></header>
<div class="rule2"></div>
<div class="prose" id="main" tabindex="-1">
<nav class="toc" id="questions" tabindex="-1" aria-label="Questions on this page"><span class="cap">Questions on this page</span>
<ol>{toc}</ol></nav>
{body}</div>
{totop}
""" + footer_html(right=None) + """
{analytics}
</div></body></html>
"""

# (anchor, question, answer). One list, so the contents at the top of the page
# and the entries under it are the same thing rendered twice.
FAQ = (
    ("what-is-a-gap", "What is a gap?", """
<p>The number beside a song on a show page is how many shows the band played
between that performance and the one before it. A gap of
<b class="num">0</b> means they played it again the very next night;
<b class="num">485</b> means four hundred and eighty-five shows went by. This
site counts it from the show calendar rather than taking phish.net&rsquo;s.</p>
<p>It used to take phish.net&rsquo;s, and phish.net&rsquo;s is a different
number. Most of its gaps count the show itself, so a song played two nights
running reads 1 there, and some do not; in the autumn of 2026 it renumbered
figures it had already published, and a song entered during a show reads 0
until it gets round to measuring it. Counted against the calendar, its gap
was one too high on three performances in four. So the figure here is now
simply the definition above, counted.</p>
<p>A gap is not a length of time. A song with a gap of 30 in 1995 had been gone
about five weeks; the same gap today is closer to a year.</p>"""),

    ("shows-since", "Why does a song page say &ldquo;shows since&rdquo; rather"
                    " than giving a current gap?", """
<p>Because a gap belongs to a performance &mdash; it is measured back from the
night the song was played &mdash; and until the song is played again there is
no performance to measure from. So the live figure counts the shows the band
has played since this song was last played, and calls it that. It is counted
off the same calendar as every gap on the site, so the day the song comes
back, its gap is the number this page was showing the night before.</p>"""),

    ("segues", "What do <span class=\"num\">&gt;</span> and"
               " <span class=\"num\">&#8211;&gt;</span> mean, and how do they"
               " differ?", """
<p>Both are phish.net&rsquo;s marks, both say the band did not stop between two
songs, and they are not interchangeable. Their definitions:</p>
<dl class="defs">
<dt>&#8211;&gt;</dt><dd>An actual segue: one song jams fluidly and without
interruption into another.</dd>
<dt>&gt;</dt><dd>Everything else that runs together &mdash; one song stops and
the next starts immediately with no jamming between them, or a member begins
the next while the last is still ending.</dd>
</dl>
<p>The second one also carries a convention, which is the part worth knowing.
phish.net uses <span class="num">&gt;</span> between songs that are simply
always played together &mdash; Mike&rsquo;s Song, I Am Hydrogen and Weekapaug
Groove; The Horse and Silent in the Morning &mdash; and around lead-in and exit
songs such as Hold Your Head Up, <em>even where there was an audible gap in the
music</em>. A <span class="num">&gt;</span> is not always a claim about
sound.</p>
<p>On this site a plain <span class="num">&#8592;</span> or
<span class="num">&#8594;</span> means neither of those: the song before or
after, played as its own song, with a stop between them. The arrow is the
absence of a segue rather than the presence of anything.</p>
<p class="src">Definitions are phish.net&rsquo;s, from
<a href="https://phish.net/faq/segues" target="_blank"
rel="noopener noreferrer">their FAQ on segues</a>.</p>"""),

    ("no-bar", "Why does this row have no range bar?", """
<p>A song needs <b>eight</b> performances inside the ten-year window before
there is a usual range to draw. Below that there is no norm for a performance
to be early or late against, so the cell carries a dim
<span class="num">&mdash;</span> rather than an empty track implying a
comparison that was never made.</p>
<p>Two quite different songs land there: one played six times in ten years, and
one not played in ten years at all. The statistics say which.</p>"""),

    ("due", "What does &ldquo;due&rdquo; mean, and why is a song that has been"
            " gone for years not on the list?", """
<p>Due means past its own recent usual gap &mdash; measured against that
song&rsquo;s habit, not against a single number for the whole catalog. A
staple is late at eight shows and a rarity is not late at eighty.</p>
<p><em>Recent</em> means the last ten years of shows, counted back from the
newest show in the archive rather than from the song&rsquo;s own last night on
stage. That distinction is the whole of the previous paragraph: measured from
its own last performance, a song that stopped being played in 2011 still has a
tidy ten-year habit ending in 2011, and would be ranked as running late against
a band that has since played a thousand shows without it.</p>
<p>Being late is not the same as being expected, though, and more late is not
more expected. A song at six times its usual gap is not one anybody is waiting
on; it is drifting out of rotation. So the <a href="./due.html">due page</a>
sorts songs into four:</p>
<dl class="defs">
<dt>Due</dt><dd>The band plays it at least every twenty shows or so, and it is
now past its usual gap but less than three and a half times past. A song you
would not be surprised to hear tonight.</dd>
<dt>Slipping</dt><dd>Well past its usual gap, or too rare to expect on any one
night. Could come back, could be on the way out of rotation.</dd>
<dt>On the shelf</dt><dd>Gone more than a hundred shows &mdash; long enough
that the habit it is being measured against has probably stopped being
true.</dd>
<dt>Out of rotation</dt><dd>No recent record at all, and gone a hundred shows or
more. Nobody is expecting it, and ranking these would bury the songs somebody
might actually shout for tonight &mdash; so they have
<a href="./{page}">a page of their own</a>, grouped by the year they were
last heard rather than by a lateness they cannot have.</dd>
</dl>
<p>That fourth group is three groups, and the difference matters more than the
other three lists put together. <em>Dormant</em> means a song used to be
otherwise, and that is only true of the ones the band actually played: a song
performed once at a Halloween show never had a rotation to fall out of. So the
page splits on how many times the song was ever played &mdash; {floor} or more
is <strong>dormant</strong>, {lo} to {hi} is a <strong>rarity</strong>, and a
song played <strong>{few_times}</strong> is filed under exactly that &mdash;
and the archive says the
split is worth making. Of every silence of a hundred shows or more it holds,
the share ever ended by another performance runs 84%, 65% and 30% down those
three. A song played {few_times} is the only kind here that is likelier to
stay gone than to come back, which is the one thing the old single list could
not say.</p>
<p><em>Slipping</em>, not <em>overdue</em>, because a show page already uses
overdue for something narrower: a single performance that came back later than
that song usually does. Every song on the due page would be stamped overdue if
it turned up tonight, so the word cannot also name one of the lists.</p>
<p>None of it knows what the band has planned. A themed night overrides every
figure &mdash; the 2021 Halloween runs built around numbers and animals, the
elements nights of the first Sphere run, a run played out of a single decade
&mdash; and the theme is usually not public beforehand.</p>
<p>The hundred-show line is where this site already draws a bustout. It is
counted in shows rather than in months on purpose: a gap of thirty-six shows is
thirty-six chances to hear it, whether the band took eight months over them or
two years. The band averaged about ninety-five shows a year through the 1990s
and about forty-four across 2021&ndash;2025, so counting in time would quietly
mean something different in each era.</p>
<p>Within each list the order is how far past each song is as a multiple of its
own usual gap &mdash; the figure on the right of every row &mdash; not how many
shows it has been gone, since a hundred shows is nothing for one song and a
decade for another.</p>""".format(
        floor=ROTATION_PLAYS, lo=FEW_PLAYS + 1, hi=ROTATION_PLAYS - 1,
        few_times=FEW_TIMES, few_title=FEW_TITLE.lower(),
        page=ROTATION_PAGE)),

    ("eras", "What are the eras &mdash; 1.0, 2.0, 3.0 and 4.0?", """
<p><em>Era</em> is the word this site uses for them, and the one on the chips
that group a song&rsquo;s performances and filter the show list. There are four
of them, and they are separated by the <em>three</em> long breaks between them:
the hiatus that began in 2000, the split that followed Coventry, and the
shutdown of 2020.</p>
<p>Bounded by date rather than by year, because every one of those breaks falls
mid-year.</p>
<dl class="defs">
<dt>1.0</dt><dd>The beginning through 2000-10-07, the last show before the
hiatus.</dd>
<dt>2.0</dt><dd>2002-12-31 to 2004-08-15, ending at Coventry.</dd>
<dt>3.0</dt><dd>2009-03-06, the Hampton reunion, to 2020-02-23.</dd>
<dt>4.0</dt><dd>2021-07-28 onwards.</dd>
</dl>
<p>They are used here for grouping and for counting a show&rsquo;s place inside
its own era &mdash; the <span class="num">312th</span> show of 3.0 &mdash;
because there is no honest count of where a show sits overall.
<a href="./method.html#which-show-this-was">The method page says why.</a></p>"""),

    ("not-part-of-a-tour", "Why do some shows say &ldquo;Not Part of a"
                          " Tour&rdquo;?", """
<p>Because phish.net does. It is where they file everything that was not a leg
of a tour: the festivals, the television and radio sessions, the New Year&rsquo;s
runs held somewhere unusual, and the Mexico runs.</p>
<p>Several of those have famous names, and this site does not print them,
which is deliberate. The names exist only inside freeform prose notes, spelled
inconsistently and often not at all &mdash; pulling them out gives a handful of
shows a label, some of them wrong, and leaves the rest blank. A blank is
honest. A wrong festival name is not.</p>"""),

    ("where-from", "Where does all of this come from?", """
<p>Three projects. <b>Phish.net</b> &mdash; a project of the volunteer-run
Mockingbird Foundation &mdash; is the setlists, the gaps, the venues and tours,
and the show ratings. <b>phish.in</b> is every <b>Listen</b> link, and holds
the audio. <b>fouldomain</b> is the version scores.</p>
<p>Each of them is worth more than the credit line a footer can hold, so
<a href="./{ack}">they have a page</a>: who they are, what they give away, and
where to send money if any of this has been useful.</p>""".format(
        ack=ACK_PAGE)),

    ("still-coming-in", "Why does a show page say &ldquo;setlist still coming"
                        " in&rdquo;?", """
<p>Because the show is still being played. A report is published mid-show and
fills in as phish.net records each song, so the figures on it are real but
partial &mdash; a median gap over nine songs is the median of those nine, not
of the night.</p>
<p>Nothing in the data says when a show has ended, so stability stands in for
it: once the song count has stopped moving, the report stops calling itself
provisional.
<a href="./method.html#when-a-report-appears">The method page says how
long.</a></p>"""),
)


def render_faq(card=None):
    """Short answers, deep-linkable, with the long reasoning left on method."""
    # The question goes inside a span of its own. The anchor is a two-column
    # grid -- number, question -- and a grid container makes *every* child a
    # grid item, so the <span class="num"> marks inside the segues question
    # were each taking a cell and that entry rendered as three broken lines.
    # One element for the whole question, whatever markup is inside it.
    toc = "".join(
        "<li><a href=\"#%s\"><span>%s</span></a></li>" % (anchor, question)
        for anchor, question, _ in FAQ)
    # Every answer ends with the way back to the index. `tabindex="-1"` on the
    # target means keyboard focus actually lands there rather than staying
    # where it was, so the next Tab is the first question and not whatever
    # followed the link.
    body = "\n".join(
        "<h2 id=\"%s\">%s</h2>\n%s\n"
        "<p class=\"backtop\"><a href=\"#questions\">&uarr; All questions</a></p>"
        % (anchor, question, answer.strip())
        for anchor, question, answer in FAQ)
    blurb = ("What the numbers on this site mean: gaps, segue marks, eras, "
             "and what &ldquo;due&rdquo; counts as.")
    return FAQ_SHELL.format(
        crumb=nav_strip(here="FAQ"),
        ago_js=AGO_JS,
        new_rows_js=NEW_ROWS_JS,
        analytics=ANALYTICS,
        css=FAQ_CSS, totop=TOTOP_JS, fonts=WEB_FONTS, sheet=sheet_links("./%s/%s" % (STATIC_DIR, SITE_SHEET)),
        theme_js=THEME_JS, keys_js=KEYS_JS, theme_ui=THEME_UI,
        toc=toc, body=body,
        share=share_meta("FAQ", html.escape(blurb, quote=True),
                         "faq.html", card=card))


# ------------------------------------------------------- acknowledgments ---

# Built on the method page's sheet like the FAQ is. The one rule this page
# wanted from elsewhere -- `.src`, the small dim line under a heading naming
# where something came from -- was on the FAQ's sheet, which is built on this
# one, so it moved down into METHOD_CSS rather than being copied up.
#
# The colophon is this page's own, and it is a block rather than a fifth
# section on purpose. Ian: "it's of a different nature than the data and
# service and source material providers, so I feel like it should be set off
# somehow. Font designers deserve love, though." A typeface is a tool this
# site was made with; the three above it are the material it is made of. So it
# gets the tear line this site already uses between one set and the next, a
# caption where the others have a heading, and a size down -- a coda, not a
# fourth name in the list.
#
# `.prose .colophon p` and not `.colophon p`: the latter is one class and one
# type, exactly equal to `.prose p`, so it would win on source order alone --
# and betting on source order is how `.src` and `.backtop` came to be rules
# that had never once been drawn.
ACK_CSS = METHOD_CSS + """
.colophon{max-width:66ch;margin:0 0 1rem}
.colophon .cap{display:block;font-size:.625rem;letter-spacing:.14em;
   text-transform:uppercase;color:var(--ink);font-weight:600;margin:0 0 .7rem}
.prose .colophon p{font-size:.9375rem;font-variation-settings:'opsz' 15;
   margin:0 0 .7rem}
.prose .colophon p:last-child{margin-bottom:0;color:var(--dim)}
/* Each name set in the face it names, which is the whole convention of a
   colophon and the only place on this site where all three appear together.
   Not <b>: Bagnard ships at 400 and nothing else, so asking for bold would
   have the browser draw a synthetic one -- a slanted, smeared version of a
   face being shown off. The weight each of these gets is the weight it has.
   Plex is stepped down because a mono at the same nominal size sets visibly
   larger than a serif beside it. */
/* A name is one word however many spaces are in it: IBM Plex Mono broke over
   two lines at this measure, and a typeface's name snapped in half is a poor
   advertisement for the care being thanked. */
.colophon .f-bag,.colophon .f-lit,.colophon .f-mono{white-space:nowrap}
.colophon .f-bag{font-family:'Bagnard',Georgia,serif;font-size:1.0625rem}
.colophon .f-lit{font-family:'Literata',Georgia,serif;font-weight:500}
.colophon .f-mono{font-family:'IBM Plex Mono',ui-monospace,monospace;
   font-weight:600;font-size:.875rem}
"""

ACK_SHELL = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Acknowledgments &mdash; Possum Logic</title>
<meta property="og:type" content="article">{share}
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>{css}</style>{theme_js}{keys_js}{ago_js}{new_rows_js}</head><body id="top"><div class="wrap">
<a class="skip" href="#main">Skip to content</a>
{crumb}
<div class="rule2"></div>
<header><h1><a href="./index.html">Possum <em>Logic</em></a></h1>
<p class="show">Acknowledgments</p>
<p class="dek">This archive rests on three projects, and on the people who
keep them going.</p></header>
<div class="rule2"></div>
<div class="prose" id="main" tabindex="-1">
{body}
<div class="perf"></div>
<div class="colophon">
<span class="cap">Set in</span>
<p><a class="f-bag" href="https://github.com/sebsan/Bagnard" target="_blank"
rel="noopener noreferrer">Bagnard</a>, by Sebastien Sanfilippo.
<a class="f-lit" href="https://www.type-together.com/literata-font"
target="_blank" rel="noopener noreferrer">Literata</a>, by TypeTogether.
<a class="f-mono" href="https://www.ibm.com/plex/" target="_blank"
rel="noopener noreferrer">IBM Plex Mono</a>, by Mike Abbink and Bold
Monday.</p>
<p>All three are given away under the SIL Open Font License &mdash; years of
drawing, free to anyone, and the reason this site can look like itself.</p>
</div></div>
{totop}
""" + footer_html(right=None, here=ACK_PAGE) + """
{analytics}
</div></body></html>
"""

# (anchor, heading, source line, body). No contents block, unlike the two
# prose pages this is built beside: theirs index eight and nine sections, and
# an index over four would be furniture -- a list of the same four headings
# already visible without scrolling.
#
# Short on purpose. The first draft said what this site is *not* three times
# over -- no audio, no opinion, nothing of its own -- and Ian read it as
# self-deprecation wearing a thank-you: "keep our thanks succinct, heartfelt,
# and earnest, without pontificating too much." It also carried a remark about
# how long phish.in takes to post audio after a show, which is a true
# operational fact and, on a page of thanks, a backhanded one. Both are gone.
# What each project gives, who gives it, and where to send money.
#
# `{listens}` in the phish.in entry is filled at render time from the
# catalogue on disk, because a count typed into prose is a figure like any
# other and goes stale the ordinary way -- a comment in this file said "nine"
# soundchecks for the eleven months it was twenty. It is left out entirely
# when the catalogue has never been fetched, rather than printed as zero.
ACKNOWLEDGMENTS = (
    ("phish-net", "Phish.net, and the Mockingbird Foundation",
     '<a href="https://phish.net/" target="_blank" rel="noopener noreferrer">'
     'phish.net</a> &middot; '
     '<a href="https://mbird.org/" target="_blank" rel="noopener noreferrer">'
     'mbird.org</a>', """
<p>The setlists are theirs: what was played, in what order, what ran into what,
at which venue, on which tour. So are the gaps and the show ratings, and the
jam chart notes under a performance.</p>
<p>Phish.net is a project of the <b>Mockingbird Foundation</b>, a 501(c)(3)
started in 1996 by fans and run entirely by volunteers &mdash; no salaries, no
paid staff, no office. Hundreds of people have kept that record night after
night for close to thirty years, which the Foundation conservatively estimates
at over <b class="num">100,000</b> hours. It is an extraordinary thing to have
been given.</p>
<p>And it is a means rather than an end. The Foundation exists to fund music
education for children, and by July 2026 had made its <b class="num">800th</b>
grant, more than <b class="num">$3</b> million in total. If this site has been
of any use to you,
<a href="https://mbird.org/donations/" target="_blank"
rel="noopener noreferrer">that is a good place to send something</a>.</p>"""),

    ("phish-in", "phish.in",
     '<a href="https://phish.in/" target="_blank" rel="noopener noreferrer">'
     'phish.in</a>', """
<p>Every <b>Listen</b> link goes to phish.in, an open archive of audience
recordings made under the band&rsquo;s own taping policy.{listens} Because of
them, a page about a performance can be a way to hear it.</p>
<p>The recordings themselves are the tapers&rsquo;, made at their own expense
and given away, and phish.in is where forty years of that generosity is kept
in one place and kept free.</p>"""),

    ("fouldomain", "fouldomain",
     '<a href="https://fouldomain.com/" target="_blank" '
     'rel="noopener noreferrer">fouldomain.com</a>', """
<p>The version scores are fouldomain&rsquo;s: every circulating performance
rated out of <b class="num">100</b> from a blend of audio analysis and
community signal, recomputed nightly. It is also how phish.net&rsquo;s own show
rating reaches this site, since their API does not expose it.</p>
<p>It is one person&rsquo;s work &mdash; <b>Kevin Spence</b>, building on
phish.net&rsquo;s setlists and phish.in&rsquo;s audio &mdash; and it is the
reason a song page here can point you at a version worth hearing rather than
just counting the times it was played.</p>"""),

    ("the-band", "And the band",
     "", """
<p>This site is not affiliated with Phish and not endorsed by them. The taping
policy is theirs, though, and it is a generous and unusual one: forty years of
live music recorded, traded and given away with permission. Every archive on
this page rests on it.</p>"""),
)


def render_acknowledgments(on_phishin=None):
    """Who the data belongs to, at the address every footer points at.

    Off the nav strip on purpose -- see ACK_PAGE -- so its door is the footer,
    which is the one element every page on this site carries. The strip marks
    FAQ as this page's section, because the FAQ is where a reader asking
    "where does this come from?" is answered in a paragraph and sent here for
    the rest.
    """
    listens = ""
    if on_phishin:
        listens = (" Their archive covers <b class=\"num\">%s</b> nights."
                   % f"{len(on_phishin):,}")
    body = "\n".join(
        "<h2 id=\"%s\">%s</h2>\n%s\n%s"
        % (anchor, head,
           "<p class=\"src\">%s</p>" % src if src else "",
           text.strip().format(listens=listens))
        for anchor, head, src, text in ACKNOWLEDGMENTS)
    blurb = ("The sources this archive is built from: phish.net and the "
             "Mockingbird Foundation, phish.in, and fouldomain.")
    return ACK_SHELL.format(
        crumb=nav_strip(section="FAQ"),
        ago_js=AGO_JS,
        new_rows_js=NEW_ROWS_JS,
        analytics=ANALYTICS,
        css=ACK_CSS, totop=TOTOP_JS, fonts=WEB_FONTS,
        sheet=sheet_links("./%s/%s" % (STATIC_DIR, SITE_SHEET)),
        theme_js=THEME_JS, keys_js=KEYS_JS, theme_ui=THEME_UI,
        body=body,
        share=share_meta("Acknowledgments", html.escape(blurb, quote=True),
                         ACK_PAGE))


# ------------------------------------------------------------------ cards ---

CARD_W, CARD_H = 1200, 630
# How many cards go into one browser launch. Each launch costs about 2.7s of
# startup and a font fetch, so doing them one at a time put eight minutes on a
# full rebuild; stacked and sliced, the same 185 take about twenty seconds.
# Chrome will not screenshot past roughly 16,000px, which is 26 of these.
CARDS_PER_SHOT = 24
# What each card was drawn from, so a card is redrawn when its own contents
# change and not merely when the page around it does. A stylesheet edit
# rewrites every page and no card: the two have nothing in common but a name.
CARD_INDEX = "cards.json"


def card_prints(site_dir):
    path = os.path.join(site_dir, "data", CARD_INDEX)
    if not os.path.isfile(path):
        return {}
    with open(path, encoding="utf-8") as fh:
        try:
            return json.load(fh)
        except ValueError:
            return {}


def save_card_prints(site_dir, prints):
    path = os.path.join(site_dir, "data", CARD_INDEX)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(prints, fh, indent=1, sort_keys=True)


# Bumped by hand when the way a card is drawn changes somewhere the hash below
# cannot see -- the shooter's flags, the fonts it is pointed at, the substitution
# `shoot_cards` performs on the shell. Without it a fix to the drawing pipeline
# leaves every card in the index recorded as current, and nothing is ever
# redrawn: on 2026-07-30 all 1,301 recorded hashes matched the then-current code
# while 14 of the published images had "{sheet}" printed across the top of them.
# A version field is the only thing that can express "same input, different
# output" -- see docs/TODO.md 8i.
CARD_REVISION = 2


def card_print(markup):
    """What a card would look like, as a hash.

    The stylesheet is part of it. It was not, on the reasoning that a page
    carries a stylesheet and a card does not -- but CARD_CSS *is* the card's
    stylesheet, so changing the display face would have redrawn none of the
    711 cards and left every one of them set in the old type with no way to
    notice. A card is markup plus the rules that draw it.

    And the shell it is drawn in, for the same reason one step out: CARDS_SHELL
    carries the font links, so an edit there changes every card's type and used
    to change no card's hash. That is how the "{sheet}" leak survived three days
    and would have survived indefinitely -- the index was not wrong about the
    markup, it was answering a narrower question than the one being asked.
    """
    return hashlib.sha256(
        ("%d\n%s%s%s" % (CARD_REVISION, markup, CARD_CSS, CARDS_SHELL)
         ).encode("utf-8")).hexdigest()[:16]


def chrome_exe():
    """The Chrome-family browser to shoot cards with, or None."""
    exe = next((c for c in CHROME_CANDIDATES
                if os.path.isfile(c) or shutil.which(c)), None)
    return exe if not exe or os.path.isfile(exe) else shutil.which(exe)


CARD_CSS = """
*{box-sizing:border-box;margin:0}
body{background:#e9e3d6;font-family:'IBM Plex Mono',ui-monospace,monospace}
/* The bottom padding is the wordmark's strip, reserved. The wordmark is
   positioned absolutely and the content is centered in the box, so a title that
   took three lines pushed the figures down onto it -- "The Inner Reaches of
   Outer" printed POSSUMLOGIC hard against TIMES PLAYED. Centring inside a box
   that stops short of the wordmark cannot collide with it at any title length,
   where stepping the type size down again only moves the length where it
   happens. */
.card{width:%(w)dpx;height:%(h)dpx;background:#f2ece0;color:#17150f;
  display:flex;flex-direction:column;justify-content:center;
  padding:0 84px 84px;position:relative;overflow:hidden}
.kind{font-size:25px;letter-spacing:.14em;text-transform:uppercase;color:#877e6e}
/* Kept clear of the mark, which starts around x=870: without a ceiling a
   middling title like "You Enjoy Myself" ran under it and the last word went
   muddy. Wrapping is better than colliding. */
h1{font-family:'Bagnard',Georgia,serif;font-weight:400;line-height:.94;
   letter-spacing:-.01em;margin-top:16px;word-break:break-word;max-width:770px}
/* Same rule as the pages: a card whose headline is a date or a song title
   sets it in Aleo, so a link and the page behind it speak the same way. */
h1.data{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;letter-spacing:-.01em}
h1 em{font-style:normal;color:#c8371b}
/* Wraps. It was nowrap + text-overflow:ellipsis, which cut 212 of the drawn
   cards mid-venue -- "Bonnaroo Music & Arts Festival, Manchest…" -- and looked
   deliberate doing it. A preview card is a thing people see instead of the
   page, so it is the last place that should be quietly dropping words. Two
   lines is fine here: the content is centred in a box that stops short of the
   wordmark strip, so a second line moves the block, not the brand. */
.sub{font-size:30px;letter-spacing:.14em;text-transform:uppercase;color:#413c31;
  margin-top:20px;line-height:1.25}
.rule{height:7px;background:#17150f;margin-top:38px}
.stats{display:flex;gap:58px;margin-top:30px;font-size:23px;letter-spacing:.14em;
  text-transform:uppercase;color:#877e6e}
.stats b{font-family:'IBM Plex Mono',ui-monospace,monospace;font-weight:600;font-size:52px;
  letter-spacing:0;color:#17150f;display:block;margin-bottom:4px;white-space:nowrap}
.stats .hot{color:#c8371b}
.mark{position:absolute;right:-64px;top:-72px;width:392px;height:392px;opacity:.12}
.brand{position:absolute;left:84px;bottom:40px;font-size:21px;letter-spacing:.14em;
  text-transform:uppercase;color:#877e6e}
""" % {"w": CARD_W, "h": CARD_H}

CARDS_SHELL = """<!DOCTYPE html><html><head><meta charset="utf-8">
<link href="{fonts}" rel="stylesheet">
{sheet}
<style>%s</style></head><body>__CARDS__</body></html>""" % CARD_CSS


#: What .sub can hold now that it wraps: two lines rather than one. The card is
#: 1200px with 84px of padding each side and .sub is 30px mono tracked .14em,
#: which measures about 22.1px per character -- 46 to a line, so 92 to two, and
#: 88 leaves a couple of characters of slack. Nothing on the site comes near
#: it; the longest venue in the archive is 46. It is a backstop against a
#: subtitle long enough to push the figures into the wordmark, not a line
#: anything is expected to sit against.
CARD_SUB_MAX = 88


def card_sub(text):
    """A subtitle that fits .sub, trimmed on a word boundary when it does not.

    An assert was the first shape of this and it was wrong: it stopped the
    build on "Bonnaroo Music & Arts Festival, Manchester, TN", which is a
    venue, which is data. Not everything that overflows is a sentence somebody
    can rewrite.

    Two things it does that leaving it to CSS did not. It measures *rendered*
    glyphs -- html.unescape first, because "&amp;" is five characters and one
    glyph, and counting the source called that venue 50 wide when it is 45.
    And it cuts on a word boundary and says so in the log, where
    `text-overflow:ellipsis` cut mid-character and said nothing: some published
    show cards have carried a chopped venue since the day they were drawn and
    nothing anywhere reported it.
    """
    plain = html.unescape(text)
    if len(plain) <= CARD_SUB_MAX:
        return text
    cut = plain[:CARD_SUB_MAX - 1].rsplit(" ", 1)[0].rstrip(" ,;-") + "\u2026"
    log("card subtitle trimmed to fit: %r -> %r", plain, cut)
    return html.escape(cut)


def card_markup(kind, title, subtitle, stats, size=96, data=False):
    """One 1200x630 card: what it is, what it is called, and three figures."""
    subtitle = card_sub(subtitle)
    figures = "".join(
        "<span><b class='%s'>%s</b>%s</span>" % (cls, val, lbl)
        for val, lbl, cls in stats)
    return ("<div class='card'>%s"
            "<div class='kind'>%s</div>"
            "<h1 class='%s' style='font-size:%dpx'>%s</h1>"
            "<div class='sub'>%s</div><div class='rule'></div>"
            "<div class='stats'>%s</div>"
            "<div class='brand'>possumlogic</div></div>"
            % (FAVICON.replace("<svg", "<svg class='mark'", 1), kind,
               "data" if data else "", size, title, subtitle, figures))


def shoot_cards(exe, jobs, site_dir):
    """Render a batch of cards in one browser launch, then slice them apart.

    -> the number written. Any failure is reported and returns 0, because a
    missing card costs a page its preview image and nothing else.
    """
    try:
        from PIL import Image
    except ImportError:
        log("cards: Pillow not installed, skipping previews")
        return 0
    out_dir = os.path.join(site_dir, CARD_DIR)
    os.makedirs(out_dir, exist_ok=True)
    written = 0
    for start in range(0, len(jobs), CARDS_PER_SHOT):
        batch = jobs[start:start + CARDS_PER_SHOT]
        # replace, not format: the stylesheet above is full of braces. Which
        # is exactly why `{fonts}` and `{sheet}` have to be replaced by hand --
        # they are .format() fields in a template nothing ever calls .format()
        # on, so both stood as literal text. `{fonts}` sat inside an href and
        # merely 404ed; `{sheet}` had been inside one too until it was unwrapped
        # on 2026-07-27, and bare text in <head> is moved into <body> by the
        # parser, painted at the top of the page and captured in the first card
        # of every 24-card batch. 14 published cards carry a visible "{sheet}",
        # among them index.png and due.png -- the two a shared link is most
        # likely to unfurl. Neither face was loading either, so every card has
        # been drawn in fallbacks.
        #
        # The sheet is addressed absolutely: the markup is written to a temp
        # directory, so a relative sheet name resolves next to the temp file
        # and never to the built site.
        page = (CARDS_SHELL
                .replace("{fonts}", WEB_FONTS)
                .replace("{sheet}", sheet_links(
                    "file://" + urllib.parse.quote(
                        os.path.abspath(os.path.join(site_dir, STATIC_DIR, SITE_SHEET)))))
                .replace("__CARDS__", "".join(m for _, m in batch)))
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "cards.html")
            shot = os.path.join(tmp, "cards.png")
            with open(src, "w", encoding="utf-8") as fh:
                fh.write(page)
            cmd = [exe, "--headless", "--disable-gpu", "--hide-scrollbars",
                   "--force-device-scale-factor=1",
                   "--window-size=%d,%d" % (CARD_W, CARD_H * len(batch)),
                   "--screenshot=" + shot,
                   # Generous, because the whole batch waits on the webfonts
                   # and display=swap will happily paint a fallback first --
                   # at 6s the third family was still in flight and cards came
                   # out in whatever the system offered.
                   "--virtual-time-budget=15000",
                   "file://" + urllib.parse.quote(src)]
            try:
                with _muted_stderr():
                    subprocess.run(cmd, check=True, timeout=180,
                                   stdout=subprocess.DEVNULL,
                                   stderr=subprocess.DEVNULL)
                sheet = Image.open(shot)
            except (subprocess.SubprocessError, OSError) as exc:
                log("cards: %s", exc)
                return written
            for i, (name, _) in enumerate(batch):
                top = i * CARD_H
                if top + CARD_H > sheet.height:
                    break
                sheet.crop((0, top, CARD_W, top + CARD_H)).save(
                    os.path.join(out_dir, "%s.png" % name), optimize=True)
                written += 1
    return written


def report_card(report):
    """A show: what it was, where, and the night's headline gap.

    A show still being played gets a different card, and deliberately a fixed
    one. Withholding it entirely was the wrong call: a show in progress is
    exactly when a link gets shared, and a shared link with no preview is the
    one that looks broken. But drawing the real card would redraw it every five
    minutes all night, so the in-progress card says only what will not change
    -- the date, the venue, and that the setlist is still coming in. Its
    content hash is therefore stable, so it is drawn once at first sighting and
    then left alone until the show settles and the real one replaces it.
    """
    if report.get("provisional"):
        return card_markup(
            "Possum Logic", html.escape(report["date"]),
            html.escape((report.get("venue") or "").upper()),
            ((" ", "Setlist still coming in", "hot"),),
            size=104)
    gaps = [s["gap"] for s in report["songs"] if s["gap"] is not None]
    biggest = max(gaps) if gaps else None
    song = next((s["song"] for s in report["songs"] if s["gap"] == biggest), "")
    where = report.get("venue") or ""
    return card_markup(
        "Possum Logic", html.escape(report["date"]), html.escape(where.upper()),
        (("%d" % len(report["songs"]), "Songs", ""),
         (_stat(_median(gaps)) if gaps else "&mdash;", "Median gap", ""),
         (_stat(biggest) if gaps else "&mdash;",
          html.escape(song[:22]) or "Longest gap", "hot")),
        # No `data`: the card is a small copy of the masthead, and the masthead
        # sets its date in the display face. A shared link should look like the
        # page it opens.
        size=104)


def _card_size(title):
    """Three steps rather than a cliff, so titles do not lurch between sizes."""
    n = len(title)
    return 104 if n <= 15 else 84 if n <= 26 else 68


def song_card(doc, counting=None):
    """A song: how often, how long between, and its best version.

    Every figure here comes from `countable_gaps`, the same call the song page
    makes, because this card is the picture of that page and the two used to
    be worked out separately -- see that function for what they disagreed on.
    """
    countable, debut, gaps = countable_gaps(doc, counting)
    best = (doc.get("best") or [None])[0]
    # Newest first, so the span runs from the last row to the first.
    span = ("%s &ndash; %s" % (countable[-1]["date"][:4], countable[0]["date"][:4])
            if countable else "")
    title = html.escape(typographic(doc["song"]))
    # The same threshold the page uses, so a shared link and the page it opens
    # tell the same story. This card is the picture of that page: when the page
    # stopped printing three "n/a"s the card had to stop too, or the preview
    # would advertise a page that no longer exists. 143 of them read
    # "1 / N/A / N/A" -- three slots, one fact.
    if len(countable) <= SPARSE_HISTORY:
        stats = [(debut or "&mdash;", "Debuted", "")]
        if gaps:
            stats.append(((_stat(gaps[0]) if len(gaps) == 1 else _stat(max(gaps))),
                          "Shows between" if len(gaps) == 1 else "Longest gap",
                          "hot"))
        # A one-year span is not a span, it is the same year printed twice --
        # and where the song was played is a fact the card had nowhere else to
        # put. The show cards already read "VENUE, CITY, ST" on this line.
        if len(countable) == 1:
            p = countable[0]
            where = ", ".join(x for x in (p["venue"], p["city"], p["state"]) if x)
            span = html.escape(where.upper()) or span
        return card_markup("Every performance", title, span, tuple(stats),
                           size=_card_size(doc["song"]), data=True)
    return card_markup(
        "Every performance", title, span,
        (("%d" % len(countable), "Times played", ""),
         (_stat(_median(gaps)) if gaps else "n/a", "Median gap", ""),
         # The third slot is the best version's score where there is one and
         # the longest gap where there is not. The label already said so; the
         # value was an em-dash either way, which is how a card could sit under
         # the words LONGEST GAP for 340 songs and never print one.
         (("%s" % best["score"]) if best else
          (_stat(max(gaps)) if gaps else "n/a"),
          "Best version" if best else "Longest gap", "hot")),
        size=_card_size(doc["song"]), data=True)


def index_card(reports):
    entries = [summarize(r) for r in reports]
    longest = max((e["longest"] or 0) for e in entries) if entries else 0
    return card_markup(
        # "How long since they last played it" described a gap calculator. The
        # site stopped being one a while ago; the gap is the spine of an
        # archive rather than the whole of it, and the card was the last place
        # still saying otherwise.
        "Phish", "Possum <em>Logic</em>", "An archive of every performance",
        (("%d" % len(entries), "Shows", ""),
         ("{:,}".format(sum(e["songs"] for e in entries)), "Songs logged", ""),
         (_stat(longest) if longest else "&mdash;", "Longest gap", "hot")))


def songs_card(docs, counting=None):
    # The same three figures the page's hero now carries, counted the same way
    # -- see render_songs for both, on why the top fouldomain score is not one
    # of them and why the uncounted performances go before the first row does.
    # It was worse here than on the page: the card had room for the number and
    # not for the song, so it published a bare 97 under "Best rated version"
    # with nothing anywhere to say whose.
    def shows(d):
        return [p for p in d["performances"]
                if not counting or p["date"] in counting]
    total = sum(len(shows(d)) for d in docs)
    longest = max((p["gap"] for d in docs for p in shows(d)[1:]
                   if p["gap"] is not None), default=None)
    return card_markup(
        "Every song", "Possum <em>Logic</em>", "One page per song, all the way back",
        (("%d" % len(docs), "Songs", ""),
         ("{:,}".format(total), "Song performances", ""),
         (_stat(longest) if longest is not None else "&mdash;",
          "Longest gap", "hot")))


# The six pages that had no card of their own. Every one of them fell back to
# a hand-made og.png committed once in July 2026 and never regenerated: it said
# "Gap Reports" in a face this site does not use and claimed 169 songs against
# the 589 it now has. A fallback that cannot be rebuilt from the data is a
# figure with no source, and it was the last one on the site -- see docs/TODO
# 8k. These are drawn by the same pipeline as the other 1,304, so they cannot
# go stale without the index noticing.
#
# Each takes what its page takes and recomputes from it, the way due_card and
# songs_card already do, rather than having the render function hand its
# workings back. The labels come from the same constants the page headings do,
# so a card cannot name a section the page calls something else.

def venues_card(reports):
    by_venue = {}
    for e in (summarize(r) for r in reports):
        if e["venue"]:
            by_venue.setdefault(e["venue"], []).append(e)
    most = max((len(v) for v in by_venue.values()), default=0)
    return card_markup(
        "Every venue", "Possum <em>Logic</em>", "Where the shows happened",
        (("{:,}".format(len(by_venue)), "Venues", ""),
         ("{:,}".format(sum(len(v) for v in by_venue.values())), "Shows", ""),
         ("%d" % most, "Most at one room", "hot")))


def rotation_card(docs, counting, since):
    parts = rotation_split(due_rows(docs, counting, since)[3])
    return card_markup(
        "Out of rotation", "Possum <em>Logic</em>",
        "What the band has stopped playing",
        tuple(("%d" % len(rows), ROTATION_SECTIONS[i][1],
               "hot" if i == 0 else "")
              for i, rows in enumerate(parts)))


def not_a_show_card(reports, docs, calendar):
    counting = set(calendar)
    _, aside = split_archive(reports, calendar)
    return card_markup(
        "Not a show", "Possum <em>Logic</em>",
        "Soundchecks, sessions, and the rest",
        (("%d" % len(aside), "Entries", ""),
         ("%d" % len(never_at_a_show(docs, counting)), "Never at a show", ""),
         ("%d" % len(rated_off_stage(docs, counting)), "Rated versions",
          "hot")))


def years_card(profiles):
    busiest = max(profiles, key=lambda p: p["shows"]) if profiles else None
    return card_markup(
        "Every year", "Possum <em>Logic</em>", "What each year sounded like",
        (("%d" % len(profiles), "Years", ""),
         ("{:,}".format(sum(p["shows"] for p in profiles)), "Shows", ""),
         (("%s" % busiest["year"]) if busiest else "&mdash;", "Busiest year",
          "hot")))


def explainer_card(kind, subtitle, reports):
    """method and faq: pages about the archive rather than views of it.

    They carry the archive's own three figures rather than invented ones. The
    alternative was a card with no numbers on a template built around three,
    and the alternative to that was making some up.
    """
    entries = [summarize(r) for r in reports]
    longest = max((e["longest"] or 0) for e in entries) if entries else 0
    return card_markup(
        kind, "Possum <em>Logic</em>", subtitle,
        (("%d" % len(entries), "Shows", ""),
         ("{:,}".format(sum(e["songs"] for e in entries)), "Songs logged", ""),
         (_stat(longest) if longest else "&mdash;", "Longest gap", "hot")))


# ------------------------------------------------------------------- site ---

SHOW_DIR = "show"

# The same move the pages made, made for the archive. 711 dated files lay flat
# in data/ beside the five index files -- calendar, cards, current, phishin,
# schedule -- and one directory that already did it properly, songs/. Which of
# those is a report was a question about the shape of a filename rather than
# about where the file lived, and REPORT_NAME below exists only because of it.
SHOW_DATA_DIR = os.path.join("data", "shows")


def show_data_dir(site_dir):
    return os.path.join(site_dir, SHOW_DATA_DIR)


def site_paths(site_dir, date):
    # Reports live in their own directory rather than the site root. At
    # fourteen of them the root was tidy enough; at 259 it was the whole site,
    # and any future top-level page would have had to pick a name no show could
    # ever be called.
    return (os.path.join(site_dir, SHOW_DIR, "%s.html" % date),
            os.path.join(show_data_dir(site_dir), "%s.json" % date))


# A report is named for its date and nothing else is. data/ also holds indexes
# -- current.json, calendar.json, cards.json -- and globbing every .json in
# there read one as a show whose date key was missing, which is a KeyError at
# build time rather than anything as polite as a skip.
#
# Kept after the move to data/shows/, where nothing else lives and it therefore
# guards nothing. It is what migrate_show_data() recognizes a stray report by,
# and a directory that holds one kind of file is worth asserting rather than
# assuming.
REPORT_NAME = re.compile(r"^\d{4}-\d{2}-\d{2}\.json$")


def migrate_show_data(site_dir):
    """Move any reports still lying flat in data/ into data/shows/.

    One pass; after the first build there is nothing left for it to find. It
    exists rather than a bare `git mv` because a checkout made before the move
    would otherwise build a site with every show missing -- and this file has
    published a site missing its shows three times already under other names,
    every time cheerfully and without an error. Moves rather than copies, so
    there is never a second copy of a report to disagree with the first.
    """
    flat = os.path.join(site_dir, "data")
    if not os.path.isdir(flat):
        return 0
    names = sorted(n for n in os.listdir(flat) if REPORT_NAME.match(n))
    if not names:
        return 0
    into = show_data_dir(site_dir)
    os.makedirs(into, exist_ok=True)
    for name in names:
        os.replace(os.path.join(flat, name), os.path.join(into, name))
    log("moved %d report%s from data/ into %s",
        len(names), "" if len(names) == 1 else "s", SHOW_DATA_DIR)
    return len(names)


# The only two report URLs that were ever shared before reports moved into
# show/. Everything else on the site is linked, not remembered, so it follows
# the move for free; these two are out in a chat somewhere and cannot.
MOVED = ("2026-07-24", "2026-07-25")

#: Pages that changed filename, and what they became. Same argument as MOVED
#: and a stronger one: this URL is in the published sitemap, so it is not only
#: possibly remembered, it has been handed to crawlers as a page that exists.
#: See ROTATION_PAGE for why it moved.
MOVED_PAGES = {"dormant.html": (ROTATION_PAGE, "Out of rotation")}

REDIRECT = """<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta http-equiv="refresh" content="0; url=./{href}">
<link rel="canonical" href="{site}/{href}">
<title>{title} &mdash; Possum Logic</title>
<style>body{{font-family:ui-monospace,monospace;margin:4rem auto;max-width:32rem;
padding:0 1rem;line-height:1.6}}a{{color:#c8371b}}</style></head>
<body><p>{what} has moved to <a href="./{href}">{href}</a>.</p></body></html>
"""


#: How strong the paper texture is, as the standard deviation of CIE L* across
#: the tile once it is blended onto the paper. A perceptual target rather than
#: a pixel range, because the same pixel range is not the same texture on cream
#: as on near-black: `soft-light` perturbs a mid backdrop far more than an
#: extreme one, so the tile that had been specified for both read four times
#: stronger in the dark palette. Each palette solves for its own spread below.
#: 0.80 is "felt rather than seen" -- the dark palette shipped at 1.31 and the
#: light at 0.30, and this sits between them.
GRAIN_TARGET_DL = 0.80


def _grain_spread(paper, target=GRAIN_TARGET_DL):
    """The +/- band around mid-grey that hits `target` on this paper. """
    def lstar(v):
        v = max(0.0, min(255.0, v)) / 255
        y = v / 12.92 if v <= .03928 else ((v + .055) / 1.055) ** 2.4
        return 116 * (y ** (1 / 3)) - 16 if y > 0.008856 else 903.3 * y

    def soft(cb, cs):
        # The CSS/PDF soft-light. It is the identity at cs = 0.5, which is the
        # whole reason the tile is centred on mid-grey: the paper's mean comes
        # out exactly where it went in, whatever the spread.
        if cs <= 0.5:
            return cb - (1 - 2 * cs) * cb * (1 - cb)
        d = ((16 * cb - 12) * cb + 4) * cb if cb <= 0.25 else math.sqrt(cb)
        return cb + (2 * cs - 1) * (d - cb)

    def sd(spread):
        vals = [lstar(soft(paper / 255, g / 255) * 255)
                for g in range(128 - spread, 128 + spread + 1)]
        mean = sum(vals) / len(vals)
        return (sum((v - mean) ** 2 for v in vals) / len(vals)) ** .5

    lo, hi = 1, 120
    while lo < hi:
        mid = (lo + hi) // 2
        if sd(mid) < target:
            lo = mid + 1
        else:
            hi = mid
    return lo


def write_grain(site_dir, size=140):
    """The paper texture: one tile per palette, beside the site sheet.

    Two things about this were wrong for its whole life, and neither was
    visible, because it never painted at all -- BODY_BOX_CSS set the
    `background` shorthand one link later and that resets `background-image`.

    The blend was `multiply` on cream and `screen` on near-black. Against a
    mid-grey tile neither of those is a texture: multiply took the light paper
    from #f2ece0 to a measured #dad5ca, 20.8% of its luminance, and screen took
    the dark paper up 216%. `soft-light` is the identity at mid-grey, so the
    paper's mean survives exactly and the tile only perturbs around it.

    And one tile cannot serve both palettes, because soft-light's swing depends
    on how far the backdrop is from the extremes: the same +/-20 band measured
    sd(L*) 0.30 on cream and 1.31 on near-black, four times the texture in the
    dark. Each palette gets a tile solved for GRAIN_TARGET_DL instead.

    Deterministic, so a rebuild does not produce new files and republish them.
    """
    try:
        from PIL import Image
    except ImportError:
        return None
    out = []
    for name, palette in (("light", LIGHT), ("dark", DARK)):
        paper = int(palette["paper"].lstrip("#")[:2], 16)
        spread = _grain_spread(paper)
        path = os.path.join(site_dir, STATIC_DIR, "grain-%s.png" % name)
        # write_if_changed makes its own directory; this one saves through PIL.
        os.makedirs(os.path.dirname(path), exist_ok=True)
        rnd = random.Random(20260727)      # fixed: the tile must not change
        img = Image.new("L", (size, size))
        img.putdata([rnd.randint(128 - spread, 128 + spread)
                     for _ in range(size * size)])
        # Opaque. The alpha used to do the dimming that soft-light now does
        # properly, and a translucent tile would only dilute the texture back
        # towards the flat paper it is meant to relieve.
        scratch = path + ".tmp"
        img.convert("RGB").save(scratch, "PNG", optimize=True)
        with open(scratch, "rb") as fh:
            blob = fh.read()
        os.remove(scratch)
        if not (os.path.isfile(path) and open(path, "rb").read() == blob):
            with open(path, "wb") as fh:
                fh.write(blob)
            log("wrote %s (%d bytes, spread +-%d)", path, len(blob), spread)
        out.append(path)
    return out


def write_redirects(site_dir):
    """Leave a forwarding note wherever an old link used to point."""
    for date in MOVED:
        if not os.path.isfile(site_paths(site_dir, date)[1]):
            continue
        write_if_changed(
            os.path.join(site_dir, "%s.html" % date),
            REDIRECT.format(href="%s/%s.html" % (SHOW_DIR, date),
                            site=SITE_URL, title=date, what="This report"))
    # Only once the destination is on disk. A forwarding page written ahead of
    # the page it forwards to would replace a working document with a bounce
    # to a 404 -- and this one overwrites the old build's real dormant.html, so
    # there would be nothing left to fall back to.
    for old, (new, title) in MOVED_PAGES.items():
        if not os.path.isfile(os.path.join(site_dir, new)):
            continue
        write_if_changed(
            os.path.join(site_dir, old),
            REDIRECT.format(href=new, site=SITE_URL, title=title,
                            what="This page"))


def write_sitemap(site_dir):
    """Every page this site actually serves, listed once.

    Walked off the built directory rather than assembled from what the build
    thinks it wrote. Those are different claims, and the one worth publishing is
    "here is what is there" -- a sitemap generated from intent is the same shape
    as every other record in this file that outlived the work it recorded.

    **No `<lastmod>`, deliberately.** The honest value is when the page's content
    last changed, and nothing here knows that: CI checks the repository out
    fresh, so every file's mtime is the build time, and stamping 1,300 pages
    with "changed just now" on every run is worse than saying nothing -- it is
    the kind of confidently wrong figure this archive exists not to publish. The
    show date would be wrong for a different reason: a 2009 page changes
    whenever the archive behind it does. `<changefreq>` and `<priority>` are
    omitted for the simpler reason that Google has said for years it ignores
    them.

    The forwarding pages left where old shared links used to point are
    excluded: a redirect is not a page, and listing one asks a crawler to index
    a document whose only content is a meta refresh. dormant.html has to be
    taken out by name as well as written by name -- it was in the last sitemap
    as a real page, so leaving it in would be this file publishing a claim it
    had just stopped being true.
    """
    moved = {"%s.html" % d for d in MOVED} | set(MOVED_PAGES)
    pages = []
    for root, dirs, files in os.walk(site_dir):
        dirs[:] = [d for d in dirs if d not in ("data", "card", "font")]
        for name in files:
            if not name.endswith(".html"):
                continue
            rel = os.path.relpath(os.path.join(root, name), site_dir)
            if rel in moved:
                continue
            pages.append(rel.replace(os.sep, "/"))
    # index.html serves the front page, and a crawler should be told about the
    # directory rather than the file -- otherwise the same page is two URLs.
    locs = sorted("%s/%s" % (SITE_URL, "" if p == "index.html" else p)
                  for p in pages)
    body = "".join("<url><loc>%s</loc></url>" % html.escape(u, quote=False)
                   for u in locs)
    write_if_changed(
        os.path.join(site_dir, "sitemap.xml"),
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">'
        + body + "</urlset>\n")
    write_if_changed(
        os.path.join(site_dir, "robots.txt"),
        "User-agent: *\nAllow: /\nSitemap: %s/sitemap.xml\n" % SITE_URL)
    return len(locs)


def archived_dates(site_dir):
    data_dir = show_data_dir(site_dir)
    if not os.path.isdir(data_dir):
        return set()
    return {n[:-5] for n in os.listdir(data_dir) if REPORT_NAME.match(n)}


_UNREADABLE = []


def saved_reports(site_dir):
    """Every report JSON already in the site, oldest first."""
    data_dir = show_data_dir(site_dir)
    out = []
    for name in sorted(os.listdir(data_dir) if os.path.isdir(data_dir) else []):
        if not REPORT_NAME.match(name):
            continue
        with open(os.path.join(data_dir, name), encoding="utf-8") as fh:
            try:
                out.append(json.load(fh))
            except ValueError:
                # Loud, and counted, because an unreadable report is a show
                # missing from the site and the build will otherwise publish
                # cheerfully without it.
                log("warning: skipping unreadable %s", name)
                _UNREADABLE.append(name)
    return out


def archived(site_dir, date):
    """The report already on disk for `date`, or None."""
    _, blob = site_paths(site_dir, date)
    if not os.path.isfile(blob):
        return None
    with open(blob, encoding="utf-8") as fh:
        try:
            return json.load(fh)
        except ValueError:
            return None


# What a song page needs off each performance row. The full payload carries
# setlist notes, jamchart prose, tour ids and permalinks besides, several times
# the weight, and all of it either reconstructible or already in the show's own
# report. Trimmed, the archive's 165 songs come to 3.4 MB; untrimmed they would
# not be worth the disk.
def counts_toward(counting, date):
    """Whether a performance on `date` is at a show that counts toward a gap.

    The calendar, or a date newer than the whole calendar: fetch_calendar holds
    back today's UTC date so a show is never *counted* before it is played, and
    for the hour or two before 00:00 UTC that leaves the show being played
    tonight off it. A performance on that date is the proof it happened.
    """
    return date in counting or (bool(counting) and date > max(counting))


def true_gaps(rows, counting, key="showdate"):
    """`rows`, oldest first, with each gap counted off the calendar. -> copies.

    A gap is the number of counting shows strictly between a performance and
    the one before it: 0 for back-to-back nights. That is what the FAQ has
    always said it was. It was not what was printed. The figure came from
    phish.net, and measured against the calendar on 2026-10-03, phish.net's gap
    was one higher than that on 28,206 of 36,466 performance pairs, equal on
    7,562, and higher still on 683 -- and at some point after 2026-09-07 it
    renumbered rows it had already published, so Tweezer's 2026-09-05 went
    from 1 to 2 with no new API version. It also files 0 for any song entered
    during a show and leaves it there for hours. None of that is a gap.

    So phish.net's number is kept on disk and never displayed. A performance at
    an event that does not count gets None, and so does the first counting
    performance, which has nothing before it to be absent from.
    """
    cal = _sorted_calendar(counting)
    out, prev = [], None
    for row in rows:
        row = dict(row)
        date = row[key]
        if not counts_toward(counting, date):
            row["gap"] = None
            out.append(row)
            continue
        row["gap"] = (None if prev is None else
                      bisect.bisect_left(cal, date) - bisect.bisect_right(cal, prev))
        prev = date
        out.append(row)
    return out


_CALENDAR_SORTED = {}


def _sorted_calendar(counting):
    # true_gaps runs once per song per report, and a remeasure is 40,000 of
    # them over the same set.
    k = (len(counting), max(counting) if counting else "")
    if k not in _CALENDAR_SORTED:
        _CALENDAR_SORTED.clear()
        _CALENDAR_SORTED[k] = sorted(counting)
    return _CALENDAR_SORTED[k]


def _gap(row):
    """The gap on this row as an int, or None. 0 is a real gap.

    With a calendar to hand every gap is replaced by true_gaps before anyone
    reads it, so this only ever sees phish.net's raw figure on the one path
    without a site: a bare single-show report.
    """
    gap = row.get("gap")
    if not str(gap).lstrip("-").isdigit():
        return None
    return int(gap) if int(gap) >= 0 else None


def by_show(rows):
    """One row per show, out of a history that has one row per setlist slot.

    A song can come round more than once in a night -- Hold Your Head Up
    bookends the Fishman song, Tweezer came back twice at SNHU Arena in 2025 --
    and phish.net records each appearance. That is 717 of the archive's 28,519
    rows, across 79 of its 165 songs, and a page listing performances rather
    than setlist slots wants them collapsed: three rows reading 2025-06-22,
    2025-06-22, 2025-06-22 look like a bug even when they are the truth.

    The night's gap is the largest of them. Only the standalone performance has
    a gap to speak of -- the repeats sit at 0, having missed no shows since the
    one an hour earlier -- and taking the maximum finds it wherever it sits.
    phish.net is not consistent about that: on 2025-06-22 Tweezer's 5 is on the
    third of the three rows, and on 2025-09-19 it is on the first.

    Everything else comes off the first appearance, which is the one the set
    and position describe. `times` records how many there were, and is left off
    the ordinary single-performance night.

    Copies rather than the rows themselves: add_previous goes on to measure the
    song's gap distribution off the same list, and a collapse it did not ask
    for should not reach it from here.
    """
    out, seen = [], {}
    for row in rows:
        date = row.get("showdate")
        first = seen.get(date)
        if first is None:
            first = seen[date] = dict(row)
            out.append(first)
            continue
        first["_times"] = first.get("_times", 1) + 1
        if (_gap(row) or 0) > (_gap(first) or 0):
            first["gap"] = row.get("gap")
        # The annotated version of the night is not always the first one out of
        # the gate, so the flag and the note come off whichever appearance
        # earned them rather than off whichever came first.
        if str(row.get("isjamchart")) == "1":
            first["isjamchart"] = "1"
        for field in ("jamchart_description", "footnote"):
            if not (first.get(field) or "").strip():
                first[field] = row.get(field)
    return out


def _performance(row):
    out = {
        "date": row.get("showdate"),
        "venue": row.get("venue") or "",
        "city": row.get("city") or "",
        "state": row.get("state") or "",
        "gap": _gap(row),
        "set": str(row.get("set") or ""),
    }
    if row.get("_times"):
        out["times"] = row["_times"]
    # phish.net's own note on why this version is worth hearing, which is the
    # closest thing the API has to a rating: there is no per-performance score
    # anywhere in v5 -- reviews attach to shows, not to songs within them.
    # 15.7% of performances are jamcharted and every one of them carries prose,
    # median 178 characters. Kept verbatim, entities and all; the renderer
    # unescapes and re-escapes rather than trusting it as markup.
    if str(row.get("isjamchart")) == "1":
        out["jamchart"] = True
    jam = (row.get("jamchart_description") or "").strip()
    if jam:
        out["jam"] = jam
    # phish.net's footnote on the performance itself -- "Unfinished.", "Lyrics
    # altered to reference a hot tub." Terser and more factual than the jamchart
    # prose, on 8.6% of performances, and riding along in the same response.
    note = (row.get("footnote") or "").strip()
    if note:
        out["note"] = note
    # How the song left: 9,373 performances go out on a ">" and 1,513 on a true
    # "->". Stored now because it costs nothing; what it segued *into* needs the
    # whole setlist and does not.
    mark = (row.get("trans_mark") or "").strip()
    if mark and mark != ",":
        out["out"] = mark
    return out


def best_versions(song, **kw):
    """fouldomain's top-rated versions of one song, best first.

    Matched on the song's title, not its slug: `song=you-enjoy-myself` comes
    back empty where `song=You Enjoy Myself` returns ten. How many come back
    varies by song -- 25 for Tweezer, 10 for You Enjoy Myself -- so this takes
    what it is given rather than promising a count.

    A version only has a score once a recording of it circulates, because
    nearly half the weighting is audio analysis. That makes this a poor thing
    to block a report on, so every caller treats failure as "no scores yet".
    """
    # Ten come back unasked; the endpoint caps at 25 however much more you ask
    # for, and 25 marks on a 654-row page is still only the notable 4%.
    tracks = (foul("best-versions", song=song, limit=BEST_LIMIT,
                   **kw) or {}).get("tracks") or []
    out, seen = [], set()
    for t in tracks:
        date = t.get("date")
        # The same night can appear twice when the song was played twice; the
        # page has one row per show to hang these on, so the better score wins.
        if not date or t.get("score") is None:
            continue
        if date in seen:
            continue
        seen.add(date)
        out.append({"date": date, "score": t.get("score"),
                    "venue": t.get("venue") or "", "city": t.get("city") or "",
                    "state": t.get("state") or "", "link": t.get("link") or ""})
    out.sort(key=lambda v: (-v["score"], v["date"]))
    return out


def add_ratings(report, **kw):
    """Attach the show's ratings, or leave the report exactly as it was.

    One call, and a failed or empty one costs nothing: a show played last night
    has no rating yet either way, so the page simply does not carry the line.
    """
    try:
        report.update(show_ratings(report["date"], **kw))
    except ApiError as exc:
        log("warning: no ratings for %s: %s", report["date"], exc)
    return report


def show_ratings(date, **kw):
    """phish.net's rating for a show, and fouldomain's own score for it.

    phish.net's rating is theirs; we are taking it second-hand because their
    API does not offer it. Attributed as such wherever it is shown.
    """
    data = foul("show", date=date, **kw) or {}
    out = {}
    if data.get("pnetRating") is not None:
        out["pnet_rating"] = data["pnetRating"]
    if data.get("showScore") is not None:
        out["foul_score"] = data["showScore"]
    return out


PHISHIN = ("data", "phishin.json")


def phishin_dates(site_dir):
    """Show dates phish.in holds audio for, from disk. Empty if never fetched."""
    path = os.path.join(site_dir, *PHISHIN)
    if not os.path.isfile(path):
        return set()
    try:
        with open(path, encoding="utf-8") as fh:
            return set(json.load(fh).get("dates") or [])
    except ValueError:
        log("warning: unreadable %s", path)
        return set()


def fetch_phishin(site_dir, **kw):
    """Refresh the list of shows phish.in has. -> the set of dates.

    Three calls at a thousand a page for the whole catalog, which is cheaper
    than asking about one show and far cheaper than being wrong: a link to
    phish.in for a show they do not have is a 404, and the show most likely to
    be missing is the one being played tonight, which is exactly the page most
    likely to be shared.
    """
    dates, page = set(), 1
    while True:
        got = foulless_json(
            "https://phish.in/api/v2/shows?per_page=1000&page=%d" % page, **kw)
        if not got:
            break
        dates |= {s["date"] for s in got.get("shows") or [] if s.get("date")}
        if page >= (got.get("total_pages") or 1):
            break
        page += 1
    if not dates:
        return phishin_dates(site_dir)
    path = os.path.join(site_dir, *PHISHIN)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    write_if_changed(path, json.dumps({"dates": sorted(dates)},
                                      separators=(",", ":")) + "\n")
    log("phish.in has audio for %d shows", len(dates))
    return dates


def foulless_json(url, cache_dir=DEFAULT_CACHE, refresh=False, **_):
    """One JSON GET with no API key, uncached. -> parsed body, or None."""
    req = urllib.request.Request(
        url, headers={"User-Agent": "possumlogic/1.0 (+personal use)",
                      "Accept": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=30) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except Exception as exc:                                   # noqa: BLE001
        log("phish.in: %s", exc)
        return None


def write_if_changed(path, text):
    """Write only when the bytes differ. -> True if it wrote.

    There are one of these pages per song rather than per show, and a rebuild
    renders all of them. Writing every time meant a template edit -- or a run
    that changed nothing at all -- pushed the whole set to gh-pages again as
    new blobs. Nothing downstream can tell an unchanged rewrite from a real
    one, so the cheapest place to notice is here.
    """
    if os.path.isfile(path):
        with open(path, encoding="utf-8") as fh:
            if fh.read() == text:
                return False
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)
    return True


def song_path(site_dir, slug):
    return os.path.join(site_dir, "data", "songs", "%s.json" % slug)


def archived_songs(site_dir):
    """Slugs whose history the site already holds."""
    songs_dir = os.path.join(site_dir, "data", "songs")
    if not os.path.isdir(songs_dir):
        return set()
    return {n[:-5] for n in os.listdir(songs_dir) if n.endswith(".json")}


def save_song_history(site_dir, slug, song, rows, artist=None, best=None):
    """Archive one song's complete performance history, oldest first.

    Oldest first because that is the order the gaps were earned in, and
    because a show being added then appends at the end of the file instead of
    shifting every line in it -- this archive lives in git and is rewritten
    once per song per show.

    One performance per line for the same reason. json.dump(indent=2) spends
    107 KB on You Enjoy Myself's 654 performances where this spends 78 KB, and
    turns a one-show diff into six changed lines rather than one.
    """
    path = song_path(site_dir, slug)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    # No fetched-at stamp: it would rewrite every file on every run whether or
    # not the history moved, and the last row already says when it last moved.
    # Scores are fetched separately and can fail on their own, so a history
    # rewritten while fouldomain is down keeps the ones it already had rather
    # than dropping them and waiting for the next seed.
    held = song_history(site_dir, slug) or {}
    if best is None:
        best = held.get("best") or []
    # Neighbors cost a call per show to work out and are not in this response,
    # so a history rewritten from the API carries forward the ones it had
    # rather than making the twenty-minute backfill run again.
    keep = {p["date"]: {k: p[k] for k in NB_CARRY if k in p}
            for p in held.get("performances") or []}
    perfs = [_performance(r) for r in by_show(rows)]
    for p in perfs:
        p.update(keep.get(p["date"]) or {})
    return write_song_file(site_dir, slug,
                           {"song": song, "slug": slug, "artist": artist or ""},
                           perfs, best)


def write_song_file(site_dir, slug, head, perfs, best):
    """The archive file itself, given rows already in their stored shape."""
    path = song_path(site_dir, slug)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    lines = lambda rows: ",\n".join(
        "  " + json.dumps(r, separators=(", ", ": ")) for r in rows)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("{\n%s,\n \"best\": [\n%s\n ],\n \"performances\": [\n%s\n ]\n}\n"
                 % (",\n".join(" %s: %s" % (json.dumps(k), json.dumps(v))
                               for k, v in head.items()),
                    lines(best), lines(perfs)))
    return path


def song_history(site_dir, slug):
    """The archived history for `slug`, or None."""
    path = song_path(site_dir, slug)
    if not os.path.isfile(path):
        return None
    with open(path, encoding="utf-8") as fh:
        try:
            doc = json.load(fh)
        except ValueError:
            log("warning: skipping unreadable %s", path)
            return None
    # Every reader takes a gap off a performance by subscript, so this is the
    # one place to put them on the calendar -- see true_gaps. The file keeps
    # phish.net's figure; nothing reads it.
    counting = set(load_calendar(site_dir))
    if counting:
        doc["performances"] = true_gaps(doc.get("performances") or [],
                                        counting, key="date")
    return doc


# --------------------------------------------------------------- schedule ---

# phish.net lists announced dates alongside played ones, so the schedule comes
# from a call the calendar already makes. What it does not carry is a start
# time -- there is no time field of any kind -- so knowing *when* to look still
# needs a local clock, and a local clock needs the venue's zone.
#
# Not derived from coordinates. Zone boundaries follow county lines rather than
# meridians, so deriving them means either a geo API with a quota or a shapefile
# dependency, to answer a question with 157 distinct venues and three countries
# in it. A checked table is smaller than the code that would avoid it, costs no
# network, and is wrong only where a diff can show it.
TZ_BY_STATE = {
    # Eastern
    "CT": "America/New_York", "DC": "America/New_York", "DE": "America/New_York",
    "GA": "America/New_York", "MA": "America/New_York", "MD": "America/New_York",
    "ME": "America/New_York", "NC": "America/New_York", "NH": "America/New_York",
    "NJ": "America/New_York", "NY": "America/New_York", "OH": "America/New_York",
    "PA": "America/New_York", "RI": "America/New_York", "SC": "America/New_York",
    "VA": "America/New_York", "VT": "America/New_York", "WV": "America/New_York",
    # Central
    "AL": "America/Chicago", "AR": "America/Chicago", "IA": "America/Chicago",
    "IL": "America/Chicago", "LA": "America/Chicago", "MN": "America/Chicago",
    "MO": "America/Chicago", "MS": "America/Chicago", "OK": "America/Chicago",
    "WI": "America/Chicago",
    # Mountain and Pacific
    "CO": "America/Denver", "MT": "America/Denver", "NM": "America/Denver",
    "UT": "America/Denver", "WY": "America/Denver",
    "CA": "America/Los_Angeles", "NV": "America/Los_Angeles",
    "WA": "America/Los_Angeles",
    # Outside the US, by province rather than state
    "Quintana Roo": "America/Cancun", "Ontario": "America/Toronto",
}

# The eight states Phish plays that span two zones. Every venue in them
# resolves by city, and Tennessee is the only one where it genuinely decides
# anything -- Knoxville is Eastern, Nashville and Manchester are Central.
TZ_BY_CITY = {
    ("AZ", "Phoenix"): "America/Phoenix",          # no DST, so not Denver
    ("FL", "Jacksonville"): "America/New_York",
    ("FL", "Miami"): "America/New_York",
    ("IN", "Noblesville"): "America/Indiana/Indianapolis",
    ("KY", "Louisville"): "America/New_York",
    ("MI", "Clarkston"): "America/Detroit",
    ("MI", "Detroit"): "America/Detroit",
    ("MI", "Grand Rapids"): "America/Detroit",
    ("OR", "Bend"): "America/Los_Angeles",
    ("OR", "Eugene"): "America/Los_Angeles",
    ("OR", "Portland"): "America/Los_Angeles",
    ("TN", "Knoxville"): "America/New_York",
    ("TN", "Manchester"): "America/Chicago",
    ("TN", "Nashville"): "America/Chicago",
    ("TX", "Austin"): "America/Chicago",
    ("TX", "Del Valle"): "America/Chicago",
    ("TX", "Grand Prairie"): "America/Chicago",
}


def venue_zone(row):
    """IANA zone for a show row, or None when we cannot say.

    None is a real answer and the caller must treat it as one: a venue we have
    no zone for gets no watch window and falls back to the ordinary sweep,
    which is late but never wrong. Guessing a zone would schedule a burst of
    polling at the wrong hour and quietly miss the show.
    """
    state = (row.get("state") or "").strip()
    city = (row.get("city") or "").strip()
    return TZ_BY_CITY.get((state, city)) or TZ_BY_STATE.get(state)


# When to be watching, in the venue's own local time. Deliberately generous at
# both ends, because the two ways of being wrong do not cost the same: polling
# a few extra times on a public repo costs nothing, and being twenty minutes
# late to open costs the first set. So exceptions widen the window; none of
# them narrows it.
#
# The default opens before the earliest plausible downbeat -- setlist.fm has
# tonight's Garden show scheduled for 19:30, and shows run 19:25 to 20:10 -- and
# closes after a four-hour show plus the quiet period a setlist needs to settle.
WATCH_DEFAULT = ((19, 0), (2, 30))

# Mexico is the standing exception and the reason the window is a table rather
# than a constant. The run does not keep one start time: the first night runs
# late for people still arriving, the middle nights are ordinary but early, and
# the last night is early again for people flying out. Rather than encode which
# night is which -- and be wrong the year they reorder it -- the window spans
# all of them.
WATCH_RULES = (
    (lambda s: s.get("tz") == "America/Cancun", ((17, 0), (3, 30))),
)

SCHEDULE = ("data", "schedule.json")

# phish.net logs unnamed improvisation under the title "Jam", which makes it
# the 125th most played "song" in the catalog with 93 performances. It is not
# a composition, so every figure on its page answers a different question than
# the same figure does anywhere else: its median gap is how often the band
# improvises without naming what came out, not how often they play a song.
# Left unsaid, the page reads as a straightforwardly popular tune.
#
# Only entries that are genuinely not songs. Big Ball Jam is a song, Woodlands
# Jam is a named one-off, and neither belongs here.
NOT_A_SONG = {
    "jam": "phish.net files unnamed improvisation under this title, so this is "
           "not one composition but every jam the band never named. The figures "
           "below are real counts, but they describe how often that happens "
           "rather than how often a particular song is played.",
    # Found by the dormant page, which put it top of its LONGEST GONE card --
    # the loudest figure on a new page, attached to a thing that is not a song.
    # Nine performances, nine different titles in the notes, every gap zero:
    # Me and Bobby McGee, We've Only Just Begun, Magilla, Mountain Dew, Goodbye
    # Jam, Down Home Dirty Blues, What's The Use?, Dog Log, and a Devil With a
    # Blue Dress On jam. Structurally the same entry as "jam" above, and it had
    # simply never been noticed, because nothing had ever ranked it first.
    "custom": "phish.net files one-off and unlisted titles under this entry, so "
              "the performances below are nine different pieces of music rather "
              "than nine of one. Every count on this page is real and none of "
              "them is about a single song.",
}


def watch_window(show):
    """(open, close) in UTC for one scheduled show, or None without a zone.

    The close is on the following day whenever it falls after midnight, which
    for a show starting at seven in the evening it always does.
    """
    if not show.get("tz"):
        return None
    try:
        zone = zoneinfo.ZoneInfo(show["tz"])
    except Exception:                                          # noqa: BLE001
        return None
    (oh, om), (ch, cm) = WATCH_DEFAULT
    for matches, window in WATCH_RULES:
        if matches(show):
            (oh, om), (ch, cm) = window
            break
    try:
        day = datetime.date.fromisoformat(show["date"])
    except ValueError:
        return None
    start = datetime.datetime.combine(
        day, datetime.time(oh, om), tzinfo=zone)
    end = datetime.datetime.combine(
        day + datetime.timedelta(days=1), datetime.time(ch, cm), tzinfo=zone)
    return start.astimezone(datetime.timezone.utc), \
        end.astimezone(datetime.timezone.utc)


def next_show(site_dir, now=None):
    """The soonest scheduled show still ahead of `now`, or None.

    Only for the log: a run that did nothing is much easier to trust when it
    says what it is waiting for.
    """
    now = (now or _utcnow()).date().isoformat()
    path = os.path.join(site_dir, *SCHEDULE)
    if not os.path.isfile(path):
        return None
    try:
        with open(path, encoding="utf-8") as fh:
            shows = json.load(fh).get("shows") or []
    except ValueError:
        return None
    return next((s for s in shows if s.get("date", "") >= now), None)


def released(site_dir, live, quiet=None):
    """True when the watcher may stop polling every show in `live`.

    Deliberately *not* `provisional`, and this distinction is the whole point.
    `settle()` releases the page half an hour after an encore is recorded,
    because an encore is the band saying the show is over and holding the page
    at "still coming in" for two more hours is wrong for most of that time.
    That shortcut is safe for a label, which the next pass can take back. It is
    not safe for the watcher, because the watcher leaving is what stops the
    next pass happening.

    Ian, who has been to them: encores of six or seven songs exist. They are
    exceedingly rare and they run close to an hour. Songs arriving keep
    resetting `count_since`, so a long encore does not trip this on its own --
    but phish.net posting the first encore song and then straggling for over
    half an hour would, and that is ordinary. So the watcher holds for the full
    QUIET_HOURS of stillness whether or not an encore is on the record, and
    ignores the shortcut that exists for the reader's benefit.

    Costs about an hour of runner time against releasing on `provisional`, and
    still exits hours before the 7h30m window closes.

    A show with no report, or no `count_since` to measure from, is not
    released. That is the whole first hour of every night.
    """
    if not live:
        return False
    quiet = quiet or datetime.timedelta(hours=QUIET_HOURS)
    now = _utcnow()
    for s in live:
        rep = archived(site_dir, s["date"])
        if not rep:
            return False
        since = _ts(rep.get("count_since"))
        if not since or now - since < quiet:
            return False
    return True


def watching(site_dir, now=None, lead=0):
    """Scheduled shows whose watch window contains `now`. Usually empty.

    This is the whole gate: a run that finds nothing here has done no API call
    and can stop. Reading a file the repo already holds is the cheapest
    possible answer to "is anything happening", and on most days it is no.

    `lead` opens each window early, in minutes. The watcher's cron fires about
    13% of the time it is scheduled to, and the window opens only half an hour
    before the first song is usually posted -- so on the three show nights
    measured it started 6, 10 and 14 minutes late, which was luck rather than
    margin. Starting early costs runner time and buys the show's opening.
    """
    now = now or _utcnow()
    if lead:
        now = now + datetime.timedelta(minutes=lead)
    path = os.path.join(site_dir, *SCHEDULE)
    if not os.path.isfile(path):
        return []
    try:
        with open(path, encoding="utf-8") as fh:
            shows = json.load(fh).get("shows") or []
    except ValueError:
        log("warning: unreadable %s", path)
        return []
    live = []
    for s in shows:
        w = watch_window(s)
        if w and w[0] <= now <= w[1]:
            live.append(s)
    return live


def opens_in(site_dir, now=None, lead=0):
    """Whole minutes until the next watch window opens, 0 if one is open now,
    None if nothing on the schedule has a window still ahead.

    The arming question, asked hours before a show. Both crons that could
    start a watcher were measured on 2026-10-02 landing about four times a day,
    hours off their schedule -- watch.yml's show-hours cron ran at 14:06 UTC --
    and on that night neither fired between 19:47 and the second hour of the
    show. A firing that lands at all, whenever it lands, is the only reliable
    thing the scheduler offers, so whichever one does asks this and leaves a
    run waiting for the window rather than hoping one lands inside it.
    """
    now = (now or _utcnow()) + datetime.timedelta(minutes=lead)
    path = os.path.join(site_dir, *SCHEDULE)
    if not os.path.isfile(path):
        return None
    try:
        with open(path, encoding="utf-8") as fh:
            shows = json.load(fh).get("shows") or []
    except ValueError:
        return None
    ahead = []
    for s in shows:
        w = watch_window(s)
        if w and now <= w[1]:
            ahead.append(max(0, (w[0] - now).total_seconds()))
    return int(min(ahead) // 60) if ahead else None


def fetch_schedule(site_dir, apikey, artist="Phish", **kw):
    """Announced shows that have not happened yet. -> the list, soonest first.

    Rewritten whole every run rather than merged, which is what makes it
    self-correcting: the 2021 New Year's run was announced for December, then
    withdrawn, then re-announced for the following April. A merge would have
    kept believing in the December dates forever.
    """
    today = _utcnow().date()
    out = []
    # Always past the cache: an announced date that has been withdrawn is
    # exactly the thing this file exists to notice, and a cached answer cannot.
    fresh = dict(kw, refresh=True)
    for year in (today.year, today.year + 1):
        for row in get("shows/showyear/%d" % year, apikey, **fresh):
            if artist and row.get("artist_name") != artist:
                continue
            # Yesterday counts. A show is dated by its local evening, but its
            # watch window runs past midnight UTC -- a Garden show on the 27th
            # is watched until 06:30 UTC on the 28th. Dropping anything before
            # today therefore deleted the show that was on stage at the moment
            # UTC rolled over, which is the middle of every east-coast set, and
            # the watcher then could not see a show it had been following. The
            # window decides when to stop looking; this only decides what to
            # remember.
            date = row.get("showdate") or ""
            if date < (today - datetime.timedelta(days=1)).isoformat():
                continue
            out.append({"date": date,
                        "venue": row.get("venue") or "",
                        "city": row.get("city") or "",
                        "state": row.get("state") or "",
                        "country": row.get("country") or "",
                        "tz": venue_zone(row) or ""})
    out.sort(key=lambda s: (s["date"], s["venue"]))
    path = os.path.join(site_dir, *SCHEDULE)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    write_if_changed(path, json.dumps(
        {"fetched": today.isoformat(), "shows": out}, indent=1) + "\n")
    unknown = [s for s in out if not s["tz"]]
    if unknown:
        log("warning: no time zone for %d scheduled venue(s): %s",
            len(unknown), "; ".join("%s %s" % (s["date"], s["venue"]) for s in unknown[:4]))
    return out


# --------------------------------------------------------------- calendar ---

# A gap is a count of shows, so it needs the list of shows -- and that list is
# not the archive. The archive holds the reports we have written, which is a
# subset of what the band played, so counting its rows undercounts every gap
# that spans a show we never fetched.
#
# phish.net flags the shows that do not count toward statistics. Of the 289
# Phish shows it lists for 2020-2026, 39 carry exclude_from_stats: 27 are the
# canceled 2020 Summer Tour dates that became the Dinner and a Movie webcasts,
# which are replays of shows already in the record and would otherwise inflate
# every gap spanning that summer. The flag is phish.net's own judgment about
# what counts, which is a better thing to defer to than a rule of our own.
CALENDAR = ("data", "calendar.json")


def calendar_path(site_dir):
    return os.path.join(site_dir, *CALENDAR)


def load_calendar(site_dir):
    """Every show date that counts toward a gap, oldest first."""
    path = calendar_path(site_dir)
    if not os.path.isfile(path):
        return []
    # Read on every song_history call now that gaps are counted off it, so
    # cached against the file's mtime: a --calendar refresh mid-run is seen.
    stamp = (path, os.path.getmtime(path))
    if _CALENDAR_READ.get("stamp") != stamp:
        with open(path, encoding="utf-8") as fh:
            try:
                shows = json.load(fh).get("shows") or []
            except ValueError:
                log("warning: skipping unreadable %s", path)
                return []
        _CALENDAR_READ.update(stamp=stamp, shows=shows)
    return list(_CALENDAR_READ["shows"])


_CALENDAR_READ = {}


def fetch_calendar(site_dir, apikey, years, artist="Phish", **kw):
    """Refresh `years` of the show calendar. -> every counting date, sorted.

    One call per year. Only the current year needs re-asking on a normal run,
    which is why this is cheap enough to sit in the scheduled job; a full
    backfill is one call per year of the band's career and happens once.
    """
    have = set(load_calendar(site_dir))
    # showyear lists a tour that has been announced as readily as one that has
    # been played -- asking in July 2026 returns dates into September -- and a
    # show nobody has played yet cannot be a show a song has gone without.
    #
    # Strictly before today in UTC, not up to and including it. The band plays
    # in the evening in North America, which is already tomorrow in UTC, so a
    # date equal to the UTC date is a show that has either not started or not
    # finished. Cutting below it costs nothing -- a show that ended at 04:00
    # UTC is counted the moment that day ends -- and never counts a concert
    # that has not happened.
    today = _utcnow().date().isoformat()
    for year in years:
        prefix = "%d-" % year
        fresh = set()
        for row in get("shows/showyear/%d" % year, apikey, **kw):
            if artist and row.get("artist_name") != artist:
                continue
            if str(row.get("exclude_from_stats")) in ("1", "True"):
                continue
            date = row.get("showdate") or ""
            # Two shows on one date is still one date: .net's own gap figures
            # count 2021-12-31 once, and a date is what a performance carries.
            if date and date < today:
                fresh.add(date)
        # Replace the year wholesale, so a show phish.net has since withdrawn
        # or newly flagged actually leaves the calendar.
        have = {d for d in have if not d.startswith(prefix)} | fresh
    dates = sorted(have)
    path = calendar_path(site_dir)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    write_if_changed(path, "{\n \"shows\": [\n%s\n ]\n}\n"
                     % ",\n".join('  "%s"' % d for d in dates))
    return dates


def shows_since(dates, date):
    """How many counting shows the band has played since `date`."""
    return len(dates) - bisect.bisect_right(dates, date)


def write_current(site_dir, dates=None):
    """The one file that changes when a show is played.

    Every song's count moves at once -- play one song and all the others go up
    by one -- so this cannot be rendered into the pages without rewriting all
    of them every time. At 379 songs that is 48 MB pushed per show, and the
    catalog is nowhere near its full size. Here it is a single file of a few
    kilobytes that the pages read at load, so a show changes exactly one blob.

    Not called a gap because there is no performance yet to hang one on, but
    it is the same count true_gaps makes: the day the song is played again,
    its gap is the figure this file held the night before.
    """
    if dates is None:
        dates = load_calendar(site_dir)
    if not dates:
        return None
    # Counted from the last performance that was at a *show*, which is not
    # always the last performance. Every page that prints a last-played date
    # filters to the counting calendar first -- a soundcheck is not a night the
    # band played -- so measuring from the raw last row meant two songs in the
    # archive carried a figure anchored to a date no page displays. Windora Bug
    # read 251 shows since beside a last-played date of 2000-09-15, because its
    # newest row is an uncounted 2020 soundcheck; the honest figure against the
    # date its own page prints is 769. Two songs of 588 today, and wrong by five
    # hundred shows on both -- exactly the shape this archive's rule is for: a
    # wrong figure is worse than a missing one.
    counting = set(dates)
    since = {}
    for slug in sorted(archived_songs(site_dir)):
        doc = song_history(site_dir, slug)
        perfs = (doc or {}).get("performances") or []
        played = [p for p in perfs if p["date"] in counting] or perfs
        if played:
            since[slug] = shows_since(dates, played[-1]["date"])
    path = os.path.join(site_dir, "data", "current.json")
    write_if_changed(path, json.dumps(
        {"as_of": dates[-1], "shows": len(dates), "since": since},
        separators=(",", ":"), sort_keys=True) + "\n")
    return path


def show_kind(report, calendar=None):
    """Whether an archived report is a show, a soundcheck or a session.

    Twenty of the archive's entries are not concerts -- thirteen soundchecks
    and seven television or radio sessions, listed on not-a-show.html. phish.net
    lists them and flags them exclude_from_stats, which is why they are absent
    from the calendar, and their notes say which kind they are. A gap counted
    over them would be counting a soundcheck as a show the band played, and
    2020-02-19 -- a soundcheck -- is the oldest entry in the archive, so it
    opened the index.

    This docstring said "nine" and enumerated them by name until 2026-07-31,
    which was true when it was written and had drifted by eleven. A count in a
    comment is a figure like any other; the two figures above are the ones this
    function's own output produces, so they are checkable against the page.

    phish.net is not consistent about this across its whole history: of twenty
    studio, TV and radio sessions in the song histories, eight count and twelve
    do not, split roughly at 1999. We defer to the flag rather than invent a
    rule, so where they disagree with themselves we disagree with ourselves in
    exactly the same places, which is at least auditable.
    """
    if calendar is None:
        calendar = ()
    if report["date"] in set(calendar):
        return "show"
    notes = re.sub(r"<[^>]+>", " ", html.unescape(str(report.get("notes") or "")))
    for kind, pattern in KIND_PATTERNS:
        if re.search(pattern, notes, re.I):
            return kind
    # A show being played tonight is not on the calendar yet, by design:
    # fetch_calendar holds back today's UTC date so a show is never counted
    # before it has happened. But that hold says "do not count it", not "it is
    # not a concert", and reading it as the second filed the live show under
    # "Also on file" with the soundchecks -- with no "On stage now" banner --
    # for every minute before 00:00 UTC. On 2026-10-02 that was the opening
    # hour at Atlantic City. A report still coming in that does not read as a
    # soundcheck or a taping is the concert; the counts are untouched, because
    # they read the calendar, not this.
    if report.get("provisional"):
        return "show"
    return "session"


#: How to read a not-a-show entry's note, in order. First match wins.
#:
#: This returned two values until 2026-07-31 -- "soundcheck" for anything whose
#: note said soundcheck *or* rehearsal, and "session" for everything else --
#: and Ian objected to the first half of that: "a tech rehearsal is not really
#: a soundcheck. You could put them in the same bucket … but they're not the
#: same thing." He is right, and the 2011-05-26 Bethel Woods entry is the one
#: it was wrong about: phish.net calls it a tech rehearsal for a whole run
#: rather than the soundcheck for a night, and this site called it a soundcheck
#: because one regex covered both words.
#:
#: The second half was lumpier still. "Session" held five television
#: appearances, one NPR taping and the 2010 Rock and Roll Hall of Fame
#: ceremony where Phish inducted Genesis, which is not a session by any
#: reading.
#:
#: The notes are formulaic enough to carry this: phish.net writes "This was
#: the soundcheck for X" and "were the musical guests on X" almost verbatim
#: every time. What they are not is guaranteed, so `session` stays as the
#: fallback rather than a sixth pattern that pretends to know. Two traps this
#: ordering exists for: *rehearsal* is tested before *soundcheck* because the
#: Bethel note says both is not true -- it says rehearsal only -- but a future
#: note may say "the rehearsal, in place of a soundcheck"; and *broadcast* is
#: deliberately not a television signal, because two soundcheck notes say the
#: soundcheck was broadcast on The Bunny.
KIND_PATTERNS = (
    ("rehearsal", r"\brehearsals?\b"),
    ("soundcheck", r"\bsoundchecks?\b"),
    ("ceremony", r"\bhall of fame\b|\binduct(?:ing|ed|ion)\b"),
    ("radio", r"\btiny desk\b|\bNPR\b"),
    ("television", r"\b(?:tonight show|late night|musical guests?"
                   r"|in-studio guest|saturday night live)\b"),
)

#: What each kind is called on a page, and whether it happened because of a
#: show. The second is the distinction the not-a-show page is built on -- a
#: soundcheck and a rehearsal exist for a concert that follows, and a taping
#: or a ceremony is its own occasion.
KIND_LABEL = {"soundcheck": "Soundcheck", "rehearsal": "Tech rehearsal",
              "television": "Television", "radio": "Radio",
              "ceremony": "Ceremony", "session": "Not a show"}
#: (one, many) for counting them in a sentence. Written out because three of
#: the six do not take a plural by adding an s -- "5 televisions" was the first
#: thing the new kinds published, and a label that names a medium is not a
#: label that counts occasions.
KIND_COUNTED = {"soundcheck": ("soundcheck", "soundchecks"),
                "rehearsal": ("tech rehearsal", "tech rehearsals"),
                "television": ("television appearance",
                               "television appearances"),
                "radio": ("radio taping", "radio tapings"),
                "ceremony": ("ceremony", "ceremonies"),
                "session": ("other", "others")}
BEFORE_A_SHOW = ("soundcheck", "rehearsal")


def split_archive(reports, calendar):
    """(concerts, everything else), the second oldest-first and annotated.

    A soundcheck belongs to the show it precedes -- that is what it is for --
    so each one carries the date of the next concert on the calendar.
    """
    dates = sorted(calendar)
    shows, aside = [], []
    for r in sorted(reports, key=lambda r: r["date"]):
        kind = show_kind(r, dates)
        if kind == "show":
            shows.append(r)
            continue
        i = bisect.bisect_right(dates, r["date"])
        aside.append({"report": r, "kind": kind,
                      "before": dates[i] if i < len(dates) else None})
    return shows, aside


def archived_history(site_dir, slug, date):
    """A song's history from disk, in the shape add_previous wants, or None.

    setlists/slug returns a song's *whole* history, so archiving one show's
    songs archives their 1980s performances too. Backfilling therefore asks
    phish.net for history it already has: at 21 songs a show, a 440-show
    backfill of 3.0 is some 9,000 calls to re-read files on this disk.

    Returned only when the stored history already contains the show being
    built. That is the exact condition under which it is known to be complete
    for this purpose -- a history missing tonight is a history that predates
    tonight, and its gaps stop short. Anything else falls through to the API.
    """
    if not site_dir:
        return None
    doc = song_history(site_dir, slug)
    perfs = (doc or {}).get("performances") or []
    if not any(p.get("date") == date for p in perfs):
        return None
    # Stored oldest-first and already one row per show, which is what by_show
    # and own_history would have produced on the way in.
    return [{"showdate": p["date"], "venue": p.get("venue") or "",
             "city": p.get("city") or "", "state": p.get("state") or "",
             "gap": p.get("gap"), "out": p.get("out") or ""} for p in perfs]


# The running order of every show we have ever walked, under site/data with the
# rest of the archive. It lived in a top-level archive/ for a day, on the theory
# that site/ is what readers see and this is a build input. That theory does not
# survive measurement: of site/data's 19 MB, only data/shows and current.json
# are ever fetched by a page -- data/songs is 10 MB that no reader has ever
# requested. .gitignore has said the real rule the whole time, that "site/data
# is the archive that regenerates them". Being published costs 3.5 MB on a
# 228 MB tree and buys the thing that matters: the workflows already commit
# site/data, so CI keeps this file without a special case, and it takes
# `site_dir` like every other archive path instead of an absolute one derived
# from __file__.
def order_path(site_dir):
    return os.path.join(site_dir, "data", "setlist-order.jsonl")


# The only six fields kept. Everything else the endpoint returns is either
# already in the archive or of no use here; see docs/setlist-order.md.
ORDER_FIELDS = ("showid", "set", "position", "slug", "song", "trans_mark")


def running_key(r):
    """Sort key for one setlist row: phish.net's own running order.

    `(showid, position)`, and *not* `(SET_ORDER, position)`, which is what this
    used to be and which was wrong twice.

    A festival secret set is filed after the encore and numbered accordingly --
    the IT Tower Jam is set 4 at position 27, behind an encore ending at 26 --
    but SET_ORDER puts "4" before "e", so the site moved it in front of the
    encore and credited the wrong song with closing the night. Six shows, every
    one a festival: the Clifford Ball's Flatbed Truck Jam, Lemonwheel's Ambient
    Jam, IT's Tower Jam, Super Ball's Storage Jam, Magnaball's Drive-In Jam and
    Mondegreen's Woodlands Jam. **Mondegreen's is filed as set 3, not set 4**,
    so a rule that special-cased "4" would have missed the most recent one.

    And ten dates hold two separate performances -- a WNEW radio session in the
    afternoon and the Beacon Theatre that night, The Late Show and then Live on
    Letterman -- each numbered from position 1. Sorting on position alone
    interleaves them. `showid` is what separates them, positions are unique
    within one, and the pair is a total order across all 2,008 archived dates.

    Ordering the performances against each other is by showid, which is a
    record id rather than a clock; in all ten it agrees with the notes about
    which came first, and nothing here depends on it beyond keeping each
    performance contiguous.
    """
    return (int(r.get("showid") or 0), int(r.get("position") or 0))


def order_rows(rows, artist="Phish"):
    """One show's running order, reduced to the six fields worth keeping.

    `trans_mark` is stripped, because phish.net sends it padded inconsistently
    -- ", " and "," and " > " and ">" all appear -- and both readers of this
    field strip it anyway. Storing the padded form meant the same show
    re-derived from the same response did not equal what was on disk, so the
    write-if-changed guard in --catch-up would have rewritten a date that had
    not moved. 380 of the archive's 39,774 rows were stored padded; they
    normalize on the next write of their date.
    """
    rows = [r for r in rows
            if r.get("song") and (not artist or r.get("artist_name") == artist)]
    rows.sort(key=running_key)
    return [{"showid": int(r.get("showid") or 0),
             "set": str(r.get("set") or ""),
             "position": int(r.get("position") or 0),
             "slug": r.get("slug") or r.get("song") or "",
             "song": r.get("song") or "",
             "trans_mark": (r.get("trans_mark") or "").strip()}
            for r in rows]


def setlist_order(site_dir, path=None):
    """{date: rows} for every show the extract holds, or {} if it is missing.

    Missing is not an error. It costs API calls, not correctness -- every date
    absent here is simply fetched -- so a checkout without the archive still
    builds, just slowly.

    One JSON object per line, `{"date": ..., "rows": [...]}`. A damaged line is
    skipped rather than failing the read: the file's whole purpose is to save
    API calls, so 2,007 usable dates and one refetch beats none.
    """
    path = path or order_path(site_dir)
    if not os.path.isfile(path):
        return {}
    shows, bad = {}, 0
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
                shows[rec["date"]] = rec["rows"]
            except (ValueError, KeyError, TypeError):
                bad += 1
    if bad:
        log("warning: %s has %d unreadable line%s; those dates will be refetched",
            path, bad, "" if bad == 1 else "s")
    return shows


def save_setlist_order(shows, site_dir, path=None):
    """Write the extract back, whole, via a temporary file.

    One line per date, sorted by date, because the reason this is line-oriented
    is the diff. A backfilled show lands mid-history, and as a single JSON
    document that read as one changed line of 3.3 MB -- git's own --numstat
    called it "1 line" either way, so a pull request summary looked harmless
    and the diff itself was 7 MB of unreadable. One date per line makes the
    same insert a one-line diff of about 1 KB.

    Whole rather than appended because a backfill inserts in the middle, and a
    file that is only correct when writes arrive in date order is a file that
    silently stops being sorted. Via a temporary file because a write
    interrupted half way would leave the record of 2,008 walked shows
    truncated -- and this file exists so those shows are never fetched twice.
    """
    path = path or order_path(site_dir)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        for date in sorted(shows):
            fh.write(json.dumps({"date": date, "rows": shows[date]},
                                sort_keys=True, separators=(",", ":")) + "\n")
    os.replace(tmp, path)
    log("archive: running order for %d show%s",
        len(shows), "" if len(shows) == 1 else "s")


def setlist_neighbors(rows, artist=None):
    """What each song followed and led into, per slug, for one show.

    Within a set, `prev`/`next` and the mark that joins them. Across a set
    break, `xprev`/`xnext` -- the same adjacency, named as what it is and
    never carrying a mark, because a mark across twenty minutes of setbreak
    would be a lie about a segue. Adjacency itself is not: an encore is chosen
    in answer to how set 2 ended, and a blank cell threw that away.

    At the two ends of the night, `first` and `last`. Those are the only two
    true terminals -- a set opener and a set closer both have a real song on
    the far side of a break, which is why they get a song and these get a
    flag. The four together mean a blank cell now says one thing only: we
    have not walked this setlist.

    The mark between two songs belongs to the earlier of them -- phish.net
    stores it as the trailing punctuation -- so the way *into* a song is the
    previous row's mark, not its own.

    "The show" means this artist's show. Rows by anyone else are dropped
    before the ends are found, so at a festival the first Phish song is the
    show opener even where another band played earlier. That is the same
    reading every other page here takes.

    A song played more than once in a night keeps the first appearance, which
    is the row the archive keeps too.

    Every song found in `rows` gets an entry, even an empty one. That is the
    difference between "this setlist says the song opened its set" and "this
    setlist did not mention the song at all", and the caller needs it: it used
    to record both as asked-and-answered, so a show fetched while it was still
    being typed up locked in an answer of "no neighbors" that no later run
    would revisit.
    """
    rows = [r for r in rows
            if r.get("song") and (not artist or r.get("artist_name") == artist)]
    rows.sort(key=running_key)
    out = {}
    # Ten dates hold two performances -- a radio session in the afternoon and
    # a theatre that night. Both are "set 1" and both number from position 1,
    # so a set test alone made the last song of the radio set and the first of
    # the concert into neighbors, and only one of the two got a `first`. The
    # show is the performance, not the date: adjacency is within a showid, and
    # each performance has its own two ends.
    for i, r in enumerate(rows):
        slug = r.get("slug") or r.get("song")
        if slug in out:
            continue
        # Bound per row rather than once, so they close over this `r` and not
        # over whatever the loop last left behind.
        perf = lambda j: (0 <= j < len(rows)
                          and str(rows[j].get("showid") or "")
                          == str(r.get("showid") or ""))
        same = lambda j: (perf(j)
                          and str(rows[j].get("set")) == str(r.get("set")))
        nb = {}
        if same(i - 1):
            nb["prev"] = rows[i - 1].get("song") or ""
            mark = (rows[i - 1].get("trans_mark") or "").strip()
            if mark and mark != ",":
                nb["in"] = mark
        elif perf(i - 1):
            nb["xprev"] = rows[i - 1].get("song") or ""
        else:
            nb["first"] = 1
        if same(i + 1):
            nb["next"] = rows[i + 1].get("song") or ""
        elif perf(i + 1):
            nb["xnext"] = rows[i + 1].get("song") or ""
        else:
            nb["last"] = 1
        out[slug] = nb
    return out


def apply_neighbors(perf, found, settled=True):
    """Write one walk's answer onto one performance, replacing the last one.

    Cleared before updating rather than merged over: a key this walk did not
    set is a key that is no longer true, and merging would leave a row that
    was a set closer carrying both that answer and the newer one.

    `last` and `nb` are withheld while the show is still being played. `last`
    means "closed the show", a claim about songs nobody has played yet, wrong
    from the moment the next one lands. `nb` means the walk is finished, and
    it is the thing that stops a date ever being asked again -- writing it
    mid-show is how the Before / after column was emptied on 758 rows.
    """
    for k in NB_KEYS:
        perf.pop(k, None)
    perf.update(found)
    if settled:
        perf["nb"] = 1
    else:
        perf.pop("last", None)
        perf.pop("nb", None)


def record_neighbors(site_dir, date, rows, artist=None, settled=True):
    """Write one show's neighbors into the songs that were played in it.

    Free. The setlist that built the report is already in hand, so this is the
    walk `--seed-setlists` does, done at the moment the show is fetched rather
    than whenever somebody next runs the backfill by hand. Before this, a show
    played tonight kept a blank Before / after column on every one of its songs
    until a manual run -- which is how 2026-07-29 shipped.

    Nothing is claimed about a show still being played. `last` means "closed
    the show", a statement about songs that have not happened, wrong from the
    moment the next one lands; `nb` means the walk is finished, and it is what
    stops a date ever being asked again. Both wait for the show to settle.
    Everything else is true as soon as the song after it exists, so the column
    fills in live.
    """
    nb = setlist_neighbors(rows, artist)
    wrote = 0
    for slug, found in nb.items():
        doc = song_history(site_dir, slug)
        if not doc:
            continue                      # song not archived, nothing to hold it
        hit = False
        for p in doc["performances"]:
            if p["date"] != date:
                continue
            apply_neighbors(p, found, settled)
            hit = True
        if not hit:
            continue
        write_song_file(site_dir, slug,
                        {k: doc.get(k, "") for k in ("song", "slug", "artist")},
                        doc["performances"], doc.get("best") or [])
        wrote += 1
    if wrote:
        log("neighbors: %s on %d song%s%s", date, wrote,
            "" if wrote == 1 else "s",
            "" if settled else " (show still on; not final)")
    return wrote


NEIGHBOR_FLUSH = 150


def seed_setlists(site_dir, apikey=None, artist="Phish", force=False, **kw):
    """Backfill what came before and after each archived performance.

    Walked from `site/data/setlist-order.jsonl` wherever it reaches, and fetched
    only where it does not -- so changing the neighbor rules and re-walking
    all 1,966 shows with `--force` costs nothing and needs no API key.

    One setlist call per distinct show not in that archive. Every row a call
    covers is marked
    asked, on the row itself rather than in an index of dates: a date index
    cannot tell "asked, and this song opened the set" from "never asked", so
    adding songs later left them with no neighbors on dates the index already
    called done -- 88 songs added in one backfill came out at 0.3% covered.

    Flushed in batches, because twenty minutes of fetching should not have to
    start over because a laptop lid closed.
    """
    songs = {}
    for slug in sorted(archived_songs(site_dir)):
        doc = song_history(site_dir, slug)
        if doc:
            songs[slug] = doc

    todo = sorted({p["date"] for d in songs.values() for p in d["performances"]
                   if force or not p.get("nb")})
    if not todo:
        log("neighbors: nothing to walk")
        return 0

    # The running order we already own. A date in here costs nothing, which is
    # what the extract is for: the rules above can change and every one of
    # 1,966 shows is re-walked for free. Only what it is missing is fetched,
    # and what is fetched goes into it, so no date is ever paid for twice.
    #
    # Except for a show still being played. An extract is a cache with no
    # expiry at all, and the archive already holds tonight's show at the 12
    # songs it had when it was harvested. Reading that back would freeze the
    # running order of the one show whose running order is still changing --
    # the same shape as the six-hour cache that cost the first hour of
    # 2026-07-29, and it would not even have the decency to expire. So a show
    # whose report is still provisional is always re-fetched, and what comes
    # back replaces what the extract held.
    order = setlist_order(site_dir)
    unsettled = {r["date"] for r in saved_reports(site_dir)
                 if r.get("provisional")}
    have = sum(1 for d in todo if d in order and d not in unsettled)
    log("neighbors: %d show%s to walk, %d from the archive, %d to fetch",
        len(todo), "" if len(todo) == 1 else "s", have, len(todo) - have)
    pending, walked, fetched, missed, absent, grew = {}, 0, 0, [], 0, False

    def flush():
        for slug in sorted(pending):
            doc = songs[slug]
            write_song_file(site_dir, slug,
                            {k: doc.get(k, "") for k in ("song", "slug", "artist")},
                            doc["performances"], doc.get("best") or [])
        pending.clear()

    for i, date in enumerate(todo, 1):
        rows = None if date in unsettled else order.get(date)
        if rows is None:
            # Not in the extract, so this one has to be bought. The key is
            # loaded here rather than up front: a re-walk the archive covers
            # end to end needs no key at all, and asking for one would have
            # made a free run fail on a machine that has none.
            #
            # A missing key is a missed date, not a dead run. Thirty seconds
            # of walking is already on the floor by this point and the flush
            # that would save it is at the bottom of this loop.
            if apikey is None:
                apikey = load_key(None, required=False) or ""
            if not apikey:
                missed.append("%s (no API key)" % date)
                continue
            try:
                rows = get("setlists/showdate/%s" % date, apikey, **kw)
            except ApiError as exc:
                missed.append("%s (%s)" % (date, exc))
                continue
            nb = setlist_neighbors(rows, artist)
            kept = order_rows(rows, artist)
            if date in unsettled:
                # A show still being played is never written down here. Its
                # order is partial by definition, and the day it settles a
                # partial record stops being skipped and starts being
                # believed. Any earlier partial goes too: the extract was
                # first harvested mid-show and holds one already.
                if order.pop(date, None) is not None:
                    grew = True
            elif kept:
                order[date] = kept
                grew = True
            fetched += 1
        else:
            # No artist filter: the extract is one artist already and does not
            # carry `artist_name`, so filtering on it would empty every row.
            nb = setlist_neighbors(rows)
        for slug, doc in songs.items():
            for p in doc["performances"]:
                if p["date"] != date:
                    continue
                # Marked when this setlist actually mentioned the song, whether
                # or not it had a neighbor to report: a set opener genuinely
                # has nothing before it and must not be asked again every run.
                #
                # Not marked when the setlist never mentioned it. That reading
                # is not an answer, and recording it as one is what emptied the
                # Before / after column on songs that have never once been
                # played without a neighbor. Colonel Forbin's Ascent > Fly
                # Famous Mockingbird is the same pair every time it is played,
                # and 75 of the Mockingbird's 131 performances showed nothing,
                # because those shows were read at a moment the song was not in
                # the setlist yet -- and nb=1 meant no later run would look
                # again. Leaving it unmarked costs one call per such date per
                # run and repairs itself the first time the answer is there.
                if slug not in nb:
                    absent += 1
                    continue
                # Same guard as --catch-up's: a hand-run of this during a show
                # would otherwise stamp "closed the show" on whatever song was
                # last at that moment and mark the date answered, which is the
                # one state no later run would revisit.
                apply_neighbors(p, nb[slug], date not in unsettled)
                pending[slug] = True
        walked += 1
        if i % NEIGHBOR_FLUSH == 0:
            flush()
            log("  %d/%d shows", i, len(todo))
    flush()
    if grew:
        save_setlist_order(order, site_dir)
    if missed:
        log("warning: no setlist for %d show%s: %s",
            len(missed), "" if len(missed) == 1 else "s", "; ".join(missed[:5]))
    # Said out loud rather than left in the data: these are the performances
    # left deliberately unmarked, so they are asked again next run. A number
    # that does not fall over successive runs means the archive and phish.net
    # genuinely disagree about who played what, which is worth knowing.
    if absent:
        log("neighbors: %d performance%s not in the setlist fetched for its "
            "own date; left unmarked to ask again", absent,
            "" if absent == 1 else "s")
    log("neighbors: %d show%s walked, %d of them fetched",
        walked, "" if walked == 1 else "s", fetched)
    return walked


# How far back to keep asking about a show that still has no rating. Measured
# on this archive: every show four days old or more had one, the two newer than
# that had none, so the answer arrives somewhere in between. --recheck's three
# days would have missed a rating landing on the fourth, and re-fetching whole
# shows to find out is a poor trade when the rating is one call on its own.
RATING_CHASE_DAYS = 21


def sweep_ratings(site_dir, days=RATING_CHASE_DAYS, **kw):
    """Re-ask about archived shows that still have no rating.

    Ratings show up days after a show, long after its setlist has settled and
    the report stopped being re-fetched. This asks only about the shows still
    missing one, only for as long as one might plausibly arrive, and only of
    fouldomain -- phish.net is not touched.
    """
    cutoff = (_utcnow().date() - datetime.timedelta(days=days)).isoformat()
    todo = [r for r in saved_reports(site_dir)
            if r["date"] >= cutoff and r.get("pnet_rating") is None]
    if not todo:
        return []
    log("ratings: %d recent show%s still without one",
        len(todo), "" if len(todo) == 1 else "s")
    found = []
    for report in todo:
        got = {}
        try:
            got = show_ratings(report["date"], **kw)
        except ApiError as exc:
            log("  %s: %s", report["date"], exc)
        if not got:
            continue
        # fouldomain answers with whatever it has, and it has its own score for
        # a show well before phish.net has a rating for it -- so a non-empty
        # reply is not the same as the reply we came for. Keeping the score is
        # still worth the write; announcing a rating that is not there is a
        # KeyError that kills the whole run, which is what it did.
        report.update(got)
        _, blob = site_paths(site_dir, report["date"])
        with open(blob, "w", encoding="utf-8") as fh:
            json.dump(report, fh, indent=2)
        rating = got.get("pnet_rating")
        if rating is None:
            log("  %s: fouldomain has a score but phish.net has no rating yet",
                report["date"])
            continue
        found.append(report["date"])
        log("  %s rated %.2f", report["date"], rating)
    return found


def seed_scores(site_dir, songs=None, **kw):
    """Fill in fouldomain's top-rated versions for archived songs.

    One call per song. Songs that already have scores are skipped unless named
    explicitly, because the top of a forty-year song's ranking does not move
    when the band plays it once more -- a new performance essentially never
    enters its own all-time best list on the night.
    """
    have = archived_songs(site_dir)
    todo = sorted(songs if songs is not None
                  else (s for s in have
                        if not (song_history(site_dir, s) or {}).get("best")))
    if not todo:
        return 0
    log("scores: %d song%s to ask fouldomain about",
        len(todo), "" if len(todo) == 1 else "s")
    written, missed = 0, []
    for i, slug in enumerate(todo, 1):
        doc = song_history(site_dir, slug)
        if not doc:
            continue
        try:
            best = best_versions(doc["song"], **kw)
        except ApiError as exc:
            missed.append("%s (%s)" % (doc["song"], exc))
            continue
        write_song_file(site_dir, slug,
                        {k: doc.get(k, "") for k in ("song", "slug", "artist")},
                        doc["performances"], best)
        written += 1
        top = best[0] if best else None
        log(" [%d/%d] %-34s %2d rated%s",
            i, len(todo), doc["song"], len(best), " best %s (%s)" % (top["date"], top["score"]) if top else "")
    if missed:
        log("warning: no scores for %d song%s: %s",
            len(missed), "" if len(missed) == 1 else "s", "; ".join(missed[:5]))
    return written


def seed_songs(site_dir, apikey, artist="Phish", force=False, **kw):
    """Backfill histories for every song the saved reports already name.

    Ordinarily a song's history arrives with the show that played it, which
    means the corpus fills in over tours rather than all at once. This pays
    the calls up front instead, so every song in the archive has a page today.
    Songs already held are skipped unless --force, which makes a second run
    cost nothing.
    """
    wanted = {}
    for report in saved_reports(site_dir):
        for s in report["songs"]:
            wanted.setdefault(s["slug"], s["song"])
    have = set() if force else archived_songs(site_dir)
    todo = sorted(slug for slug in wanted if slug not in have)
    log("seeding: %d song%s named by the archive, %d already held, %d to fetch",
        len(wanted), "" if len(wanted) == 1 else "s", len(wanted) - len(todo), len(todo))

    missed, written = [], 0
    for i, slug in enumerate(todo, 1):
        try:
            rows = get("setlists/slug/%s" % slug, apikey, **kw)
        except ApiError as exc:
            missed.append("%s (%s)" % (wanted[slug], exc))
            continue
        rows = own_history(rows, artist)
        if not rows:
            # Every song here came out of a report for this artist, so an empty
            # history means the slug moved rather than that the song is new.
            missed.append("%s (no %s performances)" % (wanted[slug], artist))
            continue
        save_song_history(site_dir, slug, wanted[slug], rows, artist)
        written += 1
        shows = len(by_show(rows))
        log(" [%d/%d] %-34s %4d show%s%s",
            i, len(todo), wanted[slug], shows, " " if shows == 1 else "s", "" if shows == len(rows) else " (+%d same-night repeat%s)" % (len(rows) - shows, "" if len(rows) - shows == 1 else "s"))
    if missed:
        log("warning: no history for %d song%s: %s",
            len(missed), "" if len(missed) == 1 else "s", "; ".join(missed))
    log("seeded %d song histor%s into %s",
        written, "y" if written == 1 else "ies", os.path.join(site_dir, "data", "songs"))
    return written


def _coverage(report):
    """Songs, and how many of them know when they were last played.

    Song count alone is too coarse a measure of a better report: a re-fetch
    interrupted by a network drop returns the whole setlist with some of the
    per-song history missing, and would pass a count-only comparison.
    """
    songs = report.get("songs") or []
    return len(songs), sum(1 for s in songs if s.get("prev_date") or s.get("debut"))


def is_fuller(report, prior):
    """Whether a re-fetched show is worth replacing the archived one with.

    A re-check exists to complete a setlist that was archived mid-entry, so it
    must never do the reverse and trade a fuller report for a thinner one.
    """
    if not prior:
        return True
    was, now = _coverage(prior), _coverage(report)
    if now >= was:
        return True
    log("keeping archived %s: %d songs/%d with history beats the %d/%d just " "fetched",
        report["date"], was[0], was[1], now[0], now[1])
    return False


def _ts(value):
    """Parse an archived timestamp, or None if it is missing or unreadable.

    Naive values are read as UTC. A stamp we cannot trust restarts the quiet
    period, which delays a show rather than publishing a partial one.
    """
    try:
        t = datetime.datetime.fromisoformat(value)
    except (TypeError, ValueError):
        return None
    return t if t.tzinfo else t.replace(tzinfo=datetime.timezone.utc)


def _certainly_over(showdate, now):
    """True once no show on `showdate` could still be running anywhere in NA."""
    bound = datetime.datetime.combine(
        datetime.date.fromisoformat(showdate) + datetime.timedelta(days=1),
        LAST_END_UTC, tzinfo=datetime.timezone.utc)
    return now >= bound


def settle(report, prior, now):
    """Mark a freshly fetched show provisional until its song count holds still.

    Completeness cannot be read off the data. There is no showtime to reason
    from, the show record's updated_at lags by days, and the format is not
    promised -- a rained-out show can stop mid-second-set with no encore, so
    counting sets proves nothing. Stability stands in for completeness instead:
    a count that has not moved for QUIET_HOURS is taken for the whole show.
    Nothing about geography or set lengths is assumed, so a weather-shortened
    night converges exactly like a normal one; it just stops growing sooner.
    """
    count = len(report["songs"])
    same = prior and len(prior.get("songs") or []) == count
    since = _ts((prior or {}).get("count_since")) if same else None
    since = since if since and since <= now else now
    report["count_since"] = since.isoformat(timespec="seconds")
    held = now - since
    # An encore is the band saying the show is over, so the quiet period after
    # one can be much shorter than the one after an ordinary song. Two hours is
    # sized for the worst case -- a rained-out show that stops mid-second-set
    # with no encore and no other signal that it has ended. Once an encore has
    # been recorded, that worst case is not the case we are in, and holding the
    # page at "still coming in" for another two hours is simply wrong for most
    # of that time. Thirty minutes still covers a second encore, which is the
    # only thing that realistically follows the first.
    encored = any(str(s.get("set") or "").lower().startswith("e")
                  for s in report["songs"])
    wait = ENCORE_QUIET if encored else datetime.timedelta(hours=QUIET_HOURS)
    report["encored"] = encored
    report["provisional"] = not (held >= wait
                                or _certainly_over(report["date"], now))
    if report["provisional"]:
        log("%s still coming in: %d song%s, unchanged for %d of the %d min "
            "needed to call it finished%s",
            report["date"], count, "" if count == 1 else "s",
            held.total_seconds() // 60, wait.total_seconds() // 60,
            " (encore played)" if encored else "")
    elif prior is not None and (prior or {}).get("provisional"):
        log("%s settled: %d song%s, publishing as complete",
            report["date"], count, "" if count == 1 else "s")
    return report


def write_site(site_dir, reports, bar_scale="linear", rebuild=False):
    """Add reports to the site and rebuild the index around them.

    The JSON sidecar in data/shows/ is the archive: it is what lets --rebuild
    re-render every page after a template change without touching the API.
    """
    os.makedirs(show_data_dir(site_dir), exist_ok=True)
    # Archive everything first, provisional included, so the neighbor map that
    # the prev/next links need is built from the whole published site at once.
    for report in reports:
        _, blob = site_paths(site_dir, report["date"])
        with open(blob, "w", encoding="utf-8") as fh:
            json.dump(report, fh, indent=2)

    # Everything publishes, unfinished included. A show is worth reading while
    # it is happening, and the page says plainly that it is still coming in --
    # which is more honest than a site that pretends nothing is going on for
    # the four hours a show takes plus the two it takes to settle.
    known = list(saved_reports(site_dir))
    order = sorted(r["date"] for r in known)
    around = {d: (order[i - 1] if i else None,
                  order[i + 1] if i + 1 < len(order) else None)
              for i, d in enumerate(order)}

    # A new show gives its neighbor a next link it did not have, so that page
    # is stale too. --rebuild rewrites the lot regardless.
    fresh = {r["date"] for r in reports}
    stale = set(fresh)
    for date in fresh:
        stale |= {d for d in around.get(date, ()) if d}

    # A page and its preview card are made together, so a link shared the
    # moment a show lands already has a picture on it. No browser to draw them
    # with means no cards, and every page falls back to the house one rather
    # than pointing at a file that will never exist.
    # Drawing them needs a browser; naming them does not. A build without one
    # leaves the cards to the next build that has one, and the pages stay
    # byte-identical either way.
    exe = chrome_exe()
    jobs, prints = [], card_prints(site_dir)

    def want_card(name, markup):
        """A card is due when what it says has changed, or it is not there.

        Not when its page changed: a page carries a stylesheet and a card does
        not, so an edit to one rewrites all 169 pages and should redraw none of
        the cards. The second half keeps the pair self-healing -- a run that
        died before drawing, or a directory deleted by hand, is put right on the
        next build rather than leaving pages pointing at previews that do not
        exist.
        """
        if not exe:
            return False
        if card_print(markup) == prints.get(name) and os.path.isfile(
                os.path.join(site_dir, CARD_DIR, "%s.png" % name)):
            return False
        jobs.append((name, markup))
        return True

    # Slug -> the dates that song's page will carry a row for, not just the set
    # of slugs. Report pages anchor into those rows and one anchor pointed at a
    # row that does not exist; see render_html. Measured at 0.15s for 589 songs
    # against a ~2s rebuild, and it is read once rather than per report.
    songs = {slug: frozenset(p["date"] for p in
                             (song_history(site_dir, slug) or {}).get(
                                 "performances") or [])
             for slug in archived_songs(site_dir)}
    have_dates = {r["date"] for r in known}
    calendar = load_calendar(site_dir)
    counting = set(calendar)
    on_phishin = phishin_dates(site_dir) or None
    rebuilt = 0
    live_now = [r["date"] for r in known if r.get("provisional")]
    if live_now:
        log("%d show(s) still coming in: %s", len(live_now), ", ".join(live_now))
    no_tour_link = ambiguous_tours(known)
    if no_tour_link:
        log("tour names too alike to link: %s", ", ".join(sorted(no_tour_link)))
    for report in known:
        date = report["date"]
        if not (rebuild or date in stale):
            continue
        page, _ = site_paths(site_dir, date)
        prev, nxt = around.get(date, (None, None))
        if write_if_changed(page, render_html(
                report, bar_scale=bar_scale, index_href="../index.html",
                prev_date=prev, next_date=nxt, songs=songs,
                card=date, archived_show=have_dates,
                sheet="../%s/%s" % (STATIC_DIR, SITE_SHEET), calendar=calendar,
                on_phishin=on_phishin, unlinkable_tours=no_tour_link)):
            if date in fresh:
                log("wrote %s", page)
            else:
                rebuilt += 1
        # Provisional shows included -- see report_card, where the in-progress
        # card is built from only the facts that will not move, so its hash
        # holds still and it is drawn once rather than every five minutes.
        want_card(date, report_card(report))

    # Song pages last, so they can link to whichever reports now exist. They
    # are cheap to write and the archive is the only input, so a rebuild does
    # the lot; otherwise only the songs this run touched.
    have = archived_dates(site_dir)
    played = {s["slug"] for r in reports for s in r["songs"]}
    # Date -> "soundcheck" or "session", for the rows a song page shows but
    # does not count. Built once here rather than per song page: it is a read
    # of every archived report's notes, and there are 589 pages.
    kinds = {a["report"]["date"]: a["kind"]
             for a in split_archive(known, sorted(counting))[1]}
    wrote, considered, docs = 0, 0, []
    for slug in sorted(archived_songs(site_dir)):
        doc = song_history(site_dir, slug)
        if not doc or not doc.get("performances"):
            continue
        docs.append(doc)
        if not (rebuild or slug in played):
            continue
        considered += 1
        page = os.path.join(site_dir, "song", "%s.html" % slug)
        name = "song-%s" % slug
        moved = write_if_changed(page, render_song(doc, archived=have,
                                                   card=name, counting=counting,
                                                   kinds=kinds))
        wrote += 1 if moved else 0
        want_card(name, song_card(doc, counting))
    if considered:
        log("song pages: %d rendered, %d changed",
            considered, wrote)

    if rebuilt:
        log("re-rendered %d unchanged-content page(s) after a template change",
            rebuilt)
    # Before the cards are shot, and it has to stay that way: `shoot_cards`
    # points the card renderer at this exact file, so a build that drew cards
    # first would set every one of them in whatever face the machine happened
    # to have -- silently, since a fallback is not an error. That is the bug
    # the "{sheet}" fix was half of.
    write_if_changed(os.path.join(site_dir, STATIC_DIR, SITE_SHEET),
                     FONTS_CSS)
    write_grain(site_dir)
    # Regenerated every publish, because every publish would otherwise remove
    # it. Never deleted when DOMAIN is empty: an unset variable in one
    # environment is not an instruction to unpublish the domain in all of them,
    # which is exactly the mistake this file exists to survive.
    if DOMAIN:
        write_if_changed(os.path.join(site_dir, "CNAME"), DOMAIN + "\n")
    # Rewritten every run, but it is one small file and write_if_changed means
    # a run that moved nothing publishes nothing.
    write_current(site_dir)
    if _UNREADABLE:
        log("warning: %d archived report(s) could not be read and are missing "
            "from this build: %s", len(_UNREADABLE),
            ", ".join(sorted(set(_UNREADABLE))[:5]))

    # After write_current, because it reads what that just wrote.
    since = {}
    cur_path = os.path.join(site_dir, "data", "current.json")
    if os.path.isfile(cur_path):
        try:
            with open(cur_path, encoding="utf-8") as fh:
                since = json.load(fh).get("since") or {}
        except ValueError:
            pass
    # Stays None when the due page was not built, so the index hero leaves the
    # card out rather than offering a figure and a link to a page that is not
    # there.
    n_due = n_rotation = None
    if docs and since:
        due_page = os.path.join(site_dir, "due.html")
        if write_if_changed(due_page, render_due(docs, counting, since,
                                                 card="due")):
            log("wrote %s", due_page)
        want_card("due", due_card(docs, counting, since))
        n_due = len(due_rows(docs, counting, since)[0])
        # Written beside the due page rather than on its own terms: it is the
        # fourth of that page's four lists, and its only door is the hero cell
        # there. Both are built from one due_rows() call's worth of definitions,
        # so the figure on the card and the length of the page cannot disagree.
        rotation_page = os.path.join(site_dir, ROTATION_PAGE)
        if write_if_changed(rotation_page,
                            render_dormant(docs, counting, since,
                                           card=ROTATION_CARD)):
            log("wrote %s", rotation_page)
        want_card(ROTATION_CARD, rotation_card(docs, counting, since))
        n_rotation = len(due_rows(docs, counting, since)[3])

    # After the due figures, and for the same reason the index waits for them:
    # this page is the door to Out of rotation now that the nav is four browse
    # spines, and a door with no figure on it is the one card on this site that
    # would not say how much is behind it. Written here rather than earlier so
    # the count comes from the same due_rows() call the page itself is built
    # from -- the alternative was a second definition of "out of rotation"
    # living on a different page, which is how the songs index came to disagree
    # with the song pages about 127 songs.
    if docs:
        songs_page = os.path.join(site_dir, "songs.html")
        moved = write_if_changed(songs_page,
                                 render_songs(docs, card="songs",
                                              counting=counting, n_due=n_due,
                                              n_rotation=n_rotation))
        if moved:
            log("wrote %s (%d songs)", songs_page, len(docs))
        want_card("songs", songs_card(docs, counting))

    # After the pages, because a forwarding note is only honest once the page
    # it points at is on disk -- and the note for dormant.html lands on top of
    # the previous build's copy of that page.
    write_redirects(site_dir)

    method = os.path.join(site_dir, "method.html")
    if write_if_changed(method, render_method(card="method")):
        log("wrote %s", method)

    faq = os.path.join(site_dir, "faq.html")
    if write_if_changed(faq, render_faq(card="faq")):
        log("wrote %s", faq)

    # Reads the phish.in catalogue off disk rather than being handed the set
    # the show pages use: those are built above from a different call in a
    # branch this one is not inside, and a page whose only figure came from
    # somewhere else would be the songs-index bug again -- two definitions of
    # one count, on two pages, disagreeing.
    ack = os.path.join(site_dir, ACK_PAGE)
    if write_if_changed(ack, render_acknowledgments(phishin_dates(site_dir))):
        log("wrote %s", ack)

    index = os.path.join(site_dir, "index.html")
    # Twenty of the archive's entries are soundchecks or TV and radio
    # sessions, which phish.net does not count toward a gap. Keeping them in
    # the list meant the index counted 259 shows the band had not played 259
    # of, and opened on a 2020 Moon Palace soundcheck. (It was nine when that
    # was written and this line said nine until 2026-07-31 -- a count in a
    # comment is a figure like any other, and it went stale the ordinary way.)
    shows, aside = split_archive(known, load_calendar(site_dir))
    venues_page = os.path.join(site_dir, "venues.html")
    if write_if_changed(venues_page, render_venues(shows, card="venues")):
        log("wrote %s", venues_page)
    want_card("venues", venues_card(shows))
    # These two are pages about the archive rather than views of it, so they
    # carry its figures; both are built here because `shows` is what they need
    # and it is not settled until split_archive above.
    want_card("method", explainer_card(
        "How this works", "What the numbers mean", shows))
    want_card("faq", explainer_card(
        "Questions", "Short answers, deep-linkable", shows))

    # The one page whose input is the running order rather than the gaps, so
    # the one page that reads the extract at build time. A checkout without it
    # still builds: year_order falls back to the running order inside each
    # saved report, and the page then covers the years the archive reaches
    # rather than the career -- shorter, and honest about being shorter,
    # because every figure on it is stated against the nights it read.
    read = year_order(setlist_order(site_dir), counting, known)
    if read:
        years_page = os.path.join(site_dir, "years.html")
        profiles = year_profiles(read, counting, docs)
        if write_if_changed(years_page, render_years(
                profiles, len(counting) - len(read),
                pages={doc["slug"] for doc in docs}, card="years")):
            log("wrote %s (%d of %d counting nights read)",
                years_page, len(read), len(counting))
        want_card("years", years_card(profiles))

    # Needs the song histories as well as the reports, so it is built here
    # rather than beside the due page: the entries are reports, the songs that
    # exist only at them and the versions of them that got out are not.
    if docs:
        nas = os.path.join(site_dir, NOT_A_SHOW_PAGE)
        calendar = load_calendar(site_dir)
        if write_if_changed(nas, render_not_a_show(known, docs, calendar,
                                                   card=NOT_A_SHOW_CARD)):
            log("wrote %s", nas)
        want_card(NOT_A_SHOW_CARD, not_a_show_card(known, docs, calendar))
    changed = write_if_changed(
        index, render_index(shows, card="index", aside=aside, n_due=n_due))
    want_card("index", index_card(shows))
    if jobs:
        made = shoot_cards(exe, jobs, site_dir)
        log("preview cards: %d of %d drawn", made, len(jobs))
        # Only what was actually drawn, so a batch that died partway is
        # retried next run rather than recorded as done.
        for name, markup in jobs[:made]:
            prints[name] = card_print(markup)
        save_card_prints(site_dir, prints)
    # Last, so it lists the pages this run wrote rather than the ones the last
    # run left behind.
    log("sitemap: %d pages", write_sitemap(site_dir))
    # Serve the directory verbatim on GitHub Pages, Jekyll out of the way.
    open(os.path.join(site_dir, ".nojekyll"), "a").close()
    log("%s %s (%d report%s)",
        "wrote" if changed else "unchanged", index, len(known), "" if len(known) == 1 else "s")
    return index


PDF_MAX_IN = 200.0        # PDF user-space ceiling: 14400 units = 200in


def _page_count(data):
    """Page count, or None if it genuinely cannot be determined.

    Never guess here. An earlier version returned 1 on failure, which the
    fitting search read as "it fits" and happily shrank the page to its floor,
    producing dozens of tiny pages. Unknown has to stay unknown.
    """
    try:
        import io
        from pypdf import PdfReader
        return len(PdfReader(io.BytesIO(data)).pages)
    except ImportError:
        pass
    except Exception:                                 # noqa: BLE001
        return None
    if b"/ObjStm" in data:
        return None          # page objects live inside compressed streams
    import re as _re
    return len(_re.findall(rb"/Type\s*/Page(?!\w)", data)) or None


def _page_css(height_in, width_in=8.5, margin="12mm"):
    return "@page{size:%.4gin %.4gin;margin:%s}" % (width_in, height_in, margin)


def _with_page_css(markup, css):
    """Author-level injection.

    WeasyPrint's render(stylesheets=...) are *user* stylesheets, which lose to
    the document's own @page rule, so the override goes into the markup.
    """
    tag = "<style>%s</style>" % css
    return (markup.replace("</head>", tag + "</head>", 1)
            if "</head>" in markup else tag + markup)


MIN_PAGE_IN = 3.0         # no real report legitimately fits under this


def fit_single_page(pages_at, tolerance=0.08):
    """pages_at(height_in) -> page count, or None when it cannot be measured.

    Grows the page until the content lands on one sheet, then binary searches
    downward for the shortest height that still fits. Returns that height, or
    None if one page is unreachable or the count cannot be trusted.
    """
    hi = 22.0
    while True:
        count = pages_at(hi)
        if count is None:
            return None                    # refuse to search blind
        if count == 1:
            break
        if hi >= PDF_MAX_IN:
            return None
        hi = min(hi * 2, PDF_MAX_IN)

    lo = MIN_PAGE_IN
    if pages_at(lo) == 1:
        return lo                          # genuinely tiny document
    while hi - lo > tolerance:
        mid = (lo + hi) / 2
        count = pages_at(mid)
        if count is None:
            return None
        if count == 1:
            hi = mid
        else:
            lo = mid
    return hi


@contextlib.contextmanager
def _muted_stderr():
    """Silence fd 2 for the duration.

    WeasyPrint prints a multi-line installation banner straight to stderr when
    its native libs are missing, before raising. On macOS that import is never
    going to work from a venv, so the banner is noise on every single run.
    Muting the fd catches it whether it comes from Python or the C layer.
    """
    saved = os.dup(2)
    try:
        with open(os.devnull, "w") as null:
            os.dup2(null.fileno(), 2)
        yield
    finally:
        os.dup2(saved, 2)
        os.close(saved)


def _pdf_via_module(markup, path, base_url, single_page=False):
    with _muted_stderr():
        from weasyprint import HTML       # raises OSError on missing dylibs

    def doc(css=""):
        return HTML(string=_with_page_css(markup, css) if css else markup,
                    base_url=base_url)

    if not single_page:
        doc().write_pdf(path)
        return
    # exact count straight from the layout tree, no PDF parsing involved
    height = fit_single_page(lambda h: len(doc(_page_css(h)).render().pages))
    if height is None:
        raise RuntimeError("could not fit one page under %gin" % PDF_MAX_IN)
    doc(_page_css(height)).write_pdf(path)


def _in_current_env(path):
    """True if path lives inside the running venv/interpreter prefix."""
    try:
        real = os.path.realpath(path)
    except OSError:
        return False
    prefixes = {os.path.realpath(p) for p in (sys.prefix, sys.exec_prefix)
                if p}
    return any(real.startswith(p + os.sep) for p in prefixes)


# Packaged installs (brew, macports, apt) link their native libs correctly.
# A weasyprint on PATH may instead be the venv's own copy -- the exact one
# that already failed to import -- so those are skipped.
CLI_CANDIDATES = (
    "/opt/homebrew/bin/weasyprint",     # Homebrew, Apple silicon
    "/usr/local/bin/weasyprint",        # Homebrew, Intel
    "/opt/local/bin/weasyprint",        # MacPorts
    "/usr/bin/weasyprint",              # apt
)


def _weasyprint_clis():
    seen, out = set(), []
    for cand in CLI_CANDIDATES:
        if os.path.isfile(cand) and os.access(cand, os.X_OK):
            seen.add(os.path.realpath(cand))
            out.append(cand)
    found = shutil.which("weasyprint")
    if found and os.path.realpath(found) not in seen \
            and not _in_current_env(found):
        out.append(found)
    return out


def _pdf_via_weasyprint_cli(markup, path, base_url, single_page=False):
    """Packaged weasyprint CLIs run in the environment their packager built.

    That sidesteps the dlopen failure that hits an importable module inside a
    venv -- but only if we skip the venv's own CLI, which shares the fault.
    """
    exes = _weasyprint_clis()
    if not exes:
        raise FileNotFoundError(
            "no weasyprint CLI outside this venv (checked %s)"
            % ", ".join(CLI_CANDIDATES))
    last = None
    for exe in exes:
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "report.html")
            with open(src, "w", encoding="utf-8") as fh:
                fh.write(markup)
            out = os.path.join(tmp, "out.pdf")

            def run(css="", uncompressed=False, _exe=exe, _src=src, _out=out):
                doc = _with_page_css(markup, css) if css else markup
                with open(_src, "w", encoding="utf-8") as fh2:
                    fh2.write(doc)
                cmd = [_exe, "--base-url", base_url]
                if uncompressed:
                    # keeps page objects out of compressed streams so they
                    # stay countable without pypdf
                    cmd.append("--uncompressed-pdf")
                subprocess.run(cmd + [_src, _out], check=True,
                               capture_output=True, timeout=180)
                with open(_out, "rb") as fh2:
                    return fh2.read()

            try:
                if single_page:
                    height = fit_single_page(
                        lambda h: _page_count(run(_page_css(h), True)))
                    if height is None:
                        raise RuntimeError(
                            "could not fit one page under %gin" % PDF_MAX_IN)
                    data = run(_page_css(height))
                else:
                    data = run()
                with open(path, "wb") as fh:
                    fh.write(data)
                return
            except subprocess.CalledProcessError as exc:
                last = exc
    raise last


# Chrome has no single-page switch, so the document measures itself and sets
# @page before printing. Needs preferCSSPageSize, which --print-to-pdf honors.
MEASURE_JS = """<script>
(function(){
  var d=document.documentElement, b=document.body;
  var h=Math.max(b.scrollHeight,d.scrollHeight,b.offsetHeight,d.offsetHeight);
  var s=document.createElement('style');
  s.textContent='@page{size:8.5in '+((h/96)+0.4).toFixed(3)+'in;margin:12mm}';
  document.head.appendChild(s);
})();
</script>"""

CHROME_CANDIDATES = (
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    "/Applications/Chromium.app/Contents/MacOS/Chromium",
    "/Applications/Microsoft Edge.app/Contents/MacOS/Microsoft Edge",
    "/Applications/Brave Browser.app/Contents/MacOS/Brave Browser",
    "google-chrome", "chromium", "chromium-browser", "msedge",
)


def _pdf_via_chrome(markup, path, base_url, single_page=False):
    exe = next((c for c in CHROME_CANDIDATES
                if os.path.isfile(c) or shutil.which(c)), None)
    if not exe:
        raise FileNotFoundError("no Chrome-family browser found")
    exe = exe if os.path.isfile(exe) else shutil.which(exe)
    with tempfile.TemporaryDirectory() as tmp:
        src = os.path.join(tmp, "report.html")
        if single_page:
            markup = markup.replace("</body>", MEASURE_JS + "</body>")
        with open(src, "w", encoding="utf-8") as fh:
            fh.write(markup)
        proc = subprocess.run(
            [exe, "--headless", "--disable-gpu", "--no-sandbox",
             "--no-pdf-header-footer",
             "--virtual-time-budget=4000",       # let the webfonts arrive
             "--user-data-dir=" + os.path.join(tmp, "profile"),
             "--print-to-pdf=" + os.path.abspath(path),
             "file://" + src],
            capture_output=True, timeout=180)
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or b"").decode("utf-8", "replace")
                           .strip() or "browser exited %d" % proc.returncode)


def _looks_like_pdf(path):
    try:
        if os.path.getsize(path) < 1024:
            return False
        with open(path, "rb") as fh:
            return fh.read(5) == b"%PDF-"
    except OSError:
        return False


PDF_BACKENDS = (
    ("module", _pdf_via_module),
    ("cli", _pdf_via_weasyprint_cli),
    ("browser", _pdf_via_chrome),
)

BACKEND_HELP = {
    "module": "weasyprint python module",
    "cli": "weasyprint command-line binary",
    "browser": "headless chrome/chromium/edge/brave",
}


def write_pdf(markup, path, base_url=None, prefer=None, single_page=False):
    """Try each backend in turn, verifying real PDF bytes before accepting.

    Each backend renders to a scratch file. A backend that exits cleanly but
    writes nothing (or writes non-PDF bytes) counts as a failure, and the
    destination is only replaced once the output is confirmed good.
    """
    base_url = base_url or (os.getcwd() + os.sep)
    backends = PDF_BACKENDS
    if prefer:
        backends = [b for b in PDF_BACKENDS if b[0] == prefer] or PDF_BACKENDS
    problems = []
    scratch_dir = os.path.dirname(os.path.abspath(path)) or "."
    for name, fn in backends:
        fd, scratch = tempfile.mkstemp(suffix=".pdf", dir=scratch_dir)
        os.close(fd)
        os.unlink(scratch)
        try:
            fn(markup, scratch, base_url, single_page)
            if not _looks_like_pdf(scratch):
                raise RuntimeError("produced no usable PDF")
            if single_page:
                with open(scratch, "rb") as fh:
                    n = _page_count(fh.read())
                if n is not None and n != 1:
                    raise RuntimeError("asked for one page, got %d" % n)
            shutil.move(scratch, path)
            return name
        except Exception as exc:                      # noqa: BLE001
            detail = getattr(exc, "stderr", b"") or b""
            if isinstance(detail, bytes):
                detail = detail.decode("utf-8", "replace")
            first = next((ln for ln in detail.strip().splitlines()
                          if ln.strip() and not ln.startswith("-")), "")
            problems.append("  %-8s %-34s %s" % (
                name, BACKEND_HELP[name],
                ("%s: %s" % (type(exc).__name__, first or str(exc)))[:110]))
        finally:
            if os.path.exists(scratch):
                os.unlink(scratch)
    raise ApiError(
        "No working PDF backend. Tried:\n%s\n\n"
        "Options:\n"
        "  brew install weasyprint   the cli backend then needs no venv\n"
        "  --html out.html           then Cmd-P in your browser; the print\n"
        "                            stylesheet is already in the document"
        % "\n".join(problems))


# ------------------------------------------------------------------- main ---

def main():
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("showdate", nargs="*", metavar="SHOWDATE",
                    help="one or more show dates, YYYY-MM-DD")
    ap.add_argument("--apikey", help="overrides PL_PHISHNET_API_KEY")
    ap.add_argument("--artist", default="Phish",
                    help="artist filter when a date has multiple (default Phish)")
    ap.add_argument("--previous", action="store_true",
                    help="also fetch each song's prior performance "
                         "(one extra API call per song)")
    ap.add_argument("--site", metavar="DIR",
                    help="add each show to DIR as DIR/<date>.html, archive the "
                         "data in DIR/data, and regenerate DIR/index.html")
    ap.add_argument("--force", action="store_true",
                    help="with --site, re-fetch dates the site already has")
    ap.add_argument("--rebuild", action="store_true",
                    help="with --site, re-render every archived report "
                         "(use after a template change; no API calls)")
    ap.add_argument("--seed-songs", action="store_true",
                    help="with --site, fetch a performance history for every "
                         "song the archive already names (one call per song, "
                         "skipping songs already held)")
    ap.add_argument("--sweep-ratings", nargs="?", type=int,
                    const=RATING_CHASE_DAYS, metavar="DAYS",
                    help="with --site, re-ask fouldomain about archived shows "
                         "from the last DAYS (default %d) that still have no "
                         "rating; one call per show and none to phish.net"
                         % RATING_CHASE_DAYS)
    ap.add_argument("--seed-setlists", action="store_true",
                    help="with --site, fetch the full setlist of every show in "
                         "the archive to record what each performance followed "
                         "and led into (one call per show, resumable)")
    ap.add_argument("--seed-scores", action="store_true",
                    help="with --site, fetch fouldomain's top-rated versions "
                         "for archived songs that have none yet; --force "
                         "re-asks for every song")
    ap.add_argument("--remeasure", action="store_true",
                    help="with --site, recompute gaps, verdicts and previous "
                         "performances for every archived report from the "
                         "stored song histories (no API calls)")
    ap.add_argument("--watching", action="store_true",
                    help="with --site, print watching=true when a scheduled "
                         "show is inside its watch window and watching=false "
                         "otherwise, then exit (no API calls). Also prints "
                         "released=, which is true once every show in the "
                         "window has been still for QUIET_HOURS -- the "
                         "watcher's stop signal, held longer than the page's "
                         "because leaving is what stops corrections arriving")
    ap.add_argument("--lead", type=int, default=0, metavar="MINUTES",
                    help="with --watching, treat a window as open this many "
                         "minutes early. The watcher uses it to be already "
                         "running when the first song is posted, because its "
                         "cron fires about 13%% of the time and a show only "
                         "gives it half an hour of slack")
    ap.add_argument("--phishin", action="store_true",
                    help="with --site, refresh the list of shows phish.in has "
                         "audio for, so links to them are only shown when they "
                         "will resolve (three calls, no key)")
    ap.add_argument("--schedule", action="store_true",
                    help="with --site, refresh the list of announced shows "
                         "that have not happened yet, with each venue's time "
                         "zone (two API calls)")
    ap.add_argument("--calendar", nargs="?", type=int, const=0, metavar="FROM",
                    help="with --site, refresh the show calendar that gap "
                         "counts are measured against, from year FROM to now "
                         "(default: the current year only; one call per year)")
    ap.add_argument("--catch-up", nargs="?", type=int, const=21, metavar="DAYS",
                    help="with --site, add every show played in the last DAYS "
                         "(default 21) that the site does not have yet, and "
                         "re-fetch any it is still holding as provisional")
    ap.add_argument("--recheck", nargs="?", type=int, const=RECHECK_DAYS,
                    metavar="DAYS",
                    help="with --catch-up, also re-fetch settled shows from "
                         "the last DAYS (default %d) to pick up corrections"
                         % RECHECK_DAYS)
    ap.add_argument("--html", help="write an HTML report here")
    ap.add_argument("--pdf", help="write a PDF report here")
    ap.add_argument("--bar-scale", choices=BAR_SCALES, default="linear",
                    metavar="{linear,sqrt,log}",
                    help="bar length scaling (default linear)")
    ap.add_argument("--single-page", action="store_true",
                    help="one continuous page, no page breaks")
    ap.add_argument("--pdf-backend", choices=("module", "cli", "browser"),
                    metavar="{module,cli,browser}",
                    help="force one PDF backend instead of trying each")
    ap.add_argument("--json", help="write the raw report here")
    ap.add_argument("--cache-dir", default=DEFAULT_CACHE)
    ap.add_argument("--refresh", action="store_true", help="bypass the cache")
    ap.add_argument("--from-json", help="render a saved --json file, no API call")
    args = ap.parse_args()

    one_file = next((f for f in ("html", "pdf", "json")
                     if getattr(args, f)), None)
    if one_file and len(args.showdate) > 1:
        sys.exit("error: --%s names a single file; use --site DIR to render "
                 "several dates at once" % one_file)
    if (args.rebuild or args.force or args.catch_up or args.seed_songs
            or args.seed_scores or args.seed_setlists or args.sweep_ratings
            or args.calendar is not None or args.schedule
            or args.remeasure or args.phishin) and not args.site:
        sys.exit("error: --rebuild, --force, --catch-up, --seed-songs, "
                 "--seed-scores, --seed-setlists, --sweep-ratings and "
                 "--calendar need --site DIR")
    if args.site:
        # Before anything reads the archive, and before --watching, which
        # takes its own early exit below.
        migrate_show_data(args.site)
        jobs = [n for n, on in (
            ("catch-up %s days" % args.catch_up, args.catch_up),
            ("recheck", args.recheck), ("previous", args.previous),
            ("rebuild", args.rebuild), ("sweep-ratings", args.sweep_ratings),
            ("calendar", args.calendar is not None), ("schedule", args.schedule),
            ("remeasure", args.remeasure), ("seed-songs", args.seed_songs),
            ("seed-scores", args.seed_scores),
            ("seed-setlists", args.seed_setlists)) if on]
        if jobs and not args.watching:
            log("run starting: %s", ", ".join(jobs))
            check_env()

    if args.watching:
        if not args.site:
            sys.exit("error: --watching needs --site DIR")
        live = watching(args.site, lead=args.lead)
        for s in live:
            w = watch_window(s)
            log("show in progress: %s %s (%s) -- window %s to %s UTC",
                s["date"], s["venue"], s["tz"],
                w[0].strftime("%H:%M"), w[1].strftime("%H:%M"))
        if not live:
            nxt = next_show(args.site)
            log("nothing playing%s", " -- next is %s %s" % (nxt["date"], nxt["venue"])
                if nxt else "")
        done = released(args.site, live)
        if live:
            log("released: %s", "yes -- safe to stop polling"
                if done else "no -- still watching")
        # stdout stays machine-readable: a workflow reads these lines. Named
        # for what they actually report -- whether a scheduled show is inside
        # its watch window right now, and whether every such show has stopped
        # changing -- and not for what a caller might do about it, which is
        # the caller's question and has other answers.
        #
        # Separate lines because they answer different questions
        # and the callers differ: the gate wants `watching`, the watcher's loop
        # wants `settled` to stop early. Both are parsed with `cut -d= -f2`
        # after a `grep`, so adding a line cannot break a reader of the other.
        print("watching=%s" % ("true" if live else "false"))
        print("released=%s" % ("true" if done else "false"))
        # Empty when nothing is scheduled, so a caller comparing it as a
        # number must treat "" as "no".
        mins = opens_in(args.site, lead=args.lead)
        print("opens_in=%s" % ("" if mins is None else mins))
        return
    if args.recheck and not args.catch_up:
        sys.exit("error: --recheck only means something with --catch-up")
    if not (args.showdate or args.from_json or args.rebuild or args.catch_up
            or args.seed_songs or args.seed_scores or args.seed_setlists
            or args.sweep_ratings or args.calendar is not None
            or args.schedule or args.remeasure or args.phishin):
        sys.exit("error: give at least one show date (YYYY-MM-DD)")
    if args.html and args.pdf and \
            os.path.abspath(args.html) == os.path.abspath(args.pdf):
        sys.exit("error: --html and --pdf point at the same file")

    reports, key, dates, recheck = [], None, list(args.showdate), set()
    # Running orders picked up by the fetch loop below, saved once after it
    # rather than per show: the extract is one file and rewriting it inside
    # the loop would write it once per date for nothing.
    fresh_order = {}
    # What the archive already holds, which the fetch loop below consults to
    # decide whether a setlist may come from the cache. Bound here rather than
    # only under --catch-up because every path reaches that loop.
    have = {}
    kw = {"cache_dir": args.cache_dir, "refresh": args.refresh}
    try:
        if args.catch_up:
            key = load_key(args.apikey)
            played = recent_shows(key, args.catch_up, artist=args.artist, **kw)
            have = {} if args.force else {r["date"]: r
                                          for r in saved_reports(args.site)}
            # Anything still unsettled is re-fetched every run, however often
            # that is; settled shows only when --recheck asks for corrections.
            recheck = {d for d in played if (have.get(d) or {}).get("provisional")}
            if args.recheck:
                cutoff = (_utcnow().date()
                          - datetime.timedelta(days=args.recheck)).isoformat()
                recheck |= {d for d in played if d >= cutoff and d in have}
            fresh = [d for d in played
                     if (d not in have or d in recheck) and d not in dates]
            log("catch-up: %d show%s played in the last %d days, " "%d new, %d re-fetched",
                len(played), "" if len(played) == 1 else "s", args.catch_up, len(fresh) - len(recheck), len(recheck))
            dates += fresh

        if args.from_json:
            with open(args.from_json, encoding="utf-8") as fh:
                reports.append(json.load(fh))
        for date in dates:
            if args.site and not args.force and date not in recheck:
                _, blob = site_paths(args.site, date)
                if os.path.exists(blob):
                    log("%s is already in the site (--force to re-fetch)", date)
                    continue
            key = key or load_key(args.apikey)   # not needed for --rebuild
            # A show that is not settled is still changing, so its setlist must
            # not come from the cache. The cache holds a response for six hours
            # and a watch job runs for five, so without this the first pass
            # froze the setlist and every pass after it republished that same
            # copy -- the watcher reporting 13 songs while phish.net had 16,
            # unable to ever see another.
            #
            # `recheck` covers a show archived while still provisional, and
            # the settled ones --recheck asks after. What it cannot cover is a
            # show with no report at all -- and that is the one that happens
            # every night. A window opens at 23:00 UTC and the first song of
            # an east coast show is posted around 23:30, so the watcher's
            # first pass reliably asks for a setlist that does not exist yet,
            # and the six-hour cache then serves that same emptiness back for
            # the rest of the show. Nothing is archived, so the show never
            # becomes provisional, so it never reaches `recheck`, so it never
            # earns a refresh: the one show being watched was the one show
            # that could never be seen.
            #
            # It cost the 2026-07-29 Madison Square Garden show, which sat
            # unarchived while --calendar had already counted it -- so every
            # song's figure moved up by one and the five actually played that
            # night never reset to zero.
            #
            # Only this call bypasses the cache; song histories and the
            # calendar stay cached, which is most of the traffic and none of
            # the volatility.
            unarchived = date not in have
            live = (dict(kw, refresh=True) if date in recheck or unarchived
                    else kw)
            setlist = []
            try:
                report = build(date, key, artist=args.artist,
                               rows_out=setlist, **live)
            except ApiError as exc:
                # A tour-length run should not die on tonight's show having no
                # setlist posted yet.
                if not args.site:
                    raise
                log("skipping %s: %s", date, exc)
                continue
            if args.previous:
                add_previous(report, key, site_dir=args.site, **kw)
            if args.site or args.html or args.pdf:
                add_ratings(report, **kw)
            # After add_previous, not before: the comparison counts how many
            # songs know their history, which is only true once it has run.
            prior = archived(args.site, date) if args.site else None
            if not is_fuller(report, prior):
                continue
            if args.site:
                settle(report, prior, _utcnow())
                # After settle(), because whether the show is still on decides
                # what may be written down; and only with --previous, because
                # without it the songs of a brand-new show have no archived
                # history for these to be written into.
                if args.previous:
                    record_neighbors(args.site, report["date"], setlist,
                                     artist=args.artist,
                                     settled=not report.get("provisional"))
                # Free, and for the same reason record_neighbors above is:
                # the setlist that built the report is already in hand, so the
                # running order costs no call. Without this the extract only
                # grew when somebody ran --seed-setlists by hand, so it lagged
                # by however many nights since -- and the whole point of it is
                # that a change to the neighbor rules re-walks every show for
                # nothing. A night it is missing is a night that costs a call.
                #
                # Settled shows only, which is the rule the extract has always
                # had: it is a cache with no expiry, so a show written down at
                # the 12 songs it had mid-performance would be believed at 12
                # songs forever. The first harvest did exactly that.
                if not report.get("provisional"):
                    kept = order_rows(setlist, args.artist)
                    if kept:
                        fresh_order[report["date"]] = kept
            reports.append(report)

        # After the fetch loop, so the file is written once however many shows
        # were caught up, and only when a date is genuinely new or has changed
        # -- a --catch-up that finds nothing new must not touch it, or every
        # run puts a fresh commit in the archive saying nothing.
        if fresh_order:
            order = setlist_order(args.site)
            changed = {d: r for d, r in fresh_order.items() if order.get(d) != r}
            if changed:
                order.update(changed)
                save_setlist_order(order, args.site)

        if args.seed_songs:
            # After the fetch loop, so anything new tonight is already archived
            # by add_previous and does not get asked for twice.
            key = key or load_key(args.apikey)
            seed_songs(args.site, key, artist=args.artist, force=args.force,
                       **kw)
        if args.sweep_ratings:
            sweep_ratings(args.site, days=args.sweep_ratings, **kw)
        if args.seed_setlists:
            # No key loaded here on purpose: the walk buys one only if the
            # archive turns out not to cover the dates it needs.
            seed_setlists(args.site, key or args.apikey, artist=args.artist,
                          force=args.force, **kw)
        if args.seed_songs or args.seed_scores:
            seed_scores(args.site,
                        songs=sorted(archived_songs(args.site))
                        if args.force and args.seed_scores else None, **kw)
        if args.remeasure:
            remeasure(args.site, artist=args.artist)
        if args.phishin:
            fetch_phishin(args.site, **kw)
        if args.schedule:
            key = key or load_key(args.apikey)
            fetch_schedule(args.site, key, artist=args.artist, **kw)
        if args.calendar is not None:
            # The current year alone on a scheduled run: earlier years cannot
            # gain shows, and a year that gains a correction is rare enough to
            # ask for by hand.
            key = key or load_key(args.apikey)
            first = args.calendar or _utcnow().date().year
            fetch_calendar(args.site, key, range(first, _utcnow().date().year + 1),
                           artist=args.artist, **kw)
    except ApiError as exc:
        sys.exit("error: %s" % exc)

    if args.site:
        write_site(args.site, reports, bar_scale=args.bar_scale,
                   rebuild=args.rebuild)
    elif reports:
        sys.stdout.write(render_text(reports[0]))

    if not (one_file and reports):
        return

    report = reports[0]
    if args.html or args.pdf:
        # No stylesheet beside a single file, so it carries the display face
        # itself -- but only on a show still being played, which is the only
        # page here with a rule that asks for it. See render_html.
        markup = render_html(report, bar_scale=args.bar_scale, sheet=None)
        if args.html:
            with open(args.html, "w", encoding="utf-8") as fh:
                fh.write(markup)
            log("wrote %s", args.html)
        if args.pdf:
            try:
                used = write_pdf(markup, args.pdf, prefer=args.pdf_backend,
                                 single_page=args.single_page)
            except ApiError as exc:
                sys.exit("error: %s" % exc)
            log("wrote %s (via %s)", args.pdf, used)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump(report, fh, indent=2)
        log("wrote %s", args.json)


if __name__ == "__main__":
    main()