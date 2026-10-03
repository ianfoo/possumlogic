# possumlogic

One Python file (`possumlogic.py`) builds a static site from the phish.net API
and publishes it to <https://possumlogic.com> from the `gh-pages` branch. The
README covers what it does; `docs/TODO.md` opens with a §0 handoff block
holding current state and the work queue.

```bash
./possumlogic.py --site site --rebuild   # re-render everything from the local archive; no API calls, ~2s
./possumlogic.py --site site --watching  # is a show inside its watch window now?
```

Serve the built site with the `site` entry in `.claude/launch.json`, not over
`file://` — `history.pushState` and other same-origin APIs behave differently
there, which makes local verification lie.

## Gotchas

**There are still three base stylesheets, but what they share is now named.**
`CSS` (show pages), `INDEX_CSS` and `SONG_CSS`; `SONGS_CSS`, `METHOD_CSS`,
`FAQ_CSS`, `DORMANT_CSS` and `YEARS_CSS` extend `INDEX_CSS`. The rules that
were identical in all three live in `BASE_CSS`, `BODY_BOX_CSS`, `NAV_CSS`,
`RULE2_CSS`, `FIGURE_CSS`, `FOOTER_BOX_CSS`, `FOOTER_LINK_CSS`, `TOTOP_CSS`
and `CARD_LINK_CSS` — edit those once. (`DEK_CSS` is the same idea across two
of the three, not all three.) `CARD_LINK_CSS` was named on 2026-07-30 the
moment a third sheet wanted a linked hero card, rather than after: it holds
the three rules that do not depend on where the card goes, and deliberately
leaves out the fourth, which carries the arrow — the index points right
because the card leaves the page, the show and song sheets point down because
it lands further down this one. `YEAR_STRIP_CSS` is the year strip; it was
named when a second page wanted it and is back to one caller, because the
dormant page was regrouped into three sections and dropped its strip.
`NAV_CSS` is the whole nav strip and replaced `NAV_HIT_CSS`: the four
near-identical `.crumb{…}` rules are gone, and the show sheet keeps only what
is genuinely its own — the pager row and a margin. **The markup is one
function too**, `nav_strip()`, after ten hand-written copies left every show
and song page — 1,302 of 1,310 — marking no current location at all while the
other eight marked themselves. A nav in ten copies is ten chances to be
inconsistent about the one thing a nav must be right about, and the tenth
arrived on `main` while the ninth was being removed on a branch. **The strip
is four destinations**, and it is four on purpose: Due, Out of rotation and
Not a show are questions asked *about* the archive rather than ways into it,
so each hangs off the parent that owns it as a hero card and marks that
parent as its section. Adding a fifth is a decision about the whole strip's
width rather than a one-line edit — at 390px one line holds 336px and the
four spines use 219px of it. **Taking one out is the riskier edit**: it can
strand a page while every link on the site still resolves, so assert that
anything off the strip still has a door from a page on it.
**Everything else is still copied**: 32–46 rules repeat pairwise, and the
near-miss `.hero{…}` (flex in one sheet, grid in another) differs by a real
amount. `footer{…}` was listed with them and had stopped differing: measured
2026-07-30 its three copies were identical once whitespace was normalized, so
it was hoisted into `FOOTER_BOX_CSS`. **The stale note is the lesson** — it
told several sessions to leave a pure triplicate alone, and a wrong constraint
in a doc gets obeyed.
So a plain string replace on any rule
outside a named block will still hit two or three sheets, or — worse — one.
Anchor on a neighboring line that differs and assert the match count. Five
bugs have come out of the copies: a nav that could not wrap, a footer link in
the browser's default blue, a sticky-header hide out-specified by a modifier
class, tabular figures on show pages only, and — 2026-07-30, caught by
measurement before it shipped — a `.crumb{gap:.35rem}` in the show sheet's
narrow media query, written when both nav strips wanted the same geometry,
which out-specified the shared row gap the moment the strip got 44px tap
targets and left four overlapping targets on show pages and nowhere else.
**The check that found it is the one to reuse**: walk every page type at every
breakpoint and assert no two tap targets overlap, rather than looking at one
page and calling it done. `docs/TODO.md` §8e.
`TOTOP_CSS` was named when the floating back-to-top control went from one
sheet to all of them. **The markup had the same problem**: five functions
built the hero cards from five copies of the same two lines, three escaping
the href and two not. `hero_html` is the one copy now, and `hero_cols` beside
it is the pattern — the builder *states* what the CSS needs to know (how many
columns, which card carries a name) rather than the CSS inferring it, because
an inference like `:has(.of)` fails silent. The outbound chips were the same
shape in two copies and are now `_badge`, which is also the one place the href
is escaped. **The footer is `footer_html()`**
for the same reason as the nav — it was eleven copies in eleven shells, and
adding one cell to it would have been eleven chances to miss a page. It also
reserves a lane at the page bottom for the floating back-to-top: `.totop` is
fixed to the viewport's bottom right, so the footer's last row is the one
piece of content it is guaranteed to cover, and a fourth cell put a 65×26px
control under it. Reserve the lane rather than move the victim; the sweep
found a second one at 768px.

**`.prose p` beats a bare class, and two rules have lost to it.** `.prose p`
is one class and one type, so any single-class rule styling a `<p>` inside the
prose loses outright — order cannot help, because the two are not equal.
`.backtop` was found this way; `.src` had *never once been drawn* since the
FAQ's segues answer was written, rendering as an ordinary body paragraph. Both
are `X,.prose X` now. **Check any single-class rule that styles a `<p>` inside
`.prose`, and check it by reading the computed style off the built page** —
and reload past the cache first: this was measured as still-broken once,
against a page the browser had kept.

**A chip out to another site needs its slug measured, not assumed.**
`foul_song_slug` derives fouldomain's slug from the song's *title*, because
phish.net's slug — what every other identifier here keys on — lands on
fouldomain's "Song Not Found" for 13 of the 589 songs: punctuation phish.net
drops and fouldomain keeps as a separator (`acdc-bag` against `ac-dc-bag`),
disambiguation suffixes fouldomain has no need of (`gloria-branigan`,
`invisible-2`), and one slug with an `<em>` baked into it,
`theme-from-emnew-york-new-yorkem`. An apostrophe is *dropped* rather than
separated on, and a first pass that got that one detail wrong broke 24 more
songs while still looking like an improvement. **Check the whole set against
the live site, and check identity rather than existence** — nine of their
pages answer with a `<title>` of `1993 · 6:16`, so "not a 404" proves nothing;
`og:title` names the song, and all 589 chips were confirmed to land on a page
naming this song exactly. One page carries no fouldomain chip — `custom`,
where phish.net files one-off and unlisted titles and this archive shows the
page as Dog Log because Dog Log is one of the nine, so a title match would
have claimed the other eight were versions of it. `TITLE_NOT_THE_ENTRY` is
that gate, and the first version of it was `NOT_A_SONG`, which was **too wide
by one**: `jam` is equally not a composition, but its title names the bucket
rather than one of the things in it and fouldomain files unnamed improvisation
under the same word. The test is whether a title match lands on the same set,
not whether the page is a song.

**A debut carries a "gap" that is not a gap, and skipping row 0 does not
always skip it.** phish.net gives a song's first counted performance a gap
equal to every show the band had played before it — 2,022 for What's Going
Through Your Mind. That is the band's history length, not a silence. The site
drops it by ignoring each song's first row, which is right for 473 of the 518
debuts and wrong for the other 45: those songs first appeared at a date
phish.net does not count toward gaps (Festival 8's 2009-10-29, 1997-06-06,
1999-06-24, 1995-05-14 and a dozen more), the archive keeps that appearance as
row 0, and the debut gap lands on row 1 where "skip the first row" cannot
reach it. **Filter to counted performances first, then drop the first** —
`due_rows` and `render_song` have always done it in that order; `render_songs`
and `songs_card` did not, and published 42 wrong longest gaps. Fixed, and the
whole songs index counts shows now: 127 songs had a "shows" figure that
included soundchecks, so the index and the song page one click away disagreed
about 127 songs. **A page that summarizes other pages must count the way they
do** — the check that found it was reading both. `docs/TODO.md` §2k.

**Every gap is counted here, off the calendar — phish.net's is never shown.**
A gap is the counting shows strictly *between* two performances, 0 for
back-to-back nights; `true_gaps` computes it, and `song_history` and
`_finish_song` apply it, so the figure phish.net sent stays on disk unread.
This replaced a note that said phish.net's gaps were sound and not to go
looking. Measured on 2026-10-03 across 36,466 performance pairs, phish.net's
figure was one *higher* than the shows between on 28,206, equal on 7,562 and
higher still on 683 — a mix by song and era, so no constant offset fixes it —
and sometime after 2026-09-07 it renumbered published rows (Tweezer's
2026-09-05 went from 1 to 2) with no new API version. It also files 0 for a
song entered mid-show and leaves it for hours. The FAQ had always defined a gap
as shows between, with 0 for the next night, and said the number came from
phish.net: the definition was right and three printed figures in four did not
meet it. Ian caught it from one row he knew by heart. **A definition is only
true of the data if something checks the data against it.** The same night,
another session read phish.net's new scale off the API and rewrote `_gap`'s
docstring to say a gap "cannot be below 1" — and this session then quoted that
docstring to Ian as fact. A two-hour-old comment is still just a claim.

**But a 0 is not a gap, and phish.net revises.** That check only asked whether
a gap was too *large*. phish.net also files 0 (debuts since its September 2026
revision, same-night repeats, and songs entered during a show it has not
measured yet), and a 0 is a fine number to every comparison: on 2026-10-02 the
show page printed Mercury at "Gap 0 · premature", fourteen shows after it was
last played. `_gap` returns None below 1 and `song_history` applies it on read.
The same month phish.net shifted most gaps up by one, and a history is only
re-fetched when its song is played again, so the archive holds old figures for
most songs and new ones for the rest. Dispatch `possumlogic.yml` with `reseed`
to re-read them all. **And "N in 10 yr" counts plays, not gaps**: it was the
length of the gap list, which leaves the debut out, so every second performance
read "0 in 10 yr".

**A `hidden` attribute loses to any author `display`.** The browser hides
`[hidden]` with a *user-agent* rule, and a user-agent rule loses to an author
declaration outright — specificity does not enter into it. `.totop` declared
`display:flex`, so `hidden` did nothing, and the back-to-top button sat on
every song page permanently, pinned over the header it exists to replace, from
the day it shipped. The script had been setting `.hidden` correctly the whole
time. **Prove the state you are claiming, not its opposite**: every screenshot
of that button showed it working. `docs/TODO.md` §2k.

**A stamp that reverses on hover can lose its text to a plainer rule, and you
cannot see it in the source.** The Jam chart chip hovered to `var(--hot)` on a
`var(--hot)` fill — 1.00:1, a solid red block where a word had been — because
`a.jc-chip:hover` is 0-2-1 and `td.song a:hover`, further down the same sheet,
is 0-2-2. What made it look handled was the dead half of the chip's own
selector: `td.song a:hover .jc-chip` had never matched anything, because the
chip is a *sibling* of the title link, not a descendant. **The fifth instance
of a modifier class losing to a descendant selector**, after the sticky-header
hide, `.backtop` and `.live span`. The same shape was live in `.onstage`: its
hover repaint named three children and missed a fourth, leaving "songs so far"
at 1.12:1 / 1.08:1 — on the banner that appears *only* while a show is being
played, so no amount of browsing the archive could turn it up. **A list of
children is a list a fourth child is not on.** Beware the obvious cure:
`.onstage:hover *` does not work, because `*` contributes nothing to
specificity, so at 0-2-0 it still loses to `.onstage .n b` at 0-2-1. Repeat
the class instead.

None of this is visible in the CSS, in a resting screenshot, or to anything
that reads the source — the cascade has to be resolved *in the state*.
`tools/contrast_audit.html` does that for every colour, state, palette and
layout, and the `audit` entry in `.claude/launch.json` serves it. Run it after
touching a palette token, a `:hover`/`:focus` rule, or any selector that could
out-specify one. It caught both bugs above, and then caught the first fix for
the second one being wrong. `docs/TODO.md` §8j.

**`--hot` is the display accent and `--hot-text` is everything else.** The
brighter one reads 4.44:1 on paper — fine against a 40px figure, under the
floor for the 10–22px text it had spread to. As of 2026-07-30 the only places
still allowed to use `--hot` for *text* are `.num.hot`, `h1 em` and
`.card.since.over .num`; 31 other sites were moved, along with the
`border-bottom-color` in the same hover rules so a hovered link is one colour.
Backgrounds, focus rings and the `.bar` marks are non-text and stay `--hot`.
Watch for the other half of this: `--dim` is 4.98:1 on bare paper and fails on
anything tinted — `.toc a::before` sat on the index panel's `--rule-soft` wash
at 4.13:1 light and 4.49:1 dark. **A token that passes on paper has not been
checked until it is checked on the thing it actually sits on.**

**The paper texture is on now, and `getComputedStyle` cannot see it.** The
grain was generated, published, linked and *never painted* for its entire life,
because `BODY_BOX_CSS` set the `background` shorthand one link after the sheet
set `background-image`, and the shorthand resets it. Nothing caught that: the
page is the right colour either way, just flat. Two more things were wrong
underneath. `multiply` on cream and `screen` on near-black against a mid-grey
tile are not a texture but a dimmer -- measured, they moved the light paper
-20.8% and the dark paper +216% -- so the blend is `soft-light`, which is the
identity at mid-grey and leaves the mean exactly where it was. And one tile
cannot serve both palettes, because soft-light's swing depends on how far the
backdrop sits from the extremes: the same band read sd(L*) 0.30 on cream and
1.31 on near-black. `write_grain` now solves each palette its own spread from
one perceptual target, `GRAIN_TARGET_DL`.
**`tools/contrast_audit.html` is structurally blind to all of this** -- it reads
`getComputedStyle().backgroundColor`, which returns the token, not the
composite. `tools/check_paper.py` shoots the built pages headless and measures
the painted pixels: the mean must stay within 2 levels of the palette's paper,
and the texture must actually be there. Run it after touching the grain, the
palette's paper, or anything that sets `background` on `body`.

**And a clean sweep is true of the tree it ran on and nothing else.** Merging
`main` into a branch that had just cleared the whole site brought nine fresh
`color:var(--hot)` sites on small text — `.show a`, `.crumb a.sect`,
`details.how > summary`, `.aside a`, `.ax-note a`, `.years a`, `.yh .up`,
`.chips a` — plus two page types the audit had never opened. None of it
conflicted; git had no reason to flag any of it. **Re-run the audit after a
merge, not just after your own edits**, and when you add a page, add it to
`PAGES` in `tools/contrast_audit.html` in the same change — a page type missing
from that list is a page type nothing checks, and the report still says "Pass."

**A filled red stamp of reversed 10px caps is the bustout's costume, and only
the bustout's.** It is the headline of a show, struck twice and set two degrees
off true so it cannot be mistaken for anything else. The Jam chart chip had
always been *specified* to reverse into the same fill on hover — but the text
was being overpainted the colour of the fill, so what shipped was a featureless
block and nobody could see the collision. Fixing the contrast is what made it
visible; Ian caught it in the very next screenshot. The chip reverses to
`--ink` now (15.51:1 / 14.92:1), which is already the site's way of saying
"this is a state, not a claim" — `.yr h2 .tab` and the tooltip do the same.
**A bug can be hiding a design decision, so look at what the fix reveals, not
just at whether the number went up.**

**Drawing preview cards locally poisons CI.** `site/data/cards.json` records
what each card was drawn from and is tracked; `site/card/*.png` is gitignored.
So a local `--rebuild` draws the images here, writes "already drawn" into a
file that ships, and CI then restores the *published* PNGs, sees an index
claiming everything is current, and draws nothing. The markup updates and the
images do not. **This is the fourth instance of the shape below** — a record
that outlives the work it records. Check the published PNG, not the log line.
If you must draw locally to see a change, `git checkout HEAD -- site/data/cards.json`
before committing: an index that says "stale" is true of the published images
and makes CI redraw, where a fresh one silently freezes them.

**And the card index was keyed on only part of what draws a card.**
`card_print` hashed markup + `CARD_CSS` but not `CARDS_SHELL`, so the three
days when `{sheet}` was printed literally across the top of every batch's first
card — 14 published PNGs, `index.png` and `due.png` among them — never
invalidated anything: all 1,301 recorded hashes matched the code that was
producing the broken images. The same omission had every card drawn in Georgia
and system mono, because the shell is where the font links live. `CARDS_SHELL`
is hashed now, and `CARD_REVISION` is a hand-bumped integer for what no hash of
the inputs can see. **A cache key must cover the whole pipeline; when you fix a
renderer, ask what invalidates the render.** `docs/TODO.md` §8i.

**And the fifth: `nb` on a performance meant "we asked", not "we know".**
`setlist_neighbors` returned an entry only for songs that *had* a neighbor,
and the caller then stamped `nb=1` on every song of that date. So "the setlist
we fetched did not mention this song" was written down identically to "this
song genuinely opened its set" — and `nb` is what keeps a date from being
asked again, so the guess became permanent. It emptied the Before / after
column on 758 performances across 601 dates, concentrated in songs that have
almost never been played without a neighbor: the Sloth 107 of 177, Colonel
Forbin's Ascent 75 of 130, Fly Famous Mockingbird 74 of 131 — a song whose
every performance follows Colonel Forbin's, showing nothing. Fixed by having
the extractor report every song it *saw*, empty entry included. **When a flag
means "handled", check what it does when the answer was unavailable rather
than absent.**

**And the sixth, in the same flag: the migration that created it deleted the
record it replaced before writing its own.** `nb` took over from a central
`site/data/neighbors.json` listing walked dates. The migration block sets `nb`
in memory, calls `os.remove(index)` immediately, then writes files only via
`flush()` — which writes only the slugs the *fetch loop* queued. Every song that
run did not re-fetch lost its record permanently; an empty `todo` would have
returned before writing anything. Measured cost: 28,264 performances carry
neighbor data but only 18,292 carry the flag, and 10,718 of the difference sit
on dates the deleted index had recorded as walked. Only ~78 performances in the
archive were genuinely never asked. **Do not delete the old record until the new
one is on disk** — and the block is still there, unreachable but loaded, so
`docs/TODO.md` §0 argues for removing it.

**And the seventh, caught before it shipped: a carry-forward list in another
function.** `save_song_history` rewrites a song's history from the API, and the
neighbor fields are in no such response, so it copies them across by name —
through a hardcoded tuple of four key names, in a function nobody editing the
neighbor walk would think to open. Adding four new fields to the walk would
have dropped every one of them on the next `--previous` run. The list is now
one constant, `NB_CARRY`, sitting beside the walk that produces it. **When you
add a field, grep for the list that copies fields.**

**`site/data/setlist-order.jsonl` makes a re-walk free, and is a cache with no
expiry at all.** It holds the running order of every settled show, so changing
the neighbor rules and re-walking all 2,009 of them cost 44 API calls rather
than 2,009, and needs no API key. But the first harvest ran *during* a show and
wrote down that show at the 12 songs it had at the time. Reading that back
would have frozen the running order of the one show still moving — the six-hour
cache bug again, minus the six hours. So `--seed-setlists` always re-fetches a
show whose report is still `provisional`, and neither writer records one: its
order is partial by definition, and the day it settles a partial record stops
being skipped and starts being believed. **An extract of a live source needs
the same staleness rules as the cache it replaced.** `--catch-up` writes it too
as of 2026-07-31, because the setlist that built the report is already in hand
and the order costs no extra call — the same argument that already had
`record_neighbors` writing the derived neighbors at fetch time.

**And the cost model that kept it un-automated was invented, not measured.**
The README here said a nightly append would add a fresh 3.4 MB blob to git
history every day, and gave that as the reason CI must not maintain the file.
Git stores the delta: thirty nightly appends measured 13.0 KiB on the wire and
16 KiB of pack growth, about **500 bytes per show**. The 3.4 MB is the loose
object before `git gc`, which is not what ends up in history or on the wire.
The wrong number came from an earlier session of mine, went into a doc as a
justification, and was then reasoned from twice. **Measure a storage cost
before designing around it** — and see the note above about stale constraints
in docs getting obeyed. Sharding was measured at the same time: by year it is a
wash, and by song — the intuitive fix, since a show only touches the songs it
played — it is *fourteen times worse*, because small blobs do not delta and
each night adds a new tree over a 981-entry directory. `docs/setlist-order.md` has
the table.

**Measures are in `rem`, and one place was missed for a year.** `.wrap` is
`max-width:60rem` precisely so it travels with the type scale, and the comment
there says so. `.stuck .in` kept the literal `960px`, so when the scale went up
a step the content grew to 1080px and the sticky bar held still — putting every
column label 60px off the column it names. It read as a *content* bug: a long
note in the venue cell appeared to run past the "Before / after" label while
never touching that column. Before believing a cell overflows, measure the
header against the row.

**Every API response is on disk for six hours — count the cache before quoting
a cost.** `DEFAULT_CACHE` is `~/.cache/phishgap`, `CACHE_TTL` is 6h. A job that
looks like a thousand calls is often zero. On 2026-07-29 a re-seed of 1,966
setlists was quoted at "1,298 calls, ~13 minutes" twenty minutes after those
exact responses had been fetched and cached — the real cost was nothing.
The TTL also runs the other way: it is a **deadline on data already paid for**,
so if a pending change will need something a run just fetched, copy it out of
the cache before it expires rather than planning to re-fetch. Knowing the cache
exists is not the same as remembering it while costing work.

**`body` is IBM Plex Mono site-wide.** Literata is loaded and applied
deliberately to running prose (`.jam`, `.note`, `.prose`). Mono prose anywhere
else is usually an artifact of that default rather than a decision.
**Bagnard ships at weight 400 and nothing else**, so `<b>` around it draws a
synthetic bold — the colophon on `acknowledgments.html` sets each typeface's
name in its own face and uses classes rather than `<b>` for that reason.

**American spellings, and the exceptions are somebody else's words.** Ian is
American and never asked for the other kind; it accumulated across sessions
until a pass on 2026-07-31 rewrote it. The exceptions in the *built* pages are
not ours to change: the 157 "Centre"s are phish.net's venue names and the
"organism"s are their jam-chart prose. "Catalogue" is a house habit in four
places. The last one standing was `aria-label='Colour theme'`, on all 1,311
pages, and it lasted because it is read aloud rather than seen — **scan
reader-visible text *and* the aria/title/alt attributes of the built site, not
the source.**

**The running order is `(showid, position)`, not `(SET_ORDER, position)`, and
"the show" is the performance rather than the date.** phish.net files a
festival secret set *after* the encore — the IT Tower Jam is set 4 at position
27, behind an encore ending at 26 — and `SET_ORDER` puts `"4"` before `"e"`, so
six shows had their secret set moved in front of the encore and the wrong song
credited with closing the night. **Mondegreen's Woodlands Jam is filed as set
3**, so special-casing `"4"` would have missed the newest one. Sorting on
`position` alone breaks a different ten: those dates hold two performances,
each numbered from 1, and interleave. `showid` is the discriminator, and the
neighbor walk uses it too — before this, *Buried Alive* opening the Beacon
Theatre was recorded as following a song played hours earlier in a WNEW radio
studio. 92 performances across 17 dates were wrong. Ian found it by naming a
counterexample from memory, which is worth more here than any sweep: the bug
lived entirely in six festivals and ten double-headers, so every aggregate
check averaged it away. **The backfill cost zero API calls** — all 39,774 rows
found their `showid` in the six-hour cache on disk, which still held every
date. Count the cache first.

**Actions runtime: measure jobs, not runs — `created_at` to `updated_at` counts
time a run spent queued.** The two workflows serialize through concurrency
groups, so a cron firing mid-show sits *pending* and is superseded rather than
executed. Those runs report a `conclusion` of `cancelled` and a multi-hour span
that is entirely queue. Measured from run metadata, the watcher looked like
17.2 hours over five days; measured from `actions/runs/<id>/jobs`, which gives
real `started_at`/`completed_at`, it is **12.9 hours**, and one show night is
5.4–7.4 hours rather than the 11.6 the run spans implied. `run_duration_ms`
from the timing endpoint does *not* fix this — it agrees with the wrong number.
Ian caught this by disbelieving the total: 25 runs against three shows.
**The repo is public, so Actions is free and unlimited** — but if it ever goes
private, the Free tier is 2,000 minutes a month and the watcher alone is about
45 hours for seven shows, which is the whole allowance twice over.

**The same measurement showed the handoff already works.** On 2026-07-29 the
second shift started **three seconds** after the first exited, because the
queued run was standing by. Mid-show succession was never the fragile part;
*initial start* is, and the watcher's cron fires 13% of the time it is
scheduled to. Hence the sentinel in `possumlogic.yml`, which dispatches
`watch.yml` when a show is on and no watcher is up — `workflow_dispatch` is not
a scheduled event and is not throttled.

**A watcher that only watches the window runs long after the show ends — but
the page's "settled" is not the watcher's "safe to leave".** The loop's exit
test was `watching()`, which asks about the 7h30m window, so a show that ended
at midnight held a runner until half past two. The obvious fix is to exit on
`provisional`, and it is wrong: `settle()` releases the page **half an hour**
after an encore is recorded, which is right for a label the next pass can take
back and wrong for the watcher, because the watcher leaving is what stops the
next pass. Ian, who has been to them: six and seven song encores exist and run
close to an hour. Songs arriving keep resetting `count_since`, so a long encore
does not trip it by itself — but phish.net posting the first encore song and
then straggling past thirty minutes is ordinary, and that is enough. So
`released()` measures stillness directly against the full `QUIET_HOURS` and
ignores the encore shortcut, costing about an hour of runner time and still
exiting hours before the window closes. **When you make a display heuristic
load-bearing for control flow, re-derive its safety margin** — 30 minutes was
tuned for how long a reader should see "still coming in", not for how long a
show can surprise you. `--watching` prints `released=` now. Adding that second line nearly
broke the gate: all three callers parsed the output with a bare `cut -d= -f2`,
which turns two lines into `"false\nfalse"` — never equal to `"true"`, so the
gate would have failed closed and the watcher would silently never run again.
**When a command's stdout is a machine contract, adding a line is a breaking
change**; the callers `grep '^watching='` first.

**Anything long-running must re-read its inputs each pass.** Three separate
outages have had one shape — a job that publishes from something it read once:
a swallowed rebase conflict published a site missing the show it was watching;
a six-hour HTTP cache served one watcher the same setlist for five hours; a
resident watcher republished the whole site from its startup commit every five
minutes, reverting everything pushed during a show; and a card index that said
588 previews were current while the published images were a build behind.
Assume a fifth exists.

**The fifth existed, and the cure had a hole in exactly the shape of the
common case.** The six-hour cache above was fixed by refreshing the setlist of
any show in `recheck` — archived but still provisional. A show with no report
yet is not in `recheck`, and that is every show on the night it is played: the
window opens at 23:00 UTC, the first song is posted around 23:30, so the
watcher's first pass asks for a setlist that does not exist and then serves
that emptiness back for six hours. Nothing archived means never provisional,
means never rechecked, means never refreshed — the one show being watched was
the one show that could never be seen. It cost the whole first hour of
2026-07-29 at MSG, live, and it had been latent every night since the original
fix. When fixing a cache-staleness bug, check the bootstrap case: the first
fetch is the one guaranteed to be too early.

**The sixth was on the client, and it was the page itself.** The live show page
carried `<meta http-equiv="refresh" content="120">` — present, well-formed,
correctly placed, and never once firing: Pages sends `max-age=600`, so a reload
inside ten minutes can be answered from the browser's own cache with the same
document, and browsers throttle meta refresh in background tabs for as long as
they like. A page that reloads on a timer is a long-running job that publishes
from something it read once. It now polls the report JSON with a changing query
string, which puts each request on its own CDN cache key, and reloads only when
the song count actually moves. **Any reload-on-a-timer needs a changing URL, or
it is asking the cache whether the cache has changed.**

**A show can be counted before its setlist is known, and then every figure is
wrong.** `--calendar` builds the counting calendar from phish.net's show list,
so it adds tonight's show the moment the API lists it — while `--catch-up`
fetches the setlist separately and may fail. On 2026-07-29 that combination
advanced `current.json` to `as_of: 2026-07-29`, `shows: 2108`, and moved all
588 songs up by one, with none of the six actually played reset to zero. The
root cause above is fixed, so the window is now one pass rather than a whole
show — but the two steps are still independent, and a wrong figure is worse
than a missing one. `docs/TODO.md` carries this as open.

**Re-check the assumptions written here before designing against one.** The
`--html` output was documented as needing to stay self-contained long after
that stopped being a goal — and it was never self-contained anyway: it links
Google Fonts for the two faces that set nearly all the text, and inlines only
the display face. A stale constraint in a doc is more expensive than a missing
one, because it gets obeyed.

**GitHub Pages serves `cache-control: max-age=600`.** `curl` of the live site
can be ten minutes stale and look exactly like a failed publish. `git fetch
origin gh-pages && git show origin/gh-pages:<path>` is the ground truth for
what was actually published.

**This is a reference archive, so a wrong figure is worse than a missing one.**
Where the data will not support a claim, the site says nothing — the 35 shows filed as "Not Part of a Tour" stay
unnamed because their festival names exist only in freeform prose.

## Verifying a change

Claims about this site have been wrong in every session so far, in the same
few ways. Before reporting that a site change works, use the `verify-site`
skill in `.claude/skills/`.
