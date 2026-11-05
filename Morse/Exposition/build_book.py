#!/usr/bin/env python3
"""Assemble the whole exposition into one web page: Exposition/morse-theory-rewritten.html.

Every chapter is converted by pandoc (TeX math left for MathJax, typeset lazily as it scrolls into
view), the interactive figures are inlined (each in its own function scope so their names cannot
collide), and a contents rail is generated from the chapter and section headings.

Usage: python3 build_book.py
"""
import html, math, os, re, subprocess

import checked_marks

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "morse-theory-rewritten.html")  # tracked, beside the other two web editions
PREVIEW = os.path.join(HERE, "preview-morse-theory-rewritten.html")  # gitignored

CHAPTERS = [  # (file, Milnor sections, book pages, part)
    ("Chapter1", "§§1–2", "pp. 1–12", "I"),
    ("Chapter2", "§3", "pp. 12–24", "I"),
    ("Chapter3", "§§4–5", "pp. 25–32", "I"),
    ("Chapter4", "§6", "pp. 32–38", "I"),
    ("Chapter5", "§7", "pp. 39–42", "I"),
    ("Chapter6", "§§8–9", "pp. 43–54", "II"),
    ("Chapter7", "§10", "pp. 55–66", "II"),
    ("Chapter8", "§§11–13", "pp. 67–76", "III"),
    ("Chapter9", "§§14–15", "pp. 77–87", "III"),
    ("Chapter10", "§§16–17", "pp. 88–97", "III"),
    ("Chapter11", "§§18–19", "pp. 98–108", "III"),
    ("Chapter12", "§§20–21", "pp. 109–117", "IV"),
    ("Chapter13", "§22", "pp. 118–123", "IV"),
    ("Chapter14", "§23", "pp. 124–132", "IV"),
    ("Chapter15", "§24", "pp. 133–148", "IV"),
    ("Appendix", "Appendix", "pp. 149–153", "A"),
]
PARTS = {
    "I": "Part I. Non-degenerate smooth functions on a manifold",
    "II": "Part II. A rapid course in Riemannian geometry",
    "III": "Part III. The calculus of variations applied to geodesics",
    "IV": "Part IV. Applications to Lie groups and symmetric spaces",
    "A": "Appendix",
}


def emblem_svg():
    """Level sets of f(x, y) = (x² − 1)² + y²: two wells, a saddle at the origin, and the
    figure-eight level through it (drawn in the accent colour)."""
    W, H, sx, sy, cx, cy = 300, 132, 92.0, 92.0, 150, 66

    def curves(c):
        # y = ±sqrt(c − (x² − 1)²) on the x-intervals where it is real
        paths, n = [], 600
        xs = [-1.75 + 3.5 * i / n for i in range(n + 1)]
        seg = []
        for x in xs:
            v = c - (x * x - 1) ** 2
            if v >= 0:
                seg.append((x, math.sqrt(v)))
            elif seg:
                paths.append(seg)
                seg = []
        if seg:
            paths.append(seg)
        out = []
        for s in paths:
            top = [(cx + sx * x, cy - sy * y) for x, y in s]
            bot = [(cx + sx * x, cy + sy * y) for x, y in reversed(s)]
            pts = top + bot
            out.append("M" + " L".join(f"{a:.1f},{b:.1f}" for a, b in pts) + " Z")
        return out

    levels = [0.06, 0.25, 0.55, 1.0, 1.6, 2.4]
    parts = []
    for c in levels:
        cls = "lv crit" if c == 1.0 else "lv"
        for d in curves(c):
            parts.append(f'<path class="{cls}" d="{d}"/>')
    dots = (f'<circle class="pt" cx="{cx - sx}" cy="{cy}" r="2.6"/>'
            f'<circle class="pt" cx="{cx + sx}" cy="{cy}" r="2.6"/>'
            f'<circle class="pt crit-pt" cx="{cx}" cy="{cy}" r="3"/>')
    return (f'<svg class="emblem" viewBox="0 0 {W} {H}" role="img" '
            f'aria-label="Level curves of a function with two minima and a saddle; the level curve '
            f'through the saddle is a figure eight.">' + "".join(parts) + dots + "</svg>")


def chapter_html(name, n):
    md = checked_marks.mark(name, open(os.path.join(HERE, name + ".md")).read())
    md = re.sub(r"\*\(In the printed version[^)]*\)\*\s*\n", "", md)
    md = re.sub(r"!\[[^\]]*\]\(fig[^)]+\.png\)\s*\n", "", md)
    r = subprocess.run(["pandoc", "-f", "markdown", "-t", "html5", "--mathjax",
                        "--shift-heading-level-by=1", "--wrap=none", f"--id-prefix=c{n}-"],
                       input=md, text=True, capture_output=True, check=True)
    # pandoc parses the figure <div> as a native Div and prefixes its id; the figure scripts look
    # for the unprefixed id, so restore it
    body = re.sub(rf'id="c{n}-([A-Za-z0-9_-]+-figure)"', r'id="\1"', r.stdout)
    pngs = re.findall(r"!\[[^\]]*\]\((fig[^)]+\.png)\)", open(os.path.join(HERE, name + ".md")).read())
    scripts = []
    for png in pngs:
        js = os.path.join(HERE, png[:-4] + ".js")
        if os.path.exists(js):
            scripts.append(f"/* {os.path.basename(js)} */\n(function () {{\n{open(js).read()}\n}})();")
    return body, scripts


def toc_entries(body):
    h2 = re.search(r'<h2 id="([^"]+)"[^>]*>(.*?)</h2>', body, re.S)
    secs = re.findall(r'<h3 id="([^"]+)"[^>]*>(.*?)</h3>', body, re.S)
    return h2, secs


def strip_tags(s):
    return re.sub(r"<[^>]+>", "", s).strip()


HEAD = r"""<title>Morse Theory, Rewritten</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Cormorant+Garamond:wght@500;600&family=IBM+Plex+Sans+Condensed:wght@400;500&family=STIX+Two+Text:ital,wght@0,400;0,600;1,400&display=swap">
<style>
/* Layout: a reading desk. A quiet contents rail on the left (sticky on wide screens, a fold-out
   at the top on phones) and one text column of about 66 characters; every chapter opens with a
   running label giving Milnor's section numbers and page range. */
:root {
  --bg: #f5f7f6;        /* cool paper, slight green bias */
  --fg: #1b2530;        /* ink */
  --muted: #5f6b75;     /* captions, rail, secondary text */
  --accent: #19657f;    /* contour blue: links, the critical level */
  --rule: #d6dcdb;      /* hairlines */
  --panel: #e9eeec;     /* asides */
  --display: "Cormorant Garamond", "Iowan Old Style", Palatino, Georgia, serif;
  --body: "STIX Two Text", "Iowan Old Style", Palatino, Georgia, serif;
  --ui: "IBM Plex Sans Condensed", "Avenir Next Condensed", "Helvetica Neue", Arial, sans-serif;
}
@media (prefers-color-scheme: dark) {
  :root:not([data-theme="light"]) {
    --bg: #121a20; --fg: #dbe3e7; --muted: #8e9ba5; --accent: #72bcd6; --rule: #27323a;
    --panel: #18232a; color-scheme: dark;
  }
}
:root[data-theme="dark"] {
  --bg: #121a20; --fg: #dbe3e7; --muted: #8e9ba5; --accent: #72bcd6; --rule: #27323a;
  --panel: #18232a; color-scheme: dark;
}
* { box-sizing: border-box; }
body { background: var(--bg); color: var(--fg); font: 400 1.0625rem/1.62 var(--body);
  margin: 0; padding-inline: 16px; padding-block: 0; }
.desk { max-width: 76rem; margin: 0 auto; display: grid; grid-template-columns: minmax(0, 1fr);
  gap: 2.5rem; }
@media (min-width: 1100px) { .desk { grid-template-columns: 16.5rem minmax(0, 1fr); } }
main { min-width: 0; max-width: 42rem; padding-block: 2rem 6rem; }
a { color: var(--accent); text-underline-offset: 0.15em; }
a:focus-visible, summary:focus-visible, button:focus-visible, input:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; }

/* masthead */
.mast { padding-block: 3rem 1.5rem; border-bottom: 1px solid var(--rule); display: grid; gap: 0.9rem; }
.mast .kicker { font: 500 0.78rem/1.3 var(--ui); letter-spacing: 0.08em; text-transform: uppercase; color: var(--muted); }
.mast h1 { font: 600 clamp(2.4rem, 6vw, 3.6rem)/1.02 var(--display); margin: 0; letter-spacing: -0.005em; text-wrap: balance; }
.mast .lede { font-size: 1.12rem; margin: 0; max-width: 36rem; text-wrap: pretty; }
.mast .meta { font: 400 0.86rem/1.5 var(--ui); color: var(--muted); margin: 0; }
.checked { font: 400 0.86rem/1.4 var(--ui); color: var(--muted); }
.emblem { width: min(100%, 300px); height: auto; display: block; }
.emblem .lv { fill: none; stroke: var(--muted); stroke-width: 0.9; opacity: 0.7; }
.emblem .crit { stroke: var(--accent); stroke-width: 1.6; opacity: 1; }
.emblem .pt { fill: var(--muted); }
.emblem .crit-pt { fill: var(--accent); }
.emblem-cap { font: 400 0.8rem/1.4 var(--ui); color: var(--muted); margin: -0.4rem 0 0; }

/* contents rail */
.rail { font: 400 0.9rem/1.35 var(--ui); color: var(--muted); }
@media (min-width: 1100px) {
  .rail { position: sticky; top: env(safe-area-inset-top, 0px); max-height: 100vh; overflow-y: auto;
    padding-block: 2rem; border-right: 1px solid var(--rule); padding-right: 1.25rem; }
  .rail details > summary { display: none; }
}
.rail summary { cursor: pointer; font-weight: 500; color: var(--fg); padding-block: 0.9rem;
  border-bottom: 1px solid var(--rule); list-style: none; }
.rail summary::-webkit-details-marker { display: none; }
.rail summary::after { content: " +"; color: var(--accent); }
.rail details[open] summary::after { content: " −"; }
.rail .part { font: 500 0.72rem/1.3 var(--ui); letter-spacing: 0.08em; text-transform: uppercase;
  color: var(--muted); margin: 1.2rem 0 0.4rem; }
.rail ol { list-style: none; margin: 0; padding: 0; display: grid; gap: 0.15rem; }
.rail li > a { display: block; padding: 0.22rem 0; color: var(--fg); text-decoration: none; }
.rail li > a:hover { color: var(--accent); }
.rail li > a .sec { color: var(--muted); font-variant-numeric: tabular-nums; margin-right: 0.35rem; }
.rail li.current > a { color: var(--accent); }

/* chapters */
article.chapter { padding-block: 3.5rem 1rem; border-bottom: 1px solid var(--rule); }
.runlabel { font: 500 0.78rem/1.3 var(--ui); letter-spacing: 0.08em; text-transform: uppercase;
  color: var(--muted); display: flex; flex-wrap: wrap; gap: 0.4rem 1rem; align-items: baseline; }
.runlabel a { color: var(--muted); text-decoration: none; margin-left: auto; letter-spacing: 0.04em; }
.runlabel a:hover { color: var(--accent); }
main h2 { font: 600 clamp(1.75rem, 3.6vw, 2.35rem)/1.1 var(--display); margin: 0.6rem 0 1.2rem; text-wrap: balance; }
main h3 { font: 600 1.28rem/1.3 var(--body); margin: 2.4rem 0 0.7rem; text-wrap: balance; }
main h4 { font: 600 1.06rem/1.35 var(--body); margin: 1.8rem 0 0.5rem; }
main p { margin: 0 0 1em; hyphens: auto; }
main hr { border: 0; border-top: 1px solid var(--rule); margin: 2rem 0; }
main blockquote { margin: 1.3rem 0; padding: 0.7rem 1rem; background: var(--panel); border-radius: 3px; }
main blockquote > :last-child { margin-bottom: 0; }
main ul, main ol { padding-left: 1.4rem; }
main table { border-collapse: collapse; display: block; overflow-x: auto; max-width: 100%;
  font: 400 0.9rem/1.45 var(--body); margin: 1.2rem 0; }
main th { font: 500 0.78rem/1.3 var(--ui); letter-spacing: 0.04em; text-transform: uppercase; color: var(--muted); text-align: left; }
main td, main th { border-bottom: 1px solid var(--rule); padding: 0.45rem 0.7rem 0.45rem 0; vertical-align: top; }
main code { font-size: 0.88em; }
mjx-container[display="true"] { overflow-x: auto; overflow-y: hidden; max-width: 100%; padding-block: 0.2rem; }
mjx-container.wide { display: inline-block; max-width: 100%; overflow-x: auto; overflow-y: hidden; vertical-align: middle; }
[id$="-figure"] { margin: 1.6rem 0; min-width: 0; }
.colophon { font: 400 0.86rem/1.55 var(--ui); color: var(--muted); padding-block: 2rem; }
@media (prefers-reduced-motion: reduce) { html { scroll-behavior: auto; } }
@media (prefers-reduced-motion: no-preference) { html { scroll-behavior: smooth; } }
</style>
<script>
window.MathJax = {
  loader: { load: ['ui/lazy'] },
  svg: { fontCache: 'global' },
  options: { lazyMargin: '600px' }
};
</script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.2/es5/tex-svg.js" defer></script>
"""


def main():
    rail_parts, articles, scripts = [], [], []
    current_part = None
    rail_items = []
    for n, (name, secs, pages, part) in enumerate(CHAPTERS, start=1):
        if not os.path.exists(os.path.join(HERE, name + ".md")):
            continue
        body, sc = chapter_html(name, n)
        scripts += sc
        h2, h3s = toc_entries(body)
        anchor = f"c{n}"
        title = strip_tags(h2.group(2)) if h2 else name
        short = re.sub(r"^(Chapter \d+|Appendix)\.\s*", "", title).split(":")[0]
        num = "A" if name == "Appendix" else str(n)
        if part != current_part:
            rail_items.append(f'<li class="part" aria-hidden="true">{html.escape(PARTS[part])}</li>')
            current_part = part
        rail_items.append(f'<li data-for="{anchor}"><a href="#{anchor}"><span class="sec">{num}</span>{short}</a></li>')
        label = (f'<div class="runlabel"><span>{"Appendix" if name == "Appendix" else f"Chapter {n}"}</span>'
                 f'<span>Milnor {secs}</span><span>{pages}</span><a href="#contents">Contents ↑</a></div>')
        articles.append(f'<article class="chapter" id="{anchor}">{label}\n{body}\n</article>')

    rail = ('<nav class="rail" id="contents" aria-label="Contents"><details open><summary>Contents</summary>'
            '<ol>' + "".join(rail_items) + '</ol></details></nav>')

    mast = f"""<header class="mast">
<div class="kicker">J. Milnor, <i>Morse Theory</i> (Princeton, 1963), rewritten</div>
<h1>Morse Theory, Rewritten</h1>
<p class="lede">All twenty-four sections and the appendix of Milnor's book, with every proof given in
full, every silently assumed hypothesis made explicit, an interactive figure in each chapter, and
an application in each chapter: the equilibria of a double pendulum, the conformers of a two-rotor
molecule, echoes in an oval room, Foucault's pendulum, the ringing of the Earth after a great
earthquake, and how many independent directions can be combed on a sphere.</p>
{emblem_svg()}
<p class="emblem-cap">Level curves of (x² − 1)² + y². The curve through the saddle, in colour, is
where the sublevel set changes its topology: two discs become one.</p>
<p class="meta">Companion to the rewritten <i>Topology from the Differentiable Viewpoint</i>, cited
here as the companion volume. Each numbered result says whether it has been checked by machine,
with its number in the verified edition, and each chapter ends with what was checked. Edition of {__import__('datetime').date.today():%-d %B %Y}.</p>
</header>"""

    js_fit = """
(function () {
  /* MathJax 3 does not break long inline formulas; let one that is wider than its line scroll
     inside itself instead of pushing past the column. Checked as each formula is typeset. */
  var main = document.querySelector('main');
  if (!main || !('MutationObserver' in window)) return;
  function fit(c) {
    if (!c || c.getAttribute('display') === 'true' || !c.parentElement) return;
    if (c.getBoundingClientRect().width > c.parentElement.getBoundingClientRect().width + 1) c.classList.add('wide');
  }
  new MutationObserver(function (recs) {
    recs.forEach(function (r) {
      var t = r.target.nodeType === 1 ? r.target : r.target.parentElement;
      var c = t && t.closest ? t.closest('mjx-container') : null;
      if (c) fit(c);
    });
  }).observe(main, { childList: true, subtree: true });
})();"""
    js_rail = """
(function () {
  var rail = document.getElementById('contents');
  var det = rail && rail.querySelector('details');
  var mq = window.matchMedia('(min-width: 1100px)');
  function sync() { if (det) det.open = mq.matches ? true : det.open; }
  if (mq.addEventListener) mq.addEventListener('change', sync); sync();
  if (det && !mq.matches) det.open = false;
  var items = Array.prototype.slice.call(document.querySelectorAll('.rail li[data-for]'));
  var map = {};
  items.forEach(function (li) { map[li.getAttribute('data-for')] = li; });
  if (!('IntersectionObserver' in window)) return;
  var io = new IntersectionObserver(function (entries) {
    entries.forEach(function (e) {
      if (e.isIntersecting) {
        items.forEach(function (li) { li.classList.remove('current'); });
        var li = map[e.target.id]; if (li) li.classList.add('current');
      }
    });
  }, { rootMargin: '-40% 0px -55% 0px' });
  document.querySelectorAll('article.chapter').forEach(function (a) { io.observe(a); });
})();"""

    page = (HEAD + '<div class="desk">' + rail + '<main>' + mast + "\n".join(articles) +
            '<footer class="colophon">Built from the Markdown sources in <code>Exposition/</code> of the '
            'Morse project. Figures are drawn in your browser; the printed edition has still images.</footer>'
            '</main></div>\n<script>\n' + "\n".join(scripts) + js_rail + js_fit + "\n</script>\n")
    open(OUT, "w").write(page)
    # local preview copy with the skeleton the publisher adds (doctype, charset, viewport)
    open(PREVIEW, "w").write(
        '<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" '
        'content="width=device-width, initial-scale=1, viewport-fit=cover"></head><body>' + page +
        "</body></html>")
    print(f"{os.path.basename(OUT)}: {len(page) / 1e6:.2f} MB, {len(articles)} chapters, {len(scripts)} figures")


if __name__ == "__main__":
    main()
