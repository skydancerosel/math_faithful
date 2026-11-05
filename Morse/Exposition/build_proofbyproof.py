"""Build the prose edition of "Morse Theory, proof by proof" (Exposition/ProofByProof.md).

Usage: python3 Exposition/build_proofbyproof.py [outdir] [--no-pdf] [--no-html]

Every trace tag ⟦Path/File · declName⟧ in the source is resolved against the Lean sources with
Exposition/check_trace.py; an unresolved tag stops the build. Then two editions are written
(default: into Exposition/):

  morse-proof-by-proof.html   the web edition: one hidden view per part, a collapsible table of
                               contents, tags in the right margin, lazy MathJax, a concordance
  preview-pbp.html             the same page wrapped in a minimal document, for opening locally
  ProofByProof.pdf             the print edition, through pandoc and xelatex
  proofbyproof-header.tex      the LaTeX preamble the PDF needs, written by this script

The PDF needs pandoc and xelatex on the PATH. The design of the web page (the style block, the
MathJax configuration and the routing script below) is the one first published for this book; keep
it here so that it cannot go missing again.
"""
import re, sys, html, pathlib, datetime, subprocess, collections

EXDIR = pathlib.Path(__file__).resolve().parent
PROJ = EXDIR.parent
SRC = EXDIR / 'ProofByProof.md'
sys.path.insert(0, str(EXDIR))
import check_trace as T

TITLE = 'Morse Theory, Proof by Proof'
SUBTITLE = "The formal proof of Milnor's Morse Theory, in words"
EYEBROW = 'Milnor · Morse Theory · the formal proof in words'
H1 = 'Morse Theory, <em>proof by proof</em>'
SAMPLE = ('Chapter2/Regular', 'theorem_3_1')
LEGEND = ('A trace tag looks like this: {tag}, a file of the project and the declaration in it that '
          'proves the sentence. Each part opens on its own; use the contents or the links at the end '
          'of a part.')
CONC_TITLE = 'Concordance'
CONC_INTRO = ('Every declaration cited in this book, by file, with its line in the source and the '
              'sections that cite it. {ndecl} declarations in {nfile} files. Open “formal statement” '
              'to compare a sentence of the book with the Lean statement it translates.')
CONC_INTRO_PDF = ('Every declaration cited in this book, by file, with its line in the source. '
                  '{ndecl} declarations in {nfile} files. The web edition also shows each exact '
                  'formal statement.')
FOOTER = ('Every declaration named here is checked by Lean’s kernel and depends only on propext, '
          'Classical.choice and Quot.sound. Source: Morse/*.lean; this text: '
          'Exposition/ProofByProof.md.')

# A tag is lifted out of the Markdown before pandoc sees it and put back into the HTML afterwards:
# pandoc leaves this token alone, and nothing else in the book looks like it.
MARK = 'TRACEMARK%05dEND'
MARK_RE = r'TRACEMARK(\d{5})END'

LATEX_HEADER = r"""% Preamble for Exposition/ProofByProof.pdf.
% Written by Exposition/build_proofbyproof.py; edit the script, not this file.
\usepackage{xcolor}
\definecolor{tracegrey}{gray}{0.42}
% A trace tag: the file and the declaration that proves the sentence, inline, small, grey, monospaced.
\newcommand{\trace}[2]{{\footnotesize\ttfamily\color{tracegrey}#1\,·\,#2}}
% Declaration names are long and unbreakable; let the paragraph stretch rather than overflow.
\setlength{\emergencystretch}{4em}
\tolerance=1800
\hbadness=1800
"""

# The head of the published page: the fonts, the light and dark tokens, and MathJax with
# typesetting held back until a view is shown. Reproduced verbatim from the first edition.
HEAD = r'''<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Newsreader:ital,opsz,wght@0,6..72,500;0,6..72,600;1,6..72,500&family=Source+Serif+4:ital,opsz,wght@0,8..60,400;0,8..60,600;1,8..60,400&family=IBM+Plex+Mono:wght@400;500&display=swap">
<style>
:root{
  --bg:#f6f7f9; --paper:#ffffff; --ink:#1c2330; --ink-2:#4a5568; --muted:#7a8494;
  --rule:#d5dae2; --accent:#2b5aa8; --accent-ink:#1e4380; --note-bg:#eef2f8; --note-rule:#9db3d9;
  --mono-bg:#eceff4; --table-head:#e7ebf2;
  --trace:#56647c; --trace-name:#2f3b50; --trace-bg:#eef2f8; --trace-rule:#b8c6de; --hl:#fff4c7;
  --toc-w:250px; --margin-w:236px;
}
@media (prefers-color-scheme: dark){
  :root:not([data-theme="light"]){
    --bg:#12161c; --paper:#181d25; --ink:#e3e7ed; --ink-2:#b4bcc8; --muted:#8792a1;
    --rule:#2c343f; --accent:#8fb2ec; --accent-ink:#b7ccf2; --note-bg:#1c2533; --note-rule:#4a6aa0;
    --mono-bg:#20272f; --table-head:#222a34;
    --trace:#94a3bb; --trace-name:#c9d3e2; --trace-bg:#1c2533; --trace-rule:#3d4f6d; --hl:#3a3420;
  }
}
:root[data-theme="dark"]{
  --bg:#12161c; --paper:#181d25; --ink:#e3e7ed; --ink-2:#b4bcc8; --muted:#8792a1;
  --rule:#2c343f; --accent:#8fb2ec; --accent-ink:#b7ccf2; --note-bg:#1c2533; --note-rule:#4a6aa0;
  --mono-bg:#20272f; --table-head:#222a34;
  --trace:#94a3bb; --trace-name:#c9d3e2; --trace-bg:#1c2533; --trace-rule:#3d4f6d; --hl:#3a3420;
}
html{background:var(--bg);scroll-padding-top:16px}
body{background:var(--bg);color:var(--ink);font-family:"Source Serif 4",Georgia,"Times New Roman",serif;
  font-size:17px;line-height:1.62;margin:0;font-variant-numeric:oldstyle-nums}
.book{max-width:1400px;margin:0 auto;padding-inline:20px;display:grid;grid-template-columns:minmax(0,1fr)}
main.text{min-width:0;max-width:68ch;margin:0 auto;padding-block:0 96px;width:100%}
nav.toc{font-family:"Source Serif 4",Georgia,serif;font-size:14.5px;line-height:1.4;padding-block:16px 8px;border-bottom:1px solid var(--rule);margin-bottom:8px}
nav.toc .toc-label{font-family:"IBM Plex Mono",ui-monospace,Menlo,monospace;font-size:11.5px;letter-spacing:.09em;text-transform:uppercase;color:var(--muted);margin:0 0 10px}
nav.toc details{margin:0 0 6px}
nav.toc summary{cursor:pointer;list-style:none;color:var(--ink);padding:3px 0 3px 14px;position:relative;text-wrap:balance}
nav.toc summary::-webkit-details-marker{display:none}
nav.toc summary::before{content:"›";position:absolute;left:0;top:2px;color:var(--muted);transition:transform .15s}
nav.toc details[open]>summary::before{transform:rotate(90deg)}
nav.toc ol{list-style:none;margin:2px 0 8px;padding:0 0 0 14px;border-left:1px solid var(--rule)}
nav.toc li{margin:0}
nav.toc a{display:block;padding:2px 0 2px 10px;color:var(--ink-2);text-decoration:none}
nav.toc a:hover{color:var(--accent-ink)}
nav.toc a.current{color:var(--accent-ink);font-weight:600}
nav.toc summary a{display:inline;padding:0;color:inherit}
@media (min-width:1180px){
  .book{grid-template-columns:var(--toc-w) minmax(0,68ch) var(--margin-w);column-gap:36px;padding-inline:28px}
  main.text{margin:0;max-width:none}
  nav.toc{position:sticky;top:env(safe-area-inset-top,0px);align-self:start;max-height:100vh;overflow-y:auto;padding-block:44px 32px;border-bottom:0;margin:0}
}
header.mast{padding:48px 0 26px;border-bottom:1px solid var(--rule);margin-bottom:36px}
.eyebrow{font-family:"IBM Plex Mono",ui-monospace,Menlo,monospace;font-size:12px;letter-spacing:.08em;text-transform:uppercase;color:var(--accent);margin:0 0 14px}
header.mast h1{font-family:"Newsreader",Georgia,serif;font-weight:500;font-size:clamp(32px,4.6vw,46px);line-height:1.08;margin:0 0 14px;text-wrap:balance;letter-spacing:-.012em}
header.mast h1 em{font-style:italic;font-weight:500;color:var(--ink-2)}
header.mast .dek{color:var(--ink-2);font-style:italic;margin:0;max-width:62ch}
header.mast .meta{margin:22px 0 0;font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:12.5px;color:var(--muted);display:flex;gap:10px 22px;flex-wrap:wrap;font-variant-numeric:tabular-nums}
.legend{margin:20px 0 0;display:flex;align-items:center;gap:12px;flex-wrap:wrap;font-size:14.5px;color:var(--ink-2)}
h2{font-family:"Newsreader",Georgia,serif;font-weight:600;font-size:29px;line-height:1.18;margin:72px 0 18px;text-wrap:balance;letter-spacing:-.006em;padding-top:18px;border-top:1px solid var(--rule)}
h3{font-family:"Newsreader",Georgia,serif;font-weight:600;font-size:21px;line-height:1.28;margin:40px 0 12px;text-wrap:balance}
h4{font-family:"Newsreader",Georgia,serif;font-weight:600;font-style:italic;font-size:18px;margin:28px 0 10px}
p{margin:0 0 1.05em}
strong{font-weight:600}
hr{border:0;border-top:1px solid var(--rule);margin:44px 0}
a{color:var(--accent-ink);text-decoration-thickness:1px;text-underline-offset:2px}
code{font-family:"IBM Plex Mono",ui-monospace,Menlo,monospace;font-size:.84em;background:var(--mono-bg);padding:.06em .32em;border-radius:3px;color:var(--ink)}
ul,ol{padding-left:1.4em;margin:0 0 1.1em}
li{margin:0 0 .45em}
li p{margin:0 0 .4em}
blockquote{margin:22px 0 26px;padding:14px 20px 12px;background:var(--note-bg);border-left:3px solid var(--note-rule);border-radius:0 4px 4px 0;font-size:16px}
blockquote p:last-child{margin:0}
.math.display{display:block;overflow-x:auto;overflow-y:hidden;padding:4px 0;margin:4px 0 10px}
mjx-container[display="true"]{margin:.35em 0 !important}
.tablewrap{overflow-x:auto;margin:20px 0}
table{border-collapse:collapse;width:100%;font-size:15px;line-height:1.45;font-variant-numeric:tabular-nums lining-nums}
th{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:11.5px;letter-spacing:.06em;text-transform:uppercase;text-align:left;color:var(--ink-2);background:var(--table-head);padding:9px 12px;border-bottom:1px solid var(--rule)}
td{padding:9px 12px;border-bottom:1px solid var(--rule);vertical-align:top}
/* the apparatus: trace tags */
a.trace{font-family:"IBM Plex Mono",ui-monospace,Menlo,monospace;font-size:11.5px;line-height:1.35;text-decoration:none;color:var(--trace);
  display:inline-block;vertical-align:1px;background:var(--trace-bg);border-radius:3px;padding:.05em .45em;margin:0 .1em;
  max-width:100%;overflow-wrap:anywhere;font-variant-numeric:lining-nums}
a.trace .tf{color:var(--trace)}
a.trace .tf::after{content:" · "}
a.trace .td{color:var(--trace-name);font-weight:500}
a.trace:hover,a.trace:focus-visible{color:var(--accent-ink);background:var(--hl)}
a.trace:hover .td{color:var(--accent-ink)}
@media (min-width:1180px){
  main.text p a.trace, main.text li a.trace, main.text blockquote a.trace{
    float:right;clear:right;width:var(--margin-w);margin:.2em calc(-1 * (var(--margin-w) + 36px)) .45em 0;
    background:transparent;border-left:1px solid var(--trace-rule);border-radius:0;padding:0 0 0 10px;vertical-align:baseline}
  main.text li a.trace{margin-right:calc(-1 * (var(--margin-w) + 36px + 1.4em))}
  main.text blockquote a.trace{margin-right:calc(-1 * (var(--margin-w) + 36px + 23px))}
  a.trace .tf{display:block}
  a.trace .tf::after{content:""}
  main.text td a.trace{float:none}
}
/* concordance */
.conc-intro{color:var(--ink-2)}
.conc-file{margin:26px 0 8px;font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:13px;font-weight:500;color:var(--ink);border-bottom:1px solid var(--rule);padding-bottom:4px}
.conc-entry{padding:6px 0 6px;border-bottom:1px dashed var(--rule);scroll-margin-top:16px}
.conc-entry:target{background:var(--hl)}
.conc-head{display:flex;flex-wrap:wrap;gap:4px 14px;align-items:baseline}
.conc-name{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:13px;color:var(--trace-name);overflow-wrap:anywhere}
.conc-line{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:12px;color:var(--muted);font-variant-numeric:tabular-nums}
.conc-cited{font-size:14px;color:var(--ink-2)}
.conc-cited a{margin-right:.4em}
.conc-entry details{margin:4px 0 2px}
.conc-entry summary{cursor:pointer;font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:11.5px;letter-spacing:.06em;text-transform:uppercase;color:var(--muted)}
.conc-entry pre{margin:6px 0 4px;padding:10px 12px;background:var(--mono-bg);border-radius:4px;overflow-x:auto;font-family:"IBM Plex Mono",ui-monospace,Menlo,monospace;font-size:12.5px;line-height:1.5;color:var(--ink);white-space:pre}
[hidden]{display:none!important}
nav.prevnext{display:flex;justify-content:space-between;gap:16px;flex-wrap:wrap;margin:56px 0 0;padding-top:18px;border-top:1px solid var(--rule);font-size:15px}
nav.prevnext a.pn{color:var(--accent-ink);text-decoration:none;max-width:48%}
nav.prevnext a.pn:hover{text-decoration:underline}
nav.prevnext a.next{text-align:right;margin-left:auto}
section.view > h2:first-child{margin-top:44px}
.footer{margin-top:64px;padding-top:20px;border-top:1px solid var(--rule);font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:12.5px;color:var(--muted);line-height:1.6}
:focus-visible{outline:2px solid var(--accent);outline-offset:2px}
@media (prefers-reduced-motion: reduce){*{animation:none!important;transition:none!important}}
</style>
<script>
window.MathJax = {
  tex: { inlineMath: [['\\(','\\)']], displayMath: [['\\[','\\]']] },
  svg: { fontCache: 'global' },
  loader: { load: [] },
  options: { enableMenu: false, menuOptions: { settings: { assistiveMml: false } } },
  startup: { typeset: false }
};
</script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.2/es5/tex-svg.js"></script>
'''

# The routing script of the published page: show the view holding the hash target, typeset its
# mathematics once, and follow the reader in the table of contents.
SCRIPT = r'''<script>
(function(){
  var views=[].slice.call(document.querySelectorAll('section.view'));
  var done=new Set();
  var links={};document.querySelectorAll('nav.toc a[href^="#"]').forEach(function(a){links[a.getAttribute('href').slice(1)]=a;});
  var current=null;
  function mark(id){ var a=links[id]; if(!a) return; if(current) current.classList.remove('current'); a.classList.add('current'); current=a;
    var d=a.closest('details'); if(d&&!d.open){ document.querySelectorAll('nav.toc details[open]').forEach(function(x){if(x!==d)x.open=false;}); d.open=true; } }
  function typeset(sec){ if(done.has(sec.id)) return; done.add(sec.id);
    try{ if(window.MathJax&&MathJax.startup&&MathJax.startup.promise){ MathJax.startup.promise.then(function(){ return MathJax.typesetPromise([sec]); }).catch(function(){}); } }catch(e){} }
  function show(id, scroll){
    var el=id?document.getElementById(id):null;
    var sec=el?el.closest('section.view'):null;
    if(!sec) sec=views[0];
    views.forEach(function(v){ v.hidden=(v!==sec); });
    typeset(sec);
    if(scroll){ if(el&&el!==sec&&el.id!==sec.getAttribute('data-first')) el.scrollIntoView(); else window.scrollTo(0,0); }
    mark(sec.getAttribute('data-first')); if(el) mark(el.id);
  }
  window.addEventListener('hashchange', function(){ show(location.hash.slice(1), true); });
  show(location.hash.slice(1), !!location.hash);
  try{
    if('IntersectionObserver' in window){
      var io=new IntersectionObserver(function(es){ es.forEach(function(e){ if(e.isIntersecting&&!e.target.closest('section.view').hidden) mark(e.target.id); }); },{rootMargin:'0px 0px -75% 0px'});
      document.querySelectorAll('main.text h2[id], main.text h3[id]').forEach(function(h){ io.observe(h); });
    }
  }catch(e){}
})();
</script>'''

def pandoc(args, text):
    """Run pandoc over text and return what it wrote to stdout."""
    p = subprocess.run(['pandoc', '--from=markdown'] + args, input=text, text=True,
                       capture_output=True)
    if p.returncode:
        sys.exit('pandoc failed:\n' + p.stderr)
    return p.stdout


def strip_tags(s):
    """The text of a heading: its inner HTML with the tags taken out."""
    return re.sub(r'\s+', ' ', re.sub(r'<[^>]+>', '', s)).strip()


def lean_file(path):
    """Where a tag's file really is."""
    if path.startswith('Mathlib/'):
        return path + '.lean'
    if path.startswith('Milnor/'):
        return '../' + path + '.lean'
    return 'Morse/' + path + '.lean'


def cite_label(text, width=38):
    """How a citing section is named in the concordance: its result label, or its title, cut short."""
    m = re.match(r'V[0-9.]*[0-9A]', text)
    if m:
        return m.group(0)
    return text if len(text) <= width else text[:width - 2].rstrip() + '…'


def latex_escape(s):
    for a, b in (('\\', r'\textbackslash{}'), ('{', r'\{'), ('}', r'\}'), ('_', r'\_'),
                 ('#', r'\#'), ('$', r'\$'), ('%', r'\%'), ('&', r'\&'), ('~', r'\textasciitilde{}'),
                 ('^', r'\textasciicircum{}')):
        s = s.replace(a, b)
    # a declaration name is one long unbreakable word: offer the line breaker somewhere to break
    return re.sub(r'([/._])', r'\1\\allowbreak{}', s)


def source():
    """The book, its title and the tag occurrences in it, in order."""
    md = SRC.read_text()
    title = re.match(r'#\s+(.+)', md).group(1).strip()
    occ = [(m.start(), m.end(), m.group(1), m.group(2)) for m in T.TAG.finditer(md)]
    return md, title, occ


def resolve(occ):
    """Resolve every tag; the second result is the list of tags that name nothing."""
    report, bad = T.check([SRC])
    decls = {}
    for _, _, path, name in occ:
        key = (path, name)
        if key in decls:
            continue
        d = report.get(key) or T.resolve(path, name)
        if d is not None:
            decls[key] = d
    return decls, bad


def tag_ids(decls):
    """One anchor per declaration, distinct even when two names flatten to the same slug."""
    ids, used = {}, {}
    for key in sorted(decls, key=lambda k: (k[0], decls[k]['line'], k[1])):
        base = 't-' + re.sub(r'[^A-Za-z0-9]+', '-', key[0] + '-' + key[1]).strip('-')
        used[base] = used.get(base, 0) + 1
        ids[key] = base if used[base] == 1 else f'{base}-{used[base]}'
    return ids


def anchor(path, name, d, ids):
    return (f'<a class="trace" href="#{ids[(path, name)]}" '
            f'title="{html.escape(lean_file(path))} line {d["line"]}">'
            f'<span class="tf">{html.escape(path)}</span>'
            f'<span class="td">{html.escape(name)}</span></a>')


def masthead(dek, md, occ, decls):
    """The front of the first view: title, blurb, the tally, and how to read a tag."""
    lines = re.search(r'occupy\s+([\d,]+)\s+lines', md)
    nlines = lines.group(1) if lines else f'{sum(1 for f in (PROJ / "Morse").rglob("*.lean") for _ in f.open()):,}'
    ver = re.sub(r'.*:v?', '', (PROJ / 'lean-toolchain').read_text().strip())
    when = datetime.date.fromtimestamp(SRC.stat().st_mtime).strftime('%B %Y')
    tag = (f'<a class="trace" href="#concordance"><span class="tf">{SAMPLE[0]}</span>'
           f'<span class="td">{SAMPLE[1]}</span></a>')
    return f"""<header class="mast">
  <p class="eyebrow">{EYEBROW}</p>
  <h1>{H1}</h1>
  <p class="dek">{dek}</p>
  <p class="meta"><span>{nlines} lines of Lean</span><span>{len(occ):,} trace tags</span>\
<span>{len(decls):,} declarations cited</span><span>Lean {ver} · Mathlib · {when}</span></p>
  <p class="legend">{LEGEND.format(tag=tag)}</p>
</header>"""


def toc(parts):
    """The sidebar: one collapsible entry per part, its sections inside."""
    out = ['<nav class="toc" aria-label="Contents"><p class="toc-label">Contents</p>']
    for pid, ptext, subs, _ in parts:
        out.append(f'<details><summary><a href="#{pid}">{html.escape(ptext)}</a></summary>')
        if subs:
            out.append('<ol>' + ''.join(f'<li><a href="#{sid}">{html.escape(stext)}</a></li>'
                                        for sid, stext in subs) + '</ol>')
        out.append('</details>')
    out.append(f'<details><summary><a href="#concordance">{CONC_TITLE}</a></summary></details></nav>')
    return ''.join(out)


def prevnext(labels, k):
    """The links at the foot of a view; an empty span keeps the other one against its margin."""
    out = ['<nav class="prevnext" aria-label="Part navigation">']
    out.append(f'<a class="pn prev" href="#{labels[k - 1][0]}">← {html.escape(labels[k - 1][1])}</a>'
               if k > 0 else '<span></span>')
    out.append(f'<a class="pn next" href="#{labels[k + 1][0]}">{html.escape(labels[k + 1][1])} →</a>'
               if k + 1 < len(labels) else '<span></span>')
    return ''.join(out) + '</nav>'


def concordance(decls, cites, heads, ids):
    """Every cited declaration, by file, with its line, its citations and its Lean statement."""
    by_file = collections.defaultdict(list)
    for key, d in decls.items():
        by_file[key[0]].append((d['line'], key[1], key, d))
    out = [f'<h2 id="concordance">{CONC_TITLE}</h2>',
           '<p class="conc-intro">'
           + html.escape(CONC_INTRO.format(ndecl=len(decls), nfile=len(by_file)), quote=False)
           + '</p>']
    for path in sorted(by_file):
        out.append(f'<div class="conc-file">{html.escape(lean_file(path))}</div>')
        for line, name, key, d in sorted(by_file[path]):
            cited = ' '.join(f'<a href="#{sid}">{html.escape(cite_label(heads[sid][1]))}</a>'
                             for sid in cites.get(key, []))
            out.append(f'<div class="conc-entry" id="{ids[key]}"><div class="conc-head">'
                       f'<span class="conc-name">{html.escape(d["full"])}</span>'
                       f'<span class="conc-line">line {line}</span>'
                       f'<span class="conc-cited">{cited}</span></div>'
                       f'<details><summary>formal statement</summary>'
                       f'<pre>{html.escape(d["header"])}</pre></details></div>')
    return '\n'.join(out)


def build_html(md, occ, decls, ids, outdir):
    """The web edition. Returns the number of views written."""
    # hand pandoc the book with the tags replaced by tokens it will pass through untouched
    piece, prev = [], 0
    for k, (s, e, _, _) in enumerate(occ):
        piece += [md[prev:s], MARK % k]
        prev = e
    piece.append(md[prev:])
    # --wrap=none: the split into views matches '<h2 id="' at the start of a line, and pandoc's
    # default wrapping would break that
    body = pandoc(['--to=html', '--mathjax', '--wrap=none'], ''.join(piece))

    # the title and the italic blurb become the masthead instead of staying in the text
    cut = re.search(r'(?m)^<h2 id="', body)
    front, body = body[:cut.start()], body[cut.start():]
    m = re.search(r'<p><em>(.*?)</em></p>', front, re.S)
    dek = m.group(1) if m else ''

    body = re.sub(r'(<table\b[^>]*>)', r'<div class="tablewrap">\1', body)
    body = body.replace('</table>', '</table></div>')

    # one pass: note every heading, and turn every token back into a link into the concordance
    heads, cites = {}, collections.defaultdict(list)
    scan = re.compile(r'(?m)^<h([23]) id="([^"]+)"[^>]*>(.*?)</h\1>|' + MARK_RE)
    out, prev, here = [], 0, None
    for m in scan.finditer(body):
        if m.group(4) is None:
            here = m.group(2)
            heads[here] = (int(m.group(1)), strip_tags(m.group(3)))
            continue
        _, _, path, name = occ[int(m.group(4))]
        if here and here not in cites[(path, name)]:
            cites[(path, name)].append(here)
        out += [body[prev:m.start()], anchor(path, name, decls[(path, name)], ids)]
        prev = m.end()
    out.append(body[prev:])
    body = ''.join(out)

    # one view per part, plus the concordance; all hidden but the first
    parts = []
    for chunk in re.split(r'(?m)(?=^<h2 id=")', body):
        if not chunk.strip():
            continue
        h = re.match(r'<h2 id="([^"]+)"[^>]*>(.*?)</h2>', chunk, re.S)
        subs = [(s.group(1), strip_tags(s.group(2)))
                for s in re.finditer(r'(?m)^<h3 id="([^"]+)"[^>]*>(.*?)</h3>', chunk)]
        parts.append((h.group(1), strip_tags(h.group(2)), subs, chunk))
    labels = [(pid, ptext) for pid, ptext, _, _ in parts] + [('concordance', CONC_TITLE)]

    views = []
    for k, (pid, _, _, chunk) in enumerate(parts):
        mast = masthead(dek, md, occ, decls) if k == 0 else ''
        views.append(f'<section class="view" id="view-{k}" data-first="{pid}"'
                     + ('' if k == 0 else ' hidden') + '>' + mast + chunk.rstrip('\n')
                     + prevnext(labels, k) + '</section>')
    views.append('<section class="view" id="view-conc" data-first="concordance" hidden>'
                 + concordance(decls, cites, heads, ids)
                 + prevnext(labels, len(labels) - 1) + '</section>')

    page = (f'<title>{html.escape(TITLE)}</title>\n' + HEAD + '<div class="book">' + toc(parts) + '<main class="text">' + ''.join(views)
            + f'<p class="footer">{FOOTER}</p></main></div>' + SCRIPT)
    (outdir / 'morse-proof-by-proof.html').write_text(page)
    (outdir / 'preview-pbp.html').write_text(
        '<!doctype html><html lang="en"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">'
        '</head><body>' + page + '</body></html>')
    for f in ('morse-proof-by-proof.html', 'preview-pbp.html'):
        print(f'  wrote {outdir / f}  ({(outdir / f).stat().st_size:,} bytes)')
    print(f'  {len(views)} section.view: {len(parts)} parts + the concordance')
    return len(views)


def pdf_concordance(decls):
    """The concordance as a chapter of the print edition: a run-in paragraph per file."""
    by_file = collections.defaultdict(list)
    for (path, name), d in decls.items():
        by_file[path].append((d['line'], name))
    out = [f'## {CONC_TITLE}', '',
           CONC_INTRO_PDF.format(ndecl=len(decls), nfile=len(by_file)), '']
    for path in sorted(by_file):
        run = '; '.join(f'`{name}` ({line})' for line, name in sorted(by_file[path]))
        out += [f'**{lean_file(path)}.** {run}.', '']
    return '\n'.join(out)


def build_pdf(md, title, occ, decls, outdir):
    """The print edition: tags inline through \\trace, a concordance appendix, pandoc and xelatex."""
    piece, prev = [], 0
    for s, e, path, name in occ:
        piece += [md[prev:s],
                  '`\\trace{%s}{%s}`{=latex}' % (latex_escape(path), latex_escape(name))]
        prev = e
    piece.append(md[prev:])
    text = ''.join(piece)
    # the masthead of the web page becomes the title page: drop the title and the italic blurb
    text = text[re.search(r'(?m)^## ', text).start():] + '\n\n' + pdf_concordance(decls)

    hdr = outdir / 'proofbyproof-header.tex'
    hdr.write_text(LATEX_HEADER)
    out = outdir / 'ProofByProof.pdf'
    pandoc(['--output=' + str(out), '--pdf-engine=xelatex', f'--include-in-header={hdr}',
            '--toc', '--toc-depth=1', '--shift-heading-level-by=-1',
            '--top-level-division=chapter',
            '-V', 'documentclass=report', '-V', 'mainfont=Palatino', '-V', 'monofont=Menlo',
            '-V', 'geometry:margin=1.1in',
            '-M', 'title=' + title, '-M', 'subtitle=' + SUBTITLE], text)
    print(f'  wrote {hdr}')
    print(f'  wrote {out}  ({out.stat().st_size:,} bytes, {pages(out)} pages)')


def pages(pdf):
    try:
        p = subprocess.run(['pdfinfo', str(pdf)], capture_output=True, text=True)
        return re.search(r'(?m)^Pages:\s+(\d+)', p.stdout).group(1)
    except Exception:
        return '?'


def main(outdir, want=('html', 'pdf')):
    md, title, occ = source()
    decls, bad = resolve(occ)
    print(f'{SRC.name}: {len(md.split()):,} words, {len(occ):,} trace tags, '
          f'{len(decls):,} distinct declarations, {len(bad)} unresolved')
    if bad:
        for where, path, name in bad:
            print(f'  UNRESOLVED {path} · {name}  (in {where})')
        sys.exit(f'{len(bad)} unresolved trace tags: nothing written')
    ids = tag_ids(decls)
    if 'html' in want:
        build_html(md, occ, decls, ids, outdir)
    if 'pdf' in want:
        build_pdf(md, title, occ, decls, outdir)
    return 0


if __name__ == '__main__':
    args = sys.argv[1:]
    want = tuple(w for w in ('html', 'pdf') if '--no-' + w not in args)
    rest = [a for a in args if not a.startswith('-')]
    sys.exit(main(pathlib.Path(rest[0]) if rest else EXDIR, want))
