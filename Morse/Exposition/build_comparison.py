"""Build the comparison edition: Milnor's statements beside the formal ones.

Usage: python3 Exposition/build_comparison.py [outdir]

Assembles Exposition/Comparison.json from the per-part files Exposition/cmp/*.json (in file-name
order; a new part is picked up by its file name alone), checks every declaration tag against the Lean
sources, and writes Comparison.md and the web page morse-beside-lean.html (default: into
Exposition/). Source paths are printed relative to Morse/ (`../Milnor/…` for the companion project).
"""
import re, sys, json, html, pathlib, collections

EXDIR = pathlib.Path(__file__).resolve().parent
CMP = EXDIR
sys.path.insert(0, str(EXDIR))
import check_trace as T

def lean_file(path):
    """Where a tag's file really is."""
    if path.startswith('Mathlib/'):
        return path + '.lean'
    if path.startswith('Milnor/'):
        return '../' + path + '.lean'
    return 'Morse/' + path + '.lean'

TITLE = 'Morse Theory beside Lean'
EYEBROW = 'Milnor · Morse Theory · the statements compared'
DEK = ('Every result of the book beside the statement the machine actually checked. The left column is '
       'Milnor, in his own terms. The right column is the formal statement, with the hypotheses he leaves '
       'to the reader written out. Click a declaration to see the Lean it names.')

VERDICTS = [
    ('same',      'as in the book',      'The formal statement is Milnor’s, hypothesis for hypothesis.'),
    ('explicit',  'hypotheses explicit', 'Same mathematics; the formal statement names what the book leaves implicit.'),
    ('stronger',  'stronger',            'The formal statement proves more than the book’s.'),
    ('narrower',  'narrower',            'The formal statement assumes more, or covers fewer cases.'),
    ('restated',  'restated',            'Same mathematics in a different formulation.'),
    ('extra',     'not in the book',     'A definition or a tool built for the formalization.'),
    ('sign',      'value differs',       'The formal value differs from the book’s, through a difference of convention.'),
    ('gap',       'not formalized',      'The book states it; the formalization does not prove it.'),
]
VNAME = {k: n for k, n, _ in VERDICTS}
CHAPTERS = [
    ('V1', 'Chapter 1', 'Milnor §§1–2, pp. 1–12: critical points, the Hessian and the index, the Morse lemma, flows'),
    ('V2', 'Chapter 2', 'Milnor §3, pp. 12–24: the homotopy type of sublevel sets, attaching cells'),
    ('V3', 'Chapter 3', 'Milnor §§4–5, pp. 25–32: Reeb, the torus, the Morse inequalities, the Euler characteristic'),
    ('V4', 'Chapter 4', 'Milnor §6, pp. 32–38: focal points, existence and density of Morse functions'),
    ('V5', 'Chapter 5', 'Milnor §7, pp. 39–42: the Lefschetz theorem on hyperplane sections'),
    ('V6', 'Chapter 6', 'Milnor §§8–9, pp. 43–54: covariant differentiation, the curvature tensor'),
    ('V7', 'Chapter 7', 'Milnor §10, pp. 55–66: geodesics and completeness'),
    ('V8', 'Chapter 8', 'Milnor §§11–13, pp. 67–76: the path space, the energy, the second variation'),
    ('V9', 'Chapter 9', 'Milnor §§14–15, pp. 77–87: Jacobi fields and the index theorem'),
    ('V10', 'Chapter 10', 'Milnor §§16–17, pp. 88–97: the finite-dimensional approximation, the full path space'),
    ('V11', 'Chapter 11', 'Milnor §§18–19, pp. 98–108: non-conjugate points, topology and curvature'),
    ('V12', 'Chapter 12', 'Milnor §§20–21, pp. 109–117: symmetric spaces, Lie groups'),
    ('V13', 'Chapter 13', 'Milnor §22, pp. 118–123: whole manifolds of minimal geodesics'),
    ('V14', 'Chapter 14', 'Milnor §23, pp. 124–132: Bott periodicity for the unitary group'),
    ('V15', 'Chapter 15', 'Milnor §24, pp. 133–148: periodicity for the orthogonal group'),
    ('VA', 'Appendix', 'Milnor pp. 149–153: the homotopy type of a monotone union'),
    ('G', 'Not formalized', 'What the book states and the formalization does not prove, and what it does instead'),
]

MATHS = re.compile(r'\$\$.+?\$\$|\$[^$]+?\$', re.S)


def chapter_of(vid):
    """Which chapter an item belongs to: V5.3 -> V5, V.A' -> V.A, G.2 -> G."""
    if vid.startswith('VA') or vid.startswith('V.A'):
        return 'VA'
    if vid.startswith('G.'):
        return 'G'
    m = re.match(r'(V\d+)\.', vid)
    return m.group(1) if m else '?'


def md(text):
    """Tiny markdown: math protected, then escaping, code spans and emphasis, then paragraphs."""
    if text is None:
        return ''
    keep = []

    def stash(m):
        keep.append(m.group(0).replace('&', '&amp;').replace('<', '&lt;'))
        return f'\x00{len(keep) - 1}\x00'

    s = MATHS.sub(stash, str(text))
    s = html.escape(s, quote=False)
    s = re.sub(r'`([^`]+)`', r'<code>\1</code>', s)
    s = re.sub(r'\*\*([^*]+)\*\*', r'<strong>\1</strong>', s)
    s = re.sub(r'(?<![\w*])\*([^*\n]+)\*(?![\w*])', r'<em>\1</em>', s)
    s = re.sub(r'\x00(\d+)\x00', lambda m: keep[int(m.group(1))], s)
    paras = [p.strip() for p in re.split(r'\n\s*\n', s) if p.strip()]
    return ''.join('<p>' + p.replace('\n', ' ') + '</p>' for p in paras)


def plain(text):
    """Searchable plain text."""
    return re.sub(r'\s+', ' ', re.sub(r'[$*`\\]', ' ', str(text or ''))).strip()


def item_id(vid):
    # primes must survive slugification: V.A′ and V.A″ would otherwise collide in one anchor
    vid = vid.replace('\u2032', '-prime').replace('\u2033', '-prime2').replace("'", '-prime')
    return 'item-' + re.sub(r'[^A-Za-z0-9.-]+', '-', vid)


CHAPTER_ORDER = [p for p, _, _ in CHAPTERS]


def id_key(it):
    """Book order of an item id: chapter, then number, then primes (V7.10 < V7.10′ < V7.11)."""
    vid = it['id']
    m = re.match(r'(V\d+|VA)\.(\d+)(.*)$', vid)
    if not m:
        return (len(CHAPTER_ORDER), 0, vid)
    return (CHAPTER_ORDER.index(m.group(1)), int(m.group(2)), m.group(3))


def assemble():
    """Merge the per-part data files cmp/*.json, in file-name order, into Comparison.json.

    Items are sorted into book order by id; the notFormalized entries keep file order, so that the
    G-numbers of earlier parts do not move when a later part is appended. Without cmp/, the existing
    Comparison.json is used as it stands."""
    parts = sorted((EXDIR / 'cmp').glob('*.json'))
    if not parts:
        return
    items, gaps = [], []
    for f in parts:
        d = json.loads(f.read_text())
        items += d.get('items', [])
        gaps += d.get('notFormalized', [])
    items.sort(key=id_key)
    (EXDIR / 'Comparison.json').write_text(
        json.dumps({'items': items, 'notFormalized': gaps}, ensure_ascii=False, indent=1) + '\n')
    print(f'Comparison.json assembled from {", ".join(f.name for f in parts)}')


def load():
    assemble()
    data = json.loads((EXDIR / 'Comparison.json').read_text())
    items = list(data['items'])
    if data.get('notFormalized'):
        for k, g in enumerate(data['notFormalized'], 1):
            items.append({'id': f'G.{k}', 'title': g['title'], 'verdict': 'gap',
                          'milnor': {'label': g['label'], 'page': g.get('page'), 'statement': g['book']},
                          'lean': {'statement': g['instead'], 'decls': []},
                          'chips': [], 'diff': []})
    return items


def validate(items):
    bad = []
    seen = set()
    for it in items:
        vid = it.get('id', '?')
        if vid in seen:
            bad.append(f'{vid}: duplicate id')
        seen.add(vid)
        if it.get('verdict') not in VNAME:
            bad.append(f'{vid}: verdict {it.get("verdict")!r}')
        for key in ('title', 'milnor', 'lean'):
            if not it.get(key):
                bad.append(f'{vid}: missing {key}')
        if not it.get('milnor', {}).get('statement'):
            bad.append(f'{vid}: empty Milnor statement')
        if not it.get('lean', {}).get('statement'):
            bad.append(f'{vid}: empty formal statement')
        if not it.get('lean', {}).get('decls') and it.get('verdict') != 'gap':
            bad.append(f'{vid}: no declarations')
        for ch in it.get('chips', []):
            if len(ch) > 44:
                bad.append(f'{vid}: chip too long: {ch!r}')
    return bad


def resolve_decls(items):
    """Attach {path, name, line, header} to each declaration; return the list of failures."""
    bad = []
    for it in items:
        out = []
        for tag in it['lean']['decls']:
            m = re.match(r'^\s*([A-Za-z0-9_/]+)\s*·\s*(.+?)\s*$', tag)
            if not m:
                bad.append(f'{it["id"]}: malformed tag {tag!r}')
                continue
            path, name = m.group(1), m.group(2)
            r = T.resolve(path, name)
            if r is None:
                bad.append(f'{it["id"]}: unresolved {path} · {name}')
                continue
            out.append({'path': path, 'name': name, **r})
        it['_decls'] = out
    return bad


def render(items):
    head = (EXDIR / 'comparison-head.html').read_text()
    counts = collections.Counter(it['verdict'] for it in items)
    tally = ''.join(
        f'<span class="t"><span class="sw" style="background:var(--v-{k})"></span>'
        f'<b>{counts.get(k, 0)}</b> {html.escape(n)}</span>' for k, n, _ in VERDICTS)
    ndecl = len({(d['path'], d['name']) for it in items for d in it['_decls']})
    mast = f"""<header class="mast">
<p class="eyebrow">{EYEBROW}</p>
<h1>Morse Theory <em>beside</em> Lean</h1>
<p class="dek">{DEK}</p>
<div class="tally"><span class="t"><b>{len(items)}</b> results</span>
<span class="t"><b>{ndecl}</b> declarations</span>{tally}</div>
<div class="howto"><b>How to read a row.</b> The left panel states the result as the book states it,
with the page. The right panel states what Lean proves, and every hypothesis in it is one the formal
proof really uses. Where the two differ, the strip underneath says how, and the label on the right of
the title says what kind of difference it is. The grey buttons are the declarations: click one to see
its exact statement in the source, with its file and line.</div>
</header>"""

    ctrl = ['<div class="controls" role="search">',
            '<input type="search" id="q" placeholder="Search statements, e.g. Hausdorff, linking, isotopy" '
            'aria-label="Search the statements">',
            '<div class="vset" role="group" aria-label="Filter by kind of difference">']
    for k, n, tip in VERDICTS:
        ctrl.append(f'<button class="vb" type="button" data-v="{k}" aria-pressed="true" title="{html.escape(tip)}">'
                    f'<span class="sw" style="background:var(--v-{k})"></span>{html.escape(n)}</button>')
    ctrl.append('</div><span class="shown" id="shown" aria-live="polite"></span></div>')

    nav = ['<nav class="chap" aria-label="Chapters">']
    body = []
    for prefix, name, sub in CHAPTERS:
        sel = [it for it in items if chapter_of(it['id']) == prefix]
        if not sel:
            continue
        cid = 'ch-' + prefix.replace('.', '')
        nav.append(f'<a href="#{cid}">{html.escape(name)}</a>')
        body.append(f'<section class="chapter" id="{cid}" data-n="{len(sel)}">'
                    f'<h2>{html.escape(name)}</h2><p class="csub">{html.escape(sub)}</p>')
        for it in sel:
            body.append(render_item(it))
        body.append('</section>')
    nav.append('</nav>')

    script = """<script>
(function(){
  var items=[].slice.call(document.querySelectorAll('article.item'));
  var chaps=[].slice.call(document.querySelectorAll('section.chapter'));
  var on={}; document.querySelectorAll('button.vb').forEach(function(b){on[b.dataset.v]=true;});
  var q=document.getElementById('q'), shown=document.getElementById('shown');
  function apply(){
    var t=(q.value||'').trim().toLowerCase(), n=0;
    items.forEach(function(el){
      var ok=on[el.dataset.v] && (!t || el.dataset.s.indexOf(t)>=0);
      el.hidden=!ok; if(ok) n++;
    });
    chaps.forEach(function(s){
      s.hidden=!s.querySelector('article.item:not([hidden])');
    });
    shown.textContent=n+' of '+items.length+' shown';
    var e=document.getElementById('none'); if(e) e.hidden=(n>0);
  }
  document.querySelectorAll('button.vb').forEach(function(b){
    b.addEventListener('click',function(){
      var v=b.dataset.v; on[v]=!on[v]; b.setAttribute('aria-pressed',on[v]?'true':'false'); apply();
    });
  });
  q.addEventListener('input',apply);
  document.addEventListener('click',function(e){
    var b=e.target.closest('button.decl'); if(!b) return;
    var open=b.getAttribute('aria-expanded')==='true';
    b.setAttribute('aria-expanded',open?'false':'true');
    document.getElementById(b.getAttribute('aria-controls')).hidden=open;
  });
  var typed=new Set();
  function typeset(sec){
    if(!sec||typed.has(sec.id)) return; typed.add(sec.id);
    try{ if(window.MathJax&&MathJax.startup&&MathJax.startup.promise){
      MathJax.startup.promise.then(function(){ return MathJax.typesetPromise([sec]); }).catch(function(){}); } }catch(e){}
  }
  typeset(document.querySelector('header.mast'));
  try{
    if('IntersectionObserver' in window){
      var io=new IntersectionObserver(function(es){
        es.forEach(function(e){ if(e.isIntersecting) typeset(e.target); });
      },{rootMargin:'900px 0px 900px 0px'});
      chaps.forEach(function(s){ io.observe(s); });
    } else { chaps.forEach(typeset); }
  }catch(e){ chaps.forEach(typeset); }
  apply();
  if(location.hash){ var el=document.querySelector(location.hash);
    if(el){ typeset(el.closest('section.chapter')); el.scrollIntoView(); } }
})();
</script>"""

    page = (head + '<div class="wrap"><main>' + mast + ''.join(ctrl) + ''.join(nav) + ''.join(body)
            + '<p class="empty" id="none" hidden>Nothing matches. Clear the search, or switch a label back on.</p>'
            + '<p class="foot">Left column: John W. Milnor, <em>Morse Theory</em> (Princeton, 1963), '
              'paraphrased, with his page numbers. Right column: the statements proved in Lean 4 against Mathlib in '
              'Morse/*.lean (on top of the Milnor project and Mathlib), checked by Lean’s kernel, depending only on propext, Classical.choice and Quot.sound. '
              'Every declaration named here was resolved mechanically in the source. Companion texts: '
              'Exposition/Verification.md, Exposition/ProofByProof.md.</p>'
            + '</main></div>' + script)
    return page


def render_item(it):
    vid, v = it['id'], it['verdict']
    mil, lean = it['milnor'], it['lean']
    label = mil.get('label')
    page = mil.get('page')
    # a label that already quotes the page ("§7, p. 50") must not have it printed twice
    label_has_page = bool(label and re.search(r'p\.\s*\d', label))
    src = ' · '.join(x for x in [html.escape(label) if label else 'no counterpart in the book',
                                 f'p.&nbsp;{page}' if page and not label_has_page else ''] if x)
    chips = ''.join(f'<span class="chip">{md(c)[3:-4] if md(c).startswith("<p>") else html.escape(c)}</span>'
                    for c in it.get('chips', []))
    decl_html, code_html = [], []
    for k, d in enumerate(it['_decls']):
        panel = f'{item_id(vid)}-d{k}'
        decl_html.append(
            f'<button class="decl" type="button" aria-expanded="false" aria-controls="{panel}">'
            f'<span class="f">{html.escape(d["path"])}&nbsp;·&nbsp;</span>'
            f'{html.escape(d["full"].removeprefix("Morse."))}</button>')
        code_html.append(
            f'<div class="code" id="{panel}" hidden><p class="where">{html.escape(lean_file(d["path"]))}, '
            f'line {d["line"]} &nbsp;·&nbsp; {html.escape(d["full"])}</p>'
            f'<pre>{html.escape(d["header"])}</pre></div>')
    diff = it.get('diff') or []
    diff_html = ('<div class="diff"><p class="dlabel">What differs</p><ul>'
                 + ''.join('<li>' + (md(d)[3:-4] if md(d).startswith('<p>') else md(d)) + '</li>' for d in diff)
                 + '</ul></div>') if diff else ''
    note = f'<p class="note">{md(mil["note"])[3:-4]}</p>' if mil.get('note') else ''
    searchable = html.escape(' '.join([vid, it['title'], plain(mil['statement']), plain(mil.get('note')),
                                       plain(lean['statement']), ' '.join(it.get('chips', [])),
                                       ' '.join(plain(d) for d in diff),
                                       ' '.join(d['name'] + ' ' + d['path'] for d in it['_decls'])]).lower(),
                             quote=True)
    return f"""<article class="item" id="{item_id(vid)}" data-v="{v}" data-s="{searchable}">
<div class="ihead"><a class="vid" href="#{item_id(vid)}">{html.escape(vid)}</a><h3>{html.escape(it['title'])}</h3>
<span class="verdict">{html.escape(VNAME[v])}</span></div>
{f'<div class="chips">{chips}</div>' if chips else ''}
<div class="cols">
<div class="col book"><p class="clabel">Milnor <span class="src">{src}</span></p>{md(mil['statement'])}{note}</div>
<div class="col lean"><p class="clabel">{'In the formalization' if v == 'gap' else 'Proved in Lean'}</p>{md(lean['statement'])}
{f'<div class="decls">{"".join(decl_html)}</div>' if decl_html else ''}{''.join(code_html)}</div>
</div>{diff_html}</article>"""


def markdown_source(items):
    out = [f'# {TITLE}', '', f'*{DEK}*', '',
           'Left: the statement as the book states it. Right: the statement proved in Lean, with the '
           'hypotheses written out. Each declaration is given with its file and line.', '']
    for prefix, name, sub in CHAPTERS:
        sel = [it for it in items if chapter_of(it['id']) == prefix]
        if not sel:
            continue
        out += [f'## {name}', '', f'*{sub}*', '']
        for it in sel:
            mil, lean = it['milnor'], it['lean']
            src = mil.get('label') or 'no counterpart in the book'
            if mil.get('page') and not re.search(r'p\.\s*\d', src):
                src += f', p. {mil["page"]}'
            out += [f'### {it["id"]}. {it["title"]}', '',
                    f'*{VNAME[it["verdict"]]}*'
                    + (' · ' + ' · '.join(it['chips']) if it.get('chips') else ''), '',
                    f'**Milnor ({src}).** {mil["statement"]}', '']
            if mil.get('note'):
                out += [f'*{mil["note"]}*', '']
            out += [f'**Proved in Lean.** {lean["statement"]}', '']
            for d in it['_decls']:
                out += [f'- `{d["full"]}` — {lean_file(d["path"])}, line {d["line"]}']
            out += ['']
            if it.get('diff'):
                out += ['*What differs.*']
                out += [f'- {d}' for d in it['diff']]
                out += ['']
    return '\n'.join(out) + '\n'


def main(outdir):
    items = load()
    print(f'{len(items)} items')
    bad = validate(items)
    bad += resolve_decls(items)
    for b in bad:
        print('  PROBLEM', b)
    counts = collections.Counter(it['verdict'] for it in items)
    print('verdicts:', dict(counts))
    page = render(items)
    (outdir / 'morse-beside-lean.html').write_text(page)
    (outdir / 'preview-cmp.html').write_text(
        '<!doctype html><html lang="en"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">'
        '</head><body>' + page + '</body></html>')
    print('html', (outdir / 'morse-beside-lean.html').stat().st_size, 'bytes')
    text = markdown_source(items)
    (outdir / 'Comparison.md').write_text(text)
    print('markdown', len(text), 'chars ->', outdir / 'Comparison.md')
    return len(bad)


if __name__ == '__main__':
    where = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else EXDIR
    sys.exit(1 if main(where) else 0)
