#!/usr/bin/env python3
"""Build the sign-off page: every sign-off item of the verified edition on one page, with the full
verified statement, Milnor's statement beside it, the comparison's label, a tick box and a notes field.

Ticks and notes are kept in the browser (localStorage) and can be exported as the Markdown checklist
`SIGNOFF.md` (`- [x]` / `- [ ]` lines, notes indented under them) to be committed, and imported back.

Usage:
    python3 build_signoff.py                      # Morse: Exposition/morse-signoff.html
    python3 build_signoff.py --book milnor        # the root project: ../Exposition/milnor-signoff.html
"""
import argparse, glob, html, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))

BOOKS = {
    'morse': dict(
        title='Morse Theory', short='Morse',
        verification=os.path.join(HERE, 'Verification.md'),
        cmp=glob.glob(os.path.join(HERE, 'cmp', '*.json')),
        out=os.path.join(HERE, 'morse-signoff.html'),
        md=os.path.join(HERE, 'SIGNOFF.md')),
    'milnor': dict(
        title='Topology from the Differentiable Viewpoint', short='TDV',
        verification=os.path.join(HERE, '..', '..', 'Exposition', 'Verification.md'),
        cmp=[os.path.join(HERE, '..', '..', 'Exposition', 'Comparison.json')],
        out=os.path.join(HERE, '..', '..', 'Exposition', 'milnor-signoff.html'),
        md=os.path.join(HERE, '..', '..', 'Exposition', 'SIGNOFF.md')),
}

VERDICT_NAME = {
    'same': 'as in the book', 'explicit': 'hypotheses explicit', 'stronger': 'stronger',
    'narrower': 'narrower', 'restated': 'restated', 'extra': 'not in the book',
    'sign': 'value differs', 'gap': 'not formalized',
}


def md_inline(s):
    """Markdown inline → HTML, leaving $…$ for MathJax. Code spans are protected from emphasis."""
    s = html.escape(s, quote=False)
    codes = []
    def keep(m):
        codes.append(f'<code>{m.group(1)}</code>')
        return f'\x00{len(codes) - 1}\x00'
    s = re.sub(r'`([^`]+)`', keep, s)
    s = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', s, flags=re.S)
    s = re.sub(r'(?<![\w$\\])\*(?!\s)(.+?)(?<!\s)\*(?![\w])', r'<em>\1</em>', s, flags=re.S)
    s = re.sub(r'\x00(\d+)\x00', lambda m: codes[int(m.group(1))], s)
    return s


def md_block(text):
    """Paragraphs and simple bullet lists."""
    out, para, lst = [], [], []
    def flush():
        nonlocal para, lst
        if para:
            out.append('<p>' + md_inline(' '.join(para)) + '</p>'); para = []
        if lst:
            out.append('<ul>' + ''.join(f'<li>{md_inline(x)}</li>' for x in lst) + '</ul>'); lst = []
    for line in text.split('\n'):
        t = line.strip()
        if not t:
            flush(); continue
        if re.match(r'^[-*]\s+', t):
            if para: flush()
            lst.append(re.sub(r'^[-*]\s+', '', t)); continue
        if lst and line.startswith('  '):
            lst[-1] += ' ' + t; continue
        if lst: flush()
        para.append(t)
    flush()
    return '\n'.join(out)


def parse_verification(path):
    txt = open(path, encoding='utf-8').read()
    # sections
    secs = [(m.start(), m.group(1)) for m in re.finditer(r'^## \d+\. (.*)$', txt, re.M)]
    def section_of(pos):
        prior = [s for s in secs if s[0] < pos]
        return prior[-1][1].split(':')[0] if prior else 'Other'
    # V-items: **Vk.m (title; `names`).** body  … up to the next **V item, heading, or sign-off
    items = {}
    pat = re.compile(r'^\*\*(V[\w]*\.[\w′]+) \((.*?)\)\.\*\*\s*(.*?)(?=^\*\*V[\w]*\.[\w′]+ \(|^#{2,3} |\Z)', re.S | re.M)
    for m in pat.finditer(txt):
        vid, head, body = m.group(1), m.group(2), m.group(3).strip()
        names = re.findall(r'`([^`]+)`', head)
        title = head.split(';')[0].strip()
        items[vid] = dict(vid=vid, title=title, names=names, body=body, section=section_of(m.start()))
    # sign-off list
    so = re.search(r'^## \d+\. Sign-off\n(.*)', txt, re.S | re.M).group(1)
    signoff = []
    for n, rest in re.findall(r'^(\d+)\. (.*?)$', so, re.M):
        mm = re.match(r'\(([^)]+)\)\s*(.*)', rest)
        if mm:
            signoff.append(dict(n=int(n), vid=mm.group(1), summary=mm.group(2)))
    return items, signoff


def load_cmp(paths):
    cmp = {}
    for f in paths:
        if not os.path.exists(f):
            continue
        d = json.load(open(f, encoding='utf-8'))
        rows = d.get('items', d) if isinstance(d, dict) else d
        if isinstance(rows, list):
            for e in rows:
                if isinstance(e, dict) and 'id' in e:
                    cmp[e['id']] = e
    return cmp


CSS = r"""
:root{--bg:#f4f6f8;--paper:#fff;--ink:#1b222e;--ink-2:#48536a;--muted:#78838f;--rule:#d7dce4;--accent:#2b5aa8;
--accent-ink:#1e4380;--hl:#fff3c4;--mono-bg:#eceff4;--chip-bg:#e9edf3;--book-bg:#fffdf7;--book-rule:#e6ddc7;
--book-label:#8a6d3b;--lean-bg:#f6f9fd;--lean-rule:#cfdbec;--lean-label:#2d5a94;--ok:#2f7a4f;--ok-bg:#e8f4ec;
--v-same:#2f7a4f;--v-explicit:#2b5aa8;--v-stronger:#6b4aa8;--v-narrower:#96660f;--v-restated:#1c7178;
--v-extra:#5f6b7a;--v-sign:#b4531a;--v-gap:#a04141;--code-ink:#243044}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){--bg:#11151b;--paper:#181d25;--ink:#e4e8ee;
--ink-2:#b2bac6;--muted:#8a94a2;--rule:#2b323d;--accent:#8fb2ec;--accent-ink:#b6cbf2;--hl:#3b3520;--mono-bg:#20262f;
--chip-bg:#222a35;--book-bg:#1d1b17;--book-rule:#3b352a;--book-label:#d0b285;--lean-bg:#161c25;--lean-rule:#2c3a4e;
--lean-label:#9dc0f0;--ok:#7fc99b;--ok-bg:#16261c;--v-same:#7fc99b;--v-explicit:#8fb2ec;--v-stronger:#bda6f2;
--v-narrower:#e0b256;--v-restated:#74cdd3;--v-extra:#9aa4b2;--v-sign:#eb9a63;--v-gap:#e08d8d;--code-ink:#d7deea}}
html{background:var(--bg);scroll-padding-top:96px}
body{margin:0;background:var(--bg);color:var(--ink);font-family:"Source Serif 4",Georgia,"Times New Roman",serif;
font-size:16.5px;line-height:1.6}
.wrap{max-width:1480px;margin:0 auto;padding:0 18px 110px}
h1,h2,h3{font-family:"Newsreader",Georgia,serif;text-wrap:balance}
.mast{padding:40px 0 18px;border-bottom:1px solid var(--rule)}
.eyebrow{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:11.5px;letter-spacing:.09em;text-transform:uppercase;color:var(--accent);margin:0 0 10px}
.mast h1{font-weight:500;font-size:clamp(28px,4vw,40px);line-height:1.1;margin:0 0 10px;letter-spacing:-.01em}
.mast h1 em{font-style:italic;color:var(--ink-2);font-weight:500}
.howto{margin:16px 0 0;padding:14px 18px;background:var(--paper);border:1px solid var(--rule);border-radius:6px;font-size:15.5px;color:var(--ink-2);max-width:84ch}
.howto b{color:var(--ink)}
.controls{position:sticky;top:0;z-index:20;background:var(--bg);padding:10px 0;border-bottom:1px solid var(--rule);display:flex;flex-wrap:wrap;gap:8px 12px;align-items:center}
.controls input[type=search]{font:inherit;font-size:15px;padding:7px 12px;border:1px solid var(--rule);border-radius:6px;background:var(--paper);color:var(--ink);min-width:200px;flex:1 1 200px;max-width:320px}
.vset{display:flex;flex-wrap:wrap;gap:6px}
button.vb,button.act,label.tog{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:11.5px;letter-spacing:.04em;text-transform:uppercase;border:1px solid var(--rule);background:var(--paper);color:var(--ink-2);border-radius:999px;padding:5px 11px;cursor:pointer}
button.vb .sw,.tally .sw{display:inline-block;width:8px;height:8px;border-radius:2px;margin-right:6px}
button.vb[aria-pressed=true]{color:var(--ink);border-color:currentColor;background:var(--chip-bg)}
button.vb:not([aria-pressed=true]){opacity:.5}
button.act{color:var(--accent-ink);border-color:var(--accent)}
label.tog input{vertical-align:-1px;margin:0 6px 0 0}
.progress{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:12px;color:var(--muted);margin-left:auto;font-variant-numeric:tabular-nums}
.progress b{color:var(--ink);font-weight:500}
.bar{height:4px;background:var(--rule);border-radius:2px;margin:6px 0 0;width:100%}
.bar i{display:block;height:100%;background:var(--ok);border-radius:2px;width:0}
nav.chap{display:flex;flex-wrap:wrap;gap:4px 6px;margin:12px 0 22px}
nav.chap a{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:12px;text-decoration:none;color:var(--ink-2);border:1px solid var(--rule);border-radius:999px;padding:4px 10px;background:var(--paper)}
nav.chap a .n{color:var(--muted)}
section.chapter>h2{font-size:24px;font-weight:600;margin:44px 0 16px;padding-top:14px;border-top:1px solid var(--rule)}
article.item{background:var(--paper);border:1px solid var(--rule);border-left:3px solid var(--vc,var(--rule));border-radius:5px;padding:14px 18px 14px;margin:0 0 14px;scroll-margin-top:110px}
article.item.done{border-left-color:var(--ok);background:var(--ok-bg)}
article.item[data-v=same]{--vc:var(--v-same)}article.item[data-v=explicit]{--vc:var(--v-explicit)}
article.item[data-v=stronger]{--vc:var(--v-stronger)}article.item[data-v=narrower]{--vc:var(--v-narrower)}
article.item[data-v=restated]{--vc:var(--v-restated)}article.item[data-v=extra]{--vc:var(--v-extra)}
article.item[data-v=sign]{--vc:var(--v-sign)}article.item[data-v=gap]{--vc:var(--v-gap)}
.ihead{display:flex;flex-wrap:wrap;gap:6px 12px;align-items:baseline}
.ihead .num{font-family:"Newsreader",Georgia,serif;font-size:22px;font-weight:600;color:var(--ink-2);min-width:2.2em}
.ihead .vid{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:12.5px;color:var(--muted);text-decoration:none}
.ihead h3{font-size:18.5px;font-weight:600;margin:0;flex:1 1 300px}
.verdict{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:11px;letter-spacing:.05em;text-transform:uppercase;color:var(--vc,var(--muted));border:1px solid var(--vc,var(--rule));border-radius:999px;padding:3px 9px;white-space:nowrap}
.summary{margin:8px 0 0;font-size:16.5px}
.summary .lbl{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:11px;letter-spacing:.07em;text-transform:uppercase;color:var(--muted);margin-right:8px}
.chips{display:flex;flex-wrap:wrap;gap:6px;margin:8px 0 0}
.chip{font-size:13px;background:var(--chip-bg);color:var(--ink-2);border-radius:4px;padding:2px 8px}
details.full{margin:10px 0 0}
details.full>summary{cursor:pointer;font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:12px;color:var(--accent-ink);list-style:none}
details.full>summary::before{content:"▸ ";color:var(--muted)}details.full[open]>summary::before{content:"▾ "}
.cols{display:grid;grid-template-columns:minmax(0,1fr);gap:12px;margin:10px 0 0}
@media (min-width:900px){.cols{grid-template-columns:1fr 1fr;gap:18px}}
.col{border:1px solid var(--rule);border-radius:4px;padding:12px 14px 10px;min-width:0;font-size:15.5px}
.col.book{background:var(--book-bg);border-color:var(--book-rule)}.col.lean{background:var(--lean-bg);border-color:var(--lean-rule)}
.clabel{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:11px;letter-spacing:.07em;text-transform:uppercase;margin:0 0 8px;display:flex;gap:10px;flex-wrap:wrap}
.col.book .clabel{color:var(--book-label)}.col.lean .clabel{color:var(--lean-label)}
.clabel .src{text-transform:none;letter-spacing:0;color:var(--muted);font-size:11.5px}
.col p{margin:0 0 .7em}.col p:last-child{margin:0}.col ul{margin:.3em 0;padding-left:1.1em}
.names{display:flex;flex-wrap:wrap;gap:6px;margin:10px 0 0}
.names code{font-size:11.5px;background:var(--mono-bg);color:var(--code-ink);border:1px solid var(--lean-rule);border-radius:4px;padding:2px 7px}
.diff{margin:12px 0 0;padding:10px 14px 8px;border:1px dashed var(--rule);border-radius:4px;background:var(--bg)}
.diff .dlabel{font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:11px;letter-spacing:.07em;text-transform:uppercase;color:var(--muted);margin:0 0 6px}
.diff ul{margin:0;padding-left:1.1em}.diff li{margin:0 0 .35em;font-size:15px}
.sign{display:flex;flex-wrap:wrap;gap:10px 18px;align-items:flex-start;margin:14px 0 0;padding-top:12px;border-top:1px solid var(--rule)}
.sign label.ok{display:flex;align-items:center;gap:8px;font-weight:600;cursor:pointer;white-space:nowrap}
.sign label.ok input{width:18px;height:18px;accent-color:var(--ok)}
.sign textarea{flex:1 1 320px;min-height:38px;font:inherit;font-size:14.5px;padding:7px 10px;border:1px solid var(--rule);border-radius:4px;background:var(--paper);color:var(--ink);resize:vertical}
code{font-family:"IBM Plex Mono",ui-monospace,Menlo,monospace;font-size:.85em;background:var(--mono-bg);padding:.05em .3em;border-radius:3px}
mjx-container{max-width:100%;overflow-x:auto;overflow-y:hidden}
.foot{margin-top:56px;padding-top:18px;border-top:1px solid var(--rule);font-family:"IBM Plex Mono",ui-monospace,monospace;font-size:12px;color:var(--muted);line-height:1.65}
[hidden]{display:none!important}
@media print{.controls,nav.chap,.howto{display:none}body{font-size:10.5pt;background:#fff;color:#000}article.item{break-inside:avoid}.sign textarea{border:1px solid #999}details.full{display:block}details.full>summary{display:none}details.full>*{display:block}}
"""

JS = r"""
const BOOK = document.body.dataset.book;
const KEY = id => `signoff:${BOOK}:${id}`;
const items = [...document.querySelectorAll('article.item')];
function load(){
  for (const it of items){
    const id = it.dataset.id;
    try{
      const raw = localStorage.getItem(KEY(id));
      if(raw){ const s = JSON.parse(raw); it.querySelector('input.ok').checked = !!s.ok; it.querySelector('textarea').value = s.note||''; }
    }catch(e){}
    paint(it);
  }
  progress();
}
function save(it){
  const s = {ok: it.querySelector('input.ok').checked, note: it.querySelector('textarea').value};
  try{ localStorage.setItem(KEY(it.dataset.id), JSON.stringify(s)); }catch(e){}
  paint(it); progress(); filter();
}
function paint(it){ it.classList.toggle('done', it.querySelector('input.ok').checked); }
function progress(){
  const done = items.filter(i=>i.querySelector('input.ok').checked).length;
  const noted = items.filter(i=>i.querySelector('textarea').value.trim()).length;
  document.getElementById('prog').innerHTML = `<b>${done}</b> / ${items.length} signed · <b>${noted}</b> with notes`;
  document.getElementById('bar').style.width = (100*done/items.length)+'%';
  for (const sec of document.querySelectorAll('section.chapter')){
    const its=[...sec.querySelectorAll('article.item')], d=its.filter(i=>i.querySelector('input.ok').checked).length;
    const n = document.querySelector(`nav.chap a[href="#${sec.id}"] .n`); if(n) n.textContent = `${d}/${its.length}`;
  }
}
const on = {}; document.querySelectorAll('button.vb').forEach(b=>{ on[b.dataset.v]=true;
  b.addEventListener('click',()=>{ on[b.dataset.v]=!on[b.dataset.v]; b.setAttribute('aria-pressed', on[b.dataset.v]); filter(); }); });
function filter(){
  const q = document.getElementById('q').value.trim().toLowerCase();
  const onlyOpen = document.getElementById('open').checked;
  let shown=0;
  for (const it of items){
    const ok = it.querySelector('input.ok').checked;
    const vis = (on[it.dataset.v] !== false) && (!onlyOpen || !ok) && (!q || it.dataset.s.includes(q));
    it.hidden = !vis; if(vis) shown++;
  }
  for (const sec of document.querySelectorAll('section.chapter')) sec.hidden = ![...sec.querySelectorAll('article.item')].some(i=>!i.hidden);
  document.getElementById('shown').textContent = `${shown} shown`;
}
document.getElementById('q').addEventListener('input', filter);
document.getElementById('open').addEventListener('change', filter);
items.forEach(it=>{ it.querySelector('input.ok').addEventListener('change',()=>save(it)); it.querySelector('textarea').addEventListener('input',()=>save(it)); });
document.getElementById('export').addEventListener('click', ()=>{
  const lines = [`# ${document.body.dataset.title}: sign-off checklist`, '', `Exported from the sign-off page on ${new Date().toISOString().slice(0,10)}. ${items.filter(i=>i.querySelector('input.ok').checked).length} of ${items.length} items signed.`, ''];
  for (const sec of document.querySelectorAll('section.chapter')){
    lines.push(`## ${sec.querySelector('h2').textContent}`, '');
    for (const it of sec.querySelectorAll('article.item')){
      const ok = it.querySelector('input.ok').checked, note = it.querySelector('textarea').value.trim();
      const v = it.dataset.v ? ` \`[${it.dataset.v}]\`` : '';
      lines.push(`- [${ok?'x':' '}] **${it.dataset.n}.** (${it.dataset.id})${v} ${it.dataset.summary}${it.dataset.page?' — Milnor '+it.dataset.page:''}`);
      if(note) for (const l of note.split('\n')) lines.push(`    > ${l}`);
    }
    lines.push('');
  }
  const blob = new Blob([lines.join('\n')], {type:'text/markdown'});
  const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = 'SIGNOFF.md'; a.click();
});
document.getElementById('import').addEventListener('change', ev=>{
  const f = ev.target.files[0]; if(!f) return;
  f.text().then(t=>{
    let cur=null, n=0;
    for (const line of t.split('\n')){
      const m = line.match(/^- \[([ xX])\] \*\*\d+\.\*\* \(([^)]+)\)/);
      if(m){ cur = items.find(i=>i.dataset.id===m[2]); if(cur){ cur.querySelector('input.ok').checked = m[1]!==' '; cur.querySelector('textarea').value=''; n++; } continue; }
      const nm = line.match(/^    > ?(.*)$/); if(nm && cur){ const ta=cur.querySelector('textarea'); ta.value = (ta.value? ta.value+'\n':'') + nm[1]; }
    }
    items.forEach(save); alert(`Imported ${n} items.`);
  });
});
document.getElementById('clear').addEventListener('click', ()=>{
  if(!confirm('Clear all ticks and notes stored in this browser for this book?')) return;
  items.forEach(it=>{ it.querySelector('input.ok').checked=false; it.querySelector('textarea').value=''; try{localStorage.removeItem(KEY(it.dataset.id));}catch(e){} paint(it); });
  progress(); filter();
});
load(); filter();
"""


def build(book):
    b = BOOKS[book]
    items, signoff = parse_verification(b['verification'])
    cmp = load_cmp(b['cmp'])
    # group by the section of the V-item
    sections, order = {}, []
    for so in signoff:
        it = items.get(so['vid'])
        if it is None:  # ids like "V8.14 a, b", "V5.10, converse", "V.A′": fall back to the base item
            base = re.match(r'(V[\w]*\.[\w]+)', so['vid'])
            it = items.get(base.group(1)) if base else None
        sec = it['section'] if it else 'Other'
        if sec not in sections:
            sections[sec] = []; order.append(sec)
        sections[sec].append((so, it, cmp.get(so['vid'])))
    def esc(s): return html.escape(s, quote=True)
    parts = []
    parts.append(f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{esc(b['title'])}: sign-off</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Newsreader:ital,opsz,wght@0,6..72,500;0,6..72,600;1,6..72,500&family=Source+Serif+4:ital,opsz,wght@0,8..60,400;0,8..60,600;1,8..60,400&family=IBM+Plex+Mono:wght@400;500&display=swap">
<style>{CSS}</style>
<script>window.MathJax={{tex:{{inlineMath:[['$','$'],['\\\\(','\\\\)']],displayMath:[['$$','$$'],['\\\\[','\\\\]']]}},svg:{{fontCache:'global'}},options:{{enableMenu:false}}}};</script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.2.2/es5/tex-svg.js"></script>
</head><body data-book="{esc(book)}" data-title="{esc(b['title'])}"><div class="wrap">
<header class="mast"><p class="eyebrow">Milnor · {esc(b['title'])} · the verified edition, signed off</p>
<h1>{esc(b['title'])} <em>sign-off</em></h1>
<div class="howto"><b>How to sign an item.</b> Read the summary, then open <em>the full statement</em>: the left panel is the book's result,
with its page; the right panel is what Lean proves, with every hypothesis the formal proof uses, and the <em>Book</em> and <em>Hidden hypotheses</em>
notes of the verified edition. Tick <b>says what Milnor means</b> when the formal statement is the book's result (or the labelled difference is
correctly described); otherwise leave it unticked and write the objection in the notes. Ticks and notes are saved in this browser as you go.
<b>Export</b> writes them to <code>SIGNOFF.md</code> for git; <b>Import</b> restores them from such a file on another machine.</div>
</header>
<div class="controls" role="search"><input type="search" id="q" placeholder="Search items" aria-label="Search">
<div class="vset">""")
    for v, name in VERDICT_NAME.items():
        parts.append(f'<button class="vb" type="button" data-v="{v}" aria-pressed="true"><span class="sw" style="background:var(--v-{v})"></span>{esc(name)}</button>')
    parts.append(f"""<button class="vb" type="button" data-v="" aria-pressed="true"><span class="sw" style="background:var(--rule)"></span>no label</button></div>
<label class="tog"><input type="checkbox" id="open">unsigned only</label>
<button class="act" type="button" id="export">Export SIGNOFF.md</button>
<label class="tog act" style="color:var(--accent-ink);border-color:var(--accent)"><input type="file" id="import" accept=".md,.txt" hidden>Import…</label>
<button class="act" type="button" id="clear" style="color:var(--muted);border-color:var(--rule)">Clear</button>
<span class="progress" id="prog"></span><span class="progress" id="shown"></span><div class="bar"><i id="bar"></i></div></div>
<nav class="chap" aria-label="Sections">""")
    for i, sec in enumerate(order):
        parts.append(f'<a href="#sec-{i}">{esc(sec)} <span class="n"></span></a>')
    parts.append('</nav>')
    total = 0
    for i, sec in enumerate(order):
        parts.append(f'<section class="chapter" id="sec-{i}"><h2>{esc(sec)}</h2>')
        for so, it, c in sections[sec]:
            total += 1
            vid, n = so['vid'], so['n']
            v = (c or {}).get('verdict', '') or ''
            page = (((c or {}).get('milnor') or {}).get('label') or '') if c else ''
            title = it['title'] if it else vid
            search = ' '.join([vid, title, so['summary'], (it or {}).get('body', ''), (((c or {}).get('milnor') or {}).get('statement') or '') if c else '']).lower()
            search = re.sub(r'\s+', ' ', html.escape(search, quote=True))[:4000]
            parts.append(f'<article class="item" id="item-{esc(vid)}" data-id="{esc(vid)}" data-n="{n}" data-v="{esc(v)}" data-page="{esc(page)}" data-summary="{esc(so["summary"])}" data-s="{search}">')
            parts.append(f'<div class="ihead"><span class="num">{n}</span><a class="vid" href="#item-{esc(vid)}">{esc(vid)}</a><h3>{md_inline(title)}</h3>'
                         + (f'<span class="verdict">{esc(VERDICT_NAME.get(v, v))}</span>' if v else '') + '</div>')
            parts.append(f'<p class="summary"><span class="lbl">to confirm</span>{md_inline(so["summary"])}</p>')
            if c and c.get('chips'):
                parts.append('<div class="chips">' + ''.join(f'<span class="chip">{md_inline(ch)}</span>' for ch in c['chips']) + '</div>')
            parts.append('<details class="full"><summary>the full statement, Milnor beside Lean</summary><div class="cols">')
            if c and (c.get('milnor') or {}).get('statement'):
                m = c['milnor']
                parts.append(f'<div class="col book"><p class="clabel">Milnor <span class="src">{esc(m.get("label") or "")}</span></p>{md_block(m["statement"])}'
                             + (f'<p class="note"><em>{md_inline(m["note"])}</em></p>' if m.get('note') else '') + '</div>')
            else:
                parts.append('<div class="col book"><p class="clabel">Milnor</p><p><em>No comparison row for this item; the Book note on the right gives the page.</em></p></div>')
            if it:
                parts.append(f'<div class="col lean"><p class="clabel">Verified edition <span class="src">{esc(vid)}</span></p>{md_block(it["body"])}'
                             + ('<div class="names">' + ''.join(f'<code>{esc(x)}</code>' for x in it['names']) + '</div>' if it['names'] else '') + '</div>')
            else:
                parts.append('<div class="col lean"><p class="clabel">Verified edition</p><p><em>Item not found in the verified edition.</em></p></div>')
            parts.append('</div>')
            if c and c.get('diff'):
                parts.append('<div class="diff"><p class="dlabel">What differs (the comparison)</p><ul>' + ''.join(f'<li>{md_inline(d)}</li>' for d in c['diff']) + '</ul></div>')
            parts.append('</details>')
            parts.append(f'<div class="sign"><label class="ok"><input type="checkbox" class="ok">says what Milnor means</label>'
                         f'<textarea placeholder="Notes or objection (saved as you type)"></textarea></div>')
            parts.append('</article>')
        parts.append('</section>')
    parts.append(f'<p class="foot">{total} sign-off items of the verified edition (`Exposition/Verification.md`), with the comparison\'s rows where they exist. '
                 f'Built by `build_signoff.py`. Ticks and notes live in this browser only until exported.</p></div><script>{JS}</script></body></html>')
    out = b['out']
    open(out, 'w', encoding='utf-8').write(''.join(parts))
    def resolved(vid):
        if vid in items: return True
        base = re.match(r'(V[\w]*\.[\w]+)', vid)
        return bool(base and base.group(1) in items)
    missing = [so['vid'] for so in signoff if not resolved(so['vid'])]
    nocmp = sum(1 for so in signoff if so['vid'] not in cmp)
    print(f"{book}: {total} items, {len(order)} sections → {os.path.relpath(out)} ({os.path.getsize(out)//1024} KB); "
          f"{len(missing)} items without a V-item text{(' ' + str(missing)) if missing else ''}; {nocmp} without a comparison row")


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--book', choices=list(BOOKS) + ['all'], default='morse')
    a = ap.parse_args()
    for bk in (list(BOOKS) if a.book == 'all' else [a.book]):
        build(bk)
