#!/usr/bin/env python3
"""Assemble and build "Morse Theory, the shortest path".

Usage: python3 Exposition/build_shortest_path.py [--no-pdf] [--no-html]

1. Reads the chapters Exposition/shortest/s00.md … s10.md and the dependency data that
   Exposition/shortest/deps.py derives from the Lean dependency graph (items.json).
2. Fills the generated tables of Chapter 0, gives every section an anchor, and turns every
   reference to a result, "[V2.8]", into "[V2.8, §2.3]" with a link to the section that proves it.
3. Appends Appendix A (each result on the path and the results it uses directly), Appendix B (the
   results of the book that are off the path) and Appendix C (the path, file by file), and draws the
   chapter diagram (shortest-path-dag.png).
4. Writes Exposition/ShortestPath.md and checks it: every trace tag resolves and lies on the path,
   and every result on the path is labelled.
5. Builds ShortestPath.pdf and the web edition morse-shortest-path.html with the machinery of
   build_proofbyproof.py (pandoc and xelatex for the PDF).
"""
import base64, collections, json, pathlib, re, shutil, subprocess, sys, tempfile

EXDIR = pathlib.Path(__file__).resolve().parent
SH = EXDIR / 'shortest'
OUT = EXDIR / 'ShortestPath.md'
FIG = EXDIR / 'shortest-path-dag.png'
sys.path.insert(0, str(EXDIR))
sys.path.insert(0, str(SH))
import deps as D

TITLE = 'Morse Theory, the Shortest Path'
DEK = ("The main theorems of Milnor's Morse Theory, and exactly what their formal proofs use: a route "
       "through the book read off the dependency graph of its Lean formalization.")
# a labelled result: "**Theorem 3.2** [V2.8]", "**Lemma 23.4** ($\pi_{j+1}G_m \cong \pi_jU(m)$) [V14.26]",
# "**Definitions** [V8.4] [V8.10]"; group 3 holds the brackets
LABEL = re.compile(r'\*\*(.+?)\*\*(\s*\((?:[^()\n]|\([^()\n]*\))*\))?\s*'
                   r'((?:\[V[0-9A]+\.\d+(?:,\s*V[0-9A]+\.\d+)*\]\s*)+)')
# a reference may already carry a section, "[V1.14, §2.2]": it is recomputed
REF = re.compile(r'\[((?:V[0-9A]+\.\d+)(?:,\s*V[0-9A]+\.\d+)*)(?:,\s*§\s*[\d.]+)?\](?!\()')


def vkey(v):
    return D.vkey(v)


def chapter_of(items):
    out = {}
    for c, (_, vch) in D.CHAPTERS.items():
        for v in items:
            if D.ITEM_CHAPTER.get(v, c if v.split('.')[0] in vch else None) == c:
                out[v] = c
    return out


def anchors(text):
    """Give `## N. Title` and `### N.k Title` headings explicit ids."""
    text = re.sub(r'(?m)^## (\d+)\. (.+?)[ \t]*$', lambda m: f'## {m.group(1)}. {m.group(2)} {{#ch-{m.group(1)}}}', text)
    text = re.sub(r'(?m)^### (\d+)\.(\d+) (.+?)[ \t]*$',
                  lambda m: f'### {m.group(1)}.{m.group(2)} {m.group(3)} {{#sec-{m.group(1)}-{m.group(2)}}}', text)
    return text


def label_index(text):
    """V-number -> the section (N.k) where it is labelled as a result."""
    where, sec = {}, None
    for line in text.split('\n'):
        m = re.match(r'### (\d+\.\d+) ', line)
        if m:
            sec = m.group(1)
        m2 = re.match(r'## (\d+)\. ', line)
        if m2:
            sec = m2.group(1)
        for lm in LABEL.finditer(line):
            for v in re.findall(r'V[0-9A]+\.\d+', lm.group(3)):
                where.setdefault(v, sec)
    return where


def link(sec):
    if sec is None:
        return '§?'
    a = 'sec-' + sec.replace('.', '-') if '.' in sec else 'ch-' + sec
    return f'[§{sec}](#{a})'


def resolve_refs(text, where):
    """Leave defining labels alone; turn every other [Vx.y] into [Vx.y, §N.k]."""
    out, missing = [], set()
    for line in text.split('\n'):
        spans = [m.span(3) for m in LABEL.finditer(line)]
        def rep(m):
            s, e = m.span(1)
            if any(a <= s and e <= b for a, b in spans):
                return m.group(0)
            parts = []
            for v in re.split(r',\s*', m.group(1)):
                if v not in where:
                    missing.add(v)
                parts.append(f'{v}, {link(where.get(v))}')
            return '[' + '; '.join(parts) + ']'
        out.append(REF.sub(rep, line))
    return '\n'.join(out), missing


def targets_table(data, chof):
    rows = ['| Main theorem | Ch. | Decls. | Results | Needs chapters |',
            '|:---------------------------------------------|:---|-------:|-------:|:-------------|']
    for t in data['targets']:
        chs = sorted({chof[v] for v in t['items']} | {t['chapter']})
        name, _, what = t['what'].partition(': ')
        rows.append(f'| **{name}**: {what} | {t["chapter"]} | {t["decl_count"]:,} | {len(t["items"])} | '
                    f'{", ".join(str(c) for c in chs)} |')
    return '\n'.join(rows)


def counts_par(data):
    c = data['counts']
    n_items, n_off = len(data['items']), len(data['off'])
    return (f'Of the {c["project"]:,} declarations of this project, {c["onpath_project"]:,} are on the path '
            f'({100 * c["onpath_project"] / c["project"]:.0f}%); of the {c["milnor"]:,} of the companion '
            f'project, {c["onpath_milnor"]:,} are. Of the results of the verified edition, {n_items} are on the '
            f'path and {n_off} are not.')


def appendix_a(data, chof, where):
    L = ['## Appendix A. The dependency map', '',
         'For each result on the path: where it is proved, the main theorems that need it, and the results '
         'on the path that its formal proof uses directly (those it uses only through another listed result '
         'are omitted). Generated from the Lean dependency graph by `Exposition/shortest/deps.py`.', '']
    items = data['items']
    for c, (title, _) in D.CHAPTERS.items():
        mine = sorted((v for v in items if chof[v] == c), key=lambda v: (where.get(v) or '99', vkey(v)))
        if not mine:
            continue
        L += [f'**Chapter {c}. {title}.**', '']
        for v in mine:
            it = items[v]
            uses = '; '.join(f'{u} ({link(where.get(u))})' for u in it['direct']) or 'nothing on the path'
            L.append(f'- {v} ({link(where.get(v))}), {it["title"]}. *For* {", ".join(it["targets"])}. *Uses* {uses}.')
        L.append('')
    return '\n'.join(L)


def appendix_b(data):
    L = ['## Appendix B. What is left out', '',
         'The results of the verified edition that no main theorem uses: none of their declarations is on '
         'the path. They are true and machine-checked, and many are interesting, but the main theorems do '
         'not need them. Grouped by the chapter of the verified edition (the Milnor sections in brackets).', '']
    sects = {'V1': '§§1–2', 'V2': '§3', 'V3': '§§4–5', 'V4': '§6', 'V5': '§7', 'V6': '§§8–9', 'V7': '§10',
             'V8': '§§11–13', 'V9': '§§14–15', 'V10': '§§16–17', 'V11': '§§18–19', 'V12': '§§20–21',
             'V13': '§22', 'V14': '§23', 'V15': '§24', 'VA': 'Appendix'}
    by = collections.defaultdict(list)
    for v, t in data['off']:
        by[v.split('.')[0]].append((v, t))
    for k in sorted(by, key=lambda k: vkey(k + '.0')):
        L.append(f'- **{k} ({sects.get(k, "")})**: ' + '; '.join(f'{v} {t}' for v, t in sorted(by[k], key=lambda x: vkey(x[0]))) + '.')
    return '\n'.join(L) + '\n'


def appendix_c():
    info = {}
    for line in open(SH / 'onpath.txt'):
        if not line.startswith('#'):
            n, m, _ = line.split()
            info[n] = m
    tot = collections.Counter()
    on = collections.Counter()
    for line in open(SH / 'deps.jsonl'):
        d = json.loads(line)
        c = D.canon(d['n'])
        if d['n'] != c or not d['m'].startswith('Morse.'):
            continue
        top = '/'.join(d['m'].split('.')[1:2])
        tot[top] += 1
        on[top] += c in info
    L = ['## Appendix C. The path, directory by directory', '',
         'Declarations of each directory of `Morse/Morse/` (user-facing ones, auxiliary proof terms folded into '
         'their declaration) and how many of them are on the path.', '',
         '| Directory | Declarations | On the path |', '|:--|--:|--:|']
    order = ['Chapter1', 'Flow', 'Chapter2', 'Chapter3', 'Homology', 'Chapter4', 'Chapter5', 'Chapter6', 'Chapter7',
             'Chapter8', 'Chapter9', 'Chapter10', 'Appendix', 'Chapter11', 'Chapter12', 'Chapter13', 'Homotopy',
             'Chapter14', 'Chapter15']
    for k in order + sorted(set(tot) - set(order)):
        if tot[k]:
            L.append(f'| `{k}` | {tot[k]:,} | {on[k]:,} ({100 * on[k] / tot[k]:.0f}%) |')
    return '\n'.join(L) + '\n'


def draw(data, chof):
    """The chapters as a layered diagram; an arrow when a result of one is used in the other."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import FancyBboxPatch
    E = set()
    for v, it in data['items'].items():
        for u in it['direct']:
            if chof[u] != chof[v]:
                E.add((chof[u], chof[v]))
    # transitive reduction
    def reach(a, b, skip):
        todo, seen = [a], set()
        while todo:
            x = todo.pop()
            for (p, q) in E:
                if p == x and (p, q) != skip and q not in seen:
                    if q == b:
                        return True
                    seen.add(q)
                    todo.append(q)
        return False
    R = {e for e in E if not reach(e[0], e[1], e)}
    main = collections.defaultdict(list)
    for t in data['targets']:
        main[t['chapter']].append(t['label'])
    pos = {1: (0.5, 6), 2: (0.17, 5), 3: (0.5, 5), 5: (0.83, 5), 4: (0.13, 4), 6: (0.83, 4), 7: (0.72, 3),
           8: (0.5, 2), 9: (0.5, 1), 10: (0.5, 0)}
    fig, ax = plt.subplots(figsize=(6.8, 6.4), dpi=150)
    ax.set_xlim(-0.05, 1.05)
    ax.set_ylim(-0.6, 6.6)
    ax.axis('off')
    for (a, b) in sorted(R):
        (x1, y1), (x2, y2) = pos[a], pos[b]
        ax.annotate('', xy=(x2, y2 + 0.32), xytext=(x1, y1 - 0.32),
                    arrowprops=dict(arrowstyle='-|>', color='#7a8494', lw=0.9, shrinkA=2, shrinkB=2))
    for c, (x, y) in pos.items():
        title = D.CHAPTERS[c][0]
        thm = ', '.join(main.get(c, []))
        w = 0.31
        import textwrap
        lines = textwrap.wrap(f'{c}. {title}', 30)
        ax.add_patch(FancyBboxPatch((x - w / 2, y - 0.3), w, 0.6, boxstyle='round,pad=0.01,rounding_size=0.03',
                                    fc='#eef2f8' if thm else '#ffffff', ec='#2b5aa8' if thm else '#9aa3b0', lw=1))
        ax.text(x, y + (0.1 if thm else 0), '\n'.join(lines), ha='center', va='center', fontsize=6.0,
                linespacing=1.15)
        if thm:
            ax.text(x, y - 0.19, 'main: ' + thm, ha='center', va='center', fontsize=5.8, color='#1e4380')
    fig.tight_layout()
    fig.savefig(FIG, dpi=150)
    plt.close(fig)


def assemble():
    data = json.load(open(SH / 'items.json'))
    chof = chapter_of(data['items'])
    parts = []
    for c in range(0, 11):
        f = SH / f's{c:02d}.md'
        if f.exists():
            parts.append(f.read_text().strip())
        else:
            parts.append(f'## {c}. {D.CHAPTERS[c][0]}\n\n*(Chapter not yet written.)*')
    body = '\n\n'.join(parts)
    body = body.replace('<!-- generated: targets -->', targets_table(data, chof))
    body = body.replace('<!-- generated: counts -->', counts_par(data))
    body = body.replace('### 0.1 The main theorems', '### 0.1 The main theorems', 1)
    draw(data, chof)
    fig_md = (f'![The chapters of this text. An arrow means that a result of one chapter is used in the other '
              f'(arrows implied by others omitted); shaded chapters prove a main theorem.]({FIG.name})')
    body = body.replace('### 0.2 How the path was found', fig_md + '\n\n### 0.2 How the path was found', 1)
    body = anchors(body)
    where = label_index(body)
    body, missing = resolve_refs(body, where)
    body += '\n\n' + appendix_a(data, chof, where) + '\n' + appendix_b(data) + '\n' + appendix_c()
    text = f'# {TITLE}\n\n*{DEK}*\n\n{body}\n'
    OUT.write_text(text)
    print(f'{OUT.name}: {len(text.split()):,} words')
    if missing:
        print('  REFERENCES TO RESULTS NOT LABELLED ANYWHERE:', ', '.join(sorted(missing, key=vkey)))
    unlabelled = [v for v in data['items'] if v not in where]
    if unlabelled:
        print(f'  {len(unlabelled)} results on the path not labelled:', ', '.join(sorted(unlabelled, key=vkey)))
    import check as C
    C.main(str(OUT))
    return data


def build(want):
    import build_proofbyproof as B
    B.SRC = OUT
    B.TITLE = TITLE
    B.SUBTITLE = "The main theorems of Milnor's Morse Theory and what their formal proofs use"
    B.EYEBROW = 'Milnor · Morse Theory · the shortest path'
    B.H1 = 'Morse Theory, <em>the shortest path</em>'
    B.SAMPLE = ('Chapter2/CellAttachSubmanifold', 'theorem_3_2_attach_submanifold')
    B.LEGEND = ('A trace tag looks like this: {tag}, a file of the project and the declaration in it that '
                'proves the sentence; every tag in this text names a declaration on the path. Each chapter '
                'opens on its own; use the contents or the links at the end of a chapter.')
    B.FOOTER = ('Every declaration named here is on the path of the main theorems, checked by Lean’s kernel, '
                'and depends only on propext, Classical.choice and Quot.sound. Source: Morse/*.lean; this '
                'text: Exposition/ShortestPath.md; the path: Exposition/shortest/.')
    md, title, occ = B.source()
    decls, bad = B.resolve(occ)
    if bad:
        sys.exit(f'{len(bad)} unresolved trace tags: nothing built')
    ids = B.tag_ids(decls)
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        if 'html' in want:
            B.build_html(md, occ, decls, ids, tmp)
            html = (tmp / 'morse-proof-by-proof.html').read_text()
            png = 'data:image/png;base64,' + base64.b64encode(FIG.read_bytes()).decode()
            html = html.replace(f'src="{FIG.name}"', f'src="{png}"')
            (EXDIR / 'morse-shortest-path.html').write_text(html)
            preview = (tmp / 'preview-pbp.html').read_text().replace(f'src="{FIG.name}"', f'src="{png}"')
            (EXDIR / 'preview-shortest.html').write_text(preview)
            print(f'  wrote {EXDIR / "morse-shortest-path.html"}')
        if 'pdf' in want:
            cwd = pathlib.Path.cwd()
            try:
                import os
                os.chdir(EXDIR)
                B.build_pdf(md, title, occ, decls, tmp)
            finally:
                os.chdir(cwd)
            shutil.copy(tmp / 'ProofByProof.pdf', EXDIR / 'ShortestPath.pdf')
            print(f'  wrote {EXDIR / "ShortestPath.pdf"}')


if __name__ == '__main__':
    args = sys.argv[1:]
    assemble()
    want = tuple(w for w in ('html', 'pdf') if '--no-' + w not in args)
    if want:
        build(want)
