#!/usr/bin/env python3
"""The shortest path to the main theorems, read off the Lean dependency graph.

Input: `Exposition/shortest/deps.jsonl`, written by `DepDump.lean` (see there). Output, in
`Exposition/shortest/`:

  onpath.txt    every project declaration (Morse or Milnor) that some main theorem uses,
                transitively, with its module and the first main theorem (in TARGETS order) that
                needs it
  items.json    the results of the verified edition (V-items) that lie on the path: their
                on-path declarations, the on-path items each one uses, the targets that use it
  data/chNN.md  for each chapter of the shortest path: its items in dependency order, the items of
                the same Milnor sections that are off the path, and the on-path declarations first
                needed there (the briefing for whoever writes the chapter)

Usage: python3 Exposition/shortest/deps.py [--stats]
"""
import json, re, sys, pathlib, collections

HERE = pathlib.Path(__file__).resolve().parent
EXP = HERE.parent
VER = EXP / 'verification'

# The main theorems, in the order of the path. Each is (label, description, chapter, declarations).
TARGETS = [
    ('2.2', 'Lemma 2.2: the lemma of Morse, on a manifold', 1, ['Morse.morse_lemmaM']),
    ('3.1', 'Theorem 3.1: no critical values, no change of homotopy type', 2, ['Morse.theorem_3_1_submanifold']),
    ('3.2', 'Theorem 3.2: crossing a critical level attaches a cell', 2, ['Morse.theorem_3_2_attach_submanifold']),
    ('3.5', 'Theorem 3.5: a compact manifold is a cell complex, one cell per critical point', 2, ["Morse.theorem_3_5_count'"]),
    ('6.6', 'Theorem 6.6: Morse functions exist (almost every $L_p$)', 3, ['Morse.ae_isMorseFunction_normSq_sub']),
    ('5.2', 'Theorem 5.2 and the Euler characteristic: the Morse inequalities', 4,
     ['Morse.Homology.bettiNumber_le_critCount', 'Morse.Homology.sum_bettiNumber_eq_sum_critCount']),
    ('15.1', 'Theorem 15.1: the Morse index theorem', 6, ['Morse.theorem_15_1']),
    ('17.1', 'Theorem 17.1: piecewise smooth paths suffice', 7, ['Morse.theorem_17_1']),
    ('17.3', 'Theorem 17.3: the fundamental theorem of Morse theory', 7, ['Morse.theorem_17_3']),
    ('22.1', 'Theorem 22.1: whole manifolds of minimal geodesics', 8, ['Morse.theorem_22_1']),
    ('23.5', 'The periodicity theorem and Theorem 23.5: Bott periodicity for the unitary group ($\\pi_{2k+1}U(m) \\cong \\mathbb Z$)', 9,
     ['Morse.theorem_23_5_mulEquiv', 'Morse.periodicity_theorem_stable']),
    ('24.7', 'Theorem 24.7: Bott periodicity for the orthogonal group', 10, ['Morse.theorem_24_7']),
]

CHAPTERS = {  # chapter: (title, verified-edition chapters whose on-path items it covers)
    1: ('Critical points and the lemma of Morse', ['V1', 'V5']),
    2: ('Sublevel sets and attached cells', ['V2']),
    3: ('Morse functions exist', ['V4']),
    4: ('Homology and the Morse inequalities', ['V3']),
    5: ('Geodesics on a submanifold', ['V6', 'V7', 'V11']),
    6: ('Energy, Jacobi fields and the index theorem', ['V8', 'V9']),
    7: ('The path space and the fundamental theorem', ['V10', 'VA']),
    8: ('Whole manifolds of minimal geodesics', ['V13']),
    9: ('Bott periodicity for the unitary group', ['V12', 'V14']),
    10: ('Bott periodicity for the orthogonal group', ['V15']),
}

# Results placed outside the chapter of their Milnor section, because an earlier chapter needs them:
# the tangent projection is part of the setting (Chapter 1 uses it); exp on its whole domain uses
# Lemma 14.4; the stability of homotopy groups and the stable form of the unitary periodicity
# theorem are needed by Theorem 23.5.
ITEM_CHAPTER = {'V6.1': 1, 'V11.1': 6, 'V15.44': 9, 'V15.46': 9}

# Lean files whose on-path declarations are described in a given chapter (first match wins).
FILE_CHAPTER = [
    ('Morse.Chapter1.', 1), ('Morse.Chapter6.Projection', 1), ('Morse.Chapter11.ExpSmooth', 6),
    ('Morse.Chapter15.StablePeriodicity', 9), ('Morse.Homotopy.BundlesOrthogonal', 9), ('Morse.Flow.', 2), ('Morse.Chapter2.', 2), ('Morse.Chapter4.', 3),
    ('Morse.Chapter3.', 4), ('Morse.Homology.', 4), ('Morse.Chapter6.', 5), ('Morse.Chapter7.', 5),
    ('Morse.Chapter11.', 5), ('Morse.Chapter8.', 6), ('Morse.Chapter9.', 6), ('Morse.Chapter10.', 7),
    ('Morse.Appendix.', 7), ('Morse.Chapter13.Componentwise', 10), ('Morse.Chapter13.', 8),
    ('Morse.Homotopy.CellAttach', 8), ('Morse.Homotopy.PushOff', 8), ('Morse.Homotopy.BundlesOrthogonal', 10),
    ('Morse.Homotopy.', 9), ('Morse.Chapter12.', 9), ('Morse.Chapter14.', 9), ('Morse.Chapter15.', 10),
]

STRIP = {'rec', 'recOn', 'casesOn', 'noConfusion', 'noConfusionType', 'below', 'brecOn', 'binductionOn',
         'ibelow', 'mk', 'sizeOf_spec', 'injEq', 'inj', 'eq_def', 'ext_iff'}


def canon(n):
    """The user-facing declaration an auxiliary one belongs to (proof terms, matchers, private names)."""
    m = re.match(r'_private\.(?:[^.]+\.)*?0\.(.*)$', n)
    if m:
        n = m.group(1)
    parts = n.split('.')
    while len(parts) > 1 and (parts[-1].startswith('_') or parts[-1] in STRIP
                              or re.fullmatch(r'(match|proof|eq|fun|lambda)_\d+', parts[-1])):
        parts.pop()
    return '.'.join(parts)


def load():
    G = collections.defaultdict(set)
    info = {}
    for line in open(HERE / 'deps.jsonl'):
        d = json.loads(line)
        c = canon(d['n'])
        if d['n'] == c or c not in info:
            info[c] = {'m': d['m'], 'k': d['k'], 'l': d['l']}
        for x in d['t'] + d['v']:
            cx = canon(x)
            if cx != c:
                G[c].add(cx)
    return G, info


def closure(G, roots):
    seen, todo = set(), list(roots)
    while todo:
        n = todo.pop()
        if n not in seen:
            seen.add(n)
            todo.extend(G.get(n, ()))
    return seen


def vitems():
    out = []
    for f in sorted(VER.glob('ch*.md')):
        for p in f.read_text().split('\n\n'):
            flat = ' '.join(p.split('\n'))
            m = re.match(r'\*\*(V[0-9A]+\.\d+) \((.*?)\)\.\*\*', flat)
            if m:
                head = m.group(2)
                out.append((m.group(1), re.split(r';\s*`', head)[0],
                            re.findall(r'`((?:Morse|Milnor)\.[^`]+)`', head)))
    return out


def vkey(v):
    a, b = v.split('.')
    return (int(a[1:]) if a[1:].isdigit() else 99, int(b))


def topo(ids, deps):
    """Dependency order (prerequisites first), ties and cycles broken by V-number."""
    ids = sorted(ids, key=vkey)
    done, out = set(), []
    def visit(v, stack):
        if v in done or v in stack:
            return
        stack.add(v)
        for d in sorted(deps.get(v, ()), key=vkey):
            if d in ids_set:
                visit(d, stack)
        stack.discard(v)
        done.add(v)
        out.append(v)
    ids_set = set(ids)
    for v in ids:
        visit(v, set())
    return out


def main(stats=False):
    G, info = load()
    first, union = {}, set()
    for label, _, _, roots in TARGETS:
        missing = [r for r in roots if r not in info]
        if missing:
            sys.exit(f'unknown target declarations: {missing}')
        cl = closure(G, roots)
        for n in cl - union:
            first[n] = label
        union |= cl
    union = {n for n in union if n in info}
    with open(HERE / 'onpath.txt', 'w') as f:
        f.write('# declaration  module  first-target  (generated by deps.py)\n')
        for n in sorted(union):
            f.write(f'{n}  {info[n]["m"]}  {first[n]}\n')
    tcl = {label: closure(G, roots) for label, _, _, roots in TARGETS}
    items, off = {}, []
    for vid, title, names in vitems():
        known = [n for n in names if n in info]
        on = [n for n in known if n in union]
        if on:
            items[vid] = {'title': title, 'on': on, 'off': [n for n in known if n not in union],
                          'targets': [t for t, _, _, _ in TARGETS if any(n in tcl[t] for n in on)]}
        elif known:
            off.append((vid, title))
    owner = collections.defaultdict(set)
    for vid, it in items.items():
        for n in it['on']:
            owner[n].add(vid)
    for vid, it in items.items():
        ds = set()
        for n in closure(G, it['on']):
            ds |= owner.get(n, set())
        ds.discard(vid)
        it['uses'] = sorted(ds, key=vkey)
    # direct prerequisites: drop those implied through another prerequisite
    for vid, it in items.items():
        indirect = set()
        for d in it['uses']:
            indirect |= set(items[d]['uses']) - {vid}
        it['direct'] = [d for d in it['uses'] if d not in indirect or vid in items[d]['uses']]
    json.dump({'targets': [{'label': t, 'what': w, 'chapter': c, 'decls': r,
                            'items': [v for v, it in items.items() if t in it['targets']],
                            'decl_count': len([n for n in tcl[t] if n in info])}
                           for t, w, c, r in TARGETS],
               'items': items, 'off': off,
               'counts': {'project': sum(1 for n in info if info[n]['m'].startswith('Morse.')),
                          'milnor': sum(1 for n in info if info[n]['m'].startswith('Milnor.')),
                          'onpath_project': sum(1 for n in union if info[n]['m'].startswith('Morse.')),
                          'onpath_milnor': sum(1 for n in union if info[n]['m'].startswith('Milnor.'))}},
              open(HERE / 'items.json', 'w'), ensure_ascii=False, indent=1)
    # briefing per chapter
    tagged = set()
    sys.path.insert(0, str(EXP))
    import check_trace as CT
    for f in (EXP / 'pbp').glob('part*.md'):
        for m in CT.TAG.finditer(f.read_text()):
            r = CT.resolve(m.group(1), m.group(2))
            if r:
                tagged.add(r['full'])
    def chapter_of_file(m):
        for pre, c in FILE_CHAPTER:
            if m.startswith(pre):
                return c
        return None
    for c, (title, vch) in CHAPTERS.items():
        mine = [v for v in items if ITEM_CHAPTER.get(v, c if v.split('.')[0] in vch else None) == c]
        order = topo(mine, {v: items[v]['uses'] for v in items})
        L = [f'# Chapter {c} data: {title}', '',
             'Generated by `Exposition/shortest/deps.py` from the Lean dependency graph. Do not edit.', '']
        tg = [t for t in TARGETS if t[2] == c]
        if tg:
            L += ['## Main theorems proved in this chapter', '']
            L += [f'- {t[1]} (`{"`, `".join(t[3])}`)' for t in tg] + ['']
        L += ['## Results on the path, in dependency order', '',
              'Each: verified-edition number and title; the targets that need it; its on-path '
              'declarations; the declarations the verified edition cites for it that are NOT on the path '
              '(leave those parts out); the on-path results it uses directly.', '']
        for v in order:
            it = items[v]
            L.append(f'- **{v}** {it["title"]} — needed for: {", ".join(it["targets"])}')
            L.append(f'  - on path: {", ".join("`" + n + "`" for n in it["on"])}')
            if it['off']:
                L.append(f'  - off path (omit): {", ".join("`" + n + "`" for n in it["off"])}')
            if it['direct']:
                L.append(f'  - uses: {", ".join(it["direct"])}')
        offc = [(v, t) for v, t in off if v.split('.')[0] in vch]
        moved = sorted((v for v in items if v.split('.')[0] in vch and ITEM_CHAPTER.get(v, c) != c), key=vkey)
        if moved:
            L += ['', '## Results of these sections placed in another chapter (refer to them by number; do not '
                  're-prove them)', '']
            L += [f'- {v} {items[v]["title"]} → Chapter {ITEM_CHAPTER[v]}' for v in moved]
        if offc:
            L += ['', '## Results of these sections that are OFF the path (leave out; at most one '
                  'sentence in the chapter introduction saying what is skipped)', '']
            L += [f'- {v} {t}' for v, t in offc]
        decls = [n for n in union if info[n]['m'].startswith('Morse.') and chapter_of_file(info[n]['m']) == c]
        bym = collections.defaultdict(list)
        for n in decls:
            bym[info[n]['m']].append(n)
        L += ['', '## On-path Lean declarations described in this chapter, by file', '',
              'T = theorem, D = definition or structure; * = traced in the proof by proof; '
              '[x] = first main theorem that needs it.', '']
        for m in sorted(bym):
            L.append(f'### {m.replace("Morse.", "").replace(".", "/")}.lean ({len(bym[m])})')
            for n in sorted(bym[m], key=lambda n: info[n]['l'] or 0):
                k = 'T' if info[n]['k'] == 'thm' else 'D'
                L.append(f'- {k}{"*" if n in tagged else " "} `{n}` (line {info[n]["l"]}) [{first[n]}]')
            L.append('')
        (HERE / 'data' / f'ch{c:02d}.md').write_text('\n'.join(L) + '\n')
    if stats:
        c = json.load(open(HERE / 'items.json'))['counts']
        print(c, f'{len(items)} items on the path, {len(off)} off')
        for t in json.load(open(HERE / 'items.json'))['targets']:
            print(f'  {t["label"]:5s} {t["decl_count"]:5d} declarations  {len(t["items"]):4d} items  {t["what"]}')


if __name__ == '__main__':
    main('--stats' in sys.argv)
