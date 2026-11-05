#!/usr/bin/env python3
"""Check a chapter of "Morse Theory, the shortest path" against the Lean dependency graph.

Usage: python3 Exposition/shortest/check.py Exposition/shortest/s02.md [--chapter 2]

1. Every trace tag ⟦Path · name⟧ must resolve to a declaration (as in Exposition/check_trace.py).
2. Every tag into this project or the Milnor project must name a declaration ON the path
   (listed in Exposition/shortest/onpath.txt): the text may only use what the main theorems use.
   Tags into Mathlib are allowed.
3. With --chapter k: every result that Exposition/shortest/data/chNN.md lists as on the path must
   be labelled somewhere in the file by its verified-edition number, as "[V2.8]", and no result
   that is off the path may be labelled.
Also prints the number of words.
"""
import re, sys, json, pathlib
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import check_trace as CT

STRIP = None


def main(path, chapter=None):
    sys.path.insert(0, str(HERE))
    from deps import canon
    onpath = {l.split()[0] for l in open(HERE / 'onpath.txt') if not l.startswith('#')}
    text = pathlib.Path(path).read_text()
    bad, off, n = [], [], 0
    for m in CT.TAG.finditer(text):
        n += 1
        p, name = m.group(1), m.group(2)
        r = CT.resolve(p, name)
        if r is None:
            bad.append(f'{p} · {name}')
        elif not p.startswith('Mathlib/') and canon(r['full']) not in onpath:
            off.append(f'{p} · {name} ({r["full"]})')
    print(f'{path}: {len(text.split()):,} words, {n} trace tags, {len(bad)} unresolved, {len(off)} off the path')
    for b in bad:
        print('  UNRESOLVED', b)
    for o in off:
        print('  OFF PATH  ', o)
    problems = len(bad) + len(off)
    if chapter is not None:
        items = json.load(open(HERE / 'items.json'))
        data = (HERE / 'data' / f'ch{chapter:02d}.md').read_text()
        want = re.findall(r'^- \*\*(V[0-9A]+\.\d+)\*\*', data, re.M)
        offv = {v for v, _ in items['off']}
        labels = set()
        for b in re.findall(r'\[(V[0-9A]+\.\d+[^\]]*)\]', text):
            labels |= set(re.findall(r'V[0-9A]+\.\d+', b))
        missing = [v for v in want if v not in labels]
        offl = sorted(l for l in labels if l in offv)
        print(f'  coverage: {len(want) - len(missing)}/{len(want)} on-path results labelled')
        if missing:
            print('  MISSING', ', '.join(missing))
        if offl:
            print('  OFF-PATH RESULT LABELLED', ', '.join(offl))
        problems += len(missing) + len(offl)
    return problems


if __name__ == '__main__':
    args = sys.argv[1:]
    ch = None
    if '--chapter' in args:
        i = args.index('--chapter')
        ch = int(args[i + 1])
        del args[i:i + 2]
    sys.exit(1 if main(args[0], ch) else 0)
