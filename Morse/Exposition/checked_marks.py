#!/usr/bin/env python3
"""Mark the numbered results of the rewritten book with what the machine checked.

The comparison (`Exposition/cmp/*.json`) gives, for every result of the book, its number in the
verified edition (V2.8, ...) and how the checked statement compares with Milnor's (its verdict).
`mark(name, md)` puts that after the bold label of each numbered result in the chapter `name`
("**Theorem 3.2.**" becomes "**Theorem 3.2.** *(checked by machine: V2.6, V2.8, in a narrower
form)*"); the first mark of a chapter carries a footnote that explains the verdicts. Used by
`build.py` (PDFs, per-chapter web pages) and `build_book.py` (the single-page web edition); the
Markdown sources are not changed.

Usage: python3 checked_marks.py      lists, chapter by chapter, the results marked and those whose
                                      label was not found in the text.
"""
import glob, json, os, re

HERE = os.path.dirname(os.path.abspath(__file__))

# Milnor's section -> chapter of the rewritten book
SECTION_CHAPTER = {1: 1, 2: 1, 3: 2, 4: 3, 5: 3, 6: 4, 7: 5, 8: 6, 9: 6, 10: 7, 11: 8, 12: 8, 13: 8,
                   14: 9, 15: 9, 16: 10, 17: 10, 18: 11, 19: 11, 20: 12, 21: 12, 22: 13, 23: 14,
                   24: 15}
VERDICT = {'same': 'as stated', 'restated': 'restated', 'explicit': 'with its hypotheses made explicit',
           'stronger': 'in a stronger form', 'narrower': 'in a narrower form',
           'sign': 'with a sign corrected'}
LEGEND = ("Checked by machine: the result has been verified in the Lean proof assistant. The numbers are "
          "those of the verified edition and of the comparison, which give the checked statement in full. "
          "*As stated*: the same statement. *Restated*: an equivalent statement in other terms. *With its "
          "hypotheses made explicit*: a hypothesis the book uses silently is stated. *In a stronger form*: "
          "the checked statement says more than the book's. *In a narrower form*: it covers less, a "
          "special setting or a weaker conclusion. *With a sign corrected*: the book's statement has a "
          "slip. *Not checked*: no part of the result has been verified. The section \"Checked by "
          "machine\" at the end of the chapter says which forms were checked, and covers the results "
          "that carry no such note.")
RESULT = r'(?:Theorem|Lemma|Corollary|Remark|Assertion|Proposition|Definition)\s+[0-9A-Z][0-9.]*[0-9A-Z]?'
LABEL = re.compile(r'^(?:§(\d+)|Appendix)[^,]*,\s*(' + RESULT + r')((?:,?\s*(?:and\s+)?\(\d+\))*)')


def keys(m):
    """The result labels a comparison label names: "Lemma 24.6 (3), (5)" -> Lemma 24.6-(3), Lemma 24.6-(5)."""
    parts = re.findall(r'\((\d+)\)', m.group(3))
    return [f'{m.group(2)}-({k})' for k in parts] if parts else [m.group(2)]


def chapter_name(sec):
    return 'Appendix' if sec is None else f'Chapter{SECTION_CHAPTER[int(sec)]}'


def vkey(v):
    a, b = v[1:].split('.')
    return (int(a) if a.isdigit() else 99, int(b))


def table():
    """{chapter name: {result label: (sorted [(V, verdict)], not_checked)}}"""
    items, nf = [], []
    for f in sorted(glob.glob(os.path.join(HERE, 'cmp', '*.json'))):
        d = json.load(open(f))
        items += d['items']
        nf += d['notFormalized']
    out = {}
    for i in items:
        if i['verdict'] == 'extra':
            continue
        m = LABEL.match(i['milnor']['label'])
        for k in keys(m) if m else []:
            e = out.setdefault(chapter_name(m.group(1)), {}).setdefault(k, [[], False])
            e[0].append((i['id'], i['verdict']))
    for x in nf:
        m = LABEL.match(x['label'])
        for k in keys(m) if m else []:
            e = out.setdefault(chapter_name(m.group(1)), {}).setdefault(k, [[], False])
            e[1] = True
    return {c: {r: (sorted(v, key=lambda p: vkey(p[0])), n) for r, (v, n) in d.items()}
            for c, d in out.items()}


def phrase(checked, not_checked):
    if not checked:
        return 'not checked by machine'
    groups = {}
    for v, verdict in checked:
        groups.setdefault(verdict, []).append(v)
    parts = [f'{", ".join(vs)}, {VERDICT[verdict]}' for verdict, vs in groups.items()]
    return 'checked by machine: ' + '; '.join(parts)


def mark(name, md, report=None):
    marks = dict(table().get(name, {}))
    # a part, "Lemma 10.3-(3)", that the text does not state on its own goes with the whole result
    for k in [k for k in marks if '-(' in k and f'**{k}' not in md]:
        base = k.split('-(')[0]
        (c1, n1), (c2, n2) = marks.pop(k), marks.get(base, ([], False))
        marks[base] = (sorted(set(c1) | set(c2), key=lambda p: vkey(p[0])), n1 or n2)
    done = set()
    for result, (checked, not_checked) in marks.items():
        if not checked and not not_checked:
            continue
        # the bold label that states the result: "**Theorem 3.2.**", "**Lemma 3.6 (Whitehead).**"
        pat = re.compile(r'(?m)^(\*\*' + re.escape(result) + r'(?![0-9.]*[0-9])(?!-\()[^*\n]*\*\*)')
        m = pat.search(md)
        if not m:
            continue
        done.add(result)
        note = f' [*({phrase(checked, not_checked)})*]{{.checked}}'
        md = md[:m.end()] + note + '\0' + md[m.end():]
    # the legend goes on the first mark in the text
    i = md.find('\0')
    if i >= 0:
        md = md[:i] + f'^[{LEGEND}]' + md[i + 1:]
    md = md.replace('\0', '')
    if report is not None:
        report[name] = (sorted(done), sorted(set(marks) - done))
    return md


if __name__ == '__main__':
    names = [f'Chapter{i}' for i in range(1, 16)] + ['Appendix']
    rep = {}
    for n in names:
        mark(n, open(os.path.join(HERE, n + '.md')).read(), rep)
        done, missing = rep[n]
        print(f'{n}: {len(done)} marked' + (f'; label not found: {", ".join(missing)}' if missing else ''))
