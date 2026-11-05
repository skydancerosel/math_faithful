"""Summaries of the round-trip results for REPORT.md.

Reads Items/*.json (prover records) and $RT_DIR/keys/*.json (the comparison's labels, never shown to
provers) and prints Markdown tables: label × relation, by chapter, the embedded special case, the
blind statements refuted (not_B), revised verdicts, and vacuous directions.
Usage: RT_DIR=… python3 RoundTrip/harness/summarize.py [--rows]
"""
import json, glob, os, sys, collections

R = os.environ.get('RT_DIR', '/tmp/claude-0/rt')
here = os.path.dirname(os.path.abspath(__file__))
REL = ['equivalent', 'A_stronger', 'A_narrower', 'incomparable', 'unclear']
EXP = {'same': 'equivalent', 'explicit': 'equivalent', 'restated': 'equivalent',
       'stronger': 'A_stronger', 'narrower': 'A_narrower', 'sign': 'incomparable'}


def chap(i):
    c = i.split('_')[0]
    return c


def chapkey(c):
    return (1, 0) if c == 'VA' else (0, int(c[1:]))


rows = []
for f in sorted(glob.glob(os.path.join(here, '../Items/*.json'))):
    r = json.load(open(f))
    i = os.path.basename(f)[:-5]
    k = json.load(open(f'{R}/keys/{i}.json'))
    rows.append((i, k, r))

print(f'{len(rows)} items\n')


def logic(r):
    """The relation the proved directions establish, ignoring vacuous ones (a direction proved
    without using its hypothesis says nothing about the other side)."""
    if r.get('not_B') or r.get('A_to_B') == 'false':
        return 'B false'
    uh = r.get('uses_hypothesis') if isinstance(r.get('uses_hypothesis'), dict) else {}
    ab = r.get('A_to_B') == 'proved' and uh.get('A_to_B', True)
    ba = r.get('B_to_A') == 'proved' and uh.get('B_to_A', True)
    return {(True, True): 'equivalent', (True, False): 'A ⇒ B only', (False, True): 'B ⇒ A only',
            (False, False): 'neither'}[(ab, ba)]


lt = collections.Counter(logic(r) for i, k, r in rows)
print('proved directions (non-vacuous):', dict(lt), '\n')
print('| label \\ proved | equivalent | A ⇒ B only | B ⇒ A only | neither | B false | n |')
print('|---|---|---|---|---|---|---|')
for l in ['same', 'explicit', 'restated', 'stronger', 'narrower', 'sign']:
    c = collections.Counter(logic(r) for i, k, r in rows if k['verdict'] == l)
    if c:
        print(f"| {l} | {c['equivalent']} | {c['A ⇒ B only']} | {c['B ⇒ A only']} | {c['neither']} | {c['B false']} | {sum(c.values())} |")
print()

# label × relation
tab = collections.Counter((k['verdict'], r['relation']) for i, k, r in rows)
labels = ['same', 'explicit', 'restated', 'stronger', 'narrower', 'sign']
print('| label \\ logic | ' + ' | '.join(REL[:4]) + ' | n |')
print('|---|' + '---|' * 5)
for l in labels:
    n = sum(tab[(l, x)] for x in REL)
    if n:
        print(f'| {l} | ' + ' | '.join(str(tab[(l, x)]) for x in REL[:4]) + f' | {n} |')
print()

# match / partial / mismatch
m = collections.Counter()
for i, k, r in rows:
    e = EXP.get(k['verdict'])
    rel = r['relation']
    m['match' if rel == e else ('partial' if rel == 'incomparable' and k['verdict'] in ('narrower', 'stronger') else 'mismatch')] += 1
print('label vs logic:', dict(m), '\n')

# by chapter
print('| chapter | n | equivalent | A stronger | A narrower | incomparable | B false | embedded proved / one way / failed / n.a. |')
print('|---|---|---|---|---|---|---|---|')
by = collections.defaultdict(list)
for i, k, r in rows:
    by[chap(i)].append(r)
for c in sorted(by, key=chapkey):
    rs = by[c]
    cnt = collections.Counter(x['relation'] for x in rs)
    nb = sum(1 for x in rs if x.get('not_B'))
    em = collections.Counter(x.get('embedded_special_case', '—') for x in rs)
    one = em['A_to_Bemb_only'] + em['Bemb_to_A_only'] + em['proved_partial']
    print(f"| {c} | {len(rs)} | {cnt['equivalent']} | {cnt['A_stronger']} | {cnt['A_narrower']} | {cnt['incomparable']} | {nb} | "
          f"{em['proved']} / {one} / {em['failed']} / {em['not_applicable'] + em['—'] + em['not_attempted']} |")
print()

# embedded special case overall
em = collections.Counter(r.get('embedded_special_case', '—') for i, k, r in rows)
print('embedded special case:', dict(em), '\n')

# B false
print('B false (not_B proved or A_to_B false):')
for i, k, r in rows:
    if r.get('not_B') or r.get('A_to_B') == 'false':
        print(f"- {i}: {(r.get('B_issue') or '')[:160]}")
print()

# revised
print('revised:', ', '.join(i for i, k, r in rows if r.get('revised')), '\n')

# vacuous
vac = [i for i, k, r in rows if isinstance(r.get('uses_hypothesis'), dict)
       and any(r['A_to_B' if d == 'A_to_B' else 'B_to_A'] == 'proved' and not v for d, v in r['uses_hypothesis'].items())]
print(f'directions proved without using the hypothesis (vacuous): {len(vac)}: ' + ', '.join(vac), '\n')

if '--rows' in sys.argv:
    print('| item | title | label | A→B | B→A | relation | embedded | note |')
    print('|---|---|---|---|---|---|---|---|')
    for i, k, r in sorted(rows, key=lambda x: (chapkey(chap(x[0])), x[0])):
        why = (r.get('why') or '').replace('|', '/').replace('\n', ' ')
        print(f"| {k['id']} | {k['title']} | {k['verdict']} | {r['A_to_B']} | {r['B_to_A']} | {r['relation']}"
              f"{' **B false**' if r.get('not_B') else ''} | {r.get('embedded_special_case', '—')} | {why[:200]}… |")
