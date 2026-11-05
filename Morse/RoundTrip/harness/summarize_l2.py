"""Summary of layer 2 (RoundTrip/L2/Items/*.json) for REPORT.md."""
import json, glob, os, collections
here = os.path.dirname(os.path.abspath(__file__))
groups = {}
for line in open(os.path.join(here, 'l2_groups.txt')):
    g, ids = line.strip().split(':')
    for i in ids.split():
        groups[i] = g
rows = []
for f in sorted(glob.glob(os.path.join(here, '../L2/Items/*.json'))):
    r = json.load(open(f)); rows.append((os.path.basename(f)[:-5], r))
print(f'{len(rows)} notions\n')
print('| group | n | equal | equal under hypotheses | differ | harmless | proved partially |')
print('|---|---|---|---|---|---|---|')
by = collections.defaultdict(list)
for i, r in rows:
    by[groups.get(i, '?')].append(r)
for g in sorted(by):
    rs = by[g]; c = collections.Counter(x['agreement'] for x in rs)
    print(f"| {g} | {len(rs)} | {c['equal']} | {c['equal_under_hypotheses']} | {c['differ']} | "
          f"{sum(1 for x in rs if x.get('harmless'))} | {sum(1 for x in rs if x.get('proved') == 'partial')} |")
c = collections.Counter(r['agreement'] for i, r in rows)
print(f"| all | {len(rows)} | {c['equal']} | {c['equal_under_hypotheses']} | {c['differ']} | "
      f"{sum(1 for i, r in rows if r.get('harmless'))} | {sum(1 for i, r in rows if r.get('proved') == 'partial')} |\n")
print('Not harmless:', [i for i, r in rows if not r.get('harmless')] or 'none')
print('\nDiffer / partial / T_issue:')
for i, r in rows:
    if r['agreement'] == 'differ' or r.get('proved') == 'partial' or r.get('T_issue'):
        d = (r.get('difference') or r.get('why') or '').replace('\n', ' ')
        print(f"- {i} ({r['agreement']}, proved {r.get('proved')}{', T_issue: ' + str(r['T_issue']) if r.get('T_issue') else ''}): {d[:260]}")
