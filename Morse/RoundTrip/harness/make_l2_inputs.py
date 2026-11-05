"""Layer 2 inputs: one file per textbook notion under $RT_DIR/l2/blind/<ID>.md.

Reads $RT_DIR/l2_triage.json (the triage of the definitions under Milnor's numbered theorems, made by
`#rt_defs` + a classification pass) and $RT_DIR/l2_sigs.txt (Lean signatures, `ppSignature`). The
blind formalizer sees the signature and a neutral textbook description, never the body or docstring.
ID = the Lean name with '.' replaced by '_'.
"""
import json, os, re
R = os.environ.get('RT_DIR', '/tmp/claude-0/rt')
os.makedirs(f'{R}/l2/blind', exist_ok=True)
sigs = {}
for blk in open(f'{R}/l2_sigs.txt').read().split('=== ')[1:]:
    name, body = blk.split('\n', 1)
    sigs[name.strip()] = body.strip()
tri = json.load(open(f'{R}/l2_triage.json'))
ids = []
for x in tri:
    if x['class'] != 'notion':
        continue
    n = x['name']; i = re.sub(r'[^A-Za-z0-9_]', '_', n.replace('.', '_'))
    ids.append((i, n, x.get('priority', 'low')))
    open(f'{R}/l2/blind/{i}.md', 'w').write(
        f"# {i}\n\nTextbook notion: {x['textbook']}\n\nSignature of the project's definition "
        f"(your `T` must have the same arguments and result type; instantiate universes at 0 if needed):\n\n```\n{sigs[n]}\n```\n")
open(f'{R}/l2/ids.txt', 'w').write('\n'.join(f'{i} {n} {p}' for i, n, p in ids) + '\n')
print(len(ids), 'notions')
