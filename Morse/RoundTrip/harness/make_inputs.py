"""Regenerate the round-trip inputs under $RT_DIR (default /tmp/claude-0/rt/) from Exposition/cmp/*.json.

blind/<ID>.md  Milnor's statement only (given to the blind formalizer)
keys/<ID>.json the full comparison item, verdict included (never shown to blind formalizers or provers)
decls/<ID>.txt the item's declaration names (given to provers, without the verdict)
The vocabulary dump: `lake env lean RoundTrip/harness/Vocab.lean` writes $RT_DIR/vocab.md.
"""
import json, glob, os
R = os.environ.get('RT_DIR', '/tmp/claude-0/rt')
for d in ('blind', 'keys', 'decls'):
    os.makedirs(f'{R}/{d}', exist_ok=True)
here = os.path.dirname(os.path.abspath(__file__))
for f in sorted(glob.glob(os.path.join(here, '../../Exposition/cmp/*.json'))):
    for e in json.load(open(f))['items']:
        i = e['id'].replace('.', '_'); m = e['milnor']
        open(f'{R}/blind/{i}.md', 'w').write(f"# {e['id']}: {e['title']}\n\nMilnor, *Morse Theory*, {m['label']}.\n\n{m['statement']}\n" + (f"\n(Context note: {m['note']})\n" if m.get('note') else ''))
        json.dump(e, open(f'{R}/keys/{i}.json', 'w'), ensure_ascii=False, indent=1)
        open(f'{R}/decls/{i}.txt', 'w').write('\n'.join(d.split('·')[-1].strip() for d in e['lean']['decls']) + '\n')
