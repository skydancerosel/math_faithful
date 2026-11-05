#!/usr/bin/env python3
"""Assemble Exposition/ProofByProof.md from the parts in Exposition/pbp/.

1. `--normalize` (run once, after all parts exist): subsection numbers become `<Roman part>.k`
   ("### 2.3" in Part II becomes "### II.3"; Part 0 keeps "0.k"), and every cross-reference
   "§2.3" to such a subsection is rewritten the same way, in every part.
2. Concatenate: the title, the prologue (Exposition/pbp/prologue.md, if present) and the parts in
   order, into Exposition/ProofByProof.md.

Usage: python3 assemble_pbp.py [--normalize]
Then:  python3 build_proofbyproof.py [outdir]
"""
import pathlib, re, sys

HERE = pathlib.Path(__file__).resolve().parent
PBP = HERE / 'pbp'
ROMAN = {1: 'I', 2: 'II', 3: 'III', 4: 'IV', 5: 'V', 6: 'VI', 7: 'VII', 8: 'VIII', 9: 'IX',
         10: 'X', 11: 'XI', 12: 'XII', 13: 'XIII'}
TITLE = '# Morse Theory, proof by proof'
DEK = ('*The formal proof of Milnor\'s* Morse Theory, *retold as mathematics: every definition as the '
       'formalization makes it, every proof step by step as the Lean proof goes, and on every step of '
       'substance a trace tag naming the declaration that proves it.*')


def parts():
    return sorted(p for p in PBP.glob('part[0-9][0-9].md'))


def normalize():
    files = parts()
    texts = {f: f.read_text() for f in files}
    for f in files:
        n = int(f.stem[4:])
        if n == 0:
            continue
        rom = ROMAN[n]
        # headings "### n.k" -> "### ROM.k"
        texts[f] = re.sub(rf'(?m)^(###\s+){n}\.(\d+)\b', rf'\g<1>{rom}.\2', texts[f])
    # cross-references "§n.k" (n >= 1, Arabic) -> "§ROM.k", in every part
    def fix(m):
        n = int(m.group(1))
        return f'§{ROMAN[n]}.{m.group(2)}' if n in ROMAN else m.group(0)
    for f in files:
        texts[f] = re.sub(r'§\s?(\d{1,2})\.(\d+)', fix, texts[f])
        f.write_text(texts[f])
    print(f'normalized {len(files)} parts')


def assemble():
    chunks = [TITLE, '', DEK, '']
    pro = PBP / 'prologue.md'
    if pro.exists():
        chunks += [pro.read_text().strip(), '']
    for f in parts():
        chunks += [f.read_text().strip(), '']
    out = HERE / 'ProofByProof.md'
    out.write_text('\n'.join(chunks) + '\n')
    words = len(out.read_text().split())
    print(f'ProofByProof.md: {len(parts())} parts, {words:,} words')


if __name__ == '__main__':
    if '--normalize' in sys.argv:
        normalize()
    assemble()
