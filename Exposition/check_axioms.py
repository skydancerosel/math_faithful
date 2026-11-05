"""Axiom check: every declaration the comparison edition cites uses only the standard axioms.

Usage: python3 Exposition/check_axioms.py

Collects the declarations cited in Exposition/Comparison.json (resolved exactly as
build_comparison.py resolves them) and those named by `#print axioms` in Milnor/Test.lean, runs
`#print axioms` on each through `lake env lean`, and fails if any of them depends on an axiom
other than propext, Classical.choice and Quot.sound (in particular on sorryAx), or if Lean does
not report on every one. Needs the project built first (`lake build`).
"""
import re, sys, json, pathlib, subprocess, tempfile

EXDIR = pathlib.Path(__file__).resolve().parent
PROJ = EXDIR.parent
sys.path.insert(0, str(EXDIR))
import build_comparison as B

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
REPORT = re.compile(r"^'(.+?)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)", re.M | re.S)


def cited():
    items = json.loads((EXDIR / 'Comparison.json').read_text())['items']
    bad = B.resolve_decls(items)
    if bad:
        for b in bad:
            print('UNRESOLVED', b)
        sys.exit(1)
    names = {d['full'] for it in items for d in it['_decls']}
    test = (PROJ / 'Milnor' / 'Test.lean').read_text()
    names |= set(re.findall(r'^#print axioms\s+(\S+)', test, re.M))
    return sorted(names)


def main():
    names = cited()
    src = 'import Milnor\n' + ''.join(f'#print axioms {n}\n' for n in names)
    with tempfile.NamedTemporaryFile('w', suffix='.lean', dir=PROJ, delete=False) as f:
        f.write(src)
        tmp = pathlib.Path(f.name)
    try:
        r = subprocess.run(['lake', 'env', 'lean', str(tmp)], cwd=PROJ, capture_output=True, text=True)
    finally:
        tmp.unlink()
    out = r.stdout + r.stderr
    seen, bad = set(), []
    for m in REPORT.finditer(out):
        name, axs = m.group(1), m.group(2)
        seen.add(name)
        extra = {a.strip() for a in (axs or '').split(',') if a.strip()} - ALLOWED
        if extra:
            bad.append(f'{name}: {", ".join(sorted(extra))}')
    missing = [n for n in names if n not in seen]
    print(f'{len(names)} declarations checked, {len(bad)} with nonstandard axioms, {len(missing)} unreported')
    for b in bad:
        print('  AXIOM', b)
    for n in missing:
        print('  UNREPORTED', n)
    if r.returncode != 0 or missing:
        print(out[-4000:])
    return 1 if (bad or missing or r.returncode != 0) else 0


if __name__ == '__main__':
    sys.exit(main())
