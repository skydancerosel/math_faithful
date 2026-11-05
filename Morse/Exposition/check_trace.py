"""Trace-tag checker for "Morse Theory, proof by proof" (Exposition/ProofByProof.md).

Adapted from the Milnor project. Paths are relative to Morse/ (this project), or begin with
`Milnor/` (the Milnor dependency) or `Mathlib/`.

Usage: python3 Exposition/check_trace.py Exposition/ProofByProof.md

A tag has the form  ⟦Chapter2/Regular · theorem_3_1⟧ .
For each tag we find the declaration in Morse/<path>.lean, record its line number and full
name, and extract the declaration header (the statement, up to ':=' or 'where').
"""
import re, sys, json, pathlib, collections

_PROJ = pathlib.Path(__file__).resolve().parents[1]
ROOT = _PROJ / 'Morse'
MATHLIB = _PROJ / '.lake' / 'packages' / 'mathlib'
# Milnor sources: the repository root (Morse lives in its subfolder), else a Lake package checkout.
MILNOR = (_PROJ.parent / 'Milnor' if (_PROJ.parent / 'Milnor.lean').exists()
          else _PROJ / '.lake' / 'packages' / 'Milnor' / 'Milnor')
TAG = re.compile(r'⟦([A-Za-z0-9_/]+) · ([^⟧]+?)⟧')
KW = r'(?:theorem|lemma|def|irreducible_def|abbrev|instance|structure|class|inductive|opaque)'
DECL = re.compile(r'^(\s*)(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|nonrec|partial|unsafe|meta)\s+)*'
                  + KW + r'\s+([^\s:({\[⦃]+)')

_cache = {}

def decls(path):
    """Return list of (line_no, declared_token, namespace_prefix) for a file."""
    if path in _cache:
        return _cache[path]
    if path.startswith('Mathlib/'):
        f = MATHLIB / (path + '.lean')
    elif path.startswith('Milnor/'):
        f = MILNOR / (path[len('Milnor/'):] + '.lean')
    else:
        f = ROOT / (path + '.lean')
    if not f.exists():
        _cache[path] = None
        return None
    lines = f.read_text().split('\n')
    out = []
    ns = []
    for i, l in enumerate(lines, 1):
        m = re.match(r'^\s*namespace\s+([\w.]+)', l)
        if m:
            ns.append(m.group(1))
            continue
        m = re.match(r'^\s*end\s+([\w.]+)\s*$', l)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
            continue
        m = DECL.match(l)
        if m:
            out.append((i, m.group(2), '.'.join(ns)))
    _cache[path] = (lines, out)
    return _cache[path]

def resolve(path, name):
    d = decls(path)
    if d is None:
        return None
    lines, out = d
    name = name.strip()
    cands = []
    for (i, tok, ns) in out:
        root = tok.startswith('_root_.')
        t = tok[len('_root_.'):] if root else tok
        full = t if root else (ns + '.' + t if ns else t)
        if full == name or full.endswith('.' + name):
            cands.append((i, full))
    if not cands:
        return None
    i, full = cands[0]
    # extract the header: from the declaration line (including preceding docstring? no) to ':=' / 'where'
    hdr = []
    depth = 0
    for j in range(i - 1, min(i - 1 + 40, len(lines))):
        l = lines[j]
        hdr.append(l)
        s = re.sub(r'--.*$', '', l)
        if re.search(r':=\s*(by\b.*)?$', s) or re.search(r':=\s', s) or re.search(r'\bwhere\s*$', s):
            break
    text = '\n'.join(hdr)
    text = re.sub(r'\s*:=\s*by\b.*$', ' := …', text, flags=re.S)
    text = re.sub(r'\s*:=\s*$', ' := …', text)
    return {'line': i, 'full': full, 'header': text.rstrip()}

def check(md_paths):
    report = collections.OrderedDict()
    bad = []
    for p in md_paths:
        txt = pathlib.Path(p).read_text()
        for m in TAG.finditer(txt):
            path, name = m.group(1), m.group(2)
            key = (path, name)
            r = resolve(path, name)
            if r is None:
                bad.append((p, path, name))
            else:
                report.setdefault(key, {**r, 'where': []})['where'].append(pathlib.Path(p).name)
    return report, bad

if __name__ == '__main__':
    rep, bad = check(sys.argv[1:])
    print(f'{len(rep)} distinct declarations cited, {len(bad)} unresolved tags')
    for b in bad:
        print('UNRESOLVED', *b)
