#!/usr/bin/env python3
"""Check that every Lean declaration cited in a Markdown report exists.

Collects every backticked identifier of the form `Morse.…` or `Milnor.…` (several may share one
pair of backticks, separated by commas or spaces), writes a Lean file that `#check`s each of them,
runs it in the project environment, and reports the names Lean cannot resolve.

Usage: python3 check_names.py Verification.md [more.md ...]
Exit status 0 if every name resolves.
"""
import os, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
NAME = re.compile(r"\b((?:Morse|Milnor)(?:\.[^\W\d][\w'!?₀-₉ₐ-ₜ]*)+)")  # \w is Unicode-aware


def names_in(path):
    text = open(path, encoding="utf-8").read()
    found = []
    for code in re.findall(r"`([^`\n]+)`", text):
        if re.match(r"\s*(import|lake|open)\b", code):
            continue  # module paths in commands, not declarations
        found += NAME.findall(code)
    return found


def run_lean(src):
    """Elaborate `src` in the project environment; return Lean's output."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=HERE) as f:
        f.write(src)
        tmp = f.name
    try:
        r = subprocess.run(["lake", "env", "lean", "-DmaxSynthPendingDepth=3", tmp],
                           cwd=ROOT, capture_output=True, text=True)
    finally:
        os.unlink(tmp)
    return r.stdout + r.stderr


def main(paths):
    names = sorted({n.rstrip(".") for p in paths for n in names_in(p)})
    if not names:
        print("no Lean names cited")
        return 0
    checks = "\n".join(f"#check @{n}" for n in names) + "\n"
    out = run_lean("import Morse\nimport Milnor\n\n" + checks)
    if re.search(r"object file .*/Milnor\.olean.* does not exist", out):
        # the companion project's root module is not built: its modules imported by Morse suffice
        # for the names cited here (any other Milnor name is then reported as unresolved)
        print("note: `Milnor` (the root module) is not built; checking against `import Morse` alone")
        out = run_lean("import Morse\n\n" + checks)
    if re.search(r"object file .* does not exist|unknown module prefix", out):
        print("could not check: the project is not built (or is being rebuilt) — run `lake build` first")
        for l in out.splitlines()[:3]:
            print("  lean:", l)
        return 2
    bad = sorted(set(re.findall(r"[Uu]nknown (?:identifier|constant) [`'‘]([^`'’]+)[`'’]", out)))
    print(f"{len(names)} distinct names cited, {len(names) - len(bad)} resolved, {len(bad)} unresolved")
    for b in bad:
        print("  unresolved:", b)
    other = [l for l in out.splitlines() if "error" in l and "nknown identifier" not in l
             and "nknown constant" not in l]
    for l in other[:10]:
        print("  lean:", l)
    return 1 if bad or other else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:] or [os.path.join(HERE, "Verification.md")]))
