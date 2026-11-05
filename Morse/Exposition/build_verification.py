#!/usr/bin/env python3
"""Assemble Exposition/Verification.md from the per-chapter sections in Exposition/verification/.

Each section file `chNN.md` (or `chA.md`) starts with a heading `## Chapter N (Milnor …): status`,
contains V-items, a `### What is not verified in this chapter` list and a `### Sign-off items`
list. The assembler numbers the sections, moves every sign-off list to a final numbered sign-off
section, adds the summary table (Lean lines per chapter directory, counted with `wc -l`), and
builds `Verification.pdf` with the same pandoc settings as the chapters.

Usage: python3 build_verification.py
"""
import datetime, glob, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
SEC = os.path.join(HERE, "verification")
sys.path.insert(0, HERE)
from build import PDF_ARGS  # noqa: E402

CHAPTERS = [  # file key, Milnor sections, short content (for the summary table), Lean dirs
    ("01", "§§1–2", "critical points, Hessian and index, the Morse lemma, flows (Lemma 2.4)", ["Chapter1", "Flow"]),
    ("02", "§3", "Theorems 3.1, 3.2, 3.5, Lemmas 3.6–3.7, Remarks 3.3–3.4", ["Chapter2"]),
    ("03", "§§4–5", "Reeb's theorem, the torus, the Morse inequalities in singular homology, the Euler characteristic", ["Chapter3", "Homology"]),
    ("04", "§6", "focal points, existence and density of Morse functions, compact abstract manifolds", ["Chapter4"]),
    ("05", "§7", "the index bound behind the Lefschetz theorem", ["Chapter5"]),
    ("06", "§§8–9", "connections, parallel transport and curvature, for submanifolds of $\\mathbb R^K$", ["Chapter6"]),
    ("07", "§10", "geodesics, the exponential map, the Gauss lemma, the Hopf–Rinow theorem", ["Chapter7"]),
    ("08", "§§11–13", "the path space, the energy, the first and second variation formulas", ["Chapter8"]),
    ("09", "§§14–15", "Jacobi fields and the index theorem", ["Chapter9"]),
    ("10", "§§16–17", "the finite-dimensional approximation, the full path space", ["Chapter10"]),
    ("11", "§§18–19", "non-conjugate points, topology and curvature", ["Chapter11"]),
    ("12", "§§20–21", "bi-invariant metrics, matrix groups, their geodesics and curvature", ["Chapter12"]),
    ("13", "§22", "manifolds of minimal geodesics, Freudenthal's theorem", ["Chapter13"]),
    ("14", "§23", "Bott periodicity for the unitary group", ["Chapter14"]),
    ("15", "§24", "Bott periodicity for the orthogonal group", ["Chapter15"]),
    ("A", "Appendix", "the homotopy type of a monotone union", ["Appendix"]),
]

INTRO = r"""# Morse Theory, verified: the machine-checked edition

*A companion to "Morse Theory, Rewritten", the expanded edition of J. Milnor's* Morse Theory
*(Princeton, 1963). That edition is written to be read; this one is written to be checked. It
records, chapter by chapter, exactly which statements of the book have been verified by the Lean 4
proof assistant against the Mathlib library and the formalization of Milnor's* Topology from the
Differentiable Viewpoint *(the companion project), what each verified statement says when read back
in ordinary language, which hypotheses the book left silent, where the formal statement or proof
departs from the book's, and what remains unverified and why. Nothing here needs to be read in
Lean; every checked statement is restated in prose, and the Lean names are given only so that the
claims can be audited.*

**Where to start.** The project has three parts:

- *Morse Theory, Rewritten*, the book for reading;
- *Morse Theory, Checked*, the Lean formalization and the reports on it;
- *Morse Theory, the Shortest Path*, the main theorems and exactly what their formal proofs use.

This edition is the way into the second part. Its four reports each answer one question:

- **What is proved?** This edition: every checked result in plain language, with all its
  hypotheses, and the list of statements to sign off.
- **How is it proved?** *Morse Theory, proof by proof* (`Exposition/ProofByProof.md`): the formal
  proofs retold as mathematics, with a trace tag on each step naming the Lean declaration that
  carries it.
- **How does it differ from Milnor?** *Morse Theory beside Lean*, the comparison
  (`Exposition/morse-beside-lean.html`): each result of the book beside the checked statement, with
  a verdict (the same, restated, hypotheses made explicit, stronger, narrower) and the differences.
- **Are the comparison's verdicts right?** The round-trip audit (`RoundTrip/REPORT.md`): Milnor's
  statements are formalized blind, without sight of the project's Lean, and proved equivalent, or
  not, to the checked ones; the definitions under the main theorems are checked against blind
  textbook definitions in the same way.

A result has the same number, V2.8 say, in this edition, the comparison, the rewritten book's notes
and the shortest path.

---
"""

HOWTO = r"""## 1. How to read a verified statement

**The statements are the contract.** A machine-checked proof guarantees that the *stated* theorem
follows from Lean's axioms. It guarantees nothing about whether the statement is the one Milnor
meant. The reader's job, and the only mathematical judgement this document asks for, is to read
each prose restatement and confirm that it says what the book means. Where the restatement is
weaker or stronger than the book, or uses a different but equivalent definition, this is flagged as
a **Deviation**.

**Three settings.** Mathlib's manifolds are abstract spaces with atlases. The results of §2 are
proved for abstract manifolds. Most of Part I is proved for submanifolds of a Euclidean space in the
sense of the companion project (subsets with slice charts), and carried to abstract *compact*
manifolds through Mathlib's Whitney embedding theorem; non-compact abstract manifolds would need a
Whitney embedding that Mathlib does not have. Part II, and Part III as far as it is verified
(§§11–19), are verified for submanifolds of $\mathbb R^K$ with the induced metric (every
Riemannian manifold is such a submanifold by Nash's theorem, which is quoted, not proved); Part IV
(§§20–24) for compact groups of matrices and the spaces $\Omega_k(n)$ of §24, as submanifolds of a
space of matrices, and in its algebraic cores; the Appendix for arbitrary topological spaces.
Homology is Mathlib's singular homology, extended here by relative homology, the exact sequences of
pairs and triples, and excision (Chapter 3).

**What "smooth" means.** Smooth means $C^\infty$. Hausdorffness and second countability, which
Milnor uses silently, are explicit hypotheses wherever they are needed; submanifolds of a Euclidean
space have both automatically.

**Axioms.** Every verified theorem depends only on the three standard axioms of Lean's Mathlib
(`propext`, `Classical.choice`, `Quot.sound`), as `Morse/Test.lean` prints; there is no `sorry`.
"""


def lean_lines(dirs):
    files = []
    for d in dirs:
        files += [f for f in glob.glob(os.path.join(ROOT, "Morse", d, "*.lean"))
                  if not os.path.basename(f).startswith("WIP_")]
    return sum(sum(1 for _ in open(f, encoding="utf-8")) for f in files), len(files)


def main():
    body, signoffs, rows = [], [], []
    k = 2
    for key, secs, content, dirs in CHAPTERS:
        path = os.path.join(SEC, f"ch{key}.md")
        lines, nfiles = lean_lines(dirs)
        chap = "Appendix" if key == "A" else f"Chapter {int(key)}"
        if not os.path.exists(path):
            rows.append(f"| {chap} | {secs} | {content} | not verified | {lines:,} |" if lines else
                        f"| {chap} | {secs} | {content} | not verified | — |")
            continue
        text = open(path, encoding="utf-8").read().strip()
        head = re.match(r"##\s+(.*)", text)
        status = head.group(1).split(":")[-1].strip() if head else "verified"
        rows.append(f"| {chap} | {secs} | {content} | **{status}** | {lines:,} |")
        m = re.search(r"^###\s+Sign-off items\s*\n(.*?)(?=^##\s|\Z)", text, re.S | re.M)
        if m:
            items = re.findall(r"^\d+\.\s+(.*?)(?=^\d+\.\s|\Z)", m.group(1), re.S | re.M)
            signoffs += [" ".join(i.split()) for i in items]
            text = (text[:m.start()] + text[m.end():]).rstrip()
        text = re.sub(r"^##\s+", f"## {k}. ", text, count=1, flags=re.M)
        body.append(text)
        k += 1
    total_lines, total_files = lean_lines(sorted({d for *_, ds in CHAPTERS for d in ds}))
    summary = ["## 0. Summary", "",
               "| Chapter | Milnor | Content | Status | Lean lines |",
               "|:--|:--|:--|:--|--:|"] + rows + ["",
               f"Total: {total_lines:,} lines of Lean in {total_files} files under `Morse/` "
               f"(`wc -l`, excluding unfinished `WIP_` files), on top of the companion project. "
               f"Toolchain: Lean 4.33.1, Mathlib 4.33.1. To reproduce: `lake build`, then "
               f"`lake env lean -DmaxSynthPendingDepth=3 Morse/Test.lean`, which prints the axioms "
               f"of every main theorem. Edition of {datetime.date.today():%-d %B %Y}.", ""]
    sign = [f"## {k}. Sign-off", "",
            "The statements below are the ones the reader is asked to confirm say what Milnor means. "
            "Each is a summary of the V-item it names; the standing hypotheses of that item are not "
            "repeated.", ""] + [f"{i}. {s}" for i, s in enumerate(signoffs, 1)]
    doc = "\n\n---\n\n".join([INTRO.rstrip().rstrip("-").rstrip(), "\n".join(summary).rstrip(), HOWTO.strip(),
                                 "\n\n---\n\n".join(body), "\n".join(sign)]) + "\n"
    out = os.path.join(HERE, "Verification.md")
    open(out, "w", encoding="utf-8").write(doc)
    print(f"Verification.md: {len(body)} chapter sections, {len(signoffs)} sign-off items, "
          f"{len(doc.split()):,} words")
    if shutil.which("pandoc") is None:
        print("Verification.pdf: skipped (pandoc is not installed; the PDF also needs xelatex)")
        return
    r = subprocess.run(["pandoc", "-f", "markdown", "-o", os.path.join(HERE, "Verification.pdf"),
                        "--toc", "--toc-depth=1"] + PDF_ARGS, input=doc, text=True,
                       capture_output=True, cwd=HERE)
    print("Verification.pdf:", "ok" if r.returncode == 0 else "FAILED\n" + r.stderr[-2000:])


if __name__ == "__main__":
    main()
