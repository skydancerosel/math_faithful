# Handoff: continuing the Morse project locally

Written 2026-10-05 at the end of a cloud session (`morse-work`, fast-forwarded into `main` at
`9d50474`), and updated on 2026-10-05 at the end of the first local session, which did
items 1–4 of the original list, and after the second (the audit) and the third (the shortest path,
the three parts), which ran in parallel and were merged on 2026-10-06. Everything below is in git.

## 1. Setting up the Mac

The GitHub repository has the Milnor project at the root and Morse in `Morse/`. On this Mac the
clone is `~/math_faithful` (the old `~/faithful_math` no longer exists). On another machine:

```bash
cd ~
git clone https://github.com/skydancerosel/math_faithful.git
cd math_faithful/Morse
lake exe cache get                                          # Mathlib, once
lake build                                                  # compiles Milnor (..) and Morse; long the first time
```

The scan and the book PDF are not in git (copyright). The PDF is kept, untracked, at
`Morse/MorseTheory.pdf`; the page images are regenerated from it:

```bash
mkdir -p Exposition/pages && pdftoppm -r 110 -png MorseTheory.pdf Exposition/pages/p
```

(79 images, two book pages each; book page `b` is on image `p-(⌊b/2⌋+3)`.)

A git worktree of the repository has no `.lake` folders. Copying them from the main checkout
(`cp -Rcp ~/math_faithful/.lake .lake` and the same for `Morse/.lake`; on APFS these are clones and
take no space) makes `lake build` up to date at once.

Checks that must stay green after any change:

```bash
lake build                                        # no errors
lake env lean -DmaxSynthPendingDepth=3 Morse/Test.lean | grep -v "propext, Classical.choice, Quot.sound\]"   # nothing but continuation lines and the 3 lines [propext, Quot.sound]
python3 Exposition/check_names.py                 # every cited name exists
python3 Exposition/check_trace.py Exposition/ProofByProof.md   # 0 unresolved trace tags
```

A rebuild of Morse after touching an early file (e.g. `Chapter7/Exp.lean`, some 125 files
downstream) takes minutes, not hours, on this Mac. Editing a Lean docstring moves the line numbers that the comparison and the proof by
proof print, so rebuild both reports afterwards.

Rules: no `sorry`; add `#print axioms` to `Morse/Test.lean` for every new theorem; temporary Lean
files only as gitignored `Morse/**/WIP_*.lean`; existing V-items of the verified edition keep their
numbers (a mathematician is signing off the current edition) — add new ones after them. The global
numbers of the final sign-off list do move when a chapter gains items; the V-number is the stable
name.

## 2. State of the project

* **Lean**: Parts I–IV formalized; see the status table of `README.md` and §2 of `PLAN.md`. Not
  formalized: π₁ torsion-free (second half of 19.3); group-isomorphism versions of real Bott
  periodicity (it is a bijection of sets); the limit spaces `Ω_k` and the table of `πᵢO`; integral
  homology of `ℂPⁿ`; Hanner's theorem in general (replaced by explicit retractions wherever used).
* **Reports**: proof by proof Parts 0–XIII built (`Exposition/ProofByProof.{md,pdf}`,
  `morse-proof-by-proof.html`; 452 pages); comparison Chapters 1–15 and the Appendix
  (`Exposition/cmp/*.json`, `morse-beside-lean.html`; 452 items); verified edition 16 sections,
  396 sign-off items, PDF built. The verified edition and the comparison now report every result
  of the book that is formalized, including §24's geometry and topology (V15.21–V15.46), `ℂPⁿ`
  (V3.41–V3.43), the Lefschetz theorems (V5.13–V5.19) and Corollaries 17.2 and 17.4 for loops
  (V10.28–V10.30). Of the 1,498 theorems of `Morse/Test.lean`, 333 are not cited in the verified
  edition: auxiliary lemmas and infrastructure that is not in the book (most of `Morse/Homotopy/`,
  the subdivision files of `Morse/Homology/`), which the proof by proof reports. One of these
  groups touches a statement of Milnor's and could get a V-item in Chapter 14:
  `Morse/Homotopy/GrassmannianQuotient.lean` (the Grassmannian of projections is the space of
  subspaces and the quotient of the Stiefel manifold, p. 129).
* **Audit** (`RoundTrip/`): complete (2026-10-05, second local session). Layer 1: 348 blind
  statements, 348 round-tripped, with the embedded special case for §§8–19 through
  `RoundTrip/Bridge.lean`; layer 2: the 116 textbook notions under Milnor's numbered theorems all
  agree with blind textbook definitions (`RoundTrip/L2/`); layer 3: failure labels
  (`RoundTrip/layer3_labels.json`). Final report `RoundTrip/REPORT.md`, notes for further passes
  `RoundTrip/RESUME.md`.
* **Docstring errata**: `DocstringErrata.md`; no open row.

## 3. What remains, in order

1. ~~Audit, layers 1–3~~ — done on 2026-10-05 (see `RoundTrip/REPORT.md`). Follow-ups it suggests
   (`RoundTrip/RESUME.md`): a shared dictionary module for the audit's glue. The comparison's
   label of V15.14 was corrected to *narrower* on 2026-11-04 (the formal result covers k ≤ 8 only).
2. Lower priority Lean: group isomorphisms for real periodicity (the audit shows they take about
   100 lines: `RoundTrip/Items/V15_45.lean`, `stratumM`, `linkM`, `chainM`); Theorem 23.3 with the
   isomorphism induced by the inclusion Ω^d → Ω (V14.22); §24 for every anticommuting family, not
   only `bott16`; the table of `πᵢO`; the colimit spaces `Ω_k`; π₁ torsion-free; integral homology.

Done in the first local session: the §24 rows of the comparison and of the verified edition, and
those for the late Lean additions to Chapters 3, 5 and 10; the open docstring errata; the PDFs with
the real fonts; and the three web editions republished at their existing private links (comparison
https://claude.ai/artifact/2gCU32LTuUBs2kSzQgSJBd, proof by proof
https://claude.ai/artifact/BcXexY9ZNAxJoesrskHxDh, the book
https://claude.ai/artifact/Nap97EqZwj1ZjHek4DG4zW). Updating one of these in place from a new session
requires reading the whole published page first; for the comparison that is about 1.7 MB, so
give it to a helper agent with a fresh context. The questions that needed the scan are
settled (see `DocstringErrata.md`): Theorem 23.5 is on p. 130; Lemma 23.1 is stated on p. 128 (its
argument is on p. 127); Lemma 23.4 is stated on p. 128 and proved on pp. 128–129; on p. 129 Milnor's
chain holds for `1 ≤ i ≤ 2m` and the Periodicity Theorem is stated for `i ≥ 1` (the formal ranges
are `i ≤ 2m − 2` inside one `U(m)`, and any two groups in the stable range, V15.46); p. 26 prints
`f = c_j|z_j|`, and the next display, `f = c₀ + Σ(c_j − c₀)(x_j² + y_j²)`, confirms the reading
`Σ c_j|z_j|²`; "components of varying dimension" is on pp. 139 and 141, not 137.

Done in the third local session (2026-10-06), in parallel with the audit:

- **The project is presented in three parts.** The README now names them: *Morse Theory, Rewritten*,
  *Morse Theory, Checked* and *Morse Theory, the Shortest Path*. The verified edition's introduction
  is the way into the second part.
- **The book's numbered results carry notes.** Each says whether the result has been checked by
  machine, with its V-number and the comparison's verdict. The notes are added at build time by
  `Exposition/checked_marks.py`; the chapter PDFs, the verified edition and
  `morse-theory-rewritten.html` were rebuilt. The published book (Nap97…) was
  republished with them and the torus figure.
- **Chapter 1 has Milnor's Diagram 1.** The torus standing on a plane, with level curves and the
  four sublevel sets, is `fig1-torus.{py,png,js}`; the web version has a water-level slider.
- **The shortest path is written.**
  - The source is `Exposition/ShortestPath.md`, with `.pdf` and `morse-shortest-path.html`, published
    privately at https://claude.ai/artifact/AqVhqo3Qs7hvXBFR4ZP4MZ.
  - It is built from `Exposition/shortest/` (brief: `Exposition/SHORTEST.md`).
  - To rebuild after Lean changes:
    1. Run `lake env lean -DmaxSynthPendingDepth=3 Exposition/shortest/DepDump.lean` (about 3 min;
       writes the gitignored `deps.jsonl`).
    2. Run `python3 Exposition/shortest/deps.py`.
    3. Run `python3 Exposition/build_shortest_path.py`. Its checker must report 0 unresolved,
       0 off the path, and every on-path result labelled.

### Which model for the audit

Run the session on **Claude Opus 5.5** and move to **Claude Fable 5.1** only where proving is the
bottleneck. Measured on 2026-10-05: on five items of `p4a` run independently, Opus 5.5 (267k tokens)
and Fable 5.1 (332k) reached the same relation on four and Opus proved one direction more on the
fifth; at list prices Fable cost ≈ 3× for no gain. The second local session therefore ran every
prover on Opus 5.5, the triage and layer 3 on Sonnet 5.5, and Fable 5.1 once, for new analysis
(`RoundTrip/EnergyC2.lean`, 214k tokens). The table below is the original plan.

| Work | Model | Why |
|---|---|---|
| Prover batches `p4a`–`p7b`, and the new §§20–24 items | Opus 5.5 | The 124 finished items came from Opus 5.5 sessions; only 7 were marked `effort_only` (true but not proved). The failures were mostly the embedded-vs-abstract setting gap and blind-statement bugs, not prover weakness. |
| Blind statements (re-blind V7_9–V7_16, the new items) | the model that wrote the first 237 | Keeps the two halves comparable. `REPORT.md` does not name it; the audit commits all carry the Opus 5.5 trailer, so use Opus 5.5 unless you know otherwise. |
| `RoundTrip/Bridge.lean` and the §§8–10 re-run through it | Fable 5.1 | New formalization (the induced Levi-Civita connection, geodesics, `exp`, curvature as Mathlib objects): the hardest Lean work left. |
| A second attempt at items Opus leaves unproved in the hard chapters | Fable 5.1 | A failed direction is ambiguous between "different statements" and "not proved"; a stronger prover resolves that. |
| Layer 3 (labels from the JSON diagnoses) | Sonnet 5.5 | Classification over short texts. |

One session is enough: a subagent can be pinned to another model (the Agent tool's `model`
parameter, e.g. `fable` or `sonnet`), so an Opus session hands `Bridge.lean` to a Fable agent and
layer 3 to a Sonnet agent. To decide the prover on data rather than judgement, run `p4a` (15 items)
once on each of Opus 5.5 and Fable 5.1 and compare the directions proved and the tokens used; if
the verdicts agree, stay on Opus. On price, API list rates (as of 2026-09-25) are $10/$50 per
million input/output tokens for Fable 5.1, $4/$20 for Opus 5.5 and $2/$10 for Sonnet 5.5, so Fable
costs 2.5 times Opus per token; on a subscription the limit is usage rather than dollars, but the
ratio is a fair guide. The cloud runs left no token counts, so the cost of a batch is not known yet:
record it for `p4a`.

## 4. First message for the next session

> Read `Morse/HANDOFF.md`, `Morse/PLAN.md`, `Morse/RoundTrip/RESUME.md` and `Morse/DocstringErrata.md`.
> Build from `Morse/` with `lake build`. Do the items of HANDOFF.md §3 in order, committing after
> each; keep the four checks of §1 green; no `sorry`; `#print axioms` lines for new theorems; never
> renumber existing V-items. The scan is in `Morse/Exposition/pages/` (regenerate it as §1 says).
> For the audit, regenerate the scratch inputs as RESUME.md says (adjust the `/tmp/claude-0/rt/`
> paths to a local scratch folder), run one prover batch at a time with a blind formalizer that
> never sees `Morse/Morse/`, `Exposition/` or the answer keys, and commit after each batch. Choose
> models as "Which model for the audit" in HANDOFF.md §3 says (this session on Opus 5.5; Fable 5.1
> subagents for `Bridge.lean` and for second attempts at unproved directions).
