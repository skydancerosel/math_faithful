# How to write a section of the verified edition

The verified edition (`Exposition/Verification.md`) is written to be *checked*, not read for
pleasure. It records, chapter by chapter, exactly which statements of Milnor's *Morse Theory* have
been verified by Lean against Mathlib, what each verified statement says when read back in ordinary
language, which hypotheses the book left silent, where the formal statement or proof departs from
the book's, and what remains unverified and why. The model is the Milnor project's
`../Exposition/Verification.md` — read its §1 ("How to read a verified
statement"), one chapter section (e.g. its §5) and its §12 (sign-off) before writing.

## Sources of truth

- The Lean files (`Morse/**/*.lean`): read every statement you cite, with its hypotheses. The
  statement is the contract; the docstring is not.
- The book: `Exposition/pages/p-NN.png` (book page `b` ≈ image `p-(floor(b/2)+3)`), for Milnor's
  own statement and page. Beware: the scan drops glyphs (see `Exposition/Findings.md`, "About the
  scan").
- `Exposition/Findings.md` (gaps and slips, with what was confirmed or withdrawn), `README.md`
  (status table), the expanded chapters `Exposition/ChapterN.md`.

## Shape of a section

```
## k. Chapter N (Milnor §a–§b): verified | partly verified | not verified

One paragraph: what the chapter of the book proves, what of it is verified, the setting used
(finite-dimensional inner product space; slice submanifolds of a Euclidean space; abstract compact
manifolds via the Whitney embedding), and what is not verified.

**VN.1 (short title; `Morse.name1`, `Morse.name2`).** The statement in ordinary mathematical
language, with every hypothesis of the formal statement (dimensions, smoothness class, compactness,
Hausdorff, closedness, non-degeneracy, …). *Book:* Milnor's statement, paraphrased, with page.
*Hidden hypotheses:* … (or "none"). *Deviation (stronger | narrower | restated | not in the book |
value differs):* what differs and why (omit if none). *Proof:* one or two sentences, only where the
formal proof departs from Milnor's (e.g. the Morse lemma by one inverse-function-theorem step).

…

### What is not verified in this chapter

A short list, each item with the reason (missing Mathlib infrastructure, out of scope, not yet
done).

### Sign-off items

1. (VN.1) One sentence a mathematician can confirm says what Milnor means.
2. …
```

Numbering: `VN.i` with `N` the exposition chapter number (1–15, or `A` for the Appendix), `i`
from 1 in book order. Definitions that matter (critical point, Hessian, index, Morse function,
strong deformation retract, the cell-complex predicate, the Poincaré–Hopf integer) get their own
V-items, stated precisely, since every later item depends on them.

## Rules

- Every Lean name you cite must exist: run `python3 Exposition/check_names.py <your file>` from the
  project root before finishing; it must report 0 unresolved.
- No Lean syntax in the prose statements except the names in backticks. Use `$…$` for math.
- No claims about Milnor's text that are not checked against the scan. No long quotations of the
  book (a short phrase at most).
- Plain, precise prose; no filler.
