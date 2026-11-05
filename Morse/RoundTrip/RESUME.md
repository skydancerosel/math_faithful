# Resuming the audit

Status 2026-10-05: layers 1, 2 and 3 are complete (`REPORT.md`). This file says how to regenerate
the scratch inputs and what could still be done.

## Scratch inputs

All harness scripts read the scratch folder from `$RT_DIR` (default `/tmp/claude-0/rt`):

```
export RT_DIR=<a scratch folder>; mkdir -p $RT_DIR
python3 RoundTrip/harness/make_inputs.py            # blind/, keys/, decls/ from Exposition/cmp/*.json
lake env lean RoundTrip/harness/Vocab.lean          # $RT_DIR/vocab.md (project definitions)
cp RoundTrip/harness/{PROVER_PROMPT.md,score.py,p*.txt,n*.txt,batch*.txt} $RT_DIR/
python3 RoundTrip/harness/make_l2_inputs.py         # layer 2: $RT_DIR/l2/ (needs l2_triage.json, l2_sigs.txt)
```

The prompts contain placeholders for the local paths (`<P>` = the `Morse/` folder, `<RT>` or
`$RT_DIR` = the scratch folder); substitute them before handing a prompt to an agent.
`l2_sigs.txt` is produced by a small `PrettyPrinter.ppSignature` loop over the names of
`harness/l2_triage.json` (class "notion"); `l2_triage.json` itself came from `#rt_defs` over the
declarations of the comparison items whose title is a numbered theorem or corollary.

Summaries: `RT_DIR=… python3 RoundTrip/harness/summarize.py [--rows]` (layer 1, needs `keys/`),
`python3 RoundTrip/harness/summarize_l2.py` (layer 2). Layer 3 labels: `layer3_labels.json`.

## Prompts

| file | role |
|---|---|
| `harness/BLIND_PROMPT.md` | layer-1 blind formalizer |
| `harness/PROVER_PROMPT.md` + `harness/EMBEDDED_ADDENDUM.md` | layer-1 prover (with the embedded special case and tips) |
| `harness/RERUN_PROMPT.md` | second pass adding the embedded special case to an existing item |
| `harness/SECOND_PROMPT.md` | second attempt once a missing lemma exists (EnergyC2) |
| `harness/L2_BLIND_PROMPT.md`, `harness/L2_PROVER_PROMPT.md` | layer 2 |
| `harness/taxonomy.md` | layer 3 codes |

Run one batch per agent group (5–7 items per prover agent, ~10 per blind agent), commit after
each, and recompile everything at the end (`lake env lean RoundTrip/Items/<id>.lean` for every
item; all must report no error and no `rt_check FAIL`).

## What could still be done

* **A shared dictionary module.** Items cannot import each other, so the provers copied the same
  glue into many files (blind Ω ≃ₕ `PathSp` from `Items/V10_19.lean`, the Hessian dictionary of
  `Items/V8_13.lean`, `LamPf` of `Items/V9_23.lean`, the Jacobi dictionary of `Items/V9_10.lean`,
  normal balls of `Items/V7_13.lean`, matrix-group Lie structure of `Items/V12_15.lean`). Moving
  them into a module on top of `Bridge.lean` and `EnergyC2.lean` would make further passes cheap.
* **Effort-only gaps** (layer 3 code `effort`): V9_7–V9_7″ nullity clauses (TΩ dictionary),
  V15_11 (steps (5)–(7) of Lemma 24.6), V15_32/V15_39 (transport between the blind `OmIn` and the
  project's `PathSp`), V11_16 B_emb ⇒ A (λ(1) ≤ formIndex, ~80 lines).
* **Project Lean suggested by the audit** (HANDOFF §3 item 4): the group-level real periodicity is
  ~100 lines (`Items/V15_45.lean`, `stratumM`, `linkM`, `chainM`); Theorem 23.3 with the inclusion
  inducing the isomorphism (V14.22); the §24 results for every family, not only `bott16`.
* **Label corrections for the comparison:** V15.14 should be *narrower* (k ≤ 8). Done on
  2026-11-04.
