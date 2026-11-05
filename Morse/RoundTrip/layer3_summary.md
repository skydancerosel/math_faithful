# Layer 3: failure-type labels for the 348 layer-1 round-trip records

Source: `RoundTrip/Items/*.json` (348 records), labelled by reading each record's `why`, `B_issue`, `embedded_special_case_note` and revision fields against `harness/taxonomy.md`. Output: `layer3_labels.json` (`{id: {codes, primary, evidence}}`).

## Summary by code

| code | meaning | items carrying | as primary |
|---|---|---:|---:|
| `setting` | abstract vs embedded/matrix/vector-space setting | 183 | 118 |
| `extra_A` | A states proof steps / auxiliary lemmas absent from B | 145 | 24 |
| `general_A` | A more general (any field/ring/index type/model, weaker hypotheses) | 175 | 48 |
| `hyp_A` | A assumes more (compactness, regular value, closed, BrokenSetup, ...) | 48 | 13 |
| `cw_model` | Mathlib CWComplex vs iterated adjunction spaces / telescopes | 22 | 21 |
| `coefficients` | field coefficients vs integral homology | 5 | 3 |
| `taken_as_hyp` | A takes Hanner / Hypothesis (N) / pushing neighbourhood / connectedness of SU(n) as hypothesis | 16 | 9 |
| `algebraic_only` | only the algebraic/arithmetic step is formalized | 26 | 18 |
| `range` | smaller range (explicit family, k<=8, one base point, sets, partial clauses) | 75 | 21 |
| `structure_choice` | one structure/model/frame/path-space where B quantifies over all (or vice versa) | 28 | 11 |
| `reading` | different reading of a word/definition of Milnor | 47 | 6 |
| `finrank` | finiteness hidden by finrank / N-valued encodings | 6 | 2 |
| `vacuous` | a proved direction does not use its hypothesis | 88 | 17 |
| `B_false_milnor` | B false where Milnor's statement, read literally, does not hold (n=0/1, closedness, "x axis", "clearly") | 12 | 12 |
| `B_false_blind` | B false because of a blind-formalization bug | 1 | 1 |
| `missing_math` | failed direction needs mathematics absent from project and Mathlib | 123 | 9 |
| `effort` | believed true, only glue/effort missing | 15 | 7 |
| `harness` | #rt_check limitations shaped the result | 18 | 0 |
| `match` | A and B equivalent, nothing else applies | 8 | 8 |
| total | | | 348 |

## Primary code by chapter group

| chapter | n | `setting` | `extra_A` | `general_A` | `hyp_A` | `cw_model` | `coefficients` | `taken_as_hyp` | `algebraic_only` | `range` | `structure_choice` | `reading` | `finrank` | `vacuous` | `B_false_milnor` | `B_false_blind` | `missing_math` | `effort` | `match` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| V1 | 13 | 4 |  | 6 |  |  |  |  |  |  |  |  |  | 1 | 1 |  |  | 1 |  |
| V2 | 15 | 6 | 2 |  | 1 | 3 |  |  |  |  |  |  |  |  |  |  |  |  | 3 |
| V3 | 33 | 8 | 8 | 8 |  | 1 |  |  |  | 1 |  |  | 2 | 2 | 1 |  |  |  | 2 |
| V4 | 21 |  | 5 | 4 | 2 |  |  |  |  |  | 7 |  |  | 3 |  |  |  |  |  |
| V5 | 13 |  | 1 | 2 |  | 2 | 1 | 2 |  |  |  |  |  | 4 |  |  |  | 1 |  |
| V6 | 19 | 14 |  |  |  |  |  |  | 1 | 1 |  |  |  | 1 |  |  | 1 | 1 |  |
| V7 | 31 | 26 |  | 1 |  |  |  |  |  | 1 |  |  |  | 3 |  |  |  |  |  |
| V8 | 16 | 15 |  |  |  |  |  |  |  |  |  |  |  | 1 |  |  |  |  |  |
| V9 | 26 | 14 |  | 1 |  |  |  |  |  | 1 | 1 | 6 |  | 1 |  | 1 | 1 |  |  |
| V10 | 26 | 5 |  |  | 8 | 8 | 2 |  |  |  |  |  |  |  | 3 |  |  |  |  |
| V11 | 21 | 13 |  |  |  | 2 |  |  |  |  |  |  |  |  | 5 |  | 1 |  |  |
| V12 | 17 | 4 |  |  |  |  |  |  | 11 | 1 |  |  |  |  |  |  | 1 |  |  |
| V13 | 14 | 3 | 1 | 1 |  | 1 |  | 7 |  | 1 |  |  |  |  |  |  |  |  |  |
| V14 | 28 | 6 | 4 | 9 |  |  |  |  | 2 | 3 | 1 |  |  |  |  |  | 1 |  | 2 |
| V15 | 40 |  | 2 | 13 |  |  |  |  | 4 | 11 | 2 |  |  |  |  |  | 4 | 4 |  |
| VA | 15 |  | 1 | 3 | 2 | 4 |  |  |  | 1 |  |  |  | 1 | 2 |  |  |  | 1 |

## Items labelled `match` (equivalent, nothing else applies)

V2_1, V2_13, V2_14, V3_5, V3_17, V14_8, V14_29, VA_8

## Items with B false (primary `B_false_*`)

- V1_12 (`B_false_milnor`): critical set of x^2 is {x=0}, not the 'x axis'; B false
- V3_8 (`B_false_milnor`): B allows n=0 where S(X0,X0)≤0 fails; Milnor's chain implicitly has n≥1
- V9_13 (`B_false_blind`): Clause (2) quantifies over arbitrary sets A⊆V; false for A=∅; Milnor's TΩ is a subspace
- V10_18 (`B_false_milnor`): B believed false: Milnor's 'Clearly h is continuous' fails for metric d; A is project's dyadic JoinSystem repair
- V10_19 (`B_false_milnor`): First conjunct (Lemma 17.C continuity of h) believed false; A has Appendix lemmas and JoinSystem Theorem 17.1
- V10_23 (`B_false_milnor`): B quantifies n≥1 but for n=1 no conjugate points; Milnor's sphere example meant n≥2
- V11_11 (`B_false_milnor`): B allows n=1 where 'E**(W_i,W_i)<0 for some i≠n' is empty; Milnor needs n≥2; counter-model S^1
- V11_12 (`B_false_milnor`): B allows n=1 (Myers fails on circle: no conjugate points); A dim≥2; B adds index clause
- V11_14 (`B_false_milnor`): B allows n=1 where circle has no conjugate points; A only unit Sⁿ; clauses (d),(e) formalizer's reading
- V11_15 (`B_false_milnor`): B false for n=1 (flat line has long geodesics but E**≥0); Milnor presupposes n≥2; A uses explicit sin-bump fields
- V11_16 (`B_false_milnor`): B false at n=0 (attained unit vector needed); Milnor's (n−1)/r²>0 presupposes n≥2; A dim≥2, index estimate for any N
- VA_9 (`B_false_milnor`): Milnor's lemma has no closedness hypothesis but does not hold for non-closed X_0; A adds 'all X_n closed'
- VA_11 (`B_false_milnor`): Milnor never states closedness of Y_i; G not continuous for non-closed Y_i; project adds closedness

## Labelling conventions and judgment calls

- `setting` is applied whenever B quantifies over abstract manifolds/Lie groups (or an abstract model such as S^{2n+1}/S^1, an isometric copy of S^n via psi) while A is about a vector space E, a slice submanifold of V, a matrix group or the embedded sphere. It is not applied when A is itself abstract (Mathlib connection on any manifold, abstract Lie algebra, pure topology); the V12_1..V12_13 Lie-algebra items are coded `algebraic_only` instead.
- `vacuous` is added for every proved direction whose `uses_hypothesis` entry is false, and also where the text says a direction was re-proved outright although the field is empty (e.g. V1_4, V1_13, V6_x series). Embedded-case vacuity is noted too (V7_3, V9_15).
- Edge-case falsity (n = 0, n = 1, missing closedness of X_n/Y_i) is attributed to Milnor's text read literally (`B_false_milnor`) because the records say Milnor presupposes n >= 2 / closed subcomplexes; the sets-versus-subspaces bug of V9_13 is `B_false_blind`. V10_18 and V10_19 are coded `B_false_milnor` although `not_B` is False in the record: the text says B is believed false (Milnor's "clearly h is continuous") but this was not formalized.
- V15_13, V15_14, V15_17 carry `effort_only: true` in the record, but the text says the failed direction needs Clifford periodicity (absent from project and Mathlib), so they are `missing_math`, as in the taxonomy; V1_4, V5_6, V6_3 (Christoffel-symbol construction), V15_11, V15_28, V15_32, V15_39 are primary `effort`, and V1_9, V2_10, V6_7, V11_13, V15_41 carry it as a secondary code.
- The §16 BrokenSetup-versus-Milnor-subdivision gap (V10_5..V10_11, V10_14) is `hyp_A` (the taxonomy's "BrokenSetup instead of Milnor's subdivision"); the unrelated "fineness" notions of V9_16..V9_21 are `reading`.
- Near-matches that differ only by range or generality (e.g. V14_7, V14_28, V15_4, V15_16, VA_5) are coded with the corresponding `range`/`general_A`/`extra_A` code rather than `match`; only the 8 items above are pure matches.
- `harness` is a secondary code only (never primary): it is used where the record says a banned proof term sits in A's statement/definitions so that `#rt_check` was run on an A' or could not pass (V3_19, V3_22, V3_23, V4_6, V4_21, V6_9, V7_21, V8_14, V8_16, V9_1, V11_15, V11_24, V12_14, V13_6, V14_13, V15_23, V15_41, V15_42 and others).
- No record was left unclassified.
