# Failure taxonomy of the round trip (layer 3 labels)

Each item of `RoundTrip/Items/*.json` gets every code that applies to it (zero or more), read from
its `why`, `B_issue`, `embedded_special_case_note` and other notes. A code describes *why* A and B
are not simply equivalent (or why a direction is vacuous / B is false).

| code | meaning |
|---|---|
| `setting` | Abstract vs embedded: B quantifies over abstract (Riemannian) manifolds or abstract Lie groups, A over submanifolds of a Euclidean space / matrix groups. |
| `extra_A` | A states steps of Milnor's proof, auxiliary lemmas or bookkeeping as theorems that B does not contain. |
| `general_A` | A is more general: abstract algebra, any field/ring/index type/family, C² instead of C^∞, any model space, weaker hypotheses. |
| `hyp_A` | A assumes more: compactness, regular values, closedness, non-emptiness, finite dimension, a `BrokenSetup`/analytic fineness instead of Milnor's subdivision, connectedness. |
| `cw_model` | Mathlib `CWComplex` vs the project's iterated adjunction spaces / telescopes (cellular approximation missing). |
| `coefficients` | Homology over a field (project) vs over ℤ (Milnor); universal coefficients missing. |
| `taken_as_hyp` | A takes as a hypothesis something Milnor proves or cites: Hanner's theorem, Hypothesis (N), a pushing neighbourhood, connectedness of SU(n). |
| `algebraic_only` | The project formalizes only the algebraic/arithmetic step (Lie algebra model, spectral index formulas), not the geometric statement. |
| `range` | The formal result covers a smaller range: k ≤ 8, an explicit family, sets instead of groups, one base point, one model. |
| `structure_choice` | A uses one choice of structure (slice chart, model, base point) where B quantifies over all, or vice versa. |
| `reading` | The two read a word of Milnor differently ("diffeomorphic", "fine", "minimal", "manifold", Fréchet vs iterated derivative). |
| `finrank` | Finiteness hidden by `finrank` / ℕ-valued encodings (0 for infinite). |
| `vacuous` | A direction was proved without using its hypothesis (the conclusion is provable outright). |
| `B_false_milnor` | B is false because Milnor's statement is (n = 1, n = 0, closedness, "x axis", "clearly continuous"). |
| `B_false_blind` | B is false because of a blind-formalization bug (prelude norm, path space, sets vs subspaces, n = 0). |
| `missing_math` | A failed direction needs mathematics absent from the project and Mathlib (e.g. Clifford periodicity, normal form of skew matrices, uniqueness of the Levi-Civita connection, colimit spaces, π₁ torsion-free). |
| `effort` | A failed direction is believed true and only glue/effort is missing. |
| `harness` | `#rt_check` limitations shaped the result (banned proofs inside A's statement or definitions; checked on A′). |
| `match` | No obstacle: A and B say the same thing (equivalent with non-vacuous directions). |
