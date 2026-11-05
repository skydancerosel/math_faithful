import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.Parity
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
Milnor, *Morse Theory*, §5 (The Morse inequalities), pp. 28–31.

# The algebra of the Morse inequalities

Once the homology of each "slab" `(M^{a_i}, M^{a_{i-1}})` is known, everything Milnor does in
§5 is linear algebra over a field.  This file proves that linear algebra for an abstract
*homology of a filtration*, so that the topology enters only through two clearly separated
hypotheses: the exact sequence of a triple (an axiom of the abstract structure) and the
homology of the slabs (a hypothesis of the final theorems).

## Milnor's text (pp. 28–31), paraphrased

* **Definition** (p. 28).  `S` is an integer-valued function defined on some pairs of spaces.
  It is *subadditive* if `S(X,Z) ≤ S(X,Y) + S(Y,Z)` whenever `X ⊃ Y ⊃ Z`, and *additive* if
  equality always holds.
* **Examples** (p. 28).  For a field `F`, the Betti number `R_λ(X,Y) = dim_F H_λ(X,Y;F)`, on
  the pairs where it is finite, is subadditive, which Milnor reads off from the exact segment
  `H_λ(Y,Z) → H_λ(X,Z) → H_λ(X,Y)` of the triple `(X,Y,Z)`; the Euler characteristic
  `χ(X,Y) = Σ_λ (-1)^λ R_λ(X,Y)` is additive.  No further argument is given for either.
* **Lemma 5.1** (p. 28).  If `S` is subadditive and `X_0 ⊂ X_1 ⊂ ⋯ ⊂ X_n`, then
  `S(X_n,X_0) ≤ Σ_{i=1}^n S(X_i,X_{i-1})`, with equality when `S` is additive.  The proof is an
  induction on `n` through `S(X_n,X_0) ≤ S(X_{n-1},X_0) + S(X_n,X_{n-1})`.  Writing
  `S(X) = S(X,∅)` and taking `X_0 = ∅` gives inequality (1): `S(X_n) ≤ Σ_i S(X_i,X_{i-1})`.
* **The slabs** (p. 29).  For `M` compact and `f` with non-degenerate critical points, Milnor
  picks `a_1 < ⋯ < a_k` with exactly `i` critical points in `M^{a_i}` and `M^{a_k} = M`, and
  computes `H_*(M^{a_i}, M^{a_{i-1}}) = H_*(e^{λ_i}, ė^{λ_i})` by excision: the coefficient
  field in degree `λ_i`, the index of the `i`-th critical point, and `0` otherwise.  Hence
  `Σ_i R_λ(M^{a_i}, M^{a_{i-1}}) = C_λ`, the number of critical points of index `λ`.
* **Theorem 5.2** (weak Morse inequalities, p. 29).  (2) `R_λ(M) ≤ C_λ`, and
  (3) `Σ_λ (-1)^λ R_λ(M) = Σ_λ (-1)^λ C_λ`, by (1) for `S = R_λ` and for `S = χ`.
* **Lemma 5.3** (pp. 29–30).  `S_λ(X,Y) = R_λ(X,Y) - R_{λ-1}(X,Y) + ⋯ ± R_0(X,Y)` is
  subadditive.  Proof: for an exact sequence `→ A → B → C → ⋯ → D → 0` of vector spaces, with
  `h` the map into `A` and `i` the map out of it, `rank h + rank i = dim A`, so by unwinding
  `rank h = dim A - dim B + dim C - ⋯ ± dim D`, which is therefore `≥ 0`.  For the homology
  sequence of a triple `X ⊃ Y ⊃ Z` and `h = ∂ : H_{λ+1}(X,Y) → H_λ(Y,Z)` the right side is
  `S_λ(Y,Z) - S_λ(X,Z) + S_λ(X,Y)`.
* **The Morse inequalities** (p. 30).  Lemma 5.1 for `S_λ` and the chain
  `∅ ⊂ M^{a_1} ⊂ ⋯ ⊂ M^{a_k}` gives
  `(4_λ)  R_λ(M) - R_{λ-1}(M) + ⋯ ± R_0(M) ≤ C_λ - C_{λ-1} + ⋯ ± C_0`.
  Milnor then observes that `(4_λ)` and `(4_{λ-1})` together give (2), that `(4_λ)` and
  `(4_{λ-1})` for `λ > n` give (3), and that `(4_λ)` is an equality when `C_{λ+1} = 0`.
* **Corollary 5.4** (p. 31).  If `C_{λ+1} = C_{λ-1} = 0` then `R_λ = C_λ` and
  `R_{λ+1} = R_{λ-1} = 0`.  Milnor remarks that this computes the homology of `ℂPⁿ` without
  Theorem 3.5.

(The strong inequalities `(4_λ)` are unnumbered in the book; Lemma 5.3 is the subadditivity
of `S_λ`, and Theorem 5.2 is the *weak* inequalities.)

## The abstraction

* **Spaces become indices.**  A preorder `ι` indexes the spaces, `a ≤ b` standing for
  `X_a ⊆ X_b`.  For Milnor, `ι = ℝ` with `X_a = M^a = f⁻¹(-∞, a]`, or `ι = ℕ` with
  `X_k = M^{a_k}`; `ι = Set M` ordered by inclusion also works.  A function on pairs is a
  function `S : ι → ι → ℤ` of which only the values at `a ≤ b` are ever used.
* **Argument order.**  Lean's `S a b` (with `a ≤ b`) is Milnor's `S(X_b, X_a)`: Milnor writes
  the bigger space first, Lean lists the indices in increasing order.  Milnor's triple
  `X ⊃ Y ⊃ Z` is `a ≤ b ≤ c` with `Z = X_a`, `Y = X_b`, `X = X_c`, and his
  `S(X,Z) ≤ S(X,Y) + S(Y,Z)` reads `S a c ≤ S a b + S b c` (`Morse.IsSubadditive`).
* **Homology.**  `Morse.FiltrationHomology F ι H` packages exactly what §5 uses:
  `H i a b` is `H_i(X_b, X_a; F)`, finite-dimensional for `a ≤ b`, and for every triple
  `a ≤ b ≤ c` there is a long exact sequence (`Morse.LongExactSeq`)
  `⋯ → H_i(X_b,X_a) → H_i(X_c,X_a) → H_i(X_c,X_b) →∂ H_{i-1}(X_b,X_a) → ⋯ → H_0(X_c,X_b) → 0`,
  exact at every node.  Nothing else is assumed: no functoriality, no compatibility between
  the sequences of different triples, no `H_*(X,X) = 0`, no excision.  Values `H i a b` with
  `a ≰ b` are never used (an instance may take, e.g., `H_i(X_a ∪ X_b, X_a)`).
* **The chain.**  `X : ℕ → ι` with `X k ≤ X (k+1)` for `k < n` is Milnor's
  `X_0 ⊂ X_1 ⊂ ⋯ ⊂ X_n` (for a filtration indexed by `ℕ` itself, take `X = id`).  The Betti
  numbers of the filtration are `b_i = dim H_i(X_n, X_0)` (Milnor's `R_i(M)` when `X_0 = ∅`,
  `X_n = M`), and its *Morse numbers* are `C_i = Σ_{k<n} dim H_i(X_{k+1}, X_k)`
  (`Morse.morseNumber`).
* **Critical points.**  A finite set `P` with an index `ind p` and a step `step p < n` (the slab
  `a_k < f(p) < a_{k+1}` containing `p`, for `k = step p`).  The topological input of p. 29
  becomes the hypothesis `dim H_i(X_{k+1}, X_k) = #{p ∈ P | step p = k ∧ ind p = i}`
  (step `k` attaches one `i`-cell for each critical point of index `i` in the slab), under
  which `C_i = #{p ∈ P | ind p = i}` (`Morse.morseNumber_eq_card`).  The special case of one
  critical point per step, as in Milnor, is `Morse.morseNumber_eq_card_of_single`.

## What Milnor leaves implicit, and how it is handled

* **The domain of `S`** (p. 28).  Milnor does not say on which pairs `S` is defined.
  Subadditivity only makes sense on a class of pairs closed under the passage from `(X,Y)`,
  `(Y,Z)` to `(X,Z)`.  For `R_λ` the class is the pairs with finite-dimensional homology, and its
  closedness is itself a small lemma (if `H_λ(Y,Z)` and `H_λ(X,Y)` are finite-dimensional, so is
  `H_λ(X,Z)`): `Morse.LongExactSeq.finiteDimensional_middle`.  Here all pairs `a ≤ b` are
  assumed finite-dimensional; `Morse.FiltrationHomology.ofSteps` builds the structure on a chain
  from the finiteness of the slabs alone, so that the finiteness of `H_*(M; F)` is a
  consequence, as in Milnor, and not an assumption.
* **Subadditivity of `R_λ`** (p. 28), which Milnor leaves to the reader: rank–nullity at the
  middle of `H_λ(Y,Z) → H_λ(X,Z) → H_λ(X,Y)`, `Morse.LongExactSeq.finrank_le`.
* **Additivity of `χ`** (p. 28), asserted without proof.  It needs `Σ_λ R_λ < ∞` for the three
  pairs, and is the vanishing of the alternating sum of a finite exact sequence.  Here `χ` is
  truncated at a degree `N`, and additivity on a triple `a ≤ b ≤ c` needs only
  `H_{N+1}(X_c, X_b) = 0`: `Morse.LongExactSeq.altSum_eq_of_finrank_eq_zero`,
  `Morse.FiltrationHomology.isAdditive_eulerChar`.
* **Lemma 5.1 for `n = 0`.**  Milnor's induction starts at `n = 1`.  For the empty chain the
  statement would be `S(X_0, X_0) ≤ 0`, which subadditivity does not give (it gives only
  `S(X,X) ≥ 0`); hence the hypothesis `0 < n` throughout.  The induction uses subadditivity only
  on the triples `X_m ⊃ X_{m-1} ⊃ X_0`; `Morse.le_sum_of_chain` assumes exactly that.
* **Distinct critical values** (p. 29).  Milnor's choice of `a_i` with exactly `i` critical
  points in `M^{a_i}` requires distinct critical points to have distinct critical values,
  which is not assumed.  The cell hypothesis above allows any number of critical points per
  slab; this is the form in which the slab computation holds in general.
* **The bottom of the chain** (p. 29).  Milnor applies (1) to `∅ = M^{a_0} ⊂ ⋯ ⊂ M^{a_k} = M`,
  but only `a_1, …, a_k` were introduced; `a_0` is any number below `min f`.  Likewise the last
  term `± C_n` of his formula for `χ(M)` takes `n = dim M`, the indices being at most `n`.  Here
  the bottom `X_0` is arbitrary (`b_i = dim H_i(X_n, X_0)`), and the bound on the indices is a
  hypothesis (`hN` in `Morse.FiltrationHomology.euler_characteristic_eq`).
* **Excision** (p. 29).  The identification `H_*(M^{a_{i-1}} ∪ e^λ, M^{a_{i-1}}) =
  H_*(e^λ, ė^λ)` is not literally an excision (the closure of the excised set is not in the
  interior of `M^{a_{i-1}}`; one thickens first).  It is not part of the algebra: it is the
  content of the cell hypothesis `hcells` of the final theorems.
* **The end of the sequence** (p. 29).  Milnor's exact sequence ends with `→ D → 0`.  For the
  homology sequence of a triple this is the surjectivity of `H_0(X,Z) → H_0(X,Y)`, true because
  `H_{-1} = 0`; it is the field `Morse.LongExactSeq.surjective_g_zero`.  Milnor's "rank" of a
  vector space is its dimension, and finite-dimensionality is needed for rank–nullity.
* **`Σ_i S_λ(M^{a_i}, M^{a_{i-1}}) = C_λ - C_{λ-1} + ⋯ ± C_0`** (p. 30) is the linearity of the
  alternating sum (`Morse.altSum_sum`).
* **(3) from the strong inequalities** (p. 30).  Milnor compares `(4_λ)` and `(4_{λ-1})` for
  `λ > n = dim M`.  Only `λ = n + 1` matters: `(4_{n+1})` and `(4_n)` give
  `Σ_{i ≤ n} (-1)^i R_i = Σ_{i ≤ n} (-1)^i C_i` using only `C_{n+1} = 0` and `R_{n+1} ≥ 0`
  (`Morse.sum_neg_one_pow_eq_of_altSum_le`).  That the left side is the whole alternating sum
  `Σ_i (-1)^i R_i(M)` uses `R_i(M) = 0` for `i > n`, which is (2), there being no critical
  points of index `> n` (`Morse.FiltrationHomology.finrank_eq_zero_of_forall_ne`).
* **Corollary 5.4 for `λ = 0`**, where `C_{λ-1}` is meaningless (read: `0`):
  `Morse.eq_of_altSum_le_zero`, beside the case `λ ≥ 1`, `Morse.eq_of_altSum_le_succ`.
  Milnor's argument uses `R_{λ+1} = 0`; only `R_{λ+1} ≥ 0` is needed.
* **`ℂPⁿ`** (p. 31).  Corollary 5.4 gives the Betti numbers over every field, not the integral
  homology groups.  The field statement, in the form "if no two consecutive Morse numbers are
  nonzero then `b_i = C_i` for all `i`" (the lacunary principle), is
  `Morse.eq_of_altSum_le_of_lacunary` and
  `Morse.FiltrationHomology.finrank_eq_morseNumber_of_lacunary`.

## Main results

* `Morse.finrank_range_eq_altSum`: Milnor's computation (p. 30) for an exact sequence
  `V_{n+1} → V_n → ⋯ → V_0 → 0`: the rank of the first map is `Σ_{k ≤ n} (-1)^{n-k} dim V_k`.
  `Morse.altSum_finrank_eq_zero_of_exact`: the alternating sum of a finite exact sequence is
  `0` (Mathlib has this for `Fin`-indexed sequences,
  `Module.sum_neg_one_pow_finrank_eq_zero_of_exact`; the truncated version is not in Mathlib).
* `Morse.LongExactSeq.finrank_range_δ`: for the sequence of a triple,
  `rank ∂_λ = S_λ(Y,Z) - S_λ(X,Z) + S_λ(X,Y)`.
* `Morse.IsSubadditive.le_sum`, `Morse.IsAdditive.eq_sum`: Lemma 5.1.
* `Morse.FiltrationHomology.isSubadditive_finrank`: `R_λ` is subadditive (p. 28).
  `Morse.FiltrationHomology.isSubadditive_altSum`: Lemma 5.3.
  `Morse.FiltrationHomology.isAdditive_eulerChar`: `χ` is additive (p. 28).
* `Morse.FiltrationHomology.finrank_le_morseNumber` (Theorem 5.2 (2)),
  `Morse.FiltrationHomology.altSum_le_morseNumber` (the Morse inequalities `(4_λ)`),
  `Morse.FiltrationHomology.sum_neg_one_pow_finrank_eq` (Theorem 5.2 (3)), for any filtration.
* `Morse.le_of_altSum_le`, `Morse.altSum_eq_of_altSum_le`, `Morse.eq_of_altSum_le_succ`,
  `Morse.eq_of_altSum_le_zero` (Corollary 5.4), `Morse.eq_of_altSum_le_of_lacunary`: the
  numerical consequences on pp. 30–31, for any two sequences satisfying `(4_λ)` for all `λ`;
  for a filtration, `Morse.FiltrationHomology.finrank_eq_morseNumber_of_succ`,
  `Morse.FiltrationHomology.finrank_eq_morseNumber_of_zero` (Corollary 5.4) and
  `Morse.FiltrationHomology.finrank_eq_morseNumber_of_lacunary`.
* `Morse.FiltrationHomology.weak_morse_inequality`, `Morse.FiltrationHomology.morse_inequality`,
  `Morse.FiltrationHomology.euler_characteristic_eq`: the three statements in terms of critical
  points: `b_λ ≤ C_λ`, `(4_λ)`, and `Σ_{i ≤ N} (-1)^i b_i = Σ_{p ∈ P} (-1)^{ind p}` when all
  indices are `≤ N`, where `C_λ = #{p ∈ P | ind p = λ}`.

## How the results here are instantiated

To obtain Milnor's Theorem 5.2 and `(4_λ)` for a Morse function `f` on a compact manifold `M`
from the results here, one needs the three steps below.  All three are now carried out in
`Morse/Homology/` (relative singular homology, the sequences of pairs and triples, and excision in
`Relative.lean`, `Triple.lean` and `Excision.lean`; the instantiation in `MorseHomology.lean`:
`Morse.Homology.bettiNumber_le_critCount`, `Morse.Homology.altSum_bettiNumber_le`,
`Morse.Homology.sum_bettiNumber_eq_sum_critCount`); the list records what was needed:

1. **Relative singular homology with coefficients in `F` and the exact sequence of a triple.**
   Mathlib (v4.33.1) has the absolute singular homology functor
   (`AlgebraicTopology.singularHomologyFunctor`) with its homotopy invariance, and the
   Eilenberg–Steenrod data `TopPair.HomologyPretheory` (relative functors and boundary maps),
   but not relative singular homology, the exactness of its sequences, or excision.  Given
   those, `H i j k := H_i(M^{a_k}, M^{a_j}; F)` (with `ι = ℕ`), or `H i a b := H_i(M^b, M^a; F)`
   (with `ι = ℝ`), together with the sequences of the triples, is a
   `Morse.FiltrationHomology`; on a chain, `Morse.FiltrationHomology.ofSteps` reduces the
   finiteness to that of the slabs.
2. **The homology of a slab** (Milnor p. 29): for a slab containing critical points of indices
   `ind p`, `dim H_i(M^{a_{k+1}}, M^{a_k}; F) = #{p | ind p = i}`.  This uses Theorem 3.1 (with
   no critical values in between, `M^a` is a deformation retract of `M^b`), Theorem 3.2 with
   Remark 3.3 (`M^{c-ε}` with cells attached is a deformation retract of `M^{c+ε}`), homotopy
   invariance, excision (after thickening), and `H_*(D^λ, S^{λ-1}; F) = F` in degree `λ`.  This
   is the hypothesis `hcells`.
3. **The choice of the chain**: `a_0 < min f`, one critical value in each `(a_k, a_{k+1})`,
   `a_n ≥ max f`, so that `X_0 = ∅` and `X_n = M` and `b_i = dim H_i(M; F)`.
-/

open Finset Module

noncomputable section

namespace Morse

/-! ## Alternating sums -/

section AltSum

/-- The truncated alternating sum `d n - d (n - 1) + d (n - 2) - ⋯ ± d 0`.

With `d i = R_i(X, Y)` and `n = λ` this is Milnor's
`S_λ(X, Y) = R_λ(X, Y) - R_{λ-1}(X, Y) + R_{λ-2}(X, Y) - + ⋯ ± R_0(X, Y)` (p. 29), and with
`d i = C_i` the right side `C_λ - C_{λ-1} + ⋯ ± C_0` of the Morse inequality `(4_λ)` (p. 30). -/
def altSum (d : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ i ∈ range (n + 1), (-1) ^ (n - i) * d i

@[simp]
theorem altSum_zero (d : ℕ → ℤ) : altSum d 0 = d 0 := by
  simp [altSum]

/-- The recursion `S_{λ+1} = R_{λ+1} - S_λ`. -/
theorem altSum_succ (d : ℕ → ℤ) (n : ℕ) : altSum d (n + 1) = d (n + 1) - altSum d n := by
  have h : ∀ i ∈ range (n + 1), (-1 : ℤ) ^ (n + 1 - i) * d i = -((-1) ^ (n - i) * d i) := by
    intro i hi
    rw [show n + 1 - i = n - i + 1 by have := mem_range.mp hi; omega, pow_succ]
    ring
  rw [altSum, sum_range_succ, sum_congr rfl h, sum_neg_distrib, altSum, Nat.sub_self, pow_zero,
    one_mul]
  ring

/-- `S_{λ+1} + S_λ = R_{λ+1}`: this is why adding `(4_{λ+1})` and `(4_λ)` gives `(2_{λ+1})`
(Milnor p. 30). -/
theorem altSum_succ_add_altSum (d : ℕ → ℤ) (n : ℕ) : altSum d (n + 1) + altSum d n = d (n + 1) := by
  rw [altSum_succ]
  ring

/-- `altSum d n` only depends on `d 0, …, d n`. -/
theorem altSum_congr {d e : ℕ → ℤ} {n : ℕ} (h : ∀ i ≤ n, d i = e i) : altSum d n = altSum e n :=
  sum_congr rfl fun i hi ↦ by rw [h i (Nat.lt_succ_iff.mp (mem_range.mp hi))]

theorem altSum_add (d e : ℕ → ℤ) (n : ℕ) :
    altSum (fun i ↦ d i + e i) n = altSum d n + altSum e n := by
  simp only [altSum, mul_add, sum_add_distrib]

theorem altSum_sub (d e : ℕ → ℤ) (n : ℕ) :
    altSum (fun i ↦ d i - e i) n = altSum d n - altSum e n := by
  simp only [altSum, mul_sub, sum_sub_distrib]

/-- The alternating sum of a finite sum is the sum of the alternating sums.  Milnor uses this on
p. 30 to rewrite `Σ_i S_λ(M^{a_i}, M^{a_{i-1}})` as `C_λ - C_{λ-1} + ⋯ ± C_0`. -/
theorem altSum_sum {κ : Type*} (s : Finset κ) (d : κ → ℕ → ℤ) (n : ℕ) :
    altSum (fun i ↦ ∑ k ∈ s, d k i) n = ∑ k ∈ s, altSum (d k) n := by
  simp only [altSum, mul_sum]
  exact sum_comm

/-- The telescoping identity behind Milnor's computation on p. 30: if `d 0 = r 0` and
`d (i + 1) = r (i + 1) + r i` for `i < n`, then `d n - d (n - 1) + ⋯ ± d 0 = r n`. -/
theorem altSum_eq_of_telescope {d r : ℕ → ℤ} {n : ℕ} (h₀ : d 0 = r 0)
    (h : ∀ i < n, d (i + 1) = r (i + 1) + r i) : altSum d n = r n := by
  induction n with
  | zero => simpa using h₀
  | succ n ih =>
    rw [altSum_succ, ih fun i hi ↦ h i (by omega), h n (by omega)]
    ring

/-- The Euler characteristic truncated at degree `N` is `(-1)^N` times the alternating sum
`S_N`: `Σ_{i ≤ N} (-1)^i d i = (-1)^N (d N - d (N-1) + ⋯ ± d 0)`. -/
theorem sum_neg_one_pow_mul_eq (d : ℕ → ℤ) (N : ℕ) :
    ∑ i ∈ range (N + 1), (-1) ^ i * d i = (-1) ^ N * altSum d N := by
  rw [altSum, mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (mem_range.mp hi))
  rw [Nat.add_sub_cancel_left, pow_add]
  rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] <;> ring

end AltSum

/-! ## Exact sequences of finite-dimensional vector spaces -/

section ExactSequence

variable {F : Type*} [Field F]

/-- **Milnor's computation in the proof of Lemma 5.3** (pp. 29–30).  Let
`V (n+1) →d_n V n →d_{n-1} ⋯ →d_0 V 0 → 0` be exact at `V 0, …, V n`, with every `V k`
finite-dimensional.  Then `rank d_n = dim V n - dim V (n-1) + ⋯ ± dim V 0`.

In Milnor's notation `h = d_n`, `A = V n`, `B = V (n-1)`, …, `D = V 0`.  His first step
`rank h + rank i = dim A` is rank–nullity for `i = d_{n-1}` together with exactness at `A`
(`ker i = range h`); unwinding it down the sequence is `Morse.altSum_eq_of_telescope`. -/
theorem finrank_range_eq_altSum {V : ℕ → Type*} [∀ k, AddCommGroup (V k)] [∀ k, Module F (V k)]
    [∀ k, FiniteDimensional F (V k)] (d : ∀ k, V (k + 1) →ₗ[F] V k) {n : ℕ}
    (exact : ∀ k < n, Function.Exact (d (k + 1)) (d k)) (surj : Function.Surjective (d 0)) :
    (finrank F (LinearMap.range (d n)) : ℤ) = altSum (fun k ↦ (finrank F (V k) : ℤ)) n := by
  refine (altSum_eq_of_telescope (r := fun k ↦ (finrank F (LinearMap.range (d k)) : ℤ)) ?_
    fun k hk ↦ ?_).symm
  · rw [LinearMap.range_eq_top.mpr surj, finrank_top]
  · rw [← (d k).finrank_range_add_finrank_ker, (exact k hk).linearMap_ker_eq]
    push_cast
    ring

/-- **The alternating sum of the dimensions in a finite exact sequence is zero.**  If
`0 → V n → V (n-1) → ⋯ → V 0 → 0` is exact (that is, `d_n = 0` in the setting of
`Morse.finrank_range_eq_altSum`), then `Σ_{k ≤ n} (-1)^{n-k} dim V k = 0`.  This is the
argument behind the additivity of the Euler characteristic, which Milnor asserts on p. 28.
Mathlib has the same statement for `Fin`-indexed sequences,
`Module.sum_neg_one_pow_finrank_eq_zero_of_exact`. -/
theorem altSum_finrank_eq_zero_of_exact {V : ℕ → Type*} [∀ k, AddCommGroup (V k)]
    [∀ k, Module F (V k)] [∀ k, FiniteDimensional F (V k)] (d : ∀ k, V (k + 1) →ₗ[F] V k)
    {n : ℕ} (exact : ∀ k < n, Function.Exact (d (k + 1)) (d k))
    (surj : Function.Surjective (d 0)) (hn : d n = 0) :
    altSum (fun k ↦ (finrank F (V k) : ℤ)) n = 0 := by
  rw [← finrank_range_eq_altSum d exact surj, hn, LinearMap.range_zero, finrank_bot,
    Nat.cast_zero]

/-- A long exact sequence of vector spaces over `F`, indexed by the degree `i : ℕ` and ending in
`0`:
`⋯ → A (i+1) → B (i+1) → C (i+1) →δ A i → B i → C i → ⋯ → A 0 → B 0 → C 0 → 0`.

This is the shape of the homology sequence of a triple `X ⊃ Y ⊃ Z` (Milnor p. 30), with
`A i = H_i(Y, Z)`, `B i = H_i(X, Z)`, `C i = H_i(X, Y)`, `f` and `g` induced by the inclusions
of pairs and `δ` the boundary `∂ : H_{i+1}(X, Y) → H_i(Y, Z)`.  The sequence is exact at every
node; exactness at `C 0` (the map into `A_{-1} = 0`) is the surjectivity of `g 0`. -/
structure LongExactSeq (F : Type*) [Field F] (A B C : ℕ → Type*)
    [∀ i, AddCommGroup (A i)] [∀ i, Module F (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module F (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module F (C i)] where
  /-- `H_i(Y, Z) → H_i(X, Z)`. -/
  f : ∀ i, A i →ₗ[F] B i
  /-- `H_i(X, Z) → H_i(X, Y)`. -/
  g : ∀ i, B i →ₗ[F] C i
  /-- The boundary `∂ : H_{i+1}(X, Y) → H_i(Y, Z)`. -/
  δ : ∀ i, C (i + 1) →ₗ[F] A i
  /-- Exactness at `B i`. -/
  exact_f_g : ∀ i, Function.Exact (f i) (g i)
  /-- Exactness at `C (i + 1)`. -/
  exact_g_δ : ∀ i, Function.Exact (g (i + 1)) (δ i)
  /-- Exactness at `A i`. -/
  exact_δ_f : ∀ i, Function.Exact (δ i) (f i)
  /-- Exactness at `C 0`: the sequence ends with `B 0 → C 0 → 0`. -/
  surjective_g_zero : Function.Surjective (g 0)

namespace LongExactSeq

variable {A B C : ℕ → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module F (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module F (B i)]
  [∀ i, AddCommGroup (C i)] [∀ i, Module F (C i)]
  (E : LongExactSeq F A B C)
include E

/-- If `H_i(Y,Z)` and `H_i(X,Y)` are finite-dimensional, so is `H_i(X,Z)`.  Milnor defines `R_λ`
only on the pairs whose `λ`-th homology is finite-dimensional (p. 28); this lemma is the
closedness of that class under `(X,Y), (Y,Z) ↦ (X,Z)`, which his statement that `R_λ` is
subadditive presupposes. -/
theorem finiteDimensional_middle (i : ℕ) [FiniteDimensional F (A i)]
    [FiniteDimensional F (C i)] : FiniteDimensional F (B i) := by
  have hex : Function.Exact (E.f i) (E.g i).rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, ← LinearMap.exact_iff]
    exact E.exact_f_g i
  exact Module.Finite.of_exact hex (E.g i).surjective_rangeRestrict

variable [∀ i, FiniteDimensional F (A i)] [∀ i, FiniteDimensional F (B i)]
  [∀ i, FiniteDimensional F (C i)]

/-- **`R_λ` is subadditive** (Milnor p. 28, left to the reader with a pointer to the exact
segment `H_λ(Y,Z) → H_λ(X,Z) → H_λ(X,Y)`): `R_λ(X,Z) ≤ R_λ(Y,Z) + R_λ(X,Y)`.  Proof:
rank–nullity for `g`, with `ker g = range f`. -/
theorem finrank_le (i : ℕ) : finrank F (B i) ≤ finrank F (A i) + finrank F (C i) := by
  have h₁ := (E.g i).finrank_range_add_finrank_ker
  rw [(E.exact_f_g i).linearMap_ker_eq] at h₁
  have h₂ := (E.f i).finrank_range_le
  have h₃ := Submodule.finrank_le (LinearMap.range (E.g i))
  omega

/-- **The key identity of Lemma 5.3** (Milnor p. 30): for the boundary
`∂ = δ λ : C (λ+1) → A λ`,
`rank ∂ = S_λ(A) - S_λ(B) + S_λ(C)`, where `S_λ(V) = dim V λ - dim V (λ-1) + ⋯ ± dim V 0`.
In Milnor's notation, `rank ∂ = S_λ(Y,Z) - S_λ(X,Z) + S_λ(X,Y)`.

Rank–nullity at the three kinds of nodes gives `dim A i = rank f_i + rank δ_i`,
`dim B i = rank g_i + rank f_i`, `dim C (i+1) = rank δ_i + rank g_{i+1}` and
`dim C 0 = rank g_0`; so `dim A i - dim B i + dim C i = rank δ_i + rank δ_{i-1}` (without the
second term for `i = 0`), and the alternating sum telescopes to `rank δ_λ`.  This is Milnor's
unwinding along the sequence `H_λ(Y,Z) → H_λ(X,Z) → H_λ(X,Y) → H_{λ-1}(Y,Z) → ⋯ → 0`,
grouped by degree. -/
theorem finrank_range_δ (l : ℕ) :
    (finrank F (LinearMap.range (E.δ l)) : ℤ) =
      altSum (fun i ↦ (finrank F (A i) : ℤ)) l - altSum (fun i ↦ (finrank F (B i) : ℤ)) l +
        altSum (fun i ↦ (finrank F (C i) : ℤ)) l := by
  have hA : ∀ i, (finrank F (A i) : ℤ) =
      finrank F (LinearMap.range (E.f i)) + finrank F (LinearMap.range (E.δ i)) := by
    intro i
    rw [← (E.f i).finrank_range_add_finrank_ker, (E.exact_δ_f i).linearMap_ker_eq]
    push_cast
    ring
  have hB : ∀ i, (finrank F (B i) : ℤ) =
      finrank F (LinearMap.range (E.g i)) + finrank F (LinearMap.range (E.f i)) := by
    intro i
    rw [← (E.g i).finrank_range_add_finrank_ker, (E.exact_f_g i).linearMap_ker_eq]
    push_cast
    ring
  have hC : ∀ i, (finrank F (C (i + 1)) : ℤ) =
      finrank F (LinearMap.range (E.δ i)) + finrank F (LinearMap.range (E.g (i + 1))) := by
    intro i
    rw [← (E.δ i).finrank_range_add_finrank_ker, (E.exact_g_δ i).linearMap_ker_eq]
    push_cast
    ring
  have hC₀ : (finrank F (C 0) : ℤ) = finrank F (LinearMap.range (E.g 0)) := by
    rw [LinearMap.range_eq_top.mpr E.surjective_g_zero, finrank_top]
  have key : altSum (fun i ↦ (finrank F (A i) : ℤ) - finrank F (B i) + finrank F (C i)) l =
      finrank F (LinearMap.range (E.δ l)) := by
    refine altSum_eq_of_telescope
      (r := fun i ↦ (finrank F (LinearMap.range (E.δ i)) : ℤ)) ?_ fun i _ ↦ ?_
    · simp only [hA, hB, hC₀]
      ring
    · simp only [hA, hB, hC]
      ring
  rw [← key, altSum_add, altSum_sub]

/-- **Lemma 5.3 for one triple** (Milnor p. 30): `S_λ(X,Z) ≤ S_λ(X,Y) + S_λ(Y,Z)`, because
`rank ∂ ≥ 0`. -/
theorem altSum_le (l : ℕ) :
    altSum (fun i ↦ (finrank F (B i) : ℤ)) l ≤
      altSum (fun i ↦ (finrank F (A i) : ℤ)) l + altSum (fun i ↦ (finrank F (C i) : ℤ)) l := by
  have h := E.finrank_range_δ l
  have h₀ : (0 : ℤ) ≤ finrank F (LinearMap.range (E.δ l)) := Nat.cast_nonneg _
  linarith

/-- **Additivity of the Euler characteristic for one triple** (Milnor p. 28, stated without
proof).  If `C (N+1) = 0` (in Milnor's notation `H_{N+1}(X,Y) = 0`), then `∂_N = 0`, and the
truncated alternating sums are additive: `S_N(X,Z) = S_N(X,Y) + S_N(Y,Z)`. -/
theorem altSum_eq_of_finrank_eq_zero {N : ℕ} (hN : finrank F (C (N + 1)) = 0) :
    altSum (fun i ↦ (finrank F (B i) : ℤ)) N =
      altSum (fun i ↦ (finrank F (A i) : ℤ)) N + altSum (fun i ↦ (finrank F (C i) : ℤ)) N := by
  have h := E.finrank_range_δ N
  have h₀ : finrank F (LinearMap.range (E.δ N)) = 0 := by
    have := (E.δ N).finrank_range_le
    omega
  rw [h₀, Nat.cast_zero] at h
  linarith

end LongExactSeq

end ExactSequence

/-! ## Subadditive functions and Lemma 5.1 -/

section Subadditive

variable {ι : Type*}

/-- **Subadditive functions** (Milnor p. 28).  `S a b` (for `a ≤ b`) is Milnor's `S(X_b, X_a)`;
`S` is subadditive if `S(X,Z) ≤ S(X,Y) + S(Y,Z)` whenever `X ⊃ Y ⊃ Z`, i.e.
`S a c ≤ S a b + S b c` whenever `a ≤ b ≤ c`. -/
def IsSubadditive [Preorder ι] (S : ι → ι → ℤ) : Prop :=
  ∀ ⦃a b c : ι⦄, a ≤ b → b ≤ c → S a c ≤ S a b + S b c

/-- **Additive functions** (Milnor p. 28): equality in the subadditivity inequality. -/
def IsAdditive [Preorder ι] (S : ι → ι → ℤ) : Prop :=
  ∀ ⦃a b c : ι⦄, a ≤ b → b ≤ c → S a c = S a b + S b c

theorem IsAdditive.isSubadditive [Preorder ι] {S : ι → ι → ℤ} (hS : IsAdditive S) :
    IsSubadditive S :=
  fun _ _ _ hab hbc ↦ (hS hab hbc).le

/-- **Milnor's induction for Lemma 5.1** (p. 28), with the hypothesis it actually uses:
subadditivity on the triples `X_{m+1} ⊃ X_m ⊃ X_0` only. -/
theorem le_sum_of_chain (S : ι → ι → ℤ) (X : ℕ → ι) {n : ℕ} (hn : 0 < n)
    (hS : ∀ m, 0 < m → m < n → S (X 0) (X (m + 1)) ≤ S (X 0) (X m) + S (X m) (X (m + 1))) :
    S (X 0) (X n) ≤ ∑ k ∈ range n, S (X k) (X (k + 1)) := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n ih =>
    rw [sum_range_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp
    · have h₁ := ih hn' fun m hm hmn ↦ hS m hm (by omega)
      have h₂ := hS n hn' (by omega)
      linarith

/-- The equality case of Milnor's induction for Lemma 5.1 (p. 28). -/
theorem eq_sum_of_chain (S : ι → ι → ℤ) (X : ℕ → ι) {n : ℕ} (hn : 0 < n)
    (hS : ∀ m, 0 < m → m < n → S (X 0) (X (m + 1)) = S (X 0) (X m) + S (X m) (X (m + 1))) :
    S (X 0) (X n) = ∑ k ∈ range n, S (X k) (X (k + 1)) := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n ih =>
    rw [sum_range_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simp
    · rw [hS n hn' (by omega), ih hn' fun m hm hmn ↦ hS m hm (by omega)]

/-- In a chain `X_0 ≤ X_1 ≤ ⋯ ≤ X_n`, `X_i ≤ X_j` for `i ≤ j ≤ n`. -/
theorem chain_le [Preorder ι] {X : ℕ → ι} {n : ℕ} (hX : ∀ k < n, X k ≤ X (k + 1)) {i j : ℕ}
    (hij : i ≤ j) (hjn : j ≤ n) : X i ≤ X j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (hX j (by omega))

/-- **Lemma 5.1** (Milnor p. 28).  If `S` is subadditive and `X_0 ≤ X_1 ≤ ⋯ ≤ X_n` with
`n ≥ 1`, then `S(X_n, X_0) ≤ Σ_{k=1}^{n} S(X_k, X_{k-1})`. -/
theorem IsSubadditive.le_sum [Preorder ι] {S : ι → ι → ℤ} (hS : IsSubadditive S) {X : ℕ → ι}
    {n : ℕ} (hX : ∀ k < n, X k ≤ X (k + 1)) (hn : 0 < n) :
    S (X 0) (X n) ≤ ∑ k ∈ range n, S (X k) (X (k + 1)) :=
  le_sum_of_chain S X hn fun m _ hmn ↦ hS (chain_le hX (Nat.zero_le m) hmn.le) (hX m hmn)

/-- **Lemma 5.1, equality case** (Milnor p. 28): for additive `S`,
`S(X_n, X_0) = Σ_{k=1}^{n} S(X_k, X_{k-1})`. -/
theorem IsAdditive.eq_sum [Preorder ι] {S : ι → ι → ℤ} (hS : IsAdditive S) {X : ℕ → ι}
    {n : ℕ} (hX : ∀ k < n, X k ≤ X (k + 1)) (hn : 0 < n) :
    S (X 0) (X n) = ∑ k ∈ range n, S (X k) (X (k + 1)) :=
  eq_sum_of_chain S X hn fun m _ hmn ↦ hS (chain_le hX (Nat.zero_le m) hmn.le) (hX m hmn)

end Subadditive

/-! ## The homology of a filtration -/

/-- **The homology of a filtration**, abstracting what Milnor uses in §5 (pp. 28–30).

The preorder `ι` indexes spaces `X_a`, with `a ≤ b` meaning `X_a ⊆ X_b`, and `H i a b` is the
relative homology `H_i(X_b, X_a; F)`.  The structure records:
* `finiteDimensional`: `H_i(X_b, X_a; F)` is finite-dimensional for `a ≤ b` (Milnor's `R_λ` is
  only used on such pairs);
* `les`: for every triple `a ≤ b ≤ c` (Milnor's `X ⊃ Y ⊃ Z` with `Z = X_a`, `Y = X_b`,
  `X = X_c`) the homology sequence of the triple,
  `⋯ → H_i(X_b,X_a) → H_i(X_c,X_a) → H_i(X_c,X_b) →∂ H_{i-1}(X_b,X_a) → ⋯ → H_0(X_c,X_b) → 0`,
  exact at every node.

Nothing else is assumed: no functoriality, no compatibility of the sequences of different
triples, no vanishing of `H_*(X_a, X_a)`.  Values `H i a b` with `a ≰ b` are never used. -/
structure FiltrationHomology (F : Type*) [Field F] (ι : Type*) [Preorder ι]
    (H : ℕ → ι → ι → Type*) [∀ i a b, AddCommGroup (H i a b)] [∀ i a b, Module F (H i a b)] where
  /-- `H_i(X_b, X_a; F)` is finite-dimensional for `a ≤ b`. -/
  finiteDimensional : ∀ (i : ℕ) ⦃a b : ι⦄, a ≤ b → FiniteDimensional F (H i a b)
  /-- The exact homology sequence of the triple `X_c ⊇ X_b ⊇ X_a`. -/
  les : ∀ ⦃a b c : ι⦄, a ≤ b → b ≤ c →
    LongExactSeq F (fun i ↦ H i a b) (fun i ↦ H i a c) (fun i ↦ H i b c)

section MorseNumber

variable (F : Type*) [Field F] {ι : Type*} (H : ℕ → ι → ι → Type*)
  [∀ i a b, AddCommGroup (H i a b)] [∀ i a b, Module F (H i a b)]

/-- The **Morse numbers** of a chain `X_0 ≤ X_1 ≤ ⋯ ≤ X_n`:
`C_i = Σ_{k<n} dim H_i(X_{k+1}, X_k)`.  For Milnor's chain `X_k = M^{a_k}` the slab computation
of p. 29 makes `C_i` the number of critical points of index `i`
(`Morse.morseNumber_eq_card`); Milnor writes `C_λ` for that number. -/
def morseNumber (X : ℕ → ι) (n i : ℕ) : ℕ :=
  ∑ k ∈ range n, finrank F (H i (X k) (X (k + 1)))

end MorseNumber

namespace FiltrationHomology

variable {F : Type*} [Field F] {ι : Type*} [Preorder ι] {H : ℕ → ι → ι → Type*}
  [∀ i a b, AddCommGroup (H i a b)] [∀ i a b, Module F (H i a b)]
  (h : FiltrationHomology F ι H)
include h

/-- **`R_λ` is subadditive** (Milnor p. 28): `R_λ(X,Z) ≤ R_λ(X,Y) + R_λ(Y,Z)`. -/
theorem isSubadditive_finrank (l : ℕ) : IsSubadditive fun a b ↦ (finrank F (H l a b) : ℤ) := by
  intro a b c hab hbc
  have := fun i ↦ h.finiteDimensional i hab
  have := fun i ↦ h.finiteDimensional i hbc
  have := fun i ↦ h.finiteDimensional i (hab.trans hbc)
  have := (h.les hab hbc).finrank_le l
  dsimp only at this ⊢
  exact_mod_cast this

/-- **Lemma 5.3** (Milnor pp. 29–30): `S_λ = R_λ - R_{λ-1} + ⋯ ± R_0` is subadditive. -/
theorem isSubadditive_altSum (l : ℕ) :
    IsSubadditive fun a b ↦ altSum (fun i ↦ (finrank F (H i a b) : ℤ)) l := by
  intro a b c hab hbc
  have := fun i ↦ h.finiteDimensional i hab
  have := fun i ↦ h.finiteDimensional i hbc
  have := fun i ↦ h.finiteDimensional i (hab.trans hbc)
  have := (h.les hab hbc).altSum_le l
  dsimp only at this ⊢
  linarith

/-- **The Euler characteristic is additive** (Milnor p. 28).  Here `χ` is truncated at degree
`N`, `χ_N(X_b, X_a) = Σ_{i ≤ N} (-1)^i R_i(X_b, X_a)`, and the hypothesis is that homology
vanishes in degree `N + 1` (if it vanishes in all degrees `> N`, `χ_N` is Milnor's `χ`). -/
theorem isAdditive_eulerChar {N : ℕ} (hN : ∀ ⦃a b : ι⦄, a ≤ b → finrank F (H (N + 1) a b) = 0) :
    IsAdditive fun a b ↦ ∑ i ∈ range (N + 1), (-1) ^ i * (finrank F (H i a b) : ℤ) := by
  intro a b c hab hbc
  have := fun i ↦ h.finiteDimensional i hab
  have := fun i ↦ h.finiteDimensional i hbc
  have := fun i ↦ h.finiteDimensional i (hab.trans hbc)
  have := (h.les hab hbc).altSum_eq_of_finrank_eq_zero (hN hbc)
  dsimp only at this ⊢
  rw [sum_neg_one_pow_mul_eq, sum_neg_one_pow_mul_eq, sum_neg_one_pow_mul_eq, this]
  ring

variable {X : ℕ → ι} {n : ℕ}

/-- **Theorem 5.2 (2), the weak Morse inequalities, for any filtration** (Milnor p. 29):
`R_λ(X_n, X_0) ≤ C_λ = Σ_{k<n} R_λ(X_{k+1}, X_k)`. -/
theorem finrank_le_morseNumber (hX : ∀ k < n, X k ≤ X (k + 1)) (hn : 0 < n) (l : ℕ) :
    finrank F (H l (X 0) (X n)) ≤ morseNumber F H X n l := by
  have := (h.isSubadditive_finrank l).le_sum hX hn
  unfold morseNumber
  exact_mod_cast this

/-- **The Morse inequalities `(4_λ)`, for any filtration** (Milnor p. 30):
`R_λ - R_{λ-1} + ⋯ ± R_0 ≤ C_λ - C_{λ-1} + ⋯ ± C_0`, where `R_i = dim H_i(X_n, X_0)` and
`C_i = Σ_{k<n} dim H_i(X_{k+1}, X_k)`.  Lemma 5.1 applied to `S_λ` (Lemma 5.3), and the
linearity of the alternating sum. -/
theorem altSum_le_morseNumber (hX : ∀ k < n, X k ≤ X (k + 1)) (hn : 0 < n) (l : ℕ) :
    altSum (fun i ↦ (finrank F (H i (X 0) (X n)) : ℤ)) l ≤
      altSum (fun i ↦ (morseNumber F H X n i : ℤ)) l := by
  have := (h.isSubadditive_altSum l).le_sum hX hn
  simp only [morseNumber, Nat.cast_sum, altSum_sum]
  exact this

/-- **Theorem 5.2 (3), for any filtration** (Milnor p. 29): if the slabs have no homology in
degree `N + 1`, then `Σ_{i ≤ N} (-1)^i R_i(X_n, X_0) = Σ_{i ≤ N} (-1)^i C_i`.  Milnor's proof:
Lemma 5.1 (equality case) for the additive function `χ`. -/
theorem sum_neg_one_pow_finrank_eq (hX : ∀ k < n, X k ≤ X (k + 1)) (hn : 0 < n) {N : ℕ}
    (hN : ∀ k < n, finrank F (H (N + 1) (X k) (X (k + 1))) = 0) :
    ∑ i ∈ range (N + 1), (-1) ^ i * (finrank F (H i (X 0) (X n)) : ℤ) =
      ∑ i ∈ range (N + 1), (-1) ^ i * (morseNumber F H X n i : ℤ) := by
  have hadd : ∀ m, 0 < m → m < n →
      ∑ i ∈ range (N + 1), (-1) ^ i * (finrank F (H i (X 0) (X (m + 1))) : ℤ) =
        ∑ i ∈ range (N + 1), (-1) ^ i * (finrank F (H i (X 0) (X m)) : ℤ) +
          ∑ i ∈ range (N + 1), (-1) ^ i * (finrank F (H i (X m) (X (m + 1))) : ℤ) := by
    intro m _ hmn
    have hab := chain_le hX (Nat.zero_le m) hmn.le
    have hbc := hX m hmn
    have := fun i ↦ h.finiteDimensional i hab
    have := fun i ↦ h.finiteDimensional i hbc
    have := fun i ↦ h.finiteDimensional i (hab.trans hbc)
    have := (h.les hab hbc).altSum_eq_of_finrank_eq_zero (hN m hmn)
    rw [sum_neg_one_pow_mul_eq, sum_neg_one_pow_mul_eq, sum_neg_one_pow_mul_eq, this]
    ring
  rw [eq_sum_of_chain (fun a b ↦ ∑ i ∈ range (N + 1), (-1) ^ i * (finrank F (H i a b) : ℤ))
    X hn hadd, sum_comm]
  simp only [morseNumber, Nat.cast_sum, mul_sum]

end FiltrationHomology

/-! ## Numerical consequences of the Morse inequalities (Milnor pp. 30–31)

Throughout, `b c : ℕ → ℤ` satisfy `(4_λ)` for every `λ`: `altSum b λ ≤ altSum c λ`.  For a
filtration, `b i = dim H_i(X_n, X_0)` and `c i` is the Morse number `C_i`
(`Morse.FiltrationHomology.altSum_le_morseNumber`). -/

section Numerical

variable {b c : ℕ → ℤ}

/-- **The strong inequalities imply the weak ones** (Milnor p. 30): adding `(4_λ)` and
`(4_{λ-1})` gives `(2_λ)`, `b λ ≤ c λ` (for `λ = 0`, `(4_0)` is `(2_0)`). -/
theorem le_of_altSum_le (hbc : ∀ l, altSum b l ≤ altSum c l) (l : ℕ) : b l ≤ c l := by
  cases l with
  | zero => simpa using hbc 0
  | succ l =>
    have h₁ := hbc (l + 1)
    have h₀ := hbc l
    have e₁ := altSum_succ_add_altSum b l
    have e₂ := altSum_succ_add_altSum c l
    linarith

/-- **Milnor p. 30**: if `C_{λ+1} = 0`, then `(4_λ)` and `(4_{λ+1})` together make `(4_λ)` an
equality, `R_λ - R_{λ-1} + ⋯ ± R_0 = C_λ - C_{λ-1} + ⋯ ± C_0`.  (Milnor first deduces
`R_{λ+1} = 0`; only `R_{λ+1} ≥ 0` is needed.) -/
theorem altSum_eq_of_altSum_le (hbc : ∀ l, altSum b l ≤ altSum c l) {l : ℕ}
    (hb : 0 ≤ b (l + 1)) (hc : c (l + 1) = 0) : altSum b l = altSum c l := by
  have h₁ := hbc (l + 1)
  have h₀ := hbc l
  rw [altSum_succ, altSum_succ, hc] at h₁
  linarith

/-- **Theorem 5.2 (3) from the strong inequalities** (Milnor p. 30, where `(4_λ)` and
`(4_{λ-1})` are compared for `λ > n`): if `C_{N+1} = 0` then
`Σ_{i ≤ N} (-1)^i R_i = Σ_{i ≤ N} (-1)^i C_i`.  Only `R_{N+1} ≥ 0` is used, not
`R_{N+1} = 0`.  (For a manifold of dimension `n` take `N = n`; that `R_i = 0` for `i > n`, so
that the left side is the whole alternating sum, is (2).) -/
theorem sum_neg_one_pow_eq_of_altSum_le (hb : ∀ i, 0 ≤ b i) (hbc : ∀ l, altSum b l ≤ altSum c l)
    {N : ℕ} (hc : c (N + 1) = 0) :
    ∑ i ∈ range (N + 1), (-1) ^ i * b i = ∑ i ∈ range (N + 1), (-1) ^ i * c i := by
  rw [sum_neg_one_pow_mul_eq, sum_neg_one_pow_mul_eq, altSum_eq_of_altSum_le hbc (hb _) hc]

/-- **Corollary 5.4** (Milnor p. 31), for `λ = l + 1 ≥ 1`: if `C_{λ+1} = C_{λ-1} = 0` then
`R_λ = C_λ` and `R_{λ+1} = R_{λ-1} = 0`. -/
theorem eq_of_altSum_le_succ (hb : ∀ i, 0 ≤ b i) (hbc : ∀ l, altSum b l ≤ altSum c l) {l : ℕ}
    (hc₂ : c (l + 2) = 0) (hc₀ : c l = 0) : b (l + 1) = c (l + 1) ∧ b (l + 2) = 0 ∧ b l = 0 := by
  have hb₂ : b (l + 2) = 0 := le_antisymm (hc₂ ▸ le_of_altSum_le hbc (l + 2)) (hb _)
  have hb₀ : b l = 0 := le_antisymm (hc₀ ▸ le_of_altSum_le hbc l) (hb _)
  refine ⟨?_, hb₂, hb₀⟩
  have e₁ : altSum b (l + 1) = altSum c (l + 1) := altSum_eq_of_altSum_le hbc (hb _) hc₂
  have e₀ : altSum b l = altSum c l := by
    cases l with
    | zero => simp [hb₀, hc₀]
    | succ l => rw [altSum_succ, altSum_succ, hb₀, hc₀, altSum_eq_of_altSum_le hbc (hb _) hc₀]
  have := altSum_succ_add_altSum b l
  have := altSum_succ_add_altSum c l
  linarith

/-- **Corollary 5.4** (Milnor p. 31), for `λ = 0`, where the hypothesis `C_{λ-1} = 0` is empty:
if `C_1 = 0` then `R_0 = C_0` and `R_1 = 0`. -/
theorem eq_of_altSum_le_zero (hb : ∀ i, 0 ≤ b i) (hbc : ∀ l, altSum b l ≤ altSum c l)
    (hc₁ : c 1 = 0) : b 0 = c 0 ∧ b 1 = 0 := by
  refine ⟨?_, le_antisymm (hc₁ ▸ le_of_altSum_le hbc 1) (hb 1)⟩
  simpa using altSum_eq_of_altSum_le (l := 0) hbc (hb 1) hc₁

/-- **The lacunary principle** (Milnor p. 31, the remark on `ℂPⁿ`): if no two consecutive
`C_i` are nonzero, then `R_i = C_i` for every `i`.  For `ℂPⁿ`, `C_i = 1` for even `i ≤ 2n`
and `0` otherwise (§4), so `R_i(ℂPⁿ; F) = C_i` for every field `F`. -/
theorem eq_of_altSum_le_of_lacunary (hb : ∀ i, 0 ≤ b i) (hbc : ∀ l, altSum b l ≤ altSum c l)
    (hc : ∀ i, c i = 0 ∨ c (i + 1) = 0) (i : ℕ) : b i = c i := by
  rcases eq_or_ne (c i) 0 with h | h
  · rw [h]
    exact le_antisymm (h ▸ le_of_altSum_le hbc i) (hb i)
  · have h₁ : c (i + 1) = 0 := (hc i).resolve_left h
    cases i with
    | zero => exact (eq_of_altSum_le_zero hb hbc h₁).1
    | succ l => exact (eq_of_altSum_le_succ hb hbc h₁ ((hc l).resolve_right h)).1

/-- The Morse numbers of `ℂPⁿ` (all odd ones zero) satisfy the hypothesis of the lacunary
principle. -/
theorem lacunary_of_odd (hc : ∀ i, Odd i → c i = 0) (i : ℕ) : c i = 0 ∨ c (i + 1) = 0 := by
  rcases Nat.even_or_odd i with he | ho
  · exact Or.inr (hc _ he.add_one)
  · exact Or.inl (hc _ ho)

end Numerical

namespace FiltrationHomology

variable {F : Type*} [Field F] {ι : Type*} [Preorder ι] {H : ℕ → ι → ι → Type*}
  [∀ i a b, AddCommGroup (H i a b)] [∀ i a b, Module F (H i a b)]
  (h : FiltrationHomology F ι H) {X : ℕ → ι} {n : ℕ}
include h

/-- **Corollary 5.4 for a filtration** (Milnor p. 31), `λ = l + 1 ≥ 1`: if `C_{λ+1} = 0` and
`C_{λ-1} = 0`, then `R_λ = C_λ` and `R_{λ+1} = R_{λ-1} = 0`, where `R_i = dim H_i(X_n, X_0)`
and `C_i` are the Morse numbers. -/
theorem finrank_eq_morseNumber_of_succ (hX : ∀ k < n, X k ≤ X (k + 1)) (hn : 0 < n) {l : ℕ}
    (hc₂ : morseNumber F H X n (l + 2) = 0) (hc₀ : morseNumber F H X n l = 0) :
    finrank F (H (l + 1) (X 0) (X n)) = morseNumber F H X n (l + 1) ∧
      finrank F (H (l + 2) (X 0) (X n)) = 0 ∧ finrank F (H l (X 0) (X n)) = 0 := by
  have := eq_of_altSum_le_succ (b := fun i ↦ (finrank F (H i (X 0) (X n)) : ℤ))
    (c := fun i ↦ (morseNumber F H X n i : ℤ)) (fun _ ↦ Nat.cast_nonneg _)
    (h.altSum_le_morseNumber hX hn) (l := l) (by simp [hc₂]) (by simp [hc₀])
  exact_mod_cast this

/-- **Corollary 5.4 for a filtration** (Milnor p. 31), `λ = 0`: if `C_1 = 0`, then `R_0 = C_0`
and `R_1 = 0`. -/
theorem finrank_eq_morseNumber_of_zero (hX : ∀ k < n, X k ≤ X (k + 1)) (hn : 0 < n)
    (hc₁ : morseNumber F H X n 1 = 0) :
    finrank F (H 0 (X 0) (X n)) = morseNumber F H X n 0 ∧ finrank F (H 1 (X 0) (X n)) = 0 := by
  have := eq_of_altSum_le_zero (b := fun i ↦ (finrank F (H i (X 0) (X n)) : ℤ))
    (c := fun i ↦ (morseNumber F H X n i : ℤ)) (fun _ ↦ Nat.cast_nonneg _)
    (h.altSum_le_morseNumber hX hn) (by simp [hc₁])
  exact_mod_cast this

/-- **The lacunary principle for a filtration** (Milnor p. 31, the remark on `ℂPⁿ`): if no two
consecutive Morse numbers are nonzero, the Betti numbers of `(X_n, X_0)` are the Morse
numbers. -/
theorem finrank_eq_morseNumber_of_lacunary (hX : ∀ k < n, X k ≤ X (k + 1)) (hn : 0 < n)
    (hc : ∀ i, morseNumber F H X n i = 0 ∨ morseNumber F H X n (i + 1) = 0) (i : ℕ) :
    finrank F (H i (X 0) (X n)) = morseNumber F H X n i := by
  have := eq_of_altSum_le_of_lacunary (b := fun i ↦ (finrank F (H i (X 0) (X n)) : ℤ))
    (c := fun i ↦ (morseNumber F H X n i : ℤ)) (fun _ ↦ Nat.cast_nonneg _)
    (h.altSum_le_morseNumber hX hn) (fun i ↦ by exact_mod_cast hc i) i
  exact_mod_cast this

end FiltrationHomology

/-! ## Finiteness along a chain -/

section Finiteness

variable {F : Type*} [Field F] {H : ℕ → ℕ → ℕ → Type*}
  [∀ i a b, AddCommGroup (H i a b)] [∀ i a b, Module F (H i a b)]

/-- **Finiteness propagates along a chain.**  For a filtration indexed by `ℕ` with exact
sequences of triples, if every slab `H_i(X_{k+1}, X_k)` and every `H_i(X_k, X_k)` is
finite-dimensional, then so is every `H_i(X_b, X_a)`, `a ≤ b`.  (In singular homology
`H_*(X_k, X_k) = 0`.)  Milnor's `R_λ(M)` is finite because of this. -/
theorem finiteDimensional_of_steps
    (les : ∀ ⦃a b c : ℕ⦄, a ≤ b → b ≤ c →
      LongExactSeq F (fun i ↦ H i a b) (fun i ↦ H i a c) (fun i ↦ H i b c))
    (hstep : ∀ i k, FiniteDimensional F (H i k (k + 1)))
    (hdiag : ∀ i k, FiniteDimensional F (H i k k)) :
    ∀ (i : ℕ) ⦃a b : ℕ⦄, a ≤ b → FiniteDimensional F (H i a b) := by
  intro i a b hab
  induction b, hab using Nat.le_induction generalizing i with
  | base => exact hdiag i a
  | succ b hab ih =>
    have := fun j ↦ ih j
    have := fun j ↦ hstep j b
    exact (les hab (Nat.le_succ b)).finiteDimensional_middle i

/-- A `Morse.FiltrationHomology` on a chain indexed by `ℕ`, from the exact sequences of triples
and the finiteness of the slabs (and of the `H_*(X_k, X_k)`, which vanish in singular
homology). -/
def FiltrationHomology.ofSteps
    (les : ∀ ⦃a b c : ℕ⦄, a ≤ b → b ≤ c →
      LongExactSeq F (fun i ↦ H i a b) (fun i ↦ H i a c) (fun i ↦ H i b c))
    (hstep : ∀ i k, FiniteDimensional F (H i k (k + 1)))
    (hdiag : ∀ i k, FiniteDimensional F (H i k k)) : FiltrationHomology F ℕ H where
  finiteDimensional := finiteDimensional_of_steps les hstep hdiag
  les := les

end Finiteness

/-! ## The Morse inequalities in terms of critical points -/

section Cells

variable {F : Type*} [Field F] {ι : Type*} {H : ℕ → ι → ι → Type*}
  [∀ i a b, AddCommGroup (H i a b)] [∀ i a b, Module F (H i a b)]
  {X : ℕ → ι} {n : ℕ} {α : Type*} {P : Finset α} {step ind : α → ℕ}

/-- **The Morse numbers count critical points** (Milnor p. 29).  Suppose each critical point
`p ∈ P` lies in the slab `step p < n` and has index `ind p`, and the slab homology is that of
the attached cells: `dim H_i(X_{k+1}, X_k) = #{p ∈ P | step p = k ∧ ind p = i}`.  Then
`C_i = #{p ∈ P | ind p = i}`, the number of critical points of index `i`. -/
theorem morseNumber_eq_card (hstep : ∀ p ∈ P, step p < n)
    (hcells : ∀ k < n, ∀ i, finrank F (H i (X k) (X (k + 1))) =
      #{p ∈ P | step p = k ∧ ind p = i}) (i : ℕ) :
    morseNumber F H X n i = #{p ∈ P | ind p = i} := by
  have hmaps : Set.MapsTo step ↑({p ∈ P | ind p = i} : Finset α) ↑(range n) := by
    intro p hp
    rw [mem_coe, mem_filter] at hp
    exact mem_coe.mpr (mem_range.mpr (hstep p hp.1))
  rw [morseNumber, sum_congr rfl fun k hk ↦ hcells k (mem_range.mp hk) i,
    card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun k _ ↦ congrArg card ?_
  ext p
  simp only [mem_filter]
  tauto

/-- **One critical point per slab**, as in Milnor's choice of the `a_i` (p. 29): if
`H_*(X_{k+1}, X_k)` is one-dimensional in degree `idx k` and zero otherwise ("step `k` attaches
one `idx k`-cell"), then `C_i = #{k < n | idx k = i}`. -/
theorem morseNumber_eq_card_of_single {idx : ℕ → ℕ}
    (hcells : ∀ k < n, ∀ i, finrank F (H i (X k) (X (k + 1))) = if idx k = i then 1 else 0)
    (i : ℕ) : morseNumber F H X n i = #{k ∈ range n | idx k = i} := by
  rw [morseNumber, sum_congr rfl fun k hk ↦ hcells k (mem_range.mp hk) i, card_filter]

variable [Preorder ι] (h : FiltrationHomology F ι H)
include h

/-- **Theorem 5.2 (2), the weak Morse inequalities** (Milnor p. 29): `R_λ ≤ C_λ`, where
`R_λ = dim H_λ(X_n, X_0)` and `C_λ` is the number of critical points of index `λ`. -/
theorem FiltrationHomology.weak_morse_inequality (hX : ∀ k < n, X k ≤ X (k + 1)) (hn : 0 < n)
    (hstep : ∀ p ∈ P, step p < n)
    (hcells : ∀ k < n, ∀ i, finrank F (H i (X k) (X (k + 1))) =
      #{p ∈ P | step p = k ∧ ind p = i}) (l : ℕ) :
    finrank F (H l (X 0) (X n)) ≤ #{p ∈ P | ind p = l} :=
  morseNumber_eq_card hstep hcells l ▸ h.finrank_le_morseNumber hX hn l

/-- **The Morse inequalities `(4_λ)`** (Milnor p. 30):
`R_λ - R_{λ-1} + ⋯ ± R_0 ≤ C_λ - C_{λ-1} + ⋯ ± C_0`, where `R_i = dim H_i(X_n, X_0)` and
`C_i` is the number of critical points of index `i`. -/
theorem FiltrationHomology.morse_inequality (hX : ∀ k < n, X k ≤ X (k + 1)) (hn : 0 < n)
    (hstep : ∀ p ∈ P, step p < n)
    (hcells : ∀ k < n, ∀ i, finrank F (H i (X k) (X (k + 1))) =
      #{p ∈ P | step p = k ∧ ind p = i}) (l : ℕ) :
    altSum (fun i ↦ (finrank F (H i (X 0) (X n)) : ℤ)) l ≤
      altSum (fun i ↦ (#{p ∈ P | ind p = i} : ℤ)) l := by
  simpa only [morseNumber_eq_card hstep hcells] using h.altSum_le_morseNumber hX hn l

/-- No homology above the largest index: if no critical point has index `l`, then
`H_l(X_n, X_0) = 0` (by the weak inequality). -/
theorem FiltrationHomology.finrank_eq_zero_of_forall_ne (hX : ∀ k < n, X k ≤ X (k + 1))
    (hn : 0 < n) (hstep : ∀ p ∈ P, step p < n)
    (hcells : ∀ k < n, ∀ i, finrank F (H i (X k) (X (k + 1))) =
      #{p ∈ P | step p = k ∧ ind p = i}) {l : ℕ} (hl : ∀ p ∈ P, ind p ≠ l) :
    finrank F (H l (X 0) (X n)) = 0 := by
  have := h.weak_morse_inequality hX hn hstep hcells l
  rw [card_eq_zero.mpr (filter_eq_empty_iff.mpr hl)] at this
  omega

/-- **Theorem 5.2 (3)** (Milnor p. 29): if every critical point has index `≤ N`, then
`Σ_{i ≤ N} (-1)^i R_i = Σ_{p ∈ P} (-1)^{ind p}`, where `R_i = dim H_i(X_n, X_0)`.  The left
side is the whole Euler characteristic of `(X_n, X_0)`: `R_i = 0` for `i > N`
(`Morse.FiltrationHomology.finrank_eq_zero_of_forall_ne`). -/
theorem FiltrationHomology.euler_characteristic_eq (hX : ∀ k < n, X k ≤ X (k + 1)) (hn : 0 < n)
    (hstep : ∀ p ∈ P, step p < n)
    (hcells : ∀ k < n, ∀ i, finrank F (H i (X k) (X (k + 1))) =
      #{p ∈ P | step p = k ∧ ind p = i}) {N : ℕ} (hN : ∀ p ∈ P, ind p ≤ N) :
    ∑ i ∈ range (N + 1), (-1) ^ i * (finrank F (H i (X 0) (X n)) : ℤ) =
      ∑ p ∈ P, (-1) ^ ind p := by
  have hvan : ∀ k < n, finrank F (H (N + 1) (X k) (X (k + 1))) = 0 := by
    intro k hk
    rw [hcells k hk, card_eq_zero, filter_eq_empty_iff]
    rintro p hp ⟨-, hi⟩
    have := hN p hp
    omega
  rw [h.sum_neg_one_pow_finrank_eq hX hn hvan]
  simp only [morseNumber_eq_card hstep hcells]
  rw [← sum_fiberwise_of_maps_to (g := ind) (t := range (N + 1))
    (fun p hp ↦ mem_range.mpr (Nat.lt_succ_of_le (hN p hp)))]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_congr rfl fun p hp ↦ by rw [(mem_filter.mp hp).2], sum_const, nsmul_eq_mul, mul_comm]

end Cells

section Example

variable {F : Type*} [Field F] {H : ℕ → ℕ → ℕ → Type*}
  [∀ i a b, AddCommGroup (H i a b)] [∀ i a b, Module F (H i a b)]

/-- Milnor's own setting (p. 29), for a filtration indexed by `ℕ` itself (`X = id`), with one
critical point, of index `idx k`, in the `k`-th slab: the Morse inequalities `(4_λ)` with
`C_i = #{k < n | idx k = i}`. -/
example (h : FiltrationHomology F ℕ H) {n : ℕ} (hn : 0 < n) {idx : ℕ → ℕ}
    (hcells : ∀ k < n, ∀ i, finrank F (H i k (k + 1)) = if idx k = i then 1 else 0) (l : ℕ) :
    altSum (fun i ↦ (finrank F (H i 0 n) : ℤ)) l ≤
      altSum (fun i ↦ (#{k ∈ range n | idx k = i} : ℤ)) l := by
  simpa only [morseNumber_eq_card_of_single (X := id) hcells, id_eq] using
    h.altSum_le_morseNumber (X := id) (fun k _ ↦ Nat.le_succ k) hn l

end Example

end Morse
