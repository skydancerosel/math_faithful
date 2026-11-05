import Morse.Homology.Triple
import Morse.Chapter3.Inequalities
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The Morse inequalities for singular homology

`Morse/Chapter3/Inequalities.lean` proves Milnor's algebra of the Morse inequalities (§5) for an
abstract `Morse.FiltrationHomology`: finite-dimensional groups `H i a b = H_i(X_b, X_a)` for
`a ≤ b` and, for every triple `a ≤ b ≤ c`, the exact sequence of the triple as a
`Morse.LongExactSeq`.  This file provides the instance with singular homology over a field `𝕜`.

## Contents

* `Morse.Homology.TopTriple.longExactSeq`: the long exact sequence of any triple of spaces, with
  coefficients in `𝕜`, as a `Morse.LongExactSeq` (categorical exactness in `ModuleCat 𝕜` becomes
  `Function.Exact`).
* `Morse.Homology.subsetHomology 𝕜 i h = H_i(B, A; 𝕜)` for subsets `A ⊆ B` (`h : A ⊆ B`) of a
  space `E`, and `Morse.Homology.subsetTripleLongExactSeq`, the sequence of a triple of subsets.
* `Morse.Homology.filtrationHomology`: for a monotone sequence `X : ℕ → Set E` of subsets whose
  steps `(X_{k+1}, X_k)` have finite-dimensional homology, the `Morse.FiltrationHomology` with
  `H i a b = H_i(X_{max a b}, X_a; 𝕜)` (`Morse.Homology.filtrationGroup`); for `a ≤ b` this is
  `H_i(X_b, X_a; 𝕜)` (`Morse.Homology.finrank_filtrationGroup`).  All results of
  `Morse/Chapter3/Inequalities.lean` therefore hold for singular homology.
  `Morse.Homology.truncatedFiltrationHomology` is the same for the filtration `k ↦ X_{min k n}`,
  which only needs the steps `k < n` to be finite-dimensional.
* For a monotone `X` and `n > 0`, with finite-dimensional step homology for `k < n` only:
  `Morse.Homology.finiteDimensional_subsetHomology_of_steps` (`H_i(X_n, X_0; 𝕜)` is
  finite-dimensional), `Morse.Homology.singular_weak_morse_inequality` (`b_l ≤ C_l`),
  `Morse.Homology.singular_morse_inequality` (the strong inequalities `(4_l)`) and
  `Morse.Homology.singular_euler_characteristic` (`Σ (-1)^i b_i = Σ (-1)^i C_i` when the steps
  have no homology in degree `N + 1`), where `b_i = dim H_i(X_n, X_0; 𝕜)` and
  `C_i = Σ_{k<n} dim H_i(X_{k+1}, X_k; 𝕜)` (`Morse.Homology.singularMorseNumber`).
* In terms of critical points, when the step `k` has the homology of the cells attached at the
  critical points of the `k`-th slab (the hypothesis `hcells`, Milnor p. 29):
  `Morse.Homology.singularMorseNumber_eq_card` (`C_i` is the number of critical points of index
  `i`), `Morse.Homology.singular_weak_morse_inequality_of_cells`,
  `Morse.Homology.singular_morse_inequality_of_cells` and
  `Morse.Homology.singular_euler_characteristic_of_cells` (Theorem 5.2 and `(4_λ)`).

## Indexing

`Morse.FiltrationHomology` needs `H i a b` for all `a b : ℕ`, but only uses it for `a ≤ b`.  The
choice `H i a b = H_i(X_{max a b}, X_a)` makes the pair a pair of subsets for all `a, b`; for
`a ≤ b`, `max a b = b` only propositionally, so the exact sequences of triples are transported
along equalities of subsets (`Morse.Homology.subsetTripleLongExactSeq'`).  The final theorems are
stated with the honest pairs `(X_n, X_0)` and `(X_{k+1}, X_k)`; they only assume finiteness of the
steps `k < n`, by applying the general construction to the filtration `k ↦ X_{min k n}`, which is
constant from `n` on.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Module Finset

universe u

namespace Morse.Homology

variable (𝕜 : Type u) [Field 𝕜]

/-! ### The exact sequence of a triple as a `Morse.LongExactSeq` -/

namespace TopTriple

variable (T : TopTriple.{u})

/-- **The long exact sequence of a triple** `Z ⊆ Y ⊆ X` in singular homology with coefficients in
a field `𝕜`, as a `Morse.LongExactSeq`: `A i = H_i(Y, Z)`, `B i = H_i(X, Z)`, `C i = H_i(X, Y)`. -/
def longExactSeq :
    LongExactSeq 𝕜 (fun i ↦ (relHomology (ModuleCat.of 𝕜 𝕜) i).obj T.pairYZ)
      (fun i ↦ (relHomology (ModuleCat.of 𝕜 𝕜) i).obj T.pairXZ)
      (fun i ↦ (relHomology (ModuleCat.of 𝕜 𝕜) i).obj T.pairXY) where
  f i := ((relHomology (ModuleCat.of 𝕜 𝕜) i).map T.map₁).hom
  g i := ((relHomology (ModuleCat.of 𝕜 𝕜) i).map T.map₂).hom
  δ i := (T.δ (ModuleCat.of 𝕜 𝕜) i).hom
  exact_f_g i := by
    have h := T.exact₂ (ModuleCat.of 𝕜 𝕜) i
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h
  exact_g_δ i := by
    have h := T.exact₃ (ModuleCat.of 𝕜 𝕜) i
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h
  exact_δ_f i := by
    have h := T.exact₁ (ModuleCat.of 𝕜 𝕜) i
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h
  surjective_g_zero := by
    have h := T.epi_map₂_zero (ModuleCat.of 𝕜 𝕜)
    exact (ModuleCat.epi_iff_surjective _).1 h

end TopTriple

/-! ### Pairs and triples of subsets -/

section Subsets

variable {E : Type u} [TopologicalSpace E]

/-- The singular homology `H_i(B, A; 𝕜)` of a pair of subsets `A ⊆ B` of a space, with
coefficients in a field `𝕜`. -/
abbrev subsetHomology (i : ℕ) {A B : Set E} (h : A ⊆ B) : ModuleCat.{u} 𝕜 :=
  (relHomology (ModuleCat.of 𝕜 𝕜) i).obj (subsetPair h)

variable {𝕜}

/-- The homology of a pair of subsets only depends on the subsets. -/
lemma finrank_subsetHomology_congr {A B A' B' : Set E} (h : A ⊆ B) (h' : A' ⊆ B') (hA : A = A')
    (hB : B = B') (i : ℕ) :
    finrank 𝕜 (subsetHomology 𝕜 i h) = finrank 𝕜 (subsetHomology 𝕜 i h') := by
  subst hA hB
  rfl

lemma finiteDimensional_subsetHomology_congr {A B A' B' : Set E} (h : A ⊆ B) (h' : A' ⊆ B')
    (hA : A = A') (hB : B = B') (i : ℕ) [FiniteDimensional 𝕜 (subsetHomology 𝕜 i h)] :
    FiniteDimensional 𝕜 (subsetHomology 𝕜 i h') := by
  subst hA hB
  assumption

/-- `H_i(A, A) = 0`. -/
lemma subsingleton_subsetHomology_self (i : ℕ) (A : Set E) :
    Subsingleton (subsetHomology 𝕜 i (subset_refl A)) :=
  (ModuleCat.isZero_iff_subsingleton).1 (isZero_relHomology_of_isIso _ _ i)

variable (𝕜)

/-- The long exact sequence of a triple of subsets `A ⊆ B ⊆ D`:
`⋯ → H_i(B, A) → H_i(D, A) → H_i(D, B) → H_{i-1}(B, A) → ⋯ → H_0(D, B) → 0`. -/
def subsetTripleLongExactSeq {A B D : Set E} (hAB : A ⊆ B) (hBD : B ⊆ D) :
    LongExactSeq 𝕜 (fun i ↦ subsetHomology 𝕜 i hAB) (fun i ↦ subsetHomology 𝕜 i (hAB.trans hBD))
      (fun i ↦ subsetHomology 𝕜 i hBD) :=
  (TopTriple.ofSubsets hAB hBD).longExactSeq 𝕜

/-- The long exact sequence of a triple of subsets `A ⊆ B ⊆ D`, with the pair `(D, B)` replaced
by an equal pair `(D', B')`. -/
def subsetTripleLongExactSeq' {A B D B' D' : Set E} (hAB : A ⊆ B) (hBD : B ⊆ D)
    (hB'D' : B' ⊆ D') (hB : B' = B) (hD : D' = D) :
    LongExactSeq 𝕜 (fun i ↦ subsetHomology 𝕜 i hAB) (fun i ↦ subsetHomology 𝕜 i (hAB.trans hBD))
      (fun i ↦ subsetHomology 𝕜 i hB'D') := by
  subst hB hD
  exact subsetTripleLongExactSeq 𝕜 hAB hBD

end Subsets

/-! ### The homology of a filtration -/

section Filtration

variable {E : Type u} [TopologicalSpace E] {X : ℕ → Set E} (hX : Monotone X)

/-- The groups `H_i(X_{max a b}, X_a; 𝕜)` of a monotone filtration (for `a ≤ b`, this is
`H_i(X_b, X_a; 𝕜)`). -/
abbrev filtrationGroup (i a b : ℕ) : ModuleCat.{u} 𝕜 :=
  subsetHomology 𝕜 i (hX (le_max_left a b))

/-- **The singular homology of a filtration** `X_0 ⊆ X_1 ⊆ ⋯` of subsets of `E`, over a field
`𝕜`, as a `Morse.FiltrationHomology`, assuming that every step `(X_{k+1}, X_k)` has
finite-dimensional homology.  Finite-dimensionality of all pairs `(X_b, X_a)` follows
(`Morse.FiltrationHomology.ofSteps`). -/
def filtrationHomology
    (hstep : ∀ i k, FiniteDimensional 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k)))) :
    FiltrationHomology 𝕜 ℕ (fun i a b ↦ filtrationGroup 𝕜 hX i a b) :=
  FiltrationHomology.ofSteps
    (fun a b c hab hbc ↦ subsetTripleLongExactSeq' 𝕜 (hX (le_max_left a b))
      (hX (max_le_max_left a hbc)) (hX (le_max_left b c))
      (congrArg X (max_eq_right hab).symm)
      (congrArg X ((max_eq_right hbc).trans (max_eq_right (hab.trans hbc)).symm)))
    (fun i k ↦ by
      have := hstep i k
      exact finiteDimensional_subsetHomology_congr _ _ rfl
        (congrArg X (max_eq_right (Nat.le_succ k)).symm) i)
    (fun i k ↦ by
      have := subsingleton_subsetHomology_self (𝕜 := 𝕜) i (X k)
      exact finiteDimensional_subsetHomology_congr (subset_refl (X k)) _ rfl
        (congrArg X (max_self k).symm) i)

/-- For `a ≤ b`, the group `H i a b` of `Morse.Homology.filtrationHomology` is
`H_i(X_b, X_a; 𝕜)`. -/
lemma finrank_filtrationGroup {i a b : ℕ} (hab : a ≤ b) :
    finrank 𝕜 (filtrationGroup 𝕜 hX i a b) = finrank 𝕜 (subsetHomology 𝕜 i (hX hab)) :=
  finrank_subsetHomology_congr _ _ rfl (congrArg X (max_eq_right hab)) i

/-- The `i`-th **Morse number** of the filtration up to `n`:
`C_i = Σ_{k < n} dim H_i(X_{k+1}, X_k; 𝕜)`. -/
def singularMorseNumber (n i : ℕ) : ℕ :=
  ∑ k ∈ range n, finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k)))

omit [TopologicalSpace E] in
include hX in
/-- The filtration `k ↦ X_{min k n}`, constant from `n` on. -/
lemma monotone_truncate (n : ℕ) : Monotone fun k ↦ X (min k n) :=
  fun _ _ h ↦ hX (min_le_min_right n h)

/-- The steps of the truncated filtration `k ↦ X_{min k n}` have finite-dimensional homology if
the steps `k < n` of `X` do. -/
lemma finiteDimensional_truncate_step {n : ℕ}
    (hfin : ∀ k < n, ∀ i, FiniteDimensional 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k))))
    (i k : ℕ) :
    FiniteDimensional 𝕜 (subsetHomology 𝕜 i (monotone_truncate hX n (Nat.le_succ k))) := by
  rcases lt_or_ge k n with hk | hk
  · have := hfin k hk i
    exact finiteDimensional_subsetHomology_congr _ _ (congrArg X (min_eq_left hk.le).symm)
      (congrArg X (min_eq_left (Nat.succ_le_of_lt hk)).symm) i
  · have := subsingleton_subsetHomology_self (𝕜 := 𝕜) i (X n)
    exact finiteDimensional_subsetHomology_congr (subset_refl (X n)) _
      (congrArg X (min_eq_right hk).symm)
      (congrArg X (min_eq_right (hk.trans (Nat.le_succ k))).symm) i

/-- The truncated filtration has the same Betti numbers `dim H_i(X_n, X_0)`. -/
lemma finrank_truncate_total (n i : ℕ) :
    finrank 𝕜 (filtrationGroup 𝕜 (monotone_truncate hX n) i 0 n) =
      finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.zero_le n))) :=
  finrank_subsetHomology_congr (monotone_truncate hX n (le_max_left 0 n)) (hX (Nat.zero_le n))
    (congrArg X (by omega)) (congrArg X (by omega)) i

/-- The truncated filtration has the same Morse numbers. -/
lemma morseNumber_truncate (n i : ℕ) :
    morseNumber 𝕜 (fun i a b ↦ filtrationGroup 𝕜 (monotone_truncate hX n) i a b) id n i =
      singularMorseNumber 𝕜 hX n i := by
  refine sum_congr rfl fun k hk ↦ ?_
  have hk : k < n := mem_range.1 hk
  exact finrank_subsetHomology_congr _ _ (congrArg X (by simp only [id_eq]; omega))
    (congrArg X (by simp only [id_eq]; omega)) i

variable {n : ℕ}
  (hfin : ∀ k < n, ∀ i, FiniteDimensional 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k))))

/-- The singular homology of the filtration `k ↦ X_{min k n}`, which is constant from `n` on, as
a `Morse.FiltrationHomology`; only the steps `k < n` of `X` need finite-dimensional homology. -/
def truncatedFiltrationHomology :
    FiltrationHomology 𝕜 ℕ (fun i a b ↦ filtrationGroup 𝕜 (monotone_truncate hX n) i a b) :=
  filtrationHomology 𝕜 (monotone_truncate hX n) (finiteDimensional_truncate_step 𝕜 hX hfin)

include hfin

/-- **Finiteness of the homology of a filtration** (Milnor p. 28): if every step
`(X_{k+1}, X_k)`, `k < n`, has finite-dimensional homology over `𝕜`, so does `(X_n, X_0)`. -/
theorem finiteDimensional_subsetHomology_of_steps (i : ℕ) :
    FiniteDimensional 𝕜 (subsetHomology 𝕜 i (hX (Nat.zero_le n))) := by
  have := (truncatedFiltrationHomology 𝕜 hX hfin).finiteDimensional i (Nat.zero_le n)
  exact finiteDimensional_subsetHomology_congr (monotone_truncate hX n (le_max_left 0 n))
    (hX (Nat.zero_le n)) (congrArg X (by omega)) (congrArg X (by omega)) i

/-- **The weak Morse inequalities for singular homology** (Milnor Theorem 5.2 (2)):
`dim H_l(X_n, X_0; 𝕜) ≤ C_l = Σ_{k<n} dim H_l(X_{k+1}, X_k; 𝕜)`. -/
theorem singular_weak_morse_inequality (hn : 0 < n) (l : ℕ) :
    finrank 𝕜 (subsetHomology 𝕜 l (hX (Nat.zero_le n))) ≤ singularMorseNumber 𝕜 hX n l := by
  have h := (truncatedFiltrationHomology 𝕜 hX hfin).finrank_le_morseNumber (X := id)
    (fun k _ ↦ Nat.le_succ k) hn l
  rw [morseNumber_truncate 𝕜 hX n] at h
  exact (finrank_truncate_total 𝕜 hX n l).symm.trans_le h

/-- **The strong Morse inequalities for singular homology** (Milnor p. 30, `(4_l)`):
`b_l - b_{l-1} + ⋯ ± b_0 ≤ C_l - C_{l-1} + ⋯ ± C_0`, where `b_i = dim H_i(X_n, X_0; 𝕜)` and
`C_i = Σ_{k<n} dim H_i(X_{k+1}, X_k; 𝕜)`. -/
theorem singular_morse_inequality (hn : 0 < n) (l : ℕ) :
    altSum (fun i ↦ (finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.zero_le n))) : ℤ)) l ≤
      altSum (fun i ↦ (singularMorseNumber 𝕜 hX n i : ℤ)) l := by
  have h := (truncatedFiltrationHomology 𝕜 hX hfin).altSum_le_morseNumber (X := id)
    (fun k _ ↦ Nat.le_succ k) hn l
  simp only [morseNumber_truncate 𝕜 hX n] at h
  rw [altSum_congr (fun i _ ↦ congrArg (Nat.cast : ℕ → ℤ) (finrank_truncate_total 𝕜 hX n i).symm)]
  exact h

/-- **The Euler characteristic for singular homology** (Milnor Theorem 5.2 (3)): if the steps
have no homology in degree `N + 1`, then
`Σ_{i ≤ N} (-1)^i dim H_i(X_n, X_0; 𝕜) = Σ_{i ≤ N} (-1)^i C_i`. -/
theorem singular_euler_characteristic (hn : 0 < n) {N : ℕ}
    (hN : ∀ k < n, finrank 𝕜 (subsetHomology 𝕜 (N + 1) (hX (Nat.le_succ k))) = 0) :
    ∑ i ∈ range (N + 1), (-1) ^ i * (finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.zero_le n))) : ℤ) =
      ∑ i ∈ range (N + 1), (-1) ^ i * (singularMorseNumber 𝕜 hX n i : ℤ) := by
  have h := (truncatedFiltrationHomology 𝕜 hX hfin).sum_neg_one_pow_finrank_eq (X := id)
    (fun k _ ↦ Nat.le_succ k) hn (N := N) (fun k hk ↦ by
      rw [← hN k hk]
      exact finrank_subsetHomology_congr _ _ (congrArg X (by simp only [id_eq]; omega))
        (congrArg X (by simp only [id_eq]; omega)) _)
  simp only [morseNumber_truncate 𝕜 hX n] at h
  rw [sum_congr rfl (fun i _ ↦ congrArg (fun m : ℕ ↦ (-1) ^ i * (m : ℤ))
    (finrank_truncate_total 𝕜 hX n i).symm)]
  exact h

omit hfin in
/-- **The Morse numbers count critical points** (Milnor p. 29), for singular homology: if the
step `(X_{k+1}, X_k)` has the homology of the cells attached at the critical points `p` of the
`k`-th slab, `dim H_i(X_{k+1}, X_k; 𝕜) = #{p ∈ P | step p = k ∧ ind p = i}`, then
`C_i = #{p ∈ P | ind p = i}`. -/
theorem singularMorseNumber_eq_card {α : Type*} {P : Finset α} {step ind : α → ℕ}
    (hstep : ∀ p ∈ P, step p < n)
    (hcells : ∀ k < n, ∀ i, finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k))) =
      #{p ∈ P | step p = k ∧ ind p = i}) (i : ℕ) :
    singularMorseNumber 𝕜 hX n i = #{p ∈ P | ind p = i} := by
  rw [← morseNumber_eq_card (F := 𝕜) (H := fun i a b ↦ filtrationGroup 𝕜 hX i a b) (X := id)
    hstep (fun k hk i ↦ (finrank_filtrationGroup 𝕜 hX (Nat.le_succ k)).trans (hcells k hk i)) i]
  exact sum_congr rfl fun k _ ↦ (finrank_filtrationGroup 𝕜 hX (Nat.le_succ k)).symm

/-- **Theorem 5.2 (2), the weak Morse inequalities, for singular homology and critical points**
(Milnor p. 29): `dim H_λ(X_n, X_0; 𝕜) ≤ #{p ∈ P | ind p = λ}`. -/
theorem singular_weak_morse_inequality_of_cells (hn : 0 < n) {α : Type*} {P : Finset α}
    {step ind : α → ℕ} (hstep : ∀ p ∈ P, step p < n)
    (hcells : ∀ k < n, ∀ i, finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k))) =
      #{p ∈ P | step p = k ∧ ind p = i}) (l : ℕ) :
    finrank 𝕜 (subsetHomology 𝕜 l (hX (Nat.zero_le n))) ≤ #{p ∈ P | ind p = l} :=
  singularMorseNumber_eq_card 𝕜 hX hstep hcells l ▸ singular_weak_morse_inequality 𝕜 hX hfin hn l

/-- **The Morse inequalities `(4_λ)` for singular homology and critical points** (Milnor p. 30):
`b_λ - b_{λ-1} + ⋯ ± b_0 ≤ C_λ - C_{λ-1} + ⋯ ± C_0`, where `b_i = dim H_i(X_n, X_0; 𝕜)` and
`C_i = #{p ∈ P | ind p = i}` is the number of critical points of index `i`. -/
theorem singular_morse_inequality_of_cells (hn : 0 < n) {α : Type*} {P : Finset α}
    {step ind : α → ℕ} (hstep : ∀ p ∈ P, step p < n)
    (hcells : ∀ k < n, ∀ i, finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k))) =
      #{p ∈ P | step p = k ∧ ind p = i}) (l : ℕ) :
    altSum (fun i ↦ (finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.zero_le n))) : ℤ)) l ≤
      altSum (fun i ↦ (#{p ∈ P | ind p = i} : ℤ)) l := by
  simpa only [singularMorseNumber_eq_card 𝕜 hX hstep hcells] using
    singular_morse_inequality 𝕜 hX hfin hn l

/-- **Theorem 5.2 (3) for singular homology and critical points** (Milnor p. 29): if every
critical point has index `≤ N`, then
`Σ_{i ≤ N} (-1)^i dim H_i(X_n, X_0; 𝕜) = Σ_{p ∈ P} (-1)^{ind p}`. -/
theorem singular_euler_characteristic_of_cells (hn : 0 < n) {α : Type*} {P : Finset α}
    {step ind : α → ℕ} (hstep : ∀ p ∈ P, step p < n)
    (hcells : ∀ k < n, ∀ i, finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.le_succ k))) =
      #{p ∈ P | step p = k ∧ ind p = i}) {N : ℕ} (hN : ∀ p ∈ P, ind p ≤ N) :
    ∑ i ∈ range (N + 1), (-1) ^ i * (finrank 𝕜 (subsetHomology 𝕜 i (hX (Nat.zero_le n))) : ℤ) =
      ∑ p ∈ P, (-1) ^ ind p := by
  have hvan : ∀ k < n, finrank 𝕜 (subsetHomology 𝕜 (N + 1) (hX (Nat.le_succ k))) = 0 := by
    intro k hk
    rw [hcells k hk, card_eq_zero, filter_eq_empty_iff]
    rintro p hp ⟨-, hi⟩
    have := hN p hp
    omega
  rw [singular_euler_characteristic 𝕜 hX hfin hn hvan]
  simp only [singularMorseNumber_eq_card 𝕜 hX hstep hcells]
  rw [← sum_fiberwise_of_maps_to (g := ind) (t := range (N + 1))
    (fun p hp ↦ mem_range.mpr (Nat.lt_succ_of_le (hN p hp)))]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_congr rfl fun p hp ↦ by rw [(mem_filter.mp hp).2], sum_const, nsmul_eq_mul, mul_comm]

end Filtration

end Morse.Homology
