import Morse.Chapter1.ManifoldMorse
import Morse.Chapter3.EulerCharGradient

/-!
Milnor, *Morse Theory*, §5, p. 29 (the display `χ(M) = C₀ - C₁ + C₂ - ⋯ ± Cₙ` and formula (3) of
Theorem 5.2), read through §6, Application 2 (pp. 36–37); without homology.

# `Σ_λ (-1)^λ C_λ` is the Euler number of Poincaré–Hopf

## Milnor's text, paraphrased

* **§5, p. 29.**  For a compact manifold `M` and a differentiable function on `M` with isolated,
  non-degenerate critical points, Milnor chooses `a₁ < ⋯ < a_k` with exactly `i` critical points in
  `M^{a_i}` and `M^{a_k} = M`, computes the homology of each slab `(M^{a_i}, M^{a_{i-1}})` by
  excision, and applies Lemma 5.1 to `S = χ`:
  `χ(M) = Σ_i χ(M^{a_i}, M^{a_{i-1}}) = C₀ - C₁ + C₂ - ⋯ ± Cₙ`, `C_λ` the number of critical
  points of index `λ`.  Theorem 5.2 records this as formula (3),
  `Σ_λ (-1)^λ R_λ(M) = Σ_λ (-1)^λ C_λ`.  The algebraic part of the argument is
  `Morse/Chapter3/Inequalities.lean` (`Morse.FiltrationHomology.euler_characteristic_eq`); its
  topological input — relative singular homology, the exact sequence of a triple, excision — is not
  in Mathlib.
* **§6, Application 2, pp. 36–37.**  On a compact manifold there is a vector field whose index sum
  is `χ(M)`: for a function `f` on `M`, `χ(M) = Σ (-1)^λ C_λ` by §5, and `(-1)^λ` is the index of
  `grad f` at a critical point of index `λ`.  Since the index sum is a topological invariant (Milnor
  cites Steenrod, *The Topology of Fibre Bundles*, 39.7), the index sum of *every* vector field on
  `M` is `χ(M)`.

## What is proved here

Application 2 run in the direction that needs no homology.  The index sum of every smooth tangent
field on `N` is one integer `χN` (the Poincaré–Hopf theorem of the companion project, Milnor's
"topological invariant"), and the index sum of the gradient field of a Morse function `f` is
`Σ_λ (-1)^λ C_λ(f)` (`Morse.indexN_tangentialGradient`).  Hence `Σ_λ (-1)^λ C_λ(f) = χN` for every
Morse function `f`: the right-hand side of Milnor's display is a topological invariant.  The same
argument is Milnor's "Step 1" in *Topology from the Differentiable Viewpoint* (§6, p. 40).  For a
compact submanifold `N ⊆ ℝᴷ⁺¹` of positive dimension `d + 1`, `K ≥ 1`:

* `Morse.IsEulerNumber hN hNc hne χN`: `χN` is the index sum of every smooth tangent field on `N`
  with finitely many zeros (the indices being those of the companion project,
  `Milnor.Tub.indexN`).  Such an integer exists by the Poincaré–Hopf theorem
  (`Morse.exists_isEulerNumber`, which is `Milnor.Tub.poincare_hopf`).
* `Morse.IsEulerNumber.finsum_eq` and `Morse.IsEulerNumber.sum_critCount_eq` (**the main
  theorem**): for every Morse function `f : N → ℝ` (smooth, with non-degenerate critical points;
  `Morse.IsMorseFunction`), `Σ_{q critical} (-1)^{index_q f} = χN`, equivalently
  `Σ_{λ=0}^{d+1} (-1)^λ C_λ = χN`, `C_λ = Morse.critCount 𝔻 f λ` the number of critical points of
  index `λ`.  `Morse.exists_eulerNumber_eq_sum_critCount` packages the two.
* `Morse.sum_critCount_eq_of_isMorseFunction`: **the alternating count is the same for all Morse
  functions on `N`.**
* `Morse.exists_contDiff_comp_val_eq`: every smooth `f : N → ℝ` is the restriction of a smooth
  function on `ℝᴷ⁺¹` (`f ∘ r` cut off away from `N`, `r` the nearest-point retraction); this is
  how the intrinsic statement reduces to the ambient one,
  `Morse.IsEulerNumber.finsum_eq_of_ambient`.

The sphere is treated in `Morse/Chapter3/EulerCharSphere.lean`.

## What Milnor leaves implicit, and what is not done

* **"For any differentiable function `f`"** (Application 2) must read "for any differentiable
  function with only non-degenerate critical points": `C_λ` and the index `(-1)^λ` are meaningless
  otherwise.  Such functions exist by Corollary 6.7, which is not used here: the statements are
  about every Morse function and are vacuous if there is none.  Likewise "the sum of the indices
  of the critical points of `X`" means the sum over the zeros of `X`.
* **"`(-1)^λ` is the index of `grad f`"** is asserted without proof; it is
  `Morse.indexN_tangentialGradient`, whose ingredients (the choice of metric, the linear algebra of
  `Morse/Chapter3/EulerCharAlgebra.lean`, the Hessian of a function on a submanifold) are discussed
  in `Morse/Chapter3/EulerCharGradient.lean`.
* **"Isolated"** in Milnor's hypothesis on p. 29 is redundant: non-degenerate critical points are
  isolated (Corollary 2.3), so a Morse function on a compact manifold has finitely many
  (`Morse.IsMorseFunction.finite_setOf_isCriticalPointM`), and every `C_λ` is finite.
* **The last term `± Cₙ`** takes `n = dim M`: `C_λ = 0` for `λ > dim M`
  (`Morse.indexM_le_finrank`), which is why the sum stops at `d + 1`.
* **Distinct critical values are not needed.**  Milnor's slab argument (p. 29) needs one critical
  point per slab (see `Morse/Chapter3/Inequalities.lean`); the vector-field argument does not
  order the critical points at all.
* **The Euler number is not identified with the Euler characteristic.**  `χN` is the integer of the
  Poincaré–Hopf theorem (the degree of the Gauss map of the boundary of a tubular neighbourhood).
  That it equals `Σ (-1)^i dim H_i(N; F)` is formula (3) and needs homology; with a homology
  theory satisfying the hypotheses of `Morse.FiltrationHomology.euler_characteristic_eq`, the two
  results together would give it.
* **Dimension `0` is excluded**: the companion project computes the index of a non-degenerate zero
  (`Milnor.Tub.indexN_eq_sgn_det`) only on manifolds of dimension `d + 1 ≥ 1`.  (For `dim N = 0`
  every point is a critical point of index `0` and `χN = #N`.)
* **`N` is a compact submanifold of Euclidean space** with a slice-chart atlas, as in the companion
  project.  The transfer to an abstract compact Hausdorff manifold `M`, through Mathlib's Whitney
  embedding for compact manifolds (which Milnor quotes in the proof of Corollary 6.7), is in
  `Morse/Chapter4/Whitney.lean`: `Morse.eulerNumberM`, `Morse.sum_critCount_eq_eulerNumberM`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### The Morse numbers `C_λ` -/

section Count

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

variable (E) in
/-- **The Morse number `C_λ`** (Milnor, p. 29): the number of critical points of `f` of index `k`
(by the convention of `Set.ncard`, `0` if there are infinitely many). -/
def critCount (f : M → ℝ) (k : ℕ) : ℕ :=
  {p : M | IsCriticalPointM E f p ∧ indexM E f p = k}.ncard

/-- **Regrouping the critical points by their index**: if `f` has finitely many critical points,
`Σ_{p critical} (-1)^{index_p f} = Σ_{λ ≤ dim E} (-1)^λ C_λ`. -/
theorem finsum_neg_one_pow_indexM_eq_sum_critCount [FiniteDimensional ℝ E] {f : M → ℝ}
    (hfin : {p : M | IsCriticalPointM E f p}.Finite) :
    ∑ᶠ p ∈ {p : M | IsCriticalPointM E f p}, (-1 : ℤ) ^ indexM E f p =
      ∑ k ∈ Finset.range (finrank ℝ E + 1), (-1 : ℤ) ^ k * critCount E f k := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    ← Finset.sum_fiberwise_of_maps_to (g := fun p => indexM E f p)
      (t := Finset.range (finrank ℝ E + 1))
      (fun p _ => Finset.mem_range.2 (Nat.lt_succ_of_le (indexM_le_finrank f p)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.1 hp).2], Finset.sum_const,
    nsmul_eq_mul, mul_comm]
  congr 2
  rw [critCount, ← Set.ncard_coe_finset]
  congr 1
  ext p
  simp

end Count

/-! ### Compact submanifolds of `ℝᴷ⁺¹` -/

section Tub

variable {K d m : ℕ} {N : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
    (EuclideanSpace ℝ (Fin (d + 1))) (EuclideanSpace ℝ (Fin m)) N)
  (hNc : IsCompact N) (hne : N.Nonempty)

local notation "𝔼" => EuclideanSpace ℝ (Fin (K + 1))
local notation "𝔻" => EuclideanSpace ℝ (Fin (d + 1))

/-- **`χN` is the Euler number of `N`** in the sense of the Poincaré–Hopf theorem: the sum of the
indices of every smooth tangent field `v` on `N` whose zeros are finitely many distinct points
`z₁, …, z_j` is `χN`.  (This is the property of the integer of `Milnor.Tub.poincare_hopf`.) -/
def IsEulerNumber (χN : ℤ) : Prop :=
  ∀ (v : N → 𝔼) (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) ∞ v)
    (_hvT : letI := hN.chartedSpace; ∀ q : N, v q ∈ LinearMap.range
      ((Milnor.mfd 𝓘(ℝ, 𝔻) 𝓘(ℝ, 𝔼) (Subtype.val : N → 𝔼) q : 𝔻 →L[ℝ] 𝔼) : 𝔻 →ₗ[ℝ] 𝔼))
    {j : ℕ} (z : Fin j → N) (_hz : Injective z) (_hzero : ∀ q, v q = 0 ↔ ∃ i, q = z i),
    ∑ i, Milnor.Tub.indexN hN hNc hne v hv (z i) = χN

/-- **The Poincaré–Hopf theorem** (the companion project's `Milnor.Tub.poincare_hopf`): a compact
submanifold of `ℝᴷ⁺¹`, `K ≥ 1`, has an Euler number. -/
theorem exists_isEulerNumber (hK : 0 < K) : ∃ χN : ℤ, IsEulerNumber hN hNc hne χN :=
  Milnor.Tub.poincare_hopf hN hNc hne hK

/-- **The main theorem for the restriction of an ambient function**: if `F : ℝᴷ⁺¹ → ℝ` is smooth
and all critical points of `F|N` are non-degenerate, then `Σ_{q critical} (-1)^{index_q} = χN`.
The tangential gradient of `F` is a smooth tangent field whose zeros are the critical points of
`F|N`, finitely many, with index `(-1)^{index_q}` at `q` (`Morse.indexN_tangentialGradient`). -/
theorem IsEulerNumber.finsum_eq_of_ambient (hK : 0 < K) {χN : ℤ}
    (hχ : IsEulerNumber hN hNc hne χN) {F : 𝔼 → ℝ} (hF : ContDiff ℝ ∞ F)
    (hnd : letI := hN.chartedSpace; ∀ q : N, IsCriticalPointM 𝔻 (F ∘ Subtype.val) q →
      IsNondegenerate (hessianM 𝔻 (F ∘ Subtype.val) q)) :
    letI := hN.chartedSpace
    ∑ᶠ q ∈ {q : N | IsCriticalPointM 𝔻 (F ∘ Subtype.val) q},
      (-1 : ℤ) ^ indexM 𝔻 (F ∘ Subtype.val) q = χN := by
  classical
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  have hsmooth : ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, ℝ) ∞ (F ∘ (Subtype.val : N → 𝔼)) :=
    contMDiff_comp_val hN hF
  have hMorse : IsMorseFunction 𝔻 (F ∘ Subtype.val) := ⟨hsmooth, hnd⟩
  have hfin := hMorse.finite_setOf_isCriticalPointM
  set s := hfin.toFinset with hs
  -- the critical points, enumerated
  set z : Fin s.card → N := fun i => (s.equivFin.symm i).1 with hzdef
  have hz : Injective z := fun i j h => s.equivFin.symm.injective (Subtype.ext h)
  have hzero : ∀ q, tangentialGradient hN F q = 0 ↔ ∃ i, q = z i := by
    intro q
    rw [tangentialGradient_eq_zero_iff hN (hF.differentiable (by simp) _)]
    constructor
    · intro hq
      refine ⟨s.equivFin ⟨q, hfin.mem_toFinset.2 hq⟩, ?_⟩
      simp [hzdef]
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.1 (s.equivFin.symm i).2
  have hsum := hχ (tangentialGradient hN F) (contMDiff_tangentialGradient hN hNc hne hF)
    (tangentialGradient_mem_range hN F) z hz hzero
  rw [← hsum, finsum_mem_eq_finite_toFinset_sum _ hfin, ← hs, ← Finset.sum_coe_sort s,
    ← s.equivFin.symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcrit : IsCriticalPointM 𝔻 (F ∘ Subtype.val) (z i) :=
    hfin.mem_toFinset.1 (s.equivFin.symm i).2
  exact (indexN_tangentialGradient hN hNc hne hK hF ⟨hcrit, hnd _ hcrit⟩).symm

include hNc hne in
/-- **Every smooth function on `N` is the restriction of a smooth function on `ℝᴷ⁺¹`**: `f ∘ r`,
`r` the nearest-point retraction, is smooth on the tubular neighbourhood, and a cut-off
(`Milnor.exists_extension`) makes it global without changing it near `N`. -/
theorem exists_contDiff_comp_val_eq {f : N → ℝ}
    (hf : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, 𝔻) 𝓘(ℝ, ℝ) ∞ f) :
    ∃ F : 𝔼 → ℝ, ContDiff ℝ ∞ F ∧ F ∘ Subtype.val = f := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  set U : TopologicalSpace.Opens 𝔼 :=
    ⟨Milnor.Tub.Nε hN hNc hne, Milnor.Tub.isOpen_Nε hN hNc hne⟩ with hU
  -- `r` as a smooth map `U → N`
  have hrU : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔼) ∞ (fun x : U => tubRet hN hNc hne x.1) := by
    intro x
    have := contDiffAt_tubRet hN hNc hne x.2
    rw [← contMDiffAt_iff_contDiffAt] at this
    exact (contMDiffAt_subtype_iff (I := 𝓘(ℝ, 𝔼)) (I' := 𝓘(ℝ, 𝔼)) (n := ∞) (U := U)
      (f := tubRet hN hNc hne) (x := x)).2 this
  have hrN : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔻) ∞ (fun x : U => Milnor.Tub.tubr hN hNc hne x.1) :=
    hN.contMDiff_codRestrict hrU (fun x => tubRet_mem hN hNc hne x.1)
  have hfU : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ, ℝ) ∞ (fun x : U => f (Milnor.Tub.tubr hN hNc hne x.1)) :=
    hf.comp hrN
  have hfW : ContMDiffOn 𝓘(ℝ, 𝔼) 𝓘(ℝ, ℝ) ∞ (fun x => f (Milnor.Tub.tubr hN hNc hne x))
      (Milnor.Tub.Nε hN hNc hne) := by
    intro x hx
    exact ((contMDiffAt_subtype_iff (I := 𝓘(ℝ, 𝔼)) (I' := 𝓘(ℝ, ℝ)) (n := ∞) (U := U)
      (f := fun x => f (Milnor.Tub.tubr hN hNc hne x)) (x := ⟨x, hx⟩)).1
        (hfU ⟨x, hx⟩)).contMDiffWithinAt
  obtain ⟨F, hF, hFeq⟩ := Milnor.exists_extension (Milnor.Tub.isOpen_Nε hN hNc hne) hfW
    (Milnor.Tub.isCompact_X hN hNc hne) (Milnor.Tub.X_subset_Nε hN hNc hne)
  refine ⟨F, contMDiff_iff_contDiff.1 hF, funext fun q => ?_⟩
  have h := hFeq.self_of_nhdsSet q.1 (Milnor.Tub.N_subset_X hN hNc hne q.2)
  rw [comp_apply, h, Milnor.Tub.tubr_val hN hNc hne q]

/-- **The main theorem** (Milnor, p. 29, formula (3), with the Euler number of Poincaré–Hopf in
place of the Euler characteristic): for every Morse function `f` on `N`, the sum of
`(-1)^{index}` over the critical points of `f` is the Euler number `χN`. -/
theorem IsEulerNumber.finsum_eq (hK : 0 < K) {χN : ℤ} (hχ : IsEulerNumber hN hNc hne χN)
    {f : N → ℝ} (hf : letI := hN.chartedSpace; IsMorseFunction 𝔻 f) :
    letI := hN.chartedSpace
    ∑ᶠ q ∈ {q : N | IsCriticalPointM 𝔻 f q}, (-1 : ℤ) ^ indexM 𝔻 f q = χN := by
  let _ := hN.chartedSpace
  obtain ⟨F, hF, rfl⟩ := exists_contDiff_comp_val_eq hN hNc hne hf.contMDiff
  exact hχ.finsum_eq_of_ambient hN hNc hne hK hF hf.isNondegenerate

/-- **The main theorem, with the Morse numbers** (Milnor, p. 29, formula (3)): for every Morse
function `f` on `N`, `Σ_{λ=0}^{dim N} (-1)^λ C_λ = χN`, `C_λ` the number of critical points of
index `λ`. -/
theorem IsEulerNumber.sum_critCount_eq (hK : 0 < K) {χN : ℤ} (hχ : IsEulerNumber hN hNc hne χN)
    {f : N → ℝ} (hf : letI := hN.chartedSpace; IsMorseFunction 𝔻 f) :
    letI := hN.chartedSpace
    ∑ k ∈ Finset.range (d + 2), (-1 : ℤ) ^ k * critCount 𝔻 f k = χN := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  have : CompactSpace N := isCompact_iff_compactSpace.1 hNc
  have h := finsum_neg_one_pow_indexM_eq_sum_critCount hf.finite_setOf_isCriticalPointM
  rw [finrank_euclideanSpace_fin] at h
  rw [← h]
  exact hχ.finsum_eq hN hNc hne hK hf

/-- **`Σ (-1)^λ C_λ` is the Euler number of Poincaré–Hopf** (Milnor, p. 29, formula (3), without
homology): a compact submanifold `N ⊆ ℝᴷ⁺¹` (`K ≥ 1`, `dim N ≥ 1`) has an integer `χN` which is at
the same time the index sum of every smooth tangent field with finitely many zeros and the
alternating count `Σ_λ (-1)^λ C_λ` of the critical points of every Morse function. -/
theorem exists_eulerNumber_eq_sum_critCount (hK : 0 < K) :
    ∃ χN : ℤ, IsEulerNumber hN hNc hne χN ∧
      ∀ f : N → ℝ, (letI := hN.chartedSpace; IsMorseFunction 𝔻 f) →
        letI := hN.chartedSpace
        ∑ k ∈ Finset.range (d + 2), (-1 : ℤ) ^ k * critCount 𝔻 f k = χN := by
  obtain ⟨χN, hχ⟩ := exists_isEulerNumber hN hNc hne hK
  exact ⟨χN, hχ, fun f hf => hχ.sum_critCount_eq hN hNc hne hK hf⟩

include hNc hne in
/-- **The alternating count of critical points does not depend on the Morse function**
(Milnor, p. 29: both sides of formula (3) are then `χ(M)`): for any two Morse functions `f`, `g`
on `N`, `Σ_λ (-1)^λ C_λ(f) = Σ_λ (-1)^λ C_λ(g)`. -/
theorem sum_critCount_eq_of_isMorseFunction (hK : 0 < K) {f g : N → ℝ}
    (hf : letI := hN.chartedSpace; IsMorseFunction 𝔻 f)
    (hg : letI := hN.chartedSpace; IsMorseFunction 𝔻 g) :
    letI := hN.chartedSpace
    ∑ k ∈ Finset.range (d + 2), (-1 : ℤ) ^ k * critCount 𝔻 f k =
      ∑ k ∈ Finset.range (d + 2), (-1 : ℤ) ^ k * critCount 𝔻 g k := by
  obtain ⟨χN, hχ⟩ := exists_isEulerNumber hN hNc hne hK
  rw [hχ.sum_critCount_eq hN hNc hne hK hf, hχ.sum_critCount_eq hN hNc hne hK hg]

/-- **The Euler number is the alternating count of any one Morse function**: once a Morse function
exists, the integer of the Poincaré–Hopf theorem is determined by its critical points. -/
theorem IsEulerNumber.eq_sum_critCount (hK : 0 < K) {χN : ℤ} (hχ : IsEulerNumber hN hNc hne χN)
    {f : N → ℝ} (hf : letI := hN.chartedSpace; IsMorseFunction 𝔻 f) :
    letI := hN.chartedSpace
    χN = ∑ k ∈ Finset.range (d + 2), (-1 : ℤ) ^ k * critCount 𝔻 f k :=
  (hχ.sum_critCount_eq hN hNc hne hK hf).symm

end Tub

end Morse
