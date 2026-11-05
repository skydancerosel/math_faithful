import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §3, "Proof of Sard's theorem", pp. 16–17.

# Setup for Sard's theorem

> **Theorem of Sard.** Let `f : U → ℝᵖ` be a smooth map, with `U` open in `ℝⁿ`, and let `C` be the
> set of critical points; that is the set of all `x ∈ U` with `rank dfₓ < p`. Then `f(C) ⊆ ℝᵖ`
> has measure zero.

This file sets up the objects in Milnor's proof, for maps `f : E → F` between finite-dimensional
real normed spaces (so that the induction on `n = dim E` can pass to subspaces without
choosing coordinates):

* `critSet f U`, Milnor's `C`: the points of `U` where `dfₓ` is not surjective;
* `vanishSet f U k`, Milnor's `Cₖ`: the points of `U` where all derivatives of order `1, …, k`
  vanish;
* `SardStatement n`: the statement of Sard's theorem for all domains of dimension `n`, all
  targets, and all Haar measures on the target. Milnor proves it by induction on `n`.

It also proves two facts Milnor uses without comment:

* the critical set is closed in `U`, because "`dfₓ` is surjective" is an open condition on the
  linear map `dfₓ` (`isOpen_setOf_surjective`); Milnor uses this on p. 18 ("this set is
  measurable, since it can be expressed as a countable union of compact subsets");
* a set of Hausdorff dimension less than `dim F` has Haar measure zero
  (`addHaar_eq_zero_of_dimH_lt_finrank`). This replaces Milnor's cube-counting in Step 3.
-/

open Set Filter Topology Function MeasureTheory Module
open scoped ContDiff NNReal ENNReal

noncomputable section

namespace Milnor

namespace Sard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Milnor's `C`: the set of critical points of `f` in `U`, i.e. the points where the derivative
is not onto. -/
def critSet (f : E → F) (U : Set E) : Set E :=
  {x ∈ U | ¬ Surjective (fderiv ℝ f x)}

/-- Milnor's `Cₖ`: the points of `U` where all derivatives of order `1, …, k` vanish. (Milnor
p. 16: "let `Cᵢ` denote the set of `x` such that all partial derivatives of `f` of order `≤ i`
vanish at `x`".) -/
def vanishSet (f : E → F) (U : Set E) (k : ℕ) : Set E :=
  {x ∈ U | ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0}

theorem vanishSet_antitone (f : E → F) (U : Set E) : Antitone (vanishSet f U) :=
  fun _ _ hkl _ hx => ⟨hx.1, fun j hj hjl => hx.2 j hj (hjl.trans hkl)⟩

theorem vanishSet_subset (f : E → F) (U : Set E) (k : ℕ) : vanishSet f U k ⊆ U := fun _ hx => hx.1

theorem critSet_subset (f : E → F) (U : Set E) : critSet f U ⊆ U := fun _ hx => hx.1

/-- `C₁ ⊆ C` when the target is nontrivial: a zero derivative is not onto. -/
theorem vanishSet_one_subset_critSet [Nontrivial F] (f : E → F) (U : Set E) :
    vanishSet f U 1 ⊆ critSet f U := by
  intro x hx
  refine ⟨hx.1, fun hsurj => ?_⟩
  have h1 : iteratedFDeriv ℝ 1 f x = 0 := hx.2 1 le_rfl le_rfl
  have hf : fderiv ℝ f x = 0 := by
    have := congrArg norm h1
    rw [norm_iteratedFDeriv_one, norm_zero, norm_eq_zero] at this
    exact this
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  obtain ⟨v, hv⟩ := hsurj y
  rw [hf] at hv
  exact hy (by simpa using hv.symm)

/-- `C` is the union of `C ∖ C₁`, `C₁ ∖ C₂`, …, `Cₖ₋₁ ∖ Cₖ`, and `Cₖ` (Milnor p. 16). We only need
the inclusion. -/
theorem critSet_subset_union (f : E → F) (U : Set E) (k : ℕ) :
    critSet f U ⊆ (critSet f U \ vanishSet f U 1) ∪
      (⋃ i ∈ Finset.Ico 1 k, vanishSet f U i \ vanishSet f U (i + 1)) ∪ vanishSet f U k := by
  intro x hx
  by_cases h1 : x ∈ vanishSet f U 1
  · by_cases hk : x ∈ vanishSet f U k
    · exact Or.inr hk
    · -- Find the last `i < k` with `x ∈ Cᵢ`.
      have hex : ∃ i, x ∈ vanishSet f U i ∧ x ∉ vanishSet f U (i + 1) := by
        by_contra hcon
        push Not at hcon
        have : ∀ i, 1 ≤ i → x ∈ vanishSet f U i := by
          intro i hi
          induction i with
          | zero => exact absurd hi (by omega)
          | succ n ih =>
            rcases Nat.eq_zero_or_pos n with rfl | hn
            · exact h1
            · exact hcon n (ih hn)
        exact hk (this k (by
          rcases Nat.eq_zero_or_pos k with rfl | hk'
          · exact absurd (vanishSet_antitone f U (Nat.zero_le 1) h1) hk
          · exact hk'))
      obtain ⟨i, hi, hi'⟩ := hex
      have hi1 : 1 ≤ i := by
        by_contra h
        push Not at h
        interval_cases i
        exact hi' h1
      have hik : i < k := by
        by_contra h
        push Not at h
        exact hk (vanishSet_antitone f U h hi)
      exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨i, Finset.mem_Ico.2 ⟨hi1, hik⟩, hi, hi'⟩))
  · exact Or.inl (Or.inl ⟨hx, h1⟩)

/-! ### Surjectivity is an open condition -/

section openSurj

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The surjective continuous linear maps form an open subset of `E →L[ℝ] F`. -/
theorem isOpen_setOf_surjective :
    IsOpen {L : E →L[ℝ] F | Surjective L} := by
  rw [isOpen_iff_mem_nhds]
  intro L hL
  -- Choose a linear right inverse `R` of `L`.
  obtain ⟨R, hR⟩ : ∃ R : F →ₗ[ℝ] E, (L : E →ₗ[ℝ] F).comp R = LinearMap.id := by
    have hsurj : LinearMap.range (L : E →ₗ[ℝ] F) = ⊤ := LinearMap.range_eq_top.2 hL
    exact (L : E →ₗ[ℝ] F).exists_rightInverse_of_surjective hsurj
  let Rc : F →L[ℝ] E := LinearMap.toContinuousLinearMap R
  -- The map `L' ↦ L' ∘ R` is continuous, and sends `L` to the identity, which is invertible.
  have hcont : Continuous fun L' : E →L[ℝ] F => L'.comp Rc :=
    (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := F) (F := E) (G := F)).continuous_left
  have hLR : L.comp Rc = ContinuousLinearMap.id ℝ F := by
    ext y
    have := LinearMap.congr_fun hR y
    simpa [Rc] using this
  have hmem : range ((↑) : (F ≃L[ℝ] F) → F →L[ℝ] F) ∈ 𝓝 (L.comp Rc) := by
    rw [hLR]
    exact ContinuousLinearEquiv.nhds (ContinuousLinearEquiv.refl ℝ F)
  filter_upwards [hcont.continuousAt.preimage_mem_nhds hmem] with L' hL'
  obtain ⟨e, he⟩ := hL'
  have he' : (e : F →L[ℝ] F) = L'.comp Rc := by simpa using he
  intro y
  refine ⟨Rc (e.symm y), ?_⟩
  have : (L'.comp Rc) (e.symm y) = y := by
    rw [← he']
    simp
  simpa using this

/-- The critical set of a `C¹` map is closed in `U`: its intersection with any compact subset
of `U` is compact. -/
theorem isCompact_critSet_inter {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    IsCompact (critSet f U ∩ K) := by
  have hcont : ContinuousOn (fderiv ℝ f) K :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU
  have hclosed : IsClosed (K ∩ fderiv ℝ f ⁻¹' {L : E →L[ℝ] F | Surjective L}ᶜ) :=
    hcont.preimage_isClosed_of_isClosed hK.isClosed isOpen_setOf_surjective.isClosed_compl
  have heq : critSet f U ∩ K = K ∩ fderiv ℝ f ⁻¹' {L : E →L[ℝ] F | Surjective L}ᶜ := by
    ext x
    constructor
    · rintro ⟨⟨-, hx⟩, hxK⟩
      exact ⟨hxK, hx⟩
    · rintro ⟨hxK, hx⟩
      exact ⟨⟨hKU hxK, hx⟩, hxK⟩
  rw [heq]
  exact hK.of_isClosed_subset hclosed inter_subset_left

end openSurj

/-! ### Hausdorff dimension and Haar measure -/

section haar

variable [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- A subset of a finite-dimensional real normed space with Hausdorff dimension strictly less than
the dimension of the space has Haar measure zero. -/
theorem addHaar_eq_zero_of_dimH_lt_finrank (μ : Measure F) [μ.IsAddHaarMeasure]
    {s : Set F} (hs : dimH s < finrank ℝ F) : μ s = 0 := by
  set p := finrank ℝ F with hp
  -- Transport to `Fin p → ℝ`.
  let e : F ≃L[ℝ] (Fin p → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_fin_fun])
  have hdim : dimH (e '' s) < p := by
    calc dimH (e '' s) ≤ dimH s := e.lipschitz.dimH_image_le s
      _ < p := hs
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · exfalso
    rw [hp0] at hs
    simp at hs
  · have : Nonempty (Fin p) := ⟨⟨0, hp0⟩⟩
    have hvol : volume (e '' s) = 0 := by
      have h1 : μH[p] (e '' s) = 0 := hausdorffMeasure_of_dimH_lt (d := p) hdim
      have h2 : (μH[Fintype.card (Fin p)] : Measure (Fin p → ℝ)) = volume := hausdorffMeasure_pi_real
      rw [Fintype.card_fin] at h2
      rw [← h2]
      exact_mod_cast h1
    have hmap : (μ.map e) ≪ (volume : Measure (Fin p → ℝ)) :=
      Measure.absolutelyContinuous_isAddHaarMeasure _ _
    have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
    have : (μ.map e) (e '' s) = μ s := by
      rw [hemb.map_apply, e.injective.preimage_image]
    rw [← this]
    exact hmap hvol

end haar

/-! ### The statement to be proved by induction -/

universe u

/-- Sard's theorem for domains of dimension `n`: for every finite-dimensional real normed space
`E` of dimension `n`, every finite-dimensional real normed space `F` with a Haar measure `μ`, every
open `U ⊆ E` and every smooth `f : U → F`, the set of critical values `f(C)` is `μ`-null. -/
def SardStatement (n : ℕ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
    finrank ℝ E = n →
    ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
      [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
      (U : Set E), IsOpen U → ∀ f : E → F, ContDiffOn ℝ ∞ f U →
      μ (f '' critSet f U) = 0

end Sard

end Milnor
