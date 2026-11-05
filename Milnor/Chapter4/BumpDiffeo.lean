import Mathlib

/-!
# Bump-function diffeomorphisms of a finite-dimensional space

For Milnor's Homogeneity Lemma (chapter 4) we need, for a smooth compactly supported
`φ : F → ℝ` and a small vector `c`, that the map `u ↦ u + φ(u) • c` is a diffeomorphism of `F`
which is the identity outside the support of `φ`.  Injectivity comes from a Lipschitz estimate,
surjectivity from the contraction principle, and smoothness of the inverse from the inverse
function theorem (the derivative `id + dφ ⊗ c` is invertible because `‖dφ‖‖c‖ < 1`).
-/

open Set Metric Function Filter Topology NNReal
open scoped ContDiff Manifold

noncomputable section

namespace Milnor.Bump

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The map `u ↦ u + φ(u) • c`. -/
def shift (φ : F → ℝ) (c : F) (u : F) : F := u + φ u • c

theorem shift_contDiff {φ : F → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : F) : ContDiff ℝ ∞ (shift φ c) :=
  contDiff_id.add (hφ.smul contDiff_const)

@[simp] theorem shift_zero (φ : F → ℝ) (u : F) : shift φ 0 u = u := by simp [shift]

theorem shift_of_eq_zero {φ : F → ℝ} {c u : F} (h : φ u = 0) : shift φ c u = u := by
  simp [shift, h]

theorem norm_shift_sub_le {φ : F → ℝ} {L : NNReal} (hL : LipschitzWith L φ) (c u v : F) :
    ‖φ v • c - φ u • c‖ ≤ (L : ℝ) * ‖c‖ * ‖u - v‖ := by
  rw [← sub_smul, norm_smul, Real.norm_eq_abs, ← Real.dist_eq]
  calc dist (φ v) (φ u) * ‖c‖ ≤ (L * dist v u) * ‖c‖ := by gcongr; exact hL.dist_le_mul v u
    _ = L * ‖c‖ * ‖u - v‖ := by rw [dist_eq_norm, ← norm_neg, neg_sub]; ring

/-- Injectivity when `φ` is `L`-Lipschitz and `L * ‖c‖ < 1`. -/
theorem shift_injective {φ : F → ℝ} {L : NNReal} (hL : LipschitzWith L φ) {c : F}
    (hc : (L : ℝ) * ‖c‖ < 1) : Injective (shift φ c) := by
  intro u v huv
  have h1 : u - v = φ v • c - φ u • c := by
    simp only [shift] at huv
    rw [eq_sub_iff_add_eq, sub_add_eq_add_sub, huv, add_sub_cancel_left]
  have h2 := norm_shift_sub_le hL c u v
  rw [← h1] at h2
  by_contra hne
  have hpos : 0 < ‖u - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have : ‖u - v‖ < ‖u - v‖ :=
    calc ‖u - v‖ ≤ L * ‖c‖ * ‖u - v‖ := h2
      _ < 1 * ‖u - v‖ := mul_lt_mul_of_pos_right hc hpos
      _ = ‖u - v‖ := one_mul _
  exact lt_irrefl _ this

/-- Surjectivity: `u ↦ w - φ(u) • c` is a contraction, so it has a fixed point. -/
theorem shift_surjective {φ : F → ℝ} {L : NNReal} (hL : LipschitzWith L φ) {c : F}
    (hc : (L : ℝ) * ‖c‖ < 1) : Surjective (shift φ c) := by
  intro w
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
  let T : F → F := fun u => w - φ u • c
  have hT : ContractingWith (L * ‖c‖₊) T := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
    · rw [← NNReal.coe_lt_coe, NNReal.coe_mul, coe_nnnorm, NNReal.coe_one]; exact hc
    · simp only [T, dist_eq_norm, sub_sub_sub_cancel_left, NNReal.coe_mul, coe_nnnorm]
      exact norm_shift_sub_le hL c u v
  obtain ⟨u, hu, -⟩ := hT.exists_fixedPoint w (edist_ne_top _ _)
  refine ⟨u, ?_⟩
  have hu' : w - φ u • c = u := hu
  show u + φ u • c = w
  have h := congrArg (fun x => x + φ u • c) hu'
  simp only [sub_add_cancel] at h
  exact h.symm

/-- A smooth compactly supported function is Lipschitz, with a bound on its derivative. -/
theorem exists_lipschitz_of_hasCompactSupport {φ : F → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hs : HasCompactSupport φ) :
    ∃ L : NNReal, LipschitzWith L φ ∧ ∀ u, ‖fderiv ℝ φ u‖ ≤ L := by
  obtain ⟨C, hC⟩ := (hs.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hφ.continuous_fderiv (by simp))
  refine ⟨Real.toNNReal C, ?_, fun u => (hC u).trans (Real.le_coe_toNNReal C)⟩
  refine lipschitzWith_of_nnnorm_fderiv_le (hφ.differentiable (by simp)) fun u => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact (hC u).trans (Real.le_coe_toNNReal C)

theorem shift_hasStrictFDerivAt {φ : F → ℝ} (hφ : ContDiff ℝ ∞ φ) (c u : F) :
    HasStrictFDerivAt (shift φ c) (ContinuousLinearMap.id ℝ F + (fderiv ℝ φ u).smulRight c) u :=
  (hasStrictFDerivAt_id u).add ((hφ.contDiffAt.hasStrictFDerivAt (by simp)).smul_const c)

/-- The derivative of the shift is invertible when `‖dφ‖ ‖c‖ < 1`. -/
theorem exists_continuousLinearEquiv_shift {φ : F → ℝ} {L : NNReal}
    (hL' : ∀ u, ‖fderiv ℝ φ u‖ ≤ L) {c : F} (hc : (L : ℝ) * ‖c‖ < 1) (u : F) :
    ∃ e : F ≃L[ℝ] F,
      (e : F →L[ℝ] F) = ContinuousLinearMap.id ℝ F + (fderiv ℝ φ u).smulRight c := by
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hA : ‖-((fderiv ℝ φ u).smulRight c)‖ < 1 := by
    rw [norm_neg, ContinuousLinearMap.norm_smulRight_apply]
    calc ‖fderiv ℝ φ u‖ * ‖c‖ ≤ L * ‖c‖ := by gcongr; exact hL' u
      _ < 1 := hc
  refine ⟨ContinuousLinearEquiv.ofUnit (Units.oneSub _ hA), ?_⟩
  ext v
  simp [ContinuousLinearEquiv.ofUnit, Units.oneSub, sub_neg_eq_add]

/-- The inverse of the shift is smooth (inverse function theorem). -/
theorem shift_symm_contDiff {φ : F → ℝ} (hφ : ContDiff ℝ ∞ φ) {L : NNReal}
    (hL' : ∀ u, ‖fderiv ℝ φ u‖ ≤ L) {c : F} (hc : (L : ℝ) * ‖c‖ < 1)
    (hbij : Bijective (shift φ c)) :
    ContDiff ℝ ∞ (Equiv.ofBijective (shift φ c) hbij).symm := by
  haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
  rw [contDiff_iff_contDiffAt]
  intro w
  obtain ⟨u, rfl⟩ := hbij.2 w
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_shift hL' hc u
  have hd : HasStrictFDerivAt (shift φ c) (e : F →L[ℝ] F) u := by
    rw [he]; exact shift_hasStrictFDerivAt hφ c u
  have hloc := (shift_contDiff hφ c).contDiffAt.to_localInverse (f' := e) hd.hasFDerivAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  refine hloc.congr_of_eventuallyEq ?_
  have hright : ∀ᶠ w in 𝓝 (shift φ c u),
      shift φ c (((shift_contDiff hφ c).contDiffAt.hasStrictFDerivAt' hd.hasFDerivAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)).localInverse (shift φ c) e u w) = w :=
    HasStrictFDerivAt.eventually_right_inverse _
  filter_upwards [hright] with w hw
  show (Equiv.ofBijective (shift φ c) hbij).symm w = _
  conv_lhs => rw [← hw]
  exact (Equiv.ofBijective (shift φ c) hbij).symm_apply_apply _

/-- An injective map which is the identity outside `K` maps any set containing `K` into itself. -/
theorem mapsTo_of_eq_id_outside {g : F → F} {K S : Set F} (hKS : K ⊆ S) (hinj : Injective g)
    (hgK : ∀ u, u ∉ K → g u = u) : ∀ u ∈ S, g u ∈ S := by
  intro u hu
  by_cases h : g u ∈ K
  · exact hKS h
  · have : g (g u) = g u := hgK _ h
    rw [hinj this]; exact hu

end Milnor.Bump
