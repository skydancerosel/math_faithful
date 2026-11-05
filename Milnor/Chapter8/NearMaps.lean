import Milnor.Chapter7.Stereo
import Milnor.Chapter7.Homotopy

/-!
# Problem 3: maps which are never antipodal are homotopic

If `f, g : X → Sᵖ` satisfy `‖f x - g x‖ < 2` for all `x`, then `f` and `g` are homotopic, by the
normalized straight-line homotopy; the homotopy is smooth if `f` and `g` are.
-/

open Set Filter Topology Function Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

open Sphere

namespace Problems

variable {p : ℕ}

theorem norm_sph (a : Sph p) : ‖a.1‖ = 1 := (mem_iff_norm).1 a.2

/-- The chord between two points of the sphere at distance `< 2` avoids the origin. -/
theorem chord_ne_zero {a b : Sph p} (h : ‖a.1 - b.1‖ < 2) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) • a.1 + s • b.1 ≠ 0 := by
  intro h0
  have h1 : (1 - s) • a.1 = -(s • b.1) := eq_neg_of_add_eq_zero_left h0
  have h2 : ‖(1 - s) • a.1‖ = ‖s • b.1‖ := by rw [h1, norm_neg]
  rw [norm_smul, norm_smul, norm_sph, norm_sph, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith), abs_of_nonneg hs0, mul_one, mul_one] at h2
  have hs : s = 1 / 2 := by linarith
  subst hs
  have h3 : a.1 = -b.1 := by
    have := h1
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at this
    have h4 : (1 / 2 : ℝ) • a.1 = (1 / 2 : ℝ) • (-b.1) := by rw [this, smul_neg]
    exact smul_right_injective _ (by norm_num) h4
  have : ‖a.1 - b.1‖ = 2 := by
    rw [h3, show -b.1 - b.1 = (-2 : ℝ) • b.1 by module, norm_smul, norm_sph]; norm_num
  linarith

theorem normalize_sph (a : Sph p) : normalize a.1 = a.1 := by
  show ‖a.1‖⁻¹ • a.1 = a.1
  rw [norm_sph, inv_one, one_smul]

theorem nv0_sph (a : Sph p) : nv0 a.1 = a := by
  have ha : a.1 ≠ 0 := fun h => by simpa [h] using norm_sph a
  exact Subtype.ext (by rw [nv0_val ha, normalize_sph])

/-- **Problem 3, continuous form.** -/
theorem homotopic_of_norm_sub_lt_two {X : Type*} [TopologicalSpace X] (f g : C(X, Sph p))
    (h : ∀ x, ‖(f x).1 - (g x).1‖ < 2) : f.Homotopic g := by
  have hne : ∀ (q : unitInterval × X), (1 - (q.1 : ℝ)) • (f q.2).1 + (q.1 : ℝ) • (g q.2).1 ≠ 0 :=
    fun q => chord_ne_zero (h q.2) q.1.2.1 q.1.2.2
  have hcont : Continuous fun q : unitInterval × X =>
      (1 - (q.1 : ℝ)) • (f q.2).1 + (q.1 : ℝ) • (g q.2).1 := by
    have hf : Continuous fun q : unitInterval × X => (f q.2).1 :=
      continuous_subtype_val.comp (f.continuous.comp continuous_snd)
    have hg : Continuous fun q : unitInterval × X => (g q.2).1 :=
      continuous_subtype_val.comp (g.continuous.comp continuous_snd)
    have ht : Continuous fun q : unitInterval × X => (q.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub ht).smul hf).add (ht.smul hg)
  refine ⟨{ toFun := fun q => ⟨normalize ((1 - (q.1 : ℝ)) • (f q.2).1 + (q.1 : ℝ) • (g q.2).1),
              normalize_mem (hne q)⟩
            continuous_toFun := ?_
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · refine Continuous.subtype_mk ?_ _
    refine continuous_iff_continuousAt.2 fun q => ?_
    exact ContinuousAt.comp (g := normalize (n := p))
      (f := fun q : unitInterval × X => (1 - (q.1 : ℝ)) • (f q.2).1 + (q.1 : ℝ) • (g q.2).1)
      (contDiffAt_normalize (hne q)).continuousAt hcont.continuousAt
  · intro x
    apply Subtype.ext
    simp only [Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero]
    exact normalize_sph (f x)
  · intro x
    apply Subtype.ext
    simp only [Set.Icc.coe_one, sub_self, zero_smul, one_smul, zero_add]
    exact normalize_sph (g x)

/-- **Problem 3, smooth form.** Two smooth maps `f, g : X → Sᵖ` from a manifold with
`‖f x - g x‖ < 2` are smoothly homotopic. -/
theorem smoothHomotopic_of_norm_sub_lt_two {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I ∞ X] {f g : X → Sph p}
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hg : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g) (h : ∀ x, ‖(f x).1 - (g x).1‖ < 2) :
    SmoothHomotopic I 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f g := by
  set σ : ℝ → ℝ := Real.smoothTransition with hσ
  have hσs : ContDiff ℝ ∞ σ := Real.smoothTransition.contDiff
  set w : X × ℝ → EuclideanSpace ℝ (Fin (p + 1)) :=
    fun q => (1 - σ q.2) • (f q.1).1 + σ q.2 • (g q.1).1 with hw
  have hne : ∀ q, w q ≠ 0 := fun q =>
    chord_ne_zero (h q.1) (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
  have hfv : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) ∞
      (fun q : X × ℝ => (f q.1).1) := contMDiff_val.comp (hf.comp contMDiff_fst)
  have hgv : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) ∞
      (fun q : X × ℝ => (g q.1).1) := contMDiff_val.comp (hg.comp contMDiff_fst)
  have hσq : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun q : X × ℝ => σ q.2) :=
    hσs.contMDiff.comp contMDiff_snd
  have hwc : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) ∞ w :=
    ((contMDiff_const.sub hσq).smul hfv).add (hσq.smul hgv)
  refine ⟨fun q => nv0 (w q), contMDiff_nv0_comp hwc hne, fun x => ?_, fun x => ?_⟩
  · simp only [hw, hσ, Real.smoothTransition.zero, sub_zero, one_smul, zero_smul, add_zero]
    exact nv0_sph (f x)
  · simp only [hw, hσ, Real.smoothTransition.one, sub_self, zero_smul, one_smul, zero_add]
    exact nv0_sph (g x)

end Problems

end Milnor
