import Milnor.Chapter7.Compose
import Milnor.Chapter7.Rotation

/-!
# The rotation homotopy `F(x, t) = r_{θ₀ ρ(t)} (f x)` (Milnor §7, Lemma 2)

For a planar rotation `r_θ` of the sphere, the homotopy from `f` to `r_{θ₀} ∘ f` obtained by
rotating the target is smooth, constant near the ends of `[0, 1]`, and `r_{θ₀} y` is a regular
value of it as soon as every point `r_τ y`, `0 ≤ τ ≤ θ₀`, of the arc is a regular value of `f`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) {p : ℕ}
  {u v : EuclideanSpace ℝ (Fin (p + 1))} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0)

include hu hv huv in
theorem rotS_add (a b : ℝ) (x : Sph p) : rotS u v a (rotS u v b x) = rotS u v (a + b) x := by
  apply Subtype.ext
  rw [rotS_val hu hv huv, rotS_val hu hv huv, rotS_val hu hv huv, rotCLM_add hu hv huv]
  rfl

include hu hv huv in
theorem dist_rotS (θ : ℝ) (a b : Sph p) : dist (rotS u v θ a) (rotS u v θ b) = dist a b := by
  rw [Subtype.dist_eq, Subtype.dist_eq, rotS_val hu hv huv, rotS_val hu hv huv, dist_eq_norm,
    dist_eq_norm, ← map_sub, norm_rotCLM hu hv huv]

variable {f : M → Sph p}
  (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)

include hu hv huv hf in
set_option maxHeartbeats 1000000 in
/-- **The rotation homotopy.** -/
theorem exists_rotHomotopy (θ₀ : ℝ) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ F' : M × ℝ → Sph p,
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ F' ∧
      (∀ x t, t ≤ ε → F' (x, t) = f x) ∧
      (∀ x t, 1 - ε ≤ t → F' (x, t) = rotS u v θ₀ (f x)) ∧
      ∀ y : Sph p, 0 ≤ θ₀ →
        (∀ τ, 0 ≤ τ → τ ≤ θ₀ →
          IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
            (rotS u v τ y)) →
        IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
          F' (rotS u v θ₀ y) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨ρ, hρs, hρ0, hρ1, hρ01, -⟩ := exists_timeTransition hε hε'
  have hρ's : ContDiff ℝ ∞ (fun t => θ₀ * ρ t) := contDiff_const.mul hρs
  have hfam : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun q : Sph p × ℝ => rotS u v (θ₀ * ρ q.2) q.1) :=
    contMDiff_rotS_family hu hv huv (ρ := fun t => θ₀ * ρ t) hρ's
  have hΨ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ)) ∞ (fun q : M × ℝ => (f q.1, q.2)) :=
    (hf.comp contMDiff_fst).prodMk contMDiff_snd
  have hF's : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ ((fun q : Sph p × ℝ => rotS u v (θ₀ * ρ q.2) q.1) ∘
        fun q : M × ℝ => (f q.1, q.2)) := hfam.comp hΨ
  have heq : ((fun q : Sph p × ℝ => rotS u v (θ₀ * ρ q.2) q.1) ∘
        fun q : M × ℝ => (f q.1, q.2)) = fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1) := by
    funext q; rfl
  rw [heq] at hF's
  refine ⟨fun q => rotS u v (θ₀ * ρ q.2) (f q.1), hF's, ?_, ?_, ?_⟩
  · intro x t ht
    show rotS u v (θ₀ * ρ t) (f x) = f x
    rw [hρ0 t ht, mul_zero]
    exact rotS_zero hu hv huv (f x)
  · intro x t ht
    show rotS u v (θ₀ * ρ t) (f x) = rotS u v θ₀ (f x)
    rw [hρ1 t ht, mul_one]
  · intro y hθ₀ harc q hq
    have hq' : rotS u v (θ₀ * ρ q.2) (f q.1) = rotS u v θ₀ y := hq
    have hfq : f q.1 = rotS u v (θ₀ - θ₀ * ρ q.2) y := by
      have := congrArg (rotS u v (-(θ₀ * ρ q.2))) hq'
      rw [rotS_neg_rotS hu hv huv, rotS_add hu hv huv] at this
      rw [this]
      congr 1
      ring
    have hρb := hρ01 q.2
    have hreg : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
        (f q.1) := by
      rw [hfq]
      refine harc _ ?_ ?_
      · nlinarith [hρb.2, hθ₀]
      · nlinarith [hρb.1, hθ₀]
    have hr : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (rotS u v (θ₀ * ρ q.2)) := contMDiff_rotS hu hv huv _
    have hbij := mfd_rotS_bijective hu hv huv (θ₀ * ρ q.2) (f q.1)
    have hslice : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun x => rotS u v (θ₀ * ρ q.2) (f x)) q.1) := by
      have h1 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        (hr.mdifferentiableAt (by simp) : MDifferentiableAt _ _ (rotS u v (θ₀ * ρ q.2)) (f q.1))
      have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
        (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        (hf.mdifferentiableAt (by simp) : MDifferentiableAt _ _ f q.1)
      have h3 := HasMFDerivAt.mfd_eq (h1.comp q.1 h2)
      have h4 : (rotS u v (θ₀ * ρ q.2) ∘ f) = fun x => rotS u v (θ₀ * ρ q.2) (f x) := rfl
      rw [h4] at h3
      rw [h3]
      exact hbij.2.comp (hreg q.1 rfl)
    have hpart : ∀ a, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun x => rotS u v (θ₀ * ρ q.2) (f x)) q.1 a =
        mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
          (fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) q (a, 0) := by
      intro a
      have h1 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) (fun x : M => (x, q.2)) q.1
          ((ContinuousLinearMap.id ℝ _).prod (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)) :=
        (hasMFDerivAt_id (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) q.1).prodMk
          (hasMFDerivAt_const (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ)) (c := q.2)
            (x := q.1))
      have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (hF's.mdifferentiableAt (by simp) :
          MDifferentiableAt _ _ (fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) (q.1, q.2))
      have h3 := HasMFDerivAt.mfd_eq (h2.comp q.1 h1)
      have h4 : ((fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) ∘ fun x : M => (x, q.2)) =
          fun x => rotS u v (θ₀ * ρ q.2) (f x) := rfl
      rw [h4] at h3
      rw [h3]
      rfl
    show Surjective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) q)
    intro wv
    obtain ⟨a, ha⟩ := hslice wv
    exact ⟨(a, 0), by rw [← hpart]; exact ha⟩

end Framed

end Milnor
