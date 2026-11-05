import Milnor.Chapter7.Framed
import Milnor.Chapter7.Transition

/-!
# Reparametrizing a homotopy to be constant near the ends

A smooth homotopy `F : M × ℝ → Sᵖ` with regular value `z` (also regular for `F(·,0)` and
`F(·,1)`) is replaced by `F'(x,t) = F(x, ρ(t))`, which is `F(·,0)` for `t ≤ ε`, `F(·,1)` for
`t ≥ 1 - ε`, and still has `z` as a regular value.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {k m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin k))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) {p : ℕ}

/-- **Reparametrization of a homotopy.** -/
theorem exists_reparam {F : M × ℝ → Sph p}
    (hF : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ F)
    {z : Sph p}
    (hz : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F z)
    (hz0 : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fun x => F (x, 0)) z)
    (hz1 : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fun x => F (x, 1)) z)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ F' : M × ℝ → Sph p,
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ F' ∧
      (∀ x t, t ≤ ε → F' (x, t) = F (x, 0)) ∧ (∀ x t, 1 - ε ≤ t → F' (x, t) = F (x, 1)) ∧
      IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F' z := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨ρ, hρs, hρ0, hρ1, hρ01, hρd⟩ := exists_timeTransition hε hε'
  set Φ : M × ℝ → M × ℝ := fun q => (q.1, ρ q.2) with hΦ
  have hΦs : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) ∞ Φ :=
    contMDiff_fst.prodMk (hρs.contMDiff.comp contMDiff_snd)
  refine ⟨fun q => F (Φ q), hF.comp hΦs, ?_, ?_, ?_⟩
  · intro x t ht; simp only [Φ, hρ0 t ht]
  · intro x t ht; simp only [Φ, hρ1 t ht]
  · intro q hq
    have hq' : F (Φ q) = z := hq
    -- the derivative of `Φ`
    have hρt : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ρ q.2
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (deriv ρ q.2)) :=
      ((hρs.differentiable (by simp)) q.2).hasDerivAt.hasFDerivAt.hasMFDerivAt
    have hΦd : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) Φ q
        ((ContinuousLinearMap.fst ℝ _ _).prod
          (((ContinuousLinearMap.id ℝ ℝ).smulRight (deriv ρ q.2)).comp (ContinuousLinearMap.snd ℝ _ _))) :=
      (hasMFDerivAt_fst q).prodMk (hρt.comp q (hasMFDerivAt_snd q))
    have hFd := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (hF.mdifferentiableAt (by simp) :
        MDifferentiableAt _ _ F (Φ q))
    have hchain : mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fun q => F (Φ q)) q =
        (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F (Φ q)).comp
          ((ContinuousLinearMap.fst ℝ _ _).prod
            (((ContinuousLinearMap.id ℝ ℝ).smulRight (deriv ρ q.2)).comp (ContinuousLinearMap.snd ℝ _ _))) :=
      HasMFDerivAt.mfd_eq (hFd.comp q hΦd)
    show Surjective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fun q => F (Φ q)) q)
    rw [hchain]
    -- the partial derivative in `x` at time `s`: `d_x F(·, s) a = dF_{(x,s)} (a, 0)`
    have hpart : ∀ s : ℝ, ∀ a, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun x => F (x, s)) q.1 a = mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F (q.1, s) (a, 0) := by
      intro s a
      have h1 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
          (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) (fun x : M => (x, s)) q.1
          ((ContinuousLinearMap.id ℝ _).prod (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)) :=
        (hasMFDerivAt_id (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) q.1).prodMk
          (hasMFDerivAt_const (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ)) (c := s) (x := q.1))
      have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (hF.mdifferentiableAt (by simp) :
          MDifferentiableAt _ _ F (q.1, s))
      have h3 := HasMFDerivAt.mfd_eq (h2.comp q.1 h1)
      have h4 : (F ∘ fun x : M => (x, s)) = fun x => F (x, s) := rfl
      rw [h4] at h3
      rw [h3]
      rfl
    intro wv
    by_cases h01 : ρ q.2 = 0 ∨ ρ q.2 = 1
    · -- the partial derivative in `x` already surjects
      have hsurj : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
          (fun x => F (x, ρ q.2)) q.1) := by
        rcases h01 with h | h
        · rw [h]; exact hz0 q.1 (by rw [← hq']; simp [Φ, h])
        · rw [h]; exact hz1 q.1 (by rw [← hq']; simp [Φ, h])
      obtain ⟨a, ha⟩ := hsurj wv
      refine ⟨(a, 0), ?_⟩
      rw [hpart] at ha
      simpa using ha
    · -- `ρ' > 0`, so `dΦ` is bijective
      push_neg at h01
      have ht : ε < q.2 ∧ q.2 < 1 - ε := by
        constructor
        · by_contra h; push_neg at h; exact h01.1 (hρ0 _ h)
        · by_contra h; push_neg at h; exact h01.2 (hρ1 _ h)
      have hd : 0 < deriv ρ q.2 := hρd q.2 ht.1 ht.2
      have hsurj : Surjective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F (Φ q)) := hz (Φ q) hq'
      obtain ⟨⟨a, b⟩, hab⟩ := hsurj wv
      refine ⟨(a, b / deriv ρ q.2), ?_⟩
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_id', id_eq, smul_eq_mul, div_mul_cancel₀ _ hd.ne']
      exact hab

end Framed

end Milnor
