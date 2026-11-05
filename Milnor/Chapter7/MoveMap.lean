import Milnor.Chapter7.Scale

/-!
# The moving collapse map

Given a basis `b`, a scale `c`, a time-dependent frame `τ t` and a time-dependent centre `γ t`,
the map `Φ (s, t) = collapse b c (B_{τ t} (s - γ t))` is a smooth map `ℝᵐ × ℝ → Sᵐ` whose
`t`-slice sends exactly `γ t` to the north pole, with derivative `(c • B_b) ∘ B_{τ t}` there.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {m : ℕ}

/-- The moving collapse map `(s, t) ↦ collapse (B_{τ t} (s - γ t))`. -/
def moveΦ {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b) (c : ℝ)
    (τ : ℝ → Fin m → EuclideanSpace ℝ (Fin m)) (γ : ℝ → EuclideanSpace ℝ (Fin m))
    (q : EuclideanSpace ℝ (Fin m) × ℝ) : Sph m :=
  collapse hb c (basisCLM (τ q.2) (q.1 - γ q.2))

theorem contMDiff_moveΦ {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b) (c : ℝ)
    {τ : ℝ → Fin m → EuclideanSpace ℝ (Fin m)}
    (hτ : ContDiff ℝ ∞ (fun t => basisCLM (τ t))) {γ : ℝ → EuclideanSpace ℝ (Fin m)}
    (hγ : ContDiff ℝ ∞ γ) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (moveΦ hb c τ γ) := by
  have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) ∞
      (fun q : EuclideanSpace ℝ (Fin m) × ℝ => basisCLM (τ q.2)) :=
    hτ.contMDiff.comp contMDiff_snd
  have h2 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun q : EuclideanSpace ℝ (Fin m) × ℝ => q.1 - γ q.2) :=
    contMDiff_fst.sub (hγ.contMDiff.comp contMDiff_snd)
  exact (contMDiff_collapse hb c).comp (h1.clm_apply h2)

theorem moveΦ_eq_north_iff {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b)
    {c : ℝ} (hc : c ≠ 0) {τ : ℝ → Fin m → EuclideanSpace ℝ (Fin m)}
    (hτ : ∀ t, LinearIndependent ℝ (τ t)) (γ : ℝ → EuclideanSpace ℝ (Fin m))
    (s : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    moveΦ hb c τ γ (s, t) = north ↔ s = γ t := by
  show collapse hb c (basisCLM (τ t) (s - γ t)) = north ↔ s = γ t
  rw [collapse_eq_north_iff hb hc]
  constructor
  · intro h
    exact sub_eq_zero.1 ((injective_iff_map_eq_zero _).1 (basisCLM_injective (hτ t)) _ h)
  · intro h
    rw [h, sub_self, map_zero]

theorem moveΦ_eq_south {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b)
    {c ε₀ μ : ℝ} (hsouth : ∀ z, ε₀ / 2 ≤ ‖z‖ → collapse hb c z = south)
    {τ : ℝ → Fin m → EuclideanSpace ℝ (Fin m)} (hμ : ∀ t z, μ * ‖z‖ ≤ ‖basisCLM (τ t) z‖)
    (γ : ℝ → EuclideanSpace ℝ (Fin m)) {s : EuclideanSpace ℝ (Fin m)} {t : ℝ}
    (h : ε₀ / 2 ≤ μ * ‖s - γ t‖) : moveΦ hb c τ γ (s, t) = south := by
  show collapse hb c (basisCLM (τ t) (s - γ t)) = south
  exact hsouth _ (h.trans (hμ t _))

theorem hasMFDerivAt_moveΦ_slice {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b)
    (c : ℝ) (τ : ℝ → Fin m → EuclideanSpace ℝ (Fin m)) (γ : ℝ → EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun s => moveΦ hb c τ γ (s, t)) (γ t) ((c • basisCLM b).comp (basisCLM (τ t))) := by
  set f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun s => basisCLM (τ t) (s - γ t) with hf
  have hf0 : f (γ t) = 0 := by simp [hf]
  have h1 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f (γ t)
      (basisCLM (τ t)) := by
    have := (basisCLM (τ t)).hasFDerivAt.comp (γ t) ((hasFDerivAt_id (γ t)).sub_const (γ t))
    rw [ContinuousLinearMap.comp_id] at this
    exact hasMFDerivAt_iff_hasFDerivAt.2 this
  have h2 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (collapse hb c) (f (γ t)) (c • basisCLM b) := by
    rw [hf0]
    exact hasMFDerivAt_collapse_zero hb c
  exact h2.comp (γ t) h1

theorem surjective_mfderiv_moveΦ {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b)
    {c : ℝ} (hc : c ≠ 0) {τ : ℝ → Fin m → EuclideanSpace ℝ (Fin m)}
    (hτ : ContDiff ℝ ∞ (fun t => basisCLM (τ t))) (hτi : ∀ t, LinearIndependent ℝ (τ t))
    {γ : ℝ → EuclideanSpace ℝ (Fin m)} (hγ : ContDiff ℝ ∞ γ) (t : ℝ) :
    Function.Surjective (mfderiv (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (moveΦ hb c τ γ) (γ t, t)) := by
  -- the full map is differentiable at `(γ t, t)`
  have hΦ := ((contMDiff_moveΦ hb c hτ hγ).mdifferentiableAt (by simp) (x := (γ t, t))).hasMFDerivAt
  -- the inclusion `s ↦ (s, t)`
  have hι : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (fun s : EuclideanSpace ℝ (Fin m) => (s, t)) (γ t)
      ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))).prod
        (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)) :=
    (hasMFDerivAt_id (γ t)).prodMk (hasMFDerivAt_const t (γ t))
  have hcomp := hΦ.comp (γ t) hι
  have hslice := hasMFDerivAt_moveΦ_slice hb c τ γ t
  have heq := hcomp.mfderiv.symm.trans hslice.mfderiv
  -- the slice derivative is surjective
  have hsc : Surjective (c • basisCLM b) := by
    intro y
    obtain ⟨x, hx⟩ := (basisCLM_bijective hb).2 (c⁻¹ • y)
    exact ⟨x, by rw [smul_apply, hx, smul_inv_smul₀ hc]⟩
  have hsurj : Surjective ((c • basisCLM b).comp (basisCLM (τ t))) := by
    rw [ContinuousLinearMap.coe_comp]
    exact hsc.comp (basisCLM_bijective (hτi t)).2
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  refine ⟨(x, 0), ?_⟩
  have hx' := congrArg (fun L => L x) heq
  exact hx'.trans hx

theorem moveΦ_congr_time {b : Fin m → EuclideanSpace ℝ (Fin m)} (hb : LinearIndependent ℝ b) (c : ℝ)
    {τ : ℝ → Fin m → EuclideanSpace ℝ (Fin m)} {γ : ℝ → EuclideanSpace ℝ (Fin m)} {t t' : ℝ}
    (h1 : τ t = τ t') (h2 : γ t = γ t') (s : EuclideanSpace ℝ (Fin m)) :
    moveΦ hb c τ γ (s, t) = moveΦ hb c τ γ (s, t') := by simp [moveΦ, h1, h2]

end Framed

end Milnor
