import Milnor.Chapter6.Region

/-!
# Hopf's lemma (Milnor, Lemma 3, p. 35)

If a vector field `v` on a compact region `X = {G ≥ 0} ⊆ ℝⁿ⁺¹` with isolated zeros points
outward along the boundary (`dG(v) < 0` on `∂X`), then the sum of the indices of `v` at its
zeros equals the degree of the Gauss map `∂X → Sⁿ` (the outward unit normal `-∇G/|∇G|`), a
number depending only on `X`.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

section gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem fderiv_apply_eq_inner_gradient (G : E → ℝ) (x v : E) :
    fderiv ℝ G x v = ⟪gradient G x, v⟫ := by
  unfold gradient; rw [InnerProductSpace.toDual_symm_apply]

theorem contMDiff_gradient {G : E → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (gradient G) := by
  rw [contMDiff_iff_contDiff]
  exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp (hG.fderiv_right (by simp))

theorem gradient_ne_zero_of_fderiv_ne_zero {G : E → ℝ} {x : E} (h : fderiv ℝ G x ≠ 0) :
    gradient G x ≠ 0 := by
  intro h0
  apply h
  ext v
  rw [fderiv_apply_eq_inner_gradient, h0, inner_zero_left]; rfl

end gradient

namespace Sphere

variable {n k : ℕ}

/-- **Hopf's lemma** (Milnor, Lemma 3, p. 35), in the form: if the smooth vector field `v` on
`ℝⁿ⁺¹` points outward along `∂X = G⁻¹(0)` (`dG(v) < 0` there) and its zeros in the compact region
`X = {G ≥ 0}` are the centres `zᵢ` of disjoint closed `ε`-balls inside `{G > 0}`, then the index
sum equals the degree of the Gauss map `x ↦ -∇G(x)/|∇G(x)|` of `∂X`.  (Orientation conventions
as in `sum_indexAt_eq_deg`.) -/
theorem hopf_lemma (hn : 0 < n)
    {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG : ContDiff ℝ ∞ G)
    (h0 : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) G 0)
    (hX : IsCompact {x | 0 ≤ G x}) {z : Fin k → EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ}
    (hε : 0 < ε) (hzin : ∀ i x, dist x (z i) ≤ ε → 0 < G x)
    (hdisj : ∀ i j, i ≠ j → 2 * ε < dist (z i) (z j))
    (hzero : ∀ x, 0 ≤ G x → v x = 0 → ∃ i, x = z i)
    (hout : ∀ x, G x = 0 → fderiv ℝ G x (v x) < 0) :
    letI := (isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ)
      hG.contMDiff h0).chartedSpace
    ∑ i, indexAt v (z i) ε =
      deg ((levelOrientM hE hZ (Orient.const (finBasisOfFinrankEq ℝ _ hE).orientation)
          hG.contMDiff h0).neg hZ)
        (sphOr n) (fun q : G ⁻¹' {0} => nv0 (-gradient G q.1)) := by
  have hS := isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ)
    hG.contMDiff h0
  letI := hS.chartedSpace
  haveI := hS.isManifold
  haveI : PreconnectedSpace (Sph n) := preconnectedSpace hn
  haveI : CompactSpace (G ⁻¹' {0}) := isCompact_iff_compactSpace.1
    (hX.of_isClosed_subset (isClosed_singleton.preimage hG.continuous)
      (fun x hx => le_of_eq (mem_singleton_iff.1 hx).symm))
  rw [sum_indexAt_eq_deg hn hv hG.contMDiff h0 hX hε hzin hdisj hzero]
  -- the homotopy from `v` to `-∇G` along `∂X`
  set ρ : ℝ → ℝ := Real.smoothTransition with hρ
  set w : G ⁻¹' {0} × ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun p => (1 - ρ p.2) • v p.1.1 + ρ p.2 • (-gradient G p.1.1) with hw
  have hdG : ∀ q : G ⁻¹' {0}, fderiv ℝ G q.1 ≠ 0 := fun q h => by
    have hs : Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) G q.1) :=
      h0 q.1 q.2
    have : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) G q.1 = fderiv ℝ G q.1 :=
      mfderiv_eq_fderiv
    rw [this, h] at hs
    obtain ⟨u, hu⟩ := hs 1
    simp at hu
  have hwne : ∀ p, w p ≠ 0 := by
    rintro ⟨q, t⟩ hw0
    have h1 : fderiv ℝ G q.1 (w (q, t)) < 0 := by
      simp only [w, map_add, map_smul, map_neg, smul_eq_mul]
      have ha := hout q.1 q.2
      have hb : 0 < fderiv ℝ G q.1 (gradient G q.1) := by
        rw [fderiv_apply_eq_inner_gradient, real_inner_self_eq_norm_sq]
        exact pow_pos (norm_pos_iff.2 (gradient_ne_zero_of_fderiv_ne_zero (hdG q))) 2
      have hρ0 := Real.smoothTransition.nonneg t
      have hρ1 := Real.smoothTransition.le_one t
      rcases le_or_gt (ρ t) (1 / 2) with h | h
      · nlinarith
      · nlinarith
    rw [hw0, map_zero] at h1
    exact lt_irrefl _ h1
  have hws : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ w := by
    have hρs : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : G ⁻¹' {0} × ℝ => ρ p.2) :=
      (Real.smoothTransition.contDiff.contMDiff).comp contMDiff_snd
    have h1s : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : G ⁻¹' {0} × ℝ => 1 - ρ p.2) := contMDiff_const.sub hρs
    have hvs : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ (fun p : G ⁻¹' {0} × ℝ => v p.1.1) :=
      hv.comp (hS.contMDiff_val.comp contMDiff_fst)
    have hgs : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ (fun p : G ⁻¹' {0} × ℝ => -gradient G p.1.1) :=
      ((contMDiff_gradient hG).comp (hS.contMDiff_val.comp contMDiff_fst)).neg
    exact (h1s.smul hvs).add (hρs.smul hgs)
  have hF' := deg_eq_of_homotopy hZ hZ
    ((levelOrientM hE hZ (Orient.const (finBasisOfFinrankEq ℝ _ hE).orientation) hG.contMDiff h0).neg hZ)
    (sphOr n) (contMDiff_nv0_comp hws hwne)
  have e0 : (fun q : G ⁻¹' {0} => nv0 (w (q, 0))) = fun q => nv0 (v q.1) := by
    funext q; simp [w, ρ, Real.smoothTransition.zero]
  have e1 : (fun q : G ⁻¹' {0} => nv0 (w (q, 1))) = fun q => nv0 (-gradient G q.1) := by
    funext q; simp [w, ρ, Real.smoothTransition.one]
  rw [e0, e1] at hF'
  exact hF'

end Sphere

end Milnor
