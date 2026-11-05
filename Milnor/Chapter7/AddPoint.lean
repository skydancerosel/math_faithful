import Milnor.Chapter7.Move
import Milnor.Chapter7.Reach

/-!
# Adding a framed point

Given a framed `0`-manifold `F`, a point `x_c ∉ F.N` and a frame `v` at `x_c`, there is a
framed `0`-manifold `F'` with `F'.N = F.N ∪ {x_c}`, the frames of `F` on `F.N` and the frame
`v` at `x_c`.  It is the Pontryagin manifold of the map obtained by gluing a stationary bump
(`moveΦ` with constant path) at `x_c` onto the Theorem-B map of `F`.

**No orientation of `M` is needed**: neither the statement nor the construction mentions a sign.
An orientation appeared in an earlier version only because the good ball and the dual tuple it uses
were stated with one; `exists_goodBall_free` and `exists_dualTuple` need none, so `exists_add_point`
carries no orientation binder at all.  The oriented `exists_framedSub_of_card` of
`Chapter7/Hopf.lean` calls it in that form.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} (hMc : IsCompact M) (hne : M.Nonempty)

/-- A bijective `basisCLM` is bounded below. -/
theorem exists_lower_bound_basisCLM {τ : Fin m → EuclideanSpace ℝ (Fin m)}
    (hτ : LinearIndependent ℝ τ) : ∃ μ : ℝ, 0 < μ ∧ ∀ z, μ * ‖z‖ ≤ ‖basisCLM τ z‖ := by
  set E : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m) :=
    ContinuousLinearEquiv.ofBijective (basisCLM τ)
      (LinearMap.ker_eq_bot.2 (basisCLM_bijective hτ).1)
      (LinearMap.range_eq_top.2 (basisCLM_bijective hτ).2) with hE
  set Kc : NNReal := ‖(E.symm : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))‖₊
  have hanti : AntilipschitzWith Kc E := E.antilipschitz
  refine ⟨(Kc + 1)⁻¹, by positivity, fun z => ?_⟩
  have h1 : ‖z‖ ≤ Kc * ‖E z‖ := by
    have := hanti.le_mul_dist z 0
    simpa [dist_zero_right] using this
  have hEz : E z = basisCLM τ z := rfl
  rw [← hEz]
  have h2 : 0 ≤ ‖E z‖ := norm_nonneg _
  rw [inv_mul_le_iff₀ (by positivity)]
  nlinarith

include hMc hne in
/-- **Adding a framed point.**  No orientation of `M`. -/
theorem exists_add_point (hm : 0 < m)
    (F : FramedSub hM 0 m) {x_c : M} (hx_c : x_c ∉ F.N)
    {v : Fin m → EuclideanSpace ℝ (Fin (K + 1))} (hvT : ∀ i, v i ∈ tangentM hM x_c)
    (hv : LinearIndependent ℝ v) :
    ∃ F' : FramedSub hM 0 m, F'.N = F.N ∪ {x_c} ∧
      (∀ i x (hx : x ∈ F.N) (hx' : x ∈ F'.N), F'.v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩) ∧
      (∀ i (hx' : x_c ∈ F'.N), F'.v i ⟨x_c, hx'⟩ = v i) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set φ := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x_c with hφdef
  -- a good ball around `x_c`
  obtain ⟨R, hR, hRt, hcl, -⟩ :=
    exists_goodBall_free x_c (P := F.N) F.finite_N hx_c isOpen_univ (mem_univ x_c)
  have hxU : x_c ∈ ballU hM x_c R := x_c_mem_ballU x_c hR
  -- the dual tuple of `v`
  obtain ⟨τ₀, hτ₀i, -, hc₀2, -⟩ := exists_dualTuple (mem_ballU.1 hxU).1 hvT hv
  obtain ⟨μ, hμ, hτμ⟩ := exists_lower_bound_basisCLM hτ₀i
  set τ : ℝ → Fin m → EuclideanSpace ℝ (Fin m) := fun _ => τ₀ with hτdef
  have hτ : ContDiff ℝ ∞ (fun t => basisCLM (τ t)) := by
    show ContDiff ℝ ∞ (fun _ : ℝ => basisCLM τ₀)
    exact contDiff_const
  have hτi : ∀ t, LinearIndependent ℝ (τ t) := fun _ => hτ₀i
  have hτμ' : ∀ t z, μ * ‖z‖ ≤ ‖basisCLM (τ t) z‖ := fun _ z => hτμ z
  set γ : ℝ → EuclideanSpace ℝ (Fin m) := fun _ => φ x_c with hγdef
  have hγ : ContDiff ℝ ∞ γ := by
    show ContDiff ℝ ∞ (fun _ : ℝ => φ x_c)
    exact contDiff_const
  have hγR : ∀ t, ‖γ t - φ x_c‖ < R / 4 := fun t => by
    simp only [hγdef, sub_self, norm_zero]; positivity
  -- the collapse basis and scale
  set b : Fin m → EuclideanSpace ℝ (Fin m) := fun i => EuclideanSpace.single i 1 with hbdef
  have hb : LinearIndependent ℝ b := linearIndependent_single
  have hR4 : 0 < μ * R / 2 := by positivity
  obtain ⟨c₁, hc₁, hc₁s⟩ := exists_scale_all hb hR4
  -- the Theorem-B map, supported away from the closed ball
  set W : Set M := (closure (ballU hM x_c R))ᶜ with hWdef
  have hW : IsOpen W := isClosed_closure.isOpen_compl
  have hNW : F.N ⊆ W := fun x hx hxc => hcl x hxc hx
  obtain ⟨k, hk, hkn, c, hc, hcb, hc₁c, hkF, Kc, hKc, hKcW, hkS⟩ :=
    exists_map_of_framedSub_subset hM hMc hne F b hb W hW hNW c₁
  have hsouth : ∀ z, μ * R / 2 / 2 ≤ ‖z‖ → collapse hb c z = south := hc₁s c hc₁c
  have hO : IsOpen Kcᶜ := hKc.isClosed.isOpen_compl
  have hOU : closure (ballU hM x_c R) \ ballU hM x_c R ⊆ Kcᶜ := by
    rintro z ⟨hz1, -⟩ hzK
    exact hKcW hzK hz1
  have hkO : ∀ z ∈ Kcᶜ, k z = south := fun z hz => hkS z hz
  have hkN : k ⁻¹' {north} = F.N := congrArg FramedSub.N hkF
  -- the glued map (time slice `0` of the stationary homotopy)
  set H := glueH hM x_c R (moveΦ hb c τ γ) k with hHdef
  have hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      ∞ H :=
    contMDiff_moveH (hM := hM) (x_c := x_c) hR hRt hb hsouth hμ rfl hτ hτμ' hγ hγR hk hO hOU hkO
  have hf0 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (fun x => H (x, 0)) := hH.comp (contMDiff_id.prodMk contMDiff_const)
  have hn0 : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (fun x => H (x, 0)) north :=
    isRegularValue_moveH_slice hR hRt hb hc hsouth hμ rfl hτ hτi hτμ' hγ hγR hkn hO hOU hkO 0
  have hφ0 : φ x_c = γ 0 := rfl
  have hpre0 := moveH_slice_preimage (hb := hb) (k := k) hc hτi 0 hxU hφ0
  rw [hkN] at hpre0
  have hN0 : (fun x => H (x, 0)) ⁻¹' {north} = F.N ∪ {x_c} := by
    rw [hpre0]
    ext x
    simp only [mem_union, Set.mem_sdiff, mem_singleton_iff]
    constructor
    · rintro (⟨hx, -⟩ | rfl)
      · exact Or.inl hx
      · exact Or.inr rfl
    · rintro (hx | rfl)
      · exact Or.inl ⟨hx, fun hU => hcl x (subset_closure hU) hx⟩
      · exact Or.inr rfl
  refine ⟨pontryagin hM hMc hne hf0 hn0 (zero_add m) (fun i => c • b i) hcb, hN0, ?_, ?_⟩
  · intro i x hx hx'
    have hxU' : x ∉ ballU hM x_c R := fun hU => hcl x (subset_closure hU) hx
    have hkx : k x = north := by rw [← mem_singleton_iff, ← mem_preimage, hkN]; exact hx
    have h1 := pontV_moveH_slice_of_notMem hMc hne (hb := hb) (k := k) hR hRt hsouth hμ rfl hτμ'
      hγR hO hOU hkO 0 hf0 x.2 hxU' hx' hkx (fun i => c • b i) i
    have h2 := FramedSub.v_congr hkF i ⟨x, hkx⟩
    simp only at h2
    exact h1.trans h2
  · intro i hx'
    exact pontV_moveH_slice_of_mem hMc hne (hb := hb) (k := k) hτ hγ 0 hf0 hn0 hxU hφ0 hx'
      hvT hc₀2 hcb i

end Framed

end Milnor
