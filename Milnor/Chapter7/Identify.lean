import Milnor.Chapter7.ThmB

/-!
# Identifying a Pontryagin manifold from the collapse form along the framing

If `k : M → Sᵖ` is smooth, `k⁻¹(north) = N`, and along each framing line `k(r(x + s vᵢ(x))) =
collapse (s eᵢ)`, then the Pontryagin manifold of `k` at `north` (with basis `c • b`) is
exactly the framed submanifold `(N, v)`.  This is the last part of the proof of Theorem B,
factored out so that it applies to both ends of a framed cobordism.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty)
  {n p : ℕ}

/-- **Identification of the Pontryagin manifold.** -/
theorem pontryagin_eq_of_collapse (F : FramedSub hM n p) {k : M → Sph p}
    (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ k)
    (hkN : k ⁻¹' {north} = F.N) {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    {c : ℝ} (hc : 0 < c) {ε' : ℝ} (hε' : 0 < ε')
    (hline : ∀ (x : F.N) (i : Fin p) (s : ℝ), |s| < ε' →
      k (Tub.tubr hM hMc hne (x.1.1 + s • F.v i x)) = collapse hb c (s • EuclideanSpace.single i 1)) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ (hy : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) k north)
      (hcb : LinearIndependent ℝ (fun i => c • b i)),
      pontryagin hM hMc hne hk hy F.dim (fun i => c • b i) hcb = F := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  -- the derivative of `k` along the framing
  have hAv : ∀ (x : F.N) (i : Fin p), At hM hMc hne k north x.1.1 (F.v i x) = c • b i := by
    intro x i
    have hxN : x.1 ∈ k ⁻¹' {north} := by rw [hkN]; exact x.2
    have hfx : k x.1 = north := hxN
    have hsrc : k ⟨x.1.1, x.1.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north).source := by
      rw [Subtype.coe_eta, hfx]; exact mem_extChartAt_source north
    have hxW : x.1.1 ∈ Wt hM hMc hne k north := mem_Wt_of_mem hM hMc hne x.1.2 hsrc
    have hd1 : HasDerivAt (fun s : ℝ => Ft hM hMc hne k north (x.1.1 + s • F.v i x))
        (At hM hMc hne k north x.1.1 (F.v i x)) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => x.1.1 + s • F.v i x) (F.v i x) 0 := by
        have := (hasDerivAt_id (0 : ℝ)).smul_const (F.v i x)
        simpa using (this.const_add x.1.1)
      have h2 : HasFDerivAt (Ft hM hMc hne k north) (At hM hMc hne k north x.1.1)
          (x.1.1 + (0 : ℝ) • F.v i x) := by
        rw [zero_smul, add_zero]; exact hasFDerivAt_Ft hM hMc hne hk hxW
      exact h2.comp_hasDerivAt (0 : ℝ) h1
    have hd2 : HasDerivAt (fun s : ℝ => Ft hM hMc hne k north (x.1.1 + s • F.v i x))
        (c • basisCLM b (EuclideanSpace.single i 1)) 0 := by
      have h0 := hasDerivAt_chart_collapse hb c (EuclideanSpace.single i (1 : ℝ))
      refine h0.congr_of_eventuallyEq ?_
      have hev : ∀ᶠ s : ℝ in 𝓝 0, |s| < ε' := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε'] with s hs
        simpa [Real.dist_eq] using hs
      filter_upwards [hev] with s hs
      show Ft hM hMc hne k north (x.1.1 + s • F.v i x) =
        extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north (collapse hb c (s • EuclideanSpace.single i 1))
      unfold Ft
      rw [hline x i s hs]
    have := hd1.unique hd2
    rw [this, basisCLM_single]
  have hcb : LinearIndependent ℝ (fun i => c • b i) := by
    convert hb.units_smul (fun _ => Units.mk0 c hc.ne') using 1
    funext i
    simp [Pi.smul_apply', Units.smul_def]
  -- `north` is a regular value
  have hy : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) k north := by
    intro x hx
    have hxN : x ∈ F.N := by rw [← hkN]; exact hx
    have hsrc : k ⟨x.1, x.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north).source := by
      rw [Subtype.coe_eta]
      have : k x = north := hx
      rw [this]; exact mem_extChartAt_source north
    have hsurj : Surjective (At hM hMc hne k north x.1) := by
      have hspan : Submodule.span ℝ (range (fun i => c • b i)) = ⊤ :=
        hcb.span_eq_top_of_card_eq_finrank' (by simp)
      have hle : Submodule.span ℝ (range (fun i => c • b i)) ≤
          LinearMap.range (At hM hMc hne k north x.1 :
            EuclideanSpace ℝ (Fin (K + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact ⟨F.v i ⟨x, hxN⟩, hAv ⟨x, hxN⟩ i⟩
      rw [hspan, top_le_iff] at hle
      exact LinearMap.range_eq_top.1 hle
    exact isRegularPoint_of_surjective_At hM hMc hne hk x.2 hsrc hsurj
  refine ⟨hy, hcb, ?_⟩
  refine FramedSub.ext' hM hkN ?_
  intro i x hx hx'
  show pontV hM hMc hne k north (fun i => c • b i) i ⟨x, hx⟩ = F.v i ⟨x, hx'⟩
  refine pontV_eq_of hM hMc hne hk hy F.dim ⟨x, hx⟩ (F.tangent i ⟨x, hx'⟩) ?_ _ i (hAv ⟨x, hx'⟩ i)
  intro w hw
  rw [tangentN_congr hM hkN (isSliceSubmanifold_level hM hk hy F.dim) F.hN ⟨x, hx⟩] at hw
  exact F.normal i ⟨x, hx'⟩ w hw

end Framed

end Milnor
