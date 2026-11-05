import Milnor.Chapter7.ProdNbhd2
import Milnor.Chapter7.ProdNbhdM
import Milnor.Chapter7.PontFrame
import Milnor.Chapter7.Collapse
import Milnor.Chapter7.Clamp
import Milnor.Chapter7.ThmB
import Milnor.Chapter7.Deform
import Milnor.Chapter7.Scale

/-!
# Theorem B with control of the support

Given a framed submanifold `(N, v)` of `M`, the product neighbourhood theorem gives a
diffeomorphism `G : N × B_ε → V ⊆ M`; the map `f = collapse ∘ pr₂ ∘ G⁻¹` on `V`, `f = south`
elsewhere, is smooth, has `f⁻¹(north) = N`, `north` is a regular value, and the Pontryagin
framing `f^*(c • b)` is `v` (for a suitable `c > 0`, any basis `b`).
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

/-- Two framed submanifolds with the same underlying set and framing are equal. -/
theorem exists_map_of_framedSub_subset (F : FramedSub hM n p) (b : Fin p → EuclideanSpace ℝ (Fin p))
    (hb : LinearIndependent ℝ b) (W : Set M) (hW : IsOpen W) (hNW : F.N ⊆ W) (c₀ : ℝ) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ (f : M → Sph p) (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
      (hy : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f north)
      (c : ℝ) (hc : 0 < c) (hcb : LinearIndependent ℝ (fun i => c • b i)),
      c₀ ≤ c ∧ pontryagin hM hMc hne hf hy F.dim (fun i => c • b i) hcb = F ∧
        ∃ Kc : Set M, IsCompact Kc ∧ Kc ⊆ W ∧ ∀ z ∉ Kc, f z = south := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  by_cases hNe : Nonempty F.N
  swap
  · -- `N = ∅`: the constant map
    have hempty : F.N = ∅ := by
      rw [not_nonempty_iff] at hNe
      exact Set.eq_empty_of_isEmpty _
    have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun _ : M => (south : Sph p)) := contMDiff_const
    have hy : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun _ : M => (south : Sph p)) north := fun x hx => absurd hx south_ne_north
    have hc1 : (0 : ℝ) < max c₀ 1 := lt_max_of_lt_right one_pos
    have hcb : LinearIndependent ℝ (fun i => max c₀ 1 • b i) := by
      convert hb.units_smul (fun _ => Units.mk0 _ hc1.ne') using 1
      funext i
      simp [Pi.smul_apply', Units.smul_def]
    refine ⟨_, hf, hy, max c₀ 1, hc1, hcb, le_max_left _ _, ?_, ∅, isCompact_empty,
      empty_subset _, fun _ _ => rfl⟩
    apply FramedSub.ext'
    · show (fun _ : M => (south : Sph p)) ⁻¹' {north} = F.N
      rw [hempty]
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact south_ne_north
    · intro i x hx hx'
      rw [hempty] at hx'
      exact absurd hx' (notMem_empty x)
  -- the tube map
  obtain ⟨C, hC0, hC⟩ := exists_bound_v F
  set tε := Tub.tubε hM hMc hne with htε
  have htε0 : 0 < tε := Tub.tubε_pos hM hMc hne
  set a₀ : ℝ := tε / (8 * (p * C + 1)) with ha₀def
  have ha₀ : 0 < a₀ := by positivity
  obtain ⟨lam, hlam, hlam_id, hlam_b, -⟩ := exists_clamp (E := EuclideanSpace ℝ (Fin p)) ha₀ (le_refl (2 * a₀))
  have hbC : p * (2 * a₀ * C) < tε := by
    rw [ha₀def]
    have h1 : (p : ℝ) * (2 * (tε / (8 * (p * C + 1))) * C) = tε * (2 * p * C) / (8 * (p * C + 1)) := by
      field_simp
    rw [h1, div_lt_iff₀ (by positivity)]
    have hpc : (0 : ℝ) ≤ p * C := by positivity
    exact mul_lt_mul_of_pos_left (by nlinarith [hpc]) htε0
  have hmem : ∀ q, Gamb F lam q ∈ Tub.Nε hM hMc hne :=
    Gamb_mem_Nε hMc hne F hC hlam_b hC0.le hbC
  have hlam_ev : ∀ᶠ t in 𝓝 (0 : EuclideanSpace ℝ (Fin p)), lam t = t := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin p)) ha₀] with t ht
    exact hlam_id t (mem_ball_zero_iff.1 ht).le
  have hlam0 : lam 0 = 0 := hlam_ev.self_of_nhds
  set G := Gx hMc hne F lam with hGdef
  have hG : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ G := contMDiff_Gx hMc hne F hlam hmem
  have hbij0 := bijective_mfd_Gx_zero hMc hne F hlam hlam_ev hmem
  haveI : CompactSpace F.N := isCompact_iff_compactSpace.1 F.compact
  -- the injectivity radius
  obtain ⟨ε₁, hε₁, hb₁⟩ := PN.exists_ball_bijective hG univ isCompact_univ (fun x _ => hbij0 x)
  -- the tube can be kept inside `W`
  obtain ⟨δ, hδ, hδW⟩ := exists_tube_subset (W := G ⁻¹' W) (hW.preimage hG.continuous)
    (fun x => by
      show G (x, 0) ∈ W
      rw [hGdef, Gx_zero hMc hne F hlam0]; exact hNW x.2)
  obtain ⟨ε, hε, hεle₀, hinj⟩ := PN.exists_injOn hG univ isCompact_univ (ε₀ := min (min ε₁ a₀) δ)
    (lt_min (lt_min hε₁ ha₀) hδ) (fun x _ => hbij0 x) (Gx_zero_injective hMc hne F hlam0)
    (fun q q' _ _ hq _ => absurd (mem_univ q.1) hq)
  have hεle : ε ≤ min ε₁ a₀ := hεle₀.trans (min_le_left _ _)
  have hεδ : ε ≤ δ := hεle₀.trans (min_le_right _ _)
  have hinj' : InjOn G (PN.tube F.N p ε) := fun q hq q' hq' h => hinj q q' hq hq' h
  have hbijε : ∀ q ∈ PN.tube F.N p ε, Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) G q) := by
    rintro ⟨x, t⟩ hq
    exact hb₁ x (mem_univ _) t (lt_of_lt_of_le hq (hεle.trans (min_le_left _ _)))
  have hεa : ε ≤ a₀ := hεle.trans (min_le_right _ _)
  set V := G '' PN.tube F.N p ε with hVdef
  have hV : IsOpen V := PN.isOpen_image_tube hG hbijε
  -- the collapse map
  obtain ⟨c, hc₀, hc, hcs⟩ := exists_scale_ge hb hε c₀
  set π' := collapse hb c with hπ'
  -- the map
  set f : M → Sph p := fun z => if z ∈ V then π' (PN.Ginv G ε z).2 else south with hfdef
  have hf_of_mem : ∀ z ∈ V, f z = π' (PN.Ginv G ε z).2 := fun z hz => by simp [hfdef, hz]
  have hf_of_not : ∀ z ∉ V, f z = south := fun z hz => by simp [hfdef, hz]
  -- the closed core
  set Cl := G '' (univ ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin p)) (ε / 2)) with hCl
  have hClc : IsCompact Cl :=
    (isCompact_univ.prod (isCompact_closedBall _ _)).image hG.continuous
  have hVW : V ⊆ W := by
    rintro _ ⟨q, hq, rfl⟩
    exact hδW q.1 q.2 (lt_of_lt_of_le hq hεδ)
  have hClV : Cl ⊆ V := by
    rintro _ ⟨q, ⟨-, hq⟩, rfl⟩
    exact ⟨q, (mem_closedBall_zero_iff.1 hq).trans_lt (by linarith), rfl⟩
  have hf_south : ∀ z ∉ Cl, f z = south := by
    intro z hz
    by_cases hzV : z ∈ V
    · rw [hf_of_mem z hzV]
      obtain ⟨q, hq, rfl⟩ := hzV
      rw [PN.Ginv_G hinj' hq]
      apply hcs
      by_contra hlt
      push_neg at hlt
      exact hz ⟨q, ⟨mem_univ _, mem_closedBall_zero_iff.2 hlt.le⟩, rfl⟩
    · exact hf_of_not z hzV
  -- smoothness
  have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f := by
    intro z
    by_cases hz : z ∈ V
    · have h1 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
          (fun z' => π' (PN.Ginv G ε z').2) z := by
        have hsnd : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
            𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun q : F.N × EuclideanSpace ℝ (Fin p) => q.2) :=
          contMDiff_snd
        exact ((contMDiff_collapse hb c).comp hsnd).contMDiffAt.comp z
          (PN.contMDiffAt_Ginv hG hbijε hinj' hz)
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hV.mem_nhds hz] with z' hz'
      exact hf_of_mem z' hz'
    · have hzC : z ∈ Clᶜ := fun h => hz (hClV h)
      have h1 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
          (fun _ : M => (south : Sph p)) z := contMDiffAt_const
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hClc.isClosed.isOpen_compl.mem_nhds hzC] with z' hz'
      exact hf_south z' hz'
  -- the level set
  have hpre : f ⁻¹' {north} = F.N := by
    ext z
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro hz
      by_cases hzV : z ∈ V
      · rw [hf_of_mem z hzV, hπ', collapse_eq_north_iff hb hc.ne'] at hz
        have h1 := PN.G_Ginv (G := G) (ε := ε) hzV
        have h2 : PN.Ginv G ε z = ((PN.Ginv G ε z).1, 0) := Prod.ext rfl hz
        rw [h2, hGdef, Gx_zero hMc hne F hlam0] at h1
        rw [← h1]
        exact ((PN.Ginv G ε z).1).2
      · rw [hf_of_not z hzV] at hz
        exact absurd hz south_ne_north
    · intro hz
      have hq : ((⟨z, hz⟩ : F.N), (0 : EuclideanSpace ℝ (Fin p))) ∈ PN.tube F.N p ε := by
        show ‖(0 : EuclideanSpace ℝ (Fin p))‖ < ε
        rw [norm_zero]; exact hε
      have hzV : z ∈ V := ⟨_, hq, by rw [hGdef, Gx_zero hMc hne F hlam0]⟩
      rw [hf_of_mem z hzV]
      have h1 : G (⟨z, hz⟩, 0) = z := by rw [hGdef, Gx_zero hMc hne F hlam0]
      have h2 : PN.Ginv G ε z = (⟨z, hz⟩, 0) := by
        have h3 : PN.Ginv G ε (G (⟨z, hz⟩, 0)) = (⟨z, hz⟩, 0) := PN.Ginv_G hinj' hq
        rw [h1] at h3
        exact h3
      rw [h2]
      exact collapse_zero hb c
  -- the derivative of `f` along the framing
  have hAv : ∀ (x : F.N) (i : Fin p), At hM hMc hne f north x.1.1 (F.v i x) = c • b i := by
    intro x i
    have hxN : x.1 ∈ f ⁻¹' {north} := by rw [hpre]; exact x.2
    have hfx : f x.1 = north := hxN
    have hsrc : f ⟨x.1.1, x.1.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north).source := by
      rw [Subtype.coe_eta, hfx]; exact mem_extChartAt_source north
    have hxW : x.1.1 ∈ Wt hM hMc hne f north := mem_Wt_of_mem hM hMc hne x.1.2 hsrc
    -- first description of the derivative along the line
    have hd1 : HasDerivAt (fun s : ℝ => Ft hM hMc hne f north (x.1.1 + s • F.v i x))
        (At hM hMc hne f north x.1.1 (F.v i x)) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => x.1.1 + s • F.v i x) (F.v i x) 0 := by
        have := (hasDerivAt_id (0 : ℝ)).smul_const (F.v i x)
        simpa using (this.const_add x.1.1)
      have h2 : HasFDerivAt (Ft hM hMc hne f north) (At hM hMc hne f north x.1.1)
          (x.1.1 + (0 : ℝ) • F.v i x) := by
        rw [zero_smul, add_zero]; exact hasFDerivAt_Ft hM hMc hne hf hxW
      exact h2.comp_hasDerivAt (0 : ℝ) h1
    -- second description: through the tube map
    have hd2 : HasDerivAt (fun s : ℝ => Ft hM hMc hne f north (x.1.1 + s • F.v i x))
        (c • basisCLM b (EuclideanSpace.single i 1)) 0 := by
      have h0 := hasDerivAt_chart_collapse hb c (EuclideanSpace.single i (1 : ℝ))
      refine h0.congr_of_eventuallyEq ?_
      have hev : ∀ᶠ s : ℝ in 𝓝 0, |s| < min a₀ ε := by
        have := Metric.ball_mem_nhds (0 : ℝ) (lt_min ha₀ hε)
        filter_upwards [this] with s hs
        simpa [Real.dist_eq] using hs
      filter_upwards [hev] with s hs
      have hs1 : ‖s • EuclideanSpace.single i (1 : ℝ)‖ = |s| := by
        rw [norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      -- the point `x + s v_i` is `G (x, s e_i)`
      have hG : G (x, s • EuclideanSpace.single i (1 : ℝ)) = Tub.tubr hM hMc hne (x.1.1 + s • F.v i x) := by
        rw [hGdef]
        unfold Gx Gamb
        congr 1
        rw [hlam_id _ (by rw [hs1]; exact (hs.trans_le (min_le_left _ _)).le)]
        simp [emb, EuclideanSpace.single_apply, Finset.sum_ite_eq']
      have hq : (x, s • EuclideanSpace.single i (1 : ℝ)) ∈ PN.tube F.N p ε := by
        show ‖s • EuclideanSpace.single i (1 : ℝ)‖ < ε
        rw [hs1]; exact hs.trans_le (min_le_right _ _)
      have hzV : Tub.tubr hM hMc hne (x.1.1 + s • F.v i x) ∈ V := ⟨_, hq, hG⟩
      show Ft hM hMc hne f north (x.1.1 + s • F.v i x) =
        extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north (collapse hb c (s • EuclideanSpace.single i 1))
      unfold Ft
      rw [hf_of_mem _ hzV, ← hG, PN.Ginv_G hinj' hq]
    have := hd1.unique hd2
    rw [this, basisCLM_single]
  -- `north` is a regular value
  have hy : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f north := by
    intro x hx
    have hxN : x ∈ F.N := by rw [← hpre]; exact hx
    have hsrc : f ⟨x.1, x.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) north).source := by
      rw [Subtype.coe_eta]
      have : f x = north := hx
      rw [this]; exact mem_extChartAt_source north
    have hsurj : Surjective (At hM hMc hne f north x.1) := by
      have hcb : LinearIndependent ℝ (fun i => c • b i) := by
        convert hb.units_smul (fun _ => Units.mk0 c hc.ne') using 1
        funext i
        simp [Pi.smul_apply', Units.smul_def]
      have hspan : Submodule.span ℝ (range (fun i => c • b i)) = ⊤ :=
        hcb.span_eq_top_of_card_eq_finrank' (by simp)
      have hle : Submodule.span ℝ (range (fun i => c • b i)) ≤
          LinearMap.range (At hM hMc hne f north x.1 :
            EuclideanSpace ℝ (Fin (K + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact ⟨F.v i ⟨x, hxN⟩, hAv ⟨x, hxN⟩ i⟩
      rw [hspan, top_le_iff] at hle
      exact LinearMap.range_eq_top.1 hle
    exact isRegularPoint_of_surjective_At hM hMc hne hf x.2 hsrc hsurj
  have hcb : LinearIndependent ℝ (fun i => c • b i) := by
    convert hb.units_smul (fun _ => Units.mk0 c hc.ne') using 1
    funext i
    simp [Pi.smul_apply', Units.smul_def]
  refine ⟨f, hf, hy, c, hc, hcb, hc₀, ?_, Cl, hClc, hClV.trans hVW, hf_south⟩
  refine FramedSub.ext' hM hpre ?_
  intro i x hx hx'
  show pontV hM hMc hne f north (fun i => c • b i) i ⟨x, hx⟩ = F.v i ⟨x, hx'⟩
  refine pontV_eq_of hM hMc hne hf hy F.dim ⟨x, hx⟩ (F.tangent i ⟨x, hx'⟩) ?_ _ i (hAv ⟨x, hx'⟩ i)
  intro w hw
  rw [tangentN_congr hM hpre (isSliceSubmanifold_level hM hf hy F.dim) F.hN ⟨x, hx⟩] at hw
  exact F.normal i ⟨x, hx'⟩ w hw

end Framed

end Milnor
