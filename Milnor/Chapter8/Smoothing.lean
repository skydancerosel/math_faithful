import Milnor.Chapter8.Approx

/-!
# Problems 4 and 5: smoothing maps into spheres, and maps from lower-dimensional manifolds

Let `M ⊆ ℝᴷ⁺¹` be a compact submanifold of dimension `m`.

* **Problem 4.** Every continuous map `M → Sᵖ` is uniformly approximated by smooth maps: approximate
  it by a smooth map into `ℝᵖ⁺¹` (Stone–Weierstrass) and normalize.  Two smooth maps `M → Sᵖ`
  which are continuously homotopic are smoothly homotopic: approximate the homotopy, viewed as a
  continuous map on the compact set `M × [0,1] ⊆ ℝᴷ⁺¹ × ℝ`, within `1/4` by a smooth map `Q`, and
  normalize `(x, t) ↦ Q(x, σ t)` with `σ` a smooth transition from `0` to `1`.  Its ends are within
  distance `< 2` of the given maps, which are therefore smoothly homotopic to them (Problem 3).
* **Problem 5.** If `m < p`, every map `M → Sᵖ` is homotopic to a constant.  For a smooth map `f`
  a regular value `y` (Brown) cannot be a value, since the derivative `ℝᵐ → ℝᵖ` cannot be onto;
  then `f` is contracted to the constant `-y` along straight lines in stereographic coordinates
  from `y`.  A continuous map is homotopic to a smooth one by Problems 4 and 3.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

open Sphere

namespace Problems

/-! ### Problem 5, smooth form -/

section Contract

variable {E : Type} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [SecondCountableTopology X]

/-- A smooth map from a manifold of dimension `m < p` into `Sᵖ` misses a point. -/
theorem exists_notMem_range_of_lt {m p : ℕ} (hE : finrank ℝ E = m) (hmp : m < p) {f : X → Sph p}
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f) : ∃ y : Sph p, ∀ x, f x ≠ y := by
  have : Nonempty (Sph p) := ⟨sphPt⟩
  obtain ⟨y, hy⟩ := (dense_regularValues hf).nonempty
  refine ⟨y, fun x hx => ?_⟩
  have hsurj : Surjective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x) := hy x hx
  let L : E →L[ℝ] EuclideanSpace ℝ (Fin p) := mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x
  have hL : LinearMap.range (L : E →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) = ⊤ :=
    LinearMap.range_eq_top.2 hsurj
  have h1 := LinearMap.finrank_range_le (L : E →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
  rw [hL, finrank_top, finrank_euclideanSpace_fin, hE] at h1
  omega

/-- **Problem 5, smooth form**: for any second countable boundaryless manifold of dimension
`m < p`, every smooth map into `Sᵖ` is smoothly homotopic to a constant. -/
theorem exists_smoothHomotopic_const_of_lt {m p : ℕ} (hE : finrank ℝ E = m) (hmp : m < p)
    {f : X → Sph p} (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f) :
    ∃ c : Sph p, SmoothHomotopic I 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f (fun _ => c) := by
  obtain ⟨y, hny⟩ := exists_notMem_range_of_lt hE hmp hf
  have hlt : ∀ x, ⟪(f x).1, y.1⟫ < 1 := fun x => inner_lt_one_of_ne (hny x)
  -- the straight-line contraction to `0` in stereographic coordinates from `y`
  obtain ⟨Hamb, hHamb⟩ : ∃ Hamb : X × ℝ → EuclideanSpace ℝ (Fin (p + 1)), ∀ q,
      Hamb q = stereoInv y ((1 - Real.smoothTransition q.2) • stereo y (f q.1).1) :=
    ⟨_, fun _ => rfl⟩
  have hinner : ∀ q : X × ℝ,
      ⟪(1 - Real.smoothTransition q.2) • stereo y (f q.1).1, y.1⟫ = 0 := fun q => by
    rw [real_inner_smul_left, inner_stereo_y, mul_zero]
  have hmem : ∀ q, Hamb q ∈ Sph p := fun q => by rw [hHamb]; exact stereoInv_mem y (hinner q)
  have hsmooth : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) ∞ Hamb := by
    have hfun :
        Hamb = fun q => stereoInv y ((1 - Real.smoothTransition q.2) • stereo y (f q.1).1) :=
      funext hHamb
    rw [hfun]
    intro q
    have hval : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) ∞
        (fun q : X × ℝ => (f q.1).1) :=
      contMDiff_val.comp (hf.comp contMDiff_fst)
    have hs : ContMDiffAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) ∞
        (fun q : X × ℝ => stereo y (f q.1).1) q :=
      ContMDiffAt.comp (g := stereo y) (f := fun q : X × ℝ => (f q.1).1) q
        (contDiffAt_stereo y (hlt q.1)).contMDiffAt (hval q)
    have hσ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : X × ℝ => 1 - Real.smoothTransition q.2) :=
      contMDiff_const.sub ((Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp contMDiff_snd)
    exact (contDiff_stereoInv y).contMDiff.contMDiffAt.comp q ((hσ q).smul hs)
  refine ⟨⟨stereoInv y 0, stereoInv_mem y (by simp)⟩, fun q => ⟨Hamb q, hmem q⟩,
    (sphS p).contMDiff_codRestrict hsmooth hmem, fun x => ?_, fun x => ?_⟩
  · apply Subtype.ext
    change Hamb (x, 0) = (f x).1
    rw [hHamb]
    simp only [Real.smoothTransition.zero, sub_zero, one_smul]
    exact stereoInv_stereo (hny x)
  · apply Subtype.ext
    change Hamb (x, 1) = stereoInv y 0
    rw [hHamb]
    simp only [Real.smoothTransition.one, sub_self, zero_smul]

end Contract

/-! ### Compact submanifolds of `ℝᴷ⁺¹` -/

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M)

/-- **Problem 4, first part.** Every continuous map from a compact manifold to `Sᵖ` can be
uniformly approximated by a smooth map. -/
theorem exists_smooth_approx (hMc : IsCompact M) {p : ℕ} (G : C(M, Sph p)) {ε : ℝ} (hε : 0 < ε) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ f : M → Sph p, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f ∧
      ∀ x, ‖(f x).1 - (G x).1‖ < ε := by
  let _ := hM.chartedSpace
  have _ := hM.isManifold
  classical
  -- `G`, extended by `0`, is continuous on the compact set `M`
  obtain ⟨G', hG'⟩ : ∃ G' : EuclideanSpace ℝ (Fin (K + 1)) → EuclideanSpace ℝ (Fin (p + 1)),
      ∀ x, G' x = if hx : x ∈ M then (G ⟨x, hx⟩).1 else 0 := ⟨_, fun _ => rfl⟩
  have hG'M : ∀ x : M, G' x.1 = (G x).1 := fun x => by rw [hG', dif_pos x.2]
  have hG'c : ContinuousOn G' M := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : M.domRestrict G' = fun x : M => (G x).1 := funext hG'M
    rw [this]
    exact continuous_subtype_val.comp G.continuous
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (ε / 2) (1 / 2) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact lt_min (half_pos hε) (by norm_num)
  have hδε : 2 * δ ≤ ε := by rw [hδ]; linarith [min_le_left (ε / 2) (1 / 2)]
  have hδ1 : δ ≤ 1 / 2 := by rw [hδ]; exact min_le_right _ _
  obtain ⟨Q, hQ, hQG⟩ := exists_contDiff_approx_of_isCompact hMc hG'c hδpos
  have hQx : ∀ x : M, ‖Q x.1 - (G x).1‖ < δ := fun x => by rw [← hG'M x]; exact hQG x.1 x.2
  have hne : ∀ x : M, Q x.1 ≠ 0 := by
    intro x h0
    have h := hQx x
    rw [h0, zero_sub, norm_neg, norm_sph] at h
    linarith
  refine ⟨fun x => nv0 (Q x.1),
    contMDiff_nv0_comp (w := fun x : M => Q x.1) (hQ.contMDiff.comp hM.contMDiff_val) hne,
    fun x => ?_⟩
  calc ‖(nv0 (Q x.1)).1 - (G x).1‖ ≤ 2 * ‖Q x.1 - (G x).1‖ := norm_nv0_sub_le (G x) (Q x.1) (hne x)
    _ < 2 * δ := by linarith [hQx x]
    _ ≤ ε := hδε

/-- **Problem 4, second part.** Two smooth maps from a compact manifold to `Sᵖ` which are
continuously homotopic are smoothly homotopic. -/
theorem smoothHomotopic_of_homotopic (hMc : IsCompact M) {p : ℕ} {f g : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g)
    (h : letI := hM.chartedSpace;
      (⟨f, hf.continuous⟩ : C(M, Sph p)).Homotopic ⟨g, hg.continuous⟩) :
    letI := hM.chartedSpace;
    SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f g := by
  let _ := hM.chartedSpace
  have _ := hM.isManifold
  classical
  obtain ⟨H⟩ := h
  -- the homotopy as a function on the compact set `M × [0,1] ⊆ ℝᴷ⁺¹ × ℝ`
  obtain ⟨G', hG'⟩ : ∃ G' : EuclideanSpace ℝ (Fin (K + 1)) × ℝ → EuclideanSpace ℝ (Fin (p + 1)),
      ∀ q, G' q = if hq : q.1 ∈ M ∧ q.2 ∈ Icc (0 : ℝ) 1 then (H (⟨q.2, hq.2⟩, ⟨q.1, hq.1⟩)).1
        else 0 := ⟨_, fun _ => rfl⟩
  have hG'S : ∀ (x : M) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1), G' (x.1, t) = (H (⟨t, ht⟩, x)).1 :=
    fun x t ht => by rw [hG', dif_pos ⟨x.2, ht⟩]
  have hSc : IsCompact (M ×ˢ Icc (0 : ℝ) 1) := hMc.prod isCompact_Icc
  have hG'c : ContinuousOn G' (M ×ˢ Icc (0 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (M ×ˢ Icc (0 : ℝ) 1).domRestrict G' = fun q : ↥(M ×ˢ Icc (0 : ℝ) 1) =>
        (H (⟨q.1.2, (Set.mem_prod.1 q.2).2⟩, ⟨q.1.1, (Set.mem_prod.1 q.2).1⟩)).1 := by
      funext q
      exact hG'S ⟨q.1.1, (Set.mem_prod.1 q.2).1⟩ q.1.2 (Set.mem_prod.1 q.2).2
    rw [this]
    refine continuous_subtype_val.comp (H.continuous.comp ?_)
    exact ((continuous_snd.comp continuous_subtype_val).subtype_mk _).prodMk
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _)
  obtain ⟨Q, hQ, hQG⟩ :=
    exists_contDiff_approx_of_isCompact hSc hG'c (by norm_num : (0 : ℝ) < 1 / 4)
  -- the smooth homotopy `(x, t) ↦ nv0 (Q (x, σ t))`
  have hσ01 : ∀ t : ℝ, Real.smoothTransition t ∈ Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hQM : ∀ (x : M) (t : ℝ),
      ‖Q (x.1, Real.smoothTransition t) - (H (⟨_, hσ01 t⟩, x)).1‖ < 1 / 4 := by
    intro x t
    rw [← hG'S x _ (hσ01 t)]
    exact hQG _ (Set.mem_prod.2 ⟨x.2, hσ01 t⟩)
  have hne : ∀ q : M × ℝ, Q (q.1.1, Real.smoothTransition q.2) ≠ 0 := by
    intro q h0
    have h := hQM q.1 q.2
    rw [h0, zero_sub, norm_neg, norm_sph] at h
    norm_num at h
  have hw : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin m))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (p + 1))) ∞
      (fun q : M × ℝ => Q (q.1.1, Real.smoothTransition q.2)) := by
    have h1 : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin m))).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ (fun q : M × ℝ => q.1.1) :=
      hM.contMDiff_val.comp contMDiff_fst
    have h2 : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin m))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : M × ℝ => Real.smoothTransition q.2) :=
      (Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp contMDiff_snd
    exact hQ.contMDiff.comp (h1.prodMk_space h2)
  obtain ⟨Ht, hHt⟩ : ∃ Ht : M × ℝ → Sph p,
      ∀ q, Ht q = nv0 (Q (q.1.1, Real.smoothTransition q.2)) := ⟨_, fun _ => rfl⟩
  have hHts : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin m))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ Ht := by
    have hfun : Ht = fun q => nv0 (Q (q.1.1, Real.smoothTransition q.2)) := funext hHt
    rw [hfun]
    exact contMDiff_nv0_comp hw hne
  -- its ends are near `f` and `g`
  have hend : ∀ (t : ℝ) (k : M → Sph p), (∀ x, H (⟨_, hσ01 t⟩, x) = k x) →
      ∀ x, ‖(k x).1 - (Ht (x, t)).1‖ < 2 := by
    intro t k hk x
    have h1 := hQM x t
    rw [hk x] at h1
    have h2 := norm_nv0_sub_le (k x) _ (hne (x, t))
    rw [norm_sub_rev, hHt]
    change ‖(nv0 (Q (x.1, Real.smoothTransition t))).1 - (k x).1‖ < 2
    linarith
  have hH0 : ∀ x, H (⟨_, hσ01 0⟩, x) = f x := fun x => by
    have : (⟨_, hσ01 0⟩ : unitInterval) = 0 := Subtype.ext Real.smoothTransition.zero
    rw [this, H.apply_zero]
    rfl
  have hH1 : ∀ x, H (⟨_, hσ01 1⟩, x) = g x := fun x => by
    have : (⟨_, hσ01 1⟩ : unitInterval) = 1 := Subtype.ext Real.smoothTransition.one
    rw [this, H.apply_one]
    rfl
  have hk : ∀ t : ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun x : M => Ht (x, t)) := fun t => hHts.comp (contMDiff_id.prodMk contMDiff_const)
  have hA : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      f (fun x => Ht (x, 0)) :=
    smoothHomotopic_of_norm_sub_lt_two hf (hk 0) (hend 0 f hH0)
  have hB : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun x => Ht (x, 0)) (fun x => Ht (x, 1)) :=
    ⟨Ht, hHts, fun _ => rfl, fun _ => rfl⟩
  have hC : SmoothHomotopic 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      g (fun x => Ht (x, 1)) :=
    smoothHomotopic_of_norm_sub_lt_two hg (hk 1) (hend 1 g hH1)
  exact (hA.trans hB).trans hC.symm

include hM in
/-- **Problem 5.** Every continuous map `M → Sᵖ` from a compact `m`-manifold, `m < p`, is homotopic
to a constant. -/
theorem exists_homotopic_const_of_lt (hMc : IsCompact M) {p : ℕ} (hmp : m < p) (f : C(M, Sph p)) :
    ∃ c : Sph p, f.Homotopic (ContinuousMap.const M c) := by
  let _ := hM.chartedSpace
  have _ := hM.isManifold
  obtain ⟨f', hf', hclose⟩ := exists_smooth_approx hM hMc f two_pos
  have h1 : f.Homotopic ⟨f', hf'.continuous⟩ :=
    homotopic_of_norm_sub_lt_two f ⟨f', hf'.continuous⟩ fun x => by
      rw [norm_sub_rev]; exact hclose x
  obtain ⟨c, hc⟩ := exists_smoothHomotopic_const_of_lt finrank_euclideanSpace_fin hmp hf'
  exact ⟨c, h1.trans (hc.homotopic hf'.continuous continuous_const)⟩

end Problems

end Milnor
