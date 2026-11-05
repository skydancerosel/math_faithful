import Morse.Chapter10.BrokenEnergy

/-!
Milnor, *Morse Theory*, §16, p. 91: the critical points of `E'` (Theorem 16.2, third assertion),
for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Variations through broken geodesics, and the critical points of `E'`

## Milnor's text, paraphrased

(p. 91) Every geodesic is a broken geodesic, so every critical point of `E` in `Int Ω^c` lies in
`B`.  "Using the first variation formula (§12.2) it is clear that the critical points of `E'`
are precisely the unbroken geodesics."

## In the embedded setting

For `B : Morse.BrokenSetup hN p q c m`:

* `Morse.BrokenSetup.exists_variation_path`: **a smooth curve `u ↦ y(u)` in `U` gives a variation
  `u ↦ B.path (y u)` through broken geodesics** (`Morse.IsVariation`, smooth on every strip
  `(−ε, ε) × [tᵢ, t_{i+1}]`): on the `i`-th strip it is `exp_{xᵢ(u)}(s vᵢ(u))`, smooth by the
  smooth dependence of geodesics on their initial data (`Morse.raysGood_of_isGeodesicOn`) and of
  `vᵢ` on the end points (Corollary 10.8).  Its variation field takes the values `y'(0)` at the
  break points (`Morse.BrokenSetup.varField_path_node`).
* `Morse.BrokenSetup.firstVariation_path`: at a broken geodesic `γ = B.path y`, the first
  variation is `−Σ_j ⟨W(t_j), Δ_{t_j} γ'⟩` (the acceleration vanishes on the segments).
* `Morse.BrokenSetup.hasFDerivAt_energy'`: **the derivative of `E'`**: if `F` is smooth near `y`
  and agrees with `E'` on `N^m ∩ O`, then `dF_y(w) = −2 Σ_j ⟨w_j, Δ_{t_j} γ'⟩` for every
  `w ∈ ∏ T_{y_j}N` (curves in the chart of `N^m ∩ O` realize every tangent vector).
* **Theorem 16.2, critical points**, `Morse.BrokenSetup.isCriticalPointM_iff`: `y` is a critical
  point of `E'` on the manifold `N^m ∩ O` (any open `O` with `N^m ∩ O ⊆ U`) if and only if
  `B.path y` is an unbroken geodesic (Corollary 12.3), i.e. a critical point of `E` on `Ω`.

## What Milnor leaves implicit

* **"It is clear"** needs, besides the first variation formula, that every tangent vector to `B`
  at `γ` is realized by a variation *through broken geodesics*, smooth on the strips: the smooth
  dependence of a geodesic segment on its end points over the whole segment.
* **Testing one break point at a time**: a field with value `Δ_{t_j}γ'` at `t_j` (tangent, as a
  difference of one-sided velocities of a path in `N`, `Morse.prj_jump`) gives
  `dE'(w) = −2 Σ ‖Δ_{t_j}γ'‖²`; a broken geodesic without velocity jumps is unbroken (uniqueness
  of geodesics, Corollary 12.3).
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **Every tangent vector of a slice submanifold is a velocity**: for `w ∈ T_{y₀}S` there is a
smooth curve `y(u) = x(z₀ + u z)` (`x` the parametrization of a slice chart at `y₀`) in `S` with
`y(0) = y₀`, `y'(0) = w`. -/
theorem exists_curve_of_mem_tangentSubspace {V' Z' W' : Type*} [NormedAddCommGroup V']
    [NormedSpace ℝ V'] [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] [NormedAddCommGroup W']
    [NormedSpace ℝ W'] {S : Set V'} (hS : Milnor.IsSliceSubmanifold 𝓘(ℝ, V') Z' W' S) (y₀ : S)
    {w : V'} (hw : w ∈ tangentSubspace hS y₀) :
    ∃ y : ℝ → V', ∃ U₀ : Set ℝ, IsOpen U₀ ∧ (0 : ℝ) ∈ U₀ ∧ ContDiffOn ℝ ∞ y U₀ ∧
      y 0 = y₀ ∧ HasDerivAt y w 0 ∧ ∀ u ∈ U₀, y u ∈ S := by
  set σ := (hS y₀ y₀.2).choose
  have hσ : (y₀ : V') ∈ σ.φ.source := (hS y₀ y₀.2).choose_spec
  rw [tangentSubspace_eq_range_fderiv_sliceParam hS σ hσ] at hw
  obtain ⟨z, rfl⟩ := hw
  set z₀ := (σ.φ y₀).1
  have hz₀ : z₀ ∈ σ.toChart.target := toChart_apply_mem_target σ hσ
  set ℓ : ℝ → Z' := fun u => z₀ + u • z
  have hℓ : ContDiff ℝ ∞ ℓ := contDiff_const.add (contDiff_id.smul contDiff_const)
  refine ⟨fun u => sliceParam σ (ℓ u), ℓ ⁻¹' σ.toChart.target,
    (isOpen_toChart_target σ).preimage hℓ.continuous, by simpa [ℓ] using hz₀,
    (contDiffOn_sliceParam σ).comp hℓ.contDiffOn fun u hu => hu, ?_, ?_,
    fun u hu => sliceParam_mem σ hu⟩
  · simp only [ℓ, zero_smul, add_zero]
    exact sliceParam_toChart σ hσ
  · have hℓd : HasDerivAt ℓ z 0 := by
      simpa [ℓ] using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add z₀
    have hℓ0 : z₀ = ℓ 0 := by simp [ℓ]
    exact ((contDiffAt_sliceParam σ hz₀).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hℓd hℓ0

namespace BrokenSetup

variable {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

/-! ### Variations through broken geodesics -/

/-- **A smooth curve of break points gives a variation through broken geodesics.**  If
`u ↦ y(u)` is smooth on an open set `U₀ ∋ 0` with values in `U`, then for some `ε > 0`, on each
`i`-th strip the map `(u, s) ↦ B.path (y u) (tᵢ + s (t_{i+1} − tᵢ))` is smooth on `(−ε, ε) × [0, 1]`
and a geodesic in `s` for every `u`, and `u ↦ B.path (y u)` is a variation with break points
`t₁, …, t_m`. -/
theorem exists_variation_path {y : ℝ → Fin m → V} {U₀ : Set ℝ} (hU₀ : IsOpen U₀)
    (h0 : (0 : ℝ) ∈ U₀) (hys : ContDiffOn ℝ ∞ y U₀) (hyU : ∀ u ∈ U₀, y u ∈ B.nodes) :
    ∃ ε > 0, Ioo (-ε) ε ⊆ U₀ ∧
      (∀ i : Fin (m + 1),
        ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => B.path (y z.1) (B.t i.castSucc + z.2 * B.len i))
          (Ioo (-ε) ε ×ˢ Icc 0 1) ∧
        ∀ u ∈ Ioo (-ε) ε,
          IsGeodesicOn hN (fun s => B.path (y u) (B.t i.castSucc + s * B.len i)) (Ioo 0 1)) ∧
      IsVariation N (Ioo (-ε) ε) (fun u => B.path (y u)) B.breaks := by
  -- the data of each segment
  have hseg : ∀ i : Fin (m + 1), ∃ ε > 0, ∃ η > 0, Ioo (-ε) ε ⊆ U₀ ∧
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => exp hN (vert p q (y z.1) i.castSucc)
        (z.2 • B.joinVec (vert p q (y z.1) i.castSucc) (vert p q (y z.1) i.succ)))
        (Ioo (-ε) ε ×ˢ Ioo (-η) (1 + η)) ∧
      ∀ u ∈ Ioo (-ε) ε, IsGeodesicOn hN (fun s => exp hN (vert p q (y u) i.castSucc)
        (s • B.joinVec (vert p q (y u) i.castSucc) (vert p q (y u) i.succ)))
        (Ioo (-η) (1 + η)) := by
    intro i
    set c₀ : ℝ → V := fun u => vert p q (y u) i.castSucc
    set c₁ : ℝ → V := fun u => vert p q (y u) i.succ
    have hc₀ : ContDiffOn ℝ ∞ c₀ U₀ := (contDiff_vert p q _).comp_contDiffOn hys
    have hc₁ : ContDiffOn ℝ ∞ c₁ U₀ := (contDiff_vert p q _).comp_contDiffOn hys
    have hy0 := hyU 0 h0
    -- the smooth local representative of the join vector at `u = 0`
    obtain ⟨v, -, -, -, -, -, O₂, hO₂, hmem, G, hG, -, hGspec⟩ :=
      B.join ⟨c₀ 0, B.vert_mem hy0.1 _⟩ ⟨c₁ 0, B.vert_mem hy0.1 _⟩ (B.vert_mem_ball hy0 i.castSucc)
        (B.vert_mem_ball hy0 i.succ) (B.riemDist_vert_lt hy0 i)
    set U₁ := U₀ ∩ (fun u => (c₀ u, c₁ u)) ⁻¹' O₂
    have hU₁ : IsOpen U₁ := (hc₀.continuousOn.prodMk hc₁.continuousOn).isOpen_inter_preimage hU₀ hO₂
    have h0U₁ : (0 : ℝ) ∈ U₁ := ⟨h0, hmem⟩
    have hwG : ∀ u ∈ U₁, B.joinVec (c₀ u) (c₁ u) = G (c₀ u, c₁ u) := by
      intro u hu
      have hyu := hyU u hu.1
      obtain ⟨hGT, hGδ, hGexp⟩ := hGspec ⟨c₀ u, B.vert_mem hyu.1 _⟩ ⟨c₁ u, B.vert_mem hyu.1 _⟩
        hu.2 (B.riemDist_vert_lt hyu i)
      exact ((B.joinVec_spec (B.vert_mem_ball hyu _) (B.vert_mem_ball hyu _)
        (B.riemDist_vert_lt hyu i)).2.2.2.2 _ ((prj_eq_self_iff hN (B.vert_mem hyu.1 _)).2 hGT)
        hGδ hGexp).symm
    have hws : ContDiffOn ℝ ∞ (fun u => B.joinVec (c₀ u) (c₁ u)) U₁ :=
      (hG.comp ((hc₀.prodMk hc₁).mono inter_subset_left) fun u hu => hu.2).congr hwG
    have hcN : ∀ u ∈ U₁, c₀ u ∈ N := fun u hu => B.vert_mem (hyU u hu.1).1 _
    have hwT : ∀ u ∈ U₁, prj hN (c₀ u) (B.joinVec (c₀ u) (c₁ u)) = B.joinVec (c₀ u) (c₁ u) :=
      fun u hu => (B.joinVec_vert (hyU u hu.1) i).1
    -- the base ray is a geodesic beyond `[0, 1]`
    obtain ⟨γ, hγ⟩ := B.mem_expDom_joinVec (B.vert_mem_ball hy0 i.castSucc)
      (B.vert_mem_ball hy0 i.succ) (B.riemDist_vert_lt hy0 i)
    obtain ⟨δ', hδ', hbase, -⟩ := hγ.isGeodesicOn_exp_smul
    obtain ⟨ε, hε, η, hη, hsub, hsm, hgeo⟩ := raysGood_of_isGeodesicOn hU₁ h0U₁
      (hc₀.mono inter_subset_left) hws hcN hwT zero_le_one hδ' hbase
    exact ⟨ε, hε, η, hη, hsub.trans inter_subset_left, hsm, hgeo⟩
  choose ε hε η hη hsub hsm hgeo using hseg
  set ε₀ := Finset.univ.inf' Finset.univ_nonempty ε with hε₀_def
  have hε₀ : 0 < ε₀ := (Finset.lt_inf'_iff _).2 fun i _ => hε i
  have hε₀i : ∀ i, Ioo (-ε₀) ε₀ ⊆ Ioo (-ε i) (ε i) := fun i u hu => by
    have := Finset.inf'_le ε (Finset.mem_univ i)
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hsubU : Ioo (-ε₀) ε₀ ⊆ U₀ := (hε₀i 0).trans (hsub 0)
  -- on the `i`-th strip, the path is the ray
  have hray : ∀ i, ∀ u ∈ Ioo (-ε₀) ε₀, ∀ s ∈ Icc (0 : ℝ) 1,
      B.path (y u) (B.t i.castSucc + s * B.len i) = exp hN (vert p q (y u) i.castSucc)
        (s • B.joinVec (vert p q (y u) i.castSucc) (vert p q (y u) i.succ)) := by
    intro i u hu s hs
    have hl := B.len_pos i
    have hmem : B.t i.castSucc + s * B.len i ∈ Icc (B.t i.castSucc) (B.t i.succ) :=
      ⟨by nlinarith [hs.1], by
        have : B.t i.succ = B.t i.castSucc + B.len i := by simp [Subdivision.len]
        nlinarith [hs.2]⟩
    rw [B.path_eq_segPath (hyU u (hsubU hu)) i hmem, segPath]
    congr 2
    field_simp
    ring
  have hstrip : ∀ i : Fin (m + 1),
      ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => B.path (y z.1) (B.t i.castSucc + z.2 * B.len i))
        (Ioo (-ε₀) ε₀ ×ˢ Icc 0 1) := fun i =>
    (hsm i).mono (prod_mono (hε₀i i) fun s hs => ⟨by linarith [hs.1, hη i],
      by linarith [hs.2, hη i]⟩) |>.congr fun z hz => hray i z.1 hz.1 z.2 hz.2
  refine ⟨ε₀, hε₀, hsubU, fun i => ⟨hstrip i, fun u hu => ?_⟩, ?_⟩
  · refine ((hgeo i u (hε₀i i hu)).mono isOpen_Ioo fun s hs => ⟨by linarith [hs.1, hη i],
      by linarith [hs.2, hη i]⟩).congr fun s hs => (hray i u hu s (Ioo_subset_Icc_self hs)).symm
  · refine ⟨isOpen_Ioo, ⟨by linarith, hε₀⟩, fun u hu t ht => B.path_mem (hyU u (hsubU hu)) t ht,
      fun u hu => ?_, fun u hu => ?_, fun a b ha hab hb hBab => ?_⟩
    · rw [(B.path_mem_pathSpace (hyU u (hsubU hu))).2.2.1,
        (B.path_mem_pathSpace (hyU 0 h0)).2.2.1]
    · rw [(B.path_mem_pathSpace (hyU u (hsubU hu))).2.2.2,
        (B.path_mem_pathSpace (hyU 0 h0)).2.2.2]
    · obtain ⟨i, hai, hbi⟩ := B.exists_seg_of_piece ha hab hb hBab
      have hl := B.len_pos i
      have hmaps : MapsTo (fun z : ℝ × ℝ => (z.1, (z.2 - B.t i.castSucc) / B.len i))
          (Ioo (-ε₀) ε₀ ×ˢ Icc a b) (Ioo (-ε₀) ε₀ ×ˢ Icc 0 1) := fun z hz =>
        ⟨hz.1, div_nonneg (by linarith [hz.2.1]) hl.le, by
          rw [div_le_one hl]
          have : B.t i.succ = B.t i.castSucc + B.len i := by simp [Subdivision.len]
          linarith [hz.2.2]⟩
      refine ((hstrip i).comp (contDiff_fst.prodMk ((contDiff_snd.sub contDiff_const).div_const
        _)).contDiffOn hmaps).congr fun z _ => ?_
      simp only [Function.comp_apply]
      congr 1
      field_simp
      ring

/-- **The variation field at the break points** is the velocity of the curve of break points. -/
theorem varField_path_node {y : ℝ → Fin m → V} {U₀ : Set ℝ} (hU₀ : IsOpen U₀)
    (h0 : (0 : ℝ) ∈ U₀) {y' : Fin m → V} (hyd : HasDerivAt y y' 0)
    (hyU : ∀ u ∈ U₀, y u ∈ B.nodes) (j : Fin m) :
    varField (fun u => B.path (y u)) (B.t j.castSucc.succ) = y' j := by
  have hev : (fun u => B.path (y u) (B.t j.castSucc.succ)) =ᶠ[𝓝 0] fun u => y u j := by
    filter_upwards [hU₀.mem_nhds h0] with u hu
    exact congrFun (B.nodeVal_path (hyU u hu)) j
  rw [varField, hev.deriv_eq]
  exact (hasDerivAt_pi.1 hyd j).deriv

/-! ### The first variation at a broken geodesic -/

/-- **The first variation at a broken geodesic** `γ = B.path y`: the acceleration vanishes on the
segments, so `firstVariation γ X = −Σ_j ⟨X(t_j), Δ_{t_j} γ'⟩`. -/
theorem firstVariation_path {y : Fin m → V} (hy : y ∈ B.nodes) (X : ℝ → V) :
    firstVariation hN (B.path y) X =
      -∑ j : Fin m, ⟪X (B.t j.castSucc.succ), jump (B.path y) (B.t j.castSucc.succ)⟫ := by
  have hbr := B.isBroken_path hy
  -- off the break points, `γ` is a geodesic near `τ`
  have hgeo : ∀ τ ∈ Ioo (0 : ℝ) 1, τ ∉ B.breaks → ∃ s, IsOpen s ∧ τ ∈ s ∧
      IsGeodesicOn hN (B.path y) s := by
    intro τ hτ hτB
    have hτi := B.mem_Icc_segOf (Ioo_subset_Icc_self hτ)
    generalize B.segOf τ = i at hτi
    refine ⟨Ioo (B.t i.castSucc) (B.t i.succ), isOpen_Ioo, ⟨?_, ?_⟩, hbr i⟩
    · rcases eq_or_lt_of_le hτi.1 with h | h
      · exfalso
        -- `τ = tᵢ` with `0 < τ`: an interior break point
        have hi0 : i ≠ 0 := by
          rintro rfl
          rw [Fin.castSucc_zero, B.t_zero] at h
          exact absurd h.symm hτ.1.ne'
        obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi0
        exact hτB (B.mem_breaks.2 ⟨k, h⟩)
      · exact h
    · rcases eq_or_lt_of_le hτi.2 with h | h
      · exfalso
        have hil : i ≠ Fin.last m := by
          rintro rfl
          rw [Fin.succ_last, B.t_last] at h
          exact absurd h hτ.2.ne
        obtain ⟨k, rfl⟩ := Fin.exists_castSucc_eq.2 hil
        exact hτB (B.mem_breaks.2 ⟨k, h.symm⟩)
      · exact h
  have hacc : ∀ τ ∈ Ioo (0 : ℝ) 1, τ ∉ B.breaks → accel hN (B.path y) τ = 0 := by
    intro τ hτ hτB
    obtain ⟨s, hs, hτs, hg⟩ := hgeo τ hτ hτB
    rw [accel, covD, prj_of_mem hN (hg.mem τ hτs), hg.tanProj_deriv_deriv hτs]
  have hint : ∫ t in (0 : ℝ)..1, ⟪X t, accel hN (B.path y) t⟫ = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
    · simp
    have hfin : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ insert (1 : ℝ) (B.breaks : Set ℝ) :=
      (B.breaks.finite_toSet.insert 1).countable.ae_notMem _
    filter_upwards [hfin] with t htB ht
    rw [uIoc_of_le zero_le_one] at ht
    rw [mem_insert_iff, not_or] at htB
    rw [hacc t ⟨ht.1, lt_of_le_of_ne ht.2 htB.1⟩ htB.2, inner_zero_right]
  have hsum : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X t, jump (B.path y) t⟫ =
      ∑ x ∈ B.breaks with x ∈ Ioo (0 : ℝ) 1, ⟪X x, jump (B.path y) x⟫ :=
    finsum_jump_eq_sum fun τ hτ hτB => by
      obtain ⟨s, hs, hτs, hg⟩ := hgeo τ hτ hτB
      exact (hg.hasDerivAt hτs).differentiableAt
  have hfilter : B.breaks.filter (· ∈ Ioo (0 : ℝ) 1) = B.breaks :=
    Finset.filter_true_of_mem fun x hx => B.breaks_subset hx
  have himage : ∑ x ∈ B.breaks, ⟪X x, jump (B.path y) x⟫ =
      ∑ j : Fin m, ⟪X (B.t j.castSucc.succ), jump (B.path y) (B.t j.castSucc.succ)⟫ := by
    rw [Subdivision.breaks, Finset.sum_image]
    intro j _ k _ hjk
    have := B.strictMono.injective hjk
    exact Fin.castSucc_injective _ (Fin.succ_injective _ this)
  rw [firstVariation, hint, hsum, hfilter, himage, sub_zero]

/-- The velocity jumps of a broken geodesic are tangent. -/
theorem prj_jump_path {y : Fin m → V} (hy : y ∈ B.nodes) (j : Fin m) :
    prj hN (y j) (jump (B.path y) (B.t j.castSucc.succ)) =
      jump (B.path y) (B.t j.castSucc.succ) := by
  have h := prj_jump hN (B.path_mem_pathSpace hy) (B := B.breaks)
    (fun s t hs hst ht hB => B.contDiffOn_path hy hs hst ht hB) (B.breaks_subset
      (B.mem_breaks.2 ⟨j, rfl⟩))
  rwa [show B.path y (B.t j.castSucc.succ) = y j from congrFun (B.nodeVal_path hy) j] at h

/-! ### Theorem 16.2: the critical points of `E'` -/

/-- **The derivative of `E'`** (the first variation formula on `B`): if `F` is smooth and agrees
with `E'` on the manifold `N^m ∩ O ⊆ U`, then at `y₀` and for every tangent vector
`w ∈ ∏ T_{y₀ j}N`, `dF(w) = −2 Σ_j ⟨w_j, Δ_{t_j} γ'⟩`, `γ = B.path y₀`. -/
theorem fderiv_eq_jumps {O : Set (Fin m → V)} (hO : IsOpen O)
    (hOU : (Set.pi univ fun _ => N) ∩ O ⊆ B.nodes) {F : (Fin m → V) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFE : ∀ y ∈ (Set.pi univ fun _ => N) ∩ O, F y = B.energy' y)
    (y₀ : ↥((Set.pi univ fun _ => N) ∩ O)) {w : Fin m → V}
    (hw : w ∈ tangentSubspace (isSliceSubmanifold_pi_inter hN hO) y₀) :
    fderiv ℝ F y₀ w =
      -2 * ∑ j : Fin m, ⟪w j, jump (B.path y₀) (B.t j.castSucc.succ)⟫ := by
  obtain ⟨y, U₀, hU₀, h0, hys, hy0, hyd, hyS⟩ :=
    exists_curve_of_mem_tangentSubspace (isSliceSubmanifold_pi_inter hN hO) y₀ hw
  have hyU : ∀ u ∈ U₀, y u ∈ B.nodes := fun u hu => hOU (hyS u hu)
  obtain ⟨ε, hε, hsub, -, hα⟩ := B.exists_variation_path hU₀ h0 hys hyU
  have h1 := first_variation hN hα (c := B.path y₀) fun t _ => by rw [hy0]
  have h2 : HasDerivAt (fun u => F (y u)) (fderiv ℝ F y₀ w) 0 := by
    have := (hF.differentiable (by simp) (y 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hyd
    rwa [hy0] at this
  have h3 : HasDerivAt (fun u => F (y u))
      (2 * firstVariation hN (B.path y₀) (varField fun u => B.path (y u))) 0 := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)]
      with u hu
    rw [hFE _ (hyS u (hsub hu)), B.energy_path (hyU u (hsub hu))]
  rw [h2.unique h3, B.firstVariation_path (hOU y₀.2)]
  have hnode : ∀ j, varField (fun u => B.path (y u)) (B.t j.castSucc.succ) = w j :=
    fun j => B.varField_path_node hU₀ h0 hyd hyU j
  simp only [hnode]
  ring

/-- **Theorem 16.2, the critical points of `E'`** (Milnor p. 91): let `O ⊆ V^m` be open with
`N^m ∩ O ⊆ U` (for instance `U` itself, `Morse.BrokenSetup.exists_isOpen_nodes`), and let `F` be
a smooth function on `V^m` agreeing with `E'` on `N^m ∩ O`.  Then `y` is a critical point of
`E' = F|(N^m ∩ O)` if and only if the broken geodesic `B.path y` is an unbroken geodesic — by
Corollary 12.3, a critical point of the energy `E` on `Ω`. -/
theorem isCriticalPointM_iff {O : Set (Fin m → V)} (hO : IsOpen O)
    (hOU : (Set.pi univ fun _ => N) ∩ O ⊆ B.nodes) {F : (Fin m → V) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFE : ∀ y ∈ (Set.pi univ fun _ => N) ∩ O, F y = B.energy' y)
    (y₀ : ↥((Set.pi univ fun _ => N) ∩ O)) :
    letI := (isSliceSubmanifold_pi_inter hN hO).chartedSpace
    IsCriticalPointM (Fin m → Z) (F ∘ Subtype.val) y₀ ↔ IsUnbrokenGeodesic hN (B.path y₀) := by
  have hy₀ : (y₀ : Fin m → V) ∈ B.nodes := hOU y₀.2
  rw [isCriticalPointM_comp_val_iff_forall_tangent (isSliceSubmanifold_pi_inter hN hO)
    ((hF.differentiable (by simp)) _)]
  constructor
  · intro hcrit
    -- test with the jumps themselves
    set Δ : Fin m → V := fun j => jump (B.path y₀) (B.t j.castSucc.succ)
    have hΔT : Δ ∈ tangentSubspace (isSliceSubmanifold_pi_inter hN hO) y₀ := by
      rw [tangentSubspace_pi_inter hN hO y₀]
      intro j _
      exact (prj_eq_self_iff hN (y₀.2.1 j trivial)).1 (B.prj_jump_path hy₀ j)
    have h1 := hcrit Δ hΔT
    rw [B.fderiv_eq_jumps hO hOU hF hFE y₀ hΔT] at h1
    have h2 : ∑ j : Fin m, ‖Δ j‖ ^ 2 = 0 := by
      have : ∑ j : Fin m, ⟪Δ j, Δ j⟫ = 0 := by linarith
      simpa only [real_inner_self_eq_norm_sq] using this
    have hΔ0 : ∀ j, Δ j = 0 := fun j => by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖Δ j‖).1 h2 j
        (Finset.mem_univ j)
      rwa [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at this
    have hγ := B.path_mem_pathSpace hy₀
    rw [← corollary_12_3 hN hγ, isCriticalPath_iff hN hγ]
    intro X _
    rw [B.firstVariation_path hy₀]
    have hΔ0' : ∀ j : Fin m, jump (B.path y₀) (B.t j.castSucc.succ) = 0 := hΔ0
    simp only [hΔ0', inner_zero_right, Finset.sum_const_zero, neg_zero]
  · intro hgeo w hw
    rw [B.fderiv_eq_jumps hO hOU hF hFE y₀ hw]
    have hj : ∀ j : Fin m, jump (B.path y₀) (B.t j.castSucc.succ) = 0 := fun j =>
      jump_eq_zero (hgeo.2.hasDerivAt (B.breaks_subset (B.mem_breaks.2 ⟨j, rfl⟩))).differentiableAt
    simp only [hj, inner_zero_right, Finset.sum_const_zero, mul_zero]

end BrokenSetup

end Morse
