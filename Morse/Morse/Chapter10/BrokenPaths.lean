import Morse.Chapter10.Broken

/-!
Milnor, *Morse Theory*, §16, p. 89: the end of the proof of Lemma 16.1, for a submanifold
`N ⊆ ℝᴷ` with the induced metric.

# Broken geodesics are determined by their break points

## Milnor's text, paraphrased

(p. 89) For a broken geodesic `ω ∈ Ω(t₀, …, t_k)^c`,
`(L_{t_{i−1}}^{t_i} ω)² = (t_i − t_{i−1}) E_{t_{i−1}}^{t_i} ω ≤ (t_i − t_{i−1}) c < ε²`, so the
geodesic `ω|[t_{i−1}, t_i]` is uniquely determined by its two end points, and `ω` is uniquely
determined by `(ω(t₁), …, ω(t_{k−1}))`; "evidently" this correspondence is a homeomorphism of
`Int Ω(t₀, …, t_k)^c` onto an open subset of `M × ⋯ × M`.

## In the embedded setting

For `B : Morse.BrokenSetup hN p q c m`:

* `Morse.contDiffOn_Icc_of_isGeodesicOn`: a piecewise smooth path which is a geodesic on `(a, b)`
  is smooth on `[a, b]`.
* `Morse.BrokenSetup.exists_segVec` (**Step 3**): on each `[tᵢ, t_{i+1}]` a broken geodesic of
  energy `< c` is `τ ↦ exp_{γ(tᵢ)}((τ − tᵢ)/(t_{i+1} − tᵢ) · w)` with `‖w‖ < δ`,
  `E_{tᵢ}^{t_{i+1}} = ‖w‖²/(t_{i+1} − tᵢ)` and `ρ(γ(tᵢ), γ(t_{i+1})) ≤ ‖w‖`.
* `Morse.BrokenSetup.brokenPaths`: Milnor's `Int Ω(t₀, …, t_k)^c` (paths of `Ω(N; p, q)` that are
  geodesics on each `(tᵢ, t_{i+1})` and have energy `< c`).
* **Lemma 16.1**, `Morse.BrokenSetup.lemma_16_1`: `y ↦ B.path y` maps `U = B.nodes` into
  `Int Ω(t₀, …, t_k)^c`, `γ ↦ B.nodeVal γ` maps `Int Ω(t₀, …, t_k)^c` into `U`, and they are
  inverse to each other (paths being compared on `[0, 1]`).  With formula (∗)
  (`Morse.BrokenSetup.energy_path`) the energy of `B.path y` is `B.energy' y`.

The topology of `Int Ω(t₀, …, t_k)^c` (Milnor's metric `d`) is not used here: the manifold
structure is the one of `U`, an open subset of `N^m` (`Morse/Chapter10/BrokenEnergy.lean`).
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **A piecewise smooth path which is a geodesic on `(a, b)` is smooth on `[a, b]`** (at the end
points, by its own pieces). -/
theorem contDiffOn_Icc_of_isGeodesicOn {γ : ℝ → V} (hγ : IsPiecewiseSmooth γ 0 1) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) (hg : IsGeodesicOn hN γ (Ioo a b)) :
    ContDiffOn ℝ ∞ γ (Icc a b) := by
  obtain ⟨-, -, Bγ, hBγ⟩ := hγ
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  rcases eq_or_lt_of_le hx.1 with hax | hax
  · obtain ⟨s', hxs', hs'b, hs'⟩ := exists_piece_right Bγ hab
    refine ⟨Iio s', isOpen_Iio, hax ▸ hxs', (hBγ a s' ha hxs' (hs'b.trans hb) hs').mono
      fun τ hτ => ⟨hτ.1.1, hτ.2.le⟩⟩
  rcases eq_or_lt_of_le hx.2 with hxb | hxb
  · obtain ⟨s, has, hsx, hs⟩ := exists_piece_left Bγ hab
    exact ⟨Ioi s, isOpen_Ioi, hxb ▸ hsx, (hBγ s b (ha.trans has) hsx hb hs).mono
      fun τ hτ => ⟨hτ.2.le, hτ.1.2⟩⟩
  · exact ⟨Ioo a b, isOpen_Ioo, ⟨hax, hxb⟩, hg.contDiffOn.mono inter_subset_right⟩

namespace BrokenSetup

variable {hN} {p q : V} {c : ℝ} {m : ℕ} (B : BrokenSetup hN p q c m)

/-- **Milnor's `Int Ω(t₀, …, t_k)^c`** (p. 88): the paths of `Ω(N; p, q)` which are geodesics on
every `(tᵢ, t_{i+1})` and have energy `< c`. -/
def brokenPaths : Set (ℝ → V) :=
  {γ | γ ∈ pathSpace N p q ∧ B.IsBroken γ ∧ energy γ 0 1 < c}

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The vertices of the break points of a path are its values at the division points. -/
theorem vert_nodeVal {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) (k : Fin (m + 2)) :
    vert p q (B.nodeVal γ) k = γ (B.t k) := by
  induction k using Fin.cases with
  | zero => rw [vert_zero, B.t_zero, hγ.2.2.1]
  | succ k =>
    induction k using Fin.lastCases with
    | last => rw [Fin.succ_last, vert_last, B.t_last, hγ.2.2.2]
    | cast j => rw [vert_inner]; rfl

/-- **Step 3 of Lemma 16.1** (Milnor p. 89): on each `[tᵢ, t_{i+1}]` a broken geodesic `γ` of energy
`< c` is the radial geodesic `τ ↦ exp_{γ(tᵢ)}((τ − tᵢ)/(t_{i+1} − tᵢ) · w)` with `‖w‖ < δ`; its
energy there is `‖w‖²/(t_{i+1} − tᵢ)`, and `ρ(γ(tᵢ), γ(t_{i+1})) ≤ ‖w‖`.  (`‖w‖ < δ` comes from
`‖w‖² = (t_{i+1} − tᵢ) E_{tᵢ}^{t_{i+1}} ≤ (t_{i+1} − tᵢ) c < δ²`.) -/
theorem exists_segVec {γ : ℝ → V} (hγ : γ ∈ B.brokenPaths) (i : Fin (m + 1)) :
    ∃ w, prj hN (γ (B.t i.castSucc)) w = w ∧ ‖w‖ < B.δ ∧
      (∀ τ ∈ Icc (B.t i.castSucc) (B.t i.succ),
        exp hN (γ (B.t i.castSucc)) (((τ - B.t i.castSucc) / B.len i) • w) = γ τ) ∧
      energy γ (B.t i.castSucc) (B.t i.succ) = ‖w‖ ^ 2 / B.len i ∧
      riemDist (N := N) (γ (B.t i.castSucc)) (γ (B.t i.succ)) ≤ ENNReal.ofReal ‖w‖ := by
  obtain ⟨hγΩ, hbr, hE⟩ := hγ
  set a := B.t i.castSucc with ha_def
  set b := B.t i.succ with hb_def
  set h := B.len i with hh_def
  have hhpos : 0 < h := B.len_pos i
  have hhab : b = h * 1 + a := by simp [hh_def, Subdivision.len, ha_def, hb_def]
  have hab : a < b := by linarith
  have ha0 : 0 ≤ a := B.t_nonneg _
  have hb1 : b ≤ 1 := B.t_le_one _
  have hsmooth := contDiffOn_Icc_of_isGeodesicOn hN hγΩ.1 ha0 hab hb1 (hbr i)
  -- the segment, reparametrized by `[0, 1]`
  set γ' : ℝ → V := fun s => γ (h * s + a) with hγ'_def
  have hmaps : ∀ s ∈ Icc (0 : ℝ) 1, h * s + a ∈ Icc a b := fun s hs =>
    ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have hc : IsSmoothCurveIn hN γ' :=
    ⟨hsmooth.comp ((contDiff_const.mul contDiff_id).add contDiff_const).contDiffOn hmaps,
      fun s hs => hγΩ.2.1 _ ⟨ha0.trans (hmaps s hs).1, (hmaps s hs).2.trans hb1⟩⟩
  have hgeo : IsGeodesicOn hN γ' (Ioo 0 1) :=
    ((hbr i).comp_mul_add h a).mono isOpen_Ioo fun s hs =>
      ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  obtain ⟨η, hη, hray, hrayγ⟩ := exists_initial_ray hc hgeo
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hγ'0 : γ' 0 = γ a := by simp [hγ'_def]
  set w := velAlong γ' 0 with hw_def
  have hxN : γ' 0 ∈ N := hc.mem 0 h0
  have hwT : prj hN (γ' 0) w = w := hc.velAlong_mem h0
  have hd0 : HasDerivAt (fun s : ℝ => exp hN (γ' 0) (s • w)) w 0 :=
    hasDerivAt_exp_smul_zero ⟨_, hxN⟩ ((prj_eq_self_iff hN hxN).1 hwT)
  -- the speed of `γ` on `(a, b)` is `‖w‖ / h`
  have hspeed : ∀ τ ∈ Ioo a b, ‖deriv γ τ‖ = ‖w‖ / h := by
    intro τ hτ
    set s := (τ - a) / h with hs_def
    have hτs : h * s + a = τ := by rw [hs_def]; field_simp; ring
    have hs : s ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · rw [hs_def]; exact div_pos (by linarith [hτ.1]) hhpos
      · rw [hs_def, div_lt_one hhpos]; linarith [hτ.2]
    have h1 := hray.norm_deriv_eq isPreconnected_Ioo (t := s) ⟨by linarith [hs.1], by
      linarith [hs.2]⟩ (t' := 0) ⟨by linarith, by linarith⟩
    rw [hd0.deriv] at h1
    have hev : (fun s : ℝ => exp hN (γ' 0) (s • w)) =ᶠ[𝓝 s] γ' :=
      eventually_of_mem (Ioo_mem_nhds hs.1 hs.2) fun σ hσ => hrayγ σ (Ioo_subset_Icc_self hσ)
    rw [hev.deriv_eq] at h1
    have hγd : HasDerivAt γ (deriv γ τ) (h * s + a) := by
      rw [hτs]; exact (hbr i).hasDerivAt hτ
    have haff : HasDerivAt (fun s : ℝ => h * s + a) h s := by
      simpa using ((hasDerivAt_id s).const_mul h).add_const a
    have hγ'd : HasDerivAt γ' (h • deriv γ τ) s := hγd.scomp s haff
    rw [hγ'd.deriv, norm_smul, Real.norm_eq_abs, abs_of_pos hhpos] at h1
    field_simp
    linarith
  have hadm : IsAdmissible γ a b := (hγΩ.1.mono ha0 hab.le hb1).isAdmissible
  have hEab : energy γ a b = ‖w‖ ^ 2 / h := by
    rw [energy_eq_of_norm_deriv hadm (k := ‖w‖ / h) fun τ hτ _ => hspeed τ hτ]
    have : b - a = h := by simp [hh_def, Subdivision.len, ha_def, hb_def]
    rw [this]
    field_simp
  have hLab : pathLength γ a b = ‖w‖ := by
    rw [pathLength_eq_of_norm_deriv hadm (k := ‖w‖ / h) fun τ hτ _ => hspeed τ hτ]
    have : b - a = h := by simp [hh_def, Subdivision.len, ha_def, hb_def]
    rw [this]
    field_simp
  refine ⟨w, by rw [← hγ'0]; exact hwT, ?_, fun τ hτ => ?_, hEab, ?_⟩
  · -- `‖w‖² = h E_a^b ≤ h E < h c < δ²`
    have hEle : energy γ a b ≤ energy γ 0 1 :=
      intervalIntegral.integral_mono_interval ha0 hab.le hb1
        (Eventually.of_forall fun _ => sq_nonneg _) hγΩ.1.intervalIntegrable_norm_deriv_sq
    have h1 : ‖w‖ ^ 2 = h * energy γ a b := by rw [hEab]; field_simp
    have h2 : ‖w‖ ^ 2 < B.δ ^ 2 := by
      have := B.fine i
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 B.δ_pos.le h2
  · have hs : (τ - a) / h ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith [hτ.1]) hhpos.le, by
        rw [div_le_one hhpos]; have : b - a = h := by simp [hh_def, Subdivision.len, ha_def,
          hb_def]
        linarith [hτ.2]⟩
    have := hrayγ _ hs
    rw [hγ'0] at this
    rw [this]
    simp only [hγ'_def]
    congr 1
    field_simp
    ring
  · have h1 := riemDist_le_pathLength (N := N) (hγΩ.1.mono ha0 hab.le hb1)
      fun τ hτ => hγΩ.2.1 τ ⟨ha0.trans hτ.1, hτ.2.trans hb1⟩
    rwa [hLab] at h1

/-- **The break points of a broken geodesic in `Int Ω^c` lie in `U`**. -/
theorem nodeVal_mem_nodes {γ : ℝ → V} (hγ : γ ∈ B.brokenPaths) : B.nodeVal γ ∈ B.nodes := by
  choose w hwT hwδ hwexp hwE hwρ using fun i => B.exists_segVec hγ i
  refine ⟨fun j => hγ.1.2.1 _ ⟨B.t_nonneg _, B.t_le_one _⟩, fun i => ?_, ?_⟩
  · rw [B.vert_nodeVal hγ.1, B.vert_nodeVal hγ.1]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hwρ i)
  · -- `Σ ρ²/(t_{i+1} − tᵢ) ≤ Σ ‖wᵢ‖²/(t_{i+1} − tᵢ) = Σ E_{tᵢ}^{t_{i+1}} = E < c`
    have hint : ∀ i j, IntervalIntegrable (fun τ => ‖deriv γ τ‖ ^ 2) volume (B.t i) (B.t j) := by
      have hmem : ∀ i, B.t i ∈ uIcc (0 : ℝ) 1 := fun i => by
        rw [uIcc_of_le zero_le_one]; exact ⟨B.t_nonneg i, B.t_le_one i⟩
      exact fun i j => hγ.1.1.intervalIntegrable_norm_deriv_sq.mono_set
        (uIcc_subset_uIcc (hmem i) (hmem j))
    have hsum := sum_integral_fin B.t hint
    rw [B.t_zero, B.t_last] at hsum
    calc B.energy' (B.nodeVal γ) ≤ ∑ i, ‖w i‖ ^ 2 / B.len i := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [B.vert_nodeVal hγ.1, B.vert_nodeVal hγ.1]
          have h1 := ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (hwρ i)
          have h2 := B.len_pos i
          gcongr
      _ = energy γ 0 1 := by
          rw [energy, ← hsum]
          exact Finset.sum_congr rfl fun i _ => (hwE i).symm
      _ < c := hγ.2.2

/-- **A broken geodesic in `Int Ω^c` is the broken geodesic of its break points**. -/
theorem path_nodeVal {γ : ℝ → V} (hγ : γ ∈ B.brokenPaths) :
    EqOn (B.path (B.nodeVal γ)) γ (Icc 0 1) := by
  intro τ hτ
  have hy := B.nodeVal_mem_nodes hγ
  set i := B.segOf τ
  have hτi := B.mem_Icc_segOf hτ
  obtain ⟨w, hwT, hwδ, hwexp, -, hwρ⟩ := B.exists_segVec hγ i
  rw [B.path_eq_segPath hy i hτi, segPath, B.vert_nodeVal hγ.1, B.vert_nodeVal hγ.1]
  -- the join vector is `w`, by uniqueness
  have hball : ∀ σ ∈ Icc (0 : ℝ) 1, γ σ ∈ closedRiemBall N p √c := fun σ hσ =>
    mem_closedRiemBall_of_energy_le hγ.1 hγ.2.2.le hσ
  have hi0 : B.t i.castSucc ∈ Icc (0 : ℝ) 1 := ⟨B.t_nonneg _, B.t_le_one _⟩
  have hi1 : B.t i.succ ∈ Icc (0 : ℝ) 1 := ⟨B.t_nonneg _, B.t_le_one _⟩
  have hρ : riemDist (N := N) (γ (B.t i.castSucc)) (γ (B.t i.succ)) < ENNReal.ofReal B.δ :=
    (hwρ.trans_lt ((ENNReal.ofReal_lt_ofReal_iff B.δ_pos).2 hwδ))
  have hend : exp hN (γ (B.t i.castSucc)) w = γ (B.t i.succ) := by
    have := hwexp (B.t i.succ) ⟨(B.t_le_iff.2 Fin.castSucc_lt_succ.le), le_rfl⟩
    rwa [show (B.t i.succ - B.t i.castSucc) / B.len i = 1 from div_self (B.len_pos i).ne',
      one_smul] at this
  have hj := (B.joinVec_spec (hball _ hi0) (hball _ hi1) hρ).2.2.2.2 w hwT hwδ hend
  rw [← hj]
  exact hwexp τ hτi

/-- **Lemma 16.1** (Milnor p. 88), in the embedded setting: the broken geodesics in
`Int Ω(t₀, …, t_k)^c` correspond bijectively to their break points, which form Milnor's open set
`U ⊆ N^m`: `B.path` maps `U` into `Int Ω(t₀, …, t_k)^c` and is a right inverse of `B.nodeVal`, and
every element of `Int Ω(t₀, …, t_k)^c` is the broken geodesic of its break points (on `[0, 1]`). -/
theorem lemma_16_1 :
    (∀ y ∈ B.nodes, B.path y ∈ B.brokenPaths ∧ B.nodeVal (B.path y) = y ∧
      energy (B.path y) 0 1 = B.energy' y) ∧
    (∀ γ ∈ B.brokenPaths, B.nodeVal γ ∈ B.nodes ∧ EqOn (B.path (B.nodeVal γ)) γ (Icc 0 1)) :=
  ⟨fun y hy => ⟨⟨B.path_mem_pathSpace hy, B.isBroken_path hy, by
      rw [B.energy_path hy]; exact hy.2.2⟩, B.nodeVal_path hy, B.energy_path hy⟩,
    fun γ hγ => ⟨B.nodeVal_mem_nodes hγ, B.path_nodeVal hγ⟩⟩

end BrokenSetup

end Morse
