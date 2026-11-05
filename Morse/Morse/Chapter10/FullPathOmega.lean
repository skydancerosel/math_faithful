import Morse.Chapter10.FullPathDeform

/-!
Milnor, *Morse Theory*, §17, pp. 93–94, as repaired in Exposition/Chapter10.md, §5 ("A proof that
works", Lemma 17.C (ii)): the deformation onto dyadic broken geodesics on the side of `Ω`, which is
continuous for Milnor's metric `d`.

# The deformation of `X_k = Y_k ∩ Ω` onto broken geodesics

## Milnor's text, paraphrased

(p. 94) Milnor's map `h : Ω* → Ω` replaces a continuous path `ω` by the broken geodesic through
the points `ω(j A(ω))`; he says that `h` is clearly continuous, and that arguments as in §16 give
homotopies `h ∘ i ≃ id` and `i ∘ h ≃ id`.

## In the embedded setting

* `Morse.tendsto_integral_deriv_comp_sub_sq`: **`L²` continuity of velocities under a smooth
  map**: if `Fᵢ → F` uniformly, with `Fᵢ' → F'` in `L²` and bounded energies, then
  `(Φ ∘ Fᵢ)' → (Φ ∘ F)'` in `L²`, for `Φ` of class `C¹` near the curve `F`.
* `Morse.JoinSystem.IsGood.broken_mem_pathSpace`, `Morse.JoinSystem.IsGood.interp_mem_pathSpace`:
  the broken geodesic of a good path, and the deformation of a good piecewise smooth path, are
  piecewise smooth: on each dyadic piece they are given by one smooth formula
  (`Morse.JoinSystem.IsGood.exists_formula`).
* `Morse.JoinSystem.XSet J k`: the set `X_k = i⁻¹(Y_k)` of `Ω`
  (`Morse.JoinSystem.XSet_eq_preimage`).
* `Morse.JoinSystem.brokenΩ`: **the broken geodesic `b : Y_k → X_k`**, continuous from the uniform
  topology to Milnor's metric (`Morse.JoinSystem.continuous_brokenΩ`): on each dyadic piece it is
  a smooth function of the two vertices.
* `Morse.JoinSystem.interpΩ`: **the deformation `X_k × [0, 1] → X_k`** along minimal geodesics,
  continuous for Milnor's metric (`Morse.JoinSystem.continuous_interpΩ`).
* `Morse.JoinSystem.isHomotopyEquiv_toY`: **Lemma 17.C (ii) of the exposition**: the inclusion
  `X_k → Y_k` is a homotopy equivalence, with homotopy inverse `b`.

## What Milnor leaves implicit

* **Milnor's `h` is not continuous for `d`** (the exposition gives an example in which a new last
  segment of `h(ω)` is born with energy tending to infinity).  The subdivision is therefore kept
  fixed on each of the open sets `Y_k`, and the sets are glued with the Appendix
  (`Morse/Chapter10/FullPathTheorem.lean`).
* **Continuity for `d` needs velocities, not only speeds.**  `d` compares the speeds `‖γ'‖`, but a
  path given by a smooth formula `Φ(γ(s), b(s), u)` has velocity `DΦ(γ', b', 0)`, whose
  convergence needs `γ' → γ₀'` in `L²`; this does follow from convergence for `d`
  (`Morse.PathSp.tendsto_integral_norm_deriv_sub_sq`).
* **Paths at distance `0`.**  `d` is only a pseudo-metric (it ignores values off `[0, 1]`): the
  maps are normalized to be constant off `[0, 1]` (`Morse.JoinSystem.clampF`), and the homotopy
  `b ∘ i ≃ id` reaches the identity only up to paths at distance `0`, which is harmless
  (`Morse.PathSp.continuous_of_edist_eq_zero`).
-/

open Set Filter Topology Function Module Metric MeasureTheory
open scoped ContDiff Manifold RealInnerProductSpace ENNReal Interval NNReal

noncomputable section

namespace Morse

/-- **`L²` continuity of velocities under a smooth map**: if `Φ` is `C¹` on an open set `U`
containing the curve `F₀([a, b])`, `Fᵢ → F₀` uniformly on `[a, b]`, the velocities `Fᵢ'` are
bounded in `L²` and converge to `F₀'` in `L²`, then `(Φ ∘ Fᵢ)' → (Φ ∘ F₀)'` in `L²` (all curves
differentiable off finite sets). -/
theorem tendsto_integral_deriv_comp_sub_sq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {Φ : E → F} {U : Set E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 1 Φ U) {a b : ℝ} (hab : a ≤ b) {ι : Type*}
    {l : Filter ι} {Fs : ι → ℝ → E} {F₀ : ℝ → E} (hF₀ : ContinuousOn F₀ (Icc a b))
    (hF₀U : MapsTo F₀ (Icc a b) U) (hunif : TendstoUniformlyOn Fs F₀ l (Icc a b))
    {Fs' : ι → ℝ → E} {F₀' : ℝ → E}
    (hd : ∀ i, ∃ B : Finset ℝ, ∀ s ∈ Ioo a b, s ∉ B → HasDerivAt (Fs i) (Fs' i s) s)
    (hd₀ : ∃ B : Finset ℝ, ∀ s ∈ Ioo a b, s ∉ B → HasDerivAt F₀ (F₀' s) s)
    (hint : ∀ i, IntervalIntegrable (fun s => ‖Fs' i s‖ ^ 2) volume a b)
    (hintd : ∀ i, IntervalIntegrable (fun s => ‖Fs' i s - F₀' s‖ ^ 2) volume a b)
    {C : ℝ} (hC : ∀ᶠ i in l, ∫ s in a..b, ‖Fs' i s‖ ^ 2 ≤ C)
    (hL2 : Tendsto (fun i => ∫ s in a..b, ‖Fs' i s - F₀' s‖ ^ 2) l (𝓝 0)) :
    Tendsto (fun i => ∫ s in a..b, ‖deriv (Φ ∘ Fs i) s - deriv (Φ ∘ F₀) s‖ ^ 2) l (𝓝 0) := by
  classical
  -- a compact neighbourhood of the curve inside `U`
  have hK : IsCompact (F₀ '' Icc a b) := isCompact_Icc.image_of_continuousOn hF₀
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU (image_subset_iff.2 hF₀U)
  set K' := cthickening δ (F₀ '' Icc a b) with hK'
  have hK'c : IsCompact K' := hK.cthickening
  have hDc : ContinuousOn (fderiv ℝ Φ) U := hΦ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hDK' : ContinuousOn (fderiv ℝ Φ) K' := hDc.mono hδU
  obtain ⟨M, hM⟩ := hK'c.exists_bound_of_continuousOn hDK'
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ (self_subset_cthickening _
    (mem_image_of_mem F₀ (left_mem_Icc.2 hab))))
  have hUC := hK'c.uniformContinuousOn_of_continuous hDK'
  have hC0 : ∀ᶠ i in l, 0 ≤ C := hC.mono fun i hi =>
    le_trans (intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _) hi
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose `η` with `2 η² C < ε / 2`
  set η : ℝ := √(ε / (4 * (|C| + 1))) with hη_def
  have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hη2 : 2 * η ^ 2 * (|C| + 1) = ε / 2 := by
    rw [hη_def, Real.sq_sqrt (by positivity)]
    field_simp
    ring
  obtain ⟨ρ, hρ, hρη⟩ := Metric.uniformContinuousOn_iff.1 hUC η hη
  have hunif' := Metric.tendstoUniformlyOn_iff.1 hunif (min δ ρ) (lt_min hδ hρ)
  have hL2' := (Metric.tendsto_nhds.1 hL2) (ε / (4 * (M ^ 2 + 1))) (by positivity)
  filter_upwards [hunif', hL2', hC, hC0] with i hi hiL2 hiC hiC0
  -- pointwise estimates on `[a, b]`
  have hmem : ∀ s ∈ Icc a b, Fs i s ∈ K' := fun s hs => by
    refine mem_cthickening_of_dist_le _ (F₀ s) _ _ (mem_image_of_mem F₀ hs) ?_
    rw [dist_comm]
    exact (hi s hs).le.trans (min_le_left _ _)
  have hclose : ∀ s ∈ Icc a b, ‖fderiv ℝ Φ (Fs i s) - fderiv ℝ Φ (F₀ s)‖ < η := fun s hs => by
    rw [← dist_eq_norm]
    refine hρη _ (hmem s hs) _ (self_subset_cthickening _ (mem_image_of_mem F₀ hs)) ?_
    rw [dist_comm]
    exact lt_of_lt_of_le (hi s hs) (min_le_right _ _)
  obtain ⟨Bi, hBi⟩ := hd i
  obtain ⟨B₀, hB₀⟩ := hd₀
  have hpt : ∀ s ∈ Ioo a b, s ∉ Bi ∪ B₀ → ‖deriv (Φ ∘ Fs i) s - deriv (Φ ∘ F₀) s‖ ^ 2 ≤
      2 * η ^ 2 * ‖Fs' i s‖ ^ 2 + 2 * M ^ 2 * ‖Fs' i s - F₀' s‖ ^ 2 := by
    intro s hs hsB
    have hsI : s ∈ Icc a b := Ioo_subset_Icc_self hs
    have hUi : Fs i s ∈ U := hδU (hmem s hsI)
    have hU₀ : F₀ s ∈ U := hF₀U hsI
    have hdi : HasDerivAt (Φ ∘ Fs i) (fderiv ℝ Φ (Fs i s) (Fs' i s)) s :=
      ((hΦ.differentiableOn one_ne_zero _ hUi).differentiableAt
        (hU.mem_nhds hUi)).hasFDerivAt.comp_hasDerivAt
        s (hBi s hs fun h => hsB (Finset.mem_union_left _ h))
    have hd0 : HasDerivAt (Φ ∘ F₀) (fderiv ℝ Φ (F₀ s) (F₀' s)) s :=
      ((hΦ.differentiableOn one_ne_zero _ hU₀).differentiableAt
        (hU.mem_nhds hU₀)).hasFDerivAt.comp_hasDerivAt
        s (hB₀ s hs fun h => hsB (Finset.mem_union_right _ h))
    rw [hdi.deriv, hd0.deriv]
    have hsplit : fderiv ℝ Φ (Fs i s) (Fs' i s) - fderiv ℝ Φ (F₀ s) (F₀' s) =
        (fderiv ℝ Φ (Fs i s) - fderiv ℝ Φ (F₀ s)) (Fs' i s) +
          fderiv ℝ Φ (F₀ s) (Fs' i s - F₀' s) := by
      simp only [sub_apply, map_sub]
      abel
    rw [hsplit]
    have h1 : ‖(fderiv ℝ Φ (Fs i s) - fderiv ℝ Φ (F₀ s)) (Fs' i s)‖ ≤
        η * ‖Fs' i s‖ :=
      ((fderiv ℝ Φ (Fs i s) - fderiv ℝ Φ (F₀ s)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hclose s hsI).le (norm_nonneg _))
    have h2 : ‖fderiv ℝ Φ (F₀ s) (Fs' i s - F₀' s)‖ ≤
        M * ‖Fs' i s - F₀' s‖ :=
      ((fderiv ℝ Φ (F₀ s)).le_opNorm _).trans (mul_le_mul_of_nonneg_right
        (hM _ (self_subset_cthickening _ (mem_image_of_mem F₀ hsI))) (norm_nonneg _))
    have h3 := norm_add_le ((fderiv ℝ Φ (Fs i s) - fderiv ℝ Φ (F₀ s)) (Fs' i s))
      (fderiv ℝ Φ (F₀ s) (Fs' i s - F₀' s))
    have h4 : ‖(fderiv ℝ Φ (Fs i s) - fderiv ℝ Φ (F₀ s)) (Fs' i s) +
        fderiv ℝ Φ (F₀ s) (Fs' i s - F₀' s)‖ ≤
        η * ‖Fs' i s‖ + M * ‖Fs' i s - F₀' s‖ := h3.trans (add_le_add h1 h2)
    have h5 := pow_le_pow_left₀ (norm_nonneg _) h4 2
    nlinarith [sq_nonneg (η * ‖Fs' i s‖ - M * ‖Fs' i s - F₀' s‖)]
  -- integrate
  have hg : IntervalIntegrable (fun s => 2 * η ^ 2 * ‖Fs' i s‖ ^ 2 +
      2 * M ^ 2 * ‖Fs' i s - F₀' s‖ ^ 2) volume a b :=
    ((hint i).const_mul _).add ((hintd i).const_mul _)
  have hle : ∫ s in a..b, ‖deriv (Φ ∘ Fs i) s - deriv (Φ ∘ F₀) s‖ ^ 2 ≤
      ∫ s in a..b, (2 * η ^ 2 * ‖Fs' i s‖ ^ 2 +
        2 * M ^ 2 * ‖Fs' i s - F₀' s‖ ^ 2) := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
      (hg.1) ?_
    have hnull : volume (((Bi ∪ B₀ : Finset ℝ) : Set ℝ) ∪ {b}) = 0 :=
      ((Bi ∪ B₀).finite_toSet.union (finite_singleton b)).measure_zero _
    have hae : ∀ᵐ s ∂volume, s ∉ ((Bi ∪ B₀ : Finset ℝ) : Set ℝ) ∪ {b} :=
      measure_eq_zero_iff_ae_notMem.1 hnull
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hae] with s hs hsI
    have hs' : s ∈ Ioo a b := ⟨hsI.1, lt_of_le_of_ne hsI.2 fun h => hs (Or.inr h)⟩
    exact hpt s hs' fun h => hs (Or.inl h)
  rw [intervalIntegral.integral_add ((hint i).const_mul _) ((hintd i).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hle
  have hpos : 0 ≤ ∫ s in a..b, ‖deriv (Φ ∘ Fs i) s - deriv (Φ ∘ F₀) s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _
  have hd0 : 0 ≤ ∫ s in a..b, ‖Fs' i s - F₀' s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun _ _ => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hd0] at hiL2
  have e1 : 2 * η ^ 2 * (∫ s in a..b, ‖Fs' i s‖ ^ 2) ≤ ε / 2 := by
    rw [← hη2]
    have : (∫ s in a..b, ‖Fs' i s‖ ^ 2) ≤ |C| + 1 := hiC.trans (by
      linarith [le_abs_self C])
    have h2η : 0 ≤ 2 * η ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left this h2η
  have e2 : 2 * M ^ 2 * (∫ s in a..b, ‖Fs' i s - F₀' s‖ ^ 2) < ε / 2 := by
    have h1 : 2 * M ^ 2 * (∫ s in a..b, ‖Fs' i s - F₀' s‖ ^ 2) ≤
        2 * (M ^ 2 + 1) * (ε / (4 * (M ^ 2 + 1))) := by
      have : 2 * M ^ 2 ≤ 2 * (M ^ 2 + 1) := by nlinarith
      calc _ ≤ 2 * (M ^ 2 + 1) * (∫ s in a..b, ‖Fs' i s - F₀' s‖ ^ 2) :=
            mul_le_mul_of_nonneg_right this hd0
        _ ≤ _ := mul_le_mul_of_nonneg_left hiL2.le (by positivity)
    have h2 : 2 * (M ^ 2 + 1) * (ε / (4 * (M ^ 2 + 1))) = ε / 2 := by
      field_simp
      ring
    have h3 : 2 * M ^ 2 * (∫ s in a..b, ‖Fs' i s - F₀' s‖ ^ 2) <
        2 * (M ^ 2 + 1) * (ε / (4 * (M ^ 2 + 1))) := by
      calc _ ≤ 2 * (M ^ 2 + 1) * (∫ s in a..b, ‖Fs' i s - F₀' s‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (by nlinarith) hd0
        _ < _ := mul_lt_mul_of_pos_left hiL2 (by positivity)
    linarith
  linarith

namespace JoinSystem

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {N : Set V} {J : JoinSystem N} {k : ℕ} {c : ℝ → V}

/-- A closed interval without dyadic points of level `k` inside lies in one dyadic piece. -/
theorem exists_piece_of_Icc {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hD : ∀ j ≤ 2 ^ k, dy k j ∉ Ioo a b) :
    ∃ j < 2 ^ k, Icc a b ⊆ Icc (dy k j) (dy k (j + 1)) := by
  set m := (a + b) / 2 with hm
  have hm01 : m ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hmab : m ∈ Ioo a b := ⟨by linarith, by linarith⟩
  set j := dseg k m with hj
  have hjk := dseg_lt k m
  have hmj := mem_Icc_dseg (k := k) hm01
  refine ⟨j, hjk, fun s hs => ⟨?_, ?_⟩⟩
  · by_contra h
    push Not at h
    have h1 : dy k j ≤ m := hmj.1
    rcases eq_or_lt_of_le h1 with h2 | h2
    · exact hD j hjk.le (h2 ▸ hmab)
    · exact hD j hjk.le ⟨by linarith [hs.1], by linarith [hmab.2]⟩
  · by_contra h
    push Not at h
    have h1 : m ≤ dy k (j + 1) := hmj.2
    rcases eq_or_lt_of_le h1 with h2 | h2
    · exact hD (j + 1) hjk (h2 ▸ hmab)
    · exact hD (j + 1) hjk ⟨by linarith [hmab.1], by linarith [hs.2]⟩

omit [FiniteDimensional ℝ V] in
/-- On a piece, the broken geodesic and the deformation are given by one smooth formula. -/
theorem IsGood.exists_formula (hc : J.IsGood k c) {j : ℕ} (hj : j < 2 ^ k) :
    ∃ O ∈ J.good, (∀ s ∈ Icc (dy k j) (dy k (j + 1)), c s ∈ N ∩ O) ∧
    ∃ U : Set (V × V), IsOpen U ∧ (N ∩ O) ×ˢ (N ∩ O) ⊆ U ∧ ∃ ε > 0, ∃ Φ : (V × V) × ℝ → V,
      ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-ε) (1 + ε)) ∧
      (∀ s ∈ Icc (dy k j) (dy k (j + 1)),
        J.broken k c s = Φ ((c (dy k j), c (dy k (j + 1))), s * 2 ^ k - j)) ∧
      ∀ s ∈ Icc (dy k j) (dy k (j + 1)), ∀ u ∈ Icc (0 : ℝ) 1,
        J.interp k c u s = Φ ((c s, Φ ((c (dy k j), c (dy k (j + 1))), s * 2 ^ k - j)), u) := by
  obtain ⟨O, hO, hOc⟩ := hc j hj
  obtain ⟨U, hU, hNU, ε, hε, Φ, hΦ, hΦeq⟩ := J.smooth O hO
  have hIoo : ∀ u ∈ Icc (0 : ℝ) 1, u ∈ Ioo (-ε) (1 + ε) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb : ∀ s ∈ Icc (dy k j) (dy k (j + 1)),
      J.broken k c s = Φ ((c (dy k j), c (dy k (j + 1))), s * 2 ^ k - j) := fun s hs => by
    rw [hc.broken_eq hj hs, hΦeq _ (hOc _ ⟨le_rfl, (dy_lt_succ k j).le⟩) _
      (hOc _ ⟨(dy_lt_succ k j).le, le_rfl⟩) _ (hIoo _ (param_mem_Icc hs))]
  refine ⟨O, hO, hOc, U, hU, hNU, ε, hε, Φ, hΦ, hb, fun s hs u hu => ?_⟩
  rw [JoinSystem.interp, ← hb s hs,
    hΦeq _ (hOc s hs) _ (broken_mem_of hc hj hO hOc hs) _ (hIoo u hu)]

/-- The dyadic points of level `k`, as a finite set. -/
def dyPts (k : ℕ) : Finset ℝ := (Finset.range (2 ^ k + 1)).image (dy k)

theorem dy_mem_dyPts {j : ℕ} (hj : j ≤ 2 ^ k) : dy k j ∈ dyPts k :=
  Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩

omit [FiniteDimensional ℝ V] in
/-- **The broken geodesic is smooth on every interval without dyadic points.** -/
theorem IsGood.contDiffOn_broken (hc : J.IsGood k c) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) (hD : ∀ x ∈ dyPts k, x ∉ Ioo a b) : ContDiffOn ℝ ∞ (J.broken k c) (Icc a b) := by
  obtain ⟨j, hj, hsub⟩ := exists_piece_of_Icc ha hab hb fun j hj => hD _ (dy_mem_dyPts hj)
  obtain ⟨O, hO, hOc, U, hU, hNU, ε, hε, Φ, hΦ, hb', -⟩ := hc.exists_formula hj
  have hIoo : ∀ u ∈ Icc (0 : ℝ) 1, u ∈ Ioo (-ε) (1 + ε) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  refine ContDiffOn.congr (f := fun s => Φ ((c (dy k j), c (dy k (j + 1))), s * 2 ^ k - j)) ?_
    fun s hs => hb' s (hsub hs)
  refine hΦ.comp (contDiffOn_const.prodMk ((contDiffOn_id.mul contDiffOn_const).sub
    contDiffOn_const)) fun s hs => ⟨hNU ⟨hOc _ ⟨le_rfl, (dy_lt_succ k j).le⟩,
      hOc _ ⟨(dy_lt_succ k j).le, le_rfl⟩⟩, hIoo _ (param_mem_Icc (hsub hs))⟩

omit [FiniteDimensional ℝ V] in
/-- **The deformation is smooth on every interval without dyadic points where the path is.** -/
theorem IsGood.contDiffOn_interp (hc : J.IsGood k c) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hb : b ≤ 1) (hD : ∀ x ∈ dyPts k, x ∉ Ioo a b) (hcs : ContDiffOn ℝ ∞ c (Icc a b)) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : ContDiffOn ℝ ∞ (J.interp k c u) (Icc a b) := by
  obtain ⟨j, hj, hsub⟩ := exists_piece_of_Icc ha hab hb fun j hj => hD _ (dy_mem_dyPts hj)
  obtain ⟨O, hO, hOc, U, hU, hNU, ε, hε, Φ, hΦ, hb', hH⟩ := hc.exists_formula hj
  have hIoo : ∀ u ∈ Icc (0 : ℝ) 1, u ∈ Ioo (-ε) (1 + ε) := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hinner : ContDiffOn ℝ ∞ (fun s => Φ ((c (dy k j), c (dy k (j + 1))), s * 2 ^ k - j))
      (Icc a b) :=
    hΦ.comp (contDiffOn_const.prodMk ((contDiffOn_id.mul contDiffOn_const).sub
      contDiffOn_const)) fun s hs => ⟨hNU ⟨hOc _ ⟨le_rfl, (dy_lt_succ k j).le⟩,
        hOc _ ⟨(dy_lt_succ k j).le, le_rfl⟩⟩, hIoo _ (param_mem_Icc (hsub hs))⟩
  refine ContDiffOn.congr (f := fun s =>
    Φ ((c s, Φ ((c (dy k j), c (dy k (j + 1))), s * 2 ^ k - j)), u)) ?_
    fun s hs => hH s (hsub hs) u hu
  refine hΦ.comp ((hcs.prodMk hinner).prodMk contDiffOn_const) fun s hs => ⟨?_, hIoo u hu⟩
  rw [← hb' s (hsub hs)]
  exact hNU ⟨hOc s (hsub hs), broken_mem_of hc hj hO hOc (hsub hs)⟩

omit [FiniteDimensional ℝ V] in
theorem IsGood.mem_N_broken (hc : J.IsGood k c) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    J.broken k c s ∈ N := by
  obtain ⟨O, hO, hOc⟩ := hc (dseg k s) (dseg_lt k s)
  exact (broken_mem_of hc (dseg_lt k s) hO hOc (mem_Icc_dseg hs)).1

omit [FiniteDimensional ℝ V] in
theorem IsGood.mem_N_interp (hc : J.IsGood k c) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : J.interp k c u s ∈ N := by
  obtain ⟨O, hO, hOc⟩ := hc (dseg k s) (dseg_lt k s)
  exact (interp_mem_of hc (dseg_lt k s) hO hOc (mem_Icc_dseg hs) hu).1

omit [FiniteDimensional ℝ V] in
/-- **The broken geodesic of a good path is in `Ω`.** -/
theorem IsGood.broken_mem_pathSpace {p q : V} (hc : J.IsGood k c) (h0 : c 0 = p) (h1 : c 1 = q) :
    J.broken k c ∈ pathSpace N p q := by
  have hpw : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ dyPts k, x ∉ Ioo s t) →
      ContDiffOn ℝ ∞ (J.broken k c) (Icc s t) := fun s t hs hst ht hD =>
    hc.contDiffOn_broken hs hst ht hD
  refine ⟨⟨zero_le_one, continuousOn_of_piecewise fun s t hs hst ht hD =>
    (hpw s t hs hst ht hD).continuousOn, dyPts k, hpw⟩, fun s hs => hc.mem_N_broken hs, ?_, ?_⟩
  · rw [broken_zero hc, h0]
  · rw [broken_one hc, h1]

omit [FiniteDimensional ℝ V] in
/-- **The deformation of a good path of `Ω` stays in `Ω`.** -/
theorem IsGood.interp_mem_pathSpace {p q : V} (hc : J.IsGood k c) (hcΩ : c ∈ pathSpace N p q)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : J.interp k c u ∈ pathSpace N p q := by
  classical
  obtain ⟨-, -, Bc, hBc⟩ := hcΩ.1
  have hpw : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ dyPts k ∪ Bc, x ∉ Ioo s t) →
      ContDiffOn ℝ ∞ (J.interp k c u) (Icc s t) := fun s t hs hst ht hD =>
    hc.contDiffOn_interp hs hst ht (fun x hx => hD x (Finset.mem_union_left _ hx))
      (hBc s t hs hst ht fun x hx => hD x (Finset.mem_union_right _ hx)) hu
  refine ⟨⟨zero_le_one, continuousOn_of_piecewise fun s t hs hst ht hD =>
    (hpw s t hs hst ht hD).continuousOn, dyPts k ∪ Bc, hpw⟩,
    fun s hs => hc.mem_N_interp hs hu, ?_, ?_⟩
  · rw [interp_zero_right hc, hcΩ.2.2.1]
  · rw [interp_one_right hc, hcΩ.2.2.2]

/-! ### The maps on `Ω` -/

section Omega

open scoped unitInterval

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {p q : V}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A function extended from `[0, 1]` by constants. -/
def clampF (c : ℝ → V) : ℝ → V := fun s => c (projIcc (0 : ℝ) 1 zero_le_one s)

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem clampF_eqOn (c : ℝ → V) : EqOn (clampF c) c (Icc 0 1) := fun s hs => by
  simp [clampF, projIcc_of_mem _ hs]

variable (J) in
/-- **The sets `X_k = Y_k ∩ Ω`** (Lemma 17.C of the exposition). -/
def XSet (k : ℕ) : Set (PathSp N p q) := {γ | J.IsGood k γ}

omit [FiniteDimensional ℝ V] in
theorem ext_toPathC_eqOn (γ : PathSp N p q) : EqOn (ext (PathSp.toPathC γ)) γ (Icc 0 1) :=
  fun s hs => by rw [ext_of_mem _ hs]; rfl

omit [FiniteDimensional ℝ V] in
theorem XSet_eq_preimage (k : ℕ) :
    J.XSet k = PathSp.toPathC ⁻¹' J.YSet k (p := p) (q := q) := by
  ext γ
  exact (isGood_congr (ext_toPathC_eqOn γ)).symm

variable (J) in
/-- **The broken geodesic `b : Y_k → X_k`** (`b = D(·, 1)` in the exposition), normalized to be
constant off `[0, 1]`. -/
def brokenΩ (k : ℕ) (γ : ↥(J.YSet k (p := p) (q := q))) : ↥(J.XSet k (p := p) (q := q)) :=
  ⟨⟨clampF (J.broken k (ext γ.1)), PathSp.pathSpace_congr
    (IsGood.broken_mem_pathSpace γ.2 (by rw [ext_of_mem _ ⟨le_rfl, zero_le_one⟩]; exact γ.1.2.2.1)
      (by rw [ext_of_mem _ ⟨zero_le_one, le_rfl⟩]; exact γ.1.2.2.2)) (clampF_eqOn _)⟩,
    (isGood_congr (clampF_eqOn _)).2 (IsGood.broken γ.2)⟩

omit [FiniteDimensional ℝ V] in
theorem brokenΩ_eqOn (k : ℕ) (γ : ↥(J.YSet k (p := p) (q := q))) :
    EqOn ((J.brokenΩ k γ : PathSp N p q) : ℝ → V) (J.broken k (ext γ.1)) (Icc 0 1) :=
  clampF_eqOn (J.broken k (ext γ.1))

omit [FiniteDimensional ℝ V] in
/-- Integrals of the squared difference of two velocities split over adjacent intervals. -/
theorem integral_deriv_sub_sq_add {α β : PathSp N p q} {a x b : ℝ} (ha : 0 ≤ a) (hax : a ≤ x)
    (hxb : x ≤ b) (hb : b ≤ 1) :
    ∫ t in a..b, ‖deriv α t - deriv β t‖ ^ 2 =
      (∫ t in a..x, ‖deriv α t - deriv β t‖ ^ 2) + ∫ t in x..b, ‖deriv α t - deriv β t‖ ^ 2 := by
  have hint : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 →
      IntervalIntegrable (fun t => ‖deriv α t - deriv β t‖ ^ 2) volume a b := fun a b ha hab hb =>
    intervalIntegrable_comp_deriv α.mem.1 β.mem.1 (Φ := fun z : V × V => ‖z.1 - z.2‖ ^ 2)
      (by fun_prop) ha hab hb
  exact (intervalIntegral.integral_add_adjacent_intervals (hint a x ha hax (hxb.trans hb))
    (hint x b (ha.trans hax) hxb hb)).symm

/-- **The velocities of the broken geodesics converge in `L²`** (`γ → γ₀` uniformly). -/
theorem tendsto_integral_brokenΩ {k : ℕ} (γ₀ : ↥(J.YSet k (p := p) (q := q))) :
    Tendsto (fun γ : ↥(J.YSet k (p := p) (q := q)) => ∫ t in (0 : ℝ)..1,
      ‖deriv ((J.brokenΩ k γ : PathSp N p q) : ℝ → V) t -
        deriv ((J.brokenΩ k γ₀ : PathSp N p q) : ℝ → V) t‖ ^ 2) (𝓝 γ₀) (𝓝 0) := by
  refine piecewise_induction (B := dyPts k) (lo := 0) (hi := 1)
    (P := fun a b => Tendsto (fun γ : ↥(J.YSet k (p := p) (q := q)) => ∫ t in a..b,
      ‖deriv ((J.brokenΩ k γ : PathSp N p q) : ℝ → V) t -
        deriv ((J.brokenΩ k γ₀ : PathSp N p q) : ℝ → V) t‖ ^ 2) (𝓝 γ₀) (𝓝 0))
    (fun a b ha hab hb hD => ?_) (fun a x b ha hax hxb hb _ h₁ h₂ => ?_) 0 1 le_rfl zero_lt_one
    le_rfl
  · obtain ⟨j, hj, hsub⟩ := exists_piece_of_Icc ha hab hb fun j hj => hD _ (dy_mem_dyPts hj)
    have hg₀ : J.IsGood k (ext γ₀.1) := γ₀.2
    obtain ⟨O, hO, hOc⟩ := hg₀ j hj
    obtain ⟨U, hU, hNU, ε, hε, Φ, hΦ, hΦeq⟩ := J.smooth O hO
    have hIoo : ∀ u ∈ Icc (0 : ℝ) 1, u ∈ Ioo (-ε) (1 + ε) := fun u hu =>
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    -- near `γ₀`, the `j`-th piece stays in `O`
    have hmaps : MapsTo ((γ₀.1 : PathC N p q) : C(I, V)) (piece k j) O := by
      intro t ht
      have := (hOc t ht).2
      rwa [ext_of_mem _ t.2] at this
    have hev : ∀ᶠ γ in 𝓝 γ₀, MapsTo (((γ : ↥(J.YSet k (p := p) (q := q))).1 : PathC N p q) :
        C(I, V)) (piece k j) O :=
      ((continuous_subtype_val.comp continuous_subtype_val).tendsto γ₀).eventually
        (ContinuousMap.eventually_mapsTo (isCompact_piece k j) (J.isOpen O hO) hmaps)
    have hmemO : ∀ γ : ↥(J.YSet k (p := p) (q := q)),
        MapsTo ((γ.1 : PathC N p q) : C(I, V)) (piece k j) O →
          ∀ s ∈ Icc (dy k j) (dy k (j + 1)), ext γ.1 s ∈ N ∩ O := by
      intro γ hγ s hs
      have hs01 : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(dy_nonneg k j).trans hs.1, hs.2.trans (dy_le_one (by omega))⟩
      refine ⟨ext_mem _ s, ?_⟩
      rw [ext_of_mem _ hs01]
      exact hγ (show (⟨s, hs01⟩ : I) ∈ piece k j from hs)
    -- the formula `b_γ = Φ ∘ F_γ` on the piece
    set F : ↥(J.YSet k (p := p) (q := q)) → ℝ → (V × V) × ℝ := fun γ s =>
      ((ext γ.1 (dy k j), ext γ.1 (dy k (j + 1))), s * 2 ^ k - j) with hF
    have hformula : ∀ γ : ↥(J.YSet k (p := p) (q := q)),
        MapsTo ((γ.1 : PathC N p q) : C(I, V)) (piece k j) O → ∀ s ∈ Icc a b,
          ((J.brokenΩ k γ : PathSp N p q) : ℝ → V) s = (Φ ∘ F γ) s := by
      intro γ hγ s hs
      have hs' := hsub hs
      have hs01 : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(dy_nonneg k j).trans hs'.1, hs'.2.trans (dy_le_one (by omega))⟩
      rw [brokenΩ_eqOn k γ hs01, (show J.IsGood k (ext γ.1) from γ.2).broken_eq hj hs']
      exact (hΦeq _ (hmemO γ hγ _ ⟨le_rfl, (dy_lt_succ k j).le⟩) _
        (hmemO γ hγ _ ⟨(dy_lt_succ k j).le, le_rfl⟩) _ (hIoo _ (param_mem_Icc hs'))).symm
    have hderiv : ∀ γ : ↥(J.YSet k (p := p) (q := q)),
        MapsTo ((γ.1 : PathC N p q) : C(I, V)) (piece k j) O → ∀ s ∈ Ioo a b,
          deriv ((J.brokenΩ k γ : PathSp N p q) : ℝ → V) s = deriv (Φ ∘ F γ) s := by
      intro γ hγ s hs
      exact Filter.EventuallyEq.deriv_eq (eventually_of_mem (Icc_mem_nhds hs.1 hs.2)
        (hformula γ hγ))
    -- the `L²` convergence of `(Φ ∘ F_γ)'`
    have hmain := tendsto_integral_deriv_comp_sub_sq (Φ := Φ) (hU.prod isOpen_Ioo)
      (hΦ.of_le (by norm_cast)) hab.le (l := 𝓝 γ₀) (Fs := F) (F₀ := F γ₀)
      (Fs' := fun _ _ => ((0, 0), (2 : ℝ) ^ k)) (F₀' := fun _ => ((0, 0), (2 : ℝ) ^ k))
      (by fun_prop) (fun s hs => ⟨hNU ⟨hmemO γ₀ hmaps _ ⟨le_rfl, (dy_lt_succ k j).le⟩,
        hmemO γ₀ hmaps _ ⟨(dy_lt_succ k j).le, le_rfl⟩⟩, hIoo _ (param_mem_Icc (hsub hs))⟩)
      ?_ (fun γ => ⟨∅, fun s _ _ => ?_⟩) ⟨∅, fun s _ _ => ?_⟩
      (fun γ => intervalIntegrable_const) (fun γ => by simp)
      (C := ∫ s in a..b, ‖(((0 : V), (0 : V)), (2 : ℝ) ^ k)‖ ^ 2)
      (Eventually.of_forall fun γ => le_rfl) (by simp)
    · refine hmain.congr' ?_
      filter_upwards [hev] with γ hγ
      refine intervalIntegral.integral_congr_Ioo_of_le hab.le fun s hs => ?_
      rw [hderiv γ hγ s hs, hderiv γ₀ hmaps s hs]
    · -- uniform convergence of `F_γ`
      rw [Metric.tendstoUniformlyOn_iff]
      intro δ hδ
      have h1 : Tendsto (fun γ : ↥(J.YSet k (p := p) (q := q)) =>
          (ext γ.1 (dy k j), ext γ.1 (dy k (j + 1)))) (𝓝 γ₀)
          (𝓝 (ext γ₀.1 (dy k j), ext γ₀.1 (dy k (j + 1)))) :=
        ((continuous_ext_comp (continuous_subtype_val) continuous_const).prodMk
          (continuous_ext_comp continuous_subtype_val continuous_const)).tendsto γ₀
      filter_upwards [Metric.tendsto_nhds.1 h1 δ hδ] with γ hγ s _
      have : dist (F γ₀ s) (F γ s) = dist (ext γ.1 (dy k j), ext γ.1 (dy k (j + 1)))
          (ext γ₀.1 (dy k j), ext γ₀.1 (dy k (j + 1))) := by
        rw [dist_comm, Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
      rw [this]
      exact hγ
    · exact ((hasDerivAt_const s _).prodMk
        ((hasDerivAt_id s).mul_const _ |>.sub_const _)).congr_deriv (by simp; rfl)
    · exact ((hasDerivAt_const s _).prodMk
        ((hasDerivAt_id s).mul_const _ |>.sub_const _)).congr_deriv (by simp; rfl)
  · rw [show (0 : ℝ) = 0 + 0 by ring]
    refine (h₁.add h₂).congr fun γ => ?_
    exact (integral_deriv_sub_sq_add ha hax.le hxb.le hb).symm

variable (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
include hN

/-- **`b : Y_k → X_k` is continuous from `d*` to Milnor's `d`.** -/
theorem continuous_brokenΩ (k : ℕ) : Continuous (J.brokenΩ k (p := p) (q := q)) := by
  refine continuous_iff_continuousAt.2 fun γ₀ => ?_
  rw [ContinuousAt, tendsto_subtype_rng]
  refine PathSp.tendsto_of_tendsto_apply_of_integral hN (fun s hs => ?_)
    (J.tendsto_integral_brokenΩ γ₀)
  have key : ∀ γ : ↥(J.YSet k (p := p) (q := q)), ((J.brokenΩ k γ : PathSp N p q) : ℝ → V) s =
      J.interp k (ext γ.1) ((1 : I) : ℝ) ((⟨s, hs⟩ : I) : ℝ) := by
    intro γ
    rw [brokenΩ_eqOn k γ hs]
    exact (interp_one γ.2 hs).symm
  simp only [key]
  exact ((J.continuous_interp_star k).tendsto ((γ₀, (1 : I)), (⟨s, hs⟩ : I))).comp
    (((continuous_id.prodMk continuous_const).prodMk continuous_const).tendsto γ₀)

omit hN

variable (J) in
/-- The inclusion `X_k → Y_k`. -/
def toY (k : ℕ) : C(↥(J.XSet k (p := p) (q := q)), ↥(J.YSet k (p := p) (q := q))) where
  toFun γ := ⟨PathSp.toPathC γ.1, (isGood_congr (ext_toPathC_eqOn γ.1)).2 γ.2⟩
  continuous_toFun := (PathSp.continuous_toPathC.comp continuous_subtype_val).subtype_mk _

variable (J) in
/-- **The deformation `H : X_k × [0, 1] → X_k`** (normalized to be constant off `[0, 1]`). -/
def interpΩ (k : ℕ) (x : ↥(J.XSet k (p := p) (q := q)) × I) : ↥(J.XSet k (p := p) (q := q)) :=
  ⟨⟨clampF (J.interp k x.1.1 x.2), PathSp.pathSpace_congr
    (IsGood.interp_mem_pathSpace x.1.2 x.1.1.2 x.2.2) (clampF_eqOn _)⟩,
    (isGood_congr (clampF_eqOn _)).2 (IsGood.interp x.1.2 x.2.2)⟩

omit [FiniteDimensional ℝ V] in
theorem interpΩ_eqOn (k : ℕ) (x : ↥(J.XSet k (p := p) (q := q)) × I) :
    EqOn ((J.interpΩ k x : PathSp N p q) : ℝ → V) (J.interp k x.1.1 x.2) (Icc 0 1) :=
  clampF_eqOn (J.interp k x.1.1 x.2)

theorem interpΩ_eq_star (k : ℕ) (x : ↥(J.XSet k (p := p) (q := q)) × I) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : ((J.interpΩ k x : PathSp N p q) : ℝ → V) s =
      J.interp k (ext (J.toY k x.1).1) x.2 s := by
  rw [interpΩ_eqOn k x hs]
  exact (interp_congr (ext_toPathC_eqOn x.1.1) hs).symm

/-- The broken geodesic of a path of `X_k`, as a function, agrees with `b ∘ i` on `[0, 1]`. -/
theorem brokenΩ_toY_eqOn (k : ℕ) (γ : ↥(J.XSet k (p := p) (q := q))) :
    EqOn ((J.brokenΩ k (J.toY k γ) : PathSp N p q) : ℝ → V) (J.broken k γ.1) (Icc 0 1) :=
  fun s hs => by
    rw [brokenΩ_eqOn k _ hs]
    exact broken_congr (ext_toPathC_eqOn γ.1)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
theorem norm_pair_zero_sq_le {V : Type*} [NormedAddCommGroup V] (x y : V) :
    ‖((x, y), (0 : ℝ))‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [Prod.norm_def, Prod.norm_def, norm_zero, max_eq_left (le_max_of_le_left (norm_nonneg _))]
  rcases le_total ‖x‖ ‖y‖ with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg ‖x‖]
  · rw [max_eq_left h]
    nlinarith [sq_nonneg ‖y‖]

omit [FiniteDimensional ℝ V] in
/-- A continuous function of the velocities of four piecewise smooth paths is integrable. -/
theorem intervalIntegrable_comp_deriv₄ {α β γ δ : ℝ → V} (hα : IsPiecewiseSmooth α 0 1)
    (hβ : IsPiecewiseSmooth β 0 1) (hγ : IsPiecewiseSmooth γ 0 1) (hδ : IsPiecewiseSmooth δ 0 1)
    {Φ : (V × V) × (V × V) → ℝ} (hΦ : Continuous Φ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) :
    IntervalIntegrable (fun t => Φ ((deriv α t, deriv β t), (deriv γ t, deriv δ t)))
      volume a b := by
  classical
  obtain ⟨B₁, h₁⟩ := hα.exists_deriv_piece
  obtain ⟨B₂, h₂⟩ := hβ.exists_deriv_piece
  obtain ⟨B₃, h₃⟩ := hγ.exists_deriv_piece
  obtain ⟨B₄, h₄⟩ := hδ.exists_deriv_piece
  refine intervalIntegrable_of_piecewise (B := B₁ ∪ B₂ ∪ B₃ ∪ B₄) (lo := 0) (hi := 1)
    (fun s t hs hst ht hB => ?_) ha hab hb
  obtain ⟨K₁, hK₁, hE₁⟩ := h₁ s t hs hst ht fun x hx =>
    hB x (by simp [hx])
  obtain ⟨K₂, hK₂, hE₂⟩ := h₂ s t hs hst ht fun x hx =>
    hB x (by simp [hx])
  obtain ⟨K₃, hK₃, hE₃⟩ := h₃ s t hs hst ht fun x hx =>
    hB x (by simp [hx])
  obtain ⟨K₄, hK₄, hE₄⟩ := h₄ s t hs hst ht fun x hx =>
    hB x (by simp [hx])
  exact ⟨fun τ => Φ ((K₁ τ, K₂ τ), (K₃ τ, K₄ τ)),
    hΦ.comp_continuousOn ((hK₁.prodMk hK₂).prodMk (hK₃.prodMk hK₄)),
    fun τ hτ => by simp only [hE₁ hτ, hE₂ hτ, hE₃ hτ, hE₄ hτ]⟩

include hN in
/-- **The deformation `H : X_k × [0, 1] → X_k` is continuous for Milnor's metric** (the step that
fails for Milnor's `h`): pointwise convergence, and `L²` convergence of the velocities on each
piece, `H(γ, u)(s) = Φ(γ(s), b(γ)(s), u)` with `Φ` smooth (Lemma 17.B), from the `L²`
convergence of the velocities of `γ` and of its broken geodesic. -/
theorem continuous_interpΩ (k : ℕ) : Continuous (J.interpΩ k (p := p) (q := q)) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [ContinuousAt, tendsto_subtype_rng]
  set bb : ↥(J.XSet k (p := p) (q := q)) × I → PathSp N p q := fun x =>
    (J.brokenΩ k (J.toY k x.1) : PathSp N p q) with hbb
  have hγ : Tendsto (fun x : ↥(J.XSet k (p := p) (q := q)) × I => (x.1 : PathSp N p q)) (𝓝 x₀)
      (𝓝 (x₀.1 : PathSp N p q)) := (continuous_subtype_val.comp continuous_fst).tendsto x₀
  have hbc : Continuous bb := (continuous_subtype_val.comp (J.continuous_brokenΩ hN k)).comp
    ((J.toY k).continuous.comp continuous_fst)
  have hbt : Tendsto bb (𝓝 x₀) (𝓝 (bb x₀)) := hbc.tendsto x₀
  have hu : Tendsto (fun x : ↥(J.XSet k (p := p) (q := q)) × I => (x.2 : ℝ)) (𝓝 x₀)
      (𝓝 (x₀.2 : ℝ)) := (continuous_subtype_val.comp continuous_snd).tendsto x₀
  refine PathSp.tendsto_of_tendsto_apply_of_integral hN (fun s hs => ?_) ?_
  · -- pointwise convergence, through `Ω*`
    have key : ∀ x : ↥(J.XSet k (p := p) (q := q)) × I,
        ((J.interpΩ k x : PathSp N p q) : ℝ → V) s =
          J.interp k (ext (J.toY k x.1).1) ((x.2 : I) : ℝ) ((⟨s, hs⟩ : I) : ℝ) :=
      fun x => interpΩ_eq_star k x hs
    have hg : Continuous fun x : ↥(J.XSet k (p := p) (q := q)) × I =>
        (((J.toY k x.1, x.2), (⟨s, hs⟩ : I)) :
          (↥(J.YSet k (p := p) (q := q)) × I) × I) :=
      (((J.toY k).continuous.comp continuous_fst).prodMk continuous_snd).prodMk continuous_const
    have hcont := (J.continuous_interp_star k).comp hg
    have h2 := hcont.tendsto x₀
    refine Tendsto.congr (fun x => (key x).symm) ?_
    rw [key x₀]
    exact h2
  -- `L²` convergence of the velocities
  have hL2γ := PathSp.tendsto_integral_norm_deriv_sub_sq hγ
  have hL2b := PathSp.tendsto_integral_norm_deriv_sub_sq hbt
  have hEγ : Tendsto (fun x : ↥(J.XSet k (p := p) (q := q)) × I =>
      energy ((x.1 : PathSp N p q) : ℝ → V) 0 1) (𝓝 x₀)
      (𝓝 (energy ((x₀.1 : PathSp N p q) : ℝ → V) 0 1)) :=
    ((PathSp.continuous_energy le_rfl zero_le_one le_rfl).tendsto _).comp hγ
  have hEb : Tendsto (fun x => energy ((bb x : PathSp N p q) : ℝ → V) 0 1) (𝓝 x₀)
      (𝓝 (energy ((bb x₀ : PathSp N p q) : ℝ → V) 0 1)) :=
    ((PathSp.continuous_energy le_rfl zero_le_one le_rfl).tendsto _).comp hbt
  obtain ⟨-, -, B₀, hB₀⟩ := (x₀.1 : PathSp N p q).mem.1
  refine piecewise_induction (B := dyPts k ∪ B₀) (lo := 0) (hi := 1)
    (P := fun a b => Tendsto (fun x : ↥(J.XSet k (p := p) (q := q)) × I => ∫ t in a..b,
      ‖deriv ((J.interpΩ k x : PathSp N p q) : ℝ → V) t -
        deriv ((J.interpΩ k x₀ : PathSp N p q) : ℝ → V) t‖ ^ 2) (𝓝 x₀) (𝓝 0))
    (fun a b ha hab hb hD => ?_) (fun a x b ha hax hxb hb _ h₁ h₂ => ?_) 0 1 le_rfl zero_lt_one
    le_rfl
  · have hDk : ∀ x ∈ dyPts k, x ∉ Ioo a b := fun x hx => hD x (Finset.mem_union_left _ hx)
    obtain ⟨j, hj, hsub⟩ := exists_piece_of_Icc ha hab hb fun j hj => hDk _ (dy_mem_dyPts hj)
    have hg₀ : J.IsGood k ((x₀.1 : PathSp N p q) : ℝ → V) := x₀.1.2
    obtain ⟨O, hO, hOc⟩ := hg₀ j hj
    obtain ⟨U, hU, hNU, ε, hε, Φ, hΦ, hΦeq⟩ := J.smooth O hO
    have hIoo : ∀ u ∈ Icc (0 : ℝ) 1, u ∈ Ioo (-ε) (1 + ε) := fun u hu =>
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    -- near `x₀`, the `j`-th piece stays in `O`
    have hmaps : MapsTo (((J.toY k x₀.1).1 : PathC N p q) : C(I, V)) (piece k j) O := by
      intro t ht
      have := (hOc t ht).2
      rwa [← ext_toPathC_eqOn x₀.1.1 t.2, ext_of_mem _ t.2] at this
    have hev : ∀ᶠ x in 𝓝 x₀, MapsTo (((J.toY k (x : ↥(J.XSet k (p := p) (q := q)) × I).1).1 :
        PathC N p q) : C(I, V)) (piece k j) O :=
      ((continuous_subtype_val.comp (continuous_subtype_val.comp ((J.toY k).continuous.comp
        continuous_fst))).tendsto x₀).eventually
        (ContinuousMap.eventually_mapsTo (isCompact_piece k j) (J.isOpen O hO) hmaps)
    have hmemO : ∀ x : ↥(J.XSet k (p := p) (q := q)) × I,
        MapsTo (((J.toY k x.1).1 : PathC N p q) : C(I, V)) (piece k j) O →
          ∀ s ∈ Icc (dy k j) (dy k (j + 1)), ((x.1 : PathSp N p q) : ℝ → V) s ∈ N ∩ O := by
      intro x hx s hs
      have hs01 : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(dy_nonneg k j).trans hs.1, hs.2.trans (dy_le_one (by omega))⟩
      refine ⟨(x.1 : PathSp N p q).mem.2.1 s hs01, ?_⟩
      have := hx (show (⟨s, hs01⟩ : I) ∈ piece k j from hs)
      have h2 : ext ((J.toY k x.1).1) s = ((x.1 : PathSp N p q) : ℝ → V) s :=
        ext_toPathC_eqOn x.1.1 hs01
      rw [← ext_of_mem _ hs01, h2] at this
      exact this
    -- the formula `H = Φ ∘ F`
    set F : ↥(J.XSet k (p := p) (q := q)) × I → ℝ → (V × V) × ℝ := fun x s =>
      ((((x.1 : PathSp N p q) : ℝ → V) s, ((bb x : PathSp N p q) : ℝ → V) s), (x.2 : ℝ)) with hF
    have hformula : ∀ x : ↥(J.XSet k (p := p) (q := q)) × I,
        MapsTo (((J.toY k x.1).1 : PathC N p q) : C(I, V)) (piece k j) O → ∀ s ∈ Icc a b,
          ((J.interpΩ k x : PathSp N p q) : ℝ → V) s = (Φ ∘ F x) s := by
      intro x hx s hs
      have hs' := hsub hs
      have hs01 : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(dy_nonneg k j).trans hs'.1, hs'.2.trans (dy_le_one (by omega))⟩
      have hgx : J.IsGood k ((x.1 : PathSp N p q) : ℝ → V) := x.1.2
      rw [interpΩ_eqOn k x hs01, JoinSystem.interp, Function.comp_apply, hF]
      simp only
      rw [brokenΩ_toY_eqOn k x.1 hs01]
      exact (hΦeq _ (hmemO x hx s hs') _ (broken_mem_of hgx hj hO (hmemO x hx) hs') _
        (hIoo _ x.2.2)).symm
    have hderiv : ∀ x : ↥(J.XSet k (p := p) (q := q)) × I,
        MapsTo (((J.toY k x.1).1 : PathC N p q) : C(I, V)) (piece k j) O → ∀ s ∈ Ioo a b,
          deriv ((J.interpΩ k x : PathSp N p q) : ℝ → V) s = deriv (Φ ∘ F x) s := by
      intro x hx s hs
      exact Filter.EventuallyEq.deriv_eq (eventually_of_mem (Icc_mem_nhds hs.1 hs.2)
        (hformula x hx))
    -- the derivatives of `F`
    have hdF : ∀ x : ↥(J.XSet k (p := p) (q := q)) × I, ∃ B : Finset ℝ, ∀ s ∈ Ioo a b, s ∉ B →
        HasDerivAt (F x) ((deriv ((x.1 : PathSp N p q) : ℝ → V) s,
          deriv ((bb x : PathSp N p q) : ℝ → V) s), (0 : ℝ)) s := by
      intro x
      classical
      obtain ⟨-, -, B₁, hB₁⟩ := (x.1 : PathSp N p q).mem.1
      obtain ⟨-, -, B₂, hB₂⟩ := (bb x).mem.1
      refine ⟨B₁ ∪ B₂, fun s hs hsB => ?_⟩
      have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_lt hs.1, hs.2.trans_le hb⟩
      exact ((PathSp.hasDerivAt_of_notMem hB₁ hs01 fun h => hsB (Finset.mem_union_left _ h)).prodMk
        (PathSp.hasDerivAt_of_notMem hB₂ hs01 fun h => hsB (Finset.mem_union_right _ h))).prodMk
        (hasDerivAt_const s _)
    -- the bound on the energies
    set C : ℝ := energy ((x₀.1 : PathSp N p q) : ℝ → V) 0 1 + energy ((bb x₀ : PathSp N p q) :
      ℝ → V) 0 1 + 2 with hC
    have hEγ' := hEγ.eventually (gt_mem_nhds (lt_add_one
      (energy ((x₀.1 : PathSp N p q) : ℝ → V) 0 1)))
    have hEb' := hEb.eventually (gt_mem_nhds (lt_add_one
      (energy ((bb x₀ : PathSp N p q) : ℝ → V) 0 1)))
    have hsq_int : ∀ β : PathSp N p q, IntervalIntegrable (fun t => ‖deriv (β : ℝ → V) t‖ ^ 2)
        volume a b := fun β => (β.mem.1.mono ha hab.le hb).intervalIntegrable_norm_deriv_sq
    have hsub_E : ∀ β : PathSp N p q, ∫ t in a..b, ‖deriv (β : ℝ → V) t‖ ^ 2 ≤
        energy (β : ℝ → V) 0 1 := fun β =>
      intervalIntegral.integral_mono_interval ha hab.le hb
        (Eventually.of_forall fun _ => sq_nonneg _) β.mem.1.intervalIntegrable_norm_deriv_sq
    have hsub_d : ∀ β β' : PathSp N p q, ∫ t in a..b, ‖deriv (β : ℝ → V) t - deriv β' t‖ ^ 2 ≤
        ∫ t in (0 : ℝ)..1, ‖deriv (β : ℝ → V) t - deriv β' t‖ ^ 2 := fun β β' =>
      intervalIntegral.integral_mono_interval ha hab.le hb
        (Eventually.of_forall fun _ => sq_nonneg _)
        (intervalIntegrable_comp_deriv β.mem.1 β'.mem.1 (Φ := fun z : V × V => ‖z.1 - z.2‖ ^ 2)
          (by fun_prop) le_rfl zero_le_one le_rfl)
    have hmain := tendsto_integral_deriv_comp_sub_sq (Φ := Φ) (hU.prod isOpen_Ioo)
      (hΦ.of_le (by norm_cast)) hab.le (l := 𝓝 x₀) (Fs := F) (F₀ := F x₀)
      (Fs' := fun x s => ((deriv ((x.1 : PathSp N p q) : ℝ → V) s,
        deriv ((bb x : PathSp N p q) : ℝ → V) s), (0 : ℝ)))
      (F₀' := fun s => ((deriv ((x₀.1 : PathSp N p q) : ℝ → V) s,
        deriv ((bb x₀ : PathSp N p q) : ℝ → V) s), (0 : ℝ)))
      ?_ ?_ ?_ hdF (hdF x₀) ?_ ?_ (C := C) ?_ ?_
    · refine hmain.congr' ?_
      filter_upwards [hev] with x hx
      refine intervalIntegral.integral_congr_Ioo_of_le hab.le fun s hs => ?_
      rw [hderiv x hx s hs, hderiv x₀ hmaps s hs]
    · -- continuity of `F x₀`
      have h1 : ContinuousOn ((x₀.1 : PathSp N p q) : ℝ → V) (Icc a b) :=
        (x₀.1 : PathSp N p q).mem.1.2.1.mono (Icc_subset_Icc ha hb)
      have h2 : ContinuousOn ((bb x₀ : PathSp N p q) : ℝ → V) (Icc a b) :=
        (bb x₀).mem.1.2.1.mono (Icc_subset_Icc ha hb)
      exact (h1.prodMk h2).prodMk continuousOn_const
    · -- `F x₀` maps into `U × (−ε, 1 + ε)`
      intro s hs
      have hs' := hsub hs
      have hs01 : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(dy_nonneg k j).trans hs'.1, hs'.2.trans (dy_le_one (by omega))⟩
      refine ⟨hNU ⟨hmemO x₀ hmaps s hs', ?_⟩, hIoo _ x₀.2.2⟩
      change ((bb x₀ : PathSp N p q) : ℝ → V) s ∈ N ∩ O
      rw [hbb]
      simp only
      rw [brokenΩ_toY_eqOn k x₀.1 hs01]
      exact broken_mem_of hg₀ hj hO (hmemO x₀ hmaps) hs'
    · -- uniform convergence of `F`
      rw [Metric.tendstoUniformlyOn_iff]
      intro δ hδ
      filter_upwards [PathSp.eventually_norm_sub_le_of_tendsto hγ (half_pos hδ),
        PathSp.eventually_norm_sub_le_of_tendsto hbt (half_pos hδ),
        Metric.tendsto_nhds.1 hu _ (half_pos hδ)] with x hx1 hx2 hx3 s hs
      have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hs.1, hs.2.trans hb⟩
      rw [Prod.dist_eq, Prod.dist_eq]
      refine max_lt (max_lt ?_ ?_) ?_
      · rw [dist_eq_norm, norm_sub_rev]
        exact (hx1 s hs01).trans_lt (half_lt_self hδ)
      · rw [dist_eq_norm, norm_sub_rev]
        exact (hx2 s hs01).trans_lt (half_lt_self hδ)
      · rw [dist_comm]
        exact hx3.trans (half_lt_self hδ)
    · -- integrability of `‖F'‖²`
      intro x
      exact intervalIntegrable_comp_deriv (x.1 : PathSp N p q).mem.1 (bb x).mem.1
        (Φ := fun z : V × V => ‖((z.1, z.2), (0 : ℝ))‖ ^ 2) (by fun_prop) ha hab.le hb
    · -- integrability of `‖F' − F₀'‖²`
      intro x
      have := intervalIntegrable_comp_deriv₄ (x.1 : PathSp N p q).mem.1 (bb x).mem.1
        (x₀.1 : PathSp N p q).mem.1 (bb x₀).mem.1
        (Φ := fun z => ‖((z.1.1 - z.2.1, z.1.2 - z.2.2), (0 : ℝ))‖ ^ 2) (by fun_prop) ha hab.le hb
      refine this.congr fun t _ => ?_
      simp only [Prod.mk_sub_mk, sub_zero]
    · -- the energy bound
      filter_upwards [hEγ', hEb'] with x hx1 hx2
      calc ∫ s in a..b, ‖((deriv ((x.1 : PathSp N p q) : ℝ → V) s,
            deriv ((bb x : PathSp N p q) : ℝ → V) s), (0 : ℝ))‖ ^ 2
          ≤ ∫ s in a..b, (‖deriv ((x.1 : PathSp N p q) : ℝ → V) s‖ ^ 2 +
              ‖deriv ((bb x : PathSp N p q) : ℝ → V) s‖ ^ 2) :=
            intervalIntegral.integral_mono_on hab.le
              (intervalIntegrable_comp_deriv (x.1 : PathSp N p q).mem.1 (bb x).mem.1
                (Φ := fun z : V × V => ‖((z.1, z.2), (0 : ℝ))‖ ^ 2) (by fun_prop) ha hab.le hb)
              ((hsq_int _).add (hsq_int _)) fun s _ => norm_pair_zero_sq_le _ _
        _ = (∫ s in a..b, ‖deriv ((x.1 : PathSp N p q) : ℝ → V) s‖ ^ 2) +
              ∫ s in a..b, ‖deriv ((bb x : PathSp N p q) : ℝ → V) s‖ ^ 2 :=
            intervalIntegral.integral_add (hsq_int _) (hsq_int _)
        _ ≤ C := by
            have := hsub_E x.1
            have := hsub_E (bb x)
            rw [hC]
            linarith
    · -- `L²` convergence of `F'`
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using hL2γ.add hL2b) (fun x => intervalIntegral.integral_nonneg hab.le
          fun _ _ => sq_nonneg _) fun x => ?_
      calc ∫ s in a..b, ‖((deriv ((x.1 : PathSp N p q) : ℝ → V) s,
            deriv ((bb x : PathSp N p q) : ℝ → V) s), (0 : ℝ)) -
            ((deriv ((x₀.1 : PathSp N p q) : ℝ → V) s,
            deriv ((bb x₀ : PathSp N p q) : ℝ → V) s), (0 : ℝ))‖ ^ 2
          ≤ ∫ s in a..b, (‖deriv ((x.1 : PathSp N p q) : ℝ → V) s -
              deriv ((x₀.1 : PathSp N p q) : ℝ → V) s‖ ^ 2 +
              ‖deriv ((bb x : PathSp N p q) : ℝ → V) s -
                deriv ((bb x₀ : PathSp N p q) : ℝ → V) s‖ ^ 2) := by
            refine intervalIntegral.integral_mono_on hab.le ?_ ?_ fun s _ => ?_
            · have := intervalIntegrable_comp_deriv₄ (x.1 : PathSp N p q).mem.1 (bb x).mem.1
                (x₀.1 : PathSp N p q).mem.1 (bb x₀).mem.1
                (Φ := fun z => ‖((z.1.1 - z.2.1, z.1.2 - z.2.2), (0 : ℝ))‖ ^ 2) (by fun_prop) ha
                hab.le hb
              refine this.congr fun t _ => ?_
              simp only [Prod.mk_sub_mk, sub_zero]
            · exact (intervalIntegrable_comp_deriv (x.1 : PathSp N p q).mem.1
                (x₀.1 : PathSp N p q).mem.1 (Φ := fun z : V × V => ‖z.1 - z.2‖ ^ 2) (by fun_prop)
                ha hab.le hb).add (intervalIntegrable_comp_deriv (bb x).mem.1 (bb x₀).mem.1
                (Φ := fun z : V × V => ‖z.1 - z.2‖ ^ 2) (by fun_prop) ha hab.le hb)
            · simp only [Prod.mk_sub_mk, sub_zero]
              exact norm_pair_zero_sq_le _ _
        _ = (∫ s in a..b, ‖deriv ((x.1 : PathSp N p q) : ℝ → V) s -
              deriv ((x₀.1 : PathSp N p q) : ℝ → V) s‖ ^ 2) +
            ∫ s in a..b, ‖deriv ((bb x : PathSp N p q) : ℝ → V) s -
              deriv ((bb x₀ : PathSp N p q) : ℝ → V) s‖ ^ 2 :=
            intervalIntegral.integral_add (intervalIntegrable_comp_deriv
              (x.1 : PathSp N p q).mem.1 (x₀.1 : PathSp N p q).mem.1
              (Φ := fun z : V × V => ‖z.1 - z.2‖ ^ 2) (by fun_prop) ha hab.le hb)
              (intervalIntegrable_comp_deriv (bb x).mem.1 (bb x₀).mem.1
                (Φ := fun z : V × V => ‖z.1 - z.2‖ ^ 2) (by fun_prop) ha hab.le hb)
        _ ≤ _ := add_le_add (hsub_d _ _) (hsub_d _ _)
  · rw [show (0 : ℝ) = 0 + 0 by ring]
    refine (h₁.add h₂).congr fun x => ?_
    exact (integral_deriv_sub_sq_add ha hax.le hxb.le hb).symm

/-! ### `i : X_k → Y_k` is a homotopy equivalence -/

theorem interpΩ_one (k : ℕ) (γ : ↥(J.XSet k (p := p) (q := q))) :
    J.interpΩ k (γ, 1) = J.brokenΩ k (J.toY k γ) := by
  refine Subtype.ext (Subtype.ext (funext fun s => ?_))
  have hs := (projIcc (0 : ℝ) 1 zero_le_one s).2
  change J.interp k γ.1 ((1 : I) : ℝ) _ = J.broken k (ext (J.toY k γ).1) _
  rw [show ((1 : I) : ℝ) = 1 from rfl, interp_one γ.2 hs]
  exact (broken_congr (ext_toPathC_eqOn γ.1)).symm

omit [FiniteDimensional ℝ V] in
theorem edist_interpΩ_zero (k : ℕ) (γ : ↥(J.XSet k (p := p) (q := q))) :
    edist (J.interpΩ k (γ, 0)) γ = 0 := by
  change edist (J.interpΩ k (γ, 0) : PathSp N p q) (γ : PathSp N p q) = 0
  refine PathSp.edist_eq_zero_of_eqOn fun s hs => ?_
  rw [interpΩ_eqOn k _ hs]
  exact interp_zero γ.2 hs

theorem toY_brokenΩ (k : ℕ) (γ : ↥(J.YSet k (p := p) (q := q))) :
    J.toY k (J.brokenΩ k γ) = J.interpStar k (γ, 1) := by
  refine Subtype.ext (Subtype.ext (ContinuousMap.ext fun t => ?_))
  change ((J.brokenΩ k γ : PathSp N p q) : ℝ → V) t = J.interp k (ext γ.1) ((1 : I) : ℝ) t
  rw [brokenΩ_eqOn k γ t.2, show ((1 : I) : ℝ) = 1 from rfl, interp_one γ.2 t.2]

include hN in
/-- **Lemma 17.C (ii) of the exposition**: the inclusion `i : X_k → Y_k` is a homotopy
equivalence, with homotopy inverse the broken geodesic `b`; both homotopies are the deformation
along minimal geodesics. -/
theorem isHomotopyEquiv_toY (k : ℕ) : IsHomotopyEquiv (J.toY k (p := p) (q := q)) := by
  set g : C(↥(J.YSet k (p := p) (q := q)), ↥(J.XSet k (p := p) (q := q))) :=
    ⟨J.brokenΩ k, J.continuous_brokenΩ hN k⟩ with hg
  refine ⟨g, ?_, ?_⟩
  · -- `b ∘ i ≃ id`, through `H(γ, 1 − t)` (adjusted at `t = 1` by a path at distance `0`)
    classical
    have hc : Continuous fun x : I × ↥(J.XSet k (p := p) (q := q)) =>
        J.interpΩ k (x.2, unitInterval.symm x.1) :=
      (J.continuous_interpΩ hN k).comp (continuous_snd.prodMk (unitInterval.continuous_symm.comp
        continuous_fst))
    refine ⟨{
      toFun := fun x => if x.1 = 1 then x.2 else J.interpΩ k (x.2, unitInterval.symm x.1)
      continuous_toFun := PathSp.continuous_of_edist_eq_zero hc fun x => ?_
      map_zero_left := fun γ => ?_
      map_one_left := fun γ => by simp }⟩
    · split_ifs with h
      · rw [h, unitInterval.symm_one, edist_comm]
        exact J.edist_interpΩ_zero k x.2
      · exact edist_self _
    · simp only [zero_ne_one, if_false, unitInterval.symm_zero]
      rw [interpΩ_one]
      rfl
  · -- `i ∘ b ≃ id`, through `H*(γ, 1 − t)`
    refine ⟨{
      toFun := fun x => J.interpStar k (x.2, unitInterval.symm x.1)
      continuous_toFun := (J.interpStar k).continuous.comp (continuous_snd.prodMk
        (unitInterval.continuous_symm.comp continuous_fst))
      map_zero_left := fun γ => ?_
      map_one_left := fun γ => ?_ }⟩
    · simp only [unitInterval.symm_zero]
      rw [← toY_brokenΩ]
      rfl
    · simp only [unitInterval.symm_one]
      exact interpStar_zero γ

end Omega

end JoinSystem

end Morse
