import Mathlib

/-!
Milnor, *Morse Theory*, §10, pp. 59–62 (and the definition on p. 67): piecewise smooth paths and
their lengths.

# Paths and their lengths

## Milnor's text, paraphrased

A *piecewise smooth path* `ω : [a, b] → M` is a continuous map for which there is a subdivision
`a = t₀ < t₁ < ⋯ < t_k = b` such that each `ω|[t_{i-1}, t_i]` is smooth (p. 67, used from Theorem
10.4 on, p. 59).  Its length is `∫ₐᵇ ‖dω/dt‖ dt`.

## Definitions and results

For curves `c : ℝ → V` in a finite-dimensional real normed space (the ambient space of `N`):

* `Morse.pathLength c a b = ∫ₐᵇ ‖c'(t)‖ dt`.
* `Morse.IsPiecewiseSmooth c a b`: Milnor's piecewise smooth paths, with the subdivision given as
  a finite set `B` of break points: `c` is continuous on `[a, b]` and smooth on every closed
  subinterval containing no point of `B` in its interior.
* `Morse.IsAdmissible c a b`: `c` is continuous on `[a, b]`, differentiable off a countable set,
  and `‖c'‖` is integrable.  Every piecewise smooth path is admissible
  (`Morse.IsPiecewiseSmooth.isAdmissible`).  The lower bounds for lengths (Theorem 10.4 and the
  lemmas before it, `Morse/Chapter7/Shortest.lean`) are proved for admissible paths: this class is
  stable under restriction, and the fundamental theorem of calculus holds in it
  (`Morse.IsAdmissible.integral_deriv`, from Mathlib's version with countably many exceptional
  points).
* Lengths are additive (`Morse.IsAdmissible.pathLength_add`), nonnegative, and bound the distance
  in `V` between the endpoints (`Morse.IsAdmissible.norm_sub_le_pathLength`); a path of length `0`
  is constant (`Morse.IsAdmissible.eq_of_pathLength_eq_zero`); a path of constant speed `k` has
  length `k (b − a)` (`Morse.pathLength_eq_of_norm_deriv`).
* Concatenation (`Morse.IsPiecewiseSmooth.concat`, `Morse.pathLength_concat`), reversal and
  translation of parameters (`Morse.IsPiecewiseSmooth.reverse`, `Morse.pathLength_reverse`,
  `Morse.IsPiecewiseSmooth.translate`, `Morse.pathLength_translate`).

## What Milnor leaves implicit

* That the length is additive under subdivision and concatenation, unchanged under reversal and
  translation, and that the restriction of a piecewise smooth path to a subinterval (with endpoints
  not among the break points) is piecewise smooth: all used in §10 without comment.
* That `‖ω'‖` is integrable: on each piece the one-sided derivatives at the break points make
  `‖ω'‖` continuous on the closed piece (`Morse.IsPiecewiseSmooth.isAdmissible`).
-/

open Set Filter Topology Function MeasureTheory Metric
open scoped ContDiff Interval

noncomputable section

namespace Morse

/-! ### Countable exceptional sets -/

/-- A property holding on `(a, b)` off a countable set holds almost everywhere on `Ι a b`. -/
theorem ae_uIoc_of_forall_Ioo_diff {p : ℝ → Prop} {a b : ℝ} (hab : a ≤ b) {C : Set ℝ}
    (hC : C.Countable) (h : ∀ t ∈ Ioo a b \ C, p t) : ∀ᵐ t ∂(volume.restrict (Ι a b)), p t := by
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ C ∪ {b} :=
    (hC.union (countable_singleton b)).ae_notMem volume
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [h1] with t ht htI
  rw [uIoc_of_le hab] at htI
  simp only [mem_union, mem_singleton_iff, not_or] at ht
  exact h t ⟨⟨htI.1, lt_of_le_of_ne htI.2 ht.2⟩, ht.1⟩

/-- A property holding on `(a, b)` off a countable set holds almost everywhere on `[a, b]`. -/
theorem ae_Icc_of_forall_Ioo_diff {p : ℝ → Prop} {a b : ℝ} {C : Set ℝ}
    (hC : C.Countable) (h : ∀ t ∈ Ioo a b \ C, p t) : ∀ᵐ t ∂(volume.restrict (Icc a b)), p t := by
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ C ∪ {a, b} :=
    (hC.union ((countable_singleton a).insert b |>.mono (by
      intro x hx; simp only [mem_insert_iff, mem_singleton_iff] at hx ⊢; tauto))).ae_notMem volume
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h1] with t ht htI
  simp only [mem_union, mem_insert_iff, mem_singleton_iff, not_or] at ht
  exact h t ⟨⟨lt_of_le_of_ne htI.1 (Ne.symm ht.2.1), lt_of_le_of_ne htI.2 ht.2.2⟩, ht.1⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Length -/

/-- **The length** `∫ₐᵇ ‖c'(t)‖ dt` of a path `c` on `[a, b]`. -/
def pathLength (c : ℝ → V) (a b : ℝ) : ℝ := ∫ t in a..b, ‖deriv c t‖

/-- **Admissible paths** on `[a, b]`: continuous on `[a, b]`, differentiable at all but countably
many points of `(a, b)`, with integrable speed.  Piecewise smooth paths are admissible. -/
structure IsAdmissible (c : ℝ → V) (a b : ℝ) : Prop where
  le : a ≤ b
  continuousOn : ContinuousOn c (Icc a b)
  countable : ∃ C : Set ℝ, C.Countable ∧ ∀ t ∈ Ioo a b \ C, DifferentiableAt ℝ c t
  integrable : IntervalIntegrable (fun t => ‖deriv c t‖) volume a b

variable [CompleteSpace V] in
theorem aestronglyMeasurable_deriv' (c : ℝ → V) (μ : Measure ℝ) :
    AEStronglyMeasurable (deriv c) μ :=
  aestronglyMeasurable_deriv c μ

namespace IsAdmissible

variable {c : ℝ → V} {a b : ℝ}

theorem mono (h : IsAdmissible c a b) {a' b' : ℝ} (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) :
    IsAdmissible c a' b' := by
  obtain ⟨C, hC, hd⟩ := h.countable
  refine ⟨hab, h.continuousOn.mono (Icc_subset_Icc ha hb), ⟨C, hC, fun t ht => hd t
    ⟨⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩, ht.2⟩⟩, h.integrable.mono_set ?_⟩
  rw [uIcc_of_le hab, uIcc_of_le h.le]
  exact Icc_subset_Icc ha hb

variable [CompleteSpace V] in
theorem intervalIntegrable_deriv (h : IsAdmissible c a b) :
    IntervalIntegrable (deriv c) volume a b :=
  (IntervalIntegrable.intervalIntegrable_norm_iff (aestronglyMeasurable_deriv c _)).1 h.integrable

variable [CompleteSpace V] in
/-- **The fundamental theorem of calculus** for admissible paths. -/
theorem integral_deriv (h : IsAdmissible c a b) : ∫ t in a..b, deriv c t = c b - c a := by
  obtain ⟨C, hC, hd⟩ := h.countable
  exact integral_eq_of_hasDerivAt_off_countable_of_le c (deriv c) h.le hC h.continuousOn
    (fun t ht => (hd t ht).hasDerivAt) h.intervalIntegrable_deriv

theorem pathLength_nonneg (h : IsAdmissible c a b) : 0 ≤ pathLength c a b :=
  intervalIntegral.integral_nonneg h.le fun _ _ => norm_nonneg _

variable [CompleteSpace V] in
/-- The length bounds the distance in `V` between the endpoints. -/
theorem norm_sub_le_pathLength (h : IsAdmissible c a b) : ‖c b - c a‖ ≤ pathLength c a b := by
  rw [← h.integral_deriv]
  exact intervalIntegral.norm_integral_le_integral_norm h.le

/-- **Additivity of length.** -/
theorem pathLength_add (h : IsAdmissible c a b) {m : ℝ} (hm : m ∈ Icc a b) :
    pathLength c a m + pathLength c m b = pathLength c a b :=
  intervalIntegral.integral_add_adjacent_intervals (h.mono le_rfl hm.1 hm.2).integrable
    (h.mono hm.1 hm.2 le_rfl).integrable

theorem pathLength_le (h : IsAdmissible c a b) {a' b' : ℝ} (ha : a ≤ a') (hab : a' ≤ b')
    (hb : b' ≤ b) : pathLength c a' b' ≤ pathLength c a b := by
  have h1 := h.pathLength_add (m := a') ⟨ha, hab.trans hb⟩
  have h2 := (h.mono ha (hab.trans hb) le_rfl).pathLength_add (m := b') ⟨hab, hb⟩
  have h3 := (h.mono le_rfl ha (hab.trans hb)).pathLength_nonneg
  have h5 := (h.mono (ha.trans hab) hb le_rfl).pathLength_nonneg
  linarith

variable [CompleteSpace V] in
/-- A path of length `0` is constant. -/
theorem eq_of_pathLength_eq_zero (h : IsAdmissible c a b) (h0 : pathLength c a b = 0) :
    ∀ t ∈ Icc a b, c t = c a := by
  intro t ht
  have h1 := (h.mono le_rfl ht.1 ht.2).norm_sub_le_pathLength
  have h2 := h.pathLength_le le_rfl ht.1 ht.2
  rw [h0] at h2
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (h1.trans h2))

/-- The length of the initial segment `[a, t]` is continuous in `t`. -/
theorem continuousOn_pathLength (h : IsAdmissible c a b) :
    ContinuousOn (fun t => pathLength c a t) (Icc a b) := by
  have := intervalIntegral.continuousOn_primitive_interval' h.integrable
    (left_mem_uIcc (a := a) (b := b))
  rwa [uIcc_of_le h.le] at this

/-- The length of the initial segment `[a, t]` is nondecreasing in `t`. -/
theorem monotoneOn_pathLength (h : IsAdmissible c a b) :
    MonotoneOn (fun t => pathLength c a t) (Icc a b) := by
  intro s hs t ht hst
  have := (h.mono le_rfl ht.1 ht.2).pathLength_add (m := s) ⟨hs.1, hst⟩
  have h2 := (h.mono hs.1 hst ht.2).pathLength_nonneg
  simp only
  linarith

end IsAdmissible

/-- **Constant speed**: a path with `‖c'(t)‖ = k` wherever it is differentiable has length
`k (b − a)`. -/
theorem pathLength_eq_of_norm_deriv {c : ℝ → V} {a b k : ℝ} (h : IsAdmissible c a b)
    (hk : ∀ t ∈ Ioo a b, DifferentiableAt ℝ c t → ‖deriv c t‖ = k) :
    pathLength c a b = k * (b - a) := by
  obtain ⟨C, hC, hd⟩ := h.countable
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b → ‖deriv c t‖ = k := by
    have := ae_uIoc_of_forall_Ioo_diff h.le hC (fun t ht => hk t ht.1 (hd t ht))
    rwa [ae_restrict_iff' measurableSet_uIoc] at this
  rw [pathLength, intervalIntegral.integral_congr_ae hae]
  simp [mul_comm]

/-! ### Piecewise smooth paths -/

/-- **A piecewise smooth path** on `[a, b]` (Milnor, pp. 59, 67): `c` is continuous on `[a, b]`,
and there is a finite set `B` of break points such that `c` is smooth (`C^∞`, with one-sided
derivatives at the ends) on every closed subinterval `[s, t] ⊆ [a, b]` with no point of `B` in
`(s, t)`.  (For Milnor's subdivision `a = t₀ < ⋯ < t_k = b`, take `B = {t_i}`.) -/
def IsPiecewiseSmooth (c : ℝ → V) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn c (Icc a b) ∧ ∃ B : Finset ℝ, ∀ s t, a ≤ s → s < t → t ≤ b →
    (∀ x ∈ B, x ∉ Ioo s t) → ContDiffOn ℝ ∞ c (Icc s t)

namespace IsPiecewiseSmooth

variable {c : ℝ → V} {a b : ℝ}

/-- A smooth piece has integrable speed. -/
theorem intervalIntegrable_of_contDiffOn {s t : ℝ} (hst : s < t)
    (hc : ContDiffOn ℝ ∞ c (Icc s t)) :
    IntervalIntegrable (fun x => ‖deriv c x‖) volume s t := by
  have hcont : ContinuousOn (derivWithin c (Icc s t)) (Icc s t) :=
    hc.continuousOn_derivWithin (uniqueDiffOn_Icc hst) (by simp)
  have hint : IntervalIntegrable (fun x => ‖derivWithin c (Icc s t) x‖) volume s t :=
    hcont.norm.intervalIntegrable_of_Icc hst.le
  refine hint.congr_uIoo fun x hx => ?_
  rw [uIoo_of_le hst.le] at hx
  have hx' : Icc s t ∈ 𝓝 x := Icc_mem_nhds hx.1 hx.2
  simp only
  rw [derivWithin_of_mem_nhds hx']

/-- **Piecewise smooth paths are admissible.** -/
theorem isAdmissible (h : IsPiecewiseSmooth c a b) : IsAdmissible c a b := by
  obtain ⟨hab, hcont, B, hB⟩ := h
  refine ⟨hab, hcont, ⟨B, B.countable_toSet, fun t ht => ?_⟩, ?_⟩
  · have hopen : IsOpen (Ioo a b \ (B : Set ℝ)) := isOpen_Ioo.sdiff B.finite_toSet.isClosed
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen t ht
    have hsub : Icc (t - δ / 2) (t + δ / 2) ⊆ Ioo a b \ (B : Set ℝ) := fun x hx =>
      hball (by rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])
    have h1 := hsub ⟨le_rfl, by linarith⟩
    have h2 := hsub ⟨by linarith, le_rfl⟩
    have hcd := hB (t - δ / 2) (t + δ / 2) h1.1.1.le (by linarith) h2.1.2.le
      fun x hx hx' => (hsub (Ioo_subset_Icc_self hx')).2 hx
    exact (hcd.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))).differentiableAt (by simp)
  · -- induction on the number of break points in the open interval
    suffices key : ∀ n : ℕ, ∀ a' b', a ≤ a' → a' ≤ b' → b' ≤ b →
        (B.filter (· ∈ Ioo a' b')).card ≤ n →
        IntervalIntegrable (fun t => ‖deriv c t‖) volume a' b' from
      key _ a b le_rfl hab le_rfl le_rfl
    intro n
    induction n with
    | zero =>
      intro a' b' ha' hab' hb' hcard
      rcases eq_or_lt_of_le hab' with heq | hlt
      · rw [heq]
      have hnone : ∀ x ∈ B, x ∉ Ioo a' b' := by
        intro x hx hx'
        have hmem : x ∈ B.filter (· ∈ Ioo a' b') := Finset.mem_filter.2 ⟨hx, hx'⟩
        rw [Nat.le_zero, Finset.card_eq_zero] at hcard
        rw [hcard] at hmem
        exact Finset.notMem_empty x hmem
      exact intervalIntegrable_of_contDiffOn hlt (hB a' b' ha' hlt hb' hnone)
    | succ n ih =>
      intro a' b' ha' hab' hb' hcard
      by_cases hex : ∃ x ∈ B, x ∈ Ioo a' b'
      · obtain ⟨x, hxB, hx⟩ := hex
        have hlt₁ : (B.filter (· ∈ Ioo a' x)).card < (B.filter (· ∈ Ioo a' b')).card := by
          refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
          · rw [Finset.mem_filter] at hy ⊢
            exact ⟨hy.1, hy.2.1, hy.2.2.trans hx.2⟩
          · have := hsub (Finset.mem_filter.2 ⟨hxB, hx⟩)
            rw [Finset.mem_filter] at this
            exact lt_irrefl x this.2.2
        have hlt₂ : (B.filter (· ∈ Ioo x b')).card < (B.filter (· ∈ Ioo a' b')).card := by
          refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
          · rw [Finset.mem_filter] at hy ⊢
            exact ⟨hy.1, hx.1.trans hy.2.1, hy.2.2⟩
          · have := hsub (Finset.mem_filter.2 ⟨hxB, hx⟩)
            rw [Finset.mem_filter] at this
            exact lt_irrefl x this.2.1
        exact (ih a' x ha' hx.1.le (hx.2.le.trans hb') (by omega)).trans
          (ih x b' (ha'.trans hx.1.le) hx.2.le hb' (by omega))
      · push Not at hex
        rcases eq_or_lt_of_le hab' with heq | hlt
        · rw [heq]
        exact intervalIntegrable_of_contDiffOn hlt (hB a' b' ha' hlt hb' fun x hx => hex x hx)

/-- A path smooth on an open set containing `[a, b]` is piecewise smooth (with no break). -/
theorem of_contDiffOn {s : Set ℝ} (hc : ContDiffOn ℝ ∞ c s) (hab : a ≤ b)
    (hsub : Icc a b ⊆ s) : IsPiecewiseSmooth c a b :=
  ⟨hab, hc.continuousOn.mono hsub, ∅, fun _ _ ha _ hb _ =>
    hc.mono ((Icc_subset_Icc ha hb).trans hsub)⟩

/-- Restriction to a subinterval. -/
theorem mono (h : IsPiecewiseSmooth c a b) {a' b' : ℝ} (ha : a ≤ a') (hab : a' ≤ b')
    (hb : b' ≤ b) : IsPiecewiseSmooth c a' b' := by
  obtain ⟨-, hcont, B, hB⟩ := h
  exact ⟨hab, hcont.mono (Icc_subset_Icc ha hb), B, fun s t hs hst ht hB' =>
    hB s t (ha.trans hs) hst (ht.trans hb) hB'⟩

/-- **Concatenation** of piecewise smooth paths. -/
theorem concat {c₁ c₂ : ℝ → V} {a m b : ℝ} (h₁ : IsPiecewiseSmooth c₁ a m)
    (h₂ : IsPiecewiseSmooth c₂ m b) (hm : c₁ m = c₂ m) :
    IsPiecewiseSmooth (fun t => if t ≤ m then c₁ t else c₂ t) a b := by
  obtain ⟨ham, hc₁, B₁, hB₁⟩ := h₁
  obtain ⟨hmb, hc₂, B₂, hB₂⟩ := h₂
  have heq₁ : EqOn (fun t => if t ≤ m then c₁ t else c₂ t) c₁ (Icc a m) := fun t ht => by
    simp only [if_pos ht.2]
  have heq₂ : EqOn (fun t => if t ≤ m then c₁ t else c₂ t) c₂ (Icc m b) := fun t ht => by
    rcases eq_or_lt_of_le ht.1 with h | h
    · simp only [← h, le_refl, if_pos, hm]
    · simp only [if_neg (not_le.2 h)]
  refine ⟨ham.trans hmb, ?_, B₁ ∪ B₂ ∪ {m}, fun s t hs hst ht hB => ?_⟩
  · rw [← Icc_union_Icc_eq_Icc ham hmb]
    exact ContinuousOn.union_of_isClosed (hc₁.congr heq₁) (hc₂.congr heq₂) isClosed_Icc
      isClosed_Icc
  · have hmB : m ∉ Ioo s t := hB m (by simp)
    rcases le_or_gt t m with htm | htm
    · exact (hB₁ s t hs hst htm fun x hx => hB x (by simp [hx])).congr
        fun y hy => heq₁ ⟨hs.trans hy.1, hy.2.trans htm⟩
    · have hms : m ≤ s := by
        by_contra hlt
        exact hmB ⟨lt_of_not_ge hlt, htm⟩
      exact (hB₂ s t hms hst ht fun x hx => hB x (by simp [hx])).congr
        fun y hy => heq₂ ⟨hms.trans hy.1, hy.2.trans ht⟩

/-- **Reversal** of a piecewise smooth path. -/
theorem reverse (h : IsPiecewiseSmooth c a b) :
    IsPiecewiseSmooth (fun t => c (a + b - t)) a b := by
  obtain ⟨hab, hcont, B, hB⟩ := h
  have hmaps : ∀ s t, MapsTo (fun x : ℝ => a + b - x) (Icc s t) (Icc (a + b - t) (a + b - s)) :=
    fun s t x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩
  refine ⟨hab, hcont.comp (continuous_const.sub continuous_id).continuousOn
    (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩),
    B.image (fun x => a + b - x), fun s t hs hst ht hB' => ?_⟩
  have hc := hB (a + b - t) (a + b - s) (by linarith) (by linarith) (by linarith)
    fun x hx hx' => hB' (a + b - x) (Finset.mem_image.2 ⟨x, hx, rfl⟩)
      ⟨by linarith [hx'.2], by linarith [hx'.1]⟩
  exact hc.comp (contDiff_const.sub contDiff_id).contDiffOn (hmaps s t)

/-- **Translation** of the parameter. -/
theorem translate (h : IsPiecewiseSmooth c a b) (d : ℝ) :
    IsPiecewiseSmooth (fun t => c (t + d)) (a - d) (b - d) := by
  obtain ⟨hab, hcont, B, hB⟩ := h
  refine ⟨by linarith, hcont.comp (continuous_id.add continuous_const).continuousOn
    (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩),
    B.image (fun x => x - d), fun s t hs hst ht hB' => ?_⟩
  have hc := hB (s + d) (t + d) (by linarith) (by linarith) (by linarith)
    fun x hx hx' => hB' (x - d) (Finset.mem_image.2 ⟨x, hx, rfl⟩)
      ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  exact hc.comp (contDiff_id.add contDiff_const).contDiffOn
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

end IsPiecewiseSmooth

/-- **Length of a concatenation.** -/
theorem pathLength_concat {c₁ c₂ : ℝ → V} {a m b : ℝ} (h₁ : IsAdmissible c₁ a m)
    (h₂ : IsAdmissible c₂ m b) :
    pathLength (fun t => if t ≤ m then c₁ t else c₂ t) a b =
      pathLength c₁ a m + pathLength c₂ m b := by
  set c := fun t => if t ≤ m then c₁ t else c₂ t with hc
  have hd₁ : ∀ t < m, deriv c t = deriv c₁ t := fun t ht => by
    have hev : c =ᶠ[𝓝 t] c₁ := by
      filter_upwards [Iio_mem_nhds ht] with x hx
      simp only [hc, if_pos (le_of_lt (mem_Iio.1 hx))]
    exact hev.deriv_eq
  have hd₂ : ∀ t, m < t → deriv c t = deriv c₂ t := fun t ht => by
    have hev : c =ᶠ[𝓝 t] c₂ := by
      filter_upwards [Ioi_mem_nhds ht] with x hx
      simp only [hc, if_neg (not_le.2 (mem_Ioi.1 hx))]
    exact hev.deriv_eq
  have hm : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ m := (countable_singleton m).ae_notMem volume
  have hI₁ : pathLength c a m = pathLength c₁ a m := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hm] with t htm ht
    rw [uIoc_of_le h₁.le] at ht
    rw [hd₁ t (lt_of_le_of_ne ht.2 htm)]
  have hI₂ : pathLength c m b = pathLength c₂ m b := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with t ht
    rw [uIoc_of_le h₂.le] at ht
    rw [hd₂ t ht.1]
  have hint₁ : IntervalIntegrable (fun t => ‖deriv c t‖) volume a m :=
    h₁.integrable.congr_uIoo fun t ht => by
      rw [uIoo_of_le h₁.le] at ht
      simp only [hd₁ t ht.2]
  have hint₂ : IntervalIntegrable (fun t => ‖deriv c t‖) volume m b :=
    h₂.integrable.congr_uIoo fun t ht => by
      rw [uIoo_of_le h₂.le] at ht
      simp only [hd₂ t ht.1]
  rw [← hI₁, ← hI₂, pathLength, pathLength, pathLength,
    intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]

/-- **Length of the reversed path.** -/
theorem pathLength_reverse (c : ℝ → V) (a b : ℝ) :
    pathLength (fun t => c (a + b - t)) a b = pathLength c a b := by
  have hd : ∀ t, deriv (fun t => c (a + b - t)) t = -deriv c (a + b - t) := fun t => by
    have := deriv_comp_const_sub (f := c) (a := a + b) (x := t)
    simpa using this
  simp only [pathLength, hd, norm_neg]
  rw [intervalIntegral.integral_comp_sub_left (fun t => ‖deriv c t‖) (a + b)]
  simp only [add_sub_cancel_left, add_sub_cancel_right]

/-- **Length is invariant under translation of the parameter.** -/
theorem pathLength_translate (c : ℝ → V) (a b d : ℝ) :
    pathLength (fun t => c (t + d)) (a - d) (b - d) = pathLength c a b := by
  have hd : ∀ t, deriv (fun t => c (t + d)) t = deriv c (t + d) := fun t =>
    deriv_comp_add_const (f := c) (a := d) (x := t)
  simp only [pathLength, hd]
  rw [intervalIntegral.integral_comp_add_right (fun t => ‖deriv c t‖) d]
  simp only [sub_add_cancel]

end Morse
