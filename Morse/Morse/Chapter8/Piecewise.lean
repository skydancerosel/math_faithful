import Morse.Chapter7.Path
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
Milnor, *Morse Theory*, §§11–13 (pp. 67–76): the calculus of piecewise smooth functions on an
interval and on strips `U × [a, b]` that the variation formulas use.

# Piecewise calculus

## What Milnor uses without comment

Milnor's proofs of the first and second variation formulas (pp. 71–72 and 74–76) differentiate
under the integral sign, integrate by parts "on `[t_{i-1}, t_i]`" and add up the results over the
pieces of a subdivision.  Behind this are the following facts, proved here.

* **Smoothness on a closed strip.**  A variation is smooth on each strip `(-ε, ε) × [t_{i-1}, t_i]`
  (p. 68), closed in the `t` direction; its `t`-derivatives along the edges are one-sided.  Here
  smoothness on `U × [a, b]` is `ContDiffOn ℝ ∞ F (U ×ˢ Icc a b)`, and the partial derivatives
  `Morse.pdU`, `Morse.pdT` are computed within the strip.  They are smooth on the closed strip
  (`Morse.contDiffOn_pdU`, `Morse.contDiffOn_pdT`), are the honest partial derivatives inside, give
  the one-sided `t`-derivatives on the edges (`Morse.hasDerivWithinAt_pdT`), and commute, also on
  the edges (`Morse.pdU_pdT`: symmetry of second derivatives within a set whose interior is dense
  in it).
* **Differentiation under the integral sign** on a closed strip, with the domination bound coming
  from the compactness of `[u₀ - δ, u₀ + δ] × [a, b]` (`Morse.hasDerivAt_integral_strip`).
* **Gluing over the pieces.**  Break points are a finite set `B`, as in `Morse.IsPiecewiseSmooth`; a
  *piece* is an interval `[s, t]` with no point of `B` in `(s, t)`.  An induction over the number of
  break points (`Morse.piecewise_induction`) glues: integrability
  (`Morse.intervalIntegrable_of_piecewise`); the integration by parts, whose boundary terms
  telescope into a sum of jumps at the break points (`Morse.integral_eq_of_piecewise`); and the
  differentiation under the integral sign (`Morse.hasDerivAt_integral_of_piecewise`).
-/

open Set Filter Topology Function MeasureTheory Metric
open scoped ContDiff Interval

noncomputable section

namespace Morse

/-! ### Induction over the pieces of a subdivision -/

/-- **Induction over the pieces.**  Let `B` be a finite set of break points.  A property of
intervals `[a, b] ⊆ [lo, hi]` which holds for every interval with no break point in its interior,
and which can be glued at a break point, holds for every interval. -/
theorem piecewise_induction {B : Finset ℝ} {lo hi : ℝ} {P : ℝ → ℝ → Prop}
    (base : ∀ a b, lo ≤ a → a < b → b ≤ hi → (∀ x ∈ B, x ∉ Ioo a b) → P a b)
    (glue : ∀ a x b, lo ≤ a → a < x → x < b → b ≤ hi → x ∈ B → P a x → P x b → P a b) :
    ∀ a b, lo ≤ a → a < b → b ≤ hi → P a b := by
  suffices key : ∀ n : ℕ, ∀ a b, lo ≤ a → a < b → b ≤ hi →
      (B.filter (· ∈ Ioo a b)).card ≤ n → P a b from
    fun a b ha hab hb => key _ a b ha hab hb le_rfl
  intro n
  induction n with
  | zero =>
    intro a b ha hab hb hcard
    refine base a b ha hab hb fun x hx hx' => ?_
    have hmem : x ∈ B.filter (· ∈ Ioo a b) := Finset.mem_filter.2 ⟨hx, hx'⟩
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    rw [hcard] at hmem
    exact Finset.notMem_empty x hmem
  | succ n ih =>
    intro a b ha hab hb hcard
    by_cases hex : ∃ x ∈ B, x ∈ Ioo a b
    · obtain ⟨x, hxB, hx⟩ := hex
      have hlt₁ : (B.filter (· ∈ Ioo a x)).card < (B.filter (· ∈ Ioo a b)).card := by
        refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
        · rw [Finset.mem_filter] at hy ⊢
          exact ⟨hy.1, hy.2.1, hy.2.2.trans hx.2⟩
        · have := hsub (Finset.mem_filter.2 ⟨hxB, hx⟩)
          rw [Finset.mem_filter] at this
          exact lt_irrefl x this.2.2
      have hlt₂ : (B.filter (· ∈ Ioo x b)).card < (B.filter (· ∈ Ioo a b)).card := by
        refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
        · rw [Finset.mem_filter] at hy ⊢
          exact ⟨hy.1, hx.1.trans hy.2.1, hy.2.2⟩
        · have := hsub (Finset.mem_filter.2 ⟨hxB, hx⟩)
          rw [Finset.mem_filter] at this
          exact lt_irrefl x this.2.1
      exact glue a x b ha hx.1 hx.2 hb hxB
        (ih a x ha hx.1 (hx.2.le.trans hb) (by omega))
        (ih x b (ha.trans hx.1.le) hx.2 hb (by omega))
    · exact base a b ha hab hb fun x hx hx' => hex ⟨x, hx, hx'⟩

/-- Splitting a sum over the break points in `(a, b)` at a break point `x`. -/
theorem sum_filter_Ioo_split {E : Type*} [AddCommMonoid E] {B : Finset ℝ} (f : ℝ → E)
    {a x b : ℝ} (hax : a < x) (hxb : x < b) (hx : x ∈ B) :
    ∑ y ∈ B with y ∈ Ioo a b, f y =
      (∑ y ∈ B with y ∈ Ioo a x, f y) + f x + ∑ y ∈ B with y ∈ Ioo x b, f y := by
  classical
  simp only [Finset.sum_filter]
  have h : ∀ y ∈ B, (if y ∈ Ioo a b then f y else 0) =
      (if y ∈ Ioo a x then f y else 0) + (if x = y then f y else 0) +
        (if y ∈ Ioo x b then f y else 0) := by
    intro y _
    rcases lt_trichotomy y x with hyx | rfl | hyx
    · have h1 : ¬ x = y := hyx.ne'
      have h2 : y ∉ Ioo x b := fun h => lt_asymm hyx h.1
      by_cases hy : a < y
      · simp [hy, hyx, h1, h2, hyx.trans hxb]
      · simp [hy, h1, h2]
    · simp [hax, hxb]
    · have h1 : ¬ x = y := hyx.ne
      have h2 : y ∉ Ioo a x := fun h => lt_asymm hyx h.2
      by_cases hy : y < b
      · simp [hy, hyx, h1, h2, hax.trans hyx]
      · simp [hy, h1, h2]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos hx]

/-- For `t ∈ (a, b]`, there is a piece `[s, t] ⊆ [a, b]` to the left of `t`. -/
theorem exists_piece_left (B : Finset ℝ) {a t : ℝ} (hat : a < t) :
    ∃ s, a ≤ s ∧ s < t ∧ ∀ x ∈ B, x ∉ Ioo s t := by
  classical
  set S := insert a (B.filter (· < t))
  have hS : S.Nonempty := ⟨a, Finset.mem_insert_self _ _⟩
  refine ⟨S.max' hS, S.le_max' _ (Finset.mem_insert_self _ _), ?_, fun x hx hx' => ?_⟩
  · obtain ⟨y, hy, hy'⟩ := S.exists_max_image id hS
    have : S.max' hS = y := le_antisymm (S.max'_le _ _ fun z hz => hy' z hz) (S.le_max' _ hy)
    rw [this]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hat
    · exact (Finset.mem_filter.1 hy).2
  · have : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, hx'.2⟩)
    exact absurd (S.le_max' x this) (not_le.2 hx'.1)

/-- For `t ∈ [a, b)`, there is a piece `[t, s] ⊆ [a, b]` to the right of `t`. -/
theorem exists_piece_right (B : Finset ℝ) {t b : ℝ} (htb : t < b) :
    ∃ s, t < s ∧ s ≤ b ∧ ∀ x ∈ B, x ∉ Ioo t s := by
  classical
  set S := insert b (B.filter (t < ·))
  have hS : S.Nonempty := ⟨b, Finset.mem_insert_self _ _⟩
  refine ⟨S.min' hS, ?_, S.min'_le _ (Finset.mem_insert_self _ _), fun x hx hx' => ?_⟩
  · obtain ⟨y, hy, hy'⟩ := S.exists_min_image id hS
    have : S.min' hS = y := le_antisymm (S.min'_le _ hy) (S.le_min' _ _ fun z hz => hy' z hz)
    rw [this]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact htb
    · exact (Finset.mem_filter.1 hy).2
  · have : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, hx'.1⟩)
    exact absurd (S.min'_le x this) (not_le.2 hx'.2)

/-- A point not in `B`, inside `(a, b)`, lies inside a piece. -/
theorem exists_piece_around (B : Finset ℝ) {a b t : ℝ} (hat : a < t) (htb : t < b)
    (ht : t ∉ B) : ∃ s s', a ≤ s ∧ s < t ∧ t < s' ∧ s' ≤ b ∧ ∀ x ∈ B, x ∉ Ioo s s' := by
  obtain ⟨s, has, hst, hs⟩ := exists_piece_left B hat
  obtain ⟨s', hts', hs'b, hs'⟩ := exists_piece_right B htb
  refine ⟨s, s', has, hst, hts', hs'b, fun x hx hx' => ?_⟩
  rcases lt_trichotomy x t with h | rfl | h
  · exact hs x hx ⟨hx'.1, h⟩
  · exact ht hx
  · exact hs' x hx ⟨h, hx'.2⟩

/-- Every point of `[a, b]` (`a < b`) lies in some piece. -/
theorem exists_piece_mem (B : Finset ℝ) {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    ∃ s s', a ≤ s ∧ s < s' ∧ s' ≤ b ∧ t ∈ Icc s s' ∧ ∀ x ∈ B, x ∉ Ioo s s' := by
  rcases eq_or_lt_of_le ht.2 with rfl | htb
  · obtain ⟨s, hs, hst, hB⟩ := exists_piece_left B hab
    exact ⟨s, t, hs, hst, le_rfl, ⟨hst.le, le_rfl⟩, hB⟩
  · obtain ⟨s', hts', hs', hB⟩ := exists_piece_right B htb
    exact ⟨t, s', ht.1, hts', hs', ⟨le_rfl, hts'.le⟩, hB⟩

/-! ### Continuity, integrability and integrals of piecewise functions -/

section Integral

variable {E : Type*} [NormedAddCommGroup E]

/-- **Gluing continuity**: a function continuous on every piece of `[lo, hi]` is continuous on
`[lo, hi]`. -/
theorem continuousOn_of_piecewise {g : ℝ → E} {B : Finset ℝ} {lo hi : ℝ}
    (h : ∀ s t, lo ≤ s → s < t → t ≤ hi → (∀ x ∈ B, x ∉ Ioo s t) → ContinuousOn g (Icc s t)) :
    ContinuousOn g (Icc lo hi) := by
  rcases lt_or_ge lo hi with hlt | hle
  · refine piecewise_induction (P := fun a b => ContinuousOn g (Icc a b)) h ?_ lo hi le_rfl hlt
      le_rfl
    intro a x b _ hax hxb _ _ h₁ h₂
    rw [← Icc_union_Icc_eq_Icc hax.le hxb.le]
    exact h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc
  · intro x hx
    have : x = lo := le_antisymm (hx.2.trans hle) hx.1
    subst this
    exact (continuousWithinAt_singleton (f := g) (x := x)).mono fun y hy =>
      le_antisymm (hy.2.trans hle) hy.1

/-- **Integrability of a piecewise continuous function**: if on every piece `[s, t]` the function
agrees on `(s, t)` with a function continuous on `[s, t]`, it is integrable on `[a, b]`. -/
theorem intervalIntegrable_of_piecewise {g : ℝ → E} {B : Finset ℝ} {lo hi : ℝ}
    (h : ∀ s t, lo ≤ s → s < t → t ≤ hi → (∀ x ∈ B, x ∉ Ioo s t) →
      ∃ G : ℝ → E, ContinuousOn G (Icc s t) ∧ EqOn g G (Ioo s t))
    {a b : ℝ} (ha : lo ≤ a) (hab : a ≤ b) (hb : b ≤ hi) : IntervalIntegrable g volume a b := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact IntervalIntegrable.refl
  refine piecewise_induction (B := B) (P := fun a b => IntervalIntegrable g volume a b) ?_ ?_
    a b ha hlt hb
  · intro s t hs hst ht hB
    obtain ⟨G, hG, hgG⟩ := h s t hs hst ht hB
    refine (hG.intervalIntegrable_of_Icc hst.le).congr_uIoo fun x hx => ?_
    rw [uIoo_of_le hst.le] at hx
    exact (hgG hx).symm
  · intro a x b _ _ _ _ _ h₁ h₂
    exact h₁.trans h₂

/-- **Integration by parts over the pieces** (the telescoping in Milnor's proofs of 12.2 and 13.1).
If on every piece `[s, t]`, `∫ₛᵗ g = F⁻(t) - F⁺(s)` (with `F⁻`, `F⁺` the left and right boundary
values, functions of the endpoint only), then on `[a, b]` the boundary terms at the break points
add up to jumps: `∫ₐᵇ g = F⁻(b) - F⁺(a) - Σ_{x ∈ B ∩ (a, b)} (F⁺(x) - F⁻(x))`. -/
theorem integral_eq_of_piecewise [NormedSpace ℝ E] [CompleteSpace E] {g Fl Fr : ℝ → E}
    {B : Finset ℝ} {lo hi : ℝ}
    (hint : ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → IntervalIntegrable g volume a b)
    (h : ∀ s t, lo ≤ s → s < t → t ≤ hi → (∀ x ∈ B, x ∉ Ioo s t) →
      ∫ τ in s..t, g τ = Fl t - Fr s) :
    ∀ a b, lo ≤ a → a < b → b ≤ hi →
      ∫ τ in a..b, g τ = Fl b - Fr a - ∑ x ∈ B with x ∈ Ioo a b, (Fr x - Fl x) := by
  refine piecewise_induction (B := B) ?_ ?_
  · intro s t hs hst ht hB
    have : (B.filter (· ∈ Ioo s t)) = ∅ := Finset.filter_eq_empty_iff.2 hB
    rw [h s t hs hst ht hB, this, Finset.sum_empty, sub_zero]
  · intro a x b ha hax hxb hb hx h₁ h₂
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint a x ha hax.le (hxb.le.trans hb)) (hint x b (ha.trans hax.le) hxb.le hb), h₁, h₂,
      sum_filter_Ioo_split _ hax hxb hx]
    abel

end Integral

/-! ### Partial derivatives on a closed strip `U × [a, b]` -/

section Strip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `∂F/∂u` on a strip `S ⊆ ℝ × ℝ` (first variable `u`, second `t`), computed within `S`. -/
def pdU (S : Set (ℝ × ℝ)) (F : ℝ × ℝ → E) (p : ℝ × ℝ) : E := fderivWithin ℝ F S p (1, 0)

/-- `∂F/∂t` on a strip `S ⊆ ℝ × ℝ`, computed within `S`: on the edges `t = a`, `t = b` of
`U × [a, b]` these are the one-sided derivatives. -/
def pdT (S : Set (ℝ × ℝ)) (F : ℝ × ℝ → E) (p : ℝ × ℝ) : E := fderivWithin ℝ F S p (0, 1)

variable {U : Set ℝ} {a b : ℝ}

theorem uniqueDiffOn_strip (hU : IsOpen U) (hab : a < b) : UniqueDiffOn ℝ (U ×ˢ Icc a b) :=
  hU.uniqueDiffOn.prod (uniqueDiffOn_Icc hab)

theorem mk_mem_strip {u t : ℝ} (hu : u ∈ U) (ht : t ∈ Icc a b) : (u, t) ∈ U ×ˢ Icc a b :=
  mk_mem_prod hu ht

theorem strip_mem_nhds (hU : IsOpen U) {u t : ℝ} (hu : u ∈ U) (ht : t ∈ Ioo a b) :
    U ×ˢ Icc a b ∈ 𝓝 (u, t) :=
  prod_mem_nhds (hU.mem_nhds hu) (Icc_mem_nhds ht.1 ht.2)

theorem contDiffOn_pdU (hU : IsOpen U) (hab : a < b) {F : ℝ × ℝ → E}
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ Icc a b)) : ContDiffOn ℝ ∞ (pdU (U ×ˢ Icc a b) F) (U ×ˢ Icc a b) :=
  (hF.fderivWithin (uniqueDiffOn_strip hU hab) (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem contDiffOn_pdT (hU : IsOpen U) (hab : a < b) {F : ℝ × ℝ → E}
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ Icc a b)) : ContDiffOn ℝ ∞ (pdT (U ×ˢ Icc a b) F) (U ×ˢ Icc a b) :=
  (hF.fderivWithin (uniqueDiffOn_strip hU hab) (m := ∞) (by simp)).clm_apply contDiffOn_const

/-- `∂F/∂u` is the derivative along the horizontal line through a point of the strip (the
`u`-direction is open). -/
theorem hasDerivAt_pdU (hU : IsOpen U) {F : ℝ × ℝ → E}
    (hF : DifferentiableOn ℝ F (U ×ˢ Icc a b)) {u t : ℝ} (hu : u ∈ U) (ht : t ∈ Icc a b) :
    HasDerivAt (fun u => F (u, t)) (pdU (U ×ˢ Icc a b) F (u, t)) u := by
  have h1 : HasFDerivWithinAt F (fderivWithin ℝ F (U ×ˢ Icc a b) (u, t)) (U ×ˢ Icc a b) (u, t) :=
    (hF (u, t) (mk_mem_strip hu ht)).hasFDerivWithinAt
  have h2 : HasDerivWithinAt (fun u => F (u, t)) (pdU (U ×ˢ Icc a b) F (u, t)) U u :=
    h1.comp_hasDerivWithinAt (x := u) (f := fun u : ℝ => (u, t))
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u t)).hasDerivWithinAt
      fun v hv => mk_mem_strip hv ht
  exact h2.hasDerivAt (hU.mem_nhds hu)

/-- `∂F/∂t` is the derivative within `[a, b]` along the vertical segment through a point of the
strip: on the edges, a one-sided derivative. -/
theorem hasDerivWithinAt_pdT {F : ℝ × ℝ → E} (hF : DifferentiableOn ℝ F (U ×ˢ Icc a b)) {u t : ℝ}
    (hu : u ∈ U) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun t => F (u, t)) (pdT (U ×ˢ Icc a b) F (u, t)) (Icc a b) t := by
  have h1 : HasFDerivWithinAt F (fderivWithin ℝ F (U ×ˢ Icc a b) (u, t)) (U ×ˢ Icc a b) (u, t) :=
    (hF (u, t) (mk_mem_strip hu ht)).hasFDerivWithinAt
  exact h1.comp_hasDerivWithinAt (x := t) (f := fun t : ℝ => (u, t))
    ((hasDerivAt_const t u).prodMk (hasDerivAt_id t)).hasDerivWithinAt
    fun v hv => mk_mem_strip hu hv

theorem hasDerivAt_pdT {F : ℝ × ℝ → E} (hF : DifferentiableOn ℝ F (U ×ˢ Icc a b)) {u t : ℝ}
    (hu : u ∈ U) (ht : t ∈ Ioo a b) :
    HasDerivAt (fun t => F (u, t)) (pdT (U ×ˢ Icc a b) F (u, t)) t :=
  (hasDerivWithinAt_pdT hF hu (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- On the left edge, `∂F/∂t` is the right derivative. -/
theorem derivWithin_Ici_eq_pdT (hab : a < b) {F : ℝ × ℝ → E}
    (hF : DifferentiableOn ℝ F (U ×ˢ Icc a b)) {u : ℝ} (hu : u ∈ U) :
    derivWithin (fun t => F (u, t)) (Ici a) a = pdT (U ×ˢ Icc a b) F (u, a) :=
  ((hasDerivWithinAt_pdT hF hu (left_mem_Icc.2 hab.le)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE hab)).derivWithin (uniqueDiffWithinAt_Ici a)

/-- On the right edge, `∂F/∂t` is the left derivative. -/
theorem derivWithin_Iic_eq_pdT (hab : a < b) {F : ℝ × ℝ → E}
    (hF : DifferentiableOn ℝ F (U ×ˢ Icc a b)) {u : ℝ} (hu : u ∈ U) :
    derivWithin (fun t => F (u, t)) (Iic b) b = pdT (U ×ˢ Icc a b) F (u, b) :=
  ((hasDerivWithinAt_pdT hF hu (right_mem_Icc.2 hab.le)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsLE hab)).derivWithin (uniqueDiffWithinAt_Iic b)

/-- Inside the strip, `pdT` is the ordinary partial derivative. -/
theorem deriv_eq_pdT {F : ℝ × ℝ → E} (hF : DifferentiableOn ℝ F (U ×ˢ Icc a b)) {u t : ℝ}
    (hu : u ∈ U) (ht : t ∈ Ioo a b) :
    deriv (fun t => F (u, t)) t = pdT (U ×ˢ Icc a b) F (u, t) :=
  (hasDerivAt_pdT hF hu ht).deriv

theorem deriv_eq_pdU (hU : IsOpen U) {F : ℝ × ℝ → E} (hF : DifferentiableOn ℝ F (U ×ˢ Icc a b))
    {u t : ℝ} (hu : u ∈ U) (ht : t ∈ Icc a b) :
    deriv (fun u => F (u, t)) u = pdU (U ×ˢ Icc a b) F (u, t) :=
  (hasDerivAt_pdU hU hF hu ht).deriv

/-- **Symmetry of the mixed partial derivatives on a closed strip**, also on its edges:
`∂/∂u ∂F/∂t = ∂/∂t ∂F/∂u`. -/
theorem pdU_pdT (hU : IsOpen U) (hab : a < b) {F : ℝ × ℝ → E}
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ Icc a b)) {p : ℝ × ℝ} (hp : p ∈ U ×ˢ Icc a b) :
    pdU (U ×ˢ Icc a b) (pdT (U ×ˢ Icc a b) F) p = pdT (U ×ˢ Icc a b) (pdU (U ×ˢ Icc a b) F) p := by
  set S := U ×ˢ Icc a b
  have hS : UniqueDiffOn ℝ S := uniqueDiffOn_strip hU hab
  have hd : DifferentiableWithinAt ℝ (fderivWithin ℝ F S) S p :=
    ((hF.fderivWithin hS (m := ∞) (by simp)).differentiableOn (by simp)) p hp
  have key : ∀ v w : ℝ × ℝ,
      fderivWithin ℝ (fun q => fderivWithin ℝ F S q v) S p w =
        fderivWithin ℝ (fderivWithin ℝ F S) S p w v := by
    intro v w
    rw [fderivWithin_clm_apply (hS p hp) hd (differentiableWithinAt_const v)]
    simp
  have hclos : p ∈ closure (interior S) := by
    have : interior S = U ×ˢ Ioo a b := by
      rw [interior_prod_eq, hU.interior_eq, interior_Icc]
    rw [this, closure_prod_eq, closure_Ioo hab.ne]
    exact ⟨subset_closure hp.1, hp.2⟩
  have hsymm := (hF p hp).isSymmSndFDerivWithinAt (n := ∞)
    (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
    hS hclos hp
  change fderivWithin ℝ (fun q => fderivWithin ℝ F S q (0, 1)) S p (1, 0) =
    fderivWithin ℝ (fun q => fderivWithin ℝ F S q (1, 0)) S p (0, 1)
  rw [key, key]
  exact hsymm _ _

/-! ### Differentiation under the integral sign -/

/-- **Differentiation under the integral sign on a closed strip.**  If `F` and `F'` are continuous
on `U × [a, b]` and `F'(u, t)` is the `u`-derivative of `F` at the interior points, then
`u ↦ ∫ₐᵇ F(u, t) dt` has derivative `∫ₐᵇ F'(u₀, t) dt` at every `u₀ ∈ U`. -/
theorem hasDerivAt_integral_strip [CompleteSpace E] {F F' : ℝ × ℝ → E} (hU : IsOpen U)
    (hab : a ≤ b) (hF : ContinuousOn F (U ×ˢ Icc a b)) (hF' : ContinuousOn F' (U ×ˢ Icc a b))
    (hd : ∀ u ∈ U, ∀ t ∈ Ioo a b, HasDerivAt (fun u => F (u, t)) (F' (u, t)) u) {u₀ : ℝ}
    (hu₀ : u₀ ∈ U) :
    HasDerivAt (fun u => ∫ t in a..b, F (u, t)) (∫ t in a..b, F' (u₀, t)) u₀ := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU u₀ hu₀
  have hcb : closedBall u₀ (δ / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hδ)).trans hball
  have hK : IsCompact (closedBall u₀ (δ / 2) ×ˢ Icc a b) :=
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hKS : closedBall u₀ (δ / 2) ×ˢ Icc a b ⊆ U ×ˢ Icc a b := prod_mono hcb le_rfl
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hF'.mono hKS)
  have hsec : ∀ {G : ℝ × ℝ → E}, ContinuousOn G (U ×ˢ Icc a b) → ∀ u ∈ U,
      ContinuousOn (fun t => G (u, t)) (Icc a b) := fun hG u hu =>
    hG.comp (continuousOn_const.prodMk continuousOn_id) fun t ht => mk_mem_strip hu ht
  have huIoc : Ι a b ⊆ Icc a b := by
    rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self
  have hb_ae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := (countable_singleton b).ae_notMem volume
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun u t => F (u, t)) (F' := fun u t => F' (u, t)) (bound := fun _ => M)
    (ball_mem_nhds u₀ (half_pos hδ)) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [hU.mem_nhds hu₀] with u hu
    exact ((hsec hF u hu).mono huIoc).aestronglyMeasurable measurableSet_uIoc
  · exact (hsec hF u₀ hu₀).intervalIntegrable_of_Icc hab
  · exact ((hsec hF' u₀ hu₀).mono huIoc).aestronglyMeasurable measurableSet_uIoc
  · refine .of_forall fun t ht u hu => hM _ ⟨ball_subset_closedBall hu, huIoc ht⟩
  · filter_upwards [hb_ae] with t htb ht u hu
    rw [uIoc_of_le hab] at ht
    exact hd u (hball (ball_subset_ball (half_le_self hδ.le) hu)) t
      ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩

/-- **Differentiation under the integral sign for a piecewise smooth integrand.**  If on every
piece `[s, t]` the integrand `g u τ` agrees, for `τ ∈ (s, t)`, with a function `G` that is `C¹` on
the closed strip `U × [s, t]`, then `u ↦ ∫ₐᵇ g u τ dτ` is differentiable on `U`, with derivative
`∫ₐᵇ ∂g/∂u dτ`. -/
theorem hasDerivAt_integral_of_piecewise [CompleteSpace E] {g : ℝ → ℝ → E} (hU : IsOpen U)
    {B : Finset ℝ} {lo hi : ℝ}
    (h : ∀ s t, lo ≤ s → s < t → t ≤ hi → (∀ x ∈ B, x ∉ Ioo s t) → ∃ G : ℝ × ℝ → E,
      ContDiffOn ℝ 1 G (U ×ˢ Icc s t) ∧ ∀ u ∈ U, ∀ τ ∈ Ioo s t, G (u, τ) = g u τ)
    {a b : ℝ} (ha : lo ≤ a) (hab : a ≤ b) (hb : b ≤ hi) {u₀ : ℝ} (hu₀ : u₀ ∈ U) :
    HasDerivAt (fun u => ∫ τ in a..b, g u τ) (∫ τ in a..b, deriv (fun u => g u τ) u₀) u₀ := by
  -- on a piece
  have hpiece : ∀ s t, lo ≤ s → s < t → t ≤ hi → (∀ x ∈ B, x ∉ Ioo s t) →
      (∀ u ∈ U, ∃ G : ℝ → E, ContinuousOn G (Icc s t) ∧ EqOn (g u) G (Ioo s t)) ∧
      (∀ u ∈ U, ∃ G : ℝ → E, ContinuousOn G (Icc s t) ∧
        EqOn (fun τ => deriv (fun u => g u τ) u) G (Ioo s t)) ∧
      ∀ u ∈ U, HasDerivAt (fun u => ∫ τ in s..t, g u τ)
        (∫ τ in s..t, deriv (fun u => g u τ) u) u := by
    intro s t hs hst ht hB
    obtain ⟨G, hG, hGg⟩ := h s t hs hst ht hB
    set S := U ×ˢ Icc s t
    have hGd : DifferentiableOn ℝ G S := hG.differentiableOn one_ne_zero
    have hG' : ContinuousOn (pdU S G) S :=
      (hG.continuousOn_fderivWithin (uniqueDiffOn_strip hU hst) le_rfl).clm_apply
        continuousOn_const
    have hderiv : ∀ u ∈ U, ∀ τ ∈ Ioo s t, deriv (fun u => g u τ) u = pdU S G (u, τ) := by
      intro u hu τ hτ
      have hev : (fun u => g u τ) =ᶠ[𝓝 u] fun u => G (u, τ) := by
        filter_upwards [hU.mem_nhds hu] with v hv
        exact (hGg v hv τ hτ).symm
      rw [hev.deriv_eq]
      exact (hasDerivAt_pdU hU hGd hu (Ioo_subset_Icc_self hτ)).deriv
    have hsec : ∀ {K : ℝ × ℝ → E}, ContinuousOn K S → ∀ u ∈ U,
        ContinuousOn (fun τ => K (u, τ)) (Icc s t) := fun hK u hu =>
      hK.comp (continuousOn_const.prodMk continuousOn_id) fun τ hτ => mk_mem_strip hu hτ
    refine ⟨fun u hu => ⟨_, hsec hG.continuousOn u hu, fun τ hτ => (hGg u hu τ hτ).symm⟩,
      fun u hu => ⟨_, hsec hG' u hu, fun τ hτ => hderiv u hu τ hτ⟩, fun u hu => ?_⟩
    have h1 := hasDerivAt_integral_strip hU hst.le hG.continuousOn hG'
      (fun u hu τ hτ => hasDerivAt_pdU hU hGd hu (Ioo_subset_Icc_self hτ)) hu
    have e1 : ∀ v ∈ U, ∫ τ in s..t, g v τ = ∫ τ in s..t, G (v, τ) := fun v hv =>
      intervalIntegral.integral_congr_Ioo_of_le hst.le fun τ hτ => (hGg v hv τ hτ).symm
    have e2 : ∫ τ in s..t, deriv (fun u => g u τ) u = ∫ τ in s..t, pdU S G (u, τ) :=
      intervalIntegral.integral_congr_Ioo_of_le hst.le fun τ hτ => hderiv u hu τ hτ
    rw [e2]
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hu] with v hv
    exact e1 v hv
  have hint : ∀ u ∈ U, ∀ a b, lo ≤ a → a ≤ b → b ≤ hi →
      IntervalIntegrable (g u) volume a b := fun u hu a b ha hab hb =>
    intervalIntegrable_of_piecewise (fun s t hs hst ht hB => (hpiece s t hs hst ht hB).1 u hu)
      ha hab hb
  have hint' : ∀ u ∈ U, ∀ a b, lo ≤ a → a ≤ b → b ≤ hi →
      IntervalIntegrable (fun τ => deriv (fun u => g u τ) u) volume a b :=
    fun u hu a b ha hab hb => intervalIntegrable_of_piecewise
      (fun s t hs hst ht hB => (hpiece s t hs hst ht hB).2.1 u hu) ha hab hb
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp only [intervalIntegral.integral_same]
    exact hasDerivAt_const _ _
  refine piecewise_induction (P := fun a b => HasDerivAt (fun u => ∫ τ in a..b, g u τ)
    (∫ τ in a..b, deriv (fun u => g u τ) u₀) u₀) (fun s t hs hst ht hB =>
      (hpiece s t hs hst ht hB).2.2 u₀ hu₀) ?_ a b ha hlt hb
  intro a x b ha hax hxb hb _ h₁ h₂
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint' u₀ hu₀ a x ha hax.le (hxb.le.trans hb)) (hint' u₀ hu₀ x b (ha.trans hax.le) hxb.le hb)]
  refine (h₁.add h₂).congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hu₀] with v hv
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hint v hv a x ha hax.le (hxb.le.trans hb)) (hint v hv x b (ha.trans hax.le) hxb.le hb)).symm

end Strip

end Morse
