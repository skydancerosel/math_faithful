import Mathlib

/-!
Milnor, *Morse Theory*, §3, pp. 12–13 (the topological half of Theorem 3.1).

# Trajectories cross a regular slab once; sublevel sets and deformation retractions

Milnor's proof of Theorem 3.1 (p. 13) studies, for a fixed point `q`, the function
`t ↦ f(φ_t(q))`, where `φ` is the flow of the field `X = ρ · grad f`. Its derivative is `+1` at
every time at which `φ_t(q)` lies in `f⁻¹[a, b]`, and he concludes: "Thus the correspondence
`t → f(φ_t(q))` is linear with derivative `+1` as long as `f(φ_t(q))` lies between `a` and `b`."
From this he reads off, "clearly", that `φ_{b-a}` carries `M^a` onto `M^b`, and that his formula
for `r_t` (`q` if `f(q) ≤ a`, `φ_{t(a - f(q))}(q)` if `a ≤ f(q) ≤ b`) defines a deformation
retraction of `M^b` onto `M^a`.

Everything after the computation of the derivative is one-dimensional calculus and point-set
topology, and is proved here for an arbitrary continuous flow `φ` on a topological space `T` and
an arbitrary continuous `F : T → ℝ` such that `t ↦ F(φ_t(x))` has derivative `1` whenever its value
lies in `[a, b]` (`Morse.IsSlabFlow`). The Euclidean case of Theorem 3.1 (`T = E`, `F = f`,
`φ` the flow of `ρ · grad f`) is `Morse/Chapter2/Regular.lean`; the same abstract results apply to
a submanifold `M ⊆ ℝᴷ` invariant under an ambient flow (`T = M`).

## What Milnor's text leaves implicit

* **One crossing.** The derivative of `g(t) = f(φ_t(q))` is known only while `a ≤ g(t) ≤ b`; outside
  the slab nothing is known (Milnor does not even require `ρ ≥ 0`). "Linear as long as it lies
  between `a` and `b`" needs a continuity argument: a trajectory which is in the slab stays in it,
  moving linearly, until it leaves through the top (`UnitSpeedInSlab.eq_add`), and it can never
  cross a level `c ∈ [a, b]` downwards (`UnitSpeedInSlab.le_of_le`, `UnitSpeedInSlab.le_of_le'`).
  Both are proved by "continuous induction" (`IsClosed.Icc_subset_of_forall_mem_nhdsWithin`): at a
  time where `g = c ∈ [a, b]` the derivative `1 > 0` pushes `g` above `c`. This is Lemma C of the
  exposition (`Exposition/Chapter2.md`).
* **`φ_{b-a}(M^a) = M^b`**, which Milnor calls clear, needs both inclusions: a trajectory starting
  below `a` cannot be above `b` at time `b - a` (it crosses the slab at unit speed), and a
  trajectory ending below `b` at time `b - a` cannot have started above `a` (it cannot cross a
  level of the slab downwards). Both directions are `IsSlabFlow.image_sublevel`, proved more
  generally for `a ≤ c ≤ c' ≤ b`: `φ_{c'-c}(M^c) = M^{c'}`.
* **That `r_t` maps `M^b` into `M^b`, and `r_1` into `M^a`**: along the trajectory of
  `q ∈ f⁻¹[a, b]`, `f(φ_s(q)) = f(q) + s` for `a - f(q) ≤ s ≤ 0`, so
  `f(r_t(q)) = f(q) + t (a - f(q)) ∈ [a, f(q)]` (`IsSlabFlow.apply_deformation`).
* **Continuity of `r`.** Milnor's two formulas agree on `f = a` because `φ_0 = id`; the pasting
  lemma is avoided by writing `r_t(q) = φ_{t · min(0, a - f(q))}(q)` (`Morse.deformation`), visibly
  continuous in `(t, q)`, and checking that it agrees with both of Milnor's formulas
  (`deformation_of_le`, `deformation_of_ge`).
* **The homotopy equivalence.** "`M^a` is a deformation retract of `M^b`, so that the inclusion map
  `M^a → M^b` is a homotopy equivalence": the homotopy inverse is `r_1`
  (`IsStrongDeformationRetract.exists_homotopyEquiv`). Milnor's `r_t` fixes `M^a` pointwise for
  every `t`, so it is a *strong* deformation retraction, which is what is formalized.

## Main definitions and results

* `Morse.sublevel F c = {x | F x ≤ c}`: Milnor's `M^c`.
* `Morse.IsStrongDeformationRetract A`: there is a homotopy rel `A` from the identity to a map with
  values in `A`.
* `Morse.IsStrongDeformationRetract.exists_homotopyEquiv`: then the inclusion is a homotopy
  equivalence.
* `Morse.UnitSpeedInSlab g a b`: `g : ℝ → ℝ` is continuous with `g' = 1` wherever `g ∈ [a, b]`;
  `UnitSpeedInSlab.eq_add`, `le_of_le`, `le_of_le'` (one crossing).
* `Morse.IsSlabFlow F a b φ`, and for it: `apply_eq_add`, `image_sublevel` (Milnor's first half),
  `homotopyRel` (Milnor's `r_t`), `isStrongDeformationRetract`, `homotopyEquiv` (second half).
-/

open Set Filter Topology Function
open scoped unitInterval

noncomputable section

namespace Morse

/-! ### Sublevel sets and strong deformation retracts -/

/-- Milnor's `M^c = f⁻¹(-∞, c] = {p ∈ M : f(p) ≤ c}` (p. 12). -/
def sublevel {T : Type*} (F : T → ℝ) (c : ℝ) : Set T :=
  {x | F x ≤ c}

@[simp]
theorem mem_sublevel {T : Type*} {F : T → ℝ} {c : ℝ} {x : T} : x ∈ sublevel F c ↔ F x ≤ c :=
  Iff.rfl

theorem sublevel_mono {T : Type*} (F : T → ℝ) {c c' : ℝ} (h : c ≤ c') :
    sublevel F c ⊆ sublevel F c' :=
  fun _ hx => le_trans hx h

/-- **Strong deformation retract.** `A ⊆ X` is a strong deformation retract of `X` if there are a
continuous map `r : X → X` with values in `A` and a homotopy from the identity of `X` to `r` which
fixes `A` pointwise at all times (Mathlib's `ContinuousMap.HomotopyRel`). In Milnor's notation
(p. 13) the homotopy is `(t, x) ↦ r_t(x)`, `0 ≤ t ≤ 1`, with `r_0 = id`, `r_1 = r`,
`r_1(X) ⊆ A`, and `r_t = id` on `A`. Since `r` agrees with the identity on `A`, it is a retraction
onto `A`. -/
def IsStrongDeformationRetract {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ r : C(X, X), (∀ x, r x ∈ A) ∧ Nonempty ((ContinuousMap.id X).HomotopyRel r A)

/-- **The inclusion of a strong deformation retract is a homotopy equivalence** (Milnor p. 12:
"`M^a` is a deformation retract of `M^b`, so that the inclusion map `M^a → M^b` is a homotopy
equivalence"). Stated for subsets `A ⊆ B` of a space `T`, `A` being viewed inside the subspace `B`;
the homotopy inverse is the retraction `r_1`. -/
theorem IsStrongDeformationRetract.exists_homotopyEquiv {T : Type*} [TopologicalSpace T]
    {A B : Set T} (hAB : A ⊆ B) (h : IsStrongDeformationRetract ((↑) ⁻¹' A : Set B)) :
    ∃ e : ContinuousMap.HomotopyEquiv A B, ⇑e = Set.inclusion hAB := by
  obtain ⟨r, hrA, ⟨H⟩⟩ := h
  let i : C(A, B) := ⟨Set.inclusion hAB, continuous_inclusion hAB⟩
  let j : C(B, A) :=
    ⟨fun x => ⟨r x, hrA x⟩, (r.continuous.comp continuous_id).subtype_val.subtype_mk _⟩
  have hji : j.comp i = ContinuousMap.id A := by
    refine ContinuousMap.ext fun x => Subtype.ext ?_
    have := H.fst_eq_snd (x := i x) x.2
    change ((r (i x) : B) : T) = x
    rw [← this]
    rfl
  have hij : i.comp j = r := by
    ext x
    rfl
  refine ⟨⟨i, j, ?_, ?_⟩, rfl⟩
  · rw [hji]
  · rw [hij]
    exact ⟨H.toHomotopy.symm⟩

/-! ### One crossing -/

/-- If `g` has positive derivative at `t`, then `g > g(t)` just to the right of `t`. -/
theorem eventually_lt_of_hasDerivAt_pos {g : ℝ → ℝ} {g' t : ℝ} (h : HasDerivAt g g' t)
    (hg' : 0 < g') : ∀ᶠ s in 𝓝[>] t, g t < g s := by
  have h1 : Tendsto (slope g t) (𝓝[>] t) (𝓝 g') :=
    (hasDerivAt_iff_tendsto_slope.1 h).mono_left (nhdsWithin_mono _ fun s hs => ne_of_gt hs)
  filter_upwards [h1.eventually (lt_mem_nhds hg'), self_mem_nhdsWithin] with s hs hst
  rw [slope_def_field] at hs
  have hst' : 0 < s - t := sub_pos.2 hst
  have := (div_pos_iff_of_pos_right hst').1 hs
  linarith

/-- The hypothesis of the one-crossing lemma: `g : ℝ → ℝ` is continuous and has derivative `1` at
every time `t` with `a ≤ g(t) ≤ b`. This is the behaviour of `t ↦ f(φ_t(q))` along a trajectory of
Milnor's field `X = ρ · grad f` (p. 13); nothing is assumed outside the slab `[a, b]`. -/
structure UnitSpeedInSlab (g : ℝ → ℝ) (a b : ℝ) : Prop where
  continuous : Continuous g
  hasDerivAt : ∀ t, g t ∈ Icc a b → HasDerivAt g 1 t

namespace UnitSpeedInSlab

variable {g : ℝ → ℝ} {a b : ℝ}

/-- **Time reversal**: `t ↦ -g(-t)` crosses the slab `[-b, -a]` at unit speed. -/
theorem reverse (hg : UnitSpeedInSlab g a b) : UnitSpeedInSlab (fun t => -g (-t)) (-b) (-a) where
  continuous := (hg.continuous.comp continuous_neg).neg
  hasDerivAt t ht := by
    have h : g (-t) ∈ Icc a b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h1 : HasDerivAt (fun t => g (-t)) (1 * -1) t :=
      (hg.hasDerivAt (-t) h).comp t (hasDerivAt_neg t)
    have h2 : HasDerivAt (fun t => -g (-t)) (-(1 * -1)) t := h1.neg
    convert h2 using 1
    norm_num

/-- **No downward crossing**: once `g` has reached a level `c ∈ [a, b]`, it stays at or above
`c`. At a time where `g = c` the derivative `1 > 0` pushes `g` above `c`. -/
theorem le_of_le (hg : UnitSpeedInSlab g a b) {c s t : ℝ} (hc : c ∈ Icc a b) (hst : s ≤ t)
    (hs : c ≤ g s) : c ≤ g t := by
  have key : Icc s t ⊆ {r | c ≤ g r} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin
      ((isClosed_le continuous_const hg.continuous).inter isClosed_Icc) hs ?_
    rintro r ⟨hr, -⟩
    rcases (show c ≤ g r from hr).lt_or_eq with hlt | heq
    · exact mem_nhdsWithin_of_mem_nhds (mem_of_superset
        ((isOpen_lt continuous_const hg.continuous).mem_nhds hlt)
          fun x (hx : c < g x) => show c ≤ g x from hx.le)
    · have hd := hg.hasDerivAt r (heq ▸ hc)
      filter_upwards [eventually_lt_of_hasDerivAt_pos hd one_pos] with x hx
      exact heq.le.trans hx.le
  exact key ⟨hst, le_rfl⟩

/-- The time-reversed form of `le_of_le`: if `g` is at or below a level `c ∈ [a, b]` at time `t`,
it was at or below `c` at every earlier time. -/
theorem le_of_le' (hg : UnitSpeedInSlab g a b) {c s t : ℝ} (hc : c ∈ Icc a b) (hst : s ≤ t)
    (ht : g t ≤ c) : g s ≤ c := by
  have := hg.reverse.le_of_le (c := -c) (s := -t) (t := -s) ⟨neg_le_neg hc.2, neg_le_neg hc.1⟩
    (neg_le_neg hst) (by simpa using ht)
  simpa using this

/-- **Linear while in the slab, forwards**: if `a ≤ g(s)` and `g(s) + (t - s) ≤ b`, then
`g(t) = g(s) + (t - s)`. -/
theorem eq_add_of_le (hg : UnitSpeedInSlab g a b) {s t : ℝ} (hs : a ≤ g s) (hst : s ≤ t)
    (ht : g s + (t - s) ≤ b) : g t = g s + (t - s) := by
  have hab : a ≤ b := by linarith
  have key : Icc s t ⊆ {r | g r = g s + (r - s)} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin
      ((isClosed_eq hg.continuous (by fun_prop)).inter isClosed_Icc) (by simp) ?_
    rintro r ⟨hr, hr1, hr2⟩
    have hr : g r = g s + (r - s) := hr
    have hrb : g r < b := by rw [hr]; linarith
    obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1
      (hg.continuous.continuousAt.eventually (gt_mem_nhds hrb))
    filter_upwards [Ioo_mem_nhdsGT (show r < r + δ by linarith)] with r' hr'
    have hslab : ∀ x ∈ Icc r r', g x ∈ Icc a b := fun x hx =>
      ⟨hg.le_of_le ⟨le_rfl, hab⟩ (hr1.trans hx.1) hs,
        (hδb (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2, hr'.2])).le⟩
    have hconst := constant_of_has_deriv_right_zero (f := fun x => g x - x) (a := r) (b := r')
      (hg.continuous.sub continuous_id).continuousOn (fun x hx => by
        have h1 : HasDerivAt (fun x => g x - x) (1 - 1) x :=
          (hg.hasDerivAt x (hslab x (Ico_subset_Icc_self hx))).sub (hasDerivAt_id' x)
        rw [sub_self] at h1
        exact h1.hasDerivWithinAt) r' ⟨hr'.1.le, le_rfl⟩
    change g r' = g s + (r' - s)
    linarith
  exact key ⟨hst, le_rfl⟩

/-- **Linear while in the slab** (Milnor p. 13: "`t → f(φ_t(q))` is linear with derivative `+1` as
long as `f(φ_t(q))` lies between `a` and `b`"): if `g(s) ∈ [a, b]` then `g(s + τ) = g(s) + τ` for
all `τ ∈ [a - g(s), b - g(s)]`, in both directions of time. -/
theorem eq_add (hg : UnitSpeedInSlab g a b) {s τ : ℝ} (hs : g s ∈ Icc a b)
    (hτ : τ ∈ Icc (a - g s) (b - g s)) : g (s + τ) = g s + τ := by
  rcases le_total 0 τ with h | h
  · have := hg.eq_add_of_le hs.1 (le_add_of_nonneg_right h) (by linarith [hτ.2])
    rwa [add_sub_cancel_left] at this
  · have := hg.reverse.eq_add_of_le (s := -s) (t := -(s + τ)) (by simp; linarith [hs.2])
      (by linarith) (by simp; linarith [hτ.1])
    simp only [neg_neg] at this
    linarith

end UnitSpeedInSlab

/-! ### Slab flows -/

variable {T : Type*}

/-- Milnor's deformation `r_t` (p. 13), written as one formula:
`r_t(x) = φ_{t · min(0, a - F(x))}(x)`. It equals `x` if `F(x) ≤ a`
(`IsSlabFlow.deformation_of_le`) and `φ_{t(a - F(x))}(x)` if `F(x) ≥ a` (`deformation_of_ge`),
which are Milnor's two cases. -/
def deformation (φ : ℝ → T → T) (F : T → ℝ) (a t : ℝ) (x : T) : T :=
  φ (t * min 0 (a - F x)) x

theorem deformation_of_ge {φ : ℝ → T → T} {F : T → ℝ} {a : ℝ} {x : T} (hx : a ≤ F x) (t : ℝ) :
    deformation φ F a t x = φ (t * (a - F x)) x := by
  simp [deformation, min_eq_right (sub_nonpos.2 hx)]

variable [TopologicalSpace T]

/-- The abstract situation of Milnor's proof of Theorem 3.1: `φ` is a continuous flow on `T`
(`φ_0 = id`, `φ_{s+t} = φ_s ∘ φ_t`, `(t, x) ↦ φ_t(x)` continuous), `F : T → ℝ` is continuous,
and along every trajectory `t ↦ F(φ_t(x))` has derivative `1` at the times at which
`F(φ_t(x)) ∈ [a, b]`. For Milnor, `F = f` and `φ` is the flow of `ρ · grad f`. -/
structure IsSlabFlow (F : T → ℝ) (a b : ℝ) (φ : ℝ → T → T) : Prop where
  continuous : Continuous fun p : ℝ × T => φ p.1 p.2
  zero : ∀ x, φ 0 x = x
  add : ∀ s t x, φ (s + t) x = φ s (φ t x)
  continuous_F : Continuous F
  hasDerivAt : ∀ x t, F (φ t x) ∈ Icc a b → HasDerivAt (fun s => F (φ s x)) 1 t

namespace IsSlabFlow

variable {F : T → ℝ} {a b : ℝ} {φ : ℝ → T → T}

theorem deformation_of_le (h : IsSlabFlow F a b φ) {x : T} (hx : F x ≤ a) (t : ℝ) :
    deformation φ F a t x = x := by
  simp [deformation, min_eq_left (sub_nonneg.2 hx), h.zero]

theorem deformation_zero (h : IsSlabFlow F a b φ) (x : T) : deformation φ F a 0 x = x := by
  simp [deformation, h.zero]

theorem continuous_left (h : IsSlabFlow F a b φ) (x : T) : Continuous fun t => φ t x :=
  h.continuous.comp (continuous_id.prodMk continuous_const)

theorem continuous_right (h : IsSlabFlow F a b φ) (t : ℝ) : Continuous (φ t) :=
  h.continuous.comp (continuous_const.prodMk continuous_id)

theorem continuous_deformation (h : IsSlabFlow F a b φ) :
    Continuous fun p : ℝ × T => deformation φ F a p.1 p.2 :=
  h.continuous.comp ((continuous_fst.mul (continuous_const.min
    (continuous_const.sub (h.continuous_F.comp continuous_snd)))).prodMk continuous_snd)

/-- Along each trajectory, `t ↦ F(φ_t(x))` crosses `[a, b]` at unit speed. -/
theorem unitSpeed (h : IsSlabFlow F a b φ) (x : T) : UnitSpeedInSlab (fun t => F (φ t x)) a b :=
  ⟨h.continuous_F.comp (h.continuous_left x), h.hasDerivAt x⟩

/-- **Milnor p. 13**: `F(φ_t(x)) = F(x) + t` for `x` in the slab and `a - F(x) ≤ t ≤ b - F(x)`. -/
theorem apply_eq_add (h : IsSlabFlow F a b φ) {x : T} (hx : F x ∈ Icc a b) {t : ℝ}
    (ht : t ∈ Icc (a - F x) (b - F x)) : F (φ t x) = F x + t := by
  have := (h.unitSpeed x).eq_add (s := 0) (by simpa [h.zero] using hx)
    (by simpa [h.zero] using ht)
  simpa [h.zero] using this

/-- A trajectory never crosses a level `c ∈ [a, b]` downwards: if `F(φ_t(x)) ≤ c` with `t ≥ 0`,
then `F(x) ≤ c`. -/
theorem le_of_apply_le (h : IsSlabFlow F a b φ) {x : T} {c t : ℝ} (hc : c ∈ Icc a b) (ht : 0 ≤ t)
    (hxt : F (φ t x) ≤ c) : F x ≤ c := by
  have := (h.unitSpeed x).le_of_le' hc ht hxt
  simpa [h.zero] using this

/-- A trajectory starting at or below `c` is at or below `c'` at time `c' - c`
(`a ≤ c ≤ c' ≤ b`): if it ever reaches the level `c`, it then rises at unit speed. -/
theorem apply_le_of_le (h : IsSlabFlow F a b φ) {x : T} {c c' : ℝ} (hac : a ≤ c) (hcc' : c ≤ c')
    (hc'b : c' ≤ b) (hx : F x ≤ c) : F (φ (c' - c) x) ≤ c' := by
  by_cases hT : F (φ (c' - c) x) ≤ c
  · linarith
  rw [not_le] at hT
  have hg := h.unitSpeed x
  obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc (sub_nonneg.2 hcc') hg.continuous.continuousOn
    (show c ∈ Icc (F (φ 0 x)) (F (φ (c' - c) x)) by rw [h.zero]; exact ⟨hx, hT.le⟩)
  have hgu' : F (φ u x) = c := hgu
  have := hg.eq_add_of_le (s := u) (t := c' - c) (by rw [hgu']; exact hac) hu.2
    (by rw [hgu']; linarith [hu.1])
  rw [this, hgu']
  linarith [hu.1]

/-- A trajectory which is at or below `c'` at time `c' - c` started at or below `c`
(`a ≤ c ≤ c' ≤ b`). -/
theorem le_of_apply_le' (h : IsSlabFlow F a b φ) {y : T} {c c' : ℝ} (hac : a ≤ c) (hcc' : c ≤ c')
    (hc'b : c' ≤ b) (hy : F y ≤ c') : F (φ (c - c') y) ≤ c := by
  have hcab : c ∈ Icc a b := ⟨hac, hcc'.trans hc'b⟩
  have hxy : φ (c' - c) (φ (c - c') y) = y := by
    rw [← h.add, show c' - c + (c - c') = 0 by ring, h.zero]
  rcases le_or_gt (F y) c with h1 | h1
  · exact h.le_of_apply_le hcab (sub_nonneg.2 hcc') (by rwa [hxy])
  · -- going back from `y` for the time `F(y) - c`, the trajectory reaches the level `c`
    have hFy : F y ∈ Icc a b := ⟨by linarith, by linarith⟩
    have h2 : F (φ (c - F y) y) = c := by
      have := h.apply_eq_add hFy (t := c - F y) ⟨by linarith, by linarith⟩
      linarith
    have h3 : φ (c' - F y) (φ (c - c') y) = φ (c - F y) y := by
      rw [← h.add]
      congr 1
      ring
    exact h.le_of_apply_le hcab (show 0 ≤ c' - F y by linarith) (by rw [h3, h2])

/-- **Theorem 3.1, first half** (Milnor p. 13: "Clearly this carries `M^a` diffeomorphically onto
`M^b`"), in the general form `φ_{c'-c}(M^c) = M^{c'}` for `a ≤ c ≤ c' ≤ b`. -/
theorem image_sublevel (h : IsSlabFlow F a b φ) {c c' : ℝ} (hac : a ≤ c) (hcc' : c ≤ c')
    (hc'b : c' ≤ b) : φ (c' - c) '' sublevel F c = sublevel F c' := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact h.apply_le_of_le hac hcc' hc'b hx
  · intro hy
    refine ⟨φ (c - c') y, h.le_of_apply_le' hac hcc' hc'b hy, ?_⟩
    rw [← h.add, show c' - c + (c - c') = 0 by ring, h.zero]

/-- Along Milnor's deformation, for `x` in the slab and `0 ≤ t ≤ 1`,
`F(r_t(x)) = F(x) + t (a - F(x))`, a value in `[a, F(x)]`. -/
theorem apply_deformation (h : IsSlabFlow F a b φ) {x : T} (hx : F x ∈ Icc a b) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : F (deformation φ F a t x) = F x + t * (a - F x) := by
  rw [deformation_of_ge hx.1]
  refine h.apply_eq_add hx ⟨?_, ?_⟩
  · nlinarith [ht.1, ht.2, hx.1]
  · nlinarith [ht.1, ht.2, hx.1, hx.2]

/-- `r_t` maps `M^b` into `M^b` for `0 ≤ t ≤ 1`. -/
theorem deformation_mem (h : IsSlabFlow F a b φ) {x : T} (hx : F x ≤ b) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : F (deformation φ F a t x) ≤ b := by
  rcases le_total (F x) a with h1 | h1
  · rwa [h.deformation_of_le h1]
  · rw [h.apply_deformation ⟨h1, hx⟩ ht]
    nlinarith [ht.1]

/-- `r_1` maps `M^b` into `M^a`. -/
theorem deformation_one_mem (h : IsSlabFlow F a b φ) {x : T} (hx : F x ≤ b) :
    F (deformation φ F a 1 x) ≤ a := by
  rcases le_total (F x) a with h1 | h1
  · rwa [h.deformation_of_le h1]
  · rw [h.apply_deformation ⟨h1, hx⟩ ⟨zero_le_one, le_rfl⟩]
    linarith

/-- Milnor's retraction `r_1 : M^b → M^b`, with values in `M^a`. -/
def retraction (h : IsSlabFlow F a b φ) : C(sublevel F b, sublevel F b) where
  toFun x := ⟨deformation φ F a 1 x, h.deformation_mem x.2 ⟨zero_le_one, le_rfl⟩⟩
  continuous_toFun := (h.continuous_deformation.comp
    (continuous_const.prodMk continuous_subtype_val)).subtype_mk _

theorem retraction_mem (h : IsSlabFlow F a b φ) (x : sublevel F b) :
    F (h.retraction x) ≤ a :=
  h.deformation_one_mem x.2

/-- **Theorem 3.1, second half**: Milnor's `r_t`, `0 ≤ t ≤ 1`, as a homotopy from the identity of
`M^b` to the retraction `r_1`, fixing `M^a` pointwise at all times. -/
def homotopyRel (h : IsSlabFlow F a b φ) :
    (ContinuousMap.id (sublevel F b)).HomotopyRel h.retraction {x | F x ≤ a} where
  toFun p := ⟨deformation φ F a p.1 p.2, h.deformation_mem p.2.2 p.1.2⟩
  continuous_toFun := (h.continuous_deformation.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left x := Subtype.ext (h.deformation_zero x)
  map_one_left _ := rfl
  prop' t _ hx := Subtype.ext (h.deformation_of_le hx t)

/-- **Theorem 3.1, second half**: `M^a` is a strong deformation retract of `M^b`. -/
theorem isStrongDeformationRetract (h : IsSlabFlow F a b φ) :
    IsStrongDeformationRetract ((↑) ⁻¹' sublevel F a : Set (sublevel F b)) :=
  ⟨h.retraction, h.retraction_mem, ⟨h.homotopyRel⟩⟩

/-- **Theorem 3.1**: the inclusion `M^a → M^b` is a homotopy equivalence (with homotopy inverse
Milnor's `r_1`). -/
theorem exists_homotopyEquiv (h : IsSlabFlow F a b φ) (hab : a ≤ b) :
    ∃ e : ContinuousMap.HomotopyEquiv (sublevel F a) (sublevel F b),
      ⇑e = Set.inclusion (sublevel_mono F hab) :=
  h.isStrongDeformationRetract.exists_homotopyEquiv (sublevel_mono F hab)

end IsSlabFlow

end Morse
