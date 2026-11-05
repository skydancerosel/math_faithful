import Mathlib
import Morse.Chapter2.Attaching

/-!
Milnor, *Morse Theory*, Appendix, pp. 149–150 (the telescope, the homotopy direct limit) and
pp. 152–153 (the truncations `X^n_Σ`).

# The telescope of a monotone sequence of subspaces

Milnor's Appendix starts from subspaces `X₀ ⊆ X₁ ⊆ X₂ ⊆ ⋯` of a space `X` and asks to what extent
the homotopy types of the `X_i` determine that of `X`. His tool (p. 149) is the infinite union
`X_Σ = X₀ × [0,1] ∪ X₁ × [1,2] ∪ X₂ × [2,3] ∪ ⋯`, to be topologized as a subset of `X × ℝ`
(`Morse.telescope`), with the projection `p(x, τ) = x` (`Morse.telescopeProj`). `X` is the
*homotopy direct limit* of `{X_i}` if `p` is a homotopy equivalence
(`Morse.IsHomotopyDirectLimit`).

## What Milnor's text leaves implicit

Milnor uses the following facts without comment; they are (T1)–(T3) of the exposition
(`Exposition/Appendix.md`, §1).

* **(T1) Upward closure.** For a monotone sequence, `(x, τ) ∈ X_Σ` iff `x ∈ X_n` for some
  integer `n ≤ τ` (`Morse.mem_telescope_iff`), so raising the second coordinate never leaves the
  telescope (`Morse.mem_telescope_of_le`).
* **(T2) Truncations.** The truncation `X^n_Σ = {(x, τ) ∈ X_Σ : τ ≤ n}` (Milnor, p. 152) deforms
  into `X_n × {n}` by raising `τ` to `n`, so `x ↦ (x, n)` is a homotopy equivalence
  `X_n → X^n_Σ` (`Morse.isHomotopyEquiv_truncIncl`). Milnor states this deformation retraction
  without proof (p. 152).
* **(T3) Pasting.** Every map Milnor writes down on `X_Σ` is given strip by strip, by formulas in
  `(x, n + t)`, `0 ≤ t ≤ 1`. Such a map is continuous when **every `X_n` is closed**: then the
  strips `X_n × [n, n+1]` are closed in `X_Σ` and form a locally finite family
  (`Morse.continuous_of_stripMap`). Milnor never states this hypothesis; without it his Case 1
  of Theorem A breaks down (the exposition gives an example where his map `g` is discontinuous).
  The maps and homotopies out of `X_Σ` are built with `Morse.telescopeLift`,
  `Morse.telescopeDesc` and `Morse.telescopeHomotopy`, from data on the strips that agree at the
  integer levels.
* **"Clearly sufficient"** (p. 150): if `X` and `Y` are homotopy direct limits and `f_Σ` is a
  homotopy equivalence, so is `f`, since `p_Y ∘ f_Σ = f ∘ p_X`
  (`Morse.IsHomotopyEquiv.of_telescopeMap`).
* **The mechanism of Example 1** (Lemma 2.1 of the exposition): if `f : X → [0, ∞)` is continuous
  and `f(x) ≥ i + 1` whenever `x ∉ X_i`, then the graph of `f` lies in `X_Σ`, it is a deformation
  retract of `X_Σ` (Milnor's "clearly a deformation retract": the straight-line homotopy in `τ`
  stays in `X_Σ` by (T1)), and `p` is a homotopy equivalence
  (`Morse.isHomotopyDirectLimit_of_level`). Neither closedness nor paracompactness is needed for
  this step.
* **Case 2 of Theorem A silently uses** that `X_Σ` is the homotopy direct limit of its truncations
  `{X^n_Σ}`: Milnor applies Case 1 to the sequence `{X^n_Σ}` and draws the conclusion for `G f_Σ`
  itself (p. 153). This is Lemma 2.1 with `f(x, τ) = τ + 1`
  (`Morse.isHomotopyDirectLimit_truncation`). Example 1 does not give it, since `X_Σ` need not be
  paracompact.

## Main definitions and results

* `Morse.IsHomotopyEquiv f`: `f` has a two-sided homotopy inverse; `Morse.restrictTo`.
* `Morse.telescope A` (Milnor's `X_Σ`), `Morse.stripMap`, `Morse.telescopeProj` (`p`),
  `Morse.telescopeMap` (`f_Σ`), `Morse.IsHomotopyDirectLimit`.
* `Morse.continuous_of_stripMap` (T3), `Morse.telescopeLift`, `Morse.telescopeDesc`,
  `Morse.telescopeHomotopy`, `Morse.telescope_ext`.
* `Morse.truncation` (`X^n_Σ`), `Morse.truncIncl`, `Morse.truncProj`,
  `Morse.isHomotopyEquiv_truncIncl`, `Morse.isHomotopyEquiv_truncProj` (T2).
* `Morse.isHomotopyDirectLimit_of_level` (Lemma 2.1), `Morse.isHomotopyDirectLimit_truncation`
  (Lemma 2.2), `Morse.IsHomotopyEquiv.of_telescopeMap`.
-/

open Set Filter Topology Function
open scoped unitInterval

noncomputable section

namespace Morse

/-! ### Homotopy equivalences as a property of a map -/

section IsHomotopyEquiv

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- **`f` is a homotopy equivalence**: it has a homotopy inverse `g`, with `g ∘ f ≃ id` and
`f ∘ g ≃ id` (Milnor, p. 12). Mathlib's `ContinuousMap.HomotopyEquiv` is the corresponding
structure. -/
def IsHomotopyEquiv (f : C(X, Y)) : Prop :=
  ∃ g : C(Y, X), (g.comp f).Homotopic (ContinuousMap.id X) ∧
    (f.comp g).Homotopic (ContinuousMap.id Y)

namespace IsHomotopyEquiv

theorem of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) : IsHomotopyEquiv e.toFun :=
  ⟨e.invFun, e.left_inv, e.right_inv⟩

theorem exists_homotopyEquiv {f : C(X, Y)} (hf : IsHomotopyEquiv f) :
    ∃ e : ContinuousMap.HomotopyEquiv X Y, e.toFun = f := by
  obtain ⟨g, h₁, h₂⟩ := hf
  exact ⟨⟨f, g, h₁, h₂⟩, rfl⟩

theorem nonempty {f : C(X, Y)} (hf : IsHomotopyEquiv f) :
    Nonempty (ContinuousMap.HomotopyEquiv X Y) :=
  let ⟨e, _⟩ := hf.exists_homotopyEquiv
  ⟨e⟩

protected theorem id : IsHomotopyEquiv (ContinuousMap.id X) :=
  ⟨ContinuousMap.id X, .refl _, .refl _⟩

theorem of_homeomorph (e : X ≃ₜ Y) : IsHomotopyEquiv (e : C(X, Y)) :=
  of_homotopyEquiv e.toHomotopyEquiv

theorem comp {f : C(X, Y)} {g : C(Y, Z)} (hf : IsHomotopyEquiv f) (hg : IsHomotopyEquiv g) :
    IsHomotopyEquiv (g.comp f) := by
  obtain ⟨e₁, rfl⟩ := hf.exists_homotopyEquiv
  obtain ⟨e₂, rfl⟩ := hg.exists_homotopyEquiv
  exact of_homotopyEquiv (e₁.trans e₂)

/-- A map homotopic to a homotopy equivalence is a homotopy equivalence. -/
theorem of_homotopic {f f' : C(X, Y)} (hf : IsHomotopyEquiv f) (h : f.Homotopic f') :
    IsHomotopyEquiv f' := by
  obtain ⟨g, h₁, h₂⟩ := hf
  exact ⟨g, ((ContinuousMap.Homotopic.refl g).comp h.symm).trans h₁,
    (h.symm.comp (ContinuousMap.Homotopic.refl g)).trans h₂⟩

/-- **Milnor's Assertion** (p. 22): a map with a left and a right homotopy inverse is a homotopy
equivalence (`Morse.homotopic_of_leftInv_rightInv`). -/
theorem of_leftInv_rightInv {f : C(X, Y)} {L R : C(Y, X)}
    (hL : (L.comp f).Homotopic (ContinuousMap.id X))
    (hR : (f.comp R).Homotopic (ContinuousMap.id Y)) : IsHomotopyEquiv f :=
  ⟨R, homotopic_of_leftInv_rightInv hL hR, hR⟩

/-- A homotopy inverse is a homotopy equivalence. -/
theorem of_inverse {f : C(X, Y)} {g : C(Y, X)} (h₁ : (g.comp f).Homotopic (ContinuousMap.id X))
    (h₂ : (f.comp g).Homotopic (ContinuousMap.id Y)) : IsHomotopyEquiv g :=
  ⟨f, h₂, h₁⟩

end IsHomotopyEquiv

/-- The restriction `s → t` of `f : X → Y`, when `f(s) ⊆ t`. -/
def restrictTo (f : C(X, Y)) {s : Set X} {t : Set Y} (h : MapsTo f s t) : C(s, t) :=
  ⟨h.restrict f s t, f.continuous.restrict h⟩

@[simp]
theorem coe_restrictTo_apply (f : C(X, Y)) {s : Set X} {t : Set Y} (h : MapsTo f s t) (x : s) :
    (restrictTo f h x : Y) = f x :=
  rfl

end IsHomotopyEquiv

/-! ### Clamping to `[0, 1]` -/

theorem clampI_coe (t : I) : clampI (t : ℝ) = t :=
  Subtype.ext (clampI_val t.2.1 t.2.2)

theorem clampI_eq {s : ℝ} {t : I} (h : s = t) : clampI s = t :=
  h ▸ clampI_coe t

theorem clampI_zero : clampI 0 = 0 :=
  clampI_coe 0

theorem clampI_one : clampI 1 = 1 :=
  clampI_coe 1

theorem clampI_of_le_zero {s : ℝ} (h : s ≤ 0) : clampI s = 0 :=
  Subtype.ext (by simp [clampI, Set.projIcc_of_le_left _ h])

theorem clampI_of_one_le {s : ℝ} (h : 1 ≤ s) : clampI s = 1 :=
  Subtype.ext (by simp [clampI, Set.projIcc_of_right_le _ h])

/-! ### The telescope -/

section Telescope

variable {X : Type*} {A : ℕ → Set X}

/-- **The telescope** (Milnor, p. 149): `X_Σ = X₀ × [0,1] ∪ X₁ × [1,2] ∪ X₂ × [2,3] ∪ ⋯`,
"topologized as a subset of `X × ℝ`". -/
def telescope (A : ℕ → Set X) : Set (X × ℝ) :=
  ⋃ n : ℕ, A n ×ˢ Icc (n : ℝ) (n + 1)

theorem mem_telescope {z : X × ℝ} :
    z ∈ telescope A ↔ ∃ n : ℕ, z.1 ∈ A n ∧ (n : ℝ) ≤ z.2 ∧ z.2 ≤ n + 1 := by
  simp only [telescope, mem_iUnion, mem_prod, mem_Icc]

theorem nonneg_of_mem_telescope {z : X × ℝ} (hz : z ∈ telescope A) : 0 ≤ z.2 := by
  obtain ⟨n, -, hn, -⟩ := mem_telescope.1 hz
  exact le_trans (Nat.cast_nonneg n) hn

/-- **(T1)** For a monotone sequence, `(x, τ) ∈ X_Σ` iff `x ∈ X_n` for some integer `n ≤ τ`. -/
theorem mem_telescope_iff (hA : Monotone A) {z : X × ℝ} :
    z ∈ telescope A ↔ ∃ n : ℕ, z.1 ∈ A n ∧ (n : ℝ) ≤ z.2 := by
  constructor
  · intro hz
    obtain ⟨n, hx, hn, -⟩ := mem_telescope.1 hz
    exact ⟨n, hx, hn⟩
  · rintro ⟨n, hx, hn⟩
    have h0 : 0 ≤ z.2 := le_trans (Nat.cast_nonneg n) hn
    exact mem_telescope.2 ⟨⌊z.2⌋₊, hA (Nat.le_floor hn) hx, Nat.floor_le h0,
      (Nat.lt_floor_add_one z.2).le⟩

/-- **(T1) Upward closure**: raising the second coordinate does not leave the telescope. -/
theorem mem_telescope_of_le (hA : Monotone A) {x : X} {τ τ' : ℝ} (hz : (x, τ) ∈ telescope A)
    (h : τ ≤ τ') : (x, τ') ∈ telescope A := by
  obtain ⟨n, hx, hn⟩ := (mem_telescope_iff hA).1 hz
  exact (mem_telescope_iff hA).2 ⟨n, hx, hn.trans h⟩

/-- A point of the telescope at level `τ < n + 1` lies over `X_n`. -/
theorem mem_of_mem_telescope (hA : Monotone A) {z : X × ℝ} (hz : z ∈ telescope A) {n : ℕ}
    (h : z.2 < n + 1) : z.1 ∈ A n := by
  obtain ⟨m, hx, hm⟩ := (mem_telescope_iff hA).1 hz
  have : (m : ℝ) < n + 1 := lt_of_le_of_lt hm h
  have : m < n + 1 := by exact_mod_cast this
  exact hA (by omega) hx

variable [TopologicalSpace X]

/-- The inclusion `X_n ⊆ X_{n+1}`. -/
def up (hA : Monotone A) (n : ℕ) : C(A n, A (n + 1)) :=
  ⟨Set.inclusion (hA (Nat.le_add_right n 1)), continuous_inclusion _⟩

@[simp]
theorem coe_up (hA : Monotone A) (n : ℕ) (x : A n) : (up hA n x : X) = x :=
  rfl

/-- **The strips.** The strip `X_n × [n, n+1]` of the telescope, parametrized by `X_n × [0, 1]`:
`(x, t) ↦ (x, n + t)`, Milnor's notation `(x, n + t)` (p. 151). -/
def stripMap (A : ℕ → Set X) (n : ℕ) : C(A n × I, telescope A) where
  toFun q := ⟨((q.1 : X), (n : ℝ) + q.2), mem_telescope.2
    ⟨n, q.1.2, le_add_of_nonneg_right q.2.2.1, by linarith [q.2.2.2]⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_const.add (continuous_subtype_val.comp continuous_snd))

@[simp]
theorem stripMap_apply_fst (n : ℕ) (q : A n × I) : (stripMap A n q : X × ℝ).1 = q.1 :=
  rfl

@[simp]
theorem stripMap_apply_snd (n : ℕ) (q : A n × I) : (stripMap A n q : X × ℝ).2 = n + q.2 :=
  rfl

theorem stripMap_congr {n : ℕ} {x x' : A n} {t t' : I} (hx : (x : X) = x') (ht : (t : ℝ) = t') :
    stripMap A n (x, t) = stripMap A n (x', t') := by
  rw [Subtype.ext hx, Subtype.ext ht]

/-- The top of the `n`-th strip is the bottom of the next one. -/
theorem stripMap_one (hA : Monotone A) (n : ℕ) (x : A n) :
    stripMap A n (x, 1) = stripMap A (n + 1) (up hA n x, 0) :=
  Subtype.ext (Prod.ext rfl (by simp))

/-- Every point of the telescope lies on a strip. -/
theorem exists_stripMap (z : telescope A) : ∃ n x t, stripMap A n (x, t) = z := by
  obtain ⟨n, hx, h₁, h₂⟩ := mem_telescope.1 z.2
  exact ⟨n, ⟨(z : X × ℝ).1, hx⟩, ⟨(z : X × ℝ).2 - n, by linarith, by linarith⟩,
    Subtype.ext (Prod.ext rfl (by simp))⟩

/-- A point of the telescope at an integer level `m` is the bottom point `(x, m + 0)` of the
`m`-th strip. -/
theorem eq_stripMap_of_level (hA : Monotone A) {z : telescope A} {m : ℕ}
    (h : (z : X × ℝ).2 = m) :
    z = stripMap A m (⟨(z : X × ℝ).1, mem_of_mem_telescope hA z.2 (by rw [h]; linarith)⟩, 0) :=
  Subtype.ext (Prod.ext rfl (by simp [h]))

/-- The canonical strip of a point: `n = ⌊τ⌋`, `t = τ - ⌊τ⌋ < 1`. -/
theorem exists_stripMap_lt_one (hA : Monotone A) (z : telescope A) :
    ∃ n x, ∃ t : I, (t : ℝ) < 1 ∧ stripMap A n (x, t) = z := by
  have h0 := nonneg_of_mem_telescope z.2
  have h1 := Nat.lt_floor_add_one (z : X × ℝ).2
  let t : I := ⟨(z : X × ℝ).2 - ⌊(z : X × ℝ).2⌋₊, sub_nonneg.2 (Nat.floor_le h0), by linarith⟩
  refine ⟨⌊(z : X × ℝ).2⌋₊, ⟨(z : X × ℝ).1, mem_of_mem_telescope hA z.2 h1⟩, t, ?_, ?_⟩
  · change (z : X × ℝ).2 - ⌊(z : X × ℝ).2⌋₊ < 1
    linarith
  · refine Subtype.ext (Prod.ext rfl ?_)
    change (⌊(z : X × ℝ).2⌋₊ : ℝ) + ((z : X × ℝ).2 - ⌊(z : X × ℝ).2⌋₊) = (z : X × ℝ).2
    ring

/-- Two functions on the telescope which agree on every strip are equal. -/
theorem telescope_ext {Z : Sort*} {f g : telescope A → Z}
    (h : ∀ n x t, f (stripMap A n (x, t)) = g (stripMap A n (x, t))) : f = g :=
  funext fun z => by
    obtain ⟨n, x, t, rfl⟩ := exists_stripMap z
    exact h n x t

theorem telescope_ext' {Z : Type*} [TopologicalSpace Z] {f g : C(telescope A, Z)}
    (h : ∀ n x t, f (stripMap A n (x, t)) = g (stripMap A n (x, t))) : f = g :=
  ContinuousMap.ext (congrFun (telescope_ext h))

/-! ### (T3) Pasting along the strips -/

/-- **(T3) Pasting** (used by Milnor for every map he defines on a telescope): if all `X_n` are
closed, a function on `P × X_Σ` is continuous as soon as it is continuous on each `P × (strip)`.
The strips are closed and locally finite (an open slab `|τ - τ₀| < 1` meets finitely many). -/
theorem continuous_of_stripMap (hAc : ∀ n, IsClosed (A n)) {P Z : Type*} [TopologicalSpace P]
    [TopologicalSpace Z] {F : P × telescope A → Z}
    (hF : ∀ n, Continuous fun q : P × (A n × I) => F (q.1, stripMap A n q.2)) : Continuous F := by
  have hτ : Continuous fun q : P × telescope A => (q.2 : X × ℝ).2 :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
  have hx : Continuous fun q : P × telescope A => (q.2 : X × ℝ).1 :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
  let S : ℕ → Set (P × telescope A) := fun n =>
    {q | (q.2 : X × ℝ).1 ∈ A n ∧ (n : ℝ) ≤ (q.2 : X × ℝ).2 ∧ (q.2 : X × ℝ).2 ≤ n + 1}
  refine LocallyFinite.continuous (f := S) ?_ ?_ ?_ ?_
  · intro q₀
    refine ⟨{q | |(q.2 : X × ℝ).2 - (q₀.2 : X × ℝ).2| < 1}, ?_, ?_⟩
    · refine (isOpen_lt (continuous_abs.comp (hτ.sub continuous_const))
        continuous_const).mem_nhds ?_
      simp
    · refine (Set.finite_lt_nat ⌈(q₀.2 : X × ℝ).2 + 1⌉₊).subset ?_
      rintro n ⟨q, ⟨-, hn, -⟩, hq⟩
      have hq' : |(q.2 : X × ℝ).2 - (q₀.2 : X × ℝ).2| < 1 := hq
      exact Nat.lt_ceil.2 (by linarith [(abs_lt.1 hq').2])
  · exact eq_univ_of_forall fun q => mem_iUnion.2 (mem_telescope.1 q.2.2)
  · intro n
    exact ((hAc n).preimage hx).inter ((isClosed_le continuous_const hτ).inter
      (isClosed_le hτ continuous_const))
  · intro n
    rw [continuousOn_iff_continuous_domRestrict]
    have hg : Continuous fun q : S n => ((q.1.1, (⟨(q.1.2 : X × ℝ).1, q.2.1⟩,
        ⟨(q.1.2 : X × ℝ).2 - n, by linarith [q.2.2.1], by linarith [q.2.2.2]⟩)) :
          P × (A n × I)) := by
      refine (continuous_fst.comp continuous_subtype_val).prodMk
        (Continuous.prodMk ?_ ?_)
      · exact (hx.comp continuous_subtype_val).subtype_mk _
      · exact ((hτ.comp continuous_subtype_val).sub continuous_const).subtype_mk _
    refine ((hF n).comp hg).congr fun q => ?_
    simp only [domRestrict_apply, Function.comp_apply]
    exact congrArg F (Prod.ext rfl (Subtype.ext (Prod.ext rfl (by simp))))

section Lift

variable {P Z : Type*} [TopologicalSpace P] [TopologicalSpace Z]

omit [TopologicalSpace X] in
theorem mem_floor (hA : Monotone A) (z : telescope A) : (z : X × ℝ).1 ∈ A ⌊(z : X × ℝ).2⌋₊ :=
  mem_of_mem_telescope hA z.2 (Nat.lt_floor_add_one _)

omit [TopologicalSpace X] in
theorem fract_mem (z : telescope A) : (z : X × ℝ).2 - ⌊(z : X × ℝ).2⌋₊ ∈ I :=
  ⟨sub_nonneg.2 (Nat.floor_le (nonneg_of_mem_telescope z.2)),
    by linarith [Nat.lt_floor_add_one (z : X × ℝ).2]⟩

/-- The function underlying `Morse.telescopeLift`: at `(x, τ)` it uses the strip `n = ⌊τ⌋`. -/
def telescopeLiftFun (hA : Monotone A) (Φ : ∀ n, C(P × (A n × I), Z)) (q : P × telescope A) : Z :=
  Φ ⌊(q.2 : X × ℝ).2⌋₊ (q.1, (⟨(q.2 : X × ℝ).1, mem_floor hA q.2⟩, ⟨_, fract_mem q.2⟩))

theorem apply_congr_level (Φ : ∀ n, C(P × (A n × I), Z)) {m n : ℕ} (h : m = n) (p : P) {x : X}
    (hm : x ∈ A m) (hn : x ∈ A n) {s s' : I} (hs : (s : ℝ) = s') :
    Φ m (p, (⟨x, hm⟩, s)) = Φ n (p, (⟨x, hn⟩, s')) := by
  subst h
  rw [Subtype.ext hs]

theorem telescopeLiftFun_eq (hA : Monotone A) (Φ : ∀ n, C(P × (A n × I), Z))
    {q : P × telescope A} {n : ℕ}
    (hn : ⌊(q.2 : X × ℝ).2⌋₊ = n) (hx : (q.2 : X × ℝ).1 ∈ A n) (ht : (q.2 : X × ℝ).2 - n ∈ I) :
    telescopeLiftFun hA Φ q = Φ n (q.1, (⟨_, hx⟩, ⟨_, ht⟩)) :=
  apply_congr_level Φ hn q.1 _ _ (by simp only [hn])

theorem telescopeLiftFun_stripMap (hA : Monotone A) (Φ : ∀ n, C(P × (A n × I), Z))
    (hΦ : ∀ n p (x : A n), Φ (n + 1) (p, (up hA n x, 0)) = Φ n (p, (x, 1))) (n : ℕ) (p : P)
    (x : A n) (t : I) : telescopeLiftFun hA Φ (p, stripMap A n (x, t)) = Φ n (p, (x, t)) := by
  rcases eq_or_lt_of_le t.2.2 with ht | ht
  · obtain rfl : t = 1 := Subtype.ext ht
    have hfl : ⌊((stripMap A n (x, 1) : telescope A) : X × ℝ).2⌋₊ = n + 1 := by
      rw [stripMap_apply_snd, Set.Icc.coe_one]
      exact_mod_cast Nat.floor_natCast (R := ℝ) (n + 1)
    rw [telescopeLiftFun_eq hA Φ hfl (hA (Nat.le_add_right n 1) x.2)
      (by simp only [stripMap_apply_snd, Set.Icc.coe_one]; push_cast; simp), ← hΦ n p x]
    exact apply_congr_level Φ rfl p _ _ (by simp)
  · have hfl : ⌊((stripMap A n (x, t) : telescope A) : X × ℝ).2⌋₊ = n := by
      rw [stripMap_apply_snd, Nat.floor_eq_iff (add_nonneg (Nat.cast_nonneg n) t.2.1)]
      constructor <;> linarith [t.2.1]
    rw [telescopeLiftFun_eq hA Φ hfl x.2 (by simp)]
    exact apply_congr_level Φ rfl p _ _ (by simp)

/-- **Maps out of `P × X_Σ`, given strip by strip** ((T3)): a family of continuous maps
`Φ_n : P × X_n × [0,1] → Z` which agree at the integer levels (`Φ_{n+1}(p, x, 0) = Φ_n(p, x, 1)`)
defines a continuous map `P × X_Σ → Z`, `(p, (x, n + t)) ↦ Φ_n(p, x, t)`. -/
def telescopeLift (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) (Φ : ∀ n, C(P × (A n × I), Z))
    (hΦ : ∀ n p (x : A n), Φ (n + 1) (p, (up hA n x, 0)) = Φ n (p, (x, 1))) :
    C(P × telescope A, Z) where
  toFun := telescopeLiftFun hA Φ
  continuous_toFun := continuous_of_stripMap hAc fun n => by
    have : (fun q : P × (A n × I) => telescopeLiftFun hA Φ (q.1, stripMap A n q.2)) = Φ n := by
      funext ⟨p, x, t⟩
      exact telescopeLiftFun_stripMap hA Φ hΦ n p x t
    rw [this]
    exact (Φ n).continuous

@[simp]
theorem telescopeLift_stripMap (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (Φ : ∀ n, C(P × (A n × I), Z))
    (hΦ : ∀ n p (x : A n), Φ (n + 1) (p, (up hA n x, 0)) = Φ n (p, (x, 1))) (n : ℕ) (p : P)
    (x : A n) (t : I) : telescopeLift hA hAc Φ hΦ (p, stripMap A n (x, t)) = Φ n (p, (x, t)) :=
  telescopeLiftFun_stripMap hA Φ hΦ n p x t

/-- **Maps out of `X_Σ`, given strip by strip** ((T3)). -/
def telescopeDesc (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) (Φ : ∀ n, C(A n × I, Z))
    (hΦ : ∀ n (x : A n), Φ (n + 1) (up hA n x, 0) = Φ n (x, 1)) : C(telescope A, Z) :=
  (telescopeLift hA hAc (P := Unit) (fun n => (Φ n).comp ContinuousMap.snd)
    fun n _ x => hΦ n x).comp ((ContinuousMap.const _ ()).prodMk (ContinuousMap.id _))

@[simp]
theorem telescopeDesc_stripMap (hA : Monotone A) (hAc : ∀ n, IsClosed (A n))
    (Φ : ∀ n, C(A n × I, Z))
    (hΦ : ∀ n (x : A n), Φ (n + 1) (up hA n x, 0) = Φ n (x, 1)) (n : ℕ) (x : A n) (t : I) :
    telescopeDesc hA hAc Φ hΦ (stripMap A n (x, t)) = Φ n (x, t) :=
  telescopeLiftFun_stripMap hA (fun n => (Φ n).comp ContinuousMap.snd) (fun n _ x => hΦ n x) n ()
    x t

/-- **Homotopies of maps out of `X_Σ`, given strip by strip** ((T3)). -/
def telescopeHomotopy (hA : Monotone A) (hAc : ∀ n, IsClosed (A n)) {f₀ f₁ : C(telescope A, Z)}
    (Φ : ∀ n, C(I × (A n × I), Z))
    (hΦ : ∀ n s (x : A n), Φ (n + 1) (s, (up hA n x, 0)) = Φ n (s, (x, 1)))
    (h₀ : ∀ n x t, Φ n (0, (x, t)) = f₀ (stripMap A n (x, t)))
    (h₁ : ∀ n x t, Φ n (1, (x, t)) = f₁ (stripMap A n (x, t))) : f₀.Homotopy f₁ where
  toContinuousMap := telescopeLift hA hAc Φ hΦ
  map_zero_left z := by
    obtain ⟨n, x, t, rfl⟩ := exists_stripMap z
    exact (telescopeLiftFun_stripMap hA Φ hΦ n 0 x t).trans (h₀ n x t)
  map_one_left z := by
    obtain ⟨n, x, t, rfl⟩ := exists_stripMap z
    exact (telescopeLiftFun_stripMap hA Φ hΦ n 1 x t).trans (h₁ n x t)

end Lift

/-! ### The projection, the induced maps, homotopy direct limits -/

/-- **The projection** `p : X_Σ → X`, `p(x, τ) = x` (Milnor, p. 149). -/
def telescopeProj (A : ℕ → Set X) : C(telescope A, X) :=
  ⟨fun z => (z : X × ℝ).1, continuous_fst.comp continuous_subtype_val⟩

@[simp]
theorem telescopeProj_apply (z : telescope A) : telescopeProj A z = (z : X × ℝ).1 :=
  rfl

/-- **Homotopy direct limit** (Milnor, p. 149): `X` is the homotopy direct limit of the sequence
`{X_i}` if the projection `p : X_Σ → X` is a homotopy equivalence. -/
def IsHomotopyDirectLimit (A : ℕ → Set X) : Prop :=
  IsHomotopyEquiv (telescopeProj A)

variable {Y : Type*} [TopologicalSpace Y] {B : ℕ → Set Y}

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem mem_telescope_map (f : X → Y) (hf : ∀ n, MapsTo f (A n) (B n)) {z : X × ℝ}
    (hz : z ∈ telescope A) : (f z.1, z.2) ∈ telescope B := by
  obtain ⟨n, hx, h₁, h₂⟩ := mem_telescope.1 hz
  exact mem_telescope.2 ⟨n, hf n hx, h₁, h₂⟩

/-- **The induced map of telescopes** `f_Σ(x, τ) = (f(x), τ)` (Milnor, p. 150), for `f` carrying
each `X_n` into `Y_n`. -/
def telescopeMap (f : C(X, Y)) (hf : ∀ n, MapsTo f (A n) (B n)) :
    C(telescope A, telescope B) where
  toFun z := ⟨(f (z : X × ℝ).1, (z : X × ℝ).2), mem_telescope_map f hf z.2⟩
  continuous_toFun := ((f.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val)).subtype_mk _

@[simp]
theorem telescopeMap_stripMap (f : C(X, Y)) (hf : ∀ n, MapsTo f (A n) (B n)) (n : ℕ) (x : A n)
    (t : I) : telescopeMap f hf (stripMap A n (x, t)) = stripMap B n (restrictTo f (hf n) x, t) :=
  rfl

theorem telescopeProj_comp_telescopeMap (f : C(X, Y)) (hf : ∀ n, MapsTo f (A n) (B n)) :
    (telescopeProj B).comp (telescopeMap f hf) = f.comp (telescopeProj A) :=
  rfl

/-- **Reducing Theorem A to `f_Σ`**, "clearly sufficient" according to Milnor (p. 150):
`p_Y ∘ f_Σ = f ∘ p_X`, so if `s` is a homotopy inverse of `p_X`, then
`f ≃ f ∘ p_X ∘ s = p_Y ∘ f_Σ ∘ s`, a composite of homotopy equivalences. -/
theorem IsHomotopyEquiv.of_telescopeMap {f : C(X, Y)} {hf : ∀ n, MapsTo f (A n) (B n)}
    (hX : IsHomotopyDirectLimit A) (hY : IsHomotopyDirectLimit B)
    (h : IsHomotopyEquiv (telescopeMap f hf)) : IsHomotopyEquiv f := by
  obtain ⟨s, hs₁, hs₂⟩ := hX
  have hs : IsHomotopyEquiv s := IsHomotopyEquiv.of_inverse hs₁ hs₂
  have h1 : IsHomotopyEquiv ((telescopeProj B).comp ((telescopeMap f hf).comp s)) :=
    (hs.comp h).comp hY
  refine h1.of_homotopic ?_
  have : (telescopeProj B).comp ((telescopeMap f hf).comp s) =
      f.comp ((telescopeProj A).comp s) := rfl
  rw [this]
  have h2 := (ContinuousMap.Homotopic.refl f).comp hs₂
  rwa [ContinuousMap.comp_id] at h2

/-! ### (T2) Truncations -/

/-- **The truncation** `X^n_Σ = {(x, τ) ∈ X_Σ : τ ≤ n} = X₀ × [0,1] ∪ ⋯ ∪ X_{n-1} × [n-1, n] ∪
X_n × [n]` (Milnor, p. 152). -/
def truncation (A : ℕ → Set X) (n : ℕ) : Set (telescope A) :=
  {z | (z : X × ℝ).2 ≤ n}

theorem isClosed_truncation (n : ℕ) : IsClosed (truncation A n) :=
  isClosed_le (continuous_snd.comp continuous_subtype_val) continuous_const

omit [TopologicalSpace X] in
theorem monotone_truncation : Monotone (truncation A) := fun m n h z hz => by
  change (z : X × ℝ).2 ≤ (n : ℝ)
  exact le_trans hz (by exact_mod_cast h)

/-- `X_n → X^n_Σ`, `x ↦ (x, n)`. -/
theorem stripMap_zero_mem_truncation (n : ℕ) (x : A n) :
    stripMap A n (x, 0) ∈ truncation A n := by
  change (n : ℝ) + ((0 : I) : ℝ) ≤ n
  simp

def truncIncl (A : ℕ → Set X) (n : ℕ) : C(A n, truncation A n) where
  toFun x := ⟨stripMap A n (x, 0), stripMap_zero_mem_truncation n x⟩
  continuous_toFun :=
    ((stripMap A n).continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _

@[simp]
theorem coe_truncIncl (n : ℕ) (x : A n) : (truncIncl A n x : telescope A) = stripMap A n (x, 0) :=
  rfl

/-- `X^n_Σ → X_n`, `(x, τ) ↦ x`. -/
def truncProj (hA : Monotone A) (n : ℕ) : C(truncation A n, A n) where
  toFun z := ⟨(z.1 : X × ℝ).1, mem_of_mem_telescope hA z.1.2 (lt_of_le_of_lt z.2 (by linarith))⟩
  continuous_toFun := (continuous_fst.comp (continuous_subtype_val.comp
    continuous_subtype_val)).subtype_mk _

@[simp]
theorem coe_truncProj (hA : Monotone A) (n : ℕ) (z : truncation A n) :
    (truncProj hA n z : X) = (z.1 : X × ℝ).1 :=
  rfl

theorem truncProj_comp_truncIncl (hA : Monotone A) (n : ℕ) :
    (truncProj hA n).comp (truncIncl A n) = ContinuousMap.id _ :=
  rfl

/-- **(T2)** `X^n_Σ` deforms into `X_n × {n}` by raising `τ` to `n`: `(x, τ) ↦ (x, τ + s(n - τ))`
stays in `X^n_Σ` by (T1). -/
theorem truncIncl_comp_truncProj (hA : Monotone A) (n : ℕ) :
    ((truncIncl A n).comp (truncProj hA n)).Homotopic (ContinuousMap.id _) := by
  have hmem : ∀ q : I × truncation A n,
      ((q.2.1 : X × ℝ).1, (1 - (q.1 : ℝ)) * n + q.1 * (q.2.1 : X × ℝ).2) ∈ telescope A := by
    intro q
    refine mem_telescope_of_le hA q.2.1.2 ?_
    have h1 : (q.2.1 : X × ℝ).2 ≤ n := q.2.2
    nlinarith [q.1.2.1, q.1.2.2]
  refine ⟨⟨⟨fun q => ⟨⟨_, hmem q⟩, ?_⟩, ?_⟩, ?_, ?_⟩⟩
  · have h1 : (q.2.1 : X × ℝ).2 ≤ n := q.2.2
    change (1 - (q.1 : ℝ)) * n + q.1 * (q.2.1 : X × ℝ).2 ≤ n
    nlinarith [q.1.2.1, q.1.2.2]
  · refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
    have hτ : Continuous fun q : I × truncation A n => (q.2.1 : X × ℝ).2 :=
      continuous_snd.comp (continuous_subtype_val.comp (continuous_subtype_val.comp
        continuous_snd))
    exact (continuous_fst.comp (continuous_subtype_val.comp (continuous_subtype_val.comp
      continuous_snd))).prodMk (((continuous_const.sub (continuous_subtype_val.comp
        continuous_fst)).mul continuous_const).add ((continuous_subtype_val.comp
          continuous_fst).mul hτ))
  · intro z
    exact Subtype.ext (Subtype.ext (Prod.ext rfl (by simp)))
  · intro z
    exact Subtype.ext (Subtype.ext (Prod.ext rfl (by simp)))

theorem isHomotopyEquiv_truncIncl (hA : Monotone A) (n : ℕ) :
    IsHomotopyEquiv (truncIncl A n) :=
  ⟨truncProj hA n, by rw [truncProj_comp_truncIncl], truncIncl_comp_truncProj hA n⟩

theorem isHomotopyEquiv_truncProj (hA : Monotone A) (n : ℕ) :
    IsHomotopyEquiv (truncProj hA n) :=
  IsHomotopyEquiv.of_inverse (by rw [truncProj_comp_truncIncl]) (truncIncl_comp_truncProj hA n)

/-- **Maps of telescope shape preserve the truncations.** If `F` carries the `n`-th strip to
levels `≤ n + 1` and its bottom `X_n × {n}` to levels `≤ n`, then it carries `X^m_Σ` to levels
`≤ m`, for every `m`. -/
theorem level_le_of_stripMap (hA : Monotone A) {Z : Type*} (ℓ : Z → ℝ) (F : telescope A → Z)
    (h₁ : ∀ n x t, ℓ (F (stripMap A n (x, t))) ≤ n + 1)
    (h₀ : ∀ n x, ℓ (F (stripMap A n (x, 0))) ≤ n) {m : ℕ} {z : telescope A}
    (hz : (z : X × ℝ).2 ≤ m) : ℓ (F z) ≤ m := by
  obtain ⟨n, x, t, ht1, rfl⟩ := exists_stripMap_lt_one hA z
  simp only [stripMap_apply_snd] at hz
  rcases eq_or_lt_of_le t.2.1 with ht0 | ht0
  · have : t = 0 := Subtype.ext ht0.symm
    subst this
    refine (h₀ n x).trans ?_
    simpa using hz
  · have hnm : (n : ℝ) < m := by linarith
    have hnm' : n + 1 ≤ m := by exact_mod_cast hnm
    refine (h₁ n x t).trans ?_
    exact_mod_cast hnm'

/-! ### Lemma 2.1 (the mechanism of Example 1) and Lemma 2.2 -/

/-- **Lemma 2.1 of the exposition** (the proof of Milnor's Example 1, p. 149). If
`f : X → [0, ∞)` is continuous and `f(x) ≥ i + 1` whenever `x ∉ X_i`, then `x ↦ (x, f(x))` maps
`X` into `X_Σ`, its image is a deformation retract of `X_Σ` ("clearly", says Milnor: the homotopy
`(x, τ) ↦ (x, (1 - s) f(x) + s τ)` stays in `X_Σ` by (T1)), and `X` is the homotopy direct limit
of `{X_i}`. -/
theorem isHomotopyDirectLimit_of_level (hA : Monotone A) (f : C(X, ℝ)) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ (n : ℕ) x, x ∉ A n → (n : ℝ) + 1 ≤ f x) : IsHomotopyDirectLimit A := by
  have hσ : ∀ x, (x, f x) ∈ telescope A := fun x => by
    refine (mem_telescope_iff hA).2 ⟨⌊f x⌋₊, ?_, Nat.floor_le (hf0 x)⟩
    by_contra h
    linarith [hf _ x h, Nat.lt_floor_add_one (f x)]
  let sec : C(X, telescope A) :=
    ⟨fun x => ⟨(x, f x), hσ x⟩, (continuous_id.prodMk f.continuous).subtype_mk _⟩
  have hmem : ∀ q : I × telescope A,
      ((q.2 : X × ℝ).1, (1 - (q.1 : ℝ)) * f (q.2 : X × ℝ).1 + q.1 * (q.2 : X × ℝ).2) ∈
        telescope A := by
    intro q
    rcases le_total (q.2 : X × ℝ).2 (f (q.2 : X × ℝ).1) with h | h
    · exact mem_telescope_of_le hA q.2.2 (by nlinarith [q.1.2.1, q.1.2.2])
    · exact mem_telescope_of_le hA (hσ _) (by nlinarith [q.1.2.1, q.1.2.2])
  refine ⟨sec, ⟨⟨⟨fun q => ⟨_, hmem q⟩, ?_⟩, ?_, ?_⟩⟩, ?_⟩
  · refine Continuous.subtype_mk ?_ _
    have hx : Continuous fun q : I × telescope A => (q.2 : X × ℝ).1 :=
      continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
    have hτ : Continuous fun q : I × telescope A => (q.2 : X × ℝ).2 :=
      continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
    exact hx.prodMk (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (f.continuous.comp hx)).add ((continuous_subtype_val.comp continuous_fst).mul hτ))
  · intro z
    exact Subtype.ext (Prod.ext rfl (by simp [sec]))
  · intro z
    exact Subtype.ext (Prod.ext rfl (by simp))
  · rfl

/-- **Lemma 2.2 of the exposition**: a telescope is the homotopy direct limit of its truncations
`{X^n_Σ}`, with no hypothesis on the `X_n`. This is the fact used without comment at the end of
Case 2 of Theorem A (Milnor, p. 153). Lemma 2.1 with `f(x, τ) = τ + 1`. -/
theorem isHomotopyDirectLimit_truncation : IsHomotopyDirectLimit (truncation A) :=
  isHomotopyDirectLimit_of_level monotone_truncation
    ⟨fun z => (z : X × ℝ).2 + 1, (continuous_snd.comp continuous_subtype_val).add continuous_const⟩
    (fun z => by
      have := nonneg_of_mem_telescope z.2
      simp only [ContinuousMap.coe_mk]
      linarith)
    (fun n z hz => by
      have hz' : (n : ℝ) < (z : X × ℝ).2 := not_le.1 hz
      simp only [ContinuousMap.coe_mk]
      linarith)

end Telescope

end Morse
