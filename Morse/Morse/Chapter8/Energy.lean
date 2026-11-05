import Morse.Chapter8.Piecewise
import Morse.Chapter7.Geodesic

/-!
Milnor, *Morse Theory*, §11 (pp. 67–69) and §12, p. 70, for a submanifold `N ⊆ ℝᴷ` with the
induced metric.

# The path space, its "tangent spaces", variations, and the energy of a path

## Milnor's text, paraphrased

* (p. 67) `Ω = Ω(M; p, q)` is the set of piecewise smooth paths `ω : [0, 1] → M` from `p` to `q`:
  smooth on each interval of some subdivision `0 = t₀ < ⋯ < t_k = 1`.  Its "tangent space"
  `TΩ_ω` is the vector space of piecewise smooth vector fields `W` along `ω` with `W(0) = 0`,
  `W(1) = 0`.  Milnor stresses that this is an analogy: no topology on `Ω` is used before §16.
* (p. 68) A *variation* of `ω` (keeping the end points fixed) is a map `ᾱ : (-ε, ε) → Ω` with
  `ᾱ(0) = ω` and a subdivision such that `α(u, t) = ᾱ(u)(t)` is smooth on each strip
  `(-ε, ε) × [t_{i-1}, t_i]`; then `α(u, 0) = p` and `α(u, 1) = q`.  Its *variation vector field*
  `W_t = ∂α/∂u (0, t)` is "clearly" in `TΩ_ω`.  Conversely, for `W ∈ TΩ_ω` the formula
  `ᾱ(u)(t) = exp_{ω(t)}(u W_t)` gives a variation with field `W` (Lemma 11.A of the exposition,
  `Morse.exists_variation`).  Neighbourhoods of `0` in `ℝⁿ` give `n`-parameter variations.
* (p. 70) The *energy* from `a` to `b` is `E_a^b(ω) = ∫ₐᵇ ‖dω/dt‖² dt`, `E = E_0^1`; with the
  length `L_a^b(ω) = ∫ₐᵇ ‖dω/dt‖ dt`, Schwarz's inequality gives `(L_a^b)² ≤ (b - a) E_a^b`, with
  equality if and only if the parameter is proportional to arc length.

## In the embedded setting

`N ⊆ V` is a slice submanifold (`Milnor.IsSliceSubmanifold`) with the induced metric, as in
Chapters 6 and 7.

* `Morse.pathSpace N p q` is `Ω(N; p, q)`: functions `c : ℝ → V` with `Morse.IsPiecewiseSmooth
  c 0 1` (the notion of Chapter 7: a finite set `B` of break points, `c` smooth on every closed
  interval whose interior misses `B`), `c(t) ∈ N` on `[0, 1]`, `c 0 = p`, `c 1 = q`.  The values
  off `[0, 1]` play no role.
* `Morse.prj hN x` is the tangent projection `P_x` at `x ∈ N` (and `0` off `N`); a vector `v` is
  tangent at `x ∈ N` iff `P_x v = v` (`Morse.prj_eq_self_iff`).
* `Morse.pathTangent hN ω` is `TΩ_ω`, a `Submodule ℝ (ℝ → V)`.
* `Morse.IsVariation N U α B`: a variation with parameters in an open set `U ∋ 0` of any normed
  space `P` (Milnor's `(-ε, ε)` for `P = ℝ`, a neighbourhood of `0` in `ℝ²` in §13), smooth on
  every closed strip `U × [s, t]` free of break points; it is a variation of the path `α 0`.
  `Morse.IsVariation.mem_pathSpace`: each `α u` is in `Ω`.  `Morse.IsVariation.comp`:
  reparametrizations `u ↦ α(φ(u))`, e.g. the slices `u₂ ↦ α(u₁, u₂)` of a 2-parameter variation.
* `Morse.varField α` is `W_t = ∂α/∂u (0, t)`; **"clearly `W ∈ TΩ_ω`"** is
  `Morse.IsVariation.varField_mem`.
* `Morse.energy c a b` is `E_a^b`; **Lemma 12.A of the exposition** (Schwarz's inequality with
  its equality case): `Morse.pathLength_sq_le_energy`, `Morse.pathLength_sq_eq_energy_iff`.
* `Morse.jump f t = f'(t⁺) - f'(t⁻)` (Milnor's `Δ_t`, p. 71), from one-sided derivatives.

## How `TΩ_ω` is formalized

`Ω` is given no topology or manifold structure, as in Milnor's §§11–15: `TΩ_ω` is *defined* as a
vector space of fields along `ω`, and is related to `Ω` only through variations: the variation
field of every variation lies in it (`Morse.IsVariation.varField_mem`), and every finite family
of its elements is the family of variation fields of one variation (`Morse.exists_variation`).
Derivatives of the energy "on `Ω`" are always derivatives of functions `u ↦ E(ᾱ(u))` of finitely
many real variables.  Elements of `TΩ_ω` are functions on `ℝ`; only their values on `[0, 1]`
matter for the first and second variations (`Morse.firstVariation_congr_field`,
`Morse.secondVariation_congr`).

## What Milnor leaves implicit

* **"Clearly `W ∈ TΩ_ω`"** (p. 68): `W` is smooth on each piece because `α` is smooth on the
  strip; it is continuous at a break point `t_i` because both adjacent strips compute the velocity
  of the same curve `u ↦ α(u, t_i)`; it is tangent because that curve lies in `N`; and it vanishes
  at `t = 0, 1` because the end points are fixed.
* **Smoothness on a closed strip** means one-sided derivatives in `t` along its edges (Milnor:
  smooth on `(-ε, ε) × [t_{i-1}, t_i]`).  That such one-sided derivatives of maps into `N` are
  tangent (needed for the jumps `Δ_t V` and `Δ_t DW/dt`) is
  `Morse.hasFDerivWithinAt_mem_tangentSubspace`, from a slice chart and the uniqueness of
  derivatives within a set.
* **Schwarz's inequality with equality case** for a speed that is only piecewise continuous:
  equality forces `‖dω/dt‖` to be constant off the break points (and at break points where `ω`
  is differentiable), not everywhere; proved with the variance identity
  `(b - a) ∫ (g - ḡ)² = (b - a) E - L²` and continuity on the closed pieces.
-/

open Set Filter Topology Function MeasureTheory Metric
open scoped ContDiff Manifold RealInnerProductSpace Interval

noncomputable section

namespace Morse

/-! ### Piecewise smooth functions: closure properties -/

namespace IsPiecewiseSmooth

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {a b : ℝ}

theorem of_contDiff {c : ℝ → E} (hc : ContDiff ℝ ∞ c) (hab : a ≤ b) : IsPiecewiseSmooth c a b :=
  of_contDiffOn hc.contDiffOn hab (subset_univ _)

theorem congr {c c' : ℝ → E} (h : IsPiecewiseSmooth c a b) (heq : EqOn c c' (Icc a b)) :
    IsPiecewiseSmooth c' a b := by
  obtain ⟨hab, hcont, B, hB⟩ := h
  exact ⟨hab, hcont.congr fun t ht => (heq ht).symm, B, fun s t hs hst ht hB' =>
    (hB s t hs hst ht hB').congr fun x hx => (heq ⟨hs.trans hx.1, hx.2.trans ht⟩).symm⟩

/-- A smooth function of two piecewise smooth functions is piecewise smooth (break points: the
union of the two sets). -/
theorem map₂ {Φ : E → F → G} (hΦ : ContDiff ℝ ∞ (fun p : E × F => Φ p.1 p.2)) {f : ℝ → E}
    {g : ℝ → F} (hf : IsPiecewiseSmooth f a b) (hg : IsPiecewiseSmooth g a b) :
    IsPiecewiseSmooth (fun t => Φ (f t) (g t)) a b := by
  classical
  obtain ⟨hab, hfc, B₁, hB₁⟩ := hf
  obtain ⟨-, hgc, B₂, hB₂⟩ := hg
  refine ⟨hab, hΦ.continuous.comp_continuousOn (hfc.prodMk hgc), B₁ ∪ B₂,
    fun s t hs hst ht hB => ?_⟩
  have h1 := hB₁ s t hs hst ht fun x hx => hB x (Finset.mem_union_left _ hx)
  have h2 := hB₂ s t hs hst ht fun x hx => hB x (Finset.mem_union_right _ hx)
  exact hΦ.comp_contDiffOn (h1.prodMk h2)

theorem add {f g : ℝ → E} (hf : IsPiecewiseSmooth f a b) (hg : IsPiecewiseSmooth g a b) :
    IsPiecewiseSmooth (fun t => f t + g t) a b :=
  map₂ (Φ := fun x y => x + y) (contDiff_fst.add contDiff_snd) hf hg

theorem smul {f : ℝ → ℝ} {g : ℝ → E} (hf : IsPiecewiseSmooth f a b)
    (hg : IsPiecewiseSmooth g a b) : IsPiecewiseSmooth (fun t => f t • g t) a b :=
  map₂ (Φ := fun x y => x • y) (contDiff_fst.smul contDiff_snd) hf hg

theorem clm_apply {A : ℝ → E →L[ℝ] F} {g : ℝ → E} (hA : IsPiecewiseSmooth A a b)
    (hg : IsPiecewiseSmooth g a b) : IsPiecewiseSmooth (fun t => A t (g t)) a b :=
  map₂ (Φ := fun L x => L x) (contDiff_fst.clm_apply contDiff_snd) hA hg

theorem const_smul (c : ℝ) {g : ℝ → E} (hg : IsPiecewiseSmooth g a b) :
    IsPiecewiseSmooth (fun t => c • g t) a b :=
  (of_contDiff (contDiff_const (c := c)) hg.1).smul hg

theorem comp_clm (L : E →L[ℝ] F) {g : ℝ → E} (hg : IsPiecewiseSmooth g a b) :
    IsPiecewiseSmooth (fun t => L (g t)) a b :=
  (of_contDiff (contDiff_const (c := L)) hg.1).clm_apply hg

/-- On a piece, the derivative within the piece is smooth and equals the derivative inside. -/
theorem derivWithin_piece {c : ℝ → E} {s t : ℝ} (hst : s < t) (hc : ContDiffOn ℝ ∞ c (Icc s t)) :
    ContDiffOn ℝ ∞ (derivWithin c (Icc s t)) (Icc s t) ∧
      EqOn (deriv c) (derivWithin c (Icc s t)) (Ioo s t) :=
  ⟨hc.derivWithin (uniqueDiffOn_Icc hst) (m := ∞) (by simp), fun x hx =>
    (derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)).symm⟩

end IsPiecewiseSmooth

/-! ### One-sided derivatives and jumps -/

section Jump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The jump of the derivative** `Δ_t f = f'(t⁺) - f'(t⁻)` at `t` (Milnor p. 71, for the
velocity), from the one-sided derivatives `derivWithin f (Ici t) t` and
`derivWithin f (Iic t) t`.  It vanishes where `f` is differentiable (`Morse.jump_eq_zero`). -/
def jump (f : ℝ → E) (t : ℝ) : E := derivWithin f (Ici t) t - derivWithin f (Iic t) t

theorem jump_eq_zero {f : ℝ → E} {t : ℝ} (hf : DifferentiableAt ℝ f t) : jump f t = 0 := by
  rw [jump, hf.derivWithin (uniqueDiffWithinAt_Ici t), hf.derivWithin (uniqueDiffWithinAt_Iic t),
    sub_self]

theorem jump_congr {f g : ℝ → E} {x : ℝ} (h : f =ᶠ[𝓝 x] g) : jump f x = jump g x := by
  rw [jump, jump, (h.filter_mono nhdsWithin_le_nhds).derivWithin_eq h.self_of_nhds,
    (h.filter_mono nhdsWithin_le_nhds).derivWithin_eq h.self_of_nhds]

/-- A function smooth on a piece `[s, t]` has the right derivative at `s` given by the derivative
within the piece. -/
theorem derivWithin_Ici_eq_of_piece {f : ℝ → E} {s t : ℝ} (hst : s < t)
    (hf : DifferentiableOn ℝ f (Icc s t)) :
    derivWithin f (Ici s) s = derivWithin f (Icc s t) s :=
  (((hf s (left_mem_Icc.2 hst.le)).hasDerivWithinAt).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE hst)).derivWithin (uniqueDiffWithinAt_Ici s)

theorem derivWithin_Iic_eq_of_piece {f : ℝ → E} {s t : ℝ} (hst : s < t)
    (hf : DifferentiableOn ℝ f (Icc s t)) :
    derivWithin f (Iic t) t = derivWithin f (Icc s t) t :=
  (((hf t (right_mem_Icc.2 hst.le)).hasDerivWithinAt).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsLE hst)).derivWithin (uniqueDiffWithinAt_Iic t)

/-- At a point where a piecewise smooth function is differentiable, its derivative is the derivative
within any piece containing the point. -/
theorem derivWithin_eq_deriv_of_piece {f : ℝ → E} {s t x : ℝ} (hst : s < t) (hx : x ∈ Icc s t)
    (hf : DifferentiableAt ℝ f x) : derivWithin f (Icc s t) x = deriv f x :=
  hf.derivWithin (uniqueDiffOn_Icc hst x hx)

end Jump

/-! ### The tangent projection along paths -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

open Classical in
/-- **The tangent projection at a point `x` of `V`**: `P_x = Morse.tanProj hN ⟨x, _⟩` (orthogonal
projection onto `T_xN`) for `x ∈ N`, and `0` off `N`.  Paths lie in `N` only for `t ∈ [0, 1]`, and
a total function of `x` is convenient in integrands. -/
def prj (x : V) : V →L[ℝ] V := if h : x ∈ N then tanProj hN ⟨x, h⟩ else 0

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem prj_of_mem {x : V} (hx : x ∈ N) : prj hN x = tanProj hN ⟨x, hx⟩ := by
  rw [prj, dif_pos hx]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem prj_of_notMem {x : V} (hx : x ∉ N) : prj hN x = 0 := by
  rw [prj, dif_neg hx]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem prj_mem {x : V} (hx : x ∈ N) (v : V) : prj hN x v ∈ tangentSubspace hN ⟨x, hx⟩ := by
  rw [prj_of_mem hN hx]; exact tanProj_apply_mem hN _ _

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem prj_eq_self_iff {x v : V} (hx : x ∈ N) :
    prj hN x v = v ↔ v ∈ tangentSubspace hN ⟨x, hx⟩ := by
  rw [prj_of_mem hN hx]; exact tanProj_eq_self_iff hN

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem prj_prj (x v : V) : prj hN x (prj hN x v) = prj hN x v := by
  by_cases hx : x ∈ N
  · rw [prj_of_mem hN hx]; exact tanProj_tanProj hN _ _
  · simp [prj_of_notMem hN hx]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem inner_prj_left (x v w : V) : ⟪prj hN x v, w⟫ = ⟪v, prj hN x w⟫ := by
  by_cases hx : x ∈ N
  · rw [prj_of_mem hN hx]; exact inner_tanProj_left hN _ _ _
  · simp [prj_of_notMem hN hx]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- For a tangent vector `v` (`P_x v = v`), `⟨v, P_x w⟩ = ⟨v, w⟩`. -/
theorem inner_prj_right_of_eq {x v : V} (hv : prj hN x v = v) (w : V) :
    ⟪v, prj hN x w⟫ = ⟪v, w⟫ := by
  rw [← inner_prj_left, hv]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem prj_eq_self_of_prj_eq {x v : V} (hv : prj hN x v = v) : prj hN x v = v := hv

/-- **Derivatives of maps into `N` are tangent to `N`**, also derivatives within a set (for
instance one-sided derivatives along the edge of a strip): if `g` maps `s` into `N` and has
derivative `g'` within `s` at `p ∈ s`, where `s` has unique derivatives, then
`g'(w) ∈ T_{g(p)}N` for every `w`. -/
theorem hasFDerivWithinAt_mem_tangentSubspace {E₀ : Type*} [NormedAddCommGroup E₀]
    [NormedSpace ℝ E₀] {g : E₀ → V} {g' : E₀ →L[ℝ] V} {s : Set E₀} {p : E₀}
    (hg : HasFDerivWithinAt g g' s p) (hs : UniqueDiffWithinAt ℝ s p) (hgs : ∀ x ∈ s, g x ∈ N)
    (hp : p ∈ s) (w : E₀) : g' w ∈ tangentSubspace hN ⟨g p, hgs p hp⟩ := by
  set q : N := ⟨g p, hgs p hp⟩
  set σ := sliceAt hN q
  have hq : g p ∈ σ.φ.source := mem_sliceAt_source hN q
  have hφ : HasFDerivAt σ.φ (fderiv ℝ σ.φ (g p)) (g p) :=
    (Milnor.Problems.sliceChart_differentiableAt σ hq).hasFDerivAt
  have h1 : HasFDerivWithinAt (fun x => (σ.φ (g x)).2)
      ((ContinuousLinearMap.snd ℝ Z W).comp ((fderiv ℝ σ.φ (g p)).comp g')) s p :=
    (ContinuousLinearMap.snd ℝ Z W).hasFDerivAt.comp_hasFDerivWithinAt p
      (hφ.comp_hasFDerivWithinAt p hg)
  have hsrc : ∀ᶠ x in 𝓝[s] p, g x ∈ σ.φ.source :=
    hg.continuousWithinAt.preimage_mem_nhdsWithin (σ.φ.open_source.mem_nhds hq)
  have h0 : (fun x => (σ.φ (g x)).2) =ᶠ[𝓝[s] p] fun _ => (0 : W) := by
    filter_upwards [hsrc, self_mem_nhdsWithin] with x h2 h1
    exact (σ.slice _ h2).1 (hgs x h1)
  have h2 : HasFDerivWithinAt (fun x => (σ.φ (g x)).2) (0 : E₀ →L[ℝ] W) s p :=
    (hasFDerivWithinAt_const (0 : W) p s).congr_of_eventuallyEq h0 ((σ.slice _ hq).1 (hgs p hp))
  have h3 := hs.eq h1 h2
  have h4 : (fderiv ℝ σ.φ (g p) (g' w)).2 = 0 := by
    have := DFunLike.congr_fun h3 w
    simpa using this
  exact (Milnor.Problems.sliceChart_mem_tangentSpace_iff hN σ (a := q) hq (g' w)).2 h4

theorem hasDerivWithinAt_mem_tangentSubspace {g : ℝ → V} {v : V} {s : Set ℝ} {t : ℝ}
    (hg : HasDerivWithinAt g v s t) (hs : UniqueDiffWithinAt ℝ s t) (hgs : ∀ x ∈ s, g x ∈ N)
    (ht : t ∈ s) : v ∈ tangentSubspace hN ⟨g t, hgs t ht⟩ := by
  have := hasFDerivWithinAt_mem_tangentSubspace hN hg.hasFDerivWithinAt hs hgs ht 1
  simpa using this

omit [FiniteDimensional ℝ W] in
/-- **The tangent projection along a smooth map into `N` is smooth**: `x ↦ P_{g(x)}` is `C^∞`
within `s` if `g` is and maps `s` into `N`.  (Near `g(p)`, `P` is the restriction of the smooth
ambient map `Morse.projRep`.) -/
theorem contDiffWithinAt_prj_comp {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    {g : E₀ → V} {s : Set E₀} {p : E₀} (hg : ContDiffWithinAt ℝ ∞ g s p) (hgs : ∀ x ∈ s, g x ∈ N)
    (hp : p ∈ s) : ContDiffWithinAt ℝ ∞ (fun x => prj hN (g x)) s p := by
  set q : N := ⟨g p, hgs p hp⟩
  set σ := sliceAt hN q
  have hq : g p ∈ σ.φ.source := mem_sliceAt_source hN q
  have h1 : ContDiffWithinAt ℝ ∞ (fun x => projRep σ (g x)) s p :=
    (contDiffAt_projRep σ (q := q) hq).comp_contDiffWithinAt p hg
  have hsrc : ∀ᶠ x in 𝓝[s] p, g x ∈ σ.φ.source :=
    hg.continuousWithinAt.preimage_mem_nhdsWithin (σ.φ.open_source.mem_nhds hq)
  refine h1.congr_of_eventuallyEq_of_mem ?_ hp
  filter_upwards [hsrc, self_mem_nhdsWithin] with x h2 h3
  rw [prj_of_mem hN (hgs x h3)]
  exact (projRep_eq hN σ (x := ⟨g x, hgs x h3⟩) h2).symm

omit [FiniteDimensional ℝ W] in
theorem ContDiffOn.prj_comp {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    {g : E₀ → V} {s : Set E₀} (hg : ContDiffOn ℝ ∞ g s) (hgs : ∀ x ∈ s, g x ∈ N) :
    ContDiffOn ℝ ∞ (fun x => prj hN (g x)) s :=
  fun p hp => contDiffWithinAt_prj_comp hN (hg p hp) hgs hp

omit [FiniteDimensional ℝ W] in
/-- Along a piecewise smooth path in `N`, `t ↦ P_{ω(t)}` is piecewise smooth. -/
theorem IsPiecewiseSmooth.prj_comp {c : ℝ → V} {a b : ℝ} (h : IsPiecewiseSmooth c a b)
    (hmem : ∀ t ∈ Icc a b, c t ∈ N) : IsPiecewiseSmooth (fun t => prj hN (c t)) a b := by
  obtain ⟨hab, -, B, hB⟩ := h
  have hpiece : ∀ s t, a ≤ s → s < t → t ≤ b → (∀ x ∈ B, x ∉ Ioo s t) →
      ContDiffOn ℝ ∞ (fun t => prj hN (c t)) (Icc s t) := fun s t hs hst ht hB' =>
    ContDiffOn.prj_comp hN (hB s t hs hst ht hB') fun x hx => hmem x ⟨hs.trans hx.1, hx.2.trans ht⟩
  exact ⟨hab, continuousOn_of_piecewise fun s t hs hst ht hB' =>
    (hpiece s t hs hst ht hB').continuousOn, B, hpiece⟩

/-! ### The path space and the energy -/

variable (N) in
/-- **Milnor's path space** `Ω(N; p, q)` (p. 67): the piecewise smooth paths `ω : [0, 1] → N` from
`p` to `q` (`Morse.IsPiecewiseSmooth`, Chapter 7).  A path is represented by a function `ℝ → V`;
its values off `[0, 1]` play no role. -/
def pathSpace (p q : V) : Set (ℝ → V) :=
  {c | IsPiecewiseSmooth c 0 1 ∧ (∀ t ∈ Icc (0 : ℝ) 1, c t ∈ N) ∧ c 0 = p ∧ c 1 = q}

/-- **The energy** of a path from `a` to `b` (Milnor p. 70): `E_a^b(ω) = ∫ₐᵇ ‖dω/dt‖² dt`.
Milnor's `E` is `energy ω 0 1`.  (The norm is the norm of `V`, i.e. the induced metric.) -/
def energy {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv c t‖ ^ 2

/-! ### Lemma 12.A: Schwarz's inequality `L² ≤ (b - a) E`, with its equality case -/

section Schwarz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ → E} {a b : ℝ}

theorem IsPiecewiseSmooth.intervalIntegrable_norm_deriv_sq (h : IsPiecewiseSmooth c a b) :
    IntervalIntegrable (fun t => ‖deriv c t‖ ^ 2) volume a b := by
  obtain ⟨hab, -, B, hB⟩ := h
  refine intervalIntegrable_of_piecewise (B := B) (lo := a) (hi := b)
    (fun s t hs hst ht hB' => ?_) le_rfl hab le_rfl
  obtain ⟨h1, h2⟩ := IsPiecewiseSmooth.derivWithin_piece hst (hB s t hs hst ht hB')
  exact ⟨fun x => ‖derivWithin c (Icc s t) x‖ ^ 2, h1.continuousOn.norm.pow 2,
    fun x hx => by simp only [h2 hx]⟩

/-- `∫ₐᵇ (‖c'‖ - k)² = E - 2kL + k²(b - a)`. -/
theorem integral_norm_deriv_sub_sq (h : IsPiecewiseSmooth c a b) (k : ℝ) :
    ∫ t in a..b, (‖deriv c t‖ - k) ^ 2 =
      energy c a b - 2 * k * pathLength c a b + k ^ 2 * (b - a) := by
  have h1 := h.intervalIntegrable_norm_deriv_sq
  have h2 : IntervalIntegrable (fun t => 2 * k * ‖deriv c t‖) volume a b :=
    h.isAdmissible.integrable.const_mul _
  have e : (fun t => (‖deriv c t‖ - k) ^ 2) =
      fun t => ‖deriv c t‖ ^ 2 - 2 * k * ‖deriv c t‖ + k ^ 2 := funext fun t => by ring
  rw [e, intervalIntegral.integral_add (h1.sub h2) intervalIntegrable_const,
    intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul, energy, pathLength]
  ring

/-- **Lemma 12.A** (Schwarz's inequality, Milnor p. 70): `L_a^b(ω)² ≤ (b - a) E_a^b(ω)`. -/
theorem pathLength_sq_le_energy (h : IsPiecewiseSmooth c a b) :
    pathLength c a b ^ 2 ≤ (b - a) * energy c a b := by
  rcases eq_or_lt_of_le h.1 with rfl | hlt
  · simp [pathLength]
  have hpos : 0 < b - a := sub_pos.2 hlt
  set k := pathLength c a b / (b - a)
  have hk : k * (b - a) = pathLength c a b := div_mul_cancel₀ _ hpos.ne'
  have h0 : 0 ≤ ∫ t in a..b, (‖deriv c t‖ - k) ^ 2 :=
    intervalIntegral.integral_nonneg hlt.le fun t _ => sq_nonneg _
  rw [integral_norm_deriv_sub_sq h k] at h0
  have : (b - a) * energy c a b - pathLength c a b ^ 2 =
      (b - a) * (energy c a b - 2 * k * pathLength c a b + k ^ 2 * (b - a)) := by
    rw [← hk]; ring
  nlinarith [mul_nonneg hpos.le h0]

/-- A path of constant speed `k` has energy `k² (b - a)`. -/
theorem energy_eq_of_norm_deriv (h : IsAdmissible c a b)
    {k : ℝ} (hk : ∀ t ∈ Ioo a b, DifferentiableAt ℝ c t → ‖deriv c t‖ = k) :
    energy c a b = k ^ 2 * (b - a) := by
  obtain ⟨C, hC, hd⟩ := h.countable
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ι a b → ‖deriv c t‖ ^ 2 = k ^ 2 := by
    have := ae_uIoc_of_forall_Ioo_diff h.le hC (fun t ht => hk t ht.1 (hd t ht))
    rw [ae_restrict_iff' measurableSet_uIoc] at this
    filter_upwards [this] with t ht ht'
    rw [ht ht']
  rw [energy, intervalIntegral.integral_congr_ae hae]
  simp [mul_comm]

/-- **The equality case of Lemma 12.A** (Milnor p. 70): `L² = (b - a) E` if and only if the speed
`‖dω/dt‖` is constant (at the points where `ω` is differentiable), i.e. the parameter is
proportional to arc length. -/
theorem pathLength_sq_eq_energy_iff (h : IsPiecewiseSmooth c a b) :
    pathLength c a b ^ 2 = (b - a) * energy c a b ↔
      ∃ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ c t → ‖deriv c t‖ = k := by
  constructor
  · intro heq
    rcases eq_or_lt_of_le h.1 with rfl | hlt
    · exact ⟨0, fun t ht => (lt_irrefl a (ht.1.trans ht.2)).elim⟩
    have hpos : 0 < b - a := sub_pos.2 hlt
    set k := pathLength c a b / (b - a)
    have hk : k * (b - a) = pathLength c a b := div_mul_cancel₀ _ hpos.ne'
    have h0 : ∫ t in a..b, (‖deriv c t‖ - k) ^ 2 = 0 := by
      rw [integral_norm_deriv_sub_sq h k]
      have : (b - a) * (energy c a b - 2 * k * pathLength c a b + k ^ 2 * (b - a)) = 0 := by
        rw [← hk] at heq ⊢; linear_combination -heq
      exact (mul_eq_zero.1 this).resolve_left hpos.ne'
    have hint : IntervalIntegrable (fun t => (‖deriv c t‖ - k) ^ 2) volume a b := by
      have e : (fun t => (‖deriv c t‖ - k) ^ 2) =
          fun t => ‖deriv c t‖ ^ 2 - 2 * k * ‖deriv c t‖ + k ^ 2 := funext fun t => by ring
      rw [e]
      exact (h.intervalIntegrable_norm_deriv_sq.sub
        (h.isAdmissible.integrable.const_mul _)).add intervalIntegrable_const
    have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hlt.le
      (.of_forall fun t => sq_nonneg _) hint).1 h0
    refine ⟨k, fun t ht hdt => ?_⟩
    obtain ⟨hab, -, B, hB⟩ := h
    obtain ⟨s, has, hst, hBs⟩ := exists_piece_left B ht.1
    have hpiece := hB s t has hst ht.2.le hBs
    obtain ⟨hd1, hd2⟩ := IsPiecewiseSmooth.derivWithin_piece hst hpiece
    set G : ℝ → ℝ := fun x => (‖derivWithin c (Icc s t) x‖ - k) ^ 2
    have hG : ContinuousOn G (Icc s t) := (hd1.continuousOn.norm.sub continuousOn_const).pow 2
    have hGae : G =ᵐ[volume.restrict (Icc s t)] 0 := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      have h1 : (fun t => (‖deriv c t‖ - k) ^ 2) =ᵐ[volume.restrict (Ioo s t)] 0 :=
        ae_restrict_of_ae_restrict_of_subset (s := Ioo s t) (t := Ioc a b)
          (fun x hx => (⟨has.trans_lt hx.1, hx.2.le.trans ht.2.le⟩ : x ∈ Ioc a b)) hae
      have h2 : G =ᵐ[volume.restrict (Ioo s t)] fun t => (‖deriv c t‖ - k) ^ 2 :=
        (ae_restrict_mem measurableSet_Ioo).mono fun x hx => by simp only [G, hd2 hx]
      exact h2.trans h1
    have hclos : Icc s t ⊆ closure (interior (Icc s t)) := by
      rw [interior_Icc, closure_Ioo hst.ne]
    have hGt := Measure.eqOn_of_ae_eq hGae hG continuousOn_const hclos
      (right_mem_Icc.2 hst.le)
    simp only [G, Pi.zero_apply, derivWithin_eq_deriv_of_piece hst (right_mem_Icc.2 hst.le) hdt,
      pow_eq_zero_iff two_ne_zero, sub_eq_zero] at hGt
    exact hGt
  · rintro ⟨k, hk⟩
    rw [pathLength_eq_of_norm_deriv h.isAdmissible hk,
      energy_eq_of_norm_deriv h.isAdmissible hk]
    ring

end Schwarz

/-! ### The "tangent space" `TΩ_ω` -/

/-- **Milnor's "tangent space" `TΩ_ω`** (p. 67), as a vector space of functions: the piecewise
smooth vector fields `W` along `ω` (tangent: `P_{ω(t)} W(t) = W(t)` for `t ∈ [0, 1]`) which vanish
at `t = 0` and `t = 1`.  `Ω` itself carries no manifold structure here, as in Milnor's §§11–15;
this vector space is a definition, and its relation with `Ω` is made through variations
(`Morse.IsVariation.varField_mem`, and Lemma 11.A, `Morse.exists_variation`). -/
def pathTangent (c : ℝ → V) : Submodule ℝ (ℝ → V) where
  carrier := {X | IsPiecewiseSmooth X 0 1 ∧ (∀ t ∈ Icc (0 : ℝ) 1, prj hN (c t) (X t) = X t) ∧
    X 0 = 0 ∧ X 1 = 0}
  add_mem' := by
    rintro X Y ⟨hX, hXt, hX0, hX1⟩ ⟨hY, hYt, hY0, hY1⟩
    refine ⟨hX.add hY, fun t ht => ?_, ?_, ?_⟩
    · simp only [Pi.add_apply, map_add, hXt t ht, hYt t ht]
    · simp [hX0, hY0]
    · simp [hX1, hY1]
  zero_mem' := ⟨IsPiecewiseSmooth.of_contDiff contDiff_const zero_le_one, fun t _ => by simp,
    rfl, rfl⟩
  smul_mem' := by
    rintro r X ⟨hX, hXt, hX0, hX1⟩
    exact ⟨hX.const_smul r, fun t ht => by simp [hXt t ht], by simp [hX0], by simp [hX1]⟩

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem mem_pathTangent {c X : ℝ → V} : X ∈ pathTangent hN c ↔ IsPiecewiseSmooth X 0 1 ∧
    (∀ t ∈ Icc (0 : ℝ) 1, prj hN (c t) (X t) = X t) ∧ X 0 = 0 ∧ X 1 = 0 := Iff.rfl

/-! ### Variations -/

section Variation

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

variable (N) in
/-- **A variation with fixed end points** (Milnor p. 68), with parameters in an open set `U ∋ 0`
of a normed space `P`: Milnor's `(-ε, ε)` for `P = ℝ`, a neighbourhood of `0 ∈ ℝ²` for the
2-parameter variations of §13.  `α u t ∈ N` for `u ∈ U`, `t ∈ [0, 1]`; the end points `α u 0`,
`α u 1` do not depend on `u`; and `(u, t) ↦ α u t` is smooth on each closed strip `U × [s, t]`
whose interior contains no point of the finite set `B` of break points (Milnor: smooth on each
strip `(-ε, ε) × [t_{i-1}, t_i]` of a subdivision).  It is a variation *of `α 0`*. -/
structure IsVariation (U : Set P) (α : P → ℝ → V) (B : Finset ℝ) : Prop where
  isOpen : IsOpen U
  zero_mem : (0 : P) ∈ U
  mem : ∀ u ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, α u t ∈ N
  start : ∀ u ∈ U, α u 0 = α 0 0
  finish : ∀ u ∈ U, α u 1 = α 0 1
  smooth : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) →
    ContDiffOn ℝ ∞ (fun p : P × ℝ => α p.1 p.2) (U ×ˢ Icc s t)

namespace IsVariation

variable {U : Set P} {α : P → ℝ → V} {B : Finset ℝ}

omit [FiniteDimensional ℝ V] in
/-- Each path `α u` of a variation is piecewise smooth. -/
theorem isPiecewiseSmooth (hα : IsVariation N U α B) {u : P} (hu : u ∈ U) :
    IsPiecewiseSmooth (α u) 0 1 := by
  have hpiece : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) →
      ContDiffOn ℝ ∞ (α u) (Icc s t) := fun s t hs hst ht hB =>
    (hα.smooth s t hs hst ht hB).comp (contDiffOn_const.prodMk contDiffOn_id)
      fun τ hτ => mk_mem_prod hu hτ
  exact ⟨zero_le_one, continuousOn_of_piecewise fun s t hs hst ht hB =>
    (hpiece s t hs hst ht hB).continuousOn, B, hpiece⟩

omit [FiniteDimensional ℝ V] in
/-- Each path `α u` of a variation lies in `Ω(N; p, q)`, `p = α 0 0`, `q = α 0 1`. -/
theorem mem_pathSpace (hα : IsVariation N U α B) {u : P} (hu : u ∈ U) :
    α u ∈ pathSpace N (α 0 0) (α 0 1) :=
  ⟨hα.isPiecewiseSmooth hu, hα.mem u hu, hα.start u hu, hα.finish u hu⟩

omit [FiniteDimensional ℝ V] in
/-- **Reparametrizing a variation**: for a smooth `φ : P' → P` with `φ 0 ∈ U`, `u ↦ α (φ u)` is a
variation (of the path `α (φ 0)`) with the same break points.  For instance `u₂ ↦ α (u₁, u₂)`, or
`u ↦ α (u • e)`. -/
theorem comp {P' : Type*} [NormedAddCommGroup P'] [NormedSpace ℝ P'] (hα : IsVariation N U α B)
    {φ : P' → P} (hφ : ContDiff ℝ ∞ φ) (h0 : φ 0 ∈ U) :
    IsVariation N (φ ⁻¹' U) (fun u => α (φ u)) B where
  isOpen := hα.isOpen.preimage hφ.continuous
  zero_mem := h0
  mem _ hu t ht := hα.mem _ hu t ht
  start _ hu := (hα.start _ hu).trans (hα.start _ h0).symm
  finish _ hu := (hα.finish _ hu).trans (hα.finish _ h0).symm
  smooth s t hs hst ht hB :=
    (hα.smooth s t hs hst ht hB).comp ((hφ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      fun _ hp => mk_mem_prod hp.1 hp.2

end IsVariation

/-- **The variation vector field** `W_t = ∂α/∂u (0, t)` of a 1-parameter variation
(Milnor p. 68). -/
def varField (α : ℝ → ℝ → V) (t : ℝ) : V := deriv (fun u => α u t) 0

omit [FiniteDimensional ℝ V] in
/-- Along the parameter, a 1-parameter variation is differentiable at every `t ∈ [0, 1]`. -/
theorem IsVariation.hasDerivAt_param {U : Set ℝ} {α : ℝ → ℝ → V} {B : Finset ℝ}
    (hα : IsVariation N U α B) {u t : ℝ} (hu : u ∈ U) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun v => α v t) (deriv (fun v => α v t) u) u := by
  obtain ⟨s, s', hs, hss', hs'1, hts, hB⟩ := exists_piece_mem B zero_lt_one ht
  have hF := hα.smooth s s' hs hss' hs'1 hB
  exact (hasDerivAt_pdU hα.isOpen (F := fun p : ℝ × ℝ => α p.1 p.2)
    (hF.differentiableOn (by simp)) hu hts).differentiableAt.hasDerivAt

/-- **The variation field is tangent**: `∂α/∂u (u, t) ∈ T_{α(u, t)}N`, the derivative of the curve
`v ↦ α(v, t)` in `N`. -/
theorem IsVariation.prj_varDeriv {U : Set ℝ} {α : ℝ → ℝ → V} {B : Finset ℝ}
    (hα : IsVariation N U α B) {u t : ℝ} (hu : u ∈ U) (ht : t ∈ Icc (0 : ℝ) 1) :
    prj hN (α u t) (deriv (fun v => α v t) u) = deriv (fun v => α v t) u := by
  have hmem : ∀ᶠ v in 𝓝 u, α v t ∈ N := by
    filter_upwards [hα.isOpen.mem_nhds hu] with v hv
    exact hα.mem v hv t ht
  exact (prj_eq_self_iff hN (hα.mem u hu t ht)).2
    (hasDerivAt_mem_tangentSubspace hN (hα.hasDerivAt_param hu ht) hmem)

/-- **"Clearly `W ∈ TΩ_ω`"** (Milnor p. 68): the variation field of a variation of `ω` is a
piecewise smooth vector field along `ω` vanishing at the ends.  It is continuous at the break
points because there both strips compute the velocity of the same curve `u ↦ α(u, t_i)`. -/
theorem IsVariation.varField_mem {U : Set ℝ} {α : ℝ → ℝ → V} {B : Finset ℝ}
    (hα : IsVariation N U α B) : varField α ∈ pathTangent hN (α 0) := by
  have hpiece : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) →
      ContDiffOn ℝ ∞ (varField α) (Icc s t) := by
    intro s t hs hst ht hB
    have hF := hα.smooth s t hs hst ht hB
    have h1 : ContDiffOn ℝ ∞ (fun τ => pdU (U ×ˢ Icc s t) (fun p : ℝ × ℝ => α p.1 p.2) (0, τ))
        (Icc s t) :=
      (contDiffOn_pdU hα.isOpen hst hF).comp (contDiffOn_const.prodMk contDiffOn_id)
        fun τ hτ => mk_mem_prod hα.zero_mem hτ
    refine h1.congr fun τ hτ => ?_
    exact deriv_eq_pdU hα.isOpen (F := fun p : ℝ × ℝ => α p.1 p.2)
      (hF.differentiableOn (by simp)) hα.zero_mem hτ
  refine ⟨⟨zero_le_one, continuousOn_of_piecewise fun s t hs hst ht hB =>
    (hpiece s t hs hst ht hB).continuousOn, B, hpiece⟩,
    fun t ht => hα.prj_varDeriv hN hα.zero_mem ht, ?_, ?_⟩
  · have hev : (fun u => α u 0) =ᶠ[𝓝 0] fun _ => α 0 0 := by
      filter_upwards [hα.isOpen.mem_nhds hα.zero_mem] with u hu
      exact hα.start u hu
    rw [varField, hev.deriv_eq, deriv_const]
  · have hev : (fun u => α u 1) =ᶠ[𝓝 0] fun _ => α 0 1 := by
      filter_upwards [hα.isOpen.mem_nhds hα.zero_mem] with u hu
      exact hα.finish u hu
    rw [varField, hev.deriv_eq, deriv_const]

end Variation

end Morse
