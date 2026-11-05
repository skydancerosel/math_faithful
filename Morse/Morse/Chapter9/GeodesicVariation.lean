import Morse.Chapter9.JacobiVariation

/-!
Milnor, *Morse Theory*, §14, p. 81: Lemma 14.4 (every Jacobi field is the variation field of a
variation through geodesics), with the smooth dependence of geodesics on their initial data over a
compact interval on which its proof rests, for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Lemma 14.4

## Milnor's proof, paraphrased (p. 81)

Choose a neighbourhood `U` of `γ(0)` in which any two points are joined by a unique minimal
geodesic depending differentiably on its end points, and `δ > 0` with `γ([0, δ]) ⊆ U`.  Moving the
end points along curves `a(u)`, `b(u)` with prescribed velocities at `u = 0` and joining them by
minimal geodesics gives a variation through geodesics whose variation field (a Jacobi field, by
Lemma 14.3) takes prescribed values at `0` and `δ`.  So `J ↦ (J(0), J(δ))` is onto, hence an
isomorphism (both spaces have dimension `2n`), and every Jacobi field along `γ|[0, δ]` arises.
(More generally, a Jacobi field is determined by its values at two non-conjugate points.)  Finally,
for small `u`, compactness of `[0, 1]` lets the geodesics `ᾱ(u)` be extended over all of `[0, 1]`.

## In the embedded setting

* `Morse.exists_smooth_ray`: **the local smooth geodesic flow, uniformly**: near any `x₁ ∈ N` and
  for speeds `< R`, the radial geodesics `t ↦ exp_y(tw)` exist for a uniform time `h` and are
  given there by a map `Φ(y, w, t)` smooth in all variables (Lemma 10.2 with its smooth dependence,
  rescaled by homogeneity).
* `Morse.exists_midpoint_ray`, `Morse.exists_initial_ray`: **a geodesic segment extends past its
  end points**: `γ : [0, 1] → N` is the radial geodesic `t ↦ exp_{γ(0)}(t γ'(0))`, a geodesic on
  an open interval containing `[0, 1]` (first from the midpoint, continuing past both ends by the
  local flow at `γ(0)` and `γ(1)`).
* `Morse.raysGood_of_isGeodesicOn`: **smooth dependence on the initial data over a compact
  interval**: for a smooth curve `u ↦ (c(u), w(u))` in `TN`, if the radial geodesic of
  `(c(0), w(0))` exists on an open interval containing `[0, B]`, then for small `u` those of
  `(c(u), w(u))` exist on a common such interval and `(u, t) ↦ exp_{c(u)}(t w(u))` is smooth there
  (`Morse.RaysGood`).  The geodesics are continued step by step, a step being a composition with
  the local smooth flow (`Morse.RaysGood.step`); a supremum argument replaces a finite cover.
* `Morse.lemma_14_4`: **Lemma 14.4**: for every Jacobi field `J` along a geodesic `γ` there is a
  smooth `α : (−ε, ε) × [0, 1] → N` with `α(0, ·) = γ`, each `α(u, ·)` a geodesic, and
  `∂α/∂u (0, t) = J(t)` on `[0, 1]`: the converse of Lemma 14.3 (`Morse.lemma_14_3`).
* `Morse.jacEvalEnds_bijective_of_not_isConjugate`: the parenthetical remark, with the dimension
  count: if `a ≠ b` are not conjugate, `J ↦ (J(a), J(b))` is an isomorphism
  `𝒥(γ) ≅ T_{γ(a)}N × T_{γ(b)}N`.

## The proof here differs from Milnor's

The variation is built from initial data instead of end points: `α(u, t) = exp_{c(u)}(t w(u))`
with `c(u) = exp_{γ(0)}(u J(0))` and `w(u) = P_{c(u)}(γ'(0) + u DJ/dt(0))` (`P_x` the orthogonal
projection onto `T_xN`).  Its variation field `W` is a Jacobi field (Lemma 14.3) with
`W(0) = c'(0) = J(0)` and, by the symmetry of the mixed partials, `DW/dt(0) = Dw/du(0) = DJ/dt(0)`
(using `P P' P = 0`); so `W = J` by uniqueness.  This replaces the end-point data of Theorem 10.4,
the restriction to `[0, δ]` and the dimension count; the extension over `[0, 1]` is the same
compactness step.

## What Milnor leaves implicit

* The compactness step ("`ᾱ(u)` can be extended to `[0, 1]`") is the smooth dependence of the
  solutions of an ODE on their initial data over a compact time interval (the geodesic equation,
  in charts changing along `γ`), with the openness of the domain of `exp`; neither is among the
  statements of §10.  Here it is `Morse.raysGood_of_isGeodesicOn`.
* That the extended variation still has `J` as its variation field: its variation field is a
  Jacobi field along all of `γ` (Lemma 14.3) that agrees with `J` on `[0, δ]`, hence everywhere by
  uniqueness.
* For `α(0, ·) = γ` on `[0, δ]`, `γ|[0, δ]` must itself be the minimal geodesic from `γ(0)` to
  `γ(δ)`; `γ([0, δ]) ⊆ U` alone does not give this (a geodesic inside `U` need not be minimal).
  One needs `δ` small, e.g. the length of `γ|[0, δ]` below the `ε` of Theorem 10.4.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### The local smooth flow -/

variable (hN) in
/-- **The local smooth geodesic flow, uniformly** (Lemma 10.2, rescaled): near `x₁ ∈ N`, for speeds
`< R`, the radial geodesics `t ↦ exp_y(tw)` exist on a uniform interval `(−h, h)` and are there
`Φ(y, w, t)`, `Φ` smooth. -/
theorem exists_smooth_ray (x₁ : N) {R : ℝ} (hR : 0 < R) :
    ∃ U : Set V, IsOpen U ∧ (x₁ : V) ∈ U ∧ ∃ h > 0, ∃ Φ : V × V × ℝ → V,
      ContDiffOn ℝ ∞ Φ (U ×ˢ ball (0 : V) R ×ˢ Ioo (-h) h) ∧
      ∀ y : N, (y : V) ∈ U → ∀ w ∈ tangentSubspace hN y, ‖w‖ < R →
        IsGeodesicOn hN (fun t => exp hN y (t • w)) (Ioo (-h) h) ∧
        ∀ t ∈ Ioo (-h) h, exp hN y (t • w) = Φ (y, w, t) := by
  obtain ⟨U, hU, hx₁, ε, hε, Γ, hΓ, hgeo⟩ := lemma_10_2 hN x₁
  set c := ε / R with hcdef
  have hc : 0 < c := div_pos hε hR
  have hcR : c * R = ε := by rw [hcdef]; field_simp
  have hball : ∀ w : V, ‖w‖ < R → ‖c • w‖ < ε := fun w hw => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, ← hcR]
    exact mul_lt_mul_of_pos_left hw hc
  have hdiv : ∀ t ∈ Ioo (-(2 * c)) (2 * c), t / c ∈ Ioo (-2 : ℝ) 2 := fun t ht => by
    constructor
    · rw [lt_div_iff₀ hc]; linarith [ht.1]
    · rw [div_lt_iff₀ hc]; linarith [ht.2]
  refine ⟨U, hU, hx₁, 2 * c, by positivity, fun z => Γ (z.1, c • z.2.1, z.2.2 / c), ?_,
    fun y hy w hw hwR => ?_⟩
  · refine hΓ.comp (by fun_prop : ContDiff ℝ ∞
      (fun z : V × V × ℝ => (z.1, c • z.2.1, z.2.2 / c))).contDiffOn ?_
    rintro ⟨y, w, t⟩ ⟨hy, hw, ht⟩
    exact ⟨hy, mem_ball_zero_iff.2 (hball w (mem_ball_zero_iff.1 hw)), hdiv t ht⟩
  · have hcw : c • w ∈ tangentSubspace hN y := Submodule.smul_mem _ c hw
    obtain ⟨hg, hg0, hgd, -⟩ := hgeo y hy (c • w) hcw (hball w hwR)
    have hray : ∀ t ∈ Ioo (-(2 * c)) (2 * c), exp hN y (t • w) = Γ (y, c • w, t / c) := by
      intro t ht
      have := hg.exp_smul_eq isPreconnected_Ioo ⟨by norm_num, by norm_num⟩ (hdiv t ht)
      rw [hg0, hgd.deriv, smul_smul, div_mul_cancel₀ t hc.ne'] at this
      exact this
    refine ⟨?_, hray⟩
    have hcomp := hg.comp_mul_add (1 / c) 0
    have hsub : Ioo (-(2 * c)) (2 * c) ⊆ (fun t => 1 / c * t + 0) ⁻¹' Ioo (-2) 2 := fun t ht => by
      have := hdiv t ht
      simpa [div_eq_inv_mul] using this
    refine (hcomp.mono isOpen_Ioo hsub).congr fun t ht => ?_
    change Γ (y, c • w, 1 / c * t + 0) = exp hN y (t • w)
    rw [hray t ht]
    congr 3
    ring

/-! ### Extending a geodesic segment -/

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The geodesic flow at time `s`: the position and velocity of the radial geodesic. -/
theorem geoFlow_eq_exp (y w : V) (s : ℝ) :
    geoFlow hN (y, w) s = (exp hN y (s • w), deriv (fun t => exp hN y (t • w)) s) := rfl

/-- **A geodesic segment extends past its end points**: an unbroken geodesic `γ` on `[0, 1]` is
the radial geodesic from its midpoint, `t ↦ exp_{γ(1/2)}((t − 1/2) γ'(1/2))`, which is a geodesic
on an open interval containing `[0, 1]`. -/
theorem exists_midpoint_ray {γ : ℝ → V} (hc : IsSmoothCurveIn hN γ)
    (hgeo : IsGeodesicOn hN γ (Ioo 0 1)) :
    ∃ η > 0, IsGeodesicOn hN (fun t => exp hN (γ (1 / 2)) (t • deriv γ (1 / 2)))
        (Ioo (-(1 / 2) - η) (1 / 2 + η)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, exp hN (γ (1 / 2)) ((t - 1 / 2) • deriv γ (1 / 2)) = γ t := by
  set x := γ (1 / 2)
  set v := deriv γ (1 / 2)
  set ray : ℝ → V := fun t => exp hN x (t • v)
  have hmid : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hxN : x ∈ N := hgeo.mem _ hmid
  have hvT : v ∈ tangentSubspace hN ⟨x, hxN⟩ := hgeo.deriv_mem hmid
  -- `γ(· + 1/2)` is a geodesic on `(−1/2, 1/2)`, equal to the ray there
  set g : ℝ → V := fun t => γ (t + 1 / 2)
  have hg : IsGeodesicOn hN g (Ioo (-(1 / 2)) (1 / 2)) := by
    have := hgeo.comp_mul_add 1 (1 / 2)
    have hpre : (fun t : ℝ => 1 * t + 1 / 2) ⁻¹' Ioo 0 1 = Ioo (-(1 / 2)) (1 / 2) := by
      ext t; simp only [mem_preimage, mem_Ioo, one_mul]; constructor <;> intro h <;>
        constructor <;> linarith [h.1, h.2]
    rw [hpre] at this
    simpa [g] using this
  have hg0 : g 0 = x := by simp [g, x]
  have hg0' : deriv g 0 = v := by
    have : deriv g 0 = deriv γ (0 + 1 / 2) := deriv_comp_add_const (f := γ) (a := 1 / 2) (x := 0)
    rw [this, zero_add]
  have hI0 : (0 : ℝ) ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by norm_num, by norm_num⟩
  have hrayg : EqOn ray g (Ioo (-(1 / 2)) (1 / 2)) := by
    have := hg.eqOn_exp_smul isPreconnected_Ioo hI0
    rwa [hg0, hg0'] at this
  have hray0 : IsGeodesicOn hN ray (Ioo (-(1 / 2)) (1 / 2)) := hg.congr hrayg.symm
  -- the ray continues past each end point by the local flow there
  have hend : ∀ e ∈ ({0, 1} : Set ℝ), ∃ h > 0, ∃ s ∈ Ioo (-(1 / 2) : ℝ) (1 / 2),
      |s - (e - 1 / 2)| < h / 2 ∧ IsGeodesicOn hN
        (fun t => exp hN (geoFlow hN (x, v) s).1 (t • (geoFlow hN (x, v) s).2)) (Ioo (-h) h) := by
    intro e he
    have he01 : e ∈ Icc (0 : ℝ) 1 := by
      rcases he with rfl | rfl
      · exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨zero_le_one, le_rfl⟩
    set R := ‖velAlong γ e‖ + 1
    obtain ⟨U, hU, heU, h, hh, Φ, -, hloc⟩ := exists_smooth_ray hN ⟨γ e, hc.mem e he01⟩
      (R := R) (by positivity)
    -- times `t ∈ (0, 1)` close to `e` with `γ(t) ∈ U` and `‖γ'(t)‖ < R`
    have hcont := (hc.contDiffOn.continuousOn e he01).prodMk
      (hc.contDiffOn_velAlong.continuousOn e he01)
    have hev : ∀ᶠ t in 𝓝[Icc 0 1] e, γ t ∈ U ∧ ‖velAlong γ t‖ < R := by
      have h1 := hcont.eventually ((hU.prod (isOpen_lt continuous_norm continuous_const)).mem_nhds
        (show (γ e, velAlong γ e) ∈ U ×ˢ {w : V | ‖w‖ < R} from ⟨heU, by simp [R]⟩))
      exact h1
    have hsub : Ioo (0 : ℝ) 1 ∩ Ioo (e - h / 2) (e + h / 2) ∈ 𝓝[Ioo 0 1] e :=
      inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith)
        (by linarith)))
    have : (𝓝[Ioo (0 : ℝ) 1] e).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo zero_ne_one]; exact he01
    obtain ⟨t, ⟨htU, htR⟩, ht01, hth⟩ := ((hev.filter_mono (nhdsWithin_mono _
      Ioo_subset_Icc_self)).and hsub).exists
    refine ⟨h, hh, t - 1 / 2, ⟨by linarith [ht01.1], by linarith [ht01.2]⟩, ?_, ?_⟩
    · rw [abs_lt]; constructor <;> linarith [hth.1, hth.2]
    -- the flow at time `t − 1/2` is `(γ t, γ' t)`
    have hs : t - 1 / 2 ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by linarith [ht01.1], by linarith [ht01.2]⟩
    have hflow : geoFlow hN (x, v) (t - 1 / 2) = (γ t, velAlong γ t) := by
      have hev' : ray =ᶠ[𝓝 (t - 1 / 2)] g := eventually_of_mem (isOpen_Ioo.mem_nhds hs) hrayg
      have e1 : ray (t - 1 / 2) = γ t := by rw [hrayg hs]; simp [g]
      have e2 : deriv ray (t - 1 / 2) = velAlong γ t := by
        rw [hev'.deriv_eq, hc.velAlong_eq ht01]
        have := deriv_comp_add_const (f := γ) (a := 1 / 2) (x := t - 1 / 2)
        rw [sub_add_cancel] at this
        exact this
      exact Prod.ext e1 e2
    rw [hflow]
    have htN : γ t ∈ N := hc.mem t (Ioo_subset_Icc_self ht01)
    exact (hloc ⟨γ t, htN⟩ htU (velAlong γ t)
      ((prj_eq_self_iff hN htN).1 (hc.velAlong_mem (Ioo_subset_Icc_self ht01))) htR).1
  obtain ⟨h₁, hh₁, s₁, hs₁, hd₁, hJ₁⟩ := hend 1 (by simp)
  obtain ⟨h₀, hh₀, s₀, hs₀, hd₀, hJ₀⟩ := hend 0 (by simp)
  -- glue at the right end, then at the left end
  obtain ⟨hR1, -⟩ := isGeodesicOn_exp_smul_union hxN hvT hray0 isPreconnected_Ioo hI0 hs₁ hJ₁
    isPreconnected_Ioo ⟨by linarith, hh₁⟩
  set I₁ := Ioo (-(1 / 2) : ℝ) (1 / 2) ∪ (fun t => t - s₁) ⁻¹' Ioo (-h₁) h₁
  have hI₁c : IsPreconnected I₁ := by
    refine IsPreconnected.union s₁ hs₁ ?_ isPreconnected_Ioo ?_
    · simp only [mem_preimage, sub_self, mem_Ioo]; exact ⟨by linarith, hh₁⟩
    · have : (fun t => t - s₁) ⁻¹' Ioo (-h₁) h₁ = Ioo (s₁ - h₁) (s₁ + h₁) := by
        ext t; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;>
          constructor <;> linarith [h.1, h.2]
      rw [this]; exact isPreconnected_Ioo
  have hs₀I₁ : s₀ ∈ I₁ := Or.inl hs₀
  have hflow₀ : geoFlow hN (x, v) s₀ = geoFlow hN (x, v) s₀ := rfl
  obtain ⟨hR2, -⟩ := isGeodesicOn_exp_smul_union hxN hvT hR1 hI₁c (Or.inl hI0) hs₀I₁ hJ₀
    isPreconnected_Ioo ⟨by linarith, hh₀⟩
  set η := min (h₁ / 2) (h₀ / 2) / 2
  have hη : 0 < η := by positivity
  have hη0 : η ≤ h₀ / 4 := by
    have := min_le_right (h₁ / 2) (h₀ / 2); simp only [η]; linarith
  have hη1 : η ≤ h₁ / 4 := by
    have := min_le_left (h₁ / 2) (h₀ / 2); simp only [η]; linarith
  have hcover : Ioo (-(1 / 2) - η) (1 / 2 + η) ⊆
      (Ioo (-(1 / 2) : ℝ) (1 / 2) ∪ (fun t => t - s₁) ⁻¹' Ioo (-h₁) h₁) ∪
        (fun t => t - s₀) ⁻¹' Ioo (-h₀) h₀ := by
    intro t ht
    have hd₁' := abs_lt.1 hd₁
    have hd₀' := abs_lt.1 hd₀
    rcases le_or_gt t (-(1 / 2) + h₀ / 4) with htl | htl
    · refine Or.inr ?_
      simp only [mem_preimage, mem_Ioo]
      constructor <;> linarith [ht.1, ht.2]
    rcases le_or_gt (1 / 2 - h₁ / 4) t with htr | htr
    · refine Or.inl (Or.inr ?_)
      simp only [mem_preimage, mem_Ioo]
      constructor <;> linarith [ht.1, ht.2]
    · exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
  refine ⟨η, hη, hR2.mono isOpen_Ioo hcover, fun t ht => ?_⟩
  -- `ray(t − 1/2) = γ t` on `(0, 1)`, hence on `[0, 1]` by continuity
  have hIoo : EqOn (fun t => ray (t - 1 / 2)) γ (Ioo 0 1) := fun t ht => by
    have hs : t - 1 / 2 ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    change ray (t - 1 / 2) = γ t
    rw [hrayg hs]; simp [g]
  have hcont : ContinuousOn (fun t => ray (t - 1 / 2)) (Icc 0 1) := by
    have h1 : ContinuousOn ray (Ioo (-(1 / 2) - η) (1 / 2 + η)) :=
      (hR2.mono isOpen_Ioo hcover).contDiffOn.continuousOn
    exact h1.comp (continuousOn_id.sub continuousOn_const) fun t ht =>
      ⟨by change -(1 / 2) - η < t - 1 / 2; linarith [ht.1],
        by change t - 1 / 2 < 1 / 2 + η; linarith [ht.2]⟩
  have hcl : Icc (0 : ℝ) 1 ⊆ closure (Ioo 0 1) := by rw [closure_Ioo zero_ne_one]
  exact hIoo.of_subset_closure hcont hc.contDiffOn.continuousOn Ioo_subset_Icc_self hcl ht

/-! ### Smooth dependence on the initial data -/

section Rays

variable (hN) in
/-- The radial geodesics `t ↦ exp_{c(u)}(t w(u))` of a family of initial data, as a function of
`(u, t)`. -/
def rays (c w : ℝ → V) (p : ℝ × ℝ) : V := exp hN (c p.1) (p.2 • w p.1)

variable (hN) in
/-- The radial geodesics of the data `(c(u), w(u))`, `|u| < ε`, exist on `(−η, b + η)` and depend
smoothly on `(u, t)` there. -/
def RaysGood (c w : ℝ → V) (U₀ : Set ℝ) (b : ℝ) : Prop :=
  ∃ ε > 0, ∃ η > 0, Ioo (-ε) ε ⊆ U₀ ∧
    ContDiffOn ℝ ∞ (rays hN c w) (Ioo (-ε) ε ×ˢ Ioo (-η) (b + η)) ∧
    ∀ u ∈ Ioo (-ε) ε, IsGeodesicOn hN (fun t => exp hN (c u) (t • w u)) (Ioo (-η) (b + η))

variable {c w : ℝ → V} {U₀ : Set ℝ} (hU₀ : IsOpen U₀) (h0U₀ : (0 : ℝ) ∈ U₀)
  (hcs : ContDiffOn ℝ ∞ c U₀) (hws : ContDiffOn ℝ ∞ w U₀) (hcN : ∀ u ∈ U₀, c u ∈ N)
  (hwT : ∀ u ∈ U₀, prj hN (c u) (w u) = w u)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem RaysGood.mono {b b' : ℝ} (h : RaysGood hN c w U₀ b) (hb' : b' ≤ b) :
    RaysGood hN c w U₀ b' := by
  obtain ⟨ε, hε, η, hη, hsub, hsm, hgeo⟩ := h
  have hI : Ioo (-η) (b' + η) ⊆ Ioo (-η) (b + η) := Ioo_subset_Ioo le_rfl (by linarith)
  exact ⟨ε, hε, η, hη, hsub, hsm.mono (prod_mono subset_rfl hI),
    fun u hu => (hgeo u hu).mono isOpen_Ioo hI⟩

include hU₀ h0U₀ hcs hws hcN hwT in
/-- The start: near `t = 0`, the local smooth flow. -/
theorem raysGood_zero : RaysGood hN c w U₀ 0 := by
  obtain ⟨U₁, hU₁, hx, h, hh, Φ, hΦ, hloc⟩ := exists_smooth_ray hN ⟨c 0, hcN 0 h0U₀⟩
    (R := ‖w 0‖ + 1) (by positivity)
  have hcont : ContinuousAt (fun u => (c u, w u)) 0 :=
    (hcs.prodMk hws).continuousOn.continuousAt (hU₀.mem_nhds h0U₀)
  have hev : ∀ᶠ u in 𝓝 (0 : ℝ), u ∈ U₀ ∧ c u ∈ U₁ ∧ ‖w u‖ < ‖w 0‖ + 1 := by
    have h1 := hcont.eventually ((hU₁.prod (isOpen_lt continuous_norm continuous_const)).mem_nhds
      (show (c 0, w 0) ∈ U₁ ×ˢ {x : V | ‖x‖ < ‖w 0‖ + 1} from ⟨hx, by simp⟩))
    filter_upwards [hU₀.mem_nhds h0U₀, h1] with u hu h1u using ⟨hu, h1u.1, h1u.2⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hball' : ∀ u ∈ Ioo (-ε) ε, u ∈ U₀ ∧ c u ∈ U₁ ∧ ‖w u‖ < ‖w 0‖ + 1 := fun u hu =>
    hball u (by rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact hu)
  have hI : Ioo (-(h / 2)) (0 + h / 2) ⊆ Ioo (-h) h :=
    Ioo_subset_Ioo (by linarith) (by linarith)
  refine ⟨ε, hε, h / 2, by positivity, fun u hu => (hball' u hu).1, ?_, fun u hu => ?_⟩
  · have hmaps : MapsTo (fun p : ℝ × ℝ => (c p.1, w p.1, p.2))
        (Ioo (-ε) ε ×ˢ Ioo (-(h / 2)) (0 + h / 2)) (U₁ ×ˢ ball (0 : V) (‖w 0‖ + 1) ×ˢ Ioo (-h) h) :=
      fun p hp => ⟨(hball' p.1 hp.1).2.1, mem_ball_zero_iff.2 (hball' p.1 hp.1).2.2, hI hp.2⟩
    have hinner : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (c p.1, w p.1, p.2))
        (Ioo (-ε) ε ×ˢ Ioo (-(h / 2)) (0 + h / 2)) :=
      ((hcs.comp contDiffOn_fst fun p hp => (hball' p.1 hp.1).1).prodMk
        ((hws.comp contDiffOn_fst fun p hp => (hball' p.1 hp.1).1).prodMk contDiffOn_snd))
    refine (hΦ.comp hinner hmaps).congr fun p hp => ?_
    have hu := hball' p.1 hp.1
    exact ((hloc ⟨c p.1, hcN p.1 hu.1⟩ hu.2.1 (w p.1)
      ((prj_eq_self_iff hN (hcN p.1 hu.1)).1 (hwT p.1 hu.1)) hu.2.2).2 p.2 (hI hp.2))
  · have hu' := hball' u hu
    exact (hloc ⟨c u, hcN u hu'.1⟩ hu'.2.1 (w u) ((prj_eq_self_iff hN (hcN u hu'.1)).1
      (hwT u hu'.1)) hu'.2.2).1.mono isOpen_Ioo hI

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The velocity of the ray of `(c(u), w(u))` at time `t` is the partial derivative `∂/∂t` of
`rays`. -/
theorem deriv_rays_eq {O : Set (ℝ × ℝ)} (hO : IsOpen O) (hsm : ContDiffOn ℝ ∞ (rays hN c w) O)
    {p : ℝ × ℝ} (hp : p ∈ O) :
    deriv (fun t => exp hN (c p.1) (t • w p.1)) p.2 = partialY (rays hN c w) p :=
  (hasDerivAt_partialY ((hsm.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp))).deriv

include hcN hwT in
/-- **One step**: if the rays are good up to `b ≥ 0`, and the position and velocity at time `b` of
the ray of `(c(0), w(0))` lie in the domain of a local smooth flow `Φ` (for the time `h`), the rays
are good up to `b + h/2`: each ray continues by `Φ`, glued with `isGeodesicOn_exp_smul_union`, and
its continuation is the composition of `Φ` with the (smooth) position and velocity at time `b`. -/
theorem RaysGood.step {b : ℝ} (hb : 0 ≤ b) (hgood : RaysGood hN c w U₀ b) {U₁ : Set V}
    (hU₁ : IsOpen U₁) {R h : ℝ} (hh : 0 < h) {Φ : V × V × ℝ → V}
    (hΦ : ContDiffOn ℝ ∞ Φ (U₁ ×ˢ ball (0 : V) R ×ˢ Ioo (-h) h))
    (hloc : ∀ y : N, (y : V) ∈ U₁ → ∀ v ∈ tangentSubspace hN y, ‖v‖ < R →
      IsGeodesicOn hN (fun t => exp hN y (t • v)) (Ioo (-h) h) ∧
      ∀ t ∈ Ioo (-h) h, exp hN y (t • v) = Φ (y, v, t))
    (hb₁ : exp hN (c 0) (b • w 0) ∈ U₁) (hb₂ : ‖deriv (fun t => exp hN (c 0) (t • w 0)) b‖ < R) :
    RaysGood hN c w U₀ (b + h / 2) := by
  obtain ⟨ε, hε, η, hη, hsub, hsm, hgeo⟩ := hgood
  have hO : IsOpen (Ioo (-ε) ε ×ˢ Ioo (-η) (b + η)) := isOpen_Ioo.prod isOpen_Ioo
  have hbI : b ∈ Ioo (-η) (b + η) := ⟨by linarith, by linarith⟩
  have h0I : (0 : ℝ) ∈ Ioo (-η) (b + η) := ⟨by linarith, by linarith⟩
  have h0ε : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  -- position and velocity at time `b`, smooth in `u`
  set F : ℝ → V := fun u => rays hN c w (u, b) with hFdef
  set G : ℝ → V := fun u => partialY (rays hN c w) (u, b) with hGdef
  have hmapsb : MapsTo (fun u : ℝ => (u, b)) (Ioo (-ε) ε) (Ioo (-ε) ε ×ˢ Ioo (-η) (b + η)) :=
    fun u hu => ⟨hu, hbI⟩
  have hF : ContDiffOn ℝ ∞ F (Ioo (-ε) ε) :=
    hsm.comp (contDiffOn_id.prodMk contDiffOn_const) hmapsb
  have hG : ContDiffOn ℝ ∞ G (Ioo (-ε) ε) :=
    (contDiffOn_partialY hO hsm).comp (contDiffOn_id.prodMk contDiffOn_const) hmapsb
  have hG' : ∀ u ∈ Ioo (-ε) ε, deriv (fun t => exp hN (c u) (t • w u)) b = G u := fun u hu =>
    deriv_rays_eq hO hsm (hmapsb hu)
  -- for small `u`, they stay in the domain of `Φ`
  have hcont : ContinuousAt (fun u => (F u, G u)) 0 :=
    (hF.prodMk hG).continuousOn.continuousAt (isOpen_Ioo.mem_nhds h0ε)
  have hev : ∀ᶠ u in 𝓝 (0 : ℝ), u ∈ Ioo (-ε) ε ∧ F u ∈ U₁ ∧ ‖G u‖ < R := by
    have hFG0 : (F 0, G 0) ∈ U₁ ×ˢ {x : V | ‖x‖ < R} := by
      refine ⟨hb₁, ?_⟩
      change ‖G 0‖ < R
      rw [← hG' 0 h0ε]
      exact hb₂
    have h1 := hcont.eventually
      ((hU₁.prod (isOpen_lt continuous_norm continuous_const)).mem_nhds hFG0)
    filter_upwards [isOpen_Ioo.mem_nhds h0ε, h1] with u hu h1u using ⟨hu, h1u.1, h1u.2⟩
  obtain ⟨ε', hε', hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hball' : ∀ u ∈ Ioo (-ε') ε', u ∈ Ioo (-ε) ε ∧ F u ∈ U₁ ∧ ‖G u‖ < R := fun u hu =>
    hball u (by rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact hu)
  have hpre : (fun t => t - b) ⁻¹' Ioo (-h) h = Ioo (b - h) (b + h) := by
    ext t; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h' <;>
      constructor <;> linarith [h'.1, h'.2]
  -- each ray continues by the flow `Φ`
  have hcontu : ∀ u ∈ Ioo (-ε') ε',
      IsGeodesicOn hN (fun t => exp hN (c u) (t • w u)) (Ioo (-η) (b + η) ∪ Ioo (b - h) (b + h)) ∧
      ∀ t ∈ Ioo (b - h) (b + h), exp hN (c u) (t • w u) = Φ (F u, G u, t - b) := by
    intro u hu
    obtain ⟨huε, hFU, hGR⟩ := hball' u hu
    have hgu := hgeo u huε
    have hcu : c u ∈ N := hcN u (hsub huε)
    have hwu : w u ∈ tangentSubspace hN ⟨c u, hcu⟩ := (prj_eq_self_iff hN hcu).1 (hwT u (hsub huε))
    have hFN : F u ∈ N := hgu.mem b hbI
    have hGT : G u ∈ tangentSubspace hN ⟨F u, hFN⟩ := by
      rw [← hG' u huε]; exact hgu.deriv_mem hbI
    have hflow : geoFlow hN (c u, w u) b = (F u, G u) := by
      rw [geoFlow_eq_exp, hG' u huε]
      rfl
    have hJ := hloc ⟨F u, hFN⟩ hFU (G u) hGT hGR
    have hJ' : IsGeodesicOn hN (fun t => exp hN (geoFlow hN (c u, w u) b).1
        (t • (geoFlow hN (c u, w u) b).2)) (Ioo (-h) h) := by
      rw [hflow]; exact hJ.1
    obtain ⟨hU, hfl⟩ := isGeodesicOn_exp_smul_union hcu hwu hgu isPreconnected_Ioo h0I hbI hJ'
      isPreconnected_Ioo ⟨by linarith, hh⟩
    rw [hpre] at hU
    refine ⟨hU, fun t ht => ?_⟩
    have ht' : t - b ∈ Ioo (-h) h := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := congrArg Prod.fst (hfl (t - b) ht')
    rw [add_sub_cancel, hflow] at this
    rw [← (hJ.2 (t - b) ht')]
    exact this
  set η' := min η (h / 4) with hη'def
  have hη' : 0 < η' := lt_min hη (by positivity)
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'h : η' ≤ h / 4 := min_le_right _ _
  have hsub' : Ioo (-ε') ε' ⊆ Ioo (-ε) ε := fun u hu => (hball' u hu).1
  have hcover : Ioo (-η') (b + h / 2 + η') ⊆ Ioo (-η) (b + η) ∪ Ioo (b - h) (b + h) := by
    intro t ht
    rcases lt_or_ge t (b + η) with htb | htb
    · exact Or.inl ⟨by linarith [ht.1], htb⟩
    · exact Or.inr ⟨by linarith, by linarith [ht.2]⟩
  refine ⟨ε', hε', η', hη', fun u hu => hsub (hsub' hu), ?_, fun u hu =>
    (hcontu u hu).1.mono isOpen_Ioo hcover⟩
  -- smoothness: near each point, either the old rays or the composition with `Φ`
  have hA : ContDiffOn ℝ ∞ (rays hN c w) (Ioo (-ε') ε' ×ˢ Ioo (b - h) (b + h)) := by
    have hinner : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (F p.1, G p.1, p.2 - b))
        (Ioo (-ε') ε' ×ˢ Ioo (b - h) (b + h)) :=
      ((hF.mono hsub').comp contDiffOn_fst fun p hp => hp.1).prodMk
        (((hG.mono hsub').comp contDiffOn_fst fun p hp => hp.1).prodMk
          (contDiffOn_snd.sub contDiffOn_const))
    have hmaps : MapsTo (fun p : ℝ × ℝ => (F p.1, G p.1, p.2 - b))
        (Ioo (-ε') ε' ×ˢ Ioo (b - h) (b + h)) (U₁ ×ˢ ball (0 : V) R ×ˢ Ioo (-h) h) :=
      fun p hp => ⟨(hball' p.1 hp.1).2.1, mem_ball_zero_iff.2 (hball' p.1 hp.1).2.2,
        by linarith [hp.2.1], by linarith [hp.2.2]⟩
    refine (hΦ.comp hinner hmaps).congr fun p hp => ?_
    exact (hcontu p.1 hp.1).2 p.2 hp.2
  refine contDiffOn_of_locally_contDiffOn fun p hp => ?_
  rcases lt_or_ge p.2 (b + η) with hpb | hpb
  · refine ⟨Ioo (-ε) ε ×ˢ Ioo (-η) (b + η), hO, ⟨hsub' hp.1, by linarith [hp.2.1], hpb⟩, ?_⟩
    exact hsm.mono inter_subset_right
  · refine ⟨Ioo (-ε') ε' ×ˢ Ioo (b - h) (b + h), isOpen_Ioo.prod isOpen_Ioo,
      ⟨hp.1, by linarith, by linarith [hp.2.2]⟩, ?_⟩
    exact hA.mono inter_subset_right

include hU₀ h0U₀ hcs hws hcN hwT in
/-- **Smooth dependence on the initial data over a compact interval** (the step "using the
compactness of `[0, 1]`" in Milnor's proof of Lemma 14.4): if the ray of `(c(0), w(0))` is a
geodesic on `(−δ, B + δ)`, the rays of `(c(u), w(u))`, `u` small, are geodesics on a common interval
`(−η, B + η)` and depend smoothly on `(u, t)` there.  Proof: the supremum `b₀` of the `b ≤ B` up
to which this holds is `B` and is attained, by `RaysGood.step` at a point of the base ray near
time `b₀`. -/
theorem raysGood_of_isGeodesicOn {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ)
    (hbase : IsGeodesicOn hN (fun t => exp hN (c 0) (t • w 0)) (Ioo (-δ) (B + δ))) :
    RaysGood hN c w U₀ B := by
  set S := {b ∈ Icc 0 B | RaysGood hN c w U₀ b} with hSdef
  have hS0 : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hB⟩, raysGood_zero hU₀ h0U₀ hcs hws hcN hwT⟩
  have hSbdd : BddAbove S := ⟨B, fun b hb => hb.1.2⟩
  set b₀ := sSup S with hb₀def
  have hb₀0 : 0 ≤ b₀ := le_csSup hSbdd hS0
  have hb₀B : b₀ ≤ B := csSup_le ⟨0, hS0⟩ fun b hb => hb.1.2
  have hb₀I : b₀ ∈ Ioo (-δ) (B + δ) := ⟨by linarith, by linarith⟩
  set γ₀ : ℝ → V := fun t => exp hN (c 0) (t • w 0) with hγ₀
  -- the local flow at the point of the base ray at time `b₀`
  obtain ⟨U₁, hU₁, hxU, h, hh, Φ, hΦ, hloc⟩ := exists_smooth_ray hN ⟨γ₀ b₀, hbase.mem b₀ hb₀I⟩
    (R := ‖deriv γ₀ b₀‖ + 1) (by positivity)
  have hcont : ContinuousAt (fun t => (γ₀ t, deriv γ₀ t)) b₀ :=
    (hbase.contDiffOn.continuousOn.prodMk hbase.contDiffOn_deriv.continuousOn).continuousAt
      (isOpen_Ioo.mem_nhds hb₀I)
  have hev : ∀ᶠ t in 𝓝 b₀, γ₀ t ∈ U₁ ∧ ‖deriv γ₀ t‖ < ‖deriv γ₀ b₀‖ + 1 :=
    hcont.eventually ((hU₁.prod (isOpen_lt continuous_norm continuous_const)).mem_nhds
      (show (γ₀ b₀, deriv γ₀ b₀) ∈ U₁ ×ˢ {x : V | ‖x‖ < ‖deriv γ₀ b₀‖ + 1} from ⟨hxU, by simp⟩))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  -- a time `s` up to which the rays are good, close to `b₀`
  have hm : 0 < min r (h / 4) := lt_min hr (by positivity)
  obtain ⟨s, hsS, hs⟩ := exists_lt_of_lt_csSup ⟨0, hS0⟩ (show b₀ - min r (h / 4) < b₀ by linarith)
  have hsb₀ : s ≤ b₀ := le_csSup hSbdd hsS
  have hsr : s ∈ ball b₀ r := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [min_le_left r (h / 4)]
  obtain ⟨hsU, hsR⟩ := hball s hsr
  have hstep := hsS.2.step hcN hwT hsS.1.1 hU₁ hh hΦ hloc hsU hsR
  have hmin : min (s + h / 2) B ∈ S := ⟨⟨le_min (by linarith [hsS.1.1]) hB, min_le_right _ _⟩,
    hstep.mono (min_le_left _ _)⟩
  have hle : min (s + h / 2) B ≤ b₀ := le_csSup hSbdd hmin
  have hlt : b₀ < s + h / 2 := by linarith [min_le_right r (h / 4)]
  have hBeq : min (s + h / 2) B = B := by
    rcases min_choice (s + h / 2) B with h' | h'
    · rw [h'] at hle; exfalso; linarith
    · exact h'
  rw [hBeq] at hmin
  exact hmin.2

end Rays

/-! ### Lemma 14.4 -/

/-- **A geodesic segment is the radial geodesic from its initial point**: `γ` on `[0, 1]` is
`t ↦ exp_{γ(0)}(t γ'(0))` (`γ'(0)` the one-sided velocity), a geodesic on an open interval
containing `[0, 1]`. -/
theorem exists_initial_ray {γ : ℝ → V} (hc : IsSmoothCurveIn hN γ)
    (hgeo : IsGeodesicOn hN γ (Ioo 0 1)) :
    ∃ η > 0, IsGeodesicOn hN (fun t => exp hN (γ 0) (t • velAlong γ 0)) (Ioo (-η) (1 + η)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, exp hN (γ 0) (t • velAlong γ 0) = γ t := by
  obtain ⟨η, hη, hray, heq⟩ := exists_midpoint_ray hc hgeo
  set g : ℝ → V := fun t => exp hN (γ (1 / 2)) ((t - 1 / 2) • deriv γ (1 / 2)) with hgdef
  have hg : IsGeodesicOn hN g (Ioo (-η) (1 + η)) := by
    have := hray.comp_mul_add 1 (-(1 / 2))
    have hpre : (fun t : ℝ => 1 * t + -(1 / 2)) ⁻¹' Ioo (-(1 / 2) - η) (1 / 2 + η) =
        Ioo (-η) (1 + η) := by
      ext t; simp only [mem_preimage, mem_Ioo, one_mul]; constructor <;> intro h <;>
        constructor <;> linarith [h.1, h.2]
    rw [hpre] at this
    refine this.congr fun t _ => ?_
    simp only [hgdef]
    congr 2
    ring
  have h0 : (0 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
  have h0' : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hgγ : EqOn g γ (Icc 0 1) := fun t ht => heq t ht
  have hg0 : g 0 = γ 0 := hgγ h0'
  have hg0' : deriv g 0 = velAlong γ 0 := by
    have h1 : HasDerivWithinAt γ (deriv g 0) (Icc 0 1) 0 :=
      (hg.hasDerivAt h0).hasDerivWithinAt.congr_of_mem (fun t ht => (hgγ ht).symm) h0'
    exact (h1.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 h0')).symm
  have hE := hg.eqOn_exp_smul isPreconnected_Ioo h0
  rw [hg0, hg0'] at hE
  exact ⟨η, hη, hg.congr hE.symm, fun t ht =>
    (hE ⟨by linarith [ht.1], by linarith [ht.2]⟩).trans (hgγ ht)⟩

/-- **Lemma 14.4** (Milnor p. 81): every Jacobi field `J` along a geodesic `γ : [0, 1] → N` is the
variation field `∂α/∂u (0, t)` of a variation `α` of `γ` through geodesics.  Here
`α(u, t) = exp_{c(u)}(t w(u))` with `c(u) = exp_{γ(0)}(u J(0))` and
`w(u) = P_{c(u)}(γ'(0) + u DJ/dt(0))`: its variation field is a Jacobi field (Lemma 14.3) with the
initial values `J(0)`, `DJ/dt(0)` (symmetry of the mixed partials), hence equals `J`. -/
theorem lemma_14_4 {γ : ℝ → V} (hc : IsSmoothCurveIn hN γ) (hgeo : IsGeodesicOn hN γ (Ioo 0 1))
    {J : ℝ → V} (hJ : IsJacobiField hN γ J) :
    ∃ ε > 0, ∃ α : ℝ → ℝ → V,
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1 p.2) (Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ u ∈ Ioo (-ε) ε, ∀ t ∈ Icc (0 : ℝ) 1, α u t ∈ N) ∧
      (∀ u ∈ Ioo (-ε) ε, IsGeodesicOn hN (α u) (Ioo 0 1)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, deriv (fun u => α u t) 0 = J t := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hxN : γ 0 ∈ N := hc.mem 0 h0
  have hvT : prj hN (γ 0) (velAlong γ 0) = velAlong γ 0 := hc.velAlong_mem h0
  have hjT : J 0 ∈ tangentSubspace hN ⟨γ 0, hxN⟩ := (prj_eq_self_iff hN hxN).1 (hJ.tangent 0 h0)
  have haT : prj hN (γ 0) (covAlong hN γ J 0) = covAlong hN γ J 0 := prj_prj hN _ _
  -- the curve `c(u) = exp_{γ(0)}(u J(0))` of initial points
  obtain ⟨U₁, -, hxU, h, hh, Φ, hΦ, hloc⟩ := exists_smooth_ray hN ⟨γ 0, hxN⟩ (R := ‖J 0‖ + 1)
    (by positivity)
  obtain ⟨hcgeo, hcΦ⟩ := hloc ⟨γ 0, hxN⟩ hxU (J 0) hjT (by linarith)
  set c : ℝ → V := fun u => exp hN (γ 0) (u • J 0) with hcdef
  have hU₀ : IsOpen (Ioo (-h) h) := isOpen_Ioo
  have h0U₀ : (0 : ℝ) ∈ Ioo (-h) h := ⟨by linarith, hh⟩
  have hcs : ContDiffOn ℝ ∞ c (Ioo (-h) h) := by
    have : ContDiffOn ℝ ∞ (fun u : ℝ => Φ (γ 0, J 0, u)) (Ioo (-h) h) :=
      hΦ.comp (contDiffOn_const.prodMk (contDiffOn_const.prodMk contDiffOn_id))
        fun u hu => ⟨hxU, mem_ball_zero_iff.2 (by linarith), hu⟩
    exact this.congr fun u hu => hcΦ u hu
  have hcN : ∀ u ∈ Ioo (-h) h, c u ∈ N := fun u hu => hcgeo.mem u hu
  have hc0 : c 0 = γ 0 := by simp only [hcdef, zero_smul, exp_zero hxN]
  have hc' : HasDerivAt c (J 0) 0 := hasDerivAt_exp_smul_zero ⟨γ 0, hxN⟩ hjT
  -- the initial velocities `w(u) = P_{c(u)}(γ'(0) + u DJ/dt(0))`
  set w : ℝ → V := fun u => prj hN (c u) (velAlong γ 0 + u • covAlong hN γ J 0) with hwdef
  have hP : ContDiffOn ℝ ∞ (fun u => prj hN (c u)) (Ioo (-h) h) := ContDiffOn.prj_comp hN hcs hcN
  have hws : ContDiffOn ℝ ∞ w (Ioo (-h) h) :=
    hP.clm_apply (contDiffOn_const.add (contDiffOn_id.smul contDiffOn_const))
  have hwT : ∀ u ∈ Ioo (-h) h, prj hN (c u) (w u) = w u := fun u _ => prj_prj hN _ _
  have hw0 : w 0 = velAlong γ 0 := by simp only [hwdef, hc0, zero_smul, add_zero, hvT]
  -- the base ray is `γ`; the rays of `(c(u), w(u))` exist on `[0, 1]` for small `u`
  obtain ⟨η, hη, hray, hrayγ⟩ := exists_initial_ray hc hgeo
  have hbase : IsGeodesicOn hN (fun t => exp hN (c 0) (t • w 0)) (Ioo (-η) (1 + η)) := by
    rw [hc0, hw0]; exact hray
  obtain ⟨ε, hε, η', hη', hsub, hsm, hrays⟩ :=
    raysGood_of_isGeodesicOn hU₀ h0U₀ hcs hws hcN hwT zero_le_one hη hbase
  -- the variation
  set α : ℝ → ℝ → V := fun u t => exp hN (c u) (t • w u) with hαdef
  have hIcc : Icc (0 : ℝ) 1 ⊆ Ioo (-η') (1 + η') := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hα : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1 p.2) (Ioo (-ε) ε ×ˢ Icc (0 : ℝ) 1) :=
    hsm.mono (prod_mono subset_rfl hIcc)
  have hαN : ∀ u ∈ Ioo (-ε) ε, ∀ t ∈ Icc (0 : ℝ) 1, α u t ∈ N := fun u hu t ht =>
    (hrays u hu).mem t (hIcc ht)
  have hαgeo : ∀ u ∈ Ioo (-ε) ε, IsGeodesicOn hN (α u) (Ioo 0 1) := fun u hu =>
    (hrays u hu).mono isOpen_Ioo (Ioo_subset_Ioo (by linarith) (by linarith))
  have hα0 : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t := fun t ht => by
    change exp hN (c 0) (t • w 0) = γ t
    rw [hc0, hw0]; exact hrayγ t ht
  refine ⟨ε, hε, α, hα, hαN, hαgeo, hα0, ?_⟩
  -- its variation field is a Jacobi field along `γ` (Lemma 14.3) ...
  set Wf : ℝ → V := fun t => deriv (fun u => α u t) 0 with hWf
  have hW : IsJacobiField hN γ Wf := (lemma_14_3 hε hα hαN hαgeo).congr_curve hα0
  -- ... with `W(0) = c'(0) = J(0)` ...
  have h0ε : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hW0 : Wf 0 = J 0 := by
    have hev : (fun u => α u 0) =ᶠ[𝓝 0] c := by
      filter_upwards [hU₀.mem_nhds h0U₀] with u hu
      change exp hN (c u) ((0 : ℝ) • w u) = c u
      rw [zero_smul, exp_zero (hcN u hu)]
    change deriv (fun u => α u 0) 0 = J 0
    rw [hev.deriv_eq, hc'.deriv]
  -- ... and `DW/dt(0) = Dw/du(0) = DJ/dt(0)` (symmetry of the mixed partials)
  set F := rays hN c w with hFdef
  have hO : IsOpen (Ioo (-ε) ε ×ˢ Ioo (-η') (1 + η')) := isOpen_Ioo.prod isOpen_Ioo
  have h0η : (0 : ℝ) ∈ Ioo (-η') (1 + η') := ⟨by linarith, by linarith⟩
  have hp₀ : ((0 : ℝ), (0 : ℝ)) ∈ Ioo (-ε) ε ×ˢ Ioo (-η') (1 + η') := ⟨h0ε, h0η⟩
  have hFdiff : ∀ p ∈ Ioo (-ε) ε ×ˢ Ioo (-η') (1 + η'), DifferentiableAt ℝ F p := fun p hp =>
    (hsm.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)
  have hWX : ∀ t ∈ Ioo (-η') (1 + η'), Wf t = partialX F (0, t) := fun t ht =>
    (hasDerivAt_partialX (hFdiff (0, t) ⟨h0ε, ht⟩)).deriv
  have hWd : HasDerivAt Wf (partialY (partialX F) (0, 0)) 0 := by
    have hd : DifferentiableAt ℝ (partialX F) (0, 0) :=
      ((contDiffOn_partialX hO hsm).contDiffAt (hO.mem_nhds hp₀)).differentiableAt (by simp)
    refine (hasDerivAt_partialY hd).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds h0η] with t ht
    exact hWX t ht
  have hYw : ∀ u ∈ Ioo (-ε) ε, partialY F (u, 0) = w u := fun u hu => by
    have h1 := (hasDerivAt_partialY (hFdiff (u, 0) ⟨hu, h0η⟩)).deriv
    have h2 := (hasDerivAt_exp_smul_zero (hN := hN) ⟨c u, hcN u (hsub hu)⟩
      ((prj_eq_self_iff hN (hcN u (hsub hu))).1 (hwT u (hsub hu)))).deriv
    rw [← h1]
    exact h2
  have hmixed : partialY (partialX F) (0, 0) = deriv w 0 := by
    rw [← partialX_partialY_of_contDiffOn hO hsm hp₀]
    have hd : DifferentiableAt ℝ (partialY F) (0, 0) :=
      ((contDiffOn_partialY hO hsm).contDiffAt (hO.mem_nhds hp₀)).differentiableAt (by simp)
    rw [← (hasDerivAt_partialX hd).deriv]
    exact Filter.EventuallyEq.deriv_eq (eventually_of_mem (isOpen_Ioo.mem_nhds h0ε) hYw)
  -- `Dw/du(0) = DJ/dt(0)`, using `P P' P = 0`
  have hPd : HasDerivAt (fun u => prj hN (c u)) (deriv (fun u => prj hN (c u)) 0) 0 :=
    ((hP.contDiffAt (hU₀.mem_nhds h0U₀)).differentiableAt (by simp)).hasDerivAt
  have hl : HasDerivAt (fun u : ℝ => velAlong γ 0 + u • covAlong hN γ J 0)
      (covAlong hN γ J 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (covAlong hN γ J 0)).const_add
      (velAlong γ 0)
  have hwd : HasDerivAt w (deriv (fun u => prj hN (c u)) 0
      (velAlong γ 0 + (0 : ℝ) • covAlong hN γ J 0) + prj hN (c 0) (covAlong hN γ J 0)) 0 :=
    hPd.clm_apply hl
  have hPP : prj hN (γ 0) (deriv (fun u => prj hN (c u)) 0 (velAlong γ 0)) = 0 := by
    have h1 := hPd.clm_comp hPd
    have h2 : HasDerivAt (fun u => prj hN (c u)) ((deriv (fun u => prj hN (c u)) 0).comp
        (prj hN (c 0)) + (prj hN (c 0)).comp (deriv (fun u => prj hN (c u)) 0)) 0 := by
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards with u
      ext y
      exact (prj_prj hN _ _).symm
    have h3 := congrArg (fun L => L (velAlong γ 0)) (h2.unique hPd)
    simp only [add_apply, ContinuousLinearMap.comp_apply, hc0, hvT] at h3
    exact add_eq_left.1 h3
  have hcovW : covAlong hN γ Wf 0 = covAlong hN γ J 0 := by
    rw [covAlong, hWd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 h0), hmixed,
      hwd.deriv, zero_smul, add_zero, hc0, map_add, hPP, zero_add, haT]
    exact haT
  -- so `W = J` (uniqueness)
  intro t ht
  have e1 := hW.eqOn_jacSol hc h0 ht
  have e2 := hJ.eqOn_jacSol hc h0 ht
  rw [hW0, hcovW] at e1
  exact congrArg Prod.fst (e1.trans e2.symm)

/-- **A Jacobi field is determined by its values at two non-conjugate points, and these values can
be prescribed** (Milnor p. 81, the parenthetical remark in the proof of Lemma 14.4, with the
dimension count): if `a ≠ b` are not conjugate along `γ`, `J ↦ (J(a), J(b))` is an isomorphism
`𝒥(γ) ≅ T_{γ(a)}N × T_{γ(b)}N`. -/
theorem jacEvalEnds_bijective_of_not_isConjugate {γ : ℝ → V} (hc : IsSmoothCurveIn hN γ)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a ≠ b)
    (hnc : ¬IsConjugate hN γ a b) : Bijective (jacEvalEnds hc ha hb) := by
  have hinj : Injective (jacEvalEnds hc ha hb) := by
    refine (injective_iff_map_eq_zero _).2 fun J hJ => ?_
    have h1 : (J : ℝ → V) a = 0 := congrArg (fun z => (z.1 : V)) hJ
    have h2 : (J : ℝ → V) b = 0 := congrArg (fun z => (z.2 : V)) hJ
    refine Subtype.ext (jacobiSpace_eq_zero hc J.2 fun t ht => ?_)
    by_contra hne
    exact hnc ⟨ha, hb, hab, J, J.2.1, h1, h2, t, ht, hne⟩
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [finrank_jacobiSpace hc, Module.finrank_prod, finrank_tanAt hN (hc.mem a ha),
    finrank_tanAt hN (hc.mem b hb)]
  ring

end Morse
