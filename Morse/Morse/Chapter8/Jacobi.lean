import Morse.Chapter8.Hessian

/-!
Milnor, *Morse Theory*, §14, pp. 77–79 (the Jacobi equation, Theorem 14.1), for a submanifold
`N ⊆ ℝᴷ` with the induced metric.

# Jacobi fields and the null space of the Hessian

## Milnor's text, paraphrased

* (p. 77) A smooth vector field `J` along a geodesic `γ` is a *Jacobi field* if
  `D²J/dt² + R(V, J)V = 0`, `V = dγ/dt`.  In a parallel orthonormal frame this is a linear
  second-order system, so there are `2n` linearly independent solutions, defined along all of `γ`
  and smooth, determined by `J(0)` and `DJ/dt(0)`.  Two parameter values `a ≠ b` are *conjugate*
  along `γ` if a nonzero Jacobi field vanishes at both.
* **Theorem 14.1** (p. 78): `W₁ ∈ TΩ_γ` lies in the null space of `E_**` if and only if `W₁` is a
  Jacobi field.  Proof: a Jacobi field vanishing at the ends is smooth, so the second variation
  formula gives `E_**(J, W₂) = 0`.  Conversely, testing against `W₂ = f(t)(D²W₁/dt² + R(V, W₁)V)`,
  `f` vanishing exactly at the break points, shows that `W₁` is a Jacobi field on each piece;
  testing against `W₂` with `W₂(t_i) = Δ_{t_i} DW₁/dt` shows that `DW₁/dt` has no jumps; since a
  Jacobi field is determined by its value and derivative at one point, the pieces fit together into
  one smooth Jacobi field.

## In the embedded setting

* `Morse.jacobiExpr hN γ J = D²J/dt² + R(V, J)V`; `Morse.IsJacobiField hN γ J`: `J` is `C^∞` on
  `[0, 1]`, tangent to `N` along `γ`, and `Morse.jacobiExpr hN γ J = 0` on `(0, 1)`.
* **Theorem 14.1**: `Morse.theorem_14_1`, for the bilinear form `Morse.energyHessian` on `TΩ_γ`.
  The steps: `Morse.IsJacobiField.secondVariation_eq_zero` (the easy direction),
  `Morse.jacobiExpr_eq_zero_of_null` (each piece is a Jacobi field), `Morse.jump_eq_zero_of_null`
  (no jumps), `Morse.smooth_near_of_null` (smoothness across the former break points).
* `Morse.deriv_deriv_eq_of_jacobiExpr`: the Jacobi equation for a field tangent to `N` is the
  second-order equation `J'' = -P(P'J') - R(V, J)V + (1 - P)(P''J + 2P'J')` in `V`
  (`P(t) = P_{γ(t)}`), whose right side is smooth in `(t, J, J')`.

## What Milnor leaves implicit

* **The test fields.**  As in Corollary 12.3: the field `f (D²W₁/dt² + R(V, W₁)V)` needs to be
  continuous at the break points, where the one-sided expressions differ; here bump functions
  supported inside a piece are used instead, one point at a time.  The field with prescribed
  values `Δ_{t_i} DW₁/dt` is `φ P(Δ_x DW₁/dt)`, `φ` a bump function at the break point `x`.
* **"`DW₁/dt` has no jumps" gives `W₁ ∈ C¹`**: in `ℝᴷ` the jump of `W₁'` also has a normal part,
  which vanishes because both one-sided normal parts are `II(V, W₁)` (`Morse.jump_eq_prj_jump`).
* **The pieces fit together** "since a Jacobi field is determined by its value and derivative at
  one point": this needs the existence and uniqueness theory of linear equations along all of `γ`
  (Lemma 14.A of the exposition), which is formalized later (`Morse.exists_linearODE`,
  `Morse/Chapter9/JacobiODE.lean`) but not used here.  The argument used instead is local and
  needs no existence theorem: the second-order equation above holds on both sides of a former
  break point `x`, with a right side that is smooth and continuous across `x`; hence `W₁'` is
  differentiable at `x` (`Morse.hasDerivAt_of_hasDerivAt_punctured`), and a solution of a smooth
  second-order equation is smooth (`Morse.contDiffOn_of_ode`, a bootstrap).

## Formalized in `Morse/Chapter9/`

The `2n`-dimensional space of Jacobi fields (Milnor's "`2n` linearly independent solutions",
Lemma 14.A and Corollary 14.B of the exposition: `Morse.exists_linearODE`,
`Morse.finrank_jacobiSpace`), conjugate points and their multiplicity as a dimension
(`Morse.IsConjugate`, `Morse.conjMultiplicity`), the nullity of `E_**` as that multiplicity
(`Morse.theorem_14_1_nullity`), Remark 14.2 (`0 ≤ ν < n`, `Morse.remark_14_2`), Lemmas 14.3 and
14.4 (Jacobi fields from families of geodesics, `Morse.lemma_14_3`, `Morse.lemma_14_4`), and
Remarks 14.5 and 14.6 (`Morse.remark_14_5`, `Morse.remark_14_6`).
-/

open Set Filter Topology Function MeasureTheory Metric
open scoped ContDiff Manifold RealInnerProductSpace Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Regularity of solutions of smooth second-order equations -/

omit [FiniteDimensional ℝ V] in
/-- **Bootstrap**: a solution `J` of `J'' = F(t, J, J')` on an open set, `F` smooth, is smooth. -/
theorem contDiffOn_of_ode {O : Set ℝ} (hO : IsOpen O) {F : ℝ × V × V → V}
    (hF : ContDiffOn ℝ ∞ F (O ×ˢ univ)) {J J' : ℝ → V}
    (hJ : ∀ t ∈ O, HasDerivAt J (J' t) t) (hJ' : ∀ t ∈ O, HasDerivAt J' (F (t, J t, J' t)) t) :
    ContDiffOn ℝ ∞ J O := by
  have key : ∀ n : ℕ, ContDiffOn ℝ n J O ∧ ContDiffOn ℝ n J' O := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, contDiffOn_zero]
      exact ⟨fun t ht => (hJ t ht).continuousAt.continuousWithinAt,
        fun t ht => (hJ' t ht).continuousAt.continuousWithinAt⟩
    | succ n ih =>
      push_cast
      refine ⟨(contDiffOn_succ_iff_deriv_of_isOpen hO).2 ⟨fun t ht =>
        (hJ t ht).differentiableAt.differentiableWithinAt, by simp, ih.2.congr fun t ht =>
          (hJ t ht).deriv⟩, (contDiffOn_succ_iff_deriv_of_isOpen hO).2 ⟨fun t ht =>
        (hJ' t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩⟩
      have h1 : ContDiffOn ℝ n (fun t => F (t, J t, J' t)) O :=
        (hF.of_le (by exact_mod_cast le_top)).comp (contDiffOn_id.prodMk (ih.1.prodMk ih.2))
          fun t ht => mk_mem_prod ht (mem_univ _)
      exact h1.congr fun t ht => (hJ' t ht).deriv
  exact contDiffOn_infty.2 fun n => (key n).1

omit [FiniteDimensional ℝ V] in
/-- **Extension of a derivative across a point**: if `f` and `g` are continuous at `x` and
`f' = g` on a punctured neighbourhood of `x`, then `f'(x) = g(x)`. -/
theorem hasDerivAt_of_hasDerivAt_punctured {f g : ℝ → V} {x r : ℝ} (hr : 0 < r)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hd : ∀ t ∈ Ioo (x - r) (x + r), t ≠ x → HasDerivAt f (g t) t) : HasDerivAt f (g x) x := by
  have hR : HasDerivWithinAt f (g x) (Ici x) x := by
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo x (x + r)) (fun t ht => ?_)
      hf.continuousWithinAt (Ioo_mem_nhdsGT (by linarith)) ?_
    · exact (hd t ⟨by linarith [ht.1], ht.2⟩ (ne_of_gt ht.1)).differentiableAt
        |>.differentiableWithinAt
    · have hev : g =ᶠ[𝓝[>] x] deriv f := by
        filter_upwards [Ioo_mem_nhdsGT (show x < x + r by linarith)] with t ht
        exact (hd t ⟨by linarith [ht.1], ht.2⟩ (ne_of_gt ht.1)).deriv.symm
      exact (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' hev
  have hL : HasDerivWithinAt f (g x) (Iic x) x := by
    refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo (x - r) x) (fun t ht => ?_)
      hf.continuousWithinAt (Ioo_mem_nhdsLT (by linarith)) ?_
    · exact (hd t ⟨ht.1, by linarith [ht.2]⟩ (ne_of_lt ht.2)).differentiableAt
        |>.differentiableWithinAt
    · have hev : g =ᶠ[𝓝[<] x] deriv f := by
        filter_upwards [Ioo_mem_nhdsLT (show x - r < x by linarith)] with t ht
        exact (hd t ⟨ht.1, by linarith [ht.2]⟩ (ne_of_lt ht.2)).deriv.symm
      exact (hg.tendsto.mono_left nhdsWithin_le_nhds).congr' hev
  have := hL.union hR
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

/-! ### Smoothness of the curvature term along a path -/

omit [FiniteDimensional ℝ W] in
/-- Along a smooth path in `N`, `τ ↦ R(a(τ), b(τ))c(τ)` is smooth where `γ, a, b, c` are,
provided `a(τ), b(τ)` are tangent. -/
theorem contDiffAt_curvR {γ a b c : ℝ → V} {τ₀ : ℝ} (hγ : ContDiffAt ℝ ∞ γ τ₀)
    (hγN : ∀ᶠ τ in 𝓝 τ₀, γ τ ∈ N) (ha : ContDiffAt ℝ ∞ a τ₀) (hb : ContDiffAt ℝ ∞ b τ₀)
    (hc : ContDiffAt ℝ ∞ c τ₀) (haT : ∀ᶠ τ in 𝓝 τ₀, prj hN (γ τ) (a τ) = a τ)
    (hbT : ∀ᶠ τ in 𝓝 τ₀, prj hN (γ τ) (b τ) = b τ) :
    ContDiffAt ℝ ∞ (fun τ => curvR hN (γ τ) (a τ) (b τ) (c τ)) τ₀ := by
  set q : N := ⟨γ τ₀, hγN.self_of_nhds⟩
  set σ := sliceAt hN q
  have hq : γ τ₀ ∈ σ.φ.source := mem_sliceAt_source hN q
  set Qd := fderiv ℝ (projRep σ)
  have hQd : ContDiffAt ℝ ∞ Qd (γ τ₀) :=
    (contDiffAt_projRep σ (q := q) hq).fderiv_right (m := ∞) (by simp)
  have hQγ : ContDiffAt ℝ ∞ (fun τ => Qd (γ τ)) τ₀ := hQd.comp τ₀ hγ
  have h1 : ContDiffAt ℝ ∞ (fun τ => Qd (γ τ) (b τ) (Qd (γ τ) (a τ) (c τ)) -
      Qd (γ τ) (a τ) (Qd (γ τ) (b τ) (c τ))) τ₀ :=
    ((hQγ.clm_apply hb).clm_apply ((hQγ.clm_apply ha).clm_apply hc)).sub
      ((hQγ.clm_apply ha).clm_apply ((hQγ.clm_apply hb).clm_apply hc))
  refine h1.congr_of_eventuallyEq ?_
  have hsrc : ∀ᶠ τ in 𝓝 τ₀, γ τ ∈ σ.φ.source :=
    hγ.continuousAt.eventually (σ.φ.open_source.mem_nhds hq)
  filter_upwards [hsrc, hγN, haT, hbT] with τ h1 hN' ha' hb'
  have ha'' : a τ ∈ tangentSubspace hN ⟨γ τ, hN'⟩ := (prj_eq_self_iff hN hN').1 ha'
  have hb'' : b τ ∈ tangentSubspace hN ⟨γ τ, hN'⟩ := (prj_eq_self_iff hN hN').1 hb'
  rw [curvR_of_mem hN hN', curvOp_apply]
  simp only [secondFundForm]
  rw [dN_tanProj_eq_fderiv hN σ (q := ⟨γ τ, hN'⟩) h1 ha'',
    dN_tanProj_eq_fderiv hN σ (q := ⟨γ τ, hN'⟩) h1 hb'']

/-! ### Jacobi fields -/

/-- **The Jacobi operator** `D²J/dt² + R(V, J)V` along `γ` (Milnor p. 77), `V = dγ/dt`. -/
def jacobiExpr (γ J : ℝ → V) (t : ℝ) : V :=
  covD hN γ (covD hN γ J) t + curvR hN (γ t) (deriv γ t) (J t) (deriv γ t)

/-- **A Jacobi field along `γ`** on `[0, 1]` (Milnor p. 77): a smooth vector field along `γ`
(`C^∞` on `[0, 1]`, with one-sided derivatives at the ends, and tangent to `N`) satisfying the
Jacobi equation `D²J/dt² + R(V, J)V = 0` (on `(0, 1)`, hence on `[0, 1]` by continuity). -/
structure IsJacobiField (γ J : ℝ → V) : Prop where
  contDiffOn : ContDiffOn ℝ ∞ J (Icc 0 1)
  tangent : ∀ t ∈ Icc (0 : ℝ) 1, prj hN (γ t) (J t) = J t
  eq : ∀ t ∈ Ioo (0 : ℝ) 1, jacobiExpr hN γ J t = 0

variable {hN} {γ J : ℝ → V}

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- A Jacobi field vanishing at both ends lies in `TΩ_γ`. -/
theorem IsJacobiField.mem_pathTangent (hJ : IsJacobiField hN γ J) (h0 : J 0 = 0)
    (h1 : J 1 = 0) : J ∈ pathTangent hN γ :=
  ⟨IsPiecewiseSmooth.of_contDiffOn hJ.contDiffOn zero_le_one subset_rfl, hJ.tangent, h0, h1⟩

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **The easy half of Theorem 14.1** (Milnor p. 78): for a Jacobi field `J`, the second variation
`½ E_**(J, W₂)` vanishes for every `W₂`: `DJ/dt` has no jumps and `D²J/dt² + R(V, J)V = 0`. -/
theorem IsJacobiField.secondVariation_eq_zero (hJ : IsJacobiField hN γ J) (Y : ℝ → V) :
    secondVariation hN γ J Y = 0 := by
  have hj : ∀ t ∈ Ioo (0 : ℝ) 1, ⟪Y t, prj hN (γ t) (jump J t)⟫ = 0 := fun t ht => by
    rw [jump_eq_zero ((hJ.contDiffOn.contDiffAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt
      (by simp)), map_zero, inner_zero_right]
  have hi : ∀ t ∈ Ioo (0 : ℝ) 1,
      ⟪Y t, covD hN γ (covD hN γ J) t + curvR hN (γ t) (deriv γ t) (J t) (deriv γ t)⟫ = 0 :=
    fun t ht => by
      have := hJ.eq t ht
      rw [jacobiExpr] at this
      rw [this, inner_zero_right]
  rw [secondVariation, finsum_mem_eq_zero_of_forall_eq_zero hj,
    intervalIntegral.integral_congr_Ioo_of_le zero_le_one (g := fun _ => (0 : ℝ)) hi]
  simp

/-! ### Theorem 14.1, the converse: a null vector of `E_**` is a Jacobi field -/

section Null

variable {X : ℝ → V}

theorem IsUnbrokenGeodesic.prj_deriv (hgeo : IsUnbrokenGeodesic hN γ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : prj hN (γ t) (deriv γ t) = deriv γ t :=
  (prj_eq_self_iff hN (hgeo.2.mem t ht)).2 (hgeo.2.deriv_mem ht)

/-- The Jacobi operator of a tangent field is tangent. -/
theorem prj_jacobiExpr (hgeo : IsUnbrokenGeodesic hN γ)
    (hXT : ∀ t ∈ Icc (0 : ℝ) 1, prj hN (γ t) (X t) = X t) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    prj hN (γ t) (jacobiExpr hN γ X t) = jacobiExpr hN γ X t := by
  have hN' := hgeo.2.mem t ht
  rw [jacobiExpr, map_add, covD, prj_prj]
  congr 1
  rw [prj_eq_self_iff hN hN', curvR_of_mem hN hN']
  exact curvOp_mem hN (hgeo.2.deriv_mem ht)
    ((prj_eq_self_iff hN hN').1 (hXT t (Ioo_subset_Icc_self ht))) (hgeo.2.deriv_mem ht)

/-- On an open interval of `(0, 1)` where the field is smooth, so is its Jacobi operator. -/
theorem contDiffOn_jacobiExpr (hgeo : IsUnbrokenGeodesic hN γ)
    (hXT : ∀ t ∈ Icc (0 : ℝ) 1, prj hN (γ t) (X t) = X t) {O : Set ℝ} (hO : IsOpen O)
    (hO01 : O ⊆ Ioo 0 1) (hX : ContDiffOn ℝ ∞ X O) : ContDiffOn ℝ ∞ (jacobiExpr hN γ X) O := by
  have hγ : ContDiffOn ℝ ∞ γ O := hgeo.2.contDiffOn.mono hO01
  have hP : ContDiffOn ℝ ∞ (fun t => prj hN (γ t)) O :=
    ContDiffOn.prj_comp hN hγ fun t ht => hgeo.2.mem t (hO01 ht)
  have hD : ContDiffOn ℝ ∞ (covD hN γ X) O :=
    hP.clm_apply (hX.deriv_of_isOpen hO (m := ∞) (by simp))
  have hDD : ContDiffOn ℝ ∞ (covD hN γ (covD hN γ X)) O :=
    hP.clm_apply (hD.deriv_of_isOpen hO (m := ∞) (by simp))
  refine hDD.add fun t ht => ?_
  have hn : O ∈ 𝓝 t := hO.mem_nhds ht
  have hγ' : ContDiffOn ℝ ∞ (deriv γ) O := hγ.deriv_of_isOpen hO (m := ∞) (by simp)
  refine (contDiffAt_curvR hN (hγ.contDiffAt hn) (eventually_of_mem hn fun τ hτ =>
    hgeo.2.mem τ (hO01 hτ)) (hγ'.contDiffAt hn) (hX.contDiffAt hn) (hγ'.contDiffAt hn)
    (eventually_of_mem hn fun τ hτ => hgeo.prj_deriv (hO01 hτ))
    (eventually_of_mem hn fun τ hτ => hXT τ (Ioo_subset_Icc_self (hO01 hτ)))).contDiffWithinAt

/-- **Step 1 of Theorem 14.1** (Milnor p. 78): a null vector of `E_**` satisfies the Jacobi
equation off its break points.  Test field `W₂ = φ (D²W₁/dt² + R(V, W₁)V)`, `φ` a bump function
supported where `W₁` is smooth (Milnor: `f (D²W₁/dt² + R(V, W₁)V)` with `f` vanishing at the
break points). -/
theorem jacobiExpr_eq_zero_of_null (hgeo : IsUnbrokenGeodesic hN γ) (hX : X ∈ pathTangent hN γ)
    (hnull : ∀ Y ∈ pathTangent hN γ, secondVariation hN γ X Y = 0) {B : Finset ℝ}
    (hB : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) → ContDiffOn ℝ ∞ X (Icc s t))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxB : x ∉ B) : jacobiExpr hN γ X x = 0 := by
  obtain ⟨s, s', hs, hsx, hxs', hs', hBs⟩ := exists_piece_around B hx.1 hx.2 hxB
  set r := min (x - s) (s' - x) / 2
  have hr : 0 < r := half_pos (lt_min (by linarith) (by linarith))
  have hr1 : r < x - s := by
    have := min_le_left (x - s) (s' - x); simp only [r]; linarith
  have hr2 : r < s' - x := by
    have := min_le_right (x - s) (s' - x); simp only [r]; linarith
  have hball : closedBall x r ⊆ Ioo s s' := fun t ht => by
    rw [mem_closedBall, Real.dist_eq, abs_le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hO01 : Ioo s s' ⊆ Ioo 0 1 := Ioo_subset_Ioo (by linarith) (by linarith)
  have hXs : ContDiffOn ℝ ∞ X (Ioo s s') :=
    (hB s s' hs (hsx.trans hxs') hs' hBs).mono Ioo_subset_Icc_self
  have hJ := contDiffOn_jacobiExpr hgeo hX.2.1 isOpen_Ioo hO01 hXs
  set φ := bumpAt x hr
  have hrOut : φ.rOut = r := rfl
  have hrIn : φ.rIn = r / 2 := rfl
  have hφs : tsupport φ ⊆ Ioo s s' := by rw [φ.tsupport_eq, hrOut]; exact hball
  have hφc : ContDiff ℝ ∞ φ := φ.contDiff (n := ⊤)
  have hφ0 : φ 0 = 0 := by
    rw [← notMem_support, φ.support_eq, hrOut, mem_ball, Real.dist_eq, not_lt, zero_sub,
      abs_neg, abs_of_pos hx.1]
    linarith
  have hφ1 : φ 1 = 0 := by
    rw [← notMem_support, φ.support_eq, hrOut, mem_ball, Real.dist_eq, not_lt,
      abs_of_pos (by linarith : 0 < 1 - x)]
    linarith
  have hφout : ∀ t, t ∉ Ioo s s' → φ t = 0 := fun t ht => by
    by_contra h
    exact ht (hφs (subset_tsupport _ h))
  set Y : ℝ → V := fun t => φ t • jacobiExpr hN γ X t
  have hY : Y ∈ pathTangent hN γ := by
    refine ⟨IsPiecewiseSmooth.of_contDiff (contDiff_smul_of_tsupport_subset hφc isOpen_Ioo hφs hJ)
      zero_le_one, fun t _ => ?_, ?_, ?_⟩
    · by_cases ht : t ∈ Ioo s s'
      · simp only [Y, map_smul, prj_jacobiExpr hgeo hX.2.1 (hO01 ht)]
      · simp [Y, hφout t ht]
    · simp [Y, hφ0]
    · simp [Y, hφ1]
  have h0 := hnull Y hY
  have hj : ∀ t ∈ Ioo (0 : ℝ) 1, ⟪Y t, prj hN (γ t) (jump X t)⟫ = 0 := by
    intro t _
    by_cases ht : t ∈ Ioo s s'
    · rw [jump_eq_zero ((hXs.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)),
        map_zero, inner_zero_right]
    · simp [Y, hφout t ht]
  rw [secondVariation, finsum_mem_eq_zero_of_forall_eq_zero hj, neg_zero, zero_sub,
    neg_eq_zero] at h0
  set g : ℝ → ℝ := fun t => ⟪Y t, jacobiExpr hN γ X t⟫
  have hg : ∀ t, g t = φ t * ‖jacobiExpr hN γ X t‖ ^ 2 := fun t => by
    simp only [g, Y, inner_smul_left, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
  have hgc : Continuous g := by
    have : ContDiff ℝ ∞ (fun t => φ t • ‖jacobiExpr hN γ X t‖ ^ 2) :=
      contDiff_smul_of_tsupport_subset hφc isOpen_Ioo hφs (hJ.norm_sq ℝ)
    exact this.continuous.congr fun t => by rw [hg, smul_eq_mul]
  have hg0 : ∀ t, 0 ≤ g t := fun t => by rw [hg]; exact mul_nonneg φ.nonneg (sq_nonneg _)
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    (.of_forall hg0) (hgc.intervalIntegrable 0 1)).1 h0
  have hgx := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset
    Ioo_subset_Ioc_self hae) isOpen_Ioo hgc.continuousOn continuousOn_const hx
  have hφx : φ x = 1 := φ.one_of_mem_closedBall (mem_closedBall_self (by rw [hrIn]; positivity))
  simp only [Pi.zero_apply, hg, hφx, one_mul, pow_eq_zero_iff two_ne_zero, norm_eq_zero] at hgx
  exact hgx

omit [FiniteDimensional ℝ W] in
/-- The one-sided derivatives of a tangent field along a smooth path in `N` differ by a tangent
vector: the normal parts `II(V, W)` of `W'(t^±)` agree. -/
theorem jump_eq_prj_jump (hgeo : IsUnbrokenGeodesic hN γ)
    (hXT : ∀ t ∈ Icc (0 : ℝ) 1, prj hN (γ t) (X t) = X t) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hXR : DifferentiableWithinAt ℝ X (Ici x) x) (hXL : DifferentiableWithinAt ℝ X (Iic x) x) :
    jump X x = prj hN (γ x) (jump X x) := by
  have hP : ContDiffOn ℝ ∞ (fun t => prj hN (γ t)) (Ioo 0 1) :=
    ContDiffOn.prj_comp hN hgeo.2.contDiffOn fun t ht => hgeo.2.mem t ht
  have hPd : HasDerivAt (fun t => prj hN (γ t)) (deriv (fun t => prj hN (γ t)) x) x :=
    ((hP.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by simp)).hasDerivAt
  have hev : ∀ s : Set ℝ, X =ᶠ[𝓝[s] x] fun t => prj hN (γ t) (X t) := fun s => by
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds hx.1 hx.2)] with t ht
    exact (hXT t (Ioo_subset_Icc_self ht)).symm
  have hside : ∀ s : Set ℝ, UniqueDiffWithinAt ℝ s x → DifferentiableWithinAt ℝ X s x →
      derivWithin X s x = deriv (fun t => prj hN (γ t)) x (X x) +
        prj hN (γ x) (derivWithin X s x) := fun s hs hXs => by
    rw [(hev s).derivWithin_eq (hXT x (Ioo_subset_Icc_self hx)).symm]
    exact (hPd.hasDerivWithinAt.clm_apply hXs.hasDerivWithinAt).derivWithin hs |>.trans
      (by rw [(hev s).derivWithin_eq (hXT x (Ioo_subset_Icc_self hx)).symm])
  rw [jump, map_sub, hside _ (uniqueDiffWithinAt_Ici x) hXR,
    hside _ (uniqueDiffWithinAt_Iic x) hXL]
  simp only [map_add, prj_prj]
  abel

/-- **Step 2 of Theorem 14.1** (Milnor p. 78): for a null vector `W₁` of `E_**`, `DW₁/dt` has no
jumps; hence (the normal parts agreeing) `W₁` is `C¹`.  Test field `W₂ = φ P(Δ_x DW₁/dt)`, `φ` a
bump function at the break point `x` (Milnor: "a field such that `W₂(t_i) = Δ_{t_i} DW₁/dt`"). -/
theorem jump_eq_zero_of_null {p q : V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) (hX : X ∈ pathTangent hN γ)
    (hnull : ∀ Y ∈ pathTangent hN γ, secondVariation hN γ X Y = 0) {B : Finset ℝ}
    (hB : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) → ContDiffOn ℝ ∞ X (Icc s t))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : jump X x = 0 := by
  by_cases hxB : x ∉ B
  · obtain ⟨s, s', hs, hsx, hxs', hs', hBs⟩ := exists_piece_around B hx.1 hx.2 hxB
    exact jump_eq_zero (((hB s s' hs (hsx.trans hxs') hs' hBs).contDiffAt
      (Icc_mem_nhds hsx hxs')).differentiableAt (by simp))
  push Not at hxB
  obtain ⟨s, hs, hsx, hBs⟩ := exists_piece_left B hx.1
  obtain ⟨s', hxs', hs', hBs'⟩ := exists_piece_right B hx.2
  have hL := hB s x hs hsx hx.2.le hBs
  have hR := hB x s' hx.1.le hxs' hs' hBs'
  set r := min (x - s) (s' - x) / 2
  have hr : 0 < r := half_pos (lt_min (by linarith) (by linarith))
  have hr1 : r < x - s := by
    have := min_le_left (x - s) (s' - x); simp only [r]; linarith
  have hr2 : r < s' - x := by
    have := min_le_right (x - s) (s' - x); simp only [r]; linarith
  set Δ := prj hN (γ x) (jump X x)
  have hΔ : prj hN (γ x) Δ = Δ := prj_prj hN _ _
  set φ := bumpAt x hr
  have hrOut : φ.rOut = r := rfl
  have hrIn : φ.rIn = r / 2 := rfl
  have hφc : ContDiff ℝ ∞ φ := φ.contDiff (n := ⊤)
  have hφ0 : φ 0 = 0 := by
    rw [← notMem_support, φ.support_eq, hrOut, mem_ball, Real.dist_eq, not_lt, zero_sub,
      abs_neg, abs_of_pos hx.1]
    linarith
  have hφ1 : φ 1 = 0 := by
    rw [← notMem_support, φ.support_eq, hrOut, mem_ball, Real.dist_eq, not_lt,
      abs_of_pos (by linarith : 0 < 1 - x)]
    linarith
  set Y : ℝ → V := fun t => φ t • prj hN (γ t) Δ
  have hY : Y ∈ pathTangent hN γ := by
    refine ⟨(IsPiecewiseSmooth.of_contDiff hφc zero_le_one).smul
      ((hγ.1.prj_comp hN hγ.2.1).clm_apply
        (IsPiecewiseSmooth.of_contDiff contDiff_const zero_le_one)), fun t _ => ?_, ?_, ?_⟩
    · simp only [Y, map_smul, prj_prj]
    · simp [Y, hφ0]
    · simp [Y, hφ1]
  have h0 := hnull Y hY
  -- the integral term vanishes by Step 1
  have hint : ∫ t in (0 : ℝ)..1, ⟪Y t, covD hN γ (covD hN γ X) t +
      curvR hN (γ t) (deriv γ t) (X t) (deriv γ t)⟫ = 0 := by
    have hfin : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ insert (1 : ℝ) (B : Set ℝ) :=
      (B.finite_toSet.insert 1).countable.ae_notMem _
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_]
    · simp
    filter_upwards [hfin] with t htB ht
    rw [uIoc_of_le zero_le_one] at ht
    rw [mem_insert_iff, not_or] at htB
    have := jacobiExpr_eq_zero_of_null hgeo hX hnull hB ⟨ht.1, lt_of_le_of_ne ht.2 htB.1⟩ htB.2
    rw [jacobiExpr] at this
    rw [this, inner_zero_right]
  -- the jump sum reduces to `‖Δ‖²`
  have hsum : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪Y t, prj hN (γ t) (jump X t)⟫ = ‖Δ‖ ^ 2 := by
    rw [finsum_mem_eq_sum_of_subset (t := {x}) _ ?_ (by simpa using hx), Finset.sum_singleton]
    · have hφx : φ x = 1 :=
        φ.one_of_mem_closedBall (mem_closedBall_self (by rw [hrIn]; positivity))
      simp only [Y, hφx, one_smul, hΔ, real_inner_self_eq_norm_sq, Δ]
    · rintro t ⟨_, hts⟩
      rw [Finset.coe_singleton, mem_singleton_iff]
      by_contra htx
      apply hts
      by_cases htb : t ∈ ball x r
      · rw [Real.ball_eq_Ioo] at htb
        have hdt : DifferentiableAt ℝ X t := by
          rcases lt_or_gt_of_ne htx with h | h
          · exact (hL.contDiffAt (Icc_mem_nhds (by linarith [htb.1]) h)).differentiableAt
              (by simp)
          · exact (hR.contDiffAt (Icc_mem_nhds h (by linarith [htb.2]))).differentiableAt
              (by simp)
        change ⟪Y t, prj hN (γ t) (jump X t)⟫ = 0
        rw [jump_eq_zero hdt, map_zero, inner_zero_right]
      · have : φ t = 0 := by
          rw [← notMem_support, φ.support_eq, hrOut]; exact htb
        change ⟪Y t, prj hN (γ t) (jump X t)⟫ = 0
        simp [Y, this]
  rw [secondVariation, hsum, hint, sub_zero, neg_eq_zero, pow_eq_zero_iff two_ne_zero,
    norm_eq_zero] at h0
  -- the normal part of the jump vanishes too
  have hXR : DifferentiableWithinAt ℝ X (Ici x) x :=
    ((hR.differentiableOn (by simp)) x (left_mem_Icc.2 hxs'.le)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE hxs')
  have hXL : DifferentiableWithinAt ℝ X (Iic x) x :=
    ((hL.differentiableOn (by simp)) x (right_mem_Icc.2 hsx.le)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsLE hsx)
  rw [jump_eq_prj_jump hgeo hX.2.1 hx hXR hXL]
  exact h0

omit [FiniteDimensional ℝ W] in
/-- **The Jacobi equation as a second-order equation in `V`**: for a smooth tangent field `X`
along `γ`, with `P(t) = P_{γ(t)}`, the Jacobi equation at `t` gives
`X'' = -P(P'X') - R(V, X)V + (1 - P)(P''X + 2P'X')` (tangential part from the equation, normal part
from differentiating `X = PX` twice). -/
theorem deriv_deriv_eq_of_jacobiExpr (hgeo : IsUnbrokenGeodesic hN γ)
    (hXT : ∀ t ∈ Icc (0 : ℝ) 1, prj hN (γ t) (X t) = X t) {O : Set ℝ} (hO : IsOpen O)
    (hO01 : O ⊆ Ioo 0 1) (hX : ContDiffOn ℝ ∞ X O) {t : ℝ} (ht : t ∈ O)
    (hJ : jacobiExpr hN γ X t = 0) :
    deriv (deriv X) t = -(prj hN (γ t) (deriv (fun τ => prj hN (γ τ)) t (deriv X t))) -
      curvR hN (γ t) (deriv γ t) (X t) (deriv γ t) +
      (ContinuousLinearMap.id ℝ V - prj hN (γ t))
        (deriv (deriv fun τ => prj hN (γ τ)) t (X t) +
          (2 : ℝ) • deriv (fun τ => prj hN (γ τ)) t (deriv X t)) := by
  set P : ℝ → V →L[ℝ] V := fun τ => prj hN (γ τ)
  have hγO : ContDiffOn ℝ ∞ γ O := hgeo.2.contDiffOn.mono hO01
  have hP : ContDiffOn ℝ ∞ P O := ContDiffOn.prj_comp hN hγO fun τ hτ => hgeo.2.mem τ (hO01 hτ)
  have hP' : ContDiffOn ℝ ∞ (deriv P) O := hP.deriv_of_isOpen hO (m := ∞) (by simp)
  have hX' : ContDiffOn ℝ ∞ (deriv X) O := hX.deriv_of_isOpen hO (m := ∞) (by simp)
  have hPd : ∀ τ ∈ O, DifferentiableAt ℝ P τ := fun τ hτ =>
    (hP.contDiffAt (hO.mem_nhds hτ)).differentiableAt (by simp)
  have hP'd : ∀ τ ∈ O, DifferentiableAt ℝ (deriv P) τ := fun τ hτ =>
    (hP'.contDiffAt (hO.mem_nhds hτ)).differentiableAt (by simp)
  have hXd : ∀ τ ∈ O, DifferentiableAt ℝ X τ := fun τ hτ =>
    (hX.contDiffAt (hO.mem_nhds hτ)).differentiableAt (by simp)
  have hX'd : ∀ τ ∈ O, DifferentiableAt ℝ (deriv X) τ := fun τ hτ =>
    (hX'.contDiffAt (hO.mem_nhds hτ)).differentiableAt (by simp)
  -- `X' = P'X + PX'` on `O`, from `X = PX`
  have hb : ∀ τ ∈ O, deriv X τ = deriv P τ (X τ) + P τ (deriv X τ) := fun τ hτ => by
    have hev : X =ᶠ[𝓝 τ] fun σ => P σ (X σ) := eventually_of_mem (hO.mem_nhds hτ) fun σ hσ =>
      (hXT σ (Ioo_subset_Icc_self (hO01 hσ))).symm
    conv_lhs => rw [hev.deriv_eq]
    rw [deriv_clm_apply (hPd τ hτ) (hXd τ hτ)]
  -- `X'' = P''X + 2P'X' + PX''`
  have hc : deriv (deriv X) t = deriv (deriv P) t (X t) + deriv P t (deriv X t) +
      (deriv P t (deriv X t) + P t (deriv (deriv X) t)) := by
    have hev : deriv X =ᶠ[𝓝 t] fun σ => deriv P σ (X σ) + P σ (deriv X σ) :=
      eventually_of_mem (hO.mem_nhds ht) hb
    conv_lhs => rw [hev.deriv_eq]
    rw [deriv_fun_add ((hP'd t ht).clm_apply (hXd t ht))
      ((hPd t ht).clm_apply (hX'd t ht)), deriv_clm_apply (hP'd t ht) (hXd t ht),
      deriv_clm_apply (hPd t ht) (hX'd t ht)]
  -- the Jacobi equation: `P(P'X' + PX'') + R(V, X)V = 0`
  have he : covD hN γ (covD hN γ X) t = P t (deriv P t (deriv X t) + P t (deriv (deriv X) t)) := by
    change P t (deriv (fun σ => P σ (deriv X σ)) t) = _
    rw [deriv_clm_apply (hPd t ht) (hX'd t ht)]
  rw [jacobiExpr, he, map_add, prj_prj] at hJ
  have hR : curvR hN (γ t) (deriv γ t) (X t) (deriv γ t) =
      -(P t (deriv P t (deriv X t))) - P t (deriv (deriv X) t) := by
    have h := hJ
    change P t (deriv P t (deriv X t)) + P t (deriv (deriv X) t) +
      curvR hN (γ t) (deriv γ t) (X t) (deriv γ t) = 0 at h
    rw [← sub_eq_zero, ← h]
    abel
  have h2 : deriv (deriv P) t (X t) + (2 : ℝ) • deriv P t (deriv X t) =
      deriv (deriv X) t - P t (deriv (deriv X) t) := by
    rw [two_smul]
    nth_rw 1 [hc]
    abel
  rw [h2, hR, sub_apply, ContinuousLinearMap.id_apply, map_sub, prj_prj]
  abel

/-- **Step 3 of Theorem 14.1** (Milnor p. 79: the Jacobi fields on adjacent pieces fit together):
a null vector `W₁` of `E_**` is smooth near every point of `(0, 1)` and satisfies the Jacobi
equation there.  At a former break point `x`, `W₁` is `C¹` (Step 2) and solves on both sides the
equation `W'' = F(t, W, W')` of `Morse.deriv_deriv_eq_of_jacobiExpr`, where `F` is smooth near `x`;
so `W₁'` is differentiable at `x` as well (`Morse.hasDerivAt_of_hasDerivAt_punctured`), and a
solution of a smooth second-order equation is smooth (`Morse.contDiffOn_of_ode`). -/
theorem smooth_near_of_null {p q : V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) (hX : X ∈ pathTangent hN γ)
    (hnull : ∀ Y ∈ pathTangent hN γ, secondVariation hN γ X Y = 0) {B : Finset ℝ}
    (hB : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) → ContDiffOn ℝ ∞ X (Icc s t))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ∃ η > 0, Ioo (x - η) (x + η) ⊆ Ioo 0 1 ∧ ContDiffOn ℝ ∞ X (Ioo (x - η) (x + η)) ∧
      ∀ t ∈ Ioo (x - η) (x + η), jacobiExpr hN γ X t = 0 := by
  obtain ⟨s, hs, hsx, hBs⟩ := exists_piece_left B hx.1
  obtain ⟨s', hxs', hs', hBs'⟩ := exists_piece_right B hx.2
  set r := min (x - s) (s' - x)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have hr1 : r ≤ x - s := min_le_left _ _
  have hr2 : r ≤ s' - x := min_le_right _ _
  have hL : ContDiffOn ℝ ∞ X (Icc (x - r) x) :=
    (hB s x hs hsx hx.2.le hBs).mono (Icc_subset_Icc (by linarith) le_rfl)
  have hR : ContDiffOn ℝ ∞ X (Icc x (x + r)) :=
    (hB x s' hx.1.le hxs' hs' hBs').mono (Icc_subset_Icc le_rfl (by linarith))
  have hnoB : ∀ t ∈ Ioo (x - r) (x + r), t ≠ x → t ∉ B := by
    intro t ht htx htB
    rcases lt_or_gt_of_ne htx with h | h
    · exact hBs t htB ⟨by linarith [ht.1], h⟩
    · exact hBs' t htB ⟨h, by linarith [ht.2]⟩
  have hsm : ∀ t ∈ Ioo (x - r) (x + r), t ≠ x → ∃ O : Set ℝ, IsOpen O ∧ t ∈ O ∧
      O ⊆ Ioo 0 1 ∧ ContDiffOn ℝ ∞ X O := by
    intro t ht htx
    rcases lt_or_gt_of_ne htx with h | h
    · exact ⟨Ioo (x - r) x, isOpen_Ioo, ⟨ht.1, h⟩, Ioo_subset_Ioo (by linarith) (by linarith),
        hL.mono Ioo_subset_Icc_self⟩
    · exact ⟨Ioo x (x + r), isOpen_Ioo, ⟨h, ht.2⟩, Ioo_subset_Ioo (by linarith) (by linarith),
        hR.mono Ioo_subset_Icc_self⟩
  -- `W₁` is differentiable at `x` (Step 2) and `W₁'` is continuous there
  have hjump := jump_eq_zero_of_null hγ hgeo hX hnull hB hx
  have hdx : HasDerivAt X (deriv X x) x := by
    have h1 : HasDerivWithinAt X (derivWithin X (Ici x) x) (Ici x) x :=
      (((hR.differentiableOn (by simp)) x (left_mem_Icc.2 (by linarith))).hasDerivWithinAt
        |>.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE (by linarith))).congr_deriv
        (derivWithin_Ici_eq_of_piece (by linarith) (hR.differentiableOn (by simp))).symm
    have h2 : HasDerivWithinAt X (derivWithin X (Iic x) x) (Iic x) x :=
      (((hL.differentiableOn (by simp)) x (right_mem_Icc.2 (by linarith))).hasDerivWithinAt
        |>.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE (by linarith))).congr_deriv
        (derivWithin_Iic_eq_of_piece (by linarith) (hL.differentiableOn (by simp))).symm
    rw [jump, sub_eq_zero] at hjump
    rw [hjump] at h1
    have := h2.union h1
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at this
    exact this.differentiableAt.hasDerivAt
  have hcont : ContinuousAt (deriv X) x := by
    obtain ⟨hL1, hL2⟩ := IsPiecewiseSmooth.derivWithin_piece (by linarith : x - r < x) hL
    obtain ⟨hR1, hR2⟩ := IsPiecewiseSmooth.derivWithin_piece (by linarith : x < x + r) hR
    have eL := derivWithin_eq_deriv_of_piece (by linarith : x - r < x)
      (right_mem_Icc.2 (by linarith)) hdx.differentiableAt
    have eR := derivWithin_eq_deriv_of_piece (by linarith : x < x + r)
      (left_mem_Icc.2 (by linarith)) hdx.differentiableAt
    refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
    · refine (((hL1.continuousOn x (right_mem_Icc.2 (by linarith))).mono
        Ioc_subset_Icc_self).congr (fun y hy => ?_) eL.symm).mono_of_mem_nhdsWithin
        (Ioc_mem_nhdsLE (by linarith))
      rcases eq_or_lt_of_le hy.2 with rfl | h
      · exact eL.symm
      · exact hL2 ⟨hy.1, h⟩
    · refine (((hR1.continuousOn x (left_mem_Icc.2 (by linarith))).mono
        Ico_subset_Icc_self).congr (fun y hy => ?_) eR.symm).mono_of_mem_nhdsWithin
        (Ico_mem_nhdsGE (by linarith))
      rcases eq_or_lt_of_le hy.1 with rfl | h
      · exact eR.symm
      · exact hR2 ⟨h, hy.2⟩
  -- the chart at `γ(x)` and the smooth right side `F`
  set q : N := ⟨γ x, hgeo.2.mem x hx⟩
  set σ := sliceAt hN q
  have hq : γ x ∈ σ.φ.source := mem_sliceAt_source hN q
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hgeo.2.contDiffAt hx).continuousAt.eventually (σ.φ.open_source.mem_nhds hq))
  set r' := min r δ
  have hr' : 0 < r' := lt_min hr hδ
  set O := Ioo (x - r') (x + r')
  have hxO : x ∈ O := ⟨by linarith, by linarith⟩
  have hOr : O ⊆ Ioo (x - r) (x + r) :=
    Ioo_subset_Ioo (by linarith [min_le_left r δ]) (by linarith [min_le_left r δ])
  have hO01 : O ⊆ Ioo 0 1 := fun t ht => ⟨by linarith [(hOr ht).1], by linarith [(hOr ht).2]⟩
  have hOsrc : ∀ t ∈ O, γ t ∈ σ.φ.source := fun t ht => hball t (by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2, min_le_right r δ])
  set P : ℝ → V →L[ℝ] V := fun τ => prj hN (γ τ)
  set Qd := fderiv ℝ (projRep σ)
  set F : ℝ × V × V → V := fun z => -(P z.1 (deriv P z.1 z.2.2)) -
    (Qd (γ z.1) (P z.1 z.2.1) (Qd (γ z.1) (deriv γ z.1) (deriv γ z.1)) -
      Qd (γ z.1) (deriv γ z.1) (Qd (γ z.1) (P z.1 z.2.1) (deriv γ z.1))) +
    (ContinuousLinearMap.id ℝ V - P z.1) (deriv (deriv P) z.1 z.2.1 + (2 : ℝ) • deriv P z.1 z.2.2)
  have hγO : ContDiffOn ℝ ∞ γ O := hgeo.2.contDiffOn.mono hO01
  have hγ'O : ContDiffOn ℝ ∞ (deriv γ) O := hγO.deriv_of_isOpen isOpen_Ioo (m := ∞) (by simp)
  have hPO : ContDiffOn ℝ ∞ P O := ContDiffOn.prj_comp hN hγO fun t ht => hgeo.2.mem t (hO01 ht)
  have hP'O : ContDiffOn ℝ ∞ (deriv P) O := hPO.deriv_of_isOpen isOpen_Ioo (m := ∞) (by simp)
  have hP''O : ContDiffOn ℝ ∞ (deriv (deriv P)) O :=
    hP'O.deriv_of_isOpen isOpen_Ioo (m := ∞) (by simp)
  have hQO : ContDiffOn ℝ ∞ (fun t => Qd (γ t)) O := fun t ht =>
    (((contDiffAt_projRep σ (q := ⟨γ t, hgeo.2.mem t (hO01 ht)⟩) (hOsrc t ht)).fderiv_right
      (m := ∞) (by simp)).comp t (hγO.contDiffAt (isOpen_Ioo.mem_nhds ht))).contDiffWithinAt
  have hF : ContDiffOn ℝ ∞ F (O ×ˢ univ) := by
    have hmaps : MapsTo (fun z : ℝ × V × V => z.1) (O ×ˢ univ) O := fun z hz => hz.1
    have c1 := hPO.comp contDiffOn_fst hmaps
    have c2 := hP'O.comp contDiffOn_fst hmaps
    have c3 := hP''O.comp contDiffOn_fst hmaps
    have c4 := hQO.comp contDiffOn_fst hmaps
    have c5 := hγ'O.comp contDiffOn_fst hmaps
    have cj : ContDiffOn ℝ ∞ (fun z : ℝ × V × V => z.2.1) (O ×ˢ univ) :=
      contDiff_snd.fst.contDiffOn
    have cj' : ContDiffOn ℝ ∞ (fun z : ℝ × V × V => z.2.2) (O ×ˢ univ) :=
      contDiff_snd.snd.contDiffOn
    exact ((c1.clm_apply (c2.clm_apply cj')).neg.sub
      (((c4.clm_apply (c1.clm_apply cj)).clm_apply ((c4.clm_apply c5).clm_apply c5)).sub
        ((c4.clm_apply c5).clm_apply ((c4.clm_apply (c1.clm_apply cj)).clm_apply c5)))).add
      ((contDiffOn_const.sub c1).clm_apply ((c3.clm_apply cj).add
        (contDiffOn_const.smul (c2.clm_apply cj'))))
  -- off `x`, `W₁'' = F(t, W₁, W₁')`
  have hFX : ∀ t ∈ O, t ≠ x → HasDerivAt (deriv X) (F (t, X t, deriv X t)) t := by
    intro t ht htx
    obtain ⟨O', hO', htO', hO'01, hXO'⟩ := hsm t (hOr ht) htx
    have hJt := jacobiExpr_eq_zero_of_null hgeo hX hnull hB (hO'01 htO') (hnoB t (hOr ht) htx)
    have h1 := deriv_deriv_eq_of_jacobiExpr hgeo hX.2.1 hO' hO'01 hXO' htO' hJt
    have hd2 : HasDerivAt (deriv X) (deriv (deriv X) t) t :=
      (((hXO'.deriv_of_isOpen hO' (m := ∞) (by simp)).contDiffAt
        (hO'.mem_nhds htO')).differentiableAt (by simp)).hasDerivAt
    refine hd2.congr_deriv ?_
    rw [h1]
    have hN' := hgeo.2.mem t (hO01 ht)
    have hXt : prj hN (γ t) (X t) = X t := hX.2.1 t (Ioo_subset_Icc_self (hO01 ht))
    have hcurv : curvR hN (γ t) (deriv γ t) (X t) (deriv γ t) =
        Qd (γ t) (P t (X t)) (Qd (γ t) (deriv γ t) (deriv γ t)) -
          Qd (γ t) (deriv γ t) (Qd (γ t) (P t (X t)) (deriv γ t)) := by
      change curvR hN (γ t) (deriv γ t) (X t) (deriv γ t) =
        Qd (γ t) (prj hN (γ t) (X t)) (Qd (γ t) (deriv γ t) (deriv γ t)) -
          Qd (γ t) (deriv γ t) (Qd (γ t) (prj hN (γ t) (X t)) (deriv γ t))
      rw [hXt, curvR_of_mem hN hN', curvOp_apply]
      simp only [secondFundForm]
      rw [dN_tanProj_eq_fderiv hN σ (q := ⟨γ t, hN'⟩) (hOsrc t ht)
          ((prj_eq_self_iff hN hN').1 hXt),
        dN_tanProj_eq_fderiv hN σ (q := ⟨γ t, hN'⟩) (hOsrc t ht) (hgeo.2.deriv_mem (hO01 ht))]
    rw [hcurv]
  -- at `x`, by continuity
  have hFx : HasDerivAt (deriv X) (F (x, X x, deriv X x)) x := by
    have hz : ContinuousAt (fun t => (t, X t, deriv X t)) x :=
      continuousAt_id.prodMk (hdx.continuousAt.prodMk hcont)
    have hFc : ContinuousAt F (x, X x, deriv X x) :=
      hF.continuousOn.continuousAt (prod_mem_nhds (isOpen_Ioo.mem_nhds hxO) univ_mem)
    exact hasDerivAt_of_hasDerivAt_punctured hr' hcont
      (ContinuousAt.comp (f := fun t => (t, X t, deriv X t)) hFc hz) fun t ht htx => hFX t ht htx
  have hdX : ∀ t ∈ O, HasDerivAt X (deriv X t) t := by
    intro t ht
    rcases eq_or_ne t x with rfl | htx
    · exact hdx
    obtain ⟨O', hO', htO', -, hXO'⟩ := hsm t (hOr ht) htx
    exact ((hXO'.contDiffAt (hO'.mem_nhds htO')).differentiableAt (by simp)).hasDerivAt
  have hXO : ContDiffOn ℝ ∞ X O := contDiffOn_of_ode isOpen_Ioo hF hdX fun t ht => by
    rcases eq_or_ne t x with rfl | htx
    · exact hFx
    · exact hFX t ht htx
  refine ⟨r', hr', hO01, hXO, fun t ht => ?_⟩
  rcases eq_or_ne t x with rfl | htx
  · -- the Jacobi equation at `x`, by continuity
    have hJc : ContinuousAt (jacobiExpr hN γ X) t :=
      (contDiffOn_jacobiExpr hgeo hX.2.1 isOpen_Ioo hO01 hXO).continuousOn.continuousAt
        (isOpen_Ioo.mem_nhds ht)
    have hlim : Tendsto (jacobiExpr hN γ X) (𝓝[≠] t) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ht), self_mem_nhdsWithin]
        with τ hτ hτt
      obtain ⟨O', -, hτO', hO'01, -⟩ := hsm τ (hOr hτ) hτt
      exact (jacobiExpr_eq_zero_of_null hgeo hX hnull hB (hO'01 hτO')
        (hnoB τ (hOr hτ) hτt)).symm
    exact tendsto_nhds_unique (hJc.tendsto.mono_left nhdsWithin_le_nhds) hlim
  · obtain ⟨O', -, htO', hO'01, -⟩ := hsm t (hOr ht) htx
    exact jacobiExpr_eq_zero_of_null hgeo hX hnull hB (hO'01 htO') (hnoB t (hOr ht) htx)

end Null

/-- **Theorem 14.1** (Milnor p. 78): a vector field `W₁ ∈ TΩ_γ` belongs to the null space of the
Hessian `E_**` of the energy at the geodesic `γ` if and only if it is a Jacobi field (necessarily
vanishing at the ends).  So `E_**` is degenerate iff the end points are conjugate along `γ`, and
its null space is the space of Jacobi fields vanishing at the ends. -/
theorem theorem_14_1 {p q : V} (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ)
    (X : pathTangent hN γ) :
    (∀ Y : pathTangent hN γ, energyHessian hN hγ X Y = 0) ↔ IsJacobiField hN γ X := by
  constructor
  · intro h
    have hnull : ∀ Y ∈ pathTangent hN γ, secondVariation hN γ X Y = 0 := fun Y hY => by
      have := h ⟨Y, hY⟩
      rw [energyHessian_apply] at this
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    obtain ⟨-, -, B, hB⟩ := X.2.1
    refine ⟨fun t ht => ?_, X.2.2.1, fun t ht => ?_⟩
    · rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · obtain ⟨s', h0s', hs', hBs'⟩ := exists_piece_right B zero_lt_one
        refine ((hB 0 s' le_rfl h0s' hs' hBs') 0 (left_mem_Icc.2 h0s'.le)).mono_of_mem_nhdsWithin
          ?_
        exact mem_nhdsWithin.2 ⟨Iio s', isOpen_Iio, h0s', fun y hy => ⟨hy.2.1, hy.1.le⟩⟩
      rcases eq_or_lt_of_le ht.2 with rfl | ht1
      · obtain ⟨s, hs, hs1, hBs⟩ := exists_piece_left B zero_lt_one
        refine ((hB s 1 hs hs1 le_rfl hBs) 1 (right_mem_Icc.2 hs1.le)).mono_of_mem_nhdsWithin ?_
        exact mem_nhdsWithin.2 ⟨Ioi s, isOpen_Ioi, hs1, fun y hy => ⟨hy.1.le, hy.2.2⟩⟩
      · obtain ⟨η, hη, -, hsm, -⟩ := smooth_near_of_null hγ hgeo X.2 hnull hB ⟨ht0, ht1⟩
        exact (hsm.contDiffAt (Ioo_mem_nhds (by linarith) (by linarith))).contDiffWithinAt
    · obtain ⟨η, hη, -, -, hJ⟩ := smooth_near_of_null hγ hgeo X.2 hnull hB ht
      exact hJ t ⟨by linarith, by linarith⟩
  · intro hJ Y
    rw [energyHessian_apply, hJ.secondVariation_eq_zero, mul_zero]

end Morse
