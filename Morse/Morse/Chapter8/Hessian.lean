import Morse.Chapter8.SecondVariation

/-!
Milnor, *Morse Theory*, §13, pp. 74–76: the Hessian `E_**` of the energy at a geodesic as a
symmetric bilinear form on `TΩ_γ` (Corollary 13.4), for a submanifold `N ⊆ ℝᴷ` with the induced
metric.

# The Hessian of the energy

## Milnor's text, paraphrased

* (p. 74) `E_** : TΩ_γ × TΩ_γ → ℝ`, the Hessian of `E` at a geodesic `γ`, is defined through
  2-parameter variations (see `Morse/Chapter8/SecondVariation.lean`).
* **Corollary 13.4** (p. 76): `E_**(W₁, W₂)` is a well defined symmetric bilinear function of
  `W₁, W₂`: the formula of 13.1 shows that it is well defined and bilinear, and symmetry follows
  from `∂²E/∂u₁∂u₂ = ∂²E/∂u₂∂u₁`.
* **Lemma 13.6** (p. 76): if `γ` is a minimal geodesic from `p` to `q`, `E_**` is positive
  semi-definite, hence its index is `0`: `E(ᾱ(u)) ≥ E(γ)` forces `d²E(ᾱ(u))/du² (0) ≥ 0`, which is
  `E_**(W, W)` by Remark 13.5.

## How the Hessian `E_**` on `TΩ_γ` is formalized

`Ω` has no manifold structure (as in Milnor's §§11–15).  `TΩ_γ` is the vector space
`Morse.pathTangent hN γ` of piecewise smooth tangent fields along `γ` vanishing at the ends, and
`E_**` is the bilinear form `Morse.energyHessian hN hγ : LinearMap.BilinForm ℝ (pathTangent hN γ)`
*defined by Milnor's formula*: `E_**(W₁, W₂) = 2 secondVariation γ W₁ W₂`.  The theorems relating
it to the energy are:

* `Morse.hasDerivAt_energyHessian` (Theorem 13.1): for **every** 2-parameter variation `ᾱ` of the
  geodesic `γ` with variation fields `W₁, W₂`, the iterated derivative
  `∂/∂u₁ (∂E(ᾱ(u₁, u₂))/∂u₂ (u₁, 0))` at `u₁ = 0` exists and equals `E_**(W₁, W₂)`;
* `Morse.exists_variation_two` (Lemma 11.A): **every** pair `W₁, W₂ ∈ TΩ_γ` arises in this way;
* `Morse.hasDerivAt_deriv_energy` (Remark 13.5): `d²E(ᾱ(u))/du² (0) = E_**(W, W)` for every
  1-parameter variation with field `W`.

So Milnor's definition through variations is well defined and agrees with `Morse.energyHessian`;
**Corollary 13.4** is `Morse.energyHessian_isSymm` together with the bilinearity built into
`Morse.energyHessian`; **Lemma 13.6** is `Morse.lemma_13_6`.  **Proposition 13.A of the
exposition** (not in Milnor), the integral form
`½ E_**(W₁, W₂) = ∫₀¹ (⟨DW₁/dt, DW₂/dt⟩ - ⟨R(V, W₁)V, W₂⟩) dt`, is
`Morse.secondVariation_eq_hessForm`, `Morse.energyHessian_eq_integral`.

## What Milnor leaves implicit

* **Symmetry** (Corollary 13.4) is derived in the book from `∂²E/∂u₁∂u₂ = ∂²E/∂u₂∂u₁`, which
  needs `E ∘ ᾱ` to be `C²` near `(0, 0)` — not addressed in the book.  Here symmetry comes from the
  integral form (one integration by parts on each piece, the boundary terms cancelling the jump
  terms) and the symmetry `⟨R(V, W₁)V, W₂⟩ = ⟨R(V, W₂)V, W₁⟩` (Lemma 9.3 (4), here from the Gauss
  equation and the symmetry of the second fundamental form, `Morse.inner_curvR_comm`).
* **Bilinearity** in `W₁` is not visible in Milnor's formula without knowing that `W ↦ Δ_t DW/dt`
  and `W ↦ D²W/dt²` are linear on piecewise smooth fields (one-sided differentiability at the
  break points); here it also comes from the integral form, linear off the break points.
* **Lemma 13.6**: only the minimality of `γ` is used, not completeness; `E(γ) = L(γ)² ≤ L(ω)² ≤
  E(ω)` uses the constant speed of a geodesic and the equality case of Schwarz's inequality
  (`Morse.energy_le_of_isMinimalPath`).  The step "a minimum forces a nonnegative second
  derivative" needs only the existence of the second derivative at `0`: if it were negative, `0`
  would also be a local maximum (second derivative test), the function would be locally constant,
  and its second derivative would vanish.
-/

open Set Filter Topology Function MeasureTheory Metric
open scoped ContDiff Manifold RealInnerProductSpace Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Continuity of the curvature term along a path -/

omit [FiniteDimensional ℝ W] in
/-- Along a path in `N`, `τ ↦ R(a(τ), b(τ))c(τ)` is continuous where `γ, a, b, c` are, provided
`a(τ), b(τ)` are tangent: near `γ(τ₀)`, `II_x(v, ·) = d(projRep σ)_x(v)` for tangent `v`. -/
theorem continuousWithinAt_curvR {γ a b c : ℝ → V} {s : Set ℝ} {τ₀ : ℝ} (hτ₀ : τ₀ ∈ s)
    (hγ : ContinuousWithinAt γ s τ₀) (hγN : ∀ τ ∈ s, γ τ ∈ N) (ha : ContinuousWithinAt a s τ₀)
    (hb : ContinuousWithinAt b s τ₀) (hc : ContinuousWithinAt c s τ₀)
    (haT : ∀ τ ∈ s, prj hN (γ τ) (a τ) = a τ) (hbT : ∀ τ ∈ s, prj hN (γ τ) (b τ) = b τ) :
    ContinuousWithinAt (fun τ => curvR hN (γ τ) (a τ) (b τ) (c τ)) s τ₀ := by
  set q : N := ⟨γ τ₀, hγN τ₀ hτ₀⟩
  set σ := sliceAt hN q
  have hq : γ τ₀ ∈ σ.φ.source := mem_sliceAt_source hN q
  set Qd := fderiv ℝ (projRep σ)
  have hQd : ContinuousAt Qd (γ τ₀) :=
    ((contDiffAt_projRep σ (q := q) hq).fderiv_right (m := 0) (by simp)).continuousAt
  have hQγ : ContinuousWithinAt (fun τ => Qd (γ τ)) s τ₀ := hQd.comp_continuousWithinAt hγ
  have h1 : ContinuousWithinAt (fun τ => Qd (γ τ) (b τ) (Qd (γ τ) (a τ) (c τ)) -
      Qd (γ τ) (a τ) (Qd (γ τ) (b τ) (c τ))) s τ₀ :=
    ((hQγ.clm_apply hb).clm_apply ((hQγ.clm_apply ha).clm_apply hc)).sub
      ((hQγ.clm_apply ha).clm_apply ((hQγ.clm_apply hb).clm_apply hc))
  refine h1.congr_of_eventuallyEq_of_mem ?_ hτ₀
  have hsrc : ∀ᶠ τ in 𝓝[s] τ₀, γ τ ∈ σ.φ.source :=
    hγ.preimage_mem_nhdsWithin (σ.φ.open_source.mem_nhds hq)
  filter_upwards [hsrc, self_mem_nhdsWithin] with τ h1 h2
  have hN' := hγN τ h2
  have ha' : a τ ∈ tangentSubspace hN ⟨γ τ, hN'⟩ := (prj_eq_self_iff hN hN').1 (haT τ h2)
  have hb' : b τ ∈ tangentSubspace hN ⟨γ τ, hN'⟩ := (prj_eq_self_iff hN hN').1 (hbT τ h2)
  rw [curvR_of_mem hN hN', curvOp_apply]
  simp only [secondFundForm]
  rw [dN_tanProj_eq_fderiv hN σ (q := ⟨γ τ, hN'⟩) h1 ha',
    dN_tanProj_eq_fderiv hN σ (q := ⟨γ τ, hN'⟩) h1 hb']

/-! ### Proposition 13.A: the Hessian as an integral -/

/-- **The Hessian in integral form** (half of `E_**`):
`∫₀¹ (⟨DW₁/dt, DW₂/dt⟩ - ⟨R(V, W₁)V, W₂⟩) dt`. -/
def hessForm (γ X₁ X₂ : ℝ → V) : ℝ :=
  ∫ t in (0 : ℝ)..1, (⟪covD hN γ X₁ t, covD hN γ X₂ t⟫ -
    ⟪curvR hN (γ t) (deriv γ t) (X₁ t) (deriv γ t), X₂ t⟫)

section Pieces

variable {γ X₁ X₂ : ℝ → V} {s t : ℝ}

/-- The data of a piece `[s, t]` on which `γ` and the fields `X₁, X₂` are smooth: continuous
representatives on `[s, t]` of the terms of the second variation. -/
structure PieceData (γ X₁ X₂ : ℝ → V) (s t : ℝ) : Prop where
  lt : s < t
  hγ : ContDiffOn ℝ ∞ γ (Icc s t)
  hX₁ : ContDiffOn ℝ ∞ X₁ (Icc s t)
  hX₂ : ContDiffOn ℝ ∞ X₂ (Icc s t)
  mem : ∀ τ ∈ Icc s t, γ τ ∈ N
  tan₁ : ∀ τ ∈ Icc s t, prj hN (γ τ) (X₁ τ) = X₁ τ
  tan₂ : ∀ τ ∈ Icc s t, prj hN (γ τ) (X₂ τ) = X₂ τ

namespace PieceData

variable {hN}

/-- `DX/dt` on the piece, with the derivative within `[s, t]`. -/
def D (_h : PieceData hN γ X₁ X₂ s t) (X : ℝ → V) (τ : ℝ) : V :=
  prj hN (γ τ) (derivWithin X (Icc s t) τ)

omit [FiniteDimensional ℝ W] in
theorem contDiffOn_prj (h : PieceData hN γ X₁ X₂ s t) :
    ContDiffOn ℝ ∞ (fun τ => prj hN (γ τ)) (Icc s t) :=
  ContDiffOn.prj_comp hN h.hγ h.mem

omit [FiniteDimensional ℝ W] in
theorem contDiffOn_D (h : PieceData hN γ X₁ X₂ s t) {X : ℝ → V}
    (hX : ContDiffOn ℝ ∞ X (Icc s t)) : ContDiffOn ℝ ∞ (h.D X) (Icc s t) :=
  h.contDiffOn_prj.clm_apply (IsPiecewiseSmooth.derivWithin_piece h.lt hX).1

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem D_eq (h : PieceData hN γ X₁ X₂ s t) {X : ℝ → V} (hX : ContDiffOn ℝ ∞ X (Icc s t))
    {τ : ℝ} (hτ : τ ∈ Ioo s t) : covD hN γ X τ = h.D X τ := by
  rw [covD, D, (IsPiecewiseSmooth.derivWithin_piece h.lt hX).2 hτ]

omit [FiniteDimensional ℝ W] in
theorem covD_covD_eq (h : PieceData hN γ X₁ X₂ s t) {X : ℝ → V}
    (hX : ContDiffOn ℝ ∞ X (Icc s t)) {τ : ℝ} (hτ : τ ∈ Ioo s t) :
    covD hN γ (covD hN γ X) τ = prj hN (γ τ) (derivWithin (h.D X) (Icc s t) τ) := by
  have hev : covD hN γ X =ᶠ[𝓝 τ] h.D X := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with x hx
    exact h.D_eq hX hx
  rw [covD, hev.deriv_eq, (IsPiecewiseSmooth.derivWithin_piece h.lt (h.contDiffOn_D hX)).2 hτ]

/-- The velocity within the piece is tangent. -/
theorem prj_derivWithin (h : PieceData hN γ X₁ X₂ s t) {τ : ℝ} (hτ : τ ∈ Icc s t) :
    prj hN (γ τ) (derivWithin γ (Icc s t) τ) = derivWithin γ (Icc s t) τ :=
  (prj_eq_self_iff hN (h.mem τ hτ)).2 (hasDerivWithinAt_mem_tangentSubspace hN
    ((h.hγ.differentiableOn (by simp)) τ hτ).hasDerivWithinAt (uniqueDiffOn_Icc h.lt τ hτ)
    h.mem hτ)

theorem continuousOn_curv (h : PieceData hN γ X₁ X₂ s t) :
    ContinuousOn (fun τ => curvR hN (γ τ) (derivWithin γ (Icc s t) τ) (X₁ τ)
      (derivWithin γ (Icc s t) τ)) (Icc s t) := fun τ hτ => by
  have hV := (IsPiecewiseSmooth.derivWithin_piece h.lt h.hγ).1.continuousOn
  exact continuousWithinAt_curvR hN hτ (h.hγ.continuousOn τ hτ) h.mem (hV τ hτ)
    (h.hX₁.continuousOn τ hτ) (hV τ hτ) (fun τ hτ => h.prj_derivWithin hτ) h.tan₁

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curv_eq (h : PieceData hN γ X₁ X₂ s t) {τ : ℝ} (hτ : τ ∈ Ioo s t) :
    curvR hN (γ τ) (deriv γ τ) (X₁ τ) (deriv γ τ) =
      curvR hN (γ τ) (derivWithin γ (Icc s t) τ) (X₁ τ) (derivWithin γ (Icc s t) τ) := by
  rw [(IsPiecewiseSmooth.derivWithin_piece h.lt h.hγ).2 hτ]

omit [FiniteDimensional ℝ W] in
/-- **Integration by parts on a piece** (Lemma 8.3): `∫ₛᵗ (⟨DX₂, DX₁⟩ + ⟨X₂, D²X₁⟩) =
⟨X₂, DX₁⟩(t⁻) - ⟨X₂, DX₁⟩(s⁺)`. -/
theorem integral_eq (h : PieceData hN γ X₁ X₂ s t) :
    ∫ τ in s..t, (⟪covD hN γ X₂ τ, covD hN γ X₁ τ⟫ + ⟪X₂ τ, covD hN γ (covD hN γ X₁) τ⟫) =
      ⟪X₂ t, prj hN (γ t) (derivWithin X₁ (Iic t) t)⟫ -
        ⟪X₂ s, prj hN (γ s) (derivWithin X₁ (Ici s) s)⟫ := by
  have hD₁ := h.contDiffOn_D h.hX₁
  have hD₂ := h.contDiffOn_D h.hX₂
  have hP := h.contDiffOn_prj
  obtain ⟨hX₂', hX₂e⟩ := IsPiecewiseSmooth.derivWithin_piece h.lt h.hX₂
  obtain ⟨hD₁', hD₁e⟩ := IsPiecewiseSmooth.derivWithin_piece h.lt hD₁
  have hfc : ContinuousOn (fun τ => ⟪X₂ τ, h.D X₁ τ⟫) (Icc s t) :=
    h.hX₂.continuousOn.inner hD₁.continuousOn
  have hderiv : ∀ τ ∈ Ioo s t, HasDerivAt (fun τ => ⟪X₂ τ, h.D X₁ τ⟫)
      (⟪covD hN γ X₂ τ, covD hN γ X₁ τ⟫ + ⟪X₂ τ, covD hN γ (covD hN γ X₁) τ⟫) τ := by
    intro τ hτ
    have hn : Icc s t ∈ 𝓝 τ := Icc_mem_nhds hτ.1 hτ.2
    have e1 : HasDerivAt X₂ (derivWithin X₂ (Icc s t) τ) τ := by
      rw [← hX₂e hτ]
      exact ((h.hX₂.contDiffAt hn).differentiableAt (by simp)).hasDerivAt
    have e2 : HasDerivAt (h.D X₁) (derivWithin (h.D X₁) (Icc s t) τ) τ := by
      rw [← hD₁e hτ]
      exact ((hD₁.contDiffAt hn).differentiableAt (by simp)).hasDerivAt
    refine (e1.inner ℝ e2).congr_deriv ?_
    have hτ' := Ioo_subset_Icc_self hτ
    rw [h.D_eq h.hX₂ hτ, h.D_eq h.hX₁ hτ, h.covD_covD_eq h.hX₁ hτ, D, D,
      inner_prj_right_of_eq hN (h.tan₂ τ hτ'), inner_prj_left, prj_prj]
    ring
  have hint : IntervalIntegrable (fun τ => ⟪covD hN γ X₂ τ, covD hN γ X₁ τ⟫ +
      ⟪X₂ τ, covD hN γ (covD hN γ X₁) τ⟫) volume s t := by
    refine ((hD₂.continuousOn.inner hD₁.continuousOn).add (h.hX₂.continuousOn.inner
      (hP.continuousOn.clm_apply hD₁'.continuousOn))).intervalIntegrable_of_Icc h.lt.le
      |>.congr_uIoo fun τ hτ => ?_
    rw [uIoo_of_le h.lt.le] at hτ
    simp only [Pi.add_apply]
    rw [h.D_eq h.hX₂ hτ, h.D_eq h.hX₁ hτ, h.covD_covD_eq h.hX₁ hτ]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h.lt.le hfc hderiv hint, D, D,
    derivWithin_Iic_eq_of_piece h.lt (h.hX₁.differentiableOn (by simp)),
    derivWithin_Ici_eq_of_piece h.lt (h.hX₁.differentiableOn (by simp))]

end PieceData

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- A common subdivision for a path and two fields along it. -/
theorem exists_pieceData {p q : V} (hγ : γ ∈ pathSpace N p q) (hX₁ : X₁ ∈ pathTangent hN γ)
    (hX₂ : X₂ ∈ pathTangent hN γ) : ∃ B : Finset ℝ, ∀ s t, 0 ≤ s → s < t → t ≤ 1 →
      (∀ x ∈ B, x ∉ Ioo s t) → PieceData hN γ X₁ X₂ s t := by
  classical
  obtain ⟨⟨-, -, B₀, hB₀⟩, hγN, -, -⟩ := hγ
  obtain ⟨⟨-, -, B₁, hB₁⟩, hT₁, -, -⟩ := hX₁
  obtain ⟨⟨-, -, B₂, hB₂⟩, hT₂, -, -⟩ := hX₂
  refine ⟨B₀ ∪ B₁ ∪ B₂, fun s t hs hst ht hB => ?_⟩
  have hsub : Icc s t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hs ht
  exact ⟨hst, hB₀ s t hs hst ht fun x hx => hB x (by simp [hx]),
    hB₁ s t hs hst ht fun x hx => hB x (by simp [hx]),
    hB₂ s t hs hst ht fun x hx => hB x (by simp [hx]),
    fun τ hτ => hγN τ (hsub hτ), fun τ hτ => hT₁ τ (hsub hτ), fun τ hτ => hT₂ τ (hsub hτ)⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- A piecewise smooth function is differentiable off a finite set. -/
theorem IsPiecewiseSmooth.ae_differentiableAt {X : ℝ → V} (hX : IsPiecewiseSmooth X 0 1) :
    ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Ι (0 : ℝ) 1 → DifferentiableAt ℝ X τ := by
  obtain ⟨-, -, B, hB⟩ := hX
  have hfin : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∉ insert (1 : ℝ) (B : Set ℝ) :=
    (B.finite_toSet.insert 1).countable.ae_notMem _
  filter_upwards [hfin] with τ hτB hτ
  rw [uIoc_of_le zero_le_one] at hτ
  rw [mem_insert_iff, not_or] at hτB
  obtain ⟨s, s', hs, hsτ, hτs', hs', hBs⟩ :=
    exists_piece_around B hτ.1 (lt_of_le_of_ne hτ.2 hτB.1) hτB.2
  exact ((hB s s' hs (hsτ.trans hτs') hs' hBs).contDiffAt
    (Icc_mem_nhds hsτ hτs')).differentiableAt (by simp)

/-- **Proposition 13.A of the exposition** (not in Milnor): for `W₁, W₂ ∈ TΩ_γ`,
`−Σ_t ⟨W₂, Δ_t DW₁/dt⟩ − ∫ ⟨W₂, D²W₁/dt² + R(V, W₁)V⟩ = ∫ (⟨DW₁/dt, DW₂/dt⟩ − ⟨R(V, W₁)V, W₂⟩)`:
one integration by parts on each piece (Lemma 8.3), whose boundary terms telescope into the jump
terms, `W₂` vanishing at the ends.  `γ` need not be a geodesic. -/
theorem secondVariation_eq_hessForm {p q : V} (hγ : γ ∈ pathSpace N p q)
    (hX₁ : X₁ ∈ pathTangent hN γ) (hX₂ : X₂ ∈ pathTangent hN γ) :
    secondVariation hN γ X₁ X₂ = hessForm hN γ X₁ X₂ := by
  obtain ⟨B, hB⟩ := exists_pieceData hN hγ hX₁ hX₂
  have hint : ∀ {f : ℝ → ℝ}, (∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) →
      ∃ G : ℝ → ℝ, ContinuousOn G (Icc s t) ∧ EqOn f G (Ioo s t)) →
      ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → IntervalIntegrable f volume a b :=
    fun hf a b ha hab hb => intervalIntegrable_of_piecewise hf ha hab hb
  set I₁ : ℝ → ℝ := fun τ => ⟪covD hN γ X₂ τ, covD hN γ X₁ τ⟫
  set I₂ : ℝ → ℝ := fun τ => ⟪X₂ τ, covD hN γ (covD hN γ X₁) τ⟫
  set I₃ : ℝ → ℝ := fun τ => ⟪X₂ τ, curvR hN (γ τ) (deriv γ τ) (X₁ τ) (deriv γ τ)⟫
  have hI₁ := hint (f := I₁) fun s t hs hst ht hBs => by
    have h := hB s t hs hst ht hBs
    exact ⟨_, (h.contDiffOn_D h.hX₂).continuousOn.inner (h.contDiffOn_D h.hX₁).continuousOn,
      fun τ hτ => by simp only [I₁, h.D_eq h.hX₂ hτ, h.D_eq h.hX₁ hτ]⟩
  have hI₂ := hint (f := I₂) fun s t hs hst ht hBs => by
    have h := hB s t hs hst ht hBs
    exact ⟨_, h.hX₂.continuousOn.inner (h.contDiffOn_prj.continuousOn.clm_apply
      (IsPiecewiseSmooth.derivWithin_piece h.lt (h.contDiffOn_D h.hX₁)).1.continuousOn),
      fun τ hτ => by simp only [I₂, h.covD_covD_eq h.hX₁ hτ]⟩
  have hI₃ := hint (f := I₃) fun s t hs hst ht hBs => by
    have h := hB s t hs hst ht hBs
    exact ⟨_, h.hX₂.continuousOn.inner h.continuousOn_curv,
      fun τ hτ => by simp only [I₃, h.curv_eq hτ]⟩
  -- the integration by parts, glued over the pieces
  have hparts := integral_eq_of_piecewise (B := B) (lo := 0) (hi := 1) (g := fun τ => I₁ τ + I₂ τ)
    (Fl := fun x => ⟪X₂ x, prj hN (γ x) (derivWithin X₁ (Iic x) x)⟫)
    (Fr := fun x => ⟪X₂ x, prj hN (γ x) (derivWithin X₁ (Ici x) x)⟫)
    (fun a b ha hab hb => (hI₁ a b ha hab hb).add (hI₂ a b ha hab hb))
    (fun s t hs hst ht hBs => (hB s t hs hst ht hBs).integral_eq) 0 1 le_rfl zero_lt_one le_rfl
  simp only [hX₂.2.2.1, hX₂.2.2.2, inner_zero_left, sub_zero, zero_sub] at hparts
  rw [intervalIntegral.integral_add (hI₁ 0 1 le_rfl zero_le_one le_rfl)
    (hI₂ 0 1 le_rfl zero_le_one le_rfl)] at hparts
  have hsum : ∑ᶠ τ ∈ Ioo (0 : ℝ) 1, ⟪X₂ τ, prj hN (γ τ) (jump X₁ τ)⟫ =
      ∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, (⟪X₂ x, prj hN (γ x) (derivWithin X₁ (Ici x) x)⟫ -
        ⟪X₂ x, prj hN (γ x) (derivWithin X₁ (Iic x) x)⟫) := by
    rw [finsum_mem_Ioo_eq_sum fun x hx hxB => ?_]
    · exact Finset.sum_congr rfl fun x _ => by rw [jump, map_sub, inner_sub_right]
    obtain ⟨s, s', hs, hsx, hxs', hs', hBs⟩ := exists_piece_around B hx.1 hx.2 hxB
    rw [jump_eq_zero (((hB s s' hs (hsx.trans hxs') hs' hBs).hX₁.contDiffAt
      (Icc_mem_nhds hsx hxs')).differentiableAt (by simp)), map_zero, inner_zero_right]
  have hsv : secondVariation hN γ X₁ X₂ = -(∑ᶠ τ ∈ Ioo (0 : ℝ) 1,
      ⟪X₂ τ, prj hN (γ τ) (jump X₁ τ)⟫) -
        ((∫ τ in (0 : ℝ)..1, I₂ τ) + ∫ τ in (0 : ℝ)..1, I₃ τ) := by
    rw [secondVariation, ← intervalIntegral.integral_add (hI₂ 0 1 le_rfl zero_le_one le_rfl)
      (hI₃ 0 1 le_rfl zero_le_one le_rfl)]
    congr 2
    funext τ
    simp only [I₂, I₃, inner_add_right]
  have hhf : hessForm hN γ X₁ X₂ = (∫ τ in (0 : ℝ)..1, I₁ τ) - ∫ τ in (0 : ℝ)..1, I₃ τ := by
    rw [hessForm, ← intervalIntegral.integral_sub (hI₁ 0 1 le_rfl zero_le_one le_rfl)
      (hI₃ 0 1 le_rfl zero_le_one le_rfl)]
    congr 1
    funext τ
    simp only [I₁, I₃, real_inner_comm]
  rw [hsv, hhf, hsum]
  linarith

/-! ### Corollary 13.4: `E_**` is a symmetric bilinear form on `TΩ_γ` -/

/-- **The symmetry of the curvature term** (Lemma 9.3 (4) with `X = Z = V`), from the Gauss
equation: `⟨R(v, w₁)v, w₂⟩ = ⟨R(v, w₂)v, w₁⟩` for tangent vectors. -/
theorem inner_curvR_comm {x v w₁ w₂ : V} (hx : x ∈ N) (hv : v ∈ tangentSubspace hN ⟨x, hx⟩)
    (h₁ : w₁ ∈ tangentSubspace hN ⟨x, hx⟩) (h₂ : w₂ ∈ tangentSubspace hN ⟨x, hx⟩) :
    ⟪curvR hN x v w₁ v, w₂⟫ = ⟪curvR hN x v w₂ v, w₁⟫ := by
  rw [curvR_of_mem hN hx, curvR_of_mem hN hx, inner_curvOp, inner_curvOp,
    secondFundForm_comm hN h₁ h₂, secondFundForm_comm hN h₁ hv, secondFundForm_comm hN h₂ hv,
    real_inner_comm (secondFundForm hN _ v w₂)]

/-- The integrand of `hessForm` is integrable. -/
theorem intervalIntegrable_hessIntegrand {p q : V} (hγ : γ ∈ pathSpace N p q)
    (hX₁ : X₁ ∈ pathTangent hN γ) (hX₂ : X₂ ∈ pathTangent hN γ) :
    IntervalIntegrable (fun t => ⟪covD hN γ X₁ t, covD hN γ X₂ t⟫ -
      ⟪curvR hN (γ t) (deriv γ t) (X₁ t) (deriv γ t), X₂ t⟫) volume 0 1 := by
  obtain ⟨B, hB⟩ := exists_pieceData hN hγ hX₁ hX₂
  refine intervalIntegrable_of_piecewise (B := B) (fun s t hs hst ht hBs => ?_) le_rfl
    zero_le_one le_rfl
  have h := hB s t hs hst ht hBs
  exact ⟨_, ((h.contDiffOn_D h.hX₁).continuousOn.inner (h.contDiffOn_D h.hX₂).continuousOn).sub
    (h.continuousOn_curv.inner h.hX₂.continuousOn), fun τ hτ => by
      simp only [Pi.sub_apply, h.D_eq h.hX₁ hτ, h.D_eq h.hX₂ hτ, h.curv_eq hτ]⟩

/-- **Symmetry of the Hessian** (Corollary 13.4; here from the integral form and Lemma 9.3 (4)). -/
theorem hessForm_comm {p q : V} (hγ : γ ∈ pathSpace N p q) (hX₁ : X₁ ∈ pathTangent hN γ)
    (hX₂ : X₂ ∈ pathTangent hN γ) : hessForm hN γ X₁ X₂ = hessForm hN γ X₂ X₁ := by
  rw [hessForm, hessForm]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ τ ∂(volume : Measure ℝ), τ ≠ 1 := (countable_singleton 1).ae_notMem _
  filter_upwards [hγ.1.ae_differentiableAt, hne] with τ hd h1 hτ
  have hτ' : τ ∈ Ioo (0 : ℝ) 1 := by
    rw [uIoc_of_le zero_le_one] at hτ
    exact ⟨hτ.1, lt_of_le_of_ne hτ.2 h1⟩
  have hτN : γ τ ∈ N := hγ.2.1 τ (Ioo_subset_Icc_self hτ')
  have hV : deriv γ τ ∈ tangentSubspace hN ⟨γ τ, hτN⟩ :=
    hasDerivAt_mem_tangentSubspace hN (hd hτ).hasDerivAt
      (eventually_of_mem (Ioo_mem_nhds hτ'.1 hτ'.2) fun x hx =>
        hγ.2.1 x (Ioo_subset_Icc_self hx))
  rw [real_inner_comm (covD hN γ X₁ τ), inner_curvR_comm hN hτN hV
    ((prj_eq_self_iff hN hτN).1 (hX₁.2.1 τ (Ioo_subset_Icc_self hτ')))
    ((prj_eq_self_iff hN hτN).1 (hX₂.2.1 τ (Ioo_subset_Icc_self hτ')))]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem covD_add {Y Y' : ℝ → V} {τ : ℝ} (hY : DifferentiableAt ℝ Y τ)
    (hY' : DifferentiableAt ℝ Y' τ) : covD hN γ (Y + Y') τ = covD hN γ Y τ + covD hN γ Y' τ := by
  rw [covD, covD, covD, ← map_add]
  congr 1
  exact deriv_add hY hY'

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem covD_smul {Y : ℝ → V} {τ : ℝ} (c : ℝ) (hY : DifferentiableAt ℝ Y τ) :
    covD hN γ (c • Y) τ = c • covD hN γ Y τ := by
  rw [covD, covD, ← map_smul]
  congr 1
  exact deriv_const_smul c hY

/-- **Linearity of the Hessian in the second variable** (Corollary 13.4). -/
theorem hessForm_add_right {p q : V} (hγ : γ ∈ pathSpace N p q) {Y Y' : ℝ → V}
    (hX₁ : X₁ ∈ pathTangent hN γ) (hY : Y ∈ pathTangent hN γ) (hY' : Y' ∈ pathTangent hN γ) :
    hessForm hN γ X₁ (Y + Y') = hessForm hN γ X₁ Y + hessForm hN γ X₁ Y' := by
  rw [hessForm, hessForm, hessForm, ← intervalIntegral.integral_add
    (intervalIntegrable_hessIntegrand hN hγ hX₁ hY)
    (intervalIntegrable_hessIntegrand hN hγ hX₁ hY')]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hY.1.ae_differentiableAt, hY'.1.ae_differentiableAt] with τ h1 h2 hτ
  rw [covD_add hN (h1 hτ) (h2 hτ), Pi.add_apply, inner_add_right, inner_add_right]
  ring

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem hessForm_smul_right {Y : ℝ → V} (c : ℝ)
    (hY : Y ∈ pathTangent hN γ) :
    hessForm hN γ X₁ (c • Y) = c * hessForm hN γ X₁ Y := by
  rw [hessForm, hessForm, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hY.1.ae_differentiableAt] with τ h1 hτ
  rw [covD_smul hN c (h1 hτ), Pi.smul_apply, inner_smul_right, inner_smul_right]
  ring

end Pieces

/-- **Milnor's Hessian** `E_** : TΩ_γ × TΩ_γ → ℝ` (p. 74), as a bilinear form on the vector space
`TΩ_γ` (`Morse.pathTangent`), defined by the right side of Theorem 13.1 (times 2):
`E_**(W₁, W₂) = 2 secondVariation γ W₁ W₂`.  That this is Milnor's `∂²E/∂u₁∂u₂ (0, 0)` for every
2-parameter variation with variation fields `W₁, W₂` is Theorem 13.1 (`Morse.second_variation`,
`Morse.hasDerivAt_hessian`); that every pair `(W₁, W₂)` arises is Lemma 11.A
(`Morse.exists_variation_two`).  Bilinearity (Corollary 13.4) comes from the integral form,
Proposition 13.A (`Morse.secondVariation_eq_hessForm`); only `γ ∈ Ω` is needed for it. -/
def energyHessian {γ : ℝ → V} {p q : V} (hγ : γ ∈ pathSpace N p q) :
    LinearMap.BilinForm ℝ (pathTangent hN γ) :=
  LinearMap.mk₂ ℝ (fun X₁ X₂ => 2 * secondVariation hN γ X₁ X₂)
    (fun X₁ X₁' X₂ => by
      rw [secondVariation_eq_hessForm hN hγ (X₁ + X₁').2 X₂.2,
        secondVariation_eq_hessForm hN hγ X₁.2 X₂.2, secondVariation_eq_hessForm hN hγ X₁'.2 X₂.2,
        hessForm_comm hN hγ (X₁ + X₁').2 X₂.2, hessForm_comm hN hγ X₁.2 X₂.2,
        hessForm_comm hN hγ X₁'.2 X₂.2, Submodule.coe_add,
        hessForm_add_right hN hγ X₂.2 X₁.2 X₁'.2]
      ring)
    (fun c X₁ X₂ => by
      rw [secondVariation_eq_hessForm hN hγ (c • X₁).2 X₂.2,
        secondVariation_eq_hessForm hN hγ X₁.2 X₂.2, hessForm_comm hN hγ (c • X₁).2 X₂.2,
        hessForm_comm hN hγ X₁.2 X₂.2, Submodule.coe_smul, hessForm_smul_right hN c X₁.2,
        smul_eq_mul]
      ring)
    (fun X₁ X₂ X₂' => by
      rw [secondVariation_eq_hessForm hN hγ X₁.2 (X₂ + X₂').2,
        secondVariation_eq_hessForm hN hγ X₁.2 X₂.2, secondVariation_eq_hessForm hN hγ X₁.2 X₂'.2,
        Submodule.coe_add, hessForm_add_right hN hγ X₁.2 X₂.2 X₂'.2]
      ring)
    (fun c X₁ X₂ => by
      rw [secondVariation_eq_hessForm hN hγ X₁.2 (c • X₂).2,
        secondVariation_eq_hessForm hN hγ X₁.2 X₂.2, Submodule.coe_smul,
        hessForm_smul_right hN c X₂.2, smul_eq_mul]
      ring)

theorem energyHessian_apply {γ : ℝ → V} {p q : V} (hγ : γ ∈ pathSpace N p q)
    (X₁ X₂ : pathTangent hN γ) : energyHessian hN hγ X₁ X₂ = 2 * secondVariation hN γ X₁ X₂ := rfl

/-- **Corollary 13.4** (Milnor p. 76): `E_**` is a symmetric bilinear form on `TΩ_γ`.  (Milnor
deduces the symmetry from `∂²E/∂u₁∂u₂ = ∂²E/∂u₂∂u₁`; here it comes from Proposition 13.A and
Lemma 9.3 (4).) -/
theorem energyHessian_isSymm {γ : ℝ → V} {p q : V} (hγ : γ ∈ pathSpace N p q) :
    (energyHessian hN hγ).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_def]
  intro X₁ X₂
  rw [energyHessian_apply, energyHessian_apply, secondVariation_eq_hessForm hN hγ X₁.2 X₂.2,
    secondVariation_eq_hessForm hN hγ X₂.2 X₁.2, hessForm_comm hN hγ X₁.2 X₂.2]

/-- **Proposition 13.A, for `E_**`**:
`½ E_**(W₁, W₂) = ∫₀¹ (⟨DW₁/dt, DW₂/dt⟩ - ⟨R(V, W₁)V, W₂⟩) dt`. -/
theorem energyHessian_eq_integral {γ : ℝ → V} {p q : V} (hγ : γ ∈ pathSpace N p q)
    (X₁ X₂ : pathTangent hN γ) :
    energyHessian hN hγ X₁ X₂ = 2 * ∫ t in (0 : ℝ)..1, (⟪covD hN γ X₁ t, covD hN γ X₂ t⟫ -
      ⟪curvR hN (γ t) (deriv γ t) ((X₁ : ℝ → V) t) (deriv γ t), (X₂ : ℝ → V) t⟫) := by
  rw [energyHessian_apply, secondVariation_eq_hessForm hN hγ X₁.2 X₂.2, hessForm]

/-! ### Theorem 13.1 and Remark 13.5 in terms of `E_**` -/

section Variations

variable {γ : ℝ → V}

/-- The variation field `∂α/∂u₁ (0, 0, ·)` of a 2-parameter variation of `γ` lies in `TΩ_γ`. -/
theorem IsVariation.partial₁_mem {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ}
    (hα : IsVariation N U α B) (hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) :
    (fun t => deriv (fun u₁ => α (u₁, 0) t) 0) ∈ pathTangent hN γ :=
  mem_pathTangent_congr hN (fun t ht => hαγ t ht)
    ((hα.comp (φ := fun u₁ => (u₁, (0 : ℝ))) (contDiff_id.prodMk contDiff_const)
      hα.zero_mem).varField_mem hN)

/-- The variation field `∂α/∂u₂ (0, 0, ·)` of a 2-parameter variation of `γ` lies in `TΩ_γ`. -/
theorem IsVariation.partial₂_mem {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ}
    (hα : IsVariation N U α B) (hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) :
    (fun t => deriv (fun u₂ => α (0, u₂) t) 0) ∈ pathTangent hN γ :=
  mem_pathTangent_congr hN (fun t ht => hαγ t ht)
    ((hα.comp (φ := fun u₂ => ((0 : ℝ), u₂)) (contDiff_const.prodMk contDiff_id)
      hα.zero_mem).varField_mem hN)

/-- **Theorem 13.1, with Milnor's `E_**`**: for every 2-parameter variation `α` of a geodesic
`γ ∈ Ω`, `∂²E(ᾱ(u₁, u₂))/∂u₁∂u₂ (0, 0) = E_**(W₁, W₂)`, `Wᵢ = ∂α/∂uᵢ (0, 0)`. -/
theorem hasDerivAt_energyHessian {p q : V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ}
    (hα : IsVariation N U α B) (hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) :
    HasDerivAt (fun u₁ => deriv (fun u₂ => energy (α (u₁, u₂)) 0 1) 0)
      (energyHessian hN hγ ⟨_, hα.partial₁_mem hN hαγ⟩ ⟨_, hα.partial₂_mem hN hαγ⟩) 0 :=
  second_variation hN hgeo hα hαγ

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `secondVariation` only depends on the fields on `[0, 1]`. -/
theorem secondVariation_congr {X₁ X₂ X₁' X₂' : ℝ → V}
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, X₁ t = X₁' t) (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, X₂ t = X₂' t) :
    secondVariation hN γ X₁ X₂ = secondVariation hN γ X₁' X₂' := by
  have hev : ∀ t ∈ Ioo (0 : ℝ) 1, X₁ =ᶠ[𝓝 t] X₁' := fun t ht => by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact h₁ x (Ioo_subset_Icc_self hx)
  have hev' : ∀ t ∈ Ioo (0 : ℝ) 1, covD hN γ X₁ =ᶠ[𝓝 t] covD hN γ X₁' := fun t ht => by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    rw [covD, covD, (hev x hx).deriv_eq]
  have hs : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X₂ t, prj hN (γ t) (jump X₁ t)⟫ =
      ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X₂' t, prj hN (γ t) (jump X₁' t)⟫ :=
    finsum_mem_congr rfl fun t ht => by
      rw [h₂ t (Ioo_subset_Icc_self ht), jump_congr (hev t ht)]
  have hi : ∫ t in (0 : ℝ)..1,
      ⟪X₂ t, covD hN γ (covD hN γ X₁) t + curvR hN (γ t) (deriv γ t) (X₁ t) (deriv γ t)⟫ =
      ∫ t in (0 : ℝ)..1,
      ⟪X₂' t, covD hN γ (covD hN γ X₁') t + curvR hN (γ t) (deriv γ t) (X₁' t) (deriv γ t)⟫ :=
    intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => by
      rw [h₂ t (Ioo_subset_Icc_self ht), h₁ t (Ioo_subset_Icc_self ht), covD, covD,
        (hev' t ht).deriv_eq]
  rw [secondVariation, secondVariation, hs, hi]

/-- **Remark 13.5, with Milnor's `E_**`** (p. 76): for a 1-parameter variation `ᾱ` of a geodesic
`γ ∈ Ω` with variation field `W`, `d²E(ᾱ(u))/du² (0) = E_**(W, W)`. -/
theorem hasDerivAt_deriv_energy {p q : V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) {U : Set ℝ} {α : ℝ → ℝ → V} {B : Finset ℝ}
    (hα : IsVariation N U α B) (hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) :
    HasDerivAt (deriv fun u => energy (α u) 0 1)
      (energyHessian hN hγ ⟨_, mem_pathTangent_congr hN hαγ (hα.varField_mem hN)⟩
        ⟨_, mem_pathTangent_congr hN hαγ (hα.varField_mem hN)⟩) 0 :=
  remark_13_5 hN hgeo hα hαγ

/-! ### Lemma 13.6: at a minimal geodesic `E_**` is positive semi-definite -/

variable (N) in
/-- A path of `Ω(N; p, q)` whose length is at most that of every path of `Ω(N; p, q)` (Milnor's
minimal geodesics, p. 61, when it is a geodesic). -/
def IsMinimalPath (c : ℝ → V) (p q : V) : Prop :=
  c ∈ pathSpace N p q ∧ ∀ c' ∈ pathSpace N p q, pathLength c 0 1 ≤ pathLength c' 0 1

omit [FiniteDimensional ℝ V] in
/-- The energy only depends on the path on `[0, 1]`. -/
theorem energy_congr {c c' : ℝ → V} (h : ∀ t ∈ Icc (0 : ℝ) 1, c t = c' t) :
    energy c 0 1 = energy c' 0 1 := by
  refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => ?_
  have hev : c =ᶠ[𝓝 t] c' := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact h x (Ioo_subset_Icc_self hx)
  simp only [hev.deriv_eq]

/-- **The energy at a minimal geodesic** (the inequality of Lemma 12.1, Milnor p. 70, for which
completeness is not needed): `E(γ) = L(γ)² ≤ L(ω)² ≤ E(ω)` for every `ω ∈ Ω(N; p, q)`. -/
theorem energy_le_of_isMinimalPath {p q : V} (hmin : IsMinimalPath N γ p q)
    (hgeo : IsUnbrokenGeodesic hN γ) {c : ℝ → V} (hc : c ∈ pathSpace N p q) :
    energy γ 0 1 ≤ energy c 0 1 := by
  have hγs := hmin.1.1
  have hk : ∃ k, ∀ t ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ γ t → ‖deriv γ t‖ = k :=
    ⟨‖deriv γ (1 / 2)‖, fun t ht _ => hgeo.2.norm_deriv_eq isPreconnected_Ioo ht
      ⟨by norm_num, by norm_num⟩⟩
  have h1 := (pathLength_sq_eq_energy_iff hγs).2 hk
  have h2 := pathLength_sq_le_energy hc.1
  have h3 := hmin.2 c hc
  have h4 := hγs.isAdmissible.pathLength_nonneg
  simp only [sub_zero, one_mul] at h1 h2
  nlinarith

/-- **Lemma 13.6** (Milnor p. 76): if `γ` is a minimal geodesic from `p` to `q`, then `E_**` is
positive semi-definite on `TΩ_γ` (hence its index is `0`).  Proof: for a variation with field `W`
(Lemma 11.A), `u ↦ E(ᾱ(u))` has a minimum at `0`; if its second derivative `E_**(W, W)` (Remark
13.5) were negative, `0` would also be a local maximum (second derivative test), so the function
would be locally constant, with second derivative `0`. -/
theorem lemma_13_6 {p q : V} (hmin : IsMinimalPath N γ p q) (hgeo : IsUnbrokenGeodesic hN γ)
    (X : pathTangent hN γ) : 0 ≤ energyHessian hN hmin.1 X X := by
  by_contra hneg
  push Not at hneg
  obtain ⟨ε, hε, B, hα, h0, hd⟩ := exists_variation_one hN hmin.1 X.2
  set α : ℝ → ℝ → V := fun u t => exp hN (γ t) (u • (X : ℝ → V) t)
  have hαγ : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t := h0
  set f : ℝ → ℝ := fun u => energy (α u) 0 1
  -- `f` has a local minimum at `0`
  have hmin' : IsLocalMin f 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)]
      with u hu
    have hpath := hα.mem_pathSpace hu
    rw [show α 0 0 = p from (hαγ 0 ⟨le_rfl, zero_le_one⟩).trans hmin.1.2.2.1,
      show α 0 1 = q from (hαγ 1 ⟨zero_le_one, le_rfl⟩).trans hmin.1.2.2.2] at hpath
    calc f 0 = energy γ 0 1 := energy_congr hαγ
      _ ≤ f u := energy_le_of_isMinimalPath hN hmin hgeo hpath
  -- its second derivative at `0` is `E_**(W, W) < 0`
  have hdd := hasDerivAt_deriv_energy hN hmin.1 hgeo hα hαγ
  have hW : energyHessian hN hmin.1 ⟨_, mem_pathTangent_congr hN hαγ (hα.varField_mem hN)⟩
      ⟨_, mem_pathTangent_congr hN hαγ (hα.varField_mem hN)⟩ = energyHessian hN hmin.1 X X := by
    rw [energyHessian_apply, energyHessian_apply]
    exact congrArg _ (secondVariation_congr hN hd hd)
  rw [hW] at hdd
  have hf : HasDerivAt f _ 0 := hα.hasDerivAt_energy hN hα.zero_mem
  have hmax : IsLocalMax f 0 := isLocalMax_of_deriv_deriv_neg (by rw [hdd.deriv]; exact hneg)
    hmin'.deriv_eq_zero hf.continuousAt
  have hconst : f =ᶠ[𝓝 0] fun _ => f 0 := by
    filter_upwards [hmin', hmax] with u h1 h2
    exact le_antisymm h2 h1
  have h0' : deriv (deriv f) 0 = 0 := by
    rw [hconst.deriv.deriv_eq]
    simp
  rw [hdd.deriv] at h0'
  exact hneg.ne h0'

end Variations

end Morse
