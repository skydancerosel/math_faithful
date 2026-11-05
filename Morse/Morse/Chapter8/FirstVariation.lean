import Morse.Chapter8.Energy
import Morse.Chapter7.Exp

/-!
Milnor, *Morse Theory*, §12, pp. 71–72 (Theorem 12.2), and §11, p. 68 (variations built from the
exponential map), for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# The first variation formula, and variations with given variation fields

## Milnor's text, paraphrased

* **Theorem 12.2** (p. 71, first variation formula): for a variation `ᾱ` of `ω` with variation
  field `W`, `½ dE(ᾱ(u))/du (0) = -Σ_t ⟨W_t, Δ_t V⟩ - ∫₀¹ ⟨W_t, A_t⟩ dt`, where `V = dω/dt` is the
  velocity, `A = D/dt V` the acceleration and `Δ_t V = V_{t⁺} - V_{t⁻}` the jump of the velocity,
  non-zero for finitely many `t ∈ (0, 1)`.  Proof (pp. 71–72): differentiate under the integral
  sign, `∂/∂u ⟨∂α/∂t, ∂α/∂t⟩ = 2 ⟨D/∂u ∂α/∂t, ∂α/∂t⟩` (Lemma 8.3), replace `D/∂u ∂α/∂t` by
  `D/∂t ∂α/∂u` ("by Lemma 8.5"), integrate by parts on each `[t_{i-1}, t_i]`, add up, and use
  `∂α/∂u = 0` at `t = 0, 1`.
* (p. 68) For `W ∈ TΩ_ω`, `ᾱ(u)(t) = exp_{ω(t)}(u W_t)` is a variation with variation field `W`.

## In the embedded setting

* `Morse.covD hN ω X = P_ω (dX/dt)`, the covariant derivative along the path (Chapter 6's
  `Morse.covDeriv`, `Morse.covD_eq_covDeriv`); `Morse.accel hN ω = D/dt (dω/dt)`.
* `Morse.firstVariation hN ω W` is Milnor's right side `-Σ_t ⟨W_t, Δ_t V⟩ - ∫₀¹ ⟨W_t, A_t⟩ dt`
  (half of `dE_ω(W)`); the sum `Σ_t` is the `finsum` over `t ∈ (0, 1)`, equal to the finite sum
  over any finite set containing the break points (`Morse.finsum_jump_eq_sum`).
* **Theorem 12.2**: `Morse.first_variation`.  **Formula (12.2′) at every `u`**:
  `Morse.IsVariation.hasDerivAt_energy` — `u ↦ E(α_u)` is differentiable at every `u` of the
  parameter set, with derivative `2 firstVariation hN α_u (∂α/∂u (u, ·))`.
* **Lemma 11.A of the exposition** (every finite family of tangent vectors is realized by one
  variation): `Morse.exists_variation`, for a piecewise smooth family `Λ(t) : P → T_{ω(t)}N` of
  linear maps vanishing at `t = 0, 1`, with `α(u, t) = exp_{ω(t)}(Λ(t) u)` on a ball `‖u‖ < ε`
  and `∂α/∂u (0, t) = Λ(t)`; `Morse.exists_variation_one` (one field, Milnor's formula) and
  `Morse.exists_variation_two` (two fields, for §13).

## What Milnor leaves implicit

* **The reference "Lemma 8.5"** (p. 71) should be **Lemma 8.7**: 8.5 is the definition of a
  symmetric connection, while the interchange `D/∂u ∂α/∂t = D/∂t ∂α/∂u` is Lemma 8.7.  In the
  embedded setting it is the symmetry of the mixed partial derivatives `∂²α/∂u∂t` on the closed
  strips, including their edges (`Morse.pdU_pdT`), followed by the projection.
* **The formula at every `u`.**  Milnor states it at `u = 0`, but his proof gives it at every `u`
  (formula (12.2′) of the exposition), and §13 differentiates it in a second parameter.
* **Differentiation under the integral sign** needs the smoothness of `α` on the *closed* strips
  and a domination bound from the compactness of `[u₀ - δ, u₀ + δ] × [t_{i-1}, t_i]`
  (`Morse.hasDerivAt_integral_of_piecewise`).
* **The telescoping.**  The boundary terms `⟨∂α/∂u, ∂α/∂t⟩(t_i^±)` of the integrations by parts
  combine into `-⟨∂α/∂u, Δ_{t_i} ∂α/∂t⟩` because `∂α/∂u` is continuous in `t`
  (`Morse.integral_eq_of_piecewise`).
* **`exp_{ω(t)}(u W_t)` is defined only near the zero section** (Lemma 10.2): `ε` must be chosen
  uniformly, by the compactness of `ω([0, 1])` and a bound for `‖W‖`.  Completeness of `N` is not
  needed.  Smoothness on the strips comes from the local smoothness of `exp`
  (`Morse.exists_isOpen_exp`), and `∂α/∂u (0, t) = W_t` from `d(exp_q)₀ = id`
  (`Morse.hasFDerivAt_exp_zero`).
-/

open Set Filter Topology Function MeasureTheory Metric
open scoped ContDiff Manifold RealInnerProductSpace Interval

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Covariant derivative and acceleration along a path -/

/-- **The covariant derivative of a vector field `X` along a path `ω`** (Milnor p. 46, for the
induced metric; `Morse.covDeriv` of Chapter 6): `DX/dt = P_{ω(t)}(X'(t))`, meaningful at the
points where `X` is differentiable. -/
def covD (c X : ℝ → V) (t : ℝ) : V := prj hN (c t) (deriv X t)

/-- **The acceleration** `A_t = D/dt (dω/dt)` of a path (Milnor p. 71), meaningful off the break
points. -/
def accel (c : ℝ → V) (t : ℝ) : V := covD hN c (deriv c) t

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- For a curve in `N`, `covD` is the covariant derivative `Morse.covDeriv` of Chapter 6. -/
theorem covD_eq_covDeriv (c : ℝ → N) (X : ℝ → V) (t : ℝ) :
    covD hN (fun t => (c t : V)) X t = covDeriv hN c X t := by
  rw [covD, covDeriv, prj_of_mem hN (c t).2]

/-- **The first variation of the energy** (half of `dE`) at the path `ω` in the direction of the
vector field `W` along `ω` (Milnor's Theorem 12.2): `-Σ_t ⟨W_t, Δ_t V⟩ - ∫₀¹ ⟨W_t, A_t⟩ dt`, the
sum over the finitely many `t ∈ (0, 1)` at which the velocity `V` jumps, `A` the acceleration. -/
def firstVariation (c X : ℝ → V) : ℝ :=
  -(∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X t, jump c t⟫) - ∫ t in (0 : ℝ)..1, ⟪X t, accel hN c t⟫

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The first variation only depends on the field on `[0, 1]`. -/
theorem firstVariation_congr_field {c X X' : ℝ → V} (h : ∀ t ∈ Icc (0 : ℝ) 1, X t = X' t) :
    firstVariation hN c X = firstVariation hN c X' := by
  have h1 : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X t, jump c t⟫ = ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X' t, jump c t⟫ :=
    finsum_mem_congr rfl fun t ht => by rw [h t (Ioo_subset_Icc_self ht)]
  have h2 : ∫ t in (0 : ℝ)..1, ⟪X t, accel hN c t⟫ = ∫ t in (0 : ℝ)..1, ⟪X' t, accel hN c t⟫ :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le zero_le_one] at ht
      simp only [h t ht]
  rw [firstVariation, firstVariation, h1, h2]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `TΩ_ω` only depends on the path on `[0, 1]`. -/
theorem mem_pathTangent_congr {c c' X : ℝ → V} (h : ∀ t ∈ Icc (0 : ℝ) 1, c t = c' t)
    (hX : X ∈ pathTangent hN c) : X ∈ pathTangent hN c' :=
  ⟨hX.1, fun t ht => by rw [← h t ht]; exact hX.2.1 t ht, hX.2.2⟩

/-! ### A variation on one strip -/

section Piece

variable {U : Set ℝ} {α : ℝ → ℝ → V} {s t : ℝ}

/-- The variation as a function on `ℝ²`. -/
def unc (α : ℝ → ℝ → V) (p : ℝ × ℝ) : V := α p.1 p.2

omit [FiniteDimensional ℝ V] in
theorem piece_deriv (hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t)) {u τ : ℝ} (hu : u ∈ U)
    (hτ : τ ∈ Ioo s t) : deriv (α u) τ = pdT (U ×ˢ Icc s t) (unc α) (u, τ) :=
  deriv_eq_pdT (F := unc α) (hF.differentiableOn (by simp)) hu hτ

omit [FiniteDimensional ℝ V] in
theorem piece_varDeriv (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t)) {u τ : ℝ}
    (hu : u ∈ U) (hτ : τ ∈ Icc s t) :
    deriv (fun v => α v τ) u = pdU (U ×ˢ Icc s t) (unc α) (u, τ) :=
  deriv_eq_pdU hU (F := unc α) (hF.differentiableOn (by simp)) hu hτ

omit [FiniteDimensional ℝ V] in
theorem piece_deriv_deriv (hU : IsOpen U) (hst : s < t)
    (hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t)) {u τ : ℝ} (hu : u ∈ U) (hτ : τ ∈ Ioo s t) :
    deriv (deriv (α u)) τ = pdT (U ×ˢ Icc s t) (pdT (U ×ˢ Icc s t) (unc α)) (u, τ) := by
  have hev : deriv (α u) =ᶠ[𝓝 τ] fun τ => pdT (U ×ˢ Icc s t) (unc α) (u, τ) := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with x hx
    exact piece_deriv hF hu hx
  rw [hev.deriv_eq]
  exact deriv_eq_pdT ((contDiffOn_pdT hU hst hF).differentiableOn (by simp)) hu hτ

omit [FiniteDimensional ℝ V] in
theorem piece_deriv_varDeriv (hU : IsOpen U) (hst : s < t)
    (hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t)) {u τ : ℝ} (hu : u ∈ U) (hτ : τ ∈ Ioo s t) :
    deriv (fun τ => deriv (fun v => α v τ) u) τ =
      pdT (U ×ˢ Icc s t) (pdU (U ×ˢ Icc s t) (unc α)) (u, τ) := by
  have hev : (fun τ => deriv (fun v => α v τ) u) =ᶠ[𝓝 τ]
      fun τ => pdU (U ×ˢ Icc s t) (unc α) (u, τ) := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with x hx
    exact piece_varDeriv hU hF hu (Ioo_subset_Icc_self hx)
  rw [hev.deriv_eq]
  exact deriv_eq_pdT ((contDiffOn_pdU hU hst hF).differentiableOn (by simp)) hu hτ

omit [FiniteDimensional ℝ V] in
theorem piece_derivWithin_Ici (hst : s < t) (hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t)) {u : ℝ}
    (hu : u ∈ U) : derivWithin (α u) (Ici s) s = pdT (U ×ˢ Icc s t) (unc α) (u, s) :=
  derivWithin_Ici_eq_pdT hst (F := unc α) (hF.differentiableOn (by simp)) hu

omit [FiniteDimensional ℝ V] in
theorem piece_derivWithin_Iic (hst : s < t) (hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t)) {u : ℝ}
    (hu : u ∈ U) : derivWithin (α u) (Iic t) t = pdT (U ×ˢ Icc s t) (unc α) (u, t) :=
  derivWithin_Iic_eq_pdT hst (F := unc α) (hF.differentiableOn (by simp)) hu

omit [FiniteDimensional ℝ V] in
theorem piece_differentiableAt (hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t)) {u τ : ℝ}
    (hu : u ∈ U) (hτ : τ ∈ Ioo s t) : DifferentiableAt ℝ (α u) τ :=
  (hasDerivAt_pdT (F := unc α) (hF.differentiableOn (by simp)) hu hτ).differentiableAt

omit [FiniteDimensional ℝ V] in
theorem piece_contDiffOn_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℝ}
    (hu : u ∈ U) {G : ℝ × ℝ → E} (hG : ContDiffOn ℝ ∞ G (U ×ˢ Icc s t)) :
    ContDiffOn ℝ ∞ (fun τ => G (u, τ)) (Icc s t) :=
  hG.comp (contDiffOn_const.prodMk contDiffOn_id) fun _ hτ => mk_mem_prod hu hτ

end Piece

/-! ### The first variation formula -/

section FirstVariation

variable {U : Set ℝ} {α : ℝ → ℝ → V} {B : Finset ℝ}

omit [FiniteDimensional ℝ V] in
/-- Off the break points, each path of a variation is differentiable. -/
theorem IsVariation.differentiableAt (hα : IsVariation N U α B) {u : ℝ} (hu : u ∈ U) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hxB : x ∉ B) : DifferentiableAt ℝ (α u) x := by
  obtain ⟨s, s', hs, hsx, hxs', hs', hB⟩ := exists_piece_around B hx.1 hx.2 hxB
  exact piece_differentiableAt (hα.smooth s s' hs (hsx.trans hxs') hs' hB) hu ⟨hsx, hxs'⟩

/-- A sum over `t ∈ (0, 1)` of terms vanishing off `B` is the finite sum over `B ∩ (0, 1)`. -/
theorem finsum_mem_Ioo_eq_sum {f : ℝ → ℝ} {B : Finset ℝ}
    (hf : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ B → f x = 0) :
    ∑ᶠ t ∈ Ioo (0 : ℝ) 1, f t = ∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, f x := by
  classical
  refine finsum_mem_eq_sum_of_subset _ (fun x ⟨hx, hxs⟩ => ?_) (fun x hx => ?_)
  · rw [Finset.coe_filter]
    refine ⟨?_, hx⟩
    by_contra hxB
    exact hxs (hf x hx hxB)
  · rw [Finset.coe_filter] at hx
    exact hx.2

omit [FiniteDimensional ℝ V] in
/-- The jump sum over `(0, 1)` is the finite sum over the break points. -/
theorem finsum_jump_eq_sum {c X : ℝ → V} {B : Finset ℝ}
    (hc : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ B → DifferentiableAt ℝ c x) :
    ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X t, jump c t⟫ = ∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, ⟪X x, jump c x⟫ :=
  finsum_mem_Ioo_eq_sum fun x hx hxB => by rw [jump_eq_zero (hc x hx hxB), inner_zero_right]

omit [FiniteDimensional ℝ V] in
/-- Off the break points, the variation field is differentiable in `t`. -/
theorem IsVariation.differentiableAt_varDeriv (hα : IsVariation N U α B) {u : ℝ} (hu : u ∈ U)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxB : x ∉ B) :
    DifferentiableAt ℝ (fun t => deriv (fun v => α v t) u) x := by
  obtain ⟨s, s', hs, hsx, hxs', hs', hB⟩ := exists_piece_around B hx.1 hx.2 hxB
  have hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s s') := hα.smooth s s' hs (hsx.trans hxs') hs' hB
  have h1 := ((piece_contDiffOn_slice hu (contDiffOn_pdU hα.isOpen (hsx.trans hxs') hF)).contDiffAt
    (Icc_mem_nhds hsx hxs')).differentiableAt (by simp)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hsx hxs'] with t ht
  exact piece_varDeriv hα.isOpen hF hu ht

/-- **The first variation formula, at every `u`** (Milnor's proof of Theorem 12.2, formula
(12.2′) of the exposition): for a variation `α` and `u ∈ U`,
`½ dE(α_u)/du = -Σ_t ⟨∂α/∂u, Δ_t ∂α/∂t⟩ - ∫₀¹ ⟨∂α/∂u, D/∂t ∂α/∂t⟩ dt`, everything at `(u, t)`. -/
theorem IsVariation.hasDerivAt_energy (hα : IsVariation N U α B) {u₀ : ℝ} (hu₀ : u₀ ∈ U) :
    HasDerivAt (fun u => energy (α u) 0 1)
      (2 * firstVariation hN (α u₀) (fun t => deriv (fun v => α v t) u₀)) u₀ := by
  have hU := hα.isOpen
  set Y : ℝ → V := fun t => deriv (fun v => α v t) u₀ with hY_def
  -- Step 1: differentiation under the integral sign
  have h1 : HasDerivAt (fun u => energy (α u) 0 1)
      (∫ τ in (0 : ℝ)..1, deriv (fun u => ‖deriv (α u) τ‖ ^ 2) u₀) u₀ := by
    refine hasDerivAt_integral_of_piecewise hU (B := B) (lo := 0) (hi := 1)
      (fun s t hs hst ht hB => ?_) le_rfl zero_le_one le_rfl hu₀
    have hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t) := hα.smooth s t hs hst ht hB
    refine ⟨fun p => ‖pdT (U ×ˢ Icc s t) (unc α) p‖ ^ 2,
      ((contDiffOn_pdT hU hst hF).norm_sq ℝ).of_le (by simp), fun u hu τ hτ => ?_⟩
    rw [piece_deriv hF hu hτ]
  -- Step 2: on each piece, the integrand is `2 ⟨∂/∂t ∂α/∂u, ∂α/∂t⟩`
  have h2 : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) → ∀ τ ∈ Ioo s t,
      deriv (fun u => ‖deriv (α u) τ‖ ^ 2) u₀ = 2 * ⟪deriv Y τ, deriv (α u₀) τ⟫ := by
    intro s t hs hst ht hB τ hτ
    have hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t) := hα.smooth s t hs hst ht hB
    set S := U ×ˢ Icc s t
    have hX := contDiffOn_pdT hU hst hF
    have hev : (fun u => ‖deriv (α u) τ‖ ^ 2) =ᶠ[𝓝 u₀]
        fun u => ‖pdT S (unc α) (u, τ)‖ ^ 2 := by
      filter_upwards [hU.mem_nhds hu₀] with u hu
      rw [piece_deriv hF hu hτ]
    have hd := (hasDerivAt_pdU hU (hX.differentiableOn (by simp)) hu₀
      (Ioo_subset_Icc_self hτ)).norm_sq
    rw [hev.deriv_eq, hd.deriv, pdU_pdT hU hst hF (mk_mem_prod hu₀ (Ioo_subset_Icc_self hτ)),
      piece_deriv_varDeriv hU hst hF hu₀ hτ, piece_deriv hF hu₀ hτ, real_inner_comm]
  -- Step 3: integration by parts on each piece, glued over the break points
  have hint : ∀ {G : ℝ → ℝ} (hG : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) →
      ∃ K : ℝ → ℝ, ContinuousOn K (Icc s t) ∧ EqOn G K (Ioo s t)),
      IntervalIntegrable G volume 0 1 := fun hG =>
    intervalIntegrable_of_piecewise hG le_rfl zero_le_one le_rfl
  have hpieceY : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) →
      ContDiffOn ℝ ∞ (fun τ => pdU (U ×ˢ Icc s t) (unc α) (u₀, τ)) (Icc s t) ∧
      ContDiffOn ℝ ∞ (fun τ => pdT (U ×ˢ Icc s t) (unc α) (u₀, τ)) (Icc s t) ∧
      ContDiffOn ℝ ∞ (fun τ => pdT (U ×ˢ Icc s t) (pdU (U ×ˢ Icc s t) (unc α)) (u₀, τ))
        (Icc s t) ∧
      ContDiffOn ℝ ∞ (fun τ => pdT (U ×ˢ Icc s t) (pdT (U ×ˢ Icc s t) (unc α)) (u₀, τ))
        (Icc s t) := by
    intro s t hs hst ht hB
    have hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t) := hα.smooth s t hs hst ht hB
    exact ⟨piece_contDiffOn_slice hu₀ (contDiffOn_pdU hU hst hF),
      piece_contDiffOn_slice hu₀ (contDiffOn_pdT hU hst hF),
      piece_contDiffOn_slice hu₀ (contDiffOn_pdT hU hst (contDiffOn_pdU hU hst hF)),
      piece_contDiffOn_slice hu₀ (contDiffOn_pdT hU hst (contDiffOn_pdT hU hst hF))⟩
  have hint1 : IntervalIntegrable (fun τ => ⟪deriv Y τ, deriv (α u₀) τ⟫) volume 0 1 := by
    refine hint fun s t hs hst ht hB => ?_
    have hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t) := hα.smooth s t hs hst ht hB
    obtain ⟨-, h2', h3', -⟩ := hpieceY s t hs hst ht hB
    exact ⟨_, h3'.continuousOn.inner h2'.continuousOn, fun τ hτ => by
      simp only [hY_def, piece_deriv_varDeriv hU hst hF hu₀ hτ, piece_deriv hF hu₀ hτ]⟩
  have hint2 : IntervalIntegrable (fun τ => ⟪Y τ, deriv (deriv (α u₀)) τ⟫) volume 0 1 := by
    refine hint fun s t hs hst ht hB => ?_
    have hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t) := hα.smooth s t hs hst ht hB
    obtain ⟨h1', -, -, h4'⟩ := hpieceY s t hs hst ht hB
    exact ⟨_, h1'.continuousOn.inner h4'.continuousOn, fun τ hτ => by
      simp only [hY_def, piece_varDeriv hU hF hu₀ (Ioo_subset_Icc_self hτ),
        piece_deriv_deriv hU hst hF hu₀ hτ]⟩
  have h3 : ∫ τ in (0 : ℝ)..1, (⟪deriv Y τ, deriv (α u₀) τ⟫ + ⟪Y τ, deriv (deriv (α u₀)) τ⟫) =
      ⟪Y 1, derivWithin (α u₀) (Iic 1) 1⟫ - ⟪Y 0, derivWithin (α u₀) (Ici 0) 0⟫ -
        ∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, (⟪Y x, derivWithin (α u₀) (Ici x) x⟫ -
          ⟪Y x, derivWithin (α u₀) (Iic x) x⟫) := by
    refine integral_eq_of_piecewise (B := B) (lo := 0) (hi := 1)
      (Fl := fun x => ⟪Y x, derivWithin (α u₀) (Iic x) x⟫)
      (Fr := fun x => ⟪Y x, derivWithin (α u₀) (Ici x) x⟫)
      (fun a b ha hab hb => ?_) (fun s t hs hst ht hB => ?_) 0 1 le_rfl zero_lt_one le_rfl
    · exact ((hint1.mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le zero_le_one]; exact Icc_subset_Icc ha hb)).add
        (hint2.mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le zero_le_one]; exact Icc_subset_Icc ha hb)))
    · have hF : ContDiffOn ℝ ∞ (unc α) (U ×ˢ Icc s t) := hα.smooth s t hs hst ht hB
      set S := U ×ˢ Icc s t
      obtain ⟨h1', h2', h3', h4'⟩ := hpieceY s t hs hst ht hB
      have hfc : ContinuousOn (fun τ => ⟪pdU S (unc α) (u₀, τ), pdT S (unc α) (u₀, τ)⟫)
          (Icc s t) := h1'.continuousOn.inner h2'.continuousOn
      have hd : ∀ τ ∈ Ioo s t, HasDerivAt
          (fun τ => ⟪pdU S (unc α) (u₀, τ), pdT S (unc α) (u₀, τ)⟫)
          (⟪deriv Y τ, deriv (α u₀) τ⟫ + ⟪Y τ, deriv (deriv (α u₀)) τ⟫) τ := by
        intro τ hτ
        have e1 := hasDerivAt_pdT ((contDiffOn_pdU hU hst hF).differentiableOn (by simp)) hu₀ hτ
        have e2 := hasDerivAt_pdT ((contDiffOn_pdT hU hst hF).differentiableOn (by simp)) hu₀ hτ
        have e3 : deriv Y τ = pdT S (pdU S (unc α)) (u₀, τ) :=
          piece_deriv_varDeriv hU hst hF hu₀ hτ
        have e5 : Y τ = pdU S (unc α) (u₀, τ) := piece_varDeriv hU hF hu₀ (Ioo_subset_Icc_self hτ)
        rw [e3, piece_deriv hF hu₀ hτ, e5, piece_deriv_deriv hU hst hF hu₀ hτ]
        exact (e1.inner ℝ e2).congr_deriv (add_comm _ _)
      have hfint : IntervalIntegrable
          (fun τ => ⟪deriv Y τ, deriv (α u₀) τ⟫ + ⟪Y τ, deriv (deriv (α u₀)) τ⟫) volume s t := by
        refine ((h3'.continuousOn.inner h2'.continuousOn).add
          (h1'.continuousOn.inner h4'.continuousOn)).intervalIntegrable_of_Icc hst.le
          |>.congr_uIoo fun τ hτ => ?_
        rw [uIoo_of_le hst.le] at hτ
        simp only [Pi.add_apply, hY_def, piece_deriv_varDeriv hU hst hF hu₀ hτ,
          piece_deriv hF hu₀ hτ,
          piece_varDeriv hU hF hu₀ (Ioo_subset_Icc_self hτ),
          piece_deriv_deriv hU hst hF hu₀ hτ]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst.le hfc hd hfint]
      have eYt : Y t = pdU S (unc α) (u₀, t) := piece_varDeriv hU hF hu₀ (right_mem_Icc.2 hst.le)
      have eYs : Y s = pdU S (unc α) (u₀, s) := piece_varDeriv hU hF hu₀ (left_mem_Icc.2 hst.le)
      rw [eYt, eYs, piece_derivWithin_Iic hst hF hu₀, piece_derivWithin_Ici hst hF hu₀]
  -- Step 4: the end points are fixed, so `∂α/∂u = 0` there
  have hY0 : Y 0 = 0 := by
    have hev : (fun u => α u 0) =ᶠ[𝓝 u₀] fun _ => α 0 0 := by
      filter_upwards [hU.mem_nhds hu₀] with u hu
      exact hα.start u hu
    change deriv (fun u => α u 0) u₀ = 0
    rw [hev.deriv_eq, deriv_const]
  have hY1 : Y 1 = 0 := by
    have hev : (fun u => α u 1) =ᶠ[𝓝 u₀] fun _ => α 0 1 := by
      filter_upwards [hU.mem_nhds hu₀] with u hu
      exact hα.finish u hu
    change deriv (fun u => α u 1) u₀ = 0
    rw [hev.deriv_eq, deriv_const]
  -- Step 5: `⟨∂α/∂u, ∂²α/∂t²⟩ = ⟨∂α/∂u, D/∂t ∂α/∂t⟩`, `∂α/∂u` being tangent
  have h5 : ∫ τ in (0 : ℝ)..1, ⟪Y τ, deriv (deriv (α u₀)) τ⟫ =
      ∫ τ in (0 : ℝ)..1, ⟪Y τ, accel hN (α u₀) τ⟫ := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le zero_le_one] at hτ
    simp only [accel, covD]
    exact (inner_prj_right_of_eq hN (hα.prj_varDeriv hN hu₀ hτ) _).symm
  -- Step 6: assemble
  have h6 : ∫ τ in (0 : ℝ)..1, deriv (fun u => ‖deriv (α u) τ‖ ^ 2) u₀ =
      ∫ τ in (0 : ℝ)..1, 2 * ⟪deriv Y τ, deriv (α u₀) τ⟫ := by
    refine intervalIntegral.integral_congr_ae ?_
    have hfin : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∉ insert (1 : ℝ) (B : Set ℝ) :=
      (B.finite_toSet.insert 1).countable.ae_notMem _
    filter_upwards [hfin] with τ hτB hτ
    rw [uIoc_of_le zero_le_one] at hτ
    rw [mem_insert_iff, not_or] at hτB
    obtain ⟨s, s', hs, hsτ, hτs', hs', hB⟩ :=
      exists_piece_around B hτ.1 (lt_of_le_of_ne hτ.2 hτB.1) hτB.2
    exact h2 s s' hs (hsτ.trans hτs') hs' hB τ ⟨hsτ, hτs'⟩
  rw [h6, intervalIntegral.integral_const_mul] at h1
  have hdiff : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ B → DifferentiableAt ℝ (α u₀) x :=
    fun x hx hxB => hα.differentiableAt hu₀ hx hxB
  rw [firstVariation, finsum_jump_eq_sum hdiff, ← h5]
  convert h1 using 1
  rw [intervalIntegral.integral_add hint1 hint2, hY0, hY1, inner_zero_left, inner_zero_left,
    sub_zero] at h3
  have hsum : ∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, (⟪Y x, derivWithin (α u₀) (Ici x) x⟫ -
      ⟪Y x, derivWithin (α u₀) (Iic x) x⟫) =
      ∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, ⟪Y x, jump (α u₀) x⟫ :=
    Finset.sum_congr rfl fun x _ => by rw [jump, inner_sub_right]
  rw [hsum] at h3
  linarith

/-- **Theorem 12.2 (the first variation formula)** (Milnor p. 71): for a variation `α` of `ω`
with variation field `W`,
`½ dE(ᾱ(u))/du (0) = -Σ_t ⟨W_t, Δ_t V⟩ - ∫₀¹ ⟨W_t, A_t⟩ dt`,
`V` the velocity, `A` the acceleration and `Δ_t V` the jumps of the velocity of `ω`. -/
theorem first_variation (hα : IsVariation N U α B) {c : ℝ → V}
    (hc : ∀ t ∈ Icc (0 : ℝ) 1, α 0 t = c t) :
    HasDerivAt (fun u => energy (α u) 0 1) (2 * firstVariation hN c (varField α)) 0 := by
  have h := hα.hasDerivAt_energy hN hα.zero_mem
  convert h using 2
  -- `firstVariation` only depends on the path on `[0, 1]`
  have hev : ∀ t ∈ Ioo (0 : ℝ) 1, c =ᶠ[𝓝 t] α 0 := fun t ht => by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    exact (hc x (Ioo_subset_Icc_self hx)).symm
  have hjump : ∀ t ∈ Ioo (0 : ℝ) 1, jump c t = jump (α 0) t := fun t ht => by
    rw [jump, jump, ((hev t ht).filter_mono nhdsWithin_le_nhds).derivWithin_eq
      (hev t ht).self_of_nhds, ((hev t ht).filter_mono nhdsWithin_le_nhds).derivWithin_eq
      (hev t ht).self_of_nhds]
  have hacc : ∀ t ∈ Ioo (0 : ℝ) 1, accel hN c t = accel hN (α 0) t := fun t ht => by
    rw [accel, accel, covD, covD, (hev t ht).deriv.deriv_eq, (hev t ht).self_of_nhds]
  have hint : ∫ t in (0 : ℝ)..1, ⟪varField α t, accel hN c t⟫ =
      ∫ t in (0 : ℝ)..1, ⟪varField α t, accel hN (α 0) t⟫ :=
    intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => by simp only [hacc t ht]
  have hsum : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪varField α t, jump c t⟫ =
      ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪varField α t, jump (α 0) t⟫ :=
    finsum_mem_congr rfl fun t ht => by rw [hjump t ht]
  rw [firstVariation, firstVariation, hint, hsum]
  rfl

end FirstVariation

/-! ### Lemma 11.A: every tangent vector is the variation field of a variation -/

section Exists

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `exp_q(v) ∈ N` when it is defined (private: the same statement is
`Morse.exp_mem_of_mem_expDom` in `Morse/Chapter7/HopfRinow.lean`, not imported here). -/
private theorem exp_mem_of_mem_expDom [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] {q v : V}
    (h : (q, v) ∈ expDom hN) : exp hN q v ∈ N := by
  obtain ⟨γ, ⟨δ, hδ, hγ, -, -⟩, he⟩ := exp_eq_of_mem_expDom h
  rw [he]
  exact hγ.mem 1 ⟨by linarith, by linarith⟩

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **Lemma 11.A of the exposition** (Milnor p. 68, "every tangent vector is a velocity"), in a
form covering any number of parameters: let `ω ∈ Ω(N; p, q)` and let `Λ(t) : P → T_{ω(t)}N` be a
piecewise smooth family of linear maps with `Λ(0) = Λ(1) = 0` (for `m` fields `W₁, …, W_m`,
`Λ(t)(u) = Σ uⱼ Wⱼ(t)`).  Then for some `ε > 0`, Milnor's formula
`α(u, t) = exp_{ω(t)}(Λ(t) u)` defines a variation of `ω` on the ball `‖u‖ < ε`, smooth on the
strips of the break points of `ω` and `Λ`, with `∂α/∂u (0, t) = Λ(t)`.

Proof: `exp` is defined and smooth on an open neighbourhood `O` of the zero section of `TN`
(`Morse.exists_isOpen_exp`, Lemma 10.2); by compactness of `ω([0, 1])`, `O` contains all
`(ω(t), v)` with `‖v‖ < δ`; take `ε = δ / (C + 1)`, `C` a bound for `‖Λ(t)‖`.  Completeness of `N`
is not used. -/
theorem exists_variation {c : ℝ → V} {p q : V} (hc : c ∈ pathSpace N p q)
    {Λ : ℝ → P →L[ℝ] V} (hΛ : IsPiecewiseSmooth Λ 0 1)
    (hΛT : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, prj hN (c t) (Λ t u) = Λ t u) (hΛ0 : Λ 0 = 0)
    (hΛ1 : Λ 1 = 0) :
    ∃ ε > 0, ∃ B : Finset ℝ,
      IsVariation N (ball (0 : P) ε) (fun u t => exp hN (c t) (Λ t u)) B ∧
      (∀ t ∈ Icc (0 : ℝ) 1, exp hN (c t) (Λ t 0) = c t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, HasFDerivAt (fun u => exp hN (c t) (Λ t u)) (Λ t) 0 := by
  obtain ⟨hcs, hcN, hc0, hc1⟩ := hc
  obtain ⟨O, hO, hO0, hexp⟩ := exists_isOpen_exp (hN := hN)
  -- a uniform radius around the compact set `{(ω(t), 0)}`
  have hK : IsCompact ((fun t => (c t, (0 : V))) '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn (hcs.2.1.prodMk continuousOn_const)
  have hKO : (fun t => (c t, (0 : V))) '' Icc (0 : ℝ) 1 ⊆ O := by
    rintro _ ⟨t, ht, rfl⟩
    exact hO0 _ (hcN t ht)
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hO hKO
  have hδO : ∀ t ∈ Icc (0 : ℝ) 1, ∀ v : V, ‖v‖ < δ → (c t, v) ∈ O := by
    intro t ht v hv
    refine hthick (Metric.mem_thickening_iff.2 ⟨(c t, 0), ⟨t, ht, rfl⟩, ?_⟩)
    rw [Prod.dist_eq, dist_self, dist_zero_right]
    exact max_lt hδ hv
  -- a bound for `‖Λ(t)‖`
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hΛ.2.1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  set ε := δ / (C + 1)
  have hε : 0 < ε := div_pos hδ (by linarith)
  have hsmall : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ ball (0 : P) ε, ‖Λ t u‖ < δ := by
    intro t ht u hu
    rw [mem_ball, dist_zero_right] at hu
    calc ‖Λ t u‖ ≤ ‖Λ t‖ * ‖u‖ := (Λ t).le_opNorm u
      _ ≤ C * ε := mul_le_mul (hC t ht) hu.le (norm_nonneg _) hC0
      _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  have hTN : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u, (c t, Λ t u) ∈ Milnor.Problems.tangentBundleSet hN :=
    fun t ht u => ⟨hcN t ht, (prj_eq_self_iff hN (hcN t ht)).1 (hΛT t ht u)⟩
  obtain ⟨-, -, Bc, hBc⟩ := hcs
  obtain ⟨-, -, BΛ, hBΛ⟩ := hΛ
  classical
  refine ⟨ε, hε, Bc ∪ BΛ, ⟨isOpen_ball, mem_ball_self hε, fun u hu t ht => ?_, fun u hu => ?_,
    fun u hu => ?_, fun s t hs hst ht hB => ?_⟩, fun t ht => ?_, fun t ht => ?_⟩
  · exact exp_mem_of_mem_expDom hN (hexp _ (hδO t ht _ (hsmall t ht u hu)) (hTN t ht u)).1
  · simp [hΛ0]
  · simp [hΛ1]
  · -- smoothness on a strip: near each point, `exp` is the restriction of a smooth map
    have hcp := hBc s t hs hst ht fun x hx => hB x (Finset.mem_union_left _ hx)
    have hΛp := hBΛ s t hs hst ht fun x hx => hB x (Finset.mem_union_right _ hx)
    have hφ : ContDiffOn ℝ ∞ (fun p : P × ℝ => (c p.2, Λ p.2 p.1)) (ball (0 : P) ε ×ˢ Icc s t) :=
      (hcp.comp contDiffOn_snd fun p hp => hp.2).prodMk
        ((hΛp.comp contDiffOn_snd fun p hp => hp.2).clm_apply contDiffOn_fst)
    intro p₀ hp₀
    have hp₀t : p₀.2 ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hp₀.2.1, hp₀.2.2.trans ht⟩
    obtain ⟨-, F, O', hO', hzO', hF, hFeq⟩ :=
      hexp _ (hδO _ hp₀t _ (hsmall _ hp₀t _ hp₀.1)) (hTN _ hp₀t _)
    have h1 : ContDiffWithinAt ℝ ∞ (fun p : P × ℝ => F (c p.2, Λ p.2 p.1))
        (ball (0 : P) ε ×ˢ Icc s t) p₀ :=
      (hF.contDiffAt (hO'.mem_nhds hzO')).comp_contDiffWithinAt p₀ (hφ p₀ hp₀)
    refine h1.congr_of_eventuallyEq_of_mem ?_ hp₀
    filter_upwards [(hφ p₀ hp₀).continuousWithinAt.preimage_mem_nhdsWithin
      (hO'.mem_nhds hzO'), self_mem_nhdsWithin] with p hp hps
    have hpt : p.2 ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hps.2.1, hps.2.2.trans ht⟩
    exact hFeq _ hp (hTN _ hpt _)
  · rw [map_zero]
    exact exp_zero (hcN t ht)
  · -- `d(exp_q)₀ = id`
    set qt : N := ⟨c t, hcN t ht⟩
    let L : P →L[ℝ] tangentSubspace hN qt :=
      (Λ t).codRestrict (tangentSubspace hN qt) fun u =>
        (prj_eq_self_iff hN (hcN t ht)).1 (hΛT t ht u)
    have h1 := hasFDerivAt_exp_zero (hN := hN) qt
    rw [← map_zero L] at h1
    have h2 := h1.comp (0 : P) L.hasFDerivAt
    have hL : ((tangentSubspace hN qt).subtypeL.comp L) = Λ t := by
      ext u; rfl
    rw [hL] at h2
    exact h2

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem IsPiecewiseSmooth.smulRight {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : P →L[ℝ] ℝ) {X : ℝ → E} {a b : ℝ} (hX : IsPiecewiseSmooth X a b) :
    IsPiecewiseSmooth (fun t => ℓ.smulRight (X t)) a b :=
  hX.comp_clm (ContinuousLinearMap.smulRightL ℝ P E ℓ)

/-- **Lemma 11.A for one field** (Milnor p. 68): every `W ∈ TΩ_ω` is the variation field of the
variation `ᾱ(u)(t) = exp_{ω(t)}(u W(t))`, `|u| < ε`. -/
theorem exists_variation_one {c : ℝ → V} {p q : V} (hc : c ∈ pathSpace N p q) {X : ℝ → V}
    (hX : X ∈ pathTangent hN c) :
    ∃ ε > (0 : ℝ), ∃ B : Finset ℝ,
      IsVariation N (Ioo (-ε) ε) (fun u t => exp hN (c t) (u • X t)) B ∧
      (∀ t ∈ Icc (0 : ℝ) 1, exp hN (c t) ((0 : ℝ) • X t) = c t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, varField (fun u t => exp hN (c t) (u • X t)) t = X t := by
  obtain ⟨hXs, hXT, hX0, hX1⟩ := hX
  obtain ⟨ε, hε, B, hα, h0, hd⟩ := exists_variation hN hc (P := ℝ)
    (hXs.smulRight (ContinuousLinearMap.id ℝ ℝ))
    (fun t ht u => by simp [map_smul, hXT t ht]) (by ext; simp [hX0]) (by ext; simp [hX1])
  refine ⟨ε, hε, B, ?_, fun t ht => by simpa using h0 t ht, fun t ht => ?_⟩
  · have e : ball (0 : ℝ) ε = Ioo (-ε) ε := by rw [Real.ball_eq_Ioo]; simp
    rw [← e]
    simpa using hα
  · have := (hd t ht).hasDerivAt
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      one_smul] at this
    exact this.deriv

/-- **Lemma 11.A for two fields** (Milnor p. 74): for `W₁, W₂ ∈ TΩ_ω`,
`α(u₁, u₂, t) = exp_{ω(t)}(u₁ W₁(t) + u₂ W₂(t))` is a 2-parameter variation of `ω` with
`∂α/∂uᵢ (0, 0, t) = Wᵢ(t)`. -/
theorem exists_variation_two {c : ℝ → V} {p q : V} (hc : c ∈ pathSpace N p q) {X₁ X₂ : ℝ → V}
    (hX₁ : X₁ ∈ pathTangent hN c) (hX₂ : X₂ ∈ pathTangent hN c) :
    ∃ ε > 0, ∃ B : Finset ℝ,
      IsVariation N (ball (0 : ℝ × ℝ) ε) (fun u t => exp hN (c t) (u.1 • X₁ t + u.2 • X₂ t)) B ∧
      (∀ t ∈ Icc (0 : ℝ) 1, exp hN (c t) ((0 : ℝ) • X₁ t + (0 : ℝ) • X₂ t) = c t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        deriv (fun u₁ : ℝ => exp hN (c t) (u₁ • X₁ t + (0 : ℝ) • X₂ t)) 0 = X₁ t) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        deriv (fun u₂ : ℝ => exp hN (c t) ((0 : ℝ) • X₁ t + u₂ • X₂ t)) 0 = X₂ t := by
  obtain ⟨hXs₁, hXT₁, hX0₁, hX1₁⟩ := hX₁
  obtain ⟨hXs₂, hXT₂, hX0₂, hX1₂⟩ := hX₂
  obtain ⟨ε, hε, B, hα, h0, hd⟩ := exists_variation hN hc (P := ℝ × ℝ)
    ((hXs₁.smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ)).add
      (hXs₂.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ)))
    (fun t ht u => by simp [map_smul, hXT₁ t ht, hXT₂ t ht]) (by ext <;> simp [hX0₁, hX0₂])
    (by ext <;> simp [hX1₁, hX1₂])
  refine ⟨ε, hε, B, by simpa using hα, fun t ht => by simpa using h0 t ht, fun t ht => ?_,
    fun t ht => ?_⟩
  · have h1 : HasDerivAt (fun s : ℝ => (s, (0 : ℝ))) ((1 : ℝ), (0 : ℝ)) (0 : ℝ) :=
      (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have := (hd t ht).comp_hasDerivAt_of_eq (0 : ℝ) h1 rfl
    simp only [Function.comp_def, add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', one_smul, zero_smul,
      add_zero] at this
    simpa using this.deriv
  · have h1 : HasDerivAt (fun s : ℝ => ((0 : ℝ), s)) ((0 : ℝ), (1 : ℝ)) (0 : ℝ) :=
      (hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ))
    have := (hd t ht).comp_hasDerivAt_of_eq (0 : ℝ) h1 rfl
    simp only [Function.comp_def, add_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', one_smul, zero_smul,
      zero_add] at this
    simpa using this.deriv

end Exists

end Morse
