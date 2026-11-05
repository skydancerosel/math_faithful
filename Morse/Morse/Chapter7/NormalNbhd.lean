import Morse.Chapter7.Exp

/-!
Milnor, *Morse Theory*, §10, pp. 58–59 (Lemma 10.3), for a submanifold `N ⊆ ℝᴷ` with the induced
metric.

# Uniformly normal neighbourhoods

## Milnor's text, paraphrased

(p. 58) Consider `F(q, v) = (q, exp_q(v))`, defined and smooth near `(p, 0)` in the tangent manifold
`TM`.  In the coordinates `(u, t)` of `TU` and `(u₁, u₂)` of `U × U`, `F_*(∂/∂uⁱ) = ∂/∂u₁ⁱ + ∂/∂u₂ⁱ`
and `F_*(∂/∂tʲ) = ∂/∂u₂ʲ`, so the Jacobian of `F` at `(p, 0)` is nonsingular, and by "the implicit
function theorem" `F` maps a neighbourhood `V'` of `(p, 0)` diffeomorphically onto a neighbourhood
of `(p, p)`.  One may assume that `V'` consists of the `(q, v)` with `q` in a neighbourhood `U'` of
`p` and `‖v‖ < ε`; choose `W` with `F(V') ⊃ W × W`.

**Lemma 10.3** (p. 59).  For each `p ∈ M` there are a neighbourhood `W` of `p` and `ε > 0` such that
(1) any two points of `W` are joined by a unique geodesic in `M` of length `< ε`; (2) this geodesic
depends smoothly on the two points (if `t ↦ exp_{q₁}(tv)`, `0 ≤ t ≤ 1`, is the geodesic joining
`q₁` and `q₂`, the pair `(q₁, v) ∈ TM` depends differentiably on `(q₁, q₂)`); (3) for each `q ∈ W`
the map `exp_q` maps the open `ε`-ball in `TM_q` diffeomorphically onto an open set `U_q ⊃ W`.

## In the embedded setting

* `Morse.NormalCoord hN q ε`, `Morse.IsNormalRadius hN q ε`: **`ε` is a normal radius at `q`**:
  `exp_q` is defined on `B_ε(q) = {v ∈ T_qN : ‖v‖ < ε}`, is there the restriction of a smooth map
  `F` on an open set of `V`, and is a bijection of `B_ε(q)` onto `N ∩ U` (`U` open in `V`), whose
  inverse is the restriction of a smooth map `G` on `U`.  This is Milnor's "maps diffeomorphically
  onto an open set `U_q`", with smoothness of maps between subsets of Euclidean spaces in Milnor's
  sense (locally the restriction of a smooth map).
* `Morse.lemma_10_3`: **Lemma 10.3**, items (1), (2), (3), with `W = N ∩ O` for an open `O ⊆ V`;
  `Morse.lemma_10_3_geodesic`: item (1) for geodesics.
* `Morse.exists_isNormalRadius`: every point has a normal radius.
* `Morse.NormalCoord.expDiffeo`, `Morse.exists_expDiffeo`: the same, in Mathlib's language: `exp_q`
  restricted to the `ε`-ball of the vector space `T_qN` is a `PartialDiffeomorph` onto an open
  subset of the manifold `N` (the manifold structure of the slice submanifold `N`).

The proof works in the slice chart `σ` at `p`.  With `x = Morse.sliceParam σ`, the map
`(u, w) ↦ (u, E(u, w))`, `E(u, w) = σ₁(exp(x(u), dx_u w))` (`Morse.LocalSpray.chartExp`, a flow
line of the chart spray), is smooth on `Z × Z` and its derivative at `(u₀, 0)` is
`(a, b) ↦ (a, a + b)` (`Morse.LocalSpray.hasFDerivAt_chartF`): `E(u, 0) = u` because `(u, 0)` is a
zero of the spray, and `t ↦ E(u₀, tb)` is the chart curve of the geodesic with initial velocity
`dx b`, by the homogeneity of the flow (`Morse.LocalSpray.φ_smul`).  The inverse function theorem
(the companion project's `Milnor.ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv`) gives a
local diffeomorphism `Φ` of `Z × Z`, from which `W`, `ε` and the inverse maps are read off.

## What Milnor leaves implicit

* **Inverse, not implicit, function theorem.**  Milnor says "implicit"; the statement used is the
  inverse function theorem (for `F`), on the `2n`-manifold `TM`.
* **The shape of `V'`.**  Taking `V'` to consist of the pairs `(q, v)` with `q ∈ U'` and
  `‖v‖ < ε` needs these sets to form a neighbourhood base of `(p, 0)` in `TM`, i.e. a comparison
  between `‖v‖` and the coordinates of `v`, uniform near `p`.  In the embedded setting `TN ⊆ V × V`
  carries the topology of `V × V`, `‖v‖` is the norm of `V`, and the comparison is
  `‖(dσ_q v)₁‖ ≤ ‖dσ_q‖ ‖v‖` and `‖dx_u w‖ ≤ ‖dx_u‖ ‖w‖`.
* **Uniqueness in (1)** is among geodesics `γ : [0, 1] → M` of length `< ε`: their initial vectors
  `v` have `‖v‖ = L(γ) < ε` (constant speed), so `(q₁, v) ∈ V'`, where `F` is injective; then
  `γ = exp_{q₁}(t v)` by uniqueness of geodesics (`Morse.lemma_10_3_geodesic`).
* **(3)**: `exp_q|B_ε(q)` is `v ↦ pr₂ F(q, v)`, injective since `F` is; its image is open because
  `F(V')` is; its inverse is `q' ↦ pr₂ F⁻¹(q, q')`, smooth.  `U_q ⊃ W` is (1).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Normal radii -/

/-- **Normal coordinates of radius `ε` at `q`**: `exp_q` maps the ball
`B_ε(q) = {v ∈ T_qN : ‖v‖ < ε}` diffeomorphically onto the open subset `N ∩ U` of `N`.  Precisely:
`exp_q` is defined on `B_ε(q)` and is there the restriction of the smooth map `F` on the open set
`O ⊆ V`; it is a bijection of `B_ε(q)` onto `N ∩ U`, `U` open in `V`, whose inverse is the
restriction of the smooth map `G` on `U`. -/
structure NormalCoord (q : N) (ε : ℝ) where
  /-- An open set of `V` containing `B_ε(q)`, on which `F` is smooth. -/
  O : Set V
  /-- An open set of `V` with `N ∩ U = exp_q(B_ε(q))`, on which `G` is smooth. -/
  U : Set V
  /-- A smooth extension of `exp_q|B_ε(q)`. -/
  F : V → V
  /-- A smooth extension of the inverse of `exp_q|B_ε(q)`. -/
  G : V → V
  pos : 0 < ε
  isOpen_O : IsOpen O
  isOpen_U : IsOpen U
  contDiffOn_F : ContDiffOn ℝ ∞ F O
  contDiffOn_G : ContDiffOn ℝ ∞ G U
  mem_expDom : ∀ v ∈ tangentSubspace hN q, ‖v‖ < ε → ((q : V), v) ∈ expDom hN
  mem_O : ∀ v ∈ tangentSubspace hN q, ‖v‖ < ε → v ∈ O
  F_eq : ∀ v ∈ tangentSubspace hN q, ‖v‖ < ε → F v = exp hN q v
  exp_mem_U : ∀ v ∈ tangentSubspace hN q, ‖v‖ < ε → exp hN q v ∈ U
  G_exp : ∀ v ∈ tangentSubspace hN q, ‖v‖ < ε → G (exp hN q v) = v
  G_mem : ∀ y ∈ U, y ∈ N → G y ∈ tangentSubspace hN q
  norm_G_lt : ∀ y ∈ U, y ∈ N → ‖G y‖ < ε
  exp_G : ∀ y ∈ U, y ∈ N → exp hN q (G y) = y

/-- **`ε` is a normal radius at `q`** (the exposition's term): `exp_q` maps the open `ε`-ball of
`T_qN` diffeomorphically onto an open subset of `N`. -/
def IsNormalRadius (q : N) (ε : ℝ) : Prop := Nonempty (NormalCoord hN q ε)

/-! ### `exp` read in a slice chart -/

namespace LocalSpray

variable {σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N} {u₀ : Z} (L : LocalSpray σ u₀)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem fst_mem_target {z : Z × Z} (hz : z ∈ ball (u₀, (0 : Z)) L.r) : z.1 ∈ σ.toChart.target := by
  have h := L.mem _ hz 0 ⟨by linarith [L.τ_pos], L.τ_pos⟩
  rwa [L.zero _ hz] at h

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem mem_ball_smul {u w : Z} (hz : (u, w) ∈ ball (u₀, (0 : Z)) L.r) {a : ℝ} (ha : |a| ≤ 1) :
    (u, a • w) ∈ ball (u₀, (0 : Z)) L.r := by
  rw [mem_ball, Prod.dist_eq, max_lt_iff] at hz ⊢
  refine ⟨hz.1, ?_⟩
  rw [dist_zero_right] at hz ⊢
  rw [norm_smul, Real.norm_eq_abs]
  calc |a| * ‖w‖ ≤ 1 * ‖w‖ := by gcongr
    _ < L.r := by linarith [hz.2]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- **Homogeneity of the chart flow** (Milnor's homogeneity, p. 57, in the chart):
`φ_s(u, a w) = (π₁ φ_{as}(u, w), a π₂ φ_{as}(u, w))` for `|a| ≤ 1`. -/
theorem φ_smul {u w : Z} (hz : (u, w) ∈ ball (u₀, (0 : Z)) L.r) {a : ℝ} (ha : |a| ≤ 1)
    {s : ℝ} (hs : s ∈ Ioo (-L.τ) L.τ) :
    L.φ s (u, a • w) = ((L.φ (a * s) (u, w)).1, a • (L.φ (a * s) (u, w)).2) := by
  have hza := L.mem_ball_smul hz ha
  have hτ := L.τ_pos
  have hmul : ∀ s ∈ Ioo (-L.τ) L.τ, a * s ∈ Ioo (-L.τ) L.τ := by
    intro s hs
    have h1 : |a * s| < L.τ := by
      rw [abs_mul]
      calc |a| * |s| ≤ 1 * |s| := by gcongr
        _ < L.τ := by rw [one_mul]; exact abs_lt.2 hs
    exact abs_lt.1 h1
  have hlin : ∀ s : ℝ, HasDerivAt (fun s : ℝ => a * s) a s := fun s => by
    simpa using (hasDerivAt_id s).const_mul a
  refine ode_eqOn ((isOpen_toChart_target σ).prod isOpen_univ)
    ((contDiffOn_chartSpray σ).of_le (by exact_mod_cast le_top)) isOpen_Ioo isPreconnected_Ioo
    (f := fun s => L.φ s (u, a • w))
    (g := fun s => ((L.φ (a * s) (u, w)).1, a • (L.φ (a * s) (u, w)).2))
    (fun s hs => ⟨L.hasDerivAt _ hza s hs, L.mem _ hza s hs, mem_univ _⟩)
    (fun s hs => ⟨?_, L.mem _ hz _ (hmul s hs), mem_univ _⟩)
    (t₀ := 0) ⟨by linarith, hτ⟩ (by simp [L.zero _ hza, L.zero _ hz]) hs
  have h1 : HasDerivAt (fun s => L.φ (a * s) (u, w)) (a • chartSpray σ (L.φ (a * s) (u, w))) s :=
    (L.hasDerivAt _ hz _ (hmul s hs)).scomp s (hlin s)
  have h2 := (hasDerivAt_fst_comp h1).prodMk ((hasDerivAt_snd_comp h1).const_smul a)
  have e : chartSpray σ ((L.φ (a * s) (u, w)).1, a • (L.φ (a * s) (u, w)).2) =
      ((a • chartSpray σ (L.φ (a * s) (u, w))).1,
        a • (a • chartSpray σ (L.φ (a * s) (u, w))).2) := by
    simp only [chartSpray, chartAcc_smul, Prod.smul_mk, smul_neg, smul_smul]
  rw [e]
  exact h2

/-- **The chart expression of `exp`**: `E(u, w) = σ₁(exp(x(u), dx_u w))`
(`Morse.LocalSpray.exp_eq_chartExp`), the first component of the chart flow at time `c`. -/
def chartExp (z : Z × Z) : Z := (L.φ (L.c * 1) (z.1, L.c⁻¹ • z.2)).1

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem contDiff_chartExp : ContDiff ℝ ∞ L.chartExp :=
  contDiff_fst.comp (L.contDiff.comp (contDiff_const.prodMk
    (contDiff_fst.prodMk (contDiff_const.smul contDiff_snd))))

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem chartExp_mem {z : Z × Z} (hz : z ∈ L.good) : L.chartExp z ∈ σ.toChart.target :=
  L.mem _ (L.mem_ball_of_good hz) _ (L.mul_mem_Ioo ⟨by norm_num, by norm_num⟩)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- `E(u, 0) = u`: `(u, 0)` is a zero of the chart spray. -/
theorem chartExp_zero {u : Z} (hu : u ∈ ball u₀ L.r) : L.chartExp (u, 0) = u := by
  have hz : (u, (0 : Z)) ∈ ball (u₀, (0 : Z)) L.r := by
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_self]
    exact ⟨hu, L.r_pos⟩
  have hT := L.fst_mem_target hz
  have hc : L.c * 1 ∈ Ioo (-L.τ) L.τ := L.mul_mem_Ioo ⟨by norm_num, by norm_num⟩
  have h := ode_eqOn ((isOpen_toChart_target σ).prod isOpen_univ)
    ((contDiffOn_chartSpray σ).of_le (by exact_mod_cast le_top)) isOpen_Ioo isPreconnected_Ioo
    (f := fun s => L.φ s (u, 0)) (g := fun _ => (u, (0 : Z)))
    (fun s hs => ⟨L.hasDerivAt _ hz s hs, L.mem _ hz s hs, mem_univ _⟩)
    (fun s _ => ⟨by
      have e : chartSpray σ (u, (0 : Z)) = 0 := by
        ext <;> simp [chartSpray, chartAcc_zero]
      rw [e]
      exact hasDerivAt_const s (u, (0 : Z)), hT, mem_univ _⟩)
    (t₀ := 0) ⟨by linarith [L.τ_pos], L.τ_pos⟩ (L.zero _ hz) hc
  have h' : L.φ (L.c * 1) (u, 0) = (u, 0) := h
  simp only [chartExp, smul_zero]
  rw [h']

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem isGeodesicFrom_geo {u w : Z} (h : (u, w) ∈ L.good) :
    IsGeodesicFrom hN (L.geo u w) (sliceParam σ u) (fderiv ℝ (sliceParam σ) u w) :=
  ⟨1, one_pos, (L.isGeodesicOn_geo hN h).mono isOpen_Ioo
    (Ioo_subset_Ioo (by norm_num) (by norm_num)), L.geo_zero h, (L.hasDerivAt_geo_zero h).deriv⟩

/-- **`exp` in the chart**: `exp(x(u), dx_u w) = x(E(u, w))` for chart data near `(u₀, 0)`. -/
theorem exp_eq_chartExp {z : Z × Z} (hz : z ∈ L.good) :
    exp hN (sliceParam σ z.1) (fderiv ℝ (sliceParam σ) z.1 z.2) = sliceParam σ (L.chartExp z) :=
  (L.isGeodesicFrom_geo hN hz).exp_eq

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- `t ↦ E(u₀, tb)` has velocity `b` at `0`. -/
theorem hasDerivAt_chartExp_line {b : Z} (hb : (u₀, b) ∈ L.good) :
    HasDerivAt (fun t : ℝ => L.chartExp (u₀, t • b)) b 0 := by
  have hz := L.mem_ball_of_good hb
  have hc1 : L.c * 1 ∈ Ioo (-L.τ) L.τ := L.mul_mem_Ioo ⟨by norm_num, by norm_num⟩
  have hev : (fun t : ℝ => L.chartExp (u₀, t • b)) =ᶠ[𝓝 0]
      fun t => (L.φ (L.c * t) (u₀, L.c⁻¹ • b)).1 := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
      with t ht
    have hta : |t| ≤ 1 := (abs_lt.2 ht).le
    simp only [chartExp]
    rw [smul_comm L.c⁻¹ t b, L.φ_smul hz hta hc1, mul_comm t, mul_one]
  have hlin : HasDerivAt (fun t : ℝ => L.c * t) L.c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul L.c
  have h0 : L.c * 0 ∈ Ioo (-L.τ) L.τ := L.mul_mem_Ioo ⟨by norm_num, by norm_num⟩
  have h1 := hasDerivAt_fst_comp ((L.hasDerivAt _ hz _ h0).scomp (0 : ℝ) hlin)
  rw [mul_zero, L.zero _ hz] at h1
  simp only [Prod.smul_fst, chartSpray, smul_smul, mul_inv_cancel₀ L.c_pos.ne', one_smul] at h1
  exact h1.congr_of_eventuallyEq hev

/-- The map `F(u, w) = (u, E(u, w))`, `F(q, v) = (q, exp_q v)` read in the chart. -/
def chartF (z : Z × Z) : Z × Z := (z.1, L.chartExp z)

/-- The derivative of `chartF` at `(u₀, 0)`: `(a, b) ↦ (a, a + b)` (Milnor's Jacobian, p. 58). -/
def jacobian : (Z × Z) ≃L[ℝ] (Z × Z) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℝ Z Z).prod
      (ContinuousLinearMap.fst ℝ Z Z + ContinuousLinearMap.snd ℝ Z Z))
    ((ContinuousLinearMap.fst ℝ Z Z).prod
      (ContinuousLinearMap.snd ℝ Z Z - ContinuousLinearMap.fst ℝ Z Z))
    (fun z => by simp) (fun z => by simp)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- **Milnor's Jacobian** (p. 58): `dF_{(u₀, 0)}(a, b) = (a, a + b)`. -/
theorem hasFDerivAt_chartF :
    HasFDerivAt L.chartF ((jacobian (Z := Z) : (Z × Z) ≃L[ℝ] (Z × Z)) : (Z × Z) →L[ℝ] (Z × Z))
      (u₀, 0) := by
  have hE := L.contDiff_chartExp
  have hEd : HasFDerivAt L.chartExp (fderiv ℝ L.chartExp (u₀, 0)) (u₀, 0) :=
    ((hE.differentiable (by simp)) _).hasFDerivAt
  -- derivative in the direction `(a, 0)`
  have hu : ∀ a : Z, fderiv ℝ L.chartExp (u₀, 0) (a, 0) = a := by
    intro a
    have hev : (fun u : Z => L.chartExp (u, 0)) =ᶠ[𝓝 u₀] id := by
      filter_upwards [ball_mem_nhds u₀ L.r_pos] with u hu
      exact L.chartExp_zero hu
    have hlin : HasFDerivAt (fun u : Z => ((u, 0) : Z × Z)) (ContinuousLinearMap.inl ℝ Z Z) u₀ :=
      (hasFDerivAt_id u₀).prodMk (hasFDerivAt_const _ _)
    have hEd0 : HasFDerivAt L.chartExp (fderiv ℝ L.chartExp (u₀, 0))
        ((fun u : Z => ((u, 0) : Z × Z)) u₀) := hEd
    have h1 : HasFDerivAt (L.chartExp ∘ fun u : Z => ((u, 0) : Z × Z))
        ((fderiv ℝ L.chartExp (u₀, 0)).comp (ContinuousLinearMap.inl ℝ Z Z)) u₀ :=
      HasFDerivAt.comp u₀ hEd0 hlin
    have h2 := h1.unique ((hasFDerivAt_id u₀).congr_of_eventuallyEq hev)
    have := DFunLike.congr_fun h2 a
    simpa using this
  -- derivative in the direction `(0, b)`, for small `b`
  have hw : ∀ b : Z, (u₀, b) ∈ L.good → fderiv ℝ L.chartExp (u₀, 0) (0, b) = b := by
    intro b hb
    have h1 : HasDerivAt (L.chartExp ∘ fun t : ℝ => ((u₀, t • b) : Z × Z))
        (fderiv ℝ L.chartExp (u₀, 0) (0, b)) 0 := by
      have hline : HasDerivAt (fun t : ℝ => ((u₀, t • b) : Z × Z)) (0, b) 0 :=
        (hasDerivAt_const _ _).prodMk (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const b)
      have hEd' : HasFDerivAt L.chartExp (fderiv ℝ L.chartExp (u₀, 0))
          ((fun t : ℝ => ((u₀, t • b) : Z × Z)) 0) := by
        simp only [zero_smul]; exact hEd
      exact HasFDerivAt.comp_hasDerivAt (0 : ℝ) hEd' hline
    exact h1.unique (L.hasDerivAt_chartExp_line hb)
  have hw' : ∀ b : Z, fderiv ℝ L.chartExp (u₀, 0) (0, b) = b := by
    intro b
    by_cases hb0 : b = 0
    · rw [hb0, Prod.mk_zero_zero, map_zero]
    set a : ℝ := L.c * L.r / (2 * ‖b‖) with ha_def
    have hbpos : 0 < ‖b‖ := norm_pos_iff.2 hb0
    have hcr := mul_pos L.c_pos L.r_pos
    have ha : 0 < a := by positivity
    have hab : (u₀, a • b) ∈ L.good := by
      refine ⟨mem_ball_self L.r_pos, ?_⟩
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha, ha_def]
      field_simp
      linarith
    have := hw (a • b) hab
    rw [show ((0 : Z), a • b) = a • ((0 : Z), b) by simp, map_smul] at this
    exact smul_right_injective Z ha.ne' this
  have hD : fderiv ℝ L.chartExp (u₀, 0) =
      ContinuousLinearMap.fst ℝ Z Z + ContinuousLinearMap.snd ℝ Z Z := by
    refine ContinuousLinearMap.ext fun z => ?_
    obtain ⟨a, b⟩ := z
    have hab : ((a, b) : Z × Z) = (a, 0) + (0, b) := by simp
    rw [hab, map_add, hu, hw']
    simp
  have h := hasFDerivAt_fst.prodMk hEd
  rw [hD] at h
  exact h

end LocalSpray

/-! ### Lemma 10.3 -/

/-- **Milnor's Lemma 10.3** (p. 59).  For each `p ∈ N` there are an open set `O ∋ p` of `V`
(`W = N ∩ O`) and an `ε > 0` such that
1. any two points `q₁, q₂` of `W` are joined by a unique geodesic `t ↦ exp_{q₁}(tv)`,
   `0 ≤ t ≤ 1`, of length `‖v‖ < ε`: there is one and only one `v ∈ T_{q₁}N` with `‖v‖ < ε` and
   `exp_{q₁}(v) = q₂` (for geodesics, see `Morse.lemma_10_3_geodesic`);
2. `v` depends smoothly on `(q₁, q₂)`: it is the restriction of a smooth map `G` on an open set of
   `V × V` containing `W × W`;
3. for each `q ∈ W`, `ε` is a normal radius at `q`: `exp_q` maps `B_ε(q)` diffeomorphically onto
   an open set `U_q` of `N`, and `U_q ⊇ W` by (1). -/
theorem lemma_10_3 (p : N) :
    ∃ O : Set V, IsOpen O ∧ (p : V) ∈ O ∧ ∃ ε > 0,
      (∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O →
        ∃! v, v ∈ tangentSubspace hN q₁ ∧ ‖v‖ < ε ∧ exp hN q₁ v = q₂) ∧
      (∃ O₂ : Set (V × V), IsOpen O₂ ∧ ∃ G : V × V → V, ContDiffOn ℝ ∞ G O₂ ∧
        ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O → ((q₁ : V), (q₂ : V)) ∈ O₂ ∧
          G (q₁, q₂) ∈ tangentSubspace hN q₁ ∧ ‖G (q₁, q₂)‖ < ε ∧
          exp hN q₁ (G (q₁, q₂)) = q₂) ∧
      (∀ q : N, (q : V) ∈ O → IsNormalRadius hN q ε) := by
  set σ := sliceAt hN p
  have hp : (p : V) ∈ σ.φ.source := mem_sliceAt_source hN p
  set u₀ := (σ.φ p).1 with hu₀_def
  have hu₀ : u₀ ∈ σ.toChart.target := toChart_apply_mem_target σ hp
  obtain ⟨L⟩ := nonempty_localSpray σ hu₀
  set T := σ.toChart.target with hT_def
  have hTo : IsOpen T := isOpen_toChart_target σ
  set x := sliceParam σ with hx_def
  have hφ := Milnor.Problems.sliceChart_contDiffOn σ
  have hdφ : ContDiffOn ℝ ∞ (fun y => fderiv ℝ σ.φ y) σ.φ.source :=
    hφ.fderiv_of_isOpen σ.φ.open_source (by simp)
  have hdx : ContDiffOn ℝ ∞ (fderiv ℝ x) T :=
    (contDiffOn_sliceParam σ).fderiv_of_isOpen hTo (by simp)
  have hσ₁ : ContinuousOn (fun y => (σ.φ y).1) σ.φ.source :=
    continuous_fst.comp_continuousOn hφ.continuousOn
  -- chart facts
  have hxσ : ∀ a ∈ T, (σ.φ (x a)).1 = a := fun a ha => by
    rw [hx_def, sliceChart_sliceParam σ ha]
  have hxsrc : ∀ a ∈ T, x a ∈ σ.φ.source := fun a ha => sliceParam_mem_source σ ha
  have hσx : ∀ q : N, (q : V) ∈ σ.φ.source → x (σ.φ q).1 = q := fun q hq =>
    sliceParam_toChart σ hq
  -- the inverse function theorem
  have hF : ContDiff ℝ ∞ L.chartF := contDiff_fst.prodMk L.contDiff_chartExp
  have hinv : (mfderiv 𝓘(ℝ, Z × Z) 𝓘(ℝ, Z × Z) L.chartF (u₀, 0)).IsInvertible := by
    rw [mfderiv_eq_fderiv, L.hasFDerivAt_chartF.fderiv]
    exact ⟨_, rfl⟩
  obtain ⟨Φ, hΦs, hΦF⟩ := Milnor.ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv
    hF.contMDiff (by simp) hinv
  have hΦinv : ContDiffOn ℝ ∞ Φ.invFun Φ.target :=
    contMDiffOn_iff_contDiffOn.1 Φ.contMDiffOn_invFun
  have hΦleft : ∀ z ∈ Φ.source, Φ.invFun (L.chartF z) = z := fun z hz => by
    rw [hΦF hz]; exact Φ.invFun_apply hz
  have hΦtarget : ∀ z ∈ Φ.source, L.chartF z ∈ Φ.target := fun z hz => by
    rw [hΦF hz]; exact Φ.apply_mem hz
  -- radii
  set C₂ := ‖fderiv ℝ x u₀‖ + 1 with hC₂_def
  set A := Φ.source ∩ L.good ∩ (T ∩ (fun u => fderiv ℝ x u) ⁻¹' ball 0 C₂) ×ˢ univ with hA_def
  have hA : IsOpen A :=
    (Φ.open_source.inter L.isOpen_good).inter
      ((hdx.continuousOn.isOpen_inter_preimage hTo isOpen_ball).prod isOpen_univ)
  have hA0 : (u₀, (0 : Z)) ∈ A := ⟨⟨hΦs, L.mem_good⟩, ⟨hu₀, by
    rw [mem_preimage, mem_ball, dist_zero_right]; linarith⟩, mem_univ _⟩
  obtain ⟨ρ, hρ, hρA⟩ := Metric.isOpen_iff.1 hA _ hA0
  set C₁ := ‖fderiv ℝ σ.φ p‖ + 1 with hC₁_def
  have hC₁ : 0 < C₁ := by positivity
  set ε := ρ / C₁ with hε_def
  have hε : 0 < ε := div_pos hρ hC₁
  set S := ball (u₀, (0 : Z)) ρ ∩ (fun z : Z × Z => fderiv ℝ x z.1 z.2) ⁻¹' ball 0 ε with hS_def
  have hSA : S ⊆ A := fun z hz => hρA hz.1
  have hS : IsOpen S := by
    have hc : ContinuousOn (fun z : Z × Z => fderiv ℝ x z.1 z.2) (ball (u₀, (0 : Z)) ρ) :=
      ((hdx.continuousOn.comp continuous_fst.continuousOn fun z hz => (hρA hz).2.1.1).clm_apply
        continuous_snd.continuousOn)
    exact hc.isOpen_inter_preimage isOpen_ball isOpen_ball
  have hS0 : (u₀, (0 : Z)) ∈ S := ⟨mem_ball_self hρ, by simpa using hε⟩
  have hSε : ∀ z ∈ S, ‖fderiv ℝ x z.1 z.2‖ < ε := fun z hz => by
    have := hz.2
    rwa [mem_preimage, mem_ball, dist_zero_right] at this
  have hΦS : IsOpen (L.chartF '' S) := by
    have h := Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hS
      fun z hz => (hSA hz).1.1
    have heq : L.chartF '' S = Φ.toOpenPartialHomeomorph '' S :=
      image_congr fun z hz => hΦF (hSA hz).1.1
    rw [heq]
    exact h
  have hF0 : L.chartF (u₀, 0) = (u₀, u₀) := by
    simp only [LocalSpray.chartF, L.chartExp_zero (mem_ball_self L.r_pos)]
  obtain ⟨ρ₂, hρ₂, hρ₂S⟩ := Metric.isOpen_iff.1 hΦS _ ⟨(u₀, 0), hS0, hF0⟩
  set ρ' := min ρ ρ₂ with hρ'_def
  set O := σ.φ.source ∩ (fun y => ((σ.φ y).1, fderiv ℝ σ.φ y)) ⁻¹' (ball u₀ ρ' ×ˢ ball 0 C₁)
    with hO_def
  have hO : IsOpen O :=
    (hσ₁.prodMk hdφ.continuousOn).isOpen_inter_preimage σ.φ.open_source
      (isOpen_ball.prod isOpen_ball)
  have hpO : (p : V) ∈ O := ⟨hp, mem_ball_self (lt_min hρ hρ₂), by
    rw [mem_ball, dist_zero_right]; linarith⟩
  -- facts about points of `O`
  have hOσ : ∀ y ∈ O, ‖(σ.φ y).1 - u₀‖ < ρ' := fun y hy => by
    have := hy.2.1
    rwa [mem_ball, dist_eq_norm] at this
  have hOdσ : ∀ y ∈ O, ‖fderiv ℝ σ.φ y‖ < C₁ := fun y hy => by
    have := hy.2.2
    rwa [mem_ball, dist_zero_right] at this
  -- (K1) chart data of `(y, v)`, `y ∈ O`, `‖v‖ < ε`, lies in the ball of radius `ρ`
  have hK1 : ∀ y ∈ O, ∀ v : V, ‖v‖ < ε →
      ((σ.φ y).1, (fderiv ℝ σ.φ y v).1) ∈ ball (u₀, (0 : Z)) ρ := by
    intro y hy v hv
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_zero_right]
    refine ⟨lt_of_lt_of_le (hOσ y hy) (min_le_left _ _), ?_⟩
    calc ‖(fderiv ℝ σ.φ y v).1‖ ≤ ‖fderiv ℝ σ.φ y v‖ := norm_fst_le _
      _ ≤ ‖fderiv ℝ σ.φ y‖ * ‖v‖ := (fderiv ℝ σ.φ y).le_opNorm v
      _ ≤ C₁ * ‖v‖ := by gcongr; exact (hOdσ y hy).le
      _ < C₁ * ε := by gcongr
      _ = ρ := by rw [hε_def]; field_simp
  -- (K2) points of the `ρ`-ball
  have hK2 : ∀ z ∈ ball (u₀, (0 : Z)) ρ, z ∈ Φ.source ∧ z ∈ L.good ∧ z.1 ∈ T := fun z hz =>
    ⟨(hρA hz).1.1, (hρA hz).1.2, (hρA hz).2.1.1⟩
  -- (K4) `exp` in the chart
  have hK4 : ∀ z ∈ L.good, exp hN (x z.1) (fderiv ℝ x z.1 z.2) = x (L.chartExp z) :=
    fun z hz => L.exp_eq_chartExp hN hz
  -- (K5) chart coordinates of tangent vectors
  have hK5 : ∀ q : N, (q : V) ∈ σ.φ.source → ∀ v ∈ tangentSubspace hN q,
      fderiv ℝ x (σ.φ q).1 (fderiv ℝ σ.φ q v).1 = v := fun q hq v hv =>
    fderiv_sliceParam_fst_fderiv hN σ hq hv
  have hrange : ∀ q : N, (q : V) ∈ σ.φ.source → ∀ w : Z,
      fderiv ℝ x (σ.φ q).1 w ∈ tangentSubspace hN q := fun q hq w => by
    rw [tangentSubspace_eq_range_fderiv_sliceParam hN σ hq]
    exact LinearMap.mem_range_self _ w
  -- the chart point of `q₂` determines `exp`
  have hexpS : ∀ q : N, (q : V) ∈ O → ∀ v ∈ tangentSubspace hN q, ‖v‖ < ε →
      ((σ.φ q).1, (fderiv ℝ σ.φ q v).1) ∈ S ∧
      exp hN q v = x (L.chartExp ((σ.φ q).1, (fderiv ℝ σ.φ q v).1)) := by
    intro q hq v hv hvε
    have hz := hK1 q hq v hvε
    refine ⟨⟨hz, ?_⟩, ?_⟩
    · rw [mem_preimage, mem_ball, dist_zero_right, hK5 q hq.1 v hv]
      exact hvε
    · have := hK4 _ (hK2 _ hz).2.1
      simp only at this
      rwa [hK5 q hq.1 v hv, hσx q hq.1] at this
  -- the chart point of a pair `(q₁, q₂)` of points of `O`
  have hpair : ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O → ∃ w : Z,
      ((σ.φ q₁).1, w) ∈ S ∧ L.chartF ((σ.φ q₁).1, w) = ((σ.φ q₁).1, (σ.φ q₂).1) := by
    intro q₁ q₂ hq₁ hq₂
    have hmem : ((σ.φ q₁).1, (σ.φ q₂).1) ∈ L.chartF '' S := hρ₂S (by
      rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
      exact ⟨lt_of_lt_of_le (hOσ _ hq₁) (min_le_right _ _),
        lt_of_lt_of_le (hOσ _ hq₂) (min_le_right _ _)⟩)
    obtain ⟨⟨z₁, z₂⟩, hzS, hzF⟩ := hmem
    have hz1 : z₁ = (σ.φ q₁).1 := congrArg Prod.fst hzF
    subst hz1
    exact ⟨z₂, hzS, hzF⟩
  -- `exp` of the chart vector
  have hexpw : ∀ q₁ q₂ : N, (q₁ : V) ∈ O → (q₂ : V) ∈ O → ∀ w : Z,
      ((σ.φ q₁).1, w) ∈ S → L.chartF ((σ.φ q₁).1, w) = ((σ.φ q₁).1, (σ.φ q₂).1) →
      exp hN q₁ (fderiv ℝ x (σ.φ q₁).1 w) = q₂ := by
    intro q₁ q₂ hq₁ hq₂ w hwS hwF
    have hz2 : L.chartExp ((σ.φ q₁).1, w) = (σ.φ q₂).1 := congrArg Prod.snd hwF
    have := hK4 _ (hK2 _ hwS.1).2.1
    simp only at this
    rwa [hσx q₁ hq₁.1, hz2, hσx q₂ hq₂.1] at this
  refine ⟨O, hO, hpO, ε, hε, ?_, ?_, ?_⟩
  · -- (1)
    intro q₁ q₂ hq₁ hq₂
    obtain ⟨w, hwS, hwF⟩ := hpair q₁ q₂ hq₁ hq₂
    have hwK := hK2 _ hwS.1
    refine ⟨fderiv ℝ x (σ.φ q₁).1 w, ⟨hrange q₁ hq₁.1 w, hSε _ hwS,
      hexpw q₁ q₂ hq₁ hq₂ w hwS hwF⟩, ?_⟩
    rintro v' ⟨hv', hv'ε, hexp'⟩
    obtain ⟨hz'S, hz'exp⟩ := hexpS q₁ hq₁ v' hv' hv'ε
    have hz'K := hK2 _ hz'S.1
    have hE' : L.chartExp ((σ.φ q₁).1, (fderiv ℝ σ.φ q₁ v').1) = (σ.φ q₂).1 := by
      rw [hexp'] at hz'exp
      have := congrArg (fun y => (σ.φ y).1) hz'exp
      rw [hxσ _ (L.chartExp_mem hz'K.2.1)] at this
      exact this.symm
    have hFF : L.chartF ((σ.φ q₁).1, (fderiv ℝ σ.φ q₁ v').1) = L.chartF ((σ.φ q₁).1, w) := by
      rw [hwF]
      simp only [LocalSpray.chartF, hE']
    have hww : (fderiv ℝ σ.φ q₁ v').1 = w := by
      have := congrArg Prod.snd
        ((hΦleft _ hz'K.1).symm.trans ((congrArg Φ.invFun hFF).trans (hΦleft _ hwK.1)))
      exact this
    rw [← hK5 q₁ hq₁.1 v' hv', hww]
  · -- (2)
    set O₂ := (σ.φ.source ×ˢ σ.φ.source) ∩
      (fun y : V × V => ((σ.φ y.1).1, (σ.φ y.2).1)) ⁻¹' ((T ×ˢ univ) ∩ Φ.target) with hO₂_def
    have hσ₁₂ : ContDiffOn ℝ ∞ (fun y : V × V => ((σ.φ y.1).1, (σ.φ y.2).1))
        (σ.φ.source ×ˢ σ.φ.source) :=
      (contDiff_fst.comp_contDiffOn (hφ.comp contDiffOn_fst fun y hy => hy.1)).prodMk
        (contDiff_fst.comp_contDiffOn (hφ.comp contDiffOn_snd fun y hy => hy.2))
    have hσ₁₂' : ContDiffOn ℝ ∞ (fun y : V × V => ((σ.φ y.1).1, (σ.φ y.2).1)) O₂ :=
      hσ₁₂.mono inter_subset_left
    have hO₂ : IsOpen O₂ :=
      hσ₁₂.continuousOn.isOpen_inter_preimage (σ.φ.open_source.prod σ.φ.open_source)
        ((hTo.prod isOpen_univ).inter Φ.open_target)
    refine ⟨O₂, hO₂, fun y => fderiv ℝ x (σ.φ y.1).1 (Φ.invFun ((σ.φ y.1).1, (σ.φ y.2).1)).2,
      ?_, ?_⟩
    · have h0 : ContDiffOn ℝ ∞ (fun y : V × V => (σ.φ y.1).1) O₂ := by
        have := contDiff_fst.comp_contDiffOn hσ₁₂'
        exact this
      have h1 : ContDiffOn ℝ ∞ (fun y : V × V => fderiv ℝ x (σ.φ y.1).1) O₂ :=
        hdx.comp h0 fun y hy => hy.2.1.1
      have h2 : ContDiffOn ℝ ∞ (fun y : V × V => Φ.invFun ((σ.φ y.1).1, (σ.φ y.2).1)) O₂ :=
        hΦinv.comp hσ₁₂' fun y hy => hy.2.2
      exact h1.clm_apply (contDiff_snd.comp_contDiffOn h2)
    · intro q₁ q₂ hq₁ hq₂
      obtain ⟨w, hwS, hwF⟩ := hpair q₁ q₂ hq₁ hq₂
      have hwK := hK2 _ hwS.1
      have hinvz : Φ.invFun ((σ.φ q₁).1, (σ.φ q₂).1) = ((σ.φ q₁).1, w) := by
        rw [← hwF]; exact hΦleft _ hwK.1
      have htarget : ((σ.φ q₁).1, (σ.φ q₂).1) ∈ Φ.target := by
        rw [← hwF]; exact hΦtarget _ hwK.1
      refine ⟨⟨⟨hq₁.1, hq₂.1⟩, ⟨toChart_apply_mem_target σ hq₁.1, mem_univ _⟩, htarget⟩, ?_⟩
      simp only [hinvz]
      exact ⟨hrange q₁ hq₁.1 w, hSε _ hwS, hexpw q₁ q₂ hq₁ hq₂ w hwS hwF⟩
  · -- (3)
    intro q hq
    set uq := (σ.φ q).1 with huq_def
    set Fq : V → V := fun v => x (L.chartExp (uq, (fderiv ℝ σ.φ q v).1)) with hFq_def
    set Oq := {v : V | (uq, (fderiv ℝ σ.φ q v).1) ∈ ball (u₀, (0 : Z)) ρ} with hOq_def
    have hlinq : ContDiff ℝ ∞ (fun v : V => (uq, (fderiv ℝ σ.φ q v).1)) :=
      contDiff_const.prodMk (contDiff_fst.comp (fderiv ℝ σ.φ q).contDiff)
    have hOq : IsOpen Oq := isOpen_ball.preimage hlinq.continuous
    set Uq := σ.φ.source ∩ (fun y => (uq, (σ.φ y).1)) ⁻¹' (L.chartF '' S) with hUq_def
    have hUq : IsOpen Uq :=
      (continuousOn_const.prodMk hσ₁).isOpen_inter_preimage σ.φ.open_source hΦS
    set Gq : V → V := fun y => fderiv ℝ x uq (Φ.invFun (uq, (σ.φ y).1)).2 with hGq_def
    -- points of `Uq`
    have hUqN : ∀ y ∈ Uq, ∃ w : Z, (uq, w) ∈ S ∧ L.chartExp (uq, w) = (σ.φ y).1 ∧
        Φ.invFun (uq, (σ.φ y).1) = (uq, w) ∧ (uq, (σ.φ y).1) ∈ Φ.target := by
      intro y hy
      obtain ⟨⟨z₁, z₂⟩, hzS, hzF⟩ := hy.2
      have hz1 : z₁ = uq := congrArg Prod.fst hzF
      subst hz1
      have hzF' : L.chartF (uq, z₂) = (uq, (σ.φ y).1) := hzF
      refine ⟨z₂, hzS, congrArg Prod.snd hzF', ?_, ?_⟩
      · rw [← hzF']; exact hΦleft _ (hK2 _ hzS.1).1
      · rw [← hzF']; exact hΦtarget _ (hK2 _ hzS.1).1
    refine ⟨⟨Oq, Uq, Fq, Gq, hε, hOq, hUq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · -- smoothness of `Fq`
      exact (contDiffOn_sliceParam σ).comp (L.contDiff_chartExp.comp hlinq).contDiffOn
        fun v hv => L.chartExp_mem (hK2 _ hv).2.1
    · -- smoothness of `Gq`
      have h2 : ContDiffOn ℝ ∞ (fun y => Φ.invFun (uq, (σ.φ y).1)) Uq :=
        hΦinv.comp ((contDiffOn_const.prodMk (contDiff_fst.comp_contDiffOn hφ)).mono
          inter_subset_left) fun y hy => (hUqN y hy).choose_spec.2.2.2
      exact (fderiv ℝ x uq).contDiff.comp_contDiffOn (contDiff_snd.comp_contDiffOn h2)
    · -- `B_ε(q)` is in the domain of `exp`
      intro v hv hvε
      have hz := hK1 q hq v hvε
      have h := L.isGeodesicFrom_geo hN (hK2 _ hz).2.1
      have hxq : sliceParam σ (σ.φ q).1 = q := hσx q hq.1
      rw [hK5 q hq.1 v hv, hxq] at h
      exact h.mem_expDom
    · intro v hv hvε
      exact hK1 q hq v hvε
    · intro v hv hvε
      exact ((hexpS q hq v hv hvε).2).symm
    · -- `exp_q(B_ε(q)) ⊆ U_q`
      intro v hv hvε
      obtain ⟨hzS, hexp⟩ := hexpS q hq v hv hvε
      have hzK := hK2 _ hzS.1
      rw [hexp]
      refine ⟨hxsrc _ (L.chartExp_mem hzK.2.1), ⟨_, hzS, ?_⟩⟩
      change (uq, L.chartExp (uq, (fderiv ℝ σ.φ q v).1)) =
        (uq, (σ.φ (x (L.chartExp (uq, (fderiv ℝ σ.φ q v).1)))).1)
      rw [hxσ _ (L.chartExp_mem hzK.2.1)]
    · -- `G ∘ exp_q = id`
      intro v hv hvε
      obtain ⟨hzS, hexp⟩ := hexpS q hq v hv hvε
      have hzK := hK2 _ hzS.1
      change fderiv ℝ x uq (Φ.invFun (uq, (σ.φ (exp hN q v)).1)).2 = v
      rw [hexp, hxσ _ (L.chartExp_mem hzK.2.1)]
      have h1 : (uq, L.chartExp (uq, (fderiv ℝ σ.φ q v).1)) =
          L.chartF (uq, (fderiv ℝ σ.φ q v).1) := rfl
      rw [h1, hΦleft _ hzK.1]
      exact hK5 q hq.1 v hv
    · intro y hy _
      obtain ⟨w, -, -, hinv, -⟩ := hUqN y hy
      change fderiv ℝ x uq (Φ.invFun (uq, (σ.φ y).1)).2 ∈ _
      rw [hinv]
      exact hrange q hq.1 w
    · intro y hy _
      obtain ⟨w, hwS, -, hinv, -⟩ := hUqN y hy
      change ‖fderiv ℝ x uq (Φ.invFun (uq, (σ.φ y).1)).2‖ < ε
      rw [hinv]
      exact hSε _ hwS
    · intro y hy hyN
      obtain ⟨w, hwS, hw2, hinv, -⟩ := hUqN y hy
      change exp hN q (fderiv ℝ x uq (Φ.invFun (uq, (σ.φ y).1)).2) = y
      rw [hinv]
      have := hK4 _ (hK2 _ hwS.1).2.1
      simp only at this
      rw [hσx q hq.1, hw2] at this
      rw [this]
      exact hσx ⟨y, hyN⟩ hy.1

/-- **Lemma 10.3 (1), for geodesics**: with `O`, `ε` as in `Morse.lemma_10_3`, a geodesic from
`q₁ ∈ W` with initial velocity of length `< ε` (that is, of length `< ε` on `[0, 1]`) ending at
`q₂ ∈ W` has as initial velocity the unique vector of Lemma 10.3 (1); so it is
`t ↦ exp_{q₁}(tv)` on `[0, 1]` (`Morse.IsGeodesicFrom.exp_smul`). -/
theorem lemma_10_3_geodesic {q₁ q₂ : N} {ε : ℝ}
    (huniq : ∃! v, v ∈ tangentSubspace hN q₁ ∧ ‖v‖ < ε ∧ exp hN q₁ v = q₂)
    {γ : ℝ → V} {v : V} (hγ : IsGeodesicFrom hN γ q₁ v) (hvε : ‖v‖ < ε) (h1 : γ 1 = q₂) :
    v = huniq.exists.choose := by
  obtain ⟨δ, hδ, hγo, h0, h0'⟩ := hγ
  have hv : v ∈ tangentSubspace hN q₁ := by
    have := hγo.deriv_mem (t := 0) ⟨by linarith, by linarith⟩
    rw [h0'] at this
    convert this using 2
    exact Subtype.ext h0.symm
  have hexp : exp hN q₁ v = q₂ := by
    rw [(show IsGeodesicFrom hN γ q₁ v from ⟨δ, hδ, hγo, h0, h0'⟩).exp_eq, h1]
  exact huniq.unique ⟨hv, hvε, hexp⟩ huniq.exists.choose_spec

/-- **Every point has a normal radius** (Lemma 10.3 (3) at `q = p`). -/
theorem exists_isNormalRadius (p : N) : ∃ ε > 0, IsNormalRadius hN p ε := by
  obtain ⟨O, -, hpO, ε, hε, -, -, h3⟩ := lemma_10_3 hN p
  exact ⟨ε, hε, h3 p hpO⟩

/-! ### `exp_q` as a diffeomorphism onto an open subset of the manifold `N` -/

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- A map into `N` which agrees near `x` with a smooth map into `V` is smooth at `x` as a map into
the manifold `N` (a pointwise form of the companion project's corestriction lemma). -/
theorem contMDiffAt_of_val_eventuallyEq {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {g : E' → N} {F : E' → V} {x : E'} (hF : ContDiffAt ℝ ∞ F x)
    (hg : ∀ᶠ y in 𝓝 x, (g y : V) = F y) :
    letI := hN.chartedSpace
    ContMDiffAt 𝓘(ℝ, E') 𝓘(ℝ, Z) ∞ g x := by
  let _ := hN.chartedSpace
  rw [contMDiffAt_iff_target]
  have hc : ContinuousAt (fun y => (g y : V)) x :=
    hF.continuousAt.congr (hg.mono fun y hy => hy.symm)
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.2 hc, ?_⟩
  set σ := (hN (g x) (g x).2).choose with hσ
  have hmem : (g x : V) ∈ σ.φ.source := (hN (g x) (g x).2).choose_spec
  rw [hN.extChartAt_eq (g x)]
  have hFx : F x = g x := hg.self_of_nhds.symm
  have hφ : ContDiffAt ℝ ∞ σ.φ (F x) := by
    rw [hFx]
    exact (Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt (σ.φ.open_source.mem_nhds hmem)
  have h1 : ContDiffAt ℝ ∞ (fun y => (σ.φ (F y)).1) x :=
    contDiff_fst.contDiffAt.comp x (hφ.comp x hF)
  refine h1.contMDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hg] with y hy
  change (σ.φ (g y : V)).1 = (σ.φ (F y)).1
  rw [hy]

open Classical in
/-- `exp_q` as a map `T_qN → N` (with the junk value `q` where `exp_q(v) ∉ N`). -/
def expToN (q : N) (v : tangentSubspace hN q) : N :=
  if h : exp hN q v ∈ N then ⟨exp hN q v, h⟩ else q

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem coe_expToN {q : N} {v : tangentSubspace hN q} (hv : exp hN q v ∈ N) :
    (expToN hN q v : V) = exp hN q v := by
  rw [expToN, dif_pos hv]

namespace NormalCoord

variable {hN} {q : N} {ε : ℝ} (nc : NormalCoord hN q ε)

include nc in
theorem exp_mem {v : V} (hv : v ∈ tangentSubspace hN q) (hvε : ‖v‖ < ε) : exp hN q v ∈ N := by
  obtain ⟨γ, hγ, he⟩ := exp_eq_of_mem_expDom (nc.mem_expDom v hv hvε)
  obtain ⟨δ, hδ, hγo, -, -⟩ := hγ
  rw [he]
  exact hγo.mem 1 ⟨by linarith, by linarith⟩

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem coe_orthogonalProjectionOnto_G {y : V} (hyU : y ∈ nc.U) (hyN : y ∈ N) :
    (((tangentSubspace hN q).orthogonalProjectionOnto (nc.G y) : tangentSubspace hN q) : V) =
      nc.G y := by
  rw [Submodule.coe_orthogonalProjectionOnto_apply]
  exact Submodule.starProjection_eq_self_iff.2 (nc.G_mem y hyU hyN)

/-- **`exp_q` is a diffeomorphism** from the open `ε`-ball of `T_qN` onto the open subset
`{y ∈ N | y ∈ U}` of the manifold `N` (Lemma 10.3 (3), as a Mathlib `PartialDiffeomorph`; the
inverse is `y ↦` the orthogonal projection of `G(y)` to `T_qN`, which is `G(y)`). -/
def expDiffeo :
    letI := hN.chartedSpace
    PartialDiffeomorph 𝓘(ℝ, tangentSubspace hN q) 𝓘(ℝ, Z) (tangentSubspace hN q) N ∞ := by
  letI := hN.chartedSpace
  have := hN.isManifold
  exact
    { toFun := expToN hN q
      invFun := fun y => (tangentSubspace hN q).orthogonalProjectionOnto (nc.G y)
      source := ball 0 ε
      target := {y | (y : V) ∈ nc.U}
      map_source' := fun v hv => by
        rw [mem_ball, dist_zero_right] at hv
        change (expToN hN q v : V) ∈ nc.U
        rw [coe_expToN hN (nc.exp_mem v.2 hv)]
        exact nc.exp_mem_U v v.2 hv
      map_target' := fun y hy => by
        rw [mem_ball, dist_zero_right, ← Submodule.norm_coe,
          nc.coe_orthogonalProjectionOnto_G hy y.2]
        exact nc.norm_G_lt y hy y.2
      left_inv' := fun v hv => by
        rw [mem_ball, dist_zero_right] at hv
        apply Subtype.ext
        rw [coe_expToN hN (nc.exp_mem v.2 hv), nc.coe_orthogonalProjectionOnto_G
          (nc.exp_mem_U v v.2 hv) (nc.exp_mem v.2 hv)]
        exact nc.G_exp v v.2 hv
      right_inv' := fun y hy => by
        have hy' : (y : V) ∈ nc.U := hy
        have hT := nc.G_mem y hy' y.2
        have hε := nc.norm_G_lt y hy' y.2
        apply Subtype.ext
        have hexp : exp hN q (((tangentSubspace hN q).orthogonalProjectionOnto (nc.G y) :
            tangentSubspace hN q) : V) = y := by
          rw [nc.coe_orthogonalProjectionOnto_G hy' y.2, nc.exp_G y hy' y.2]
        rw [coe_expToN hN (by rw [hexp]; exact y.2), hexp]
      open_source := isOpen_ball
      open_target := nc.isOpen_U.preimage continuous_subtype_val
      contMDiffOn_toFun := fun v hv => by
        have hv' : ‖(v : V)‖ < ε := by rwa [mem_ball, dist_zero_right] at hv
        refine (contMDiffAt_of_val_eventuallyEq hN (F := fun w : tangentSubspace hN q => nc.F w)
          ((nc.contDiffOn_F.contDiffAt (nc.isOpen_O.mem_nhds (nc.mem_O v v.2 hv'))).comp v
            (tangentSubspace hN q).subtypeL.contDiff.contDiffAt) ?_).contMDiffWithinAt
        filter_upwards [isOpen_ball.mem_nhds hv] with w hw
        rw [mem_ball, dist_zero_right] at hw
        rw [coe_expToN hN (nc.exp_mem w.2 hw)]
        exact (nc.F_eq w w.2 hw).symm
      contMDiffOn_invFun := fun y hy => by
        have hy' : (y : V) ∈ nc.U := hy
        have hG : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ (fun y : N => nc.G y) y :=
          (nc.contDiffOn_G.contDiffAt (nc.isOpen_U.mem_nhds hy')).contMDiffAt.comp y
            (hN.contMDiff_val y)
        exact ((tangentSubspace hN q).orthogonalProjectionOnto.contDiff.contMDiff.contMDiffAt.comp
          y hG).contMDiffWithinAt }

end NormalCoord

/-- **`exp_q` is a local diffeomorphism at `0`** (Milnor, p. 58, from `d(exp_q)₀ = id` and the
inverse function theorem): for every `q ∈ N` there are `ε > 0` and a `PartialDiffeomorph` of the
`ε`-ball of `T_qN` onto an open subset of `N` containing `q`, equal to `exp_q` on the ball. -/
theorem exists_expDiffeo (q : N) :
    letI := hN.chartedSpace
    ∃ ε > 0, ∃ Φ : PartialDiffeomorph 𝓘(ℝ, tangentSubspace hN q) 𝓘(ℝ, Z)
      (tangentSubspace hN q) N ∞, Φ.source = ball 0 ε ∧ q ∈ Φ.target ∧
        ∀ v ∈ Φ.source, ((Φ v : N) : V) = exp hN q v := by
  let _ := hN.chartedSpace
  obtain ⟨ε, hε, ⟨nc⟩⟩ := exists_isNormalRadius hN q
  refine ⟨ε, hε, nc.expDiffeo, rfl, ?_, fun v hv => ?_⟩
  · have := nc.exp_mem_U 0 (Submodule.zero_mem _) (by simpa using hε)
    rw [exp_zero q.2] at this
    exact this
  · have hv' : ‖(v : V)‖ < ε := by
      have : v ∈ ball (0 : tangentSubspace hN q) ε := hv
      rwa [mem_ball, dist_zero_right] at this
    exact coe_expToN hN (nc.exp_mem v.2 hv')

end Morse
