import Morse.Chapter7.Geodesic

/-!
Milnor, *Morse Theory*, §10, pp. 55–57 (Lemma 10.2), for a submanifold `N ⊆ ℝᴷ` with the induced
metric.

# Local existence of geodesics, with smooth dependence on the initial data

## Milnor's text, paraphrased

**Lemma 10.2** (p. 56): for every point `p₀` of `M` there are a neighbourhood `U` of `p₀` and a
number `ε > 0` such that for each `p ∈ U` and each `v ∈ TM_p` with `‖v‖ < ε` there is a unique
geodesic `γ_v : (-2, 2) → M` with `γ_v(0) = p` and `dγ_v/dt (0) = v`.  Proof: Theorem 10.1 in a
coordinate system gives `U`, `ε₁`, `ε₂ > 0` such that for `p ∈ U` and `‖v‖ < ε₁` the geodesic
exists on `(-2ε₂, 2ε₂)`; by homogeneity (p. 57), for `‖v‖ < ε < ε₁ε₂` the curve
`γ_v(t) = γ_{v/ε₂}(ε₂ t)` is defined for `|t| < 2`.

## The construction

* In a slice chart `σ` with parametrization `x = Morse.sliceParam σ` (defined on the open set
  `T = σ.toChart.target ⊆ Z`), `x ∘ u` is a geodesic iff `u'' = −Γ(u)(u', u')`, where
  `Γ(u)(w, w) = dx_u⁺(d²x_u(w, w))` and `A⁺ = (AᵀA)⁻¹Aᵀ` is the pseudo-inverse (`Morse.pinvL`,
  `Morse.chartAcc`).  Indeed `(x ∘ u)'' = d²x_u(u', u') + dx_u(u'')`, and `dx_u dx_u⁺ = P`, so
  for a solution `(x ∘ u)'' = (1 − P) d²x_u(u', u')` is normal (`Morse.isGeodesicOn_chart`).  This
  is the geodesic equation in Milnor's coordinates, with Christoffel symbols `Γ`.
* `Morse.chartSpray σ`: the field `(u, w) ↦ (w, −Γ(u)(w, w))` on `T × Z`, smooth
  (`Morse.contDiffOn_chartSpray`).  `Morse.LocalSpray σ u₀`: a local flow of it near `(u₀, 0)`,
  smooth in `(t, u, w)`, from Theorem 10.1 (`Morse.exists_localFlow`: bump function and the global
  flow library `Morse/Flow`).
* `Morse.LocalSpray.geo`: Milnor's rescaled geodesic `γ_v(t) = γ_{v/c}(ct)`, `c` half the time of
  existence.  It is a geodesic on `(-2, 2)` for initial data in a fixed neighbourhood of `(u₀, 0)`
  (`Morse.LocalSpray.isGeodesicOn_geo`), and smooth in all variables
  (`Morse.LocalSpray.contDiffOn_geo`).
* **Lemma 10.2**: `Morse.lemma_10_2`, including the smooth dependence of `γ_v(t)` on `(p, v, t)`
  (a smooth map on an open set of `V × V × ℝ`); uniqueness is `Morse.IsGeodesicOn.eqOn`.

## What Milnor leaves implicit

* **From coordinates to lengths.**  Theorem 10.1 gives a neighbourhood of `(p₀, 0)` in coordinates;
  to obtain "`p ∈ U` and `‖v‖ < ε₁`" one needs to bound the coordinates of `v` by its length,
  uniformly for `p` near `p₀`.  Here the coordinates of `v` are `(dσ_p v)₁`, and
  `‖dσ_p v‖ ≤ ‖dσ_p‖ ‖v‖` with `‖dσ_p‖` bounded near `p₀`.
* **Smooth dependence** of `γ_v(t)` on `(p, v, t)` is used later (smoothness of `exp`, Lemma 10.3)
  but is not part of Milnor's statement of Lemma 10.2; it is proved here.
* **Why a chart.**  The geodesic equation `(x, v)' = (v, II_x(v, v))` lives on `TN ⊆ V × V`.  A
  smooth extension of its right side to an open set of `V × V` has a flow, but the invariance of
  `TN` needs either local solutions in `N` (a chart) or an additional Grönwall estimate for the
  distance to `TN`; and `TN` need not be closed in `V × V` (`N` need not be closed in `V`), so the
  invariance criterion `Morse.IsBddLipschitz.flow_mem` does not apply as it stands.  In the chart
  the solutions lie in `N` by construction.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### The pseudo-inverse of an injective operator -/

section Pinv

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The pseudo-inverse** `A⁺ = (AᵀA)⁻¹Aᵀ : V → Y` of `A : Y → V`.  For injective `A`,
`A⁺ A = 1` (`Morse.pinvL_apply_self`) and `A A⁺` is the orthogonal projection onto `range A`
(`Morse.gramProj_eq_comp_pinvL`). -/
def pinvL (A : Y →L[ℝ] V) : V →L[ℝ] Y := (gramL A).inverse.comp (transposeL A)

omit [FiniteDimensional ℝ Y] in
theorem gramProj_eq_comp_pinvL (A : Y →L[ℝ] V) : gramProj A = A.comp (pinvL A) := rfl

theorem pinvL_apply_self {A : Y →L[ℝ] V} (hA : Injective A) (y : Y) : pinvL A (A y) = y :=
  gramL_injective hA (gramL_inverse_apply hA (gramL A y))

/-- The pseudo-inverse depends smoothly on `A` near an injective operator. -/
theorem contDiffAt_pinvL {A : Y →L[ℝ] V} (hA : Injective A) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (pinvL : (Y →L[ℝ] V) → V →L[ℝ] Y) A := by
  have h1 : ContDiff ℝ n (transposeL : (Y →L[ℝ] V) → V →L[ℝ] Y →L[ℝ] ℝ) :=
    ((ContinuousLinearMap.compL ℝ Y V ℝ).flip.contDiff).clm_comp contDiff_const
  have h2 : ContDiff ℝ n (gramL : (Y →L[ℝ] V) → Y →L[ℝ] Y →L[ℝ] ℝ) := h1.clm_comp contDiff_id
  have h3 : ContDiffAt ℝ n (fun B : Y →L[ℝ] V => (gramL B).inverse) A := by
    have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := n) (gramEquiv hA)
    rw [coe_gramEquiv] at h
    exact h.comp A h2.contDiffAt
  exact h3.clm_comp h1.contDiffAt

end Pinv

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Slice charts and their parametrizations -/

section Chart

variable (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem sliceParam_mem_source {u : Z} (hu : u ∈ σ.toChart.target) :
    sliceParam σ u ∈ σ.φ.source :=
  σ.φ.invFun_mem hu

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem sliceChart_sliceParam {u : Z} (hu : u ∈ σ.toChart.target) :
    σ.φ (sliceParam σ u) = (u, 0) :=
  σ.φ.apply_invFun hu

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- `dσ ∘ dx = (·, 0)`: the chart inverts its parametrization. -/
theorem fderiv_sliceChart_comp_fderiv_sliceParam {u : Z} (hu : u ∈ σ.toChart.target) :
    (fderiv ℝ σ.φ (sliceParam σ u)).comp (fderiv ℝ (sliceParam σ) u) =
      ContinuousLinearMap.inl ℝ Z W := by
  have hx : HasFDerivAt (sliceParam σ) (fderiv ℝ (sliceParam σ) u) u :=
    ((contDiffAt_sliceParam σ hu).differentiableAt (by simp)).hasFDerivAt
  have hφ : HasFDerivAt σ.φ (fderiv ℝ σ.φ (sliceParam σ u)) (sliceParam σ u) :=
    (Milnor.Problems.sliceChart_differentiableAt σ (sliceParam_mem_source σ hu)).hasFDerivAt
  have hev : (fun u' => σ.φ (sliceParam σ u')) =ᶠ[𝓝 u] fun u' : Z => (u', (0 : W)) := by
    filter_upwards [(isOpen_toChart_target σ).mem_nhds hu] with u' hu'
    exact σ.φ.apply_invFun hu'
  have h1 := (hφ.comp u hx).congr_of_eventuallyEq hev.symm
  have h2 : HasFDerivAt (fun u' : Z => (u', (0 : W))) (ContinuousLinearMap.inl ℝ Z W) u :=
    (hasFDerivAt_id u).prodMk (hasFDerivAt_const _ _)
  exact h1.unique h2

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem fst_fderiv_sliceChart_fderiv_sliceParam {u : Z} (hu : u ∈ σ.toChart.target) (w : Z) :
    (fderiv ℝ σ.φ (sliceParam σ u) (fderiv ℝ (sliceParam σ) u w)).1 = w := by
  have h := DFunLike.congr_fun (fderiv_sliceChart_comp_fderiv_sliceParam σ hu) w
  rw [ContinuousLinearMap.comp_apply] at h
  rw [h]
  rfl

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The tangent space at `x(u)` is the range of `dx_u`. -/
theorem tangentSubspace_sliceParam {u : Z} (hu : u ∈ σ.toChart.target) :
    tangentSubspace hN ⟨sliceParam σ u, sliceParam_mem σ hu⟩ =
      LinearMap.range (fderiv ℝ (sliceParam σ) u : Z →ₗ[ℝ] V) := by
  rw [tangentSubspace_eq_range_fderiv_sliceParam hN σ (sliceParam_mem_source σ hu)]
  change LinearMap.range (fderiv ℝ (sliceParam σ) (σ.φ (sliceParam σ u)).1 : Z →ₗ[ℝ] V) = _
  rw [sliceChart_sliceParam σ hu]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Chart coordinates of a tangent vector**: for `v ∈ T_pN`, `dx((dσ_p v)₁) = v`. -/
theorem fderiv_sliceParam_fst_fderiv {p : N} (hp : p.1 ∈ σ.φ.source) {v : V}
    (hv : v ∈ tangentSubspace hN p) :
    fderiv ℝ (sliceParam σ) (σ.φ p).1 (fderiv ℝ σ.φ p v).1 = v := by
  rw [tangentSubspace_eq_range_fderiv_sliceParam hN σ hp] at hv
  obtain ⟨z, rfl⟩ := hv
  have hu : (σ.φ p).1 ∈ σ.toChart.target := toChart_apply_mem_target σ hp
  have hx : sliceParam σ (σ.φ p).1 = p := sliceParam_toChart σ hp
  have h := fst_fderiv_sliceChart_fderiv_sliceParam σ hu z
  rw [hx] at h
  simp only [ContinuousLinearMap.coe_coe]
  rw [h]

/-- **The Christoffel term in the chart** `σ`: `Γ(u)(w, w) = dx_u⁺ (d²x_u(w, w))`. -/
def chartAcc (u w : Z) : Z :=
  pinvL (fderiv ℝ (sliceParam σ) u) (fderiv ℝ (fderiv ℝ (sliceParam σ)) u w w)

/-- **The geodesic spray in the chart** `σ`: `(u, w) ↦ (w, −Γ(u)(w, w))`. -/
def chartSpray (z : Z × Z) : Z × Z := (z.2, -chartAcc σ z.1 z.2)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem chartAcc_smul (u w : Z) (a : ℝ) : chartAcc σ u (a • w) = (a * a) • chartAcc σ u w := by
  simp [chartAcc, smul_smul]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem chartAcc_zero (u : Z) : chartAcc σ u 0 = 0 := by
  simp only [chartAcc, map_zero]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- The chart spray is smooth on `T × Z`. -/
theorem contDiffOn_chartSpray : ContDiffOn ℝ ∞ (chartSpray σ) (σ.toChart.target ×ˢ univ) := by
  set T := σ.toChart.target
  have hT : IsOpen T := isOpen_toChart_target σ
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (sliceParam σ)) T :=
    (contDiffOn_sliceParam σ).fderiv_of_isOpen hT (by simp)
  have h2 : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ (sliceParam σ))) T :=
    h1.fderiv_of_isOpen hT (by simp)
  have h3 : ContDiffOn ℝ ∞ (fun u => pinvL (fderiv ℝ (sliceParam σ) u)) T := fun u hu =>
    ((contDiffAt_pinvL (injective_fderiv_sliceParam σ hu)).comp u
      (h1.contDiffAt (hT.mem_nhds hu))).contDiffWithinAt
  have hfst : MapsTo Prod.fst (T ×ˢ (univ : Set Z)) T := fun z hz => hz.1
  have h3' := h3.comp contDiffOn_fst hfst
  have h2' := h2.comp contDiffOn_fst hfst
  exact contDiffOn_snd.prodMk
    ((h3'.clm_apply ((h2'.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd)).neg)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- The velocity of `x ∘ u` along a solution `ζ = (u, w)` of the chart equation is `dx_u w`. -/
theorem hasDerivAt_sliceParam_chart {ζ : ℝ → Z × Z} {t : ℝ} (hT : (ζ t).1 ∈ σ.toChart.target)
    (hd : HasDerivAt ζ (chartSpray σ (ζ t)) t) :
    HasDerivAt (fun t => sliceParam σ (ζ t).1) (fderiv ℝ (sliceParam σ) (ζ t).1 (ζ t).2) t := by
  have hx : HasFDerivAt (sliceParam σ) (fderiv ℝ (sliceParam σ) (ζ t).1) (ζ t).1 :=
    ((contDiffAt_sliceParam σ hT).differentiableAt (by simp)).hasFDerivAt
  exact hx.comp_hasDerivAt t (hasDerivAt_fst_comp hd)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- **Solutions of the chart equation are geodesics**: if `ζ = (u, w)` solves
`ζ' = (w, −Γ(u)(w, w))` on an open set `s`, with `u` in the chart domain, then `x ∘ u` is a
geodesic on `s` (with velocity `dx_u w`, `Morse.hasDerivAt_sliceParam_chart`): its acceleration
`d²x_u(w, w) − dx_u dx_u⁺ d²x_u(w, w) = (1 − P) d²x_u(w, w)` is normal. -/
theorem isGeodesicOn_chart {ζ : ℝ → Z × Z} {s : Set ℝ} (hs : IsOpen s)
    (hζ : ContDiffOn ℝ ∞ ζ s) (hT : ∀ t ∈ s, (ζ t).1 ∈ σ.toChart.target)
    (hd : ∀ t ∈ s, HasDerivAt ζ (chartSpray σ (ζ t)) t) :
    IsGeodesicOn hN (fun t => sliceParam σ (ζ t).1) s := by
  have hTo : IsOpen σ.toChart.target := isOpen_toChart_target σ
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (sliceParam σ)) σ.toChart.target :=
    (contDiffOn_sliceParam σ).fderiv_of_isOpen hTo (by simp)
  refine ⟨hs, fun t ht => sliceParam_mem σ (hT t ht),
    (contDiffOn_sliceParam σ).comp (contDiff_fst.comp_contDiffOn hζ) fun t ht => hT t ht,
    fun t ht => ?_⟩
  have hev : deriv (fun t => sliceParam σ (ζ t).1) =ᶠ[𝓝 t]
      fun τ => fderiv ℝ (sliceParam σ) (ζ τ).1 (ζ τ).2 :=
    eventually_of_mem (hs.mem_nhds ht) fun τ hτ =>
      (hasDerivAt_sliceParam_chart σ (hT τ hτ) (hd τ hτ)).deriv
  have hx2 : HasFDerivAt (fderiv ℝ (sliceParam σ))
      (fderiv ℝ (fderiv ℝ (sliceParam σ)) (ζ t).1) (ζ t).1 :=
    ((h1.contDiffAt (hTo.mem_nhds (hT t ht))).differentiableAt (by simp)).hasFDerivAt
  have hA : HasDerivAt (fun τ => fderiv ℝ (sliceParam σ) (ζ τ).1)
      (fderiv ℝ (fderiv ℝ (sliceParam σ)) (ζ t).1 (ζ t).2) t :=
    hx2.comp_hasDerivAt t (hasDerivAt_fst_comp (hd t ht))
  have h2 := hA.clm_apply (hasDerivAt_snd_comp (hd t ht))
  rw [hev.deriv_eq, h2.deriv]
  have hinj := injective_fderiv_sliceParam σ (hT t ht)
  set y := fderiv ℝ (fderiv ℝ (sliceParam σ)) (ζ t).1 (ζ t).2 (ζ t).2
  have key : fderiv ℝ (fderiv ℝ (sliceParam σ)) (ζ t).1 (ζ t).2 (ζ t).2 +
      fderiv ℝ (sliceParam σ) (ζ t).1 (chartSpray σ (ζ t)).2 =
      y - (LinearMap.range (fderiv ℝ (sliceParam σ) (ζ t).1 : Z →ₗ[ℝ] V)).starProjection y := by
    rw [← gramProj_eq_starProjection hinj, gramProj_eq_comp_pinvL, chartSpray, map_neg,
      ContinuousLinearMap.comp_apply, chartAcc, ← sub_eq_add_neg]
  rw [key, tangentSubspace_sliceParam hN σ (hT t ht)]
  exact Submodule.sub_starProjection_mem_orthogonal y

end Chart

/-! ### A local flow of the chart spray, and Lemma 10.2 -/

/-- **A local flow of the chart spray** near `(u₀, 0)`: Theorem 10.1 for the geodesic equation in
the chart `σ`.  `φ t z` is smooth in `(t, z)`, and for `‖z − (u₀, 0)‖ < r` the curve `t ↦ φ t z`
solves `ζ' = chartSpray σ ζ` for `|t| < τ`, with first component in the chart domain. -/
structure LocalSpray (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) (u₀ : Z) where
  φ : ℝ → Z × Z → Z × Z
  r : ℝ
  τ : ℝ
  r_pos : 0 < r
  τ_pos : 0 < τ
  contDiff : ContDiff ℝ ∞ (fun p : ℝ × (Z × Z) => φ p.1 p.2)
  zero : ∀ z ∈ ball (u₀, (0 : Z)) r, φ 0 z = z
  mem : ∀ z ∈ ball (u₀, (0 : Z)) r, ∀ t ∈ Ioo (-τ) τ, (φ t z).1 ∈ σ.toChart.target
  hasDerivAt : ∀ z ∈ ball (u₀, (0 : Z)) r, ∀ t ∈ Ioo (-τ) τ,
    HasDerivAt (fun s => φ s z) (chartSpray σ (φ t z)) t

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem nonempty_localSpray (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {u₀ : Z}
    (hu₀ : u₀ ∈ σ.toChart.target) : Nonempty (LocalSpray σ u₀) := by
  obtain ⟨φ, hφ, r, hr, τ, hτ, h⟩ := exists_localFlow
    ((isOpen_toChart_target σ).prod isOpen_univ) (contDiffOn_chartSpray σ)
    (x₁ := (u₀, 0)) ⟨hu₀, mem_univ _⟩
  exact ⟨⟨φ, r, τ, hr, hτ, hφ, fun z hz => (h z hz).1, fun z hz t ht => ((h z hz).2 t ht).1.1,
    fun z hz t ht => ((h z hz).2 t ht).2⟩⟩

namespace LocalSpray

variable {σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N} {u₀ : Z} (L : LocalSpray σ u₀)

/-- Half the time of existence: the rescaling factor in Milnor's `γ_v(t) = γ_{v/c}(ct)`. -/
def c : ℝ := L.τ / 2

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem c_pos : 0 < L.c := half_pos L.τ_pos

/-- The chart initial data `(u, w)` for which `L.geo u w` is a geodesic on `(-2, 2)`. -/
def good : Set (Z × Z) := ball u₀ L.r ×ˢ ball (0 : Z) (L.c * L.r)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem isOpen_good : IsOpen L.good := isOpen_ball.prod isOpen_ball

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem mem_good : (u₀, (0 : Z)) ∈ L.good :=
  ⟨mem_ball_self L.r_pos, mem_ball_self (mul_pos L.c_pos L.r_pos)⟩

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem mem_ball_of_good {z : Z × Z} (hz : z ∈ L.good) :
    (z.1, L.c⁻¹ • z.2) ∈ ball (u₀, (0 : Z)) L.r := by
  have h2 := hz.2
  rw [mem_ball, dist_zero_right] at h2
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  refine ⟨hz.1, ?_⟩
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos L.c_pos,
    inv_mul_lt_iff₀ L.c_pos]
  exact h2

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem mul_mem_Ioo {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) : L.c * t ∈ Ioo (-L.τ) L.τ := by
  have hτ := L.τ_pos
  unfold c
  constructor <;> nlinarith [ht.1, ht.2]

/-- Position and velocity, in the chart, of the geodesic with chart initial data `(u, w)`. -/
def chartCurve (u w : Z) (t : ℝ) : Z × Z :=
  ((L.φ (L.c * t) (u, L.c⁻¹ • w)).1, L.c • (L.φ (L.c * t) (u, L.c⁻¹ • w)).2)

/-- **The geodesic with initial point `x(u)` and initial velocity `dx_u w`**: Milnor's rescaling
`γ_v(t) = γ_{v/c}(ct)` of a flow line of the chart spray. -/
def geo (u w : Z) (t : ℝ) : V := sliceParam σ (L.φ (L.c * t) (u, L.c⁻¹ • w)).1

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem contDiff_chartCurve (u w : Z) : ContDiff ℝ ∞ (L.chartCurve u w) := by
  have h : ContDiff ℝ ∞ (fun t => L.φ (L.c * t) (u, L.c⁻¹ • w)) :=
    L.contDiff.comp ((contDiff_const.mul contDiff_id).prodMk contDiff_const)
  exact (contDiff_fst.comp h).prodMk (contDiff_const.smul (contDiff_snd.comp h))

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem hasDerivAt_chartCurve {u w : Z} (h : (u, w) ∈ L.good) {t : ℝ}
    (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (L.chartCurve u w) (chartSpray σ (L.chartCurve u w t)) t := by
  have hz := L.mem_ball_of_good h
  have hlin : HasDerivAt (fun t : ℝ => L.c * t) L.c t := by
    simpa using (hasDerivAt_id t).const_mul L.c
  have h1 : HasDerivAt (fun t => L.φ (L.c * t) (u, L.c⁻¹ • w))
      (L.c • chartSpray σ (L.φ (L.c * t) (u, L.c⁻¹ • w))) t :=
    (L.hasDerivAt _ hz _ (L.mul_mem_Ioo ht)).scomp t hlin
  have h2 := (hasDerivAt_fst_comp h1).prodMk ((hasDerivAt_snd_comp h1).const_smul L.c)
  have e : chartSpray σ (L.chartCurve u w t) =
      ((L.c • chartSpray σ (L.φ (L.c * t) (u, L.c⁻¹ • w))).1,
        L.c • (L.c • chartSpray σ (L.φ (L.c * t) (u, L.c⁻¹ • w))).2) := by
    simp only [chartSpray, chartCurve, chartAcc_smul, Prod.smul_mk, smul_neg, smul_smul]
  rw [e]
  exact h2

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem chartCurve_zero {u w : Z} (h : (u, w) ∈ L.good) : L.chartCurve u w 0 = (u, w) := by
  have hz := L.zero _ (L.mem_ball_of_good h)
  simp only [chartCurve, mul_zero, hz, smul_smul, mul_inv_cancel₀ L.c_pos.ne', one_smul]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
/-- `L.geo u w` is a geodesic on `(-2, 2)`, with initial velocity `dx_u w`. -/
theorem isGeodesicOn_geo {u w : Z} (h : (u, w) ∈ L.good) :
    IsGeodesicOn hN (L.geo u w) (Ioo (-2) 2) :=
  isGeodesicOn_chart hN σ (ζ := L.chartCurve u w) isOpen_Ioo (L.contDiff_chartCurve u w).contDiffOn
    (fun _ ht => L.mem _ (L.mem_ball_of_good h) _ (L.mul_mem_Ioo ht))
    (fun _ ht => L.hasDerivAt_chartCurve h ht)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem geo_zero {u w : Z} (h : (u, w) ∈ L.good) : L.geo u w 0 = sliceParam σ u := by
  have := congrArg Prod.fst (L.chartCurve_zero h)
  simp only [chartCurve] at this
  simp only [geo, this]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem hasDerivAt_geo_zero {u w : Z} (h : (u, w) ∈ L.good) :
    HasDerivAt (L.geo u w) (fderiv ℝ (sliceParam σ) u w) 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have := hasDerivAt_sliceParam_chart σ (L.mem _ (L.mem_ball_of_good h) _ (L.mul_mem_Ioo h0))
    (L.hasDerivAt_chartCurve h h0)
  rwa [L.chartCurve_zero h] at this

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **Smooth dependence on the initial data**: `(u, w, t) ↦ γ(t)` is smooth for chart initial data
`(u, w)` near `(u₀, 0)` and `|t| < 2`. -/
theorem contDiffOn_geo :
    ContDiffOn ℝ ∞ (fun p : (Z × Z) × ℝ => L.geo p.1.1 p.1.2 p.2) (L.good ×ˢ Ioo (-2) 2) := by
  have hF : ContDiff ℝ ∞ (fun p : (Z × Z) × ℝ => L.φ (L.c * p.2) (p.1.1, L.c⁻¹ • p.1.2)) :=
    L.contDiff.comp ((contDiff_const.mul contDiff_snd).prodMk
      ((contDiff_fst.comp contDiff_fst).prodMk (contDiff_const.smul (contDiff_snd.comp
        contDiff_fst))))
  exact (contDiffOn_sliceParam σ).comp (contDiff_fst.comp hF).contDiffOn
    fun p hp => L.mem _ (L.mem_ball_of_good hp.1) _ (L.mul_mem_Ioo hp.2)

end LocalSpray

/-- **Milnor's Lemma 10.2** (p. 56), with smooth dependence on the initial data.  For every
`q₀ ∈ N` there are an open set `U ∋ q₀` of `V`, an `ε > 0` and a map `Γ : V × V × ℝ → V`, smooth on
`U × B_ε(0) × (-2, 2)`, such that for every `p ∈ N ∩ U` and every `v ∈ T_pN` with `‖v‖ < ε`,
`γ_v = Γ(p, v, ·)` is a geodesic on `(-2, 2)` with `γ_v(0) = p` and `γ_v'(0) = v`, and it is the
only one (`Morse.IsGeodesicOn.eqOn`). -/
theorem lemma_10_2 (q₀ : N) :
    ∃ U : Set V, IsOpen U ∧ (q₀ : V) ∈ U ∧ ∃ ε > 0, ∃ Γ : V × V × ℝ → V,
      ContDiffOn ℝ ∞ Γ (U ×ˢ ball (0 : V) ε ×ˢ Ioo (-2) 2) ∧
      ∀ p : N, (p : V) ∈ U → ∀ v ∈ tangentSubspace hN p, ‖v‖ < ε →
        IsGeodesicOn hN (fun t => Γ (p, v, t)) (Ioo (-2) 2) ∧ Γ (p, v, 0) = p ∧
          HasDerivAt (fun t => Γ (p, v, t)) v 0 ∧
          ∀ γ : ℝ → V, IsGeodesicOn hN γ (Ioo (-2) 2) → γ 0 = p → deriv γ 0 = v →
            EqOn γ (fun t => Γ (p, v, t)) (Ioo (-2) 2) := by
  set σ := sliceAt hN q₀
  have hq₀ : (q₀ : V) ∈ σ.φ.source := mem_sliceAt_source hN q₀
  set u₀ := (σ.φ q₀).1
  have hu₀ : u₀ ∈ σ.toChart.target := toChart_apply_mem_target σ hq₀
  obtain ⟨L⟩ := nonempty_localSpray σ hu₀
  set C := ‖fderiv ℝ σ.φ q₀‖ + 1 with hC_def
  have hC : 0 < C := by positivity
  have hφ := Milnor.Problems.sliceChart_contDiffOn σ
  have hdφ : ContDiffOn ℝ ∞ (fun p => fderiv ℝ σ.φ p) σ.φ.source :=
    hφ.fderiv_of_isOpen σ.φ.open_source (by simp)
  set U := σ.φ.source ∩ (fun p => ((σ.φ p).1, fderiv ℝ σ.φ p)) ⁻¹' (ball u₀ L.r ×ˢ ball 0 C)
    with hU_def
  have hU : IsOpen U :=
    ((continuous_fst.comp_continuousOn hφ.continuousOn).prodMk
      hdφ.continuousOn).isOpen_inter_preimage σ.φ.open_source (isOpen_ball.prod isOpen_ball)
  have hq₀U : (q₀ : V) ∈ U := ⟨hq₀, mem_ball_self L.r_pos, by
    rw [mem_ball, dist_zero_right]; linarith⟩
  set ε := L.c * L.r / C with hε_def
  have hε : 0 < ε := div_pos (mul_pos L.c_pos L.r_pos) hC
  -- the chart data of `(p, v)` is good
  have hgood : ∀ p ∈ U, ∀ v : V, ‖v‖ < ε → ((σ.φ p).1, (fderiv ℝ σ.φ p v).1) ∈ L.good := by
    intro p hp v hv
    refine ⟨hp.2.1, ?_⟩
    rw [mem_ball, dist_zero_right]
    have h1 : ‖fderiv ℝ σ.φ p‖ < C := by
      have := hp.2.2
      rwa [mem_ball, dist_zero_right] at this
    calc ‖(fderiv ℝ σ.φ p v).1‖ ≤ ‖fderiv ℝ σ.φ p v‖ := norm_fst_le _
      _ ≤ ‖fderiv ℝ σ.φ p‖ * ‖v‖ := (fderiv ℝ σ.φ p).le_opNorm v
      _ ≤ C * ‖v‖ := by gcongr
      _ < C * ε := by gcongr
      _ = L.c * L.r := by rw [hε_def]; field_simp
  refine ⟨U, hU, hq₀U, ε, hε, fun z => L.geo (σ.φ z.1).1 (fderiv ℝ σ.φ z.1 z.2.1).1 z.2.2, ?_, ?_⟩
  · have hin : ContDiffOn ℝ ∞ (fun z : V × V × ℝ =>
        (((σ.φ z.1).1, (fderiv ℝ σ.φ z.1 z.2.1).1), z.2.2))
        (U ×ˢ ball (0 : V) ε ×ˢ Ioo (-2) 2) := by
      have hmaps : MapsTo Prod.fst (U ×ˢ ball (0 : V) ε ×ˢ Ioo (-2 : ℝ) 2) σ.φ.source :=
        fun z hz => hz.1.1
      refine ((contDiff_fst.comp_contDiffOn (hφ.comp contDiffOn_fst hmaps)).prodMk
        (contDiff_fst.comp_contDiffOn ((hdφ.comp contDiffOn_fst hmaps).clm_apply
          (contDiff_fst.comp contDiff_snd).contDiffOn))).prodMk
        (contDiff_snd.comp contDiff_snd).contDiffOn
    exact L.contDiffOn_geo.comp hin fun z hz => ⟨hgood _ hz.1 _ (by
      have := hz.2.1; rwa [mem_ball, dist_zero_right] at this), hz.2.2⟩
  · intro p hp v hv hvε
    have hg := hgood p hp v hvε
    have h0 : L.geo (σ.φ p).1 (fderiv ℝ σ.φ p v).1 0 = p := by
      simp only [L.geo_zero hg]
      exact sliceParam_toChart σ hp.1
    have hd : HasDerivAt (L.geo (σ.φ p).1 (fderiv ℝ σ.φ p v).1) v 0 := by
      have := L.hasDerivAt_geo_zero hg
      rwa [fderiv_sliceParam_fst_fderiv hN σ hp.1 hv] at this
    refine ⟨L.isGeodesicOn_geo hN hg, h0, hd, fun γ hγ hγ0 hγ0' => ?_⟩
    exact hγ.eqOn (L.isGeodesicOn_geo hN hg) isPreconnected_Ioo ⟨by norm_num, by norm_num⟩
      (hγ0.trans h0.symm) (hγ0'.trans hd.deriv.symm)

end Morse
