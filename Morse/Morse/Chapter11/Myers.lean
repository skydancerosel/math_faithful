import Morse.Chapter11.Curvature
import Morse.Chapter6.SphereCurvature
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Milnor, *Morse Theory*, §19, pp. 103–106: the Ricci tensor, Myers' theorem (Theorem 19.4),
Corollary 19.5 and the example of the sphere, for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Positive Ricci curvature: Myers' theorem

## Milnor's text, paraphrased

* **Definition** (p. 104): the *Ricci tensor* at `p` is the bilinear pairing
  `K(U₁, U₂) = trace (W ↦ R(U₁, W)U₂)` on `TM_p`; it is symmetric ("it follows easily from 9.3").
* **Assertion** (p. 104): for an orthonormal basis `U₁, …, Uₙ`, `K(Uₙ, Uₙ)` is the sum of the
  sectional curvatures `⟨R(Uₙ, Uᵢ)Uₙ, Uᵢ⟩`, `i = 1, …, n − 1`.
* **Theorem 19.4** (Myers, p. 104): if `K(U, U) ≥ (n − 1)/r²` for every unit vector `U`, every
  geodesic of length `> πr` contains conjugate points, and hence is not minimal.  Proof: with
  orthonormal parallel fields `P₁, …, Pₙ` along `γ : [0, 1] → M`, `Pₙ` along `γ`, `V = L Pₙ`, and
  `Wᵢ(t) = sin(πt) Pᵢ(t)`, the second variation formula gives
  `½ E_**(Wᵢ, Wᵢ) = ∫₀¹ sin²(πt) (π² − L² ⟨R(Pₙ, Pᵢ)Pₙ, Pᵢ⟩) dt`; summing over `i < n`,
  `Σ ½ E_**(Wᵢ, Wᵢ) = ∫₀¹ sin²(πt) ((n − 1)π² − L² K(Pₙ, Pₙ)) dt < 0` when `L > πr`.  So
  `E_**(Wᵢ, Wᵢ) < 0` for some `i`, the index is positive, and the index theorem gives conjugate
  points; a variation with field `Wᵢ` decreases the energy, so `γ` is not minimal.
* **Example** (p. 105): on a sphere of radius `r` every sectional curvature is `1/r²`, so
  `K(U, U) = (n − 1)/r²`, and 19.4 is best possible.
* **Corollary 19.5** (p. 105): if `M` is complete and `K(U, U) ≥ (n − 1)/r² > 0`, then `M` is
  compact with diameter `≤ πr`: a minimal geodesic joining two points has length `≤ πr`, and
  closed bounded sets are compact.  It applies to the universal cover, so `π₁(M)` is finite.
* **Theorem 19.6** (p. 106): if `M` is compact with positive definite Ricci tensor, `Ω(M; p, q)`
  has the homotopy type of a CW complex with finitely many cells in each dimension.

## In the embedded setting

* `Morse.ricci hN q U₁ U₂`: the Ricci tensor, literally as a trace on `T_qN`;
  `Morse.ricci_eq_sum`: its value in an orthonormal basis; `Morse.ricci_comm`: **symmetry**, from
  the pair symmetry of Lemma 9.3 (4); `Morse.ricci_eq_sum_erase`: **the Assertion**.
* `Morse.RicciLowerBound hN r`: the hypothesis `K(U, U) ≥ (n − 1)/r²`, `n = dim N`.
* `Morse.exists_smooth_extension`: a geodesic `γ : [0, 1] → N` agrees on `[0, 1]` with a smooth
  curve `c : ℝ → N` (its extension past the end points composed with the clamp
  `Morse.exists_smooth_clamp`), along which `L(γ)⁻¹ γ'` is parallel; this is what makes the
  parallel transport of Chapter 6 (along curves defined on `ℝ`) available.
* `Morse.energyHessian_sin_parallel`: `½ E_**(sin(πt) P, sin(πt) P) =
  ∫₀¹ (π² cos²(πt) − sin²(πt) ⟨R(V, P)V, P⟩) dt` for a parallel unit field `P`.
* `Morse.exists_energyHessian_neg` and **Theorem 19.4**, `Morse.theorem_19_4`: for `n ≥ 2`, a
  geodesic of length `> πr` has a conjugate point `γ(t)`, `0 < t < 1`, and is not minimal.
* **Corollary 19.5**, `Morse.corollary_19_5`: for `N` connected and complete, distances are
  `≤ πr` and `N` is compact.
* **The sphere**: `Morse.ricci_sph` (`K(U, U) = (n − 1)‖U‖²` on the unit sphere `Sⁿ`),
  `Morse.ricciLowerBound_sph`, and `Morse.sphere_myers` (19.4 and 19.5 for `Sⁿ`, `r = 1`).

## Not done here

* **Depending on §17** (and §16.3): **Theorem 19.6**.  Its index estimate (a geodesic of length
  `> kπr` has index `≥ k`) needs only the index form and is `Morse.theorem_19_6_index` in
  `Morse/Chapter11/LongGeodesics.lean`.
* Not depending on §17 but not formalized: "best possible" in the example (that a half great
  circle has no interior conjugate point), the radius-`r` sphere, and the finiteness of `π₁(M)`
  (covering spaces); the remarks on `Sᵐ × Sᵏ` and Synge's theorem (p. 106).

## What Milnor leaves implicit

* **`n ≥ 2` in Theorem 19.4** (a hidden hypothesis, recorded in `Exposition/Findings.md`): for
  `n = 1` the Ricci tensor vanishes, the hypothesis `0 ≥ 0` holds, and the conclusion fails on a
  line.  In Corollary 19.5 it is forced by `(n − 1)/r² > 0`.
* **Parallel fields along `γ : [0, 1] → M`**, orthonormal everywhere, with `Pₙ = V/L`: this uses
  Lemma 8.2 on `[0, 1]` (here: extending `γ` to `ℝ` first), the constant speed `L = L(γ)` of a
  geodesic parametrized on `[0, 1]`, and that `V` itself is parallel, so that it stays a multiple
  of the parallel transport of `Pₙ(0)`.
* **The trace in the Assertion** is computed in the orthonormal basis `Pᵢ(t)` of `T_{γ(t)}M`, so
  the frame must be orthonormal at every `t`, i.e. parallel transport must be an isometry onto
  the tangent space (Chapter 6).
* **The integral form**: Milnor's formula `−∫⟨W, D²W/dt² + R(V, W)V⟩` is used here in the form
  `∫(‖DW/dt‖² − ⟨R(V, W)V, W⟩)` (Proposition 13.A of the exposition), so `π² cos²(πt)` appears
  instead of `π² sin²(πt)`; both integrate to `π²/2` (`Morse.integral_cos_sq_pi_mul`).
* **Corollary 19.5** needs `M` connected (for the minimal geodesics of Hopf–Rinow) and uses that
  `M` is closed and bounded in itself.
-/

open Set Filter Topology Function Module Metric Real
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### The Ricci tensor -/

variable (hN) in
/-- **The Ricci tensor** at `q` (Milnor p. 104): the bilinear pairing `K(U₁, U₂)` on `T_qN`, the
trace of the linear map `W ↦ R(U₁, W)U₂` of `T_qN`. -/
def ricci (q : N) (U₁ U₂ : tangentSubspace hN q) : ℝ :=
  LinearMap.trace ℝ (tangentSubspace hN q) ((curvTensor hN q U₁).flip U₂)

omit [FiniteDimensional ℝ W] in
/-- The Ricci tensor in an orthonormal basis: `K(U₁, U₂) = Σᵢ ⟨R(U₁, Eᵢ)U₂, Eᵢ⟩`. -/
theorem ricci_eq_sum {q : N} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (tangentSubspace hN q)) (U₁ U₂ : tangentSubspace hN q) :
    ricci hN q U₁ U₂ = ∑ i, ⟪curvOp hN q U₁ (b i) U₂, (b i : V)⟫ := by
  rw [ricci, LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm, Submodule.coe_inner]
  rfl

/-- **The Ricci tensor is symmetric** (Milnor p. 104, "it follows easily from 9.3"): by the pair
symmetry `⟨R(X, Y)Z, W⟩ = ⟨R(Z, W)X, Y⟩` of Lemma 9.3 (4), in an orthonormal basis. -/
theorem ricci_comm (q : N) (U₁ U₂ : tangentSubspace hN q) :
    ricci hN q U₁ U₂ = ricci hN q U₂ U₁ := by
  set b := stdOrthonormalBasis ℝ (tangentSubspace hN q)
  rw [ricci_eq_sum b, ricci_eq_sum b]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (isCurvatureTensor_curvTensor hN q).inner_comm_pairs U₁ (b i) U₂ (b i)
  rwa [Submodule.coe_inner, Submodule.coe_inner, coe_curvTensor_apply,
    coe_curvTensor_apply] at this

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curvOp_self (q : N) (x : V) : curvOp hN q x x = 0 := by
  simp [curvOp]

omit [FiniteDimensional ℝ W] in
/-- **Milnor's Assertion** (p. 104): if `U₁, …, Uₙ` is an orthonormal basis of `T_qN`, then
`K(Uₙ, Uₙ)` is the sum of the sectional curvatures `⟨R(Uₙ, Uᵢ)Uₙ, Uᵢ⟩`, `i ≠ n`: the `n`-th
diagonal entry of the matrix of `W ↦ R(Uₙ, W)Uₙ` vanishes because `R(Uₙ, Uₙ) = 0`. -/
theorem ricci_eq_sum_erase {q : N} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ (tangentSubspace hN q)) (i₀ : ι) :
    ricci hN q (b i₀) (b i₀) =
      ∑ i ∈ Finset.univ.erase i₀, ⟪curvOp hN q (b i₀) (b i) (b i₀), (b i : V)⟫ := by
  rw [ricci_eq_sum b, ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀), curvOp_self,
    zero_apply, inner_zero_left, zero_add]

/-! ### Two auxiliary facts -/

/-- A smooth map `ℝ → [−a, 1 + a]` equal to the identity on `[0, 1]` (built from
`Real.smoothTransition`); it extends a curve given near `[0, 1]` to a smooth curve on `ℝ`. -/
theorem exists_smooth_clamp {a : ℝ} (ha : 0 < a) : ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧
    (∀ t ∈ Icc (0 : ℝ) 1, φ t = t) ∧ ∀ t, φ t ∈ Icc (-a) (1 + a) := by
  set τ := Real.smoothTransition
  refine ⟨fun t => t + (1 + a - t) * τ ((t - 1) / a) + (-a - t) * τ (-t / a), ?_, ?_, ?_⟩
  · have hτ : ContDiff ℝ ∞ τ := Real.smoothTransition.contDiff
    fun_prop
  · intro t ht
    have h1 : τ ((t - 1) / a) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2])
        ha.le)
    have h2 : τ (-t / a) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.1])
        ha.le)
    simp only [h1, h2, mul_zero, add_zero]
  · intro t
    beta_reduce
    have hs0 := Real.smoothTransition.nonneg ((t - 1) / a)
    have hs1 := Real.smoothTransition.le_one ((t - 1) / a)
    have hr0 := Real.smoothTransition.nonneg (-t / a)
    have hr1 := Real.smoothTransition.le_one (-t / a)
    rcases le_total t 0 with ht | ht
    · have h1 : τ ((t - 1) / a) = 0 :=
        Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)
      rw [h1]
      rcases le_total t (-a) with ht' | ht'
      · have h2 : τ (-t / a) = 1 :=
          Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ ha]; linarith)
        rw [h2]
        constructor <;> nlinarith
      · constructor <;> nlinarith
    · have h2 : τ (-t / a) = 0 :=
        Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)
      rw [h2]
      rcases le_total (1 + a) t with ht' | ht'
      · have h1 : τ ((t - 1) / a) = 1 :=
          Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ ha]; linarith)
        rw [h1]
        constructor <;> nlinarith
      · rcases le_total t 1 with ht'' | ht''
        · have h1 : τ ((t - 1) / a) = 0 :=
            Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
              ha.le)
          rw [h1]
          constructor <;> nlinarith
        · constructor <;> nlinarith

/-- `∫₀¹ sin²(πt) dt = ∫₀¹ cos²(πt) dt = 1/2`. -/
theorem integral_sin_sq_pi_mul : ∫ t in (0 : ℝ)..1, sin (π * t) ^ 2 = 1 / 2 := by
  have h := intervalIntegral.integral_comp_mul_left (fun x => sin x ^ 2) (c := π) pi_ne_zero
    (a := 0) (b := 1)
  simp only [mul_zero, mul_one] at h
  rw [h, integral_sin_sq]
  simp only [sin_zero, cos_zero, sin_pi, cos_pi, smul_eq_mul]
  field_simp
  ring

theorem integral_cos_sq_pi_mul : ∫ t in (0 : ℝ)..1, cos (π * t) ^ 2 = 1 / 2 := by
  have h := intervalIntegral.integral_comp_mul_left (fun x => cos x ^ 2) (c := π) pi_ne_zero
    (a := 0) (b := 1)
  simp only [mul_zero, mul_one] at h
  rw [h, integral_cos_sq]
  simp only [sin_zero, cos_zero, sin_pi, cos_pi, smul_eq_mul]
  field_simp
  ring

/-! ### The test fields `sin(πt) P(t)` -/

/-- **The second variation along `W = sin(πt) P(t)`** (Milnor p. 105): let `γ ∈ Ω(N; p, q)` be a
geodesic agreeing on `[0, 1]` with a smooth curve `c : ℝ → N`, `P` a parallel unit field along `c`
and `Vf` a field equal to `dγ/dt` on `(0, 1)`.  Then `W ∈ TΩ_γ` and
`½ E_**(W, W) = ∫₀¹ (π² cos²(πt) − sin²(πt) ⟨R(V, P)V, P⟩) dt`, since `DW/dt = π cos(πt) P`. -/
theorem energyHessian_sin_parallel {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    {c : ℝ → N} (hcs : ContDiff ℝ ∞ (fun t => (c t : V)))
    (hγc : ∀ t ∈ Icc (0 : ℝ) 1, γ t = c t) {P : ℝ → V} (hP : IsParallel hN c P)
    (hP1 : ∀ t, ‖P t‖ = 1) {Vf : ℝ → V} (hVγ : ∀ t ∈ Ioo (0 : ℝ) 1, deriv γ t = Vf t) :
    ∃ hW : (fun t => sin (π * t) • P t) ∈ pathTangent hN γ,
      energyHessian hN hγ ⟨_, hW⟩ ⟨_, hW⟩ = 2 * ∫ t in (0 : ℝ)..1,
        (π ^ 2 * cos (π * t) ^ 2 -
          sin (π * t) ^ 2 * ⟪curvR hN (c t) (Vf t) (P t) (Vf t), P t⟫) := by
  have hPs : ContDiff ℝ ∞ P := hP.contDiff hN hcs
  have hsin : ContDiff ℝ ∞ (fun t : ℝ => sin (π * t)) :=
    contDiff_sin.comp (contDiff_const.mul contDiff_id)
  have hWs : ContDiff ℝ ∞ (fun t => sin (π * t) • P t) := hsin.smul hPs
  have hT : ∀ t, prj hN (c t) (P t) = P t := fun t => (prj_eq_self_iff hN (c t).2).2 (hP.mem t)
  have hW : (fun t => sin (π * t) • P t) ∈ pathTangent hN γ := by
    refine ⟨IsPiecewiseSmooth.of_contDiff hWs zero_le_one, fun t ht => ?_, ?_, ?_⟩
    · simp only [map_smul, hγc t ht, hT]
    · simp
    · simp [sin_pi]
  refine ⟨hW, ?_⟩
  rw [energyHessian_eq_integral]
  congr 1
  refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => ?_
  have hγt : γ t = c t := hγc t (Ioo_subset_Icc_self ht)
  have hd : HasDerivAt (fun s => sin (π * s) • P s)
      (sin (π * t) • deriv P t + (cos (π * t) * π) • P t) t := by
    have h1 : HasDerivAt (fun s => sin (π * s)) (cos (π * t) * π) t := by
      simpa using ((hasDerivAt_id t).const_mul π).sin
    exact h1.smul (hP.differentiable t).hasDerivAt
  have hprj0 : prj hN (c t) (deriv P t) = 0 := by
    rw [prj_of_mem hN (c t).2]
    exact hP.covDeriv_eq_zero t
  have hcov : covD hN γ (fun s => sin (π * s) • P s) t = (π * cos (π * t)) • P t := by
    rw [covD, hd.deriv, hγt, map_add, map_smul, map_smul, hprj0, hT, smul_zero, zero_add,
      mul_comm]
  change ⟪covD hN γ (fun s => sin (π * s) • P s) t, covD hN γ (fun s => sin (π * s) • P s) t⟫ -
      ⟪curvR hN (γ t) (deriv γ t) (sin (π * t) • P t) (deriv γ t), sin (π * t) • P t⟫ = _
  rw [hcov, hγt, hVγ t ht, curvR_of_mem hN (c t).2, curvOp_smul_right, real_inner_smul_left,
    real_inner_smul_right, smul_apply, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hP1, ← curvR_of_mem hN (c t).2]
  ring

/-! ### Theorem 19.4 -/

variable (hN) in
/-- **Milnor's hypothesis of Theorem 19.4** (p. 104): `K(U, U) ≥ (n − 1)/r²` for every unit
vector `U` at every point of `N`, `n = dim N`. -/
def RicciLowerBound (r : ℝ) : Prop :=
  ∀ q : N, ∀ U : tangentSubspace hN q, ‖U‖ = 1 → ((finrank ℝ Z : ℝ) - 1) / r ^ 2 ≤ ricci hN q U U

/-- **A geodesic segment extends to a smooth curve on `ℝ`**: a geodesic `γ ∈ Ω` agrees on `[0, 1]`
with a smooth curve `c : ℝ → N` (the radial geodesic of `γ'(0)`, defined near `[0, 1]`, composed
with `Morse.exists_smooth_clamp`), and `γ'` agrees on `(0, 1)` with the smooth field
`Vf(t) = (dc/ds)(φ(t))`, which has constant norm `L(γ)` and is, up to the factor `L(γ)`, a parallel
field along `c`. -/
theorem exists_smooth_extension {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) : ∃ c : ℝ → N, ContDiff ℝ ∞ (fun t => (c t : V)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t = c t) ∧ ∃ Vf : ℝ → V, ContDiff ℝ ∞ Vf ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, deriv γ t = Vf t) ∧ (∀ t, ‖Vf t‖ = pathLength γ 0 1) ∧
      (∀ t, Vf t ∈ tangentSubspace hN (c t)) ∧
      IsParallel hN c (fun t => (pathLength γ 0 1)⁻¹ • Vf t) := by
  set hc := hgeo.isSmoothCurveIn hN hγ
  obtain ⟨η, hη, hray, hrayγ⟩ := exists_initial_ray hc hgeo.2
  set ray : ℝ → V := fun t => exp hN (γ 0) (t • velAlong γ 0) with hraydef
  have hIcc : Icc (0 : ℝ) 1 ⊆ Ioo (-η) (1 + η) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h0I : (0 : ℝ) ∈ Ioo (-η) (1 + η) := hIcc ⟨le_rfl, zero_le_one⟩
  -- the speed of the ray is `L`
  have hLray : pathLength γ 0 1 = ‖deriv ray 0‖ := by
    have h1 := hray.pathLength_eq isPreconnected_Ioo zero_le_one hIcc h0I
    rw [sub_zero, mul_one] at h1
    rw [← h1]
    refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => ?_
    have hev : γ =ᶠ[𝓝 t] ray :=
      eventually_of_mem (Icc_mem_nhds ht.1 ht.2) fun s hs => (hrayγ s hs).symm
    simp only [hev.deriv_eq]
  have hspeed : ∀ t ∈ Ioo (-η) (1 + η), ‖deriv ray t‖ = pathLength γ 0 1 := fun t ht => by
    rw [hLray]; exact hray.norm_deriv_eq isPreconnected_Ioo ht h0I
  -- the smooth curve `c = ray ∘ φ`
  obtain ⟨φ, hφs, hφid, hφmem⟩ := exists_smooth_clamp (half_pos hη)
  have hφI : ∀ t, φ t ∈ Ioo (-η) (1 + η) := fun t =>
    ⟨by linarith [(hφmem t).1], by linarith [(hφmem t).2]⟩
  set c : ℝ → N := fun t => ⟨ray (φ t), hray.mem _ (hφI t)⟩ with hcdef
  have hcs : ContDiff ℝ ∞ (fun t => (c t : V)) := hray.contDiffOn.comp_contDiff hφs hφI
  have hγc : ∀ t ∈ Icc (0 : ℝ) 1, γ t = c t := fun t ht => by
    change γ t = ray (φ t)
    rw [hφid t ht]
    exact (hrayγ t ht).symm
  -- the velocity field
  set Vf : ℝ → V := fun t => deriv ray (φ t) with hVfdef
  have hVfs : ContDiff ℝ ∞ Vf := hray.contDiffOn_deriv.comp_contDiff hφs hφI
  have hVγ : ∀ t ∈ Ioo (0 : ℝ) 1, deriv γ t = Vf t := fun t ht => by
    have hev : γ =ᶠ[𝓝 t] ray :=
      eventually_of_mem (Icc_mem_nhds ht.1 ht.2) fun s hs => (hrayγ s hs).symm
    change deriv γ t = deriv ray (φ t)
    rw [hφid t (Ioo_subset_Icc_self ht), hev.deriv_eq]
  have hVfT : ∀ t, Vf t ∈ tangentSubspace hN (c t) := fun t => hray.deriv_mem (hφI t)
  refine ⟨c, hcs, hγc, Vf, hVfs, hVγ, fun t => hspeed _ (hφI t), hVfT, ?_⟩
  -- `L⁻¹ Vf` is parallel along `c`: its derivative is `φ'(t) γ''(φ t)`, normal to `N`
  refine ⟨fun t => Submodule.smul_mem _ _ (hVfT t), (hVfs.const_smul _).differentiable (by simp),
    fun t => ?_⟩
  have hd : HasDerivAt Vf (deriv φ t • deriv (deriv ray) (φ t)) t :=
    (hray.hasDerivAt_deriv (hφI t)).scomp t (hφs.differentiable (by simp) t).hasDerivAt
  have hd' : HasDerivAt (fun t => (pathLength γ 0 1)⁻¹ • Vf t)
      ((pathLength γ 0 1)⁻¹ • (deriv φ t • deriv (deriv ray) (φ t))) t := hd.const_smul _
  rw [covDeriv, hd'.deriv, map_smul, map_smul]
  change (pathLength γ 0 1)⁻¹ • deriv φ t • tanProj hN ⟨ray (φ t), _⟩ (deriv (deriv ray) (φ t)) = 0
  rw [hray.tanProj_deriv_deriv (hφI t), smul_zero, smul_zero]

/-- **An orthonormal parallel frame along a geodesic, with one vector along `γ'`** (Milnor
p. 104: parallel fields `P₁, …, Pₙ` along `γ`, orthonormal at one point and hence everywhere, with
`Pₙ` pointing along `γ`).  For a geodesic `γ ∈ Ω(N; p, q)` of length `L > 0` there are a smooth
curve `c : ℝ → N` equal to `γ` on `[0, 1]` (`Morse.exists_smooth_extension`), a smooth field `Vf`
along `c` equal to `γ'` on `(0, 1)`, and parallel unit fields `P_i` along `c`; the indices in `s`
are the `n − 1` frame vectors other than `Vf/L`, and under the hypothesis of Theorem 19.4
`Σ_{i ∈ s} ⟨R(V, P_i)V, P_i⟩ ≥ L²(n − 1)/r²`: by the Assertion of p. 104 the sum is
`L² K(Vf/L, Vf/L)`, computed in the orthonormal basis `P_i(t)` of `T_{c(t)}N`. -/
theorem exists_parallel_frame {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) (hL : 0 < pathLength γ 0 1) :
    ∃ c : ℝ → N, ContDiff ℝ ∞ (fun t => (c t : V)) ∧ (∀ t ∈ Icc (0 : ℝ) 1, γ t = c t) ∧
    ∃ Vf : ℝ → V, ContDiff ℝ ∞ Vf ∧ (∀ t, Vf t ∈ tangentSubspace hN (c t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, deriv γ t = Vf t) ∧
    ∃ (u : Finset (tangentSubspace hN (c 0))) (s : Finset u) (P : u → ℝ → V),
      (∀ i, IsParallel hN c (P i)) ∧ (∀ i t, ‖P i t‖ = 1) ∧ s.card + 1 = finrank ℝ Z ∧
      ∀ r : ℝ, RicciLowerBound hN r → ∀ t, pathLength γ 0 1 ^ 2 * (s.card / r ^ 2) ≤
        ∑ i ∈ s, ⟪curvR hN (c t) (Vf t) (P i t) (Vf t), P i t⟫ := by
  classical
  set L := pathLength γ 0 1 with hLdef
  obtain ⟨c, hcs, hγc, Vf, hVfs, hVγ, hVn, hVfT, hTpar⟩ := exists_smooth_extension hγ hgeo
  refine ⟨c, hcs, hγc, Vf, hVfs, hVfT, hVγ, ?_⟩
  -- an orthonormal basis of `T_{c(0)}N` containing the unit tangent `e₀ = L⁻¹ V(0)`
  set T₀ := tangentSubspace hN (c 0)
  set e₀ : T₀ := ⟨L⁻¹ • Vf 0, hTpar.mem 0⟩
  have he₀ : ‖e₀‖ = 1 := by
    change ‖L⁻¹ • Vf 0‖ = 1
    rw [norm_smul, hVn, Real.norm_eq_abs, abs_inv, abs_of_pos hL, inv_mul_cancel₀ hL.ne']
  have hon : Orthonormal ℝ (Subtype.val : ({e₀} : Set T₀) → T₀) := by
    rw [orthonormal_subtype_iff_ite]
    rintro v rfl w rfl
    rw [if_pos rfl, real_inner_self_eq_norm_sq, he₀, one_pow]
  obtain ⟨u, b, hsub, hb⟩ := hon.exists_orthonormalBasis_extension
  set i₀ : u := ⟨e₀, hsub rfl⟩
  have hbi₀ : b i₀ = e₀ := by rw [hb]
  -- the parallel frame, orthonormal at every time
  set P : u → ℝ → V := fun i => parallelField hN c 0 (b i : V) with hPdef
  have hP : ∀ i, IsParallel hN c (P i) ∧ P i 0 = b i := fun i => parallelField_spec hN hcs (b i).2
  have hP₀ : (fun t => L⁻¹ • Vf t) = P i₀ := by
    refine hTpar.eq hN hcs (hP i₀).1 (t₀ := 0) ?_
    rw [(hP i₀).2, hbi₀]
  have hbt : ∀ t i, ((b.map (parallelTransport hN hcs 0 t)) i : V) = P i t := fun t i => by
    rw [OrthonormalBasis.map_apply, parallelTransport_apply]
  have hPn : ∀ i t, ‖P i t‖ = 1 := fun i t => by
    rw [← hbt t i]
    exact (b.map (parallelTransport hN hcs 0 t)).orthonormal.1 i
  have hVP : ∀ t, Vf t = L • P i₀ t := fun t => by
    rw [← congrFun hP₀ t, smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  set s := Finset.univ.erase i₀ with hs
  have hcard : s.card + 1 = finrank ℝ Z := by
    rw [hs, Finset.card_erase_add_one (Finset.mem_univ _), Finset.card_univ,
      ← Module.finrank_eq_card_basis b.toBasis]
    have := finrank_tanAt hN (c 0).2
    rwa [tanAt_of_mem hN (c 0).2] at this
  have hcardR : (s.card : ℝ) = (finrank ℝ Z : ℝ) - 1 := by
    rw [← hcard]; push_cast; ring
  refine ⟨u, s, P, fun i => (hP i).1, hPn, hcard, fun r hRic t => ?_⟩
  -- the curvature terms add up to `L² K(P_{i₀}, P_{i₀})`
  have hR := hRic (c t) ((b.map (parallelTransport hN hcs 0 t)) i₀) (by
    rw [(b.map (parallelTransport hN hcs 0 t)).orthonormal.1 i₀])
  rw [ricci_eq_sum_erase] at hR
  simp only [hbt] at hR
  have hki : ∀ i, ⟪curvR hN (c t) (Vf t) (P i t) (Vf t), P i t⟫ =
      L ^ 2 * ⟪curvOp hN (c t) (P i₀ t) (P i t) (P i₀ t), P i t⟫ := by
    intro i
    simp only [hVP t, curvR_of_mem hN (c t).2, curvOp_smul_left, smul_apply, map_smul,
      real_inner_smul_left]
    ring
  simp only [hki, ← Finset.mul_sum]
  rw [hcardR]
  exact mul_le_mul_of_nonneg_left hR (sq_nonneg L)

omit [FiniteDimensional ℝ W] in
/-- The curvature term `t ↦ ⟨R(V, P)V, P⟩` along a smooth curve, for smooth tangent fields `V`
and `P`, is continuous. -/
theorem continuous_inner_curvR {c : ℝ → N} (hcs : ContDiff ℝ ∞ (fun t => (c t : V)))
    {Vf P : ℝ → V} (hVfs : ContDiff ℝ ∞ Vf) (hVfT : ∀ t, Vf t ∈ tangentSubspace hN (c t))
    (hPs : ContDiff ℝ ∞ P) (hPT : ∀ t, P t ∈ tangentSubspace hN (c t)) :
    Continuous fun t => ⟪curvR hN (c t) (Vf t) (P t) (Vf t), P t⟫ := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hT : ∀ (X : ℝ → V), (∀ τ, X τ ∈ tangentSubspace hN (c τ)) →
      ∀ᶠ τ in 𝓝 t, prj hN (c τ) (X τ) = X τ := fun X hX =>
    Eventually.of_forall fun τ => (prj_eq_self_iff hN (c τ).2).2 (hX τ)
  exact ((contDiffAt_curvR hN hcs.contDiffAt (Eventually.of_forall fun τ => (c τ).2)
    hVfs.contDiffAt hPs.contDiffAt hVfs.contDiffAt (hT Vf hVfT)
    (hT P hPT)).continuousAt).inner hPs.continuous.continuousAt

/-- **The key step of Theorem 19.4** (Milnor pp. 104–105): if `n ≥ 2`, `K(U, U) ≥ (n − 1)/r²`
for all unit vectors `U`, and `γ ∈ Ω(N; p, q)` is a geodesic of length `L > πr`, then for an
orthonormal parallel frame `P_1, …, P_n` along `γ` with `P_n = V/L` and `W_i = sin(πt) P_i`,
`Σ_{i < n} ½ E_**(W_i, W_i) ≤ (n − 1)(π² − L²/r²)/2 < 0`; so `E_**(W_i, W_i) < 0` for some `i`. -/
theorem exists_energyHessian_neg {r : ℝ} (hr : 0 < r) (hn : 2 ≤ finrank ℝ Z)
    (hRic : RicciLowerBound hN r) {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) (hL : π * r < pathLength γ 0 1) :
    ∃ X : pathTangent hN γ, energyHessian hN hγ X X < 0 := by
  set L := pathLength γ 0 1 with hLdef
  have hLpos : 0 < L := lt_trans (by positivity) hL
  obtain ⟨c, hcs, hγc, Vf, hVfs, hVfT, hVγ, u, s, P, hP, hPn, hcard, hksum⟩ :=
    exists_parallel_frame hγ hgeo hLpos
  have hcardR : (s.card : ℝ) = (finrank ℝ Z : ℝ) - 1 := by
    rw [← hcard]; push_cast; ring
  set k : u → ℝ → ℝ := fun i t => ⟪curvR hN (c t) (Vf t) (P i t) (Vf t), P i t⟫ with hk
  -- the energies of the test fields
  have hE := fun i => energyHessian_sin_parallel hγ hcs hγc (hP i) (hPn i) hVγ
  choose hW hEq using hE
  set f : u → ℝ → ℝ := fun i t => π ^ 2 * cos (π * t) ^ 2 - sin (π * t) ^ 2 * k i t with hf
  have hfc : ∀ i, Continuous (f i) := fun i => by
    have := continuous_inner_curvR hcs hVfs hVfT ((hP i).contDiff hN hcs) (hP i).mem
    simp only [hf, hk]
    fun_prop
  have hsumE : ∑ i ∈ s, energyHessian hN hγ ⟨_, hW i⟩ ⟨_, hW i⟩ =
      2 * ∫ t in (0 : ℝ)..1, ∑ i ∈ s, f i t := by
    rw [Finset.sum_congr rfl fun i _ => hEq i, ← Finset.mul_sum,
      intervalIntegral.integral_finsetSum fun i _ => (hfc i).intervalIntegrable 0 1]
  -- the bound
  set g : ℝ → ℝ := fun t => s.card * (π ^ 2 * cos (π * t) ^ 2) -
    s.card * (L ^ 2 / r ^ 2) * sin (π * t) ^ 2 with hg
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hfg : ∀ t, ∑ i ∈ s, f i t ≤ g t := by
    intro t
    have h1 : ∑ i ∈ s, f i t = s.card * (π ^ 2 * cos (π * t) ^ 2) -
        sin (π * t) ^ 2 * ∑ i ∈ s, k i t := by
      simp only [hf, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    rw [h1]
    have h2 := hksum r hRic t
    have h3 : 0 ≤ sin (π * t) ^ 2 := sq_nonneg _
    have h4 : s.card * (L ^ 2 / r ^ 2) = L ^ 2 * (s.card / r ^ 2) := by ring
    simp only [hg]
    rw [h4]
    nlinarith
  have hint : ∫ t in (0 : ℝ)..1, g t = s.card * (π ^ 2 / 2) - s.card * (L ^ 2 / r ^ 2) / 2 := by
    simp only [hg]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos_sq_pi_mul, integral_sin_sq_pi_mul]
    · ring
    · exact (by fun_prop : Continuous fun t : ℝ => (s.card : ℝ) * (π ^ 2 * cos (π * t) ^ 2)
        ).intervalIntegrable 0 1
    · exact (by fun_prop : Continuous fun t : ℝ => (s.card : ℝ) * (L ^ 2 / r ^ 2) *
        sin (π * t) ^ 2).intervalIntegrable 0 1
  have hneg : ∑ i ∈ s, energyHessian hN hγ ⟨_, hW i⟩ ⟨_, hW i⟩ < 0 := by
    rw [hsumE]
    have hle : ∫ t in (0 : ℝ)..1, ∑ i ∈ s, f i t ≤ ∫ t in (0 : ℝ)..1, g t :=
      intervalIntegral.integral_mono_on zero_le_one
        ((continuous_finsetSum s fun i _ => hfc i).intervalIntegrable 0 1)
        (hgc.intervalIntegrable 0 1) fun t _ => hfg t
    rw [hint] at hle
    have hcpos : (1 : ℝ) ≤ s.card := by
      rw [hcardR]
      have : (2 : ℝ) ≤ finrank ℝ Z := by exact_mod_cast hn
      linarith
    have hπ : π ^ 2 < L ^ 2 / r ^ 2 := by
      rw [lt_div_iff₀ (by positivity)]
      have h := mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ π * r) hL
      nlinarith [h]
    have hneg' : (s.card : ℝ) * (π ^ 2 - L ^ 2 / r ^ 2) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  by_contra hall
  push Not at hall
  exact (Finset.sum_nonneg fun i _ => hall ⟨_, hW i⟩).not_gt hneg

/-- **Theorem 19.4 (Myers)** (Milnor p. 104): suppose `n = dim N ≥ 2` and the Ricci curvature
satisfies `K(U, U) ≥ (n − 1)/r²` for every unit vector `U` at every point.  Then every geodesic
`γ ∈ Ω(N; p, q)` of length `> πr` contains a point `γ(t)`, `0 < t < 1`, conjugate to `γ(0)`
(the index of `E_**` is positive, and the index theorem applies), and is not minimal
(`E_**(W, W) < 0` contradicts Lemma 13.6). -/
theorem theorem_19_4 {r : ℝ} (hr : 0 < r) (hn : 2 ≤ finrank ℝ Z) (hRic : RicciLowerBound hN r)
    {p q : V} {γ : ℝ → V} (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ)
    (hL : π * r < pathLength γ 0 1) :
    (∃ t ∈ Ioo (0 : ℝ) 1, IsConjugate hN γ 0 t) ∧ ¬ IsMinimalPath N γ p q := by
  obtain ⟨X, hX⟩ := exists_energyHessian_neg hr hn hRic hγ hgeo hL
  refine ⟨?_, fun hmin => (lemma_13_6 hN hmin hgeo X).not_gt hX⟩
  -- `E_**` is negative definite on the line through `X`, so the index is positive
  have hX0 : X ≠ 0 := fun h => by
    rw [h] at hX
    simp at hX
  have hneg : IsNegDefOn (energyHessian hN hγ) (ℝ ∙ X) := by
    intro Y hY hY0
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hY
    have ha : a ≠ 0 := fun h => hY0 (by rw [h, zero_smul])
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have := sq_pos_of_ne_zero ha
    nlinarith
  have h1 := le_formIndex hneg
  rw [finrank_span_singleton hX0, (theorem_15_1 hN hγ hgeo).2] at h1
  by_contra hno
  push Not at hno
  have h0 : ∀ t ∈ Ioo (0 : ℝ) 1, conjMultiplicity hN γ (hgeo.isSmoothCurveIn hN hγ) 0 t = 0 := by
    intro t ht
    by_contra h
    exact hno t ht ((isConjugate_iff _).2
      ⟨⟨le_rfl, zero_le_one⟩, Ioo_subset_Icc_self ht, ht.1.ne, Nat.pos_of_ne_zero h⟩)
  rw [finsum_mem_eq_zero_of_forall_eq_zero h0] at h1
  norm_num at h1

/-! ### Corollary 19.5 -/

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- A minimal geodesic in Milnor's sense (`Morse.IsMinimalGeodesic`, p. 61) is a geodesic of
`Ω(N; γ(0), γ(1))` of minimal length (`Morse.IsMinimalPath`). -/
theorem IsMinimalGeodesic.isMinimalPath {γ : ℝ → V} (h : IsMinimalGeodesic hN γ 0 1) :
    γ ∈ pathSpace N (γ 0) (γ 1) ∧ IsUnbrokenGeodesic hN γ ∧ IsMinimalPath N γ (γ 0) (γ 1) := by
  obtain ⟨-, ⟨s, hsub, hgeo⟩, hmin⟩ := h
  have hγ : γ ∈ pathSpace N (γ 0) (γ 1) :=
    ⟨IsPiecewiseSmooth.of_contDiffOn hgeo.contDiffOn zero_le_one hsub,
      fun t ht => hgeo.mem t (hsub ht), rfl, rfl⟩
  exact ⟨hγ, ⟨hgeo.contDiffOn.mono hsub, hgeo.mono isOpen_Ioo (Ioo_subset_Icc_self.trans hsub)⟩,
    hγ, fun c hc => hmin c 0 1 hc.1 hc.2.1 hc.2.2.1 hc.2.2.2⟩

/-- **Corollary 19.5** (Milnor p. 105): if `N` is connected and complete and
`K(U, U) ≥ (n − 1)/r² > 0` for all unit vectors `U`, then any two points of `N` have distance
at most `πr`, and `N` is compact.  (A minimal geodesic joins any two points, Hopf–Rinow, and by
Theorem 19.4 it has length `≤ πr`; closed bounded sets are compact, Corollary 10.10.) -/
theorem corollary_19_5 (hconn : IsPreconnected N) (hcomplete : IsRiemComplete N) {r : ℝ}
    (hr : 0 < r) (hpos : 0 < ((finrank ℝ Z : ℝ) - 1) / r ^ 2) (hRic : RicciLowerBound hN r) :
    (∀ p q : N, riemDist (N := N) p q ≤ ENNReal.ofReal (π * r)) ∧ IsCompact N := by
  have hn : 2 ≤ finrank ℝ Z := by
    have h1 : (0 : ℝ) < (finrank ℝ Z : ℝ) - 1 := by
      by_contra h
      push Not at h
      exact (div_nonpos_of_nonpos_of_nonneg h (sq_nonneg r)).not_gt hpos
    have : (1 : ℝ) < finrank ℝ Z := by linarith
    exact_mod_cast this
  obtain ⟨-, -, hmin, hcpt⟩ := hopf_rinow_of_isRiemComplete hN hconn hcomplete
  have hdist : ∀ p q : N, riemDist (N := N) p q ≤ ENNReal.ofReal (π * r) := by
    intro p q
    obtain ⟨γ, hγmin, hγ0, hγ1, hρ⟩ := hmin p q
    rw [hρ]
    refine ENNReal.ofReal_le_ofReal (not_lt.1 fun hlt => ?_)
    obtain ⟨hγ, hgeo, hminP⟩ := hγmin.isMinimalPath
    exact (theorem_19_4 hr hn hRic hγ hgeo hlt).2 hminP
  refine ⟨hdist, ?_⟩
  have hb : IsRiemBounded N (Subtype.val '' (univ : Set N)) := by
    refine ⟨π * r, ?_⟩
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    exact hdist x y
  have hK := (hcpt univ isClosed_univ hb).image continuous_subtype_val
  rwa [image_univ, Subtype.range_coe] at hK

/-! ### The example of the sphere (Milnor p. 105) -/

open Milnor.Sphere in
/-- **The Ricci curvature of the unit sphere** `Sⁿ`: `K(U, U) = (n − 1)‖U‖²` (Milnor p. 105), since
every sectional curvature is `1`. -/
theorem ricci_sph {n : ℕ} (q : Sph n) (U : tangentSubspace (sphSub n) q) :
    ricci (sphSub n) q U U = ((n : ℝ) - 1) * ‖U‖ ^ 2 := by
  set b := stdOrthonormalBasis ℝ (tangentSubspace (sphSub n) q)
  rw [ricci_eq_sum b]
  have hb1 : ∀ i, ‖(b i : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := fun i => b.orthonormal.1 i
  have hterm : ∀ i, ⟪curvOp (sphSub n) q U (b i) U, (b i : EuclideanSpace ℝ (Fin (n + 1)))⟫ =
      ‖U‖ ^ 2 - ⟪U, b i⟫ * ⟪b i, U⟫ := by
    intro i
    rw [curvOp_sph U.2 (b i).2 U.2, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq (b i : EuclideanSpace ℝ (Fin (n + 1))),
      hb1, Submodule.coe_inner, Submodule.coe_inner, Submodule.coe_norm]
    ring
  have hT : finrank ℝ (tangentSubspace (sphSub n) q) = n := by
    have := finrank_tanAt (sphSub n) q.2
    rwa [tanAt_of_mem (sphSub n) q.2, finrank_euclideanSpace_fin] at this
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    b.sum_inner_mul_inner, real_inner_self_eq_norm_sq, Fintype.card_fin, hT]
  ring

open Milnor.Sphere in
/-- **The unit sphere satisfies the hypothesis of Myers' theorem with `r = 1`** (Milnor p. 105):
`K(U, U) = n − 1` for unit vectors. -/
theorem ricciLowerBound_sph {n : ℕ} : RicciLowerBound (sphSub n) 1 := by
  intro q U hU
  rw [ricci_sph, hU, finrank_euclideanSpace_fin]
  norm_num

open Milnor.Sphere in
/-- **The example after Theorem 19.4** (Milnor p. 105), for the unit sphere `Sⁿ`, `n ≥ 2`: every
geodesic of length `> π` contains a point conjugate to its initial point and is not minimal; and
(Corollary 19.5) any two points of `Sⁿ` are at distance `≤ π`. -/
theorem sphere_myers {n : ℕ} (hn : 2 ≤ n) :
    (∀ {p q : EuclideanSpace ℝ (Fin (n + 1))} {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))},
      γ ∈ pathSpace (Sph n) p q → IsUnbrokenGeodesic (sphSub n) γ → π < pathLength γ 0 1 →
        (∃ t ∈ Ioo (0 : ℝ) 1, IsConjugate (sphSub n) γ 0 t) ∧ ¬ IsMinimalPath (Sph n) γ p q) ∧
    ∀ p q : Sph n, riemDist (N := Sph n) p q ≤ ENNReal.ofReal π := by
  have hn' : 2 ≤ finrank ℝ (EuclideanSpace ℝ (Fin n)) := by rwa [finrank_euclideanSpace_fin]
  refine ⟨fun hγ hgeo hL => theorem_19_4 one_pos hn' ricciLowerBound_sph hγ hgeo
    (by rwa [mul_one]), ?_⟩
  have hconn : IsPreconnected (Sph n) := by
    change IsPreconnected ((sphG (n := n)) ⁻¹' {0})
    rw [preimage_eq_sphere]
    refine (isConnected_sphere ?_ 0 zero_le_one).isPreconnected
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  have hpos : 0 < ((finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1) / 1 ^ 2 := by
    rw [finrank_euclideanSpace_fin]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    norm_num
    linarith
  have h := (corollary_19_5 hconn (isRiemComplete_of_isClosed (sphSub n) isCompact_sph.isClosed)
    one_pos hpos ricciLowerBound_sph).1
  intro p q
  simpa using h p q

end Morse
