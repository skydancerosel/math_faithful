import Morse.Chapter11.NonConjugate
import Morse.Chapter9.IndexTheorem
import Morse.Chapter6.SphereCurvature

/-!
Milnor, *Morse Theory*, §17, pp. 95–96 (the example "the path space of the sphere"), with the
example of antipodal points in §14, p. 80: the geodesics joining two points of the round sphere
`Sⁿ`, their conjugate points and their indices, the input of Corollary 17.4.

# The geodesics between two points of `Sⁿ` and their indices

## Milnor's text, paraphrased

* (p. 80) For antipodal points `p`, `q` of the unit sphere and a great semicircle `γ` from `p` to
  `q`, rotations of the sphere fixing `p` and `q` move `γ` through geodesics, so their variation
  fields are Jacobi fields vanishing at both ends (Lemma 14.3); rotating in `n − 1` independent
  directions, Milnor concludes that `p` and `q` are conjugate along `γ` with multiplicity `n − 1`.
* (p. 95) Example: the path space of `Sⁿ`.  Two points `p`, `q` are taken non-conjugate, which
  Milnor rephrases as `q ≠ p, p'`, `p'` the antipode of `p`.  Then there are countably many
  geodesics `γ₀, γ₁, γ₂, …` from `p` to `q`: `γ₀` is the short arc of the great circle through `p`
  and `q`, `γ₁` the long arc (through `q'` and `p'`, `q'` the antipode of `q`), `γ₂` runs once more
  around the circle, and so on.  (p. 96) The subscript `k` is the number of times `p` or `p'`
  occurs in the interior of `γ_k`.
* (p. 96) `λ(γ_k) = μ₁ + ⋯ + μ_k = k(n − 1)`, because each interior occurrence of `p` or `p'` is
  conjugate to `p` with multiplicity `n − 1` (the index theorem 15.1 is used implicitly); with
  Theorem 17.3 this gives Corollary 17.4 (the loop space of `Sⁿ`).

## In the embedded setting

`Sⁿ` is `Milnor.Sphere.Sph n ⊆ ℝⁿ⁺¹`, with the slice structure `Milnor.Sphere.sphSub n` and the
induced metric.

* `Morse.greatCircle p u L`: `t ↦ cos(Lt) p + sin(Lt) u`; `Morse.isGeodesicOn_greatCircle`: for
  orthonormal `p`, `u` it is a geodesic of speed `L` (`c'' = −L² c = II(c', c')`).
* `Morse.exists_eqOn_greatCircle`: **every geodesic `γ : [0, 1] → Sⁿ` from `p` is a great circle**
  on `[0, 1]`.
* `Morse.conjMultiplicity_greatCircle`: **the conjugate points along a great circle**: for `L > 0`,
  the parameter `t ∈ (0, 1]` is conjugate to `0` iff `Lt ∈ πℕ`, and then with multiplicity `n − 1`
  (`Morse.conjMultiplicity_sphGeod` along `γ_k`).
* `Morse.sphAngle p q = θ ∈ (0, π)`, `Morse.sphDir p q = u` (`q = cos θ p + sin θ u`, `u ⊥ p`),
  `Morse.sphLen p q k = L(γ_k)` (`θ + 2πj` for `k = 2j`, `2π(j + 1) − θ` for `k = 2j + 1`) and
  `Morse.sphGeod p q k = γ_k`; `Morse.sphGeod_mem_pathSpace`, `Morse.isUnbrokenGeodesic_sphGeod`,
  `Morse.energy_sphGeod` (`E(γ_k) = L(γ_k)²`), `Morse.mul_pi_lt_sphLen`, `Morse.sphLen_lt`
  (`kπ < L(γ_k) < (k + 1)π`), `Morse.sphLen_pos`, `Morse.sphLen_strictMono`.
* `Morse.exists_eqOn_sphGeod`: **the `γ_k` are all the geodesics from `p` to `q`**.
* `Morse.notMem_conjLocus_sph`: **`p` and `q` are not conjugate along any geodesic** (the
  hypothesis of Theorem 17.3).
* `Morse.formIndex_sphGeod`, `Morse.formIndex_eq_of_eqOn_sphGeod`: **`λ(γ_k) = k(n − 1)`**.
* `Morse.formIndex_energyHessian_congr` (any `N`): the index of a geodesic only depends on its
  values on `[0, 1]`.

## What Milnor leaves implicit

* **Non-conjugacy.**  Milnor's rephrasing of "non-conjugate" as `q ≠ p, p'` is not proved.  The
  half that Theorem 17.3 needs, that such `p`, `q` are not conjugate along any geodesic, requires
  the conjugate points along every great circle through `p` (p. 80 treats only the semicircle),
  the list of all geodesics from `p` to `q`, and `L(γ_k) ∉ πℤ` (`Morse.notMem_conjLocus_sph`).
* **The list of geodesics is complete.**  That every geodesic from `p` is a great circle uses the
  uniqueness of geodesics, applied after extending the segment past `t = 0`, where its velocity is
  only a one-sided derivative (`Morse.exists_initial_ray`).  That the `γ_k` are all the great
  circles reaching `q` at `t = 1` is a trigonometric computation: `cos L = cos θ` and
  `sin L · w = sin θ · u` force `(w, L) = (u, θ + 2πj)` or `(−u, 2π(j + 1) − θ)`; this uses
  `L ≥ 0` and `q ≠ ±p` (a unique great circle through `p` and `q`, and `γ` is not constant).
* **"`k` is the number of times `p` or `p'` occurs in the interior of `γ_k`"** amounts to the
  inequality `kπ < L(γ_k) < (k + 1)π`: the interior parameters conjugate to `0`, where `γ_k`
  passes through `p` or `p'`, are the `t = jπ/L(γ_k)`, `1 ≤ j ≤ k`.
* **Multiplicity `n − 1`.**  On p. 80 the `n − 1` rotations only show multiplicity `≥ n − 1`
  (equality needs Remark 14.2), and only for the antipode at the end of a semicircle.  On p. 96 the
  claim is used at `p'` and at `p` after any number of half turns, and one also needs that no other
  interior point of `γ_k` is conjugate to `p`.  Here the `n`-dimensional space of Jacobi fields
  vanishing at `0` (Remark 14.2) is determined: it is spanned by the fields `sin(Lt) e`, `e ⊥ p, w`
  constant, and `t c'(t)`; such a field vanishes at `t₀ > 0` iff its `t c'(t)` coefficient is `0`
  and `sin(Lt₀) e = 0`, because `e ⊥ c'(t₀)`.  The Jacobi equation for `sin(Lt) e` is checked
  directly (`e` is tangent along `c`, `D/dt e = 0`, and `R(c', J)c' = L² J` by
  `R(x, y)z = ⟨x, z⟩y − ⟨y, z⟩x`, `Morse.curvOp_sph`) rather than by rotations and Lemma 14.3.
* **The index only depends on `γ|[0, 1]`** (`Morse.formIndex_energyHessian_congr`): needed because
  paths are functions on `ℝ` here, so a geodesic from `p` to `q` equals some `γ_k` only on `[0, 1]`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

/-! ### Two facts about any submanifold -/

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-- The covariant derivative along `γ` of a field agreeing on `[0, 1]` with a field differentiable
at `s`. -/
theorem covAlong_eq_of_hasDerivAt {γ X Y : ℝ → V} {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hXY : EqOn X Y (Icc 0 1)) {y : V} (hY : HasDerivAt Y y s) :
    covAlong hN γ X s = prj hN (γ s) y := by
  rw [covAlong, derivWithin_congr hXY (hXY hs),
    hY.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one s hs)]

variable [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]

/-- **The index of a geodesic only depends on the geodesic on `[0, 1]`**: by the index theorem
(`Morse.theorem_15_1`) both indices count conjugate points with multiplicity, and the Jacobi fields
along two curves agreeing on `[0, 1]` are the same (`Morse.IsJacobiField.congr_curve`). -/
theorem formIndex_energyHessian_congr {p q : V} {γ γ' : ℝ → V}
    (hγ : γ ∈ pathSpace N p q) (hγ' : γ' ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ)
    (hgeo' : IsUnbrokenGeodesic hN γ') (heq : EqOn γ γ' (Icc 0 1)) :
    formIndex (energyHessian hN hγ) = formIndex (energyHessian hN hγ') := by
  rw [(theorem_15_1 hN hγ hgeo).2, (theorem_15_1 hN hγ' hgeo').2]
  congr 1
  refine finsum_mem_congr rfl fun t _ => ?_
  have hJ : jacobiSpace hN γ (hgeo.isSmoothCurveIn hN hγ) =
      jacobiSpace hN γ' (hgeo'.isSmoothCurveIn hN hγ') := by
    ext J
    exact ⟨fun h => ⟨h.1.congr_curve heq, h.2⟩, fun h => ⟨h.1.congr_curve heq.symm, h.2⟩⟩
  rw [conjMultiplicity, conjMultiplicity, conjSpace, conjSpace, hJ]

end General

open Milnor.Sphere Real

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (n + 1))

/-! ### Great circles -/

/-- **The great circle** `t ↦ cos(Lt) p + sin(Lt) u`: for orthonormal `p`, `u` a geodesic of `Sⁿ`
of speed `L` starting at `p` (`Morse.isGeodesicOn_greatCircle`). -/
def greatCircle (p u : 𝔼) (L t : ℝ) : 𝔼 := Real.cos (L * t) • p + Real.sin (L * t) • u

theorem greatCircle_zero (p u : 𝔼) (L : ℝ) : greatCircle p u L 0 = p := by
  simp [greatCircle]

theorem greatCircle_neg (p u : 𝔼) (L t : ℝ) :
    greatCircle (-p) (-u) L t = -greatCircle p u L t := by
  simp only [greatCircle, smul_neg, neg_add]

/-- `c'(t) = L (cos(Lt) u − sin(Lt) p)`. -/
theorem hasDerivAt_greatCircle (p u : 𝔼) (L t : ℝ) :
    HasDerivAt (greatCircle p u L) (L • greatCircle u (-p) L t) t := by
  have h1 : HasDerivAt (fun t => L * t) L t := by simpa using (hasDerivAt_id t).const_mul L
  have hc := ((Real.hasDerivAt_cos (L * t)).comp t h1).smul_const p
  have hs := ((Real.hasDerivAt_sin (L * t)).comp t h1).smul_const u
  have e : L • greatCircle u (-p) L t =
      (-Real.sin (L * t) * L) • p + (Real.cos (L * t) * L) • u := by
    simp only [greatCircle]
    module
  rw [e]
  exact hc.add hs

theorem deriv_greatCircle (p u : 𝔼) (L : ℝ) :
    deriv (greatCircle p u L) = fun t => L • greatCircle u (-p) L t :=
  funext fun t => (hasDerivAt_greatCircle p u L t).deriv

theorem deriv_deriv_greatCircle (p u : 𝔼) (L t : ℝ) :
    deriv (deriv (greatCircle p u L)) t = -(L ^ 2) • greatCircle p u L t := by
  have h := ((hasDerivAt_greatCircle u (-p) L t).const_smul L).deriv
  rw [deriv_greatCircle]
  refine h.trans ?_
  rw [greatCircle_neg, smul_neg, smul_neg, smul_smul, ← neg_smul, sq]

theorem contDiff_greatCircle (p u : 𝔼) (L : ℝ) : ContDiff ℝ ∞ (greatCircle p u L) :=
  ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).smul contDiff_const).add
    ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).smul contDiff_const)

theorem inner_greatCircle_left (p u x : 𝔼) (L t : ℝ) :
    ⟪greatCircle p u L t, x⟫ = Real.cos (L * t) * ⟪p, x⟫ + Real.sin (L * t) * ⟪u, x⟫ := by
  rw [greatCircle, inner_add_left, real_inner_smul_left, real_inner_smul_left]

theorem inner_greatCircle_self {p u : 𝔼} (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0)
    (L t : ℝ) : ⟪greatCircle p u L t, greatCircle p u L t⟫ = 1 := by
  rw [inner_greatCircle_left, greatCircle, inner_add_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, hp, hu, hpu, real_inner_comm, hpu]
  nlinarith [Real.cos_sq_add_sin_sq (L * t)]

theorem norm_greatCircle {p u : 𝔼} (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (L t : ℝ) :
    ‖greatCircle p u L t‖ = 1 := by
  have h := inner_greatCircle_self hp hu hpu L t
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (greatCircle p u L t)]

/-- The velocity of a great circle is tangent to `Sⁿ`. -/
theorem inner_greatCircle_greatCircle {p u : 𝔼} (hp : ‖p‖ = 1) (hu : ‖u‖ = 1)
    (hpu : ⟪p, u⟫ = 0) (L t : ℝ) : ⟪greatCircle p u L t, greatCircle u (-p) L t⟫ = 0 := by
  rw [inner_greatCircle_left, greatCircle, inner_add_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, inner_neg_right,
    inner_neg_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hp, hu, hpu,
    real_inner_comm, hpu]
  ring

theorem norm_of_mem_sph {p : 𝔼} (hp : p ∈ Sph n) : ‖p‖ = 1 := mem_iff_norm.1 hp

theorem greatCircle_mem_sph {p u : 𝔼} (hp : p ∈ Sph n) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0)
    (L t : ℝ) : greatCircle p u L t ∈ Sph n :=
  mem_iff_norm.2 (norm_greatCircle (norm_of_mem_sph hp) hu hpu L t)

/-- The tangent projection of `Sⁿ` at `x`: `P_x v = v − ⟪x, v⟫ x`. -/
theorem prj_sph {x : 𝔼} (hx : x ∈ Sph n) (v : 𝔼) : prj (sphSub n) x v = v - ⟪x, v⟫ • x := by
  rw [prj_of_mem (sphSub n) hx]
  exact tanProj_sph ⟨x, hx⟩ v

/-- The curvature tensor of `Sⁿ`: `R(a, b)c = ⟪a, c⟫ b − ⟪b, c⟫ a` on tangent vectors. -/
theorem curvR_sph {x a b c : 𝔼} (hx : x ∈ Sph n) (ha : ⟪x, a⟫ = 0) (hb : ⟪x, b⟫ = 0)
    (hc : ⟪x, c⟫ = 0) : curvR (sphSub n) x a b c = ⟪a, c⟫ • b - ⟪b, c⟫ • a := by
  rw [curvR_of_mem (sphSub n) hx]
  exact curvOp_sph ((mem_tangentSubspace_sph_iff ⟨x, hx⟩ a).2 ha)
    ((mem_tangentSubspace_sph_iff ⟨x, hx⟩ b).2 hb) ((mem_tangentSubspace_sph_iff ⟨x, hx⟩ c).2 hc)

/-- **Great circles are geodesics** of `Sⁿ`: `c'' = −L² c = II(c', c')`, the second fundamental
form being `II(v, w) = −⟪v, w⟫ c` (`Morse.secondFundForm_sph`). -/
theorem isGeodesicOn_greatCircle {p u : 𝔼} (hp : p ∈ Sph n) (hu : ‖u‖ = 1)
    (hpu : ⟪p, u⟫ = 0) (L : ℝ) : IsGeodesicOn (sphSub n) (greatCircle p u L) univ := by
  have hp1 := norm_of_mem_sph hp
  refine isGeodesicOn_of_deriv_deriv_eq (sphSub n) isOpen_univ
    (fun t _ => greatCircle_mem_sph hp hu hpu L t) (contDiff_greatCircle p u L).contDiffOn
    fun t _ => ?_
  have hT : deriv (greatCircle p u L) t ∈
      tangentSubspace (sphSub n) ⟨greatCircle p u L t, greatCircle_mem_sph hp hu hpu L t⟩ := by
    rw [mem_tangentSubspace_sph_iff, deriv_greatCircle]
    change ⟪greatCircle p u L t, L • greatCircle u (-p) L t⟫ = 0
    rw [real_inner_smul_right, inner_greatCircle_greatCircle hp1 hu hpu, mul_zero]
  rw [secondFundForm_sph hT hT, deriv_deriv_greatCircle, deriv_greatCircle]
  have hpu' : ⟪u, -p⟫ = 0 := by rw [inner_neg_right, real_inner_comm, hpu, neg_zero]
  rw [real_inner_smul_left, real_inner_smul_right,
    inner_greatCircle_self hu (by rw [norm_neg, hp1]) hpu' L t]
  simp only [mul_one, sq]

theorem isSmoothCurveIn_greatCircle {p u : 𝔼} (hp : p ∈ Sph n) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0)
    (L : ℝ) : IsSmoothCurveIn (sphSub n) (greatCircle p u L) :=
  ⟨(contDiff_greatCircle p u L).contDiffOn, fun t _ => greatCircle_mem_sph hp hu hpu L t⟩

/-- The energy of a great circle of speed `L` on `[0, 1]` is `L²`. -/
theorem energy_greatCircle {p u : 𝔼} (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (L : ℝ) :
    energy (greatCircle p u L) 0 1 = L ^ 2 := by
  have hpu' : ⟪u, -p⟫ = 0 := by rw [inner_neg_right, real_inner_comm, hpu, neg_zero]
  have h : ∀ t, ‖deriv (greatCircle p u L) t‖ ^ 2 = L ^ 2 := fun t => by
    rw [deriv_greatCircle, norm_smul, norm_greatCircle hu (by rw [norm_neg, hp]) hpu' L t,
      mul_one, Real.norm_eq_abs, sq_abs]
  simp only [energy, h, intervalIntegral.integral_const, sub_zero, one_smul]

/-! ### Every geodesic from `p` is a great circle -/

/-- A unit vector orthogonal to a given vector of `ℝⁿ⁺¹`, `n ≥ 1`. -/
theorem exists_unit_orthogonal (hn : 1 ≤ n) (p : 𝔼) : ∃ u : 𝔼, ‖u‖ = 1 ∧ ⟪p, u⟫ = 0 := by
  by_cases hp : p = 0
  · exact ⟨EuclideanSpace.single 0 1, by simp, by simp [hp]⟩
  · have : Fact (finrank ℝ 𝔼 = n + 1) := ⟨finrank_euclideanSpace_fin⟩
    have h := Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := n) hp
    obtain ⟨⟨x, hx⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (h.symm ▸ hn)
    have hx0' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0')]
    · rw [real_inner_smul_right, Submodule.mem_orthogonal_singleton_iff_inner_right.1 hx, mul_zero]

/-- **Every geodesic from `p` is a great circle** (Milnor p. 95): a geodesic `γ : [0, 1] → Sⁿ`
with `γ(0) = p` is `t ↦ cos(Lt) p + sin(Lt) u` on `[0, 1]`, for a unit vector `u ⊥ p` and
`L = ‖γ'(0)‖ ≥ 0`.  The geodesic extends past `[0, 1]` (`Morse.exists_initial_ray`), and the
extension and the great circle are geodesics with the same initial data
(`Morse.IsGeodesicOn.eqOn`). -/
theorem exists_eqOn_greatCircle (hn : 1 ≤ n) {p q : 𝔼} {γ : ℝ → 𝔼}
    (hγ : γ ∈ pathSpace (Sph n) p q) (hgeo : IsUnbrokenGeodesic (sphSub n) γ) :
    ∃ u L, ‖u‖ = 1 ∧ ⟪p, u⟫ = 0 ∧ 0 ≤ L ∧ EqOn γ (greatCircle p u L) (Icc 0 1) := by
  have hc := hgeo.isSmoothCurveIn (sphSub n) hγ
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hp : p ∈ Sph n := hγ.2.2.1 ▸ hγ.2.1 0 h0
  obtain ⟨η, hη, hray, hrayγ⟩ := exists_initial_ray hc hgeo.2
  set g : ℝ → 𝔼 := fun t => Morse.exp (sphSub n) (γ 0) (t • velAlong γ 0) with hgdef
  set v := velAlong γ 0 with hvdef
  have h0I : (0 : ℝ) ∈ Ioo (-η) (1 + η) := ⟨by linarith, by linarith⟩
  have hg0 : g 0 = p := (hrayγ 0 h0).trans hγ.2.2.1
  have hgd : deriv g 0 = v := by
    have h2 : HasDerivWithinAt γ (deriv g 0) (Icc 0 1) 0 :=
      (hray.hasDerivAt h0I).hasDerivWithinAt.congr (fun t ht => (hrayγ t ht).symm)
        (hrayγ 0 h0).symm
    exact (uniqueDiffOn_Icc zero_lt_one 0 h0).eq_deriv _ h2 (hc.hasDerivWithinAt h0)
  have hv : ⟪p, v⟫ = 0 := by
    have := hray.deriv_mem h0I
    rw [mem_tangentSubspace_sph_iff] at this
    rw [← hg0, ← hgd]
    exact this
  obtain ⟨u, hu, hpu, hLu⟩ : ∃ u : 𝔼, ‖u‖ = 1 ∧ ⟪p, u⟫ = 0 ∧ ‖v‖ • u = v := by
    by_cases hv0 : v = 0
    · obtain ⟨u, hu, hpu⟩ := exists_unit_orthogonal hn p
      exact ⟨u, hu, hpu, by rw [hv0, norm_zero, zero_smul]⟩
    · refine ⟨‖v‖⁻¹ • v, ?_, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]
      · rw [real_inner_smul_right, hv, mul_zero]
      · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hv0), one_smul]
  refine ⟨u, ‖v‖, hu, hpu, norm_nonneg _, fun t ht => ?_⟩
  have hcirc := (isGeodesicOn_greatCircle hp hu hpu ‖v‖).mono (isOpen_Ioo (a := -η) (b := 1 + η))
    (subset_univ _)
  have heq := hray.eqOn hcirc isPreconnected_Ioo h0I (by rw [hg0, greatCircle_zero])
    (by rw [hgd, deriv_greatCircle]; simp only [greatCircle_zero]; exact hLu.symm)
  rw [← hrayγ t ht]
  exact heq ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-! ### Conjugate points along a great circle -/

theorem hasDerivAt_sin_mul (L s : ℝ) :
    HasDerivAt (fun s => Real.sin (L * s)) (L * Real.cos (L * s)) s := by
  have h1 : HasDerivAt (fun t => L * t) L s := by simpa using (hasDerivAt_id s).const_mul L
  exact ((Real.hasDerivAt_sin (L * s)).comp s h1).congr_deriv (mul_comm _ _)

theorem hasDerivAt_cos_mul (L s : ℝ) :
    HasDerivAt (fun s => L * Real.cos (L * s)) (-(L ^ 2) * Real.sin (L * s)) s := by
  have h1 : HasDerivAt (fun t => L * t) L s := by simpa using (hasDerivAt_id s).const_mul L
  exact (((Real.hasDerivAt_cos (L * s)).comp s h1).const_mul L).congr_deriv (by ring)

theorem velAlong_greatCircle (p u : 𝔼) (L : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    velAlong (greatCircle p u L) s = L • greatCircle u (-p) L s :=
  (hasDerivAt_greatCircle p u L s).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc zero_lt_one s hs)

theorem mem_orthogonal_span_pair {p u y : 𝔼} :
    y ∈ (Submodule.span ℝ {p, u})ᗮ ↔ ⟪p, y⟫ = 0 ∧ ⟪u, y⟫ = 0 := by
  constructor
  · intro h
    exact ⟨Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (by simp)) h,
      Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (by simp)) h⟩
  · rintro ⟨h1, h2⟩
    rw [Submodule.mem_orthogonal]
    intro x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, h1, h2]
    ring

/-- `dim {p, u}ᗮ = n − 1` for orthonormal `p, u ∈ ℝⁿ⁺¹`. -/
theorem finrank_orthogonal_span_pair {p u : 𝔼} (hp : ‖p‖ = 1) (hu : ‖u‖ = 1)
    (hpu : ⟪p, u⟫ = 0) : finrank ℝ (Submodule.span ℝ {p, u})ᗮ = n - 1 := by
  have hli : LinearIndependent ℝ ![p, u] := by
    rw [LinearIndependent.pair_iff]
    intro a b h
    have h1 := congrArg (fun x => ⟪p, x⟫) h
    have h2 := congrArg (fun x => ⟪u, x⟫) h
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hp, hu, hpu,
      real_inner_comm p u, inner_zero_right] at h1 h2
    constructor <;> linarith
  have h2 : finrank ℝ (Submodule.span ℝ {p, u}) = 2 := by
    rw [← Matrix.range_cons_cons_empty p u ![], finrank_span_eq_card hli]
    simp
  have := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {p, u})
  rw [h2, finrank_euclideanSpace_fin] at this
  omega

section Jacobi

variable {p u : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ Sph n) (hu : ‖u‖ = 1)
  (hpu : ⟪p, u⟫ = 0)
include hp hu hpu

/-- **`sin(Lt) e` is a Jacobi field** along the great circle `c`, for a constant `e ⊥ p, u`: `e` is
tangent along `c`, `D/dt (sin(Lt) e) = L cos(Lt) e`, so `D²J/dt² = −L² J`, while
`R(c', J)c' = ‖c'‖² J − ⟨J, c'⟩ c' = L² J`. -/
theorem isJacobiField_sin_smul {e : 𝔼} (hpe : ⟪p, e⟫ = 0) (hue : ⟪u, e⟫ = 0) (L : ℝ) :
    IsJacobiField (sphSub n) (greatCircle p u L) (fun s => Real.sin (L * s) • e) := by
  have hmem := greatCircle_mem_sph hp hu hpu L
  have hp1 := norm_of_mem_sph hp
  have hpu' : ⟪u, -p⟫ = 0 := by rw [inner_neg_right, real_inner_comm, hpu, neg_zero]
  have hce : ∀ s, ⟪greatCircle p u L s, e⟫ = 0 := fun s => by
    rw [inner_greatCircle_left, hpe, hue]; ring
  have hwe : ∀ s, ⟪greatCircle u (-p) L s, e⟫ = 0 := fun s => by
    rw [inner_greatCircle_left, hue, inner_neg_left, hpe]; ring
  have hcov : covD (sphSub n) (greatCircle p u L) (fun s => Real.sin (L * s) • e) =
      fun s => (L * Real.cos (L * s)) • e := by
    funext s
    rw [covD, ((hasDerivAt_sin_mul L s).smul_const e).deriv, prj_sph (hmem s),
      real_inner_smul_right, hce, mul_zero, zero_smul, sub_zero]
  refine ⟨((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).smul
    contDiff_const).contDiffOn, fun s _ => ?_, fun s _ => ?_⟩
  · rw [prj_sph (hmem s), real_inner_smul_right, hce, mul_zero, zero_smul, sub_zero]
  · rw [jacobiExpr, hcov, covD, ((hasDerivAt_cos_mul L s).smul_const e).deriv, prj_sph (hmem s),
      real_inner_smul_right, hce, mul_zero, zero_smul, sub_zero, deriv_greatCircle]
    have hww := inner_greatCircle_self hu (by rw [norm_neg, hp1]) hpu' L s
    have hcw : ⟪greatCircle p u L s, L • greatCircle u (-p) L s⟫ = 0 := by
      rw [real_inner_smul_right, inner_greatCircle_greatCircle hp1 hu hpu, mul_zero]
    have hcs : ⟪greatCircle p u L s, Real.sin (L * s) • e⟫ = 0 := by
      rw [real_inner_smul_right, hce, mul_zero]
    rw [curvR_sph (hmem s) hcw hcs hcw, real_inner_smul_left, real_inner_smul_right, hww,
      real_inner_smul_left, real_inner_smul_right, real_inner_comm, hwe, mul_zero, mul_zero,
      zero_smul, sub_zero, smul_smul]
    rw [← add_smul]
    convert zero_smul ℝ e using 2
    ring

/-- **`t c'(t)` is a Jacobi field** along the great circle (Milnor p. 79). -/
theorem isJacobiField_smul_deriv_greatCircle (L : ℝ) :
    IsJacobiField (sphSub n) (greatCircle p u L) (fun s => s • (L • greatCircle u (-p) L s)) :=
  (isJacobiField_smul_vel (isSmoothCurveIn_greatCircle hp hu hpu L)
    ((isGeodesicOn_greatCircle hp hu hpu L).mono isOpen_Ioo (subset_univ _))).congr
    fun s hs => by simp only [velAlong_greatCircle p u L hs]

end Jacobi

open Classical in
/-- **Conjugate points along a great circle** (Milnor pp. 80, 96): along
`c(t) = cos(Lt) p + sin(Lt) u` (`L > 0`), the parameter `t ∈ (0, 1]` is conjugate to `0` iff
`Lt ∈ πℕ`, and then with multiplicity `n − 1`.  A Jacobi field `J` vanishing at `0` with
`DJ/dt(0) = e + a u`, `e ⊥ p, u`, is `L⁻¹ sin(Lt) e + (a/L) t c'(t)` (both have the same initial
data); it vanishes at `t > 0` iff `a = 0` and `sin(Lt) e = 0`, since `e ⊥ c'(t)`.  So
`J ↦ DJ/dt(0)` maps the conjugate space onto `{p, u}ᗮ` if `sin(Lt) = 0`, onto `0` otherwise.
(The hypothesis `1 ≤ n` is not needed: for `n = 0` there are no orthonormal `p`, `u`.) -/
theorem conjMultiplicity_greatCircle (_hn : 1 ≤ n) {p u : 𝔼} (hp : p ∈ Sph n) (hu : ‖u‖ = 1)
    (hpu : ⟪p, u⟫ = 0) {L : ℝ} (hL : 0 < L)
    (hc : IsSmoothCurveIn (sphSub n) (greatCircle p u L)) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    conjMultiplicity (sphSub n) (greatCircle p u L) hc 0 t =
      if ∃ k : ℕ, L * t = k * π then n - 1 else 0 := by
  have hp1 := norm_of_mem_sph hp
  have hpu' : ⟪u, -p⟫ = 0 := by rw [inner_neg_right, real_inner_comm, hpu, neg_zero]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hc0 : greatCircle p u L 0 = p := greatCircle_zero p u L
  set c := greatCircle p u L with hcdef
  set π₀ : ℝ → ℝ := fun s => (projIcc (0 : ℝ) 1 zero_le_one s : ℝ) with hπ₀
  have hπ₀s : ∀ s ∈ Icc (0 : ℝ) 1, π₀ s = s := fun s hs => by
    simp only [hπ₀, projIcc_of_mem _ hs]
  -- the Jacobi fields `sin(Ls) e`, `e ⊥ p, u`, as elements of `𝒥(c)`
  set F : 𝔼 → ℝ → 𝔼 := fun e s => Real.sin (L * π₀ s) • e with hF
  have hFm : ∀ e, ⟪p, e⟫ = 0 → ⟪u, e⟫ = 0 → F e ∈ jacobiSpace (sphSub n) c hc :=
    fun e hpe hue => (isJacobiField_sin_smul hp hu hpu hpe hue L).comp_projIcc_mem hc
  have hFc : ∀ e, ⟪p, e⟫ = 0 → covAlong (sphSub n) c (F e) 0 = L • e := fun e hpe => by
    rw [covAlong_eq_of_hasDerivAt h0 (fun s hs => by simp only [hF, hπ₀s s hs])
      ((hasDerivAt_sin_mul L 0).smul_const e), hc0, prj_sph hp, real_inner_smul_right, hpe]
    simp
  -- the Jacobi field `s c'(s)`
  set G : ℝ → 𝔼 := fun s => π₀ s • (L • greatCircle u (-p) L (π₀ s)) with hG
  have hGm : G ∈ jacobiSpace (sphSub n) c hc :=
    (isJacobiField_smul_deriv_greatCircle hp hu hpu L).comp_projIcc_mem hc
  have hGc : covAlong (sphSub n) c G 0 = L • u := by
    rw [covAlong_eq_of_hasDerivAt h0
      (fun s hs => by simp only [hG, hπ₀s s hs, Pi.smul_apply', Pi.smul_apply, id_eq])
      ((hasDerivAt_id (0 : ℝ)).smul ((hasDerivAt_greatCircle u (-p) L 0).const_smul L)), hc0,
      prj_sph hp]
    simp [greatCircle_zero, real_inner_smul_right, hpu]
  -- `D : J ↦ DJ/dt(0)` is injective on the conjugate space
  set CS := conjSpace (sphSub n) c hc 0 t with hCS
  let D : CS →ₗ[ℝ] 𝔼 := (tanAt (sphSub n) (c 0)).subtype ∘ₗ LinearMap.snd ℝ _ _ ∘ₗ
    jacEval hc h0 ∘ₗ Submodule.inclusion (conjSpace_le_jacobiSpace hc 0 t)
  have hD : ∀ J : CS, D J = covAlong (sphSub n) c (J : ℝ → 𝔼) 0 := fun J => rfl
  have hDinj : Injective D := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro J hJ
    obtain ⟨hJs, hJ0, -⟩ := (mem_conjSpace hc).1 J.2
    exact Subtype.ext (jacobiSpace_eq_zero hc hJs
      (hJs.1.eqOn_zero hc h0 hJ0 ((hD J).symm.trans hJ)))
  -- a field of the conjugate space has `DJ/dt(0) ⊥ p, u`, and `DJ/dt(0) = 0` unless `sin(Lt) = 0`
  have hi : ∀ J ∈ CS, ⟪p, covAlong (sphSub n) c J 0⟫ = 0 ∧ ⟪u, covAlong (sphSub n) c J 0⟫ = 0 ∧
      (Real.sin (L * t) ≠ 0 → covAlong (sphSub n) c J 0 = 0) := by
    intro J hJ
    obtain ⟨hJs, hJ0, hJt⟩ := (mem_conjSpace hc).1 hJ
    have hpy : ⟪p, covAlong (sphSub n) c J 0⟫ = 0 := by
      rw [covAlong, hc0, prj_sph hp, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hp1]
      ring
    set y := covAlong (sphSub n) c J 0 with hy
    set a := ⟪u, y⟫ with ha
    set e := y - a • u with he
    have hpe : ⟪p, e⟫ = 0 := by rw [he, inner_sub_right, real_inner_smul_right, hpy, hpu]; ring
    have hue : ⟪u, e⟫ = 0 := by
      rw [he, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]; ring
    -- `J = L⁻¹ sin(Ls) e + (a/L) s c'(s)`: same initial data
    set K : ℝ → 𝔼 := L⁻¹ • F e + (a / L) • G with hK
    have hKm : K ∈ jacobiSpace (sphSub n) c hc :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hFm e hpe hue)) (Submodule.smul_mem _ _ hGm)
    have hKc : covAlong (sphSub n) c K 0 = y := by
      have hF1 : ContDiffOn ℝ ∞ (L⁻¹ • F e) (Icc 0 1) :=
        (hFm e hpe hue).1.contDiffOn.const_smul L⁻¹
      have hG1 : ContDiffOn ℝ ∞ ((a / L) • G) (Icc 0 1) := hGm.1.contDiffOn.const_smul (a / L)
      rw [hK, covAlong_add h0 hF1 hG1, covAlong_smul, covAlong_smul, hFc e hpe, hGc, smul_smul,
        smul_smul, inv_mul_cancel₀ hL.ne', one_smul, div_mul_cancel₀ _ hL.ne', he, sub_add_cancel]
    have hJK : J = K := by
      have h := (jacEval_bijective hc h0).1 (a₁ := ⟨J, hJs⟩) (a₂ := ⟨K, hKm⟩)
        (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
      · exact congrArg Subtype.val h
      · change J 0 = K 0
        rw [hJ0]
        simp [hK, hF, hG, hπ₀s 0 h0]
      · change covAlong (sphSub n) c J 0 = covAlong (sphSub n) c K 0
        rw [hKc]
    have hKt0 : (L⁻¹ * Real.sin (L * t)) • e + (a * t) • greatCircle u (-p) L t = 0 := by
      rw [← hJt, hJK]
      simp only [hK, hF, hG, Pi.add_apply, Pi.smul_apply, hπ₀s t ht', smul_smul]
      rw [show a / L * (t * L) = a * t by field_simp]
    -- pair with `c'(t)/L ⊥ e`
    have hw1 := inner_greatCircle_self hu (by rw [norm_neg, hp1]) hpu' L t
    have hwe : ⟪greatCircle u (-p) L t, e⟫ = 0 := by
      rw [inner_greatCircle_left, hue, inner_neg_left, hpe]; ring
    have hat : a * t = 0 := by
      have h := congrArg (fun x => ⟪greatCircle u (-p) L t, x⟫) hKt0
      simp only [inner_add_right, real_inner_smul_right, hwe, hw1, inner_zero_right] at h
      linarith
    have ha0 : a = 0 := (mul_eq_zero.1 hat).resolve_right ht.1.ne'
    refine ⟨hpy, ha0, fun hs => ?_⟩
    rw [ha0, zero_mul, zero_smul, add_zero] at hKt0
    have he0 : e = 0 :=
      (smul_eq_zero.1 hKt0).resolve_left (mul_ne_zero (inv_ne_zero hL.ne') hs)
    have hye : y = e + a • u := by rw [he, sub_add_cancel]
    rw [hye, he0, ha0, zero_smul, add_zero]
  -- conversely, if `sin(Lt) = 0`, every `y ⊥ p, u` is `DJ/dt(0)` for `J = L⁻¹ sin(Ls) y`
  have hii : Real.sin (L * t) = 0 → ∀ y : 𝔼, ⟪p, y⟫ = 0 → ⟪u, y⟫ = 0 →
      y ∈ LinearMap.range D := by
    intro hs y hpy huy
    have hJm : L⁻¹ • F y ∈ jacobiSpace (sphSub n) c hc := Submodule.smul_mem _ _ (hFm y hpy huy)
    have hJCS : L⁻¹ • F y ∈ CS := by
      rw [hCS, mem_conjSpace hc]
      refine ⟨hJm, ?_, ?_⟩
      · simp [hF, hπ₀s 0 h0]
      · simp [hF, hπ₀s t ht', hs]
    refine LinearMap.mem_range.2 ⟨⟨_, hJCS⟩, ?_⟩
    rw [hD]
    change covAlong (sphSub n) c (L⁻¹ • F y) 0 = y
    rw [covAlong_smul, hFc y hpy, smul_smul, inv_mul_cancel₀ hL.ne', one_smul]
  rw [conjMultiplicity, ← LinearMap.finrank_range_of_inj hDinj]
  by_cases hs : Real.sin (L * t) = 0
  · have hex : ∃ k : ℕ, L * t = k * π := by
      obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.1 hs
      have hLt : 0 < L * t := mul_pos hL ht.1
      have hm0 : 0 ≤ m := by
        by_contra h
        have : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
        nlinarith [Real.pi_pos]
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
      exact ⟨k, by rw [← hm]; push_cast; ring⟩
    rw [if_pos hex]
    have hR : LinearMap.range D = (Submodule.span ℝ {p, u})ᗮ := by
      ext y
      constructor
      · intro hy
        obtain ⟨J, rfl⟩ := LinearMap.mem_range.1 hy
        obtain ⟨h1, h2, -⟩ := hi J J.2
        exact mem_orthogonal_span_pair.2 ⟨h1, h2⟩
      · intro hy
        obtain ⟨h1, h2⟩ := mem_orthogonal_span_pair.1 hy
        exact hii hs y h1 h2
    rw [hR, finrank_orthogonal_span_pair hp1 hu hpu]
  · have hex : ¬ ∃ k : ℕ, L * t = k * π := fun ⟨k, hk⟩ => hs (by rw [hk, Real.sin_nat_mul_pi])
    rw [if_neg hex]
    have hR : LinearMap.range D = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨J, rfl⟩ := LinearMap.mem_range.1 hy
      rw [Submodule.mem_bot]
      exact (hi J J.2).2.2 hs
    rw [hR, finrank_bot]

/-! ### The geodesics from `p` to `q` -/

/-- The angle `θ = ∠(p, q)`, in `(0, π)` for `q ≠ ±p`. -/
def sphAngle (p q : 𝔼) : ℝ := Real.arccos ⟪p, q⟫

/-- The unit vector `u ⊥ p` in the plane of `p` and `q` with `q = cos θ p + sin θ u`. -/
def sphDir (p q : 𝔼) : 𝔼 := (Real.sin (sphAngle p q))⁻¹ • (q - Real.cos (sphAngle p q) • p)

/-- The length `L(γ_k)` of Milnor's `k`-th geodesic from `p` to `q`: `θ + 2πj` for `k = 2j`,
`2π(j + 1) − θ` for `k = 2j + 1`. -/
def sphLen (p q : 𝔼) (k : ℕ) : ℝ :=
  if Even k then sphAngle p q + 2 * π * (k / 2 : ℕ) else 2 * π * ((k / 2 : ℕ) + 1) - sphAngle p q

/-- **Milnor's geodesic `γ_k`** from `p` to `q` (p. 95): the great circle through `p` and `q`,
run towards `q` for even `k` and in the opposite direction for odd `k`, with length `L(γ_k)`, on
`[0, 1]`. -/
def sphGeod (p q : 𝔼) (k : ℕ) : ℝ → 𝔼 :=
  greatCircle p ((if Even k then (1 : ℝ) else -1) • sphDir p q) (sphLen p q k)

section PQ

variable {p q : EuclideanSpace ℝ (Fin (n + 1))}

theorem inner_lt_one_of_ne (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hqp : q ≠ p) : ⟪p, q⟫ < 1 := by
  have h := norm_sub_sq_real p q
  have h0 : 0 < ‖p - q‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hqp))
  rw [hp, hq] at h
  nlinarith

theorem neg_one_lt_inner_of_ne (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hqn : q ≠ -p) : -1 < ⟪p, q⟫ := by
  have h := norm_add_sq_real p q
  have h0 : 0 < ‖p + q‖ := norm_pos_iff.2 fun h => hqn (eq_neg_of_add_eq_zero_right h)
  rw [hp, hq] at h
  nlinarith

theorem sphAngle_pos (hp : p ∈ Sph n) (hq : q ∈ Sph n) (hqp : q ≠ p) : 0 < sphAngle p q :=
  Real.arccos_pos.2 (inner_lt_one_of_ne (norm_of_mem_sph hp) (norm_of_mem_sph hq) hqp)

theorem sphAngle_lt_pi (hp : p ∈ Sph n) (hq : q ∈ Sph n) (hqn : q ≠ -p) : sphAngle p q < π :=
  Real.arccos_lt_pi.2 (neg_one_lt_inner_of_ne (norm_of_mem_sph hp) (norm_of_mem_sph hq) hqn)

theorem sphLen_two_mul (j : ℕ) : sphLen p q (2 * j) = sphAngle p q + 2 * π * j := by
  rw [sphLen, if_pos (even_two_mul j), Nat.mul_div_cancel_left j two_pos]

theorem sphLen_two_mul_add_one (j : ℕ) :
    sphLen p q (2 * j + 1) = 2 * π * (j + 1) - sphAngle p q := by
  rw [sphLen, if_neg (Nat.not_even_two_mul_add_one j), show (2 * j + 1) / 2 = j by omega]

theorem sphGeod_two_mul (j : ℕ) :
    sphGeod p q (2 * j) = greatCircle p (sphDir p q) (sphAngle p q + 2 * π * j) := by
  rw [sphGeod, sphLen_two_mul, if_pos (even_two_mul j), one_smul]

theorem sphGeod_two_mul_add_one (j : ℕ) :
    sphGeod p q (2 * j + 1) = greatCircle p (-sphDir p q) (2 * π * (j + 1) - sphAngle p q) := by
  rw [sphGeod, sphLen_two_mul_add_one, if_neg (Nat.not_even_two_mul_add_one j), neg_one_smul]

variable (hp : p ∈ Sph n) (hq : q ∈ Sph n) (hqp : q ≠ p) (hqn : q ≠ -p)
include hp hq hqp hqn

theorem cos_sphAngle : Real.cos (sphAngle p q) = ⟪p, q⟫ :=
  Real.cos_arccos (neg_one_lt_inner_of_ne (norm_of_mem_sph hp) (norm_of_mem_sph hq) hqn).le
    (inner_lt_one_of_ne (norm_of_mem_sph hp) (norm_of_mem_sph hq) hqp).le

theorem sin_sphAngle_pos : 0 < Real.sin (sphAngle p q) :=
  Real.sin_pos_of_pos_of_lt_pi (sphAngle_pos hp hq hqp) (sphAngle_lt_pi hp hq hqn)

theorem inner_sphDir : ⟪p, sphDir p q⟫ = 0 := by
  rw [sphDir, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_of_mem_sph hp, cos_sphAngle hp hq hqp hqn]
  ring

theorem norm_sphDir : ‖sphDir p q‖ = 1 := by
  have hs := sin_sphAngle_pos hp hq hqp hqn
  have hc := cos_sphAngle hp hq hqp hqn
  have h2 : ‖q - Real.cos (sphAngle p q) • p‖ ^ 2 = Real.sin (sphAngle p q) ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, norm_of_mem_sph hp,
      norm_of_mem_sph hq, real_inner_comm, ← hc, Real.norm_eq_abs, mul_one, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq (sphAngle p q)]
  have h3 : ‖q - Real.cos (sphAngle p q) • p‖ = Real.sin (sphAngle p q) :=
    (sq_eq_sq₀ (norm_nonneg _) hs.le).1 h2
  rw [sphDir, norm_smul, h3, norm_inv, Real.norm_eq_abs, abs_of_pos hs, inv_mul_cancel₀ hs.ne']

theorem eq_sphDir : q = Real.cos (sphAngle p q) • p + Real.sin (sphAngle p q) • sphDir p q := by
  rw [sphDir, smul_smul, mul_inv_cancel₀ (sin_sphAngle_pos hp hq hqp hqn).ne', one_smul,
    add_sub_cancel]

theorem norm_sphGeodDir (k : ℕ) : ‖(if Even k then (1 : ℝ) else -1) • sphDir p q‖ = 1 := by
  rw [norm_smul, norm_sphDir hp hq hqp hqn, mul_one]
  split_ifs <;> simp

theorem inner_sphGeodDir (k : ℕ) : ⟪p, (if Even k then (1 : ℝ) else -1) • sphDir p q⟫ = 0 := by
  rw [real_inner_smul_right, inner_sphDir hp hq hqp hqn, mul_zero]

theorem sphGeod_one (k : ℕ) : sphGeod p q k 1 = q := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [sphGeod_two_mul, greatCircle, mul_one,
      show sphAngle p q + 2 * π * j = sphAngle p q + (j : ℝ) * (2 * π) by ring,
      Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
    exact (eq_sphDir hp hq hqp hqn).symm
  · rw [sphGeod_two_mul_add_one, greatCircle, mul_one,
      show 2 * π * ((j : ℝ) + 1) - sphAngle p q = ((j + 1 : ℕ) : ℝ) * (2 * π) - sphAngle p q by
        push_cast; ring,
      Real.cos_nat_mul_two_pi_sub, Real.sin_nat_mul_two_pi_sub, smul_neg, neg_smul, neg_neg]
    exact (eq_sphDir hp hq hqp hqn).symm

/-- `γ_k ∈ Ω(Sⁿ; p, q)`. -/
theorem sphGeod_mem_pathSpace (k : ℕ) : sphGeod p q k ∈ pathSpace (Sph n) p q :=
  ⟨IsPiecewiseSmooth.of_contDiff (contDiff_greatCircle _ _ _) zero_le_one,
    fun t _ => greatCircle_mem_sph hp (norm_sphGeodDir hp hq hqp hqn k)
      (inner_sphGeodDir hp hq hqp hqn k) _ t,
    greatCircle_zero _ _ _, sphGeod_one hp hq hqp hqn k⟩

/-- `γ_k` is a geodesic. -/
theorem isUnbrokenGeodesic_sphGeod (k : ℕ) : IsUnbrokenGeodesic (sphSub n) (sphGeod p q k) :=
  ⟨(contDiff_greatCircle _ _ _).contDiffOn, (isGeodesicOn_greatCircle hp
    (norm_sphGeodDir hp hq hqp hqn k) (inner_sphGeodDir hp hq hqp hqn k) _).mono isOpen_Ioo
    (subset_univ _)⟩

/-- **`kπ < L(γ_k)`**. -/
theorem mul_pi_lt_sphLen (k : ℕ) : k * π < sphLen p q k := by
  have h1 := sphAngle_pos hp hq hqp
  have h2 := sphAngle_lt_pi hp hq hqn
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [sphLen_two_mul]; push_cast; linarith
  · rw [sphLen_two_mul_add_one]; push_cast; linarith

/-- **`L(γ_k) < (k + 1)π`**. -/
theorem sphLen_lt (k : ℕ) : sphLen p q k < (k + 1) * π := by
  have h1 := sphAngle_pos hp hq hqp
  have h2 := sphAngle_lt_pi hp hq hqn
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [sphLen_two_mul]; push_cast; linarith
  · rw [sphLen_two_mul_add_one]; push_cast; linarith

theorem sphLen_pos (k : ℕ) : 0 < sphLen p q k :=
  lt_of_le_of_lt (by positivity) (mul_pi_lt_sphLen hp hq hqp hqn k)

/-- The lengths `L(γ_0) < L(γ_1) < ⋯`. -/
theorem sphLen_strictMono : StrictMono (sphLen p q) :=
  strictMono_nat_of_lt_succ fun k => (sphLen_lt hp hq hqp hqn k).trans (by
    have := mul_pi_lt_sphLen hp hq hqp hqn (k + 1)
    push_cast at this
    exact this)

/-- **The energy of `γ_k`** is `L(γ_k)²` (constant speed `L(γ_k)` on `[0, 1]`). -/
theorem energy_sphGeod (k : ℕ) : energy (sphGeod p q k) 0 1 = sphLen p q k ^ 2 :=
  energy_greatCircle (norm_of_mem_sph hp) (norm_sphGeodDir hp hq hqp hqn k)
    (inner_sphGeodDir hp hq hqp hqn k) _

/-- **The geodesics from `p` to `q` are the `γ_k`** (Milnor p. 95): every geodesic
`γ ∈ Ω(Sⁿ; p, q)` agrees on `[0, 1]` with some `γ_k`.  `γ` is a great circle
`cos(Lt) p + sin(Lt) w` (`Morse.exists_eqOn_greatCircle`) with `γ(1) = q`, so `cos L = cos θ` and
`sin L · w = sin θ · u`. -/
theorem exists_eqOn_sphGeod (hn : 1 ≤ n) {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    (hγ : γ ∈ pathSpace (Sph n) p q) (hgeo : IsUnbrokenGeodesic (sphSub n) γ) :
    ∃ k, EqOn γ (sphGeod p q k) (Icc 0 1) := by
  obtain ⟨u, L, hu, hpu, hL, heq⟩ := exists_eqOn_greatCircle hn hγ hgeo
  have hp1 := norm_of_mem_sph hp
  have h1 : greatCircle p u L 1 = q := (heq ⟨zero_le_one, le_rfl⟩).symm.trans hγ.2.2.2
  have hθ0 := sphAngle_pos hp hq hqp
  have hθπ := sphAngle_lt_pi hp hq hqn
  have hs := sin_sphAngle_pos hp hq hqp hqn
  rw [greatCircle, mul_one] at h1
  have hcos : Real.cos L = Real.cos (sphAngle p q) := by
    have := congrArg (fun x => ⟪p, x⟫) h1
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hp1, hpu]
      at this
    rw [cos_sphAngle hp hq hqp hqn, ← this]
    ring
  have hsin : Real.sin L • u = Real.sin (sphAngle p q) • sphDir p q := by
    have := h1.trans (eq_sphDir hp hq hqp hqn)
    rw [hcos] at this
    exact add_left_cancel this
  obtain ⟨m, hm | hm⟩ := Real.cos_eq_cos_iff.1 hcos.symm
  · -- `L = θ + 2πm`, `u = sphDir p q`
    have hsL : Real.sin L = Real.sin (sphAngle p q) := by
      rw [hm, show 2 * (m : ℝ) * π + sphAngle p q = sphAngle p q + m * (2 * π) by ring,
        Real.sin_add_int_mul_two_pi]
    rw [hsL] at hsin
    have hud : u = sphDir p q := smul_right_injective _ hs.ne' hsin
    have hm0 : 0 ≤ m := by
      by_contra h
      have : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      nlinarith [Real.pi_pos]
    obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hm0
    refine ⟨2 * j, fun t ht => ?_⟩
    rw [heq ht, sphGeod_two_mul, ← hud, hm]
    push_cast
    ring_nf
  · -- `L = 2πm − θ`, `u = −sphDir p q`
    have hsL : Real.sin L = -Real.sin (sphAngle p q) := by
      rw [hm, show 2 * (m : ℝ) * π - sphAngle p q = m * (2 * π) - sphAngle p q by ring,
        Real.sin_int_mul_two_pi_sub]
    rw [hsL, neg_smul, neg_eq_iff_eq_neg, ← smul_neg] at hsin
    have hud : u = -sphDir p q := smul_right_injective _ hs.ne' hsin
    have hm0 : 0 ≤ m - 1 := by
      by_contra h
      have : (m : ℝ) ≤ 0 := by exact_mod_cast (show m ≤ 0 by omega)
      nlinarith [Real.pi_pos]
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hm0
    obtain rfl : m = j + 1 := by omega
    refine ⟨2 * j + 1, fun t ht => ?_⟩
    rw [heq ht, sphGeod_two_mul_add_one, ← hud, hm]
    push_cast
    ring_nf

end PQ

/-! ### The indices -/

open Classical in
/-- `Σ_{0 < t < 1} [Lt ∈ πℕ] m = km` for `kπ < L < (k + 1)π`: the terms are the
`t = jπ/L`, `1 ≤ j ≤ k`. -/
theorem finsum_mem_Ioo_ite_eq {L : ℝ} {k : ℕ} (hk1 : k * π < L) (hk2 : L < (k + 1) * π)
    (m : ℕ) : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, (if ∃ j : ℕ, L * t = j * π then m else 0) = k * m := by
  have hL : 0 < L := lt_of_le_of_lt (by positivity) hk1
  set f : ℝ → ℕ := fun t => if ∃ j : ℕ, L * t = j * π then m else 0 with hf
  set T : Finset ℝ := (Finset.Icc 1 k).image (fun j : ℕ => (j : ℝ) * π / L) with hT
  have hTmem : ∀ t, t ∈ T ↔ ∃ j : ℕ, (1 ≤ j ∧ j ≤ k) ∧ (j : ℝ) * π / L = t := by
    intro t
    simp only [hT, Finset.mem_image, Finset.mem_Icc]
  have hinj : Injective (fun j : ℕ => (j : ℝ) * π / L) := by
    intro i j hij
    have : (i : ℝ) = j := by
      have := hij
      simp only at this
      field_simp at this
      nlinarith [Real.pi_pos]
    exact_mod_cast this
  rw [finsum_mem_eq_sum_of_inter_support_eq f (t := T) ?_]
  · rw [Finset.sum_congr rfl (g := fun _ => m) ?_, Finset.sum_const,
      Finset.card_image_of_injective _ hinj, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
    intro t ht
    obtain ⟨j, -, rfl⟩ := (hTmem t).1 ht
    simp only [hf]
    rw [if_pos ⟨j, by field_simp⟩]
  · ext t
    simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
    constructor
    · rintro ⟨ht, hft⟩
      refine ⟨?_, hft⟩
      have hex : ∃ j : ℕ, L * t = j * π := by
        by_contra h
        exact hft (if_neg h)
      obtain ⟨j, hj⟩ := hex
      have hj0 : (0 : ℝ) < j := by
        have : 0 < (j : ℝ) * π := by rw [← hj]; exact mul_pos hL ht.1
        exact pos_of_mul_pos_left this Real.pi_pos.le
      have hjk : (j : ℝ) < k + 1 := by
        have : (j : ℝ) * π < (k + 1) * π := by rw [← hj]; nlinarith [ht.2]
        exact lt_of_mul_lt_mul_right this Real.pi_pos.le
      refine (hTmem t).2 ⟨j, ⟨?_, ?_⟩, ?_⟩
      · exact_mod_cast hj0
      · have : j < k + 1 := by exact_mod_cast hjk
        omega
      · rw [← hj]
        field_simp
    · rintro ⟨ht, hft⟩
      refine ⟨?_, hft⟩
      obtain ⟨j, ⟨hj1, hjk⟩, rfl⟩ := (hTmem t).1 ht
      have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
      refine ⟨div_pos (mul_pos (by linarith) Real.pi_pos) hL, ?_⟩
      rw [div_lt_one hL]
      nlinarith [Real.pi_pos]

section Index

variable {p q : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ Sph n) (hq : q ∈ Sph n) (hqp : q ≠ p)
  (hqn : q ≠ -p)
include hp hq hqp hqn

open Classical in
/-- **Conjugate points along `γ_k`**: `t ∈ (0, 1]` is conjugate to `0` iff `L(γ_k) t ∈ πℕ`, and
then with multiplicity `n − 1`. -/
theorem conjMultiplicity_sphGeod (hn : 1 ≤ n) (k : ℕ)
    (hc : IsSmoothCurveIn (sphSub n) (sphGeod p q k)) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    conjMultiplicity (sphSub n) (sphGeod p q k) hc 0 t =
      if ∃ j : ℕ, sphLen p q k * t = j * π then n - 1 else 0 :=
  conjMultiplicity_greatCircle hn hp (norm_sphGeodDir hp hq hqp hqn k)
    (inner_sphGeodDir hp hq hqp hqn k) (sphLen_pos hp hq hqp hqn k) hc ht

/-- **The index of `γ_k` is `k(n − 1)`** (Milnor p. 96): by the index theorem it is the number of
`t ∈ (0, 1)` with `L(γ_k) t ∈ πℕ`, that is `k` (as `kπ < L(γ_k) < (k + 1)π`), each counted with
multiplicity `n − 1`. -/
theorem formIndex_sphGeod (hn : 1 ≤ n) (k : ℕ) :
    formIndex (energyHessian (sphSub n) (sphGeod_mem_pathSpace hp hq hqp hqn k)) =
      ((k * (n - 1) : ℕ) : ℕ∞) := by
  rw [(theorem_15_1 (sphSub n) (sphGeod_mem_pathSpace hp hq hqp hqn k)
    (isUnbrokenGeodesic_sphGeod hp hq hqp hqn k)).2]
  congr 1
  refine (finsum_mem_congr rfl fun t ht => ?_).trans (finsum_mem_Ioo_ite_eq
    (mul_pi_lt_sphLen hp hq hqp hqn k) (sphLen_lt hp hq hqp hqn k) (n - 1))
  exact conjMultiplicity_sphGeod hp hq hqp hqn hn k _ ⟨ht.1, ht.2.le⟩

/-- **The index of a geodesic from `p` to `q`** agreeing with `γ_k` on `[0, 1]` is `k(n − 1)`. -/
theorem formIndex_eq_of_eqOn_sphGeod (hn : 1 ≤ n) {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    (hγ : γ ∈ pathSpace (Sph n) p q) (hgeo : IsUnbrokenGeodesic (sphSub n) γ) {k : ℕ}
    (heq : EqOn γ (sphGeod p q k) (Icc 0 1)) :
    formIndex (energyHessian (sphSub n) hγ) = ((k * (n - 1) : ℕ) : ℕ∞) := by
  rw [formIndex_energyHessian_congr hγ (sphGeod_mem_pathSpace hp hq hqp hqn k) hgeo
    (isUnbrokenGeodesic_sphGeod hp hq hqp hqn k) heq]
  exact formIndex_sphGeod hp hq hqp hqn hn k

/-- **`p` and `q` are not conjugate along any geodesic** (Milnor p. 95, the hypothesis of
Theorem 17.3): a geodesic from `p` to `q` is some `γ_k` on `[0, 1]`, along which the parameters
conjugate to `0` are the `t` with `L(γ_k) t ∈ πℕ`, and `L(γ_k) ∉ πℕ`. -/
theorem notMem_conjLocus_sph (hn : 1 ≤ n) : q ∉ conjLocus (sphSub n) p := by
  rintro ⟨γ, hc, hgeo, hγ0, hγ1, hconj⟩
  have hγ : γ ∈ pathSpace (Sph n) p q :=
    ⟨IsPiecewiseSmooth.of_contDiffOn hc.contDiffOn zero_le_one subset_rfl, hc.mem, hγ0, hγ1⟩
  obtain ⟨k, hk⟩ := exists_eqOn_sphGeod hp hq hqp hqn hn hγ ⟨hc.contDiffOn, hgeo⟩
  have hc' : IsSmoothCurveIn (sphSub n) (sphGeod p q k) :=
    (isUnbrokenGeodesic_sphGeod hp hq hqp hqn k).isSmoothCurveIn (sphSub n)
      (sphGeod_mem_pathSpace hp hq hqp hqn k)
  have h := ((isConjugate_iff hc').1 ((IsConjugate.congr_curve_iff hk).1 hconj)).2.2.2
  have hno : ¬ ∃ j : ℕ, sphLen p q k * 1 = j * π := by
    rintro ⟨j, hj⟩
    rw [mul_one] at hj
    have h1 := mul_pi_lt_sphLen hp hq hqp hqn k
    have h2 := sphLen_lt hp hq hqp hqn k
    rw [hj] at h1 h2
    have h1' : k < j := by exact_mod_cast lt_of_mul_lt_mul_right h1 Real.pi_pos.le
    have h2' : j < k + 1 := by exact_mod_cast lt_of_mul_lt_mul_right h2 Real.pi_pos.le
    omega
  rw [conjMultiplicity_sphGeod hp hq hqp hqn hn k hc' ⟨zero_lt_one, le_rfl⟩, if_neg hno] at h
  exact lt_irrefl 0 h

end Index

end Morse
