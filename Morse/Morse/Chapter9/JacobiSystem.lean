import Morse.Chapter8.Jacobi
import Morse.Chapter9.JacobiODE

/-!
Milnor, *Morse Theory*, §14, p. 77: the Jacobi equation `D²J/dt² + R(V, J)V = 0` along `γ` is a
linear second-order equation; Jacobi fields are determined by `J(0)` and `DJ/dt(0)`, are defined
along all of `γ` and are smooth (Lemma 14.A and Corollary 14.B of the exposition), for a
submanifold `N ⊆ ℝᴷ` with the induced metric.

# The Jacobi equation as a linear system

## Milnor's text, paraphrased

(p. 77) Choose orthonormal parallel fields `P₁, …, Pₙ` along `γ` and write `J = Σ fⁱ Pᵢ`; the
Jacobi equation becomes the linear system `d²fⁱ/dt² + Σ aⁱⱼ(t) fʲ = 0`, `aⁱⱼ = ⟨R(V, Pⱼ)V, Pᵢ⟩`.
"Thus the Jacobi equation has `2n` linearly independent solutions, each of which can be defined
throughout `γ`.  The solutions are all `C^∞`-differentiable.  A given Jacobi field `J` is
completely determined by its initial conditions `J(0)`, `DJ/dt(0)`."

## In the embedded setting

`γ : ℝ → V` is a smooth curve in `N` on `[0, 1]` (`Morse.IsSmoothCurveIn`); `P(t) = P_{γ(t)}` is
the tangent projection, `P'(t)` its derivative within `[0, 1]` (`Morse.dpAlong`), `V(t)` the
velocity within `[0, 1]` (`Morse.velAlong`) and `K(t)v = R(V, P(t)v)V` (`Morse.curvAlong`).
Instead of a parallel frame (which Chapter 6 only provides for curves defined on all of `ℝ`) the
unknown is the pair `(J, Y)`, `Y = DJ/dt`, in `V × V`, and the Jacobi equation is the first-order
linear system (`Morse.jacSys`)

  `J' = S J + Y`,  `Y' = S Y − K J`,  `S = P'P − PP'`,

with coefficients smooth on `[0, 1]`.  The point of the term `S` is that solutions starting
tangent stay tangent (`Morse.jacSol_mem_tanAt`): the normal parts `a = (1 − P)J`, `b = (1 − P)Y`
satisfy the linear system `a' = −P'a + b`, `b' = −P'b`, because `PP'P = 0` and `(1 − P)P' = P'P`
(differentiate `P² = P`).  Then:

* `Morse.jacSol hN γ s ζ`: the solution of the system with value `ζ` at `s` (the coefficient is
  extended to `ℝ` as a constant outside `[0, 1]`); by `Morse.JacobiODE` it exists on all of `ℝ`.
* `Morse.isJacobiField_jacSol`: for tangent initial data at `s ∈ [0, 1]` its first component is a
  Jacobi field (`Morse.IsJacobiField` of Chapter 8: smooth on `[0, 1]`, tangent, Jacobi equation),
  and its second component is `DJ/dt` (`Morse.covAlong`).
* `Morse.IsJacobiField.eqOn_jacSol`: conversely every Jacobi field `J` is, on `[0, 1]`, the first
  component of `Morse.jacSol` with data `(J(s), DJ/dt(s))`, for every `s ∈ [0, 1]`; in particular
  (`Morse.IsJacobiField.eqOn_zero`) a Jacobi field with `J(s) = 0`, `DJ/dt(s) = 0` vanishes.

## What Milnor leaves implicit

* "Each of which can be defined throughout `γ`" needs the global existence theorem for linear
  equations (`Morse.exists_linearODE`), not the local one.
* "The solutions are all `C^∞`": a bootstrap on the closed interval, with one-sided derivatives at
  the end points (`Morse.contDiffOn_Icc_of_hasDerivAt`).
* Milnor's coordinate system needs parallel fields along `γ`.  In the embedded setting the system
  above, in `V × V`, needs no frame; what replaces the frame is the invariance of the tangent
  bundle along `γ` under the flow of the system.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- **A smooth curve in `N` on `[0, 1]`**: `C^∞` on the closed interval (one-sided derivatives at
the ends), with values in `N` there.  (Milnor's `γ : [0, 1] → M`; values off `[0, 1]` play no
role.) -/
structure IsSmoothCurveIn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (γ : ℝ → V) : Prop where
  contDiffOn : ContDiffOn ℝ ∞ γ (Icc 0 1)
  mem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ N

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- A geodesic in `Ω(N; p, q)` is a smooth curve in `N`. -/
theorem IsUnbrokenGeodesic.isSmoothCurveIn {γ : ℝ → V} {p q : V} (hγ : γ ∈ pathSpace N p q)
    (hgeo : IsUnbrokenGeodesic hN γ) : IsSmoothCurveIn hN γ :=
  ⟨hgeo.1, hγ.2.1⟩

/-! ### Tangent spaces -/

open Classical in
/-- The tangent space `T_xN` as a subspace of `V` (`⊥` off `N`). -/
def tanAt (x : V) : Submodule ℝ V := if h : x ∈ N then tangentSubspace hN ⟨x, h⟩ else ⊥

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem tanAt_of_mem {x : V} (hx : x ∈ N) : tanAt hN x = tangentSubspace hN ⟨x, hx⟩ := by
  rw [tanAt, dif_pos hx]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem mem_tanAt {x v : V} (hx : x ∈ N) : v ∈ tanAt hN x ↔ prj hN x v = v := by
  rw [tanAt_of_mem hN hx, prj_eq_self_iff hN hx]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem prj_mem_tanAt {x : V} (hx : x ∈ N) (v : V) : prj hN x v ∈ tanAt hN x :=
  (mem_tanAt hN hx).2 (prj_prj hN x v)

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
/-- **`dim T_xN = n`**, the dimension of the model space `Z` of `N`: the derivative of the
inclusion is injective. -/
theorem finrank_tanAt {x : V} (hx : x ∈ N) : finrank ℝ (tanAt hN x) = finrank ℝ Z := by
  let _ := hN.chartedSpace
  rw [tanAt_of_mem hN hx, tangentSubspace]
  refine LinearMap.finrank_range_of_inj fun u v huv => ?_
  have h1 := Milnor.Problems.tangentCoord_mfd_val hN ⟨x, hx⟩ u
  have h2 := Milnor.Problems.tangentCoord_mfd_val hN ⟨x, hx⟩ v
  have huv' : Milnor.mfd 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) ⟨x, hx⟩ u =
      Milnor.mfd 𝓘(ℝ, Z) 𝓘(ℝ, V) (Subtype.val : N → V) ⟨x, hx⟩ v := huv
  rw [← h1, ← h2, huv']

/-! ### The coefficients along `γ` -/

variable (γ : ℝ → V)

/-- The velocity `V(t) = dγ/dt`, computed within `[0, 1]`. -/
def velAlong (t : ℝ) : V := derivWithin γ (Icc 0 1) t

/-- `P'(t)`, the derivative within `[0, 1]` of the tangent projection `P(t) = P_{γ(t)}`. -/
def dpAlong (t : ℝ) : V →L[ℝ] V := derivWithin (fun s => prj hN (γ s)) (Icc 0 1) t

/-- The covariant derivative `DX/dt = P(dX/dt)` of a field along `γ`, with the derivative
computed within `[0, 1]` (one-sided at the ends). -/
def covAlong (X : ℝ → V) (t : ℝ) : V := prj hN (γ t) (derivWithin X (Icc 0 1) t)

/-- The map `b ↦ R(a, b)a = II(b, II(a, a)) − II(a, II(b, a))` at `q ∈ N`, as a continuous linear
map. -/
def curvMid (q : N) (a : V) : V →L[ℝ] V :=
  (dN hN (tanProj hN) q).flip (dN hN (tanProj hN) q a a) -
    (dN hN (tanProj hN) q a).comp ((dN hN (tanProj hN) q).flip a)

open Classical in
/-- **The curvature coefficient** `K(t)v = R(V, P(t)v)V` of the Jacobi equation. -/
def curvAlong (t : ℝ) : V →L[ℝ] V :=
  if h : γ t ∈ N then (curvMid hN ⟨γ t, h⟩ (velAlong γ t)).comp (prj hN (γ t)) else 0

/-- `S = P'P − PP'`. -/
def jacS (t : ℝ) : V →L[ℝ] V :=
  (dpAlong hN γ t).comp (prj hN (γ t)) - (prj hN (γ t)).comp (dpAlong hN γ t)

/-- **The Jacobi system** `(J, Y)' = (S J + Y, S Y − K J)` at time `t`. -/
def jacSys (t : ℝ) : (V × V) →L[ℝ] (V × V) :=
  (ContinuousLinearMap.inl ℝ V V).comp
      ((jacS hN γ t).comp (ContinuousLinearMap.fst ℝ V V) + ContinuousLinearMap.snd ℝ V V) +
    (ContinuousLinearMap.inr ℝ V V).comp
      ((jacS hN γ t).comp (ContinuousLinearMap.snd ℝ V V) -
        (curvAlong hN γ t).comp (ContinuousLinearMap.fst ℝ V V))

/-- The Jacobi system with its coefficient extended to `ℝ` as a constant outside `[0, 1]`. -/
def jacA (t : ℝ) : (V × V) →L[ℝ] (V × V) :=
  jacSys hN γ (projIcc (0 : ℝ) 1 zero_le_one t)

variable {hN γ}

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem jacA_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : jacA hN γ t = jacSys hN γ t := by
  rw [jacA, projIcc_of_mem _ ht]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem jacSys_apply (t : ℝ) (z : V × V) :
    jacSys hN γ t z = (jacS hN γ t z.1 + z.2, jacS hN γ t z.2 - curvAlong hN γ t z.1) := by
  simp [jacSys]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curvMid_apply (q : N) (a b : V) : curvMid hN q a b = curvOp hN q a b a := by
  simp [curvMid, curvOp_apply, secondFundForm]

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem curvAlong_apply {t : ℝ} (ht : γ t ∈ N) (b : V) :
    curvAlong hN γ t b = curvR hN (γ t) (velAlong γ t) (prj hN (γ t) b) (velAlong γ t) := by
  rw [curvAlong, dif_pos ht, ContinuousLinearMap.comp_apply, curvMid_apply, curvR_of_mem hN ht]

section Curve

variable (hc : IsSmoothCurveIn hN γ)
include hc

omit [FiniteDimensional ℝ W] in
theorem IsSmoothCurveIn.contDiffOn_prj : ContDiffOn ℝ ∞ (fun t => prj hN (γ t)) (Icc 0 1) :=
  ContDiffOn.prj_comp hN hc.contDiffOn hc.mem

omit [FiniteDimensional ℝ W] in
theorem IsSmoothCurveIn.contDiffOn_dpAlong : ContDiffOn ℝ ∞ (dpAlong hN γ) (Icc 0 1) :=
  hc.contDiffOn_prj.derivWithin (uniqueDiffOn_Icc zero_lt_one) (by simp)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem IsSmoothCurveIn.contDiffOn_velAlong : ContDiffOn ℝ ∞ (velAlong γ) (Icc 0 1) :=
  hc.contDiffOn.derivWithin (uniqueDiffOn_Icc zero_lt_one) (by simp)

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem IsSmoothCurveIn.hasDerivWithinAt {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt γ (velAlong γ t) (Icc 0 1) t :=
  ((hc.contDiffOn.differentiableOn (by simp)) t ht).hasDerivWithinAt

omit [FiniteDimensional ℝ W] in
theorem IsSmoothCurveIn.hasDerivWithinAt_prj {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => prj hN (γ s)) (dpAlong hN γ t) (Icc 0 1) t :=
  ((hc.contDiffOn_prj.differentiableOn (by simp)) t ht).hasDerivWithinAt

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
theorem IsSmoothCurveIn.velAlong_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    velAlong γ t = deriv γ t :=
  ((hc.hasDerivWithinAt (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv.symm

omit [FiniteDimensional ℝ W] in
theorem IsSmoothCurveIn.hasDerivAt_prj {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => prj hN (γ s)) (dpAlong hN γ t) t :=
  (hc.hasDerivWithinAt_prj (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- The velocity is tangent. -/
theorem IsSmoothCurveIn.velAlong_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    prj hN (γ t) (velAlong γ t) = velAlong γ t :=
  (prj_eq_self_iff hN (hc.mem t ht)).2 (hasDerivWithinAt_mem_tangentSubspace hN
    (hc.hasDerivWithinAt ht) (uniqueDiffOn_Icc zero_lt_one t ht) hc.mem ht)

omit [FiniteDimensional ℝ W] in
/-- **`P' = P'P + PP'`** (differentiate `P² = P` within `[0, 1]`). -/
theorem IsSmoothCurveIn.dp_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (v : V) :
    dpAlong hN γ t v = dpAlong hN γ t (prj hN (γ t) v) + prj hN (γ t) (dpAlong hN γ t v) := by
  have h1 := (hc.hasDerivWithinAt_prj ht).clm_comp (hc.hasDerivWithinAt_prj ht)
  have heq : EqOn (fun s => (prj hN (γ s)).comp (prj hN (γ s))) (fun s => prj hN (γ s))
      (Icc 0 1) := fun s _ => by
    ext w
    exact prj_prj hN _ _
  have h2 := h1.congr (fun s hs => (heq hs).symm) (heq ht).symm
  have h3 := (uniqueDiffOn_Icc zero_lt_one t ht).eq_deriv _ h2 (hc.hasDerivWithinAt_prj ht)
  have := congrArg (fun L => L v) h3
  simp only [add_apply, ContinuousLinearMap.comp_apply] at this
  exact this.symm

omit [FiniteDimensional ℝ W] in
/-- **`PP'P = 0`**. -/
theorem IsSmoothCurveIn.prj_dp_prj {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (v : V) :
    prj hN (γ t) (dpAlong hN γ t (prj hN (γ t) v)) = 0 := by
  have h := congrArg (prj hN (γ t)) (hc.dp_eq ht (prj hN (γ t) v))
  rw [prj_prj, map_add, prj_prj] at h
  exact add_eq_left.1 h.symm

omit [FiniteDimensional ℝ W] in
/-- `S v = P'v` for tangent `v`. -/
theorem IsSmoothCurveIn.jacS_of_tangent {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {v : V}
    (hv : prj hN (γ t) v = v) : jacS hN γ t v = dpAlong hN γ t v := by
  have h := hc.prj_dp_prj ht v
  rw [hv] at h
  simp only [jacS, sub_apply, ContinuousLinearMap.comp_apply, hv, h, sub_zero]

omit [FiniteDimensional ℝ W] in
/-- `P S v = 0` for tangent `v`. -/
theorem IsSmoothCurveIn.prj_jacS_of_tangent {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {v : V}
    (hv : prj hN (γ t) v = v) : prj hN (γ t) (jacS hN γ t v) = 0 := by
  rw [hc.jacS_of_tangent ht hv]
  have h := hc.prj_dp_prj ht v
  rwa [hv] at h

omit [FiniteDimensional ℝ W] in
/-- `(1 − P) S v = P'P v` for every `v`. -/
theorem IsSmoothCurveIn.jacS_sub_prj {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (v : V) :
    jacS hN γ t v - prj hN (γ t) (jacS hN γ t v) = dpAlong hN γ t (prj hN (γ t) v) := by
  have h1 := hc.dp_eq ht (prj hN (γ t) v)
  have h2 := hc.prj_dp_prj ht v
  simp only [jacS, sub_apply, ContinuousLinearMap.comp_apply, map_sub,
    prj_prj] at h1 ⊢
  rw [h2]
  linear_combination (norm := module) h1 - h1

/-- The curvature coefficient takes tangent values. -/
theorem IsSmoothCurveIn.prj_curvAlong {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (v : V) :
    prj hN (γ t) (curvAlong hN γ t v) = curvAlong hN γ t v := by
  have hN' := hc.mem t ht
  rw [curvAlong_apply hN', prj_eq_self_iff hN hN', curvR_of_mem hN hN']
  have hV := (prj_eq_self_iff hN hN').1 (hc.velAlong_mem ht)
  exact curvOp_mem hN hV (prj_mem hN hN' v) hV

/-- **The curvature coefficient is smooth on `[0, 1]`**: near `γ(t₀)`, `II = dP` agrees on tangent
vectors with the derivative of the smooth ambient representative `projRep σ` of `P`. -/
theorem IsSmoothCurveIn.contDiffOn_curvAlong : ContDiffOn ℝ ∞ (curvAlong hN γ) (Icc 0 1) := by
  intro t₀ ht₀
  set q : N := ⟨γ t₀, hc.mem t₀ ht₀⟩
  set σ := sliceAt hN q
  have hq : γ t₀ ∈ σ.φ.source := mem_sliceAt_source hN q
  set Qd := fderiv ℝ (projRep σ)
  have hQd : ContDiffAt ℝ ∞ Qd (γ t₀) :=
    (contDiffAt_projRep σ (q := q) hq).fderiv_right (m := ∞) (by simp)
  have hγ := hc.contDiffOn t₀ ht₀
  have hQγ : ContDiffWithinAt ℝ ∞ (fun t => Qd (γ t)) (Icc 0 1) t₀ :=
    hQd.comp_contDiffWithinAt t₀ hγ
  have hV := hc.contDiffOn_velAlong t₀ ht₀
  have hP := hc.contDiffOn_prj t₀ ht₀
  have h1 : ContDiffWithinAt ℝ ∞ (fun t => ((Qd (γ t)).flip (Qd (γ t) (velAlong γ t)
      (velAlong γ t)) - (Qd (γ t) (velAlong γ t)).comp ((Qd (γ t)).flip (velAlong γ t))).comp
      (prj hN (γ t))) (Icc 0 1) t₀ := by
    have hflip : ∀ {f : ℝ → V →L[ℝ] V →L[ℝ] V}, ContDiffWithinAt ℝ ∞ f (Icc 0 1) t₀ →
        ContDiffWithinAt ℝ ∞ (fun t => (f t).flip) (Icc 0 1) t₀ := fun hf =>
      (ContinuousLinearMap.flipₗᵢ ℝ V V V).contDiff.comp_contDiffWithinAt hf
    exact ((((hflip hQγ).clm_apply ((hQγ.clm_apply hV).clm_apply hV)).sub
      ((hQγ.clm_apply hV).clm_comp ((hflip hQγ).clm_apply hV))).clm_comp hP)
  refine h1.congr_of_eventuallyEq_of_mem ?_ ht₀
  have hsrc : ∀ᶠ t in 𝓝[Icc 0 1] t₀, γ t ∈ σ.φ.source :=
    hγ.continuousWithinAt.preimage_mem_nhdsWithin (σ.φ.open_source.mem_nhds hq)
  filter_upwards [hsrc, self_mem_nhdsWithin] with t h1 h2
  have hN' := hc.mem t h2
  rw [curvAlong, dif_pos hN']
  ext b
  have hVt : velAlong γ t ∈ tangentSubspace hN ⟨γ t, hN'⟩ :=
    (prj_eq_self_iff hN hN').1 (hc.velAlong_mem h2)
  have hb : prj hN (γ t) b ∈ tangentSubspace hN ⟨γ t, hN'⟩ := prj_mem hN hN' b
  simp only [ContinuousLinearMap.comp_apply, curvMid, sub_apply,
    ContinuousLinearMap.flip_apply]
  rw [dN_tanProj_eq_fderiv hN σ (q := ⟨γ t, hN'⟩) h1 hb,
    dN_tanProj_eq_fderiv hN σ (q := ⟨γ t, hN'⟩) h1 hVt]

theorem IsSmoothCurveIn.contDiffOn_jacSys : ContDiffOn ℝ ∞ (jacSys hN γ) (Icc 0 1) := by
  have hS : ContDiffOn ℝ ∞ (jacS hN γ) (Icc 0 1) :=
    (hc.contDiffOn_dpAlong.clm_comp hc.contDiffOn_prj).sub
      (hc.contDiffOn_prj.clm_comp hc.contDiffOn_dpAlong)
  have hfst : ContDiffOn ℝ ∞ (fun _ : ℝ => ContinuousLinearMap.fst ℝ V V) (Icc 0 1) :=
    contDiffOn_const
  have hsnd : ContDiffOn ℝ ∞ (fun _ : ℝ => ContinuousLinearMap.snd ℝ V V) (Icc 0 1) :=
    contDiffOn_const
  have hinl : ContDiffOn ℝ ∞ (fun _ : ℝ => ContinuousLinearMap.inl ℝ V V) (Icc 0 1) :=
    contDiffOn_const
  have hinr : ContDiffOn ℝ ∞ (fun _ : ℝ => ContinuousLinearMap.inr ℝ V V) (Icc 0 1) :=
    contDiffOn_const
  exact (hinl.clm_comp ((hS.clm_comp hfst).add hsnd)).add
    (hinr.clm_comp ((hS.clm_comp hsnd).sub (hc.contDiffOn_curvAlong.clm_comp hfst)))

theorem IsSmoothCurveIn.continuous_jacA : Continuous (jacA hN γ) :=
  hc.contDiffOn_jacSys.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    fun t => (projIcc (0 : ℝ) 1 zero_le_one t).2

end Curve

omit [FiniteDimensional ℝ V] in
/-- A solution of `x' = A(t)x` with `A` smooth on `[a, b]` is smooth on `[a, b]` (bootstrap). -/
theorem contDiffOn_Icc_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → E →L[ℝ] E} {f : ℝ → E} {a b : ℝ} (hab : a < b)
    (hA : ContDiffOn ℝ ∞ A (Icc a b)) (hf : ∀ t ∈ Icc a b, HasDerivAt f (A t (f t)) t) :
    ContDiffOn ℝ ∞ f (Icc a b) := by
  have hu := uniqueDiffOn_Icc hab
  have key : ∀ n : ℕ, ContDiffOn ℝ n f (Icc a b) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, contDiffOn_zero]
      exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
    | succ n ih =>
      push_cast
      refine (contDiffOn_succ_iff_derivWithin hu).2 ⟨fun t ht =>
        (hf t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      have h1 : ContDiffOn ℝ n (fun t => A t (f t)) (Icc a b) :=
        (hA.of_le (by exact_mod_cast le_top)).clm_apply ih
      exact h1.congr fun t ht => ((hf t ht).hasDerivWithinAt.derivWithin (hu t ht))
  exact contDiffOn_infty.2 fun n => key n

/-! ### Solutions of the Jacobi system -/

variable (hN γ) in
/-- **The solution of the Jacobi system** with value `ζ = (J(s), DJ/dt(s))` at `s`. -/
def jacSol (s : ℝ) (ζ : V × V) : ℝ → V × V := linSol (jacA hN γ) s ζ

section Sol

variable (hc : IsSmoothCurveIn hN γ)
include hc

theorem jacSol_self (s : ℝ) (ζ : V × V) : jacSol hN γ s ζ s = ζ :=
  linSol_self hc.continuous_jacA s ζ

theorem hasDerivAt_jacSol (s : ℝ) (ζ : V × V) (t : ℝ) :
    HasDerivAt (jacSol hN γ s ζ) (jacA hN γ t (jacSol hN γ s ζ t)) t :=
  hasDerivAt_linSol hc.continuous_jacA s ζ t

theorem jacSol_add (s : ℝ) (ζ η : V × V) :
    jacSol hN γ s (ζ + η) = jacSol hN γ s ζ + jacSol hN γ s η :=
  linSol_add hc.continuous_jacA s ζ η

theorem jacSol_smul (s : ℝ) (c : ℝ) (ζ : V × V) :
    jacSol hN γ s (c • ζ) = c • jacSol hN γ s ζ :=
  linSol_smul hc.continuous_jacA s c ζ

theorem jacSol_zero (s : ℝ) : jacSol hN γ s 0 = 0 := by
  have := jacSol_smul hc s 0 0
  simpa using this

/-- **Solutions starting tangent stay tangent** on `[0, 1]`: the normal parts `a = (1 − P)J`,
`b = (1 − P)Y` solve `a' = −P'a + b`, `b' = −P'b` and vanish at `s`. -/
theorem jacSol_mem_tanAt {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {ζ : V × V}
    (hζ1 : prj hN (γ s) ζ.1 = ζ.1) (hζ2 : prj hN (γ s) ζ.2 = ζ.2) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    prj hN (γ t) (jacSol hN γ s ζ t).1 = (jacSol hN γ s ζ t).1 ∧
      prj hN (γ t) (jacSol hN γ s ζ t).2 = (jacSol hN γ s ζ t).2 := by
  set z := jacSol hN γ s ζ
  -- the normal parts
  set n : ℝ → V × V := fun t => ((z t).1 - prj hN (γ t) (z t).1, (z t).2 - prj hN (γ t) (z t).2)
  -- their linear system
  set M : ℝ → (V × V) →L[ℝ] (V × V) := fun t =>
    (ContinuousLinearMap.inl ℝ V V).comp
        (-((dpAlong hN γ (projIcc (0 : ℝ) 1 zero_le_one t)).comp
          (ContinuousLinearMap.fst ℝ V V)) + ContinuousLinearMap.snd ℝ V V) +
      (ContinuousLinearMap.inr ℝ V V).comp
        (-((dpAlong hN γ (projIcc (0 : ℝ) 1 zero_le_one t)).comp
          (ContinuousLinearMap.snd ℝ V V)))
  have hM : Continuous M := by
    have hD : Continuous fun t => dpAlong hN γ (projIcc (0 : ℝ) 1 zero_le_one t) :=
      hc.contDiffOn_dpAlong.continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_projIcc) fun t => (projIcc (0 : ℝ) 1 _ t).2
    exact (continuous_const.clm_comp (((hD.clm_comp continuous_const).neg).add
      continuous_const)).add (continuous_const.clm_comp (hD.clm_comp continuous_const).neg)
  have hzc : Continuous z := continuous_linSol hc.continuous_jacA s ζ
  have hnc : ContinuousOn n (Icc 0 1) := by
    have hP := hc.contDiffOn_prj.continuousOn
    exact ((hzc.fst.continuousOn).sub (hP.clm_apply hzc.fst.continuousOn)).prodMk
      ((hzc.snd.continuousOn).sub (hP.clm_apply hzc.snd.continuousOn))
  have hnd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt n (M t (n t)) t := by
    intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have hzd := hasDerivAt_jacSol hc s ζ t
    rw [jacA_of_mem ht', jacSys_apply] at hzd
    have hPd := hc.hasDerivAt_prj ht
    have h1 := (hasDerivAt_fst_comp hzd).sub (hPd.clm_apply (hasDerivAt_fst_comp hzd))
    have h2 := (hasDerivAt_snd_comp hzd).sub (hPd.clm_apply (hasDerivAt_snd_comp hzd))
    refine (h1.prodMk h2).congr_deriv ?_
    have e1 := hc.jacS_sub_prj ht' (jacSol hN γ s ζ t).1
    have e2 := hc.jacS_sub_prj ht' (jacSol hN γ s ζ t).2
    have e3 := hc.prj_curvAlong ht' (jacSol hN γ s ζ t).1
    simp only [M, projIcc_of_mem _ ht', n, z]
    refine Prod.ext ?_ ?_
    · simp only [add_apply, neg_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, Prod.fst_add,
        Prod.fst_sub, map_sub, map_add]
      linear_combination (norm := module) e1
    · simp only [add_apply, neg_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, Prod.snd_add,
        Prod.snd_sub, map_sub, map_add]
      linear_combination (norm := module) e2 + e3
  have hn0 : n s = 0 := by
    simp only [n, z, jacSol_self hc, hζ1, hζ2, sub_self, Prod.mk_zero_zero]
  have key := eqOn_Icc_linSol hM zero_lt_one hnc hnd hs ht
  have hl0 : linSol M s 0 = 0 := by
    have := linSol_smul hM s 0 0
    simpa using this
  rw [hn0, hl0] at key
  simp only [Pi.zero_apply, n] at key
  rw [Prod.mk_eq_zero, sub_eq_zero, sub_eq_zero] at key
  exact ⟨key.1.symm, key.2.symm⟩

theorem contDiffOn_jacSol (s : ℝ) (ζ : V × V) : ContDiffOn ℝ ∞ (jacSol hN γ s ζ) (Icc 0 1) :=
  contDiffOn_Icc_of_hasDerivAt zero_lt_one hc.contDiffOn_jacSys fun t ht => by
    rw [← jacA_of_mem ht]
    exact hasDerivAt_jacSol hc s ζ t

/-- **Solutions with tangent initial data are Jacobi fields**, and the second component is the
covariant derivative of the first. -/
theorem isJacobiField_jacSol {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {ζ : V × V}
    (hζ1 : prj hN (γ s) ζ.1 = ζ.1) (hζ2 : prj hN (γ s) ζ.2 = ζ.2) :
    IsJacobiField hN γ (fun t => (jacSol hN γ s ζ t).1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, covAlong hN γ (fun t => (jacSol hN γ s ζ t).1) t =
        (jacSol hN γ s ζ t).2 := by
  set z := jacSol hN γ s ζ
  have htan := fun t ht => jacSol_mem_tanAt hc hs hζ1 hζ2 (t := t) ht
  -- `DJ/dt = Y` on `[0, 1]`
  have hcov : ∀ t ∈ Icc (0 : ℝ) 1, covAlong hN γ (fun t => (z t).1) t = (z t).2 := by
    intro t ht
    have hzd := hasDerivAt_jacSol hc s ζ t
    rw [jacA_of_mem ht, jacSys_apply] at hzd
    have h1 : derivWithin (fun t => (z t).1) (Icc 0 1) t =
        jacS hN γ t (z t).1 + (z t).2 :=
      (hasDerivAt_fst_comp hzd).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht)
    rw [covAlong, h1, map_add, hc.prj_jacS_of_tangent ht (htan t ht).1, zero_add,
      (htan t ht).2]
  refine ⟨⟨fun t ht => (contDiff_fst.comp_contDiffOn (contDiffOn_jacSol hc s ζ)) t ht,
    fun t ht => (htan t ht).1, fun t ht => ?_⟩, hcov⟩
  -- the Jacobi equation at an interior point
  have ht' := Ioo_subset_Icc_self ht
  have hn : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hcovD : covD hN γ (fun t => (z t).1) =ᶠ[𝓝 t] fun t => (z t).2 := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
    have hzd := hasDerivAt_jacSol hc s ζ x
    have := hcov x (Ioo_subset_Icc_self hx)
    rw [covAlong, ((hasDerivAt_fst_comp hzd).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc zero_lt_one x (Ioo_subset_Icc_self hx)))] at this
    rw [covD, (hasDerivAt_fst_comp hzd).deriv]
    exact this
  have hzd := hasDerivAt_jacSol hc s ζ t
  rw [jacA_of_mem ht', jacSys_apply] at hzd
  rw [jacobiExpr, covD, hcovD.deriv_eq, (hasDerivAt_snd_comp hzd).deriv, map_sub,
    hc.prj_jacS_of_tangent ht' (htan t ht').2, zero_sub, hc.prj_curvAlong ht',
    curvAlong_apply (hc.mem t ht'), (htan t ht').1, hc.velAlong_eq ht, neg_add_cancel]

/-- **A Jacobi field is determined by `J(s)`, `DJ/dt(s)`** (Milnor p. 77), for any `s ∈ [0, 1]`:
on `[0, 1]`, `(J, DJ/dt)` is the solution of the Jacobi system with these initial values. -/
theorem IsJacobiField.eqOn_jacSol {J : ℝ → V} (hJ : IsJacobiField hN γ J) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    EqOn (fun t => (J t, covAlong hN γ J t)) (jacSol hN γ s (J s, covAlong hN γ J s))
      (Icc 0 1) := by
  set f : ℝ → V × V := fun t => (J t, covAlong hN γ J t)
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have hJd : ContDiffOn ℝ ∞ (derivWithin J (Icc 0 1)) (Icc 0 1) :=
    hJ.contDiffOn.derivWithin hu (by simp)
  have hfc : ContinuousOn f (Icc 0 1) :=
    hJ.contDiffOn.continuousOn.prodMk (hc.contDiffOn_prj.continuousOn.clm_apply hJd.continuousOn)
  have hfd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt f (jacA hN γ t (f t)) t := by
    intro t ht
    have ht' := Ioo_subset_Icc_self ht
    have hn : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have hJt : HasDerivAt J (deriv J t) t :=
      ((hJ.contDiffOn.contDiffAt hn).differentiableAt (by simp)).hasDerivAt
    have hev : derivWithin J (Icc 0 1) =ᶠ[𝓝 t] deriv J := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      exact ((hJ.contDiffOn.contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt
        (by simp)).hasDerivAt.hasDerivWithinAt.derivWithin (hu x (Ioo_subset_Icc_self hx))
    have hJ't : HasDerivAt (deriv J) (deriv (deriv J) t) t := by
      have := ((hJd.contDiffAt hn).differentiableAt (by simp)).hasDerivAt
      rw [hev.deriv_eq] at this
      exact this.congr_of_eventuallyEq hev.symm
    have hPd := hc.hasDerivAt_prj ht
    have hcov_ev : covAlong hN γ J =ᶠ[𝓝 t] fun x => prj hN (γ x) (deriv J x) := by
      filter_upwards [hev] with x hx
      rw [covAlong, hx]
    have hcovd : HasDerivAt (covAlong hN γ J)
        (dpAlong hN γ t (deriv J t) + prj hN (γ t) (deriv (deriv J) t)) t :=
      (hPd.clm_apply hJ't).congr_of_eventuallyEq hcov_ev
    -- `J = PJ` near `t`
    have hJP : J =ᶠ[𝓝 t] fun x => prj hN (γ x) (J x) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
      exact (hJ.tangent x (Ioo_subset_Icc_self hx)).symm
    have hJ'eq : deriv J t = dpAlong hN γ t (J t) + prj hN (γ t) (deriv J t) := by
      conv_lhs => rw [hJP.deriv_eq]
      exact (hPd.clm_apply hJt).deriv
    -- the Jacobi equation at `t`
    have hjac := hJ.eq t ht
    have hcovD : covD hN γ J =ᶠ[𝓝 t] covAlong hN γ J := by
      filter_upwards [hev] with x hx
      rw [covD, covAlong, hx]
    rw [jacobiExpr, covD, hcovD.deriv_eq, hcovd.deriv, ← hc.velAlong_eq ht] at hjac
    have hR : curvR hN (γ t) (velAlong γ t) (J t) (velAlong γ t) = curvAlong hN γ t (J t) := by
      rw [curvAlong_apply (hc.mem t ht'), hJ.tangent t ht']
    rw [hR] at hjac
    have hJtan := hJ.tangent t ht'
    have hcovt : covAlong hN γ J t = prj hN (γ t) (deriv J t) := by
      rw [covAlong, hev.eq_of_nhds]
    refine (hJt.prodMk hcovd).congr_deriv ?_
    have e2 := hc.prj_dp_prj ht' (J t)
    have e3 := hc.dp_eq ht' (deriv J t)
    have e4 := hc.prj_dp_prj ht' (deriv J t)
    rw [hJtan] at e2
    rw [jacA_of_mem ht', jacSys_apply]
    simp only [f, hcovt]
    simp only [map_add, prj_prj] at hjac
    refine Prod.ext ?_ ?_
    · simp only [jacS, sub_apply, ContinuousLinearMap.comp_apply, hJtan]
      linear_combination (norm := module) hJ'eq + e2
    · simp only [jacS, sub_apply, ContinuousLinearMap.comp_apply, prj_prj]
      linear_combination (norm := module) e3 + hjac + e4
  exact eqOn_Icc_linSol hc.continuous_jacA zero_lt_one hfc hfd hs

/-- **Uniqueness** (Milnor p. 77): a Jacobi field with `J(s) = 0` and `DJ/dt(s) = 0` vanishes on
`[0, 1]`. -/
theorem IsJacobiField.eqOn_zero {J : ℝ → V} (hJ : IsJacobiField hN γ J) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (h0 : J s = 0) (h1 : covAlong hN γ J s = 0) :
    EqOn J 0 (Icc 0 1) := fun t ht => by
  have := hJ.eqOn_jacSol hc hs ht
  rw [h0, h1, Prod.mk_zero_zero, jacSol_zero hc] at this
  exact congrArg Prod.fst this

end Sol

end Morse
