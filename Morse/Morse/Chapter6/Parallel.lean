import Morse.Chapter6.Submanifold
import Morse.Chapter6.LinearODE

/-!
Milnor, *Morse Theory*, §8, pp. 44–48: covariant differentiation along curves, parallel transport,
and compatibility with the metric, for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# Covariant derivatives along curves and parallel transport in `N ⊆ ℝᴷ`

## Milnor's text (pp. 44–48), paraphrased

* A *parametrized curve* is a smooth map `c : ℝ → M`; a *vector field along `c`* assigns to each
  `t` a vector `V_t ∈ TM_{c(t)}`, smooth in the sense that `t ↦ V_t f` is smooth for every smooth
  `f`; the velocity field is `dc/dt = c_*(d/dt)` (p. 45).
* With a connection, the covariant derivative `V ↦ DV/dt` of fields along `c` is characterized by
  the axioms (a) additivity, (b) `D(fV)/dt = (df/dt)V + f DV/dt`, (c) for `V` induced by a vector
  field `Y`, `DV/dt = (dc/dt) ⊢ Y` (p. 46).  **Lemma 8.1**: there is one and only one such
  operation; Milnor proves it with the coordinate formula
  `DV/dt = Σ_k (dv^k/dt + Σ_{i,j} (du^i/dt) Γ^k_{ij} v^j) ∂_k`.
* `V` is *parallel* if `DV/dt ≡ 0`.  **Lemma 8.2**: given `V₀ ∈ TM_{c(0)}` there is one and only
  one parallel field extending `V₀`; the equations are linear, "so the solutions can be defined
  for all relevant values of `t`" (p. 47).  `V_t` is obtained from `V₀` by *parallel translation*.
* A connection is *compatible with the metric* if parallel translation preserves inner products
  (p. 47).  **Lemma 8.3**: then `d⟨V, W⟩/dt = ⟨DV/dt, W⟩ + ⟨V, DW/dt⟩`, proved with a parallel
  orthonormal frame.

## The embedded setting

For `N ⊆ V` (`Milnor.IsSliceSubmanifold`) with the induced metric and the connection
`X ⊢ Y = P(dY(X))` of `Morse/Chapter6/Submanifold.lean`, everything is global and explicit.  A curve
is `c : ℝ → N` with `t ↦ c(t) ∈ V` smooth; a field along `c` is a map `X : ℝ → V` with
`X t ∈ T_{c(t)}N` (`Morse.IsFieldAlong`).

* `Morse.covDeriv hN c X t = P_{c(t)}(X'(t))`: the covariant derivative along `c`.  It satisfies
  Milnor's axioms (a), (b), (c) (`Morse.covDeriv_add`, `Morse.covDeriv_smul`,
  `Morse.covDeriv_comp`), and it is the only operation that does
  (`Morse.IsCovDerivAlong.eq_covDeriv`: **Lemma 8.1**).  The proof of uniqueness uses no
  coordinates: with an orthonormal basis `(e_i)` of `V`, every field along `c` is
  `X = Σᵢ ⟪eᵢ, X⟫ · (Eᵢ ∘ c)` for the smooth vector fields `Eᵢ(q) = P_q eᵢ` on `N`.
* **Lemma 8.3** for the induced metric: `Morse.hasDerivAt_inner_covDeriv`.  Here it is a direct
  computation and comes *before* parallel transport.
* `Morse.IsParallel hN c X`: `X` is a parallel field along `c`.  Writing `P(t) = P_{c(t)}`, a
  tangent field satisfies `X = PX`, so `X' = P'X + PX'` and `X` is parallel iff `X' = P'X`.
  **Lemma 8.2**: `Morse.exists_unique_isParallel`.  Uniqueness is uniqueness for the linear
  equation `X' = P'(t)X`.  For existence one solves instead `X' = Ω(t)X`,
  `Ω = P'P − PP'`, whose coefficient is skew-adjoint, so that it has global solutions
  (`Morse.exists_skewLinearODE`); since `PP'P = 0` (differentiate `P² = P`), the normal part
  `U = (1 − P)X` satisfies `U' = −P'U`, so a solution starting tangent stays tangent, and then
  `PX' = PΩX = −PP'PX = 0`.  Parallel fields are smooth (`Morse.IsParallel.contDiff`).
* **Compatibility with the metric in Milnor's sense** (p. 47): parallel translation preserves
  inner products (`Morse.IsParallel.inner_eq`).
* `Morse.parallelTransport hN hc t₀ t₁ : T_{c(t₀)}N ≃ₗᵢ T_{c(t₁)}N`: **parallel translation is a
  linear isometry** between the tangent spaces (`Morse.inner_parallelTransport`), the identity for
  `t₁ = t₀` and transitive (`Morse.parallelTransport_self`, `Morse.parallelTransport_trans`).
  (Milnor states Lemma 8.2 with initial time `0`; any initial time is allowed here.)

## What Milnor leaves implicit

* **Lemma 8.2**: "since these equations are linear, the solutions can be defined for all relevant
  values of `t`" needs a global existence theorem for linear equations, which the local theorem he
  cites does not give (see `Morse/Chapter6/LinearODE.lean`), and, on a manifold, a patching of the
  coordinate equations along the curve.  In the embedded setting there is one equation in `ℝᴷ`,
  but the naive equation `X' = P'X` has no a priori bound on its solutions; the equivalent
  equation `X' = (P'P − PP')X` with skew-adjoint coefficient does.  That a solution starting in
  `T_{c(t₀)}N` stays tangent is a second application of uniqueness (to `U' = −P'U`).
* **Lemma 8.3**: Milnor's proof expands `V` and `W` in a parallel orthonormal frame, which needs
  Lemma 8.2 for `n` initial vectors and the fact that the coefficients `⟨V, P_i⟩` are smooth.  For
  the induced metric the lemma is the product rule in `ℝᴷ` plus `⟨PX', Y⟩ = ⟨X', Y⟩` for tangent
  `Y`.
* **Lemma 8.1**: Milnor's uniqueness argument works in one coordinate neighbourhood and uses
  locality of `D/dt` in `t` (which follows from axiom (b)) and extension of the coordinate fields
  `∂_j` to global vector fields; both are hidden in "it follows from (a), (b), and (c)".  In the
  embedded setting the global fields `Eᵢ(q) = P_q eᵢ` replace the coordinate fields.
* Milnor's curves are defined on `ℝ`; so are ours.  Smoothness of a vector field along `c` is
  smoothness of `t ↦ X(t) ∈ ℝᴷ`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Vector fields along a curve and their covariant derivative -/

/-- The velocity vector `dc/dt` of a curve in `N`; it is tangent to `N`
(`Morse.deriv_mem_tangentSubspace`). -/
def velocity (c : ℝ → N) (t : ℝ) : V := deriv (fun s => (c s : V)) t

/-- A **vector field along `c`** (Milnor p. 45): `X t ∈ T_{c(t)}N` for every `t`. -/
def IsFieldAlong (c : ℝ → N) (X : ℝ → V) : Prop := ∀ t, X t ∈ tangentSubspace hN (c t)

/-- **The covariant derivative along `c`** (Milnor p. 46) for the induced metric:
`(DX/dt)(t) = P_{c(t)}(X'(t))`. -/
def covDeriv (c : ℝ → N) (X : ℝ → V) (t : ℝ) : V := tanProj hN (c t) (deriv X t)

variable {c : ℝ → N}

omit [FiniteDimensional ℝ Z] in
theorem covDeriv_mem (c : ℝ → N) (X : ℝ → V) (t : ℝ) :
    covDeriv hN c X t ∈ tangentSubspace hN (c t) :=
  tanProj_apply_mem hN _ _

omit [FiniteDimensional ℝ Z] in
/-- **Milnor's axiom (a)** (p. 46). -/
theorem covDeriv_add {X Y : ℝ → V} {t : ℝ} (hX : DifferentiableAt ℝ X t)
    (hY : DifferentiableAt ℝ Y t) :
    covDeriv hN c (fun s => X s + Y s) t = covDeriv hN c X t + covDeriv hN c Y t := by
  rw [covDeriv, covDeriv, covDeriv, ← map_add, deriv_fun_add hX hY]

omit [FiniteDimensional ℝ Z] in
/-- **Milnor's axiom (b)** (p. 46): `D(fX)/dt = (df/dt) X + f DX/dt`. -/
theorem covDeriv_smul {f : ℝ → ℝ} {X : ℝ → V} {t : ℝ} (hf : DifferentiableAt ℝ f t)
    (hX : DifferentiableAt ℝ X t) (hXT : X t ∈ tangentSubspace hN (c t)) :
    covDeriv hN c (fun s => f s • X s) t = deriv f t • X t + f t • covDeriv hN c X t := by
  rw [covDeriv, covDeriv, deriv_fun_smul hf hX, map_add, map_smul, map_smul,
    tanProj_eq_self hN hXT, add_comm]

omit [FiniteDimensional ℝ Z] in
/-- **Milnor's axiom (c)** (p. 46): for the field induced by a vector field `Y` on `N`,
`DX/dt = (dc/dt) ⊢ Y`. -/
theorem covDeriv_comp (hc : ContDiff ℝ ∞ (fun t => (c t : V))) {Y : N → V} {t : ℝ}
    (hY : letI := hN.chartedSpace; MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, V) Y (c t)) :
    covDeriv hN c (fun s => Y (c s)) t = covAt hN (c t) (velocity c t) Y := by
  rw [covDeriv, (hasDerivAt_comp_curve hN hc hY).deriv, covAt, velocity]

omit [FiniteDimensional ℝ Z] in
/-- **Lemma 8.3** (p. 47) for the induced metric:
`d⟨X, Y⟩/dt = ⟨DX/dt, Y⟩ + ⟨X, DY/dt⟩` for vector fields along `c`. -/
theorem hasDerivAt_inner_covDeriv {X Y : ℝ → V} (hXT : IsFieldAlong hN c X)
    (hYT : IsFieldAlong hN c Y) {t : ℝ} (hX : DifferentiableAt ℝ X t)
    (hY : DifferentiableAt ℝ Y t) :
    HasDerivAt (fun s => ⟪X s, Y s⟫) (⟪covDeriv hN c X t, Y t⟫ + ⟪X t, covDeriv hN c Y t⟫) t := by
  have h := hX.hasDerivAt.inner ℝ hY.hasDerivAt
  rw [covDeriv, covDeriv, inner_tanProj_of_mem hN _ (hYT t), ← inner_tanProj_left,
    tanProj_eq_self hN (hXT t), add_comm]
  exact h

/-! ### Lemma 8.1: uniqueness of the covariant derivative along curves -/

/-- Milnor's axioms (a), (b), (c) (p. 46) for an operation `D` on vector fields along `c`. -/
structure IsCovDerivAlong (c : ℝ → N) (D : (ℝ → V) → ℝ → V) : Prop where
  add : ∀ X Y : ℝ → V, ContDiff ℝ ∞ X → ContDiff ℝ ∞ Y → IsFieldAlong hN c X →
    IsFieldAlong hN c Y → ∀ t, D (fun s => X s + Y s) t = D X t + D Y t
  smul : ∀ (f : ℝ → ℝ) (X : ℝ → V), ContDiff ℝ ∞ f → ContDiff ℝ ∞ X → IsFieldAlong hN c X →
    ∀ t, D (fun s => f s • X s) t = deriv f t • X t + f t • D X t
  induced : ∀ Y : N → V, (letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, V) ∞ Y) →
    IsTangentField hN Y → ∀ t, D (fun s => Y (c s)) t = covAt hN (c t) (velocity c t) Y

omit [FiniteDimensional ℝ Z] in
/-- The covariant derivative `P(X')` satisfies Milnor's axioms (a), (b), (c). -/
theorem isCovDerivAlong_covDeriv (hc : ContDiff ℝ ∞ (fun t => (c t : V))) :
    IsCovDerivAlong hN c (covDeriv hN c) where
  add X Y hX hY _ _ t :=
    covDeriv_add hN ((hX.differentiable (by simp)) t) ((hY.differentiable (by simp)) t)
  smul f X hf hX hXT t :=
    covDeriv_smul hN ((hf.differentiable (by simp)) t) ((hX.differentiable (by simp)) t) (hXT t)
  induced Y hY _ t := by
    let _ := hN.chartedSpace
    exact covDeriv_comp hN hc (hY.mdifferentiableAt (by simp))

/-- An operation satisfying (a), (b), (c) is computed by expanding a field along the smooth
vector fields `Eᵢ(q) = P_q eᵢ`, `(eᵢ)` an orthonormal basis of `V`. -/
theorem IsCovDerivAlong.eq_sum {D : (ℝ → V) → ℝ → V} (hD : IsCovDerivAlong hN c D)
    (hc : ContDiff ℝ ∞ (fun t => (c t : V))) {X : ℝ → V} (hX : ContDiff ℝ ∞ X)
    (hXT : IsFieldAlong hN c X) (t : ℝ) :
    D X t = ∑ i, (deriv (fun s => ⟪stdOrthonormalBasis ℝ V i, X s⟫) t •
        projField hN (stdOrthonormalBasis ℝ V i) (c t) +
      ⟪stdOrthonormalBasis ℝ V i, X t⟫ •
        covAt hN (c t) (velocity c t) (projField hN (stdOrthonormalBasis ℝ V i))) := by
  let _ := hN.chartedSpace
  set b := stdOrthonormalBasis ℝ V with hb
  set F : Fin (finrank ℝ V) → ℝ → V := fun i s => ⟪b i, X s⟫ • projField hN (b i) (c s) with hF
  have hFs : ∀ i, ContDiff ℝ ∞ (F i) := fun i =>
    ((contDiff_const.inner ℝ hX)).smul
      (contDiff_comp_curve hN hc (contMDiff_projField hN (b i)))
  have hFT : ∀ i, IsFieldAlong hN c (F i) := fun i s =>
    Submodule.smul_mem _ _ (isTangentField_projField hN (b i) (c s))
  have hXF : X = fun s => ∑ i, F i s := by
    funext s
    conv_lhs => rw [← tanProj_eq_self hN (hXT s), ← b.sum_repr' (X s)]
    simp only [hF, map_sum, map_smul, projField]
  -- `D` of a finite sum
  have hzero : ∀ t, D (fun _ => (0 : V)) t = 0 := by
    intro t
    have h := hD.add (fun _ => 0) (fun _ => 0) contDiff_const contDiff_const
      (fun s => Submodule.zero_mem _) (fun s => Submodule.zero_mem _) t
    simp only [add_zero] at h
    exact (add_eq_left.1 h.symm)
  have hsum : ∀ s : Finset (Fin (finrank ℝ V)),
      D (fun r => ∑ i ∈ s, F i r) t = ∑ i ∈ s, D (F i) t := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero t
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [hD.add (F a) (fun r => ∑ i ∈ s, F i r) (hFs a) (ContDiff.sum fun i _ => hFs i) (hFT a)
        (fun r => Submodule.sum_mem _ fun i _ => hFT i r) t, ih]
  conv_lhs => rw [hXF]
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hD.smul _ _ (contDiff_const.inner ℝ hX)
      (contDiff_comp_curve hN hc (contMDiff_projField hN (b i)))
      (fun s => isTangentField_projField hN (b i) (c s)) t,
    hD.induced _ (contMDiff_projField hN (b i)) (isTangentField_projField hN (b i)) t]

/-- **Lemma 8.1** (p. 46) for the induced metric: the covariant derivative along `c` is the only
operation on smooth vector fields along `c` satisfying Milnor's axioms (a), (b), (c). -/
theorem IsCovDerivAlong.eq_covDeriv {D : (ℝ → V) → ℝ → V} (hD : IsCovDerivAlong hN c D)
    (hc : ContDiff ℝ ∞ (fun t => (c t : V))) {X : ℝ → V} (hX : ContDiff ℝ ∞ X)
    (hXT : IsFieldAlong hN c X) (t : ℝ) : D X t = covDeriv hN c X t := by
  rw [hD.eq_sum hN hc hX hXT, (isCovDerivAlong_covDeriv hN hc).eq_sum hN hc hX hXT]

/-! ### Parallel vector fields: Lemma 8.2 -/

/-- A **parallel vector field** along `c` (Milnor p. 46): a differentiable vector field along `c`
whose covariant derivative vanishes identically. -/
structure IsParallel (c : ℝ → N) (X : ℝ → V) : Prop where
  mem : IsFieldAlong hN c X
  differentiable : Differentiable ℝ X
  covDeriv_eq_zero : ∀ t, covDeriv hN c X t = 0

/-- The derivative `P'(t) = D_{c'(t)}` of `t ↦ P_{c(t)}`. -/
def dProjAlong (c : ℝ → N) (t : ℝ) : V →L[ℝ] V := dN hN (tanProj hN) (c t) (velocity c t)

variable (hc : ContDiff ℝ ∞ (fun t => (c t : V)))
include hc

theorem hasDerivAt_tanProj_along (t : ℝ) :
    HasDerivAt (fun s => tanProj hN (c s)) (dProjAlong hN c t) t :=
  hasDerivAt_tanProj_comp hN hc t

theorem deriv_tanProj_along : deriv (fun s => tanProj hN (c s)) = dProjAlong hN c :=
  funext fun t => (hasDerivAt_tanProj_along hN hc t).deriv

theorem contDiff_dProjAlong : ContDiff ℝ ∞ (dProjAlong hN c) := by
  rw [← deriv_tanProj_along hN hc]
  exact (contDiff_tanProj_comp hN hc).deriv'

theorem continuous_dProjAlong : Continuous (dProjAlong hN c) :=
  (contDiff_dProjAlong hN hc).continuous

/-- **A tangent field along `c` is parallel iff `X' = P'X`**; here the forward direction. -/
theorem IsParallel.hasDerivAt {X : ℝ → V} (hX : IsParallel hN c X) (t : ℝ) :
    HasDerivAt X (dProjAlong hN c t (X t)) t := by
  have h := (hasDerivAt_tanProj_along hN hc t).clm_apply (hX.differentiable t).hasDerivAt
  have hfun : (fun s => tanProj hN (c s) (X s)) = X := funext fun s => tanProj_eq_self hN (hX.mem s)
  rw [hfun] at h
  have h0 : tanProj hN (c t) (deriv X t) = 0 := hX.covDeriv_eq_zero t
  rwa [h0, add_zero] at h

/-- **Lemma 8.2, uniqueness**: two parallel fields along `c` with the same value at one time are
equal. -/
theorem IsParallel.eq {X Y : ℝ → V} (hX : IsParallel hN c X) (hY : IsParallel hN c Y) {t₀ : ℝ}
    (h : X t₀ = Y t₀) : X = Y :=
  linearODE_eq (continuous_dProjAlong hN hc) (hX.hasDerivAt hN hc) (hY.hasDerivAt hN hc) h

/-- The coefficient `Ω = P'P − PP'` of the equation solved for existence. -/
def skewAlong (c : ℝ → N) (t : ℝ) : V →L[ℝ] V :=
  (dProjAlong hN c t).comp (tanProj hN (c t)) - (tanProj hN (c t)).comp (dProjAlong hN c t)

omit hc in
theorem inner_skewAlong_self (t : ℝ) (x : V) : ⟪skewAlong hN c t x, x⟫ = 0 := by
  simp only [skewAlong, sub_apply, ContinuousLinearMap.comp_apply, inner_sub_left, dProjAlong]
  rw [inner_dN_tanProj_comm, inner_tanProj_left, real_inner_comm, sub_self]

/-- **Lemma 8.2, existence** (p. 47): through every tangent vector at `c(t₀)` there is a parallel
field along `c`, defined for all `t`. -/
theorem exists_isParallel {t₀ : ℝ} {v : V} (hv : v ∈ tangentSubspace hN (c t₀)) :
    ∃ X : ℝ → V, IsParallel hN c X ∧ X t₀ = v := by
  have hP : Continuous fun t => tanProj hN (c t) := (contDiff_tanProj_comp hN hc).continuous
  have hD := continuous_dProjAlong hN hc
  have hΩ : Continuous (skewAlong hN c) := (hD.clm_comp hP).sub (hP.clm_comp hD)
  obtain ⟨α, hα0, hα⟩ := exists_skewLinearODE hΩ (inner_skewAlong_self hN) t₀ v
  have hvel : ∀ t, velocity c t ∈ tangentSubspace hN (c t) := deriv_mem_tangentSubspace hN hc
  have hPDP : ∀ t w, tanProj hN (c t) (dProjAlong hN c t (tanProj hN (c t) w)) = 0 :=
    fun t w => tanProj_dN_tanProj hN (hvel t) w
  -- the normal part `U = α − Pα` satisfies `U' = −P'U`, so it vanishes
  set U : ℝ → V := fun t => α t - tanProj hN (c t) (α t) with hU
  have hU' : ∀ t, HasDerivAt U ((-dProjAlong hN c t) (U t)) t := by
    intro t
    have h : HasDerivAt U (skewAlong hN c t (α t) -
        (dProjAlong hN c t (α t) + tanProj hN (c t) (skewAlong hN c t (α t)))) t :=
      (hα t).sub ((hasDerivAt_tanProj_along hN hc t).clm_apply (hα t))
    have hval : (-dProjAlong hN c t) (U t) = skewAlong hN c t (α t) -
        (dProjAlong hN c t (α t) + tanProj hN (c t) (skewAlong hN c t (α t))) := by
      unfold skewAlong
      simp only [hU, neg_apply, sub_apply, ContinuousLinearMap.comp_apply, map_sub,
        tanProj_tanProj, hPDP]
      abel
    rw [hval]
    exact h
  have hU0 : U = fun _ => 0 :=
    linearODE_eq (A := fun t => -dProjAlong hN c t) hD.neg hU'
      (fun t => by simpa using hasDerivAt_const t (0 : V)) (t₀ := t₀)
      (by simp [hU, hα0, tanProj_eq_self hN hv])
  have hαT : ∀ t, α t ∈ tangentSubspace hN (c t) := by
    intro t
    have h := congrFun hU0 t
    simp only [hU, sub_eq_zero] at h
    rw [h]
    exact tanProj_apply_mem hN _ _
  refine ⟨α, ⟨hαT, fun t => (hα t).differentiableAt, fun t => ?_⟩, hα0⟩
  rw [covDeriv, (hα t).deriv]
  simp only [skewAlong, sub_apply, ContinuousLinearMap.comp_apply, map_sub, tanProj_tanProj,
    hPDP]
  rw [← tanProj_eq_self hN (hαT t), hPDP, sub_self]

/-- **Lemma 8.2** (p. 47): given a tangent vector `v` at `c(t₀)`, there is one and only one
parallel vector field along `c` with value `v` at `t₀`. -/
theorem exists_unique_isParallel {t₀ : ℝ} {v : V} (hv : v ∈ tangentSubspace hN (c t₀)) :
    ∃! X : ℝ → V, IsParallel hN c X ∧ X t₀ = v := by
  obtain ⟨X, hX, hX0⟩ := exists_isParallel hN hc hv
  exact ⟨X, ⟨hX, hX0⟩, fun Y ⟨hY, hY0⟩ => hY.eq hN hc hX (hY0.trans hX0.symm)⟩

/-- Parallel fields are smooth. -/
theorem IsParallel.contDiff {X : ℝ → V} (hX : IsParallel hN c X) : ContDiff ℝ ∞ X := by
  have hD := contDiff_dProjAlong hN hc
  have hderiv : deriv X = fun t => dProjAlong hN c t (X t) :=
    funext fun t => (hX.hasDerivAt hN hc t).deriv
  rw [contDiff_infty]
  intro n
  induction n with
  | zero => exact contDiff_zero.2 hX.differentiable.continuous
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
    refine ⟨hX.differentiable, fun h => absurd h (by simp), ?_⟩
    rw [hderiv]
    exact (hD.of_le (by exact_mod_cast le_top)).clm_apply ih

omit [FiniteDimensional ℝ Z] hc in
/-- **Compatibility with the metric** in Milnor's sense (definition on p. 47): parallel translation
preserves inner products, i.e. `⟨X, Y⟩` is constant for parallel fields `X`, `Y`. -/
theorem IsParallel.inner_eq {X Y : ℝ → V} (hX : IsParallel hN c X) (hY : IsParallel hN c Y)
    (s t : ℝ) : ⟪X s, Y s⟫ = ⟪X t, Y t⟫ := by
  have hd : ∀ t, HasDerivAt (fun s => ⟪X s, Y s⟫) 0 t := by
    intro t
    have h := hasDerivAt_inner_covDeriv hN hX.mem hY.mem (hX.differentiable t)
      (hY.differentiable t)
    rwa [hX.covDeriv_eq_zero, hY.covDeriv_eq_zero, inner_zero_left, inner_zero_right,
      add_zero] at h
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s t

omit [FiniteDimensional ℝ Z] hc in
theorem IsParallel.add {X Y : ℝ → V} (hX : IsParallel hN c X) (hY : IsParallel hN c Y) :
    IsParallel hN c (fun t => X t + Y t) where
  mem t := Submodule.add_mem _ (hX.mem t) (hY.mem t)
  differentiable := hX.differentiable.add hY.differentiable
  covDeriv_eq_zero t := by
    rw [covDeriv_add hN (hX.differentiable t) (hY.differentiable t), hX.covDeriv_eq_zero,
      hY.covDeriv_eq_zero, add_zero]

omit [FiniteDimensional ℝ Z] hc in
theorem IsParallel.const_smul {X : ℝ → V} (hX : IsParallel hN c X) (a : ℝ) :
    IsParallel hN c (fun t => a • X t) where
  mem t := Submodule.smul_mem _ a (hX.mem t)
  differentiable := hX.differentiable.const_smul a
  covDeriv_eq_zero t := by
    have h := covDeriv_smul hN (f := fun _ => a) (differentiableAt_const a)
      (hX.differentiable t) (hX.mem t)
    rw [h, hX.covDeriv_eq_zero, deriv_const, zero_smul, smul_zero, add_zero]

omit hc

/-! ### Parallel translation -/

open Classical in
/-- **The parallel field** along `c` with value `v` at time `t₀` (Lemma 8.2), or `0` if there is
none (which happens only when `v` is not tangent at `c(t₀)` or `c` is not smooth). -/
def parallelField (c : ℝ → N) (t₀ : ℝ) (v : V) : ℝ → V :=
  if h : ∃ X : ℝ → V, IsParallel hN c X ∧ X t₀ = v then h.choose else 0

theorem parallelField_spec (hc : ContDiff ℝ ∞ (fun t => (c t : V))) {t₀ : ℝ} {v : V}
    (hv : v ∈ tangentSubspace hN (c t₀)) :
    IsParallel hN c (parallelField hN c t₀ v) ∧ parallelField hN c t₀ v t₀ = v := by
  have h := exists_isParallel hN hc hv
  rw [parallelField, dif_pos h]
  exact h.choose_spec

theorem IsParallel.eq_parallelField (hc : ContDiff ℝ ∞ (fun t => (c t : V))) {X : ℝ → V}
    (hX : IsParallel hN c X) (t₀ : ℝ) : X = parallelField hN c t₀ (X t₀) :=
  hX.eq hN hc (parallelField_spec hN hc (hX.mem t₀)).1 (parallelField_spec hN hc (hX.mem t₀)).2.symm

/-- **Parallel translation** along `c` from `c(t₀)` to `c(t₁)` (Milnor p. 47), as a linear map
of the tangent spaces which preserves the norm. -/
def parallelTransportL (hc : ContDiff ℝ ∞ (fun t => (c t : V))) (t₀ t₁ : ℝ) :
    tangentSubspace hN (c t₀) →ₗᵢ[ℝ] tangentSubspace hN (c t₁) where
  toFun v := ⟨parallelField hN c t₀ v t₁, (parallelField_spec hN hc v.2).1.mem t₁⟩
  map_add' v w := by
    apply Subtype.ext
    have hv := parallelField_spec hN hc v.2
    have hw := parallelField_spec hN hc w.2
    have h := ((hv.1.add hN hw.1).eq_parallelField hN hc t₀)
    simp only [hv.2, hw.2] at h
    simp only [Submodule.coe_add]
    rw [← congrFun h t₁]
  map_smul' a v := by
    apply Subtype.ext
    have hv := parallelField_spec hN hc v.2
    have h := ((hv.1.const_smul hN a).eq_parallelField hN hc t₀)
    simp only [hv.2] at h
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [← congrFun h t₁]
  norm_map' v := by
    have hv := parallelField_spec hN hc v.2
    have h := hv.1.inner_eq hN hv.1 t₁ t₀
    rw [hv.2, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    change ‖parallelField hN c t₀ v t₁‖ = ‖(v : V)‖
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem parallelTransportL_apply (hc : ContDiff ℝ ∞ (fun t => (c t : V))) (t₀ t₁ : ℝ)
    (v : tangentSubspace hN (c t₀)) :
    (parallelTransportL hN hc t₀ t₁ v : V) = parallelField hN c t₀ v t₁ := rfl

theorem surjective_parallelTransportL (hc : ContDiff ℝ ∞ (fun t => (c t : V))) (t₀ t₁ : ℝ) :
    Surjective (parallelTransportL hN hc t₀ t₁) := by
  intro w
  have hw := parallelField_spec hN hc w.2
  refine ⟨⟨parallelField hN c t₁ w t₀, hw.1.mem t₀⟩, Subtype.ext ?_⟩
  rw [parallelTransportL_apply, ← hw.1.eq_parallelField hN hc t₀, hw.2]

/-- **Parallel translation along `c` is a linear isometry** `T_{c(t₀)}N ≃ T_{c(t₁)}N` (Milnor
p. 47, with the definition of compatibility with the metric). -/
def parallelTransport (hc : ContDiff ℝ ∞ (fun t => (c t : V))) (t₀ t₁ : ℝ) :
    tangentSubspace hN (c t₀) ≃ₗᵢ[ℝ] tangentSubspace hN (c t₁) :=
  LinearIsometryEquiv.ofSurjective (parallelTransportL hN hc t₀ t₁)
    (surjective_parallelTransportL hN hc t₀ t₁)

theorem parallelTransport_apply (hc : ContDiff ℝ ∞ (fun t => (c t : V))) (t₀ t₁ : ℝ)
    (v : tangentSubspace hN (c t₀)) :
    (parallelTransport hN hc t₀ t₁ v : V) = parallelField hN c t₀ v t₁ := rfl

/-- Parallel translation from `c(t₀)` to itself is the identity. -/
theorem parallelTransport_self (hc : ContDiff ℝ ∞ (fun t => (c t : V))) (t₀ : ℝ)
    (v : tangentSubspace hN (c t₀)) : parallelTransport hN hc t₀ t₀ v = v :=
  Subtype.ext (parallelField_spec hN hc v.2).2

/-- **Parallel translation is transitive**: transporting from `c(t₀)` to `c(t₁)` and then to
`c(t₂)` is transporting from `c(t₀)` to `c(t₂)`. -/
theorem parallelTransport_trans (hc : ContDiff ℝ ∞ (fun t => (c t : V))) (t₀ t₁ t₂ : ℝ)
    (v : tangentSubspace hN (c t₀)) :
    parallelTransport hN hc t₁ t₂ (parallelTransport hN hc t₀ t₁ v) =
      parallelTransport hN hc t₀ t₂ v := by
  apply Subtype.ext
  have hv := parallelField_spec hN hc v.2
  rw [parallelTransport_apply, parallelTransport_apply, parallelTransport_apply,
    ← hv.1.eq_parallelField hN hc t₁]

/-- **Parallel translation preserves inner products.** -/
theorem inner_parallelTransport (hc : ContDiff ℝ ∞ (fun t => (c t : V))) (t₀ t₁ : ℝ)
    (v w : tangentSubspace hN (c t₀)) :
    ⟪(parallelTransport hN hc t₀ t₁ v : V), parallelTransport hN hc t₀ t₁ w⟫ = ⟪(v : V), w⟫ := by
  rw [← Submodule.coe_inner, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]

end Morse
