import Morse.Chapter11.ExpSmooth
import Morse.Chapter9.IndexTheorem

/-!
Milnor, *Morse Theory*, §19, pp. 100–103: Lemma 19.1 (no conjugate points in non-positive
curvature) and its consequences that need only the index theorem, for a submanifold `N ⊆ ℝᴷ` with
the induced metric.  The statements of §19 that rest on §17 are listed below and are not proved.

# Non-positive curvature

## Milnor's text, paraphrased

* **Lemma 19.1** (p. 100): if `⟨R(A, B)A, B⟩ ≤ 0` for all tangent vectors `A, B` at every point,
  no two points are conjugate along any geodesic.  Proof: for a Jacobi field `J`,
  `⟨D²J/dt², J⟩ = −⟨R(V, J)V, J⟩ ≥ 0`, so `d/dt ⟨DJ/dt, J⟩ = ⟨D²J/dt², J⟩ + ‖DJ/dt‖² ≥ 0`; the
  function `⟨DJ/dt, J⟩` is monotone, strictly so where `DJ/dt ≠ 0`.  If `J(0) = J(t₀) = 0` it
  vanishes on `[0, t₀]`, so `J(0) = DJ/dt(0) = 0` and `J ≡ 0`.
* (p. 100) The *sectional curvature* of the plane of orthonormal `A, B` is `⟨R(A, B)A, B⟩`; it is
  the Gaussian curvature of the surface `(u₁, u₂) ↦ exp_p(u₁A + u₂B)` (Laugwitz is cited).
  (p. 101) An "optical" description of curvature; examples of complete surfaces of curvature
  `≤ 0` in `ℝ³`; (p. 102) the pseudo-sphere (curvature `−1`, not complete; Hilbert's theorem).
* **Theorem 19.2** (Cartan, p. 102): if `M` is simply connected and complete with curvature
  `≤ 0`, any two points are joined by a unique geodesic and `exp_p : TM_p → M` is a
  diffeomorphism.  Proof: every geodesic from `p` to `q` has index `0` (index theorem), so by
  Theorem 17.3 `Ω(M; p, q)` has the homotopy type of a discrete set, one point for each geodesic;
  `Ω` is connected, so there is one geodesic; `exp_p` is one-one, onto, and by 18.1 non-critical.
* (p. 103) For non-simply-connected `M` the universal cover inherits a complete metric of curvature
  `≤ 0`.  **Corollary 19.3**: if `M` is complete with curvature `≤ 0`, `π_i(M) = 0` for `i > 1`
  and `π_1(M)` has no element of finite order other than the identity.

## In the embedded setting

* `Morse.NonposCurvature hN`: Milnor's hypothesis `⟨R(A, B)A, B⟩ ≤ 0`;
  `Morse.nonposCurvature_iff_sectionalCurvature`: it says exactly that every sectional curvature
  (`Morse.sectionalCurvature` of Chapter 6) is `≤ 0`.
* `Morse.hasDerivAt_inner_covAlong`: `d/dt ⟨DJ/dt, J⟩ = ‖DJ/dt‖² − ⟨R(V, J)V, J⟩`.
* `Morse.IsJacobiField.eqOn_zero_of_nonpos` and **Lemma 19.1**, `Morse.lemma_19_1`: no two
  parameters `a ≠ b` are conjugate along a geodesic `γ : [0, 1] → N`.
* `Morse.formIndex_eq_zero_of_nonpos`: **every geodesic has index `0` and nullity `0`** (the first
  step of the proof of 19.2); `Morse.energyHessian_pos_of_nonpos`: **`E_**` is positive
  definite** at every geodesic (its integral form is `≥ 0`, and a null vector would be a Jacobi
  field vanishing at both ends); `Morse.injective_dExpAt_of_nonpos`: **`exp_p` is non-critical on
  its whole domain** (Theorem 18.1, the last step of the proof of 19.2).
* Ricci curvature, **Theorem 19.4** (Myers), Corollary 19.5 and the example of the sphere are in
  `Morse/Chapter11/Myers.lean`; the index estimate of Theorem 19.6 is in
  `Morse/Chapter11/LongGeodesics.lean`.

## Not done here

* **Depending on §17**, and proved in later files: **Theorem 19.2** (uniqueness of geodesics,
  `exp_p` a diffeomorphism, `M ≅ ℝⁿ`; `Morse.theorem_19_2`) and the first half of **Corollary
  19.3** (`π_i(M) = 0` for `i > 1`; `Morse.corollary_19_3`), both in
  `Morse/Chapter11/CartanHadamard.lean`, on the covering map `exp_p`
  (`Morse.isCoveringMap_expToN`, `Morse/Chapter11/ExpCovering.lean`); and **Theorem 19.6**
  (`Morse.theorem_19_6`, `Morse/Chapter11/PositiveRicci.lean`; for all end points
  `Morse.theorem_19_6_all`, `Morse/Chapter11/PositiveRicciAll.lean`), whose index estimate is in
  `Morse/Chapter11/LongGeodesics.lean`.  Not formalized: no torsion in `π_1(M)` (the second half
  of 19.3), which needs the cohomology of finite cyclic groups.
* Not depending on §17 and not formalized: the identification of the sectional curvature with
  the Gaussian curvature of `exp_p` of a plane (p. 100), and the optics paragraph and the
  examples of pp. 101–102.  Here only the non-criticality of `exp_p` is proved; that `exp_p` is
  then a local diffeomorphism is `Morse.isLocalDiffeomorph_expToN`
  (`Morse/Chapter11/ExpCovering.lean`).

## What Milnor leaves implicit

* **"Strictly so if `DJ/dt ≠ 0`"** is used only through `g' ≥ ‖DJ/dt‖²`: `g ≡ 0` on `[0, t₀]`
  gives `g' = 0`, hence `DJ/dt = 0` on the open interval, and at `0` by continuity (the one-sided
  derivative within `[0, 1]`).
* **Conjugate parameters need not start at `0`**: Milnor takes `J(0) = J(t₀) = 0`; for a geodesic
  on `[0, 1]` and parameters `a < b` the same argument runs on `[a, b]`.
* **The step "index `0`" of 19.2**: the index theorem gives `λ = 0` once there are no conjugate
  points; positive definiteness of `E_**` (not stated by Milnor) follows from the integral form of
  the second variation and Lemma 19.1.  Neither completeness nor compactness is used: Lemma 19.1
  is local along each geodesic.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-! ### `⟨DJ/dt, J⟩` along a Jacobi field -/

omit [FiniteDimensional ℝ W] in
/-- **The derivative of `⟨DJ/dt, J⟩`** along a Jacobi field (Milnor p. 100):
`d/dt ⟨DJ/dt, J⟩ = ⟨D²J/dt², J⟩ + ‖DJ/dt‖² = ‖DJ/dt‖² − ⟨R(V, J)V, J⟩`. -/
theorem hasDerivAt_inner_covAlong {γ J : ℝ → V} (hc : IsSmoothCurveIn hN γ)
    (hJ : IsJacobiField hN γ J) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => ⟪covAlong hN γ J s, J s⟫)
      (‖covAlong hN γ J t‖ ^ 2 - ⟪curvR hN (γ t) (deriv γ t) (J t) (deriv γ t), J t⟫) t := by
  have hO : IsOpen (Ioo (0 : ℝ) 1) := isOpen_Ioo
  have hJO : ContDiffOn ℝ ∞ J (Ioo 0 1) := hJ.contDiffOn.mono Ioo_subset_Icc_self
  have hJ' : ContDiffOn ℝ ∞ (deriv J) (Ioo 0 1) := hJO.deriv_of_isOpen hO (m := ∞) (by simp)
  have hP : ContDiffOn ℝ ∞ (fun s => prj hN (γ s)) (Ioo 0 1) :=
    hc.contDiffOn_prj.mono Ioo_subset_Icc_self
  -- `DJ/dt = P(J')` near `t`
  have hA : ContDiffOn ℝ ∞ (covD hN γ J) (Ioo 0 1) := hP.clm_apply hJ'
  have hAd : HasDerivAt (covD hN γ J) (deriv (covD hN γ J) t) t :=
    ((hA.contDiffAt (hO.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  have hJd : HasDerivAt J (deriv J t) t :=
    ((hJO.contDiffAt (hO.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  have hcov : ∀ s ∈ Ioo (0 : ℝ) 1, covAlong hN γ J s = covD hN γ J s := fun s hs => by
    rw [covAlong, covD, derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
  have hev : (fun s => ⟪covAlong hN γ J s, J s⟫) =ᶠ[𝓝 t] fun s => ⟪covD hN γ J s, J s⟫ := by
    filter_upwards [hO.mem_nhds ht] with s hs
    rw [hcov s hs]
  refine ((hAd.inner ℝ hJd).congr_of_eventuallyEq hev).congr_deriv ?_
  -- the value of the derivative
  have hT : prj hN (γ t) (J t) = J t := hJ.tangent t (Ioo_subset_Icc_self ht)
  have h1 : ⟪deriv (covD hN γ J) t, J t⟫ =
      -⟪curvR hN (γ t) (deriv γ t) (J t) (deriv γ t), J t⟫ := by
    have hjac := hJ.eq t ht
    rw [jacobiExpr, add_eq_zero_iff_eq_neg] at hjac
    rw [← hT, ← inner_prj_left, ← covD, hjac, hT, inner_neg_left]
  have h2 : ⟪covD hN γ J t, deriv J t⟫ = ‖covAlong hN γ J t‖ ^ 2 := by
    rw [hcov t ht, ← real_inner_self_eq_norm_sq, covD]
    conv_rhs => rw [inner_prj_left, prj_prj]
    exact real_inner_comm _ _
  rw [h1, h2]
  ring

omit [FiniteDimensional ℝ W] in
/-- `DX/dt` (computed within `[0, 1]`) of a field smooth on `[0, 1]` along a smooth curve is
continuous on `[0, 1]`. -/
theorem continuousOn_covAlong {γ X : ℝ → V} (hc : IsSmoothCurveIn hN γ)
    (hX : ContDiffOn ℝ ∞ X (Icc 0 1)) : ContinuousOn (covAlong hN γ X) (Icc 0 1) :=
  hc.contDiffOn_prj.continuousOn.clm_apply
    (hX.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) (by simp))

/-! ### Lemma 19.1 -/

variable (hN) in
/-- **Milnor's curvature hypothesis of Lemma 19.1** (p. 100): `⟨R(A, B)A, B⟩ ≤ 0` for all
`A, B ∈ T_qN` and all `q ∈ N`, i.e. every sectional curvature is `≤ 0`
(`Morse.nonposCurvature_iff_sectionalCurvature`). -/
def NonposCurvature : Prop :=
  ∀ q : N, ∀ A ∈ tangentSubspace hN q, ∀ B ∈ tangentSubspace hN q, ⟪curvOp hN q A B A, B⟫ ≤ 0

/-- The hypothesis of Lemma 19.1 says exactly that all sectional curvatures are `≤ 0`: the
sectional curvature of the plane spanned by independent `A, B` has the sign of `⟨R(A, B)A, B⟩`,
which vanishes for dependent `A, B`. -/
theorem nonposCurvature_iff_sectionalCurvature :
    NonposCurvature hN ↔ ∀ q : N, ∀ A B : tangentSubspace hN q, LinearIndependent ℝ ![A, B] →
      sectionalCurvature (curvTensor hN q) A B ≤ 0 := by
  constructor
  · intro h q A B hAB
    have hpos := gram_pos hAB
    rw [sectionalCurvature]
    refine div_nonpos_of_nonpos_of_nonneg ?_ hpos.le
    rw [Submodule.coe_inner, coe_curvTensor_apply]
    exact h q A A.2 B B.2
  · intro h q A hA B hB
    by_cases hAB : LinearIndependent ℝ ![(⟨A, hA⟩ : tangentSubspace hN q), ⟨B, hB⟩]
    · have h1 := h q _ _ hAB
      have hpos := gram_pos hAB
      rw [sectionalCurvature] at h1
      have h2 := (div_nonpos_iff.1 h1)
      rcases h2 with ⟨-, h3⟩ | ⟨h3, -⟩
      · exact absurd h3 (not_le.2 hpos)
      · rw [Submodule.coe_inner, coe_curvTensor_apply] at h3
        exact h3
    · have h0 :=
        (isCurvatureTensor_curvTensor hN q).inner_apply_self_eq_zero_of_not_linearIndependent hAB
      rw [Submodule.coe_inner, coe_curvTensor_apply] at h0
      exact h0.le

/-- **Lemma 19.1, the key step** (Milnor p. 100): if all sectional curvatures are `≤ 0`, a Jacobi
field along a geodesic which vanishes at two parameters `a < b` vanishes identically.
`g = ⟨DJ/dt, J⟩` has `g' = ‖DJ/dt‖² − ⟨R(V, J)V, J⟩ ≥ ‖DJ/dt‖² ≥ 0`, so `g`, vanishing at `a` and
`b`, vanishes on `[a, b]`; then `DJ/dt = 0` on `(a, b)`, hence at `a`, and `J(a) = DJ/dt(a) = 0`. -/
theorem IsJacobiField.eqOn_zero_of_nonpos (hK : NonposCurvature hN) {γ J : ℝ → V}
    (hc : IsSmoothCurveIn hN γ) (hgeo : IsGeodesicOn hN γ (Ioo 0 1)) (hJ : IsJacobiField hN γ J)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) (hab : a < b) (hJa : J a = 0)
    (hJb : J b = 0) : EqOn J 0 (Icc 0 1) := by
  set g : ℝ → ℝ := fun s => ⟪covAlong hN γ J s, J s⟫ with hg
  have hsub : Ioo a b ⊆ Ioo 0 1 := Ioo_subset_Ioo ha.1 hb.2
  have hsubI : Icc a b ⊆ Icc 0 1 := Icc_subset_Icc ha.1 hb.2
  have hd := fun t (ht : t ∈ Ioo a b) => hasDerivAt_inner_covAlong hc hJ (hsub ht)
  -- the curvature term is `≤ 0`
  have hR : ∀ t ∈ Ioo (0 : ℝ) 1, ⟪curvR hN (γ t) (deriv γ t) (J t) (deriv γ t), J t⟫ ≤ 0 := by
    intro t ht
    have hγN := hgeo.mem t ht
    rw [curvR_of_mem hN hγN]
    exact hK ⟨γ t, hγN⟩ _ (hgeo.deriv_mem ht) _
      ((prj_eq_self_iff hN hγN).1 (hJ.tangent t (Ioo_subset_Icc_self ht)))
  -- `g` is monotone on `[a, b]`
  have hcA := continuousOn_covAlong hc hJ.contDiffOn
  have hcont : ContinuousOn g (Icc a b) :=
    ((hcA.mono hsubI).inner (hJ.contDiffOn.continuousOn.mono hsubI))
  have hmono : MonotoneOn g (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont ?_ ?_
    · rw [interior_Icc]
      exact fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hd t ht).deriv]
      nlinarith [hR t (hsub ht), sq_nonneg ‖covAlong hN γ J t‖]
  -- so `g = 0` on `[a, b]`
  have hga : g a = 0 := by simp [hg, hJa]
  have hgb : g b = 0 := by simp [hg, hJb]
  have hg0 : ∀ t ∈ Icc a b, g t = 0 := fun t ht =>
    le_antisymm (hgb ▸ hmono ht ⟨hab.le, le_rfl⟩ ht.2) (hga ▸ hmono ⟨le_rfl, hab.le⟩ ht ht.1)
  -- `DJ/dt = 0` on `(a, b)`
  have hD0 : ∀ t ∈ Ioo a b, covAlong hN γ J t = 0 := by
    intro t ht
    have hderiv0 : deriv g t = 0 := by
      have hev : g =ᶠ[𝓝 t] fun _ => 0 := eventually_of_mem (Ioo_mem_nhds ht.1 ht.2)
        fun s hs => hg0 s (Ioo_subset_Icc_self hs)
      rw [hev.deriv_eq, deriv_const]
    rw [(hd t ht).deriv] at hderiv0
    have hn : ‖covAlong hN γ J t‖ ^ 2 = 0 := by
      nlinarith [hR t (hsub ht), sq_nonneg ‖covAlong hN γ J t‖]
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hn)
  -- hence at `a`, by continuity
  have hDa : covAlong hN γ J a = 0 := by
    have h1 : Tendsto (covAlong hN γ J) (𝓝[Ioo a b] a) (𝓝 (covAlong hN γ J a)) :=
      ((hcA a ha).mono (Ioo_subset_Icc_self.trans hsubI)).tendsto
    have h2 : Tendsto (covAlong hN γ J) (𝓝[Ioo a b] a) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hD0 t ht).symm)
    have := left_nhdsWithin_Ioo_neBot hab
    exact tendsto_nhds_unique h1 h2
  exact hJ.eqOn_zero hc ha hJa hDa

/-- **Lemma 19.1** (Milnor p. 100): if `⟨R(A, B)A, B⟩ ≤ 0` for all tangent vectors `A, B` at every
point, then no two points are conjugate along any geodesic. -/
theorem lemma_19_1 (hK : NonposCurvature hN) {γ : ℝ → V} (hc : IsSmoothCurveIn hN γ)
    (hgeo : IsGeodesicOn hN γ (Ioo 0 1)) (a b : ℝ) : ¬ IsConjugate hN γ a b := by
  rintro ⟨ha, hb, hab, J, hJ, hJa, hJb, t, ht, hJt⟩
  rcases lt_or_gt_of_ne hab with h | h
  · exact hJt (hJ.eqOn_zero_of_nonpos hK hc hgeo ha hb h hJa hJb ht)
  · exact hJt (hJ.eqOn_zero_of_nonpos hK hc hgeo hb ha h hJb hJa ht)

/-! ### Consequences for the index form -/

/-- **With curvature `≤ 0`, every geodesic has index `0` and nullity `0`** (Milnor p. 102, the
first step of the proof of Theorem 19.2: by the index theorem every geodesic from `p` to `q` has
index `λ = 0`; and by Theorem 14.1 its Hessian is non-degenerate). -/
theorem formIndex_eq_zero_of_nonpos (hK : NonposCurvature hN) {p q : V} {γ : ℝ → V}
    (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ) :
    formIndex (energyHessian hN hγ) = 0 ∧ hessNullity hN hγ = 0 := by
  set hc := hgeo.isSmoothCurveIn hN hγ
  refine ⟨?_, ?_⟩
  · rw [(theorem_15_1 hN hγ hgeo).2]
    have h0 : ∀ t ∈ Ioo (0 : ℝ) 1, conjMultiplicity hN γ hc 0 t = 0 := by
      intro t ht
      by_contra h
      exact lemma_19_1 hK hc hgeo.2 0 t ((isConjugate_iff hc).2
        ⟨⟨le_rfl, zero_le_one⟩, Ioo_subset_Icc_self ht, ht.1.ne, Nat.pos_of_ne_zero h⟩)
    rw [finsum_mem_eq_zero_of_forall_eq_zero h0]
    rfl
  · by_contra h
    exact lemma_19_1 hK hc hgeo.2 0 1 ((hessNullity_pos_iff hγ hgeo).1 (Nat.pos_of_ne_zero h))

/-- **With curvature `≤ 0`, `E_**` is positive definite** at every geodesic `γ ∈ Ω(N; p, q)`:
`E_**(W, W) > 0` for every `W ∈ TΩ_γ` that does not vanish identically on `[0, 1]`.  Indeed
`½ E_**(W, W) = ∫₀¹ (‖DW/dt‖² − ⟨R(V, W)V, W⟩) dt ≥ 0` (Proposition 13.A of the exposition), and a
`W` with `E_**(W, W) = 0` lies in the null space of the semi-definite form `E_**`, so it is a Jacobi
field vanishing at `0` and `1` (Theorem 14.1), hence zero by Lemma 19.1. -/
theorem energyHessian_pos_of_nonpos (hK : NonposCurvature hN) {p q : V} {γ : ℝ → V}
    (hγ : γ ∈ pathSpace N p q) (hgeo : IsUnbrokenGeodesic hN γ) (X : pathTangent hN γ)
    (hX : ∃ t ∈ Icc (0 : ℝ) 1, (X : ℝ → V) t ≠ 0) : 0 < energyHessian hN hγ X X := by
  have hnonneg : ∀ Y : pathTangent hN γ, 0 ≤ energyHessian hN hγ Y Y := by
    intro Y
    rw [energyHessian_eq_integral]
    refine mul_nonneg zero_le_two (intervalIntegral.integral_nonneg zero_le_one fun t ht => ?_)
    have h1 : 0 ≤ ⟪covD hN γ Y t, covD hN γ Y t⟫ := real_inner_self_nonneg
    have h2 : ⟪curvR hN (γ t) (deriv γ t) ((Y : ℝ → V) t) (deriv γ t), (Y : ℝ → V) t⟫ ≤ 0 := by
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · rw [← h0, Y.2.2.2.1, inner_zero_right]
      rcases eq_or_lt_of_le ht.2 with h1' | h1'
      · rw [h1', Y.2.2.2.2, inner_zero_right]
      have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1'⟩
      have hγN := hgeo.2.mem t ht'
      rw [curvR_of_mem hN hγN]
      exact hK ⟨γ t, hγN⟩ _ (hgeo.2.deriv_mem ht') _
        ((prj_eq_self_iff hN hγN).1 (Y.2.2.1 t ht))
    linarith
  rcases (hnonneg X).lt_or_eq with h | h
  · exact h
  exfalso
  have hker := ((energyHessian hN hγ).apply_apply_same_eq_zero_iff hnonneg
    (LinearMap.BilinForm.isSymm_iff.1 (energyHessian_isSymm hN hγ))).1 h.symm
  rw [LinearMap.mem_ker] at hker
  have hJ : IsJacobiField hN γ X := (theorem_14_1 hγ hgeo X).1 fun Y => by rw [hker]; rfl
  obtain ⟨t, ht, hXt⟩ := hX
  exact lemma_19_1 hK (hgeo.isSmoothCurveIn hN hγ) hgeo.2 0 1 ⟨⟨le_rfl, zero_le_one⟩,
    ⟨zero_le_one, le_rfl⟩, zero_ne_one, X, hJ, X.2.2.2.1, X.2.2.2.2, t, ht, hXt⟩

/-- **With curvature `≤ 0`, `exp_p` is non-critical on its whole domain** (Milnor p. 103, in the
proof of Theorem 19.2: "it follows from 18.1 that `exp_p` is non-critical everywhere"): by
Theorem 18.1 a critical point `v` would make `exp_p(v)` conjugate to `p` along `γ_v`. -/
theorem injective_dExpAt_of_nonpos (hK : NonposCurvature hN) {p : N} {v : tangentSubspace hN p}
    (hv : v ∈ expDomAt hN p) : Injective (dExpAt hN p v) := by
  by_contra h
  obtain ⟨δ, hδ, hgeo⟩ := isGeodesicOn_ray hv
  exact lemma_19_1 hK (isSmoothCurveIn_ray hv)
    (hgeo.mono isOpen_Ioo (Ioo_subset_Ioo (by linarith) (by linarith))) 0 1
    ((theorem_18_1 hv).2 h)

end Morse
