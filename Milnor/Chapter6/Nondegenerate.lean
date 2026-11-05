import Milnor.Chapter6.Invariance

/-!
# Milnor's Lemma 4 of §6 (p. 36): the index at a non-degenerate zero

A zero `z` of a smooth vector field `v` on `ℝⁿ⁺¹` is **non-degenerate** when the derivative
`dv_z` is non-singular.  Milnor's Lemma 4 (§6, p. 36) asserts that the index of `v` at such a
zero is `+1` or `-1` according as the determinant of `dv_z` is positive or negative; that is,
`index v z = sgn (det dv_z)`.

The proof follows Milnor.  Write `A = dv_z`.

* A bijective linear map of `ℝⁿ⁺¹` is bounded below, `‖A y‖ ≥ c ‖y‖` for some `c > 0`
  (`exists_lower_bound_of_bijective`); since `v x = A (x - z) + o(|x - z|)`, there is a radius
  `r > 0` such that on the punctured closed `r`-ball no combination
  `A (x - z) + b • (v x - A (x - z))` with `0 ≤ b ≤ 1` vanishes
  (`exists_radius_of_nondegenerate`).  The case `b = 1` says that `z` is an isolated zero.
* Consequently the straight-line homotopy `linHomotopy` from `v` to its linear part
  `x ↦ A (x - z)` keeps the sphere of radius `r` about `z` free of zeros, so homotopy invariance
  of the index (`indexAt_eq_of_homotopy`) replaces `v` by `x ↦ A (x - z)`.
* The sphere map of the linear field is `u ↦ A u / |A u|`, because normalization ignores the
  positive factor `r` (`nv0_smul`).  That map is a bijection of `Sⁿ` whose sign is `sgn (det A)`
  at every point (`signAt_nv0_linear`, the substitute in this development for Milnor's Lemma 2),
  so every point is a regular value with exactly one preimage and the degree is `sgn (det A)`
  (`deg_nv0_linear`).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Sphere

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (n + 1))

/-! ### Non-degeneracy makes the zero isolated -/

/-- **A bijective linear map of `ℝⁿ⁺¹` is bounded below**: `‖A y‖ ≥ c ‖y‖` for some `c > 0`.
(The constant is `‖A⁻¹‖⁻¹`, truncated so as to avoid discussing whether `‖A⁻¹‖ > 0`.) -/
theorem exists_lower_bound_of_bijective {A : 𝔼 →L[ℝ] 𝔼} (hA : Bijective A) :
    ∃ c > 0, ∀ y : 𝔼, c * ‖y‖ ≤ ‖A y‖ := by
  set Ae := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.2 hA.1)
    (LinearMap.range_eq_top.2 hA.2) with hAe_def
  have hAec : Ae.toContinuousLinearMap = A := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hsymm : ∀ y : 𝔼, Ae.symm.toContinuousLinearMap (A y) = y := fun y => by
    have hy : A y = Ae y := by rw [← hAec]; rfl
    rw [hy]
    exact Ae.symm_apply_apply y
  set K := max ‖Ae.symm.toContinuousLinearMap‖ 1 with hK
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨K⁻¹, inv_pos.2 hK0, fun y => ?_⟩
  have h1 : ‖y‖ ≤ K * ‖A y‖ := by
    calc ‖y‖ = ‖Ae.symm.toContinuousLinearMap (A y)‖ := by rw [hsymm]
      _ ≤ ‖Ae.symm.toContinuousLinearMap‖ * ‖A y‖ := Ae.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ K * ‖A y‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hK0).le
  rwa [← mul_assoc, inv_mul_cancel₀ hK0.ne', one_mul] at h2

/-- **The basic estimate at a non-degenerate zero.**  If `v` is smooth, `v z = 0` and `A = dv_z`
is bijective, there is `r > 0` such that for `x` in the closed `r`-ball, `x ≠ z`, and any
`0 ≤ b ≤ 1`, the vector `A (x - z) + b • (v x - A (x - z))` is nonzero.  Taking `b = 1` says that
`z` is an isolated zero of `v`; the general `b` is the straight-line homotopy from `v` to its
linear part. -/
theorem exists_radius_of_nondegenerate {v : 𝔼 → 𝔼}
    (hv : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔼) ∞ v) {z : 𝔼} (hvz : v z = 0)
    (hA : Bijective (fderiv ℝ v z)) :
    ∃ r > 0, ∀ x : 𝔼, dist x z ≤ r → x ≠ z → ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      fderiv ℝ v z (x - z) + b • (v x - fderiv ℝ v z (x - z)) ≠ 0 := by
  obtain ⟨c, hc, hcA⟩ := exists_lower_bound_of_bijective hA
  have hv' : ContDiff ℝ ∞ v := contMDiff_iff_contDiff.1 hv
  have hd : HasFDerivAt v (fderiv ℝ v z) z := (hv'.differentiable (by simp) z).hasFDerivAt
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.1 (hd.isLittleO.def (half_pos hc))
  refine ⟨δ / 2, by positivity, fun x hx hxz b hb0 hb1 => ?_⟩
  have hbd : ‖v x - fderiv ℝ v z (x - z)‖ ≤ c / 2 * ‖x - z‖ := by
    have h := hδb (lt_of_le_of_lt hx (by linarith))
    rwa [hvz, sub_zero] at h
  have hnp : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
  have hlow : ‖fderiv ℝ v z (x - z)‖ - ‖b • (v x - fderiv ℝ v z (x - z))‖ ≤
      ‖fderiv ℝ v z (x - z) + b • (v x - fderiv ℝ v z (x - z))‖ := by
    have h := norm_sub_norm_le (fderiv ℝ v z (x - z)) (-(b • (v x - fderiv ℝ v z (x - z))))
    rwa [norm_neg, sub_neg_eq_add] at h
  have hb : ‖b • (v x - fderiv ℝ v z (x - z))‖ ≤ c / 2 * ‖x - z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0]
    calc b * ‖v x - fderiv ℝ v z (x - z)‖ ≤ 1 * (c / 2 * ‖x - z‖) :=
          mul_le_mul hb1 hbd (norm_nonneg _) zero_le_one
      _ = c / 2 * ‖x - z‖ := one_mul _
  have hAl : c * ‖x - z‖ ≤ ‖fderiv ℝ v z (x - z)‖ := hcA (x - z)
  have hpos : 0 < c / 2 * ‖x - z‖ := mul_pos (half_pos hc) hnp
  exact norm_pos_iff.1 (by linarith)

/-! ### The straight-line homotopy to the linear part -/

/-- The straight-line homotopy from a vector field `v` to the linear field `x ↦ A (x - z)`,
reparametrized by `Real.smoothTransition` so as to be globally smooth and constant for `t ≤ 0`
and `t ≥ 1`: `linHomotopy v z A (x, t) = A (x - z) + (1 - σ t) • (v x - A (x - z))`, which is
`v x` at `t = 0` and `A (x - z)` at `t = 1`. -/
def linHomotopy (v : 𝔼 → 𝔼) (z : 𝔼) (A : 𝔼 →L[ℝ] 𝔼) (p : 𝔼 × ℝ) : 𝔼 :=
  A (p.1 - z) + (1 - Real.smoothTransition p.2) • (v p.1 - A (p.1 - z))

/-- The straight-line homotopy is globally smooth. -/
theorem contMDiff_linHomotopy {v : 𝔼 → 𝔼} (hv : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔼) ∞ v) (z : 𝔼)
    (A : 𝔼 →L[ℝ] 𝔼) :
    ContMDiff (𝓘(ℝ, 𝔼).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼) ∞ (linHomotopy v z A) := by
  have hs : ContMDiff (𝓘(ℝ, 𝔼).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : 𝔼 × ℝ => 1 - Real.smoothTransition p.2) :=
    contMDiff_const.sub (Real.smoothTransition.contDiff.contMDiff.comp contMDiff_snd)
  have hvp : ContMDiff (𝓘(ℝ, 𝔼).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼) ∞ (fun p : 𝔼 × ℝ => v p.1) :=
    hv.comp contMDiff_fst
  have hAp : ContMDiff (𝓘(ℝ, 𝔼).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, 𝔼) ∞ (fun p : 𝔼 × ℝ => A (p.1 - z)) :=
    A.contMDiff.comp (contMDiff_fst.sub contMDiff_const)
  exact hAp.add (hs.smul (hvp.sub hAp))

/-- At `t = 0` the homotopy is the field `v` itself. -/
theorem linHomotopy_zero (v : 𝔼 → 𝔼) (z : 𝔼) (A : 𝔼 →L[ℝ] 𝔼) :
    (fun x => linHomotopy v z A (x, 0)) = v := by
  funext x
  show A (x - z) + (1 - Real.smoothTransition (0 : ℝ)) • (v x - A (x - z)) = v x
  rw [Real.smoothTransition.zero, sub_zero, one_smul]
  abel

/-- At `t = 1` the homotopy is the linear field `x ↦ A (x - z)`. -/
theorem linHomotopy_one (v : 𝔼 → 𝔼) (z : 𝔼) (A : 𝔼 →L[ℝ] 𝔼) :
    (fun x => linHomotopy v z A (x, 1)) = fun x => A (x - z) := by
  funext x
  show A (x - z) + (1 - Real.smoothTransition (1 : ℝ)) • (v x - A (x - z)) = A (x - z)
  rw [Real.smoothTransition.one, sub_self, zero_smul, add_zero]

/-! ### The degree of the normalized linear map of the sphere -/

/-- **The degree of `u ↦ A u / |A u|` on `Sⁿ` is `sgn (det A)`**, for `A` a bijective linear map
of `ℝⁿ⁺¹`.  The map is a bijection of the sphere and its sign is `sgn (det A)` at every point
(`signAt_nv0_linear`), so every point is a regular value with a single preimage and the signed
count of preimages is a single sign. -/
theorem deg_nv0_linear (hn : 0 < n) {A : 𝔼 →L[ℝ] 𝔼} (hA : Bijective A) :
    deg (sphOr n) (sphOr n) (fun u : Sph n => nv0 (A u.1)) =
      sgn (LinearMap.det (A : 𝔼 →ₗ[ℝ] 𝔼)) := by
  have := preconnectedSpace hn
  have hune : ∀ u : Sph n, u.1 ≠ 0 := fun u h => by
    have hu := mem_iff_norm.1 u.2
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  have hs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun u : Sph n => nv0 (A u.1)) :=
    contMDiff_nv0_comp (A.contMDiff.comp contMDiff_val) (fun u => A_ne_zero hA (hune u))
  -- the inverse of `A`, used to invert `u ↦ A u / |A u|`
  set Ae := ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.2 hA.1)
    (LinearMap.range_eq_top.2 hA.2) with hAe_def
  have hAe : ∀ x, Ae x = A x := fun x => by
    have hc := ContinuousLinearEquiv.coe_ofBijective A (LinearMap.ker_eq_bot.2 hA.1)
      (LinearMap.range_eq_top.2 hA.2)
    exact congrArg (fun L : 𝔼 →L[ℝ] 𝔼 => L x) hc
  have hAeA : ∀ x, Ae.symm (A x) = x := fun x => by rw [← hAe]; exact Ae.symm_apply_apply x
  have hAAe : ∀ y, A (Ae.symm y) = y := fun y => by rw [← hAe]; exact Ae.apply_symm_apply y
  have hbij : Bijective (fun u : Sph n => nv0 (A u.1)) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun u => nv0 (Ae.symm u.1), fun u => ?_, fun u => ?_⟩
    · show nv0 (Ae.symm (nv0 (A u.1)).1) = u
      rw [nv0_val (A_ne_zero hA (hune u)), normalize, map_smul, hAeA,
        nv0_smul (inv_pos.2 (norm_pos_iff.2 (A_ne_zero hA (hune u)))), nv0_of_mem]
    · show nv0 (A (nv0 (Ae.symm u.1)).1) = u
      have hne' : Ae.symm u.1 ≠ 0 := fun h0 => hune u (by
        have hz := congrArg Ae h0
        rwa [Ae.apply_symm_apply, map_zero] at hz)
      rw [nv0_val hne', normalize, map_smul, hAAe,
        nv0_smul (inv_pos.2 (norm_pos_iff.2 hne')), nv0_of_mem]
  -- constant sign, hence every point is a regular value
  have hsign : ∀ u, signAt (sphOr n) (sphOr n) (fun u : Sph n => nv0 (A u.1)) u =
      sgn (LinearMap.det (A : 𝔼 →ₗ[ℝ] 𝔼)) := fun u => signAt_nv0_linear hA u
  have hσ : sgn (LinearMap.det (A : 𝔼 →ₗ[ℝ] 𝔼)) ≠ 0 :=
    sgn_ne_zero_iff.2 (det_ne_zero_of_bijective hA)
  have hreg : ∀ y : Sph n, IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun u : Sph n => nv0 (A u.1)) y := by
    intro y u _
    exact ((signAt_ne_zero_iff hZ hZ (sphOr n) (sphOr n) (fun u : Sph n => nv0 (A u.1)) u).1
      (by rw [hsign u]; exact hσ)).2
  -- the signed count of preimages of `A y₀ / |A y₀|`
  obtain ⟨y₀⟩ := nonempty_sph (n := n)
  rw [deg_eq hZ hZ (sphOr n) (sphOr n) hs (hreg (nv0 (A y₀.1)))]
  unfold degAt
  have hpre : (fun u : Sph n => nv0 (A u.1)) ⁻¹' {nv0 (A y₀.1)} = {y₀} := by
    ext u
    simp only [mem_preimage, mem_singleton_iff]
    exact ⟨fun hu => hbij.1 hu, fun hu => by rw [hu]⟩
  rw [hpre, finsum_mem_singleton]
  exact hsign y₀

/-! ### Milnor's Lemma 4 -/

/-- **Milnor's Lemma 4 of §6 (p. 36).**  Let `v` be a smooth vector field on `ℝⁿ⁺¹` (`n ≥ 1`)
with a zero at `z` at which the derivative `dv_z` is non-singular.  Then the index of `v` at `z`
is the sign of the determinant of `dv_z`. -/
theorem index_eq_sgn_det (hn : 0 < n) {v : 𝔼 → 𝔼} (hv : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔼) ∞ v) {z : 𝔼}
    (hvz : v z = 0) (hA : Bijective (fderiv ℝ v z)) :
    index v z = sgn (LinearMap.det (fderiv ℝ v z : 𝔼 →ₗ[ℝ] 𝔼)) := by
  obtain ⟨r, hr, hkey⟩ := exists_radius_of_nondegenerate hv hvz hA
  set A := fderiv ℝ v z with hAdef
  have hune : ∀ u : Sph n, u.1 ≠ 0 := fun u h => by
    have hu := mem_iff_norm.1 u.2
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  -- the points of the sphere of radius `r` about `z`
  have hsph : ∀ u : Sph n, dist (z + r • u.1) z ≤ r ∧ z + r • u.1 ≠ z := by
    intro u
    have hu : ‖u.1‖ = 1 := mem_iff_norm.1 u.2
    refine ⟨le_of_eq ?_, fun h => ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs,
        abs_of_pos hr]
    · have hz : r • u.1 = 0 := by simpa using congrArg (· - z) h
      rw [smul_eq_zero] at hz
      rcases hz with h1 | h1
      · exact hr.ne' h1
      · rw [h1, norm_zero] at hu; exact zero_ne_one hu
  -- `z` is an isolated zero (the case `b = 1` of the estimate)
  have hiso : IsolatedZero v z r := by
    refine ⟨hvz, fun x hx hxz => ?_⟩
    have h := hkey x hx hxz 1 zero_le_one le_rfl
    have he : A (x - z) + (1 : ℝ) • (v x - A (x - z)) = v x := by rw [one_smul]; abel
    rwa [he] at h
  rw [index_eq hn hv hr hiso hr le_rfl]
  -- the homotopy to the linear part keeps the `r`-sphere free of zeros
  have hVne : ∀ (t : ℝ) (u : Sph n), linHomotopy v z A (z + r • u.1, t) ≠ 0 := by
    intro t u
    show A (z + r • u.1 - z) +
      (1 - Real.smoothTransition t) • (v (z + r • u.1) - A (z + r • u.1 - z)) ≠ 0
    refine hkey _ (hsph u).1 (hsph u).2 _ ?_ ?_
    · have := Real.smoothTransition.le_one t; linarith
    · have := Real.smoothTransition.nonneg t; linarith
  have hhom := indexAt_eq_of_homotopy hn (contMDiff_linHomotopy hv z A) hVne
  rw [linHomotopy_zero, linHomotopy_one] at hhom
  rw [hhom]
  -- the sphere map of the linear field is `u ↦ A u / |A u|`
  have hlin : sphMap (fun x => A (x - z)) z r = fun u : Sph n => nv0 (A u.1) := by
    funext u
    have hne : (fun x : 𝔼 => A (x - z)) (z + r • u.1) ≠ 0 := by
      show A (z + r • u.1 - z) ≠ 0
      rw [add_sub_cancel_left]
      exact A_ne_zero hA (smul_ne_zero hr.ne' (hune u))
    rw [sphMap_eq_nv0 hne]
    show nv0 (A (z + r • u.1 - z)) = nv0 (A u.1)
    rw [add_sub_cancel_left, map_smul, nv0_smul hr]
  unfold indexAt
  rw [hlin]
  exact deg_nv0_linear hn hA

/-- **Milnor's Lemma 4 in his own words** (§6, p. 36): the index of `v` at a non-degenerate zero
`z` is either `+1` or `-1` according as the determinant of `dv_z` is positive or negative. -/
theorem index_nondegenerate (hn : 0 < n) {v : 𝔼 → 𝔼} (hv : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔼) ∞ v)
    {z : 𝔼} (hvz : v z = 0) (hA : Bijective (fderiv ℝ v z)) :
    (0 < LinearMap.det (fderiv ℝ v z : 𝔼 →ₗ[ℝ] 𝔼) → index v z = 1) ∧
      (LinearMap.det (fderiv ℝ v z : 𝔼 →ₗ[ℝ] 𝔼) < 0 → index v z = -1) := by
  refine ⟨fun hdet => ?_, fun hdet => ?_⟩
  · rw [index_eq_sgn_det hn hv hvz hA, sgn_pos hdet]
  · rw [index_eq_sgn_det hn hv hvz hA, sgn_neg hdet]

end Sphere

end Milnor
