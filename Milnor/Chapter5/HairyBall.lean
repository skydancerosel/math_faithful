import Milnor.Chapter5.LevelOrient
import Milnor.Chapter5.Degree
import Milnor.Chapter2.Corestrict

/-!
# The sphere, the antipodal map, and the hairy ball theorem (Milnor pp. 29–30)

`Sph n` is the unit sphere in `ℝⁿ⁺¹` (Euclidean space), as the level set `{⟪x,x⟫ - 1 = 0}` with
the submanifold structure of Chapter 2 and the level-set orientation of `LevelOrient`.

* The antipodal map `x ↦ -x` has degree `(-1)ⁿ⁺¹`.
* **Hairy ball theorem** (Milnor, Theorem on p. 30, "only if" direction): for `n` even, every
  smooth tangent vector field on `Sⁿ` vanishes somewhere.  Proof: a nonvanishing field `v` gives
  the homotopy `(x, t) ↦ cos(πt) x + sin(πt) v(x)/|v(x)|` from the identity to the antipodal map,
  so by Theorem A their degrees `1` and `(-1)ⁿ⁺¹ = -1` would agree.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Sphere

variable {n : ℕ}

/-- The defining function of the unit sphere. -/
def sphG (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ := ⟪x, x⟫ - 1

theorem contDiff_sphG : ContDiff ℝ ∞ (sphG (n := n)) :=
  (contDiff_id.inner (𝕜 := ℝ) contDiff_id).sub contDiff_const

theorem contMDiff_sphG :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) ∞ (sphG (n := n)) :=
  contMDiff_iff_contDiff.2 contDiff_sphG

theorem fderiv_sphG (x v : EuclideanSpace ℝ (Fin (n + 1))) :
    fderiv ℝ sphG x v = 2 * ⟪x, v⟫ := by
  have h := fderiv_inner_apply (𝕜 := ℝ) (f := fun y : EuclideanSpace ℝ (Fin (n + 1)) => y)
    (g := fun y : EuclideanSpace ℝ (Fin (n + 1)) => y) (x := x) differentiableAt_id
    differentiableAt_id v
  simp only [fderiv_fun_id, ContinuousLinearMap.id_apply] at h
  show fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => ⟪y, y⟫ - 1) x v = _
  rw [fderiv_sub_const, h, real_inner_comm]
  ring

theorem inner_self_eq_one_of_mem {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∈ (sphG (n := n)) ⁻¹' {0}) : ⟪x, x⟫ = 1 := by
  have : sphG x = 0 := hx
  unfold sphG at this
  linarith

theorem mem_iff_norm {x : EuclideanSpace ℝ (Fin (n + 1))} :
    x ∈ (sphG (n := n)) ⁻¹' {0} ↔ ‖x‖ = 1 := by
  simp only [mem_preimage, mem_singleton_iff, sphG, sub_eq_zero, real_inner_self_eq_norm_sq]
  exact pow_eq_one_iff_of_nonneg (norm_nonneg x) (by norm_num)

theorem preimage_eq_sphere :
    ((sphG (n := n)) ⁻¹' {0} : Set (EuclideanSpace ℝ (Fin (n + 1)))) = Metric.sphere 0 1 := by
  ext x
  rw [mem_iff_norm, mem_sphere_zero_iff_norm]

theorem isRegularValue_sphG :
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (sphG (n := n)) 0 := by
  intro x hx
  have hx1 : ⟪x, x⟫ = 1 := inner_self_eq_one_of_mem hx
  show Function.Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) sphG x)
  intro t
  refine ⟨(t / 2) • x, ?_⟩
  have hm : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) sphG x = fderiv ℝ sphG x :=
    mfderiv_eq_fderiv
  rw [hm, map_smul, fderiv_sphG, hx1]
  simp

theorem hE : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1 := finrank_euclideanSpace_fin
theorem hZ : finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin

/-- The unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`, as a set. -/
abbrev Sph (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) := (sphG (n := n)) ⁻¹' {0}

/-- The submanifold structure of the sphere (Chapter 2, Lemma 1). -/
theorem sphS (n : ℕ) : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    (EuclideanSpace ℝ (Fin n)) ℝ (Sph n) :=
  isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ) contMDiff_sphG
    isRegularValue_sphG

instance : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Sph n) := (sphS n).chartedSpace

instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Sph n) := (sphS n).isManifold

instance : CompactSpace (Sph n) := by
  rw [← isCompact_iff_compactSpace]
  show IsCompact ((sphG (n := n)) ⁻¹' {0})
  rw [preimage_eq_sphere]
  exact isCompact_sphere 0 1

theorem preconnectedSpace (hn : 0 < n) : PreconnectedSpace (Sph n) := by
  rw [← isPreconnected_iff_preconnectedSpace]
  show IsPreconnected ((sphG (n := n)) ⁻¹' {0})
  rw [preimage_eq_sphere]
  refine isPreconnected_sphere ?_ 0 1
  rw [← finrank_eq_rank, hE]
  exact_mod_cast (by omega : 1 < n + 1)

theorem contMDiff_val :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) :=
  (sphS n).contMDiff_val

/-- The orientation of the sphere: the level-set orientation for the reference orientation of
`ℝⁿ⁺¹`. -/
def sphOr (n : ℕ) : Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (Sph n) n :=
  levelOrient hE hZ (finBasisOfFinrankEq ℝ _ hE).orientation contMDiff_sphG isRegularValue_sphG

theorem sphOr_or (q : Sph n) : (sphOr n).or q =
    contractOr hZ (finBasisOfFinrankEq ℝ _ hE).orientation (outward hE sphG q.1)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → EuclideanSpace ℝ (Fin (n + 1))) q) := rfl

/-! ### The antipodal map -/

theorem neg_mem {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ Sph n) : -x ∈ Sph n := by
  rw [mem_iff_norm] at hx ⊢
  rwa [norm_neg]

/-- The antipodal map of the sphere. -/
def antip (q : Sph n) : Sph n := ⟨-q.1, neg_mem q.2⟩

theorem antip_antip (q : Sph n) : antip (antip q) = q := Subtype.ext (neg_neg _)

theorem contMDiff_antip :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (antip (n := n)) :=
  (sphS n).contMDiff_codRestrict (F := fun q : Sph n => -q.1) contMDiff_val.neg
    (fun q => neg_mem q.2)

theorem outward_neg (x : EuclideanSpace ℝ (Fin (n + 1))) :
    outward hE sphG (-x) = -outward hE sphG x := by
  simp only [outward, fderiv_sphG, inner_neg_left, mul_neg, neg_smul, Finset.sum_neg_distrib,
    neg_neg]

/-- The chain rule `dι ∘ d(antip) = -dι`. -/
theorem mfd_val_comp_antip (q : Sph n) :
    (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → _) (antip q)).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) antip q) =
      -mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → _) q := by
  have h1 := (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) (contMDiff_val.mdifferentiableAt (x := antip q)
    (by simp))).comp q (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (contMDiff_antip.mdifferentiableAt (by simp)))
  have h2 := (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) (contMDiff_val.mdifferentiableAt (x := q)
    (by simp))).neg
  have h3 : (Subtype.val ∘ antip : Sph n → EuclideanSpace ℝ (Fin (n + 1))) = -Subtype.val := by
    funext q; rfl
  rw [h3] at h1
  exact hasMFDerivAt_unique h1 h2

/-- The sign of the antipodal map is `(-1)ⁿ⁺¹` everywhere. -/
theorem signAt_antip (q : Sph n) : signAt (sphOr n) (sphOr n) antip q = (-1) ^ (n + 1) := by
  set e := finBasisOfFinrankEq ℝ (EuclideanSpace ℝ (Fin (n + 1))) hE with he
  set a₀ := e.orientation with ha₀
  set om : EuclideanSpace ℝ (Fin (n + 1)) [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ := orEpsB e a₀ • e.det with hom_def
  have hom : om ≠ 0 := orEpsB_smul_det_ne_zero e a₀
  have hom_ray : rayOfNeZero ℝ om hom = a₀ := rayOfNeZero_orEpsB_det e a₀
  set u₀ := finBasisOfFinrankEq ℝ (EuclideanSpace ℝ (Fin n)) hZ with hu₀
  -- the facts about `dι` at any point
  have hreg : ∀ p : Sph n, fderiv ℝ sphG p.1 ≠ 0 := fun p h => by
    have := fderiv_sphG p.1 p.1
    rw [h, inner_self_eq_one_of_mem p.2] at this
    simp at this
  have hker : ∀ (p : Sph n) (v : EuclideanSpace ℝ (Fin (n + 1))),
      (∃ w, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → _) p w = v) ↔ fderiv ℝ sphG p.1 v = 0 := fun p v => by
    rw [← mfderiv_eq_fderiv]
    exact mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) contMDiff_sphG isRegularValue_sphG p v
  have hdgι : ∀ (p : Sph n) (w : EuclideanSpace ℝ (Fin n)), fderiv ℝ sphG p.1
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → _) p w) = 0 := fun p w => (hker p _).1 ⟨w, rfl⟩
  have hιinj : ∀ p : Sph n, Function.Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (Subtype.val : Sph n → _) p) := by
    intro p
    set T := mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : Sph n → _) p with hT
    have hrange : LinearMap.range (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1))) =
        LinearMap.ker (fderiv ℝ sphG p.1 : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ) := by
      ext v
      simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      exact hker p v
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    have h2 := LinearMap.finrank_range_add_finrank_ker
      (fderiv ℝ sphG p.1 : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ)
    have h3 : LinearMap.range (fderiv ℝ sphG p.1 : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ) = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro t
      refine ⟨(t / 2) • p.1, ?_⟩
      simp only [ContinuousLinearMap.coe_coe, map_smul, fderiv_sphG, inner_self_eq_one_of_mem p.2,
        smul_eq_mul]
      ring
    rw [h3, finrank_top, Module.finrank_self, hE] at h2
    rw [hrange, hZ] at h1
    have h4 : finrank ℝ (LinearMap.ker
        (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))) = 0 := by omega
    rw [Submodule.finrank_eq_zero] at h4
    exact LinearMap.ker_eq_bot.1 h4
  -- representatives
  have hrep : ∀ p : Sph n, contractForm om (outward hE sphG p.1)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → _) p) u₀ ≠ 0 := fun p =>
    contractForm_basis_ne_zero hE hZ hom (hιinj p) (hdgι p) (fderiv_outward_neg hE (hreg p)).ne u₀
  have hrep' : ∀ p : Sph n, contractForm om (outward hE sphG p.1)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → _) p) ≠ 0 := fun p h => hrep p (by rw [h]; rfl)
  unfold signAt
  rw [sphOr_or, sphOr_or, ← rayOfNeZero_contractForm hZ hom hom_ray _ _ (hrep' q),
    ← rayOfNeZero_contractForm hZ hom hom_ray _ _ (hrep' (antip q))]
  rw [orSign_eq_sgn_mul hZ _ _ rfl rfl _ (hrep q)]
  -- evaluate the pulled-back form
  have key : ((contractForm om (outward hE sphG (antip q).1)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (Subtype.val : Sph n → _) (antip q))).compLinearMap
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) antip q).toLinearMap) u₀ =
      (-1) ^ (n + 1) * contractForm om (outward hE sphG q.1)
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
          (Subtype.val : Sph n → _) q) u₀ := by
    rw [contractForm_comp, mfd_val_comp_antip]
    have h1 : outward hE sphG (antip q).1 = -outward hE sphG q.1 := outward_neg q.1
    rw [h1, contractForm_apply, contractForm_apply]
    set T := mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (Subtype.val : Sph n → _) q with hT
    have h2 : Matrix.vecCons (-outward hE sphG q.1) (fun i => (-T) (u₀ i)) =
        fun i => (-1 : ℝ) • Matrix.vecCons (outward hE sphG q.1) (fun i => T (u₀ i)) i := by
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp
    rw [h2]
    have h3 := MultilinearMap.map_smul_univ (om : MultilinearMap ℝ (fun _ : Fin (n + 1) => _) ℝ)
      (fun _ => (-1 : ℝ)) (Matrix.vecCons (outward hE sphG q.1) (fun i => T (u₀ i)))
    simp only [AlternatingMap.coe_multilinearMap, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at h3
    exact h3
  rw [key, mul_assoc, sgn_mul, sgn_mul_self (hrep q), mul_one]
  rcases Nat.even_or_odd (n + 1) with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, sgn_one]
  · rw [h.neg_one_pow, h.neg_one_pow, sgn_neg (by norm_num)]

/-- All points are regular values of the antipodal map. -/
theorem isRegularValue_antip (y : Sph n) :
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) antip y := by
  intro q _
  have h := signAt_antip q
  have hne : signAt (sphOr n) (sphOr n) antip q ≠ 0 := by
    rw [h]; exact pow_ne_zero _ (by norm_num)
  exact ((signAt_ne_zero_iff hZ hZ _ _ _ _).1 hne).2

instance nonempty_sph : Nonempty (Sph n) :=
  ⟨⟨EuclideanSpace.single 0 1, by rw [mem_iff_norm]; simp⟩⟩

/-- **The degree of the antipodal map is `(-1)ⁿ⁺¹`** (Milnor p. 29). -/
theorem deg_antip (hn : 0 < n) : deg (sphOr n) (sphOr n) (antip (n := n)) = (-1) ^ (n + 1) := by
  haveI := preconnectedSpace hn
  obtain ⟨y⟩ := nonempty_sph (n := n)
  rw [deg_eq hZ hZ (sphOr n) (sphOr n) contMDiff_antip (isRegularValue_antip y)]
  unfold degAt
  have hpre : antip ⁻¹' {y} = {antip y} := by
    ext q
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h; rw [← h, antip_antip]
    · intro h; rw [h, antip_antip]
  rw [hpre, finsum_mem_singleton, signAt_antip]

/-! ### The hairy ball theorem -/

/-- **Hairy ball theorem** (Milnor p. 30): for `n` even, every smooth tangent vector field on
`Sⁿ` has a zero. -/
theorem hairy_ball (hn : Even n) (hn0 : 0 < n) (v : Sph n → EuclideanSpace ℝ (Fin (n + 1)))
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v)
    (htang : ∀ q, ⟪q.1, v q⟫ = 0) : ∃ q, v q = 0 := by
  by_contra hcon
  push_neg at hcon
  haveI := preconnectedSpace hn0
  -- the normalized field
  set w : Sph n → EuclideanSpace ℝ (Fin (n + 1)) := fun q => ‖v q‖⁻¹ • v q with hw
  have hw_smooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ w := by
    intro q
    have h1 : ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℝ (Fin (n + 1)) => ‖u‖⁻¹ • u) (v q) :=
      ((contDiffAt_norm ℝ (hcon q)).inv (norm_ne_zero_iff.2 (hcon q))).smul contDiffAt_id
    exact h1.contMDiffAt.comp q hv.contMDiffAt
  have hw_norm : ∀ q, ‖w q‖ = 1 := fun q => by
    simp only [w, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hcon q))
  have hw_tang : ∀ q, ⟪q.1, w q⟫ = 0 := fun q => by
    simp only [w, inner_smul_right, htang, mul_zero]
  have hw_tang' : ∀ q, ⟪w q, q.1⟫ = 0 := fun q => by rw [real_inner_comm]; exact hw_tang q
  -- the rotation homotopy
  set F : Sph n × ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun p => Real.cos (Real.pi * p.2) • p.1.1 + Real.sin (Real.pi * p.2) • w p.1 with hF
  have hFS : ∀ p, F p ∈ Sph n := by
    intro p
    show sphG (F p) = 0
    unfold sphG
    simp only [F, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, hw_norm, hw_tang, hw_tang', conj_trivial]
    have h1 : ‖p.1.1‖ = 1 := mem_iff_norm.1 p.1.2
    rw [h1]
    linear_combination Real.cos_sq_add_sin_sq (Real.pi * p.2)
  have hFsmooth : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ F := by
    have hc : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : Sph n × ℝ => Real.cos (Real.pi * p.2)) :=
      (Real.contDiff_cos (n := ∞)).contMDiff.comp (contMDiff_const.mul contMDiff_snd)
    have hs : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : Sph n × ℝ => Real.sin (Real.pi * p.2)) :=
      (Real.contDiff_sin (n := ∞)).contMDiff.comp (contMDiff_const.mul contMDiff_snd)
    exact (hc.smul (contMDiff_val.comp contMDiff_fst)).add (hs.smul (hw_smooth.comp contMDiff_fst))
  set Hm : Sph n × ℝ → Sph n := fun p => ⟨F p, hFS p⟩ with hHm
  have hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Hm :=
    (sphS n).contMDiff_codRestrict hFsmooth hFS
  have hH0 : (fun q => Hm (q, 0)) = id := by
    funext q; apply Subtype.ext
    simp [Hm, F]
  have hH1 : (fun q => Hm (q, 1)) = antip := by
    funext q; apply Subtype.ext
    simp [Hm, F, antip]
  have hdeg := deg_eq_of_homotopy hZ hZ (sphOr n) (sphOr n) hH
  rw [hH0, hH1, deg_id hZ (sphOr n), deg_antip hn0] at hdeg
  have : Odd (n + 1) := hn.add_one
  rw [this.neg_one_pow] at hdeg
  omega

/-! ### The converse: for odd `n` there is a nonvanishing tangent field -/

/-- For `n` odd, pairing the coordinates `(x_a, x_b) ↦ (x_b, -x_a)` gives a smooth nonvanishing
tangent vector field on `Sⁿ` (Milnor p. 30). -/
theorem exists_nonvanishing_field (hn : Odd n) :
    ∃ v : Sph n → EuclideanSpace ℝ (Fin (n + 1)),
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞ v ∧
      (∀ q, ⟪q.1, v q⟫ = 0) ∧ ∀ q, v q ≠ 0 := by
  obtain ⟨m, hm⟩ := hn
  have h : n + 1 = (m + 1) + (m + 1) := by omega
  let e : Fin (n + 1) ≃ Fin (m + 1) ⊕ Fin (m + 1) := (finCongr h).trans finSumFinEquiv.symm
  -- the coordinate map
  let Jc : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ContinuousLinearMap.pi fun i => Sum.elim
      (fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (e.symm (Sum.inr j)))
      (fun j => -ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (e.symm (Sum.inl j)))
      (e i)
  let J : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    ((EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm : (Fin (n + 1) → ℝ) →L[ℝ] _).comp
      (Jc.comp (EuclideanSpace.equiv (Fin (n + 1)) ℝ : _ →L[ℝ] (Fin (n + 1) → ℝ)))
  have hJ : ∀ (x : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin (n + 1)), J x i =
      Sum.elim (fun j => x (e.symm (Sum.inr j))) (fun j => -x (e.symm (Sum.inl j))) (e i) := by
    intro x i
    simp only [J, Jc, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    show (ContinuousLinearMap.pi _ (EuclideanSpace.equiv (Fin (n + 1)) ℝ x)) i = _
    rw [ContinuousLinearMap.pi_apply]
    rcases e i with j | j <;> simp
  -- sums over `Fin (n + 1)` split along `e`
  have hsum : ∀ f : Fin (n + 1) → ℝ, ∑ i, f i =
      ∑ j : Fin (m + 1), f (e.symm (Sum.inl j)) + ∑ j : Fin (m + 1), f (e.symm (Sum.inr j)) := by
    intro f
    rw [← Fintype.sum_equiv e.symm (fun s => f (e.symm s)) f (fun _ => rfl), Fintype.sum_sum_type]
  have hinner : ∀ x y : EuclideanSpace ℝ (Fin (n + 1)), ⟪x, y⟫ = ∑ i, x i * y i := by
    intro x y
    simp [PiLp.inner_apply, mul_comm]
  refine ⟨fun q => J q.1, J.contDiff.contMDiff.comp contMDiff_val, fun q => ?_, fun q => ?_⟩
  · rw [hinner, hsum]
    simp only [hJ, Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    ring
  · intro hzero
    change J q.1 = 0 at hzero
    have h1 : ⟪J q.1, J q.1⟫ = ⟪q.1, q.1⟫ := by
      rw [hinner, hinner, hsum, hsum (fun i => q.1 i * q.1 i)]
      simp only [hJ, Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hzero, inner_zero_left, inner_self_eq_one_of_mem q.2] at h1
    exact zero_ne_one h1

end Sphere

end Milnor
