import Milnor.Chapter5.Orient
import Milnor.Chapter2.WithBoundary

/-!
# The induced orientation of a level set in a vector space

Let `E` be an oriented finite-dimensional space of dimension `n + 1`, `g : E → ℝ` smooth with
`0` a regular value, and `S = g⁻¹(0)` the level set, a submanifold modelled on a space `Z` of
dimension `n` (Chapter 2, Lemma 1).  At `q ∈ S` the *outward* vector is `-∇g(q)` (relative to a
basis), and the orientation of `T_qS` is obtained by contracting the top form of `E` with it:
a basis `z` of `T_qS` is positive iff `(outward, z)` is a positive basis of `E`.  This is Milnor's
boundary orientation of `∂X` for `X = {g ≥ 0}` (p. 26).  We prove it is continuous in the sense
of `Orient`.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] {n : ℕ}

/-! ### Contraction of a top form -/

/-- The `n`-form `(z₁, …, zₙ) ↦ om (v, T z₁, …, T zₙ)`. -/
def contractForm (om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ) (v : E) (T : Z →L[ℝ] E) :
    Z [⋀^Fin n]→ₗ[ℝ] ℝ :=
  (om.curryLeft v).compLinearMap T.toLinearMap

theorem contractForm_apply (om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ) (v : E) (T : Z →L[ℝ] E) (u : Fin n → Z) :
    contractForm om v T u = om (Matrix.vecCons v fun i => T (u i)) := rfl

theorem contractForm_smul (c : ℝ) (om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ) (v : E) (T : Z →L[ℝ] E) :
    contractForm (c • om) v T = c • contractForm om v T := by
  ext u; simp [contractForm_apply]

theorem contractForm_comp (om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ) (v : E) (T : Z →L[ℝ] E)
    {Z' : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z'] (D : Z' →L[ℝ] Z) :
    (contractForm om v T).compLinearMap D.toLinearMap = contractForm om v (T.comp D) := by
  ext u; rfl

/-- If `T` is injective with range in a hyperplane `ker λ` and `λ v ≠ 0`, the contracted form is
nonzero on every basis of `Z` (`dim E = n + 1`, `dim Z = n`). -/
theorem contractForm_basis_ne_zero (hE : finrank ℝ E = n + 1) (hZ : finrank ℝ Z = n)
    {om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ} (hom : om ≠ 0) {v : E} {T : Z →L[ℝ] E} {lam : E →L[ℝ] ℝ}
    (hinj : Function.Injective T) (hT : ∀ z, lam (T z) = 0) (hv : lam v ≠ 0)
    (u : Basis (Fin n) ℝ Z) : contractForm om v T u ≠ 0 := by
  rw [contractForm_apply]
  -- the family `(v, T u₁, …, T uₙ)` is a basis of `E`
  have hli : LinearIndependent ℝ (Matrix.vecCons v fun i => T (u i)) := by
    rw [Matrix.vecCons, linearIndependent_finCons]
    refine ⟨u.linearIndependent.map' T.toLinearMap (LinearMap.ker_eq_bot_of_injective hinj), ?_⟩
    intro hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
    have h1 : lam v = 0 := by
      rw [← hc, map_sum]
      simp [hT]
    exact hv h1
  let b : Basis (Fin (n + 1)) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hE])
  have hb : ⇑b = Matrix.vecCons v fun i => T (u i) := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  rw [← hb]
  exact ne_zero_of_basis hom b

open Classical in
/-- The orientation of `Z` obtained by contracting a representative of `a` with `v` along `T`
(junk value if the contraction vanishes). -/
def contractOr (hZ : finrank ℝ Z = n) (a : Orientation ℝ E (Fin (n + 1))) (v : E)
    (T : Z →L[ℝ] E) : Orientation ℝ Z (Fin n) :=
  if h : contractForm a.someVector v T ≠ 0 then rayOfNeZero ℝ _ h
  else (finBasisOfFinrankEq ℝ Z hZ).orientation

/-- Any positive representative of `a` represents `contractOr a v T` after contraction. -/
theorem rayOfNeZero_contractForm (hZ : finrank ℝ Z = n) {a : Orientation ℝ E (Fin (n + 1))}
    {om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ} (hom : om ≠ 0) (ha : rayOfNeZero ℝ om hom = a) (v : E)
    (T : Z →L[ℝ] E) (h : contractForm om v T ≠ 0) :
    rayOfNeZero ℝ (contractForm om v T) h = contractOr hZ a v T := by
  have h1 : SameRay ℝ om a.someVector :=
    (ray_eq_iff hom a.someVector_ne_zero).1 (by rw [ha, Module.Ray.someVector_ray])
  obtain ⟨r, hr, hrom⟩ := h1.exists_pos_left hom a.someVector_ne_zero
  have h2 : contractForm a.someVector v T = r • contractForm om v T := by
    rw [← hrom, contractForm_smul]
  have h3 : contractForm a.someVector v T ≠ 0 := by
    rw [h2]; exact smul_ne_zero hr.ne' h
  unfold contractOr
  rw [dif_pos h3]
  show rayOfNeZero ℝ _ _ = rayOfNeZero ℝ _ h3
  rw [ray_eq_iff, h2]
  exact SameRay.sameRay_pos_smul_right (contractForm om v T) hr

/-! ### The derivative of a chart at its centre -/

/-- The derivative of `extChartAt I x` at `x` is the identity.  The model need not be
boundaryless: read in the chart at `x`, the chart at `x` is the identity on the range of the
model, which is where the derivative within that range is taken. -/
theorem hasMFDerivAt_extChartAt_self {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I x) x (ContinuousLinearMap.id ℝ E :) := by
  refine ⟨continuousAt_extChartAt x, ?_⟩
  refine (hasFDerivWithinAt_id (extChartAt I x x) (range I)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    exact writtenInExtChartAt_extChartAt (I := I) hz
  · exact writtenInExtChartAt_extChartAt (I := I) (mem_extChartAt_target x)

theorem mfd_extChartAt_self {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (x : M) :
    mfd I 𝓘(ℝ, E) (extChartAt I x) x = ContinuousLinearMap.id ℝ E :=
  HasMFDerivAt.mfd_eq (hasMFDerivAt_extChartAt_self x)

/-! ### The outward vector -/

/-- A vector on which `dg` is negative: `-∑ᵢ dg(eᵢ) eᵢ` for a basis `e`. -/
def outward (hE : finrank ℝ E = n + 1) (g : E → ℝ) (x : E) : E :=
  -∑ i, fderiv ℝ g x (finBasisOfFinrankEq ℝ E hE i) • finBasisOfFinrankEq ℝ E hE i

theorem fderiv_outward (hE : finrank ℝ E = n + 1) (g : E → ℝ) (x : E) :
    fderiv ℝ g x (outward hE g x) =
      -∑ i, fderiv ℝ g x (finBasisOfFinrankEq ℝ E hE i) ^ 2 := by
  simp only [outward, map_neg, map_sum, map_smul, smul_eq_mul, sq]

theorem fderiv_outward_neg (hE : finrank ℝ E = n + 1) {g : E → ℝ} {x : E}
    (hx : fderiv ℝ g x ≠ 0) : fderiv ℝ g x (outward hE g x) < 0 := by
  rw [fderiv_outward, neg_lt_zero]
  set e := finBasisOfFinrankEq ℝ E hE
  have hne : ∃ i, fderiv ℝ g x (e i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine hx (ContinuousLinearMap.coe_injective (e.ext fun i => ?_))
    simp [hcon i]
  obtain ⟨i, hi⟩ := hne
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by positivity⟩

theorem continuous_outward (hE : finrank ℝ E = n + 1) {g : E → ℝ} (hg : ContDiff ℝ ∞ g) :
    Continuous (outward hE g) := by
  unfold outward
  refine continuous_neg.comp (continuous_finsetSum _ fun i _ => ?_)
  exact ((hg.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const

/-! ### The orientation of the level set -/

section level

variable (hE : finrank ℝ E = n + 1) (hZ : finrank ℝ Z = n) (a₀ : Orientation ℝ E (Fin (n + 1)))
  {g : E → ℝ} (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (h0 : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g 0)

include hE hZ in
theorem finrank_Z_add : finrank ℝ Z + finrank ℝ ℝ = finrank ℝ E := by
  rw [hZ, Module.finrank_self, hE]

include hE hZ hg h0 in
/-- **Continuity of the level-set orientation.** -/
theorem levelOrient_cont :
    letI hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0
    letI := hS.chartedSpace
    ∀ q₀ : g ⁻¹' {0}, ∀ᶠ q in 𝓝 q₀,
      orSign (contractOr hZ a₀ (outward hE g q.1)
          (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q))
        (contractOr hZ a₀ (outward hE g q₀.1)
          (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q₀))
        (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) (extChartAt 𝓘(ℝ, Z) q₀) q) = 1 := by
  have hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0
  letI := hS.chartedSpace
  haveI := hS.isManifold
  intro q₀
  have hgd : ContDiff ℝ ∞ g := contMDiff_iff_contDiff.1 hg
  have hmfd_g : ∀ x, mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g x = fderiv ℝ g x := fun x => mfderiv_eq_fderiv
  -- `dg ≠ 0` on the level set
  have hreg : ∀ q : g ⁻¹' {0}, fderiv ℝ g q.1 ≠ 0 := fun q hz => by
    have hs : Function.Surjective (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g q.1) := h0 q.1 q.2
    obtain ⟨v, hv⟩ := hs 1
    rw [hmfd_g, hz] at hv
    simp at hv
  -- Lemma 2: the range of `dι` is the kernel of `dg`
  have hker : ∀ (q : g ⁻¹' {0}) (v : E),
      (∃ w, mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q w = v) ↔ fderiv ℝ g q.1 v = 0 :=
    fun q v => by
      rw [← hmfd_g]
      exact mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) hg h0 q v
  have hdgι : ∀ (q : g ⁻¹' {0}) (w : Z),
      fderiv ℝ g q.1 (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q w) = 0 :=
    fun q w => (hker q _).1 ⟨w, rfl⟩
  have hιinj : ∀ q : g ⁻¹' {0}, Function.Injective (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q) := by
    intro q
    have hrange : LinearMap.range (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q : Z →ₗ[ℝ] E) =
        LinearMap.ker (fderiv ℝ g q.1 : E →ₗ[ℝ] ℝ) := by
      ext v
      simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      exact hker q v
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q : Z →ₗ[ℝ] E)
    have h2 := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ g q.1 : E →ₗ[ℝ] ℝ)
    have h3 : LinearMap.range (fderiv ℝ g q.1 : E →ₗ[ℝ] ℝ) = ⊤ := by
      rw [LinearMap.range_eq_top]
      have hex : ∃ v, fderiv ℝ g q.1 v ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hreg q (ContinuousLinearMap.ext hcon)
      obtain ⟨v, hv⟩ := hex
      intro t
      exact ⟨(t / fderiv ℝ g q.1 v) • v, by simp [div_mul_cancel₀ _ hv]⟩
    rw [h3, finrank_top, Module.finrank_self, hE] at h2
    rw [hrange, hZ] at h1
    have h4 : finrank ℝ (LinearMap.ker
        (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q : Z →ₗ[ℝ] E)) = 0 := by omega
    rw [Submodule.finrank_eq_zero] at h4
    exact LinearMap.ker_eq_bot.1 h4
  -- the representative form of the orientation of `E`
  set e := finBasisOfFinrankEq ℝ E hE with he
  set om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ := orEpsB e a₀ • e.det with hom_def
  have hom : om ≠ 0 := orEpsB_smul_det_ne_zero e a₀
  have hom_ray : rayOfNeZero ℝ om hom = a₀ := rayOfNeZero_orEpsB_det e a₀
  set u₀ := finBasisOfFinrankEq ℝ Z hZ with hu₀
  -- the representative of the orientation at `q`
  have hrep : ∀ q : g ⁻¹' {0}, contractForm om (outward hE g q.1)
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q) u₀ ≠ 0 := fun q =>
    contractForm_basis_ne_zero hE hZ hom (hιinj q) (hdgι q)
      (fderiv_outward_neg hE (hreg q)).ne u₀
  have hrep' : ∀ q : g ⁻¹' {0}, contractForm om (outward hE g q.1)
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q) ≠ 0 := fun q h => hrep q (by rw [h]; rfl)
  -- the chart at `q₀` and the parametrization `ψ = val ∘ c₀⁻¹`
  set c₀ := extChartAt 𝓘(ℝ, Z) q₀ with hc₀
  set ψ : Z → E := fun z => (c₀.symm z).1 with hψ_def
  have hψ : ContDiffOn ℝ ∞ ψ c₀.target := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hS.contMDiff_val.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, Z)) q₀)
  have hψd : ContinuousOn (fderiv ℝ ψ) c₀.target :=
    hψ.continuousOn_fderiv_of_isOpen (isOpen_extChartAt_target q₀) (by simp)
  -- chain rule: `dι_q = dψ_{c₀ q} ∘ dc₀_q`
  have hchain : ∀ q ∈ c₀.source, mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q =
      (fderiv ℝ ψ (c₀ q)).comp (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) c₀ q) := by
    intro q hq
    have hψq : HasMFDerivAt 𝓘(ℝ, Z) 𝓘(ℝ, E) ψ (c₀ q) (fderiv ℝ ψ (c₀ q)) :=
      ((hψ.contDiffAt ((isOpen_extChartAt_target q₀).mem_nhds (c₀.map_source hq))).differentiableAt
        (by simp)).hasFDerivAt.hasMFDerivAt
    have hc := hasMFDerivAt_mfd (I := 𝓘(ℝ, Z)) (J := 𝓘(ℝ, Z)) ((contMDiffAt_extChartAt'
      (I := 𝓘(ℝ, Z)) (n := ∞) (x := q₀)
      (by rwa [← extChartAt_source 𝓘(ℝ, Z)] : q ∈ (chartAt Z q₀).source)).mdifferentiableAt
        (by simp))
    have h1 := hψq.comp q hc
    have h2 : (Subtype.val : g ⁻¹' {0} → E) =ᶠ[𝓝 q] (ψ ∘ c₀) := by
      filter_upwards [(isOpen_extChartAt_source q₀).mem_nhds hq] with z hz
      simp only [Function.comp, ψ]
      rw [c₀.left_inv hz]
    exact HasMFDerivAt.mfd_eq (h1.congr_of_eventuallyEq h2)
  -- the family of `n`-forms `Λ q = contractForm om (outward q) (dψ_{c₀ q})`
  set Λ : g ⁻¹' {0} → (Z [⋀^Fin n]→ₗ[ℝ] ℝ) := fun q =>
    contractForm om (outward hE g q.1) (fderiv ℝ ψ (c₀ q)) with hΛ
  have hrepΛ : ∀ q ∈ c₀.source, contractForm om (outward hE g q.1)
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q) =
      (Λ q).compLinearMap (mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) c₀ q).toLinearMap := by
    intro q hq
    rw [hchain q hq]
    simp only [Λ]
    rw [contractForm_comp]
  have hq₀src : q₀ ∈ c₀.source := mem_extChartAt_source q₀
  have hΛ₀ : Λ q₀ = contractForm om (outward hE g q₀.1)
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q₀) := by
    rw [hrepΛ q₀ hq₀src, mfd_extChartAt_self]
    simp only [ContinuousLinearMap.coe_id, AlternatingMap.compLinearMap_id]
  have hΛ₀u : Λ q₀ u₀ ≠ 0 := by rw [hΛ₀]; exact hrep q₀
  have hΛ₀ne : Λ q₀ ≠ 0 := fun h => hΛ₀u (by rw [h]; rfl)
  -- continuity of `q ↦ Λ q u₀`
  have hLcont : ContinuousOn (fun q : g ⁻¹' {0} => Λ q u₀) c₀.source := by
    have hout : Continuous (fun q : g ⁻¹' {0} => outward hE g q.1) :=
      (continuous_outward hE hgd).comp continuous_subtype_val
    have hfd : ContinuousOn (fun q : g ⁻¹' {0} => fderiv ℝ ψ (c₀ q)) c₀.source :=
      hψd.comp (continuousOn_extChartAt q₀) (fun q hq => c₀.map_source hq)
    simp only [Λ, contractForm_apply, om, AlternatingMap.smul_apply, smul_eq_mul, Basis.det_apply]
    have houter : Continuous (fun w : Fin (n + 1) → E => e.toMatrix w) := by
      refine continuous_matrix fun i j => ?_
      simp only [Basis.toMatrix_apply]
      exact ((e.coord i).continuous_of_finiteDimensional).comp (continuous_apply j)
    have hinner : ContinuousOn (fun q : g ⁻¹' {0} =>
        Matrix.vecCons (outward hE g q.1) (fun i => fderiv ℝ ψ (c₀ q) (u₀ i))) c₀.source := by
      rw [continuousOn_pi]; intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Matrix.cons_val_zero]
        exact hout.continuousOn
      · simp only [Matrix.cons_val_succ]
        exact hfd.clm_apply continuousOn_const
    exact continuousOn_const.mul
      ((continuous_id.matrix_det).comp_continuousOn (houter.comp_continuousOn hinner))
  -- proportionality: `Λ q = κ q • Λ q₀`
  have hprop : ∀ q, Λ q = (Λ q u₀ / Λ q₀ u₀) • Λ q₀ := by
    intro q
    obtain ⟨c, hc⟩ := exists_eq_smul_of_finrank hZ hΛ₀ne (Λ q)
    have hcu : Λ q u₀ = c * Λ q₀ u₀ := by rw [hc]; rfl
    rw [hcu, mul_div_cancel_right₀ _ hΛ₀u, hc]
  -- eventually `Λ q u₀` has the sign of `Λ q₀ u₀`
  have hev : ∀ᶠ q in 𝓝 q₀, 0 < Λ q u₀ / Λ q₀ u₀ := by
    have hc := hLcont.continuousAt ((isOpen_extChartAt_source q₀).mem_nhds hq₀src)
    rcases lt_or_gt_of_ne hΛ₀u with hneg | hpos
    · filter_upwards [hc.eventually_lt continuousAt_const hneg] with q hq
      exact div_pos_of_neg_of_neg hq hneg
    · filter_upwards [continuousAt_const.eventually_lt hc hpos] with q hq
      exact div_pos hq hpos
  filter_upwards [(isOpen_extChartAt_source q₀).mem_nhds hq₀src, hev] with q hq hκ
  -- the derivative of the chart at `q` is invertible
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, Z) 𝓘(ℝ, Z) ∞ c₀ q :=
    ⟨PartialDiffeomorph.ofExtChartAt 𝓘(ℝ, Z) q₀, hq, fun _ _ => rfl⟩
  set D := mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) c₀ q with hD
  obtain ⟨D', hD'⟩ : ∃ D' : Z ≃L[ℝ] Z, (D' : Z →L[ℝ] Z) = D :=
    ⟨hloc.mfderivToContinuousLinearEquiv (by simp), hloc.mfderivToContinuousLinearEquiv_coe (by simp)⟩
  -- rewrite the two orientations as rays of the representatives
  rw [← rayOfNeZero_contractForm hZ hom hom_ray _ _ (hrep' q),
    ← rayOfNeZero_contractForm hZ hom hom_ray _ _ (hrep' q₀)]
  -- evaluate on the tuple `z̄ = D⁻¹ u₀`
  have hz : contractForm om (outward hE g q.1) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q)
      (fun i => D'.symm (u₀ i)) ≠ 0 := by
    rw [hrepΛ q hq]
    show Λ q (fun i => D (D'.symm (u₀ i))) ≠ 0
    have : (fun i => D (D'.symm (u₀ i))) = u₀ := by
      funext i; rw [← hD', ContinuousLinearEquiv.coe_coe, D'.apply_symm_apply]
    rw [this, hprop q]
    simp only [AlternatingMap.smul_apply, smul_eq_mul]
    exact mul_ne_zero hκ.ne' hΛ₀u
  rw [orSign_eq_sgn_mul hZ _ _ rfl rfl D hz]
  -- compute the two values
  have e1 : contractForm om (outward hE g q.1) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q)
      (fun i => D'.symm (u₀ i)) = (Λ q u₀ / Λ q₀ u₀) * Λ q₀ u₀ := by
    rw [hrepΛ q hq]
    show Λ q (fun i => D (D'.symm (u₀ i))) = _
    have : (fun i => D (D'.symm (u₀ i))) = u₀ := by
      funext i; rw [← hD', ContinuousLinearEquiv.coe_coe, D'.apply_symm_apply]
    rw [this, div_mul_cancel₀ _ hΛ₀u]
  have e2 : ((contractForm om (outward hE g q₀.1) (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q₀)).compLinearMap
      D.toLinearMap) (fun i => D'.symm (u₀ i)) = Λ q₀ u₀ := by
    rw [← hΛ₀]
    show Λ q₀ (fun i => D (D'.symm (u₀ i))) = _
    have : (fun i => D (D'.symm (u₀ i))) = u₀ := by
      funext i; rw [← hD', ContinuousLinearEquiv.coe_coe, D'.apply_symm_apply]
    rw [this]
  rw [e1, e2]
  have : Λ q₀ u₀ * (Λ q u₀ / Λ q₀ u₀ * Λ q₀ u₀) = (Λ q₀ u₀ * Λ q₀ u₀) * (Λ q u₀ / Λ q₀ u₀) := by ring
  rw [this, sgn_sq_mul hΛ₀u, sgn_pos hκ]

/-- **The induced orientation of the level set** `g⁻¹(0)` (Milnor's boundary orientation of
`∂X`, `X = {g ≥ 0}`, for `X ⊆ E`). -/
def levelOrient :
    letI hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0
    letI := hS.chartedSpace
    Orient 𝓘(ℝ, Z) (g ⁻¹' {0}) n :=
  letI hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hg h0
  letI := hS.chartedSpace
  { or := fun q => contractOr hZ a₀ (outward hE g q.1)
      (mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : g ⁻¹' {0} → E) q)
    cont := levelOrient_cont hE hZ a₀ hg h0 }

end level

end Milnor
