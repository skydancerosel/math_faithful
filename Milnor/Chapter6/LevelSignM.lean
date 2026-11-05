import Milnor.Chapter6.LevelOrientM
import Milnor.Chapter6.LevelSign

/-!
# The boundary orientation versus the pair map, in a manifold

The bridge lemma of `LevelSign` for a level set `S = G⁻¹(0)` in an oriented manifold `M`
with charts in `E` (in particular an open subset of `E`): the sign of `f|S` for the level-set
orientation `levelOrientM` equals `(-1)ⁿ⁺¹` times the sign of the pair map `(f, G)`.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G' : Type*} [TopologicalSpace G'] {J : ModelWithCorners ℝ F G'} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G' N] [IsManifold J ∞ N]

variable (hE : finrank ℝ E = n + 1) (hZ : finrank ℝ Z = n) (hF : finrank ℝ F = n)
  (oM : Orient 𝓘(ℝ, E) M (n + 1)) (oN : Orient J N n)
  {G : M → ℝ} (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G) (h0 : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G 0)
  {f : M → N}

include hE hZ hF hG h0 in
/-- **Level-set sign versus pair-map sign.** For `q ∈ S = G⁻¹(0)` with `f` differentiable at
`q`, `sign (f|S)_q = (-1)ⁿ⁺¹ · sign (f, G)_q`, the first for the level-set orientation of `S` and
the orientation `oN`, the second for `a₀` and the product orientation of `N × ℝ`. -/
theorem signAt_levelOrientM_eq' :
    letI hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG h0
    letI := hS.chartedSpace
    ∀ q : G ⁻¹' {0}, MDifferentiableAt 𝓘(ℝ, E) J f q.1 →
      signAt (levelOrientM hE hZ oM hG h0) oN (f ∘ Subtype.val) q =
      (-1) ^ (n + 1) * signAt oM (oN.prodReal hF) (pairMap f G) q.1 := by
  have hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG h0
  letI := hS.chartedSpace
  haveI := hS.isManifold
  intro q hfq
  -- the pieces of the level-set orientation at `q` (as in `levelOrient_cont`)
  have hreg : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 ≠ 0 := fun hz => by
    have hs : Function.Surjective (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1) := h0 q.1 q.2
    obtain ⟨v, hv⟩ := hs 1
    rw [hz] at hv
    simp at hv
  have hker : ∀ v : E, (∃ w, mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : G ⁻¹' {0} → M) q w = v) ↔
      mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 v = 0 := fun v =>
    mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) hG h0 q v
  set T := mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : G ⁻¹' {0} → M) q with hT
  have hdgι : ∀ w : Z, mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 (T w) = 0 := fun w => (hker _).1 ⟨w, rfl⟩
  have hιinj : Function.Injective T := by
    have hrange : LinearMap.range (T : Z →ₗ[ℝ] E) =
        LinearMap.ker (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 : E →ₗ[ℝ] ℝ) := by
      ext v
      simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      exact hker v
    have h1 := LinearMap.finrank_range_add_finrank_ker (T : Z →ₗ[ℝ] E)
    have h2 := LinearMap.finrank_range_add_finrank_ker (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 : E →ₗ[ℝ] ℝ)
    have h3 : LinearMap.range (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 : E →ₗ[ℝ] ℝ) = ⊤ := by
      rw [LinearMap.range_eq_top]
      have hex : ∃ v, mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 v ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hreg (ContinuousLinearMap.ext hcon)
      obtain ⟨v, hv⟩ := hex
      intro t
      exact ⟨(t / mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 v) • v, by simp [div_mul_cancel₀ _ hv]⟩
    rw [h3, finrank_top, Module.finrank_self, hE] at h2
    rw [hrange, hZ] at h1
    have h4 : finrank ℝ (LinearMap.ker (T : Z →ₗ[ℝ] E)) = 0 := by omega
    rw [Submodule.finrank_eq_zero] at h4
    exact LinearMap.ker_eq_bot.1 h4
  set a₀ := oM.or q.1 with ha₀
  set e := finBasisOfFinrankEq ℝ E hE with he
  set om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ := orEpsB e a₀ • e.det with hom_def
  have hom : om ≠ 0 := orEpsB_smul_det_ne_zero e a₀
  have hom_ray : rayOfNeZero ℝ om hom = a₀ := rayOfNeZero_orEpsB_det e a₀
  set u₀ := finBasisOfFinrankEq ℝ Z hZ with hu₀
  set v₀ := outwardM hE G q.1 with hv₀
  have hv₀neg : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 v₀ < 0 := mfd_outwardM_neg hE hreg
  have hrep : contractForm om v₀ T u₀ ≠ 0 :=
    contractForm_basis_ne_zero hE hZ hom hιinj hdgι hv₀neg.ne u₀
  have hrep' : contractForm om v₀ T ≠ 0 := fun h => hrep (by rw [h]; rfl)
  -- the derivative of `f ∘ ι` and of the pair map
  have hfι : mfd 𝓘(ℝ, Z) J (f ∘ Subtype.val) q = (mfd 𝓘(ℝ, E) J f q.1).comp T :=
    HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := 𝓘(ℝ, E)) (J := J) hfq).comp q
      (hasMFDerivAt_mfd (I := 𝓘(ℝ, Z)) (J := 𝓘(ℝ, E)) (hS.contMDiff_val.mdifferentiableAt (by simp))))
  have hpair : mfd 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) (pairMap f G) q.1 =
      (mfd 𝓘(ℝ, E) J f q.1).prod (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1) :=
    mfd_pairMap hfq (hG.mdifferentiableAt (by simp))
  set A := mfd 𝓘(ℝ, E) J f q.1 with hA
  -- representative of `oN` at `f q`
  set fb := finBasisOfFinrankEq ℝ F hF with hfb
  set η : F [⋀^Fin n]→ₗ[ℝ] ℝ := orEpsB fb (oN.or (f q.1)) • fb.det with hη_def
  have hη : η ≠ 0 := orEpsB_smul_det_ne_zero fb _
  have hη_ray : rayOfNeZero ℝ η hη = oN.or (f q.1) := rayOfNeZero_orEpsB_det fb _
  -- the left-hand side
  have hL : signAt (levelOrientM hE hZ oM hG h0) oN (f ∘ Subtype.val) q =
      sgn (η (fun i => A (T (u₀ i))) * contractForm om v₀ T u₀) := by
    unfold signAt
    show orSign (contractOr hZ a₀ v₀ T) (oN.or (f q.1)) (mfd 𝓘(ℝ, Z) J (f ∘ Subtype.val) q) = _
    rw [← rayOfNeZero_contractForm hZ hom hom_ray v₀ T hrep', hfι,
      orSign_eq_sgn_mul hZ _ hη rfl hη_ray _ hrep]
    rfl
  -- the right-hand side: evaluate on the basis `(v₀, T u₀)` of `E`
  have hli : LinearIndependent ℝ (Matrix.vecCons v₀ fun i => T (u₀ i)) := by
    rw [Matrix.vecCons, linearIndependent_finCons]
    refine ⟨u₀.linearIndependent.map' T.toLinearMap (LinearMap.ker_eq_bot_of_injective hιinj), ?_⟩
    intro hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
    have h1 : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 v₀ = 0 := by
      rw [← hc, map_sum]; simp [hdgι]
    exact hv₀neg.ne h1
  have homv : om (Matrix.vecCons v₀ fun i => T (u₀ i)) ≠ 0 := hrep
  have hR : signAt oM (oN.prodReal hF) (pairMap f G) q.1 =
      sgn ((orEpsB fb (oN.or (f q.1)) • (prodRealBasis fb).det)
        (fun j => mfd 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) (pairMap f G) q.1
          (Matrix.vecCons v₀ (fun i => T (u₀ i)) j)) * om (Matrix.vecCons v₀ fun i => T (u₀ i))) := by
    unfold signAt
    show orSign a₀ (orProd hF (oN.or (f q.1))) _ = _
    rw [orSign_eq_sgn_mul hE hom (orProd_rep_ne_zero hF _) hom_ray (rayOfNeZero_orProd hF _) _ homv]
    rfl
  -- the block determinant
  have hdet : (prodRealBasis fb).det (fun j => mfd 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) (pairMap f G) q.1
      (Matrix.vecCons v₀ (fun i => T (u₀ i)) j)) =
      (-1) ^ n * mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 v₀ * fb.det (fun i => A (T (u₀ i))) := by
    rw [Basis.det_apply, Matrix.det_succ_row _ (Fin.last n)]
    set M := (prodRealBasis fb).toMatrix (fun j => mfd 𝓘(ℝ, E) (J.prod 𝓘(ℝ, ℝ)) (pairMap f G) q.1
      (Matrix.vecCons v₀ (fun i => T (u₀ i)) j)) with hM
    -- the last row is `(dG v₀, 0, …, 0)`
    have hlast : ∀ j : Fin (n + 1), M (Fin.last n) j =
        if j = 0 then mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 v₀ else 0 := by
      intro j
      rw [hM, Basis.toMatrix_apply, prodRealBasis_repr_last, hpair]
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp [hdgι]
    have hsub : M.submatrix (Fin.last n).succAbove (Fin.succAbove 0) =
        fb.toMatrix (fun i => A (T (u₀ i))) := by
      ext k i
      rw [Matrix.submatrix_apply, Fin.succAbove_last, hM, Basis.toMatrix_apply, Basis.toMatrix_apply,
        prodRealBasis_repr_castSucc, hpair]
      simp [Fin.succAbove_zero]
    rw [Fin.sum_univ_succ]
    simp only [hlast, if_true, Fin.succ_ne_zero, if_false, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, Fin.val_last, Fin.val_zero, add_zero, hsub, Basis.det_apply]
    try ring
  rw [hL, hR]
  simp only [AlternatingMap.smul_apply, smul_eq_mul, hdet, η, contractForm_apply]
  have hsgnpow : sgn ((-1 : ℝ) ^ n) = (-1) ^ n := by
    rcases Nat.even_or_odd n with h | h
    · rw [h.neg_one_pow, h.neg_one_pow, sgn_one]
    · rw [h.neg_one_pow, h.neg_one_pow, sgn_neg (by norm_num)]
  have hcalc : ∀ ε d c : ℝ, ε * ((-1) ^ n * mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 v₀ * d) * c =
      ((-1) ^ n * mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 v₀) * (ε * d * c) := by intros; ring
  rw [hcalc]
  conv_rhs => rw [sgn_mul, sgn_mul, hsgnpow, sgn_neg hv₀neg]
  have hpow : ((-1 : ℤ) ^ (n + 1)) * ((-1) ^ n * -1) = 1 := by
    rw [show ((-1 : ℤ) ^ n * -1) = (-1) ^ (n + 1) by rw [pow_succ], ← pow_add, ← two_mul, pow_mul]
    norm_num
  set s := sgn (orEpsB fb (oN.or (f q.1)) * fb.det (fun i => A (T (u₀ i))) *
    om (Matrix.vecCons v₀ fun i => T (u₀ i))) with hs
  linear_combination (-s) * hpow

include hE hZ hF hG h0 in
/-- The bridge lemma for a globally smooth `f`. -/
theorem signAt_levelOrientM_eq (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) :
    letI hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG h0
    letI := hS.chartedSpace
    ∀ q : G ⁻¹' {0}, signAt (levelOrientM hE hZ oM hG h0) oN (f ∘ Subtype.val) q =
      (-1) ^ (n + 1) * signAt oM (oN.prodReal hF) (pairMap f G) q.1 :=
  fun q => signAt_levelOrientM_eq' hE hZ hF oM oN hG h0 q (hf.mdifferentiableAt (by simp))

include hE hZ hF hG h0 in
/-- **Milnor's Lemma 1 (§5) for `X = {G ≥ 0} ⊆ E`, in boundary-orientation form.**  If `y` is a
regular value of `f` and of `f|∂X` (transversality `hreg`) and `f⁻¹(y) ∩ X` is compact, then
the degree of `f|∂X` at `y`, for the boundary orientation of `∂X = G⁻¹(0)`, is zero. -/
theorem degAt_levelOrientM_eq_zero [T2Space M] [T2Space N] (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {y : N}
    (hy : IsRegularValue 𝓘(ℝ, E) J f y)
    (hreg : ∀ x, f x = y → G x = 0 →
      ∃ v, mfd 𝓘(ℝ, E) J f x v = 0 ∧ mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G x v ≠ 0)
    (hX : IsCompact {x : M | f x = y ∧ 0 ≤ G x}) :
    letI hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG h0
    letI := hS.chartedSpace
    degAt (levelOrientM hE hZ oM hG h0) oN (f ∘ Subtype.val) y = 0 := by
  have hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG h0
  letI := hS.chartedSpace
  haveI := hS.isManifold
  obtain ⟨hfin0, hL⟩ := lemmaOne_ambient' hE hF oM oN hf hy hG hreg hX
  have himg : {x : M | f x = y ∧ G x = 0} =
      Subtype.val '' ((f ∘ Subtype.val) ⁻¹' {y} : Set (G ⁻¹' {0})) := by
    ext x; constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, h2⟩, h1, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨hq, q.2⟩
  rw [himg] at hfin0 hL
  rw [finsum_mem_image Subtype.val_injective.injOn] at hL
  have hfin : ((f ∘ Subtype.val) ⁻¹' {y} : Set (G ⁻¹' {0})).Finite :=
    (hfin0.of_finite_image Subtype.val_injective.injOn)
  unfold degAt
  rw [finsum_mem_congr rfl (fun q _ => signAt_levelOrientM_eq hE hZ hF oM oN hG h0 hf q),
    ← mul_finsum_mem' _ _ hfin, hL, mul_zero]

end Milnor
