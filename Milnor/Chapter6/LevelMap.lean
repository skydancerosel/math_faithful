import Milnor.Chapter6.LevelOrientM
import Milnor.Chapter6.RegularOpen
import Milnor.Chapter2.Corestrict

/-!
# Maps between level sets, and the sign of the restricted map

* `signAt_levelOrientM_map`: if `Φ : M → M'` carries the level set `G⁻¹(0)` into `G'⁻¹(0)` and
  `dG' ∘ dΦ = c · dG` with `c > 0` at a point `q` of the level set, then the sign of the
  restricted map `G⁻¹(0) → G'⁻¹(0)` at `q` (for the level-set orientations) equals the ambient
  sign of `Φ` at `q`.
* `degAt_comp_bij`: the degree is unchanged by precomposition with a bijective map of sign `+1`.
* `orSign_self_eq_sgn_det`: for a self-map of a vector space the sign is the sign of the
  determinant.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

section forms

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] {n : ℕ}

/-- Independence of the outward vector, with all vectors in the range of an `n`-dimensional
subspace. -/
theorem contractForm_eq_smul_of_mem (hZ : finrank ℝ Z = n) (om : E [⋀^Fin (n + 1)]→ₗ[ℝ] ℝ)
    {T T' : Z →L[ℝ] E} (hT : ∀ u, T u ∈ LinearMap.range (T' : Z →ₗ[ℝ] E)) {w w' t : E} {a : ℝ}
    (ht : t ∈ LinearMap.range (T' : Z →ₗ[ℝ] E)) (h : w = a • w' + t) :
    contractForm om w T = a • contractForm om w' T := by
  ext u
  simp only [contractForm_apply, AlternatingMap.smul_apply, smul_eq_mul, h]
  have hcons : Matrix.vecCons (a • w' + t) (fun i => T (u i)) =
      Function.update (Matrix.vecCons w' fun i => T (u i)) 0 (a • w' + t) := by
    funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  rw [hcons, AlternatingMap.map_update_add, AlternatingMap.map_update_smul]
  have h0 : Function.update (Matrix.vecCons w' fun i => T (u i)) 0 w' =
      Matrix.vecCons w' fun i => T (u i) := by
    funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
  have hdep : om (Function.update (Matrix.vecCons w' fun i => T (u i)) 0 t) = 0 := by
    apply AlternatingMap.map_linearDependent
    intro hli
    have hsub : Set.range (Function.update (Matrix.vecCons w' fun i => T (u i)) 0 t) ⊆
        LinearMap.range (T' : Z →ₗ[ℝ] E) := by
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using ht
      · simpa using hT (u i)
    have h1 := finrank_span_eq_card (R := ℝ) hli
    have h2 := Submodule.finrank_mono (Submodule.span_le.2 hsub)
    have h3 := LinearMap.finrank_range_le (T' : Z →ₗ[ℝ] E)
    rw [Fintype.card_fin] at h1
    rw [hZ] at h3
    omega
  rw [h0, hdep, add_zero]
  rfl

/-- For a self-map, the sign is the sign of the determinant. -/
theorem orSign_self_eq_sgn_det {m : ℕ} (hE : finrank ℝ E = m) (a : Orientation ℝ E (Fin m))
    (T : E →L[ℝ] E) : orSign a a T = sgn (LinearMap.det (T : E →ₗ[ℝ] E)) := by
  set e := finBasisOfFinrankEq ℝ E hE
  have hc : (orEpsB e a • e.det).compLinearMap T.toLinearMap =
      LinearMap.det (T : E →ₗ[ℝ] E) • (orEpsB e a • e.det) := by
    ext v
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul]
    have hd := Basis.det_comp e (T : E →ₗ[ℝ] E) v
    simp only [Function.comp_def] at hd
    rw [hd]
    ring
  exact orSign_eq_sgn _ _ (rayOfNeZero_orEpsB_det e a) (rayOfNeZero_orEpsB_det e a) hc

end forms

section bij

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {G'' : Type*} [TopologicalSpace G''] {K : ModelWithCorners ℝ F' G''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace G'' P] [IsManifold K ∞ P] {n : ℕ}

/-- **Precomposition with a bijection of sign `+1`** does not change the degree. -/
theorem degAt_comp_bij (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) (oP : Orient K P n) {f : N → P} (hf : ∀ y, MDifferentiableAt J K f y)
    {φ : M → N} (hφb : Bijective φ) (hφd : ∀ x, MDifferentiableAt I J φ x)
    (hφ : ∀ x, signAt oM oN φ x = 1) (z : P) :
    degAt oM oP (fun x => f (φ x)) z = degAt oN oP f z := by
  unfold degAt
  refine finsum_mem_eq_of_bijOn φ ?_ fun x _ => ?_
  · refine ⟨fun x hx => hx, hφb.1.injOn, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := hφb.2 y
    exact ⟨x, hy, rfl⟩
  · rw [signAt_comp' hE hF oM oN oP (hφd x) (hf (φ x)), hφ x, mul_one]

end bij

section map

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(ℝ, E) ∞ M']
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] {n : ℕ}
  (hE : finrank ℝ E = n + 1) (hZ : finrank ℝ Z = n)
  (oM : Orient 𝓘(ℝ, E) M (n + 1)) (oM' : Orient 𝓘(ℝ, E) M' (n + 1))
  {G : M → ℝ} (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G) (h0 : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G 0)
  {G' : M' → ℝ} (hG' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G')
  (h0' : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' 0)

include hE hZ hG h0 hG' h0' in
/-- **Sign of a map restricted to level sets.**  If `Φ` maps `G⁻¹(0)` into `G'⁻¹(0)`, is
smooth along `G⁻¹(0)`, and `dG'_{Φ q} ∘ dΦ_q = c · dG_q` with `c > 0`, then the sign of the
restricted map at `q` (level-set orientations) is the ambient sign of `Φ` at `q`. -/
theorem signAt_levelOrientM_map {Φ : M → M'} (hΦG : ∀ x, G x = 0 → G' (Φ x) = 0) :
    letI hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG h0
    letI := hS.chartedSpace
    letI hS' := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG' h0'
    letI := hS'.chartedSpace
    ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ (fun q : G ⁻¹' {0} => Φ q.1) →
    ∀ q : G ⁻¹' {0}, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) Φ q.1 →
      (∃ c : ℝ, 0 < c ∧ (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φ q.1)).comp (mfd 𝓘(ℝ, E) 𝓘(ℝ, E) Φ q.1) =
        c • mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1) →
      signAt (levelOrientM hE hZ oM hG h0) (levelOrientM hE hZ oM' hG' h0')
        (fun q => (⟨Φ q.1, hΦG q.1 q.2⟩ : G' ⁻¹' {0})) q = signAt oM oM' Φ q.1 := by
  have hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG h0
  letI := hS.chartedSpace
  haveI := hS.isManifold
  have hS' := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG' h0'
  letI := hS'.chartedSpace
  haveI := hS'.isManifold
  intro hΦs q hΦq hc
  obtain ⟨c, hc, hdc⟩ := hc
  set Φr : G ⁻¹' {0} → G' ⁻¹' {0} := fun q => ⟨Φ q.1, hΦG q.1 q.2⟩ with hΦr
  have hΦrs : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, Z) ∞ Φr :=
    IsSliceSubmanifold.contMDiff_codRestrict hS' hΦs (fun q => hΦG q.1 q.2)
  set T := mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : G ⁻¹' {0} → M) q with hT
  set T' := mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : G' ⁻¹' {0} → M') (Φr q) with hT'
  set DΦ := mfd 𝓘(ℝ, E) 𝓘(ℝ, E) Φ q.1 with hDΦ
  set Dr := mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) Φr q with hDr
  -- chain rule: `T' ∘ Dr = DΦ ∘ T`
  have hchain : T'.comp Dr = DΦ.comp T := by
    have hv' : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : G' ⁻¹' {0} → M') (Φr q) :=
      hS'.contMDiff_val.mdifferentiableAt (by simp)
    have hv : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : G ⁻¹' {0} → M) q :=
      hS.contMDiff_val.mdifferentiableAt (by simp)
    have h1 := (hasMFDerivAt_mfd (I := 𝓘(ℝ, Z)) (J := 𝓘(ℝ, E)) hv').comp q
      (hasMFDerivAt_mfd (I := 𝓘(ℝ, Z)) (J := 𝓘(ℝ, Z)) (hΦrs.mdifferentiableAt (by simp)))
    have h2 := (hasMFDerivAt_mfd (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, E)) hΦq).comp q
      (hasMFDerivAt_mfd (I := 𝓘(ℝ, Z)) (J := 𝓘(ℝ, E)) hv)
    have h3 : ((Subtype.val : G' ⁻¹' {0} → M') ∘ Φr) = Φ ∘ (Subtype.val : G ⁻¹' {0} → M) := rfl
    rw [h3] at h1
    exact hasMFDerivAt_unique h1 h2
  -- derivatives of `G`, `G'` and the outward vectors
  have hdG : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 ≠ 0 := mfd_ne_zero_of_level hE hZ hG h0 q
  have hdG' : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 ≠ 0 := mfd_ne_zero_of_level hE hZ hG' h0' (Φr q)
  set out := outwardM hE G q.1 with hout_def
  set out' := outwardM hE G' (Φr q).1 with hout'_def
  have hout : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 out < 0 := mfd_outwardM_neg hE hdG
  have hout' : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 out' < 0 := mfd_outwardM_neg hE hdG'
  have hDΦout : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 (DΦ out) = c * mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 out := by
    have := congrArg (fun L : E →L[ℝ] ℝ => L out) hdc
    simpa using this
  set a := mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 (DΦ out) / mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 out'
    with ha
  have ha_pos : 0 < a :=
    div_pos_of_neg_of_neg (by rw [hDΦout]; exact mul_neg_of_pos_of_neg hc hout) hout'
  have hrange' : ∀ v, v ∈ LinearMap.range (T' : Z →ₗ[ℝ] E) ↔
      mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 v = 0 := fun v => by
    rw [LinearMap.mem_range]
    exact mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) hG' h0' (Φr q) v
  have ht : DΦ out - a • out' ∈ LinearMap.range (T' : Z →ₗ[ℝ] E) := by
    rw [hrange', map_sub, map_smul, smul_eq_mul, ha, div_mul_cancel₀ _ hout'.ne, sub_self]
  have hTmem : ∀ u, (DΦ.comp T) u ∈ LinearMap.range (T' : Z →ₗ[ℝ] E) := fun u => by
    have : (DΦ.comp T) u = T' (Dr u) := by
      have := congrArg (fun L : Z →L[ℝ] E => L u) hchain
      simpa using this.symm
    rw [this]
    exact LinearMap.mem_range_self _ _
  -- representatives
  set om := (oM.or q.1).someVector with hom
  set om' := (oM'.or (Φr q).1).someVector with hom'
  obtain ⟨c', hc'⟩ := exists_eq_smul_of_finrank hE (oM.or q.1).someVector_ne_zero
    (om'.compLinearMap DΦ.toLinearMap)
  have hsign : signAt oM oM' Φ q.1 = sgn c' :=
    orSign_eq_sgn _ _ (someVector_ray' _) (someVector_ray' _) hc'
  set u₀ := finBasisOfFinrankEq ℝ Z hZ with hu₀
  have hrep : contractForm om out T u₀ ≠ 0 :=
    levelOrientM_rep_ne_zero hE hZ hG h0 q (oM.or q.1).someVector_ne_zero
  have hrepne : contractForm om out T ≠ 0 :=
    levelOrientM_rep_ne_zero' hE hZ hG h0 q (oM.or q.1).someVector_ne_zero
  have hrep' : contractForm om' out' T' ≠ 0 :=
    levelOrientM_rep_ne_zero' hE hZ hG' h0' (Φr q) (oM'.or (Φr q).1).someVector_ne_zero
  -- the key computation
  have hkey : ((contractForm om' out' T').compLinearMap Dr.toLinearMap) u₀ =
      a⁻¹ * (c' * contractForm om out T u₀) := by
    have e1 : (contractForm om' out' T').compLinearMap Dr.toLinearMap =
        contractForm om' out' (DΦ.comp T) := by
      rw [contractForm_comp, hchain]
    have e2 : contractForm om' out' (DΦ.comp T) = a⁻¹ • contractForm om' (DΦ out) (DΦ.comp T) := by
      have hdec : DΦ out = a • out' + (DΦ out - a • out') := by abel
      rw [contractForm_eq_smul_of_mem hZ om' hTmem ht hdec, smul_smul,
        inv_mul_cancel₀ ha_pos.ne', one_smul]
    have e3 : contractForm om' (DΦ out) (DΦ.comp T) = c' • contractForm om out T := by
      rw [← contractForm_pullback, hc', contractForm_smul]
    rw [e1, e2, e3]
    simp only [AlternatingMap.smul_apply, smul_eq_mul]
  -- conclude
  unfold signAt
  show orSign (contractOr hZ (oM.or q.1) out T) (contractOr hZ (oM'.or (Φr q).1) out' T') Dr =
    orSign (oM.or q.1) (oM'.or (Φ q.1)) DΦ
  rw [← rayOfNeZero_contractForm hZ (oM.or q.1).someVector_ne_zero (someVector_ray' _) _ _ hrepne,
    ← rayOfNeZero_contractForm hZ (oM'.or (Φr q).1).someVector_ne_zero (someVector_ray' _) _ _
      hrep', orSign_eq_sgn_mul hZ _ _ rfl rfl Dr hrep, hkey]
  have hs : signAt oM oM' Φ q.1 = orSign (oM.or q.1) (oM'.or (Φ q.1)) DΦ := rfl
  rw [← hs, hsign]
  have : a⁻¹ * (c' * contractForm om out T u₀) * contractForm om out T u₀ =
      (contractForm om out T u₀ * contractForm om out T u₀) * (a⁻¹ * c') := by ring
  rw [this, sgn_sq_mul hrep, sgn_mul, sgn_pos (inv_pos.2 ha_pos), one_mul]

include hE hZ hG h0 hG' h0' in
/-- **Sign of a map restricted to level sets, general constant.**  With
`dG'_{Φ q} ∘ dΦ_q = c · dG_q`, `c ≠ 0`, the sign of the restricted map is `sgn c` times the
ambient sign of `Φ`. -/
theorem signAt_levelOrientM_map' {Φ : M → M'} (hΦG : ∀ x, G x = 0 → G' (Φ x) = 0) :
    letI hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG h0
    letI := hS.chartedSpace
    letI hS' := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG' h0'
    letI := hS'.chartedSpace
    ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ (fun q : G ⁻¹' {0} => Φ q.1) →
    ∀ q : G ⁻¹' {0}, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) Φ q.1 →
      ∀ c : ℝ, c ≠ 0 → (mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φ q.1)).comp (mfd 𝓘(ℝ, E) 𝓘(ℝ, E) Φ q.1) =
        c • mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 →
      signAt (levelOrientM hE hZ oM hG h0) (levelOrientM hE hZ oM' hG' h0')
        (fun q => (⟨Φ q.1, hΦG q.1 q.2⟩ : G' ⁻¹' {0})) q = sgn c * signAt oM oM' Φ q.1 := by
  have hS := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG h0
  letI := hS.chartedSpace
  haveI := hS.isManifold
  have hS' := isSliceSubmanifold_preimage (Z := Z) (finrank_Z_add hE hZ) hG' h0'
  letI := hS'.chartedSpace
  haveI := hS'.isManifold
  intro hΦs q hΦq c hc hdc
  set Φr : G ⁻¹' {0} → G' ⁻¹' {0} := fun q => ⟨Φ q.1, hΦG q.1 q.2⟩ with hΦr
  have hΦrs : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, Z) ∞ Φr :=
    IsSliceSubmanifold.contMDiff_codRestrict hS' hΦs (fun q => hΦG q.1 q.2)
  set T := mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : G ⁻¹' {0} → M) q with hT
  set T' := mfd 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : G' ⁻¹' {0} → M') (Φr q) with hT'
  set DΦ := mfd 𝓘(ℝ, E) 𝓘(ℝ, E) Φ q.1 with hDΦ
  set Dr := mfd 𝓘(ℝ, Z) 𝓘(ℝ, Z) Φr q with hDr
  -- chain rule: `T' ∘ Dr = DΦ ∘ T`
  have hchain : T'.comp Dr = DΦ.comp T := by
    have hv' : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : G' ⁻¹' {0} → M') (Φr q) :=
      hS'.contMDiff_val.mdifferentiableAt (by simp)
    have hv : MDifferentiableAt 𝓘(ℝ, Z) 𝓘(ℝ, E) (Subtype.val : G ⁻¹' {0} → M) q :=
      hS.contMDiff_val.mdifferentiableAt (by simp)
    have h1 := (hasMFDerivAt_mfd (I := 𝓘(ℝ, Z)) (J := 𝓘(ℝ, E)) hv').comp q
      (hasMFDerivAt_mfd (I := 𝓘(ℝ, Z)) (J := 𝓘(ℝ, Z)) (hΦrs.mdifferentiableAt (by simp)))
    have h2 := (hasMFDerivAt_mfd (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, E)) hΦq).comp q
      (hasMFDerivAt_mfd (I := 𝓘(ℝ, Z)) (J := 𝓘(ℝ, E)) hv)
    have h3 : ((Subtype.val : G' ⁻¹' {0} → M') ∘ Φr) = Φ ∘ (Subtype.val : G ⁻¹' {0} → M) := rfl
    rw [h3] at h1
    exact hasMFDerivAt_unique h1 h2
  -- derivatives of `G`, `G'` and the outward vectors
  have hdG : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 ≠ 0 := mfd_ne_zero_of_level hE hZ hG h0 q
  have hdG' : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 ≠ 0 := mfd_ne_zero_of_level hE hZ hG' h0' (Φr q)
  set out := outwardM hE G q.1 with hout_def
  set out' := outwardM hE G' (Φr q).1 with hout'_def
  have hout : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 out < 0 := mfd_outwardM_neg hE hdG
  have hout' : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 out' < 0 := mfd_outwardM_neg hE hdG'
  have hDΦout : mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 (DΦ out) = c * mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G q.1 out := by
    have := congrArg (fun L : E →L[ℝ] ℝ => L out) hdc
    simpa using this
  set a := mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 (DΦ out) / mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 out'
    with ha
  have ha_ne : a ≠ 0 := by
    rw [ha, hDΦout]
    exact div_ne_zero (mul_ne_zero hc hout.ne) hout'.ne
  have hsgna : sgn a = sgn c := by
    rw [ha, hDΦout, mul_div_assoc, sgn_mul, sgn_pos (div_pos_of_neg_of_neg hout hout'), mul_one]
  have hsgninv : sgn a⁻¹ = sgn a := by
    rcases lt_or_gt_of_ne ha_ne with h | h
    · rw [sgn_neg (inv_lt_zero.2 h), sgn_neg h]
    · rw [sgn_pos (inv_pos.2 h), sgn_pos h]
  have hrange' : ∀ v, v ∈ LinearMap.range (T' : Z →ₗ[ℝ] E) ↔
      mfd 𝓘(ℝ, E) 𝓘(ℝ, ℝ) G' (Φr q).1 v = 0 := fun v => by
    rw [LinearMap.mem_range]
    exact mem_range_mfderiv_val_iff (finrank_Z_add hE hZ) hG' h0' (Φr q) v
  have ht : DΦ out - a • out' ∈ LinearMap.range (T' : Z →ₗ[ℝ] E) := by
    rw [hrange', map_sub, map_smul, smul_eq_mul, ha, div_mul_cancel₀ _ hout'.ne, sub_self]
  have hTmem : ∀ u, (DΦ.comp T) u ∈ LinearMap.range (T' : Z →ₗ[ℝ] E) := fun u => by
    have : (DΦ.comp T) u = T' (Dr u) := by
      have := congrArg (fun L : Z →L[ℝ] E => L u) hchain
      simpa using this.symm
    rw [this]
    exact LinearMap.mem_range_self _ _
  -- representatives
  set om := (oM.or q.1).someVector with hom
  set om' := (oM'.or (Φr q).1).someVector with hom'
  obtain ⟨c', hc'⟩ := exists_eq_smul_of_finrank hE (oM.or q.1).someVector_ne_zero
    (om'.compLinearMap DΦ.toLinearMap)
  have hsign : signAt oM oM' Φ q.1 = sgn c' :=
    orSign_eq_sgn _ _ (someVector_ray' _) (someVector_ray' _) hc'
  set u₀ := finBasisOfFinrankEq ℝ Z hZ with hu₀
  have hrep : contractForm om out T u₀ ≠ 0 :=
    levelOrientM_rep_ne_zero hE hZ hG h0 q (oM.or q.1).someVector_ne_zero
  have hrepne : contractForm om out T ≠ 0 :=
    levelOrientM_rep_ne_zero' hE hZ hG h0 q (oM.or q.1).someVector_ne_zero
  have hrep' : contractForm om' out' T' ≠ 0 :=
    levelOrientM_rep_ne_zero' hE hZ hG' h0' (Φr q) (oM'.or (Φr q).1).someVector_ne_zero
  -- the key computation
  have hkey : ((contractForm om' out' T').compLinearMap Dr.toLinearMap) u₀ =
      a⁻¹ * (c' * contractForm om out T u₀) := by
    have e1 : (contractForm om' out' T').compLinearMap Dr.toLinearMap =
        contractForm om' out' (DΦ.comp T) := by
      rw [contractForm_comp, hchain]
    have e2 : contractForm om' out' (DΦ.comp T) = a⁻¹ • contractForm om' (DΦ out) (DΦ.comp T) := by
      have hdec : DΦ out = a • out' + (DΦ out - a • out') := by abel
      rw [contractForm_eq_smul_of_mem hZ om' hTmem ht hdec, smul_smul,
        inv_mul_cancel₀ ha_ne, one_smul]
    have e3 : contractForm om' (DΦ out) (DΦ.comp T) = c' • contractForm om out T := by
      rw [← contractForm_pullback, hc', contractForm_smul]
    rw [e1, e2, e3]
    simp only [AlternatingMap.smul_apply, smul_eq_mul]
  -- conclude
  unfold signAt
  show orSign (contractOr hZ (oM.or q.1) out T) (contractOr hZ (oM'.or (Φr q).1) out' T') Dr =
    sgn c * orSign (oM.or q.1) (oM'.or (Φ q.1)) DΦ
  rw [← rayOfNeZero_contractForm hZ (oM.or q.1).someVector_ne_zero (someVector_ray' _) _ _ hrepne,
    ← rayOfNeZero_contractForm hZ (oM'.or (Φr q).1).someVector_ne_zero (someVector_ray' _) _ _
      hrep', orSign_eq_sgn_mul hZ _ _ rfl rfl Dr hrep, hkey]
  have hs : signAt oM oM' Φ q.1 = orSign (oM.or q.1) (oM'.or (Φ q.1)) DΦ := rfl
  rw [← hs, hsign]
  have : a⁻¹ * (c' * contractForm om out T u₀) * contractForm om out T u₀ =
      (contractForm om out T u₀ * contractForm om out T u₀) * (a⁻¹ * c') := by ring
  rw [this, sgn_sq_mul hrep, sgn_mul, hsgninv, hsgna]

end map

end Milnor
