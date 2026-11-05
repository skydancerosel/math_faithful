import Milnor.Chapter5.OrSignAlg
import Milnor.Chapter6.SignLemmas
import Milnor.Chapter6.LevelMap

/-!
# Orientations of products

For oriented vector spaces `E` (dimension `m`) and `F` (dimension `n`), the product orientation
of `E × F` (`orProdGen`) is the one for which a positive basis of `E` followed by a positive
basis of `F` is positive (`orProdGen_eq`).  We compute the sign of block-triangular maps
(`orSign_prod_triangular`, `orSign_prodMap`) and of the swap `E × F → F × E`
(`orSign_swap`, sign `(-1)^(m n)`).

For oriented manifolds `M`, `N` we obtain the product orientation `Orient.prod` of `M × N`, and
the sign of a product map is the product of the signs (`signAt_prodMap`).

Since `orSign`/`signAt` compare orientations with the same index type `Fin k`, we also provide the
transport `Orient.cast` of an orientation along an equality `k = k'` of dimension indices (which
does not change signs, `signAt_cast`), and the swap `M × N → N × M` has sign `(-1)^(m n)`
everywhere (`signAt_swap`).

The representing top-degree form of `orProdGen hE hF a b` is
`orEpsB e a * orEpsB f b • det (prodBasis e f)`, for the concatenated basis `prodBasis e f` of any
bases `e`, `f` (`rayOfNeZero_prodBasis`); determinants of block-triangular families in this basis
are products of determinants (`prodBasis_det_apply`).  The swap sign comes from the sign of the
block flip `finAddFlip`, a power of `finRotate` (`sign_finCongr_trans_finAddFlip`).
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

section linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F'] {m n : ℕ}

/-! ### The concatenated basis -/

/-- The basis `(e₁,0), …, (e_m,0), (0,f₁), …, (0,f_n)` of `E × F`. -/
def prodBasis (e : Basis (Fin m) ℝ E) (f : Basis (Fin n) ℝ F) : Basis (Fin (m + n)) ℝ (E × F) :=
  (e.prod f).reindex finSumFinEquiv

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem prodBasis_castAdd (e : Basis (Fin m) ℝ E) (f : Basis (Fin n) ℝ F) (i : Fin m) :
    prodBasis e f (Fin.castAdd n i) = (e i, 0) := by
  rw [prodBasis, Basis.reindex_apply, ← finSumFinEquiv_apply_left, Equiv.symm_apply_apply]
  exact Prod.ext (Basis.prod_apply_inl_fst _ _ _) (Basis.prod_apply_inl_snd _ _ _)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem prodBasis_natAdd (e : Basis (Fin m) ℝ E) (f : Basis (Fin n) ℝ F) (i : Fin n) :
    prodBasis e f (Fin.natAdd m i) = (0, f i) := by
  rw [prodBasis, Basis.reindex_apply, ← finSumFinEquiv_apply_right, Equiv.symm_apply_apply]
  exact Prod.ext (Basis.prod_apply_inr_fst _ _ _) (Basis.prod_apply_inr_snd _ _ _)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Block-triangular determinant.** If the first `m` vectors of `u` are `(α j, γ j)` and the last
`n` are `(0, β j)`, then the determinant of `u` in the concatenated basis is
`det_e α * det_f β`. -/
theorem prodBasis_det_apply (e : Basis (Fin m) ℝ E) (f : Basis (Fin n) ℝ F)
    (u : Fin (m + n) → E × F) (α : Fin m → E) (β : Fin n → F) (γ : Fin m → F)
    (h₁ : ∀ j, u (Fin.castAdd n j) = (α j, γ j)) (h₂ : ∀ j, u (Fin.natAdd m j) = (0, β j)) :
    (prodBasis e f).det u = e.det α * f.det β := by
  rw [prodBasis, Basis.det_reindex, Basis.det_apply, Basis.det_apply, Basis.det_apply]
  have hmat : (e.prod f).toMatrix (u ∘ finSumFinEquiv) =
      Matrix.fromBlocks (e.toMatrix α) 0 (f.toMatrix γ) (f.toMatrix β) := by
    ext (i | i) (j | j)
    · simp [Basis.toMatrix_apply, h₁]
    · simp [Basis.toMatrix_apply, h₂]
    · simp [Basis.toMatrix_apply, h₁]
    · simp [Basis.toMatrix_apply, h₂]
  rw [hmat, Matrix.det_fromBlocks_zero₁₂]

/-! ### The product orientation -/

/-- `orEpsB e₀ a * det_{e₀} e` has the sign of `orEpsB e a`. -/
theorem orEpsB_mul_det_mul_pos (e₀ e : Basis (Fin m) ℝ E) (a : Orientation ℝ E (Fin m)) :
    0 < orEpsB e₀ a * e₀.det e * orEpsB e a := by
  have hne : e₀.det e ≠ 0 := (e₀.isUnit_det e).ne_zero
  have key := e₀.orientation_eq_iff_det_pos e
  rcases e₀.orientation_eq_or_eq_neg a with h0 | h0 <;>
    rcases e.orientation_eq_or_eq_neg a with h1 | h1
  · rw [orEpsB_eq_one h0.symm, orEpsB_eq_one h1.symm]
    have : 0 < e₀.det e := key.1 (h0.symm.trans h1)
    linarith
  · rw [orEpsB_eq_one h0.symm, orEpsB_eq_neg_one h1]
    have : ¬ 0 < e₀.det e := fun hpos => Module.Ray.ne_neg_self e.orientation
      ((key.2 hpos).symm.trans (h0.symm.trans h1))
    have : e₀.det e < 0 := lt_of_le_of_ne (not_lt.1 this) hne
    linarith
  · rw [orEpsB_eq_neg_one h0, orEpsB_eq_one h1.symm]
    have : ¬ 0 < e₀.det e := fun hpos => Module.Ray.ne_neg_self e.orientation
      (h1.symm.trans (h0.trans (by rw [key.2 hpos])))
    have : e₀.det e < 0 := lt_of_le_of_ne (not_lt.1 this) hne
    linarith
  · rw [orEpsB_eq_neg_one h0, orEpsB_eq_neg_one h1]
    have : 0 < e₀.det e := key.1 (neg_inj.1 (h0.symm.trans h1))
    linarith

theorem orProdForm_ne_zero (e : Basis (Fin m) ℝ E) (f : Basis (Fin n) ℝ F)
    (a : Orientation ℝ E (Fin m)) (b : Orientation ℝ F (Fin n)) :
    (orEpsB e a * orEpsB f b) • (prodBasis e f).det ≠ 0 :=
  smul_ne_zero (mul_ne_zero (orEpsB_ne_zero e a) (orEpsB_ne_zero f b)) (prodBasis e f).det_ne_zero

/-- The product orientation: a positive basis of `E` followed by a positive basis of `F`. -/
def orProdGen (hE : finrank ℝ E = m) (hF : finrank ℝ F = n) (a : Orientation ℝ E (Fin m))
    (b : Orientation ℝ F (Fin n)) : Orientation ℝ (E × F) (Fin (m + n)) :=
  rayOfNeZero ℝ _ (orProdForm_ne_zero (finBasisOfFinrankEq ℝ E hE) (finBasisOfFinrankEq ℝ F hF) a b)

/-- The product orientation is represented by `orEpsB e a * orEpsB f b • det (e, f)` for any
bases `e` of `E` and `f` of `F`. -/
theorem rayOfNeZero_prodBasis (hE : finrank ℝ E = m) (hF : finrank ℝ F = n)
    (a : Orientation ℝ E (Fin m)) (b : Orientation ℝ F (Fin n)) (e : Basis (Fin m) ℝ E)
    (f : Basis (Fin n) ℝ F) :
    rayOfNeZero ℝ ((orEpsB e a * orEpsB f b) • (prodBasis e f).det) (orProdForm_ne_zero e f a b) =
      orProdGen hE hF a b := by
  set e₀ := finBasisOfFinrankEq ℝ E hE with he₀
  set f₀ := finBasisOfFinrankEq ℝ F hF with hf₀
  show _ = rayOfNeZero ℝ ((orEpsB e₀ a * orEpsB f₀ b) • (prodBasis e₀ f₀).det) _
  rw [ray_eq_iff]
  have hdet : (prodBasis e₀ f₀).det = (e₀.det e * f₀.det f) • (prodBasis e f).det := by
    rw [(prodBasis e₀ f₀).det.eq_smul_basis_det (prodBasis e f)]
    congr 1
    exact prodBasis_det_apply e₀ f₀ _ e f 0 (prodBasis_castAdd e f) (prodBasis_natAdd e f)
  rw [hdet, smul_smul]
  apply sameRay_smul_smul_of_mul_nonneg
  have h1 := orEpsB_mul_det_mul_pos e₀ e a
  have h2 := orEpsB_mul_det_mul_pos f₀ f b
  have : orEpsB e a * orEpsB f b * (orEpsB e₀ a * orEpsB f₀ b * (e₀.det e * f₀.det f)) =
      (orEpsB e₀ a * e₀.det e * orEpsB e a) * (orEpsB f₀ b * f₀.det f * orEpsB f b) := by ring
  rw [this]
  exact (mul_pos h1 h2).le

/-- **Characterization of the product orientation**: for positive bases `e` of `a` and `f` of `b`,
the concatenated basis is positive. -/
theorem orProdGen_eq (hE : finrank ℝ E = m) (hF : finrank ℝ F = n) (a : Orientation ℝ E (Fin m))
    (b : Orientation ℝ F (Fin n)) (e : Basis (Fin m) ℝ E) (he : e.orientation = a)
    (f : Basis (Fin n) ℝ F) (hf : f.orientation = b) :
    orProdGen hE hF a b = ((e.prod f).reindex finSumFinEquiv).orientation := by
  rw [← rayOfNeZero_prodBasis hE hF a b e f, Basis.orientation, ray_eq_iff, orEpsB_eq_one he,
    orEpsB_eq_one hf, mul_one, one_smul]
  exact SameRay.rfl

/-- `dim (E × F) = m + n`. -/
theorem finrank_prod_eq (hE : finrank ℝ E = m) (hF : finrank ℝ F = n) :
    finrank ℝ (E × F) = m + n := by
  rw [Module.finrank_prod, hE, hF]

/-! ### Signs of block maps -/

/-- **Block-triangular maps.** A map `(v, w) ↦ (A v, C v + B w)` has sign `sign A · sign B`. -/
theorem orSign_prod_triangular (hE : finrank ℝ E = m) (hF : finrank ℝ F = n)
    (hE' : finrank ℝ E' = m) (hF' : finrank ℝ F' = n) (a : Orientation ℝ E (Fin m))
    (a' : Orientation ℝ E' (Fin m)) (b : Orientation ℝ F (Fin n)) (b' : Orientation ℝ F' (Fin n))
    (A : E →L[ℝ] E') (B : F →L[ℝ] F') (C : E →L[ℝ] F') {T : E × F →L[ℝ] E' × F'}
    (hT : ∀ v w, T (v, w) = (A v, C v + B w)) :
    orSign (orProdGen hE hF a b) (orProdGen hE' hF' a' b') T = orSign a a' A * orSign b b' B := by
  set e := finBasisOfFinrankEq ℝ E hE
  set f := finBasisOfFinrankEq ℝ F hF
  set e' := finBasisOfFinrankEq ℝ E' hE'
  set f' := finBasisOfFinrankEq ℝ F' hF'
  have hω : ((orEpsB e a * orEpsB f b) • (prodBasis e f).det) (prodBasis e f) ≠ 0 := by
    rw [smul_det_apply_self]; exact mul_ne_zero (orEpsB_ne_zero e a) (orEpsB_ne_zero f b)
  have hωe : (orEpsB e a • e.det) e ≠ 0 := by
    rw [smul_det_apply_self]; exact orEpsB_ne_zero e a
  have hωf : (orEpsB f b • f.det) f ≠ 0 := by
    rw [smul_det_apply_self]; exact orEpsB_ne_zero f b
  rw [orSign_eq_sgn_mul (finrank_prod_eq hE hF) _ _ (rayOfNeZero_prodBasis hE hF a b e f)
      (rayOfNeZero_prodBasis hE' hF' a' b' e' f') T hω,
    orSign_eq_sgn_mul hE _ _ (rayOfNeZero_orEpsB_det e a) (rayOfNeZero_orEpsB_det e' a') A hωe,
    orSign_eq_sgn_mul hF _ _ (rayOfNeZero_orEpsB_det f b) (rayOfNeZero_orEpsB_det f' b') B hωf,
    ← sgn_mul]
  congr 1
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul,
    Basis.det_self, mul_one, ContinuousLinearMap.coe_coe]
  rw [prodBasis_det_apply e' f' _ (fun i => A (e i)) (fun i => B (f i)) (fun i => C (e i))
    (fun j => by rw [prodBasis_castAdd, hT, map_zero, add_zero])
    (fun j => by rw [prodBasis_natAdd, hT, map_zero, map_zero, zero_add])]
  ring

/-- **Sign of a product map.** -/
theorem orSign_prodMap (hE : finrank ℝ E = m) (hF : finrank ℝ F = n) (hE' : finrank ℝ E' = m)
    (hF' : finrank ℝ F' = n) (a : Orientation ℝ E (Fin m)) (a' : Orientation ℝ E' (Fin m))
    (b : Orientation ℝ F (Fin n)) (b' : Orientation ℝ F' (Fin n)) (A : E →L[ℝ] E')
    (B : F →L[ℝ] F') :
    orSign (orProdGen hE hF a b) (orProdGen hE' hF' a' b') (A.prodMap B) =
      orSign a a' A * orSign b b' B :=
  orSign_prod_triangular hE hF hE' hF' a a' b b' A B 0 (fun v w => by simp)

/-! ### The swap -/

/-- Powers of the rotation `i ↦ i + 1` of `Fin N`. -/
theorem val_finRotate_pow {N : ℕ} (k : ℕ) (i : Fin N) :
    ((finRotate N ^ k) i : ℕ) = (i + k) % N := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    cases N with
    | zero => exact i.elim0
    | succ N =>
      have hmod : (↑i + (k + 1)) % (N + 1) = ((↑i + k) % (N + 1) + 1) % (N + 1) := by
        rw [Nat.mod_add_mod, Nat.add_assoc]
      rw [coe_finRotate, hmod, ← ih]
      split_ifs with h
      · rw [h, Fin.val_last, Nat.mod_self]
      · have h' : ((finRotate (N + 1) ^ k) i : ℕ) ≠ N := fun h' => h (Fin.ext (by simpa using h'))
        have hlt := ((finRotate (N + 1) ^ k) i).isLt
        rw [Nat.mod_eq_of_lt (by omega)]

/-- The block flip of `Fin (n + m)` is the rotation by `n`. -/
theorem finCongr_trans_finAddFlip (m n : ℕ) :
    (finCongr (Nat.add_comm n m)).trans finAddFlip = finRotate (n + m) ^ n := by
  ext ⟨k, hk⟩
  rw [val_finRotate_pow, Equiv.trans_apply, finCongr_apply_mk]
  by_cases hkm : k < m
  · rw [finAddFlip_apply_mk_left hkm]
    simp only
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [finAddFlip_apply_mk_right (not_lt.1 hkm) (by omega)]
    simp only
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The sign of the block flip is `(-1)^(m n)`. -/
theorem sign_finCongr_trans_finAddFlip (m n : ℕ) :
    Equiv.Perm.sign ((finCongr (Nat.add_comm n m)).trans finAddFlip) = (-1) ^ (m * n) := by
  rw [finCongr_trans_finAddFlip, map_pow, sign_finRotate, ← pow_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have : (n' + 1 + m - 1) * (n' + 1) = m * (n' + 1) + (n' + 1) * n' := by
      rw [show n' + 1 + m - 1 = n' + m by omega]; ring
    have hev : Even ((n' + 1) * n') := by simpa using Nat.even_mul_pred_self (n' + 1)
    rw [this, pow_add, hev.neg_one_pow, mul_one]

/-- `sgn ((-1)^k) = (-1)^k`. -/
theorem sgn_neg_one_pow (k : ℕ) : sgn ((-1 : ℝ) ^ k) = (-1) ^ k := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_one_pow, hk.neg_one_pow, sgn_one]
  · rw [hk.neg_one_pow, hk.neg_one_pow, sgn_neg (by norm_num)]

/-- **The swap** `E × F → F × E` has sign `(-1)^(m n)`.  The product orientation of `F × E` is
indexed by `Fin (n + m)`; it is transported to `Fin (m + n)` along `n + m = m + n`. -/
theorem orSign_swap (hE : finrank ℝ E = m) (hF : finrank ℝ F = n) (a : Orientation ℝ E (Fin m))
    (b : Orientation ℝ F (Fin n)) :
    orSign (orProdGen hE hF a b)
      (Orientation.reindex ℝ (F × E) (finCongr (Nat.add_comm n m)) (orProdGen hF hE b a))
      ((ContinuousLinearMap.snd ℝ E F).prod (ContinuousLinearMap.fst ℝ E F)) = (-1) ^ (m * n) := by
  set e := finBasisOfFinrankEq ℝ E hE
  set f := finBasisOfFinrankEq ℝ F hF
  have hω : ((orEpsB e a * orEpsB f b) • (prodBasis e f).det) (prodBasis e f) ≠ 0 := by
    rw [smul_det_apply_self]; exact mul_ne_zero (orEpsB_ne_zero e a) (orEpsB_ne_zero f b)
  have hη : ((orEpsB f b * orEpsB e a) • (prodBasis f e).det).domDomCongr
      (finCongr (Nat.add_comm n m)) ≠ 0 :=
    mt ((AlternatingMap.domDomCongr_eq_zero_iff _ _).1) (orProdForm_ne_zero f e b a)
  have hrep : rayOfNeZero ℝ _ hη =
      Orientation.reindex ℝ (F × E) (finCongr (Nat.add_comm n m)) (orProdGen hF hE b a) := by
    rw [← rayOfNeZero_prodBasis hF hE b a f e, Orientation.reindex_apply]
  rw [orSign_eq_sgn_mul (finrank_prod_eq hE hF) _ _ (rayOfNeZero_prodBasis hE hF a b e f) hrep _ hω]
  have hswap : (fun i => ((ContinuousLinearMap.snd ℝ E F).prod (ContinuousLinearMap.fst ℝ E F))
      (prodBasis e f i)) = prodBasis f e ∘ finAddFlip := by
    funext i
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · simp [prodBasis_castAdd, finAddFlip_apply_castAdd, prodBasis_natAdd]
    · simp [prodBasis_natAdd, finAddFlip_apply_natAdd, prodBasis_castAdd]
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.domDomCongr_apply,
    AlternatingMap.smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe, Basis.det_self, mul_one]
  rw [hswap, show (prodBasis f e ∘ finAddFlip) ∘ finCongr (Nat.add_comm n m) =
    prodBasis f e ∘ ⇑((finCongr (Nat.add_comm n m)).trans finAddFlip) from rfl,
    AlternatingMap.map_perm, sign_finCongr_trans_finAddFlip, Basis.det_self]
  have hne : orEpsB e a * orEpsB f b ≠ 0 := mul_ne_zero (orEpsB_ne_zero e a) (orEpsB_ne_zero f b)
  rw [show orEpsB f b * orEpsB e a * ((-1 : ℤˣ) ^ (m * n) • (1 : ℝ)) * (orEpsB e a * orEpsB f b) =
    (orEpsB e a * orEpsB f b) * (orEpsB e a * orEpsB f b) * (-1 : ℝ) ^ (m * n) by
      rw [Units.smul_def, zsmul_eq_mul]; push_cast; ring,
    sgn_sq_mul hne, sgn_neg_one_pow]

omit [FiniteDimensional ℝ F] in
/-- The sign is unchanged when both orientations are transported along `k = k'`. -/
theorem orSign_reindex_finCongr {k k' : ℕ} (h : k = k') (a : Orientation ℝ E (Fin k))
    (b : Orientation ℝ F (Fin k)) (T : E →L[ℝ] F) :
    orSign (Orientation.reindex ℝ E (finCongr h) a) (Orientation.reindex ℝ F (finCongr h) b) T =
      orSign a b T := by
  subst h
  simp [finCongr_refl]

end linear

/-! ### Products of oriented manifolds -/

section manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners ℝ F' G'}
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N'] {m n : ℕ}

/-- The product orientation of `M × N`. -/
def Orient.prod [IsManifold I ∞ M] [IsManifold J ∞ N] (hE : finrank ℝ E = m)
    (hF : finrank ℝ F = n) (oM : Orient I M m) (oN : Orient J N n) :
    Orient (I.prod J) (M × N) (m + n) where
  or p := orProdGen hE hF (oM.or p.1) (oN.or p.2)
  cont := by
    rintro ⟨x, y⟩
    have h1 := (show ∀ᶠ q in 𝓝 x, q ∈ (extChartAt I x).source from
      extChartAt_source_mem_nhds x).and (oM.cont x)
    have h2 := (show ∀ᶠ q in 𝓝 y, q ∈ (extChartAt J y).source from
      extChartAt_source_mem_nhds y).and (oN.cont y)
    have h := ((continuousAt_fst (p := (x, y))).eventually h1).and
      ((continuousAt_snd (p := (x, y))).eventually h2)
    filter_upwards [h] with p hp
    obtain ⟨⟨hp1, hs1⟩, ⟨hp2, hs2⟩⟩ := hp
    have hDe := hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, E)) ((contMDiffAt_extChartAt' (I := I)
      (n := ∞) (x := x)
      (by rwa [← extChartAt_source I] : p.1 ∈ (chartAt H x).source)).mdifferentiableAt (by simp))
    have hDf := hasMFDerivAt_mfd (I := J) (J := 𝓘(ℝ, F)) ((contMDiffAt_extChartAt' (I := J)
      (n := ∞) (x := y)
      (by rwa [← extChartAt_source J] : p.2 ∈ (chartAt G y).source)).mdifferentiableAt (by simp))
    have hD0 := hDe.prodMap hDf
    have hchart : ⇑(extChartAt (I.prod J) (x, y)) =
        Prod.map (extChartAt I x) (extChartAt J y) := by
      rw [extChartAt_prod]; rfl
    have hD : HasMFDerivAt (I.prod J) 𝓘(ℝ, E × F) (extChartAt (I.prod J) (x, y)) p
        (((mfd I 𝓘(ℝ, E) (extChartAt I x) p.1).prodMap (mfd J 𝓘(ℝ, F) (extChartAt J y) p.2) :
          E × F →L[ℝ] E × F)) := by
      rw [modelWithCornersSelf_prod, hchart]; exact hD0
    rw [HasMFDerivAt.mfd_eq hD]
    show orSign (orProdGen hE hF (oM.or p.1) (oN.or p.2))
      (orProdGen hE hF (oM.or x) (oN.or y)) _ = 1
    rw [orSign_prodMap hE hF hE hF, hs1, hs2, mul_one]

/-- The orientation of `M × N` at `p` is the product of the orientations at `p.1` and `p.2`. -/
@[simp]
theorem Orient.prod_or [IsManifold I ∞ M] [IsManifold J ∞ N] (hE : finrank ℝ E = m)
    (hF : finrank ℝ F = n) (oM : Orient I M m) (oN : Orient J N n) (p : M × N) :
    (oM.prod hE hF oN).or p = orProdGen hE hF (oM.or p.1) (oN.or p.2) :=
  rfl

/-- **Sign of a product of maps.** -/
theorem signAt_prodMap [IsManifold I ∞ M] [IsManifold J ∞ N] [IsManifold I' ∞ M']
    [IsManifold J' ∞ N'] (hE : finrank ℝ E = m) (hF : finrank ℝ F = n) (hE' : finrank ℝ E' = m)
    (hF' : finrank ℝ F' = n) (oM : Orient I M m) (oN : Orient J N n) (oM' : Orient I' M' m)
    (oN' : Orient J' N' n) {φ : M → M'} {ψ : N → N'} {p : M × N}
    (hφ : MDifferentiableAt I I' φ p.1) (hψ : MDifferentiableAt J J' ψ p.2) :
    signAt (oM.prod hE hF oN) (oM'.prod hE' hF' oN') (Prod.map φ ψ) p =
      signAt oM oM' φ p.1 * signAt oN oN' ψ p.2 := by
  have hD : HasMFDerivAt (I.prod J) (I'.prod J') (Prod.map φ ψ) p
      (((mfd I I' φ p.1).prodMap (mfd J J' ψ p.2) : E × F →L[ℝ] E' × F')) :=
    (hasMFDerivAt_mfd hφ).prodMap (hasMFDerivAt_mfd hψ)
  unfold signAt
  rw [HasMFDerivAt.mfd_eq hD]
  exact orSign_prodMap hE hF hE' hF' _ _ _ _ _ _

/-! ### Transport along an equality of dimensions, and the swap of factors -/

/-- An orientation with dimension index `k`, viewed with index `k'` for `k = k'`. -/
def Orient.cast {k k' : ℕ} (h : k = k') (o : Orient I M k) : Orient I M k' where
  or x := Orientation.reindex ℝ E (finCongr h) (o.or x)
  cont x := by
    subst h
    simpa [finCongr_refl] using o.cont x

@[simp]
theorem Orient.cast_or {k k' : ℕ} (h : k = k') (o : Orient I M k) (x : M) :
    (o.cast h).or x = Orientation.reindex ℝ E (finCongr h) (o.or x) :=
  rfl

/-- Transporting both orientations along `k = k'` does not change the sign. -/
theorem signAt_cast {k k' : ℕ} (h : k = k') (oM : Orient I M k) (oN : Orient J N k) (f : M → N)
    (x : M) : signAt (oM.cast h) (oN.cast h) f x = signAt oM oN f x :=
  orSign_reindex_finCongr h _ _ _

/-- **The swap** `M × N → N × M` has sign `(-1)^(m n)` everywhere (the product orientation of
`N × M`, of index `n + m`, is transported to index `m + n`). -/
theorem signAt_swap [IsManifold I ∞ M] [IsManifold J ∞ N] (hE : finrank ℝ E = m)
    (hF : finrank ℝ F = n) (oM : Orient I M m) (oN : Orient J N n) (p : M × N) :
    signAt (oM.prod hE hF oN) ((oN.prod hF hE oM).cast (Nat.add_comm n m)) Prod.swap p =
      (-1) ^ (m * n) := by
  have hD : HasMFDerivAt (I.prod J) (J.prod I) Prod.swap p
      (((ContinuousLinearMap.snd ℝ E F).prod (ContinuousLinearMap.fst ℝ E F) :
        E × F →L[ℝ] F × E)) :=
    (hasMFDerivAt_snd p).prodMk (hasMFDerivAt_fst p)
  unfold signAt
  rw [HasMFDerivAt.mfd_eq hD]
  exact orSign_swap hE hF _ _

end manifold

end Milnor
