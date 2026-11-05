import Mathlib

/-!
# Orientations of finite-dimensional spaces and the sign of a linear map

Mathlib has `Orientation ℝ E (Fin n)` (a ray of alternating `n`-forms) but no notion of the
*sign* of a linear map `T : E → F` between oriented spaces of the same dimension.  We define it
through top-degree forms: if `ω` represents the orientation of `E` and `η` that of `F`, then the
pullback `η ∘ T` is a multiple `c • ω`, and `orSign a b T := sgn c` (`0` if `T` is singular).

We also build the orientation of `E × ℝ` induced by one of `E` (`orProd`), and prove the two
determinant formulas needed in Chapter 5: for a block-triangular map `(v, t) ↦ (A v + t w, c t)`
the sign is `orSign A * sgn c`; and for two maps `E → F × ℝ` with the same first component `P`,
the product of the signs is the sign of the product of their second components on a kernel
vector of `P`.
-/

open Module Set Function

noncomputable section

namespace Milnor

/-! ### The sign of a real number, as an integer -/

/-- The sign of a real number, as an integer. -/
def sgn (x : ℝ) : ℤ := if 0 < x then 1 else if x < 0 then -1 else 0

theorem sgn_pos {x : ℝ} (h : 0 < x) : sgn x = 1 := if_pos h
theorem sgn_neg {x : ℝ} (h : x < 0) : sgn x = -1 := by
  rw [sgn, if_neg (not_lt.2 h.le), if_pos h]
@[simp] theorem sgn_zero : sgn 0 = 0 := by simp [sgn]
theorem sgn_one : sgn 1 = 1 := sgn_pos one_pos

theorem sgn_mul (x y : ℝ) : sgn (x * y) = sgn x * sgn y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [sgn_neg hx, sgn_neg hy, sgn_pos (mul_pos_of_neg_of_neg hx hy)]; norm_num
    · simp
    · rw [sgn_neg hx, sgn_pos hy, sgn_neg (mul_neg_of_neg_of_pos hx hy)]; norm_num
  · simp
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [sgn_pos hx, sgn_neg hy, sgn_neg (mul_neg_of_pos_of_neg hx hy)]; norm_num
    · simp
    · rw [sgn_pos hx, sgn_pos hy, sgn_pos (mul_pos hx hy)]; norm_num

theorem sgn_eq_zero_iff {x : ℝ} : sgn x = 0 ↔ x = 0 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [sgn_neg hx]; simp [hx.ne]
  · simp
  · rw [sgn_pos hx]; simp [hx.ne']

theorem sgn_ne_zero_iff {x : ℝ} : sgn x ≠ 0 ↔ x ≠ 0 := sgn_eq_zero_iff.not

theorem sgn_neg' (x : ℝ) : sgn (-x) = -sgn x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [sgn_neg hx, sgn_pos (neg_pos.2 hx)]; norm_num
  · simp
  · rw [sgn_pos hx, sgn_neg (neg_neg_of_pos hx)]

theorem sgn_mul_self {x : ℝ} (hx : x ≠ 0) : sgn (x * x) = 1 := sgn_pos (mul_self_pos.2 hx)

theorem sgn_sq_mul {x : ℝ} (hx : x ≠ 0) (y : ℝ) : sgn (x * x * y) = sgn y := by
  rw [sgn_mul, sgn_mul_self hx, one_mul]

theorem sgn_mem {x : ℝ} : sgn x = 1 ∨ sgn x = -1 ∨ sgn x = 0 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · right; left; exact sgn_neg hx
  · right; right; exact sgn_zero
  · left; exact sgn_pos hx

theorem sgn_mul_sgn_self (x : ℝ) : sgn x * sgn x = if x = 0 then 0 else 1 := by
  rcases sgn_mem (x := x) with h | h | h
  · rw [h]; simp [(sgn_ne_zero_iff.1 (by rw [h]; decide))]
  · rw [h]; simp [(sgn_ne_zero_iff.1 (by rw [h]; decide))]
  · rw [h, sgn_eq_zero_iff.1 h]; simp

/-! ### Top-degree forms -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {n : ℕ}

theorem exists_ne_zero_of_ne_zero {ι : Type*} {ω : E [⋀^ι]→ₗ[ℝ] ℝ} (h : ω ≠ 0) :
    ∃ v, ω v ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  exact h (AlternatingMap.ext hcon)

theorem smul_compLinearMap {ι : Type*} (c : ℝ) (ω : E [⋀^ι]→ₗ[ℝ] ℝ) (g : F →ₗ[ℝ] E) :
    (c • ω).compLinearMap g = c • ω.compLinearMap g := by
  ext v; simp

theorem neg_compLinearMap {ι : Type*} (ω : E [⋀^ι]→ₗ[ℝ] ℝ) (g : F →ₗ[ℝ] E) :
    (-ω).compLinearMap g = -ω.compLinearMap g := by
  ext v; simp

theorem neg_eq_neg_smul_of {ι : Type*} {α ω : E [⋀^ι]→ₗ[ℝ] ℝ} {c : ℝ} (h : α = c • ω) :
    -α = (-c) • ω := by
  ext v
  have := DFunLike.congr_fun h v
  simp only [AlternatingMap.neg_apply, AlternatingMap.smul_apply, smul_eq_mul] at this ⊢
  rw [this]; ring

/-- Any two top-degree forms are proportional. -/
theorem exists_eq_smul_of_finrank (hE : finrank ℝ E = n) {ω : E [⋀^Fin n]→ₗ[ℝ] ℝ} (hω : ω ≠ 0)
    (α : E [⋀^Fin n]→ₗ[ℝ] ℝ) : ∃ c : ℝ, α = c • ω := by
  let e := finBasisOfFinrankEq ℝ E hE
  have h1 := ω.eq_smul_basis_det e
  have h2 := α.eq_smul_basis_det e
  have hωe : ω e ≠ 0 := fun h => hω (by rw [h1, h, zero_smul])
  refine ⟨α e / ω e, ?_⟩
  calc α = α e • e.det := h2
    _ = (α e / ω e) • (ω e • e.det) := by rw [smul_smul, div_mul_cancel₀ _ hωe]
    _ = (α e / ω e) • ω := by rw [← h1]

/-- A nonzero top-degree form is nonzero on every basis. -/
theorem ne_zero_of_basis {ω : E [⋀^Fin n]→ₗ[ℝ] ℝ} (hω : ω ≠ 0) (e : Basis (Fin n) ℝ E) :
    ω e ≠ 0 := fun h => hω (by rw [ω.eq_smul_basis_det e, h, zero_smul])

/-! ### The sign of a linear map -/

/-- A tuple on which the representative form of `a` does not vanish. -/
def orTuple (a : Orientation ℝ E (Fin n)) : Fin n → E :=
  Classical.choose (exists_ne_zero_of_ne_zero a.someVector_ne_zero)

theorem someVector_orTuple_ne_zero (a : Orientation ℝ E (Fin n)) :
    a.someVector (orTuple a) ≠ 0 :=
  Classical.choose_spec (exists_ne_zero_of_ne_zero a.someVector_ne_zero)

/-- The sign of `T : E → F` relative to orientations `a` of `E` and `b` of `F`: `1` if `T`
carries `a` to `b`, `-1` if to `-b`, `0` if `T` is singular (for `dim E = dim F = n`). -/
def orSign (a : Orientation ℝ E (Fin n)) (b : Orientation ℝ F (Fin n)) (T : E →L[ℝ] F) : ℤ :=
  sgn ((b.someVector.compLinearMap T.toLinearMap) (orTuple a) * a.someVector (orTuple a))

/-- The defining property: if `η ∘ T = c • ω` for representatives `ω` of `a` and `η` of `b`,
then `orSign a b T = sgn c`. -/
theorem orSign_eq_sgn {a : Orientation ℝ E (Fin n)} {b : Orientation ℝ F (Fin n)}
    {ω : E [⋀^Fin n]→ₗ[ℝ] ℝ} {η : F [⋀^Fin n]→ₗ[ℝ] ℝ} (hω : ω ≠ 0) (hη : η ≠ 0)
    (ha : rayOfNeZero ℝ ω hω = a) (hb : rayOfNeZero ℝ η hη = b) {T : E →L[ℝ] F} {c : ℝ}
    (hc : η.compLinearMap T.toLinearMap = c • ω) : orSign a b T = sgn c := by
  have h1 : SameRay ℝ ω a.someVector :=
    (ray_eq_iff hω a.someVector_ne_zero).1 (by rw [ha, Module.Ray.someVector_ray])
  obtain ⟨r, hr, hrω⟩ := h1.exists_pos_left hω a.someVector_ne_zero
  have h2 : SameRay ℝ η b.someVector :=
    (ray_eq_iff hη b.someVector_ne_zero).1 (by rw [hb, Module.Ray.someVector_ray])
  obtain ⟨s, hs, hsη⟩ := h2.exists_pos_left hη b.someVector_ne_zero
  have hv := someVector_orTuple_ne_zero a
  rw [← hrω] at hv
  simp only [AlternatingMap.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or] at hv
  rw [orSign, ← hrω, ← hsη, smul_compLinearMap, hc]
  simp only [AlternatingMap.smul_apply, smul_eq_mul]
  have : s * (c * ω (orTuple a)) * (r * ω (orTuple a)) =
      (s * r * (ω (orTuple a) * ω (orTuple a))) * c := by ring
  rw [this, sgn_mul, sgn_pos (mul_pos (mul_pos hs hr) (mul_self_pos.2 hv.2)), one_mul]

/-- The sign as the sign of a product of values (`dim E = n`). -/
theorem orSign_eq_sgn_mul (hE : finrank ℝ E = n) {a : Orientation ℝ E (Fin n)}
    {b : Orientation ℝ F (Fin n)} {ω : E [⋀^Fin n]→ₗ[ℝ] ℝ} {η : F [⋀^Fin n]→ₗ[ℝ] ℝ}
    (hω : ω ≠ 0) (hη : η ≠ 0) (ha : rayOfNeZero ℝ ω hω = a) (hb : rayOfNeZero ℝ η hη = b)
    (T : E →L[ℝ] F) {v : Fin n → E} (hv : ω v ≠ 0) :
    orSign a b T = sgn ((η.compLinearMap T.toLinearMap) v * ω v) := by
  obtain ⟨c, hc⟩ := exists_eq_smul_of_finrank hE hω (η.compLinearMap T.toLinearMap)
  rw [orSign_eq_sgn hω hη ha hb hc, hc]
  simp only [AlternatingMap.smul_apply, smul_eq_mul]
  rw [show c * ω v * ω v = ω v * ω v * c by ring, sgn_sq_mul hv]

theorem someVector_ray' (a : Orientation ℝ E (Fin n)) :
    rayOfNeZero ℝ a.someVector a.someVector_ne_zero = a := Module.Ray.someVector_ray a

/-- Multiplicativity of the sign under composition (`dim E = dim F = n`). -/
theorem orSign_comp (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (a : Orientation ℝ E (Fin n))
    (b : Orientation ℝ F (Fin n)) (c : Orientation ℝ G (Fin n)) (T : E →L[ℝ] F) (S : F →L[ℝ] G) :
    orSign a c (S.comp T) = orSign b c S * orSign a b T := by
  obtain ⟨c₁, hc₁⟩ := exists_eq_smul_of_finrank hE a.someVector_ne_zero
    (b.someVector.compLinearMap T.toLinearMap)
  obtain ⟨c₂, hc₂⟩ := exists_eq_smul_of_finrank hF b.someVector_ne_zero
    (c.someVector.compLinearMap S.toLinearMap)
  have h3 : c.someVector.compLinearMap (S.comp T).toLinearMap = (c₂ * c₁) • a.someVector := by
    have : (S.comp T).toLinearMap = S.toLinearMap.comp T.toLinearMap := rfl
    rw [this, ← AlternatingMap.compLinearMap_assoc, hc₂, smul_compLinearMap, hc₁, smul_smul]
  rw [orSign_eq_sgn _ _ (someVector_ray' a) (someVector_ray' c) h3,
    orSign_eq_sgn _ _ (someVector_ray' b) (someVector_ray' c) hc₂,
    orSign_eq_sgn _ _ (someVector_ray' a) (someVector_ray' b) hc₁, sgn_mul]

theorem orSign_id (a : Orientation ℝ E (Fin n)) : orSign a a (ContinuousLinearMap.id ℝ E) = 1 := by
  rw [orSign_eq_sgn _ _ (someVector_ray' a) (someVector_ray' a)
    (c := 1) (by rw [ContinuousLinearMap.coe_id, AlternatingMap.compLinearMap_id, one_smul])]
  exact sgn_one

theorem orSign_neg_right (hE : finrank ℝ E = n) (a : Orientation ℝ E (Fin n))
    (b : Orientation ℝ F (Fin n)) (T : E →L[ℝ] F) : orSign a (-b) T = -orSign a b T := by
  obtain ⟨c, hc⟩ := exists_eq_smul_of_finrank hE a.someVector_ne_zero
    (b.someVector.compLinearMap T.toLinearMap)
  have hb' : rayOfNeZero ℝ (-b.someVector)
      (fun h => b.someVector_ne_zero (neg_eq_zero.1 h)) = -b := by
    rw [← neg_rayOfNeZero (R := ℝ) b.someVector b.someVector_ne_zero, someVector_ray']
  rw [orSign_eq_sgn _ _ (someVector_ray' a) hb' (c := -c)
    (by rw [neg_compLinearMap]; exact neg_eq_neg_smul_of hc),
    orSign_eq_sgn _ _ (someVector_ray' a) (someVector_ray' b) hc, sgn_neg']

theorem orSign_neg_left (hE : finrank ℝ E = n) (a : Orientation ℝ E (Fin n))
    (b : Orientation ℝ F (Fin n)) (T : E →L[ℝ] F) : orSign (-a) b T = -orSign a b T := by
  obtain ⟨c, hc⟩ := exists_eq_smul_of_finrank hE a.someVector_ne_zero
    (b.someVector.compLinearMap T.toLinearMap)
  have ha' : rayOfNeZero ℝ (-a.someVector)
      (fun h => a.someVector_ne_zero (neg_eq_zero.1 h)) = -a := by
    rw [← neg_rayOfNeZero (R := ℝ) a.someVector a.someVector_ne_zero, someVector_ray']
  have hc' : b.someVector.compLinearMap T.toLinearMap = (-c) • (-a.someVector) := by
    rw [hc]; ext v; simp
  rw [orSign_eq_sgn _ _ ha' (someVector_ray' b) hc',
    orSign_eq_sgn _ _ (someVector_ray' a) (someVector_ray' b) hc, sgn_neg']

/-- The sign is nonzero exactly when the map is bijective (`dim E = dim F = n`). -/
theorem orSign_ne_zero_iff (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (a : Orientation ℝ E (Fin n)) (b : Orientation ℝ F (Fin n)) (T : E →L[ℝ] F) :
    orSign a b T ≠ 0 ↔ Function.Bijective T := by
  classical
  obtain ⟨c, hc⟩ := exists_eq_smul_of_finrank hE a.someVector_ne_zero
    (b.someVector.compLinearMap T.toLinearMap)
  rw [orSign_eq_sgn _ _ (someVector_ray' a) (someVector_ray' b) hc, sgn_ne_zero_iff]
  let e := finBasisOfFinrankEq ℝ E hE
  let f := finBasisOfFinrankEq ℝ F hF
  have hηf : b.someVector f ≠ 0 := ne_zero_of_basis b.someVector_ne_zero f
  set Te : Fin n → F := fun i => T (e i) with hTe
  have key : c ≠ 0 ↔ f.det Te ≠ 0 := by
    have h1 := DFunLike.congr_fun hc (⇑e)
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at h1
    change b.someVector Te = c * a.someVector e at h1
    have h2 : b.someVector Te = b.someVector f * f.det Te := by
      conv_lhs => rw [b.someVector.eq_smul_basis_det f]
      simp
    have h3 : a.someVector e ≠ 0 := ne_zero_of_basis a.someVector_ne_zero e
    rw [h2] at h1
    constructor
    · intro hc0 hdet
      rw [hdet, mul_zero] at h1
      exact hc0 (by
        have := mul_eq_zero.1 h1.symm
        rcases this with h | h
        · exact h
        · exact absurd h h3)
    · intro hdet hc0
      rw [hc0, zero_mul] at h1
      exact hdet (by
        have := mul_eq_zero.1 h1
        rcases this with h | h
        · exact absurd h hηf
        · exact h)
  rw [key]
  constructor
  · intro hdet
    have hb : LinearIndependent ℝ Te ∧ Submodule.span ℝ (Set.range Te) = ⊤ :=
      f.is_basis_iff_det.2 (isUnit_iff_ne_zero.2 hdet)
    have hsurj : Function.Surjective T := by
      show Function.Surjective T.toLinearMap
      rw [← LinearMap.range_eq_top]
      rw [eq_top_iff, ← hb.2, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := T.toLinearMap)
      (hE.trans hF.symm)).2 hsurj, hsurj⟩
  · intro hT
    let L := LinearEquiv.ofBijective T.toLinearMap hT
    have : Te = e.map L := by
      ext i; rfl
    rw [this]
    exact (f.isUnit_det (e.map L)).ne_zero

/-! ### Representatives from bases -/

open Classical in
/-- The sign `±1` relating the orientation `a` to that of the basis `e`. -/
def orEpsB {m : ℕ} (e : Basis (Fin m) ℝ E) (a : Orientation ℝ E (Fin m)) : ℝ :=
  if e.orientation = a then 1 else -1

theorem orEpsB_ne_zero {m : ℕ} (e : Basis (Fin m) ℝ E) (a : Orientation ℝ E (Fin m)) :
    orEpsB e a ≠ 0 := by
  unfold orEpsB; split_ifs <;> norm_num

theorem orEpsB_eq_one {m : ℕ} {e : Basis (Fin m) ℝ E} {a : Orientation ℝ E (Fin m)}
    (h : e.orientation = a) : orEpsB e a = 1 := by unfold orEpsB; rw [if_pos h]

theorem orEpsB_eq_neg_one {m : ℕ} {e : Basis (Fin m) ℝ E} {a : Orientation ℝ E (Fin m)}
    (h : a = -e.orientation) : orEpsB e a = -1 := by
  unfold orEpsB; rw [if_neg]; rw [h]; exact (Module.Ray.ne_neg_self _)

theorem smul_det_apply_self {m : ℕ} (c : ℝ) (e : Basis (Fin m) ℝ E) : (c • e.det) e = c := by
  simp [e.det_self]

theorem orEpsB_smul_det_ne_zero {m : ℕ} (e : Basis (Fin m) ℝ E) (a : Orientation ℝ E (Fin m)) :
    orEpsB e a • e.det ≠ 0 := smul_ne_zero (orEpsB_ne_zero e a) e.det_ne_zero

/-- `orEpsB e a • e.det` represents `a`. -/
theorem rayOfNeZero_orEpsB_det {m : ℕ} (e : Basis (Fin m) ℝ E) (a : Orientation ℝ E (Fin m)) :
    rayOfNeZero ℝ (orEpsB e a • e.det) (orEpsB_smul_det_ne_zero e a) = a := by
  rcases e.orientation_eq_or_eq_neg a with h | h
  · subst h
    show rayOfNeZero ℝ _ _ = rayOfNeZero ℝ e.det e.det_ne_zero
    rw [ray_eq_iff, orEpsB_eq_one rfl, one_smul]
  · subst h
    show rayOfNeZero ℝ _ _ = -rayOfNeZero ℝ e.det e.det_ne_zero
    rw [neg_rayOfNeZero (R := ℝ), ray_eq_iff, orEpsB_eq_neg_one rfl]
    have : (-1 : ℝ) • e.det = -e.det := by ext; simp
    rw [this]

theorem orEpsB_apply_self {m : ℕ} (e : Basis (Fin m) ℝ E) (a : Orientation ℝ E (Fin m)) :
    (orEpsB e a • e.det) e = orEpsB e a := by simp [e.det_self]

/-! ### The orientation of `E × ℝ` -/

/-- `Fin n ⊕ Unit ≃ Fin (n + 1)`, sending `inl i` to `castSucc i` and `inr ()` to `last n`. -/
def sumUnitEquiv (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

theorem sumUnitEquiv_inl (i : Fin n) : sumUnitEquiv n (Sum.inl i) = Fin.castSucc i := by
  simp only [sumUnitEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply,
    finSumFinEquiv_apply_left]
  rfl

theorem sumUnitEquiv_inr : sumUnitEquiv n (Sum.inr ()) = Fin.last n := by
  simp only [sumUnitEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]
  ext; simp

theorem sumUnitEquiv_symm_castSucc (i : Fin n) :
    (sumUnitEquiv n).symm (Fin.castSucc i) = Sum.inl i := by
  rw [Equiv.symm_apply_eq, sumUnitEquiv_inl]

theorem sumUnitEquiv_symm_last : (sumUnitEquiv n).symm (Fin.last n) = Sum.inr () := by
  rw [Equiv.symm_apply_eq, sumUnitEquiv_inr]

/-- The basis `(e₁,0), …, (eₙ,0), (0,1)` of `E × ℝ`. -/
def prodRealBasis (e : Basis (Fin n) ℝ E) : Basis (Fin (n + 1)) ℝ (E × ℝ) :=
  (e.prod (Basis.singleton Unit ℝ)).reindex (sumUnitEquiv n)

theorem prodRealBasis_repr (e : Basis (Fin n) ℝ E) (x : E × ℝ) (i : Fin (n + 1)) :
    (prodRealBasis e).repr x i = (e.prod (Basis.singleton Unit ℝ)).repr x ((sumUnitEquiv n).symm i) :=
  Basis.repr_reindex_apply _ _ _ _

theorem prodRealBasis_apply (e : Basis (Fin n) ℝ E) (i : Fin (n + 1)) :
    prodRealBasis e i = e.prod (Basis.singleton Unit ℝ) ((sumUnitEquiv n).symm i) :=
  Basis.reindex_apply _ _ _

theorem prodRealBasis_castSucc (e : Basis (Fin n) ℝ E) (i : Fin n) :
    prodRealBasis e (Fin.castSucc i) = (e i, 0) := by
  rw [prodRealBasis_apply, sumUnitEquiv_symm_castSucc]
  exact Prod.ext (Basis.prod_apply_inl_fst _ _ _) (Basis.prod_apply_inl_snd _ _ _)

theorem prodRealBasis_last (e : Basis (Fin n) ℝ E) : prodRealBasis e (Fin.last n) = (0, 1) := by
  rw [prodRealBasis_apply, sumUnitEquiv_symm_last]
  refine Prod.ext (Basis.prod_apply_inr_fst _ _ _) ?_
  rw [Basis.prod_apply_inr_snd, Basis.singleton_apply]

theorem prodRealBasis_repr_castSucc (e : Basis (Fin n) ℝ E) (x : E × ℝ) (i : Fin n) :
    (prodRealBasis e).repr x (Fin.castSucc i) = e.repr x.1 i := by
  rw [prodRealBasis_repr, sumUnitEquiv_symm_castSucc, Basis.prod_repr_inl]

theorem prodRealBasis_repr_last (e : Basis (Fin n) ℝ E) (x : E × ℝ) :
    (prodRealBasis e).repr x (Fin.last n) = x.2 := by
  rw [prodRealBasis_repr, sumUnitEquiv_symm_last, Basis.prod_repr_inr, Basis.singleton_repr]

theorem orProd_rep_ne_zero (hE : finrank ℝ E = n) (a : Orientation ℝ E (Fin n)) :
    orEpsB (finBasisOfFinrankEq ℝ E hE) a • (prodRealBasis (finBasisOfFinrankEq ℝ E hE)).det ≠ 0 :=
  smul_ne_zero (orEpsB_ne_zero (finBasisOfFinrankEq ℝ E hE) a)
    (prodRealBasis (finBasisOfFinrankEq ℝ E hE)).det_ne_zero

/-- The orientation of `E × ℝ` induced by an orientation `a` of `E`: a positive basis of `E`
followed by `(0, 1)` is positive.  It is represented by `orEpsB e a • (prodRealBasis e).det`
for the reference basis `e`. -/
def orProd (hE : finrank ℝ E = n) (a : Orientation ℝ E (Fin n)) :
    Orientation ℝ (E × ℝ) (Fin (n + 1)) :=
  rayOfNeZero ℝ _ (orProd_rep_ne_zero hE a)

theorem rayOfNeZero_orProd (hE : finrank ℝ E = n) (a : Orientation ℝ E (Fin n)) :
    rayOfNeZero ℝ (orEpsB (finBasisOfFinrankEq ℝ E hE) a •
      (prodRealBasis (finBasisOfFinrankEq ℝ E hE)).det) (orProd_rep_ne_zero hE a) = orProd hE a :=
  rfl

theorem finrank_prod_real (hE : finrank ℝ E = n) : finrank ℝ (E × ℝ) = n + 1 := by
  rw [Module.finrank_prod, hE, Module.finrank_self]

/-- **Block-triangular formula.** If `T (v, t) = (A v + t • w, c * t)` then
`orSign (orProd a) (orProd b) T = orSign a b A * sgn c`. -/
theorem orSign_orProd (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (a : Orientation ℝ E (Fin n))
    (b : Orientation ℝ F (Fin n)) (T : E × ℝ →L[ℝ] F × ℝ) (A : E →L[ℝ] F) (w : F) (c : ℝ)
    (hT : ∀ v t, T (v, t) = (A v + t • w, c * t)) :
    orSign (orProd hE a) (orProd hF b) T = orSign a b A * sgn c := by
  set e := finBasisOfFinrankEq ℝ E hE with he
  set f := finBasisOfFinrankEq ℝ F hF with hf
  have hωe : (orEpsB e a • e.det) e ≠ 0 := by rw [orEpsB_apply_self]; exact orEpsB_ne_zero e a
  have hωe' : (orEpsB e a • (prodRealBasis e).det) (prodRealBasis e) ≠ 0 := by
    rw [smul_det_apply_self]; exact orEpsB_ne_zero e a
  rw [orSign_eq_sgn_mul (finrank_prod_real hE) _ _ (rayOfNeZero_orProd hE a)
      (rayOfNeZero_orProd hF b) T hωe',
    orSign_eq_sgn_mul hE _ _ (rayOfNeZero_orEpsB_det e a) (rayOfNeZero_orEpsB_det f b) A hωe]
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul,
    Basis.det_self, mul_one]
  rw [← he, ← hf]
  simp only [Basis.det_self, mul_one]
  have hdet : (prodRealBasis f).det (fun i => T.toLinearMap (prodRealBasis e i)) =
      c * f.det (fun i => A.toLinearMap (e i)) := by
    rw [Basis.det_apply, Basis.det_apply]
    have hmat : (prodRealBasis f).toMatrix (fun i => T.toLinearMap (prodRealBasis e i)) =
        Matrix.reindex (sumUnitEquiv n) (sumUnitEquiv n)
          (Matrix.fromBlocks (f.toMatrix (fun i => A.toLinearMap (e i)))
            (Matrix.of fun i _ => f.repr w i) 0 (Matrix.of fun _ _ => c)) := by
      ext i j
      obtain ⟨i', rfl⟩ := (sumUnitEquiv n).surjective i
      obtain ⟨j', rfl⟩ := (sumUnitEquiv n).surjective j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Basis.toMatrix_apply]
      rcases i' with i' | ⟨⟩ <;> rcases j' with j' | ⟨⟩
      · rw [sumUnitEquiv_inl, sumUnitEquiv_inl, prodRealBasis_castSucc, prodRealBasis_repr_castSucc,
          Matrix.fromBlocks_apply₁₁, Basis.toMatrix_apply]
        simp [hT]
      · rw [sumUnitEquiv_inl, sumUnitEquiv_inr, prodRealBasis_last, prodRealBasis_repr_castSucc,
          Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
        simp [hT]
      · rw [sumUnitEquiv_inr, sumUnitEquiv_inl, prodRealBasis_castSucc, prodRealBasis_repr_last,
          Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
        simp [hT]
      · rw [sumUnitEquiv_inr, prodRealBasis_last, prodRealBasis_repr_last,
          Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
        simp [hT]
    rw [hmat, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_unique (Matrix.of fun _ _ => c)]
    simp [mul_comm]
  rw [hdet, show orEpsB f b * (c * f.det (fun i => A.toLinearMap (e i))) * orEpsB e a =
      (orEpsB f b * f.det (fun i => A.toLinearMap (e i)) * orEpsB e a) * c by ring, sgn_mul]

/-- **Kernel formula.** For `T, T' : E → F × ℝ` with the same first component `P` (surjective)
and a nonzero `v ∈ ker P`, the product of the two signs is the sign of `(T v).2 * (T' v).2`. -/
theorem orSign_prodReal_mul (hE : finrank ℝ E = n + 1) (hF : finrank ℝ F = n)
    (a : Orientation ℝ E (Fin (n + 1))) (b : Orientation ℝ F (Fin n)) (T T' : E →L[ℝ] F × ℝ)
    (P : E →L[ℝ] F) (hT : ∀ v, (T v).1 = P v) (hT' : ∀ v, (T' v).1 = P v)
    (hP : Function.Surjective P) {v : E} (hv : v ≠ 0) (hPv : P v = 0) :
    orSign a (orProd hF b) T * orSign a (orProd hF b) T' = sgn ((T v).2 * (T' v).2) := by
  set f := finBasisOfFinrankEq ℝ F hF with hf
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective P.toLinearMap
    (LinearMap.range_eq_top.2 hP)
  have hPR : ∀ x, P (R x) = x := fun x => by
    have := LinearMap.congr_fun hR x
    simpa using this
  have hRinj : Function.Injective R := fun x y hxy => by rw [← hPR x, ← hPR y, hxy]
  -- the basis `v, R f₁, …, R fₙ` of `E`
  let u : Fin (n + 1) → E := Fin.cons v (fun i => R (f i))
  have hu : LinearIndependent ℝ u := by
    rw [linearIndependent_finCons]
    refine ⟨f.linearIndependent.map' R (LinearMap.ker_eq_bot_of_injective hRinj), ?_⟩
    intro hmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hmem
    have h1 : ∑ i, c i • f i = 0 := by
      have := congrArg P hc
      rw [hPv, map_sum] at this
      simpa [hPR] using this
    have h2 : c = 0 := (Fintype.linearIndependent_iff.1 f.linearIndependent c h1) |> funext
    rw [h2] at hc
    simp at hc
    exact hv hc.symm
  let e' : Basis (Fin (n + 1)) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank hu (by rw [Fintype.card_fin, hE])
  have he' : ⇑e' = u := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hωe' : (orEpsB e' a • e'.det) e' ≠ 0 := by
    rw [orEpsB_apply_self]; exact orEpsB_ne_zero e' a
  rw [orSign_eq_sgn_mul hE _ _ (rayOfNeZero_orEpsB_det e' a) (rayOfNeZero_orProd hF b) T hωe',
    orSign_eq_sgn_mul hE _ _ (rayOfNeZero_orEpsB_det e' a) (rayOfNeZero_orProd hF b) T' hωe']
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul,
    Basis.det_self, mul_one]
  -- the determinant of `S ∘ e'` for any `S` with first component `P`
  rw [← hf]
  have key : ∀ (S : E →L[ℝ] F × ℝ), (∀ x, (S x).1 = P x) →
      (prodRealBasis f).det (fun i => S.toLinearMap (e' i)) = (-1) ^ n * (S v).2 := by
    intro S hS
    rw [Basis.det_apply, Matrix.det_succ_column_zero]
    set M := (prodRealBasis f).toMatrix (fun i => S.toLinearMap (e' i)) with hM
    have hSv : S v = (0, (S v).2) := Prod.ext (by rw [hS, hPv]) rfl
    have hM0 : ∀ i : Fin (n + 1), M i 0 = if i = Fin.last n then (S v).2 else 0 := by
      intro i
      rw [hM, Basis.toMatrix_apply, he']
      simp only [u, Fin.cons_zero, ContinuousLinearMap.coe_coe]
      rw [hSv]
      obtain ⟨i', rfl⟩ := (sumUnitEquiv n).surjective i
      rcases i' with i' | ⟨⟩
      · rw [sumUnitEquiv_inl, prodRealBasis_repr_castSucc, if_neg (Fin.castSucc_lt_last i').ne]
        simp
      · rw [sumUnitEquiv_inr, prodRealBasis_repr_last, if_pos rfl]
    have hsub : M.submatrix (Fin.last n).succAbove Fin.succ = 1 := by
      ext k j
      rw [Matrix.submatrix_apply, Fin.succAbove_last, hM, Basis.toMatrix_apply, he']
      simp only [u, Fin.cons_succ, ContinuousLinearMap.coe_coe]
      rw [prodRealBasis_repr_castSucc, hS, hPR, Basis.repr_self, Matrix.one_apply,
        Finsupp.single_apply]
      simp [eq_comm]
    rw [Fin.sum_univ_castSucc]
    simp only [hM0, Fin.castSucc_lt_last, ne_eq, (Fin.castSucc_lt_last _).ne, if_false, mul_zero,
      zero_mul, Finset.sum_const_zero, zero_add, if_true, hsub, Matrix.det_one, mul_one, Fin.val_last]
  rw [key T hT, key T' hT', ← sgn_mul]
  have hε := orEpsB_ne_zero e' a
  have hεb := orEpsB_ne_zero f b
  have hpow : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have : orEpsB f b * ((-1) ^ n * (T v).2) * orEpsB e' a *
      (orEpsB f b * ((-1) ^ n * (T' v).2) * orEpsB e' a) =
      (orEpsB f b * (-1) ^ n * orEpsB e' a) * (orEpsB f b * (-1) ^ n * orEpsB e' a) *
        ((T v).2 * (T' v).2) := by ring
  rw [this, sgn_sq_mul (mul_ne_zero (mul_ne_zero hεb hpow) hε)]

end Milnor
