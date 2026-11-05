import Morse.Chapter15.EightCommutant

/-!
Milnor, *Morse Theory*, §24, Lemma 24.6 (8) (p. 142) and Theorem 24.7 (p. 142), at the finite
stage `n = 16r`; Exposition/Chapter15.md, §4, Lemma 24.6-(8) and Theorem 24.7.

# `Ω_8(16r) ≅ O(r)`, and Bott periodicity `π_{j+1}O(r) ≅ π_{j+9}O(16r)`

## Milnor's text, paraphrased

(p. 142) "`Ω_8(16r)` is homeomorphic to `O(r)`": `J_8 ↦ J_7J_8|X_1` identifies `Ω_8(16r)` with
the isometries `X_1 → X_2`; hence (Theorem 24.7) `π_iO ≅ π_{i+8}O`.

## What is formalized

On `ℝ^{16r} = ℝ¹⁶ ⊗ ℝ^r` with `J_α = J'_α ⊗ 1` (`Morse.bottJ`):

* `Morse.Pp`, `Morse.Pm`: the projections `(1 ± W)/2` onto the eigenspaces of
  `W = 1 ⊗ 1 ⊗ 1 ⊗ τ`; `Morse.qOf U V = P₊ ⊗ U + P₋ ⊗ V` (`U, V ∈ M_r(ℝ)`), with
  `Morse.eq_qOf_of_commute`: **every matrix commuting with `J_1, …, J_7` is `qOf U V`** (from
  `Morse.eq_of_commute_bott16`, block by block), and the algebra of `qOf` (`qOf_mul`,
  `transpose_qOf`, `J_8 qOf U V = qOf V U J_8`).
* **`Morse.omegaEightHomeomorph r : Ω_8(16r) ≃ₜ O(r)`**, `J ↦ U` where `−J_8J = P₊ ⊗ U + P₋ ⊗ Uᵀ`,
  with inverse `U ↦ J_8(P₊ ⊗ U + P₋ ⊗ Uᵀ)`; `Morse.omegaEightHomeomorph_basePt`: `J_8 ↦ I`.
* **`Morse.bott_periodicity_finite`** (Theorem 24.7 at a finite stage): for `2j + 12 ≤ r`,
  `π_{j+1}(O(r), I) ≃ π_{j+9}(O(16r), I)` (as sets): `Morse.bott_chain` and `Ω_8(16r) ≅ O(r)`.

## What Milnor leaves implicit

* The conditions on `Q = −J_8J = P₊ ⊗ U + P₋ ⊗ V`: `J` orthogonal iff `U, V` orthogonal; `J² = −1`
  iff `UV = VU = 1` (as `J_8P₊ = P₋J_8`); `J` anticommutes with `J_1, …, J_7` automatically.  So
  `V = Uᵀ`, and `U` is free in `O(r)`.  Milnor's `X_1, X_2` are the images of `P₊, P₋` on a
  line of `ℝ¹⁶`.
* The passage to `π_iO ≅ π_{i+8}O` for the infinite orthogonal group needs the stabilization
  `π_iO(n) ≅ π_iO(n + 1)` for `n > i + 1` and the colimit, not formalized here.
-/

open Matrix Set Function
open scoped Kronecker Topology

noncomputable section

namespace Morse

/-! ### The projections `(1 ± W)/2` -/

/-- `P₊ = (1 + W)/2`. -/
def Pp : Matrix I16 I16 ℝ := (1 / 2 : ℝ) • (1 + W16)
/-- `P₋ = (1 − W)/2`. -/
def Pm : Matrix I16 I16 ℝ := (1 / 2 : ℝ) • (1 - W16)

theorem Pp_add_Pm : Pp + Pm = 1 := by
  rw [Pp, Pm, ← smul_add, add_add_sub_cancel, ← two_smul ℝ (1 : Matrix I16 I16 ℝ), smul_smul]
  norm_num

theorem Pp_mul_Pp : Pp * Pp = Pp := by
  simp only [Pp, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, W16_mul_self]
  module

theorem Pm_mul_Pm : Pm * Pm = Pm := by
  simp only [Pm, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, W16_mul_self]
  module

theorem Pp_mul_Pm : Pp * Pm = 0 := by
  simp only [Pp, Pm, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, W16_mul_self]
  module

theorem Pm_mul_Pp : Pm * Pp = 0 := by
  simp only [Pp, Pm, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, W16_mul_self]
  module

theorem Pp_transpose : Ppᵀ = Pp := by
  rw [Pp, transpose_smul, transpose_add, transpose_one, W16_transpose]

theorem Pm_transpose : Pmᵀ = Pm := by
  rw [Pm, transpose_smul, transpose_sub, transpose_one, W16_transpose]

theorem comm_Pp {α : ℕ} (h1 : 1 ≤ α) (h7 : α ≤ 7) : bott16 α * Pp = Pp * bott16 α := by
  rw [Pp, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, W16_comm h1 h7,
    Matrix.mul_one, Matrix.one_mul]

theorem comm_Pm {α : ℕ} (h1 : 1 ≤ α) (h7 : α ≤ 7) : bott16 α * Pm = Pm * bott16 α := by
  rw [Pm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, W16_comm h1 h7,
    Matrix.mul_one, Matrix.one_mul]

theorem eight_Pp : bott16 8 * Pp = Pm * bott16 8 := by
  rw [Pp, Pm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.sub_mul, W16_anti,
    Matrix.mul_one, Matrix.one_mul, ← sub_eq_add_neg]

theorem eight_Pm : bott16 8 * Pm = Pp * bott16 8 := by
  rw [Pp, Pm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.add_mul, W16_anti,
    Matrix.mul_one, Matrix.one_mul, sub_neg_eq_add]

/-- Two points of `ℝ¹⁶` where `W = 1` and `W = −1`. -/
def x0 : I16 := (((0, 0), 0), 0)
def x1 : I16 := (((0, 0), 0), 1)

theorem W16_x0 : W16 x0 x0 = 1 := by
  simp [W16, kword, wCode, kletter, x0, τ₂]
theorem W16_x1 : W16 x1 x1 = -1 := by
  simp [W16, kword, wCode, kletter, x1, τ₂]
theorem Pp_x0 : Pp x0 x0 = 1 := by simp [Pp, W16_x0]; norm_num
theorem Pm_x0 : Pm x0 x0 = 0 := by simp [Pm, W16_x0]
theorem Pp_x1 : Pp x1 x1 = 0 := by simp [Pp, W16_x1]
theorem Pm_x1 : Pm x1 x1 = 1 := by simp [Pm, W16_x1]; norm_num

/-! ### `P₊ ⊗ U + P₋ ⊗ V` -/

variable {r : ℕ}

/-- `qOf U V = P₊ ⊗ U + P₋ ⊗ V` on `ℝ¹⁶ ⊗ ℝ^r`. -/
def qOf (U V : Matrix (Fin r) (Fin r) ℝ) : Matrix (I16 × Fin r) (I16 × Fin r) ℝ :=
  Pp ⊗ₖ U + Pm ⊗ₖ V

/-- The `U`-coordinate: the `(x₀, x₀)` block. -/
def ext0 (Q : Matrix (I16 × Fin r) (I16 × Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => Q (x0, i) (x0, j)

/-- The `V`-coordinate: the `(x₁, x₁)` block. -/
def ext1 (Q : Matrix (I16 × Fin r) (I16 × Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => Q (x1, i) (x1, j)

theorem ext0_qOf (U V : Matrix (Fin r) (Fin r) ℝ) : ext0 (qOf U V) = U := by
  ext i j; simp [ext0, qOf, Pp_x0, Pm_x0]

theorem ext1_qOf (U V : Matrix (Fin r) (Fin r) ℝ) : ext1 (qOf U V) = V := by
  ext i j; simp [ext1, qOf, Pp_x1, Pm_x1]

theorem qOf_mul (U V U' V' : Matrix (Fin r) (Fin r) ℝ) :
    qOf U V * qOf U' V' = qOf (U * U') (V * V') := by
  simp only [qOf, Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul, Pp_mul_Pp, Pm_mul_Pm,
    Pp_mul_Pm, Pm_mul_Pp, zero_kronecker, add_zero, zero_add]

theorem transpose_qOf (U V : Matrix (Fin r) (Fin r) ℝ) : (qOf U V)ᵀ = qOf Uᵀ Vᵀ := by
  simp only [qOf, transpose_add, transpose_kronecker', Pp_transpose, Pm_transpose]

theorem qOf_one : qOf (1 : Matrix (Fin r) (Fin r) ℝ) 1 = 1 := by
  rw [qOf, ← add_kronecker, Pp_add_Pm, one_kronecker_one]

theorem bottJ_eq_kronecker (α : ℕ) :
    bottJ r α = bott16 α ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℝ) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp [bottJ, blockDiagonal_apply, Matrix.one_apply]

theorem comm_qOf {α : ℕ} (h1 : 1 ≤ α) (h7 : α ≤ 7) (U V : Matrix (Fin r) (Fin r) ℝ) :
    bottJ r α * qOf U V = qOf U V * bottJ r α := by
  simp only [bottJ_eq_kronecker, qOf, Matrix.mul_add, Matrix.add_mul, ← mul_kronecker_mul,
    comm_Pp h1 h7, comm_Pm h1 h7, Matrix.one_mul, Matrix.mul_one]

theorem eight_qOf (U V : Matrix (Fin r) (Fin r) ℝ) :
    bottJ r 8 * qOf U V = qOf V U * bottJ r 8 := by
  simp only [bottJ_eq_kronecker, qOf, Matrix.mul_add, Matrix.add_mul, ← mul_kronecker_mul,
    eight_Pp, eight_Pm, Matrix.one_mul, Matrix.mul_one]
  abel

/-- **Every matrix commuting with `J_1, …, J_7` on `ℝ^{16r}` is `P₊ ⊗ U + P₋ ⊗ V`.** -/
theorem eq_qOf_of_commute {Q : Matrix (I16 × Fin r) (I16 × Fin r) ℝ}
    (hQ : ∀ α, 1 ≤ α → α ≤ 7 → bottJ r α * Q = Q * bottJ r α) : Q = qOf (ext0 Q) (ext1 Q) := by
  -- the blocks commute with `J'_1, …, J'_7`
  have hblk : ∀ i j : Fin r, ∀ α, 1 ≤ α → α ≤ 7 →
      bott16 α * Matrix.of (fun x y => Q (x, i) (y, j)) =
        Matrix.of (fun x y => Q (x, i) (y, j)) * bott16 α := by
    intro i j α h1 h7
    have := hQ α h1 h7
    ext x y
    have h := congrFun (congrFun this (x, i)) (y, j)
    simpa [bottJ, Matrix.mul_apply, blockDiagonal_apply, Fintype.sum_prod_type,
      Finset.sum_ite_eq', Finset.sum_ite_eq] using h
  ext ⟨x, i⟩ ⟨y, j⟩
  have h := eq_of_commute_bott16 (hblk i j)
  set b := wordBasis.repr (Matrix.of fun x y => Q (x, i) (y, j)) 0
  set c := wordBasis.repr (Matrix.of fun x y => Q (x, i) (y, j)) wCode
  have hW : W16 = Pp - Pm := by
    rw [Pp, Pm, ← smul_sub, add_sub_sub_cancel, ← two_smul ℝ W16, smul_smul]; norm_num
  have h1 : Matrix.of (fun x y => Q (x, i) (y, j)) = (b + c) • Pp + (b - c) • Pm := by
    rw [h, ← Pp_add_Pm, hW]; module
  have e0 : Q (x0, i) (x0, j) = b + c := by
    have := congrFun (congrFun h1 x0) x0
    simpa [Pp_x0, Pm_x0] using this
  have e1 : Q (x1, i) (x1, j) = b - c := by
    have := congrFun (congrFun h1 x1) x1
    simpa [Pp_x1, Pm_x1] using this
  have := congrFun (congrFun h1 x) y
  rw [Matrix.of_apply] at this
  rw [this]
  simp only [qOf, Matrix.add_apply, kronecker_apply, ext0, ext1, e0, e1, Matrix.smul_apply,
    smul_eq_mul, Matrix.add_apply]
  ring

/-! ### `Ω_8(16r) ≅ O(r)` -/

theorem bottJ_eight_sq : bottJ r 8 * bottJ r 8 = -1 :=
  ((isAnticommFamily_bottJ r).cs 8 (by norm_num) le_rfl).2

theorem bottJ_eight_transpose : (bottJ r 8)ᵀ = -bottJ r 8 :=
  ((isAnticommFamily_bottJ r).cs 8 (by norm_num) le_rfl).transpose

/-- The `U` of `J ∈ Ω_8(16r)`: `−J_8J = P₊ ⊗ U + P₋ ⊗ V`. -/
def omegaEightU (J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  ext0 (-(bottJ r 8 * J))

theorem qOf_of_mem_omega_eight {J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ}
    (hJ : J ∈ Omega (bottJ r) 8) :
    -(bottJ r 8 * J) = qOf (ext0 (-(bottJ r 8 * J))) (ext1 (-(bottJ r 8 * J))) := by
  refine eq_qOf_of_commute fun α h1 h7 => ?_
  have ha := hJ.2 α h1 h7
  have h8 := (isAnticommFamily_bottJ r).anti α 8 h1 (by omega) (by norm_num) le_rfl (by omega)
  rw [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, h8, Matrix.neg_mul, Matrix.mul_assoc,
    ha, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]

theorem omegaEightU_mem {J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ}
    (hJ : J ∈ Omega (bottJ r) 8) : omegaEightU J ∈ orthogonalGroup (Fin r) ℝ := by
  have hQ := qOf_of_mem_omega_eight hJ
  have hJo : Jᵀ * J = 1 := (mem_orthogonalGroup_iff' (n := I16 × Fin r) (R := ℝ)).1 hJ.1.1
  have hQo : (-(bottJ r 8 * J))ᵀ * -(bottJ r 8 * J) = 1 := by
    rw [transpose_neg, transpose_mul, bottJ_eight_transpose, neg_mul_neg, Matrix.mul_assoc,
      ← Matrix.mul_assoc (-bottJ r 8), Matrix.neg_mul, bottJ_eight_sq, neg_neg, Matrix.one_mul,
      hJo]
  rw [hQ, transpose_qOf, qOf_mul, ← qOf_one] at hQo
  have := congrArg ext0 hQo
  rw [ext0_qOf, ext0_qOf] at this
  exact (mem_orthogonalGroup_iff' (n := Fin r) (R := ℝ)).2 this

theorem omegaEight_inv_mem {U : Matrix (Fin r) (Fin r) ℝ} (hU : U ∈ orthogonalGroup (Fin r) ℝ) :
    bottJ r 8 * qOf U Uᵀ ∈ Omega (bottJ r) 8 := by
  have h1 : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' (n := Fin r) (R := ℝ)).1 hU
  have h2 : U * Uᵀ = 1 := mul_eq_one_comm.1 h1
  refine ⟨⟨(mem_orthogonalGroup_iff' (n := I16 × Fin r) (R := ℝ)).2 ?_, ?_⟩, fun α ha h7 => ?_⟩
  · rw [transpose_mul, bottJ_eight_transpose, transpose_qOf, transpose_transpose,
      Matrix.mul_assoc, ← Matrix.mul_assoc (-bottJ r 8), Matrix.neg_mul, bottJ_eight_sq,
      neg_neg, Matrix.one_mul, qOf_mul, h1, h2, qOf_one]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (qOf U Uᵀ), ← eight_qOf, Matrix.mul_assoc,
      ← Matrix.mul_assoc (bottJ r 8) (bottJ r 8), bottJ_eight_sq, Matrix.neg_mul, Matrix.one_mul,
      qOf_mul, h1, h2, qOf_one]
  · have h78 : α ≤ 8 := le_trans h7 (by norm_num)
    have hne : α ≠ 8 := Nat.ne_of_lt (Nat.lt_of_le_of_lt h7 (by norm_num))
    have h8 := (isAnticommFamily_bottJ r).anti α 8 ha h78 (by norm_num) le_rfl hne
    rw [← Matrix.mul_assoc, h8, Matrix.neg_mul, Matrix.mul_assoc, comm_qOf ha h7,
      ← Matrix.mul_assoc]

theorem continuous_ext0 : Continuous (ext0 : Matrix (I16 × Fin r) (I16 × Fin r) ℝ → _) :=
  continuous_pi fun _ => continuous_pi fun _ =>
    (continuous_apply _).comp (continuous_apply _)

theorem continuous_qOf_transpose :
    Continuous fun U : Matrix (Fin r) (Fin r) ℝ => qOf U Uᵀ := by
  refine continuous_pi fun ⟨a1, a2⟩ => continuous_pi fun ⟨b1, b2⟩ => ?_
  simp only [qOf, Matrix.add_apply, kronecker_apply, transpose_apply]
  exact (continuous_const.mul (continuous_id.matrix_elem a2 b2)).add
    (continuous_const.mul (continuous_id.matrix_elem b2 a2))

/-- **Lemma 24.6 (8)** (Milnor p. 142): `Ω_8(16r)` is homeomorphic to `O(r)`. -/
def omegaEightHomeomorph (r : ℕ) :
    Omega (bottJ r) 8 ≃ₜ (orthogonalGroup (Fin r) ℝ : Set (Matrix (Fin r) (Fin r) ℝ)) where
  toFun J := ⟨omegaEightU (J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ), omegaEightU_mem J.2⟩
  invFun U := ⟨bottJ r 8 * qOf (U : Matrix (Fin r) (Fin r) ℝ) (U : Matrix (Fin r) (Fin r) ℝ)ᵀ,
    omegaEight_inv_mem U.2⟩
  left_inv J := by
    apply Subtype.ext
    change bottJ r 8 * qOf (omegaEightU (J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ))
      (omegaEightU (J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ))ᵀ = J
    have hU := omegaEightU_mem J.2
    have hQ := qOf_of_mem_omega_eight J.2
    set Q := -(bottJ r 8 * (J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ)) with hQdef
    set U := ext0 Q with hUdef
    set V := ext1 Q with hVdef
    have h1 : Uᵀ * U = 1 := (mem_orthogonalGroup_iff' (n := Fin r) (R := ℝ)).1 hU
    have e8 : qOf V U * bottJ r 8 = bottJ r 8 * Q := by rw [← eight_qOf, ← hQ]
    have hJ2 : (J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ) * J = -1 := J.2.1.2
    have hsq : qOf V U * qOf U V = 1 := by
      rw [← hQ]
      calc qOf V U * Q = -(qOf V U * bottJ r 8 * (J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ)) := by
            rw [hQdef, Matrix.mul_neg, Matrix.mul_assoc]
        _ = -(bottJ r 8 * Q * (J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ)) := by rw [e8]
        _ = bottJ r 8 * bottJ r 8 * ((J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ) * J) := by
            rw [hQdef, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc,
              Matrix.mul_assoc, Matrix.mul_assoc]
        _ = 1 := by rw [bottJ_eight_sq, hJ2, Matrix.neg_mul, Matrix.one_mul, neg_neg]
    rw [qOf_mul, ← qOf_one] at hsq
    have hUV : U * V = 1 := by
      have := congrArg ext1 hsq
      rwa [ext1_qOf, ext1_qOf] at this
    have hV : V = Uᵀ :=
      calc V = Uᵀ * (U * V) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
        _ = Uᵀ := by rw [hUV, Matrix.mul_one]
    change bottJ r 8 * qOf U Uᵀ = J
    rw [← hV, ← hQ, hQdef, Matrix.mul_neg, ← Matrix.mul_assoc, bottJ_eight_sq, Matrix.neg_mul,
      Matrix.one_mul, neg_neg]
  right_inv U := by
    apply Subtype.ext
    change ext0 (-(bottJ r 8 * (bottJ r 8 * qOf (U : Matrix (Fin r) (Fin r) ℝ)
      (U : Matrix (Fin r) (Fin r) ℝ)ᵀ))) = U
    rw [← Matrix.mul_assoc, bottJ_eight_sq, Matrix.neg_mul, Matrix.one_mul, neg_neg, ext0_qOf]
  continuous_toFun := (continuous_ext0.comp
    ((continuous_const.mul continuous_subtype_val).neg)).subtype_mk _
  continuous_invFun := ((continuous_const.mul
    (continuous_qOf_transpose.comp continuous_subtype_val))).subtype_mk _

/-- `J_8 ↦ I`. -/
theorem omegaEightHomeomorph_basePt (r : ℕ) :
    omegaEightHomeomorph r ⟨basePt (bottJ r) 8, basePt_mem_omega (isAnticommFamily_bottJ r)⟩ =
      ⟨1, (orthogonalGroup (Fin r) ℝ).one_mem⟩ := by
  apply Subtype.ext
  change ext0 (-(bottJ r 8 * basePt (bottJ r) 8)) = 1
  rw [show basePt (bottJ r) 8 = bottJ r 8 from rfl, bottJ_eight_sq, neg_neg, ← qOf_one,
    ext0_qOf]

/-- **Bott periodicity at a finite stage** (Milnor, Theorem 24.7, p. 142, with `n = 16r`): for
`2j + 12 ≤ r`, `π_{j+1}(O(r), I) ≃ π_{j+9}(O(16r), I)` (as sets). -/
theorem bott_periodicity_finite (r j : ℕ) (hr : 2 * j + 12 ≤ r) :
    Nonempty (π_ (j + 1) (orthogonalGroup (Fin r) ℝ : Set (Matrix (Fin r) (Fin r) ℝ))
        ⟨1, (orthogonalGroup (Fin r) ℝ).one_mem⟩ ≃
      π_ (j + 9) (orthogonalGroup (I16 × Fin r) ℝ :
        Set (Matrix (I16 × Fin r) (I16 × Fin r) ℝ))
        ⟨1, (orthogonalGroup (I16 × Fin r) ℝ).one_mem⟩) := by
  obtain ⟨e⟩ := bott_chain r j hr
  exact ⟨(Morse.Homotopy.piEquivOfHomeomorph (omegaEightHomeomorph r)
    (omegaEightHomeomorph_basePt r) (j + 1)).symm.trans e⟩

end Morse
