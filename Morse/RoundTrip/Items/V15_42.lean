import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_42

open Matrix
open scoped Kronecker

noncomputable section

namespace RoundTrip.V15_42

/-- The project's statement (no universe parameters; `W16`, `qOf`, `ext0`, `ext1`, `wordBasis` are
vocabulary). The def `omegaEightHomeomorph` is read, together with
`omegaEightHomeomorph_basePt`, as the existence of a homeomorphism `Ω_8(16r) ≃ₜ O(r)` carrying
`J_8` to `I` (as defs are read in `Items/V14_17.lean`; stating `type_of%` of
`omegaEightHomeomorph_basePt` literally would make the statement depend on the body of the def):
(1) every `X ∈ M_16(ℝ)` commuting with `J'_1, …, J'_7` is `a·1 + b·W`;
(2) every `Q` on `ℝ^{16r}` commuting with `J_1, …, J_7` is `P₊ ⊗ U + P₋ ⊗ V`;
(3) `Ω_8(16r) ≃ₜ O(r)` with `J_8 ↦ I`. All for Milnor's explicit structures `bottJ r`. -/
def A : Prop :=
  type_of% @Morse.eq_of_commute_bott16 ∧ type_of% @Morse.eq_qOf_of_commute ∧
    ∀ r : ℕ, ∃ h : Morse.Omega (Morse.bottJ r) 8 ≃ₜ
        (orthogonalGroup (Fin r) ℝ : Set (Matrix (Fin r) (Fin r) ℝ)),
      h ⟨Morse.basePt (Morse.bottJ r) 8, Morse.basePt_mem_omega (Morse.isAnticommFamily_bottJ r)⟩ =
        ⟨1, (orthogonalGroup (Fin r) ℝ).one_mem⟩

theorem A_holds : A :=
  ⟨@Morse.eq_of_commute_bott16, @Morse.eq_qOf_of_commute,
    fun r => ⟨Morse.omegaEightHomeomorph r, Morse.omegaEightHomeomorph_basePt r⟩⟩

/-! ### Glue -/

section Glue

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem isACFam_iff (Js : ℕ → Mat ι) (m : ℕ) :
    IsACFam Js m ↔ Morse.IsAnticommFamily Js m :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.cs, h.anti⟩⟩

theorem omegaK_eq_omega (Js : ℕ → Mat ι) (k : ℕ) : OmegaK Js k = Morse.Omega Js k := by
  cases k with
  | zero => rfl
  | succ k =>
    ext J
    simp only [OmegaK, Morse.Omega, IsCplxStr, Morse.IsComplexStructure, AntiComm,
      Set.mem_ofPred_eq]
    refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun _ =>
      ⟨fun h => by rw [h, neg_neg], fun h => by rw [h, neg_neg]⟩)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem continuous_reindex (e : ι ≃ κ) : Continuous fun X : Mat ι => reindex e e X :=
  continuous_id.matrix_reindex e e

theorem mem_omega_reindex_symm (e : ι ≃ κ) (J : ℕ → Mat ι) (k : ℕ) {Y : Mat κ}
    (hY : Y ∈ Morse.Omega (fun α => reindex e e (J α)) k) :
    reindex e.symm e.symm Y ∈ Morse.Omega J k := by
  have h := Morse.mem_omega_reindex e.symm hY
  have hJ : (fun α => reindex e.symm e.symm (reindex e e (J α))) = J := by
    funext α; simp [reindex_apply, submatrix_submatrix]
  rwa [hJ] at h

/-- Reindexing `Ω_k` along `e : ι ≃ κ` (for the reindexed structures). -/
def omegaReindex (e : ι ≃ κ) (J : ℕ → Mat ι) (k : ℕ) :
    Morse.Omega J k ≃ₜ Morse.Omega (fun α => reindex e e (J α)) k where
  toFun X := ⟨reindex e e X.1, Morse.mem_omega_reindex e X.2⟩
  invFun Y := ⟨reindex e.symm e.symm Y.1, mem_omega_reindex_symm e J k Y.2⟩
  left_inv X := Subtype.ext (by simp [reindex_apply, submatrix_submatrix])
  right_inv Y := Subtype.ext (by simp [reindex_apply, submatrix_submatrix])
  continuous_toFun := ((continuous_reindex e).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_reindex e.symm).comp continuous_subtype_val).subtype_mk _

end Glue

/-! ### `A`'s algebraic conjuncts, re-proved (the project's proofs, copied: `B` says nothing about
the commutant of `J_1, …, J_7`, nor about Milnor's explicit structures). -/

section Outright

open Morse

theorem eq_of_commute_bott16' {X : Matrix I16 I16 ℝ}
    (hX : ∀ α, 1 ≤ α → α ≤ 7 → bott16 α * X = X * bott16 α) :
    X = wordBasis.repr X 0 • 1 + wordBasis.repr X wCode • W16 := by
  set c := wordBasis.repr X
  have hsum : X = ∑ u, c u • kword u := by
    conv_lhs => rw [← wordBasis.sum_repr X]
    simp only [wordBasis_apply]
    rfl
  have hconj : ∀ α, 1 ≤ α → α ≤ 8 → ∀ u, bott16 α * kword u * bott16 α =
      -(bsgn (wanti (bottCode α) u) • kword u) := fun α h1 h2 u => by
    rw [bott16_eq_word h1 h2, word_comm, Matrix.smul_mul, Matrix.mul_assoc,
      ← bott16_eq_word h1 h2, (isAnticommFamily_bott16.cs α h1 h2).2, Matrix.mul_neg,
      Matrix.mul_one, smul_neg]
  have hc : ∀ u, c u ≠ 0 → ∀ α ∈ [1, 2, 3, 4, 5, 6, 7], wanti (bottCode α) u = false := by
    intro u hu α hα
    have hα1 : 1 ≤ α := by simp at hα; omega
    have hα7 : α ≤ 7 := by simp at hα; omega
    have hJ := (isAnticommFamily_bott16.cs α hα1 (by omega)).2
    have h1 : X = -(bott16 α * X * bott16 α) := by
      rw [hX α hα1 hα7, Matrix.mul_assoc, hJ, Matrix.mul_neg, Matrix.mul_one, neg_neg]
    have h2 : -(bott16 α * X * bott16 α) =
        ∑ v, (c v * bsgn (wanti (bottCode α) v)) • kword v := by
      conv_lhs => rw [hsum]
      simp only [Matrix.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
        hconj α hα1 (by omega), smul_neg, neg_neg, Finset.sum_neg_distrib, smul_smul]
    have h3 : wordBasis.repr X u = c u * bsgn (wanti (bottCode α) u) := by
      rw [h1, h2]
      simp only [← wordBasis_apply]
      rw [Module.Basis.repr_sum_self]
    change c u = _ at h3
    cases hw : wanti (bottCode α) u
    · rfl
    · rw [hw, bsgn, if_pos rfl] at h3
      exact absurd (by linarith : c u = 0) hu
  conv_lhs => rw [hsum]
  rw [Finset.sum_eq_add (0 : Fin 4 → Fin 4) wCode (by decide) ?_ (by simp) (by simp)]
  · rw [word_zero]; rfl
  · intro u _ hu
    by_contra h0
    rcases eq_of_not_wanti u (hc u (fun h => h0 (by rw [h, zero_smul]))) with h | h
    · exact hu.1 h
    · exact hu.2 h

theorem eq_qOf_of_commute' {r : ℕ} {Q : Matrix (I16 × Fin r) (I16 × Fin r) ℝ}
    (hQ : ∀ α, 1 ≤ α → α ≤ 7 → bottJ r α * Q = Q * bottJ r α) : Q = qOf (ext0 Q) (ext1 Q) := by
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
  have h := eq_of_commute_bott16' (hblk i j)
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

end Outright

/-- `B ⇒ A`. The third conjunct really comes from `B`: `B` (d) for the structures
`J_α = reindex (bottJ r α)` on `Fin (16r)` (anticommuting by the project's
`isAnticommFamily_bottJ`, outside the item) gives a homeomorphism `Ω_8(16r) ≃ₜ O(r)`; reindexing
`I16 × Fin r ≃ Fin (16r)` and a left translation of `O(r)` make it send `J_8` to `I`. The first two
conjuncts (the commutant of `J'_1, …, J'_7`, resp. `J_1, …, J_7`, for Milnor's explicit
structures) are not consequences of `B` and are re-proved outright (`Outright`). -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨@eq_of_commute_bott16', @eq_qOf_of_commute', fun r => ?_⟩
  have hc : Fintype.card (Morse.I16 × Fin r) = 16 * r := Morse.card_bottJ r
  let e : Morse.I16 × Fin r ≃ Fin (16 * r) := Fintype.equivFinOfCardEq hc
  let Js : ℕ → Mat (Fin (16 * r)) := fun α => reindex e e (Morse.bottJ r α)
  have hJs : IsACFam Js 8 := (isACFam_iff _ _).2 ((Morse.isAnticommFamily_bottJ r).reindex e)
  obtain ⟨-, -, -, h, -⟩ := hB r Js hJs
  let h₁ : Morse.Omega (Morse.bottJ r) 8 ≃ₜ ↥(Matrix.orthogonalGroup (Fin r) ℝ) :=
    ((omegaReindex e (Morse.bottJ r) 8).trans
      (Homeomorph.setCongr (omegaK_eq_omega Js 8).symm)).trans h
  let x₀ : Morse.Omega (Morse.bottJ r) 8 :=
    ⟨Morse.basePt (Morse.bottJ r) 8, Morse.basePt_mem_omega (Morse.isAnticommFamily_bottJ r)⟩
  let g : ↥(Matrix.orthogonalGroup (Fin r) ℝ) := h₁ x₀
  refine ⟨h₁.trans (Homeomorph.mulLeft g⁻¹), ?_⟩
  change g⁻¹ * g = 1
  exact inv_mul_cancel g

#rt_check RoundTrip.V15_42.B_to_A [Morse.eq_of_commute_bott16, Morse.eq_qOf_of_commute, Morse.omegaEightHomeomorph_basePt, Morse.omegaEightHomeomorph]
#rt_overlap RoundTrip.V15_42.B_to_A [Morse.eq_of_commute_bott16, Morse.eq_qOf_of_commute, Morse.omegaEightHomeomorph_basePt, Morse.omegaEightHomeomorph]

end RoundTrip.V15_42
