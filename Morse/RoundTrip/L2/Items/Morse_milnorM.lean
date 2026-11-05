import Morse
import RoundTrip.L2.Blind.Morse_milnorM

/-! Layer-2 check of `Morse.milnorM` (Milnor's table `1, 2, 4, 4, 8, 8, 8, 8, 16` for
`k = 0, …, 8`, extended by the recursion `m_{k+8} = 16 m_k`) against the blind textbook definition
(the least `n > 0` such that `ℝⁿ` carries `k` anticommuting complex structures).

* `agree_of`: equal for `k ≤ 8`, by the project's `isLeast_milnorM` (existence on `ℝ^{m_k}` and
  `m_k ∣ n` for every such `ℝⁿ`); `T_table` gives the blind values.
* `T_le`: for EVERY `k`, `T k ≤ milnorM k` (`ℝ^{m_k}` carries `k` structures: from `k` structures
  `J'` on `ℝⁿ`, the structures `J_α ⊗ 1`, `α ≤ 8`, and `ω ⊗ J'_{α−8}` on `ℝ¹⁶ ⊗ ℝⁿ`, `ω` the
  grading of `ℝ¹⁶`).
* Not proved: `milnorM k ≤ T k` for `k > 8`, i.e. that a space with `k` structures has dimension
  `≥ 16 m_{k−8}`; this is Clifford periodicity (`C_{k+8} ≅ C_k ⊗ M₁₆(ℝ)` and its consequence for
  irreducible modules), in neither Mathlib nor the project (which only uses `k ≤ 8`). -/

namespace RoundTrip.L2.Morse_milnorM

/-- The blind family predicate is the project's `IsAnticommFamily`. -/
theorem isACFam_iff {n : Type*} [Fintype n] [DecidableEq n] (J : ℕ → Matrix n n ℝ) (k : ℕ) :
    IsACFam J k ↔ Morse.IsAnticommFamily J k :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.cs, h.anti⟩⟩

/-- **Agreement for `k ≤ 8`** (the range of Milnor's table). -/
theorem agree_of {k : ℕ} (hk : k ≤ 8) : Morse.milnorM k = T k := by
  have hset : {n : ℕ | 0 < n ∧ ∃ J : ℕ → Matrix (Fin n) (Fin n) ℝ, IsACFam J k} =
      {d | 0 < d ∧ ∃ J : ℕ → Matrix (Fin d) (Fin d) ℝ, Morse.IsAnticommFamily J k} := by
    ext n
    simp only [Set.mem_ofPred_eq, isACFam_iff]
  rw [T, hset, (Morse.isLeast_milnorM hk).csInf_eq]

/-- The table, for the blind `m_k`. -/
theorem T_table : T 0 = 1 ∧ T 1 = 2 ∧ T 2 = 4 ∧ T 3 = 4 ∧ T 4 = 8 ∧ T 5 = 8 ∧ T 6 = 8 ∧
    T 7 = 8 ∧ T 8 = 16 := by
  simp only [← agree_of (show (0 : ℕ) ≤ 8 by norm_num), ← agree_of (show (1 : ℕ) ≤ 8 by norm_num),
    ← agree_of (show (2 : ℕ) ≤ 8 by norm_num), ← agree_of (show (3 : ℕ) ≤ 8 by norm_num),
    ← agree_of (show (4 : ℕ) ≤ 8 by norm_num), ← agree_of (show (5 : ℕ) ≤ 8 by norm_num),
    ← agree_of (show (6 : ℕ) ≤ 8 by norm_num), ← agree_of (show (7 : ℕ) ≤ 8 by norm_num),
    ← agree_of (le_refl 8)]
  decide

/-! ### Beyond `k = 8`: the upper bound `T k ≤ milnorM k`

From `k` anticommuting complex structures `J'` on `ℝⁿ`, the structures `J_α ⊗ 1` (`α ≤ 8`, the
project's `bott16`) and `ω ⊗ J'_{α−8}` on `ℝ¹⁶ ⊗ ℝⁿ`, with the grading `ω = 1 ⊗ κ₂`
(`ω² = 1`, `ωᵀ = ω`, `ω` anticommuting with every `J_α`), give `k + 8` of them on `ℝ^{16n}`. -/

section Upper

open Matrix Kronecker

/-- The grading operator of `ℝ¹⁶`. -/
noncomputable def ω16 : Matrix Morse.I16 Morse.I16 ℝ := ((1 ⊗ₖ 1) ⊗ₖ 1) ⊗ₖ Morse.κ₂

theorem ω16_mul_self : ω16 * ω16 = 1 := by
  simp only [ω16]; kron_simp

theorem ω16_transpose : ω16ᵀ = ω16 := by
  simp only [ω16]; kron_simp

theorem bott16_mul_ω16 {α : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ 8) :
    Morse.bott16 α * ω16 = -(ω16 * Morse.bott16 α) := by
  interval_cases α <;> (simp only [Morse.bott16, ω16]; kron_simp)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `k + 8` structures on `ℝ¹⁶ ⊗ ℝⁿ`. -/
noncomputable def up (J' : ℕ → Matrix n n ℝ) (α : ℕ) : Matrix (Morse.I16 × n) (Morse.I16 × n) ℝ :=
  if α ≤ 8 then Morse.bott16 α ⊗ₖ (1 : Matrix n n ℝ) else ω16 ⊗ₖ J' (α - 8)

omit [Fintype n] in
theorem up_of_le {J' : ℕ → Matrix n n ℝ} {α : ℕ} (h : α ≤ 8) :
    up J' α = Morse.bott16 α ⊗ₖ (1 : Matrix n n ℝ) := if_pos h

omit [Fintype n] in
theorem up_of_gt {J' : ℕ → Matrix n n ℝ} {α : ℕ} (h : 8 < α) : up J' α = ω16 ⊗ₖ J' (α - 8) :=
  if_neg (by omega)

theorem isAnticommFamily_up {J' : ℕ → Matrix n n ℝ} {k : ℕ} (h : Morse.IsAnticommFamily J' k) :
    Morse.IsAnticommFamily (up J') (k + 8) := by
  have hb := Morse.isAnticommFamily_bott16
  refine ⟨fun α h1 h2 => ?_, fun α β h1 h2 h3 h4 hab => ?_⟩
  · rw [Morse.isComplexStructure_iff]
    by_cases hα : α ≤ 8
    · have hc := Morse.isComplexStructure_iff.1 (hb.cs α h1 hα)
      rw [up_of_le hα, Morse.transpose_kronecker', hc.1, Morse.neg_kronecker', ← mul_kronecker_mul,
        hc.2, Matrix.one_mul, Morse.neg_kronecker', one_kronecker_one, transpose_one]
      exact ⟨rfl, rfl⟩
    · have hc := Morse.isComplexStructure_iff.1 (h.cs (α - 8) (by omega) (by omega))
      rw [up_of_gt (by omega), Morse.transpose_kronecker', ω16_transpose, hc.1, Morse.kronecker_neg',
        ← mul_kronecker_mul, ω16_mul_self, hc.2, Morse.kronecker_neg', one_kronecker_one]
      exact ⟨rfl, rfl⟩
  · by_cases hα : α ≤ 8 <;> by_cases hβ : β ≤ 8
    · rw [up_of_le hα, up_of_le hβ, ← mul_kronecker_mul, ← mul_kronecker_mul,
        hb.anti α β h1 hα h3 hβ hab, Morse.neg_kronecker']
    · rw [up_of_le hα, up_of_gt (by omega), ← mul_kronecker_mul, ← mul_kronecker_mul,
        bott16_mul_ω16 h1 hα, Matrix.one_mul, Matrix.mul_one, Morse.neg_kronecker']
    · rw [up_of_gt (by omega), up_of_le hβ, ← mul_kronecker_mul, ← mul_kronecker_mul,
        bott16_mul_ω16 h3 hβ, Matrix.one_mul, Matrix.mul_one, Morse.neg_kronecker', neg_neg]
    · rw [up_of_gt (by omega), up_of_gt (by omega), ← mul_kronecker_mul, ← mul_kronecker_mul,
        ω16_mul_self, h.anti (α - 8) (β - 8) (by omega) (by omega) (by omega) (by omega)
          (by omega), Morse.kronecker_neg']

/-- **`ℝ^{m_k}` carries `k` anticommuting complex structures for every `k`** (the project proves
it for `k ≤ 8`). -/
theorem exists_family (k : ℕ) :
    ∃ J : ℕ → Matrix (Fin (Morse.milnorM k)) (Fin (Morse.milnorM k)) ℝ,
      Morse.IsAnticommFamily J k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k ≤ 8
    · exact Morse.exists_isAnticommFamily_fin hk
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
      obtain ⟨J', hJ'⟩ := ih j (by omega)
      have hcard : Fintype.card (Morse.I16 × Fin (Morse.milnorM j)) = Morse.milnorM (j + 8) := by
        simp [Morse.milnorM]
      exact ⟨_, (isAnticommFamily_up hJ').reindex (Fintype.equivFinOfCardEq hcard)⟩

/-- **The upper bound for every `k`**: the blind `m_k` is at most the project's. -/
theorem T_le (k : ℕ) : T k ≤ Morse.milnorM k := by
  obtain ⟨J, hJ⟩ := exists_family k
  exact Nat.sInf_le ⟨Morse.milnorM_pos k, J, (isACFam_iff J k).2 hJ⟩

end Upper

end RoundTrip.L2.Morse_milnorM
