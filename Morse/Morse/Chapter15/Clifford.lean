import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic.FinCases
import Morse.Chapter15.ComplexStructure

/-!
Milnor, *Morse Theory*, §24, pp. 136–138 and 142–144.

# Explicit anticommuting complex structures

## Milnor's text, paraphrased

* p. 136: "Assume that `n` is divisible by a high power of 2", and fix anticommuting complex
  structures `J_1, …, J_{k−1}` on `ℝⁿ`; p. 139: "it will be convenient to set `n = 16r`".
  Milnor never writes the structures down.
* p. 138: `Ω_k(n)` is imbedded in `Ω_k(n + n')` by choosing anticommuting complex structures
  `J'_1, …, J'_k` on `ℝ^{n'}` and sending `J` to `J ⊕ J'_k`, which anticommutes with
  `J_α ⊕ J'_α`.
* Remark pp. 143–144: if `J_1, …, J_k` are anticommuting complex structures on `V` and `u` is a
  unit vector, then `J_1u, …, J_ku` are perpendicular to each other and to `u`; this gives `k`
  independent vector fields on the unit sphere of `V`: 3 on `S^{4r−1}`, 7 on `S^{8r−1}`, 8 on
  `S^{16r−1}` (Hurwitz–Radon; Adams showed these are best possible).

## What is formalized

* The `2 × 2` matrices `σ₂ = (0 −1; 1 0)`, `τ₂ = (1 0; 0 −1)`, `κ₂ = (0 1; 1 0)` and their
  relations (`σ₂² = −1`, `τ₂² = κ₂² = 1`, any two anticommute, `σ₂` skew, `τ₂`, `κ₂` symmetric),
  and Kronecker products ("words") of them.  A word with one `σ₂` is a complex structure, and two
  words anticommute iff they carry different non-identity letters in an odd number of slots; the
  tactic `kron_simp` checks this slot by slot.
* **`ℝ¹⁶` with eight anticommuting complex structures** (`Morse.isAnticommFamily_bott16`):
  `J'_1 = 1⊗1⊗σ⊗τ`, `J'_2 = 1⊗σ⊗τ⊗τ`, `J'_3 = σ⊗1⊗κ⊗τ`, `J'_4 = σ⊗τ⊗τ⊗τ`, `J'_5 = σ⊗κ⊗τ⊗τ`,
  `J'_6 = τ⊗σ⊗κ⊗τ`, `J'_7 = κ⊗σ⊗κ⊗τ`, `J'_8 = 1⊗1⊗1⊗σ` (Chapter 15 of the exposition, §3).
  Dropping the last slot, the first seven give **seven on `ℝ⁸`** (`Morse.isAnticommFamily_bott8`,
  the octonionic structures), and `1⊗σ, σ⊗τ, σ⊗κ` give **three on `ℝ⁴`**
  (`Morse.isAnticommFamily_bott4`, the quaternions); `σ₂` is one on `ℝ²`.
* Transport: `Morse.IsAnticommFamily.reindex` (any identification of the index sets, e.g. with
  `Fin 16`), `Morse.IsAnticommFamily.blockDiagonal` (**`ℝ^{16r}` with eight**, Milnor's
  `J_α = J'_α ⊕ ⋯ ⊕ J'_α`, `Morse.isAnticommFamily_bott16r`), `Morse.IsAnticommFamily.fromBlocks`
  and **Milnor's imbedding** `Morse.fromBlocks_mem_omega`: `J ↦ J ⊕ J'` maps `Ω_k(n)` into
  `Ω_k(n + n')` for the families `J_α ⊕ J'_α`.
* `Morse.milnorM k` is Milnor's `m_k` (`1, 2, 4, 4, 8, 8, 8, 8, 16`, then `m_{k+8} = 16 m_k`),
  and `Morse.exists_isAnticommFamily_fin`: for `k ≤ 8`, `ℝ^{m_k}` carries `k` anticommuting
  complex structures.  (That no smaller space does, and that `m_k` divides the dimension of every
  such space, is `Morse/Chapter15/CliffordModules.lean`.)
* **Vector fields on spheres** (pp. 143–144): `Morse.IsAnticommFamily.dotProduct_mulVec`
  (`⟨J_αu, J_βu⟩ = δ_{αβ}|u|²`) and `Morse.IsComplexStructure.dotProduct_mulVec_self`
  (`⟨J_αu, u⟩ = 0`); with the families above, `S^{16r−1}` carries 8 orthonormal tangent fields.

Not formalized: the topology of the vector fields (continuity is clear, they are linear), Adams'
upper bound, and Milnor's "it is not difficult to see that the inclusions give rise, in the limit,
to inclusions `Ω_{k+1} → ΩΩ_k`" beyond the algebraic compatibility of the imbeddings.

## Gaps in Milnor's text

* p. 136: "divisible by a high power of 2" is not enough by itself: the structures have to be
  chosen.  Here they are explicit, and `n = 16r` suffices for all `k ≤ 8`.
* p. 138: the imbedding `J ↦ J ⊕ J'_k` needs `J'_k` to anticommute with `J'_1, …, J'_{k−1}` and
  be a complex structure, i.e. `ℝ^{n'}` must itself carry `k` anticommuting structures.
-/

open Matrix Kronecker

noncomputable section

namespace Morse

/-! ### The letters -/

/-- `σ₂ = (0 −1; 1 0)`, rotation by a right angle. -/
def σ₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
/-- `τ₂ = (1 0; 0 −1)`. -/
def τ₂ : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
/-- `κ₂ = (0 1; 1 0)`. -/
def κ₂ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem σ₂_mul_σ₂ : σ₂ * σ₂ = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, mul_apply, Fin.sum_univ_two]
theorem τ₂_mul_τ₂ : τ₂ * τ₂ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [τ₂, mul_apply, Fin.sum_univ_two]
theorem κ₂_mul_κ₂ : κ₂ * κ₂ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [κ₂, mul_apply, Fin.sum_univ_two]
theorem τ₂_mul_σ₂ : τ₂ * σ₂ = -(σ₂ * τ₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, τ₂, mul_apply, Fin.sum_univ_two]
theorem κ₂_mul_σ₂ : κ₂ * σ₂ = -(σ₂ * κ₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, κ₂, mul_apply, Fin.sum_univ_two]
theorem κ₂_mul_τ₂ : κ₂ * τ₂ = -(τ₂ * κ₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [τ₂, κ₂, mul_apply, Fin.sum_univ_two]
theorem σ₂_transpose : σ₂ᵀ = -σ₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂]
theorem τ₂_transpose : τ₂ᵀ = τ₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [τ₂]
theorem κ₂_transpose : κ₂ᵀ = κ₂ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [κ₂]

theorem neg_kronecker' {l m p q : Type*} (A : Matrix l m ℝ) (B : Matrix p q ℝ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by ext; simp [neg_mul]
theorem kronecker_neg' {l m p q : Type*} (A : Matrix l m ℝ) (B : Matrix p q ℝ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by ext; simp [mul_neg]
theorem transpose_kronecker' {l m p q : Type*} (A : Matrix l m ℝ) (B : Matrix p q ℝ) :
    (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := (kroneckerMap_transpose _ _ _).symm

/-- Multiply Kronecker words slot by slot and normalize with the relations of the letters. -/
macro "kron_simp" : tactic => `(tactic| simp only [← mul_kronecker_mul, one_mul, mul_one,
  σ₂_mul_σ₂, τ₂_mul_τ₂, κ₂_mul_κ₂, τ₂_mul_σ₂, κ₂_mul_σ₂, κ₂_mul_τ₂, neg_kronecker', kronecker_neg',
  neg_neg, one_kronecker_one, transpose_kronecker', σ₂_transpose, τ₂_transpose, κ₂_transpose,
  transpose_one])

/-! ### The families on `ℝ²`, `ℝ⁴`, `ℝ⁸`, `ℝ¹⁶` -/

/-- One complex structure on `ℝ²`. -/
def bott2 : ℕ → Matrix (Fin 2) (Fin 2) ℝ
  | 1 => σ₂
  | _ => 0

/-- Three anticommuting complex structures on `ℝ⁴ = ℝ² ⊗ ℝ²` (the quaternions `i, j, k`). -/
def bott4 : ℕ → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ
  | 1 => 1 ⊗ₖ σ₂
  | 2 => σ₂ ⊗ₖ τ₂
  | 3 => σ₂ ⊗ₖ κ₂
  | _ => 0

/-- The index type of `ℝ⁸ = ℝ² ⊗ ℝ² ⊗ ℝ²`. -/
abbrev I8 := (Fin 2 × Fin 2) × Fin 2

/-- Seven anticommuting complex structures on `ℝ⁸` (the octonions). -/
def bott8 : ℕ → Matrix I8 I8 ℝ
  | 1 => (1 ⊗ₖ 1) ⊗ₖ σ₂
  | 2 => (1 ⊗ₖ σ₂) ⊗ₖ τ₂
  | 3 => (σ₂ ⊗ₖ 1) ⊗ₖ κ₂
  | 4 => (σ₂ ⊗ₖ τ₂) ⊗ₖ τ₂
  | 5 => (σ₂ ⊗ₖ κ₂) ⊗ₖ τ₂
  | 6 => (τ₂ ⊗ₖ σ₂) ⊗ₖ κ₂
  | 7 => (κ₂ ⊗ₖ σ₂) ⊗ₖ κ₂
  | _ => 0

/-- The index type of `ℝ¹⁶ = (ℝ²)^{⊗4}`. -/
abbrev I16 := I8 × Fin 2

/-- **Eight anticommuting complex structures on `ℝ¹⁶`**: `J'_α = (seven on ℝ⁸) ⊗ τ₂` for
`α ≤ 7`, and `J'_8 = 1 ⊗ σ₂`. -/
def bott16 : ℕ → Matrix I16 I16 ℝ
  | 1 => ((1 ⊗ₖ 1) ⊗ₖ σ₂) ⊗ₖ τ₂
  | 2 => ((1 ⊗ₖ σ₂) ⊗ₖ τ₂) ⊗ₖ τ₂
  | 3 => ((σ₂ ⊗ₖ 1) ⊗ₖ κ₂) ⊗ₖ τ₂
  | 4 => ((σ₂ ⊗ₖ τ₂) ⊗ₖ τ₂) ⊗ₖ τ₂
  | 5 => ((σ₂ ⊗ₖ κ₂) ⊗ₖ τ₂) ⊗ₖ τ₂
  | 6 => ((τ₂ ⊗ₖ σ₂) ⊗ₖ κ₂) ⊗ₖ τ₂
  | 7 => ((κ₂ ⊗ₖ σ₂) ⊗ₖ κ₂) ⊗ₖ τ₂
  | 8 => ((1 ⊗ₖ 1) ⊗ₖ 1) ⊗ₖ σ₂
  | _ => 0

theorem bott16_eq_kronecker {α : ℕ} (h1 : 1 ≤ α) (h7 : α ≤ 7) : bott16 α = bott8 α ⊗ₖ τ₂ := by
  interval_cases α <;> rfl

theorem isAnticommFamily_bott2 : IsAnticommFamily bott2 1 where
  cs α h1 h2 := by
    obtain rfl : α = 1 := by omega
    exact isComplexStructure_iff.2 ⟨σ₂_transpose, σ₂_mul_σ₂⟩
  anti α β h1 h2 h3 h4 hab := by omega

theorem isAnticommFamily_bott4 : IsAnticommFamily bott4 3 where
  cs α h1 h2 := by
    rw [isComplexStructure_iff]
    interval_cases α <;> exact ⟨by simp only [bott4]; kron_simp, by simp only [bott4]; kron_simp⟩
  anti α β h1 h2 h3 h4 hab := by
    interval_cases α <;> interval_cases β <;>
      first | exact absurd rfl hab | (simp only [bott4]; kron_simp)

theorem isAnticommFamily_bott8 : IsAnticommFamily bott8 7 where
  cs α h1 h2 := by
    rw [isComplexStructure_iff]
    interval_cases α <;> exact ⟨by simp only [bott8]; kron_simp, by simp only [bott8]; kron_simp⟩
  anti α β h1 h2 h3 h4 hab := by
    interval_cases α <;> interval_cases β <;>
      first | exact absurd rfl hab | (simp only [bott8]; kron_simp)

/-- **`ℝ¹⁶` carries eight anticommuting complex structures.** -/
theorem isAnticommFamily_bott16 : IsAnticommFamily bott16 8 where
  cs α h1 h2 := by
    rw [isComplexStructure_iff]
    interval_cases α <;> exact ⟨by simp only [bott16]; kron_simp, by simp only [bott16]; kron_simp⟩
  anti α β h1 h2 h3 h4 hab := by
    interval_cases α <;> interval_cases β <;>
      first | exact absurd rfl hab | (simp only [bott16]; kron_simp)

/-! ### Transporting families -/

section Transport

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem IsAnticommFamily.mono {J : ℕ → Matrix n n ℝ} {k k' : ℕ} (h : IsAnticommFamily J k)
    (hk : k' ≤ k) : IsAnticommFamily J k' :=
  ⟨fun α h1 h2 => h.cs α h1 (h2.trans hk),
    fun α β h1 h2 h3 h4 hab => h.anti α β h1 (h2.trans hk) h3 (h4.trans hk) hab⟩

theorem IsAnticommFamily.isClifford {J : ℕ → Matrix n n ℝ} {k : ℕ} (h : IsAnticommFamily J k) :
    IsClifford J k := ⟨fun α h1 h2 => (h.cs α h1 h2).2, h.anti⟩

/-- A ring homomorphism of matrix algebras compatible with transposition carries anticommuting
complex structures to anticommuting complex structures. -/
theorem IsAnticommFamily.of_ringHom {m : Type*} [Fintype m] [DecidableEq m]
    {J : ℕ → Matrix n n ℝ} {k : ℕ} (h : IsAnticommFamily J k)
    (f : Matrix n n ℝ →+* Matrix m m ℝ) (hf : ∀ A, (f A)ᵀ = f Aᵀ) :
    IsAnticommFamily (fun α => f (J α)) k := by
  refine ⟨fun α h1 h2 => ?_, fun α β h1 h2 h3 h4 hab => ?_⟩
  · have hc := isComplexStructure_iff.1 (h.cs α h1 h2)
    rw [isComplexStructure_iff]
    exact ⟨by rw [hf, hc.1, map_neg], by rw [← map_mul, hc.2, map_neg, map_one]⟩
  · rw [← map_mul, ← map_mul, h.anti α β h1 h2 h3 h4 hab, map_neg]

/-- Renaming the coordinates of `ℝⁿ`. -/
theorem IsAnticommFamily.reindex {m : Type*} [Fintype m] [DecidableEq m] {J : ℕ → Matrix n n ℝ}
    {k : ℕ} (h : IsAnticommFamily J k) (e : n ≃ m) :
    IsAnticommFamily (fun α => Matrix.reindex e e (J α)) k :=
  h.of_ringHom (reindexAlgEquiv ℝ ℝ e).toRingEquiv.toRingHom fun A => by simp

/-- Milnor's `J_α ⊕ ⋯ ⊕ J_α` on `ℝⁿ ⊗ ℝ^r`. -/
theorem IsAnticommFamily.blockDiagonal {o : Type*} [Fintype o] [DecidableEq o]
    {J : ℕ → Matrix n n ℝ} {k : ℕ} (h : IsAnticommFamily J k) :
    IsAnticommFamily (fun α => Matrix.blockDiagonal fun _ : o => J α) k :=
  h.of_ringHom
    { toFun := fun A => Matrix.blockDiagonal fun _ : o => A
      map_one' := blockDiagonal_one
      map_mul' := fun _ _ => blockDiagonal_mul _ _
      map_zero' := blockDiagonal_zero
      map_add' := fun _ _ => blockDiagonal_add _ _ }
    fun A => blockDiagonal_transpose (fun _ : o => A)

/-- **`ℝ^{16r}` carries eight anticommuting complex structures** (Milnor's `n = 16r`, p. 139). -/
theorem isAnticommFamily_bott16r (r : ℕ) :
    IsAnticommFamily (fun α => Matrix.blockDiagonal fun _ : Fin r => bott16 α) 8 :=
  isAnticommFamily_bott16.blockDiagonal

variable {n' : Type*} [Fintype n'] [DecidableEq n']

/-- `J_α ⊕ J'_α` on `ℝⁿ ⊕ ℝ^{n'}`. -/
theorem IsAnticommFamily.fromBlocks {J : ℕ → Matrix n n ℝ} {J' : ℕ → Matrix n' n' ℝ} {k : ℕ}
    (h : IsAnticommFamily J k) (h' : IsAnticommFamily J' k) :
    IsAnticommFamily (fun α => Matrix.fromBlocks (J α) 0 0 (J' α)) k := by
  refine ⟨fun α h1 h2 => ?_, fun α β h1 h2 h3 h4 hab => ?_⟩
  · have hc := isComplexStructure_iff.1 (h.cs α h1 h2)
    have hc' := isComplexStructure_iff.1 (h'.cs α h1 h2)
    rw [isComplexStructure_iff]
    refine ⟨by simp [fromBlocks_transpose, hc.1, hc'.1, fromBlocks_neg], ?_⟩
    rw [fromBlocks_multiply]
    simp [hc.2, hc'.2, ← fromBlocks_one, fromBlocks_neg]
  · simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      h.anti α β h1 h2 h3 h4 hab, h'.anti α β h1 h2 h3 h4 hab, fromBlocks_neg, neg_zero]

/-- **Milnor's imbedding** (p. 138): `J ↦ J ⊕ J'` carries `Ω_k(n) × Ω_k(n')` into `Ω_k(n + n')`
for the structures `J_α ⊕ J'_α`; with `J' = J'_k` this is `Ω_k(n) → Ω_k(n + n')`. -/
theorem fromBlocks_mem_omega {J : ℕ → Matrix n n ℝ} {J' : ℕ → Matrix n' n' ℝ} {k : ℕ}
    {P : Matrix n n ℝ} {P' : Matrix n' n' ℝ} (hP : P ∈ Omega J k) (hP' : P' ∈ Omega J' k) :
    Matrix.fromBlocks P 0 0 P' ∈ Omega (fun α => Matrix.fromBlocks (J α) 0 0 (J' α)) k := by
  cases k with
  | zero =>
    change _ ∈ orthogonalGroup _ ℝ
    have h1 : Pᵀ * P = 1 := (mem_orthogonalGroup_iff' n ℝ).1 hP
    have h2 : P'ᵀ * P' = 1 := (mem_orthogonalGroup_iff' n' ℝ).1 hP'
    rw [mem_orthogonalGroup_iff', fromBlocks_transpose, fromBlocks_multiply]
    simp [h1, h2, ← fromBlocks_one]
  | succ k =>
    obtain ⟨hc, ha⟩ := hP
    obtain ⟨hc', ha'⟩ := hP'
    have hc1 := isComplexStructure_iff.1 hc
    have hc1' := isComplexStructure_iff.1 hc'
    refine ⟨?_, fun α h1 h2 => ?_⟩
    · rw [isComplexStructure_iff]
      refine ⟨by simp [fromBlocks_transpose, hc1.1, hc1'.1, fromBlocks_neg], ?_⟩
      rw [fromBlocks_multiply]
      simp [hc1.2, hc1'.2, ← fromBlocks_one, fromBlocks_neg]
    · simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
        ha α h1 h2, ha' α h1 h2, fromBlocks_neg, neg_zero]

end Transport

/-! ### `ℝ^{m_k}` carries `k` structures -/

/-- Milnor's `m_k` (p. 143): `m_0 = 1, m_1 = 2, m_2 = m_3 = 4, m_4 = ⋯ = m_7 = 8, m_8 = 16`, and
`m_{k+8} = 16 m_k`. -/
def milnorM : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 4
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | 7 => 8
  | k + 8 => 16 * milnorM k

/-- For `k ≤ 8`, `ℝ^{m_k}` carries `k` anticommuting complex structures. -/
theorem exists_isAnticommFamily_fin {k : ℕ} (hk : k ≤ 8) :
    ∃ J : ℕ → Matrix (Fin (milnorM k)) (Fin (milnorM k)) ℝ, IsAnticommFamily J k := by
  have e4 : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  have e8 : I8 ≃ Fin 8 := Fintype.equivFinOfCardEq (by simp)
  have e16 : I16 ≃ Fin 16 := Fintype.equivFinOfCardEq (by simp)
  interval_cases k
  · exact ⟨fun _ => 0, ⟨fun α h1 h2 => by omega, fun α β h1 h2 => by omega⟩⟩
  · exact ⟨bott2, isAnticommFamily_bott2⟩
  · exact ⟨_, (isAnticommFamily_bott4.mono (by norm_num)).reindex e4⟩
  · exact ⟨_, isAnticommFamily_bott4.reindex e4⟩
  · exact ⟨_, (isAnticommFamily_bott8.mono (by norm_num)).reindex e8⟩
  · exact ⟨_, (isAnticommFamily_bott8.mono (by norm_num)).reindex e8⟩
  · exact ⟨_, (isAnticommFamily_bott8.mono (by norm_num)).reindex e8⟩
  · exact ⟨_, isAnticommFamily_bott8.reindex e8⟩
  · exact ⟨_, isAnticommFamily_bott16.reindex e16⟩

/-! ### Vector fields on spheres (Remark, pp. 143–144) -/

section VectorFields

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem dotProduct_mulVec_eq (A B : Matrix n n ℝ) (u v : n → ℝ) :
    (A *ᵥ u) ⬝ᵥ (B *ᵥ v) = u ⬝ᵥ ((Aᵀ * B) *ᵥ v) := by
  rw [← mulVec_mulVec, dotProduct_mulVec u Aᵀ, vecMul_transpose]

omit [DecidableEq n] in
theorem dotProduct_mulVec_self_eq_zero {S : Matrix n n ℝ} (hS : Sᵀ = -S) (u : n → ℝ) :
    u ⬝ᵥ (S *ᵥ u) = 0 := by
  have h : u ⬝ᵥ (S *ᵥ u) = -(u ⬝ᵥ (S *ᵥ u)) := by
    conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]
    rw [neg_mulVec, dotProduct_neg]
  linarith

/-- `J u ⟂ u`. -/
theorem IsComplexStructure.dotProduct_mulVec_self {J : Matrix n n ℝ} (h : IsComplexStructure J)
    (u : n → ℝ) : (J *ᵥ u) ⬝ᵥ u = 0 := by
  rw [dotProduct_comm]; exact dotProduct_mulVec_self_eq_zero h.transpose u

/-- `|J u| = |u|`. -/
theorem IsComplexStructure.dotProduct_mulVec_mulVec {J : Matrix n n ℝ} (h : IsComplexStructure J)
    (u : n → ℝ) : (J *ᵥ u) ⬝ᵥ (J *ᵥ u) = u ⬝ᵥ u := by
  rw [dotProduct_mulVec_eq, h.transpose_mul_self, one_mulVec]

/-- `J u ⟂ J' u` for anticommuting complex structures. -/
theorem dotProduct_mulVec_of_anticomm {J J' : Matrix n n ℝ} (h : IsComplexStructure J)
    (h' : IsComplexStructure J') (hanti : J * J' = -(J' * J)) (u : n → ℝ) :
    (J *ᵥ u) ⬝ᵥ (J' *ᵥ u) = 0 := by
  rw [dotProduct_mulVec_eq, h.transpose, Matrix.neg_mul, neg_mulVec, dotProduct_neg, neg_eq_zero]
  apply dotProduct_mulVec_self_eq_zero
  rw [transpose_mul, h.transpose, h'.transpose, neg_mul_neg, hanti, neg_neg]

/-- **Remark, pp. 143–144**: for anticommuting complex structures `J_1, …, J_k`, the vectors
`J_1u, …, J_ku` satisfy `⟨J_αu, J_βu⟩ = δ_{αβ}|u|²` and are perpendicular to `u`; for `|u| = 1`
they are `k` orthonormal tangent vectors to the unit sphere at `u`. -/
theorem IsAnticommFamily.dotProduct_mulVec {J : ℕ → Matrix n n ℝ} {k : ℕ}
    (h : IsAnticommFamily J k) {α β : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ k) (h3 : 1 ≤ β) (h4 : β ≤ k)
    (u : n → ℝ) : (J α *ᵥ u) ⬝ᵥ (J β *ᵥ u) = if α = β then u ⬝ᵥ u else 0 := by
  split_ifs with hab
  · subst hab; exact (h.cs α h1 h2).dotProduct_mulVec_mulVec u
  · exact dotProduct_mulVec_of_anticomm (h.cs α h1 h2) (h.cs β h3 h4) (h.anti α β h1 h2 h3 h4 hab) u

/-- Milnor's example: eight orthonormal tangent vector fields on the unit sphere `S^{16r−1}` of
`ℝ^{16r}`, `u ↦ J_αu`. -/
theorem bott16r_vectorFields (r : ℕ) (u : I16 × Fin r → ℝ) {α β : ℕ} (h1 : 1 ≤ α) (h2 : α ≤ 8)
    (h3 : 1 ≤ β) (h4 : β ≤ 8) :
    ((Matrix.blockDiagonal fun _ : Fin r => bott16 α) *ᵥ u) ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin r => bott16 β) *ᵥ u) = (if α = β then u ⬝ᵥ u else 0) ∧
      ((Matrix.blockDiagonal fun _ : Fin r => bott16 α) *ᵥ u) ⬝ᵥ u = 0 :=
  ⟨(isAnticommFamily_bott16r r).dotProduct_mulVec h1 h2 h3 h4 u,
    ((isAnticommFamily_bott16r r).cs α h1 h2).dotProduct_mulVec_self u⟩

end VectorFields

end Morse
