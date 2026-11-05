import Morse.Chapter15.Stabilization

/-!
Milnor, *Morse Theory*, §24, Lemma 24.6 (8) (p. 142): the eighth space; Exposition/Chapter15.md,
§4, Lemma 24.6-(8).

# The commutant of `J'_1, …, J'_7` on `ℝ¹⁶`

## Milnor's text, paraphrased

(p. 142) "`Ω_8(16r)` is homeomorphic to `O(r)`": `J_7J_8` commutes with `J_1, …, J_6`,
anticommutes with `θ₇`, and is determined by its restriction to a joint eigenspace `X_1 ≅ ℝ^r`.

## What is formalized

The key fact behind Lemma 24.6 (8) for the explicit structures `J'_α` (Kronecker words in
`σ, τ, κ`): **the matrices commuting with `J'_1, …, J'_7` are exactly `b·1 + c·W`**, where
`W = 1 ⊗ 1 ⊗ 1 ⊗ τ` (`Morse.eq_of_commute_bott16`).  The proof uses the "Pauli basis":

* `Morse.kword w` (`w : Fin 4 → Fin 4`): the Kronecker words in the letters `1, σ, τ, κ`;
  `Morse.trace_word_pair` (orthogonality for the trace form), `Morse.wordBasis` (**a basis of
  `M₁₆(ℝ)`**, 256 independent words).
* `Morse.word_comm`: two words commute or anticommute, according to the parity of the number of
  slots with different non-identity letters (`Morse.wanti`); conjugation by `J'_α` is diagonal in
  the kword basis, so a matrix commuting with `J'_1, …, J'_7` only involves words commuting with
  all seven, which are `1` and `W` (a finite check, `decide`).
* `Morse.W16`: `W² = 1`, `Wᵀ = W`, `W` commutes with `J'_1, …, J'_7` and anticommutes with `J'_8`.

## What Milnor leaves implicit

* Milnor's description via the joint eigenspace `X_1` of `θ₃, θ₅, θ₆, θ₇` is replaced by the
  equivalent statement that the commutant of the Clifford action of `J'_1, …, J'_7` on `ℝ¹⁶` is
  `ℝ ⊕ ℝ` (the two eigenspaces of `W = ±J'_1⋯J'_7`).
-/

open Matrix
open scoped Kronecker

noncomputable section

namespace Morse

/-- The letters `1, σ, τ, κ`. -/
def kletter : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ := ![1, σ₂, τ₂, κ₂]

/-- The Kronecker word `L(w₀) ⊗ L(w₁) ⊗ L(w₂) ⊗ L(w₃)` on `ℝ¹⁶`. -/
def kword (w : Fin 4 → Fin 4) : Matrix I16 I16 ℝ :=
  ((kletter (w 0) ⊗ₖ kletter (w 1)) ⊗ₖ kletter (w 2)) ⊗ₖ kletter (w 3)

theorem trace_letter_pair (a b : Fin 4) :
    trace ((kletter a)ᵀ * kletter b) = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [kletter, σ₂, τ₂, κ₂, trace, Fin.sum_univ_two, mul_apply] <;> norm_num

theorem trace_word_pair (u v : Fin 4 → Fin 4) :
    trace ((kword u)ᵀ * kword v) = if u = v then 16 else 0 := by
  simp only [kword, transpose_kronecker', ← mul_kronecker_mul, trace_kronecker, trace_letter_pair]
  by_cases h : u = v
  · subst h; simp; norm_num
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
    rw [if_neg h]
    fin_cases i <;> simp_all

theorem linearIndependent_word : LinearIndependent ℝ kword := by
  rw [Fintype.linearIndependent_iff]
  intro c hc v
  have := congrArg (fun M => trace ((kword v)ᵀ * M)) hc
  simp only [Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, trace_word_pair,
    smul_eq_mul, mul_ite, mul_zero, trace_zero] at this
  rw [Finset.sum_ite_eq] at this
  simpa using this

theorem card_word : Fintype.card (Fin 4 → Fin 4) = Module.finrank ℝ (Matrix I16 I16 ℝ) := by
  simp [Module.finrank_matrix]

/-- **The Kronecker words form a basis of `M₁₆(ℝ)`.** -/
def wordBasis : Module.Basis (Fin 4 → Fin 4) ℝ (Matrix I16 I16 ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank linearIndependent_word card_word

theorem wordBasis_apply (w : Fin 4 → Fin 4) : wordBasis w = kword w :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) w

/-- `a` and `b` anticommute (different non-identity letters). -/
def lanti (a b : Fin 4) : Bool := !(a = 0 || b = 0 || a = b)

/-- The two words anticommute (odd number of anticommuting slots). -/
def wanti (u v : Fin 4 → Fin 4) : Bool :=
  xor (xor (lanti (u 0) (v 0)) (lanti (u 1) (v 1))) (xor (lanti (u 2) (v 2)) (lanti (u 3) (v 3)))

/-- The sign `±1` of a Boolean. -/
def bsgn (b : Bool) : ℝ := if b then -1 else 1

theorem bsgn_xor (a b : Bool) : bsgn (xor a b) = bsgn a * bsgn b := by
  cases a <;> cases b <;> simp [bsgn]

theorem letter_comm (a b : Fin 4) :
    kletter a * kletter b = bsgn (lanti a b) • (kletter b * kletter a) := by
  fin_cases a <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [kletter, lanti, bsgn, σ₂, τ₂, κ₂, mul_apply, Fin.sum_univ_two]

/-- **Two words commute or anticommute.** -/
theorem word_comm (u v : Fin 4 → Fin 4) :
    kword u * kword v = bsgn (wanti u v) • (kword v * kword u) := by
  simp only [kword, ← mul_kronecker_mul, letter_comm (u 0), letter_comm (u 1), letter_comm (u 2),
    letter_comm (u 3), smul_kronecker, kronecker_smul, smul_smul, wanti, bsgn_xor]
  congr 1
  ring

/-- The codes of `J'_1, …, J'_8`. -/
def bottCode : ℕ → Fin 4 → Fin 4
  | 1 => ![0, 0, 1, 2]
  | 2 => ![0, 1, 2, 2]
  | 3 => ![1, 0, 3, 2]
  | 4 => ![1, 2, 2, 2]
  | 5 => ![1, 3, 2, 2]
  | 6 => ![2, 1, 3, 2]
  | 7 => ![3, 1, 3, 2]
  | 8 => ![0, 0, 0, 1]
  | _ => 0

theorem bott16_eq_word {α : ℕ} (h1 : 1 ≤ α) (h8 : α ≤ 8) : bott16 α = kword (bottCode α) := by
  interval_cases α <;> simp [bott16, kword, bottCode, kletter]

/-- The code `(0, 0, 0, 2)` of `W = 1 ⊗ 1 ⊗ 1 ⊗ τ`. -/
def wCode : Fin 4 → Fin 4 := ![0, 0, 0, 2]

/-- **`W = 1 ⊗ 1 ⊗ 1 ⊗ τ`**, the generator of the commutant of `J'_1, …, J'_7` besides `1`. -/
def W16 : Matrix I16 I16 ℝ := kword wCode

/-- **The finite check**: the only words commuting with the codes of `J'_1, …, J'_7` are `1` and
`W`. -/
theorem eq_of_not_wanti_aux : ∀ a b c d : Fin 4,
    (∀ α ∈ [1, 2, 3, 4, 5, 6, 7], wanti (bottCode α) ![a, b, c, d] = false) →
      (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 2) := by
  decide

theorem eq_of_not_wanti (u : Fin 4 → Fin 4)
    (h : ∀ α ∈ [1, 2, 3, 4, 5, 6, 7], wanti (bottCode α) u = false) : u = 0 ∨ u = wCode := by
  have hu : u = ![u 0, u 1, u 2, u 3] := by
    funext i; fin_cases i <;> rfl
  rw [hu] at h
  rcases eq_of_not_wanti_aux _ _ _ _ h with ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩
  · left; rw [hu, h0, h1, h2, h3]; funext i; fin_cases i <;> rfl
  · right; rw [hu, h0, h1, h2, h3]; funext i; fin_cases i <;> rfl

theorem word_zero : kword 0 = 1 := by
  simp [kword, kletter]

/-- **The commutant of `J'_1, …, J'_7` on `ℝ¹⁶` is spanned by `1` and `W`.** -/
theorem eq_of_commute_bott16 {X : Matrix I16 I16 ℝ}
    (hX : ∀ α, 1 ≤ α → α ≤ 7 → bott16 α * X = X * bott16 α) :
    X = wordBasis.repr X 0 • 1 + wordBasis.repr X wCode • W16 := by
  set c := wordBasis.repr X
  have hsum : X = ∑ u, c u • kword u := by
    conv_lhs => rw [← wordBasis.sum_repr X]
    simp only [wordBasis_apply]
    rfl
  -- conjugation by `J'_α` multiplies `kword u` by the sign
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
    -- `X = −J X J`
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

theorem W16_mul_self : W16 * W16 = 1 := by
  simp only [W16, kword, wCode, kletter, ← mul_kronecker_mul]
  simp [τ₂_mul_τ₂]

theorem W16_transpose : W16ᵀ = W16 := by
  simp only [W16, kword, wCode, kletter, transpose_kronecker']
  simp [τ₂_transpose]

theorem W16_comm {α : ℕ} (h1 : 1 ≤ α) (h7 : α ≤ 7) : bott16 α * W16 = W16 * bott16 α := by
  rw [bott16_eq_word h1 (by omega), W16, word_comm]
  interval_cases α <;> simp [wanti, bottCode, wCode, lanti, bsgn]

theorem W16_anti : bott16 8 * W16 = -(W16 * bott16 8) := by
  rw [bott16_eq_word (by norm_num) le_rfl, W16, word_comm]
  simp [wanti, bottCode, wCode, lanti, bsgn]

end Morse
