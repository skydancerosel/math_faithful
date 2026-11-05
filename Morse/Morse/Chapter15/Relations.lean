import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.IntervalCases

/-!
Milnor, *Morse Theory*, §24 (The periodicity theorem for the orthogonal group), pp. 136–143.

# Words in anticommuting square roots of `−1`

Throughout §24 Milnor computes with products of anticommuting complex structures
`J_1, J_2, …` (`J_α² = −1`, `J_α J_β = −J_β J_α` for `α ≠ β`), always by moving factors past
each other and cancelling squares.  This file isolates that bookkeeping in an arbitrary ring, so
that the same statements apply to matrices (`Morse/Chapter15/ComplexStructure.lean`) and to
endomorphisms of abstract vector spaces (`Morse/Chapter15/CliffordModules.lean`).

* `Morse.IsClifford J k`: `J 1, …, J k` satisfy the relations above (the relations of the
  Clifford algebra `C_k`, Milnor's footnote on p. 136).
* Two tactics normalize words: `word_simp [h₁, …]` rewrites with the given relations (and their
  re-associated forms), `clifford_simp h` with all the relations of an `IsClifford` family, the
  side conditions on indices being discharged by `omega`.

## Milnor's products, paraphrased (pp. 139–143)

* p. 139: `J_1J_2J_3` is an orthogonal transformation with square `+I` commuting with `J_1`,
  `J_2`; `J_3J_4` anticommutes with `J_1J_2J_3` and commutes with `J_1`, `J_2`.
* p. 140: `J_1J_4J_5` commutes with `J_1J_2J_3` and has square `+I`; `J_2` anticommutes with
  it.  `J_2J_4J_6` commutes with `J_1J_2J_3` and with `J_1J_4J_5`, with square `+I`.
* p. 141: `J_1J_6J_7` commutes with `J_1J_2J_3`, `J_1J_4J_5`, `J_2J_4J_6` and has square `+I`;
  `J_7J_8` commutes with the first three and anticommutes with `J_1J_6J_7`.
* p. 143: for `k = 7` the two minimal spaces are told apart by `J_7 = ±J_1⋯J_6`, i.e. by
  `J_1⋯J_7 = ±I`.

All of these are proved here: `Morse.θ₃_spec`, `Morse.θ₅_spec`, `Morse.θ₆_spec`,
`Morse.θ₇_spec`, `Morse.J₇J₈_spec`, `Morse.J₃J₄_spec`, with the complete "commute/anticommute"
table of the exposition (Chapter 15, §4): `J_α` commutes with `θ_{abc}` iff `α ∈ {a,b,c}`
(`Morse.θ₃_anticommute` etc. for the indices beyond those listed).  `Morse.ω₇_spec`:
`J_1⋯J_7 = −θ₃θ₅θ₇` commutes with every `J_α`, `α ≤ 7`, which is why it is `±I` on a minimal
space.  Milnor states these facts without proof ("clearly", "it is easy to see").
-/

namespace Morse

theorem mul_assoc_of_eq {R : Type*} [Semigroup R] {x y z : R} (h : x * y = z) (w : R) :
    x * (y * w) = z * w := by rw [← mul_assoc, h]

/-- `word_simp [h₁, …, hₙ]` normalizes products (right-associated, signs pulled out) using the
relations `hᵢ : x * y = z` and their re-associated forms `x * (y * w) = z * w`. -/
syntax "word_simp" " [" term,* "]" : tactic
macro_rules
  | `(tactic| word_simp [$rels,*]) => do
    let rels := rels.getElems
    let assoc ← rels.mapM fun r => `(mul_assoc_of_eq $r)
    let all := rels ++ assoc
    let args ← all.mapM fun r => `(Lean.Parser.Tactic.simpLemma| $r:term)
    `(tactic| (set_option linter.unusedSimpArgs false in
       simp only [neg_mul, mul_neg, neg_neg, mul_assoc, one_mul, mul_one, $args,*]))

variable {R : Type*} [Ring R]

/-- `J 1, …, J k` are anticommuting square roots of `−1`: the relations of the Clifford algebra
`C_k` (Milnor's footnote, p. 136). -/
structure IsClifford (J : ℕ → R) (k : ℕ) : Prop where
  sq : ∀ a, 1 ≤ a → a ≤ k → J a * J a = -1
  anti : ∀ a b, 1 ≤ a → a ≤ k → 1 ≤ b → b ≤ k → a ≠ b → J a * J b = -(J b * J a)

namespace IsClifford

variable {J : ℕ → R} {k : ℕ} (h : IsClifford J k)
include h

theorem swap {a b : ℕ} (hb : 1 ≤ b) (hba : b < a) (ha : a ≤ k) : J a * J b = -(J b * J a) :=
  h.anti a b (hb.trans hba.le) ha hb (hba.le.trans ha) hba.ne'

theorem swap_assoc {a b : ℕ} (hb : 1 ≤ b) (hba : b < a) (ha : a ≤ k) (x : R) :
    J a * (J b * x) = -(J b * (J a * x)) := by
  rw [← mul_assoc, h.swap hb hba ha, neg_mul, mul_assoc]

theorem sq' {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ k) : J a * J a = -1 := h.sq a ha1 ha

theorem sq_assoc {a : ℕ} (ha1 : 1 ≤ a) (ha : a ≤ k) (x : R) : J a * (J a * x) = -x := by
  rw [← mul_assoc, h.sq a ha1 ha, neg_one_mul]

theorem mono {k' : ℕ} (hk : k' ≤ k) : IsClifford J k' :=
  ⟨fun a h1 h2 => h.sq a h1 (h2.trans hk),
    fun a b h1 h2 h3 h4 hab => h.anti a b h1 (h2.trans hk) h3 (h4.trans hk) hab⟩

end IsClifford

/-- `clifford_simp h`, for `h : IsClifford J k`, normalizes words in the `J α` (sorted indices,
squares cancelled, signs pulled out). -/
syntax "clifford_simp" ident : tactic
macro_rules
  | `(tactic| clifford_simp $h) =>
    `(tactic| (set_option linter.unusedSimpArgs false in
       simp (disch := omega) only [neg_mul, mul_neg, neg_neg, mul_assoc, one_mul, mul_one,
        IsClifford.swap $h, IsClifford.swap_assoc $h, IsClifford.sq' $h, IsClifford.sq_assoc $h]))

/-- `x` and `y` anticommute. -/
def AntiCommute (x y : R) : Prop := x * y = -(y * x)

section Theta

variable (J : ℕ → R)

/-- Milnor's `J_1J_2J_3` (p. 139). -/
def θ₃ : R := J 1 * J 2 * J 3
/-- Milnor's `J_1J_4J_5` (p. 140). -/
def θ₅ : R := J 1 * J 4 * J 5
/-- Milnor's `J_2J_4J_6` (p. 140). -/
def θ₆ : R := J 2 * J 4 * J 6
/-- Milnor's `J_1J_6J_7` (p. 141). -/
def θ₇ : R := J 1 * J 6 * J 7
/-- `ω₇ = J_1J_2⋯J_7` (p. 143). -/
def ω₇ : R := J 1 * J 2 * J 3 * J 4 * J 5 * J 6 * J 7

variable {J}

/-- p. 139: `J_1J_2J_3` has square `+I` and commutes with `J_1`, `J_2` (and `J_3`). -/
theorem θ₃_spec (h : IsClifford J 3) :
    θ₃ J * θ₃ J = 1 ∧ Commute (θ₃ J) (J 1) ∧ Commute (θ₃ J) (J 2) ∧ Commute (θ₃ J) (J 3) := by
  unfold θ₃ Commute SemiconjBy; refine ⟨?_, ?_, ?_, ?_⟩ <;> clifford_simp h

theorem θ₃_anticommute {k α : ℕ} (h : IsClifford J k) (h4 : 4 ≤ α) (hk : α ≤ k) :
    AntiCommute (θ₃ J) (J α) := by
  unfold AntiCommute θ₃; clifford_simp h

/-- p. 140: `J_1J_4J_5` has square `+I`, commutes with `J_1J_2J_3`, and `J_2` anticommutes with
it. -/
theorem θ₅_spec (h : IsClifford J 5) :
    θ₅ J * θ₅ J = 1 ∧ Commute (θ₅ J) (J 1) ∧ Commute (θ₅ J) (J 4) ∧ Commute (θ₅ J) (J 5) ∧
      AntiCommute (θ₅ J) (J 2) ∧ AntiCommute (θ₅ J) (J 3) ∧ Commute (θ₅ J) (θ₃ J) := by
  unfold θ₅ θ₃ Commute SemiconjBy AntiCommute
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> clifford_simp h

theorem θ₅_anticommute {k α : ℕ} (h : IsClifford J k) (h6 : 6 ≤ α) (hk : α ≤ k) :
    AntiCommute (θ₅ J) (J α) := by
  unfold AntiCommute θ₅; clifford_simp h

/-- pp. 140–141: `J_2J_4J_6` has square `+I` and commutes with `J_1J_2J_3` and `J_1J_4J_5`;
`J_1` anticommutes with it. -/
theorem θ₆_spec (h : IsClifford J 6) :
    θ₆ J * θ₆ J = 1 ∧ Commute (θ₆ J) (J 2) ∧ Commute (θ₆ J) (J 4) ∧ Commute (θ₆ J) (J 6) ∧
      AntiCommute (θ₆ J) (J 1) ∧ AntiCommute (θ₆ J) (J 3) ∧ AntiCommute (θ₆ J) (J 5) ∧
      Commute (θ₆ J) (θ₃ J) ∧ Commute (θ₆ J) (θ₅ J) := by
  unfold θ₆ θ₃ θ₅ Commute SemiconjBy AntiCommute
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> clifford_simp h

theorem θ₆_anticommute {k α : ℕ} (h : IsClifford J k) (h7 : 7 ≤ α) (hk : α ≤ k) :
    AntiCommute (θ₆ J) (J α) := by
  unfold AntiCommute θ₆; clifford_simp h

/-- p. 141: `J_1J_6J_7` has square `+I` and commutes with `J_1J_2J_3`, `J_1J_4J_5`,
`J_2J_4J_6`. -/
theorem θ₇_spec (h : IsClifford J 7) :
    θ₇ J * θ₇ J = 1 ∧ Commute (θ₇ J) (J 1) ∧ Commute (θ₇ J) (J 6) ∧ Commute (θ₇ J) (J 7) ∧
      AntiCommute (θ₇ J) (J 2) ∧ AntiCommute (θ₇ J) (J 3) ∧ AntiCommute (θ₇ J) (J 4) ∧
      AntiCommute (θ₇ J) (J 5) ∧ Commute (θ₇ J) (θ₃ J) ∧ Commute (θ₇ J) (θ₅ J) ∧
      Commute (θ₇ J) (θ₆ J) := by
  unfold θ₇ θ₃ θ₅ θ₆ Commute SemiconjBy AntiCommute
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> clifford_simp h

theorem θ₇_anticommute {k α : ℕ} (h : IsClifford J k) (h8 : 8 ≤ α) (hk : α ≤ k) :
    AntiCommute (θ₇ J) (J α) := by
  unfold AntiCommute θ₇; clifford_simp h

/-- p. 141: `J_7J_8` commutes with `J_1J_2J_3`, `J_1J_4J_5`, `J_2J_4J_6` and anticommutes with
`J_1J_6J_7`. -/
theorem J₇J₈_spec (h : IsClifford J 8) :
    Commute (J 7 * J 8) (θ₃ J) ∧ Commute (J 7 * J 8) (θ₅ J) ∧ Commute (J 7 * J 8) (θ₆ J) ∧
      AntiCommute (J 7 * J 8) (θ₇ J) := by
  unfold θ₃ θ₅ θ₆ θ₇ Commute SemiconjBy AntiCommute
  refine ⟨?_, ?_, ?_, ?_⟩ <;> clifford_simp h

/-- pp. 139–140: `J_3J_4` anticommutes with `J_1J_2J_3` and commutes with `J_1`, `J_2`. -/
theorem J₃J₄_spec (h : IsClifford J 4) :
    AntiCommute (J 3 * J 4) (θ₃ J) ∧ Commute (J 3 * J 4) (J 1) ∧ Commute (J 3 * J 4) (J 2) := by
  unfold θ₃ Commute SemiconjBy AntiCommute
  refine ⟨?_, ?_, ?_⟩ <;> clifford_simp h

/-- p. 143: `J_1⋯J_7 = −θ₃θ₅θ₇` commutes with every `J_α`, `α ≤ 7`. -/
theorem ω₇_spec (h : IsClifford J 7) :
    ω₇ J = -(θ₃ J * θ₅ J * θ₇ J) ∧ ∀ α, 1 ≤ α → α ≤ 7 → Commute (ω₇ J) (J α) := by
  unfold ω₇ θ₃ θ₅ θ₇ Commute SemiconjBy
  refine ⟨by clifford_simp h, fun α h1 h2 => ?_⟩
  interval_cases α <;> clifford_simp h

end Theta

end Morse
