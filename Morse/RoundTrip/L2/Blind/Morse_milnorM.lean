import Morse
/-! Layer-2 blind definition of Morse_milnorM. Textbook: Milnor, *Morse Theory*, §24, p. 143: `m_k`
is the dimension of a minimal (irreducible) space `ℝⁿ ≠ 0` carrying `k` anticommuting complex
structures `J₁, …, J_k` (a Clifford module); Milnor quotes the values `1, 2, 4, 4, 8, 8, 8, 8, 16`
for `k = 0, …, 8` and `m_{k+8} = 16 m_k`.
Choices: `m_k` is defined as the LEAST positive `n` such that `ℝⁿ` carries `k` anticommuting
complex structures (orthogonal, `J² = −I`, pairwise anticommuting; indexed `J 1, …, J k`, `J 0`
unused). A space of least positive dimension is minimal (an invariant proper subspace would carry
the restricted structures), and all minimal spaces have the same dimension (Clifford module
theory), so this is Milnor's `m_k`; the table and the 8-periodicity are theorems, not used in the
definition. The set is never empty (`sInf ∅ = 0` is never reached); `m_0 = 1` (no structures, a
line). -/
namespace RoundTrip.L2.Morse_milnorM

/-- A complex structure (Milnor p. 133): orthogonal with `J² = −I`. -/
def IsCplxStr {n : Type*} [Fintype n] [DecidableEq n] (J : Matrix n n ℝ) : Prop :=
  J ∈ Matrix.orthogonalGroup n ℝ ∧ J * J = -1

/-- `J 1, …, J k` are pairwise anticommuting complex structures (Milnor p. 136). -/
def IsACFam {n : Type*} [Fintype n] [DecidableEq n] (J : ℕ → Matrix n n ℝ) (k : ℕ) : Prop :=
  (∀ α, 1 ≤ α → α ≤ k → IsCplxStr (J α)) ∧
  ∀ α β, 1 ≤ α → α ≤ k → 1 ≤ β → β ≤ k → α ≠ β → J α * J β = -(J β * J α)

/-- The textbook notion: the least `n > 0` such that `ℝⁿ` carries `k` anticommuting complex
structures. -/
noncomputable def T (k : ℕ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∃ J : ℕ → Matrix (Fin n) (Fin n) ℝ, IsACFam J k}

end RoundTrip.L2.Morse_milnorM
