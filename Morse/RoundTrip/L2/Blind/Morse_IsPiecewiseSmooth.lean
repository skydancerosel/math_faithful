import Morse
/-! Layer-2 blind definition of Morse_IsPiecewiseSmooth. Textbook: Milnor, *Morse Theory*, §10,
p. 59 and §13, p. 67: `c : [a, b] → N` is piecewise smooth if it is continuous and there is a
subdivision `a = t₀ < t₁ < ⋯ < t_k = b` such that `c` restricted to each closed subinterval
`[t_{i-1}, t_i]` is smooth (`C^∞`, with one-sided derivatives at the end points).
Choices: `c : ℝ → V`, only its values on `[a, b]` matter. "Smooth on `[t_{i-1}, t_i]`" is
Mathlib's `ContDiffOn ℝ ∞ c (Icc t_{i-1} t_i)` (derivatives within the closed interval, i.e.
one-sided at its end points). The subdivision is a strictly increasing `t : Fin (k + 1) → ℝ` with
`t 0 = a`, `t k = b`. Outside the textbook's hypothesis `a < b`: for `a = b` the subdivision with
`k = 0` exists and every `c` is piecewise smooth; for `a > b` no subdivision exists and `T` is
`False`. Continuity on `[a, b]` is stated explicitly (it also follows from smoothness on the
finitely many closed pieces). -/
namespace RoundTrip.L2.Morse_IsPiecewiseSmooth

open scoped ContDiff
open Set

/-- The textbook notion: `c` is piecewise smooth on `[a, b]`. -/
def T {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (c : ℝ → V) (a b : ℝ) : Prop :=
  ContinuousOn c (Icc a b) ∧
    ∃ k : ℕ, ∃ t : Fin (k + 1) → ℝ, StrictMono t ∧ t 0 = a ∧ t (Fin.last k) = b ∧
      ∀ i : Fin k, ContDiffOn ℝ ∞ c (Icc (t i.castSucc) (t i.succ))

end RoundTrip.L2.Morse_IsPiecewiseSmooth
