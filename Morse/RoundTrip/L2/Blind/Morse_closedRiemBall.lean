import Morse
/-! Layer-2 blind definition of Morse_closedRiemBall. Textbook: Milnor, *Morse Theory*, §10 p. 55
and §16 p. 89: the closed ball `{x ∈ N : ρ(p, x) ≤ r}` for the intrinsic distance `ρ` of `N`.
Choices: The Riemannian distance is defined from scratch: `ρ(p, q)` = infimum in `ℝ≥0∞` of the
lengths `∫⁻_{[0,1]} ‖c'(t)‖` of piecewise smooth paths `c` in `N` from `p` to `q` (`c` continuous
on `[0,1]`, `c([0,1]) ⊆ N`, `C^∞` on the closed pieces of a subdivision `0 = t₀ < … < t_k = 1`);
`ρ = ⊤` when no such path exists (different components, or a point outside `N`).
`ρ(p, x) ≤ r` is read in `ℝ`: `ρ(p, x)` finite and `(ρ(p, x)).toReal ≤ r`; so `r < 0` gives `∅`
and `p ∉ N` gives `∅` (no path, `ρ = ⊤`). `x ∈ N` is stated explicitly (it also follows from
`ρ(p, x) < ⊤`). -/
namespace RoundTrip.L2.Morse_closedRiemBall

open scoped ContDiff
open MeasureTheory Set

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `c` is a piecewise smooth path in `N`, parametrised by `[a, b]`. -/
def IsPSPath (N : Set V) (c : ℝ → V) (a b : ℝ) : Prop :=
  ContinuousOn c (Icc a b) ∧ MapsTo c (Icc a b) N ∧
    ∃ (k : ℕ) (τ : Fin (k + 1) → ℝ), τ 0 = a ∧ τ (Fin.last k) = b ∧ StrictMono τ ∧
      ∀ i : Fin k, ContDiffOn ℝ ∞ c (Icc (τ i.castSucc) (τ i.succ))

/-- Arc length `∫_a^b ‖c'(t)‖ dt` (in `ℝ≥0∞`). -/
noncomputable def len (c : ℝ → V) (a b : ℝ) : ENNReal :=
  ∫⁻ t in Icc a b, ENNReal.ofReal ‖deriv c t‖

/-- Riemannian distance `ρ(p, q)` in `N`: inf of the lengths of piecewise smooth paths in `N`
from `p` to `q` (`⊤` if there is none). -/
noncomputable def rho (N : Set V) (p q : V) : ENNReal :=
  ⨅ (c : ℝ → V) (_ : IsPSPath N c 0 1 ∧ c 0 = p ∧ c 1 = q), len c 0 1

end

/-- The textbook notion: `{x ∈ N : ρ(p, x) ≤ r}`. -/
noncomputable def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (N : Set V)
    (p : V) (r : ℝ) : Set V :=
  {x | x ∈ N ∧ rho N p x ≠ ⊤ ∧ (rho N p x).toReal ≤ r}

end RoundTrip.L2.Morse_closedRiemBall
