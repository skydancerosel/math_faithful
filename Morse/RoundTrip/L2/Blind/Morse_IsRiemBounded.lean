import Morse
/-! Layer-2 blind definition of Morse_IsRiemBounded. Textbook: Milnor, *Morse Theory*, §10, p. 64:
a subset `X` of `N` is bounded if it has finite diameter `sup_{x, y ∈ X} ρ(x, y) < ∞` for the
Riemannian distance `ρ`.
Choices: The Riemannian distance is defined from scratch: `ρ(p, q)` = infimum in `ℝ≥0∞` of the
lengths `∫⁻_{[0,1]} ‖c'(t)‖` of piecewise smooth paths `c` in `N` from `p` to `q` (`c` continuous
on `[0,1]`, `c([0,1]) ⊆ N`, `C^∞` on the closed pieces of a subdivision `0 = t₀ < … < t_k = 1`);
`ρ = ⊤` when no such path exists (different components, or a point outside `N`).
Textbook hypothesis `X ⊆ N`: if `X` contains a point `x ∉ N` then `ρ(x, x) = ⊤` and `X` is not
bounded. `X = ∅` is bounded (diameter `0`). -/
namespace RoundTrip.L2.Morse_IsRiemBounded

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

/-- The textbook notion: `X` has finite `ρ`-diameter. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (N X : Set V) : Prop :=
  (⨆ x ∈ X, ⨆ y ∈ X, rho N x y) < ⊤

end RoundTrip.L2.Morse_IsRiemBounded
