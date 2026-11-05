import Morse
/-! Layer-2 blind definition of Morse_IsRiemComplete. Textbook: Milnor, *Morse Theory*, §10,
p. 62-64 (Hopf–Rinow): `N` is complete as a metric space for the Riemannian distance `ρ`: every
`ρ`-Cauchy sequence of points of `N` converges (for `ρ`) to a point of `N`.
Choices: The Riemannian distance is defined from scratch: `ρ(p, q)` = infimum in `ℝ≥0∞` of the
lengths `∫⁻_{[0,1]} ‖c'(t)‖` of piecewise smooth paths `c` in `N` from `p` to `q` (`c` continuous
on `[0,1]`, `c([0,1]) ⊆ N`, `C^∞` on the closed pieces of a subdivision `0 = t₀ < … < t_k = 1`);
`ρ = ⊤` when no such path exists (different components, or a point outside `N`).
Cauchy: `∀ ε > 0, ∃ K, ∀ m n ≥ K, ρ(x_m, x_n) < ε`; convergence: `ρ(x_n, y) → 0` with `y ∈ N`
(for connected `N`, `ρ` induces the topology of `N`). No connectedness is assumed; `N = ∅` is
complete. -/
namespace RoundTrip.L2.Morse_IsRiemComplete

open scoped ContDiff Topology
open MeasureTheory Set Filter

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

/-- The textbook notion: `(N, ρ)` is a complete metric space. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (N : Set V) : Prop :=
  ∀ x : ℕ → V, (∀ n, x n ∈ N) →
    (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ m ≥ K, ∀ n ≥ K, rho N (x m) (x n) < ENNReal.ofReal ε) →
      ∃ y ∈ N, Tendsto (fun n => rho N (x n) y) atTop (𝓝 0)

end RoundTrip.L2.Morse_IsRiemComplete
