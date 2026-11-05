import Morse
/-! Layer-2 blind definition of Morse_riemDist. Textbook: Milnor, *Morse Theory*, §10, p. 62:
`ρ(p, q)` = greatest lower bound of the arc lengths `∫ ‖ω'(t)‖ dt` of the piecewise smooth paths
`ω` in `N` from `p` to `q`.
Choices: paths are maps `ω : ℝ → V` of which only `[0, 1]` matters (reparametrisation does not
change lengths). Piecewise smooth (Milnor): `ω` continuous on `[0,1]`, `ω([0,1]) ⊆ N`, and for a
subdivision `0 = t₀ < … < t_k = 1` each restriction `ω|[t_{i-1}, t_i]` is `C^∞` (as a map into
`V`, `ContDiffOn` on the closed piece). Length = `∫⁻_{[0,1]} ‖ω'(t)‖` (`deriv`, a lower Lebesgue
integral in `ℝ≥0∞`; the break points are a null set). `ρ` is the infimum in `ℝ≥0∞`; Milnor
assumes `N` connected: when no path in `N` joins `p` to `q` (in particular `p ∉ N` or `q ∉ N`,
or different components) the value is `⊤`. `N` is implicit as in the signature. -/
namespace RoundTrip.L2.Morse_riemDist

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

end

/-- The textbook notion: `ρ(p, q)` = inf of the lengths of piecewise smooth paths in `N`. -/
noncomputable def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {N : Set V}
    (p q : V) : ENNReal :=
  ⨅ (c : ℝ → V) (_ : IsPSPath N c 0 1 ∧ c 0 = p ∧ c 1 = q), len c 0 1

end RoundTrip.L2.Morse_riemDist
