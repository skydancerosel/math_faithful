import Morse
/-! Layer-2 blind definition of Morse_pathCSet. Textbook: Milnor, *Morse Theory*, §17, p. 93:
`Ω* = Ω*(M; p, q)` is the space of all continuous paths `ω : [0,1] → M` from `p` to `q`, with the
compact-open topology (for a metric space, the topology of uniform convergence).
Choices: `M` is the subset `N ⊆ V` (the setting); a path in `M` is a continuous map
`[0,1] → V` with values in `N` (for `N` with the subspace topology, continuous maps
`[0,1] → N` are exactly these, and the compact-open topology of `C([0,1], N)` is the subspace
topology of `C([0,1], V)`). No condition on `N`, `p`, `q` (if `p ∉ N` the set is empty). -/
namespace RoundTrip.L2.Morse_pathCSet

open scoped unitInterval

/-- The textbook notion: continuous paths `[0,1] → N` from `p` to `q`, as a subset of
`C([0,1], V)` (which carries the compact-open topology). -/
def T {V : Type*} [NormedAddCommGroup V] (N : Set V) (p q : V) : Set C(I, V) :=
  {ω | (∀ t, ω t ∈ N) ∧ ω 0 = p ∧ ω 1 = q}

end RoundTrip.L2.Morse_pathCSet
