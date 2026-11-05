import Morse
/-! Layer-2 blind definition of Morse_PathC. Textbook: Milnor, *Morse Theory*, §17, p. 93:
`Ω* = Ω*(M; p, q)` is the space of all continuous paths `ω : [0,1] → M` from `p` to `q`, with the
compact-open topology (for a metric space, the topology of uniform convergence).
Choices: `M` is the subset `N ⊆ V` (the setting). The type is the subtype of `C([0,1], V)` of the
continuous paths with values in `N` from `p` to `q`, carrying the subspace topology of the
compact-open topology of `C([0,1], V)` (= the compact-open topology of `C([0,1], N)`; = the
uniform topology, `[0,1]` being compact and `V` metric). The topology is given as an instance
on `T`. -/
namespace RoundTrip.L2.Morse_PathC

open scoped unitInterval

/-- The set of continuous paths `[0,1] → N` from `p` to `q`. -/
def S {V : Type*} [NormedAddCommGroup V] (N : Set V) (p q : V) : Set C(I, V) :=
  {ω | (∀ t, ω t ∈ N) ∧ ω 0 = p ∧ ω 1 = q}

/-- The textbook notion: the space `Ω*(N; p, q)`. -/
def T {V : Type*} [NormedAddCommGroup V] (N : Set V) (p q : V) : Type _ := ↥(S N p q)

/-- Its topology: the subspace topology of the compact-open topology of `C([0,1], V)`. -/
instance {V : Type*} [NormedAddCommGroup V] (N : Set V) (p q : V) : TopologicalSpace (T N p q) :=
  inferInstanceAs (TopologicalSpace ↥(S N p q))

end RoundTrip.L2.Morse_PathC
