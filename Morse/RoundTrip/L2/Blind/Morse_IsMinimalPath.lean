import Morse
/-! Layer-2 blind definition of Morse_IsMinimalPath. Textbook: Milnor, *Morse Theory*, §10,
p. 61: a path of least length in `Ω(M; p, q)`: `c ∈ Ω(M; p, q)` and `L(c) ≤ L(ω)` for every
`ω ∈ Ω(M; p, q)`.
Choices: defined from scratch (as in the layer-2 blind files of `Morse_pathSpace` and
`Morse_pathLength`): `Ω(N; p, q)` is the set of maps `ω : ℝ → V`, piecewise smooth on `[0, 1]`
(continuous, `C^∞` on the closed pieces of a subdivision), with `ω([0, 1]) ⊆ N`, `ω 0 = p`,
`ω 1 = q` (values off `[0, 1]` unconstrained); `L(ω) = ∫₀¹ ‖ω'(t)‖ dt` with Mathlib's `deriv`
(break points are a null set). `N` is any subset (no manifold hypothesis is carried). -/
namespace RoundTrip.L2.Morse_IsMinimalPath

open scoped ContDiff
open Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `c` is piecewise smooth on `[a, b]`. -/
def IsPiecewiseSmooth (c : ℝ → V) (a b : ℝ) : Prop :=
  ContinuousOn c (Icc a b) ∧
    ∃ k : ℕ, ∃ t : Fin (k + 1) → ℝ, StrictMono t ∧ t 0 = a ∧ t (Fin.last k) = b ∧
      ∀ i : Fin k, ContDiffOn ℝ ∞ c (Icc (t i.castSucc) (t i.succ))

/-- The path space `Ω(N; p, q)`. -/
def pathSpace (N : Set V) (p q : V) : Set (ℝ → V) :=
  {σ | IsPiecewiseSmooth σ 0 1 ∧ MapsTo σ (Icc 0 1) N ∧ σ 0 = p ∧ σ 1 = q}

/-- The length `L(ω) = ∫₀¹ ‖ω'(t)‖ dt`. -/
noncomputable def length (σ : ℝ → V) : ℝ :=
  ∫ t in (0 : ℝ)..1, ‖deriv σ t‖

/-- The textbook notion: `c` has least length in `Ω(N; p, q)`. -/
def T (N : Set V) (c : ℝ → V) (p q : V) : Prop :=
  c ∈ pathSpace N p q ∧ ∀ σ ∈ pathSpace N p q, length c ≤ length σ

end RoundTrip.L2.Morse_IsMinimalPath
