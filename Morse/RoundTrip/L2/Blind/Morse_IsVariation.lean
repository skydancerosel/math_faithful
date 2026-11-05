import Morse
/-! Layer-2 blind definition of Morse_IsVariation. Textbook: Milnor, *Morse Theory*, §11, p. 68
(and §13 for the two-parameter version): a variation with fixed end points of a piecewise smooth
path `ω : [0, 1] → M` is a map `α : U × [0, 1] → M`, `U` a neighbourhood of `0` (`(−ε, ε)` or a
neighbourhood of `0 ∈ ℝ²`), with `α(0, ·) = ω`, `α(u, 0) = ω(0)`, `α(u, 1) = ω(1)` for all
`u ∈ U`, and a subdivision `0 = t₀ < ⋯ < t_k = 1` such that `α` is `C^∞` on each strip
`U × [t_{i-1}, t_i]`.
Choices: the signature carries no `ω`, so `ω := α 0` and "fixed end points" reads
`α u 0 = α 0 0`, `α u 1 = α 0 1` for `u ∈ U`. `U` is required open with `0 ∈ U` (only values of
`α` on `U × [0, 1]` are constrained). The subdivision is given by the finite set `B` of break
points: its points are `{0, 1} ∪ (B ∩ (0, 1))` (elements of `B` outside `(0, 1)` are ignored),
and smoothness on each strip is `ContDiffOn ℝ ∞ (fun (u, t) => α u t) (U ×ˢ Icc s s')` for
consecutive points `s < s'` (no subdivision point strictly between them) — derivatives within
the closed strip, one-sided at its edges. Values in `M`: `α u t ∈ N` for `u ∈ U`, `t ∈ [0, 1]`.
Continuity of `α` on `U × [0, 1]` follows from smoothness on the finitely many closed strips and
is not stated separately. -/
namespace RoundTrip.L2.Morse_IsVariation

open scoped ContDiff
open Set

/-- The subdivision points `{0, 1} ∪ (B ∩ (0, 1))`. -/
def pts (B : Finset ℝ) : Set ℝ :=
  {0, 1} ∪ {b | b ∈ B ∧ b ∈ Ioo (0 : ℝ) 1}

/-- The textbook notion: `α` is a variation with fixed end points of `α 0`, defined on `U`,
smooth on the strips of the subdivision given by `B`. -/
def T {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (N : Set V) {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] (U : Set P) (α : P → ℝ → V) (B : Finset ℝ) :
    Prop :=
  IsOpen U ∧ (0 : P) ∈ U ∧
    (∀ u ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, α u t ∈ N) ∧
    (∀ u ∈ U, α u 0 = α 0 0 ∧ α u 1 = α 0 1) ∧
    ∀ s ∈ pts B, ∀ s' ∈ pts B, s < s' → (∀ r ∈ pts B, r ∉ Ioo s s') →
      ContDiffOn ℝ ∞ (fun x : P × ℝ => α x.1 x.2) (U ×ˢ Icc s s')

end RoundTrip.L2.Morse_IsVariation
