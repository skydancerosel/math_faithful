import Morse
/-! Layer-2 blind definition of Morse_IsCriticalPath. Textbook: Milnor, *Morse Theory*, §12,
p. 69: a path `ω ∈ Ω(M; p, q)` is a critical path of `E` if for every variation `α` of `ω` with
fixed end points, `d/du E(α(u))` at `u = 0` exists and is `0`, where `E(ω) = ∫₀¹ |dω/dt|² dt`.
Choices: `p := c 0`, `q := c 1`; `c ∈ Ω(N; c 0, c 1)` is required. Everything is defined from
scratch (as in the layer-2 blind files of `Morse_IsPiecewiseSmooth`, `Morse_pathSpace`,
`Morse_energy`, `Morse_IsVariation`): `Ω(N; p, q)` = maps `ℝ → V`, piecewise smooth on `[0, 1]`
(continuous, `C^∞` on the closed pieces of a subdivision), `[0, 1] → N`, ends `p`, `q`;
`E(ω) = ∫₀¹ ‖deriv ω t‖² dt` (Mathlib `deriv`; break points are a null set).
A variation is a map `α : ℝ → ℝ → V` (`α u t = α(u, t)`) on
`(−ε, ε) × [0, 1]`, `ε > 0`, with values in `N`, `α(0, t) = c(t)` for `t ∈ [0, 1]`,
`α(u, 0) = c(0)`, `α(u, 1) = c(1)`, and `C^∞` (`ContDiffOn` on the closed strips) on each strip
`(−ε, ε) × [t_{i-1}, t_i]` of a subdivision of `[0, 1]`, given by a finite set `B` of break points
(points `{0, 1} ∪ (B ∩ (0, 1))`). "Exists and equals `0`" is
`HasDerivAt (fun u => E(α u)) 0 0`. `N` is any subset (no manifold hypothesis is carried). -/
namespace RoundTrip.L2.Morse_IsCriticalPath

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

/-- The energy `E(ω) = ∫₀¹ ‖ω'(t)‖² dt`. -/
noncomputable def energy (σ : ℝ → V) : ℝ :=
  ∫ t in (0 : ℝ)..1, ‖deriv σ t‖ ^ 2

/-- The subdivision points `{0, 1} ∪ (B ∩ (0, 1))`. -/
def pts (B : Finset ℝ) : Set ℝ :=
  {0, 1} ∪ {b | b ∈ B ∧ b ∈ Ioo (0 : ℝ) 1}

/-- `α : (−ε, ε) × [0, 1] → N` is a variation of `c` with fixed end points, smooth on the
strips of the subdivision given by `B`. -/
def IsVariationOf (N : Set V) (c : ℝ → V) (ε : ℝ) (α : ℝ → ℝ → V) (B : Finset ℝ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, α 0 t = c t) ∧
    (∀ u ∈ Ioo (-ε) ε, ∀ t ∈ Icc (0 : ℝ) 1, α u t ∈ N) ∧
    (∀ u ∈ Ioo (-ε) ε, α u 0 = c 0 ∧ α u 1 = c 1) ∧
    ∀ s ∈ pts B, ∀ s' ∈ pts B, s < s' → (∀ r ∈ pts B, r ∉ Ioo s s') →
      ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => α x.1 x.2) (Ioo (-ε) ε ×ˢ Icc s s')

/-- The textbook notion: `c ∈ Ω(N; c 0, c 1)` is a critical path of the energy. -/
def T (N : Set V) (c : ℝ → V) : Prop :=
  c ∈ pathSpace N (c 0) (c 1) ∧
    ∀ ε : ℝ, 0 < ε → ∀ α : ℝ → ℝ → V, ∀ B : Finset ℝ, IsVariationOf N c ε α B →
      HasDerivAt (fun u => energy (α u)) 0 0

end RoundTrip.L2.Morse_IsCriticalPath
