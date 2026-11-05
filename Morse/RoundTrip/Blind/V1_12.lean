import Morse
/-! Blind formalization of V1_12 (Milnor §2, pp. 8-9, examples of degenerate critical points). Choices:
- Degenerate critical point := `Morse.IsCriticalPointM E f p ∧ ¬ Morse.IsNondegenerateCriticalPointM E f p` (project defs;
  `E = ℝ` or `EuclideanSpace ℝ (Fin 2)` as manifold modelled on itself).
- (a) `x^3` at 0. (b) `e^{-1/x²} sin²(1/x)` (extended by 0 at 0): smooth, 0 degenerate critical, and non-isolated:
  critical points of `f` accumulate at 0 (every nbhd of 0 contains another critical point).
- (c) monkey saddle `x³ - 3xy²` at (0,0).
- (d) `f(x,y)=x²`: Milnor says the critical points "form the x axis". Taken LITERALLY, x-axis = `{y = 0}`; (for x² the true
  critical set is {x = 0}, so this literal reading is false; formalized as Milnor wrote.) All critical points degenerate and
  the critical set is a submanifold.
- (e) `x²y²`: critical set = union of the two axes, all degenerate, and it is not a submanifold of ℝ².
- "Submanifold of ℝ²" := embedded: each point has a smooth chart (Mathlib `PartialDiffeomorph` of ℝ²) straightening the set
  to a coordinate subspace `{φ x i = 0 for i ≥ k}` (k may vary with the point -- permissive notion, making "not a submanifold" stronger).
- The pictures are not formalized. -/
open scoped ContDiff Manifold
namespace RoundTrip.V1_12

abbrev P := EuclideanSpace ℝ (Fin 2)

/-- degenerate critical point. -/
def Deg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (p : E) : Prop :=
  Morse.IsCriticalPointM E f p ∧ ¬ Morse.IsNondegenerateCriticalPointM E f p

/-- embedded smooth submanifold of the plane. -/
def IsSub (S : Set P) : Prop :=
  ∀ p ∈ S, ∃ k : ℕ, ∃ φ : PartialDiffeomorph 𝓘(ℝ, P) 𝓘(ℝ, P) P P ∞, p ∈ φ.source ∧
    ∀ x ∈ φ.source, x ∈ S ↔ ∀ i : Fin 2, k ≤ i.val → φ x i = 0

/-- `e^{-1/x²} sin²(1/x)` extended by 0. -/
noncomputable def fb (x : ℝ) : ℝ := if x = 0 then 0 else Real.exp (-1 / x ^ 2) * Real.sin (1 / x) ^ 2

/-- Milnor's claim. -/
def B : Prop :=
  Deg (fun x : ℝ => x ^ 3) 0 ∧
  (ContDiff ℝ ∞ fb ∧ Deg fb 0 ∧ ∀ U ∈ nhds (0 : ℝ), ∃ x ∈ U, x ≠ 0 ∧ Morse.IsCriticalPointM ℝ fb x) ∧
  Deg (fun p : P => p 0 ^ 3 - 3 * p 0 * p 1 ^ 2) 0 ∧
  ({p : P | Morse.IsCriticalPointM P (fun q : P => q 0 ^ 2) p} = {p | p 1 = 0} ∧
    (∀ p, Morse.IsCriticalPointM P (fun q : P => q 0 ^ 2) p → Deg (fun q : P => q 0 ^ 2) p) ∧
    IsSub {p : P | p 1 = 0}) ∧
  ({p : P | Morse.IsCriticalPointM P (fun q : P => q 0 ^ 2 * q 1 ^ 2) p} = {p | p 0 = 0 ∨ p 1 = 0} ∧
    (∀ p, Morse.IsCriticalPointM P (fun q : P => q 0 ^ 2 * q 1 ^ 2) p → Deg (fun q : P => q 0 ^ 2 * q 1 ^ 2) p) ∧
    ¬ IsSub {p : P | p 0 = 0 ∨ p 1 = 0})

end RoundTrip.V1_12
