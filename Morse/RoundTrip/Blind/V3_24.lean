import Morse
/-! Blind formalization of V3_24 (Milnor §1, p. 1: M^a for the torus, cases (1)-(5)). Choices:
- The torus is not given by equations in Milnor; I take the standard torus of revolution about the `x₃`-axis
  (`torus R r`, `0 < r < R`), standing so that the plane `V = {x₀ = -(R+r)}` is tangent at `p = (-(R+r),0,0)`;
  `q = (-(R-r),0,0)`, `r = (R-r,0,0)`, `s = (R+r,0,0)`; height `f x = x₀ + R + r` (distance from `V`), so `f p = 0`.
- Surface = 2-dimensional smooth embedded submanifold of `ℝ³`: project's `Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝ³) ℝ² ℝ¹` (Mathlib has no embedded-submanifold predicate).
- `M^a = {x ∈ torus | f x ≤ a}` (subtype of `ℝ³`); critical values `0 < 2r < 2R < 2R+2r`.
- (1) `a < 0`: empty. (5) `2R+2r < a`: all of the torus. (2) `0<a<2r`: homeomorphic to a 2-cell (closed unit disc of `ℝ²`).
  (3) `2r<a<2R`: homeomorphic to a (closed) cylinder `S¹ × [0,1]`. (4) `2R<a<2R+2r`: homeomorphic to the torus minus an open disc:
  there is an embedding `e` of the closed disc of radius 2 into the torus, and `M^a ≃ₜ torus ∖ e(open unit disc)` ("compact genus-one surface bounded by a circle"). -/
namespace RoundTrip.V3_24
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The torus of revolution about the `x₃`-axis (coordinates `x 0, x 1, x 2`) with core radius `R` and tube radius `r`. -/
def torus (R r : ℝ) : Set (Rn 3) := {x | (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - R) ^ 2 + x 2 ^ 2 = r ^ 2}

/-- The height above the plane `V = {x₀ = -(R+r)}` touching the torus at its lowest point. -/
def hgt (R r : ℝ) (x : Rn 3) : ℝ := x 0 + R + r

/-- Lowest point `p`. -/
def pP (R r : ℝ) : Rn 3 := !₂[-(R + r), 0, 0]
/-- `q`. -/
def pQ (R r : ℝ) : Rn 3 := !₂[-(R - r), 0, 0]
/-- `r` (the point). -/
def pR (R r : ℝ) : Rn 3 := !₂[R - r, 0, 0]
/-- Highest point `s`. -/
def pS (R r : ℝ) : Rn 3 := !₂[R + r, 0, 0]

/-- `M^a`. -/
def sub (R r a : ℝ) : Set (Rn 3) := {x | x ∈ torus R r ∧ hgt R r x ≤ a}

/-- Milnor's claim. -/
def B : Prop :=
  ∀ R r : ℝ, 0 < r → r < R → ∀ a : ℝ,
    (a < 0 → sub R r a = ∅) ∧
    (2 * R + 2 * r < a → sub R r a = torus R r) ∧
    (0 < a → a < 2 * r → Nonempty (↥(sub R r a) ≃ₜ ↥(Metric.closedBall (0 : Rn 2) 1))) ∧
    (2 * r < a → a < 2 * R → Nonempty (↥(sub R r a) ≃ₜ (↥(Metric.sphere (0 : Rn 2) 1) × unitInterval))) ∧
    (2 * R < a → a < 2 * R + 2 * r →
      ∃ e : ↥(Metric.closedBall (0 : Rn 2) 2) → Rn 3, Topology.IsEmbedding e ∧ Set.range e ⊆ torus R r ∧
        Nonempty (↥(sub R r a) ≃ₜ ↥(torus R r \ e '' {z | ‖z.1‖ < 1})))
end RoundTrip.V3_24
