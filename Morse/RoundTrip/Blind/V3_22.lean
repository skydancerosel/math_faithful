import Morse
/-! Blind formalization of V3_22 (Milnor §1, p. 1: the torus of Diagram 1). Choices:
- The torus is not given by equations in Milnor; I take the standard torus of revolution about the `x₃`-axis
  (`torus R r`, `0 < r < R`), standing so that the plane `V = {x₀ = -(R+r)}` is tangent at `p = (-(R+r),0,0)`;
  `q = (-(R-r),0,0)`, `r = (R-r,0,0)`, `s = (R+r,0,0)`; height `f x = x₀ + R + r` (distance from `V`), so `f p = 0`.
- Surface = 2-dimensional smooth embedded submanifold of `ℝ³`: project's `Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝ³) ℝ² ℝ¹` (Mathlib has no embedded-submanifold predicate).
- B: for `0<r<R`, the torus is compact, is a smooth surface (slice submanifold), lies on one side of `V` and meets `V` exactly at `p` (tangency). -/
namespace RoundTrip.V3_22
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

/-- Milnor's claim. -/
def B : Prop :=
  ∀ R r : ℝ, 0 < r → r < R →
    IsCompact (torus R r) ∧
    Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn 3) (Rn 2) (Rn 1) (torus R r) ∧
    (∀ x ∈ torus R r, -(R + r) ≤ x 0) ∧ (∀ x ∈ torus R r, x 0 = -(R + r) ↔ x = pP R r)
end RoundTrip.V3_22
