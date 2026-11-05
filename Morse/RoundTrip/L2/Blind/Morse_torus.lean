import Morse
/-! Layer-2 blind definition of Morse_torus. Textbook: Milnor, *Morse Theory*, §1, p. 1
(Diagram 1: torus of revolution in `ℝ³`).
Choices: the circle of radius `r` centred at distance `R` from the axis is rotated about the
`x₃`-axis (coordinates `x 0, x 1, x 2` = `x₁, x₂, x₃`), giving
`{x : (√(x₁² + x₂²) − R)² + x₃² = r²}` as in the given description. (Milnor's picture stands the
torus upright, i.e. with a horizontal axis; this only permutes coordinates.) The textbook assumes
`0 < r < R`; outside these hypotheses `T R r` is still the solution set of the same equation. -/
namespace RoundTrip.L2.Morse_torus

/-- The textbook notion: the torus of revolution with radii `R` (centre circle) and `r` (tube). -/
def T (R r : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - R) ^ 2 + x 2 ^ 2 = r ^ 2}

end RoundTrip.L2.Morse_torus
