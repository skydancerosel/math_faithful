import Morse
/-! Blind formalization of V13_9 (Milnor §22, Cor. 22.3 (Freudenthal), p. 119). Choices:
- `Sⁿ` = the Euclidean unit sphere `{x ∈ ℝ^{n+1} | ‖x‖ = 1}` (subspace topology), `Sph n`; homotopy groups are Mathlib's `HomotopyGroup.Pi i X x` (`π_ i`, classes of maps `(I^i, ∂I^i) → (X, x)`; for `i = 0` the set of path components, groups for `i ≥ 1`). No Riemannian setting is needed for the statement.
- Milnor's base-point-free `π_i` is read at every pair of base points `x ∈ Sⁿ`, `y ∈ S^{n+1}`. `i ≤ 2n − 2` is written `i + 2 ≤ 2n` (no truncated subtraction: for `n = 0` there is no `i`). All `n : ℕ`.
- `≅`: for `i = 0` both sides are only sets (a bijection, `Equiv`); for `1 ≤ i ≤ 2n − 2` (written `i = k + 1`, `k + 3 ≤ 2n`) a group isomorphism (`MulEquiv`). Only existence of an isomorphism is claimed (Milnor does not name it; his proof composes `π_iSⁿ ≅ π_iΩ^{π²} → π_iΩ ≅ π_{i+1}S^{n+1}`).
-/
open scoped ContDiff Manifold unitInterval
open Topology
namespace RoundTrip.V13_9

/-- The unit sphere `Sⁿ ⊆ ℝ^{n+1}`. -/
abbrev Sph (n : ℕ) : Type := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- Freudenthal: `π_i Sⁿ ≅ π_{i+1} S^{n+1}` for `i ≤ 2n − 2` (as sets for `i = 0`, as groups for `i ≥ 1`). -/
def B : Prop :=
  ∀ (n : ℕ) (x : Sph n) (y : Sph (n + 1)),
    (∀ i : ℕ, i + 2 ≤ 2 * n → Nonempty (HomotopyGroup.Pi i (Sph n) x ≃ HomotopyGroup.Pi (i + 1) (Sph (n + 1)) y)) ∧
    (∀ k : ℕ, k + 3 ≤ 2 * n →
      Nonempty (HomotopyGroup.Pi (k + 1) (Sph n) x ≃* HomotopyGroup.Pi (k + 2) (Sph (n + 1)) y))

end RoundTrip.V13_9
