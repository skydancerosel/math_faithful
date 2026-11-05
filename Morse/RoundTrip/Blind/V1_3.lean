import Morse
/-! Blind formalization of V1_3 (Milnor §2, pp. 4-5: critical points, Hessian, index, nullity in coordinates). Choices:
- Setting: coordinates = `Fin n → ℝ`, `f` smooth (`ContDiff ℝ ∞`) on all of ℝⁿ (a local coordinate patch is an open subset;
  statements are pointwise and local so the whole space is used).
- `f_*` zero at p = `fderiv ℝ f p = 0`; the claim is that this is equivalent to all first partials vanishing.
- Hessian matrix `H i j = ∂²f/∂x^i∂x^j (p)` (second partial derivative via nested `fderiv` on `Pi.single`).
- Non-degenerate := matrix non-singular (`det ≠ 0`).
- Index of a bilinear functional `H` (given as `V → V → ℝ`, bilinearity is not enforced in the type): sup of `finrank W`, `W`
  a subspace with `H w w < 0` for all nonzero `w ∈ W`. Nullity: `finrank` of the span of `{v | ∀ w, H v w = 0}`.
- Claims: (1) critical ⇔ partials vanish; (2) non-degenerate (det ≠ 0) ⇔ nullity of `f_**` (bilinear form of the matrix) is 0.
- Coordinate independence ("can be checked directly") is item V1_5, not repeated here. -/
open scoped ContDiff Matrix
namespace RoundTrip.V1_3

/-- index of a bilinear functional. -/
noncomputable def idx {V : Type} [AddCommGroup V] [Module ℝ V] (H : V → V → ℝ) : ℕ :=
  sSup {k | ∃ W : Submodule ℝ V, Module.finrank ℝ W = k ∧ ∀ w ∈ W, w ≠ 0 → H w w < 0}

/-- nullity of a bilinear functional. -/
noncomputable def nul {V : Type} [AddCommGroup V] [Module ℝ V] (H : V → V → ℝ) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ {v | ∀ w, H v w = 0})

/-- partial derivative `∂f/∂x^i (x)`. -/
noncomputable def part {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- Hessian matrix at `p`. -/
noncomputable def hmat {n : ℕ} (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (part f j) p (Pi.single i 1)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ), ContDiff ℝ ∞ f →
    (fderiv ℝ f p = 0 ↔ ∀ i, part f i p = 0) ∧
    ((hmat f p).det ≠ 0 ↔ nul (fun v w : Fin n → ℝ => v ⬝ᵥ ((hmat f p).mulVec w)) = 0)

end RoundTrip.V1_3
