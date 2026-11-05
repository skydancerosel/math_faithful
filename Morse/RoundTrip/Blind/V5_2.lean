import Morse
/-! Blind formalization of V5_2 (Milnor §7, p. 39: the form Q' and multiplication by i). Choices:
- Complex quadratic form `Q(z) = Σ_{h,j} b_{hj} z^h z^j` of `k` variables with arbitrary complex coefficients `b` (symmetry is not needed; Milnor's `b_hj` may be taken symmetric w.l.o.g.).
- `Q'(x,y) = Re Q(x+iy)`, a real quadratic form in `2k` variables, on `ℝ^{2k} = EuclideanSpace ℝ (Fin k ⊕ Fin k)` (first block `x`, second block `y`).
- B: (1) `Q(iz) = -Q(z)` for all `z ∈ ℂ^k`; (2) an orthogonal change of variables of `ℝ^{2k}` (a linear isometry equivalence `T`) turns `Q'` into `-Q'` : `Q'(T w) = -Q'(w)` (it is `(x,y) ↦ (-y,x)`, multiplication by `i`). -/
namespace RoundTrip.V5_2
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- Real coordinates `(x, y) ∈ ℝ^{2k} = ℝ^{Fin k ⊕ Fin k}` (first `k` coordinates `x^h`, last `k` coordinates `y^h`). -/
abbrev R2 (k : ℕ) := EuclideanSpace ℝ (Fin k ⊕ Fin k)

/-- The complex point `z^h = x^h + i y^h`. -/
noncomputable def toC {k : ℕ} (w : R2 k) : Fin k → ℂ := fun h => ⟨w (Sum.inl h), w (Sum.inr h)⟩

/-- The complex quadratic form `Q(z) = Σ b_{hj} z^h z^j`. -/
noncomputable def Qc {k : ℕ} (b : Matrix (Fin k) (Fin k) ℂ) (z : Fin k → ℂ) : ℂ := ∑ h, ∑ j, b h j * z h * z j

/-- Milnor's real quadratic form `Q'(x, y) = Re Q(x + i y)` in `2k` variables. -/
noncomputable def Qp {k : ℕ} (b : Matrix (Fin k) (Fin k) ℂ) (w : R2 k) : ℝ := (Qc b (toC w)).re

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (k : ℕ) (b : Matrix (Fin k) (Fin k) ℂ),
    (∀ z : Fin k → ℂ, Qc b (fun h => Complex.I * z h) = - Qc b z) ∧
    ∃ T : R2 k ≃ₗᵢ[ℝ] R2 k, ∀ w : R2 k, Qp b (T w) = - Qp b w
end RoundTrip.V5_2
