import Morse
/-! Blind formalization of V5_3 (Milnor §7, Assertion 1). Choices:
- `Q'` as in V5_2 (real part of the complex quadratic form `Q`, on `ℝ^{2k}`). Eigenvalues of the real quadratic form `Q'` := eigenvalues of its symmetric matrix `A` (polar form: `A_{ab} = (Q'(e_a+e_b) - Q'(e_a) - Q'(e_b))/2`) in the standard orthonormal basis.
- Multiplicity of an eigenvalue `e` stated in two ways (both asserted, for every real `e`): the dimension of the eigenspace `ker (A - e)` (`finrank`), and the number of times `e` occurs among the roots of the characteristic polynomial.
  A non-eigenvalue has multiplicity `0` in both senses, so "if `e` is an eigenvalue of multiplicity μ then `-e` is one of the same multiplicity" is the equality of multiplicities for all `e`. -/
namespace RoundTrip.V5_3
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

/-- The symmetric matrix of the real quadratic form `Q'` (via the polar form), in the standard basis. -/
noncomputable def qmat {k : ℕ} (b : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ :=
  Matrix.of fun a c =>
    (Qp b (EuclideanSpace.single a 1 + EuclideanSpace.single c 1) - Qp b (EuclideanSpace.single a 1)
      - Qp b (EuclideanSpace.single c 1)) / 2

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (k : ℕ) (b : Matrix (Fin k) (Fin k) ℂ) (e : ℝ),
    Module.finrank ℝ (LinearMap.ker (qmat b - e • (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ)).mulVecLin) =
      Module.finrank ℝ (LinearMap.ker (qmat b + e • (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ)).mulVecLin) ∧
    (qmat b).charpoly.roots.count e = (qmat b).charpoly.roots.count (-e)
end RoundTrip.V5_3
