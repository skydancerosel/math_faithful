import Morse
/-! Blind formalization of V1_5 (Milnor §2, pp. 4-5: independence of the coordinate system). Choices:
- Setting: smooth Hausdorff finite-dim manifold, `E = Fin n → ℝ`.
- (1) Non-degeneracy is coordinate independent: for smooth `f` on ℝⁿ, a smooth coordinate change `φ` (C^∞, with invertible
  derivative at `q`; Milnor's "coordinate system" change) and `p = φ q` a critical point of `f`, the Hessian matrix
  of `f ∘ φ` at `q` is non-singular iff that of `f` at `p` is. (Hessian matrix = nested partial derivatives, my own def.)
- (2) The matrix `(∂²f/∂x^i∂x^j(p))` of the coordinate function `f ∘ chart⁻¹` (preferred chart `extChartAt p`) represents the
  project's Hessian `Morse.hessianM` w.r.t. the coordinate basis: `f_**(v,w) = (D v)ᵀ H (D w)`, `D` = derivative of the chart at p
  (components of a tangent vector in the basis `∂/∂x^i`).
- Only critical points `p` are treated (Hessian is only intrinsic there). -/
open scoped ContDiff Manifold Matrix
namespace RoundTrip.V1_5

/-- partial derivative. -/
noncomputable def part {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- Hessian matrix at `p`. -/
noncomputable def hmat {n : ℕ} (f : (Fin n → ℝ) → ℝ) (p : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => fderiv ℝ (part f j) p (Pi.single i 1)

/-- Milnor's claim. -/
def B : Prop :=
  (∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ) (φ : (Fin n → ℝ) → (Fin n → ℝ)) (q : Fin n → ℝ),
    ContDiff ℝ ∞ f → ContDiff ℝ ∞ φ → Function.Bijective (fderiv ℝ φ q) → fderiv ℝ f (φ q) = 0 →
      ((hmat (f ∘ φ) q).det ≠ 0 ↔ (hmat f (φ q)).det ≠ 0)) ∧
  (∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (Fin n → ℝ) M]
    [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] (f : M → ℝ) (p : M),
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ) ∞ f → Morse.IsCriticalPointM (Fin n → ℝ) f p →
      ∀ v w : Fin n → ℝ, Morse.hessianM (Fin n → ℝ) f p v w =
        (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p) p v) ⬝ᵥ
          ((hmat (f ∘ (extChartAt 𝓘(ℝ, Fin n → ℝ) p).symm) (extChartAt 𝓘(ℝ, Fin n → ℝ) p p)).mulVec
            (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) (extChartAt 𝓘(ℝ, Fin n → ℝ) p) p w)))

end RoundTrip.V1_5
