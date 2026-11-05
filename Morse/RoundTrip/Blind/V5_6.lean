import Morse
/-! Blind formalization of V5_6 (Milnor §7, proof of Assertion 2: Q' and the second fundamental form). Choices:
- Complex coordinates `z¹..z^k` near `q` (centred at `z = 0`), `w : ℂ^k → ℂ^n` the holomorphic inclusion in coordinates (`AnalyticAt ℂ w 0`, `dw(0)` injective); `v ∈ ℂ^n` a unit normal (`‖v‖ = 1`,
  real-orthogonal to all `∂w/∂x^h, ∂w/∂y^h` at `0`, through the realification `ℂ^n ≅ ℝ^{2n}`). Real coordinates `(x,y) ∈ ℝ^{2k}`, `z = x + iy`.
- Realified parametrization `X(x,y) = w(x+iy) ∈ ℝ^{2n} = EuclideanSpace ℝ (Fin n ⊕ Fin n)` of `M`; its second fundamental form in direction `v` at `0` is, as in V4_5, the matrix `(v · ℓ_ij)` with `ℓ_ij` the normal
  component (orthogonal projection onto the orthogonal complement of the tangent space `span ∂_i X`) of `∂²X/∂ξ_i∂ξ_j`; index sets `Fin k ⊕ Fin k` are used directly.
- `w·v = Re Σ w_α \bar v_α` is `(inner ℂ v (w z)).re`.
- B: there is a complex quadratic form `Q(z) = Σ b_{hj} z^h z^j` with `Re Σ w_α \bar v_α = const + Q'(x,y) + (terms of order o(‖(x,y)‖²))`, `Q' = Re Q` (the form of V5_2), and
  "the quadratic terms `Q'` determine the second fundamental form": for all `i, j`, `(v·ℓ_ij)` equals the polar (second-derivative) form of `Q'`, `Q'(e_i+e_j) - Q'(e_i) - Q'(e_j)`. -/
namespace RoundTrip.V5_6
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

/-- Real coordinates `ξ = (x, y)` ↦ complex point `x + i y ∈ ℂ^k`. -/
noncomputable def toCk {k : ℕ} (ξ : R2 k) : EuclideanSpace ℂ (Fin k) :=
  WithLp.toLp 2 (fun h => (⟨ξ (Sum.inl h), ξ (Sum.inr h)⟩ : ℂ))

/-- Realification `ℂ^n → ℝ^{2n}`: real parts in the first block, imaginary parts in the second. -/
noncomputable def realify {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℝ (Fin n ⊕ Fin n) :=
  WithLp.toLp 2 (Sum.elim (fun a => (c a).re) (fun a => (c a).im))

section Param
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
/-- `∂X/∂ξ_i` at `u`. -/
noncomputable def dxg (X : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ) (u : EuclideanSpace ℝ ι) (i : ι) :
    EuclideanSpace ℝ κ := fderiv ℝ X u (EuclideanSpace.single i 1)
/-- `∂²X/∂ξ_i∂ξ_j` at `u`. -/
noncomputable def d2xg (X : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ) (u : EuclideanSpace ℝ ι) (i j : ι) :
    EuclideanSpace ℝ κ := fderiv ℝ (fun w => dxg X w j) u (EuclideanSpace.single i 1)
/-- Tangent space: span of the `∂X/∂ξ_i`. -/
noncomputable def tangSpg (X : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ) (u : EuclideanSpace ℝ ι) :
    Submodule ℝ (EuclideanSpace ℝ κ) := Submodule.span ℝ (Set.range (dxg X u))
/-- `ℓ_ij`: the normal component of `∂²X/∂ξ_i∂ξ_j`. -/
noncomputable def ellg (X : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ) (u : EuclideanSpace ℝ ι) (i j : ι) :
    EuclideanSpace ℝ κ := (tangSpg X u)ᗮ.starProjection (d2xg X u i j)
/-- The matrix `(v · ℓ_ij)`. -/
noncomputable def sffg (X : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ) (u : EuclideanSpace ℝ ι) (v : EuclideanSpace ℝ κ) :
    Matrix ι ι ℝ := Matrix.of fun i j => inner ℝ v (ellg X u i j)
end Param

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n k : ℕ) (w : EuclideanSpace ℂ (Fin k) → EuclideanSpace ℂ (Fin n)), AnalyticAt ℂ w 0 →
    Function.Injective (fderiv ℂ w 0) →
    ∀ v : EuclideanSpace ℂ (Fin n), ‖v‖ = 1 →
      (∀ i, inner ℝ (realify v) (dxg (fun ξ : R2 k => realify (w (toCk ξ))) 0 i) = 0) →
      ∃ b : Matrix (Fin k) (Fin k) ℂ,
        Asymptotics.IsLittleO (nhds 0)
          (fun ξ : R2 k => (inner ℂ v (w (toCk ξ))).re - (inner ℂ v (w (toCk 0))).re - Qp b ξ) (fun ξ => ‖ξ‖ ^ 2) ∧
        ∀ i j : Fin k ⊕ Fin k,
          sffg (fun ξ : R2 k => realify (w (toCk ξ))) 0 (realify v) i j =
            Qp b (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) - Qp b (EuclideanSpace.single i 1)
              - Qp b (EuclideanSpace.single j 1)
end RoundTrip.V5_6
