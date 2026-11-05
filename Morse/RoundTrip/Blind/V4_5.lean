import Morse
/-! Blind formalization of V4_5 (Milnor §6, pp. 33-34: first and second fundamental forms). Choices:
- Local coordinates `u¹..u^k` on `M ⊆ ℝⁿ` are packaged as a parametrization `x : ℝᵏ → ℝⁿ` (`x(u)` = the inclusion in coordinates), smooth (`C²` suffices) on an open set `U ∋ u`
  and an immersion there (`∂x/∂u^i` linearly independent). Derivatives are Mathlib `fderiv`s; `ℝᵏ = EuclideanSpace ℝ (Fin k)`.
- `g_ij = ⟨∂_i x, ∂_j x⟩`; `ℓ_ij` = orthogonal projection of `∂_i∂_j x` onto the orthogonal complement of `span{∂_i x}`
  (Mathlib `Submodule.starProjection`); `sff x u v` = matrix `(v · ℓ_ij)`.
- Definition item. B asserts the properties Milnor uses/implies: for a `C²` immersion, `(g_ij)` is symmetric positive definite, `ℓ_ij = ℓ_ji`, `ℓ_ij` is normal (orthogonal to every `∂_k x`),
  and consequently `(v · ℓ_ij)` is a symmetric matrix for every `v`.
- No invariant definition (as in Milnor): everything depends on the chosen coordinate system `x`. -/
namespace RoundTrip.V4_5
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

section Param
variable {k n : ℕ}

/-- `∂x/∂u^i` at `u`. -/
noncomputable def dx (x : Rn k → Rn n) (u : Rn k) (i : Fin k) : Rn n := fderiv ℝ x u (EuclideanSpace.single i 1)

/-- `∂²x/∂u^i ∂u^j` at `u`. -/
noncomputable def d2x (x : Rn k → Rn n) (u : Rn k) (i j : Fin k) : Rn n :=
  fderiv ℝ (fun w => dx x w j) u (EuclideanSpace.single i 1)

/-- First fundamental form `g_ij = ∂x/∂u^i · ∂x/∂u^j`. -/
noncomputable def gmat (x : Rn k → Rn n) (u : Rn k) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => inner ℝ (dx x u i) (dx x u j)

/-- Tangent space at `x u`: span of the `∂x/∂u^i`. -/
noncomputable def tangSp (x : Rn k → Rn n) (u : Rn k) : Submodule ℝ (Rn n) := Submodule.span ℝ (Set.range (dx x u))

/-- Second fundamental form `ℓ_ij`: the normal component of `∂²x/∂u^i ∂u^j` (orthogonal projection to the normal space). -/
noncomputable def ell (x : Rn k → Rn n) (u : Rn k) (i j : Fin k) : Rn n :=
  (tangSp x u)ᗮ.starProjection (d2x x u i j)

/-- The second fundamental form in the direction `v`: the matrix `(v · ℓ_ij)`. -/
noncomputable def sff (x : Rn k → Rn n) (u : Rn k) (v : Rn n) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => inner ℝ v (ell x u i j)
end Param

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (k n : ℕ) (x : Rn k → Rn n) (U : Set (Rn k)), IsOpen U → ContDiffOn ℝ 2 x U →
    ∀ u ∈ U, LinearIndependent ℝ (dx x u) →
      (gmat x u).IsSymm ∧ (gmat x u).PosDef ∧
      (∀ i j, ell x u i j = ell x u j i) ∧
      (∀ i j l, inner ℝ (ell x u i j) (dx x u l) = 0) ∧
      ∀ v : Rn n, (sff x u v).IsSymm
end RoundTrip.V4_5
