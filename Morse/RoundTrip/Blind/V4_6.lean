import Morse
/-! Blind formalization of V4_6 (Milnor §6, p. 34: principal curvatures). Choices:
- Local coordinates `u¹..u^k` on `M ⊆ ℝⁿ` are packaged as a parametrization `x : ℝᵏ → ℝⁿ` (`x(u)` = the inclusion in coordinates), smooth (`C²` suffices) on an open set `U ∋ u`
  and an immersion there (`∂x/∂u^i` linearly independent). Derivatives are Mathlib `fderiv`s; `ℝᵏ = EuclideanSpace ℝ (Fin k)`.
- `g_ij = ⟨∂_i x, ∂_j x⟩`; `ℓ_ij` = orthogonal projection of `∂_i∂_j x` onto the orthogonal complement of `span{∂_i x}`
  (Mathlib `Submodule.starProjection`); `sff x u v` = matrix `(v · ℓ_ij)`.
- Definition item. Coordinates are those with `(g_ij) = identity` at `q = x u` (hypothesis `gmat x u = 1`), `v` a unit normal vector at `q` (`‖v‖ = 1`, `v ⊥ ∂_i x`).
- `IsPrincCurv x u v K` : `K : Fin k → ℝ` are the eigenvalues of `(v · ℓ_ij)` with multiplicity (characteristic polynomial `∏ (X - K_i)`); `IsPrincRadius`: reciprocals of non-zero `K_i`.
  (Milnor writes `K_1..K_n`; the number of them is the dimension `k` of `M`.)
- B: such a list `K` exists, and is unique up to permutation (equal multisets) -- i.e. the principal curvatures are well defined; plus principal radii are by definition the reciprocals.
  Coordinate independence is not asserted by Milnor and not formalized. -/
namespace RoundTrip.V4_6
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

/-- `K : Fin k → ℝ` lists the principal curvatures at `x u` in the direction `v`: the eigenvalues, with multiplicity, of the symmetric
matrix `(v · ℓ_ij)` (i.e. its characteristic polynomial is `∏ (X - K_i)`). Milnor uses coordinates with `(g_ij) = 1` at `q`. -/
noncomputable def IsPrincCurv {k n : ℕ} (x : Rn k → Rn n) (u : Rn k) (v : Rn n) (K : Fin k → ℝ) : Prop :=
  (sff x u v).charpoly = ∏ i, (Polynomial.X - Polynomial.C (K i))

/-- `r` is a principal radius of curvature: the reciprocal of a non-zero principal curvature. -/
def IsPrincRadius {k n : ℕ} (x : Rn k → Rn n) (u : Rn k) (v : Rn n) (r : ℝ) : Prop :=
  ∃ K : Fin k → ℝ, IsPrincCurv x u v K ∧ ∃ i, K i ≠ 0 ∧ r = (K i)⁻¹

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (k n : ℕ) (x : Rn k → Rn n) (U : Set (Rn k)), IsOpen U → ContDiffOn ℝ 2 x U →
    ∀ u ∈ U, LinearIndependent ℝ (dx x u) → gmat x u = 1 →
    ∀ v : Rn n, ‖v‖ = 1 → v ∈ (tangSp x u)ᗮ →
      (∃ K : Fin k → ℝ, IsPrincCurv x u v K) ∧
      (∀ K K' : Fin k → ℝ, IsPrincCurv x u v K → IsPrincCurv x u v K' →
        Multiset.map K Finset.univ.val = Multiset.map K' Finset.univ.val) ∧
      ∀ r, IsPrincRadius x u v r ↔ ∃ K : Fin k → ℝ, IsPrincCurv x u v K ∧ ∃ i, K i ≠ 0 ∧ r = (K i)⁻¹
end RoundTrip.V4_6
