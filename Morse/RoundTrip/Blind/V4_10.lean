import Morse
/-! Blind formalization of V4_10 (Milnor §6, pp. 35-36: critical points and Hessian of `L_p`). Choices:
- `L_p(y) = ‖y - p‖²` on `ℝⁿ` (`Lp`); on `M ⊆ ℝⁿ` (project's `Milnor.IsSliceSubmanifold`, charted-space structure `hM.chartedSpace`) it is the restriction. Critical point: project's `Morse.IsCriticalPointM`
  (for the chart structure of `M`); tangent space `Milnor.Tub.tanN`.
- Local coordinates `u¹..u^k` on `M ⊆ ℝⁿ` are packaged as a parametrization `x : ℝᵏ → ℝⁿ` (`x(u)` = the inclusion in coordinates), smooth on an open set `U`, an immersion there.
  Derivatives are Mathlib `fderiv`s; `ℝᵏ = EuclideanSpace ℝ (Fin k)`. `g_ij = ⟨∂_i x, ∂_j x⟩`; `ℓ_ij` = orthogonal projection of `∂_i∂_j x` onto the orthogonal complement of `span{∂_i x}`;
  `sff x u v` = matrix `(v · ℓ_ij)`.
- B has two parts. (1) For `M`: `q` is a critical point of `L_p|M` iff `q - p` is normal to `M` at `q` (orthogonal to `T_qM`). (2) In a parametrization `x` of class `C²` on an open `U` (any `k, n`; no immersion needed):
  `∂f/∂u^i = 2 ∂x/∂u^i · (x - p)`; at a point where all first partials vanish the second partials `∂_i∂_j f` equal `2(g_ij + ∂²x/∂u^i∂u^j · (x - p))`;
  and for `p = x(u) + t v` with `v` normal to all `∂_i x` they equal `2(g_ij - t v·ℓ_ij)`. The identity `f(x(u)) = ‖x(u)-p‖²` is the definition of `f` (not restated).
  The second partial `∂_i∂_j f` is `fderiv (w ↦ fderiv f w e_j) u e_i`. -/
namespace RoundTrip.V4_10
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
/-- Second fundamental form `ℓ_ij`: the normal component of `∂²x/∂u^i ∂u^j`. -/
noncomputable def ell (x : Rn k → Rn n) (u : Rn k) (i j : Fin k) : Rn n :=
  (tangSp x u)ᗮ.starProjection (d2x x u i j)
/-- The second fundamental form in the direction `v`: the matrix `(v · ℓ_ij)`. -/
noncomputable def sff (x : Rn k → Rn n) (u : Rn k) (v : Rn n) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => inner ℝ v (ell x u i j)
end Param

/-- `L_p(y) = ‖y - p‖²`. -/
noncomputable def Lp {n : ℕ} (p : Rn n) (y : Rn n) : ℝ := ‖y - p‖ ^ 2

/-- Milnor's claim. -/
def B : Prop :=
  (∀ (K d m : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M) (p : Rn (K + 1)),
    letI := hM.chartedSpace
    ∀ q : M, Morse.IsCriticalPointM (Rn (d + 1)) (fun y : M => Lp p y.1) q ↔
      ∀ w ∈ Milnor.Tub.tanN hM q, inner ℝ (q.1 - p) w = 0) ∧
  ∀ (k n : ℕ) (x : Rn k → Rn n) (U : Set (Rn k)), IsOpen U → ContDiffOn ℝ 2 x U → ∀ (p : Rn n), ∀ u ∈ U,
    (∀ i, fderiv ℝ (fun w => Lp p (x w)) u (EuclideanSpace.single i 1) = 2 * inner ℝ (dx x u i) (x u - p)) ∧
    ((∀ i, inner ℝ (dx x u i) (x u - p) = 0) →
      ∀ i j, fderiv ℝ (fun w => fderiv ℝ (fun w' => Lp p (x w')) w (EuclideanSpace.single j 1)) u (EuclideanSpace.single i 1)
        = 2 * (gmat x u i j + inner ℝ (d2x x u i j) (x u - p))) ∧
    ∀ (t : ℝ) (v : Rn n), (∀ l, inner ℝ v (dx x u l) = 0) → p = x u + t • v →
      ∀ i j, fderiv ℝ (fun w => fderiv ℝ (fun w' => Lp p (x w')) w (EuclideanSpace.single j 1)) u (EuclideanSpace.single i 1)
        = 2 * (gmat x u i j - t * sff x u v i j)
end RoundTrip.V4_10
