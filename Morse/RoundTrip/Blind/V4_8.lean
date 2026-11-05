import Morse
/-! Blind formalization of V4_8 (Milnor §6, proof of Lemma 6.3: the Jacobian of the endpoint map). Choices:
- Local coordinates `u¹..u^k` on `M ⊆ ℝⁿ` are packaged as a parametrization `x : ℝᵏ → ℝⁿ` (`x(u)` = the inclusion in coordinates), smooth (`C²` suffices) on an open set `U ∋ u`
  and an immersion there (`∂x/∂u^i` linearly independent). Derivatives are Mathlib `fderiv`s; `ℝᵏ = EuclideanSpace ℝ (Fin k)`.
- `g_ij = ⟨∂_i x, ∂_j x⟩`; `ℓ_ij` = orthogonal projection of `∂_i∂_j x` onto the orthogonal complement of `span{∂_i x}`
  (Mathlib `Submodule.starProjection`); `sff x u v` = matrix `(v · ℓ_ij)`.
- Parametrization `x : ℝᵏ → ℝⁿ` smooth on open `U`, immersion; unit normal fields `w_α : ℝᵏ → ℝⁿ` (`α : Fin m`, `k + m = n`) smooth on `U`, pairwise orthonormal, orthogonal to all `∂_j x`.
- Milnor's coordinates `(u,t)` on `N` are formalized through the coordinate expression of the endpoint map `Ẽ(u,t) = x(u) + Σ_α t^α w_α(u) : ℝᵏ × ℝᵐ → ℝⁿ`
  (the claim that `(u,t) ↦ (x(u), Σ t^α w_α(u))` are coordinates on `N` is not formalized); Jacobian `J = fderiv ℝ Ẽ (u,t)`.
- `P` = matrix `⟨∂Ẽ/∂(u^i or t^α), (∂x/∂u^j or w_β)⟩` indexed by `Fin k ⊕ Fin m`. B: (1) `P_ij = g_ij - Σ_α t^α w_α·ℓ_ij` on the upper-left block `A`; (2) lower-left block `0`, lower-right block the identity;
  (3) `rank P = rank J`; (4) rank of `P` is `rank A + m` and equivalently the nullity of `J` equals the nullity of `A` (`k - rank A`)
  -- Milnor's "rank equals that of the upper left block" read as nullity equality (rank literally differs by the identity block of size `m`); both forms are stated. -/
namespace RoundTrip.V4_8
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

/-- Coordinate expression of the endpoint map: `Ẽ(u, t) = x(u) + Σ t^α w_α(u)`. -/
noncomputable def Etil {k m n : ℕ} (x : Rn k → Rn n) (w : Fin m → Rn k → Rn n) (z : Rn k × Rn m) : Rn n :=
  x z.1 + ∑ α, z.2 α • w α z.1

/-- Upper-left block `A_ij = g_ij - Σ_α t^α (w_α · ℓ_ij)`. -/
noncomputable def Ablock {k m n : ℕ} (x : Rn k → Rn n) (w : Fin m → Rn k → Rn n) (u : Rn k) (t : Rn m) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => gmat x u i j - ∑ α, t α * inner ℝ (w α u) (ell x u i j)

/-- Milnor's `n × n` matrix of inner products of the partials of `Ẽ` with `∂x/∂u^1..∂x/∂u^k, w_1..w_m`. -/
noncomputable def Pmat {k m n : ℕ} (x : Rn k → Rn n) (w : Fin m → Rn k → Rn n) (u : Rn k) (t : Rn m) :
    Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℝ :=
  Matrix.of fun a b =>
    inner ℝ (fderiv ℝ (Etil x w) (u, t)
        (Sum.elim (fun i => (EuclideanSpace.single i (1 : ℝ), (0 : Rn m))) (fun α => ((0 : Rn k), EuclideanSpace.single α (1 : ℝ))) a))
      (Sum.elim (dx x u) (fun α => w α u) b)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (k m n : ℕ), k + m = n → ∀ (x : Rn k → Rn n) (w : Fin m → Rn k → Rn n) (U : Set (Rn k)), IsOpen U →
    ContDiffOn ℝ ∞ x U → (∀ u ∈ U, LinearIndependent ℝ (dx x u)) → (∀ α, ContDiffOn ℝ ∞ (w α) U) →
    (∀ u ∈ U, ∀ α β, inner ℝ (w α u) (w β u) = if α = β then (1 : ℝ) else 0) →
    (∀ u ∈ U, ∀ α j, inner ℝ (w α u) (dx x u j) = 0) →
    ∀ u ∈ U, ∀ t : Rn m,
      (∀ i j, Pmat x w u t (Sum.inl i) (Sum.inl j) = Ablock x w u t i j) ∧
      (∀ α j, Pmat x w u t (Sum.inr α) (Sum.inl j) = 0) ∧
      (∀ α β, Pmat x w u t (Sum.inr α) (Sum.inr β) = if α = β then 1 else 0) ∧
      (Pmat x w u t).rank = Module.finrank ℝ (LinearMap.range (fderiv ℝ (Etil x w) (u, t)).toLinearMap) ∧
      (Pmat x w u t).rank = (Ablock x w u t).rank + m ∧
      Module.finrank ℝ (LinearMap.ker (fderiv ℝ (Etil x w) (u, t)).toLinearMap) = k - (Ablock x w u t).rank
end RoundTrip.V4_8
