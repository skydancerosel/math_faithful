import Morse
/-! Blind formalization of V4_9 (Milnor §6, Assertion 6.4). Choices:
- Setting (project's definitions, Mathlib lacks embedded submanifolds / tangent spaces of subsets): `M ⊆ ℝⁿ`, `n = K+1`, a smooth embedded submanifold of dimension `k = d+1`
  (`Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝⁿ) ℝᵏ ℝᵐ M`), tangent space `Milnor.Tub.tanN`. Its charted-space structure is `hM.chartedSpace`.
- `N = NSet` = `{(q,v) ∈ ℝⁿ × ℝⁿ | q ∈ M, v ⊥ T_qM}` inside `ℝ²ⁿ = ℝⁿ × ℝⁿ`; endpoint map `E(q,v) = q + v` (`endpt`). The manifold structure of `N` is a slice-submanifold
  structure `hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝ²ⁿ) ℝⁿ ℝⁿ N` (quantified as an argument).
- Jacobian of `E` at `(q,v)` = `mfderiv` of `E|N` in that structure; nullity = `finrank` of its kernel (`nullE`, `0` off `N`); `IsFocalOfMult hNN q e μ`: focal point of `(M,q)` of multiplicity `μ`.
- Local coordinates `u¹..u^k` on `M ⊆ ℝⁿ` are packaged as a parametrization `x : ℝᵏ → ℝⁿ` (`x(u)` = the inclusion in coordinates), smooth on an open set `U`, an immersion there.
  Derivatives are Mathlib `fderiv`s; `ℝᵏ = EuclideanSpace ℝ (Fin k)`. `g_ij = ⟨∂_i x, ∂_j x⟩`; `ℓ_ij` = orthogonal projection of `∂_i∂_j x` onto the orthogonal complement of `span{∂_i x}`;
  `sff x u v` = matrix `(v · ℓ_ij)`.
- `x` a coordinate patch (`IsPatch`) around `q = x u₀`; `v` a unit normal vector at `q` (`‖v‖ = 1`, `(q,v) ∈ N`). Milnor does NOT assume `(g_ij) = 1` here, so none is assumed.
- Matrix nullity = `finrank` of the kernel of `mulVecLin`; "singular of nullity μ" = nullity `μ` with `μ > 0`.
- B: for all `t` and `μ`: `q + t v` is a focal point of `(M,q)` of multiplicity `μ` iff `(g_ij - t v·ℓ_ij)` is singular of nullity `μ`. -/
namespace RoundTrip.V4_9
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

section
variable {K d m : ℕ}

/-- The normal bundle `N ⊆ M × ℝⁿ ⊆ ℝⁿ × ℝⁿ`: pairs `(q, v)` with `q ∈ M` and `v` perpendicular to `T_qM`. -/
def NSet {M : Set (Rn (K + 1))} (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M) :
    Set (Rn (K + 1) × Rn (K + 1)) :=
  {p | ∃ hq : p.1 ∈ M, ∀ w ∈ Milnor.Tub.tanN hM ⟨p.1, hq⟩, inner ℝ p.2 w = 0}

/-- The endpoint map `E(q, v) = q + v`. -/
def endpt (p : Rn (K + 1) × Rn (K + 1)) : Rn (K + 1) := p.1 + p.2

open Classical in
/-- Nullity of the Jacobian of `E : N → ℝⁿ` at `p ∈ N` (`0` if `p ∉ N`); `N` carries the structure of the slice submanifold `hNN`. -/
noncomputable def nullE {M : Set (Rn (K + 1))}
    {hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M}
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1)) (NSet hM))
    (p : Rn (K + 1) × Rn (K + 1)) : ℕ :=
  letI := hNN.chartedSpace
  if h : p ∈ NSet hM then
    Module.finrank ℝ (LinearMap.ker
      (mfderiv 𝓘(ℝ, Rn (K + 1)) 𝓘(ℝ, Rn (K + 1)) (fun x : NSet hM => endpt x.1) ⟨p, h⟩).toLinearMap)
  else 0

/-- `e` is a focal point of `(M, q)` of multiplicity `μ`: `e = q + v`, `(q, v) ∈ N`, Jacobian of `E` at `(q, v)` has nullity `μ > 0`. -/
def IsFocalOfMult {M : Set (Rn (K + 1))}
    {hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M}
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1)) (NSet hM))
    (q e : Rn (K + 1)) (μ : ℕ) : Prop := 0 < μ ∧ nullE hNN (q, e - q) = μ
end

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

/-- `x : ℝᵏ → ℝⁿ` (`k = d+1`, `n = K+1`) is a local coordinate patch of `M`: smooth on an open `U`, an immersion and injective on `U`,
`x(U) ⊆ M`, `x(U)` open in `M`. -/
def IsPatch {K d m : ℕ} {M : Set (Rn (K + 1))} (_hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
    (x : Rn (d + 1) → Rn (K + 1)) (U : Set (Rn (d + 1))) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ ∞ x U ∧ (∀ u ∈ U, LinearIndependent ℝ (dx x u)) ∧ Set.InjOn x U ∧ x '' U ⊆ M ∧
    IsOpen ((Subtype.val : M → Rn (K + 1)) ⁻¹' (x '' U))

/-- Nullity of a square matrix. -/
noncomputable def matNullity {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : ℕ :=
  Module.finrank ℝ (LinearMap.ker A.mulVecLin)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (K d m : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1)) (NSet hM))
    (x : Rn (d + 1) → Rn (K + 1)) (U : Set (Rn (d + 1))), IsPatch hM x U →
    ∀ u₀ ∈ U, ∀ v : Rn (K + 1), ‖v‖ = 1 → (x u₀, v) ∈ NSet hM →
    ∀ (t : ℝ) (μ : ℕ),
      IsFocalOfMult hNN (x u₀) (x u₀ + t • v) μ ↔ (0 < μ ∧ matNullity (gmat x u₀ - t • sff x u₀ v) = μ)
end RoundTrip.V4_9
