import Morse
/-! Blind formalization of V4_7 (Milnor §6, Lemma 6.3: focal points along a normal line). Choices:
- Setting (project's definitions, Mathlib lacks embedded submanifolds / tangent spaces of subsets): `M ⊆ ℝⁿ`, `n = K+1`, a smooth embedded submanifold of dimension `k = d+1 < n`
  (`Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝⁿ) ℝᵏ ℝᵐ M`, `d < K` required where used; dimension ≥ 1), tangent space `Milnor.Tub.tanN`.
- `N = NSet` = `{(q,v) ∈ ℝⁿ × ℝⁿ | q ∈ M, v ⊥ T_qM}` inside `ℝ²ⁿ = ℝⁿ × ℝⁿ`; endpoint map `E(q,v) = q + v` (`endpt`).
  The manifold structure of `N` is that of a slice submanifold `hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝ²ⁿ) ℝⁿ ℝⁿ N` (`hNN.chartedSpace`).
- Jacobian of `E` at `(q,v)` = `mfderiv` of `E|N` in that structure; nullity = `finrank` of its kernel (`nullE`, defined as `0` off `N`).
- Local coordinates `u¹..u^k` on `M ⊆ ℝⁿ` are packaged as a parametrization `x : ℝᵏ → ℝⁿ` (`x(u)` = the inclusion in coordinates), smooth (`C²` suffices) on an open set `U ∋ u`
  and an immersion there (`∂x/∂u^i` linearly independent). Derivatives are Mathlib `fderiv`s; `ℝᵏ = EuclideanSpace ℝ (Fin k)`.
- `g_ij = ⟨∂_i x, ∂_j x⟩`; `ℓ_ij` = orthogonal projection of `∂_i∂_j x` onto the orthogonal complement of `span{∂_i x}`
  (Mathlib `Submodule.starProjection`); `sff x u v` = matrix `(v · ℓ_ij)`.
- `x : ℝᵏ → ℝⁿ` (`k = d+1`, `n = K+1`) is a local coordinate patch of `M`: smooth on an open `U`, an immersion and injective on `U`, `x(U) ⊆ M`, `x(U)` open in `M`; `q = x u₀`, `(g_ij(u₀)) = 1`,
  `v` a unit vector with `(q, v) ∈ N` (normal at `q`), `K` principal curvatures (`IsPrincCurv`, eigenvalues of `(v·ℓ_ij)` with multiplicity, as in V4_6).
- B: for `e ∈ ℝⁿ`: `e` lies on `ℓ = {q + t v}` and is a focal point of `(M,q)` iff `e = q + K_i⁻¹ v` for some `i` with `K_i ≠ 0`; and the focal points of `(M,q)` on `ℓ`, counted with multiplicity
  (nullity of the Jacobian of `E` at `(q, t v)`), number at most `k`: the set of such `t` is finite and `∑ᶠ t, nullE (q, t v) ≤ k`. -/
namespace RoundTrip.V4_7
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

section
variable {K d m : ℕ}

/-- The normal bundle `N ⊆ M × ℝⁿ ⊆ ℝⁿ × ℝⁿ`: pairs `(q, v)` with `q ∈ M` and `v` perpendicular to `T_qM`. -/
def NSet {M : Set (Rn (K + 1))} (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M) :
    Set (Rn (K + 1) × Rn (K + 1)) :=
  {p | ∃ hq : p.1 ∈ M, ∀ w ∈ Milnor.Tub.tanN hM ⟨p.1, hq⟩, inner ℝ p.2 w = 0}

/-- The endpoint map `E(q, v) = q + v` (on `ℝⁿ × ℝⁿ`, restricted to `N` where used). -/
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

/-- `e` is a focal point of `M`: a focal point of `(M, q)` for some `q`. -/
def IsFocalPoint {M : Set (Rn (K + 1))}
    {hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M}
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1)) (NSet hM))
    (e : Rn (K + 1)) : Prop := ∃ q μ, IsFocalOfMult hNN q e μ
end

section Param
variable {k n : ℕ}
noncomputable def dx (x : Rn k → Rn n) (u : Rn k) (i : Fin k) : Rn n := fderiv ℝ x u (EuclideanSpace.single i 1)
noncomputable def d2x (x : Rn k → Rn n) (u : Rn k) (i j : Fin k) : Rn n :=
  fderiv ℝ (fun w => dx x w j) u (EuclideanSpace.single i 1)
noncomputable def gmat (x : Rn k → Rn n) (u : Rn k) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => inner ℝ (dx x u i) (dx x u j)
noncomputable def tangSp (x : Rn k → Rn n) (u : Rn k) : Submodule ℝ (Rn n) := Submodule.span ℝ (Set.range (dx x u))
noncomputable def ell (x : Rn k → Rn n) (u : Rn k) (i j : Fin k) : Rn n :=
  (tangSp x u)ᗮ.starProjection (d2x x u i j)
noncomputable def sff (x : Rn k → Rn n) (u : Rn k) (v : Rn n) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => inner ℝ v (ell x u i j)

/-- `K : Fin k → ℝ` lists the principal curvatures at `x u` in the direction `v`: the eigenvalues, with multiplicity, of the symmetric
matrix `(v · ℓ_ij)` (i.e. its characteristic polynomial is `∏ (X - K_i)`). Milnor uses coordinates with `(g_ij) = 1` at `q`. -/
noncomputable def IsPrincCurv {k n : ℕ} (x : Rn k → Rn n) (u : Rn k) (v : Rn n) (K : Fin k → ℝ) : Prop :=
  (sff x u v).charpoly = ∏ i, (Polynomial.X - Polynomial.C (K i))

/-- `r` is a principal radius of curvature: the reciprocal of a non-zero principal curvature. -/
def IsPrincRadius {k n : ℕ} (x : Rn k → Rn n) (u : Rn k) (v : Rn n) (r : ℝ) : Prop :=
  ∃ K : Fin k → ℝ, IsPrincCurv x u v K ∧ ∃ i, K i ≠ 0 ∧ r = (K i)⁻¹

end Param

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (K d m : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1)) (NSet hM))
    (x : Rn (d + 1) → Rn (K + 1)) (U : Set (Rn (d + 1))), IsOpen U → ContDiffOn ℝ ∞ x U →
    (∀ u ∈ U, LinearIndependent ℝ (dx x u)) → Set.InjOn x U → x '' U ⊆ M →
    IsOpen ((Subtype.val : M → Rn (K + 1)) ⁻¹' (x '' U)) →
    ∀ u₀ ∈ U, gmat x u₀ = 1 →
    ∀ v : Rn (K + 1), ‖v‖ = 1 → (x u₀, v) ∈ NSet hM →
    ∀ Kc : Fin (d + 1) → ℝ, IsPrincCurv x u₀ v Kc →
      (∀ e : Rn (K + 1), ((∃ t : ℝ, e = x u₀ + t • v) ∧ ∃ μ, IsFocalOfMult hNN (x u₀) e μ) ↔
        ∃ i, Kc i ≠ 0 ∧ e = x u₀ + (Kc i)⁻¹ • v) ∧
      {t : ℝ | 0 < nullE hNN (x u₀, t • v)}.Finite ∧
      ∑ᶠ t : ℝ, nullE hNN (x u₀, t • v) ≤ d + 1
end RoundTrip.V4_7
