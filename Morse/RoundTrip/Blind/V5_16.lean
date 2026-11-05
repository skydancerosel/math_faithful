import Morse
/-! Blind formalization of V5_16 (Milnor §7, Theorem 7.1, Andreotti–Frankel). Choices:
- `ℂⁿ` = `Cn n` = `EuclideanSpace ℂ (Fin n)` (polynomials are evaluated at its points). "Complex submanifold of complex dimension `k`" is the notion of the V5_10/V5_11 blind
  files transported to `ℂⁿ` (`IsCplxSubmfd`): for some real linear isometry `θ : ℂⁿ ≅ ℝ^{K+1}` carrying multiplication by `i` to `J` (`IsRealif`, `J` a complex structure
  as in V5_10), `θ(S)` is a slice submanifold (`Milnor.IsSliceSubmanifold`) of dimension `d+1 = 2k` whose tangent spaces (`Milnor.Tub.tanN`) are `J`-invariant. This does not
  depend on `θ` (two such `θ` differ by an isometry intertwining the `J`'s). Consequence of the setting: `k ≥ 1` (model `ℝ^{d+1}`), so `k = 0` (finite `M`) is not covered.
- "Non-singular affine algebraic variety `M ⊆ ℂⁿ` of real dimension `2k`": `M = {z | F(z) = 0 for all F ∈ S}` for a set `S` of complex polynomials in `n` variables, and `M` is
  a complex submanifold of complex dimension `k` (non-singular at every point, pure dimension `k`). Irreducibility is not required (Milnor's proof does not use it).
- `H_i(M; ℤ)`: the project's singular homology `relHomology (ModuleCat.of ℤ ℤ) i` of the pair `(M, ∅)` of subsets of `ℂⁿ`; "`= 0`" := subsingleton.
- Coefficients: Milnor's statement is with `ℤ`, so B uses `ℤ` (the item title says "over a field"; I follow the quoted statement). -/
namespace RoundTrip.V5_16
open scoped ContDiff Manifold
open CategoryTheory Morse.Homology

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)
/-- `ℂⁿ`. -/
abbrev Cn (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- `J` is a complex structure (multiplication by `i`): a linear isometry of `ℝ^{K+1}` with `J ∘ J = -1`. -/
def IsCplxStr {K : ℕ} (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) : Prop := ∀ x, J (J x) = -x

/-- `M` is a complex submanifold: all tangent spaces are `J`-invariant. -/
def IsCplxSub {K d m : ℕ} {M : Set (Rn (K + 1))}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M) (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) : Prop :=
  ∀ q : M, ∀ x ∈ Milnor.Tub.tanN hM q, J x ∈ Milnor.Tub.tanN hM q

/-- `θ : ℂⁿ ≅ ℝ^{K+1}` is a real linear isometry carrying multiplication by `i` to `J`. -/
def IsRealif {n K : ℕ} (θ : Cn n ≃ₗᵢ[ℝ] Rn (K + 1)) (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) : Prop :=
  ∀ z : Cn n, θ (Complex.I • z) = J (θ z)

/-- `S ⊆ ℂⁿ` is a complex submanifold of complex dimension `k` (real dimension `2k`). -/
def IsCplxSubmfd {n : ℕ} (S : Set (Cn n)) (k : ℕ) : Prop :=
  ∃ (K d m : ℕ) (θ : Cn n ≃ₗᵢ[ℝ] Rn (K + 1)) (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) (θ '' S)),
    IsCplxStr J ∧ IsRealif θ J ∧ IsCplxSub hM J ∧ d + 1 = 2 * k

/-- The common zero set in `ℂⁿ` of a set of polynomials. -/
def zeroSet {n : ℕ} (S : Set (MvPolynomial (Fin n) ℂ)) : Set (Cn n) :=
  {z | ∀ F ∈ S, MvPolynomial.eval (fun j => z j) F = 0}

/-- `H_i(A; ℤ)` for a subset `A` of a space (project's singular homology of `(A, ∅)`). -/
noncomputable def HZ {E : Type} [TopologicalSpace E] (A : Set E) (i : ℕ) : ModuleCat ℤ :=
  (relHomology (ModuleCat.of ℤ ℤ) i).obj (subsetPair (Set.empty_subset A))

/-- A non-singular affine algebraic variety `M ⊆ ℂⁿ` of real dimension `2k` has `H_i(M; ℤ) = 0` for `i > k`. -/
def B : Prop :=
  ∀ (n k : ℕ) (S : Set (MvPolynomial (Fin n) ℂ)), IsCplxSubmfd (zeroSet S) k →
    ∀ i : ℕ, k < i → Subsingleton (HZ (zeroSet S) i)
end RoundTrip.V5_16
