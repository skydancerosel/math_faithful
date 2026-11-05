import Morse
/-! Blind formalization of V5_18 (Milnor §7, Corollary 7.3, Lefschetz). Choices:
- `ℂPⁿ` as in the V3_41 blind file (copied): unit vectors of `ℂ^{n+1}` modulo `z ∼ λz`, `|λ| = 1`, quotient topology; `cls z` = `(z_0 : … : z_n)`.
- Algebraic variety `V ⊆ ℂPⁿ`: the classes of the common zeros (on the unit sphere) of a set `S` of homogeneous complex polynomials in `n+1` variables (`projZero S`; for homogeneous
  `F` the zero condition is independent of the representative). Irreducibility is not required. Hyperplane `P = {Σ a_j z_j = 0}`, `a ≠ 0` (any hyperplane, not only `z_0 = 0`).
- "`V` has complex dimension `k` and `P` contains the singular points of `V`": the affine part `V − P`, realised as `affPart S a = {w ∈ ℂ^{n+1} | Σ a_j w_j = 1, F(w) = 0 ∀ F ∈ S}`
  (homeomorphic to `V − P` by `[z] ↦ z / Σ a_j z_j`; it lies in the affine hyperplane `Σ a_j w_j = 1 ≅ ℂⁿ = ℂPⁿ − P`), is a complex submanifold of complex dimension `k`
  (`IsCplxSubmfd`, the V5_10/V5_11 notion transported to `ℂ^{n+1}` by a real isometry `θ` carrying `i` to `J`, as in the V5_16 blind file). This makes every point of `V − P`
  a non-singular point of local dimension `k`. It does not exclude components of `V` lying inside `P` (of any dimension); the conclusion is unaffected by them
  (`H_*(V, V ∩ P)` only sees `V − P`), so this reading is at least as general as Milnor's. Setting forces `k ≥ 1` (the case `k = 0` is vacuous in Milnor anyway).
- Homology: Milnor names no coefficients, so integral homology (the item title says "over a field"; I follow the quoted statement): the project's `relHomology (ModuleCat.of ℤ ℤ)`
  of the pairs `(V ∩ P, ∅)`, `(V, ∅)` of subsets of `ℂPⁿ`; the map is the one induced by the inclusion of pairs (`subsetPairHom`).
- "Dimensions less than `k − 1`": `r + 1 < k`; "dimension `k − 1`": `r + 1 = k` (avoids truncated subtraction). -/
namespace RoundTrip.V5_18
open scoped ContDiff Manifold
open CategoryTheory Morse.Homology

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)
/-- `ℂⁿ`. -/
abbrev Cn (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- Unit vectors of `ℂ^{n+1}`: `Σ |z_j|² = 1`. -/
abbrev Sph (n : ℕ) : Type := {z : Fin (n + 1) → ℂ // ∑ j, ‖z j‖ ^ 2 = 1}

/-- `z ∼ w` iff `w = λ z` with `|λ| = 1`. -/
def Rel (n : ℕ) (z w : Sph n) : Prop := ∃ c : ℂ, ‖c‖ = 1 ∧ w.1 = c • z.1

/-- `ℂPⁿ`: equivalence classes of unit vectors of `ℂ^{n+1}`, with the quotient topology. -/
def CPn (n : ℕ) : Type := Quot (Rel n)

instance (n : ℕ) : TopologicalSpace (CPn n) := inferInstanceAs (TopologicalSpace (Quot (Rel n)))

/-- The class `(z_0 : … : z_n)`. -/
def cls {n : ℕ} (z : Sph n) : CPn n := Quot.mk _ z

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

/-- The projective algebraic set `V ⊆ ℂPⁿ` of a set `S` of (homogeneous) polynomials. -/
def projZero {n : ℕ} (S : Set (MvPolynomial (Fin (n + 1)) ℂ)) : Set (CPn n) :=
  cls '' {z | ∀ F ∈ S, MvPolynomial.eval z.1 F = 0}

/-- The hyperplane `P = {Σ a_j z_j = 0}`. -/
def hyperplane {n : ℕ} (a : Fin (n + 1) → ℂ) : Set (CPn n) := cls '' {z | ∑ j, a j * z.1 j = 0}

/-- `V − P` in the affine hyperplane `{Σ a_j w_j = 1} ⊆ ℂ^{n+1}`. -/
def affPart {n : ℕ} (S : Set (MvPolynomial (Fin (n + 1)) ℂ)) (a : Fin (n + 1) → ℂ) : Set (Cn (n + 1)) :=
  {w | ∑ j, a j * w j = 1 ∧ ∀ F ∈ S, MvPolynomial.eval (fun j => w j) F = 0}

/-- `H_i(A; ℤ)` for a subset `A` of a space (project's singular homology of `(A, ∅)`). -/
noncomputable def HZ {E : Type} [TopologicalSpace E] (A : Set E) (i : ℕ) : ModuleCat ℤ :=
  (relHomology (ModuleCat.of ℤ ℤ) i).obj (subsetPair (Set.empty_subset A))

/-- The map `H_i(A; ℤ) → H_i(B; ℤ)` induced by the inclusion `A ⊆ B`. -/
noncomputable def inclZ {E : Type} [TopologicalSpace E] {A B : Set E} (h : A ⊆ B) (i : ℕ) : HZ A i ⟶ HZ B i :=
  (relHomology (ModuleCat.of ℤ ℤ) i).map (subsetPairHom (Set.empty_subset A) (Set.empty_subset B) le_rfl h)

/-- Lefschetz: `H_r(V ∩ P) → H_r(V)` is an isomorphism for `r < k − 1` and onto for `r = k − 1`. -/
def B : Prop :=
  ∀ (n k : ℕ) (S : Set (MvPolynomial (Fin (n + 1)) ℂ)) (a : Fin (n + 1) → ℂ),
    (∀ F ∈ S, ∃ d, F.IsHomogeneous d) → a ≠ 0 → IsCplxSubmfd (affPart S a) k →
    ∀ r : ℕ,
      (r + 1 < k → Function.Bijective
        (inclZ (Set.inter_subset_left : projZero S ∩ hyperplane a ⊆ projZero S) r).hom) ∧
      (r + 1 = k → Function.Surjective
        (inclZ (Set.inter_subset_left : projZero S ∩ hyperplane a ⊆ projZero S) r).hom)
end RoundTrip.V5_18
