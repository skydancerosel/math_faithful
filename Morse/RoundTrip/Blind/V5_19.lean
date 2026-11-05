import Morse
/-! Blind formalization of V5_19 (Milnor §7, Theorem 7.4, Lefschetz). Choices:
- "The same hypotheses" (those of Corollary 7.3), formalized exactly as in the V5_18 blind file (copied): `ℂPⁿ` as in V3_41 (quotient of the unit sphere of `ℂ^{n+1}`);
  `V = projZero S` for a set `S` of homogeneous polynomials; any hyperplane `P = {Σ a_j z_j = 0}`, `a ≠ 0`; "`V` of complex dimension `k`, singular points in `P`" := the affine
  part `affPart S a ⊆ {Σ a_j w_j = 1} ⊆ ℂ^{n+1}` (≅ `V − P`) is a complex submanifold of complex dimension `k` (`IsCplxSubmfd`, as in V5_16/V5_18; forces `k ≥ 1`).
- Relative homotopy groups are not in Mathlib. "`π_r(V, V ∩ P) = 0`" := `RelPiZero`: for every base point in `V ∩ P` the group vanishes, in the equivalent form of the
  compression criterion: every map `(Dʳ, Sʳ⁻¹) → (V, V ∩ P)` is homotopic rel `Sʳ⁻¹` to a map into `V ∩ P` (`Dʳ` = closed unit ball of `ℝʳ`, `Sʳ⁻¹` its boundary sphere,
  as in the other blind files). `V` carries the subspace topology of `ℂPⁿ`. Range `1 ≤ r < k` (relative homotopy groups are defined for `r ≥ 1`; `r = 0` excluded).
- B is the theorem only; the proof ingredients (`f = 1/L_p`, index `≥ k`, the deformable neighbourhood from triangulability) are not part of B (cf. V5_17). -/
namespace RoundTrip.V5_19
open scoped ContDiff Manifold

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

/-- The closed unit ball `e^r = Dʳ` in ℝʳ. -/
abbrev Cell (r : ℕ) : Type := Metric.closedBall (0 : EuclideanSpace ℝ (Fin r)) 1
/-- Its boundary sphere `Sʳ⁻¹`. -/
abbrev Bdry (r : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin r)) 1
/-- The inclusion of the boundary sphere into the cell. -/
def bdryToCell {r : ℕ} (x : Bdry r) : Cell r := ⟨x.1, Metric.sphere_subset_closedBall x.2⟩

/-- `π_r(X, A, x₀) = 0` for every `x₀ ∈ A` (compression criterion): every map `(Dʳ, Sʳ⁻¹) → (X, A)` is homotopic rel `Sʳ⁻¹`
to a map into `A`. -/
def RelPiZero (X : Type) [TopologicalSpace X] (A : Set X) (r : ℕ) : Prop :=
  ∀ f : C(Cell r, X), (∀ x : Bdry r, f (bdryToCell x) ∈ A) →
    ∃ g : C(Cell r, X), (∀ c, g c ∈ A) ∧ f.HomotopicRel g (Set.range bdryToCell)

/-- Lefschetz: `π_r(V, V ∩ P) = 0` for `r < k`. -/
def B : Prop :=
  ∀ (n k : ℕ) (S : Set (MvPolynomial (Fin (n + 1)) ℂ)) (a : Fin (n + 1) → ℂ),
    (∀ F ∈ S, ∃ d, F.IsHomogeneous d) → a ≠ 0 → IsCplxSubmfd (affPart S a) k →
    ∀ r : ℕ, 1 ≤ r → r < k → RelPiZero (projZero S) (Subtype.val ⁻¹' hyperplane a) r
end RoundTrip.V5_19
