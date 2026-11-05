import Morse
/-! Blind formalization of V5_17 (Milnor §7, pp. 41–42: Corollary 7.3 and Theorem 7.4 for an abstract pair `(X, A)` in place of `(V, V ∩ P)`). Choices:
- Reading: the quoted text says which facts about `(V, V ∩ P)` the two proofs use; B asserts that the conclusions follow for any pair with those properties.
  The role of `V − (V ∩ P) ⊆ ℂⁿ = ℂPⁿ − P` is played by a homeomorphism `X − A ≅ M` with `M` a closed complex submanifold of `ℂⁿ` of complex dimension `k`, in the setting of the
  V5_10/V5_11 blind files (copied): `M ⊆ ℝ^{K+1}` slice submanifold of dimension `d+1 = 2k`, `J`-invariant tangent spaces, `J` a complex structure, `IsClosed M`. This is what
  Theorem 7.1 (via 7.2) and the function `1/L_p` need; algebraicity of `M` is not used by either argument and is not assumed. Forces `k ≥ 1`.
- (7.3, abstract) Coefficients: a field `F` (arbitrary). Lefschetz duality `H_r(X, A) ≅ H^{2k−r}(X − A)` is taken as a hypothesis, for `r ≤ 2k`, with cohomology over a field
  written as the dual space of homology (`H^j(Y; F) = Hom_F(H_j(Y; F), F)`, universal coefficients over a field; Mathlib/the vocabulary have no singular cohomology, so an
  integral version cannot be stated). Homology: project's `relHomology (ModuleCat.of F F)` on `subsetPair` (as `Hom` in the V3_3x blind files). No compactness is assumed
  for this part (the duality is given). Conclusion as in V5_18: `H_r(A) → H_r(X)` (inclusion of pairs `(A, ∅) → (X, ∅)`) bijective for `r + 1 < k`, onto for `r + 1 = k`.
- (7.4, abstract) `X` compact Hausdorff, `A ⊆ X` closed (as `V`, `V ∩ P`; this makes `f = 0` on `A`, `1/L_p` off `A` continuous). Milnor's hypothesis "some neighborhood `U` of
  `A` can be deformed into `A` within `X`" (`Deformable`): `U` a neighbourhood of `A` (`U ∈ 𝓝ˢ A`) and a homotopy `H : U × [0,1] → X` with `H_0 = ` inclusion, `H_1(U) ⊆ A`, and
  `H_t(A) ⊆ A` for all `t`. The last condition is my reading: the phrase does not say what happens to `A`; with no condition at all the deformation is not one of pairs and
  Milnor's argument (`π_r(X^ε, A) → π_r(X, A)` must vanish) does not go through; triangulability, which Milnor cites, gives even `A` fixed pointwise (a stronger hypothesis
  than mine). Conclusion `π_r(X, A) = 0` for `1 ≤ r < k`, as `RelPiZero` of the V5_19 blind file (compression criterion, every base point in `A`).
- B = conjunction of the two abstract statements. -/
namespace RoundTrip.V5_17
open scoped ContDiff Manifold unitInterval Topology
open CategoryTheory Morse.Homology

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- `J` is a complex structure (multiplication by `i`): a linear isometry of `ℝ^{K+1}` with `J ∘ J = -1`. -/
def IsCplxStr {K : ℕ} (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) : Prop := ∀ x, J (J x) = -x

/-- `M` is a complex submanifold: all tangent spaces are `J`-invariant. -/
def IsCplxSub {K d m : ℕ} {M : Set (Rn (K + 1))}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M) (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) : Prop :=
  ∀ q : M, ∀ x ∈ Milnor.Tub.tanN hM q, J x ∈ Milnor.Tub.tanN hM q

/-- `H_n(B, A; F)` for `A ⊆ B` subsets of a space (project's relative singular homology). -/
noncomputable def Hom (F : Type) [Field F] {E : Type} [TopologicalSpace E] {A B : Set E} (h : A ⊆ B) (n : ℕ) :
    ModuleCat F := (relHomology (ModuleCat.of F F) n).obj (subsetPair h)

/-- The map `H_i(A; F) → H_i(B; F)` induced by the inclusion `A ⊆ B`. -/
noncomputable def inclF (F : Type) [Field F] {E : Type} [TopologicalSpace E] {A B : Set E} (h : A ⊆ B) (i : ℕ) :
    Hom F (Set.empty_subset A) i ⟶ Hom F (Set.empty_subset B) i :=
  (relHomology (ModuleCat.of F F) i).map (subsetPairHom (Set.empty_subset A) (Set.empty_subset B) le_rfl h)

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

/-- Some neighbourhood `U` of `A` can be deformed into `A` within `X` (points of `A` staying in `A`). -/
def Deformable (X : Type) [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ U : Set X, U ∈ 𝓝ˢ A ∧ ∃ H : C(U × I, X),
    (∀ x : U, H (x, 0) = x.1) ∧ (∀ x : U, H (x, 1) ∈ A) ∧ (∀ (x : U) (t : I), x.1 ∈ A → H (x, t) ∈ A)

/-- Corollary 7.3 and Theorem 7.4 for an abstract pair `(X, A)` with `X − A` a closed complex submanifold of `ℂⁿ`:
from Lefschetz duality, resp. from a neighbourhood of `A` deformable into `A`. -/
def B : Prop :=
  (∀ (F : Type) [Field F] (X : Type) [TopologicalSpace X] (A : Set X)
      (K d m k : ℕ) (M : Set (Rn (K + 1)))
      (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
      (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)), IsCplxStr J → IsCplxSub hM J → IsClosed M → d + 1 = 2 * k →
      Nonempty (↥(Aᶜ) ≃ₜ ↥M) →
      (∀ r : ℕ, r ≤ 2 * k → Nonempty (Hom F (Set.subset_univ A) r ≃ₗ[F]
        Module.Dual F (Hom F (Set.empty_subset (Aᶜ)) (2 * k - r)))) →
      ∀ r : ℕ, (r + 1 < k → Function.Bijective (inclF F (Set.subset_univ A) r).hom) ∧
        (r + 1 = k → Function.Surjective (inclF F (Set.subset_univ A) r).hom)) ∧
  (∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : Set X), IsClosed A →
      ∀ (K d m k : ℕ) (M : Set (Rn (K + 1)))
      (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
      (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)), IsCplxStr J → IsCplxSub hM J → IsClosed M → d + 1 = 2 * k →
      Nonempty (↥(Aᶜ) ≃ₜ ↥M) → Deformable X A →
      ∀ r : ℕ, 1 ≤ r → r < k → RelPiZero X A r)
end RoundTrip.V5_17
