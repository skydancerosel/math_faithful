import Morse
/-! Blind formalization of V5_15 (Milnor §7, Theorem 7.2). Choices (setting copied from the V5_10/V5_11 blind files):
- Complex setting: `ℂⁿ` is realified to `ℝ^{K+1} = ℝ^{2n}` (so `K+1` is even, which is forced by the existence of `J`); the complex structure (multiplication by `i`) is a linear isometry
  `J : ℝ^{K+1} ≃ₗᵢ ℝ^{K+1}` with `J² = -1`. A complex submanifold `M` of `ℂⁿ` is a smooth embedded real submanifold of `ℝ^{K+1}` (project's `Milnor.IsSliceSubmanifold`, tangent spaces `Milnor.Tub.tanN`)
  whose tangent spaces are `J`-invariant (`J (T_qM) ⊆ T_qM`). (The holomorphic-chart description, "bianalytically embedded", is equivalent by the standard integrability fact for
  submanifolds of `ℂⁿ`; it is not formalized separately.) Real dimension `d+1 = 2k`, complex dimension `k` (so `k ≥ 1`, forced by the model `ℝ^{d+1}`; `k = 0` is not covered).
- "Embedded as a closed subset": `IsClosed M`.
- "Homotopy type of a `k`-dimensional CW-complex" read as "of dimension at most `k`" (as in V5_11): there is a Hausdorff space `Y : Type` with a Mathlib classical CW structure
  `Topology.CWComplex (Set.univ : Set Y)` with no cells of dimension `l > k`, and a homotopy equivalence `ContinuousMap.HomotopyEquiv M Y` (`M` with the subspace topology).
  (Exactly `k` would fail for `M = ∅`, and is not what the proof gives.)
- B is the theorem only; the choice of `p` and the properties of `L_p` (V5_11) are not part of it. -/
namespace RoundTrip.V5_15
open scoped ContDiff Manifold

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- `J` is a complex structure (multiplication by `i`): a linear isometry of `ℝ^{K+1}` with `J ∘ J = -1`. -/
def IsCplxStr {K : ℕ} (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) : Prop := ∀ x, J (J x) = -x

/-- `M` is a complex submanifold: all tangent spaces are `J`-invariant. -/
def IsCplxSub {K d m : ℕ} {M : Set (Rn (K + 1))}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M) (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) : Prop :=
  ∀ q : M, ∀ x ∈ Milnor.Tub.tanN hM q, J x ∈ Milnor.Tub.tanN hM q

/-- A closed complex submanifold of `ℂⁿ` of complex dimension `k` has the homotopy type of a CW complex of dimension `≤ k`. -/
def B : Prop :=
  ∀ (K d m k : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
    (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)), IsCplxStr J → IsCplxSub hM J → IsClosed M → d + 1 = 2 * k →
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : Topology.CWComplex (Set.univ : Set Y)),
      Nonempty (ContinuousMap.HomotopyEquiv M Y) ∧
      ∀ l : ℕ, k < l → IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) l)
end RoundTrip.V5_15
