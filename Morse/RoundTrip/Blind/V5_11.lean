import Morse
/-! Blind formalization of V5_11 (Milnor §7, proof of Theorem 7.2: the CW-complex of dimension ≤ k). Choices:
- Complex setting: `ℂⁿ` is realified to `ℝ^{K+1} = ℝ^{2n}` (so `K+1` is even, which is forced by the existence of `J`); the complex structure (multiplication by `i`) is a linear isometry
  `J : ℝ^{K+1} ≃ₗᵢ ℝ^{K+1}` with `J² = -1`. A complex submanifold `M` of `ℂⁿ` is a smooth embedded real submanifold of `ℝ^{K+1}` (project's `Milnor.IsSliceSubmanifold`, tangent spaces `Milnor.Tub.tanN`)
  whose tangent spaces are `J`-invariant (`J (T_qM) ⊆ T_qM`). (The holomorphic-chart description is equivalent by the standard integrability fact for submanifolds of `ℂⁿ`; it is not formalized separately.)
  Real dimension `d+1 = 2k`, complex dimension `k`.
- `M` is a closed subset of `ℂⁿ` (`IsClosed M`) and of complex dimension `k` (`d + 1 = 2k`).
- `L_p(y) = ‖y - p‖²` on `M`. "No degenerate critical points": every critical point (`Morse.IsCriticalPointM`) is non-degenerate (`Morse.IsNondegenerateCriticalPointM`); index `Morse.indexM`.
- "Homotopy type of a CW-complex of dimension at most `k`": there is a Hausdorff space `Y : Type` with a Mathlib classical CW structure `CWComplex (Set.univ : Set Y)` all of whose cells of dimension `l > k` are absent
  (`IsEmpty (CWComplex.cell univ l)`), and a homotopy equivalence `ContinuousMap.HomotopyEquiv M Y` (`M` with the subspace topology).
- B: there exists `p ∈ ℂⁿ` with (1) `L_p` having no degenerate critical points, (2) every `M^a = {L_p ≤ a}` compact, (3) every critical point of `L_p` of index ≤ `k` (so (1)-(3) are Milnor's assertions),
  and (4) `M` has the homotopy type of a CW complex of dimension at most `k`. -/
namespace RoundTrip.V5_11
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- `J` is a complex structure (multiplication by `i`): a linear isometry of `ℝ^{K+1}` with `J ∘ J = -1`. -/
def IsCplxStr {K : ℕ} (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) : Prop := ∀ x, J (J x) = -x

/-- `M` is a complex submanifold: all tangent spaces are `J`-invariant. -/
def IsCplxSub {K d m : ℕ} {M : Set (Rn (K + 1))}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M) (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) : Prop :=
  ∀ q : M, ∀ x ∈ Milnor.Tub.tanN hM q, J x ∈ Milnor.Tub.tanN hM q

/-- `L_p(y) = ‖y - p‖²`. -/
noncomputable def Lp {n : ℕ} (p : Rn n) (y : Rn n) : ℝ := ‖y - p‖ ^ 2

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (K d m k : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
    (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)), IsCplxStr J → IsCplxSub hM J → IsClosed M → d + 1 = 2 * k →
    letI := hM.chartedSpace
    ∃ p : Rn (K + 1),
      (∀ q : M, Morse.IsCriticalPointM (Rn (d + 1)) (fun y : M => Lp p y.1) q →
        Morse.IsNondegenerateCriticalPointM (Rn (d + 1)) (fun y : M => Lp p y.1) q) ∧
      (∀ a : ℝ, IsCompact {q : M | Lp p q.1 ≤ a}) ∧
      (∀ q : M, Morse.IsCriticalPointM (Rn (d + 1)) (fun y : M => Lp p y.1) q →
        Morse.indexM (Rn (d + 1)) (fun y : M => Lp p y.1) q ≤ k) ∧
      ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : Topology.CWComplex (Set.univ : Set Y)),
        Nonempty (ContinuousMap.HomotopyEquiv M Y) ∧
        ∀ l : ℕ, k < l → IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) l)
end RoundTrip.V5_11
