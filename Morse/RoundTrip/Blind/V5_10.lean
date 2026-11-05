import Morse
/-! Blind formalization of V5_10 (Milnor §7, p. 41: the index bound). Choices:
- Complex setting: `ℂⁿ` is realified to `ℝ^{K+1} = ℝ^{2n}` (so `K+1` is even, which is forced by the existence of `J`); the complex structure (multiplication by `i`) is a linear isometry
  `J : ℝ^{K+1} ≃ₗᵢ ℝ^{K+1}` with `J² = -1`. A complex submanifold `M` of `ℂⁿ` is a smooth embedded real submanifold of `ℝ^{K+1}` (project's `Milnor.IsSliceSubmanifold`, tangent spaces `Milnor.Tub.tanN`)
  whose tangent spaces are `J`-invariant (`J (T_qM) ⊆ T_qM`). (The holomorphic-chart description is equivalent by the standard integrability fact for submanifolds of `ℂⁿ`; it is not formalized separately.)
  Real dimension `d+1 = 2k`, complex dimension `k`.
- `L_p(y) = ‖y - p‖²` restricted to `M` (chart structure `hM.chartedSpace`); critical point / non-degenerate / index: project's `Morse.IsCriticalPointM`, `Morse.IsNondegenerateCriticalPointM`, `Morse.indexM`.
- B: for `M` complex of complex dimension `k` (`d + 1 = 2k`), `p ∈ ℝ^{K+1}` and `q` a (non-degenerate, as in Milnor's setting where Lemma 6.9 applies) critical point of `L_p`, the index of `L_p` at `q` is at most `k`. -/
namespace RoundTrip.V5_10
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
    (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)), IsCplxStr J → IsCplxSub hM J → d + 1 = 2 * k →
    ∀ (p : Rn (K + 1)),
      letI := hM.chartedSpace
      ∀ q : M, Morse.IsCriticalPointM (Rn (d + 1)) (fun y : M => Lp p y.1) q →
        Morse.IsNondegenerateCriticalPointM (Rn (d + 1)) (fun y : M => Lp p y.1) q →
        Morse.indexM (Rn (d + 1)) (fun y : M => Lp p y.1) q ≤ k
end RoundTrip.V5_10
