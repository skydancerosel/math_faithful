import Morse
/-! Blind formalization of V5_5 (Milnor §7, proof of Assertion 2: linear terms vanish). Choices:
- Complex coordinates `z¹..z^k` for `M` near `q`, centred so that `q` corresponds to `z = 0`; `w : ℂ^k → ℂ^n` the (holomorphic) inclusion in these coordinates, `AnalyticAt ℂ w 0`
  (`ℂ^k = EuclideanSpace ℂ (Fin k)`), with `dw(0)` injective (`M` is a complex submanifold; the tangent space at `q` is the range of `dw(0)`).
- `v ∈ ℂ^n` is orthogonal to `M` at `q` in the REAL sense: `Re ⟨v, dw(0) z⟩ = 0` for all `z ∈ ℂ^k` (Milnor's "normal to `M`", the real inner product being `Re` of the Hermitian one).
- The Hermitian product `Σ_α w_α(z) \bar v_α` is `inner ℂ v (w z)` (Mathlib's inner product is conjugate-linear in the first slot).
- B (what Milnor notes): (1) the linear terms vanish, i.e. `⟨v, dw(0) z⟩ = 0` for all `z` (complex orthogonality, also asserted explicitly) and (2) the Hermitian product expands as a constant plus a homogeneous
  complex quadratic form `Q(z) = Σ b_{hj} z^h z^j` plus higher terms, formalized as `h(z) - h(0) - Q(z) = o(‖z‖²)` at `z = 0` for some coefficient matrix `b`. -/
namespace RoundTrip.V5_5
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

abbrev Rn (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The complex quadratic form `Q(z) = Σ b_{hj} z^h z^j` on `ℂ^k`. -/
noncomputable def Qz {k : ℕ} (b : Matrix (Fin k) (Fin k) ℂ) (z : EuclideanSpace ℂ (Fin k)) : ℂ :=
  ∑ h, ∑ j, b h j * z h * z j

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n k : ℕ) (w : EuclideanSpace ℂ (Fin k) → EuclideanSpace ℂ (Fin n)), AnalyticAt ℂ w 0 →
    Function.Injective (fderiv ℂ w 0) →
    ∀ v : EuclideanSpace ℂ (Fin n), (∀ z, (inner ℂ v (fderiv ℂ w 0 z)).re = 0) →
      (∀ z, inner ℂ v (fderiv ℂ w 0 z) = 0) ∧
      ∃ b : Matrix (Fin k) (Fin k) ℂ,
        Asymptotics.IsLittleO (nhds 0)
          (fun z => inner ℂ v (w z) - inner ℂ v (w 0) - Qz b z) (fun z => ‖z‖ ^ 2)
end RoundTrip.V5_5
