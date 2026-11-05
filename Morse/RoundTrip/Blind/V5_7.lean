import Morse
/-! Blind formalization of V5_7 (Milnor §7, Assertion 2). Choices:
- Setting (project's definitions, Mathlib lacks embedded submanifolds / tangent spaces of subsets): `M ⊆ ℝⁿ`, `n = K+1`, a smooth embedded submanifold of dimension `d+1`
  (`Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝⁿ) ℝᵏ ℝᵐ M`), tangent space `Milnor.Tub.tanN`. Its charted-space structure is `hM.chartedSpace`.
- `N = NSet` = `{(q,v) ∈ ℝⁿ × ℝⁿ | q ∈ M, v ⊥ T_qM}` inside `ℝ²ⁿ = ℝⁿ × ℝⁿ`; endpoint map `E(q,v) = q + v` (`endpt`). The manifold structure of `N` is a slice-submanifold
  structure `hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝ²ⁿ) ℝⁿ ℝⁿ N` (quantified as an argument).
- Jacobian of `E` at `(q,v)` = `mfderiv` of `E|N` in that structure; nullity = `finrank` of its kernel (`nullE`, `0` off `N`); `IsFocalOfMult hNN q e μ`: focal point of `(M,q)` of multiplicity `μ`.
- Complex setting: `ℂⁿ` is realified to `ℝ^{K+1} = ℝ^{2n}` (so `K+1` is even, which is forced by the existence of `J`); the complex structure (multiplication by `i`) is a linear isometry
  `J : ℝ^{K+1} ≃ₗᵢ ℝ^{K+1}` with `J² = -1`. A complex submanifold `M` of `ℂⁿ` is a smooth embedded real submanifold of `ℝ^{K+1}` (project's `Milnor.IsSliceSubmanifold`, tangent spaces `Milnor.Tub.tanN`)
  whose tangent spaces are `J`-invariant (`J (T_qM) ⊆ T_qM`). (The holomorphic-chart description is equivalent by the standard integrability fact for submanifolds of `ℂⁿ`; it is not formalized separately.)
  Real dimension `d+1 = 2k`, complex dimension `k`.
- B: for every point `q ∈ M` and every normal vector `v` at `q` (`(q,v) ∈ N`; the line `q + tv`), and every `t` and multiplicity `μ`: `q + t v` is a focal point of `(M,q)` of multiplicity `μ`
  iff `q - t v` is (the "pairs placed symmetrically about `q`", with equal multiplicities). The proof via `Q'` is not part of B. -/
namespace RoundTrip.V5_7
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
  ∀ (K d m : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1)) (NSet hM))
    (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)), IsCplxStr J → IsCplxSub hM J →
    ∀ (q : M) (v : Rn (K + 1)), (q.1, v) ∈ NSet hM → ∀ (t : ℝ) (μ : ℕ),
      IsFocalOfMult hNN q.1 (q.1 + t • v) μ ↔ IsFocalOfMult hNN q.1 (q.1 - t • v) μ
end RoundTrip.V5_7
