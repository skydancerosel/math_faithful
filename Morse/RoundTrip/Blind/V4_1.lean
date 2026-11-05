import Morse
/-! Blind formalization of V4_1 (Milnor §6, p. 32: normal bundle and endpoint map). Choices:
- Setting (project's definitions, Mathlib lacks embedded submanifolds / tangent spaces of subsets): `M ⊆ ℝⁿ`, `n = K+1`, a smooth embedded submanifold of dimension `k = d+1 < n`
  (`Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝⁿ) ℝᵏ ℝᵐ M`, `d < K` required where used; dimension ≥ 1), tangent space `Milnor.Tub.tanN`.
- `N = NSet` = `{(q,v) ∈ ℝⁿ × ℝⁿ | q ∈ M, v ⊥ T_qM}` inside `ℝ²ⁿ = ℝⁿ × ℝⁿ`; endpoint map `E(q,v) = q + v` (`endpt`).
  The manifold structure of `N` is that of a slice submanifold `hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝ²ⁿ) ℝⁿ ℝⁿ N` (`hNN.chartedSpace`).
- Jacobian of `E` at `(q,v)` = `mfderiv` of `E|N` in that structure; nullity = `finrank` of its kernel (`nullE`, defined as `0` off `N`).
- B (for every `M` with `d < K`): `N` is an `n`-dimensional smooth submanifold of `ℝ²ⁿ` (exists `hNN` slice-submanifold structure modelled on `ℝⁿ`), and `E : N → ℝⁿ` is smooth for it.
  NOT expressed: that `N` is the total space of a vector bundle (the vector-bundle structure) -- only the manifold claim. -/
namespace RoundTrip.V4_1
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

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (K d m : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M), d < K →
    ∃ hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1)) (NSet hM),
      letI := hNN.chartedSpace
      ContMDiff 𝓘(ℝ, Rn (K + 1)) 𝓘(ℝ, Rn (K + 1)) ∞ (fun x : NSet hM => endpt x.1)
end RoundTrip.V4_1
