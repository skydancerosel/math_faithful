import Morse
/-! Blind formalization of V4_23 (Milnor §6, Lemma 6.9). Choices:
- Setting (project's definitions, Mathlib lacks embedded submanifolds / tangent spaces of subsets): `M ⊆ ℝⁿ`, `n = K+1`, a smooth embedded submanifold of dimension `k = d+1`
  (`Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝⁿ) ℝᵏ ℝᵐ M`), tangent space `Milnor.Tub.tanN`. Its charted-space structure is `hM.chartedSpace`.
- `N = NSet` = `{(q,v) ∈ ℝⁿ × ℝⁿ | q ∈ M, v ⊥ T_qM}` inside `ℝ²ⁿ = ℝⁿ × ℝⁿ`; endpoint map `E(q,v) = q + v` (`endpt`). The manifold structure of `N` is a slice-submanifold
  structure `hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ,ℝ²ⁿ) ℝⁿ ℝⁿ N` (quantified as an argument).
- Jacobian of `E` at `(q,v)` = `mfderiv` of `E|N` in that structure; nullity = `finrank` of its kernel (`nullE`, `0` off `N`); `IsFocalOfMult hNN q e μ`: focal point of `(M,q)` of multiplicity `μ`.
- `L_p(y) = ‖y - p‖²` restricted to `M`; critical point / non-degenerate / index: project's `Morse.IsCriticalPointM`, `Morse.IsNondegenerateCriticalPointM`, `Morse.indexM`.
- "Number of focal points of `(M,q)` on the segment from `q` to `p`, counted with multiplicity": the points of the segment are `q + s (p - q)`, `s ∈ [0,1]`; the count is the
  `finsum` over `s ∈ [0,1]` of the nullity `nullE hNN (q, s (p - q))` of the Jacobian of `E` there (the multiplicity, `0` when not focal), and the set of `s` with positive multiplicity is asserted finite.
  (Distinct `s` give distinct points when `p ≠ q`; when `p = q` all multiplicities are `0`.) The proof via eigenvalues is not part of B. -/
namespace RoundTrip.V4_23
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

/-- `L_p(y) = ‖y - p‖²`. -/
noncomputable def Lp {n : ℕ} (p : Rn n) (y : Rn n) : ℝ := ‖y - p‖ ^ 2

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (K d m : ℕ) (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1)) (NSet hM))
    (q : M) (p : Rn (K + 1)),
    letI := hM.chartedSpace
    Morse.IsCriticalPointM (Rn (d + 1)) (fun y : M => Lp p y.1) q →
    Morse.IsNondegenerateCriticalPointM (Rn (d + 1)) (fun y : M => Lp p y.1) q →
    {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < nullE hNN (q.1, s • (p - q.1))}.Finite ∧
    Morse.indexM (Rn (d + 1)) (fun y : M => Lp p y.1) q =
      ∑ᶠ s ∈ Set.Icc (0 : ℝ) 1, nullE hNN (q.1, s • (p - q.1))
end RoundTrip.V4_23
