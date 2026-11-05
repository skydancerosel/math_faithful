import Morse
/-! Blind formalization of V2_7 (Milnor §3, proof of Thm 3.2: `e^λ ∩ M^{c-ε} = ė^λ`). Choices:
- Setting as in V2_6 (manifold on `EuclideanSpace ℝ (Fin n)`, non-degenerate critical point `p`, index `λ`, `c = f p`, a Morse chart
  `y` with `y p = 0` and `f = c - ξ + η` on its patch, `M^a` = `{f ≤ a}`).
- `e^λ` = `eCell y λ ε` = points of the patch with `y_i = 0` for `i ≥ λ` and `ξ ≤ ε`; `ė^λ` = those with `ξ = ε`.
- Claim: for `ε` small (∃ ε₀, all `0<ε<ε₀`): `e^λ ∩ M^{c-ε} = ė^λ`; and `e^λ` is a closed λ-cell with boundary `ė^λ`
  (a homeomorphism `e^λ ≃ₜ` unit ball of ℝ^λ carrying `ė^λ` exactly onto the unit sphere), i.e. a cell attached along its boundary.
- NOT formalized: that the subspace `M^{c-ε} ∪ e^λ` is the adjunction space of §1 (Milnor does not argue it). -/
open scoped ContDiff Manifold
namespace RoundTrip.V2_7

abbrev Cell (k : ℕ) : Type := Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1

/-- `ξ = Σ_{i<λ} y_i²` along a coordinate system `y`. -/
noncomputable def xi {n : ℕ} (l : ℕ) (u : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ i : Fin n with i.val < l, (u i) ^ 2
/-- `η = Σ_{i≥λ} y_i²`. -/
noncomputable def eta {n : ℕ} (l : ℕ) (u : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ i : Fin n with l ≤ i.val, (u i) ^ 2

/-- Milnor's cell `e^λ = {ξ ≤ ε, other coordinates 0}` inside the coordinate patch of `y`. -/
def eCell {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (y : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M (EuclideanSpace ℝ (Fin n)) ∞)
    (l : ℕ) (ε : ℝ) : Set M :=
  {q | q ∈ y.source ∧ (∀ i : Fin n, l ≤ i.val → y q i = 0) ∧ xi l (y q) ≤ ε}

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] (f : M → ℝ) (p : M),
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f →
    Morse.IsNondegenerateCriticalPointM (EuclideanSpace ℝ (Fin n)) f p →
    ∀ y : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
          (EuclideanSpace ℝ (Fin n)) ∞,
      p ∈ y.source → y p = 0 →
      (∀ q ∈ y.source, f q = f p - xi (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y q)
          + eta (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y q)) →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (eCell y (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) ε ∩ {x | f x ≤ f p - ε} =
          {q | q ∈ eCell y (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) ε ∧
            xi (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y q) = ε}) ∧
        ∃ h : (eCell y (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) ε) ≃ₜ
            Cell (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p),
          ∀ q, ‖(h q).1‖ = 1 ↔ xi (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y q.1) = ε

end RoundTrip.V2_7
