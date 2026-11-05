import Morse
/-! Blind formalization of V2_10 (Milnor Remark 3.4: the critical level). Choices:
- Setting and hypotheses as in Theorem 3.2 / V2_6 (manifold on `EuclideanSpace ℝ (Fin n)`, `p` non-degenerate of index `λ`,
  `c = f p`, `f⁻¹[c-ε₁,c+ε₁]` compact with `p` the only critical point there). `M^a = {f ≤ a}` subtypes.
- Claims for all small `ε` (∃ ε₀): (1) `M^c` is a deformation retract of `M^{c+ε}`; (2) for a Morse chart `y` (Lemma 2.2),
  `M^{c-ε} ∪ e^λ` is a deformation retract of `M^c` (`e^λ` = `eCell y λ ε`). Milnor derives (2) "together with 3.2";
  stated here as the claim he says one sees easily. `DefRetract` as in V2_1.
- The auxiliary `F⁻¹(-∞,c]` and Diagram 8 are not formalized; "small change in the proof" is not expressed. -/
open scoped ContDiff Manifold unitInterval
namespace RoundTrip.V2_10

/-- `A` is a deformation retract of `X`: a continuous family `r t : X → X`, `r 0 = id`, `r 1` maps into `A`,
and each `r t` fixes `A` pointwise (as in Milnor's `r_t`). -/
def DefRetract {X : Type} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ r : unitInterval → X → X, Continuous (fun z : unitInterval × X => r z.1 z.2) ∧
    (∀ x, r 0 x = x) ∧ (∀ x, r 1 x ∈ A) ∧ ∀ a ∈ A, ∀ t, r t a = a

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
    (∃ ε₁ : ℝ, 0 < ε₁ ∧ IsCompact (f ⁻¹' Set.Icc (f p - ε₁) (f p + ε₁)) ∧
      ∀ x, f x ∈ Set.Icc (f p - ε₁) (f p + ε₁) → Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) f x → x = p) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      DefRetract {x : {x : M | f x ≤ f p + ε} | f x.1 ≤ f p} ∧
      ∃ y : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
          (EuclideanSpace ℝ (Fin n)) ∞,
        p ∈ y.source ∧ y p = 0 ∧
        (∀ q ∈ y.source, f q = f p - xi (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y q)
          + eta (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y q)) ∧
        DefRetract {x : {x : M | f x ≤ f p} |
          f x.1 ≤ f p - ε ∨ x.1 ∈ eCell y (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) ε}

end RoundTrip.V2_10
