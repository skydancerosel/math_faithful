import Morse
/-! Blind formalization of V2_8 (Milnor Thm 3.2 and Assertion 3 of its proof). Choices:
- Setting as in V2_6 (abstract smooth Hausdorff manifold modelled on `EuclideanSpace ℝ (Fin n)`; a submanifold of ℝᵐ is
  a special case). `M^a = {f ≤ a}`.
- B₁ = Theorem 3.2: for small ε, `M^{c+ε} ≃ₕ M^{c-ε} ∪_g e^λ` for some attaching map `g` (hypothesis: `f⁻¹[c-ε₁,c+ε₁]`
  compact, only critical point `p`, non-degenerate).
- B₂ = Assertion 3: given a Morse chart `y` (`y p = 0`, `f = c - ξ + η` on patch `U = y.source`), `ε > 0` with
  `f⁻¹[c-ε,c+ε]` compact with only critical point `p`, the closed ball `ξ+η ≤ 2ε` of ℝⁿ inside `y.target`, and
  `μ : ℝ → ℝ` smooth with `μ 0 > ε`, `μ r = 0` for `r ≥ 2ε`, `-1 < μ' ≤ 0`, the function `F = f - μ(ξ + 2η)` on `U`,
  `F = f` off `U`, has `F⁻¹(-∞, c-ε]` as a deformation retract of `M^{c+ε}` (my `DefRetract`; Milnor derives it from Thm 3.1).
  The set `F⁻¹(-∞,c-ε]` is taken inside `M^{c+ε}` (as a subset of the subtype).
- The 'rest of the argument in the patch' is not separately stated. -/
open scoped ContDiff Manifold unitInterval
open Classical
namespace RoundTrip.V2_8

/-- The closed unit ball `e^k` in ℝ^k. -/
abbrev Cell (k : ℕ) : Type := Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1
/-- Its boundary sphere `ė^k = S^{k-1}`. -/
abbrev Bdry (k : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1
/-- The inclusion of the boundary sphere into the cell. -/
def bdryToCell {k : ℕ} (x : Bdry k) : Cell k := ⟨x.1, Metric.sphere_subset_closedBall x.2⟩

variable {Y : Type} [TopologicalSpace Y]

/-- Identification relation on the topological sum: `x ∈ S^{k-1}` is glued to `g x`. -/
def Rel {k : ℕ} (g : C(Bdry k, Y)) : (Y ⊕ Cell k) → (Y ⊕ Cell k) → Prop :=
  fun a b => ∃ x : Bdry k, a = Sum.inr (bdryToCell x) ∧ b = Sum.inl (g x)

/-- `Y ∪_g e^k`: quotient of the topological sum `Y ⊕ e^k` by the identifications. -/
def Attach {k : ℕ} (g : C(Bdry k, Y)) : Type := Quot (Rel g)

instance {k : ℕ} (g : C(Bdry k, Y)) : TopologicalSpace (Attach g) :=
  inferInstanceAs (TopologicalSpace (Quot (Rel g)))

/-- Inclusion of `Y`. -/
def inl {k : ℕ} (g : C(Bdry k, Y)) : C(Y, Attach g) :=
  ⟨fun y => Quot.mk _ (Sum.inl y), continuous_quot_mk.comp continuous_inl⟩

/-- Characteristic map of the cell. -/
def inr {k : ℕ} (g : C(Bdry k, Y)) : C(Cell k, Attach g) :=
  ⟨fun c => Quot.mk _ (Sum.inr c), continuous_quot_mk.comp continuous_inr⟩

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
    ((∃ ε₁ : ℝ, 0 < ε₁ ∧ IsCompact (f ⁻¹' Set.Icc (f p - ε₁) (f p + ε₁)) ∧
      ∀ x, f x ∈ Set.Icc (f p - ε₁) (f p + ε₁) → Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) f x → x = p) →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ g : C(Bdry (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p), {x : M | f x ≤ f p - ε}),
          Nonempty (ContinuousMap.HomotopyEquiv {x : M | f x ≤ f p + ε} (Attach g))) ∧
    (∀ y : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
          (EuclideanSpace ℝ (Fin n)) ∞,
      p ∈ y.source → y p = 0 →
      (∀ q ∈ y.source, f q = f p - xi (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y q)
          + eta (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y q)) →
      ∀ ε : ℝ, 0 < ε → IsCompact (f ⁻¹' Set.Icc (f p - ε) (f p + ε)) →
      (∀ x, f x ∈ Set.Icc (f p - ε) (f p + ε) → Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) f x → x = p) →
      (∀ u : EuclideanSpace ℝ (Fin n),
        xi (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) u + eta (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) u ≤ 2 * ε →
          u ∈ y.target) →
      ∀ μ : ℝ → ℝ, ContDiff ℝ ∞ μ → ε < μ 0 → (∀ r, 2 * ε ≤ r → μ r = 0) →
        (∀ r, -1 < deriv μ r ∧ deriv μ r ≤ 0) →
        DefRetract {x : {x : M | f x ≤ f p + ε} |
          (if x.1 ∈ y.source then f x.1 - μ (xi (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y x.1)
              + 2 * eta (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y x.1)) else f x.1) ≤ f p - ε})

end RoundTrip.V2_8
