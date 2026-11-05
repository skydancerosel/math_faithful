import Morse
/-! Blind formalization of V2_6 (Milnor Theorem 3.2). Choices:
- Setting: smooth Hausdorff manifold `M` modelled on `EuclideanSpace ℝ (Fin n)`, `f` smooth, `p` a non-degenerate critical
  point (project defs) of index `λ = Morse.indexM`, `c = f p`; hypothesis: some `ε₁ > 0` with `f⁻¹[c-ε₁,c+ε₁]` compact and
  `p` its only critical point. `M^a` = subtype `{x | f x ≤ a}`.
- B₁ (Theorem): ∃ ε₀ > 0 such that for all `0 < ε < ε₀`, `M^{c+ε}` is homotopy equivalent (`ContinuousMap.HomotopyEquiv`) to
  `M^{c-ε} ∪_g e^λ` for some continuous attaching map `g : S^{λ-1} → M^{c-ε}` (the §1 attachment space, own `Attach`; `e^λ` the unit
  ball of ℝ^λ; attaching map existentially quantified).
- B₂ (the proof's Assertions, final conclusion): ∃ a Morse chart `y` (Lemma 2.2: `y p = 0`, `f = c - ξ + η` on its patch)
  and ε₀ > 0 such that for `0 < ε < ε₀`, `M^{c-ε} ∪ e^λ` (with `e^λ = {ξ ≤ ε, y_i = 0 for i ≥ λ}` in the patch) is a deformation
  retract of `M^{c+ε}` (my `DefRetract`). The intermediate function `μ`, `F`, `H` are not formalized (the four assertions are
  steps; only their joint conclusion is stated).
- B = B₁ ∧ B₂. -/
open scoped ContDiff Manifold unitInterval
namespace RoundTrip.V2_6

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
    (∃ ε₁ : ℝ, 0 < ε₁ ∧ IsCompact (f ⁻¹' Set.Icc (f p - ε₁) (f p + ε₁)) ∧
      ∀ x, f x ∈ Set.Icc (f p - ε₁) (f p + ε₁) → Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) f x → x = p) →
    (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ g : C(Bdry (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p), {x : M | f x ≤ f p - ε}),
        Nonempty (ContinuousMap.HomotopyEquiv {x : M | f x ≤ f p + ε} (Attach g))) ∧
    (∃ y : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M
          (EuclideanSpace ℝ (Fin n)) ∞,
      p ∈ y.source ∧ y p = 0 ∧
      (∀ q ∈ y.source, f q = f p - xi (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y q)
          + eta (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) (y q)) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        DefRetract {x : {x : M | f x ≤ f p + ε} |
          f x.1 ≤ f p - ε ∨ x.1 ∈ eCell y (Morse.indexM (EuclideanSpace ℝ (Fin n)) f p) ε})

end RoundTrip.V2_6
