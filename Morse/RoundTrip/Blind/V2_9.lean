import Morse
/-! Blind formalization of V2_9 (Milnor Remark 3.3, several critical points on one level). Choices:
- Setting as in Thm 3.2: smooth Hausdorff finite-dim manifold `M`, `f : M → ℝ` smooth; `M^a = {x | f x ≤ a}` (subtype).
- Hypotheses (of Thm 3.2, extended to k points): ∃ ε₁ > 0 with `f⁻¹[c-ε₁, c+ε₁]` compact, and the critical points of `f`
  in it are exactly the distinct points `p i`, all on level `c`, all non-degenerate (project defs). Index = `Morse.indexM`.
- Conclusion: "for all sufficiently small ε": ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), `M^{c+ε} ≃ₕ` some space obtained from `M^{c-ε}` by
  attaching cells `e^{λ₁}, …, e^{λ_k}` successively (inductive predicate `IsAttached` over `TopCat`; attaching maps
  existentially quantified, arbitrary continuous maps from the sphere to the space built so far; list order = attaching order).
- Cells are the unit ball/sphere in `EuclideanSpace ℝ (Fin λ)`, attachment space is a hand-defined `Quot`. -/
open scoped ContDiff Manifold Topology

namespace RoundTrip.V2_9

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

/-- `IsAttached Y cs Z`: `Z` is obtained from `Y` by attaching cells of dimensions `cs`, in order. -/
inductive IsAttached : TopCat → List ℕ → TopCat → Prop
  | nil (Y : TopCat) : IsAttached Y [] Y
  | step {Y Y' : TopCat} {cs : List ℕ} (k : ℕ) (g : C(Bdry k, Y')) :
      IsAttached Y cs Y' → IsAttached Y (cs ++ [k]) (TopCat.of (Attach g))

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ) (c : ℝ) (k : ℕ) (p : Fin k → M),
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f → Function.Injective p →
    (∀ i, f (p i) = c) → (∀ i, Morse.IsNondegenerateCriticalPointM E f (p i)) →
    (∃ ε₁ : ℝ, 0 < ε₁ ∧ IsCompact (f ⁻¹' Set.Icc (c - ε₁) (c + ε₁)) ∧
      ∀ x, f x ∈ Set.Icc (c - ε₁) (c + ε₁) → Morse.IsCriticalPointM E f x → ∃ i, x = p i) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ W : TopCat, IsAttached (TopCat.of {x : M | f x ≤ c - ε})
          ((List.finRange k).map fun i => Morse.indexM E f (p i)) W ∧
        Nonempty (ContinuousMap.HomotopyEquiv {x : M | f x ≤ c + ε} W)

end RoundTrip.V2_9
