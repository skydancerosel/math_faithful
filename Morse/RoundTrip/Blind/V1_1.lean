import Morse
/-! Blind formalization of V1_1 (Milnor §1, the torus example). Choices:
- Concrete model: torus `T = S¹ × S¹` (`Circle × Circle`, smooth manifold modelled on `EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)`),
  standing on a plane tangent to it ("upright", as in Diagram 1). For radii `0 < r < R` the height above the plane is
  `f (w,z) = (R + r) + (R + r·Re w)·Re z` (torus of core radius `R` and tube radius `r` in ℝ³ with horizontal axis, resting on the plane).
- Claims formalized: (1) `f` has exactly four critical points `p,q,r',s` with values `0, 2r, 2R, 2R+2r`, all non-degenerate
  (project `Morse.IsCriticalPointM`, `IsNondegenerateCriticalPointM`), of indices `0,1,1,2` (project `Morse.indexM`; this encodes the
  normal forms `x²+y²`, `c+x²-y²`, `c-x²-y²`, whose number of minus signs is the cell dimension);
  (2) stages: `M^a = ∅` for `a < f p`; `M^a ≃ₜ` closed disc for `f p < a < f q`; `M^a ≃ₜ` cylinder `S¹ × [0,1]` for `f q < a < f r'`;
  `M^a = M` for `a ≥ f s` ; (3) up to homotopy type, passing each critical value attaches a cell of dimension = index
  (for small ε, `M^{c+ε} ≃ₕ M^{c-ε} ∪_g e^λ`, some attaching map `g`, own `Attach` quotient construction).
- NOT expressed: the third stage "compact genus-one surface bounded by a circle" (no canonical formulation); the diagrams;
  the explicit local coordinates (replaced by indices); the example is illustrative so the claims are Milnor's informal list.
- The tangent plane is encoded by `min f = 0`. `T` as a concrete example, not an arbitrary torus. -/
open scoped ContDiff Manifold
namespace RoundTrip.V1_1

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


abbrev E1 := EuclideanSpace ℝ (Fin 1)
abbrev T := Circle × Circle

/-- product chart structure on the torus, modelled on `E1 × E1`. -/
noncomputable instance : ChartedSpace (E1 × E1) T := prodChartedSpace E1 Circle E1 Circle

/-- height above the plane. -/
noncomputable def ht (R r : ℝ) (x : T) : ℝ := (R + r) + (R + r * (x.1 : ℂ).re) * (x.2 : ℂ).re

/-- Milnor's claim. -/
def B : Prop :=
  ∀ R r : ℝ, 0 < r → r < R →
    ∃ p q r' s : T,
      {x : T | Morse.IsCriticalPointM (E1 × E1) (ht R r) x} = {p, q, r', s} ∧
      ht R r p = 0 ∧ ht R r q = 2 * r ∧ ht R r r' = 2 * R ∧ ht R r s = 2 * R + 2 * r ∧
      (∀ x, Morse.IsCriticalPointM (E1 × E1) (ht R r) x → Morse.IsNondegenerateCriticalPointM (E1 × E1) (ht R r) x) ∧
      Morse.indexM (E1 × E1) (ht R r) p = 0 ∧ Morse.indexM (E1 × E1) (ht R r) q = 1 ∧
      Morse.indexM (E1 × E1) (ht R r) r' = 1 ∧ Morse.indexM (E1 × E1) (ht R r) s = 2 ∧
      (∀ a, a < 0 → IsEmpty {x : T // ht R r x ≤ a}) ∧
      (∀ a, 0 < a → a < 2 * r →
        Nonempty ({x : T // ht R r x ≤ a} ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)) ∧
      (∀ a, 2 * r < a → a < 2 * R →
        Nonempty ({x : T // ht R r x ≤ a} ≃ₜ (Circle × Set.Icc (0 : ℝ) 1))) ∧
      (∀ a, 2 * R + 2 * r ≤ a → ∀ x : T, ht R r x ≤ a) ∧
      (∀ (c : ℝ) (l : ℕ), (c = 0 ∧ l = 0 ∨ c = 2 * r ∧ l = 1 ∨ c = 2 * R ∧ l = 1 ∨ c = 2 * R + 2 * r ∧ l = 2) →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∃ g : C(Bdry l, {x : T // ht R r x ≤ c - ε}),
            Nonempty (ContinuousMap.HomotopyEquiv {x : T // ht R r x ≤ c + ε} (Attach g)))

end RoundTrip.V1_1
