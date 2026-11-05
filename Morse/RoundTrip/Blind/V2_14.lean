import Morse
/-! Blind formalization of V2_14 (Milnor Lemma 3.7 and the Assertion of p. 22). Choices:
- Attaching spaces as in V1_2 (own quotient def).
- Lemma: for f : X ≃ₕ Y, ∃ homotopy equivalence F : X∪_φ e^λ → Y∪_{f∘φ} e^λ with F = f on X and F = identity on
  the cell (F ∘ inl = inl ∘ f, F ∘ inr = inr).
- Assertion: F : C(A,B), L R : C(B,A) with L∘F ≃ id_A and F∘R ≃ id_B ⇒ F is (the underlying map of) a homotopy
  equivalence, and R∘F ≃ id_A and F∘L ≃ id_B (R and L are two-sided homotopy inverses). B is the conjunction. -/
open Topology

namespace RoundTrip.V2_14

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

def B₁ : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (lam : ℕ) (φ : C(Bdry lam, X))
    (f : ContinuousMap.HomotopyEquiv X Y),
    ∃ F : ContinuousMap.HomotopyEquiv (Attach φ) (Attach (f.toFun.comp φ)),
      (∀ x : X, F (inl φ x) = inl (f.toFun.comp φ) (f x)) ∧
      (∀ c : Cell lam, F (inr φ c) = inr (f.toFun.comp φ) c)

def B₂ : Prop :=
  ∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B] (F : C(A, B)) (L R : C(B, A)),
    (L.comp F).Homotopic (ContinuousMap.id A) → (F.comp R).Homotopic (ContinuousMap.id B) →
      (∃ H : ContinuousMap.HomotopyEquiv A B, ∀ a, H a = F a) ∧
      (R.comp F).Homotopic (ContinuousMap.id A) ∧ (F.comp L).Homotopic (ContinuousMap.id B)

/-- Milnor's claim. -/
def B : Prop := B₁ ∧ B₂

end RoundTrip.V2_14
