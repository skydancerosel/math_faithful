import Morse
/-! Blind formalization of V3_31 (Milnor §5, p. 29: H_*(Y ∪ e^λ, Y) = H_*(e^λ, ė^λ) by excision). Choices:
- Cell attachment is hand-built (as in other blind files): `Y ∪_g e^k` = quotient of `Y ⊕ closedBall(0,1) ⊆ ℝ^k` by `x ∼ g x` on the sphere, `g : S^{k-1} → Y` any continuous map
  (Milnor: `Y` closed in a Hausdorff space; the statement holds for any `Y`, so the hypothesis is dropped). `inr_maps` is a trivial well-definedness lemma for the map of pairs.
- B: (i) the map `H_n(e^k, ė^k) → H_n(Y ∪ e^k, Y)` induced by the characteristic map is an isomorphism for all `n` (the "by excision" identification),
  (ii) `H_n(e^k, ė^k; F)` is finite-dimensional of dimension 1 (coefficient group `F`) for `n = k` and `0` otherwise. `F` an arbitrary field. -/
namespace RoundTrip.V3_31
open CategoryTheory Morse.Homology
open scoped ContDiff Manifold unitInterval

/-- The closed unit ball `e^k` in ℝ^k. -/
abbrev Cell (k : ℕ) : Type := Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1
/-- Its boundary sphere `ė^k = S^{k-1}`. -/
abbrev Bdry (k : ℕ) : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin k)) 1
/-- The inclusion of the boundary sphere into the cell. -/
def bdryToCell {k : ℕ} (x : Bdry k) : Cell k := ⟨x.1, Metric.sphere_subset_closedBall x.2⟩

section
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

/-- The characteristic map sends `ė^k` into `Y` (well-definedness of the map of pairs). -/
theorem inr_maps {k : ℕ} (g : C(Bdry k, Y)) :
    Set.MapsTo (inr g) (Set.range (bdryToCell (k := k))) (Set.range (inl g)) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨g x, (Quot.sound ⟨x, rfl, rfl⟩).symm⟩
end

/-- `H_n(X, Y; F)`. -/
noncomputable def Hom (F : Type) [Field F] {E : Type} [TopologicalSpace E] {A B : Set E} (h : A ⊆ B) (n : ℕ) :
    ModuleCat F := (relHomology (ModuleCat.of F F) n).obj (subsetPair h)

/-- Milnor's claim. -/
def B : Prop :=
  ∀ (F : Type) [Field F] (Y : Type) [TopologicalSpace Y] (k : ℕ) (g : C(Bdry k, Y)),
    (∀ n, IsIso ((relHomology (ModuleCat.of F F) n).map
      (subsetPairMap (inr g) (Set.subset_univ (Set.range (bdryToCell (k := k))))
        (Set.subset_univ (Set.range (inl g))) (inr_maps g) (Set.mapsTo_univ _ _)))) ∧
    (∀ n, Module.Finite F (Hom F (Set.subset_univ (Set.range (bdryToCell (k := k)))) n) ∧
      Module.finrank F (Hom F (Set.subset_univ (Set.range (bdryToCell (k := k)))) n) = if n = k then 1 else 0)
end RoundTrip.V3_31
