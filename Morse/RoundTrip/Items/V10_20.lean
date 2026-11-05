import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_20
import RoundTrip.Bridge

open Set Filter Topology Function
open scoped ContDiff Manifold unitInterval

namespace RoundTrip.V10_20

/-- The project's statement (universes instantiated at `0`). `IsRelCellComplexType ι cells`
(definition, vocabulary): `X` is homotopy equivalent to a space `K` obtained from `A` by attaching
cells of the listed dimensions one at a time along arbitrary maps (`IsRelCellAttachment`,
iterated pushouts in `TopCat`), by an equivalence `e` with `e ∘ ι ≃ j` (homotopy-commutative).
The theorems:
* `IsRelCellAttachment.transport`: a relative cell attachment along `L` can be transported along
  a homotopy equivalence `L ≃ L'`;
* `IsRelCellComplexType.of_square`: invariance under homotopy-commutative squares of homotopy
  equivalences;
* `isRelCellComplexType_sublevel_of_isCompact`: for a function `F` on a slice submanifold `N`
  (FINITE-dimensional, compact sublevel `F ≤ a₀`, nondegenerate critical points), the inclusion
  `N^b → N^{a₀}` is of relative cell-complex type, one cell per critical point in `(b, a₀)`
  (Theorem 3.5's relative form, "just as in the proof of 3.5");
* `isCountableCellComplexType_of_relSublevel`: a space with a continuous `E` and levels
  `a_n → ∞` such that `E ≤ a₀` is a finite cell complex type and each `E ≤ a_n → E ≤ a_{n+1}` is
  of relative cell-complex type, has the homotopy type of a countable cell complex (a mapping
  telescope of a `CellTower`). -/
def A : Prop :=
  type_of% @Morse.IsRelCellAttachment.transport.{0} ∧
    type_of% @Morse.IsRelCellComplexType.of_square.{0} ∧
    type_of% @Morse.isRelCellComplexType_sublevel_of_isCompact.{0,0,0} ∧
    type_of% @Morse.isCountableCellComplexType_of_relSublevel.{0}

theorem A_holds : A :=
  ⟨@Morse.IsRelCellAttachment.transport, @Morse.IsRelCellComplexType.of_square,
    @Morse.isRelCellComplexType_sublevel_of_isCompact,
    @Morse.isCountableCellComplexType_of_relSublevel⟩

/-! Neither `A → B` nor `B → A` is proved; see `V10_20.json`. A is the abstract assembly
machinery (homotopy-invariance of relative cell attachments, the finite-dimensional relative
Theorem 3.5, tower ⇒ countable complex type up to homotopy) and contains nothing about `Ω`,
geodesics or indices; B is the path-space tower itself (Mathlib CW complexes `K_i ⊆ K_{i+1}`,
cells ↔ geodesics of index `λ` and energy `< a_i`, homotopy equivalences `Ω^{a_i} → K_i`
extending each other STRICTLY). -/

/-- B on embedded manifolds: `M = ↥N` with the induced connection `Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
    ∀ (p q : Bridge.Sub hN), NonConjPQ n (Bridge.conn (hN := hN)) p q →
      ∀ a : ℕ → ℝ, StrictMono a → Filter.Tendsto a Filter.atTop Filter.atTop →
      OmLe n p q (a 0) = ∅ → (∀ i, ¬ IsCritVal n (Bridge.conn (hN := hN)) p q (a i)) →
      (∀ i, ∃! v, a i < v ∧ v < a (i + 1) ∧ IsCritVal n (Bridge.conn (hN := hN)) p q v) →
      ∃ (Y : Type) (_ : TopologicalSpace Y) (K : ℕ → Set Y) (hC : ∀ i, CWComplex (K i))
        (f : ∀ i, C(OmLe n p q (a i), Y)),
        K 0 = ∅ ∧
        (∀ i, ∃ S : @RelCWComplex.Subcomplex Y _ (K (i + 1)) ∅
          (@Topology.CWComplex.instRelCWComplex Y _ (K (i + 1)) (hC (i + 1))), (S : Set Y) = K i) ∧
        (∀ i l, Nonempty (@Topology.CWComplex.cell Y _ (K i) (hC i) l ≃
          GeodIdx n (Bridge.conn (hN := hN)) p q l (Set.Iio (a i)))) ∧
        (∀ i, IsHEOnto (f i) (K i)) ∧
        ∀ i (w : Om n p q) (h : w ∈ OmLe n p q (a i)) (h' : w ∈ OmLe n p q (a (i + 1))),
          f (i + 1) ⟨w, h'⟩ = f i ⟨w, h⟩

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V10_20
