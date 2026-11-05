import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_21
import RoundTrip.Bridge

open Set Filter Topology Function
open scoped ContDiff Manifold unitInterval

namespace RoundTrip.V10_21

/-- The project's statement (universes instantiated at `0`), on a slice submanifold `N ⊆ V`
(any model `Z`):
* `BrokenSetup.isRelCellComplexType_Omega`: given Milnor's §16 data `B : BrokenSetup hN p q c m`
  (a subdivision fine for `Ω^c`), `a ≤ b < c`, no geodesic `p → q` of energy `a` or `b`, and all
  geodesics of energy `≤ b` nondegenerate (`hessNullity = 0`): there is a duplicate-free list `ys`
  of the geodesics (as broken-geodesic nodes) with energy in `(a, b)`, sorted by energy, and the
  inclusion `Ω^a → Ω^b` is of relative cell-complex type (`IsRelCellComplexType`: `Ω^b ≃ K` with
  `K` obtained from `Ω^a` by attaching one cell of dimension `geodIndex y` per `y ∈ ys`, in this
  order, with `e ∘ ι ≃ j` up to homotopy);
* `BrokenSetup.finite_geodesics`: finitely many geodesics of energy `≤ b < c`;
* `finite_geodesicEnergies`: for `N` CLOSED in `V`, finitely many geodesic energies `≤ b`;
* `geodesicIndex_eq`: `geodesicIndex` is the index of the energy Hessian.
`PathSp.energyC` and `geodesicIndex` are vocabulary. -/
def A : Prop :=
  type_of% @Morse.BrokenSetup.isRelCellComplexType_Omega.{0,0,0} ∧
    type_of% @Morse.BrokenSetup.finite_geodesics.{0,0,0} ∧
    type_of% @Morse.finite_geodesicEnergies.{0,0,0} ∧
    type_of% @Morse.geodesicIndex_eq.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.BrokenSetup.isRelCellComplexType_Omega, @Morse.BrokenSetup.finite_geodesics,
    @Morse.finite_geodesicEnergies, @Morse.geodesicIndex_eq⟩

/-! Neither `A → B` nor `B → A` is proved; see `V10_21.json`. -/

/-- B on embedded manifolds: `M = ↥N` with the induced connection `Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
    ∀ (p q : Bridge.Sub hN), NonConjPQ n (Bridge.conn (hN := hN)) p q → ∀ a b : ℝ, a < b →
      ¬ IsCritVal n (Bridge.conn (hN := hN)) p q a → ¬ IsCritVal n (Bridge.conn (hN := hN)) p q b →
      ∃ (Y : Type) (_ : TopologicalSpace Y) (D : Set Y) (hD : RelCWComplex (Set.univ : Set Y) D)
        (φ : C(OmLe n p q a, Y)) (f : C(OmLe n p q b, Y)),
        IsHEOnto φ D ∧ IsHEOnto f Set.univ ∧
        (∀ (w : Om n p q) (h : w ∈ OmLe n p q a) (h' : w ∈ OmLe n p q b), f ⟨w, h'⟩ = φ ⟨w, h⟩) ∧
        ∀ l, Nonempty (@RelCWComplex.cell Y _ Set.univ D hD l ≃
          GeodIdx n (Bridge.conn (hN := hN)) p q l (Set.Ioo a b))

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V10_21
