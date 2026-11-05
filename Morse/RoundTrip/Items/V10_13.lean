import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_13
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold

namespace RoundTrip.V10_13

/-- The project's statement (universes instantiated at `0`), for `B : Morse.BrokenSetup hN p q c m`
on a slice submanifold `N ⊆ V` with the induced metric and `a < c`:
* `theorem_16_3_Omega` (Theorem 16.3): if NO unbroken geodesic of `Ω(N; p, q)` has energy exactly
  `a` and every geodesic with `E ≤ a` has `hessNullity = 0`, then listing the break points `ys` of
  the geodesics with `E ≤ a` (sorted by energy, each with `geodIndex = formIndex energyHessian`),
  `Ω^a = {γ : PathSp N p q // E(γ) ≤ a}` (project pseudo-emetric) has
  `Morse.IsFiniteCellComplexType` with cells `geodIndex ys` (iterated adjunction space);
* `theorem_16_3_Omega_count`: the same with finitely many such geodesics and cell counts
  `count k cells = #{geodesics of index k with E ≤ a}`. -/
def A : Prop :=
  type_of% @Morse.BrokenSetup.theorem_16_3_Omega.{0, 0, 0} ∧
    type_of% @Morse.BrokenSetup.theorem_16_3_Omega_count.{0, 0, 0}

theorem A_holds : A :=
  ⟨@Morse.BrokenSetup.theorem_16_3_Omega, @Morse.BrokenSetup.theorem_16_3_Omega_count⟩

/-! Neither `A → B` nor `B → A` is proved; see `V10_13.json`. Beyond the setting (abstract complete
Riemannian manifolds vs slice submanifolds with the induced metric):

* Cell complexes: B asks for a homotopy equivalence with a finite Mathlib `CWComplex`, A gives
  `Morse.IsFiniteCellComplexType` (iterated adjunction spaces along arbitrary maps, in order of
  energy) — not interconvertible without cellular approximation (the V2_12 obstacle).
* Hypotheses: A assumes `a` is NOT a critical value of `E` (no geodesic of energy exactly `a`); B
  (as Milnor) does not — A is narrower here. B's non-conjugacy along geodesics of length `≤ √a`
  vs A's `hessNullity = 0` for geodesics with `E ≤ a`: equivalent via `E = L²` and the project's
  Theorem 14.1/15.1 (nullity = multiplicity of `q` as conjugate point), glue only.
* Index: B's `lam 1 g` is the index of the choice function `HessT` of Milnor's VARIATIONAL
  `E_**`, A's `geodIndex = formIndex energyHessian` (formula-defined). `RoundTrip/EnergyC2.lean`
  removes the analytic obstacle; the identification still needs the 2-parameter variation and
  `TΩ` dictionaries on `↥N` (see V10_10/V10_11).
* Spaces: B's `Ω^a` is the blind `OmLe` (paths `ℝ → M`, topology of Milnor's `d`), A's is a
  subtype of the project's `PathSp N p q`; on `↥N` the metrics agree (Items/V10_1.lean
  `Emb.edist_eq`), so the two are homotopy equivalent (lift/inclusion at distance `0`), glue only.
  B counts geodesics as elements of `Ω*`, A as break-point tuples (bijective by Lemma 16.1).
* B's "finitely many geodesics in `Ω^a`" corresponds to A's finiteness clause (count version).

## The embedded special case (stated, not proved) -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), induced connection. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
    ∀ (p q : Bridge.Sub hN) (a : ℝ),
      (∀ γ, IsGeodPQ n (Bridge.conn (hN := hN)) p q γ → arcLen (n := n) γ 0 1 ≤ Real.sqrt a →
        ¬ IsConj (Bridge.conn (hN := hN)) γ 0 1) →
      Set.Finite {γ : OmStar p q | ∃ g, IsGeodRep n (Bridge.conn (hN := hN)) γ g ∧
        Efun (n := n) g ≤ a} ∧
      ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : CWComplex (Set.univ : Set Y)),
        Finite (Σ l : ℕ, Topology.CWComplex.cell (Set.univ : Set Y) l) ∧
        Nonempty (ContinuousMap.HomotopyEquiv (OmLe n p q a) Y) ∧
        ∀ l : ℕ, Nonempty (Topology.CWComplex.cell (Set.univ : Set Y) l ≃
          GeodIdx n (Bridge.conn (hN := hN)) p q l (Set.Iic a))

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V10_13
