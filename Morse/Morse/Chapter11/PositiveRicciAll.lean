import Morse.Chapter11.RicciHomology
import Morse.Chapter10.CWType

/-!
Milnor, *Morse Theory*, §19, Theorem 19.6 (p. 106), for all end points; Exposition/Chapter11.md,
§5, "Arbitrary `p, q`".

# Theorem 19.6 for arbitrary end points

## Milnor's text, paraphrased

(p. 106) **Theorem 19.6**: if `M` is compact with positive definite Ricci tensor, then **for all
`p, q`** the path space `Ω(M; p, q)` has the homotopy type of a CW-complex with only finitely many
cells in each dimension.  The proof given treats only `p, q` not conjugate along any geodesic.

## What is formalized

* `Morse.theorem_19_6_all`: **Theorem 19.6 for all `p, q ∈ N`** (`N` compact, of dimension
  `≥ 2`, positive definite Ricci tensor): `Ω(N; p, q)` has the homotopy type of a countable cell
  complex with only finitely many cells in each dimension.
* `Morse.finiteDimensional_spaceHomology_omega_all`: its homology over any field is
  finite-dimensional in each degree, for all `p, q`.

## What Milnor leaves implicit

* **Moving the end point** (the exposition's completion of the proof): `q` is joined in `N` to a
  point `q'` not conjugate to `p` along any geodesic (Corollary 18.2,
  `Morse.exists_joined_notMem_conjLocus`), and `Ω(N; p, q) ≃ Ω(N; p, q')` by Lemma 17.D and
  Theorem 17.1 (`Morse.pathSpHomotopyEquiv`); the conclusion of `Morse.theorem_19_6` is invariant
  under homotopy equivalence (`Morse.IsCountableCellComplexType.of_homotopyEquiv`,
  `Morse.Homology.spaceHomologyEquivOfHomotopyEquiv`).  No connectedness of `N` is needed: `q'`
  is chosen in a small Riemannian ball around `q`.
-/

open Set Filter Topology Function Module
open scoped Manifold

noncomputable section

namespace Morse

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N}

/-- **Theorem 19.6** (Milnor p. 106), **for all end points**: if `N` is compact, of dimension
`≥ 2`, with positive definite Ricci tensor, then for all `p, q ∈ N`, `Ω(N; p, q)` has the
homotopy type of a countable cell complex with only finitely many cells in each dimension. -/
theorem theorem_19_6_all (hNc : IsCompact N) (hn : 2 ≤ finrank ℝ Z)
    (hpos : ∀ q : N, ∀ U : tangentSubspace hN q, U ≠ 0 → 0 < ricci hN q U U) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) :
    ∃ cells : ℕ → List ℕ, IsCountableCellComplexType (PathSp N p q) cells ∧
      ∀ d : ℕ, {n | d ∈ cells n}.Finite := by
  obtain ⟨q', hq', hnc, ⟨σ⟩⟩ := exists_joined_notMem_conjLocus hN hp hq
  obtain ⟨cells, h, hfin⟩ := theorem_19_6 hNc hn hpos hp hq' hnc
  exact ⟨cells, h.of_homotopyEquiv (pathSpHomotopyEquiv hN hp hq hq' σ), hfin⟩

/-- **The homology of `Ω(N; p, q)` is finite-dimensional in each degree, for all `p, q`**, under
the hypotheses of Theorem 19.6. -/
theorem finiteDimensional_spaceHomology_omega_all {𝕜 : Type u} [Field 𝕜] (hNc : IsCompact N)
    (hn : 2 ≤ finrank ℝ Z)
    (hpos : ∀ q : N, ∀ U : tangentSubspace hN q, U ≠ 0 → 0 < ricci hN q U U) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (i : ℕ) :
    FiniteDimensional 𝕜 (Homology.spaceHomology 𝕜 i (PathSp N p q)) := by
  obtain ⟨q', hq', hnc, ⟨σ⟩⟩ := exists_joined_notMem_conjLocus hN hp hq
  have := finiteDimensional_spaceHomology_omega_of_compact (𝕜 := 𝕜) hNc hn hpos hp hq' hnc i
  exact (Homology.spaceHomologyEquivOfHomotopyEquiv 𝕜
    (pathSpHomotopyEquiv hN hp hq hq' σ) i).symm.finiteDimensional

end Morse
