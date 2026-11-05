import Morse.Chapter10.SpherePaths
import Morse.Chapter10.FundamentalTheorem
import Morse.Chapter13.Corollaries

/-!
Milnor, *Morse Theory*, §17, Corollary 17.2 (p. 94) and Corollary 17.4 (p. 96), with Lemma 17.D
of Exposition/Chapter10.md, §5.

# The path space has CW homotopy type; the loop space of `Sⁿ`

## Milnor's text, paraphrased

* (p. 94) **Corollary 17.2**: `Ω` has the homotopy type of a CW-complex.  *Proof*: by Milnor's
  paper (Trans. AMS 90, 1959) `Ω*` has the homotopy type of a CW-complex; apply 17.1.
* (p. 96) **Corollary 17.4**: the loop space of `Sⁿ`, `n ≥ 2`, has the homotopy type of a
  CW-complex with one cell in each dimension `0, n − 1, 2(n − 1), …`.

## What is formalized

* `Morse.joined_of_riemDist_lt_top`, `Morse.exists_joined_notMem_conjLocus`: every `q ∈ N` is
  joined by a path in `N` to a point `q'` not conjugate to `p` along any geodesic (Corollary
  18.2, `Morse.dense_compl_conjLocus`, in a small Riemannian ball around `q`).
* `Morse.pathSpHomotopyEquiv`: **Lemma 17.D with Theorem 17.1**: a path `σ` from `q` to `q'`
  gives a homotopy equivalence `Ω(N; p, q) ≃ Ω(N; p, q')` (`Ω ≃ Ω*` by 17.1, `Ω* ≅ Path p q`,
  `ω ↦ ω · σ`).
* `Morse.corollary_17_2`: **Corollary 17.2** for `N` closed in `V`: `Ω(N; p, q)` has the homotopy
  type of a countable cell complex (`Morse.IsCountableCellComplexType`, a tower of cell
  attachments and its telescope); `Morse.corollary_17_2_pathC`: the same for `Ω*`.
* `Morse.corollary_17_4_loop`: **Corollary 17.4 for the loop space** `Ω(Sⁿ; p, p)`, `n ≥ 2`;
  `Morse.bettiNumber_sphere_loops`: its Betti numbers over any field for `n ≥ 3` (`1` in the
  degrees divisible by `n − 1`, `0` otherwise).
* `Morse.Homology.spaceHomologyEquivOfHomotopyEquiv`, `Morse.Homology.bettiNumber_eq_of_homotopyEquiv`:
  homotopy equivalent spaces have isomorphic homology over a field, and the same Betti numbers.

## Deviations from Milnor, and what he leaves implicit

* **Corollary 17.2 is proved differently**: Milnor quotes his theorem that loop spaces of CW
  spaces have CW type (not formalized).  Here `p, q` are first replaced by `p, q'` with `q'` not
  conjugate to `p` (17.D, 17.1, 18.2), and then Theorem 17.3 gives an explicit countable cell
  complex.  This needs `M` complete (`N` closed in `V`), which Milnor's route does not; on the
  other hand it gives the countable complex of 17.3 rather than an abstract CW type.  Milnor's
  own use of 17.2, Whitehead's theorem at the end of 17.3, is not needed in the project (17.3 is
  proved by the Appendix route).
* **17.4 for loops** (the hidden hypothesis of Exposition/Chapter10.md): `p` is conjugate to
  itself along every great circle, so 17.3 does not apply to `Ω(Sⁿ; p, p)`; the loop space is
  homotopy equivalent to `Ω(Sⁿ; p, q)`, `q ⊥ p`, by 17.D and 17.1 (`Sⁿ` is path connected).
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold ENNReal

noncomputable section

universe u

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V}

/-- Points at finite Riemannian distance are joined by a path in `N`. -/
theorem joined_of_riemDist_lt_top {q q' : V} (hq : q ∈ N) (hq' : q' ∈ N)
    (h : riemDist (N := N) q q' < ⊤) : Joined (⟨q, hq⟩ : N) ⟨q', hq'⟩ := by
  have hne : (pathLengths (N := N) q q').Nonempty := by
    by_contra h'
    rw [not_nonempty_iff_eq_empty] at h'
    rw [riemDist, h', sInf_empty] at h
    exact lt_irrefl _ h
  obtain ⟨L, c, a, b, hc, hcN, hca, hcb, -⟩ := hne
  have hab := hc.1
  have hmem : ∀ t : unitInterval, a + (t : ℝ) * (b - a) ∈ Icc a b := fun t =>
    ⟨by nlinarith [t.2.1, t.2.2], by nlinarith [t.2.1, t.2.2]⟩
  refine ⟨{
    toFun := fun t => ⟨c (a + (t : ℝ) * (b - a)), hcN _ (hmem t)⟩
    continuous_toFun := ?_
    source' := Subtype.ext (by simp [hca])
    target' := Subtype.ext (by simp [hcb]) }⟩
  refine Continuous.subtype_mk ?_ _
  exact hc.2.1.comp_continuous (by fun_prop) hmem

variable (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)
include hN

/-- **Every point of `N` is joined to a point not conjugate to `p`** (Corollary 18.2: the
non-conjugate points are dense, and a small Riemannian ball is path connected). -/
theorem exists_joined_notMem_conjLocus {p q : V} (hp : p ∈ N) (hq : q ∈ N) :
    ∃ q' : V, ∃ hq' : q' ∈ N, q' ∉ conjLocus hN p ∧ Joined (⟨q, hq⟩ : N) ⟨q', hq'⟩ := by
  set U : Set N := {x | riemDist (N := N) q x < 1}
  have hU : IsOpen U := by
    have hc : Continuous fun x : N => riemDist (N := N) (x : V) q :=
      (continuousOn_iff_continuous_restrict.1 (continuousOn_riemDist_left hN q))
    have : U = (fun x : N => riemDist (N := N) (x : V) q) ⁻¹' Iio 1 := by
      ext x
      simp only [U, mem_ofPred_eq, mem_preimage, mem_Iio, riemDist_comm]
    rw [this]
    exact isOpen_Iio.preimage hc
  have hqU : (⟨q, hq⟩ : N) ∈ U := by
    change riemDist (N := N) q q < 1
    rw [riemDist_self hq]
    exact zero_lt_one
  obtain ⟨x, hxU, hxd⟩ := (dense_compl_conjLocus (hN := hN) ⟨p, hp⟩).inter_open_nonempty U hU
    ⟨_, hqU⟩
  exact ⟨x, x.2, hxd, joined_of_riemDist_lt_top hq x.2
    (lt_of_lt_of_le hxU (by exact_mod_cast le_top))⟩

/-- **Lemma 17.D with Theorem 17.1**: a path from `q` to `q'` in `N` gives a homotopy equivalence
`Ω(N; p, q) ≃ Ω(N; p, q')` (Milnor's metric on both). -/
def pathSpHomotopyEquiv {p q q' : V} (hp : p ∈ N) (hq : q ∈ N) (hq' : q' ∈ N)
    (σ : Path (⟨q, hq⟩ : N) ⟨q', hq'⟩) :
    ContinuousMap.HomotopyEquiv (PathSp N p q) (PathSp N p q') :=
  ((theorem_17_1 hN p q).exists_homotopyEquiv.choose.trans
    (pathCHomeomorph hp hq).toHomotopyEquiv).trans
    ((Homotopy.pathTransHomotopyEquiv σ).trans
      ((pathCHomeomorph hp hq').symm.toHomotopyEquiv.trans
        (theorem_17_1 hN p q').exists_homotopyEquiv.choose.symm))

/-- **Corollary 17.2** (Milnor p. 94), for `N` closed in `V` (complete): `Ω(N; p, q)`, with
Milnor's metric, has the homotopy type of a countable cell complex (a cell tower,
`Morse.IsCountableCellComplexType`). -/
theorem corollary_17_2 (hcl : IsClosed N) {p q : V} (hp : p ∈ N) (hq : q ∈ N) :
    ∃ cells : ℕ → List ℕ, IsCountableCellComplexType (PathSp N p q) cells := by
  obtain ⟨q', hq', hnc, ⟨σ⟩⟩ := exists_joined_notMem_conjLocus hN hp hq
  obtain ⟨geo, -, -, -, -, -, -, h⟩ := theorem_17_3_nonconj (hN := hN) hcl hp hq' hnc
  exact ⟨_, h.of_homotopyEquiv (pathSpHomotopyEquiv hN hp hq hq' σ)⟩

/-- **Corollary 17.2 for `Ω*`**: the space of continuous paths `Ω*(N; p, q)` (compact-open
topology) has the homotopy type of a countable cell complex, `N` closed in `V`. -/
theorem corollary_17_2_pathC (hcl : IsClosed N) {p q : V} (hp : p ∈ N) (hq : q ∈ N) :
    ∃ cells : ℕ → List ℕ, IsCountableCellComplexType (PathC N p q) cells := by
  obtain ⟨cells, h⟩ := corollary_17_2 hN hcl hp hq
  exact ⟨cells, h.of_homotopyEquiv (theorem_17_1 hN p q).exists_homotopyEquiv.choose.symm⟩

omit hN

open Milnor.Sphere

/-- **Homotopy invariance of singular homology**: homotopy equivalent spaces have isomorphic
homology `H_i(X; 𝕜) ≅ H_i(Y; 𝕜)`. -/
def _root_.Morse.Homology.spaceHomologyEquivOfHomotopyEquiv (𝕜 : Type u) [Field 𝕜]
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (i : ℕ) :
    Homology.spaceHomology 𝕜 i X ≃ₗ[𝕜] Homology.spaceHomology 𝕜 i Y :=
  have := Homology.isIso_homologyMap_of_homotopyEquiv (ModuleCat.of 𝕜 𝕜) (X := TopCat.of X)
    (Y := TopCat.of Y) (TopCat.ofHom e.toFun) e rfl i
  (CategoryTheory.asIso (HomologicalComplex.homologyMap
    ((Homology.singularChains (ModuleCat.of 𝕜 𝕜)).map (TopCat.ofHom e.toFun)) i)).toLinearEquiv

/-- **Homotopy invariance of the Betti numbers.** -/
theorem _root_.Morse.Homology.bettiNumber_eq_of_homotopyEquiv (𝕜 : Type u) [Field 𝕜]
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (i : ℕ) :
    Homology.bettiNumber 𝕜 X i = Homology.bettiNumber 𝕜 Y i :=
  (Homology.spaceHomologyEquivOfHomotopyEquiv 𝕜 e i).finrank_eq

/-- The loop space of `Sⁿ`, `n ≥ 2`, is homotopy equivalent to `Ω(Sⁿ; p, q)` for a point `q ≠ ±p`
(Lemma 17.D and Theorem 17.1). -/
theorem exists_loop_homotopyEquiv_sph {n : ℕ} (hn : 2 ≤ n) {p : EuclideanSpace ℝ (Fin (n + 1))}
    (hp : p ∈ Sph n) : ∃ q, ∃ hq : q ∈ Sph n, q ≠ p ∧ q ≠ -p ∧
      Nonempty (ContinuousMap.HomotopyEquiv (PathSp (Sph n) p p) (PathSp (Sph n) p q)) := by
  obtain ⟨u, hu, hpu⟩ := exists_unit_orthogonal (by omega : 1 ≤ n) p
  have hp1 := norm_of_mem_sph hp
  have hu' : u ∈ Sph n := mem_iff_norm.2 hu
  have hup : u ≠ p := fun h => by
    rw [h, real_inner_self_eq_norm_sq, hp1] at hpu
    norm_num at hpu
  have hun : u ≠ -p := fun h => by
    rw [h, inner_neg_right, real_inner_self_eq_norm_sq, hp1] at hpu
    norm_num at hpu
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  have hpc : IsPathConnected (Sph n) := by
    have : Sph n = Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := preimage_eq_sphere
    rw [this]
    exact isPathConnected_sphere hrank 0 zero_le_one
  have hj : Joined (⟨p, hp⟩ : Sph n) ⟨u, hu'⟩ := (hpc.joinedIn p hp u hu').joined_subtype
  exact ⟨u, hu', hup, hun, ⟨pathSpHomotopyEquiv (sphSub n) hp hp hu' hj.somePath⟩⟩

/-- **Corollary 17.4** (Milnor p. 96), **for the loop space**: for `n ≥ 2` and `p ∈ Sⁿ`, the loop
space `Ω(Sⁿ; p, p)` with Milnor's metric has the homotopy type of the countable cell complex with
one cell in each dimension `0, n − 1, 2(n − 1), …`. -/
theorem corollary_17_4_loop {n : ℕ} (hn : 2 ≤ n) {p : EuclideanSpace ℝ (Fin (n + 1))}
    (hp : p ∈ Sph n) :
    IsCountableCellComplexType (PathSp (Sph n) p p) (oneCellEach fun k => k * (n - 1)) := by
  obtain ⟨q, hq, hqp, hqn, ⟨e⟩⟩ := exists_loop_homotopyEquiv_sph hn hp
  exact (corollary_17_4 hn hp hq hqp hqn).of_homotopyEquiv e

/-- **The homology of the loop space of `Sⁿ`** (Milnor p. 96), `n ≥ 3`: over any field `𝕜`,
`H_i(Ω(Sⁿ; p, p); 𝕜)` has dimension `1` if `n − 1` divides `i` and `0` otherwise. -/
theorem bettiNumber_sphere_loops {𝕜 : Type} [Field 𝕜] {n : ℕ} (hn : 3 ≤ n)
    {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ Sph n) (i : ℕ) :
    Homology.bettiNumber 𝕜 (PathSp (Sph n) p p) i = if (n - 1) ∣ i then 1 else 0 := by
  obtain ⟨q, hq, hqp, hqn, ⟨e⟩⟩ := exists_loop_homotopyEquiv_sph (by omega) hp
  rw [Homology.bettiNumber_eq_of_homotopyEquiv 𝕜 e]
  exact bettiNumber_sphere_paths hn hp hq hqp hqn i

end Morse
