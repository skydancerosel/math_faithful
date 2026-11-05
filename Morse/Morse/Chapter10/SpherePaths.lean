import Morse.Chapter10.PathHomology
import Morse.Chapter10.SphereGeodesics

/-!
Milnor, *Morse Theory*, §17, pp. 95–96: **Corollary 17.4**, the path space of the sphere `Sⁿ`, and
its homology.

# The path space of the sphere

## Milnor's text, paraphrased

(pp. 95–96) Let `p, q ∈ Sⁿ` be neither equal nor antipodal.  The geodesics from `p` to `q` run
along the great circle through `p` and `q`, possibly several times around; the shortest one has
index `0`, the next (the long arc) index `n − 1`, the next `2(n − 1)`, and so on, since a geodesic
of length between `kπ` and `(k + 1)π` passes `k` times through `p` or its antipode, each a conjugate
point of multiplicity `n − 1`.  **Corollary 17.4**: the loop space of `Sⁿ` has the homotopy type of
a CW-complex with one cell in each of the dimensions `0, n − 1, 2(n − 1), …`.  For `n > 2` the
homology of `ΩSⁿ` is therefore free of rank one in the degrees divisible by `n − 1` and zero
otherwise.

## In the embedded setting

`Sⁿ = Milnor.Sphere.Sph n ⊆ ℝⁿ⁺¹` with the induced metric; the geodesics `Morse.sphGeod p q k`,
their energies and indices are in `Morse/Chapter10/SphereGeodesics.lean`.

* `Morse.corollary_17_4`: **Corollary 17.4 for `Ω(Sⁿ; p, q)`**, `n ≥ 2`, `q ≠ ±p`: the path space,
  with Milnor's metric, has the homotopy type of the countable cell complex with one cell of each
  dimension `0, n − 1, 2(n − 1), …`, attached in this order (`Morse.oneCellEach`).
* `Morse.bettiNumber_sphere_paths`: **its homology** (`n ≥ 3`): over any field `𝕜`,
  `dim H_i(Ω(Sⁿ; p, q); 𝕜)` is `1` if `n − 1` divides `i` and `0` otherwise.

## What Milnor leaves implicit

* **Loops versus paths.**  Milnor's proof applies 17.3, which needs `p` and `q` non-conjugate;
  `p` is conjugate to itself along every great circle, so the statement for the loop space
  `Ω(Sⁿ; p, p)` needs the independence of the homotopy type of `Ω*(M; p, q)` from `q` and
  Theorem 17.1 (Lemma 17.D and §5 of Exposition/Chapter10.md).  What is proved here is the
  statement for `q ≠ ±p`, which is what Milnor's argument gives; the loop-space form is
  `Morse.corollary_17_4_loop` in `Morse/Chapter10/CWType.lean`.
* **The geodesics and their indices** (stated without proof on p. 96): the classification of the
  geodesics of `Sⁿ` from `p` to `q` and the conjugate points along great circles, with their
  multiplicities, are proved in `Morse/Chapter10/SphereGeodesics.lean`; the index is then given by
  Theorem 15.1.
* **`n > 2`.**  For `n = 2` there is a cell in every dimension and the cell structure says nothing
  about the boundary maps; the lacunary principle needs `n − 1 ≥ 2`.
* **The homology is not computed from cellular chains** but from the energy filtration of `Ω`
  (`Morse/Chapter10/PathHomology.lean`): the cell complexes of 17.3 have non-cellular attaching
  maps.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace Real

noncomputable section

namespace Morse

open Milnor.Sphere Morse.Homology

variable {n : ℕ} {p q : EuclideanSpace ℝ (Fin (n + 1))}

/-- The energies of the geodesics `sphGeod p q k` increase strictly. -/
theorem strictMono_energy_sphGeod (hp : p ∈ Sph n) (hq : q ∈ Sph n) (hqp : q ≠ p)
    (hqn : q ≠ -p) : StrictMono fun k => energy (sphGeod p q k) 0 1 := by
  intro j k hjk
  simp only [energy_sphGeod hp hq hqp hqn]
  have h1 := sphLen_strictMono hp hq hqp hqn hjk
  have h0 := sphLen_pos hp hq hqp hqn j
  nlinarith

/-- The energies of the geodesics `sphGeod p q k` tend to `∞` (`L_k > kπ`). -/
theorem tendsto_energy_sphGeod (hp : p ∈ Sph n) (hq : q ∈ Sph n) (hqp : q ≠ p)
    (hqn : q ≠ -p) : Tendsto (fun k => energy (sphGeod p q k) 0 1) atTop atTop := by
  have hL : Tendsto (sphLen p q) atTop atTop :=
    tendsto_atTop_mono (fun k => (mul_pi_lt_sphLen hp hq hqp hqn k).le)
      (tendsto_natCast_atTop_atTop.atTop_mul_const Real.pi_pos)
  refine ((tendsto_pow_atTop two_ne_zero).comp hL).congr fun k => ?_
  exact (energy_sphGeod hp hq hqp hqn k).symm

/-- **Corollary 17.4** (Milnor p. 96), for the path space `Ω(Sⁿ; p, q)`, `q ≠ ±p`, `n ≥ 2`: with
Milnor's metric it has the homotopy type of the countable cell complex with one cell in each of the
dimensions `0, n − 1, 2(n − 1), …`, attached in this order. -/
theorem corollary_17_4 (hn : 2 ≤ n) (hp : p ∈ Sph n) (hq : q ∈ Sph n) (hqp : q ≠ p)
    (hqn : q ≠ -p) :
    IsCountableCellComplexType (PathSp (Sph n) p q) (oneCellEach fun k => k * (n - 1)) :=
  omega_cells_of_unique (hN := sphSub n) isCompact_sph.isClosed hp hq
    (fun _ hγ hgeo => hessNullity_eq_zero_of_notMem_conjLocus
      (notMem_conjLocus_sph hp hq hqp hqn (by omega)) hγ hgeo)
    (sphGeod_mem_pathSpace hp hq hqp hqn) (isUnbrokenGeodesic_sphGeod hp hq hqp hqn)
    (fun γ hγ hgeo => exists_eqOn_sphGeod hp hq hqp hqn (by omega) hγ hgeo)
    (strictMono_energy_sphGeod hp hq hqp hqn) (tendsto_energy_sphGeod hp hq hqp hqn) _
    (fun k γ hγ hgeo heq => formIndex_eq_of_eqOn_sphGeod hp hq hqp hqn (by omega) hγ hgeo heq)

/-- **The homology of the path space of `Sⁿ`** (Milnor p. 96), `n ≥ 3`, `q ≠ ±p`: over any field
`𝕜`, `H_i(Ω(Sⁿ; p, q); 𝕜)` has dimension `1` if `n − 1` divides `i` and `0` otherwise. -/
theorem bettiNumber_sphere_paths {𝕜 : Type} [Field 𝕜] (hn : 3 ≤ n) (hp : p ∈ Sph n)
    (hq : q ∈ Sph n) (hqp : q ≠ p) (hqn : q ≠ -p) (i : ℕ) :
    bettiNumber 𝕜 (PathSp (Sph n) p q) i = if (n - 1) ∣ i then 1 else 0 :=
  bettiNumber_omega_of_unique (hN := sphSub n) isCompact_sph.isClosed hp hq
    (fun _ hγ hgeo => hessNullity_eq_zero_of_notMem_conjLocus
      (notMem_conjLocus_sph hp hq hqp hqn (by omega)) hγ hgeo)
    (sphGeod_mem_pathSpace hp hq hqp hqn) (isUnbrokenGeodesic_sphGeod hp hq hqp hqn)
    (fun γ hγ hgeo => exists_eqOn_sphGeod hp hq hqp hqn (by omega) hγ hgeo)
    (strictMono_energy_sphGeod hp hq hqp hqn) (tendsto_energy_sphGeod hp hq hqp hqn)
    (by omega)
    (fun k γ hγ hgeo heq => formIndex_eq_of_eqOn_sphGeod hp hq hqp hqn (by omega) hγ hgeo heq) i

end Morse
