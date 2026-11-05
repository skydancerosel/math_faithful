import Morse.Chapter10.FullPathOmega
import Morse.Chapter10.GoodJoin

/-!
Milnor, *Morse Theory*, §17, Theorem 17.1 (pp. 93–94), with the proof of Exposition/Chapter10.md,
§5 ("A proof that works").

# Theorem 17.1: the inclusion `Ω → Ω*` is a homotopy equivalence

## Milnor's text, paraphrased

(p. 93) Let `Ω*` be the space of continuous paths from `p` to `q`, with the compact-open
topology.  **Theorem 17.1**: the inclusion `i : Ω → Ω*` of the piecewise smooth paths (with
Milnor's metric `d`) is a homotopy equivalence.  (pp. 93–94) Proof: choose a continuous
`A : Ω* → (0, 1]` such that points of `ω` at times closer than `A(ω)` are joined by unique
minimal geodesics depending smoothly on them, and let `h(ω)` be the broken geodesic through
`ω(0), ω(A), ω(2A), …, ω(1)`.  Milnor says that `h` is clearly continuous, and that the arguments
of §16 give `h ∘ i ≃ id` and `i ∘ h ≃ id`.

## In the embedded setting

* `Morse.theorem_17_1`: **Theorem 17.1**: for a slice submanifold `N` of a finite-dimensional
  inner product space `V` (complete or not) and any `p, q`, the inclusion
  `i : Ω(N; p, q) → Ω*(N; p, q)` is a homotopy equivalence (`Morse.IsHomotopyEquiv`).
* `Morse.JoinSystem.isHomotopyEquiv_toPathC`: the same for any system of minimal joins
  (`Morse.JoinSystem`); `Morse.theorem_17_1` applies it to the good balls (`Morse.goodJoin`).
* The proof is the exposition's: the open sets `Y_k ⊆ Ω*` of paths whose dyadic pieces of level
  `k` lie in good balls exhaust `Ω*` (`Morse.JoinSystem.isOpen_YSet`,
  `Morse.JoinSystem.exists_mem_YSet`); on `X_k = i⁻¹(Y_k)` the inclusion `X_k → Y_k` is a
  homotopy equivalence (`Morse.JoinSystem.isHomotopyEquiv_toY`: the broken geodesic with fixed
  dyadic vertices, and the deformation along minimal geodesics); `Ω*` is metric, hence
  paracompact, so it is the homotopy direct limit of the `Y_k` (Example 1 of the Appendix,
  `Morse.example1`), and `Ω` is that of the `X_k` (`Morse.isHomotopyDirectLimit_preimage`);
  Theorem A of the Appendix (`Morse.theoremA_general`) concludes.

## What Milnor leaves implicit

* **`h` is not continuous for `d`** (the exposition's example: a new last segment of `h(ω)` can
  appear with energy tending to infinity).  The subdivision is kept fixed on each open set `Y_k`,
  and the pieces are glued with the Appendix.
* **Convexity**: minimal geodesics between points of a good ball stay in it (Whitehead), so that
  the deformation does not leave `Y_k` (`Morse/Chapter10/GoodBalls.lean`).
* **Smooth dependence on a whole good ball**: Milnor's "depending differentiably" is needed as one
  smooth function of both end points on each good set, obtained by gluing local ones
  (`Morse.exists_smooth_glue`).
* **Continuity for `d`** of maps given by smooth formulas needs the velocities of the paths to
  converge in `L²`, which follows from convergence for `d`
  (`Morse.PathSp.tendsto_integral_norm_deriv_sub_sq`), although `d` only involves the speeds.
* **`Ω` is not Hausdorff** for `d` (paths are functions on `ℝ`, and `d` only sees `[0, 1]`), so
  Example 1 of the Appendix is applied to `Ω*` and pulled back to `Ω`.
* **Theorem A for open pieces**: the `X_k` and `Y_k` are open, not closed, and Milnor's proof of
  Theorem A needs closed pieces; `Morse.theoremA_general` applies it to mapping telescopes.
* **No completeness** is needed for Theorem 17.1 (it is needed for Theorem 17.3 and in Remark
  17.5); here `N` is any slice submanifold.
-/

open Set Filter Topology Function

noncomputable section

namespace Morse

open scoped unitInterval Manifold

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- **The inclusion `i : Ω → Ω*`** as a continuous map (Milnor p. 93). -/
def pathIncl (p q : V) : C(PathSp N p q, PathC N p q) :=
  ⟨PathSp.toPathC, PathSp.continuous_toPathC⟩

namespace JoinSystem

include hN in
/-- **Theorem 17.1 from a system of minimal joins**: `X_k → Y_k` is a homotopy equivalence for
each `k`, and Theorem A of the Appendix glues these (the `X_k` and `Y_k` are open, and `Ω` and
`Ω*` are their homotopy direct limits by Example 1). -/
theorem isHomotopyEquiv_toPathC (J : JoinSystem N) (p q : V) :
    IsHomotopyEquiv (pathIncl (N := N) p q) := by
  have hint : ∀ y : PathC N p q, ∃ n, y ∈ interior (J.YSet n) := fun y => by
    obtain ⟨k, hk⟩ := J.exists_mem_YSet y
    exact ⟨k, (J.isOpen_YSet k).interior_eq.symm ▸ hk⟩
  have hXeq : (fun n => J.XSet n (p := p) (q := q)) = fun n => pathIncl p q ⁻¹' J.YSet n :=
    funext fun n => XSet_eq_preimage n
  have hX : IsHomotopyDirectLimit fun n => J.XSet n (p := p) (q := q) := by
    rw [hXeq]
    exact isHomotopyDirectLimit_preimage J.YSet_mono hint (pathIncl p q)
  have hY : IsHomotopyDirectLimit fun n => J.YSet n (p := p) (q := q) :=
    example1 J.YSet_mono hint
  have hA : Monotone fun n => J.XSet n (p := p) (q := q) := by
    rw [hXeq]
    exact fun m n h => preimage_mono (J.YSet_mono h)
  have hf : ∀ n, MapsTo (pathIncl p q) (J.XSet n) (J.YSet n) := fun n γ hγ => by
    rw [XSet_eq_preimage] at hγ
    exact hγ
  refine theoremA_general hA J.YSet_mono hX hY (pathIncl p q) hf fun n => ?_
  have : restrictTo (pathIncl p q) (hf n) = J.toY n := ContinuousMap.ext fun γ => rfl
  rw [this]
  exact J.isHomotopyEquiv_toY hN n

end JoinSystem

include hN in
/-- **Theorem 17.1** (Milnor p. 93): the inclusion `i : Ω(N; p, q) → Ω*(N; p, q)` of the
piecewise smooth paths, with Milnor's metric, into the continuous paths, with the compact-open
topology, is a homotopy equivalence.  `N` is any slice submanifold of `V`; no completeness is
needed. -/
theorem theorem_17_1 (p q : V) : IsHomotopyEquiv (pathIncl (N := N) p q) :=
  (goodJoin hN).isHomotopyEquiv_toPathC hN p q

end Morse
