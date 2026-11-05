import Milnor.Chapter7.BallChainSign
import Milnor.Chapter7.Neighbour

/-!
# Punctures: the complement of a finite set, and the punctured orientability dichotomy

Milnor's remark at the end of §7 (p. 50) is that for a *connected non-orientable* manifold the
smooth maps to a sphere are classified by the degree modulo `2`.  The argument slides a framed point
around an orientation-reversing loop of chart balls; the loop has to **avoid the other points** of
the framed `0`-manifold, and the loops produced by
`Milnor.exists_isBall_reverses_of_not_isOrientable` (`Milnor/Chapter7/OrientBall.lean`) do not.
To make them avoid a finite set one removes that set from `M` and runs the dichotomy on what is
left, which requires knowing that the complement of a finite set in a connected manifold is again a
connected manifold, and that it is again non-orientable.  Both are proved here.

This file is **Stage 5** of the plan `Milnor/Exposition/PlanMod2.md` (§3.4 and the stage list of
§7): first the point-set topology of punctures, which is independent of the rest of the plan, and
then the orientation theory that rests on it.  Five groups of statements.

* **A punctured chart ball is connected** (`Milnor.isConnected_chartBall_diff_singleton`), for
  `2 ≤ m`.  A chart ball in the sense of `Milnor.chartBall` is, when its ball lies in the target of
  the chart, the homeomorphic image of a ball of the model space
  (`Milnor.chartBall_eq_image`), so everything is transported from the model space, where
  `Metric.ball x R \ {q}` is the image of the complement of a point under the homeomorphism
  `OpenPartialHomeomorph.univBall` of the whole space with the ball, and the complement of a point
  in a real vector space of rank `> 1` is path connected by Mathlib's
  `isPathConnected_compl_singleton_of_one_lt_rank`.  Path connectedness survives both transports, so
  the punctured chart ball is in fact path connected
  (`Milnor.isPathConnected_chartBall_diff_singleton`).

* **The complement of a finite set is connected** (`Milnor.isConnected_compl_finite`, and
  `Milnor.isConnected_diff_finite` in the `univ \ P` form of the plan), for `2 ≤ m` and connected
  `M`.  By induction on the finite set it is enough to remove one point from an open preconnected
  set `U` (`Milnor.isPreconnected_diff_singleton_of_isOpen`): a disconnection of `U \ {p}` into
  `V₁, V₂` is extended over `p` by replacing `V₁` by `V₁ ∪ B` and `V₂` by `V₂ \ {p}`, where `B` is a
  chart ball about `p` inside `U` (`Milnor.exists_chartBall_subset`), which is legitimate because
  `B \ {p}` is connected and therefore lies in one of `V₁, V₂` — and if it met both, the punctured
  ball would already supply the point of `V₁ ∩ V₂` that is wanted.  Nonemptiness is a separate
  matter and needs only `0 < m` (`Milnor.nonempty_compl_finite`).

* **The two set lemmas the later stages need.**  `Milnor.compl'_eq_compl`, and
  `Milnor.compl'_eq_diff` under the plan's own name: the connected component `Milnor.compl' N x` of
  `x` in the complement of the other points of a finite set `N` is that whole complement,
  `(N \ {x})ᶜ` — so the sets in which the moving machinery of `Milnor/Chapter7/Reach.lean` works
  are literally complements of finite sets.
  Applied to a framed `0`-manifold `F` with `N := F.N` and `hN := F.finite_N` this is the statement
  of the plan.  And `Milnor.exists_mem_open_notMem_finite`: a nonempty open subset of a manifold of
  positive dimension is infinite (`Milnor.infinite_of_isOpen`), hence not contained in any finite
  set — the generalization from `M` to an arbitrary nonempty open set of
  `Milnor.Framed.exists_notMem_finite` (`Milnor/Chapter7/Hopf.lean`, line 71), whose proof is the
  model for the one here.

* **A family of orientations on the complement extends over the punctures**
  (`Milnor.extend_ballCoherent`), for `2 ≤ m`.  A family `or` of orientations of the tangent spaces
  of `M` is *ball-coherent on* a set (`Milnor.IsBallCoherentOn`) if transport along every ball hop
  whose closed chart ball lies in that set carries its value at one end of the hop to its value at
  the other.  Every orientation of `M` is ball-coherent on every set
  (`Milnor.Orient.isBallCoherentOn`), and the content of the extension lemma is the converse: a
  family ball-coherent on the complement of a finite set `P` agrees off `P` with a transport section
  (`Milnor.IsTransportSection`) on the whole of `M`, hence with an orientation of `M`.  The value
  at a point `p` is the value of the family at a point `y` near `p`, transported back to `p`
  through the chart at `p`; it does not depend on `y`
  (`Milnor.exists_eventually_orTransport_eq`) because `y ↦ orTransport I p y (or y)` is locally
  constant on a punctured chart ball about `p` — this is where the **transition cocycle lemma**
  `Milnor.eventually_jacSign_mul_jacSign_eq` of `Milnor/Chapter7/BallChainSign.lean` enters, the two
  Jacobian signs being separately discontinuous and jointly locally constant — and because
  the punctured ball is connected, which is the first item above and the only use of `2 ≤ m`.  A
  locally constant function on a connected set is constant by
  `Milnor.eq_of_eventually_eq_of_isPreconnected`, proved here by hand since the two orientations of
  the model space carry no topology.  Off `P` the extension is the original family, no point
  of a manifold of positive dimension being isolated (`Milnor.exists_ne_of_eventually`), and the
  transport-section condition is then verified at every point at once, punctured or not.

* **The punctured dichotomy** (`Milnor.HasReversingBallLoop` and
  `Milnor.hasReversingBallLoop_of_not_isOrientable`), the interface everything downstream uses: a
  connected manifold of dimension at least two that is *not* orientable has, at every point `x₀` off
  a finite set `P`, a loop of chart balls at `x₀` missing `P` whose `Milnor.chainSign` is `-1` — a
  loop along which every orientation comes back reversed.  Were there no such loop, every
  `P`-avoiding ball loop at `x₀` would have sign `1`, so the transport of one orientation along
  `P`-avoiding ball chains would not depend on the chain used; since the complement of `P` is
  connected and any two of its points are joined by such a chain (`Milnor.exists_isBallIn`),
  that transport would define a family of orientations there, ball-coherent because a ball hop
  running inside the complement extends such a chain, and the extension lemma would make `M`
  orientable.

## The hypotheses

`2 ≤ m` is used for the punctured chart ball and, through it, for the two connectedness statements,
for the extension lemma and for the punctured dichotomy, and it cannot be weakened: for `m = 1` a
punctured chart ball is an interval minus an interior point, which is disconnected, and `ℝ \ {0}`
is a disconnected complement of a finite set in a connected `1`-manifold; for `m = 0` a punctured
chart ball is empty.  This is the dimension restriction that the plan expects the final mod `2`
theorem to carry.  `0 < m` is all that infinitude and nonemptiness need.  Boundarylessness of `I`
is used exactly where chart balls have to be *produced* — `Milnor.exists_chartBall_subset` and
everything downstream of it — through the openness of the target of a chart, as in
`Milnor.exists_radius`; the statements about a chart ball that is given, with its ball inside the
chart's target, need it not.  **No separation hypothesis is needed**: every manifold is `T1`
(`ModelWithCorners.t1Space`), which is what makes `{p}` closed in the extension argument, and
Hausdorffness is nowhere used.  Connectedness of `M` is assumed only on the statements about `M`
itself.  Finiteness of `P` enters only through the closedness of `P` and of `P \ {p}`, which is
what keeps their complements open, and through the connectedness of the complement.  Smoothness —
the instance `IsManifold I ∞ M`, carried by every statement below because `Milnor.chartBall`
carries it — is irrelevant to the point-set part, where all the arguments are arguments about the
charts as homeomorphisms; the orientation part uses it through the dictionary of
`Milnor/Chapter7/BallChainSign.lean`, whose cocycle lemma differentiates the transition map between
two charts.

## What the later stages consume

Of this file only `Milnor.HasReversingBallLoop` and
`Milnor.hasReversingBallLoop_of_not_isOrientable` — together with `Milnor.compl'_eq_compl` and
`Milnor.exists_mem_open_notMem_finite` — are used by Stage 6 and beyond.  The plan
`Milnor/Exposition/PlanMod2.md` carries `Milnor.HasReversingBallLoop` as a hypothesis of the
statements of Stages 7 and 8, so that nothing downstream depends on how the reversing loop is
obtained.
-/

open Set Module Filter Topology Function

open scoped ContDiff Manifold

set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace Milnor

/-! ### Punctured balls of a normed space -/

section NormedSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **A ball of positive radius in a nontrivial real normed space is infinite.**  For a fixed
`v ≠ 0` the map `t ↦ x + t • v` is injective and carries the interval `(0, R/‖v‖)` into the ball.
This is the counting step of `Milnor.Framed.exists_notMem_finite` (`Milnor/Chapter7/Hopf.lean`,
line 71), stated for a normed space instead of for a chart of a submanifold. -/
theorem infinite_ball [Nontrivial F] (x : F) {R : ℝ} (hR : 0 < R) :
    (Metric.ball x R).Infinite := by
  obtain ⟨v, hv⟩ := exists_ne (0 : F)
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hinj : InjOn (fun t : ℝ => x + t • v) (Ioo 0 (R / ‖v‖)) := by
    intro t _ t' _ h
    have h' : t • v = t' • v := add_left_cancel h
    exact smul_left_injective ℝ hv h'
  have hsub : (fun t : ℝ => x + t • v) '' Ioo 0 (R / ‖v‖) ⊆ Metric.ball x R := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht.1]
    calc t * ‖v‖ < R / ‖v‖ * ‖v‖ := mul_lt_mul_of_pos_right ht.2 hvn
      _ = R := div_mul_cancel₀ R hvn.ne'
  exact Set.Infinite.mono hsub ((Ioo_infinite (div_pos hR hvn)).image hinj)

/-- **A punctured ball of a real normed space of rank at least two is path connected.**
`OpenPartialHomeomorph.univBall x R` is a homeomorphism of the whole space onto the ball
(`Mathlib/Analysis/Normed/Module/Ball/Homeomorph.lean`), so a ball with a point removed is the
image of the space with a point removed, which is path connected by Mathlib's
`isPathConnected_compl_singleton_of_one_lt_rank`
(`Mathlib/Analysis/Normed/Module/Connected.lean`).  If the removed point is not in the ball there is
nothing to remove and the ball is path connected by convexity. -/
theorem isPathConnected_ball_diff_singleton (h : 1 < Module.rank ℝ F) (x : F) {R : ℝ} (hR : 0 < R)
    (q : F) : IsPathConnected (Metric.ball x R \ {q}) := by
  by_cases hq : q ∈ Metric.ball x R
  · obtain ⟨f, hsrc, htgt, hcont⟩ : ∃ f : OpenPartialHomeomorph F F,
        f.source = univ ∧ f.target = Metric.ball x R ∧ Continuous f :=
      ⟨OpenPartialHomeomorph.univBall x R, OpenPartialHomeomorph.univBall_source x R,
        OpenPartialHomeomorph.univBall_target x hR,
        OpenPartialHomeomorph.continuous_univBall x R⟩
    have hmem : ∀ u : F, u ∈ f.source := fun u => by rw [hsrc]; exact mem_univ u
    have hqt : q ∈ f.target := htgt.symm.subset hq
    have himg : (f : F → F) '' {f.symm q}ᶜ = Metric.ball x R \ {q} := by
      apply Subset.antisymm
      · rintro _ ⟨u, hu, rfl⟩
        refine ⟨htgt.subset (f.map_source (hmem u)), ?_⟩
        intro hfu
        rw [mem_singleton_iff] at hfu
        exact hu (mem_singleton_iff.2 (by rw [← hfu, f.left_inv (hmem u)]))
      · intro z hz
        have hzt : z ∈ f.target := htgt.symm.subset hz.1
        refine ⟨f.symm z, ?_, f.right_inv hzt⟩
        intro hzq
        rw [mem_singleton_iff] at hzq
        exact hz.2 (mem_singleton_iff.2 (by rw [← f.right_inv hzt, hzq, f.right_inv hqt]))
    rw [← himg]
    exact (isPathConnected_compl_singleton_of_one_lt_rank h _).image hcont
  · rw [sdiff_singleton_eq_self hq]
    exact Metric.isPathConnected_ball hR

end NormedSpace

/-! ### The dimension hypotheses, read on the model space -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {m : ℕ}

/-- `2 ≤ m` in the form in which Mathlib's connectivity results want it: the rank of the model space
as a cardinal exceeds `1`. -/
theorem one_lt_rank_of_two_le (hm : finrank ℝ E = m) (hm2 : 2 ≤ m) : 1 < Module.rank ℝ E := by
  rw [← Module.finrank_eq_rank ℝ E, hm]
  exact_mod_cast hm2

/-- `0 < m` says that the model space has two distinct points. -/
theorem nontrivial_of_zero_lt (hm : finrank ℝ E = m) (hm0 : 0 < m) : Nontrivial E :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hm]; exact hm0)

/-! ### Small chart balls -/

/-- **Every point of an open set is the centre of a chart ball contained in it**, with the ball of
the same radius inside the target of the chart, so that the chart ball is the homeomorphic image of
that ball (`Milnor.chartBall_eq_image`) and in particular connected.  The inverse of the chart pulls
the open set back to a subset of the target that is open in the model space — this is where the
target of a chart has to be open, hence where the model has to be boundaryless — and a metric ball
inside that pullback is the required radius.  For `U = univ` the statement is
`Milnor.exists_radius` with a vacuous last conjunct. -/
theorem exists_chartBall_subset [I.Boundaryless] {c : M} {U : Set M} (hUo : IsOpen U)
    (hc : c ∈ U) :
    ∃ R > 0, Metric.ball (extChartAt I c c) R ⊆ (extChartAt I c).target ∧
      chartBall I c R ⊆ U := by
  have hW : IsOpen ((extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' U) :=
    (continuousOn_extChartAt_symm c).isOpen_inter_preimage (isOpen_extChartAt_target c) hUo
  have hmem : extChartAt I c c ∈ (extChartAt I c).target ∩ (extChartAt I c).symm ⁻¹' U := by
    refine ⟨(extChartAt I c).map_source (mem_extChartAt_source c), ?_⟩
    rw [mem_preimage, (extChartAt I c).left_inv (mem_extChartAt_source c)]
    exact hc
  obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.1 hW _ hmem
  refine ⟨R, hR, fun u hu => (hRW hu).1, fun z hz => ?_⟩
  have h2 := (hRW (Metric.mem_ball.2 (mem_chartBall.1 hz).2)).2
  rw [mem_preimage, (extChartAt I c).left_inv (chartBall_subset_source hz)] at h2
  exact h2

/-! ### A punctured chart ball is connected -/

/-- **A punctured chart ball is path connected** when `2 ≤ m`.  The chart ball is the image of a
ball of the model space under the inverse of the chart (`Milnor.chartBall_eq_image`), and that
inverse is injective on the target and continuous there, so removing the point `p` of the chart ball
corresponds to removing the point `extChartAt I c p` of the ball;
`Milnor.isPathConnected_ball_diff_singleton` does the rest.  If `p` is not in the chart ball, the
chart ball itself is the image of the (path connected) ball.

Neither boundarylessness nor any separation hypothesis is needed: the ball of radius `R` is assumed
to lie in the target of the chart, which for a boundaryless model is arranged by
`Milnor.exists_chartBall_subset`.  The plan `Milnor/Exposition/PlanMod2.md` calls this
`isConnected_ballU_diff_singleton`, after the chart balls `Milnor.Framed.ballU` of a submanifold of
a Euclidean space; the chart balls here are the abstract ones of
`Milnor/Chapter7/OrientBall.lean`. -/
theorem isPathConnected_chartBall_diff_singleton (hm : finrank ℝ E = m) (hm2 : 2 ≤ m) {c : M}
    {R : ℝ} (hR : 0 < R)
    (hRt : Metric.ball (extChartAt I c c) R ⊆ (extChartAt I c).target) (p : M) :
    IsPathConnected (chartBall I c R \ {p}) := by
  by_cases hp : p ∈ chartBall I c R
  · have hpm := mem_chartBall.1 hp
    have himg : (extChartAt I c).symm ''
        (Metric.ball (extChartAt I c c) R \ {extChartAt I c p}) = chartBall I c R \ {p} := by
      apply Subset.antisymm
      · rintro _ ⟨u, ⟨hu, hune⟩, rfl⟩
        refine ⟨(chartBall_eq_image hRt).symm.subset ⟨u, hu, rfl⟩, ?_⟩
        intro hzp
        rw [mem_singleton_iff] at hzp
        refine hune (mem_singleton_iff.2 ?_)
        rw [← hzp, (extChartAt I c).right_inv (hRt hu)]
      · intro z hz
        obtain ⟨hzB, hzp⟩ := hz
        refine ⟨extChartAt I c z, ⟨Metric.mem_ball.2 (mem_chartBall.1 hzB).2, ?_⟩,
          (extChartAt I c).left_inv (mem_chartBall.1 hzB).1⟩
        intro hzq
        rw [mem_singleton_iff] at hzq
        exact hzp (mem_singleton_iff.2
          ((extChartAt I c).injOn (mem_chartBall.1 hzB).1 hpm.1 hzq))
    rw [← himg]
    exact (isPathConnected_ball_diff_singleton (one_lt_rank_of_two_le hm hm2) _ hR _).image'
      ((continuousOn_extChartAt_symm c).mono (sdiff_subset.trans hRt))
  · rw [sdiff_singleton_eq_self hp, chartBall_eq_image hRt]
    exact (Metric.isPathConnected_ball hR).image'
      ((continuousOn_extChartAt_symm c).mono hRt)

/-- **A punctured chart ball is connected** when `2 ≤ m`; the form in which the second half of
Stage 5 uses the previous theorem.  For `m ≤ 1` it is false: a punctured chart ball of a
`1`-manifold is an interval with an interior point removed, and for `m = 0` it is empty. -/
theorem isConnected_chartBall_diff_singleton (hm : finrank ℝ E = m) (hm2 : 2 ≤ m) {c : M} {R : ℝ}
    (hR : 0 < R) (hRt : Metric.ball (extChartAt I c c) R ⊆ (extChartAt I c).target) (p : M) :
    IsConnected (chartBall I c R \ {p}) :=
  (isPathConnected_chartBall_diff_singleton hm hm2 hR hRt p).isConnected

/-! ### A manifold of positive dimension is locally infinite -/

/-- **A nonempty open subset of a manifold of positive dimension is infinite.**  It contains a chart
ball (`Milnor.exists_chartBall_subset`), which is the injective image of a ball of the model space
(`Milnor.chartBall_eq_image`), and that ball is infinite because the model space is nontrivial
(`Milnor.infinite_ball`). -/
theorem infinite_of_isOpen (hm : finrank ℝ E = m) (hm0 : 0 < m) [I.Boundaryless] {U : Set M}
    (hUo : IsOpen U) (hUne : U.Nonempty) : U.Infinite := by
  have : Nontrivial E := nontrivial_of_zero_lt hm hm0
  obtain ⟨c, hc⟩ := hUne
  obtain ⟨R, hR, hRt, hBU⟩ := exists_chartBall_subset (I := I) hUo hc
  have hinj : InjOn (extChartAt I c).symm (Metric.ball (extChartAt I c c) R) := by
    intro u hu u' hu' h
    rw [← (extChartAt I c).right_inv (hRt hu), ← (extChartAt I c).right_inv (hRt hu'), h]
  refine Set.Infinite.mono hBU ?_
  rw [chartBall_eq_image hRt]
  exact (infinite_ball _ hR).image hinj

/-- **A nonempty open subset of a manifold of positive dimension is not contained in any finite
set.**  This is the generalization, asked for by the plan `Milnor/Exposition/PlanMod2.md` under the
name `exists_mem_open_notMem_finite`, of `Milnor.Framed.exists_notMem_finite`
(`Milnor/Chapter7/Hopf.lean`, line 71) from the whole manifold to an arbitrary nonempty open
subset. -/
theorem exists_mem_open_notMem_finite (hm : finrank ℝ E = m) (hm0 : 0 < m) [I.Boundaryless]
    {U : Set M} (hUo : IsOpen U) (hUne : U.Nonempty) {P : Set M} (hP : P.Finite) :
    ∃ x ∈ U, x ∉ P :=
  (infinite_of_isOpen (I := I) hm hm0 hUo hUne).exists_notMem_finite hP

/-- **The complement of a finite set in a nonempty manifold of positive dimension is nonempty.**
Stated separately from the connectedness of that complement because it needs only `0 < m`. -/
theorem nonempty_compl_finite (hm : finrank ℝ E = m) (hm0 : 0 < m) [I.Boundaryless] [Nonempty M]
    {P : Set M} (hP : P.Finite) : (Pᶜ : Set M).Nonempty := by
  obtain ⟨x, -, hx⟩ := exists_mem_open_notMem_finite (I := I) hm hm0 isOpen_univ univ_nonempty hP
  exact ⟨x, hx⟩

/-! ### The complement of a finite set is connected -/

/-- **Removing one point from an open preconnected set of a manifold of dimension at least two
leaves it preconnected.**  This is the inductive step of
`Milnor.isPreconnected_compl_finite`, and the place where `2 ≤ m` enters.

Let `V₁, V₂` be open sets covering `U \ {p}` and meeting it, and let `B` be a chart ball about `p`
inside `U` (`Milnor.exists_chartBall_subset`).  The punctured ball `B \ {p}` is connected
(`Milnor.isConnected_chartBall_diff_singleton`), so either it meets both `V₁` and `V₂` — and then it
already contains a point of `V₁ ∩ V₂`, which is what has to be produced — or it lies in one of them,
say in `V₁`.  In that case `V₁ ∪ B` and `V₂ \ {p}` are open (`{p}` is closed because every
manifold is `T1`, `ModelWithCorners.t1Space`), they cover the whole of `U`, and each meets `U`; so
preconnectedness of `U` produces a point `z ∈ U ∩ (V₁ ∪ B) ∩ (V₂ \ {p})`, and `z` lies in `V₁`
either outright or through `B \ {p} ⊆ V₁`.  That `z` is the required point of
`(U \ {p}) ∩ V₁ ∩ V₂`. -/
theorem isPreconnected_diff_singleton_of_isOpen (hm : finrank ℝ E = m) (hm2 : 2 ≤ m)
    [I.Boundaryless] {U : Set M} (hUo : IsOpen U) (hU : IsPreconnected U) (p : M) :
    IsPreconnected (U \ {p}) := by
  have : T1Space M := I.t1Space M
  by_cases hp : p ∈ U
  · obtain ⟨R, hR, hRt, hBU⟩ := exists_chartBall_subset (I := I) hUo hp
    have hBo : IsOpen (chartBall I p R) := isOpen_chartBall p R
    have hpB : p ∈ chartBall I p R := self_mem_chartBall p hR
    have hBpre : IsPreconnected (chartBall I p R \ {p}) :=
      (isConnected_chartBall_diff_singleton hm hm2 hR hRt p).2
    have hBsub : chartBall I p R \ {p} ⊆ U \ {p} := fun z hz => ⟨hBU hz.1, hz.2⟩
    have main : ∀ W₁ W₂ : Set M, IsOpen W₁ → IsOpen W₂ → U \ {p} ⊆ W₁ ∪ W₂ →
        ((U \ {p}) ∩ W₂).Nonempty → chartBall I p R \ {p} ⊆ W₁ →
        ((U \ {p}) ∩ (W₁ ∩ W₂)).Nonempty := by
      intro W₁ W₂ hW₁ hW₂ hsub h₂ hBW
      obtain ⟨z₂, hz₂U, hz₂⟩ := h₂
      obtain ⟨z, hzU, hz1, hz2⟩ :=
        hU (W₁ ∪ chartBall I p R) (W₂ \ {p}) (hW₁.union hBo) (hW₂.sdiff isClosed_singleton)
          (fun w hw => by
            by_cases hwp : w = p
            · exact Or.inl (Or.inr (by rw [hwp]; exact hpB))
            · rcases hsub ⟨hw, hwp⟩ with h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inr ⟨h, hwp⟩)
          ⟨p, hp, Or.inr hpB⟩ ⟨z₂, hz₂U.1, hz₂, hz₂U.2⟩
      refine ⟨z, ⟨hzU, hz2.2⟩, ?_, hz2.1⟩
      rcases hz1 with h | h
      · exact h
      · exact hBW ⟨h, hz2.2⟩
    intro V₁ V₂ hV₁ hV₂ hsub h₁ h₂
    by_cases hb₁ : ((chartBall I p R \ {p}) ∩ V₁).Nonempty
    · by_cases hb₂ : ((chartBall I p R \ {p}) ∩ V₂).Nonempty
      · obtain ⟨z, hz, hz'⟩ := hBpre V₁ V₂ hV₁ hV₂ (fun w hw => hsub (hBsub hw)) hb₁ hb₂
        exact ⟨z, hBsub hz, hz'⟩
      · refine main V₁ V₂ hV₁ hV₂ hsub h₂ fun w hw => ?_
        rcases hsub (hBsub hw) with h | h
        · exact h
        · exact absurd ⟨w, hw, h⟩ hb₂
    · have hsub2 : chartBall I p R \ {p} ⊆ V₂ := by
        intro w hw
        rcases hsub (hBsub hw) with h | h
        · exact absurd ⟨w, hw, h⟩ hb₁
        · exact h
      obtain ⟨z, hz, hz2, hz1⟩ := main V₂ V₁ hV₂ hV₁ (by rwa [union_comm]) h₁ hsub2
      exact ⟨z, hz, hz1, hz2⟩
  · rw [sdiff_singleton_eq_self hp]
    exact hU

/-- **The complement of a finite set in a preconnected manifold of dimension at least two is
preconnected.**  Induction on the finite set: the empty set leaves `M` itself, and one further point
is removed by `Milnor.isPreconnected_diff_singleton_of_isOpen`, applicable because the complement of
a finite set is open (finite sets are closed, every manifold being `T1`). -/
theorem isPreconnected_compl_finite (hm : finrank ℝ E = m) (hm2 : 2 ≤ m) [I.Boundaryless]
    [PreconnectedSpace M] {P : Set M} (hP : P.Finite) : IsPreconnected (Pᶜ : Set M) := by
  have : T1Space M := I.t1Space M
  induction P, hP using Set.Finite.induction_on with
  | empty => rw [compl_empty]; exact isPreconnected_univ
  | @insert a s _ hs ih =>
    have hc : (insert a s)ᶜ = (sᶜ : Set M) \ {a} := by
      ext z
      simp only [mem_compl_iff, mem_insert_iff, Set.mem_sdiff, mem_singleton_iff, not_or]
      tauto
    rw [hc]
    exact isPreconnected_diff_singleton_of_isOpen (I := I) hm hm2 hs.isClosed.isOpen_compl ih a

/-- **The complement of a finite set in a connected manifold of dimension at least two is
connected.**  This is the plan's `isConnected_diff_finite`, in the form with the complement of a
set; nonemptiness is `Milnor.nonempty_compl_finite` and preconnectedness is
`Milnor.isPreconnected_compl_finite`.  Both `2 ≤ m` and the connectedness of `M` are needed, and
`2 ≤ m` is sharp: `ℝ \ {0}` is disconnected. -/
theorem isConnected_compl_finite (hm : finrank ℝ E = m) (hm2 : 2 ≤ m) [I.Boundaryless]
    [ConnectedSpace M] {P : Set M} (hP : P.Finite) : IsConnected (Pᶜ : Set M) :=
  ⟨nonempty_compl_finite (I := I) hm (by omega) hP,
    isPreconnected_compl_finite (I := I) hm hm2 hP⟩

/-- **The complement of a finite set in a connected manifold of dimension at least two is
connected**, written as `M \ P` in the notation of the plan `Milnor/Exposition/PlanMod2.md`. -/
theorem isConnected_diff_finite (hm : finrank ℝ E = m) (hm2 : 2 ≤ m) [I.Boundaryless]
    [ConnectedSpace M] {P : Set M} (hP : P.Finite) : IsConnected ((univ : Set M) \ P) := by
  rw [← compl_eq_univ_sdiff]
  exact isConnected_compl_finite (I := I) hm hm2 hP

/-! ### The complement of the other points of a finite set -/

/-- **The complement of the other points of a finite set is connected, hence is the connected
component `Milnor.compl'`.**  For a finite `N` in a preconnected manifold with `2 ≤ m` the set
`compl' N x`, the connected component of `x` in the complement of `N \ {x}`, is that whole
complement.  Applied to a framed `0`-manifold `F` with `N := F.N` and `hN := F.finite_N` this is the
plan's `compl'_eq_diff`: the sets in which the moving machinery of `Milnor/Chapter7/Reach.lean`
operates are exactly the complements of finite sets, so the connectedness and non-orientability
statements of Stage 5 apply to them. -/
theorem compl'_eq_compl (hm : finrank ℝ E = m) (hm2 : 2 ≤ m) [I.Boundaryless] [PreconnectedSpace M]
    {N : Set M} (hN : N.Finite) (x : M) : compl' N x = ((N \ {x})ᶜ : Set M) :=
  (isPreconnected_compl_finite (I := I) hm hm2 hN.sdiff).connectedComponentIn (by simp)

/-- **`Milnor.compl' N x` is `M \ (N \ {x})`**, the form in which the plan
`Milnor/Exposition/PlanMod2.md` states `compl'_eq_diff`. -/
theorem compl'_eq_diff (hm : finrank ℝ E = m) (hm2 : 2 ≤ m) [I.Boundaryless] [PreconnectedSpace M]
    {N : Set M} (hN : N.Finite) (x : M) : compl' N x = ((univ : Set M) \ (N \ {x})) := by
  rw [compl'_eq_compl (I := I) hm hm2 hN, compl_eq_univ_sdiff]

/-! ### Locally constant functions on a connected set -/

section LocallyConstant

variable {X : Type*} [TopologicalSpace X]

/-- **A locally constant function on a preconnected open set is constant on it.**  The target is an
arbitrary type, with no topology on it: the two orientations of the model space, the case applied
below, carry none, so Mathlib's `IsPreconnected.constant` — which wants a discrete topological
space — is unavailable and the argument is run by hand.  The set of points of `S` where the function
takes the value it has at one chosen point of `S`, and the set of points of `S` where it does not,
are open by local constancy, are disjoint, and cover `S`, and the first meets `S`; so
`IsPreconnected.subset_left_of_subset_union` puts all of `S` inside the first. -/
theorem eq_of_eventually_eq_of_isPreconnected {α : Type*} {S : Set X} (hSo : IsOpen S)
    (hS : IsPreconnected S) {f : X → α} (hf : ∀ z ∈ S, ∀ᶠ y in 𝓝 z, f y = f z) {x y : X}
    (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  have hu : IsOpen {z : X | z ∈ S ∧ f z = f y} := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzS, hzy⟩
    filter_upwards [hf z hzS, hSo.mem_nhds hzS] with w hw hwS
    exact ⟨hwS, hw.trans hzy⟩
  have hv : IsOpen {z : X | z ∈ S ∧ f z ≠ f y} := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzS, hzy⟩
    filter_upwards [hf z hzS, hSo.mem_nhds hzS] with w hw hwS
    exact ⟨hwS, fun h => hzy (hw.symm.trans h)⟩
  have hdisj : Disjoint {z : X | z ∈ S ∧ f z = f y} {z : X | z ∈ S ∧ f z ≠ f y} := by
    rw [Set.disjoint_left]
    rintro z ⟨-, h1⟩ ⟨-, h2⟩
    exact h2 h1
  have hcover : S ⊆ {z : X | z ∈ S ∧ f z = f y} ∪ {z : X | z ∈ S ∧ f z ≠ f y} := by
    intro z hz
    by_cases h : f z = f y
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, h⟩
  exact (hS.subset_left_of_subset_union hu hv hdisj hcover ⟨y, hy, hy, rfl⟩ hx).2

end LocallyConstant

/-! ### Ball-coherent families of orientations -/

/-- A family of orientations of the tangent spaces of `M` is **ball-coherent on `C`** if transport
along every ball hop that runs inside `C` — one whose closed chart ball is contained in `C`, in the
sense of `Milnor.BallHop.RunsIn` — carries the value of the family at the source of the hop to its
value at the target.  Only the values on `C` are constrained, both ends of such a hop lying in `C`.

Every orientation of `M` is ball-coherent on every set (`Milnor.Orient.isBallCoherentOn`), so it is
a weakening of being an orientation; the point of the notion is the converse direction.  A family
obtained on the complement of a finite set by transporting one orientation along ball chains inside
that complement is ball-coherent there, and ball coherence on that complement is all that is needed
to produce an orientation of the whole manifold (`Milnor.extend_ballCoherent`). -/
def IsBallCoherentOn (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    (or : M → Orientation ℝ E (Fin m)) (C : Set M) : Prop :=
  ∀ ⦃x y : M⦄ (b : BallHop I x y), b.RunsIn C → b.transport (or x) = or y

/-- **Every orientation of `M` is ball-coherent on every set.**  This is
`Milnor.BallHop.transport_or`, the key lemma of `Milnor/Chapter7/OrientBall.lean`: no hypothesis on
the orientation beyond its being a `Milnor.Orient` is needed, since the ball of a ball hop is
connected. -/
theorem Orient.isBallCoherentOn [I.Boundaryless] (hm : finrank ℝ E = m) (o : Orient I M m)
    (C : Set M) : IsBallCoherentOn I o.or C := by
  intro x y b _
  exact b.transport_or hm o

/-- **Near a point of an open set a ball-coherent family is the transport of its value at that
point.**  Inside the set there is a chart ball about that point whose *closed* chart ball also lies
in the set (`Milnor.exists_closedChartBall_subset`); for each `y` of that ball the ball hop from
the centre to `y` runs inside the set, and ball coherence applied to that hop says exactly that the
value at `y` is the transport of the value at the centre through the chart at the centre
(`Milnor.BallHop.transport_ofCentre`). -/
theorem IsBallCoherentOn.eventually_eq_orTransport [I.Boundaryless]
    {or : M → Orientation ℝ E (Fin m)} {C : Set M} (hor : IsBallCoherentOn I or C) (hC : IsOpen C)
    {x : M} (hx : x ∈ C) :
    ∀ᶠ y in 𝓝 x, y ∈ C ∧ or y = orTransport I x y (or x) := by
  obtain ⟨R, hR, hRt, hcl⟩ := exists_closedChartBall_subset (I := I) x (hC.mem_nhds hx)
  have hRb : Metric.ball (extChartAt I x x) R ⊆ (extChartAt I x).target :=
    Metric.ball_subset_closedBall.trans hRt
  filter_upwards [(isOpen_chartBall (I := I) x R).mem_nhds (self_mem_chartBall (I := I) x hR)]
    with y hy
  refine ⟨hcl (chartBall_subset_closedChartBall hy), ?_⟩
  have hb := hor (BallHop.ofCentre hR hRb hy) ⟨hRt, hcl⟩
  rw [BallHop.transport_ofCentre hR hRb hy] at hb
  exact hb.symm

/-- **The value of a ball-coherent family, read back through a fixed chart, is locally constant.**
Let `or` be ball-coherent on the open set `C`, let `p` be any point of `M`, and let `y₀` be a
point of `C` lying in the source of the chart centred at `p`.  Then the assignment
`y ↦ orTransport I p y (or y)` — the value of the family at `y`, transported back to `p` through the
chart at `p` — is constant on a neighbourhood of `y₀`.

This is the one place where the transition cocycle lemma
`Milnor.eventually_jacSign_mul_jacSign_eq` of `Milnor/Chapter7/BallChainSign.lean` is used, and the
reason it was proved.  By ball coherence the value at a nearby `y` is
`signAct (jacSign I y₀ y) (or y₀)` (`Milnor.orTransport_eq_signAct`), so its transport to `p` is
`signAct (jacSign I p y * jacSign I y₀ y) (or y₀)`.  Neither Jacobian sign is a continuous function
of `y` — each is the determinant sign of a fixed chart read through the chart at `y`, which jumps
about — but their product is locally constant, and at `y = y₀` the second factor is `1`
(`Milnor.jacSign_self`), which leaves exactly the value at `y₀`. -/
theorem IsBallCoherentOn.eventually_orTransport_eq (hm : finrank ℝ E = m) [I.Boundaryless]
    {or : M → Orientation ℝ E (Fin m)} {C : Set M} (hor : IsBallCoherentOn I or C) (hC : IsOpen C)
    (p : M) {y₀ : M} (hy₀C : y₀ ∈ C) (hy₀p : y₀ ∈ (extChartAt I p).source) :
    ∀ᶠ y in 𝓝 y₀, orTransport I p y (or y) = orTransport I p y₀ (or y₀) := by
  filter_upwards [hor.eventually_eq_orTransport hC hy₀C,
    eventually_jacSign_mul_jacSign_eq (I := I) hm hy₀p (mem_extChartAt_source (I := I) y₀),
    (isOpen_extChartAt_source (I := I) p).mem_nhds hy₀p,
    (isOpen_extChartAt_source (I := I) y₀).mem_nhds (mem_extChartAt_source (I := I) y₀)]
    with y hy1 hy2 hy3 hy4
  rw [orTransport_eq_signAct hm hy3, hy1.2, orTransport_eq_signAct hm hy4,
    ← signAct_mul (jacSign_eq_one_or_neg_one hm hy3) (jacSign_eq_one_or_neg_one hm hy4), hy2,
    jacSign_self, mul_one, orTransport_eq_signAct hm hy₀p]

/-- **A ball-coherent family on the complement of a finite set has a well-defined limit value at
every point.**  For every point `p` of the manifold — a puncture or not — there is one orientation
`a` with `orTransport I p y (or y) = a` for all `y` in a punctured neighbourhood of `p`: the value
of the family at a point near `p`, read back through the chart at `p`, does not depend on which
nearby point is used.  This is the well-definedness on which `Milnor.extend_ballCoherent` rests.

Take a chart ball `B` about `p` inside the complement of `P \ {p}` — open because a finite set in a
manifold is closed (`ModelWithCorners.t1Space`) — by `Milnor.exists_chartBall_subset`.  Then
`B \ {p}` lies in the complement of `P`, so the assignment is locally constant on `B \ {p}`
(`Milnor.IsBallCoherentOn.eventually_orTransport_eq`).  And `B \ {p}` is connected, which is
`Milnor.isConnected_chartBall_diff_singleton` and the only place where `2 ≤ m` is used, and in
particular nonempty, so the assignment is constant on it
(`Milnor.eq_of_eventually_eq_of_isPreconnected`). -/
theorem exists_eventually_orTransport_eq (hm : finrank ℝ E = m) (hm2 : 2 ≤ m) [I.Boundaryless]
    {P : Set M} (hP : P.Finite) {or : M → Orientation ℝ E (Fin m)}
    (hor : IsBallCoherentOn I or (Pᶜ : Set M)) (p : M) :
    ∃ a : Orientation ℝ E (Fin m), ∀ᶠ y in 𝓝[≠] p, orTransport I p y (or y) = a := by
  have : T1Space M := I.t1Space M
  have hUo : IsOpen ((P \ {p})ᶜ : Set M) := hP.sdiff.isClosed.isOpen_compl
  have hpU : p ∈ ((P \ {p})ᶜ : Set M) := by simp
  obtain ⟨R, hR, hRt, hBU⟩ := exists_chartBall_subset (I := I) hUo hpU
  have hSo : IsOpen (chartBall I p R \ {p}) :=
    (isOpen_chartBall (I := I) p R).sdiff isClosed_singleton
  have hSP : chartBall I p R \ {p} ⊆ (Pᶜ : Set M) := by
    intro z hz
    simp only [mem_compl_iff]
    intro hzP
    exact hBU hz.1 ⟨hzP, hz.2⟩
  have hPco : IsOpen (Pᶜ : Set M) := hP.isClosed.isOpen_compl
  have hconn : IsConnected (chartBall I p R \ {p}) :=
    isConnected_chartBall_diff_singleton hm hm2 hR hRt p
  obtain ⟨y₀, hy₀⟩ := hconn.nonempty
  refine ⟨orTransport I p y₀ (or y₀), ?_⟩
  have hconst : ∀ y ∈ chartBall I p R \ {p},
      orTransport I p y (or y) = orTransport I p y₀ (or y₀) := fun y hy =>
    eq_of_eventually_eq_of_isPreconnected (f := fun z => orTransport I p z (or z)) hSo hconn.2
      (fun z hz => hor.eventually_orTransport_eq hm hPco p (hSP hz)
        (chartBall_subset_source hz.1)) hy hy₀
  rw [eventually_nhdsWithin_iff]
  filter_upwards [(isOpen_chartBall (I := I) p R).mem_nhds (self_mem_chartBall (I := I) p hR)]
    with y hyB hyne
  exact hconst y ⟨hyB, hyne⟩

/-- **A property that holds near a point of a manifold of positive dimension holds at some other
point.**  Every neighbourhood of a point contains an open set about it, which is infinite
(`Milnor.infinite_of_isOpen`) and therefore contains a point different from the given one — no point
of such a manifold is isolated.  This is what identifies the limit value of
`Milnor.exists_eventually_orTransport_eq` at a point off the punctures with the value of the family
itself there. -/
theorem exists_ne_of_eventually (hm : finrank ℝ E = m) (hm0 : 0 < m) [I.Boundaryless] {x : M}
    {Q : M → Prop} (hQ : ∀ᶠ y in 𝓝 x, Q y) : ∃ y, y ≠ x ∧ Q y := by
  obtain ⟨V, hV, hVQ⟩ : ∃ V ∈ 𝓝 x, ∀ y ∈ V, Q y := ⟨{y | Q y}, hQ, fun _ h => h⟩
  obtain ⟨W, hWV, hWo, hxW⟩ := mem_nhds_iff.1 hV
  obtain ⟨y, hyW, hyx⟩ :=
    (infinite_of_isOpen (I := I) hm hm0 hWo ⟨x, hxW⟩).exists_notMem_finite (Set.finite_singleton x)
  exact ⟨y, hyx, hVQ y (hWV hyW)⟩

/-! ### The extension lemma -/

/-- **A ball-coherent family on the complement of a finite set extends to a transport section on the
whole manifold**, for `2 ≤ m`: there is a family `or'` of orientations of all the tangent spaces of
`M` agreeing with `or` off `P` and satisfying `Milnor.IsTransportSection`, hence is an orientation
of `M` by `Milnor.Orient.ofTransportSection`.  This is the first of the two results of the second
half of Stage 5 of the plan `Milnor/Exposition/PlanMod2.md`.

The value at a point `p` is the value of the family at a point near `p`, transported back to `p`
through the chart at `p`; `Milnor.exists_eventually_orTransport_eq` supplies it and its independence
of the nearby point, where the transition cocycle lemma and the connectedness of a punctured
chart ball are used.  At a point `x` off `P` this value is `or x` itself
(`Milnor.exists_ne_of_eventually` produces a nearby point different from `x`, and transport across
one chart is an involution).  The transport-section condition is then checked at every point `x` at
once, punctured or not: for `y` near `x` and different from `x` the point `y` misses `P`, so `or' y`
is `or y`, and `or' x` is by construction the transport of `or y` back to `x`, which the transport
from `x` to `y` carries back to `or y` — again because transport across one chart is an involution;
and for `y = x` the assertion is that transport from `x` to `x` is the identity. -/
theorem extend_ballCoherent (hm : finrank ℝ E = m) (hm2 : 2 ≤ m) [I.Boundaryless] {P : Set M}
    (hP : P.Finite) {or : M → Orientation ℝ E (Fin m)}
    (hor : IsBallCoherentOn I or (Pᶜ : Set M)) :
    ∃ or' : M → Orientation ℝ E (Fin m), IsTransportSection I or' ∧ ∀ x ∉ P, or' x = or x := by
  have : T1Space M := I.t1Space M
  have hPco : IsOpen (Pᶜ : Set M) := hP.isClosed.isOpen_compl
  choose a ha using exists_eventually_orTransport_eq (I := I) hm hm2 hP hor
  have hoff : ∀ x ∉ P, a x = or x := by
    intro x hx
    obtain ⟨y, hyx, hy1, hy2⟩ := exists_ne_of_eventually (I := I) hm (by omega)
      ((eventually_nhdsWithin_iff.1 (ha x)).and (hor.eventually_eq_orTransport hPco hx))
    have h3 := hy1 hyx
    rw [hy2.2, orTransport_involutive hm x y (or x)] at h3
    exact h3.symm
  refine ⟨a, ?_, hoff⟩
  intro x
  have hnb : ((P \ {x})ᶜ : Set M) ∈ 𝓝 x := hP.sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [eventually_nhdsWithin_iff.1 (ha x), hnb] with y hy1 hy2
  by_cases hyx : y = x
  · rw [hyx, transport_self]
  · rw [hoff y fun h => hy2 ⟨h, hyx⟩, ← hy1 hyx, orTransport_involutive hm x y (or y)]

/-! ### The punctured dichotomy -/

/-- **A reversing loop of chart balls at `x₀` missing `P`**: a loop of chart hops at `x₀`, each of
them coming from a ball hop whose closed chart ball avoids `P` — that is,
`Milnor.ChartChain.IsBallIn` for the complement of `P` — whose `Milnor.chainSign` is `-1`,
equivalently along which transport reverses every orientation
(`Milnor.ChartChain.reverses_iff_chainSign`).

This is the interface that the remaining stages of the plan `Milnor/Exposition/PlanMod2.md` consume.
`P` is the set of the *other* points of a framed `0`-manifold and a framed point is slid around
such a loop, returning to where it started with its frame reversed while no ball of the loop ever
meets another point of the framed set — indeed, in a Hausdorff manifold, not even the closure of a
ball does (`Milnor.BallHop.RunsIn.closure_subset`), which is what the machinery that moves a framed
point inside a ball requires. -/
def HasReversingBallLoop (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] (P : Set M) (x₀ : M) :
    Prop :=
  ∃ c : ChartChain I x₀ x₀, c.IsBallIn (Pᶜ : Set M) ∧ chainSign c = -1

/-- **The punctured dichotomy.**  A connected manifold of dimension at least two that is *not*
orientable has, at every point `x₀` lying off a finite set `P`, a loop of chart balls at `x₀` which
misses `P` and whose sign is `-1`: deleting finitely many points destroys neither the connectedness
of the manifold (`Milnor.isConnected_compl_finite`) nor its non-orientability.  It is the last piece
of new mathematics of the plan `Milnor/Exposition/PlanMod2.md`, and the hypothesis that every
statement of its Stages 7 and 8 takes as given.

The proof is by contradiction.  If there were no such loop, every `P`-avoiding ball loop at `x₀`
would have sign `1` (`Milnor.chainSign_eq_one_or_neg_one`), so the transport of one orientation `o₀`
at `x₀` along a `P`-avoiding ball chain would not depend on the chain: for two such chains the first
followed by the reverse of the second is a `P`-avoiding ball loop, whose transport is therefore the
identity, and transport along the reverse of the second chain is injective
(`Milnor.ChartChain.transport_injective`).  Since the complement of `P` is connected and any two of
its points are joined by a `P`-avoiding ball chain (`Milnor.exists_isBallIn`), this defines
a family of orientations on that complement, ball-coherent there because a ball hop running inside
the complement extends such a chain to another one.  By `Milnor.extend_ballCoherent` the family
extends to a transport section on all of `M`, and `Milnor.Orient.ofTransportSection` turns that
into an orientation of `M`, against the hypothesis.  Both `2 ≤ m` and the connectedness of `M` are
used, the first only through the connectedness of the complement of `P` and through the extension
lemma. -/
theorem hasReversingBallLoop_of_not_isOrientable (hm : finrank ℝ E = m) (hm2 : 2 ≤ m)
    [I.Boundaryless] [ConnectedSpace M] (hnor : ¬ IsOrientable I M m) {P : Set M} (hP : P.Finite)
    {x₀ : M} (hx₀ : x₀ ∉ P) : HasReversingBallLoop I P x₀ := by
  by_contra hno
  have hone : ∀ c : ChartChain I x₀ x₀, c.IsBallIn (Pᶜ : Set M) → chainSign c = 1 := by
    intro c hc
    rcases chainSign_eq_one_or_neg_one hm c with h | h
    · exact h
    · exact absurd ⟨c, hc, h⟩ hno
  have : T1Space M := I.t1Space M
  have hCo : IsOpen (Pᶜ : Set M) := hP.isClosed.isOpen_compl
  have hCconn : IsConnected (Pᶜ : Set M) := isConnected_compl_finite (I := I) hm hm2 hP
  have hx₀C : x₀ ∈ (Pᶜ : Set M) := hx₀
  obtain ⟨o₀⟩ := nonempty_orientation (E := E) hm
  have hch : ∀ y : M, ∃ c : ChartChain I x₀ y, y ∈ (Pᶜ : Set M) → c.IsBallIn (Pᶜ : Set M) := by
    intro y
    by_cases hy : y ∈ (Pᶜ : Set M)
    · obtain ⟨c, hc⟩ := exists_isBallIn (I := I) hCo hCconn.2 hx₀C hy
      exact ⟨c, fun _ => hc⟩
    · exact ⟨(nonempty_chartChain (I := I) x₀ y).some, fun h => absurd h hy⟩
  have key : ∀ {y : M} {c d : ChartChain I x₀ y}, c.IsBallIn (Pᶜ : Set M) →
      d.IsBallIn (Pᶜ : Set M) → c.transport o₀ = d.transport o₀ := by
    intro y c d hc hd
    have h1 : (c.comp d.reverse).transport o₀ = o₀ := by
      rw [(c.comp d.reverse).transport_eq_signAct hm, hone _ (hc.comp hd.reverse), signAct_one]
    rw [ChartChain.transport_comp] at h1
    exact ChartChain.transport_injective hm d.reverse
      (h1.trans (ChartChain.transport_reverse hm d o₀).symm)
  have hballcoh : IsBallCoherentOn I (fun y => (hch y).choose.transport o₀) (Pᶜ : Set M) := by
    intro x y b hb
    have hxC : x ∈ (Pᶜ : Set M) := hb.subset b.mem_left
    have hyC : y ∈ (Pᶜ : Set M) := hb.subset b.mem_right
    show b.transport ((hch x).choose.transport o₀) = (hch y).choose.transport o₀
    rw [← ChartChain.transport_comp_hop]
    exact key (((hch x).choose_spec hxC).snoc b hb) ((hch y).choose_spec hyC)
  obtain ⟨or', hts, -⟩ := extend_ballCoherent (I := I) hm hm2 hP hballcoh
  exact hnor ⟨Orient.ofTransportSection hm hts⟩

end Milnor
