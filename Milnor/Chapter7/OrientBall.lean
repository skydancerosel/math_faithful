import Milnor.Chapter7.Orientable

/-!
# Orientation transport through round balls, and the exact dichotomy

Milnor's remark at the end of §7 (p. 50) is that for a *connected non-orientable* manifold the
smooth maps to a sphere are classified by the degree modulo `2`; the content of the remark is that
such a manifold carries a loop along which a frame comes back reversed.  In
`Milnor.Chapter7.Orientable` that loop is produced as a chain of *charts*, and only one half of the
dichotomy is unconditional: the converse ("an orientation forbids reversing loops") needs the
orientation to be coherent with each chart on the *whole* of that chart's source
(`Milnor.IsChartCoherent`), and the module docstring of that file exhibits a manifold — `ℝ` with a
chart reversed on a far component of its source — where a chain of charts reverses although the
manifold is orientable.  The culprit is that the source of a chart may be disconnected.

This file replaces charts by **round balls** and thereby removes the defect.

* **Chart balls.**  `Milnor.chartBall I c R` is the preimage under the chart centred at `c` of the
  ball of radius `R` about the chart image of `c`.  When that ball is contained in the target of the
  chart, the chart ball is the homeomorphic image of a ball, hence connected
  (`Milnor.isPreconnected_chartBall`).  This is the one property that a chart source lacks and that
  makes everything below work.

* **Ball hops.**  A `Milnor.BallHop I x y` is such a ball — a centre `hub`, a radius `rad > 0`,
  the containment of the ball in the chart's target — together with the requirement that both `x`
  and `y` lie in the chart ball.  A ball hop is in particular a chart hop
  (`Milnor.BallHop.toChartHop`), and its transport of orientations is by definition the transport of
  that chart hop, so the whole transport algebra of `Milnor.Chapter7.OrientTransport` applies
  verbatim.  Reflexivity, symmetry and `Milnor.BallHop.transport_symm_transport` are inherited in
  the same way.

* **The key lemma: every orientation is ball-coherent** (`Milnor.BallHop.transport_or`).  For an
  orientation `o` of `M` and a ball hop from `x` to `y`, the transport of `o.or x` along the hop is
  `o.or y`.  The proof is the one thing in this file that has no chart-level counterpart, and is the
  reason the dichotomy becomes exact.  The function `z ↦ orSign (o.or z) (o.or c) (dφ_c|_z)` on a
  chart ball about `c` takes only the values `1` and `-1` (the derivative of a chart is invertible),
  is locally constant — this is `Milnor.eventually_signAt_eq_of_contMDiffOn`, applied to the chart
  `φ_c : M → E` regarded as a map of manifolds with the *constant* orientation
  `Milnor.orientConst` on the model space, and it is there that the continuity field `Orient.cont`
  enters through `Milnor.eventually_orSign_eq_of_continuousAt` — and equals `1` at `c`.  A locally
  constant function on a connected set is constant (`IsPreconnected.constant`, the target `ℤ` being
  discrete), so the sign is `1` on the whole ball, i.e. the orientation at every point of the ball
  is the transport of the orientation at the centre.  For a chart source this conclusion is false,
  which is exactly the counterexample of `Milnor.Chapter7.Orientable`.

* **Ball chains.**  Rather than a second inductive type of chains, a chain of ball hops is a chart
  chain together with the predicate `Milnor.ChartChain.IsBall`, so that composition, reversal,
  transport, `ChartChain.transport_comp`, `ChartChain.transport_reverse`,
  `ChartChain.transport_neg` and `ChartChain.Reverses` are literally the chart-level notions.  What
  has to be proved is only that the predicate is closed under the constructions
  (`Milnor.ChartChain.IsBall.hop`, `.comp`, `.reverse`).  Reachability by ball chains
  (`Milnor.BallReachable`) is open and closed by the chart-level argument with one change: the
  neighbourhood used is a chart ball about the point instead of the whole chart source
  (`Milnor.eventually_ballReachable`); hence a connected manifold is ball-chain connected
  (`Milnor.ballReachable_of_preconnectedSpace`).

* **The exact dichotomy** (`Milnor.isOrientable_iff_forall_not_reverses_isBall`).  For connected
  `M` and any base point, `M` is orientable if and only if no ball-chain-loop at that point
  reverses.  The forward direction is now unconditional, by the key lemma; the chart-level
  statement `Milnor.exists_isChartCoherent_iff_forall_not_reverses` needed the auxiliary notion of
  a chart-coherent orientation for this.  The converse is the chart-level argument verbatim — a
  fixed orientation is transported from the base point along a ball chain, unambiguously because
  two ball chains differ by a ball-chain-loop — with one change: the resulting family is a
  transport section because a point near `x` is joined to `x` by a *ball* hop through the chart at
  `x` (`Milnor.isTransportSection_ballTransportFrom`), where the chart-level proof used the whole
  chart source.

* **The form the endgame needs**
  (`Milnor.exists_isBall_reverses_of_not_isOrientable`).  If a connected manifold is not
  orientable, then at every point there is a ball-chain-loop whose transport reverses *every*
  orientation there.  This supersedes `Milnor.exists_reverses_of_not_isOrientable` for the purposes
  of the mod `2` theorem (plan `Milnor/Exposition/PlanMod2.md`, §3.3): the loops it produces run
  through round balls, which is what the moving and cancelling machinery of the framed-cobordism
  argument can follow, and — unlike the chart-level statement — its converse holds, so the
  existence of a reversing ball loop is a genuine obstruction to orientability rather than merely a
  consequence of a badly chosen atlas.

Boundarylessness of `I` is assumed on the individual declarations that need it, for two independent
reasons and nowhere else.  First, a ball inside the target of a chart has to exist at all: for a
model with boundary the chart image of a point may lie on the boundary of the target, and then no
ball about it is contained in the target.  This is `Milnor.exists_radius`, and with it everything
that asserts the existence of a ball hop — `Milnor.BallHop.refl`, ball reachability, and hence the
converse half of the dichotomy.  Secondly, the local constancy of the sign of a chart derivative,
`Milnor.eventually_orSign_extChartAt_eq`, inherits the hypothesis from
`Milnor.eventually_signAt_eq_of_contMDiffOn`, which uses that the target of a chart is open; with
it the key lemma and the forward half of the dichotomy.  What needs boundarylessness *not* is the
whole geometry of chart balls up to `Milnor.isPreconnected_chartBall`, the definitions of
`Milnor.chartBall`, `Milnor.BallHop` and `Milnor.ChartChain.IsBall`, and the entire transport
algebra of ball hops and ball chains.  Hausdorffness, second countability and positivity of the
dimension are nowhere needed, and `M` may be empty.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {m : ℕ}

/-! ### Chart balls -/

/-- **The chart ball** of radius `R` about `c`: the points of the source of the chart centred at
`c` whose chart image lies at distance less than `R` from the chart image of `c`.  Unlike the source
of a chart it is connected as soon as the ball of radius `R` lies in the chart's target
(`Milnor.isPreconnected_chartBall`), and that is the whole point of this file. -/
def chartBall (I : ModelWithCorners ℝ E H) (c : M) (R : ℝ) : Set M :=
  (extChartAt I c).source ∩ (extChartAt I c) ⁻¹' Metric.ball (extChartAt I c c) R

/-- Membership in a chart ball, unfolded. -/
theorem mem_chartBall {c : M} {R : ℝ} {z : M} :
    z ∈ chartBall I c R ↔ z ∈ (extChartAt I c).source ∧
      dist (extChartAt I c z) (extChartAt I c c) < R := by
  simp only [chartBall, mem_inter_iff, mem_preimage, Metric.mem_ball]

/-- A chart ball lies in the source of its chart. -/
theorem chartBall_subset_source {c : M} {R : ℝ} :
    chartBall I c R ⊆ (extChartAt I c).source := inter_subset_left

/-- A chart ball is open, the chart being continuous on its open source. -/
theorem isOpen_chartBall (c : M) (R : ℝ) : IsOpen (chartBall I c R) :=
  (continuousOn_extChartAt c).isOpen_inter_preimage (isOpen_extChartAt_source c) Metric.isOpen_ball

/-- The centre of a chart ball of positive radius belongs to it. -/
theorem self_mem_chartBall (c : M) {R : ℝ} (hR : 0 < R) : c ∈ chartBall I c R :=
  ⟨mem_extChartAt_source c, Metric.mem_ball_self hR⟩

/-- A chart ball of positive radius is a neighbourhood of its centre. -/
theorem chartBall_mem_nhds (c : M) {R : ℝ} (hR : 0 < R) : chartBall I c R ∈ 𝓝 c :=
  (isOpen_chartBall c R).mem_nhds (self_mem_chartBall c hR)

/-- **A chart ball is the image of a ball** under the inverse of the chart, provided the ball lies
in the chart's target. -/
theorem chartBall_eq_image {c : M} {R : ℝ}
    (hR : Metric.ball (extChartAt I c c) R ⊆ (extChartAt I c).target) :
    chartBall I c R = (extChartAt I c).symm '' Metric.ball (extChartAt I c c) R := by
  ext z
  constructor
  · intro hz
    exact ⟨extChartAt I c z, hz.2, (extChartAt I c).left_inv hz.1⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨(extChartAt I c).map_target (hR hu), ?_⟩
    show extChartAt I c ((extChartAt I c).symm u) ∈ Metric.ball (extChartAt I c c) R
    rw [(extChartAt I c).right_inv (hR hu)]
    exact hu

/-- **A chart ball is connected**: a ball in a normed space is convex, hence connected, and the
inverse of the chart is continuous on the chart's target, which contains the ball. -/
theorem isPreconnected_chartBall {c : M} {R : ℝ}
    (hR : Metric.ball (extChartAt I c c) R ⊆ (extChartAt I c).target) :
    IsPreconnected (chartBall I c R) := by
  rw [chartBall_eq_image hR]
  exact (convex_ball (extChartAt I c c) R).isPreconnected.image _
    ((continuousOn_extChartAt_symm c).mono hR)

/-- **Every point is the centre of a chart ball.**  For a boundaryless model the target of a chart
is open, so it contains a ball about the chart image of the centre.  This is the first place where
boundarylessness of `I` is used, and the reason it is used at all. -/
theorem exists_radius [I.Boundaryless] (c : M) :
    ∃ R > 0, Metric.ball (extChartAt I c c) R ⊆ (extChartAt I c).target :=
  Metric.isOpen_iff.1 (isOpen_extChartAt_target c) _
    ((extChartAt I c).map_source (mem_extChartAt_source c))

/-- A radius chosen once and for all at each point, as supplied by `Milnor.exists_radius`. -/
def someRadius (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [I.Boundaryless] (c : M) :
    ℝ :=
  (exists_radius (I := I) c).choose

/-- The chosen radius is positive. -/
theorem someRadius_pos (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [I.Boundaryless]
    (c : M) :
    0 < someRadius I c := (exists_radius (I := I) c).choose_spec.1

/-- The ball of the chosen radius lies in the target of the chart at the point. -/
theorem ball_someRadius_subset (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [I.Boundaryless]
    (c : M) :
    Metric.ball (extChartAt I c c) (someRadius I c) ⊆ (extChartAt I c).target :=
  (exists_radius (I := I) c).choose_spec.2

/-! ### Ball hops -/

/-- One **ball hop** from `x` to `y`: a centre `hub`, a radius `rad > 0` whose ball about the chart
image of `hub` is contained in the target of the chart at `hub`, and the requirement that `x` and
`y` both lie in the corresponding chart ball.  As for `Milnor.ChartHop` the centre is part of the
data, since two balls containing the same two points may disagree on which orientations
correspond. -/
structure BallHop (I : ModelWithCorners ℝ E H) (x y : M) where
  /-- the centre of the ball -/
  hub : M
  /-- the radius of the ball -/
  rad : ℝ
  /-- the radius is positive -/
  rad_pos : 0 < rad
  /-- the ball of radius `rad` about the chart image of `hub` lies in the chart's target -/
  ball_subset : Metric.ball (extChartAt I hub hub) rad ⊆ (extChartAt I hub).target
  /-- `x` lies in the chart ball -/
  mem_left : x ∈ chartBall I hub rad
  /-- `y` lies in the chart ball -/
  mem_right : y ∈ chartBall I hub rad

/-- **A ball hop is in particular a chart hop**, since a chart ball lies in the source of its
chart.  All the transport algebra of `Milnor.Chapter7.OrientTransport` is inherited through this
map. -/
def BallHop.toChartHop {x y : M} (b : BallHop I x y) : ChartHop I x y :=
  ⟨b.hub, chartBall_subset_source b.mem_left, chartBall_subset_source b.mem_right⟩

/-- The chart hop of a ball hop uses the same centre. -/
@[simp] theorem BallHop.toChartHop_hub {x y : M} (b : BallHop I x y) :
    b.toChartHop.hub = b.hub := rfl

/-- **The orientation transported along a ball hop**: the transport along the underlying chart hop,
that is, transport back to the centre of the ball through its chart and then out to the target
point. -/
def BallHop.transport {x y : M} (b : BallHop I x y) (o : Orientation ℝ E (Fin m)) :
    Orientation ℝ E (Fin m) := b.toChartHop.transport o

/-- Transport along a ball hop is transport along the underlying chart hop. -/
@[simp] theorem BallHop.transport_eq_chartHop {x y : M} (b : BallHop I x y)
    (o : Orientation ℝ E (Fin m)) : b.transport o = b.toChartHop.transport o := rfl

/-- Transport along a ball hop written out with `Milnor.orTransport`. -/
theorem BallHop.transport_eq {x y : M} (b : BallHop I x y) (o : Orientation ℝ E (Fin m)) :
    b.transport o = orTransport I b.hub y (orTransport I b.hub x o) := rfl

/-- **A ball hop reversed**: the same ball, with its two points exchanged. -/
def BallHop.symm {x y : M} (b : BallHop I x y) : BallHop I y x :=
  ⟨b.hub, b.rad, b.rad_pos, b.ball_subset, b.mem_right, b.mem_left⟩

/-- Reversing a ball hop reverses the underlying chart hop. -/
@[simp] theorem BallHop.symm_toChartHop {x y : M} (b : BallHop I x y) :
    b.symm.toChartHop = b.toChartHop.symm := rfl

/-- **A ball hop reversed undoes the ball hop**, because transport across one chart is an
involution; this is the chart-level `Milnor.ChartHop.transport_symm_transport` verbatim. -/
theorem BallHop.transport_symm_transport (hm : finrank ℝ E = m) {x y : M} (b : BallHop I x y)
    (o : Orientation ℝ E (Fin m)) : b.symm.transport (b.transport o) = o :=
  b.toChartHop.transport_symm_transport hm o

/-- Transport along a ball hop commutes with reversal of orientations, by the chart-level
`Milnor.ChartHop.transport_neg`. -/
theorem BallHop.transport_neg (hm : finrank ℝ E = m) {x y : M} (b : BallHop I x y)
    (o : Orientation ℝ E (Fin m)) : b.transport (-o) = -b.transport o :=
  b.toChartHop.transport_neg hm o

/-- **The ball hop from the centre of a ball to any of its points.** -/
def BallHop.ofCentre {c y : M} {R : ℝ} (hR : 0 < R)
    (hRt : Metric.ball (extChartAt I c c) R ⊆ (extChartAt I c).target)
    (hy : y ∈ chartBall I c R) : BallHop I c y :=
  ⟨c, R, hR, hRt, self_mem_chartBall c hR, hy⟩

/-- The hop from the centre of a ball transports by `Milnor.orTransport` through the chart at that
centre, exactly as `Milnor.ChartHop.transport_ofMemSource` does. -/
theorem BallHop.transport_ofCentre {c y : M} {R : ℝ} (hR : 0 < R)
    (hRt : Metric.ball (extChartAt I c c) R ⊆ (extChartAt I c).target)
    (hy : y ∈ chartBall I c R) (o : Orientation ℝ E (Fin m)) :
    (BallHop.ofCentre hR hRt hy).transport o = orTransport I c y o := by
  change orTransport I c y (orTransport I c c o) = _
  rw [transport_self]

/-- **The trivial ball hop** from a point to itself, through the ball of the radius chosen at that
point.  Unlike `Milnor.ChartHop.refl` this needs a ball to exist, hence a boundaryless model. -/
def BallHop.refl (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [I.Boundaryless] (x : M) :
    BallHop I x x :=
  BallHop.ofCentre (someRadius_pos I x) (ball_someRadius_subset I x)
    (self_mem_chartBall x (someRadius_pos I x))

/-- The trivial ball hop transports trivially. -/
@[simp] theorem BallHop.transport_refl [I.Boundaryless] (x : M)
    (o : Orientation ℝ E (Fin m)) : (BallHop.refl I x).transport o = o := by
  rw [BallHop.refl, BallHop.transport_ofCentre, transport_self]

/-! ### The constant orientation of the model space -/

/-- **The constant orientation** of the model space `E`, regarded as a manifold over itself: every
tangent space receives the same orientation `a`.  The compatibility condition of `Milnor.Orient` is
trivial, because the chart of `E` at any point is the identity, whose derivative preserves every
orientation.  This is the target orientation with which the key lemma below reads the chart of `M`
as a map of oriented manifolds. -/
def orientConst (a : Orientation ℝ E (Fin m)) : Orient 𝓘(ℝ, E) E m where
  or _ := a
  cont x := by
    filter_upwards with y
    have h2 : ⇑(extChartAt 𝓘(ℝ, E) x) = (id : E → E) := by
      funext u; simp [chartAt_self_eq]
    have h1 : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (⇑(extChartAt 𝓘(ℝ, E) x)) y
        (ContinuousLinearMap.id ℝ E) :=
      (hasMFDerivAt_id (I := 𝓘(ℝ, E)) y).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun u => congrFun h2 u)
    rw [HasMFDerivAt.mfd_eq h1]
    exact orSign_id a

/-- The orientation field of `Milnor.orientConst` is constant. -/
@[simp] theorem orientConst_or (a : Orientation ℝ E (Fin m)) (u : E) :
    (orientConst a).or u = a := rfl

/-! ### The key lemma: every orientation is ball-coherent -/

/-- **The chart sign of an orientation is locally constant.**  For an orientation `o` of `M` and a
point `z₀` of the source of the chart centred at `c`, the sign with which the derivative of that
chart compares `o.or z` with `o.or c` is the same for all `z` near `z₀`.

This is `Milnor.eventually_signAt_eq_of_contMDiffOn` applied to the chart `φ_c : M → E`, viewed as
a map of oriented manifolds from `M` to the model space carried by the constant orientation
`Milnor.orientConst (o.or c)`: the chart is smooth on its (open) source, and every point of that
source is a regular point of it because the derivative of a chart is invertible
(`Milnor.bijective_mfd_extChartAt`).  It is inside that lemma that the continuity field
`Orient.cont` of the two orientations and the local constancy of the sign of a continuous family of
linear maps (`Milnor.eventually_orSign_eq_of_continuousAt`) are used.  Boundarylessness of `I` is
inherited from that lemma. -/
theorem eventually_orSign_extChartAt_eq [I.Boundaryless] (hm : finrank ℝ E = m)
    (o : Orient I M m) {c z₀ : M} (hz₀ : z₀ ∈ (extChartAt I c).source) :
    ∀ᶠ z in 𝓝 z₀, orSign (o.or z) (o.or c) (mfd I 𝓘(ℝ, E) (extChartAt I c) z)
      = orSign (o.or z₀) (o.or c) (mfd I 𝓘(ℝ, E) (extChartAt I c) z₀) := by
  have h := eventually_signAt_eq_of_contMDiffOn hm hm o (orientConst (o.or c))
    (isOpen_extChartAt_source c) (by rw [extChartAt_source]; exact contMDiffOn_extChartAt) hz₀
    (bijective_mfd_extChartAt hz₀).surjective
  simpa only [signAt, orientConst_or] using h

/-- **The chart sign of an orientation is `1` on a whole chart ball.**  This is the key lemma of the
file: for `z` in a chart ball about `c` whose ball lies in the target of the chart at `c`, the
derivative of that chart carries `o.or z` to `o.or c`.

The proof is the one that has no chart-level counterpart.  The function
`z ↦ orSign (o.or z) (o.or c) (dφ_c|_z)` is locally constant on the chart ball
(`Milnor.eventually_orSign_extChartAt_eq`); a function into the discrete space `ℤ` that is locally
constant is continuous, the chart ball is connected (`Milnor.isPreconnected_chartBall`, where the
convexity of a ball is used), so the function is constant on the ball
(`IsPreconnected.constant`); and at the centre the derivative of the chart is the identity
(`Milnor.mfd_extChartAt_self`), where the sign is `1`.  The corresponding statement for the source
of a chart is false; see the counterexample in the module docstring of
`Milnor.Chapter7.Orientable`. -/
theorem orSign_or_eq_one_of_mem_chartBall [I.Boundaryless] (hm : finrank ℝ E = m)
    (o : Orient I M m) {c : M} {R : ℝ} (hR : 0 < R)
    (hRt : Metric.ball (extChartAt I c c) R ⊆ (extChartAt I c).target)
    {z : M} (hz : z ∈ chartBall I c R) :
    orSign (o.or z) (o.or c) (mfd I 𝓘(ℝ, E) (extChartAt I c) z) = 1 := by
  have hcont : ContinuousOn (fun w : M => orSign (o.or w) (o.or c)
      (mfd I 𝓘(ℝ, E) (extChartAt I c) w)) (chartBall I c R) := by
    intro w hw
    refine ContinuousAt.continuousWithinAt ?_
    rw [ContinuousAt, nhds_discrete ℤ, tendsto_pure]
    exact eventually_orSign_extChartAt_eq hm o (chartBall_subset_source hw)
  have hconst := (isPreconnected_chartBall hRt).constant hcont hz (self_mem_chartBall c hR)
  have hc : orSign (o.or c) (o.or c) (mfd I 𝓘(ℝ, E) (extChartAt I c) c) = 1 := by
    rw [mfd_extChartAt_self]; exact orSign_id _
  exact hconst.trans hc

/-- **Every orientation is ball-coherent**, in the form used in the induction over chains: the chart
hop underlying a ball hop from `x` to `y` carries `o.or x` to `o.or y`.  Both `x` and `y` lie in the
ball of the hop, where the previous lemma identifies the orientation with the transport of the
orientation at the centre; transport across one chart is an involution, so the two identifications
compose to the assertion.  Apart from the previous lemma this is
`Milnor.IsChartCoherent.hop_transport` verbatim — with the hypothesis of chart coherence no longer
needed. -/
theorem BallHop.chartHop_transport_or [I.Boundaryless] (hm : finrank ℝ E = m) (o : Orient I M m)
    {x y : M} (b : BallHop I x y) : b.toChartHop.transport (o.or x) = o.or y := by
  have hx : o.or x = orTransport I b.hub x (o.or b.hub) :=
    (orSign_eq_one_iff_eq_transport hm (chartBall_subset_source b.mem_left) _ _).1
      (orSign_or_eq_one_of_mem_chartBall hm o b.rad_pos b.ball_subset b.mem_left)
  have hy : o.or y = orTransport I b.hub y (o.or b.hub) :=
    (orSign_eq_one_iff_eq_transport hm (chartBall_subset_source b.mem_right) _ _).1
      (orSign_or_eq_one_of_mem_chartBall hm o b.rad_pos b.ball_subset b.mem_right)
  change orTransport I b.hub y (orTransport I b.hub x (o.or x)) = o.or y
  rw [hx, orTransport_involutive hm b.hub x, ← hy]

/-- **Every orientation is ball-coherent**: the transport along a ball hop of the value of an
orientation at the source point is its value at the target point.  No hypothesis beyond the
existence of the ball is needed — contrast `Milnor.IsChartCoherent.hop_transport`, which has to
assume the orientation coherent with every chart on the whole of its source. -/
theorem BallHop.transport_or [I.Boundaryless] (hm : finrank ℝ E = m) (o : Orient I M m)
    {x y : M} (b : BallHop I x y) : b.transport (o.or x) = o.or y :=
  b.chartHop_transport_or hm o

/-! ### Chains of ball hops -/

/-- **A chart chain all of whose hops come from ball hops.**  Making this a predicate on
`Milnor.ChartChain` rather than a second inductive type of chains means that composition, reversal,
transport and the notion of a reversing loop are literally the chart-level ones, so that
`ChartChain.transport_comp`, `ChartChain.transport_reverse`, `ChartChain.transport_neg` and
`ChartChain.Reverses` apply unchanged; only the closure of the predicate under those constructions
has to be proved. -/
inductive ChartChain.IsBall : ∀ {x y : M}, ChartChain I x y → Prop
  /-- the empty chain is a ball chain -/
  | nil (x : M) : ChartChain.IsBall (ChartChain.nil (I := I) x)
  /-- a ball hop prepended to a ball chain gives a ball chain -/
  | cons {x y z : M} (b : BallHop I x y) {c : ChartChain I y z}
      (hc : ChartChain.IsBall c) : ChartChain.IsBall (ChartChain.cons b.toChartHop c)

/-- The chain consisting of a single ball hop is a ball chain. -/
theorem ChartChain.IsBall.hop {x y : M} (b : BallHop I x y) :
    (ChartChain.hop b.toChartHop).IsBall :=
  ChartChain.IsBall.cons b (ChartChain.IsBall.nil y)

/-- **Ball chains compose**, by induction on the first chain; the chart-level
`Milnor.ChartChain.comp` is reused unchanged. -/
theorem ChartChain.IsBall.comp : ∀ {x y : M} {c : ChartChain I x y}, c.IsBall →
    ∀ {z : M} {d : ChartChain I y z}, d.IsBall → (c.comp d).IsBall := by
  intro x y c hc
  induction hc with
  | nil a => intro z d hd; exact hd
  | cons b hc' ih => intro z d hd; exact ChartChain.IsBall.cons b (ih hd)

/-- **Ball chains reverse**, because a ball hop reverses; the chart-level
`Milnor.ChartChain.reverse` is reused unchanged. -/
theorem ChartChain.IsBall.reverse : ∀ {x y : M} {c : ChartChain I x y}, c.IsBall →
    c.reverse.IsBall := by
  intro x y c hc
  induction hc with
  | nil a => exact ChartChain.IsBall.nil a
  | cons b hc' ih => exact ih.comp (ChartChain.IsBall.hop b.symm)

/-- **A ball chain extended by one further ball hop** is a ball chain. -/
theorem ChartChain.IsBall.snoc {x y z : M} {c : ChartChain I x y} (hc : c.IsBall)
    (b : BallHop I y z) : (c.comp (ChartChain.hop b.toChartHop)).IsBall :=
  hc.comp (ChartChain.IsBall.hop b)

/-- Transport along a chain extended by one ball hop applies that hop last. -/
theorem ChartChain.transport_comp_hop {x y z : M} (c : ChartChain I x y) (b : BallHop I y z)
    (o : Orientation ℝ E (Fin m)) :
    (c.comp (ChartChain.hop b.toChartHop)).transport o = b.transport (c.transport o) := by
  rw [ChartChain.transport_comp, ChartChain.transport_hop]; rfl

/-- **A ball chain carries an orientation of `M` to itself**: the transport along it of the value of
`o` at the initial point is the value of `o` at the final point.  Induction on the chain, using the
key lemma at each hop; this is `Milnor.IsChartCoherent.chain_transport` verbatim, with the
hypothesis of chart coherence no longer needed. -/
theorem ChartChain.IsBall.transport_or [I.Boundaryless] (hm : finrank ℝ E = m)
    (o : Orient I M m) : ∀ {x y : M} {c : ChartChain I x y}, c.IsBall →
      c.transport (o.or x) = o.or y := by
  intro x y c hc
  induction hc with
  | nil a => simp
  | cons b hc' ih => rw [ChartChain.transport_cons, b.chartHop_transport_or hm o, ih]

/-! ### Reachability by ball chains -/

/-- `y` is **ball-reachable** from `x` if some chain of ball hops joins `x` to `y`. -/
def BallReachable (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] (x y : M) : Prop :=
  ∃ c : ChartChain I x y, c.IsBall

/-- Ball-reachability is reflexive. -/
theorem BallReachable.refl (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] (x : M) :
    BallReachable I x x :=
  ⟨ChartChain.nil x, ChartChain.IsBall.nil x⟩

/-- Ball-reachability is symmetric, because ball chains reverse. -/
theorem BallReachable.symm {x y : M} (h : BallReachable I x y) : BallReachable I y x :=
  let ⟨c, hc⟩ := h; ⟨c.reverse, hc.reverse⟩

/-- Ball-reachability is transitive, because ball chains compose. -/
theorem BallReachable.trans {x y z : M} (h : BallReachable I x y) (h' : BallReachable I y z) :
    BallReachable I x z :=
  let ⟨c, hc⟩ := h; let ⟨d, hd⟩ := h'; ⟨c.comp d, hc.comp hd⟩

/-- A ball-reachable point is reachable by a chain of charts. -/
theorem BallReachable.reachable {x y : M} (h : BallReachable I x y) : Reachable I x y :=
  ⟨h.choose⟩

/-- A single ball hop makes its target ball-reachable from its source. -/
theorem ballReachable_of_ballHop {x y : M} (b : BallHop I x y) : BallReachable I x y :=
  ⟨ChartChain.hop b.toChartHop, ChartChain.IsBall.hop b⟩

/-- **Every point is ball-reachable from every point near it**, by the single ball hop from the
centre of the ball chosen at that point.  This is the one place where the chart-level argument has
to be changed: there the neighbourhood used was the whole source of the chart, which need not carry
a ball hop. -/
theorem eventually_ballReachable [I.Boundaryless] (x : M) :
    ∀ᶠ y in 𝓝 x, BallReachable I x y := by
  filter_upwards [chartBall_mem_nhds (I := I) x (someRadius_pos I x)] with y hy
  exact ballReachable_of_ballHop
    (BallHop.ofCentre (someRadius_pos I x) (ball_someRadius_subset I x) hy)

/-- The set of points ball-reachable from `x` is open, since each of its points has a whole
neighbourhood of ball-reachable points. -/
theorem isOpen_ballReachable [I.Boundaryless] (x : M) :
    IsOpen {y : M | BallReachable I x y} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  filter_upwards [eventually_ballReachable (I := I) y] with p hp
  exact hy.trans hp

/-- The set of points ball-reachable from `x` is closed: near a point not ball-reachable from `x`
there is no ball-reachable point. -/
theorem isClosed_ballReachable [I.Boundaryless] (x : M) :
    IsClosed {y : M | BallReachable I x y} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  filter_upwards [eventually_ballReachable (I := I) y] with p hp
  intro hpr
  exact hy (hpr.trans hp.symm)

/-- **In a connected manifold any two points are joined by a chain of ball hops**, because the set
of points ball-reachable from a fixed point is open, closed and nonempty.  This is
`Milnor.reachable_of_preconnectedSpace` verbatim, with `Milnor.eventually_ballReachable` in place
of the fact that a chart source is a neighbourhood of its centre. -/
theorem ballReachable_of_preconnectedSpace [I.Boundaryless] [PreconnectedSpace M] (x y : M) :
    BallReachable I x y := by
  have hcl : IsClopen {z : M | BallReachable I x z} :=
    ⟨isClosed_ballReachable x, isOpen_ballReachable x⟩
  have h : {z : M | BallReachable I x z} = univ :=
    IsClopen.eq_univ hcl ⟨x, BallReachable.refl I x⟩
  have hy : y ∈ {z : M | BallReachable I x z} := by rw [h]; exact mem_univ y
  exact hy

/-! ### One half of the dichotomy: an orientation forbids reversing ball loops -/

/-- **An orientation of `M` forbids reversing ball-chain-loops.**  A ball loop at `x` returns the
orientation at `x` unchanged, and an orientation of a vector space is never its own reverse.  Unlike
the chart-level `Milnor.IsChartCoherent.not_reverses` this needs no hypothesis on the orientation
beyond its being a `Milnor.Orient`: that is the gain of working with balls. -/
theorem Orient.not_reverses_isBall [I.Boundaryless] (hm : finrank ℝ E = m) (o : Orient I M m)
    {x : M} {c : ChartChain I x x} (hc : c.IsBall) : ¬ c.Reverses m := by
  intro h
  have h1 := h.transport_eq_neg hm (o.or x)
  rw [hc.transport_or hm o] at h1
  exact ne_neg (o.or x) h1

/-- **An orientable manifold has no reversing ball-chain-loop**, at any point. -/
theorem not_reverses_isBall_of_isOrientable [I.Boundaryless] (hm : finrank ℝ E = m)
    (h : IsOrientable I M m) {x : M} {c : ChartChain I x x} (hc : c.IsBall) :
    ¬ c.Reverses m := h.orient.not_reverses_isBall hm hc

/-! ### The other half: from the absence of reversing ball loops to an orientation -/

/-- **The orientation transported along a ball chain does not depend on the chain.**  If no ball
loop at `x₀` reverses, then any two ball chains from `x₀` to `y` transport an orientation at `x₀` to
the same orientation at `y`: otherwise the first followed by the reverse of the second would be a
reversing ball loop at `x₀`.  This is
`Milnor.ChartChain.transport_eq_of_forall_not_reverses` with the ball witness carried along. -/
theorem ChartChain.transport_eq_of_forall_not_reverses_isBall (hm : finrank ℝ E = m) {x₀ : M}
    (hno : ∀ c : ChartChain I x₀ x₀, c.IsBall → ¬ c.Reverses m) {y : M}
    {c d : ChartChain I x₀ y} (hc : c.IsBall) (hd : d.IsBall) (o : Orientation ℝ E (Fin m)) :
    c.transport o = d.transport o := by
  rcases eq_or_eq_neg hm (c.transport o) (d.transport o) with h | h
  · exact h
  · refine absurd (((c.comp d.reverse).reverses_def m).2 ⟨o, ?_⟩)
      (hno (c.comp d.reverse) (hc.comp hd.reverse))
    rw [ChartChain.transport_comp, h, ChartChain.transport_neg hm, ChartChain.transport_reverse hm]

/-- A ball chain from `x₀` to `y`, chosen once and for all with the axiom of choice; it exists in a
connected manifold by `Milnor.ballReachable_of_preconnectedSpace`. -/
def someBallChain (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [I.Boundaryless]
    [PreconnectedSpace M]
    (x₀ y : M) : ChartChain I x₀ y := (ballReachable_of_preconnectedSpace (I := I) x₀ y).choose

/-- The chosen chain is indeed a ball chain. -/
theorem someBallChain_isBall (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [I.Boundaryless]
    [PreconnectedSpace M]
    (x₀ y : M) : (someBallChain I x₀ y).IsBall :=
  (ballReachable_of_preconnectedSpace (I := I) x₀ y).choose_spec

/-- **The candidate orientation field**: transport the orientation `o₀` at the base point `x₀` along
a chosen ball chain to every point of `M`. -/
def ballTransportFrom (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] [I.Boundaryless]
    [PreconnectedSpace M]
    (x₀ : M) (o₀ : Orientation ℝ E (Fin m)) : M → Orientation ℝ E (Fin m) :=
  fun y => (someBallChain I x₀ y).transport o₀

/-- If no ball loop at `x₀` reverses, the candidate orientation field is computed by **every** ball
chain from `x₀`, not only by the chosen one. -/
theorem ballTransportFrom_eq (hm : finrank ℝ E = m) [I.Boundaryless] [PreconnectedSpace M]
    {x₀ : M} (hno : ∀ c : ChartChain I x₀ x₀, c.IsBall → ¬ c.Reverses m)
    (o₀ : Orientation ℝ E (Fin m)) {y : M} {c : ChartChain I x₀ y} (hc : c.IsBall) :
    ballTransportFrom I x₀ o₀ y = c.transport o₀ :=
  ChartChain.transport_eq_of_forall_not_reverses_isBall hm hno
    (someBallChain_isBall I x₀ y) hc o₀

/-- **The candidate orientation field is a transport section.**  A point `y` near `x` lies in the
ball chosen at `x`, so the ball hop from `x` to `y` through the chart at `x` extends a ball chain
from `x₀` to `x`; the extended chain transports by one further application of
`Milnor.orTransport I x y`, and by independence of the chain it computes the field at `y`.  This is
`Milnor.isChartCoherent_transportFrom` with one change: the chart-level proof produced a
*chart-coherent* family, using the whole source of the chart at `x`, whereas here only a
neighbourhood of `x` — the chosen ball — is available, which is exactly what
`Milnor.IsTransportSection` asks for. -/
theorem isTransportSection_ballTransportFrom (hm : finrank ℝ E = m) [I.Boundaryless]
    [PreconnectedSpace M] {x₀ : M}
    (hno : ∀ c : ChartChain I x₀ x₀, c.IsBall → ¬ c.Reverses m)
    (o₀ : Orientation ℝ E (Fin m)) : IsTransportSection I (ballTransportFrom I x₀ o₀) := by
  intro x
  filter_upwards [chartBall_mem_nhds (I := I) x (someRadius_pos I x)] with y hy
  obtain ⟨b, hbeq⟩ : ∃ b : BallHop I x y,
      ∀ o : Orientation ℝ E (Fin m), b.transport o = orTransport I x y o := by
    refine ⟨BallHop.ofCentre (someRadius_pos I x) (ball_someRadius_subset I x) hy, fun o => ?_⟩
    change orTransport I x y (orTransport I x x o) = _
    rw [transport_self]
  rw [ballTransportFrom_eq hm hno o₀ ((someBallChain_isBall I x₀ x).snoc b),
    ChartChain.transport_comp_hop, hbeq,
    ballTransportFrom_eq hm hno o₀ (someBallChain_isBall I x₀ x)]

/-- **A connected manifold with no reversing ball-chain-loop is orientable.** -/
theorem isOrientable_of_forall_not_reverses_isBall (hm : finrank ℝ E = m) [I.Boundaryless]
    [PreconnectedSpace M] {x₀ : M}
    (hno : ∀ c : ChartChain I x₀ x₀, c.IsBall → ¬ c.Reverses m) : IsOrientable I M m :=
  ⟨Orient.ofTransportSection hm
    (isTransportSection_ballTransportFrom hm hno (nonempty_orientation hm).some)⟩

/-! ### The exact dichotomy -/

/-- **The orientability dichotomy for balls.**  A connected manifold is orientable if and only if no
ball-chain-loop at a given point reverses orientation.  Both directions are unconditional: this is
the improvement over the chart-level `Milnor.exists_isChartCoherent_iff_forall_not_reverses`, where
the absence of reversing chart loops is equivalent not to orientability but to the existence of an
orientation coherent with every chart on the whole of its source, and where the plain converse is
false (see the module docstring of `Milnor.Chapter7.Orientable`).  Milnor p. 50. -/
theorem isOrientable_iff_forall_not_reverses_isBall (hm : finrank ℝ E = m) [I.Boundaryless]
    [PreconnectedSpace M] (x₀ : M) :
    IsOrientable I M m ↔ ∀ c : ChartChain I x₀ x₀, c.IsBall → ¬ c.Reverses m := by
  constructor
  · intro h c hc
    exact not_reverses_isBall_of_isOrientable hm h hc
  · intro hno
    exact isOrientable_of_forall_not_reverses_isBall hm hno

/-- **A connected non-orientable manifold has a reversing ball loop at every point**, and that loop
reverses every orientation there.  This is the form in which the mod `2` theorem uses the
dichotomy: the loop runs through round balls, so a framed point can be slid along it. -/
theorem exists_isBall_reverses_of_not_isOrientable (hm : finrank ℝ E = m) [I.Boundaryless]
    [PreconnectedSpace M] (h : ¬ IsOrientable I M m) (x₀ : M) :
    ∃ c : ChartChain I x₀ x₀, c.IsBall ∧
      ∀ o : Orientation ℝ E (Fin m), c.transport o = -o := by
  by_contra hcon
  refine h ((isOrientable_iff_forall_not_reverses_isBall hm x₀).2 ?_)
  intro c hc hrev
  exact hcon ⟨c, hc, fun o => hrev.transport_eq_neg hm o⟩

/-- **A connected non-orientable manifold has a point and a ball loop at it whose transport reverses
every orientation there.** -/
theorem exists_point_isBall_reverses_of_not_isOrientable (hm : finrank ℝ E = m) [I.Boundaryless]
    [PreconnectedSpace M] (h : ¬ IsOrientable I M m) :
    ∃ (x : M) (c : ChartChain I x x), c.IsBall ∧
      ∀ o : Orientation ℝ E (Fin m), c.transport o = -o := by
  obtain ⟨x₀⟩ := nonempty_of_not_isOrientable h
  exact ⟨x₀, exists_isBall_reverses_of_not_isOrientable hm h x₀⟩

end Milnor
