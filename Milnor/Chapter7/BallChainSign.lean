import Milnor.Chapter7.OrientBall

/-!
# The sign dictionary for chains of charts, the transition cocycle, and avoidance of a closed set

Milnor's remark at the end of §7 (p. 50) is that the smooth maps of a *connected non-orientable*
manifold to a sphere are classified by the degree modulo `2`; the content of the remark is that such
a manifold carries a loop along which a frame comes back reversed, so that only the parity of the
number of points of a framed `0`-manifold survives.  This file is the **remainder of Stage 4** of the
plan `Milnor/Exposition/PlanMod2.md`; the earlier part of that stage is
`Milnor.Chapter7.OrientTransport` (transport of an orientation across one chart, hops, chains),
`Milnor.Chapter7.Orientable` (orientability and the chart-level dichotomy) and
`Milnor.Chapter7.OrientBall` (chart balls, ball hops, ball chains, the ball-coherence of every
orientation and the exact dichotomy).  Three things are added here.

* **The sign dictionary** (plan §2.4).  `Milnor.jacSign I c z` is the sign of the determinant of the
  derivative at `z` of the chart centred at `c`; it is `±1` for `z` in the source of that chart,
  because the derivative of a chart is invertible (`Milnor.bijective_mfd_extChartAt`), and `1` for
  `z = c`.  Transport of an orientation across that chart is then multiplication by this sign
  (`Milnor.orTransport_eq_signAct`), where `Milnor.signAct s o` is `o` for `s = 1` and `-o`
  otherwise.  The sign of a hop is the product of the two Jacobian signs of its chart at the two
  endpoints (`Milnor.hopSign`), the sign of a chain is the product of the signs of its hops
  (`Milnor.chainSign`), and:

  - `Milnor.chainSign_comp`: the sign of a composite is the product of the signs;
  - `Milnor.chainSign_reverse`: a chain and its reverse have the same sign;
  - `Milnor.ChartChain.transport_eq_signAct`: transport along a chain is multiplication by its sign,
    hence `Milnor.ChartChain.transport_eq_self_iff`: the transport is the identity exactly when the
    sign is `1`;
  - `Milnor.ChartChain.reverses_iff_chainSign`: a loop reverses exactly when its sign is `-1`.

  All of this holds for arbitrary chart hops and chart chains — a `Milnor.ChartHop` already carries
  the two membership facts that make the Jacobian signs `±1` — so nothing has to be repeated for
  ball hops, whose chains are chart chains satisfying `Milnor.ChartChain.IsBall`.  The dichotomy of
  `Milnor.Chapter7.OrientBall` is restated arithmetically in
  `Milnor.isOrientable_iff_forall_chainSign_eq_one` and
  `Milnor.exists_isBall_chainSign_eq_neg_one`, and the "converse" direction of the plan — an
  orientation determines the sign of every ball chain — is
  `Milnor.ChartChain.IsBall.signAct_chainSign_or`.

* **The transition cocycle lemma** (plan §3.3, "the technical key used twice later"),
  `Milnor.eventually_jacSign_mul_jacSign_eq`: for two chart centres `p`, `q` and a point `y` in both
  chart sources, the product `jacSign I p z * jacSign I q z` is *locally constant* in `z` near `y`.
  Neither factor is a continuous function of `z` — each is read through the chart at `z`, which jumps
  about — but in the product the chart at `z` cancels.  Concretely, the chain rule
  (`Milnor.mfd_extChartAt_eq_comp`) factors the derivative of the chart at `p` through the derivative
  of the chart at `q` and the derivative of the *fixed* transition map
  `Milnor.chartTrans I p q = extChartAt I p ∘ (extChartAt I q).symm`, so the product equals the
  determinant sign of that transition map at `extChartAt I q z` (`Milnor.transSign`), the square of
  the Jacobian sign of the chart at `q` being `1`.  The transition map is smooth on an open set
  (`Milnor.contDiffOn_chartTrans`, from Mathlib's `contMDiffOn_extChartAt`,
  `contMDiffOn_extChartAt_symm`), so its derivative is continuous there
  (`ContDiffOn.continuousOn_fderiv_of_isOpen`) and the sign of a continuous family of invertible
  linear maps is locally constant (`Milnor.eventually_orSign_eq_of_continuousAt`).

* **Ball reachability avoiding a closed set** (plan, Stage 4, last item).  A ball hop *runs inside*
  `C` (`Milnor.BallHop.RunsIn`) if the closed ball of its radius lies in the target of its chart and
  the resulting **closed chart ball** `Milnor.closedChartBall` — the image of that closed ball under
  the inverse chart — is contained in `C`.  A chart chain is a *ball chain inside `C`*
  (`Milnor.ChartChain.IsBallIn`) if each of its hops comes from a ball hop running inside `C`; this
  predicate implies `Milnor.ChartChain.IsBall`, is monotone in `C`, and is closed under composition,
  reversal, single hops and extension.  For an open preconnected `C` any two points of `C` are
  joined by a ball chain inside `C` (`Milnor.exists_isBallIn`), by the clopen argument of
  `Milnor.ballReachable_of_preconnectedSpace` run inside `C`: the small-ball step is
  `Milnor.exists_closedChartBall_subset`, the abstract-manifold form of
  `Milnor.Framed.exists_ballU_subset` (`Milnor/Chapter7/Segment.lean`), which produces a chart ball
  about a given point whose closed chart ball lies in a given neighbourhood.  Since a chain inside
  `C` automatically avoids every set disjoint from `C`, the avoidance statement the later stages
  need follows at once (`Milnor.exists_isBallIn_avoiding`): for `P` disjoint from `C`, every ball of
  the chain, and indeed its closed chart ball, misses `P`.  Note that `P` need not be closed, and
  that `C` need not be connected but only preconnected; no local connectedness of `M` and no
  hypothesis on the dimension is used.

  The closed chart ball rather than the topological closure of the ball is used on purpose.  In a
  non-Hausdorff manifold the closure of a chart ball need not even lie in the source of the chart —
  on the line with two origins the closure of an interval about one origin contains the other — so
  no statement about that closure can be had in the generality of this file.  The two are related by
  `Milnor.closure_chartBall_subset_closedChartBall` and `Milnor.BallHop.RunsIn.closure_subset`, which
  assume `[T2Space M]` and say that a hop running inside `C` has the closure of its ball inside `C`;
  that is the form the moving machinery of the framed-cobordism argument needs, and it is available
  there, the manifolds of Chapter 7 being subsets of a Euclidean space.  Nothing else in this file
  depends on those two statements.

Boundarylessness of `I` is assumed exactly where it is forced, and for the same two reasons as in
`Milnor.Chapter7.OrientBall`: a ball inside the target of a chart has to exist at all (which is why
`Milnor.exists_closedChartBall_subset` and everything about reachability needs it), and the target
of a chart has to be open for the transition map to be smooth on an open set (which is why the
cocycle lemma needs it).  The whole sign dictionary is free of it.  Hausdorffness is used only in the
two statements flagged above, second countability and positivity of the dimension are nowhere needed,
and `M` may be empty.
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

/-! ### The Jacobian sign of a chart -/

/-- **The Jacobian sign of the chart centred at `c`, read at `z`**: the sign of the determinant of
the derivative at `z` of that chart.  For `z` in the source of the chart the derivative is a linear
automorphism of the model space, so the sign is `1` or `-1` (`Milnor.jacSign_eq_one_or_neg_one`);
for `z` outside the source the value is junk. -/
def jacSign (I : ModelWithCorners ℝ E H) (c z : M) : ℤ :=
  sgn (LinearMap.det (mfd I 𝓘(ℝ, E) (extChartAt I c) z : E →ₗ[ℝ] E))

/-- **The Jacobian sign is the sign of the chart derivative relative to any one orientation** of the
model space used at both ends; this is the bridge between `Milnor.jacSign` and the `Milnor.orSign`
calculus, and it is how `Milnor.orTransport` is computed below. -/
theorem orSign_mfd_extChartAt (hm : finrank ℝ E = m) (a : Orientation ℝ E (Fin m)) (c z : M) :
    orSign a a (mfd I 𝓘(ℝ, E) (extChartAt I c) z) = jacSign I c z :=
  orSign_self_eq_sgn_det hm a _

/-- **The Jacobian sign of a chart at its own centre is `1`**, the derivative there being the
identity (`Milnor.mfd_extChartAt_self`). -/
@[simp] theorem jacSign_self (c : M) : jacSign I c c = 1 := by
  rw [jacSign, mfd_extChartAt_self, ContinuousLinearMap.coe_id, LinearMap.det_id]
  exact sgn_one

/-- **The Jacobian sign of a chart is nonzero on the chart's source**, because the derivative of a
chart is bijective there (`Milnor.bijective_mfd_extChartAt`). -/
theorem jacSign_ne_zero (hm : finrank ℝ E = m) {c z : M} (hz : z ∈ (extChartAt I c).source) :
    jacSign I c z ≠ 0 := by
  obtain ⟨a⟩ := nonempty_orientation (E := E) hm
  rw [← orSign_mfd_extChartAt hm a]
  exact (orSign_ne_zero_iff hm hm a a _).2 (bijective_mfd_extChartAt hz)

/-- On the source of a chart the Jacobian sign is `1` or `-1`. -/
theorem jacSign_eq_one_or_neg_one (hm : finrank ℝ E = m) {c z : M}
    (hz : z ∈ (extChartAt I c).source) : jacSign I c z = 1 ∨ jacSign I c z = -1 := by
  rcases sgn_mem (x := LinearMap.det (mfd I 𝓘(ℝ, E) (extChartAt I c) z : E →ₗ[ℝ] E)) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (jacSign_ne_zero hm hz)

/-- **The Jacobian sign squares to `1`** on the source of the chart.  This cancellation is what
makes the product of two Jacobian signs a cocycle (`Milnor.eventually_jacSign_mul_jacSign_eq`). -/
theorem jacSign_mul_self (hm : finrank ℝ E = m) {c z : M} (hz : z ∈ (extChartAt I c).source) :
    jacSign I c z * jacSign I c z = 1 := by
  rcases jacSign_eq_one_or_neg_one hm hz with h | h <;> rw [h] <;> norm_num

/-! ### The action of a sign on the two orientations -/

/-- **The action of a sign on orientations**: `signAct s o` is `o` for `s = 1` and `-o` for every
other value of `s`.  Only `s = 1` and `s = -1` are ever used, and on those two values this is the
action of the multiplicative group `{±1}` on the two orientations of the model space
(`Milnor.signAct_mul`). -/
def signAct (s : ℤ) (o : Orientation ℝ E (Fin m)) : Orientation ℝ E (Fin m) :=
  if s = 1 then o else -o

/-- The sign `1` acts trivially. -/
@[simp] theorem signAct_one (o : Orientation ℝ E (Fin m)) : signAct 1 o = o := if_pos rfl

/-- The sign `-1` acts by reversing the orientation. -/
@[simp] theorem signAct_neg_one (o : Orientation ℝ E (Fin m)) : signAct (-1) o = -o :=
  if_neg (by decide)

/-- **The action is multiplicative** on the signs `±1`. -/
theorem signAct_mul {s t : ℤ} (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1)
    (o : Orientation ℝ E (Fin m)) : signAct (s * t) o = signAct s (signAct t o) := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (-1 : ℤ) * (-1 : ℤ) = 1 by norm_num, signAct_one, signAct_neg_one, signAct_neg_one]
    exact (neg_neg o).symm

/-- **A sign `±1` is determined by its action**: it acts trivially exactly when it is `1`, because
an orientation is never its own reverse (`Milnor.ne_neg`). -/
theorem signAct_eq_self_iff {s : ℤ} (hs : s = 1 ∨ s = -1) (o : Orientation ℝ E (Fin m)) :
    signAct s o = o ↔ s = 1 := by
  rcases hs with rfl | rfl
  · simp
  · refine ⟨fun h => absurd h.symm (ne_neg o), fun h => absurd h (by decide)⟩

/-- A sign `±1` reverses the orientation exactly when it is `-1`. -/
theorem signAct_eq_neg_iff {s : ℤ} (hs : s = 1 ∨ s = -1) (o : Orientation ℝ E (Fin m)) :
    signAct s o = -o ↔ s = -1 := by
  rcases hs with rfl | rfl
  · rw [signAct_one]
    exact ⟨fun h => absurd h (ne_neg o), fun h => absurd h (by decide)⟩
  · simp

/-! ### Transport across one chart is the action of the Jacobian sign -/

/-- **Transport of an orientation across one chart is multiplication by the Jacobian sign.**  This
is the first entry of the dictionary of plan §2.4. -/
theorem orTransport_eq_signAct (hm : finrank ℝ E = m) {c z : M}
    (hz : z ∈ (extChartAt I c).source) (o : Orientation ℝ E (Fin m)) :
    orTransport I c z o = signAct (jacSign I c z) o := by
  rcases jacSign_eq_one_or_neg_one hm hz with h | h
  · rw [h, signAct_one]
    exact orTransport_eq_self (by rw [orSign_mfd_extChartAt hm o]; exact h)
  · rw [h, signAct_neg_one]
    refine orTransport_eq_neg ?_
    rw [orSign_mfd_extChartAt hm o, h]
    decide

/-- **Transport across one chart is trivial exactly when the Jacobian sign is `1`.** -/
theorem orTransport_eq_self_iff (hm : finrank ℝ E = m) {c z : M}
    (hz : z ∈ (extChartAt I c).source) (o : Orientation ℝ E (Fin m)) :
    orTransport I c z o = o ↔ jacSign I c z = 1 := by
  rw [orTransport_eq_signAct hm hz]
  exact signAct_eq_self_iff (jacSign_eq_one_or_neg_one hm hz) o

/-- Transport across one chart reverses the orientation exactly when the Jacobian sign is `-1`. -/
theorem orTransport_eq_neg_iff (hm : finrank ℝ E = m) {c z : M}
    (hz : z ∈ (extChartAt I c).source) (o : Orientation ℝ E (Fin m)) :
    orTransport I c z o = -o ↔ jacSign I c z = -1 := by
  rw [orTransport_eq_signAct hm hz]
  exact signAct_eq_neg_iff (jacSign_eq_one_or_neg_one hm hz) o

/-! ### The sign of a hop -/

/-- **The sign of a chart hop**: the product of the Jacobian signs of the hop's chart at the two
endpoints.  Transport along the hop is multiplication by this sign
(`Milnor.ChartHop.transport_eq_signAct`).  Both endpoints lie in the source of the chart at the hop's
centre, so the two factors are `±1` and the sign is `±1` as well. -/
def hopSign {x y : M} (h : ChartHop I x y) : ℤ := jacSign I h.hub x * jacSign I h.hub y

/-- The sign of a hop is `1` or `-1`. -/
theorem hopSign_eq_one_or_neg_one (hm : finrank ℝ E = m) {x y : M} (h : ChartHop I x y) :
    hopSign h = 1 ∨ hopSign h = -1 := by
  rcases jacSign_eq_one_or_neg_one hm h.mem_left with h1 | h1 <;>
    rcases jacSign_eq_one_or_neg_one hm h.mem_right with h2 | h2 <;>
      rw [hopSign, h1, h2] <;> norm_num

/-- The sign of a hop is nonzero. -/
theorem hopSign_ne_zero (hm : finrank ℝ E = m) {x y : M} (h : ChartHop I x y) :
    hopSign h ≠ 0 := by
  rcases hopSign_eq_one_or_neg_one hm h with h1 | h1 <;> rw [h1] <;> decide

/-- **Reversing a hop does not change its sign**: the same chart is used, and the two Jacobian signs
are merely exchanged. -/
@[simp] theorem hopSign_symm {x y : M} (h : ChartHop I x y) : hopSign h.symm = hopSign h :=
  mul_comm _ _

/-- The trivial hop from a point to itself through the chart at that point has sign `1`. -/
@[simp] theorem hopSign_refl (x : M) : hopSign (ChartHop.refl I x) = 1 := by
  rw [hopSign]
  show jacSign I x x * jacSign I x x = 1
  rw [jacSign_self]; norm_num

/-- **Transport along a hop is multiplication by the hop's sign.** -/
theorem ChartHop.transport_eq_signAct (hm : finrank ℝ E = m) {x y : M} (h : ChartHop I x y)
    (o : Orientation ℝ E (Fin m)) : h.transport o = signAct (hopSign h) o := by
  have hx := jacSign_eq_one_or_neg_one hm h.mem_left
  have hy := jacSign_eq_one_or_neg_one hm h.mem_right
  have h1 : hopSign h = jacSign I h.hub y * jacSign I h.hub x := mul_comm _ _
  change orTransport I h.hub y (orTransport I h.hub x o) = _
  rw [orTransport_eq_signAct hm h.mem_left, orTransport_eq_signAct hm h.mem_right, h1,
    signAct_mul hy hx]

/-- Transport along a hop is trivial exactly when the hop's sign is `1`. -/
theorem ChartHop.transport_eq_self_iff (hm : finrank ℝ E = m) {x y : M} (h : ChartHop I x y)
    (o : Orientation ℝ E (Fin m)) : h.transport o = o ↔ hopSign h = 1 := by
  rw [h.transport_eq_signAct hm]
  exact signAct_eq_self_iff (hopSign_eq_one_or_neg_one hm h) o

/-! ### The sign of a chain -/

/-- **The sign of a chain of charts**: the product of the signs of its hops.  Transport along the
chain is multiplication by this sign (`Milnor.ChartChain.transport_eq_signAct`). -/
def chainSign {x y : M} (c : ChartChain I x y) : ℤ :=
  match c with
  | .nil _ => 1
  | .cons h c' => hopSign h * chainSign c'

/-- The empty chain has sign `1`. -/
@[simp] theorem chainSign_nil (x : M) : chainSign (ChartChain.nil (I := I) x) = 1 := rfl

/-- The sign of a chain that begins with a hop. -/
@[simp] theorem chainSign_cons {x y z : M} (h : ChartHop I x y) (c : ChartChain I y z) :
    chainSign (ChartChain.cons h c) = hopSign h * chainSign c := rfl

/-- The sign of a one-hop chain is the sign of the hop. -/
@[simp] theorem chainSign_hop {x y : M} (h : ChartHop I x y) :
    chainSign (ChartChain.hop h) = hopSign h := by
  rw [ChartChain.hop, chainSign_cons, chainSign_nil, mul_one]

/-- **The sign of a composite chain is the product of the signs**, by induction on the first
chain. -/
theorem chainSign_comp : ∀ {x y z : M} (c : ChartChain I x y) (d : ChartChain I y z),
    chainSign (c.comp d) = chainSign c * chainSign d := by
  intro x y z c
  induction c with
  | nil a => intro d; rw [ChartChain.nil_comp, chainSign_nil, one_mul]
  | cons h c ih => intro d; rw [ChartChain.cons_comp, chainSign_cons, chainSign_cons, ih, mul_assoc]

/-- **A chain and its reverse have the same sign**, since reversing a hop does not change its sign
and multiplication in `ℤ` is commutative. -/
theorem chainSign_reverse : ∀ {x y : M} (c : ChartChain I x y),
    chainSign c.reverse = chainSign c := by
  intro x y c
  induction c with
  | nil a => rfl
  | cons h c ih =>
      rw [ChartChain.reverse_cons, chainSign_comp, ih, chainSign_hop, hopSign_symm,
        chainSign_cons, mul_comm]

/-- The sign of a chain is `1` or `-1`. -/
theorem chainSign_eq_one_or_neg_one (hm : finrank ℝ E = m) : ∀ {x y : M} (c : ChartChain I x y),
    chainSign c = 1 ∨ chainSign c = -1 := by
  intro x y c
  induction c with
  | nil a => exact Or.inl rfl
  | cons h c ih =>
      rcases hopSign_eq_one_or_neg_one hm h with h1 | h1 <;> rcases ih with h2 | h2 <;>
        rw [chainSign_cons, h1, h2] <;> norm_num

/-- The sign of a chain is nonzero. -/
theorem chainSign_ne_zero (hm : finrank ℝ E = m) {x y : M} (c : ChartChain I x y) :
    chainSign c ≠ 0 := by
  rcases chainSign_eq_one_or_neg_one hm c with h | h <;> rw [h] <;> decide

/-- **Transport along a chain is multiplication by the chain's sign**, by induction on the chain. -/
theorem ChartChain.transport_eq_signAct (hm : finrank ℝ E = m) :
    ∀ {x y : M} (c : ChartChain I x y) (o : Orientation ℝ E (Fin m)),
      c.transport o = signAct (chainSign c) o := by
  intro x y c
  induction c with
  | nil a => intro o; rw [ChartChain.transport_nil, chainSign_nil, signAct_one]
  | cons h c ih =>
      intro o
      rw [ChartChain.transport_cons, ih, h.transport_eq_signAct hm, chainSign_cons,
        mul_comm (hopSign h) (chainSign c),
        signAct_mul (chainSign_eq_one_or_neg_one hm c) (hopSign_eq_one_or_neg_one hm h)]

/-- **Transport along a chain is the identity exactly when the chain's sign is `1`.** -/
theorem ChartChain.transport_eq_self_iff (hm : finrank ℝ E = m) {x y : M} (c : ChartChain I x y)
    (o : Orientation ℝ E (Fin m)) : c.transport o = o ↔ chainSign c = 1 := by
  rw [c.transport_eq_signAct hm]
  exact signAct_eq_self_iff (chainSign_eq_one_or_neg_one hm c) o

/-- **Transport along a chain reverses an orientation exactly when the chain's sign is `-1`.** -/
theorem ChartChain.transport_eq_neg_iff (hm : finrank ℝ E = m) {x y : M} (c : ChartChain I x y)
    (o : Orientation ℝ E (Fin m)) : c.transport o = -o ↔ chainSign c = -1 := by
  rw [c.transport_eq_signAct hm]
  exact signAct_eq_neg_iff (chainSign_eq_one_or_neg_one hm c) o

/-- **A chain-loop reverses exactly when its sign is `-1`.**  This is the last entry of the
dictionary of plan §2.4, and the form in which the dichotomy of `Milnor.Chapter7.OrientBall` becomes
a statement of arithmetic. -/
theorem ChartChain.reverses_iff_chainSign (hm : finrank ℝ E = m) {x : M} (c : ChartChain I x x) :
    c.Reverses m ↔ chainSign c = -1 := by
  obtain ⟨o⟩ := nonempty_orientation (E := E) hm
  rw [c.reverses_iff hm o]
  exact c.transport_eq_neg_iff hm o

/-! ### The dictionary applied to ball chains -/

/-- **An orientation determines the sign of every ball chain**: the value of the orientation at the
final point of a ball chain is the action of the chain's sign on its value at the initial point.
This is the "converse" direction of plan §3.3, read arithmetically; it rests on the ball-coherence of
every orientation (`Milnor.ChartChain.IsBall.transport_or`). -/
theorem ChartChain.IsBall.signAct_chainSign_or [I.Boundaryless] (hm : finrank ℝ E = m)
    (o : Orient I M m) {x y : M} {c : ChartChain I x y} (hc : c.IsBall) :
    signAct (chainSign c) (o.or x) = o.or y := by
  rw [← c.transport_eq_signAct hm]
  exact hc.transport_or hm o

/-- **An orientation forces every ball loop to have sign `1`.** -/
theorem Orient.chainSign_eq_one_of_isBall [I.Boundaryless] (hm : finrank ℝ E = m)
    (o : Orient I M m) {x : M} {c : ChartChain I x x} (hc : c.IsBall) : chainSign c = 1 := by
  rw [← ChartChain.transport_eq_self_iff hm c (o.or x)]
  exact hc.transport_or hm o

/-- **The orientability dichotomy in arithmetic form**: a connected manifold is orientable if and
only if every ball-chain-loop at a given point has sign `1`.  This is
`Milnor.isOrientable_iff_forall_not_reverses_isBall` read through the dictionary. -/
theorem isOrientable_iff_forall_chainSign_eq_one (hm : finrank ℝ E = m) [I.Boundaryless]
    [PreconnectedSpace M] (x₀ : M) :
    IsOrientable I M m ↔ ∀ c : ChartChain I x₀ x₀, c.IsBall → chainSign c = 1 := by
  rw [isOrientable_iff_forall_not_reverses_isBall hm x₀]
  refine ⟨fun h c hc => ?_, fun h c hc => ?_⟩
  · rcases chainSign_eq_one_or_neg_one hm c with h1 | h1
    · exact h1
    · exact absurd ((c.reverses_iff_chainSign hm).2 h1) (h c hc)
  · intro hrev
    have h1 := h c hc
    rw [(c.reverses_iff_chainSign hm).1 hrev] at h1
    exact absurd h1 (by decide)

/-- **A connected non-orientable manifold has, at every point, a ball-chain-loop of sign `-1`.**
This is the form in which the later stages of the plan use the dichotomy. -/
theorem exists_isBall_chainSign_eq_neg_one (hm : finrank ℝ E = m) [I.Boundaryless]
    [PreconnectedSpace M] (h : ¬ IsOrientable I M m) (x₀ : M) :
    ∃ c : ChartChain I x₀ x₀, c.IsBall ∧ chainSign c = -1 := by
  obtain ⟨c, hc, hrev⟩ := exists_isBall_reverses_of_not_isOrientable hm h x₀
  refine ⟨c, hc, (c.reverses_iff_chainSign hm).1 ?_⟩
  exact ⟨(nonempty_orientation (E := E) hm).some, hrev _⟩

/-! ### The transition map between two charts -/

/-- **The transition map** from the chart centred at `q` to the chart centred at `p`, as a map of the
model space to itself.  Unlike the derivative of a single chart, this map does not depend on the
point at which its derivative is taken, and that is what makes the cocycle lemma work. -/
def chartTrans (I : ModelWithCorners ℝ E H) (p q : M) : E → E :=
  fun u => extChartAt I p ((extChartAt I q).symm u)

/-- **The natural domain of the transition map**: the points of the target of the chart at `q` whose
image under the inverse chart lies in the source of the chart at `p`. -/
def chartTransDom (I : ModelWithCorners ℝ E H) (p q : M) : Set E :=
  (extChartAt I q).target ∩ (extChartAt I q).symm ⁻¹' (extChartAt I p).source

/-- **The determinant sign of the derivative of the transition map.** -/
def transSign (I : ModelWithCorners ℝ E H) (p q : M) (u : E) : ℤ :=
  sgn (LinearMap.det (fderiv ℝ (chartTrans I p q) u : E →ₗ[ℝ] E))

/-- The transition sign is the sign of the derivative of the transition map relative to any one
orientation of the model space used at both ends. -/
theorem transSign_eq_orSign (hm : finrank ℝ E = m) (a : Orientation ℝ E (Fin m)) (p q : M)
    (u : E) : transSign I p q u = orSign a a (fderiv ℝ (chartTrans I p q) u) :=
  (orSign_self_eq_sgn_det hm a _).symm

/-- The chart image of a point lying in both chart sources belongs to the domain of the transition
map. -/
theorem mem_chartTransDom {p q z : M} (hzq : z ∈ (extChartAt I q).source)
    (hzp : z ∈ (extChartAt I p).source) : extChartAt I q z ∈ chartTransDom I p q := by
  refine ⟨(extChartAt I q).map_source hzq, ?_⟩
  rw [mem_preimage, (extChartAt I q).left_inv hzq]
  exact hzp

/-- **The domain of the transition map is open.**  Boundarylessness enters through the openness of
the target of a chart. -/
theorem isOpen_chartTransDom [I.Boundaryless] (p q : M) : IsOpen (chartTransDom I p q) :=
  (continuousOn_extChartAt_symm q).isOpen_inter_preimage (isOpen_extChartAt_target q)
    (isOpen_extChartAt_source p)

/-- **The transition map is smooth on its domain**, being the composite of the inverse of one chart
with another chart, both smooth as maps of manifolds. -/
theorem contDiffOn_chartTrans [I.Boundaryless] (p q : M) :
    ContDiffOn ℝ ∞ (chartTrans I p q) (chartTransDom I p q) := by
  rw [← contMDiffOn_iff_contDiffOn]
  have h1 : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I q).symm (chartTransDom I p q) :=
    (contMDiffOn_extChartAt_symm q).mono inter_subset_left
  have h2 : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I p) (extChartAt I p).source := by
    rw [extChartAt_source]; exact contMDiffOn_extChartAt
  exact h2.comp h1 fun u hu => hu.2

/-- **The chain rule for two charts**: at a point of both chart sources the derivative of the chart
at `p` factors as the derivative of the transition map composed with the derivative of the chart at
`q`.  This is the computation that makes the chart at `z` cancel in the product of two Jacobian
signs. -/
theorem mfd_extChartAt_eq_comp [I.Boundaryless] {p q z : M}
    (hzq : z ∈ (extChartAt I q).source) (hzp : z ∈ (extChartAt I p).source) :
    mfd I 𝓘(ℝ, E) (extChartAt I p) z
      = (fderiv ℝ (chartTrans I p q) (extChartAt I q z)).comp
          (mfd I 𝓘(ℝ, E) (extChartAt I q) z) := by
  have hu : extChartAt I q z ∈ chartTransDom I p q := mem_chartTransDom hzq hzp
  have hdq := hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, E))
    ((contMDiffAt_extChartAt' (I := I) (n := ∞) (x := q)
      (by rwa [← extChartAt_source I] : z ∈ (chartAt H q).source)).mdifferentiableAt (by simp))
  have hdp := hasMFDerivAt_mfd (I := I) (J := 𝓘(ℝ, E))
    ((contMDiffAt_extChartAt' (I := I) (n := ∞) (x := p)
      (by rwa [← extChartAt_source I] : z ∈ (chartAt H p).source)).mdifferentiableAt (by simp))
  have hdgd : DifferentiableAt ℝ (chartTrans I p q) (extChartAt I q z) :=
    ((contDiffOn_chartTrans (I := I) p q).contDiffAt
      ((isOpen_chartTransDom (I := I) p q).mem_nhds hu)).differentiableAt (by simp)
  have hdg := hdgd.hasFDerivAt.hasMFDerivAt
  have h2 := hdg.comp z hdq
  have h3 : ⇑(extChartAt I p) =ᶠ[𝓝 z] chartTrans I p q ∘ ⇑(extChartAt I q) := by
    filter_upwards [(isOpen_extChartAt_source q).mem_nhds hzq] with w hw
    simp only [Function.comp_apply, chartTrans]
    rw [(extChartAt I q).left_inv hw]
  exact hasMFDerivAt_unique hdp (h2.congr_of_eventuallyEq h3)

/-- **The Jacobian sign of one chart, in terms of the other**: at a point of both chart sources the
Jacobian sign of the chart at `p` is the transition sign times the Jacobian sign of the chart at
`q`. -/
theorem jacSign_eq_transSign_mul [I.Boundaryless] {p q z : M}
    (hzq : z ∈ (extChartAt I q).source) (hzp : z ∈ (extChartAt I p).source) :
    jacSign I p z = transSign I p q (extChartAt I q z) * jacSign I q z := by
  have h := mfd_extChartAt_eq_comp (I := I) hzq hzp
  unfold jacSign transSign
  rw [h, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, sgn_mul]

/-- **The transition sign is locally constant** where it is nonzero: the derivative of the
transition map is continuous on the (open) domain of that map, and the sign of a continuous family
of invertible linear maps is locally constant
(`Milnor.eventually_orSign_eq_of_continuousAt`). -/
theorem eventually_transSign_eq [I.Boundaryless] (hm : finrank ℝ E = m) {p q : M} {u₀ : E}
    (hu₀ : u₀ ∈ chartTransDom I p q) (h0 : transSign I p q u₀ ≠ 0) :
    ∀ᶠ u in 𝓝 u₀, transSign I p q u = transSign I p q u₀ := by
  obtain ⟨a⟩ := nonempty_orientation (E := E) hm
  have hfd : ContinuousOn (fderiv ℝ (chartTrans I p q)) (chartTransDom I p q) :=
    (contDiffOn_chartTrans (I := I) p q).continuousOn_fderiv_of_isOpen
      (isOpen_chartTransDom (I := I) p q) (by simp)
  have h := eventually_orSign_eq_of_continuousAt hm hm a a
    (hfd.continuousAt ((isOpen_chartTransDom (I := I) p q).mem_nhds hu₀))
    (by rw [← transSign_eq_orSign hm a]; exact h0)
  filter_upwards [h] with u hu
  rw [transSign_eq_orSign hm a, transSign_eq_orSign hm a]
  exact hu

/-- **The transition cocycle lemma.**  For two chart centres `p` and `q` and a point `y` lying in
both chart sources, the product of the two Jacobian signs at `z` is locally constant in `z` near `y`.

Neither factor is continuous in `z`: each of them is the determinant sign of the derivative of a
fixed chart *read through the chart at `z`*, and that reading changes discontinuously with `z`.  In
the product the chart at `z` cancels — by the chain rule `Milnor.mfd_extChartAt_eq_comp` and because
the Jacobian sign of the chart at `q` squares to `1` — and what is left is the determinant sign of
the *fixed* transition map from the chart at `q` to the chart at `p`, which is locally constant
because that map is smooth where it is defined.

This is the technical key of Stage 4 of the plan `Milnor/Exposition/PlanMod2.md`, used twice by the
later stages: to extend a ball-coherent family of orientations across a puncture, and to see that
the sign of a chain does not change when a hop is refined. -/
theorem eventually_jacSign_mul_jacSign_eq [I.Boundaryless] (hm : finrank ℝ E = m) {p q y : M}
    (hyp : y ∈ (extChartAt I p).source) (hyq : y ∈ (extChartAt I q).source) :
    ∀ᶠ z in 𝓝 y, jacSign I p z * jacSign I q z = jacSign I p y * jacSign I q y := by
  have hkey : ∀ z ∈ (extChartAt I p).source ∩ (extChartAt I q).source,
      jacSign I p z * jacSign I q z = transSign I p q (extChartAt I q z) := by
    rintro z ⟨hzp, hzq⟩
    rw [jacSign_eq_transSign_mul hzq hzp, mul_assoc, jacSign_mul_self hm hzq, mul_one]
  have hV : (extChartAt I p).source ∩ (extChartAt I q).source ∈ 𝓝 y :=
    inter_mem ((isOpen_extChartAt_source (I := I) p).mem_nhds hyp)
      ((isOpen_extChartAt_source (I := I) q).mem_nhds hyq)
  have h0 : transSign I p q (extChartAt I q y) ≠ 0 := by
    rw [← hkey y ⟨hyp, hyq⟩]
    exact mul_ne_zero (jacSign_ne_zero hm hyp) (jacSign_ne_zero hm hyq)
  have hloc := eventually_transSign_eq hm (mem_chartTransDom hyq hyp) h0
  have hloc' := (continuousAt_extChartAt' (I := I) (x := q) hyq).eventually hloc
  filter_upwards [hV, hloc'] with z hz hz2
  rw [hkey z hz, hz2, hkey y ⟨hyp, hyq⟩]

/-! ### Closed chart balls, and small chart balls inside a neighbourhood -/

/-- **The closed chart ball** of radius `R` about `c`: the image under the inverse of the chart at
`c` of the *closed* ball of radius `R` about the chart image of `c`.  It contains the chart ball
`Milnor.chartBall I c R`, and when `M` is Hausdorff it contains the closure of the chart ball
(`Milnor.closure_chartBall_subset_closedChartBall`).  Unlike that closure it is controlled with no
separation hypothesis on `M` whatever — in a non-Hausdorff manifold the closure of a chart ball need
not even lie in the source of the chart, as the line with two origins shows — which is why the
avoidance statement below is phrased with it. -/
def closedChartBall (I : ModelWithCorners ℝ E H) (c : M) (R : ℝ) : Set M :=
  (extChartAt I c).symm '' Metric.closedBall (extChartAt I c c) R

/-- A chart ball is contained in the closed chart ball of the same radius. -/
theorem chartBall_subset_closedChartBall {c : M} {R : ℝ} :
    chartBall I c R ⊆ closedChartBall I c R := by
  intro z hz
  refine ⟨extChartAt I c z, ?_, (extChartAt I c).left_inv (mem_chartBall.1 hz).1⟩
  rw [Metric.mem_closedBall]
  exact (mem_chartBall.1 hz).2.le

/-- **In a Hausdorff manifold the closed chart ball contains the closure of the chart ball**: the
closed ball is compact and lies in the target of the chart, so its image under the inverse chart is
compact, hence closed, and it contains the chart ball.  This is the only statement of the file that
uses a separation hypothesis, and nothing else in the file depends on it. -/
theorem closure_chartBall_subset_closedChartBall [T2Space M] {c : M} {R : ℝ}
    (hRt : Metric.closedBall (extChartAt I c c) R ⊆ (extChartAt I c).target) :
    closure (chartBall I c R) ⊆ closedChartBall I c R := by
  have hKc : IsCompact (closedChartBall I c R) :=
    (isCompact_closedBall _ _).image_of_continuousOn ((continuousOn_extChartAt_symm c).mono hRt)
  exact closure_minimal chartBall_subset_closedChartBall hKc.isClosed

/-- **Small chart balls.**  Inside any neighbourhood `S` of `c` there is a radius `R > 0` such that
the *closed* ball of radius `R` about the chart image of `c` lies in the target of the chart at `c` —
so that the chart ball of radius `R` is connected (`Milnor.isPreconnected_chartBall`) and carries ball
hops — and such that the closed chart ball of radius `R` is contained in `S`.

This is the abstract-manifold form of `Milnor.Framed.exists_ballU_subset`
(`Milnor/Chapter7/Segment.lean`, line 32), which is stated for a slice submanifold of a Euclidean
space; the conclusion here is about the closed chart ball rather than the open one, which is what the
avoidance statement below needs.  Boundarylessness of `I` is used for the openness of the target of a
chart, and nothing else. -/
theorem exists_closedChartBall_subset [I.Boundaryless] (c : M) {S : Set M} (hS : S ∈ 𝓝 c) :
    ∃ R > 0, Metric.closedBall (extChartAt I c c) R ⊆ (extChartAt I c).target ∧
      closedChartBall I c R ⊆ S := by
  have h1 : (extChartAt I c).target ∈ 𝓝 (extChartAt I c c) :=
    (isOpen_extChartAt_target c).mem_nhds (mem_extChartAt_target c)
  have h2 : (extChartAt I c).symm ⁻¹' S ∈ 𝓝 (extChartAt I c c) := by
    refine (continuousAt_extChartAt_symm c).preimage_mem_nhds ?_
    rw [extChartAt_to_inv c]
    exact hS
  obtain ⟨R, hR, hR1, hR2⟩ :=
    ((eventually_closedBall_subset h1).and (eventually_closedBall_subset h2)).exists_gt
  refine ⟨R, hR, hR1, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  exact hR2 hu

/-! ### Ball hops that run inside a given set -/

/-- A ball hop **runs inside `C`** if the closed ball of its radius lies in the target of its chart
and the corresponding closed chart ball is contained in `C`.  The first condition makes the closed
chart ball a well-behaved object (in particular a compact set), the second is the containment
itself. -/
def BallHop.RunsIn {x y : M} (b : BallHop I x y) (C : Set M) : Prop :=
  Metric.closedBall (extChartAt I b.hub b.hub) b.rad ⊆ (extChartAt I b.hub).target ∧
    closedChartBall I b.hub b.rad ⊆ C

/-- A ball hop that runs inside `C` has its ball contained in `C`. -/
theorem BallHop.RunsIn.subset {x y : M} {b : BallHop I x y} {C : Set M} (h : b.RunsIn C) :
    chartBall I b.hub b.rad ⊆ C := chartBall_subset_closedChartBall.trans h.2

/-- A ball hop that runs inside `C` runs inside any larger set. -/
theorem BallHop.RunsIn.mono {x y : M} {b : BallHop I x y} {C D : Set M} (h : b.RunsIn C)
    (hCD : C ⊆ D) : b.RunsIn D := ⟨h.1, h.2.trans hCD⟩

/-- A ball hop and its reverse use the same ball, so one runs inside `C` exactly when the other
does. -/
theorem BallHop.RunsIn.symm {x y : M} {b : BallHop I x y} {C : Set M} (h : b.RunsIn C) :
    b.symm.RunsIn C := h

/-- **In a Hausdorff manifold a ball hop that runs inside `C` has the closure of its ball inside
`C`.**  This is the form in which the later stages of the plan use the notion, since the machinery
that moves a framed point inside a ball requires all the other points of the framed set to lie
outside the closure of that ball. -/
theorem BallHop.RunsIn.closure_subset [T2Space M] {x y : M} {b : BallHop I x y} {C : Set M}
    (h : b.RunsIn C) : closure (chartBall I b.hub b.rad) ⊆ C :=
  (closure_chartBall_subset_closedChartBall h.1).trans h.2

/-! ### Ball chains inside an open set, and avoidance -/

/-- **A ball chain inside `C`**: a chart chain each of whose hops comes from a ball hop running
inside `C`, that is, one whose closed chart ball is contained in `C`.  As with
`Milnor.ChartChain.IsBall` this is a predicate on `Milnor.ChartChain` rather than a separate
inductive type of chains, so that composition, reversal, transport and the sign are literally the
notions already defined; only the closure of the predicate under those constructions has to be
proved. -/
inductive ChartChain.IsBallIn (C : Set M) : ∀ {x y : M}, ChartChain I x y → Prop
  /-- the empty chain is a ball chain inside `C` -/
  | nil (x : M) : ChartChain.IsBallIn C (ChartChain.nil (I := I) x)
  /-- a ball hop running inside `C`, prepended to a ball chain inside `C` -/
  | cons {x y z : M} (b : BallHop I x y) (hb : b.RunsIn C)
      {c : ChartChain I y z} (hc : ChartChain.IsBallIn C c) :
      ChartChain.IsBallIn C (ChartChain.cons b.toChartHop c)

/-- A ball chain inside `C` is a ball chain. -/
theorem ChartChain.IsBallIn.isBall {C : Set M} : ∀ {x y : M} {c : ChartChain I x y},
    c.IsBallIn C → c.IsBall := by
  intro x y c hc
  induction hc with
  | nil a => exact ChartChain.IsBall.nil a
  | cons b hb hc ih => exact ChartChain.IsBall.cons b ih

/-- **A ball chain inside `C` is a ball chain inside any larger set.** -/
theorem ChartChain.IsBallIn.mono : ∀ {x y : M} {c : ChartChain I x y} {C D : Set M},
    c.IsBallIn C → C ⊆ D → c.IsBallIn D := by
  intro x y c C D hc
  induction hc with
  | nil a => intro _; exact ChartChain.IsBallIn.nil a
  | cons b hb hc ih => intro h; exact ChartChain.IsBallIn.cons b (hb.mono h) (ih h)

/-- The chain consisting of a single ball hop running inside `C` is a ball chain inside `C`. -/
theorem ChartChain.IsBallIn.hop {C : Set M} {x y : M} (b : BallHop I x y) (hb : b.RunsIn C) :
    (ChartChain.hop b.toChartHop).IsBallIn C :=
  ChartChain.IsBallIn.cons b hb (ChartChain.IsBallIn.nil y)

/-- **Ball chains inside `C` compose.** -/
theorem ChartChain.IsBallIn.comp {C : Set M} : ∀ {x y : M} {c : ChartChain I x y}, c.IsBallIn C →
    ∀ {z : M} {d : ChartChain I y z}, d.IsBallIn C → (c.comp d).IsBallIn C := by
  intro x y c hc
  induction hc with
  | nil a => intro z d hd; exact hd
  | cons b hb hc ih => intro z d hd; exact ChartChain.IsBallIn.cons b hb (ih hd)

/-- **Ball chains inside `C` reverse**, a ball hop and its reverse using the same ball. -/
theorem ChartChain.IsBallIn.reverse {C : Set M} : ∀ {x y : M} {c : ChartChain I x y},
    c.IsBallIn C → c.reverse.IsBallIn C := by
  intro x y c hc
  induction hc with
  | nil a => exact ChartChain.IsBallIn.nil a
  | cons b hb hc ih => exact ih.comp (ChartChain.IsBallIn.hop b.symm hb.symm)

/-- **A ball chain inside `C` extended by one further ball hop** running inside `C`. -/
theorem ChartChain.IsBallIn.snoc {C : Set M} {x y z : M} {c : ChartChain I x y}
    (hc : c.IsBallIn C) (b : BallHop I y z) (hb : b.RunsIn C) :
    (c.comp (ChartChain.hop b.toChartHop)).IsBallIn C :=
  hc.comp (ChartChain.IsBallIn.hop b hb)

/-- `y` is **ball-reachable inside `C`** from `x` if some ball chain inside `C` joins `x` to `y`. -/
def BallReachableIn (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] (C : Set M) (x y : M) : Prop :=
  ∃ c : ChartChain I x y, c.IsBallIn C

/-- Ball-reachability inside `C` is reflexive. -/
theorem BallReachableIn.refl (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M] (C : Set M) (x : M) :
    BallReachableIn I C x x :=
  ⟨ChartChain.nil x, ChartChain.IsBallIn.nil x⟩

/-- Ball-reachability inside `C` is symmetric, because ball chains inside `C` reverse. -/
theorem BallReachableIn.symm {C : Set M} {x y : M} (h : BallReachableIn I C x y) :
    BallReachableIn I C y x :=
  let ⟨c, hc⟩ := h; ⟨c.reverse, hc.reverse⟩

/-- Ball-reachability inside `C` is transitive, because ball chains inside `C` compose. -/
theorem BallReachableIn.trans {C : Set M} {x y z : M} (h : BallReachableIn I C x y)
    (h' : BallReachableIn I C y z) : BallReachableIn I C x z :=
  let ⟨c, hc⟩ := h; let ⟨d, hd⟩ := h'; ⟨c.comp d, hc.comp hd⟩

/-- A ball chain inside `C` is in particular a ball chain, so ball-reachability inside `C` implies
ball-reachability. -/
theorem BallReachableIn.ballReachable {C : Set M} {x y : M} (h : BallReachableIn I C x y) :
    BallReachable I x y :=
  let ⟨c, hc⟩ := h; ⟨c, hc.isBall⟩

/-- **Every point near a point of the open set `C` lies in `C` and is ball-reachable inside `C`**,
by the single ball hop from the centre of a small chart ball whose closed chart ball lies in `C`
(`Milnor.exists_closedChartBall_subset`).  This is the local step of the clopen argument below,
and the analogue of `Milnor.eventually_ballReachable`. -/
theorem eventually_mem_and_ballReachableIn [I.Boundaryless] {C : Set M} (hC : IsOpen C) {z : M}
    (hz : z ∈ C) : ∀ᶠ w in 𝓝 z, w ∈ C ∧ BallReachableIn I C z w := by
  obtain ⟨R, hR, hRt, hcl⟩ := exists_closedChartBall_subset (I := I) z (hC.mem_nhds hz)
  have hRb : Metric.ball (extChartAt I z z) R ⊆ (extChartAt I z).target :=
    Metric.ball_subset_closedBall.trans hRt
  filter_upwards [(isOpen_chartBall (I := I) z R).mem_nhds
    (self_mem_chartBall (I := I) z hR)] with w hw
  refine ⟨hcl (chartBall_subset_closedChartBall hw), ?_⟩
  exact ⟨ChartChain.hop (BallHop.ofCentre hR hRb hw).toChartHop,
    ChartChain.IsBallIn.hop (BallHop.ofCentre hR hRb hw) ⟨hRt, hcl⟩⟩

/-- **Ball reachability inside a preconnected open set.**  Any two points of an open preconnected
subset `C` of the manifold are joined by a chain of ball hops each of which runs inside `C`, that is,
the closed chart ball of each of which is contained in `C`.

The argument is the clopen argument of `Milnor.ballReachable_of_preconnectedSpace` run inside `C`
instead of inside `M`: the set of points of `C` reachable from `x` inside `C` and the set of points
of `C` not so reachable are both open, by `Milnor.eventually_mem_and_ballReachableIn`, they are
disjoint, they cover `C`, and the first contains `x`; so preconnectedness of `C`
(`IsPreconnected.subset_left_of_subset_union`) forces the second to miss `C`.  No local
connectedness of `M`, no Hausdorffness and no hypothesis on the dimension is used. -/
theorem exists_isBallIn [I.Boundaryless] {C : Set M} (hC : IsOpen C) (hconn : IsPreconnected C)
    {x y : M} (hx : x ∈ C) (hy : y ∈ C) : ∃ c : ChartChain I x y, c.IsBallIn C := by
  set u : Set M := {z | z ∈ C ∧ BallReachableIn I C x z} with hu_def
  set v : Set M := {z | z ∈ C ∧ ¬ BallReachableIn I C x z} with hv_def
  have hu : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzC, hzR⟩
    filter_upwards [eventually_mem_and_ballReachableIn (I := I) hC hzC] with w hw
    exact ⟨hw.1, hzR.trans hw.2⟩
  have hv : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzC, hzR⟩
    filter_upwards [eventually_mem_and_ballReachableIn (I := I) hC hzC] with w hw
    exact ⟨hw.1, fun hwR => hzR (hwR.trans hw.2.symm)⟩
  have hduv : Disjoint u v := by
    rw [Set.disjoint_left]
    rintro z ⟨-, hzR⟩ ⟨-, hzR'⟩
    exact hzR' hzR
  have hcover : C ⊆ u ∪ v := by
    intro z hzC
    by_cases h : BallReachableIn I C x z
    · exact Or.inl ⟨hzC, h⟩
    · exact Or.inr ⟨hzC, h⟩
  have hCu : C ⊆ u :=
    hconn.subset_left_of_subset_union hu hv hduv hcover
      ⟨x, hx, hx, ⟨ChartChain.nil x, ChartChain.IsBallIn.nil x⟩⟩
  exact (hCu hy).2

/-- **Ball reachability avoiding a set.**  Let `C` be an open preconnected subset of the manifold
and `P` a set disjoint from `C`.  Then any two points of `C` are joined by a chain of ball hops which
stays inside `C` — the closed chart ball of each of its hops is contained in `C` — and therefore
avoids `P`: the closed chart ball of each of its hops is contained in the complement of `P`.  When
`M` is Hausdorff the closure of each ball of the chain is contained in `C`, and misses `P`, by
`Milnor.BallHop.RunsIn.closure_subset`.

This is the statement the later stages of the plan `Milnor/Exposition/PlanMod2.md` need in order to
slide a framed point along a chain of balls without any ball meeting the other points of the framed
set: those other points form the set `P`, and the component of the complement of `P` is the set `C`.
It is worth recording that `P` is *not* required to be closed, and `C` not to be connected but only
preconnected: once every ball of the chain, with its closed chart ball, lies in `C`, avoidance of any
set disjoint from `C` is automatic. -/
theorem exists_isBallIn_avoiding [I.Boundaryless] {C P : Set M} (hC : IsOpen C)
    (hconn : IsPreconnected C) (hdisj : Disjoint C P) {x y : M} (hx : x ∈ C) (hy : y ∈ C) :
    ∃ c : ChartChain I x y, c.IsBall ∧ c.IsBallIn C ∧ c.IsBallIn Pᶜ := by
  obtain ⟨c, hc⟩ := exists_isBallIn (I := I) hC hconn hx hy
  exact ⟨c, hc.isBall, hc, hc.mono fun z hz => Set.disjoint_left.1 hdisj hz⟩

end Milnor
