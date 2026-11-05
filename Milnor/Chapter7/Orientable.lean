import Milnor.Chapter7.OrientTransport
import Milnor.Chapter6.LevelZero

/-!
# The orientability dichotomy

Milnor's remark at the end of §7 (p. 50) says, in one line, that for a *connected non-orientable*
manifold the smooth maps to a sphere are classified by the degree modulo `2`.  What that line rests
on is a dichotomy about the manifold itself: either the orientations of the tangent spaces can be
chosen coherently once and for all, or else some closed chain of charts brings an orientation back
reversed, and then a frame carried around that chain comes back with the opposite orientation.
This file proves the dichotomy, on top of the transport of orientations built in
`Milnor.Chapter7.OrientTransport`.

* **Orientability.**  `IsOrientable I M m` says that `M` carries a `Milnor.Orient`, i.e. a family
  of orientations of the tangent spaces which is compatible with the charts *near* every point.

* **Reversing loops.**  A chain-loop `c : ChartChain I x x` *reverses* (`ChartChain.Reverses`) if
  its transport carries some orientation at `x` to the opposite one.  Which orientation is tested
  is immaterial (`ChartChain.reverses_iff`), because transport commutes with reversal of
  orientations (`ChartChain.transport_neg`): a loop that reverses one of the two orientations at
  `x` reverses both.

* **Independence of the chain.**  If no chain-loop at `x₀` reverses, then the orientation
  transported from `x₀` to `y` is the same for every chain from `x₀` to `y`
  (`ChartChain.transport_eq_of_forall_not_reverses`): given two chains, follow the first by the
  reverse of the second to get a loop at `x₀`.

* **The dichotomy.**  For connected `M`: if no chain-loop at a point reverses then `M` is
  orientable (`isOrientable_of_forall_not_reverses`) — transport a fixed orientation from the base
  point along a chain, which exists by connectedness and gives an unambiguous answer by the
  previous item.  Contrapositively, a connected manifold that is *not* orientable carries, at every
  one of its points, a chain-loop whose transport reverses every orientation there
  (`exists_reverses_of_not_isOrientable`); this is the form the next stage uses.

* **The converse, and a warning.**  In the other direction an orientation of `M` forbids reversing
  loops as soon as it is coherent with each chart on the *whole* of that chart's source
  (`IsChartCoherent`, `IsChartCoherent.not_reverses`), and the orientation produced above is of
  that kind (`isChartCoherent_transportFrom`); so for connected `M` the absence of reversing loops
  is *equivalent* to the existence of a chart-coherent orientation
  (`exists_isChartCoherent_iff_forall_not_reverses`).  The compatibility demanded by
  `Milnor.Orient` is only a condition near each point, and it does **not** by itself rule out
  reversing loops: if the source of the chart at `x` is disconnected, the chart may carry the
  orientation chosen at a far component of its source to the reverse of the one chosen at `x`, and
  a loop out through that chart and back through small charts then reverses.  (Concretely, put on
  `M = ℝ` the atlas consisting of the identity together with the chart `x ↦ x` on `(-1, 0)`,
  `x ↦ 3 - x` on `(1, 2)`, and let the chart at a point of `(-1, 0) ∪ (1, 2)` be the second one.
  This is a perfectly good smooth structure on `ℝ`, and `ℝ` is orientable, but the loop
  `-1/2 ↦ 3/2 ↦ -1/2`, out through the second chart and back through the identity chart, reverses.)
  Passing from `Milnor.Orient` to a chart-coherent orientation needs the sources of the charts to
  be connected, and is not attempted here.

* **Exactly two orientations.**  On a connected manifold an orientation is determined by its value
  at one point, so there are exactly two orientations, a given one and its pointwise reverse
  (`Orient.or_eq_or_eq_neg`, `Orient.neg`, `Orient.or_ne_neg`, `Orient.setOf_or_eq`).
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

/-! ### Orientability -/

/-- **`M` is orientable** if it carries an orientation in the sense of `Milnor.Orient`: a family of
orientations of the tangent spaces which near every point is compatible with the chart there. -/
def IsOrientable (I : ModelWithCorners ℝ E H) (M : Type u) [TopologicalSpace M]
    [ChartedSpace H M] (m : ℕ) : Prop :=
  Nonempty (Orient I M m)

/-- An orientation of `M` witnesses that `M` is orientable. -/
theorem Orient.isOrientable (o : Orient I M m) : IsOrientable I M m := ⟨o⟩

/-- An orientation chosen from a proof of orientability. -/
def IsOrientable.orient (h : IsOrientable I M m) : Orient I M m := Nonempty.some h

/-- The orientation field of the orientation chosen by `IsOrientable.orient`. -/
theorem IsOrientable.orient_or (h : IsOrientable I M m) : h.orient.or = (Nonempty.some h).or := rfl

/-- The empty manifold is orientable: there is nothing to choose. -/
theorem isOrientable_of_isEmpty [IsEmpty M] : IsOrientable I M m :=
  ⟨⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩⟩

/-- A non-orientable manifold has at least one point. -/
theorem nonempty_of_not_isOrientable (h : ¬ IsOrientable I M m) : Nonempty M := by
  by_contra hM
  rw [not_nonempty_iff] at hM
  exact h isOrientable_of_isEmpty

/-- A real vector space of dimension `m` has an orientation, namely that of a basis. -/
theorem nonempty_orientation (hm : finrank ℝ E = m) : Nonempty (Orientation ℝ E (Fin m)) :=
  ⟨(finBasisOfFinrankEq ℝ E hm).orientation⟩

/-! ### Loops that reverse orientation -/

/-- Transport along a hop commutes with reversal of orientations, since transport across one chart
does. -/
theorem ChartHop.transport_neg (hm : finrank ℝ E = m) {x y : M} (h : ChartHop I x y)
    (o : Orientation ℝ E (Fin m)) : h.transport (-o) = -h.transport o := by
  change Milnor.orTransport I h.hub y (Milnor.orTransport I h.hub x (-o))
      = -Milnor.orTransport I h.hub y (Milnor.orTransport I h.hub x o)
  rw [Milnor.orTransport_neg hm, Milnor.orTransport_neg hm]

/-- **Transport along a chain commutes with reversal of orientations.** -/
theorem ChartChain.transport_neg (hm : finrank ℝ E = m) :
    ∀ {x y : M} (c : ChartChain I x y) (o : Orientation ℝ E (Fin m)),
      c.transport (-o) = -c.transport o := by
  intro x y c
  induction c with
  | nil a => intro o; simp
  | cons h c ih => intro o; simp only [transport_cons, h.transport_neg hm, ih]

/-- A chain-loop at `x` **reverses** if its transport carries some orientation at `x` to the
opposite orientation.  It does not matter which of the two orientations at `x` is tested
(`ChartChain.reverses_iff`): transport commutes with reversal of orientations
(`ChartChain.transport_neg`), so a loop that reverses one of them reverses the other as well. -/
def ChartChain.Reverses {x : M} (c : ChartChain I x x) (m : ℕ) : Prop :=
  ∃ o : Orientation ℝ E (Fin m), c.transport o = -o

/-- `ChartChain.Reverses` unfolded. -/
theorem ChartChain.reverses_def {x : M} (c : ChartChain I x x) (m : ℕ) :
    c.Reverses m ↔ ∃ o : Orientation ℝ E (Fin m), c.transport o = -o := Iff.rfl

/-- **Reversing is independent of the orientation tested**: a loop reverses if and only if it
reverses the given orientation `o`. -/
theorem ChartChain.reverses_iff (hm : finrank ℝ E = m) {x : M} (c : ChartChain I x x)
    (o : Orientation ℝ E (Fin m)) : c.Reverses m ↔ c.transport o = -o := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (c.reverses_def m).1 h
    rcases eq_or_eq_neg hm o a with hoa | hoa
    · rw [hoa]; exact ha
    · rw [hoa, ChartChain.transport_neg hm, ha]
  · intro h
    exact (c.reverses_def m).2 ⟨o, h⟩

/-- A reversing loop reverses **every** orientation at its base point. -/
theorem ChartChain.Reverses.transport_eq_neg (hm : finrank ℝ E = m) {x : M}
    {c : ChartChain I x x} (h : c.Reverses m) (o : Orientation ℝ E (Fin m)) :
    c.transport o = -o := (c.reverses_iff hm o).1 h

/-! ### Independence of the chain -/

/-- **The transported orientation does not depend on the chain.**  If no chain-loop at `x₀`
reverses, then any two chains from `x₀` to `y` transport an orientation at `x₀` to the same
orientation at `y`: otherwise the first chain followed by the reverse of the second would be a
reversing loop at `x₀`. -/
theorem ChartChain.transport_eq_of_forall_not_reverses (hm : finrank ℝ E = m) {x₀ : M}
    (hno : ∀ c : ChartChain I x₀ x₀, ¬ c.Reverses m) {y : M} (c d : ChartChain I x₀ y)
    (o : Orientation ℝ E (Fin m)) : c.transport o = d.transport o := by
  rcases eq_or_eq_neg hm (c.transport o) (d.transport o) with h | h
  · exact h
  · refine absurd (((c.comp d.reverse).reverses_def m).2 ⟨o, ?_⟩) (hno (c.comp d.reverse))
    rw [ChartChain.transport_comp, h, ChartChain.transport_neg hm, ChartChain.transport_reverse hm]

/-! ### Orientations coherent with each chart on its whole source -/

/-- A family of orientations is **chart-coherent** if for every point `x` and every point `y` of
the source of the chart centred at `x` — not merely for `y` near `x`, as `Milnor.Orient` demands —
the orientation at `y` is the transport of the orientation at `x` across that chart.  This is the
condition under which a chart, and hence a hop, is guaranteed to carry the chosen orientations to
one another; see the warning in the module docstring. -/
def IsChartCoherent (I : ModelWithCorners ℝ E H) (or : M → Orientation ℝ E (Fin m)) : Prop :=
  ∀ x y : M, y ∈ (extChartAt I x).source → or y = orTransport I x y (or x)

/-- A chart-coherent family is a transport section, because the source of the chart at `x` is a
neighbourhood of `x`; so it is an orientation of `M`. -/
theorem IsChartCoherent.isTransportSection {or : M → Orientation ℝ E (Fin m)}
    (h : IsChartCoherent I or) : IsTransportSection I or := by
  intro x
  filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy using h x y hy

/-- The orientation of `M` defined by a chart-coherent family. -/
def IsChartCoherent.orient (hm : finrank ℝ E = m) {or : M → Orientation ℝ E (Fin m)}
    (h : IsChartCoherent I or) : Orient I M m :=
  Orient.ofTransportSection hm h.isTransportSection

/-- The orientation field of `IsChartCoherent.orient` is the given family. -/
@[simp] theorem IsChartCoherent.orient_or (hm : finrank ℝ E = m)
    {or : M → Orientation ℝ E (Fin m)} (h : IsChartCoherent I or) :
    (h.orient hm).or = or := rfl

/-- A chart-coherent family gives `M` an orientation, hence makes `M` orientable. -/
theorem IsChartCoherent.isOrientable (hm : finrank ℝ E = m) {or : M → Orientation ℝ E (Fin m)}
    (h : IsChartCoherent I or) : IsOrientable I M m := ⟨h.orient hm⟩

/-- **A hop preserves a chart-coherent family**: the orientation at the source point is carried to
the orientation at the target point.  Both points lie in the source of the hop's chart, where
coherence with that chart is available. -/
theorem IsChartCoherent.hop_transport (hm : finrank ℝ E = m) {or : M → Orientation ℝ E (Fin m)}
    (hc : IsChartCoherent I or) {x y : M} (h : ChartHop I x y) :
    h.transport (or x) = or y := by
  have hx := hc h.hub x h.mem_left
  have hy := hc h.hub y h.mem_right
  change Milnor.orTransport I h.hub y (Milnor.orTransport I h.hub x (or x)) = or y
  rw [hx, orTransport_involutive hm h.hub x, ← hy]

/-- **A chain preserves a chart-coherent family**, by induction on its hops. -/
theorem IsChartCoherent.chain_transport (hm : finrank ℝ E = m)
    {or : M → Orientation ℝ E (Fin m)} (hc : IsChartCoherent I or) :
    ∀ {x y : M} (c : ChartChain I x y), c.transport (or x) = or y := by
  intro x y c
  induction c with
  | nil a => simp
  | cons h c ih => rw [ChartChain.transport_cons, hc.hop_transport hm h, ih]

/-- **A chart-coherent orientation forbids reversing loops**: a loop at `x` returns the orientation
at `x` unchanged, and an orientation is never its own reverse. -/
theorem IsChartCoherent.not_reverses (hm : finrank ℝ E = m) {or : M → Orientation ℝ E (Fin m)}
    (hc : IsChartCoherent I or) {x : M} (c : ChartChain I x x) : ¬ c.Reverses m := by
  intro h
  have h1 := h.transport_eq_neg hm (or x)
  rw [hc.chain_transport hm c] at h1
  exact ne_neg (or x) h1

/-! ### From the absence of reversing loops to an orientation -/

/-- A chain from `x₀` to `y`, chosen once and for all with the axiom of choice; it exists in a
connected manifold by `Milnor.nonempty_chartChain`. -/
def someChain (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    [PreconnectedSpace M] (x₀ y : M) : ChartChain I x₀ y :=
  (nonempty_chartChain (I := I) x₀ y).some

/-- **The candidate orientation field**: transport the orientation `o₀` at the base point `x₀`
along a chosen chain to every point of `M`. -/
def transportFrom (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    [PreconnectedSpace M] (x₀ : M) (o₀ : Orientation ℝ E (Fin m)) :
    M → Orientation ℝ E (Fin m) :=
  fun y => (someChain I x₀ y).transport o₀

/-- If no chain-loop at `x₀` reverses, the candidate orientation field is computed by **every**
chain from `x₀`, not only by the chosen one. -/
theorem transportFrom_eq (hm : finrank ℝ E = m) [PreconnectedSpace M] {x₀ : M}
    (hno : ∀ c : ChartChain I x₀ x₀, ¬ c.Reverses m) (o₀ : Orientation ℝ E (Fin m)) {y : M}
    (c : ChartChain I x₀ y) : transportFrom I x₀ o₀ y = c.transport o₀ :=
  ChartChain.transport_eq_of_forall_not_reverses hm hno (someChain I x₀ y) c o₀

/-- **The candidate orientation field is chart-coherent.**  For `y` in the source of the chart at
`x`, extend a chain from `x₀` to `x` by the point `y` (`ChartChain.snoc`): the extended chain
transports by one further application of `Milnor.orTransport I x y`, and by independence of the
chain it computes the field at `y`. -/
theorem isChartCoherent_transportFrom (hm : finrank ℝ E = m) [PreconnectedSpace M] {x₀ : M}
    (hno : ∀ c : ChartChain I x₀ x₀, ¬ c.Reverses m) (o₀ : Orientation ℝ E (Fin m)) :
    IsChartCoherent I (transportFrom I x₀ o₀) := by
  intro x y hy
  rw [transportFrom_eq hm hno o₀ ((someChain I x₀ x).snoc hy), ChartChain.transport_snoc,
    transportFrom_eq hm hno o₀ (someChain I x₀ x)]

/-- **Half of the dichotomy: a connected manifold with no reversing chain-loop is orientable.**
The orientation obtained is even chart-coherent. -/
theorem exists_isChartCoherent_of_forall_not_reverses (hm : finrank ℝ E = m)
    [PreconnectedSpace M] {x₀ : M} (hno : ∀ c : ChartChain I x₀ x₀, ¬ c.Reverses m) :
    ∃ or : M → Orientation ℝ E (Fin m), IsChartCoherent I or :=
  ⟨transportFrom I x₀ (nonempty_orientation hm).some,
    isChartCoherent_transportFrom hm hno (nonempty_orientation hm).some⟩

/-- **A connected manifold with no reversing chain-loop is orientable.** -/
theorem isOrientable_of_forall_not_reverses (hm : finrank ℝ E = m) [PreconnectedSpace M] {x₀ : M}
    (hno : ∀ c : ChartChain I x₀ x₀, ¬ c.Reverses m) : IsOrientable I M m :=
  let ⟨_, hor⟩ := exists_isChartCoherent_of_forall_not_reverses hm hno
  hor.isOrientable hm

/-- **The orientability dichotomy.**  For a connected manifold and any base point, the absence of
reversing chain-loops at that point is equivalent to the existence of an orientation coherent with
every chart on the whole of its source.  Either way `M` is then orientable
(`Milnor.isOrientable_of_forall_not_reverses`); the plain converse of that implication fails for
`Milnor.Orient`, as explained in the module docstring. -/
theorem exists_isChartCoherent_iff_forall_not_reverses (hm : finrank ℝ E = m)
    [PreconnectedSpace M] (x₀ : M) :
    (∃ or : M → Orientation ℝ E (Fin m), IsChartCoherent I or) ↔
      ∀ c : ChartChain I x₀ x₀, ¬ c.Reverses m := by
  constructor
  · intro h c
    obtain ⟨or, hor⟩ := h
    exact hor.not_reverses hm c
  · intro hno
    exact exists_isChartCoherent_of_forall_not_reverses hm hno

/-- **A connected non-orientable manifold has a reversing loop at every point**, and that loop
reverses every orientation there.  This is the contrapositive of
`Milnor.isOrientable_of_forall_not_reverses`, and the form in which the next stage uses it. -/
theorem exists_reverses_of_not_isOrientable (hm : finrank ℝ E = m) [PreconnectedSpace M]
    (h : ¬ IsOrientable I M m) (x₀ : M) :
    ∃ c : ChartChain I x₀ x₀, ∀ o : Orientation ℝ E (Fin m), c.transport o = -o := by
  by_contra hcon
  refine h (isOrientable_of_forall_not_reverses hm (x₀ := x₀) ?_)
  intro c hrev
  exact hcon ⟨c, fun o => hrev.transport_eq_neg hm o⟩

/-- **A connected non-orientable manifold has a point and a chain-loop at it whose transport
reverses every orientation there.** -/
theorem exists_point_reverses_of_not_isOrientable (hm : finrank ℝ E = m) [PreconnectedSpace M]
    (h : ¬ IsOrientable I M m) :
    ∃ (x : M) (c : ChartChain I x x), ∀ o : Orientation ℝ E (Fin m), c.transport o = -o := by
  obtain ⟨x₀⟩ := nonempty_of_not_isOrientable h
  exact ⟨x₀, exists_reverses_of_not_isOrientable hm h x₀⟩

/-! ### A connected orientable manifold has exactly two orientations -/

/-- **On a connected manifold an orientation is determined by its value at one point**: any two
orientations of `M` agree everywhere or are opposite everywhere.  The set where they agree is open
and its complement is open, because near each point both are transports of their values there and
transport is injective and commutes with reversal. -/
theorem Orient.or_eq_or_eq_neg (hm : finrank ℝ E = m) [PreconnectedSpace M]
    (o o' : Orient I M m) : o'.or = o.or ∨ o'.or = fun y => -o.or y := by
  have hopen : IsOpen {y : M | o'.or y = o.or y} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hy' : o'.or y = o.or y := hy
    filter_upwards [o.isTransportSection hm y, o'.isTransportSection hm y] with z hz hz'
    show o'.or z = o.or z
    rw [hz, hz', hy']
  have hclosed : IsClosed {y : M | o'.or y = o.or y} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    have hy' : ¬ o'.or y = o.or y := hy
    filter_upwards [o.isTransportSection hm y, o'.isTransportSection hm y] with z hz hz'
    intro hcon
    exact hy' (orTransport_injective hm y z (by rw [← hz', ← hz]; exact hcon))
  by_cases hex : ∃ y : M, o'.or y = o.or y
  · left
    obtain ⟨y₀, hy₀⟩ := hex
    have huniv := (IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨y₀, hy₀⟩)
    funext y
    have hmem : y ∈ {y : M | o'.or y = o.or y} := by rw [huniv]; exact mem_univ y
    exact hmem
  · right
    funext y
    rcases eq_or_eq_neg hm (o'.or y) (o.or y) with h | h
    · exact absurd ⟨y, h⟩ hex
    · exact h

/-- **The two orientations of a nonempty manifold are distinct**, since an orientation of a vector
space is never its own reverse. -/
theorem Orient.or_ne_neg (o : Orient I M m) (x : M) : o.or ≠ fun y => -o.or y := fun h =>
  ne_neg (o.or x) (congrFun h x)

/-- **A connected orientable manifold has exactly two orientations**: the orientation fields of
`M` are exactly a given one and its pointwise reverse (distinct by `Milnor.Orient.or_ne_neg`). -/
theorem Orient.setOf_or_eq (hm : finrank ℝ E = m) [PreconnectedSpace M] (o : Orient I M m) :
    {f : M → Orientation ℝ E (Fin m) | ∃ o' : Orient I M m, o'.or = f}
      = {o.or, fun y => -o.or y} := by
  ext f
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨o', rfl⟩ := h
    exact o.or_eq_or_eq_neg hm o'
  · intro h
    rcases h with h | h
    · exact ⟨o, h.symm⟩
    · exact ⟨o.neg hm, h.symm⟩

end Milnor
