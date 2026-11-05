import Milnor.Chapter5.LevelOrient

/-!
# Transport of an orientation across a chart, and chains of charts

Milnor remarks at the end of §7 (p. 50) that for a *connected non-orientable* manifold the smooth
maps to a sphere are classified by the degree modulo `2`.  The hidden content of the remark is that
a non-orientable manifold carries a loop along which a frame comes back reversed.  Neither Mathlib
nor this development has any notion of orientability of a manifold, so the transport of an
orientation has to be built first; this file is the first stage of that construction, and a later
file will prove the dichotomy "no reversing loop implies orientable".

Throughout, `M` is a manifold modelled on a finite-dimensional real space `E` with
`finrank ℝ E = m`, and `mfd I 𝓘(ℝ, E) (extChartAt I x) y` is the derivative at `y` of the chart
centred at `x`, as in `Milnor.Orient`.

* **One chart.**  For `y` in the source of the chart at `x` that derivative is a linear
  isomorphism of `E` (`isInvertible_mfd_extChartAt`, from Mathlib's
  `isInvertible_mfderiv_extChartAt`), and it is the identity for `y = x`
  (`mfd_extChartAt_self`).  Hence exactly one orientation of the tangent space at `y` is carried
  by it to a given orientation `o` at `x`: this is `orTransport I x y o`, characterised by
  `orSign (orTransport I x y o) o (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = 1` (`orSign_transport`,
  `eq_transport`).  Transport is an involution, hence bijective, and anticommutes with reversal
  of orientations.

* **Orientations are transport sections.**  The compatibility field of `Milnor.Orient` says
  exactly that an orientation of `M` is a family of orientations of the tangent spaces which near
  every point is the transport of its value at that point: `Orient.isTransportSection` and
  `Orient.ofTransportSection`.

* **Chains.**  A `ChartHop I x y` is one chart (given by its centre `hub`) whose source contains
  both `x` and `y`; it transports an orientation at `x` to one at `y` through that single chart.
  A `ChartChain I x y` is a finite sequence of hops from `x` to `y`; its list of vertices
  (`ChartChain.verts`) is a list of points beginning with `x` and ending with `y` in which
  consecutive points are chart-related.  Chains compose (`ChartChain.comp`) and reverse
  (`ChartChain.reverse`), transport along a composite is the composite of the transports
  (`ChartChain.transport_comp`), and transport along the reverse undoes transport along the chain
  (`ChartChain.transport_reverse`).  Finally in a connected manifold any two points are joined by
  a chain (`reachable_of_preconnectedSpace`), because the set of points reachable from a fixed
  point is open and closed: chart sources are open and contain their centre.
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

/-! ### The derivative of a chart is a linear isomorphism -/

/-- **The derivative of a chart is invertible.**  At a point `y` of the source of the chart
centred at `x`, the derivative of that chart is a linear automorphism of the model space `E`. -/
theorem isInvertible_mfd_extChartAt {x y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfd I 𝓘(ℝ, E) (extChartAt I x) y).IsInvertible :=
  _root_.isInvertible_mfderiv_extChartAt hy

/-- The derivative at `y` of the chart centred at `x` is bijective. -/
theorem bijective_mfd_extChartAt {x y : M} (hy : y ∈ (extChartAt I x).source) :
    Function.Bijective (mfd I 𝓘(ℝ, E) (extChartAt I x) y) := by
  obtain ⟨A, hA⟩ := isInvertible_mfd_extChartAt hy
  have h : ⇑(mfd I 𝓘(ℝ, E) (extChartAt I x) y) = ⇑A := by rw [← hA]; rfl
  rw [h]
  exact A.bijective

/-! ### Exactly two orientations -/

/-- The sign of a linear map is `1`, `-1` or `0`. -/
theorem orSign_mem (a b : Orientation ℝ E (Fin m)) (T : E →L[ℝ] E) :
    orSign a b T = 1 ∨ orSign a b T = -1 ∨ orSign a b T = 0 := sgn_mem

/-- An orientation is never its own reverse. -/
theorem ne_neg (a : Orientation ℝ E (Fin m)) : a ≠ -a := Module.Ray.ne_neg_self a

/-- **A finite-dimensional real vector space has exactly two orientations**: any orientation is a
given one or its reverse (and by `Milnor.ne_neg` these two are distinct). -/
theorem eq_or_eq_neg (hm : finrank ℝ E = m) (a b : Orientation ℝ E (Fin m)) : a = b ∨ a = -b := by
  set e := finBasisOfFinrankEq ℝ E hm
  rcases e.orientation_eq_or_eq_neg a with ha | ha <;>
    rcases e.orientation_eq_or_eq_neg b with hb | hb
  · exact Or.inl (by rw [ha, hb])
  · exact Or.inr (by rw [ha, hb]; exact (neg_neg e.orientation).symm)
  · exact Or.inr (by rw [ha, hb])
  · exact Or.inl (by rw [ha, hb])

/-- Since the derivative of a chart is invertible, the sign it gives to a pair of orientations is
`1` or `-1`. -/
theorem orSign_mfd_extChartAt_ne_zero (hm : finrank ℝ E = m) {x y : M}
    (hy : y ∈ (extChartAt I x).source) (a b : Orientation ℝ E (Fin m)) :
    orSign a b (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = 1 ∨
      orSign a b (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = -1 := by
  have h0 : orSign a b (mfd I 𝓘(ℝ, E) (extChartAt I x) y) ≠ 0 :=
    (orSign_ne_zero_iff hm hm a b _).2 (bijective_mfd_extChartAt hy)
  rcases orSign_mem a b (mfd I 𝓘(ℝ, E) (extChartAt I x) y) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h h0

/-! ### Transport of an orientation across one chart -/

/-- **Transport of an orientation across a chart.**  `orTransport I x y o` is the orientation of the
tangent space at `y` which the derivative of the chart centred at `x` carries to the orientation
`o` at `x`; it is `o` or `-o` according to the sign of that derivative.  For `y` outside the source
of the chart at `x` the value is junk. -/
def orTransport (I : ModelWithCorners ℝ E H) (x y : M) (o : Orientation ℝ E (Fin m)) :
    Orientation ℝ E (Fin m) :=
  if orSign o o (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = 1 then o else -o

/-- `orTransport I x y o = o` when the chart at `x` preserves `o`. -/
theorem orTransport_eq_self {x y : M} {o : Orientation ℝ E (Fin m)}
    (h : orSign o o (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = 1) : orTransport I x y o = o := by
  unfold orTransport; exact if_pos h

/-- `orTransport I x y o = -o` when the chart at `x` does not preserve `o`. -/
theorem orTransport_eq_neg {x y : M} {o : Orientation ℝ E (Fin m)}
    (h : orSign o o (mfd I 𝓘(ℝ, E) (extChartAt I x) y) ≠ 1) : orTransport I x y o = -o := by
  unfold orTransport; exact if_neg h

/-- **The characterising property of `orTransport`**: the derivative of the chart centred at `x`
carries the orientation `orTransport I x y o` at `y` to the orientation `o` at `x`. -/
theorem orSign_transport (hm : finrank ℝ E = m) {x y : M} (hy : y ∈ (extChartAt I x).source)
    (o : Orientation ℝ E (Fin m)) :
    orSign (orTransport I x y o) o (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = 1 := by
  by_cases h : orSign o o (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = 1
  · rw [orTransport_eq_self h]; exact h
  · rw [orTransport_eq_neg h, orSign_neg_left hm]
    rcases orSign_mfd_extChartAt_ne_zero hm hy o o with h1 | h1
    · exact absurd h1 h
    · rw [h1]; norm_num

/-- **Uniqueness of the transport.**  `orTransport I x y o` is the only orientation carried by the
chart at `x` to the orientation `o` at `x`; this uses that there are only two orientations. -/
theorem eq_transport (hm : finrank ℝ E = m) {x y : M} (hy : y ∈ (extChartAt I x).source)
    {o a : Orientation ℝ E (Fin m)}
    (ha : orSign a o (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = 1) : a = orTransport I x y o := by
  rcases eq_or_eq_neg hm a (orTransport I x y o) with h | h
  · exact h
  · rw [h, orSign_neg_left hm, orSign_transport hm hy] at ha
    norm_num at ha

/-- An orientation at `y` is carried by the chart at `x` to `o` if and only if it is the transport
of `o`. -/
theorem orSign_eq_one_iff_eq_transport (hm : finrank ℝ E = m) {x y : M}
    (hy : y ∈ (extChartAt I x).source) (o a : Orientation ℝ E (Fin m)) :
    orSign a o (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = 1 ↔ a = orTransport I x y o :=
  ⟨eq_transport hm hy, fun h => by rw [h]; exact orSign_transport hm hy o⟩

/-- Transport from `x` to `x` is the identity. -/
@[simp] theorem transport_self (x : M) (o : Orientation ℝ E (Fin m)) : orTransport I x x o = o :=
  orTransport_eq_self (by rw [mfd_extChartAt_self]; exact orSign_id o)

/-- Transport from `x` to `x` is the identity map on orientations. -/
theorem orTransport_self_eq_id (x : M) :
    (orTransport I x x : Orientation ℝ E (Fin m) → Orientation ℝ E (Fin m)) = id :=
  funext fun o => transport_self x o

/-- Transport anticommutes with reversal of orientations. -/
theorem orTransport_neg (hm : finrank ℝ E = m) {x y : M} (o : Orientation ℝ E (Fin m)) :
    orTransport I x y (-o) = -orTransport I x y o := by
  have h : orSign (-o) (-o) (mfd I 𝓘(ℝ, E) (extChartAt I x) y)
      = orSign o o (mfd I 𝓘(ℝ, E) (extChartAt I x) y) := by
    rw [orSign_neg_left hm, orSign_neg_right hm, neg_neg]
  by_cases hc : orSign o o (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = 1
  · rw [orTransport_eq_self (h.trans hc), orTransport_eq_self hc]
  · rw [orTransport_eq_neg (by rw [h]; exact hc), orTransport_eq_neg hc]

/-- Transport across a chart is an involution: transporting twice gives back the orientation.
(Both transports are taken through the chart at `x`.) -/
theorem orTransport_involutive (hm : finrank ℝ E = m) (x y : M) :
    Function.Involutive (orTransport I x y : Orientation ℝ E (Fin m) → Orientation ℝ E (Fin m)) := by
  intro o
  by_cases hc : orSign o o (mfd I 𝓘(ℝ, E) (extChartAt I x) y) = 1
  · rw [orTransport_eq_self hc, orTransport_eq_self hc]
  · rw [orTransport_eq_neg hc, orTransport_neg hm, orTransport_eq_neg hc]
    exact neg_neg o

/-- Transport across a chart is injective. -/
theorem orTransport_injective (hm : finrank ℝ E = m) (x y : M) :
    Function.Injective (orTransport I x y : Orientation ℝ E (Fin m) → Orientation ℝ E (Fin m)) :=
  (orTransport_involutive hm x y).injective

/-- Transport across a chart is surjective. -/
theorem orTransport_surjective (hm : finrank ℝ E = m) (x y : M) :
    Function.Surjective (orTransport I x y : Orientation ℝ E (Fin m) → Orientation ℝ E (Fin m)) :=
  (orTransport_involutive hm x y).surjective

/-! ### An orientation of `M` is a section compatible with transport -/

/-- A family of orientations of the tangent spaces of `M` is a **transport section** if near every
point it is the transport of its value at that point. -/
def IsTransportSection (I : ModelWithCorners ℝ E H) (or : M → Orientation ℝ E (Fin m)) : Prop :=
  ∀ x : M, ∀ᶠ y in 𝓝 x, or y = orTransport I x y (or x)

/-- **An orientation of `M` is a transport section**: on a neighbourhood of each point `x` the
orientation at `y` is the transport of the orientation at `x`. -/
theorem Orient.isTransportSection (hm : finrank ℝ E = m) (o : Orient I M m) :
    IsTransportSection I o.or := by
  intro x
  filter_upwards [extChartAt_source_mem_nhds (I := I) x, o.cont x] with y hy hsign
  exact eq_transport hm hy hsign

/-- **Conversely a transport section is an orientation of `M`.** -/
def Orient.ofTransportSection (hm : finrank ℝ E = m) {or : M → Orientation ℝ E (Fin m)}
    (h : IsTransportSection I or) : Orient I M m where
  or := or
  cont x := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x, h x] with y hy hor
    rw [hor]
    exact orSign_transport hm hy (or x)

/-- The orientations of `Orient.ofTransportSection` are the given ones. -/
@[simp] theorem Orient.ofTransportSection_or (hm : finrank ℝ E = m)
    {or : M → Orientation ℝ E (Fin m)} (h : IsTransportSection I or) :
    (Orient.ofTransportSection hm h).or = or := rfl

/-! ### Chains of charts -/

/-- Two points are **chart-related** if the source of some one chart contains both. -/
def ChartRel (I : ModelWithCorners ℝ E H) (x y : M) : Prop :=
  ∃ z : M, x ∈ (extChartAt I z).source ∧ y ∈ (extChartAt I z).source

/-- Every point is chart-related to itself. -/
theorem chartRel_refl (I : ModelWithCorners ℝ E H) (x : M) : ChartRel I x x :=
  ⟨x, mem_extChartAt_source x, mem_extChartAt_source x⟩

/-- Chart-relatedness is symmetric. -/
theorem ChartRel.symm {x y : M} (h : ChartRel I x y) : ChartRel I y x :=
  let ⟨z, h1, h2⟩ := h; ⟨z, h2, h1⟩

/-- A point of the source of the chart at `x` is chart-related to `x`. -/
theorem chartRel_of_mem_source {x y : M} (h : y ∈ (extChartAt I x).source) : ChartRel I x y :=
  ⟨x, mem_extChartAt_source x, h⟩

/-- One **hop** from `x` to `y`: a single chart, given by its centre `hub`, whose source contains
both `x` and `y`.  That chart identifies both tangent spaces with the model space, and so
transports an orientation at `x` to an orientation at `y`.  The centre is part of the data,
because two charts containing the same two points may well disagree on which orientations
correspond (that is exactly the phenomenon Milnor's remark is about). -/
structure ChartHop (I : ModelWithCorners ℝ E H) (x y : M) where
  /-- the centre of the chart used by the hop -/
  hub : M
  /-- the source of the chart at `hub` contains `x` -/
  mem_left : x ∈ (extChartAt I hub).source
  /-- the source of the chart at `hub` contains `y` -/
  mem_right : y ∈ (extChartAt I hub).source

/-- A hop makes its endpoints chart-related. -/
theorem ChartHop.chartRel {x y : M} (h : ChartHop I x y) : ChartRel I x y :=
  ⟨h.hub, h.mem_left, h.mem_right⟩

/-- Chart-related points admit a hop. -/
theorem ChartRel.nonempty_chartHop {x y : M} (h : ChartRel I x y) : Nonempty (ChartHop I x y) :=
  let ⟨z, h1, h2⟩ := h; ⟨⟨z, h1, h2⟩⟩

/-- The hop through the chart centred at `x` itself, available whenever `y` lies in its source. -/
def ChartHop.ofMemSource {x y : M} (h : y ∈ (extChartAt I x).source) : ChartHop I x y :=
  ⟨x, mem_extChartAt_source x, h⟩

/-- The trivial hop from a point to itself. -/
def ChartHop.refl (I : ModelWithCorners ℝ E H) (x : M) : ChartHop I x x :=
  ChartHop.ofMemSource (mem_extChartAt_source x)

/-- A hop reversed. -/
def ChartHop.symm {x y : M} (h : ChartHop I x y) : ChartHop I y x :=
  ⟨h.hub, h.mem_right, h.mem_left⟩

/-- The orientation at `y` obtained from the orientation `o` at `x` through the chart of the hop:
transport `o` back to the centre of that chart, then out to `y`.  (Transport across one chart is
an involution, so transporting back is again a transport.) -/
def ChartHop.transport {x y : M} (h : ChartHop I x y) (o : Orientation ℝ E (Fin m)) :
    Orientation ℝ E (Fin m) :=
  Milnor.orTransport I h.hub y (Milnor.orTransport I h.hub x o)

/-- The hop through the chart centred at `x` transports by `orTransport I x y`. -/
theorem ChartHop.transport_ofMemSource {x y : M} (h : y ∈ (extChartAt I x).source)
    (o : Orientation ℝ E (Fin m)) :
    (ChartHop.ofMemSource h).transport o = Milnor.orTransport I x y o := by
  change Milnor.orTransport I x y (Milnor.orTransport I x x o) = _
  rw [transport_self]

/-- The trivial hop transports trivially. -/
@[simp] theorem ChartHop.transport_refl (x : M) (o : Orientation ℝ E (Fin m)) :
    (ChartHop.refl I x).transport o = o := by
  rw [ChartHop.refl, ChartHop.transport_ofMemSource, transport_self]

/-- **A hop reversed undoes the hop.** -/
theorem ChartHop.transport_symm_transport (hm : finrank ℝ E = m) {x y : M} (h : ChartHop I x y)
    (o : Orientation ℝ E (Fin m)) : h.symm.transport (h.transport o) = o := by
  change Milnor.orTransport I h.hub x (Milnor.orTransport I h.hub y
    (Milnor.orTransport I h.hub y (Milnor.orTransport I h.hub x o))) = o
  rw [orTransport_involutive hm h.hub y, orTransport_involutive hm h.hub x]

/-- A **chain** from `x` to `y`: a finite sequence of hops, the first starting at `x` and the last
ending at `y`.  Its list of vertices `ChartChain.verts` is a list of points beginning with `x` and
ending with `y` in which consecutive points are chart-related. -/
inductive ChartChain (I : ModelWithCorners ℝ E H) : M → M → Type u
  /-- the empty chain at `x` -/
  | nil (x : M) : ChartChain I x x
  /-- a chain obtained by prepending a hop to a chain -/
  | cons {x y z : M} (h : ChartHop I x y) (c : ChartChain I y z) : ChartChain I x z

/-- The chain consisting of a single hop. -/
def ChartChain.hop {x y : M} (h : ChartHop I x y) : ChartChain I x y := .cons h (.nil y)

/-- **Chains compose**: a chain from `x` to `y` followed by a chain from `y` to `z`. -/
def ChartChain.comp {x y z : M} (c : ChartChain I x y) (d : ChartChain I y z) :
    ChartChain I x z :=
  match c with
  | .nil _ => d
  | .cons h c' => .cons h (c'.comp d)

/-- The empty chain is a left unit for composition. -/
@[simp] theorem ChartChain.nil_comp {x y : M} (d : ChartChain I x y) :
    (ChartChain.nil x).comp d = d := rfl

/-- Composition of a chain that begins with a hop: the hop is kept in front. -/
@[simp] theorem ChartChain.cons_comp {x y z w : M} (h : ChartHop I x y) (c : ChartChain I y z)
    (d : ChartChain I z w) : (ChartChain.cons h c).comp d = .cons h (c.comp d) := rfl

/-- **The orientation transported along a chain**, starting from the orientation `o` at its
initial point: each hop is applied in turn. -/
def ChartChain.transport {x y : M} (c : ChartChain I x y) (o : Orientation ℝ E (Fin m)) :
    Orientation ℝ E (Fin m) :=
  match c with
  | .nil _ => o
  | .cons h c' => c'.transport (h.transport o)

/-- The empty chain transports trivially. -/
@[simp] theorem ChartChain.transport_nil (x : M) (o : Orientation ℝ E (Fin m)) :
    (ChartChain.nil (I := I) x).transport o = o := rfl

/-- Transport along a chain that begins with a hop: the hop is applied first. -/
@[simp] theorem ChartChain.transport_cons {x y z : M} (h : ChartHop I x y) (c : ChartChain I y z)
    (o : Orientation ℝ E (Fin m)) :
    (ChartChain.cons h c).transport o = c.transport (h.transport o) := rfl

/-- Transport along a one-hop chain is transport along that hop. -/
@[simp] theorem ChartChain.transport_hop {x y : M} (h : ChartHop I x y)
    (o : Orientation ℝ E (Fin m)) : (ChartChain.hop h).transport o = h.transport o := rfl

/-- **Chains reverse**: a chain from `x` to `y` read backwards is a chain from `y` to `x`. -/
def ChartChain.reverse {x y : M} (c : ChartChain I x y) : ChartChain I y x :=
  match c with
  | .nil a => .nil a
  | .cons h c' => c'.reverse.comp (.hop h.symm)

/-- The empty chain is its own reverse. -/
@[simp] theorem ChartChain.reverse_nil (x : M) :
    (ChartChain.nil (I := I) x).reverse = ChartChain.nil x := rfl

/-- Reversing a chain that begins with a hop puts the reversed hop at the end. -/
@[simp] theorem ChartChain.reverse_cons {x y z : M} (h : ChartHop I x y) (c : ChartChain I y z) :
    (ChartChain.cons h c).reverse = c.reverse.comp (ChartChain.hop h.symm) := rfl

/-- **Transport along a composite chain is the composite of the transports.** -/
theorem ChartChain.transport_comp : ∀ {x y z : M} (c : ChartChain I x y) (d : ChartChain I y z)
    (o : Orientation ℝ E (Fin m)), (c.comp d).transport o = d.transport (c.transport o) := by
  intro x y z c
  induction c with
  | nil a => intro d o; simp
  | cons h c ih => intro d o; simp [ih]

/-- **Transport along the reverse of a chain undoes transport along the chain.** -/
theorem ChartChain.transport_reverse (hm : finrank ℝ E = m) :
    ∀ {x y : M} (c : ChartChain I x y) (o : Orientation ℝ E (Fin m)),
      c.reverse.transport (c.transport o) = o := by
  intro x y c
  induction c with
  | nil a => intro o; simp
  | cons h c ih =>
      intro o
      simp only [reverse_cons, transport_cons, transport_comp, ih, transport_hop]
      exact h.transport_symm_transport hm o

/-- Transport along a chain is injective. -/
theorem ChartChain.transport_injective (hm : finrank ℝ E = m) {x y : M} (c : ChartChain I x y) :
    Function.Injective (c.transport : Orientation ℝ E (Fin m) → Orientation ℝ E (Fin m)) :=
  Function.LeftInverse.injective (g := c.reverse.transport) (c.transport_reverse hm)

/-- A chain extended by one further point, taken in the source of the chart centred at its
endpoint.  This is the step used to propagate an orientation to a neighbourhood. -/
def ChartChain.snoc {x y : M} (c : ChartChain I x y) {z : M}
    (h : z ∈ (extChartAt I y).source) : ChartChain I x z :=
  c.comp (.hop (ChartHop.ofMemSource h))

/-- Extending a chain by a point of the chart at its endpoint transports by `orTransport`. -/
theorem ChartChain.transport_snoc {x y z : M} (c : ChartChain I x y)
    (h : z ∈ (extChartAt I y).source) (o : Orientation ℝ E (Fin m)) :
    (c.snoc h).transport o = Milnor.orTransport I y z (c.transport o) := by
  change (c.comp (.hop (ChartHop.ofMemSource h))).transport o = _
  rw [ChartChain.transport_comp, ChartChain.transport_hop, ChartHop.transport_ofMemSource]

/-! ### A chain as a list of points -/

/-- The list of points visited by a chain: `x` first, `y` last. -/
def ChartChain.verts {x y : M} (c : ChartChain I x y) : List M :=
  match c with
  | .nil a => [a]
  | .cons _ c' => x :: c'.verts

/-- The empty chain at `x` visits the single point `x`. -/
@[simp] theorem ChartChain.verts_nil (x : M) :
    (ChartChain.nil (I := I) x).verts = [x] := rfl

/-- The vertices of a chain that begins with a hop out of `x` start with `x`. -/
@[simp] theorem ChartChain.verts_cons {x y z : M} (h : ChartHop I x y) (c : ChartChain I y z) :
    (ChartChain.cons h c).verts = x :: c.verts := rfl

/-- The list of vertices of a chain is nonempty. -/
theorem ChartChain.verts_ne_nil {x y : M} (c : ChartChain I x y) : c.verts ≠ [] := by
  cases c <;> simp

/-- A chain starts at `x`. -/
@[simp] theorem ChartChain.head?_verts {x y : M} (c : ChartChain I x y) :
    c.verts.head? = some x := by
  cases c <;> simp

/-- A chain ends at `y`. -/
@[simp] theorem ChartChain.getLast?_verts : ∀ {x y : M} (c : ChartChain I x y),
    c.verts.getLast? = some y := by
  intro x y c
  induction c with
  | nil a => rfl
  | cons h c ih => rw [verts_cons]; exact List.mem_getLast?_cons ih

/-- Consecutive vertices of a chain are chart-related. -/
theorem ChartChain.isChain_verts : ∀ {x y : M} (c : ChartChain I x y),
    c.verts.IsChain (ChartRel I) := by
  intro x y c
  induction c with
  | nil a => exact List.isChain_singleton a
  | cons h c ih =>
      rw [verts_cons]
      refine ih.cons ?_
      simp only [ChartChain.head?_verts, Option.mem_some_iff]
      rintro p rfl
      exact h.chartRel

/-! ### Every point of a connected manifold is reachable by a chain -/

/-- `y` is **reachable** from `x` if some chain of charts joins `x` to `y`. -/
def Reachable (I : ModelWithCorners ℝ E H) (x y : M) : Prop := Nonempty (ChartChain I x y)

/-- Reachability is reflexive. -/
theorem Reachable.refl (I : ModelWithCorners ℝ E H) (x : M) : Reachable I x x := ⟨.nil x⟩

/-- Reachability is symmetric, because chains reverse. -/
theorem Reachable.symm {x y : M} (h : Reachable I x y) : Reachable I y x := ⟨h.some.reverse⟩

/-- Reachability is transitive, because chains compose. -/
theorem Reachable.trans {x y z : M} (h : Reachable I x y) (h' : Reachable I y z) :
    Reachable I x z := ⟨h.some.comp h'.some⟩

/-- A point of the source of the chart at `x` is reachable from `x` in one hop. -/
theorem reachable_of_mem_source {x y : M} (h : y ∈ (extChartAt I x).source) : Reachable I x y :=
  ⟨.hop (ChartHop.ofMemSource h)⟩

/-- The set of points reachable from `x` is open: it contains the source of the chart at each of
its points. -/
theorem isOpen_reachable (x : M) : IsOpen {y : M | Reachable I x y} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  refine Filter.mem_of_superset (extChartAt_source_mem_nhds (I := I) y) fun p hp => ?_
  exact hy.trans (reachable_of_mem_source hp)

/-- The set of points reachable from `x` is closed: the source of the chart at a point not
reachable from `x` contains no point reachable from `x`. -/
theorem isClosed_reachable (x : M) : IsClosed {y : M | Reachable I x y} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  refine Filter.mem_of_superset (extChartAt_source_mem_nhds (I := I) y) fun p hp hpr => ?_
  exact hy (hpr.trans (reachable_of_mem_source hp).symm)

/-- **In a connected manifold any two points are joined by a chain of charts**, because the set of
points reachable from a fixed point is open, closed and nonempty. -/
theorem reachable_of_preconnectedSpace [PreconnectedSpace M] (x y : M) : Reachable I x y := by
  have hcl : IsClopen {z : M | Reachable I x z} := ⟨isClosed_reachable x, isOpen_reachable x⟩
  have h : {z : M | Reachable I x z} = univ := IsClopen.eq_univ hcl ⟨x, Reachable.refl I x⟩
  have hy : y ∈ {z : M | Reachable I x z} := by rw [h]; exact mem_univ y
  exact hy

/-- **In a connected manifold there is a chain of charts from any point to any other.** -/
theorem nonempty_chartChain [PreconnectedSpace M] (x y : M) : Nonempty (ChartChain I x y) :=
  reachable_of_preconnectedSpace x y

end Milnor
