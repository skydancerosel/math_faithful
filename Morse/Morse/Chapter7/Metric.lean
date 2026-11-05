import Morse.Chapter7.Distance

/-!
Milnor, *Morse Theory*, §10, pp. 62–64, for a submanifold `N ⊆ ℝᴷ` with the induced metric.

# The distance `ρ`: continuity, the metric space `(N, ρ)`, completeness

## Milnor's text, paraphrased

(p. 62) The distance `ρ(p, q)` is the greatest lower bound of the lengths of piecewise smooth
paths from `p` to `q`.  Milnor says that this clearly makes the (connected) manifold `M` a metric
space, and that the metric is compatible with the topology of `M` by Theorem 10.4.  In the proof
of Theorem 10.9 (p. 63) he uses, without comment, that `ρ` is continuous: a continuous function
`ρ(·, q)` has a minimum on a compact sphere, and an identity `ρ(γ(t), q) = r − t` persists at a
supremum of times "by continuity".  On p. 64 he speaks of bounded subsets of `M` and of `M` being
complete as a metric space, i.e. every Cauchy sequence converges.

## In the embedded setting

`Morse/Chapter7/Distance.lean` proves the axioms of an extended metric for `ρ = Morse.riemDist`
(with values in `[0, ∞]`) and that the metric balls about `p` form a basis of neighbourhoods of `p`
in `N`.  Here:

* `Morse.continuousOn_riemDist`, `Morse.continuous_riemDist`: **`ρ` is continuous** on `N × N`.
* `Morse.ofReal_norm_sub_le_riemDist`: **`ρ` dominates the distance of `V`**,
  `‖q − p‖ ≤ ρ(p, q)` (a path is at least as long as the chord).
* `Morse.riemDist_ne_top`: **on a connected `N` the distance is finite.**
* `Morse.riemEMetricSpace`, `Morse.riemMetricSpace`: **`ρ` is a genuine metric**: Mathlib's
  `EMetricSpace N` and, for connected `N`, `MetricSpace N` with distance `ρ`, whose topology is the
  topology of `N` definitionally (`Morse.riemMetricSpace_topology`).  They are not instances: the
  subtype `N` already carries the metric of `V`.
* `Morse.IsRiemComplete N`: **`(N, ρ)` is complete**, every `ρ`-Cauchy sequence of points of `N`
  converges for `ρ` to a point of `N`; for connected `N` this is Mathlib's `CompleteSpace` for
  `Morse.riemMetricSpace` (`Morse.isRiemComplete_iff_completeSpace`).  `Morse.IsRiemBounded N X`:
  `X` has finite `ρ`-diameter.
* `Morse.isRiemComplete_of_isClosed`: **a closed submanifold `N ⊆ V` is complete for `ρ`**: a
  `ρ`-Cauchy sequence is Cauchy in `V`, so it converges in `V`; its limit lies in `N`, and `ρ`
  induces the topology of `N`.  With the Hopf–Rinow theorem (`Morse/Chapter7/HopfRinow.lean`) this
  makes every closed connected `N` complete in every sense.

## What Milnor leaves implicit

* **Finiteness of `ρ`** needs `M` connected, Milnor's standing assumption (p. 55): the points at
  finite distance from `p` form an open and closed subset (`Morse.riemDist_ne_top`).
* **Continuity of `ρ`**, used in the proof of Theorem 10.9, is not stated.  It follows from
  `|ρ(x, y) − ρ(x', y')| ≤ ρ(x, x') + ρ(y, y')` and the compatibility of `ρ` with the topology.
* **Closed submanifolds of `ℝᴷ` are complete.**  Milnor's manifolds are abstract and the statement
  does not occur; in the embedded setting it is the source of the complete examples (the sphere,
  compact Lie groups in a space of matrices).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace ENNReal NNReal

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-! ### Two elementary bounds -/

include hN in
/-- Points of `N` near `p` are at distance `< r` from `p`, for every `r > 0` (Milnor, p. 62: the
metric is compatible with the topology). -/
theorem eventually_riemDist_lt {p : V} (hp : p ∈ N) {r : ℝ≥0∞} (hr : 0 < r) :
    ∀ᶠ y in 𝓝[N] p, riemDist (N := N) p y < r := by
  obtain ⟨r', hr'0, hr'1, hr'2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hr
  have hr' : 0 < r' := ENNReal.ofReal_pos.1 hr'1
  filter_upwards [(hasBasis_nhdsWithin_riemDist hN ⟨p, hp⟩).mem_of_mem hr'] with y hy
  exact lt_trans hy hr'2

/-- **`ρ` dominates the distance of `V`**: the length of a path bounds the distance between its
endpoints. -/
theorem ofReal_norm_sub_le_riemDist (p q : V) :
    ENNReal.ofReal ‖q - p‖ ≤ riemDist (N := N) p q := by
  refine le_sInf ?_
  rintro L ⟨c, a, b, hc, -, rfl, rfl, rfl⟩
  exact ENNReal.ofReal_le_ofReal hc.isAdmissible.norm_sub_le_pathLength

/-! ### Continuity of the distance -/

include hN in
/-- **The distance `ρ` is continuous** on `N × N` (used, without proof, in Milnor's proof of
Theorem 10.9, p. 63).  From the triangle inequality and the compatibility of `ρ` with the topology
of `N` (`Morse.hasBasis_nhdsWithin_riemDist`). -/
theorem continuousOn_riemDist :
    ContinuousOn (fun z : V × V => riemDist (N := N) z.1 z.2) (N ×ˢ N) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  have hev : ∀ r : ℝ≥0∞, 0 < r → ∀ᶠ z in 𝓝[N ×ˢ N] (x, y),
      riemDist (N := N) x z.1 < r ∧ riemDist (N := N) y z.2 < r := by
    intro r hr
    rw [nhdsWithin_prod_eq]
    exact (eventually_riemDist_lt hN hx hr).prod_mk (eventually_riemDist_lt hN hy hr)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 ha
    have hr2 : (0 : ℝ≥0∞) < (r : ℝ≥0∞) / 2 :=
      ENNReal.half_pos (by exact_mod_cast hr0.ne')
    filter_upwards [hev _ hr2] with z hz
    by_contra hle
    rw [not_lt] at hle
    have h1 := riemDist_triangle (N := N) x z.1 y
    have h2 := riemDist_triangle (N := N) z.1 z.2 y
    rw [riemDist_comm (N := N) z.2 y] at h2
    have h3 : riemDist (N := N) x y ≤ (r : ℝ≥0∞) / 2 + (a + (r : ℝ≥0∞) / 2) :=
      h1.trans (add_le_add hz.1.le (h2.trans (add_le_add hle hz.2.le)))
    rw [add_left_comm, ← add_assoc, add_assoc, ENNReal.add_halves] at h3
    exact absurd (h3.trans_lt hr) (lt_irrefl _)
  · obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hb
    have hr2 : (0 : ℝ≥0∞) < (r : ℝ≥0∞) / 2 :=
      ENNReal.half_pos (by exact_mod_cast hr0.ne')
    filter_upwards [hev _ hr2] with z hz
    have h1 := riemDist_triangle (N := N) z.1 x z.2
    have h2 := riemDist_triangle (N := N) x y z.2
    rw [riemDist_comm (N := N) z.1 x] at h1
    have h3 : riemDist (N := N) z.1 z.2 ≤ (r : ℝ≥0∞) / 2 + (riemDist (N := N) x y +
        (r : ℝ≥0∞) / 2) := h1.trans (add_le_add hz.1.le (h2.trans (add_le_add le_rfl hz.2.le)))
    rw [add_left_comm, ← add_assoc, add_assoc, ENNReal.add_halves] at h3
    exact h3.trans_lt hr

include hN in
/-- `y ↦ ρ(y, q)` is continuous on `N`. -/
theorem continuousOn_riemDist_left (q : V) :
    ContinuousOn (fun y => riemDist (N := N) y q) N := by
  by_cases hq : q ∈ N
  · exact (continuousOn_riemDist hN).comp (continuousOn_id.prodMk continuousOn_const)
      fun y hy => ⟨hy, hq⟩
  · simp only [riemDist_eq_top_of_notMem hq]
    exact continuousOn_const

include hN in
/-- **The distance `ρ` is continuous** as a function on `N × N`. -/
theorem continuous_riemDist :
    Continuous (fun z : N × N => riemDist (N := N) (z.1 : V) z.2) := by
  have h := (continuousOn_riemDist hN).comp_continuous
    (continuous_subtype_val.prodMap continuous_subtype_val) fun z => ⟨z.1.2, z.2.2⟩
  exact h

/-! ### Finiteness on a connected `N` -/

include hN in
/-- **On a connected `N` the distance is finite** (Milnor's standing assumption that `M` is
connected, p. 55): the points at finite distance from `p` form an open and closed subset of `N`. -/
theorem riemDist_ne_top (hconn : IsPreconnected N) {p q : V} (hp : p ∈ N) (hq : q ∈ N) :
    riemDist (N := N) p q ≠ ⊤ := by
  have := isPreconnected_iff_preconnectedSpace.1 hconn
  set T : Set N := {y | riemDist (N := N) p y ≠ ⊤} with hT
  have hnear : ∀ y : N, ∀ᶠ y' : N in 𝓝 y, riemDist (N := N) y y' < 1 := fun y =>
    (eventually_nhds_subtype_iff N y _).2 (eventually_riemDist_lt hN y.2 one_pos)
  have hopen : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    filter_upwards [hnear y] with y' hy'
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hy, hy'.ne_top⟩) (riemDist_triangle _ _ _)
  have hclosed : IsClosed T := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    filter_upwards [hnear y] with y' hy' hy'T
    refine hy (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hy'T, ?_⟩)
      (riemDist_triangle (N := N) p y' y))
    rw [riemDist_comm]
    exact hy'.ne_top
  have huniv := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨⟨p, hp⟩, by
    change riemDist (N := N) p p ≠ ⊤
    rw [riemDist_self hp]
    exact ENNReal.zero_ne_top⟩
  have : (⟨q, hq⟩ : N) ∈ T := by rw [huniv]; exact mem_univ _
  exact this

/-! ### Completeness -/

/-- **`(N, ρ)` is a complete metric space** (Milnor, p. 64): every `ρ`-Cauchy sequence of points of
`N` converges, for `ρ`, to a point of `N`. -/
def IsRiemComplete (N : Set V) : Prop :=
  ∀ x : ℕ → V, (∀ n, x n ∈ N) →
    (∀ ε : ℝ, 0 < ε → ∃ n₀, ∀ m ≥ n₀, ∀ n ≥ n₀,
      riemDist (N := N) (x m) (x n) < ENNReal.ofReal ε) →
    ∃ y ∈ N, Tendsto (fun n => riemDist (N := N) (x n) y) atTop (𝓝 0)

/-- **A `ρ`-bounded set** (Milnor, p. 64): a set of finite diameter for `ρ`.  (Such a set lies in
`N`, as `ρ(x, x) = ∞` for `x ∉ N`.) -/
def IsRiemBounded (N : Set V) (X : Set V) : Prop :=
  ∃ d : ℝ, ∀ x ∈ X, ∀ y ∈ X, riemDist (N := N) x y ≤ ENNReal.ofReal d

include hN in
/-- Convergence in `N` implies convergence for `ρ`. -/
theorem tendsto_riemDist_of_tendsto {ι : Type*} {l : Filter ι} {x : ι → V} {y : V} (hy : y ∈ N)
    (hx : Tendsto x l (𝓝[N] y)) : Tendsto (fun n => riemDist (N := N) (x n) y) l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [hx.eventually (eventually_riemDist_lt hN hy hε)] with n hn
  rw [riemDist_comm]
  exact hn.le

include hN in
/-- **Closed submanifolds are complete** (the key to applying Theorem 10.9 in the embedded
setting): if `N` is a closed subset of `V`, then `(N, ρ)` is complete.  A `ρ`-Cauchy sequence is
Cauchy in `V` (`ρ` dominates the distance of `V`), so it converges in `V`; the limit lies in `N`
since `N` is closed; and `ρ` induces the topology of `N`. -/
theorem isRiemComplete_of_isClosed (hc : IsClosed N) : IsRiemComplete N := by
  intro x hxN hx
  have hcau : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hx ε hε
    refine ⟨n₀, fun m hm n hn => ?_⟩
    have h1 := ofReal_norm_sub_le_riemDist (N := N) (x n) (x m)
    rw [dist_eq_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 (h1.trans_lt (hn₀ n hn m hm))
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
  have hyN : y ∈ N := hc.mem_of_tendsto hy (Eventually.of_forall hxN)
  exact ⟨y, hyN, tendsto_riemDist_of_tendsto hN hyN
    (tendsto_nhdsWithin_iff.2 ⟨hy, Eventually.of_forall hxN⟩)⟩

/-! ### The metric space `(N, ρ)` -/

/-- The extended metric `ρ` on `N`, before adjusting its topology. -/
@[instance_reducible]
def riemEMetricSpace₀ : EMetricSpace N where
  edist x y := riemDist (N := N) (x : V) y
  edist_self x := riemDist_self x.2
  edist_comm x y := riemDist_comm _ _
  edist_triangle x y z := riemDist_triangle _ _ _
  eq_of_edist_eq_zero h := eq_of_riemDist_eq_zero hN h

/-- The topology of `ρ` is the topology of `N` (Milnor, p. 62, via
`Morse.hasBasis_nhdsWithin_riemDist`): the metric balls about `x` and the neighbourhoods of `x` in
`N` generate the same filter. -/
theorem topology_eq_riemEMetricSpace₀ :
    (instTopologicalSpaceSubtype : TopologicalSpace N) =
      (riemEMetricSpace₀ hN).toUniformSpace.toTopologicalSpace := by
  refine TopologicalSpace.ext_nhds fun x => ?_
  have hb := @Metric.nhds_basis_eball N (riemEMetricSpace₀ hN).toPseudoEMetricSpace x
  ext t
  rw [hb.mem_iff, mem_nhds_subtype_iff_nhdsWithin, (hasBasis_nhdsWithin_riemDist hN x).mem_iff]
  constructor
  · rintro ⟨r, hr, hrt⟩
    refine ⟨ENNReal.ofReal r, ENNReal.ofReal_pos.2 hr, fun y hy => ?_⟩
    have hy' : riemDist (N := N) (x : V) y < ENNReal.ofReal r := by
      have : riemDist (N := N) (y : V) x < ENNReal.ofReal r := hy
      rwa [riemDist_comm]
    obtain ⟨y', hy't, hy'y⟩ := hrt hy'
    rwa [← Subtype.ext hy'y]
  · rintro ⟨ε, hε, hεt⟩
    obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    refine ⟨r, ENNReal.ofReal_pos.1 hr1, fun y hy => ?_⟩
    have hyN : y ∈ N := by
      by_contra h
      rw [mem_ofPred_eq, riemDist_eq_top_of_notMem h] at hy
      exact not_top_lt hy
    refine ⟨⟨y, hyN⟩, hεt ?_, rfl⟩
    change riemDist (N := N) y x < ε
    rw [riemDist_comm]
    exact lt_trans hy hr2

/-- **The extended metric space `(N, ρ)`** (Milnor, p. 62), with the topology of `N`
(definitionally).  Not an instance: the subtype `N` already carries the metric of `V`. -/
@[instance_reducible]
def riemEMetricSpace : EMetricSpace N :=
  (riemEMetricSpace₀ hN).replaceTopology (topology_eq_riemEMetricSpace₀ hN)

/-- **The metric space `(N, ρ)`** for connected `N` (Milnor, p. 62: `ρ` makes `M` a metric space,
compatible with its topology): `dist x y = ρ(x, y)`, finite by `Morse.riemDist_ne_top`, and the
topology is that of `N` (definitionally, `Morse.riemMetricSpace_topology`).  Not an instance. -/
@[instance_reducible]
def riemMetricSpace (hconn : IsPreconnected N) : MetricSpace N :=
  @EMetricSpace.toMetricSpace N (riemEMetricSpace hN)
    fun x y => riemDist_ne_top hN hconn x.2 y.2

/-- The distance of `Morse.riemMetricSpace` is `ρ`. -/
theorem riemMetricSpace_dist (hconn : IsPreconnected N) (x y : N) :
    (riemMetricSpace hN hconn).dist x y = (riemDist (N := N) (x : V) y).toReal := rfl

/-- The extended distance of `Morse.riemMetricSpace` is `ρ`. -/
theorem riemMetricSpace_edist (hconn : IsPreconnected N) (x y : N) :
    (riemMetricSpace hN hconn).edist x y = riemDist (N := N) (x : V) y := rfl

/-- **`ρ` induces the topology of `N`**, definitionally. -/
theorem riemMetricSpace_topology (hconn : IsPreconnected N) :
    (riemMetricSpace hN hconn).toUniformSpace.toTopologicalSpace =
      (instTopologicalSpaceSubtype : TopologicalSpace N) := rfl

/-- `Morse.IsRiemComplete` is completeness of the metric space `Morse.riemMetricSpace` in Mathlib's
sense. -/
theorem isRiemComplete_iff_completeSpace (hconn : IsPreconnected N) :
    IsRiemComplete N ↔ @CompleteSpace N (riemMetricSpace hN hconn).toUniformSpace := by
  set m := riemMetricSpace hN hconn
  constructor
  · intro h
    refine @Metric.complete_of_cauchySeq_tendsto N m.toPseudoMetricSpace fun u hu => ?_
    rw [@EMetric.cauchySeq_iff N ℕ m.toPseudoEMetricSpace _ _ u] at hu
    obtain ⟨y, hyN, hy⟩ := h (fun n => (u n : V)) (fun n => (u n).2) fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := hu (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
      exact ⟨n₀, fun m hm n hn => hn₀ m hm n hn⟩
    exact ⟨⟨y, hyN⟩, (@tendsto_iff_edist_tendsto_0 N ℕ m.toPseudoEMetricSpace _ u _).2 hy⟩
  · intro h x hxN hx
    have hu : @CauchySeq N ℕ m.toUniformSpace _ (fun n => (⟨x n, hxN n⟩ : N)) := by
      rw [@EMetric.cauchySeq_iff N ℕ m.toPseudoEMetricSpace _ _ _]
      intro ε hε
      obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
      obtain ⟨n₀, hn₀⟩ := hx r (ENNReal.ofReal_pos.1 hr1)
      exact ⟨n₀, fun m hm n hn => lt_trans (hn₀ m hm n hn) hr2⟩
    obtain ⟨y, hy⟩ := @CompleteSpace.complete N m.toUniformSpace h _ hu
    exact ⟨y, y.2, (@tendsto_iff_edist_tendsto_0 N ℕ m.toPseudoEMetricSpace _ _ y).1 hy⟩

end Morse
