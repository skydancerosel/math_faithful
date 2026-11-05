import Milnor.Appendix.Smooth.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Milnor's Appendix, smooth version: the two non-compact cases

Milnor, *Topology from the Differentiable Viewpoint*, Appendix (book p. 54), classifies the
connected one-manifolds into four cases.  This file is **Stage 8** of the plan
`Exposition/PlanOneManifold.md`, and it settles the remaining two: **a connected, Hausdorff,
σ-compact smooth one-manifold which is not compact is diffeomorphic to `ℝ` if its boundary is empty,
and to `Ici (0 : ℝ)` if it has a boundary point** -- in which case the boundary is that point alone.

## The headline theorems

* `nonempty_diffeomorphReal` -- **the boundaryless case.**  A nonempty, Hausdorff, σ-compact,
  preconnected `C^∞` one-manifold `M` with `I.boundary M = ∅` and `¬ CompactSpace M` is
  `C^∞`-diffeomorphic to `ℝ` with the trivial model `𝓘(ℝ, ℝ)`.  `nonempty_diffeomorphReal'` is the
  same statement in the direction `M → ℝ`.
* `nonempty_diffeomorphIci` -- **the case with a boundary point.**  A Hausdorff, σ-compact,
  preconnected `C^∞` one-manifold with a point `p ∈ I.boundary M` and `¬ CompactSpace M` is
  `C^∞`-diffeomorphic to `Ici (0 : ℝ)`, with Mathlib's model `𝓡∂ 1`; `nonempty_diffeomorphIci'` is
  the reverse direction, and `boundary_eq_singleton` says `I.boundary M = {p}`.

## The intermediate results, each usable on its own

* `exists_parametrisation_of_boundary_eq_empty` -- **parametrization by an open interval.**  Such an
  `M` carries a length element `L`, an open interval `U` of times and a map `γ : ℝ → M` which is a
  *unit-speed curve* on `U` in the sense of Stage 7 -- near every time the arc-length
  parametrization of a unit-speed smooth arc -- and which is **injective on `U`** and **onto `M`**.
  This is the honest form of the statement: without compactness the interval of times need not be
  the whole line (take `M = Ioo 0 1`), so the object is a parametrization by an open interval and
  not by `ℝ`.
* `exists_ray_of_mem_boundary` -- **parametrization by a half-open interval.**  In the case with a
  boundary point there are `Γ : ℝ → M` and a set of times `T`, equal to `Ici 0` or to `Ico 0 b`,
  with `Γ 0 = p`, `Γ` smooth on `T`, injective on `T`, onto `M`, with no boundary value other than
  `Γ 0`, and with a globally `C^∞` inverse coordinate `θ : M → ℝ`.
* `exists_param_of_isOpen_ordConnected` and `exists_param_halfline` -- **every nonempty open
  interval of the line is diffeomorphic to the line, and every interval `Ici 0` or `Ico 0 b` to `Ici
  0`**, by explicit elementary formulas (`a + exp`, `b - exp`, the logistic curve, the Möbius map `u
  ↦ b u/(1+u)`) together with their explicit logarithmic or rational inverses.  Both halves are
  written down, so no inverse function theorem -- in particular none at a boundary endpoint -- is
  needed anywhere in this file.
* `IsUnitSpeedCurveOn.notMem_boundary` -- **no value of a unit-speed curve is a boundary point.**
  This single fact organises the whole file: it is why the boundary point has to be adjoined by hand
  in the half-line case, why the curve stops exactly at it, and why a repeated value is impossible.
* `eqOn_add_of_eq` -- Stage 7's `periodic_of_eq` (Milnor's Step 5) on an arbitrary interval of times
  and without boundarylessness; `isCompact_isOpen_image_Icc_of_eq` -- a repeated value makes the
  image of a compact interval of times a compact *open* set, which on a preconnected manifold is
  everything.
* `mem_image_dom_of_mem_closure` -- **the continuation step, freed of compactness**: every point of
  the closure of the image of the maximal curve which is not a boundary point is in the image.
* `SmoothArc.shrink` and `SmoothArc.unitSpeed_shrink` -- **restricting a smooth arc to an open
  subinterval of its target, with the parameter shifted, preserves smoothness and unit speed.**
  This is what converts the half-open arc issuing from a boundary point into the centred arcs with
  symmetric open target that the curve machinery of Stage 7 accepts.
* `iciHomeomorph`, `instIciChartedSpace`, `instIciIsManifold`, `contMDiff_subtypeVal_Ici`,
  `contMDiffOn_iciProj` -- **the closed half-line `Ici (0 : ℝ)` as a one-chart `C^∞` manifold with
  boundary over `𝓡∂ 1`**, with the two bridges (inclusion into `ℝ`, projection from `ℝ`) that make a
  map into or out of it smooth exactly when its real expression is.  Mathlib has these for `Icc x y`
  only, and there through two charts; here a single chart is a homeomorphism onto the whole model
  space, so `Topology.IsOpenEmbedding.singletonChartedSpace` applies and the bridges are three lines
  each.

## Where the two cases differ, and how each goes

In both cases the parametrization is the **maximal unit-speed curve** of Stage 7: `Reach`, `Dom` and
`globalCurve`, whose construction uses no compactness at all and whose interval `Dom` of reached
times is open, order-connected and contains `0`.

*Boundaryless.*  Start from a unit-speed arc centred at an arbitrary point.  The image `γ '' Dom` is
**open** because the curve is locally the parametrization of an arc, and **closed** because
`mem_image_dom_of_mem_closure` applies to every point of the closure -- here emptiness of the
boundary is exactly what makes every such point eligible.  Being a nonempty clopen subset of a
preconnected space it is everything.  Injectivity is where non-compactness enters, and it enters
only there: a repeated value would, by `eqOn_add_of_eq`, make the curve periodic, and
`isCompact_isOpen_image_Icc_of_eq` would then exhibit a nonempty compact open subset, hence all of
`M`, making `M` compact.  Finally `Dom` is a nonempty open interval, and
`exists_param_of_isOpen_ordConnected` reparametrizes it by the line.

*With a boundary point.*  The arc `A₀` issuing from `p` has half-open target `Ico 0 ε₀`, so it is
not a legitimate starting arc for a unit-speed curve -- no value of such a curve is a boundary
point. `SmoothArc.shrink` restricts it to `Ioo 0 ε₀` and recentres, producing a centred arc `A₁`;
the maximal curve from `A₁` then has `-ε₁ = -ε₀/2` as the *unattained* left end of its interval of
times (`left_notMem_dom`), because it tends to `p` there (`tendsto_left_halfline`) and cannot take
that value.  Shifting time by `ε₁` and adjoining the single time `0`, with value `p`, gives the ray
`Γ` on `T = Ici 0` or `Ico 0 b`.  Injectivity (`injOn_dom_halfline`) needs no compactness here: a
repeated value would make the curve's image all of `M` and hence cover `p`, which it cannot.
Surjectivity (`insert_image_dom_eq_univ`) is the long step: a *second* boundary point `q` in the
closure has to be excluded, and it is excluded by non-compactness -- reading the curve in an arc
issuing from `q` shows that the curve arrives exactly at `q` at an end of its interval of times, and
if that is the right end then `M` is covered by three compact pieces and so is compact.  That is
precisely the compact case `Icc 0 1` of Stage 6.

## Where σ-compactness is used, and why the theorem is false without it

**σ-compactness is used once, and only once: to build the length element**, through Stage 3's
`nonempty_lengthElement`, which needs `T2Space M` and `SigmaCompactSpace M` because Mathlib's smooth
partitions of unity do.  Everything after that -- the arcs, the curves, the propagation lemma, the
maximality of `Dom`, the continuation step and both classifications -- uses only Hausdorffness,
connectedness and the failure of compactness.

**The theorem is false without a countability hypothesis.**  The *long line* (the order topology on
`ω₁ × [0,1)` with the lexicographic order, minus its least element) is a connected, Hausdorff,
locally Euclidean space carrying a `C^∞` structure with empty boundary; it is not compact, and it is
diffeomorphic -- indeed not even homeomorphic -- to neither the circle nor any interval of the line,
since it is not second countable, not metrizable and not Lindelöf, while `ℝ` is all three.  So
σ-compactness (or second countability, or paracompactness, or metrizability) cannot be dropped from
the statements of this file.  Concretely it is *the length element* that fails: a manifold carrying
a Riemannian metric is metrizable, so the long line carries none, and Milnor's arc-length
reparametrization has nothing to start from.  Milnor's own manifolds are submanifolds of `ℝᵏ`, hence
second countable for free, and his proof uses this silently -- the Euclidean metric he restricts to
`M` is a Riemannian metric.  This is item 1 of §7 of the plan.

By contrast the **compact** cases of Stages 6 and 7 need nothing extra: compact plus Hausdorff plus
a finite-dimensional model gives second countability by Mathlib's
`ChartedSpace.secondCountable_of_sigmaCompact`, and `CompactSpace.sigmaCompact` supplies
σ-compactness.

## Hypotheses, and which step uses what

`E` is a real normed space with `Module.finrank ℝ E = 1`, `I : ModelWithCorners ℝ E H`, and `M` is a
`C^∞` manifold charted on `H` (`IsManifold I ∞ M`).  Beyond that:

* `T2Space M` is used by Stage 3 for the length element, by Stage 5's `overlap`/`trans` API, and --
  essentially -- in Stage 7's propagation lemma and in every uniqueness-of-limits argument of this
  file (`left_notMem_dom`, and the identification of the second boundary point).
* `SigmaCompactSpace M`: see above.
* `PreconnectedSpace M` is used for surjectivity in both cases and for injectivity in both cases
  (through the clopen argument).  `Nonempty M` is needed only in the boundaryless case, to choose a
  base point; in the other case the boundary point supplies one.
* `¬ CompactSpace M` is used exactly twice: once for injectivity in the boundaryless case, and once
  to exclude a second boundary point in the half-line case.
* No orientability, no `BoundarylessManifold` instance, and no boundarylessness of the *model*: the
  model range may still be a half-line or a compact interval, and `I.boundary M = ∅` is a hypothesis
  about `M`.

## What had to be restated, and what the plan's sketch got wrong

**No existing file is edited.**  Four statements of Stage 7 are *restated* here, in each case
because Stage 7 proved them under a hypothesis that this stage cannot supply:

1. `isUnitSpeedCurveOn_arc'`, `eqOn_shift_of_eventuallyEq'` and `IsUnitSpeedCurveOn.exists_shift'`
  replace Stage 7's versions, whose hypothesis `I.boundary M = ∅` was used only to know that an
  arc's target is open.  In the half-line case `M` *does* have a boundary point, while the arcs
  produced by `SmoothArc.shrink` still have open targets, so openness is the right hypothesis and
  the proofs are otherwise unchanged.  `exists_shift'` also carries one extra conclusion, that the
  arc it returns is the given one or its reverse; this is what identifies the direction in which the
  curve runs through the arc, and hence which end of an interval of times corresponds to the arc's
  parameter `0`.
2. `zero_mem_dom'` is Stage 7's `zero_mem_dom` with the same hypothesis dropped for the same reason.
3. `eqOn_add_of_eq` is Stage 7's `periodic_of_eq` on an arbitrary interval of times, with
  boundarylessness dropped: it was used only to produce a centred arc at the repeated value, and
  `IsUnitSpeedCurveOn.notMem_boundary` shows that value is not a boundary point, so Stage 4's
  `exists_unitSpeed_of_notMem_boundary` applies directly.  On an interval rather than the whole line
  the shifted curve lives on the shifted interval, so the conclusion is the shift identity where
  both times are defined, which is all that is needed.
4. `dom_glue` isolates the gluing step inside Stage 7's `not_bddAbove_dom`.  Nothing of Stage 7 is
  weakened: `Reach`, `Dom`, `globalCurve`, `subset_dom_and_eqOn`, `isUnitSpeedCurveOn_globalCurve`,
  `isOpen_dom`, `ordConnected_dom`, `eqOn_of_eventuallyEq`, `exists_sign` and `exists_injOn` are
  used verbatim, and they were already stated without compactness.

**Corrections to the plan and to the sketch.**

* The plan's Stage 8 proposes a *maximal arc* obtained by Zorn from the extension theorem of Stage
  5. That is not available: on a boundaryless manifold every arc has an open target, whereas
  `exists_extension_unitSpeed` needs the first arc's target to be half-open.  This is the same gap
  Stage 7 recorded, and the same replacement is used here -- unit-speed curves.  The plan's two
  named traps for this stage (the boundedness field of `Arc`, and setting up Zorn on a genuine set
  of functions) therefore do not arise at all.
* The sketch says the maximal curve's interval of times is open and "need not be the whole line".
  That is right, and it is why the honest intermediate statement is a parametrization by an *open
  interval*; but the sketch's reason for injectivity is not quite the one that works.  A repeated
  value does give a period, and a periodic curve does have compact image -- but only *after* one
  knows the curve is defined on the whole line, which here it need not be.  What is true, and what
  is proved (`eqOn_add_of_eq`, `isCompact_isOpen_image_Icc_of_eq`), is that a repeated value makes
  the image of one compact interval of times both compact and open, hence everything.  Surjectivity
  is then not needed as an input to injectivity, and in the half-line case injectivity needs no
  non-compactness at all.
* The sketch offers, for the case with a boundary point, either "Stage 6's exhaustion without
  compactness" or "the curve argument on a half-line of times".  The second is what is done, but not
  quite as stated: a *unit-speed curve cannot contain the boundary point*
  (`IsUnitSpeedCurveOn.notMem_boundary`), so the half-line of times is not a set of times of a
  unit-speed curve.  The boundary point is adjoined by hand, and the work is to show that the curve
  stops exactly there and that no *second* boundary point appears in the closure.  Stage 6's
  finite-cover exhaustion is not used, and nothing of it is restated.
* `Ici (0 : ℝ)` is not a manifold in Mathlib -- only `Icc x y` is -- so its charted-space and
  `IsManifold` instances, and the two smoothness bridges, are built here.

## References

* Milnor, *Topology from the Differentiable Viewpoint*, Appendix, p. 54 (the four cases).
* `Exposition/PlanOneManifold.md`, Stage 8 and §7 item 1 (the long line).
-/

open Set Filter Topology

open scoped ContDiff Manifold

noncomputable section

namespace Milnor.OneManifold.Smooth

/-! ## Open intervals of the line are parametrized by the line -/

section OpenIntervals

/-- A set which is not bounded above has a member beyond any given real. -/
theorem exists_gt_of_not_bddAbove {U : Set ℝ} (h : ¬ BddAbove U) (x : ℝ) : ∃ z ∈ U, x < z := by
  by_contra hcon
  push Not at hcon
  exact h ⟨x, fun z hz => hcon z hz⟩

/-- A set which is not bounded below has a member below any given real. -/
theorem exists_lt_of_not_bddBelow {U : Set ℝ} (h : ¬ BddBelow U) (x : ℝ) : ∃ z ∈ U, z < x := by
  by_contra hcon
  push Not at hcon
  exact h ⟨x, fun z hz => hcon z hz⟩

/-- **An open set is above its own infimum**: no member of an open set bounded below is its infimum,
because a whole ball around the member is inside the set. -/
theorem sInf_lt_of_mem_of_isOpen {U : Set ℝ} (hU : IsOpen U) (hb : BddBelow U) {x : ℝ}
    (hx : x ∈ U) : sInf U < x := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hmem : x - δ / 2 ∈ U := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    rw [show x - δ / 2 - x = -(δ / 2) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  exact lt_of_le_of_lt (csInf_le hb hmem) (by linarith)

/-- **An open set is below its own supremum.** -/
theorem lt_sSup_of_mem_of_isOpen {U : Set ℝ} (hU : IsOpen U) (hb : BddAbove U) {x : ℝ}
    (hx : x ∈ U) : x < sSup U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hmem : x + δ / 2 ∈ U := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, show x + δ / 2 - x = δ / 2 by ring,
      abs_of_pos (by linarith)]
    linarith
  exact lt_of_lt_of_le (by linarith) (le_csSup hb hmem)

/-- **The four shapes of a nonempty open interval of the line.**  A nonempty open order-connected
set of reals is the whole line, an open half-line in either direction, or a bounded open interval.
The proof is the four combinations of boundedness above and below, with the ends read off as the
infimum and the supremum; openness is what removes the closed-ended shapes. -/
theorem isOpen_ordConnected_cases {U : Set ℝ} (hU : IsOpen U) (hoc : U.OrdConnected)
    (hne : U.Nonempty) :
    U = univ ∨ (∃ a, U = Ioi a) ∨ (∃ b, U = Iio b) ∨ ∃ a b, a < b ∧ U = Ioo a b := by
  by_cases hbb : BddBelow U
  · by_cases hba : BddAbove U
    · -- bounded both ways: an open interval
      obtain ⟨x, hx⟩ := id hne
      refine Or.inr (Or.inr (Or.inr ⟨sInf U, sSup U,
        lt_trans (sInf_lt_of_mem_of_isOpen hU hbb hx) (lt_sSup_of_mem_of_isOpen hU hba hx), ?_⟩))
      refine Subset.antisymm (fun y hy =>
        ⟨sInf_lt_of_mem_of_isOpen hU hbb hy, lt_sSup_of_mem_of_isOpen hU hba hy⟩) fun y hy => ?_
      obtain ⟨c, hc, hcy⟩ := exists_lt_of_csInf_lt hne hy.1
      obtain ⟨d, hd, hyd⟩ := exists_lt_of_lt_csSup hne hy.2
      exact hoc.out hc hd ⟨hcy.le, hyd.le⟩
    · -- bounded below only: a right half-line
      refine Or.inr (Or.inl ⟨sInf U, Subset.antisymm
        (fun y hy => sInf_lt_of_mem_of_isOpen hU hbb hy) fun y hy => ?_⟩)
      obtain ⟨c, hc, hcy⟩ := exists_lt_of_csInf_lt hne hy
      obtain ⟨d, hd, hyd⟩ := exists_gt_of_not_bddAbove hba y
      exact hoc.out hc hd ⟨hcy.le, hyd.le⟩
  · by_cases hba : BddAbove U
    · -- bounded above only: a left half-line
      refine Or.inr (Or.inr (Or.inl ⟨sSup U, Subset.antisymm
        (fun y hy => lt_sSup_of_mem_of_isOpen hU hba hy) fun y hy => ?_⟩))
      obtain ⟨c, hc, hcy⟩ := exists_lt_of_not_bddBelow hbb y
      obtain ⟨d, hd, hyd⟩ := exists_lt_of_lt_csSup hne hy
      exact hoc.out hc hd ⟨hcy.le, hyd.le⟩
    · -- unbounded both ways: the whole line
      refine Or.inl (eq_univ_of_forall fun y => ?_)
      obtain ⟨c, hc, hcy⟩ := exists_lt_of_not_bddBelow hbb y
      obtain ⟨d, hd, hyd⟩ := exists_gt_of_not_bddAbove hba y
      exact hoc.out hc hd ⟨hcy.le, hyd.le⟩

/-- **Every nonempty open interval of the line is the range of a `C^∞` diffeomorphism of the line
onto it**, with an explicit smooth inverse: there are `f : ℝ → ℝ`, `C^∞` on the line with all its
values in `U`, and `g`, `C^∞` on `U`, which are mutually inverse.

The four shapes of `isOpen_ordConnected_cases` are handled by four explicit formulas -- the
identity, `a + exp`, `b - exp` and the logistic curve `a + (b-a) e^x/(1+e^x)` -- each with the
matching logarithmic inverse, so no inverse function theorem is needed.  This is what turns a
parametrization of a manifold by an open interval of times into one by the whole line. -/
theorem exists_param_of_isOpen_ordConnected {U : Set ℝ} (hU : IsOpen U) (hoc : U.OrdConnected)
    (hne : U.Nonempty) :
    ∃ f g : ℝ → ℝ, ContDiff ℝ ∞ f ∧ ContDiffOn ℝ ∞ g U ∧ (∀ x, f x ∈ U) ∧
      (∀ x, g (f x) = x) ∧ ∀ v ∈ U, f (g v) = v := by
  have hexp : ∀ x : ℝ, 0 < Real.exp x := fun x => Real.exp_pos x
  rcases isOpen_ordConnected_cases hU hoc hne with h | ⟨a, h⟩ | ⟨b, h⟩ | ⟨a, b, hab, h⟩
  · exact ⟨id, id, contDiff_id, contDiffOn_id, fun x => by rw [h]; exact mem_univ x,
      fun _ => rfl, fun _ _ => rfl⟩
  · -- the right half-line `Ioi a`
    refine ⟨fun x => a + Real.exp x, fun v => Real.log (v - a),
      contDiff_const.add Real.contDiff_exp, fun v hv => ?_, fun x => ?_, fun x => ?_,
      fun v hv => ?_⟩
    · rw [h, mem_Ioi] at hv
      exact (Real.contDiffAt_log.2 (by linarith)).comp_contDiffWithinAt v
        (contDiff_id.sub contDiff_const).contDiffWithinAt
    · rw [h]; exact by simpa using hexp x
    · show Real.log (a + Real.exp x - a) = x
      rw [show a + Real.exp x - a = Real.exp x by ring, Real.log_exp]
    · rw [h, mem_Ioi] at hv
      show a + Real.exp (Real.log (v - a)) = v
      rw [Real.exp_log (by linarith)]
      ring
  · -- the left half-line `Iio b`
    refine ⟨fun x => b - Real.exp x, fun v => Real.log (b - v),
      contDiff_const.sub Real.contDiff_exp, fun v hv => ?_, fun x => ?_, fun x => ?_,
      fun v hv => ?_⟩
    · rw [h, mem_Iio] at hv
      exact (Real.contDiffAt_log.2 (by linarith)).comp_contDiffWithinAt v
        (contDiff_const.sub contDiff_id).contDiffWithinAt
    · rw [h]; exact by simpa using hexp x
    · show Real.log (b - (b - Real.exp x)) = x
      rw [show b - (b - Real.exp x) = Real.exp x by ring, Real.log_exp]
    · rw [h, mem_Iio] at hv
      show b - Real.exp (Real.log (b - v)) = v
      rw [Real.exp_log (by linarith)]
      ring
  · -- the bounded interval `Ioo a b`: the logistic curve
    have hden : ∀ x : ℝ, (1 : ℝ) + Real.exp x ≠ 0 := fun x => by positivity
    refine ⟨fun x => a + (b - a) * (Real.exp x / (1 + Real.exp x)),
      fun v => Real.log ((v - a) / (b - v)),
      contDiff_const.add (contDiff_const.mul
        (Real.contDiff_exp.div (contDiff_const.add Real.contDiff_exp) hden)),
      fun v hv => ?_, fun x => ?_, fun x => ?_, fun v hv => ?_⟩
    · rw [h, mem_Ioo] at hv
      have hbv : b - v ≠ 0 := by intro hc; linarith [sub_eq_zero.1 hc]
      have hpos : (v - a) / (b - v) ≠ 0 := by
        refine ne_of_gt (div_pos (by linarith) (by linarith))
      have hinner : ContDiffAt ℝ ∞ (fun w : ℝ => (w - a) / (b - w)) v :=
        ContDiffAt.div (contDiff_id.sub contDiff_const).contDiffAt
          (contDiff_const.sub contDiff_id).contDiffAt hbv
      exact ((Real.contDiffAt_log.2 hpos).comp v hinner).contDiffWithinAt
    · -- the value lies in `Ioo a b`
      have h1 : 0 < Real.exp x / (1 + Real.exp x) :=
        div_pos (hexp x) (by linarith [hexp x])
      have h2 : Real.exp x / (1 + Real.exp x) < 1 := by
        rw [div_lt_one (by linarith [hexp x])]
        linarith
      rw [h, mem_Ioo]
      constructor
      · nlinarith
      · nlinarith
    · -- the logarithm inverts the logistic curve
      have he : 0 < Real.exp x := hexp x
      have hd : (1 : ℝ) + Real.exp x ≠ 0 := hden x
      have hba : b - a ≠ 0 := sub_ne_zero.2 (by linarith)
      have h2 : b - (a + (b - a) * (Real.exp x / (1 + Real.exp x)))
          = (b - a) / (1 + Real.exp x) := by
        rw [eq_div_iff hd]
        field_simp
        ring
      have hY : b - (a + (b - a) * (Real.exp x / (1 + Real.exp x))) ≠ 0 := by
        rw [h2]; exact div_ne_zero hba hd
      have key : (a + (b - a) * (Real.exp x / (1 + Real.exp x)) - a) /
          (b - (a + (b - a) * (Real.exp x / (1 + Real.exp x)))) = Real.exp x := by
        rw [div_eq_iff hY]
        field_simp
        ring
      show Real.log ((a + (b - a) * (Real.exp x / (1 + Real.exp x)) - a) /
          (b - (a + (b - a) * (Real.exp x / (1 + Real.exp x))))) = x
      rw [key, Real.log_exp]
    · -- the logistic curve inverts the logarithm
      rw [h, mem_Ioo] at hv
      have hbv : (0 : ℝ) < b - v := by linarith
      have hva : (0 : ℝ) < v - a := by linarith
      have hr : 0 < (v - a) / (b - v) := div_pos hva hbv
      show a + (b - a) * (Real.exp (Real.log ((v - a) / (b - v))) /
        (1 + Real.exp (Real.log ((v - a) / (b - v))))) = v
      rw [Real.exp_log hr]
      have hd : (1 : ℝ) + (v - a) / (b - v) ≠ 0 := by positivity
      field_simp
      ring

end OpenIntervals

/-! ## Restricting a smooth arc to an open subinterval -/

section Shrink

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **A smooth arc restricted to an open subinterval of its target, with the parameter shifted by
`m`.**  The new coordinate is `A.toFun · - m`, the new source is the part of the old one with
coordinate in `Ioo c d`, and the new target is `Ioo (c - m) (d - m)`.

The new target is *open*, so the restricted arc has no boundary point in its source -- which is
exactly the point of the construction: it turns an arc issuing from a boundary point, whose target
is half-open, into a centred arc with symmetric open target, and those are the arcs that the
unit-speed-curve machinery of Stage 7 accepts. -/
def SmoothArc.shrink (A : SmoothArc I n M) {c d : ℝ} (hcd : c < d) (hsub : Ioo c d ⊆ A.target)
    (m : ℝ) : SmoothArc I n M where
  toFun x := A.toFun x - m
  invFun t := A.invFun (t + m)
  source := A.source ∩ A.toFun ⁻¹' Ioo c d
  target := Ioo (c - m) (d - m)
  map_source' x hx := ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
  map_target' t ht := by
    have hmem : t + m ∈ Ioo c d := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨A.map_target (hsub hmem), by
      rw [Set.mem_preimage, A.right_inv (hsub hmem)]; exact hmem⟩
  left_inv' x hx := by
    show A.invFun (A.toFun x - m + m) = x
    rw [show A.toFun x - m + m = A.toFun x by ring, A.left_inv hx.1]
  right_inv' t ht := by
    have hmem : t + m ∈ Ioo c d := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    show A.toFun (A.invFun (t + m)) - m = t
    rw [A.right_inv (hsub hmem)]; ring
  open_source := A.continuousOn_toFun.isOpen_inter_preimage A.open_source isOpen_Ioo
  ordConnected_target := ordConnected_Ioo
  nontrivial_target := ⟨c - m + (d - c) / 3, ⟨by linarith, by linarith⟩,
    c - m + 2 * (d - c) / 3, ⟨by linarith, by linarith⟩, by intro hcon; linarith⟩
  bddAbove_target := bddAbove_Ioo
  bddBelow_target := bddBelow_Ioo
  continuousOn_toFun := (A.continuousOn_toFun.mono inter_subset_left).sub continuousOn_const
  continuousOn_invFun := A.continuousOn_invFun.comp
    (continuous_id.add continuous_const).continuousOn
    (fun t ht => hsub ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  bdry x hx := by
    have hxt : A.toFun x ∈ Ioo c d := hx.2
    have hint : A.toFun x ∈ interior A.target := interior_maximal hsub isOpen_Ioo hxt
    have h1 : x ∉ I.boundary M := fun hbd => ((A.bdry x hx.1).1 hbd) hint
    have h2 : A.toFun x - m ∈ interior (Ioo (c - m) (d - m)) := by
      rw [interior_Ioo]
      exact ⟨by linarith [hxt.1], by linarith [hxt.2]⟩
    exact iff_of_false h1 (not_not_intro h2)
  contMDiffOn_toFun := (A.contMDiffOn_toFun.mono inter_subset_left).sub contMDiffOn_const
  contMDiffOn_invFun := A.contMDiffOn_invFun.comp
    (contDiff_id.add contDiff_const).contMDiff.contMDiffOn
    (fun t ht => hsub ⟨by linarith [ht.1], by linarith [ht.2]⟩)

@[simp] theorem SmoothArc.shrink_toFun (A : SmoothArc I n M) {c d : ℝ} (hcd : c < d)
    (hsub : Ioo c d ⊆ A.target) (m : ℝ) (x : M) :
    (A.shrink hcd hsub m).toFun x = A.toFun x - m := rfl

@[simp] theorem SmoothArc.shrink_invFun (A : SmoothArc I n M) {c d : ℝ} (hcd : c < d)
    (hsub : Ioo c d ⊆ A.target) (m : ℝ) (t : ℝ) :
    (A.shrink hcd hsub m).invFun t = A.invFun (t + m) := rfl

@[simp] theorem SmoothArc.shrink_source (A : SmoothArc I n M) {c d : ℝ} (hcd : c < d)
    (hsub : Ioo c d ⊆ A.target) (m : ℝ) :
    (A.shrink hcd hsub m).source = A.source ∩ A.toFun ⁻¹' Ioo c d := rfl

@[simp] theorem SmoothArc.shrink_target (A : SmoothArc I n M) {c d : ℝ} (hcd : c < d)
    (hsub : Ioo c d ⊆ A.target) (m : ℝ) :
    (A.shrink hcd hsub m).target = Ioo (c - m) (d - m) := rfl

/-- **Restricting and shifting preserves unit speed.**  The transition from the new parameter to the
old one is `s ↦ s + m`, whose derivative is `1`, so the cocycle rule of the length element gives the
new density as the old one times `|1|`. -/
theorem SmoothArc.unitSpeed_shrink {L : LengthElement I n M} (A : SmoothArc I n M)
    (hA : UnitSpeed L A) {c d : ℝ} (hcd : c < d) (hsub : Ioo c d ⊆ A.target) (m : ℝ) :
    UnitSpeed L (A.shrink hcd hsub m) := by
  intro u hu
  have hu' : u ∈ Ioo (c - m) (d - m) := hu
  have hum : u + m ∈ Ioo c d := ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
  have humt : u + m ∈ A.target := hsub hum
  have hx : (A.shrink hcd hsub m).invFun u ∈ A.source := A.map_target humt
  have hco := L.cocycle (A.shrink hcd hsub m).toRealChart A.toRealChart u hu hx
  have hval : A.toFun ((A.shrink hcd hsub m).invFun u) = u + m := A.right_inv humt
  have htd : transDeriv (A.shrink hcd hsub m).toRealChart A.toRealChart u = 1 := by
    have hderiv : HasDerivWithinAt
        (fun s => A.toFun ((A.shrink hcd hsub m).invFun s)) 1 (A.shrink hcd hsub m).target u := by
      refine ((hasDerivWithinAt_id u (A.shrink hcd hsub m).target).add_const m).congr
        (fun s hs => ?_) ?_
      · exact A.right_inv (hsub ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      · exact A.right_inv humt
    exact hderiv.derivWithin
      ((A.shrink hcd hsub m).toRealChart.uniqueDiffOn_target u hu)
  rw [hco]
  simp only [SmoothArc.toRealChart_toFun, SmoothArc.toRealChart_invFun]
  rw [hval, htd, hA _ humt]
  norm_num

end Shrink

/-! ## Unit-speed curves: further general facts -/

section CurveFacts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {L : LengthElement I ∞ M} {γ : ℝ → M} {U : Set ℝ}

/-- **No value of a unit-speed curve is a boundary point.**  Near one of its times the curve is the
parametrization of an arc on a whole open interval of parameters, so the parameter of the value is
an *interior* point of the arc's target, and the boundary law of an arc says exactly that such a
point of the source is not a boundary point.

This is the reason a manifold with boundary cannot be parametrized by a unit-speed curve through its
boundary point, and hence the reason Stage 8 treats the two cases separately. -/
theorem IsUnitSpeedCurveOn.notMem_boundary (h : IsUnitSpeedCurveOn L γ U) {t : ℝ} (ht : t ∈ U) :
    γ t ∉ I.boundary M := by
  obtain ⟨A, k, η, -, hη, -, hdesc⟩ := h t ht
  have htmem : t ∈ Ioo (t - η) (t + η) := ⟨by linarith, by linarith⟩
  have hsubt : Ioo (t - η - k) (t + η - k) ⊆ A.target := by
    intro v hv
    have := (hdesc (v + k) ⟨by linarith [hv.1], by linarith [hv.2]⟩).1
    simpa using this
  have hint : t - k ∈ interior A.target :=
    interior_maximal hsubt isOpen_Ioo ⟨by linarith, by linarith⟩
  have hxs : γ t ∈ A.source := by
    rw [(hdesc t htmem).2]; exact A.map_target (hdesc t htmem).1
  intro hbd
  have hcon := (A.bdry _ hxs).1 hbd
  rw [(hdesc t htmem).2, A.right_inv (hdesc t htmem).1] at hcon
  exact hcon hint

/-- **A unit-speed curve is `C^∞` on its interval of times**, being locally the parametrization of a
smooth arc composed with a translation. -/
theorem IsUnitSpeedCurveOn.contMDiffOn (h : IsUnitSpeedCurveOn L γ U) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ U := by
  intro t ht
  obtain ⟨A, k, η, -, hη, -, hdesc⟩ := h t ht
  have hshift : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => s - k) (Ioo (t - η) (t + η)) :=
    (contDiff_id.sub contDiff_const).contMDiff.contMDiffOn
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun s => A.invFun (s - k)) (Ioo (t - η) (t + η)) :=
    A.contMDiffOn_invFun.comp hshift fun s hs => (hdesc s hs).1
  have h1 : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Ioo (t - η) (t + η)) :=
    hcomp.congr fun s hs => (hdesc s hs).2
  exact (h1.contMDiffAt (Ioo_mem_nhds (by linarith) (by linarith))).contMDiffWithinAt

/-- **The image of a unit-speed curve is open.**  Around each of its times the curve is the
parametrization of a smooth arc, and an arc carries open sets of parameters to open sets of points
(`SmoothArc.isOpen_image`). -/
theorem IsUnitSpeedCurveOn.isOpen_image (h : IsUnitSpeedCurveOn L γ U) : IsOpen (γ '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨t, ht, rfl⟩
  obtain ⟨A, k, η, -, hη, hIoo, hdesc⟩ := h t ht
  have htmem : t ∈ Ioo (t - η) (t + η) := ⟨by linarith, by linarith⟩
  refine ⟨A.invFun '' (Ioo (t - η - k) (t + η - k) ∩ A.target), ?_,
    A.isOpen_image isOpen_Ioo, ?_⟩
  · rintro y ⟨v, ⟨hvV, hvT⟩, rfl⟩
    have hmem : v + k ∈ Ioo (t - η) (t + η) := ⟨by linarith [hvV.1], by linarith [hvV.2]⟩
    refine ⟨v + k, hIoo hmem, ?_⟩
    rw [(hdesc _ hmem).2]
    congr 1
    ring
  · exact ⟨t - k, ⟨⟨by linarith, by linarith⟩, (hdesc t htmem).1⟩, ((hdesc t htmem).2).symm⟩

/-- **A shifted unit-speed arc with open target is a unit-speed curve.**  This is Stage 7's
`isUnitSpeedCurveOn_arc` with the hypothesis `I.boundary M = ∅` replaced by the weaker and
sufficient one that the arc's target be open; on a manifold with boundary the arcs produced by
`SmoothArc.shrink` have open targets, and this is what lets the curve machinery run there. -/
theorem isUnitSpeedCurveOn_arc' {A : SmoothArc I ∞ M} (hopen : IsOpen A.target)
    (hA : UnitSpeed L A) (k : ℝ) :
    IsUnitSpeedCurveOn L (fun s => A.invFun (s - k)) {s | s - k ∈ A.target} := by
  have hopen' : IsOpen {s : ℝ | s - k ∈ A.target} :=
    hopen.preimage (continuous_id.sub continuous_const)
  intro t ht
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hopen' t ht
  have hIoo : Ioo (t - η) (t + η) ⊆ {s : ℝ | s - k ∈ A.target} := by
    intro s hs
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  exact ⟨A, k, η, hA, hη, hIoo, fun s hs => ⟨hIoo hs, rfl⟩⟩

end CurveFacts

/-! ## Propagation without a boundarylessness hypothesis -/

section Propagation'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {L : LengthElement I ∞ M}

/-- Stage 7's `eqOn_shift_of_eventuallyEq` with `I.boundary M = ∅` replaced by openness of the arc's
target: a unit-speed curve agreeing with a shifted arc parametrization near one time agrees with it
at every time where both are defined. -/
theorem eqOn_shift_of_eventuallyEq' {γ : ℝ → M} {U : Set ℝ} (hU : U.OrdConnected)
    (h : IsUnitSpeedCurveOn L γ U) {B : SmoothArc I ∞ M} (hopen : IsOpen B.target)
    (hB : UnitSpeed L B) {u t : ℝ} (ht : t ∈ U) (htB : t - u ∈ B.target)
    (hloc : ∀ᶠ s in 𝓝 t, γ s = B.invFun (s - u)) :
    EqOn γ (fun s => B.invFun (s - u)) (U ∩ {s | s - u ∈ B.target}) := by
  have hWopen : IsOpen {s : ℝ | s - u ∈ B.target} :=
    hopen.preimage (continuous_id.sub continuous_const)
  have hUopen : IsOpen U := h.isOpen
  refine eqOn_of_eventuallyEq (hU.inter (ordConnected_shift B u))
    (h.mono (hUopen.inter hWopen) inter_subset_left)
    ((isUnitSpeedCurveOn_arc' hopen hB u).mono (hUopen.inter hWopen) inter_subset_right)
    (show t ∈ U ∩ {s : ℝ | s - u ∈ B.target} from ⟨ht, htB⟩) hloc

/-- **Stage 7's `IsUnitSpeedCurveOn.exists_shift`, restated without the boundarylessness hypothesis
and with the arc identified.**

Let `γ` be a unit-speed curve on an interval `U` of times and let `B` be a unit-speed arc with
symmetric open target `Ioo (-ε) ε` whose source contains `γ t`.  Then, after possibly reversing
`B`'s coordinate -- and `B'` below *is* `B` or `B.neg` -- the curve agrees with the shifted
parametrization `s ↦ B'.invFun (s - u)` at every time of `U` in `Ioo (u - ε) (u + ε)`, that shifted
parametrization is itself a unit-speed curve on the whole of `Ioo (u - ε) (u + ε)`, and `|t - u| =
|B.toFun (γ t)|`, `B'.invFun 0 = B.invFun 0`.

Two changes from Stage 7's version, both needed here.  First, `I.boundary M = ∅` is dropped: it was
used only to know that `B'.target` is open, and that is part of the hypothesis `B.target = Ioo (-ε)
ε` -- so the statement is available on a manifold *with* boundary, which is what the half-line case
of Stage 8 needs.  Second, the conclusion records that `B'` is `B` or `B.neg`, which is what
identifies the direction in which the curve runs through the arc, and hence which end of its
interval of times corresponds to the arc's parameter `0`. -/
theorem IsUnitSpeedCurveOn.exists_shift' {γ : ℝ → M} {U : Set ℝ} (hU : U.OrdConnected)
    (h : IsUnitSpeedCurveOn L γ U) {t : ℝ} (ht : t ∈ U) {B : SmoothArc I ∞ M} {ε : ℝ}
    (hB : UnitSpeed L B) (hBt : B.target = Ioo (-ε) ε) (hmem : γ t ∈ B.source) :
    ∃ (B' : SmoothArc I ∞ M) (u : ℝ), UnitSpeed L B' ∧ B'.target = Ioo (-ε) ε ∧
      |t - u| = |B.toFun (γ t)| ∧ B'.invFun 0 = B.invFun 0 ∧
      IsUnitSpeedCurveOn L (fun s => B'.invFun (s - u)) (Ioo (u - ε) (u + ε)) ∧
      EqOn γ (fun s => B'.invFun (s - u)) (U ∩ Ioo (u - ε) (u + ε)) ∧
      (B' = B ∨ B' = B.neg) := by
  obtain ⟨σ, hσ, δ, hδ, hloc⟩ := h.exists_sign ht hB hmem
  have hctgt : B.toFun (γ t) ∈ Ioo (-ε) ε := by rw [← hBt]; exact B.map_source hmem
  set c := B.toFun (γ t) with hc
  have hnegt : B.neg.target = Ioo (-ε) ε := by
    rw [SmoothArc.neg_target, hBt]
    ext v
    simp only [Set.mem_neg, mem_Ioo]
    exact ⟨fun hv => ⟨by linarith [hv.2], by linarith [hv.1]⟩,
      fun hv => ⟨by linarith [hv.2], by linarith [hv.1]⟩⟩
  have main : ∀ (B' : SmoothArc I ∞ M) (u : ℝ), UnitSpeed L B' → B'.target = Ioo (-ε) ε →
      |t - u| = |c| → B'.invFun 0 = B.invFun 0 → (B' = B ∨ B' = B.neg) →
      (∀ s ∈ Ioo (t - δ) (t + δ), γ s = B'.invFun (s - u)) →
      ∃ (B'' : SmoothArc I ∞ M) (u' : ℝ), UnitSpeed L B'' ∧ B''.target = Ioo (-ε) ε ∧
        |t - u'| = |c| ∧ B''.invFun 0 = B.invFun 0 ∧
        IsUnitSpeedCurveOn L (fun s => B''.invFun (s - u')) (Ioo (u' - ε) (u' + ε)) ∧
        EqOn γ (fun s => B''.invFun (s - u')) (U ∩ Ioo (u' - ε) (u' + ε)) ∧
        (B'' = B ∨ B'' = B.neg) := by
    intro B' u hB' hB't habs hcent hor hdesc
    have hB'open : IsOpen B'.target := by rw [hB't]; exact isOpen_Ioo
    have hWeq : {s : ℝ | s - u ∈ B'.target} = Ioo (u - ε) (u + ε) := shift_eq_Ioo hB't u
    have hcurve : IsUnitSpeedCurveOn L (fun s => B'.invFun (s - u)) (Ioo (u - ε) (u + ε)) := by
      rw [← hWeq]; exact isUnitSpeedCurveOn_arc' hB'open hB' u
    have habs' : |t - u| < ε := by
      rw [habs, abs_lt]
      exact ⟨by linarith [hctgt.1], by linarith [hctgt.2]⟩
    have htB : t - u ∈ B'.target := by
      rw [hB't, mem_Ioo]
      rw [abs_lt] at habs'
      exact ⟨by linarith [habs'.2], by linarith [habs'.1]⟩
    have heq := eqOn_shift_of_eventuallyEq' hU h hB'open hB' ht htB
      (Filter.eventually_iff_exists_mem.2 ⟨Ioo (t - δ) (t + δ),
        Ioo_mem_nhds (by linarith) (by linarith), hdesc⟩)
    refine ⟨B', u, hB', hB't, habs, hcent, hcurve, ?_, hor⟩
    rw [← hWeq]; exact heq
  rcases hσ with h1 | h1
  · refine main B (t - c) hB hBt ?_ rfl (Or.inl rfl) fun s hs => ?_
    · rw [show t - (t - c) = c by ring]
    · obtain ⟨hsrc, hval⟩ := hloc s hs
      rw [h1, one_mul] at hval
      conv_lhs => rw [← B.left_inv hsrc]
      rw [hval]
      congr 1
      ring
  · refine main B.neg (t + c) hB.neg hnegt ?_ (by simp) (Or.inr rfl) fun s hs => ?_
    · rw [show t - (t + c) = -c by ring, abs_neg]
    · obtain ⟨hsrc, hval⟩ := hloc s hs
      show γ s = B.invFun (-(s - (t + c)))
      conv_lhs => rw [← B.left_inv hsrc]
      congr 1
      rw [hval, h1]
      ring

end Propagation'

/-! ## Two times with the same value, on an interval of times -/

section Shift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {L : LengthElement I ∞ M}

include hE

/-- **Two times with the same value produce a shift: Stage 7's `periodic_of_eq` on an interval of
times, and without a boundarylessness hypothesis.**

Let `γ` be a unit-speed curve on an *interval* `U` of times and suppose `γ t₁ = γ t₂`.  Then `γ s =
γ (s + (t₂ - t₁))` at every time `s` for which both `s` and `s + (t₂ - t₁)` are times of the curve.
When `U` is the whole line this is exactly periodicity with period `t₂ - t₁`.

Two changes from Stage 7's version.  (i) `U` is an arbitrary interval, so the shifted curve is a
unit-speed curve on the *shifted* interval and the propagation lemma can only be run on the
intersection -- which is all that is needed.  (ii) `I.boundary M = ∅` is dropped: it was used only
to produce a centred unit-speed arc at the common value, and `IsUnitSpeedCurveOn.notMem_boundary`
shows that value is not a boundary point, so Stage 4's `exists_unitSpeed_of_notMem_boundary` applies
directly.

The mechanism is Milnor's Step 5.  Read in a unit-speed arc `B` centred at the common value, the
curve has slope `σ₁ = ±1` near `t₁` and `σ₂ = ±1` near `t₂`.  If the signs agree the shift follows
by propagation; if they disagree the curve would reflect about the midpoint `(t₁+t₂)/2`,
contradicting the local injectivity of a unit-speed curve.  **So the two slopes must agree** -- the
geometric fact the plan singles out as the one part of Step 5 with no counterpart in the topological
Appendix. -/
theorem eqOn_add_of_eq {γ : ℝ → M} {U : Set ℝ} (hU : U.OrdConnected)
    (hγ : IsUnitSpeedCurveOn L γ U) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ U) (ht₂ : t₂ ∈ U)
    (heq : γ t₁ = γ t₂) : ∀ s ∈ U, s + (t₂ - t₁) ∈ U → γ s = γ (s + (t₂ - t₁)) := by
  obtain ⟨B, ε, hε, hqB, hq0, hBt, hB⟩ :=
    exists_unitSpeed_of_notMem_boundary I hE L (hγ.notMem_boundary ht₁)
  obtain ⟨σ₁, hσ₁, δ₁, hδ₁, hloc₁⟩ := hγ.exists_sign ht₁ hB hqB
  obtain ⟨σ₂, hσ₂, δ₂, hδ₂, hloc₂⟩ := hγ.exists_sign ht₂ hB (by rw [← heq]; exact hqB)
  have hq0' : B.toFun (γ t₂) = 0 := by rw [← heq]; exact hq0
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  by_cases hsign : σ₁ = σ₂
  · -- the slopes agree: the difference of the two times is a shift
    have hagree : ∀ w, |w| < min δ₁ δ₂ → γ (t₁ + w) = γ (t₂ + w) := by
      intro w hw
      rw [abs_lt] at hw
      have h1 := hloc₁ (t₁ + w) ⟨by linarith [hw.1, min_le_left δ₁ δ₂],
        by linarith [hw.2, min_le_left δ₁ δ₂]⟩
      have h2 := hloc₂ (t₂ + w) ⟨by linarith [hw.1, min_le_right δ₁ δ₂],
        by linarith [hw.2, min_le_right δ₁ δ₂]⟩
      refine B.injOn h1.1 h2.1 ?_
      rw [h1.2, h2.2, hq0, hq0', hsign]
      ring
    have hVoc : ({s : ℝ | s + (t₂ - t₁) ∈ U}).OrdConnected :=
      ⟨fun a ha b hb c hc => hU.out ha hb ⟨by linarith [hc.1], by linarith [hc.2]⟩⟩
    have hcurve₂ : IsUnitSpeedCurveOn L (fun s => γ (s + (t₂ - t₁))) {s | s + (t₂ - t₁) ∈ U} :=
      hγ.comp_add (t₂ - t₁)
    have hVopen : IsOpen (U ∩ {s : ℝ | s + (t₂ - t₁) ∈ U}) :=
      hγ.isOpen.inter (hγ.isOpen.preimage (continuous_id.add continuous_const))
    have ht₁V : t₁ ∈ U ∩ {s : ℝ | s + (t₂ - t₁) ∈ U} := by
      refine ⟨ht₁, ?_⟩
      show t₁ + (t₂ - t₁) ∈ U
      rw [show t₁ + (t₂ - t₁) = t₂ from by ring]
      exact ht₂
    have hlocal : γ =ᶠ[𝓝 t₁] fun s => γ (s + (t₂ - t₁)) := by
      filter_upwards [Ioo_mem_nhds (show t₁ - min δ₁ δ₂ < t₁ by linarith)
        (show t₁ < t₁ + min δ₁ δ₂ by linarith)] with s hs
      have hw : |s - t₁| < min δ₁ δ₂ := by
        rw [abs_lt]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h := hagree (s - t₁) hw
      rw [show t₁ + (s - t₁) = s from by ring, show t₂ + (s - t₁) = s + (t₂ - t₁) from by ring] at h
      exact h
    have hres := eqOn_of_eventuallyEq (hU.inter hVoc)
      (hγ.mono hVopen inter_subset_left) (hcurve₂.mono hVopen inter_subset_right) ht₁V hlocal
    intro s hs hs'
    exact hres ⟨hs, hs'⟩
  · -- the slopes disagree: the curve would reflect, contradicting local injectivity
    exfalso
    have hopp : σ₂ = -σ₁ := by
      rcases hσ₁ with h | h <;> rcases hσ₂ with h' | h'
      · exact absurd (h.trans h'.symm) hsign
      · rw [h', h]
      · rw [h', h]; norm_num
      · exact absurd (h.trans h'.symm) hsign
    have hagree : ∀ w, |w| < min δ₁ δ₂ → γ (t₁ + w) = γ (t₂ - w) := by
      intro w hw
      rw [abs_lt] at hw
      have h1 := hloc₁ (t₁ + w) ⟨by linarith [hw.1, min_le_left δ₁ δ₂],
        by linarith [hw.2, min_le_left δ₁ δ₂]⟩
      have h2 := hloc₂ (t₂ - w) ⟨by linarith [hw.2, min_le_right δ₁ δ₂],
        by linarith [hw.1, min_le_right δ₁ δ₂]⟩
      refine B.injOn h1.1 h2.1 ?_
      rw [h1.2, h2.2, hq0, hq0', hopp]
      ring
    have hset : {s : ℝ | s + -(t₁ + t₂) ∈ {s : ℝ | -s ∈ U}} = {s : ℝ | -s + (t₁ + t₂) ∈ U} := by
      ext s
      constructor
      · intro hs
        show -s + (t₁ + t₂) ∈ U
        have hs' : -(s + -(t₁ + t₂)) ∈ U := hs
        rwa [show -(s + -(t₁ + t₂)) = -s + (t₁ + t₂) from by ring] at hs'
      · intro hs
        show -(s + -(t₁ + t₂)) ∈ U
        rwa [show -(s + -(t₁ + t₂)) = -s + (t₁ + t₂) from by ring]
    have hcurve₂ : IsUnitSpeedCurveOn L (fun s => γ (-s + (t₁ + t₂)))
        {s : ℝ | -s + (t₁ + t₂) ∈ U} := by
      have h := (hγ.comp_neg).comp_add (-(t₁ + t₂))
      rw [hset] at h
      refine h.congr fun s _ => ?_
      show γ (-s + (t₁ + t₂)) = γ (-(s + -(t₁ + t₂)))
      rw [show -(s + -(t₁ + t₂)) = -s + (t₁ + t₂) from by ring]
    have hWoc : ({s : ℝ | -s + (t₁ + t₂) ∈ U}).OrdConnected :=
      ⟨fun a ha b hb c hc => hU.out hb ha ⟨by linarith [hc.2], by linarith [hc.1]⟩⟩
    have hWopen : IsOpen (U ∩ {s : ℝ | -s + (t₁ + t₂) ∈ U}) :=
      hγ.isOpen.inter (hγ.isOpen.preimage (continuous_neg.add continuous_const))
    have ht₁W : t₁ ∈ U ∩ {s : ℝ | -s + (t₁ + t₂) ∈ U} := by
      refine ⟨ht₁, ?_⟩
      show -t₁ + (t₁ + t₂) ∈ U
      rw [show -t₁ + (t₁ + t₂) = t₂ from by ring]
      exact ht₂
    have hlocal : γ =ᶠ[𝓝 t₁] fun s => γ (-s + (t₁ + t₂)) := by
      filter_upwards [Ioo_mem_nhds (show t₁ - min δ₁ δ₂ < t₁ by linarith)
        (show t₁ < t₁ + min δ₁ δ₂ by linarith)] with s hs
      have hw : |s - t₁| < min δ₁ δ₂ := by
        rw [abs_lt]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
      have h := hagree (s - t₁) hw
      rw [show t₁ + (s - t₁) = s from by ring,
        show t₂ - (s - t₁) = -s + (t₁ + t₂) from by ring] at h
      exact h
    have hrefl := eqOn_of_eventuallyEq (hU.inter hWoc)
      (hγ.mono hWopen inter_subset_left) (hcurve₂.mono hWopen inter_subset_right) ht₁W hlocal
    have hm : (t₁ + t₂) / 2 ∈ U := by
      rcases le_total t₁ t₂ with hle | hle
      · exact hU.out ht₁ ht₂ ⟨by linarith, by linarith⟩
      · exact hU.out ht₂ ht₁ ⟨by linarith, by linarith⟩
    obtain ⟨η, hη, hsubU, hinj⟩ := hγ.exists_injOn hm
    have h1 : (t₁ + t₂) / 2 + η / 2 ∈ Ioo ((t₁ + t₂) / 2 - η) ((t₁ + t₂) / 2 + η) :=
      ⟨by linarith, by linarith⟩
    have h2 : (t₁ + t₂) / 2 - η / 2 ∈ Ioo ((t₁ + t₂) / 2 - η) ((t₁ + t₂) / 2 + η) :=
      ⟨by linarith, by linarith⟩
    have hmW : (t₁ + t₂) / 2 + η / 2 ∈ U ∩ {s : ℝ | -s + (t₁ + t₂) ∈ U} := by
      refine ⟨hsubU h1, ?_⟩
      show -((t₁ + t₂) / 2 + η / 2) + (t₁ + t₂) ∈ U
      rw [show -((t₁ + t₂) / 2 + η / 2) + (t₁ + t₂) = (t₁ + t₂) / 2 - η / 2 from by ring]
      exact hsubU h2
    have hval := hrefl hmW
    have hval' : γ ((t₁ + t₂) / 2 + η / 2) = γ ((t₁ + t₂) / 2 - η / 2) := by
      rw [hval]
      show γ (-((t₁ + t₂) / 2 + η / 2) + (t₁ + t₂)) = γ ((t₁ + t₂) / 2 - η / 2)
      rw [show -((t₁ + t₂) / 2 + η / 2) + (t₁ + t₂) = (t₁ + t₂) / 2 - η / 2 from by ring]
    have hcon := hinj h1 h2 hval'
    linarith

/-- **A unit-speed curve with a repeated value has a compact open image of a compact interval.**

If `γ t₁ = γ t₂` with `t₁ < t₂`, then `γ '' Icc t₁ t₂` is compact -- being a continuous image of a
compact interval -- *and* open, because by `eqOn_add_of_eq` the curve on a slightly larger open
interval takes no values beyond those on `Icc t₁ t₂`, and the image of an open interval of times is
open.  In a preconnected manifold such a set is everything, so the manifold is compact and is
covered by the curve.  This is how non-compactness forces a unit-speed curve to be injective. -/
theorem isCompact_isOpen_image_Icc_of_eq {γ : ℝ → M} {U : Set ℝ} (hU : U.OrdConnected)
    (hγ : IsUnitSpeedCurveOn L γ U) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ U) (ht₂ : t₂ ∈ U) (hlt : t₁ < t₂)
    (heq : γ t₁ = γ t₂) :
    IsCompact (γ '' Icc t₁ t₂) ∧ IsOpen (γ '' Icc t₁ t₂) ∧ γ '' Icc t₁ t₂ ⊆ γ '' U := by
  have hshift := eqOn_add_of_eq I hE hU hγ ht₁ ht₂ heq
  have hIcc : Icc t₁ t₂ ⊆ U := fun s hs => hU.out ht₁ ht₂ hs
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.isOpen_iff.1 hγ.isOpen t₁ ht₁
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.isOpen_iff.1 hγ.isOpen t₂ ht₂
  have hδ : 0 < min (min δ₁ δ₂) (t₂ - t₁) := lt_min (lt_min hδ₁ hδ₂) (by linarith)
  have hδ1 : min (min δ₁ δ₂) (t₂ - t₁) ≤ δ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : min (min δ₁ δ₂) (t₂ - t₁) ≤ δ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδd : min (min δ₁ δ₂) (t₂ - t₁) ≤ t₂ - t₁ := min_le_right _ _
  set δ := min (min δ₁ δ₂) (t₂ - t₁) with hδdef
  have hIooU : Ioo (t₁ - δ) (t₂ + δ) ⊆ U := by
    intro s hs
    rcases le_or_gt s t₁ with h | h
    · refine hb₁ ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1], by linarith⟩
    · rcases le_or_gt s t₂ with h' | h'
      · exact hIcc ⟨h.le, h'⟩
      · refine hb₂ ?_
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        exact ⟨by linarith, by linarith [hs.2]⟩
  have himg : γ '' Ioo (t₁ - δ) (t₂ + δ) = γ '' Icc t₁ t₂ := by
    refine Subset.antisymm ?_ (fun x hx => ?_)
    swap
    · obtain ⟨s, hs, rfl⟩ := hx
      exact ⟨s, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
    rintro x ⟨s, hs, rfl⟩
    rcases le_or_gt t₁ s with h1 | h1
    · rcases le_or_gt s t₂ with h2 | h2
      · exact ⟨s, ⟨h1, h2⟩, rfl⟩
      · refine ⟨s - (t₂ - t₁), ⟨by linarith, by linarith [hs.2]⟩, ?_⟩
        have h3 : s - (t₂ - t₁) ∈ U := hIooU ⟨by linarith, by linarith [hs.2]⟩
        have h4 : s - (t₂ - t₁) + (t₂ - t₁) ∈ U := by
          rw [show s - (t₂ - t₁) + (t₂ - t₁) = s from by ring]; exact hIooU hs
        have h5 := hshift _ h3 h4
        rwa [show s - (t₂ - t₁) + (t₂ - t₁) = s from by ring] at h5
    · refine ⟨s + (t₂ - t₁), ⟨by linarith [hs.1], by linarith⟩, ?_⟩
      have h3 : s ∈ U := hIooU hs
      have h4 : s + (t₂ - t₁) ∈ U := hIooU ⟨by linarith [hs.1], by linarith⟩
      exact (hshift _ h3 h4).symm
  have hcont : ContinuousOn γ (Icc t₁ t₂) := fun s hs =>
    (hγ.continuousAt (hIcc hs)).continuousWithinAt
  refine ⟨isCompact_Icc.image_of_continuousOn hcont, ?_, fun x hx => ?_⟩
  swap
  · obtain ⟨s, hs, rfl⟩ := hx
    exact ⟨s, hIcc hs, rfl⟩
  rw [← himg]
  exact (hγ.mono isOpen_Ioo hIooU).isOpen_image

end Shift

/-! ## The maximal curve without compactness -/

section Maximal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {L : LengthElement I ∞ M}

omit hE [IsManifold I ∞ M] in
/-- Stage 7's `zero_mem_dom` without the boundarylessness hypothesis, which it used only through the
openness of the arc's target -- and that is part of the hypothesis `A₀.target = Ioo (-ε₀) ε₀`. -/
theorem zero_mem_dom' {A₀ : SmoothArc I ∞ M} {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hA₀ : UnitSpeed L A₀)
    (hA₀t : A₀.target = Ioo (-ε₀) ε₀) :
    (0 : ℝ) ∈ Dom I L A₀ ∧ globalCurve I L A₀ =ᶠ[𝓝 (0 : ℝ)] A₀.invFun := by
  have hcurve : IsUnitSpeedCurveOn L A₀.invFun (Ioo (-ε₀) ε₀) := by
    have h := isUnitSpeedCurveOn_arc' (A := A₀) (by rw [hA₀t]; exact isOpen_Ioo) hA₀ 0
    rw [shift_eq_Ioo hA₀t 0] at h
    simpa using h
  obtain ⟨hsub, heq⟩ :=
    subset_dom_and_eqOn I (show -ε₀ < 0 by linarith) hε₀ hcurve EventuallyEq.rfl
  refine ⟨hsub ⟨by linarith, hε₀⟩, ?_⟩
  filter_upwards [Ioo_mem_nhds (show -ε₀ < (0 : ℝ) by linarith) hε₀] with s hs
  exact (heq hs).symm

include hE

/-- **The image of the maximal unit-speed curve contains every non-boundary point of its closure.**

This is the continuation step of Stage 7's `not_bddAbove_dom`, isolated and freed of compactness: if
a point `q` which is not a boundary point is in the closure of the image, then a unit-speed arc `B`
of radius `ε` centred at `q` is met by the curve at some time `t` with `B`-coordinate less than
`ε/4` in absolute value, and `IsUnitSpeedCurveOn.exists_shift'` identifies the curve, on a *whole*
interval of radius `ε` about a time `u` within `ε/4` of `t`, with the parametrization of `B`.
Gluing that description to the curve gives a unit-speed curve with the right germ at `0` on an
interval containing `u`, so by maximality (`subset_dom_and_eqOn`) `u` is a reached time, and the
curve's value there is the centre `q`.

Compactness is nowhere used: the accumulation that Stage 7 obtained from compactness is here
supplied by the hypothesis that `q` is in the closure.  Consequently the image of the maximal curve
is closed as soon as the manifold has no boundary point, which is the surjectivity half of Stage 8.
-/
theorem mem_image_dom_of_mem_closure {A₀ : SmoothArc I ∞ M} {q : M} (hq : q ∉ I.boundary M)
    (hcl : q ∈ closure (globalCurve I L A₀ '' Dom I L A₀)) :
    q ∈ globalCurve I L A₀ '' Dom I L A₀ := by
  obtain ⟨B, ε, hε, hqB, hq0, hBt, hB⟩ := exists_unitSpeed_of_notMem_boundary I hE L hq
  have hBinv : B.invFun 0 = q := by rw [← hq0, B.left_inv hqB]
  have hNopen : IsOpen (B.source ∩ B.toFun ⁻¹' Ioo (-(ε / 4)) (ε / 4)) :=
    B.continuousOn_toFun.isOpen_inter_preimage B.open_source isOpen_Ioo
  have hqN : q ∈ B.source ∩ B.toFun ⁻¹' Ioo (-(ε / 4)) (ε / 4) :=
    ⟨hqB, by rw [Set.mem_preimage, hq0]; exact ⟨by linarith, by linarith⟩⟩
  obtain ⟨y, hyN, hyim⟩ := mem_closure_iff.1 hcl _ hNopen hqN
  obtain ⟨t, htD, rfl⟩ := hyim
  obtain ⟨γ₁, α₁, β₁, hα₁, hβ₁, hc₁, ht₁β, hg₁, hv₁⟩ := reach_globalCurve I htD
  have hmemB : γ₁ t ∈ B.source := by rw [hv₁]; exact hyN.1
  obtain ⟨B', u, hB', hB't, habs, hcent, hcurve', heq', -⟩ :=
    IsUnitSpeedCurveOn.exists_shift' ordConnected_Ioo hc₁ ht₁β hB hBt hmemB
  have habs' : |t - u| < ε := by
    rw [habs, hv₁, abs_lt]
    exact ⟨by linarith [hyN.2.1], by linarith [hyN.2.2]⟩
  rw [abs_lt] at habs'
  have htu : t ∈ Ioo (u - ε) (u + ε) := ⟨by linarith [habs'.2], by linarith [habs'.1]⟩
  have h2₁ : IsUnitSpeedCurveOn L
      (fun s => if s ∈ Ioo α₁ β₁ then γ₁ s else B'.invFun (s - u)) (Ioo α₁ β₁) :=
    hc₁.congr fun s hs => if_pos hs
  have h2₂ : IsUnitSpeedCurveOn L
      (fun s => if s ∈ Ioo α₁ β₁ then γ₁ s else B'.invFun (s - u)) (Ioo (u - ε) (u + ε)) := by
    refine hcurve'.congr fun s hs => ?_
    by_cases hmem : s ∈ Ioo α₁ β₁
    · rw [if_pos hmem]; exact heq' ⟨hmem, hs⟩
    · rw [if_neg hmem]
  have hunion := h2₁.union h2₂
  rw [Ioo_union_Ioo_of_mem ht₁β htu] at hunion
  have hgerm : (fun s => if s ∈ Ioo α₁ β₁ then γ₁ s else B'.invFun (s - u)) =ᶠ[𝓝 (0 : ℝ)]
      A₀.invFun := by
    refine Filter.EventuallyEq.trans ?_ hg₁
    filter_upwards [Ioo_mem_nhds hα₁ hβ₁] with s hs using if_pos hs
  obtain ⟨hsub, heqg⟩ := subset_dom_and_eqOn (A₀ := A₀) I
    (lt_of_le_of_lt (min_le_left α₁ (u - ε)) hα₁)
    (lt_of_lt_of_le hβ₁ (le_max_left β₁ (u + ε))) hunion hgerm
  have humem : u ∈ Ioo (min α₁ (u - ε)) (max β₁ (u + ε)) :=
    ⟨lt_of_le_of_lt (min_le_right α₁ (u - ε)) (by linarith),
      lt_of_lt_of_le (by linarith) (le_max_right β₁ (u + ε))⟩
  refine ⟨u, hsub humem, ?_⟩
  rw [← heqg humem]
  show (if u ∈ Ioo α₁ β₁ then γ₁ u else B'.invFun (u - u)) = q
  by_cases hmem : u ∈ Ioo α₁ β₁
  · rw [if_pos hmem, heq' ⟨hmem, ⟨by linarith, by linarith⟩⟩]
    show B'.invFun (u - u) = q
    rw [show u - u = (0 : ℝ) from by ring, hcent, hBinv]
  · rw [if_neg hmem, show u - u = (0 : ℝ) from by ring, hcent, hBinv]

end Maximal

/-! ## The boundaryless case: parametrization by an open interval -/

section Boundaryless

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

include hE

omit hE [T2Space M] [IsManifold I ∞ M] in
/-- **The inverse coordinate of an injective, onto unit-speed curve is a global `C^∞` coordinate.**

If a unit-speed curve `γ` on an interval `U` of times is injective and onto, the inverse map `θ : M
→ ℝ` is well defined with values in `U`, and it is `C^∞`: near the point `γ t` the curve is the
parametrization of a smooth arc `A` shifted by `k`, so on the open image of an interval of
parameters the coordinate `θ` *is* `A.toFun · + k`, which is `C^∞` because the coordinate of a
smooth arc is. -/
theorem exists_inverse_coord {L : LengthElement I ∞ M} {γ : ℝ → M} {U : Set ℝ}
    (hcurve : IsUnitSpeedCurveOn L γ U) (hinj : InjOn γ U) (hsurj : γ '' U = univ) :
    ∃ θ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ θ ∧ (∀ x, θ x ∈ U) ∧ (∀ x, γ (θ x) = x) ∧
      ∀ t ∈ U, θ (γ t) = t := by
  classical
  have hex : ∀ x : M, ∃ t, t ∈ U ∧ γ t = x := by
    intro x
    have hx : x ∈ γ '' U := by rw [hsurj]; exact mem_univ x
    obtain ⟨t, ht, hxt⟩ := hx
    exact ⟨t, ht, hxt⟩
  refine ⟨fun x => (hex x).choose, ?_, fun x => (hex x).choose_spec.1,
    fun x => (hex x).choose_spec.2, fun t ht => ?_⟩
  swap
  · exact hinj (hex (γ t)).choose_spec.1 ht (hex (γ t)).choose_spec.2
  set θ : M → ℝ := fun x => (hex x).choose with hθdef
  have hθU : ∀ x, θ x ∈ U := fun x => (hex x).choose_spec.1
  have hθγ : ∀ x, γ (θ x) = x := fun x => (hex x).choose_spec.2
  have hγθ : ∀ t ∈ U, θ (γ t) = t := fun t ht => hinj (hθU _) ht (hθγ _)
  have key : ∀ t ∈ U, ContMDiffAt I 𝓘(ℝ, ℝ) ∞ θ (γ t) := by
    intro t ht
    obtain ⟨A, k, η, -, hη, hIoo, hdesc⟩ := hcurve t ht
    have htmem : t ∈ Ioo (t - η) (t + η) := ⟨by linarith, by linarith⟩
    have hW : IsOpen (A.invFun '' (Ioo (t - η - k) (t + η - k) ∩ A.target)) :=
      A.isOpen_image isOpen_Ioo
    have hxW : γ t ∈ A.invFun '' (Ioo (t - η - k) (t + η - k) ∩ A.target) :=
      ⟨t - k, ⟨⟨by linarith, by linarith⟩, (hdesc t htmem).1⟩, ((hdesc t htmem).2).symm⟩
    have hsub : A.invFun '' (Ioo (t - η - k) (t + η - k) ∩ A.target) ⊆ A.source := by
      rintro y ⟨v, ⟨-, hvT⟩, rfl⟩
      exact A.map_target hvT
    have heq : ∀ y ∈ A.invFun '' (Ioo (t - η - k) (t + η - k) ∩ A.target),
        θ y = A.toFun y + k := by
      rintro y ⟨v, ⟨hvV, hvT⟩, rfl⟩
      have hmem : v + k ∈ Ioo (t - η) (t + η) := ⟨by linarith [hvV.1], by linarith [hvV.2]⟩
      have hy : γ (v + k) = A.invFun v := by
        rw [(hdesc _ hmem).2]
        congr 1
        ring
      have h1 : θ (A.invFun v) = v + k := by rw [← hy]; exact hγθ _ (hIoo hmem)
      rw [h1, A.right_inv hvT]
    have hsm : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (fun y => A.toFun y + k) (γ t) :=
      (A.contMDiffOn_toFun.contMDiffAt (A.open_source.mem_nhds (hsub hxW))).add contMDiffAt_const
    refine hsm.congr_of_eventuallyEq ?_
    filter_upwards [hW.mem_nhds hxW] with y hy using heq y hy
  intro x
  have h := key (θ x) (hθU x)
  rwa [hθγ x] at h

variable [SigmaCompactSpace M] [PreconnectedSpace M] [Nonempty M]

/-- **A connected, σ-compact, boundaryless smooth one-manifold which is not compact is parametrized
by an open interval of the line.**

There are a length element `L`, an open interval `U` of times and a map `γ : ℝ → M` which is a
unit-speed curve on `U` -- near every time the arc-length parametrization of a unit-speed smooth arc
-- and which is **injective on `U`** and **onto `M`**.

The three ingredients.  *Existence*: the maximal unit-speed curve `globalCurve` issuing from a
unit-speed arc centred at an arbitrary point, whose set `Dom` of reached times is an open interval
containing `0`; without compactness it need not be the whole line, and that is why the honest
statement is a parametrization by an open interval.  *Surjectivity*: the image is open because the
curve is locally the parametrization of an arc, and closed by `mem_image_dom_of_mem_closure` -- here
`I.boundary M = ∅` is what makes every point of the closure eligible -- so it is a nonempty clopen
subset of a preconnected space.  *Injectivity*: a repeated value would, by `eqOn_add_of_eq`, make
the curve periodic, and then `isCompact_isOpen_image_Icc_of_eq` exhibits a nonempty compact open
subset, which in a preconnected space is everything -- so `M` would be compact.

**This is where non-compactness is used, and it is used only here.** -/
theorem exists_parametrisation_of_boundary_eq_empty (hb : I.boundary M = ∅)
    (hnc : ¬ CompactSpace M) :
    ∃ (L : LengthElement I ∞ M) (γ : ℝ → M) (U : Set ℝ), IsOpen U ∧ U.OrdConnected ∧
      U.Nonempty ∧ IsUnitSpeedCurveOn L γ U ∧ InjOn γ U ∧ γ '' U = univ := by
  obtain ⟨L⟩ := nonempty_lengthElement I hE M
  obtain ⟨A₀, ε₀, hε₀, hA₀, -, -, hA₀t⟩ :=
    exists_unitSpeed_centred I hE hb L (Classical.arbitrary M)
  obtain ⟨h0, -⟩ := zero_mem_dom' I hε₀ hA₀ hA₀t
  have hcurve : IsUnitSpeedCurveOn L (globalCurve I L A₀) (Dom I L A₀) :=
    isUnitSpeedCurveOn_globalCurve I
  have hUoc : (Dom I L A₀).OrdConnected := ordConnected_dom I
  -- the image is closed, because no point of the closure is a boundary point
  have hclosed : IsClosed (globalCurve I L A₀ '' Dom I L A₀) := by
    rw [← closure_eq_iff_isClosed]
    refine Subset.antisymm (fun q hq => mem_image_dom_of_mem_closure I hE ?_ hq) subset_closure
    rw [hb]
    exact Set.notMem_empty q
  have hsurj : globalCurve I L A₀ '' Dom I L A₀ = univ := by
    rcases isClopen_iff.1 ⟨hclosed, hcurve.isOpen_image⟩ with hemp | huniv
    · exact absurd hemp
        (Set.nonempty_iff_ne_empty.1 ⟨globalCurve I L A₀ 0, 0, h0, rfl⟩)
    · exact huniv
  -- injectivity, from non-compactness
  have hinj : InjOn (globalCurve I L A₀) (Dom I L A₀) := by
    have hkey : ∀ s ∈ Dom I L A₀, ∀ t ∈ Dom I L A₀, s < t →
        globalCurve I L A₀ s = globalCurve I L A₀ t → False := by
      intro s hs t ht hlt heq
      obtain ⟨hcomp, hopen, -⟩ :=
        isCompact_isOpen_image_Icc_of_eq I hE hUoc hcurve hs ht hlt heq
      have hne' : (globalCurve I L A₀ '' Icc s t).Nonempty :=
        ⟨globalCurve I L A₀ s, s, ⟨le_rfl, hlt.le⟩, rfl⟩
      rcases isClopen_iff.1 ⟨hcomp.isClosed, hopen⟩ with hemp | huniv
      · exact absurd hemp (Set.nonempty_iff_ne_empty.1 hne')
      · exact hnc (isCompact_univ_iff.1 (by rw [← huniv]; exact hcomp))
    intro s hs t ht hst
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hkey s hs t ht hlt hst
    · exact hkey t ht s hs hlt hst.symm
  exact ⟨L, globalCurve I L A₀, Dom I L A₀, isOpen_dom I, hUoc, ⟨0, h0⟩, hcurve, hinj, hsurj⟩

/-- **Milnor's Appendix, the fourth and last case (book p. 54): a connected, σ-compact smooth
one-manifold without boundary which is not compact is diffeomorphic to the line.**

Precisely: let `E` be a real normed space with `Module.finrank ℝ E = 1`, let `I : ModelWithCorners ℝ
E H`, and let `M` be a nonempty, Hausdorff, σ-compact, preconnected `C^∞` manifold charted on `H`
with `I.boundary M = ∅` and `¬ CompactSpace M`.  Then `M` is `C^∞`-diffeomorphic to `ℝ` with the
trivial model `𝓘(ℝ, ℝ)`.

The diffeomorphism is exhibited as `x ↦ γ (f x)`, where `γ` parametrizes `M` bijectively by an open
interval `U` of times (`exists_parametrisation_of_boundary_eq_empty`) and `f : ℝ → U` is one of the
four explicit elementary diffeomorphisms of `exists_param_of_isOpen_ordConnected`.  Its inverse is
`g ∘ θ` with `θ` the global arc-length coordinate (`exists_inverse_coord`); no inverse function
theorem is used, both halves being written down. -/
theorem nonempty_diffeomorphReal (hb : I.boundary M = ∅) (hnc : ¬ CompactSpace M) :
    Nonempty (Diffeomorph 𝓘(ℝ, ℝ) I ℝ M ∞) := by
  obtain ⟨L, γ, U, hUopen, hUoc, hUne, hcurve, hinj, hsurj⟩ :=
    exists_parametrisation_of_boundary_eq_empty I hE hb hnc
  obtain ⟨θ, hθsm, hθU, hθγ, hγθ⟩ := exists_inverse_coord I hcurve hinj hsurj
  obtain ⟨f, g, hf, hg, hfU, hgf, hfg⟩ := exists_param_of_isOpen_ordConnected hUopen hUoc hUne
  have h1 : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x : ℝ => γ (f x)) :=
    hcurve.contMDiffOn.comp_contMDiff hf.contMDiff hfU
  have h2 : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => g (θ y)) :=
    (contMDiffOn_iff_contDiffOn.2 hg).comp_contMDiff hθsm hθU
  exact ⟨⟨{ toFun := fun x => γ (f x)
            invFun := fun y => g (θ y)
            left_inv := fun x => by
              show g (θ (γ (f x))) = x
              rw [hγθ _ (hfU x), hgf x]
            right_inv := fun y => by
              show γ (f (g (θ y))) = y
              rw [hfg _ (hθU y), hθγ y] }, h1, h2⟩⟩

/-- **The boundaryless non-compact case, in the direction `M → ℝ`.**  Same hypotheses as
`nonempty_diffeomorphReal`. -/
theorem nonempty_diffeomorphReal' (hb : I.boundary M = ∅) (hnc : ¬ CompactSpace M) :
    Nonempty (Diffeomorph I 𝓘(ℝ, ℝ) M ℝ ∞) :=
  (nonempty_diffeomorphReal I hE hb hnc).map Diffeomorph.symm

end Boundaryless

/-! ## The closed half-line as a smooth manifold with boundary -/

section HalfLineModel

/-- **The single chart of the closed half-line `Ici (0 : ℝ)`**: the homeomorphism onto Mathlib's
model half-space `EuclideanHalfSpace 1`, sending `u` to the one-entry vector `(u)`.  Because it is
onto the *whole* model space, the half-line is a one-chart manifold with boundary and every
computation with it reduces to the real coordinate. -/
def iciHomeomorph : Ici (0 : ℝ) ≃ₜ EuclideanHalfSpace 1 where
  toFun u := ⟨WithLp.toLp 2 fun _ => (u : ℝ), u.2⟩
  invFun z := ⟨WithLp.ofLp z.val 0, z.2⟩
  left_inv u := by ext; simp
  right_inv z := by
    ext i
    rw [Subsingleton.elim i 0]
  continuous_toFun := Continuous.subtype_mk
    ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_subtype_val)) _
  continuous_invFun :=
    Continuous.subtype_mk ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val) _

/-- The half-line `Ici (0 : ℝ)` is a charted space over the model half-space, with one chart. -/
instance instIciChartedSpace : ChartedSpace (EuclideanHalfSpace 1) (Ici (0 : ℝ)) :=
  iciHomeomorph.isOpenEmbedding.singletonChartedSpace

/-- The half-line `Ici (0 : ℝ)` is a `C^n` manifold with boundary, modelled on `𝓡∂ 1`. -/
instance instIciIsManifold (n : WithTop ℕ∞) : IsManifold (𝓡∂ 1) n (Ici (0 : ℝ)) :=
  iciHomeomorph.isOpenEmbedding.isManifold_singleton

section

variable {n : WithTop ℕ∞}

/-- The single chart of the half-line is `C^n`. -/
theorem contMDiff_iciHomeomorph : ContMDiff (𝓡∂ 1) (𝓡∂ 1) n (iciHomeomorph : Ici (0:ℝ) → _) :=
  contMDiff_isOpenEmbedding iciHomeomorph.isOpenEmbedding

/-- The inverse of the single chart of the half-line is `C^n`. -/
theorem contMDiff_iciHomeomorph_symm :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) n (iciHomeomorph.symm : EuclideanHalfSpace 1 → Ici (0:ℝ)) := by
  have h := contMDiffOn_isOpenEmbedding_symm (I := (𝓡∂ 1)) (n := n)
    iciHomeomorph.isOpenEmbedding
  rw [← contMDiffOn_univ]
  refine ContMDiffOn.congr (h.mono ?_) ?_
  · intro z _
    exact ⟨iciHomeomorph.symm z, iciHomeomorph.apply_symm_apply z⟩
  · intro z _
    have hz := IsOpenEmbedding.toOpenPartialHomeomorph_left_inv
      (f := (iciHomeomorph : Ici (0:ℝ) → EuclideanHalfSpace 1))
      iciHomeomorph.isOpenEmbedding (x := iciHomeomorph.symm z)
    rw [iciHomeomorph.apply_symm_apply z] at hz
    exact hz.symm

/-- The real coordinate of the model half-space is `C^n`. -/
theorem contMDiff_halfSpaceCoord : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) n
    (fun z : EuclideanHalfSpace 1 => WithLp.ofLp z.val 0) := by
  have h1 : ContDiff ℝ n (fun v : EuclideanSpace ℝ (Fin 1) => WithLp.ofLp v 0) := by fun_prop
  exact h1.contMDiff.comp (ModelWithCorners.contMDiff (𝓡∂ 1))

/-- **The inclusion of the half-line into the line is `C^n`** as a map of manifolds: a map out of
`Ici (0 : ℝ)` is smooth exactly when its real expression is, and this is the identity case. -/
theorem contMDiff_subtypeVal_Ici :
    ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) n (fun u : Ici (0 : ℝ) => (u : ℝ)) :=
  contMDiff_halfSpaceCoord.comp contMDiff_iciHomeomorph

/-- **The projection of the line onto the half-line**, `w ↦ max w 0`. -/
def iciProj (w : ℝ) : Ici (0 : ℝ) := ⟨max w 0, le_max_right w 0⟩

@[simp] theorem coe_iciProj (w : ℝ) : (iciProj w : ℝ) = max w 0 := rfl

/-- **The projection of the line onto the half-line is `C^n` on the half-line**, as a map of
manifolds.  Composed with a smooth real-valued function with nonnegative values, this is how a map
*into* `Ici (0 : ℝ)` is shown to be smooth. -/
theorem contMDiffOn_iciProj : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) n iciProj (Ici 0) := by
  have h1 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) n
      (fun w : ℝ => (WithLp.toLp 2 fun _ => w : EuclideanSpace ℝ (Fin 1))) (Ici 0) := by
    have h : ContDiff ℝ n
        (fun w : ℝ => (WithLp.toLp 2 fun _ => w : EuclideanSpace ℝ (Fin 1))) := by fun_prop
    exact h.contMDiff.contMDiffOn
  have hmaps : MapsTo (fun w : ℝ => (WithLp.toLp 2 fun _ => w : EuclideanSpace ℝ (Fin 1))) (Ici 0)
      (range (𝓡∂ 1)) := by
    intro w hw
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact hw
  have h2 := (ModelWithCorners.contMDiffOn_symm (𝓡∂ 1) (n := n)).comp h1 hmaps
  refine (contMDiff_iciHomeomorph_symm.comp_contMDiffOn h2).congr fun w hw => ?_
  show iciHomeomorph.symm ((𝓡∂ 1).symm (WithLp.toLp 2 fun _ => w)) = iciProj w
  ext
  simp [iciProj, iciHomeomorph, modelWithCornersEuclideanHalfSpace_symm_apply,
    Function.update_self]

end

end HalfLineModel

/-! ## The case with a boundary point: the ray issuing from it -/

section BoundarySetup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {L : LengthElement I ∞ M} {A₀ A₁ : SmoothArc I ∞ M} {ε₀ ε₁ : ℝ} {p : M}

/-- **The recentred arc reaches a full symmetric interval of times.**

Here `A₁` is the arc `A₀` -- issuing from the boundary point and with half-open target `Ico 0 ε₀` --
restricted to `Ioo 0 (2 ε₁)` and shifted by `ε₁`, so that its target is the symmetric open interval
`Ioo (-ε₁) ε₁` and its parametrization is `s ↦ A₀.invFun (s + ε₁)`.  Being centred with open target,
`A₁` is the kind of arc the unit-speed-curve machinery accepts, and the maximal curve issuing from
it reaches every time of `Ioo (-ε₁) ε₁`, where it is that parametrization. -/
theorem subset_dom_halfline (hε₁ : 0 < ε₁) (hA₁t : A₁.target = Ioo (-ε₁) ε₁)
    (hA₁ : UnitSpeed L A₁) :
    Ioo (-ε₁) ε₁ ⊆ Dom I L A₁ ∧ EqOn A₁.invFun (globalCurve I L A₁) (Ioo (-ε₁) ε₁) := by
  have hcurve : IsUnitSpeedCurveOn L A₁.invFun (Ioo (-ε₁) ε₁) := by
    have h := isUnitSpeedCurveOn_arc' (A := A₁) (by rw [hA₁t]; exact isOpen_Ioo) hA₁ 0
    rw [shift_eq_Ioo hA₁t 0] at h
    simpa using h
  exact subset_dom_and_eqOn I (show -ε₁ < 0 by linarith) hε₁ hcurve EventuallyEq.rfl

/-- **The maximal curve tends to the boundary point as the time tends to the left end of its
interval.**  Near that end the curve is `s ↦ A₀.invFun (s + ε₁)`, and `A₀.invFun` is continuous on
its half-open target `Ico 0 ε₀` -- one-sidedly at the endpoint `0`, where its value is the boundary
point `p`. -/
theorem tendsto_left_halfline (hε₁ : 0 < ε₁) (hε : 2 * ε₁ ≤ ε₀) (hpmem : p ∈ A₀.source)
    (hp0 : A₀.toFun p = 0) (hA₀t : A₀.target = Ico 0 ε₀) (hA₁t : A₁.target = Ioo (-ε₁) ε₁)
    (hA₁ : UnitSpeed L A₁) (hA₁inv : ∀ s, A₁.invFun s = A₀.invFun (s + ε₁)) :
    Tendsto (globalCurve I L A₁) (𝓝[>] (-ε₁)) (𝓝 p) := by
  obtain ⟨-, heq⟩ := subset_dom_halfline I hε₁ hA₁t hA₁
  have hpinv : A₀.invFun 0 = p := by rw [← hp0, A₀.left_inv hpmem]
  have h1 : Tendsto A₀.invFun (𝓝[A₀.target] 0) (𝓝 p) := by
    have h := A₀.continuousOn_invFun 0 (by rw [hA₀t]; exact ⟨le_rfl, by linarith⟩)
    rw [← hpinv]
    exact h
  have hmemIio : Iio ε₁ ∈ 𝓝[>] (-ε₁) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith))
  have h2 : Tendsto (fun s : ℝ => s + ε₁) (𝓝[>] (-ε₁)) (𝓝[A₀.target] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun s : ℝ => s + ε₁) := by fun_prop
      have hc : Tendsto (fun s : ℝ => s + ε₁) (𝓝 (-ε₁)) (𝓝 0) := by
        simpa using hcont.tendsto (-ε₁)
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, hmemIio] with s hs1 hs2
      have h1 : -ε₁ < s := hs1
      have h2 : s < ε₁ := hs2
      rw [hA₀t]
      exact ⟨by linarith, by linarith⟩
  refine (h1.comp h2).congr' ?_
  filter_upwards [self_mem_nhdsWithin, hmemIio] with s hs1 hs2
  have h1 : -ε₁ < s := hs1
  have h2 : s < ε₁ := hs2
  show A₀.invFun (s + ε₁) = globalCurve I L A₁ s
  rw [← hA₁inv s]
  exact heq ⟨h1, h2⟩

/-- **The left end of the interval of reached times is not itself reached.**  If it were, the
curve's value there would be the boundary point `p` -- by the limit above and uniqueness of limits
in a Hausdorff space -- and no value of a unit-speed curve is a boundary point. -/
theorem left_notMem_dom (hε₁ : 0 < ε₁) (hε : 2 * ε₁ ≤ ε₀) (hpmem : p ∈ A₀.source)
    (hp0 : A₀.toFun p = 0) (hA₀t : A₀.target = Ico 0 ε₀) (hpb : p ∈ I.boundary M)
    (hA₁t : A₁.target = Ioo (-ε₁) ε₁) (hA₁ : UnitSpeed L A₁)
    (hA₁inv : ∀ s, A₁.invFun s = A₀.invFun (s + ε₁)) : -ε₁ ∉ Dom I L A₁ := by
  intro hmem
  have hcurve : IsUnitSpeedCurveOn L (globalCurve I L A₁) (Dom I L A₁) :=
    isUnitSpeedCurveOn_globalCurve I
  have h1 := tendsto_left_halfline I hε₁ hε hpmem hp0 hA₀t hA₁t hA₁ hA₁inv
  have h2 : Tendsto (globalCurve I L A₁) (𝓝[>] (-ε₁)) (𝓝 (globalCurve I L A₁ (-ε₁))) :=
    (hcurve.continuousAt hmem).mono_left nhdsWithin_le_nhds
  have heq := tendsto_nhds_unique h1 h2
  exact hcurve.notMem_boundary hmem (by rw [← heq]; exact hpb)

/-- **The interval of reached times lies to the right of `-ε₁`.**  It is an interval containing `0`
and missing `-ε₁`, so it cannot reach below `-ε₁` either. -/
theorem dom_subset_Ioi (hε₁ : 0 < ε₁) (hε : 2 * ε₁ ≤ ε₀) (hpmem : p ∈ A₀.source)
    (hp0 : A₀.toFun p = 0) (hA₀t : A₀.target = Ico 0 ε₀) (hpb : p ∈ I.boundary M)
    (hA₁t : A₁.target = Ioo (-ε₁) ε₁) (hA₁ : UnitSpeed L A₁)
    (hA₁inv : ∀ s, A₁.invFun s = A₀.invFun (s + ε₁)) : Dom I L A₁ ⊆ Ioi (-ε₁) := by
  intro s hs
  rw [mem_Ioi]
  by_contra hcon
  push Not at hcon
  obtain ⟨hsub, -⟩ := subset_dom_halfline I hε₁ hA₁t hA₁
  have h0 : (0 : ℝ) ∈ Dom I L A₁ := hsub ⟨by linarith, hε₁⟩
  exact left_notMem_dom I hε₁ hε hpmem hp0 hA₀t hpb hA₁t hA₁ hA₁inv
    ((ordConnected_dom I).out hs h0 ⟨hcon, by linarith⟩)

variable (hE : Module.finrank ℝ E = 1) [IsManifold I ∞ M]

include hE in
/-- **The maximal curve issuing from a boundary point is injective**, on a preconnected manifold and
*without* any compactness hypothesis.  A repeated value would, by
`isCompact_isOpen_image_Icc_of_eq`, make the image of a compact interval of times a nonempty clopen
subset, hence everything -- so the boundary point `p` would be a value of the curve, and no value of
a unit-speed curve is a boundary point. -/
theorem injOn_dom_halfline [PreconnectedSpace M] (hpb : p ∈ I.boundary M) :
    InjOn (globalCurve I L A₁) (Dom I L A₁) := by
  have hcurve : IsUnitSpeedCurveOn L (globalCurve I L A₁) (Dom I L A₁) :=
    isUnitSpeedCurveOn_globalCurve I
  have hkey : ∀ s ∈ Dom I L A₁, ∀ t ∈ Dom I L A₁, s < t →
      globalCurve I L A₁ s = globalCurve I L A₁ t → False := by
    intro s hs t ht hlt heq
    obtain ⟨hcomp, hopen, hsubim⟩ :=
      isCompact_isOpen_image_Icc_of_eq I hE (ordConnected_dom I) hcurve hs ht hlt heq
    have hne' : (globalCurve I L A₁ '' Icc s t).Nonempty :=
      ⟨globalCurve I L A₁ s, s, ⟨le_rfl, hlt.le⟩, rfl⟩
    rcases isClopen_iff.1 ⟨hcomp.isClosed, hopen⟩ with hemp | huniv
    · exact absurd hemp (Set.nonempty_iff_ne_empty.1 hne')
    · obtain ⟨u, hu, hpu⟩ : p ∈ globalCurve I L A₁ '' Dom I L A₁ := by
        refine hsubim ?_
        rw [huniv]
        exact mem_univ p
      exact hcurve.notMem_boundary hu (by rw [hpu]; exact hpb)
  intro s hs t ht hst
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hkey s hs t ht hlt hst
  · exact hkey t ht s hs hlt hst.symm

end BoundarySetup

/-! ## Gluing an arc description onto the maximal curve -/

section Glue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {L : LengthElement I ∞ M}

/-- **Maximality of the curve, in the form used twice below.**  Suppose that at a reached time `t`
the maximal curve is described, on the intersection of its own interval of times with `Ioo (t - r)
(t + r)`, by a shifted arc parametrization which is itself a unit-speed curve on the whole of `Ioo
(t - r) (t + r)`.  Then that whole interval consists of reached times, and the description holds
throughout it.

The proof is the gluing of Stage 7's `not_bddAbove_dom`, isolated: a witnessing curve with the right
germ at `0` is spliced with the arc description, the splice is a unit-speed curve on the union of
the two intervals with the same germ, and `subset_dom_and_eqOn` -- the maximality of `Dom` -- does
the rest.  Nothing here is compact, and the manifold may have boundary. -/
theorem dom_glue {A₀ : SmoothArc I ∞ M} {t : ℝ} (htD : t ∈ Dom I L A₀)
    {B : SmoothArc I ∞ M} {r : ℝ} (hr : 0 < r)
    (hcurveB : IsUnitSpeedCurveOn L (fun s => B.invFun (s - t)) (Ioo (t - r) (t + r)))
    (heqB : EqOn (globalCurve I L A₀) (fun s => B.invFun (s - t))
      (Dom I L A₀ ∩ Ioo (t - r) (t + r))) :
    Ioo (t - r) (t + r) ⊆ Dom I L A₀ ∧
      ∀ s ∈ Ioo (t - r) (t + r), globalCurve I L A₀ s = B.invFun (s - t) := by
  obtain ⟨γ₁, α₁, β₁, hα₁, hβ₁, hc₁, htβ, hg₁, hv₁⟩ := reach_globalCurve I htD
  obtain ⟨hsub₁, heq₁⟩ := subset_dom_and_eqOn (A₀ := A₀) I hα₁ hβ₁ hc₁ hg₁
  have htr : t ∈ Ioo (t - r) (t + r) := ⟨by linarith, by linarith⟩
  have h2₁ : IsUnitSpeedCurveOn L (fun s => if s ∈ Ioo α₁ β₁ then γ₁ s else B.invFun (s - t))
      (Ioo α₁ β₁) := hc₁.congr fun s hs => if_pos hs
  have h2₂ : IsUnitSpeedCurveOn L (fun s => if s ∈ Ioo α₁ β₁ then γ₁ s else B.invFun (s - t))
      (Ioo (t - r) (t + r)) := by
    refine hcurveB.congr fun s hs => ?_
    by_cases hmem : s ∈ Ioo α₁ β₁
    · rw [if_pos hmem, heq₁ hmem]
      exact heqB ⟨hsub₁ hmem, hs⟩
    · rw [if_neg hmem]
  have hunion := h2₁.union h2₂
  rw [Ioo_union_Ioo_of_mem htβ htr] at hunion
  have hgerm : (fun s => if s ∈ Ioo α₁ β₁ then γ₁ s else B.invFun (s - t)) =ᶠ[𝓝 (0 : ℝ)]
      A₀.invFun := by
    refine Filter.EventuallyEq.trans ?_ hg₁
    filter_upwards [Ioo_mem_nhds hα₁ hβ₁] with s hs using if_pos hs
  obtain ⟨hsub, heqg⟩ := subset_dom_and_eqOn (A₀ := A₀) I
    (lt_of_le_of_lt (min_le_left α₁ (t - r)) hα₁)
    (lt_of_lt_of_le hβ₁ (le_max_left β₁ (t + r))) hunion hgerm
  have hsub' : Ioo (t - r) (t + r) ⊆ Ioo (min α₁ (t - r)) (max β₁ (t + r)) :=
    Ioo_subset_Ioo (min_le_right _ _) (le_max_right _ _)
  refine ⟨fun s hs => hsub (hsub' hs), fun s hs => ?_⟩
  rw [← heqg (hsub' hs)]
  show (if s ∈ Ioo α₁ β₁ then γ₁ s else B.invFun (s - t)) = B.invFun (s - t)
  by_cases hmem : s ∈ Ioo α₁ β₁
  · rw [if_pos hmem, heq₁ hmem]
    exact heqB ⟨hsub₁ hmem, hs⟩
  · rw [if_neg hmem]

end Glue

/-! ## The case with a boundary point: the ray is onto -/

section BoundarySurj

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] [PreconnectedSpace M]
  {L : LengthElement I ∞ M} {A₀ A₁ : SmoothArc I ∞ M} {ε₀ ε₁ : ℝ} {p : M}

include hE

/-- **The ray issuing from a boundary point covers the manifold.**

With `A₀` a unit-speed arc from the boundary point `p` with target `Ico 0 ε₀`, and `A₁` its
recentred restriction, the maximal unit-speed curve from `A₁` together with the single point `p` is
all of `M`.

The set `R = {p} ∪ γ '' Dom` is *open*: near `p` it contains the part of `A₀.source` with coordinate
below `2 ε₁`, and elsewhere it is the image of a unit-speed curve.  It is *closed*, and this is the
whole content.  A point of the closure which is not a boundary point is in the image by
`mem_image_dom_of_mem_closure`.  A boundary point `q ≠ p` of the closure is analysed by taking a
unit-speed arc `C` from `q` with target `Ico 0 ε`: the curve meets `C.source` at a reached time `t`
with `C`-coordinate `cc ∈ (0, ε/4)`, and `SmoothArc.shrink` turns `C` into a centred arc of radius
`cc` about `γ t`, so `IsUnitSpeedCurveOn.exists_shift'` and `dom_glue` identify the curve with the
`C`-parametrization on the *whole* interval of times `Ioo (t - cc) (t + cc)`.  The extra conclusion
of `exists_shift'` -- that the arc is `C` or its reverse -- says which end of that interval
corresponds to the `C`-parameter `0`, i.e. to `q` itself; and that end is not a reached time, since
no value of a unit-speed curve is a boundary point.  Two cases:

* the end is the *left* end of the whole interval of reached times.  Then the curve tends to `q`
  there, and it also tends to `p` there (`tendsto_left_halfline`), so `q = p` -- excluded.
* the end is the *right* end.  Then `Dom = Ioo (-ε₁) (t + cc)` and `M` is covered by three compact
  pieces -- `A₀.invFun '' Icc 0 ε₁` around `p`, `γ '' Icc 0 (max 0 t)` in the middle and `C.invFun
  '' Icc 0 cc` around `q` -- so `M`, being also open and preconnected, is compact.  **This is the
  one place where non-compactness is used in the half-line case**: it excludes the second boundary
  point, i.e. the compact case `Icc 0 1` of Stage 6. -/
theorem insert_image_dom_eq_univ (hε₁ : 0 < ε₁) (hε : 2 * ε₁ ≤ ε₀) (hpmem : p ∈ A₀.source)
    (hp0 : A₀.toFun p = 0) (hA₀t : A₀.target = Ico 0 ε₀) (hpb : p ∈ I.boundary M)
    (hA₁t : A₁.target = Ioo (-ε₁) ε₁) (hA₁ : UnitSpeed L A₁)
    (hA₁inv : ∀ s, A₁.invFun s = A₀.invFun (s + ε₁)) (hnc : ¬ CompactSpace M) :
    insert p (globalCurve I L A₁ '' Dom I L A₁) = univ := by
  have hcurve : IsUnitSpeedCurveOn L (globalCurve I L A₁) (Dom I L A₁) :=
    isUnitSpeedCurveOn_globalCurve I
  have hDoc : (Dom I L A₁).OrdConnected := ordConnected_dom I
  obtain ⟨hsub0, heq0⟩ := subset_dom_halfline I hε₁ hA₁t hA₁
  have h0 : (0 : ℝ) ∈ Dom I L A₁ := hsub0 ⟨by linarith, hε₁⟩
  have hleft : -ε₁ ∉ Dom I L A₁ :=
    left_notMem_dom I hε₁ hε hpmem hp0 hA₀t hpb hA₁t hA₁ hA₁inv
  have hDIoi : Dom I L A₁ ⊆ Ioi (-ε₁) :=
    dom_subset_Ioi I hε₁ hε hpmem hp0 hA₀t hpb hA₁t hA₁ hA₁inv
  have hplim : Tendsto (globalCurve I L A₁) (𝓝[>] (-ε₁)) (𝓝 p) :=
    tendsto_left_halfline I hε₁ hε hpmem hp0 hA₀t hA₁t hA₁ hA₁inv
  have hpinv : A₀.invFun 0 = p := by rw [← hp0, A₀.left_inv hpmem]
  -- the curve covers the part of `A₀` with coordinate in `Ioo 0 (2 ε₁)`
  have hA₀cover : ∀ v ∈ Ioo (0 : ℝ) (2 * ε₁),
      A₀.invFun v ∈ globalCurve I L A₁ '' Dom I L A₁ := by
    intro v hv
    have hmem : v - ε₁ ∈ Ioo (-ε₁) ε₁ := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    refine ⟨v - ε₁, hsub0 hmem, ?_⟩
    rw [← heq0 hmem, hA₁inv]
    congr 1
    ring
  -- openness
  have hVopen : IsOpen (A₀.source ∩ A₀.toFun ⁻¹' Iio (2 * ε₁)) :=
    A₀.continuousOn_toFun.isOpen_inter_preimage A₀.open_source isOpen_Iio
  have hpV : p ∈ A₀.source ∩ A₀.toFun ⁻¹' Iio (2 * ε₁) :=
    ⟨hpmem, by rw [Set.mem_preimage, hp0]; exact show (0:ℝ) < 2 * ε₁ by linarith⟩
  have hVsub : A₀.source ∩ A₀.toFun ⁻¹' Iio (2 * ε₁) ⊆
      insert p (globalCurve I L A₁ '' Dom I L A₁) := by
    intro x hx
    have hv : A₀.toFun x ∈ Ico 0 ε₀ := by rw [← hA₀t]; exact A₀.map_source hx.1
    have hvlt : A₀.toFun x < 2 * ε₁ := hx.2
    have h1 : A₀.invFun (A₀.toFun x) = x := A₀.left_inv hx.1
    rcases eq_or_lt_of_le hv.1 with hz | hz
    · rw [← hz, hpinv] at h1
      exact mem_insert_iff.2 (Or.inl h1.symm)
    · have h2 := hA₀cover _ ⟨hz, hvlt⟩
      rw [h1] at h2
      exact mem_insert_iff.2 (Or.inr h2)
  have hRopen : IsOpen (insert p (globalCurve I L A₁ '' Dom I L A₁)) := by
    have heqR : insert p (globalCurve I L A₁ '' Dom I L A₁) =
        (A₀.source ∩ A₀.toFun ⁻¹' Iio (2 * ε₁)) ∪ globalCurve I L A₁ '' Dom I L A₁ := by
      refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
      · rcases hx with rfl | hx
        · exact Or.inl hpV
        · exact Or.inr hx
      · rcases hx with hx | hx
        · exact hVsub hx
        · exact mem_insert_iff.2 (Or.inr hx)
    rw [heqR]
    exact hVopen.union hcurve.isOpen_image
  -- closedness
  have hclins : closure (insert p (globalCurve I L A₁ '' Dom I L A₁)) =
      insert p (closure (globalCurve I L A₁ '' Dom I L A₁)) := by
    rw [Set.insert_eq, Set.insert_eq, closure_union, closure_singleton]
  have hRclosed : IsClosed (insert p (globalCurve I L A₁ '' Dom I L A₁)) := by
    rw [← closure_eq_iff_isClosed]
    refine Subset.antisymm (fun q hq => ?_) subset_closure
    rw [hclins] at hq
    rcases hq with rfl | hcl
    · exact mem_insert _ _
    by_cases hqb : q ∈ I.boundary M
    swap
    · exact mem_insert_iff.2 (Or.inr (mem_image_dom_of_mem_closure I hE hqb hcl))
    by_contra hqR
    -- a unit-speed arc issuing from the second boundary point
    obtain ⟨C, ε, hεpos, hqC, hqC0, hCt, hCu⟩ := exists_unitSpeed_of_mem_boundary I hE L hqb
    have hqinv : C.invFun 0 = q := by rw [← hqC0, C.left_inv hqC]
    have hNopen : IsOpen (C.source ∩ C.toFun ⁻¹' Iio (ε / 4)) :=
      C.continuousOn_toFun.isOpen_inter_preimage C.open_source isOpen_Iio
    have hqN : q ∈ C.source ∩ C.toFun ⁻¹' Iio (ε / 4) :=
      ⟨hqC, by rw [Set.mem_preimage, hqC0]; exact show (0:ℝ) < ε / 4 by linarith⟩
    obtain ⟨y, hyN, hyim⟩ := mem_closure_iff.1 hcl _ hNopen hqN
    obtain ⟨t, htD, rfl⟩ := hyim
    have htgt : -ε₁ < t := hDIoi htD
    have hccmem : C.toFun (globalCurve I L A₁ t) ∈ Ioo 0 ε := by
      have h2 : globalCurve I L A₁ t ∉ I.boundary M := hcurve.notMem_boundary htD
      have h3 : C.toFun (globalCurve I L A₁ t) ∈ interior C.target := by
        by_contra hcon
        exact h2 ((C.bdry _ hyN.1).2 hcon)
      rwa [hCt, interior_Ico] at h3
    have hcc4 : C.toFun (globalCurve I L A₁ t) < ε / 4 := hyN.2
    set cc := C.toFun (globalCurve I L A₁ t) with hccdef
    have hcc0 : 0 < cc := hccmem.1
    have h2ccpos : (0 : ℝ) < 2 * cc := by linarith
    have h2ccε : Ioo (0 : ℝ) (2 * cc) ⊆ C.target := by
      rw [hCt]
      intro v hv
      exact ⟨hv.1.le, by linarith [hv.2]⟩
    have hC't : (C.shrink h2ccpos h2ccε cc).target = Ioo (-cc) cc := by
      rw [SmoothArc.shrink_target, show (0 : ℝ) - cc = -cc from by ring,
        show 2 * cc - cc = cc from by ring]
    have hC'u : UnitSpeed L (C.shrink h2ccpos h2ccε cc) :=
      C.unitSpeed_shrink hCu h2ccpos h2ccε cc
    have hC'mem : globalCurve I L A₁ t ∈ (C.shrink h2ccpos h2ccε cc).source := by
      refine ⟨hyN.1, ?_⟩
      rw [Set.mem_preimage, ← hccdef]
      exact ⟨hcc0, by linarith⟩
    have hC'0 : (C.shrink h2ccpos h2ccε cc).toFun (globalCurve I L A₁ t) = 0 := by
      rw [SmoothArc.shrink_toFun, ← hccdef]
      ring
    obtain ⟨B', u, hB'u, hB't, habs, hcent, hcurveB, heqB, hor⟩ :=
      IsUnitSpeedCurveOn.exists_shift' hDoc hcurve htD hC'u hC't hC'mem
    have hut : u = t := by
      have h1 : |t - u| = 0 := by rw [habs, hC'0, abs_zero]
      have h2 := abs_eq_zero.1 h1
      linarith
    rw [hut] at hcurveB heqB
    obtain ⟨hsubIoo, hγB⟩ := dom_glue I htD hcc0 hcurveB heqB
    have hCq : Tendsto C.invFun (𝓝[C.target] 0) (𝓝 q) := by
      have h := C.continuousOn_invFun 0 (by rw [hCt]; exact ⟨le_rfl, hεpos⟩)
      rw [← hqinv]
      exact h
    rcases hor with hB'eq | hB'eq
    · -- the curve runs towards `q` as the time decreases: the left end
      have hval : ∀ s ∈ Ioo (t - cc) (t + cc),
          globalCurve I L A₁ s = C.invFun (s - t + cc) := by
        intro s hs
        rw [hγB s hs, hB'eq, SmoothArc.shrink_invFun]
      have hIiomem : Iio (t + cc) ∈ 𝓝[>] (t - cc) :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith))
      have hqlim : Tendsto (globalCurve I L A₁) (𝓝[>] (t - cc)) (𝓝 q) := by
        have hshift : Tendsto (fun s : ℝ => s - t + cc) (𝓝[>] (t - cc)) (𝓝[C.target] 0) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · have hcont : Continuous (fun s : ℝ => s - t + cc) := by fun_prop
            have h := (hcont.tendsto (t - cc)).mono_left
              (nhdsWithin_le_nhds (s := Ioi (t - cc)))
            simpa using h
          · filter_upwards [self_mem_nhdsWithin, hIiomem] with s hs1 hs2
            have h1 : t - cc < s := hs1
            have h2 : s < t + cc := hs2
            exact h2ccε ⟨by linarith, by linarith⟩
        refine (hCq.comp hshift).congr' ?_
        filter_upwards [self_mem_nhdsWithin, hIiomem] with s hs1 hs2
        have h1 : t - cc < s := hs1
        have h2 : s < t + cc := hs2
        exact (hval s ⟨h1, h2⟩).symm
      have hs₀ : t - cc ∉ Dom I L A₁ := by
        intro hmem
        have h2 : Tendsto (globalCurve I L A₁) (𝓝[>] (t - cc))
            (𝓝 (globalCurve I L A₁ (t - cc))) :=
          (hcurve.continuousAt hmem).mono_left nhdsWithin_le_nhds
        have heq := tendsto_nhds_unique hqlim h2
        exact hcurve.notMem_boundary hmem (by rw [← heq]; exact hqb)
      have hge : -ε₁ ≤ t - cc := by
        by_contra hcon
        push Not at hcon
        exact hleft (hsubIoo ⟨hcon, by linarith⟩)
      have hle : t - cc ≤ -ε₁ := by
        by_contra hcon
        push Not at hcon
        refine hs₀ ?_
        rcases le_or_gt (t - cc) 0 with h | h
        · exact hsub0 ⟨hcon, by linarith⟩
        · exact hDoc.out h0 htD ⟨h.le, by linarith⟩
      rw [le_antisymm hle hge] at hqlim
      exact hqR (mem_insert_iff.2 (Or.inl (tendsto_nhds_unique hqlim hplim)))
    · -- the curve runs towards `q` as the time increases: the right end, and `M` is compact
      have hval : ∀ s ∈ Ioo (t - cc) (t + cc),
          globalCurve I L A₁ s = C.invFun (-(s - t) + cc) := by
        intro s hs
        rw [hγB s hs, hB'eq, SmoothArc.neg_invFun, SmoothArc.shrink_invFun]
      have hIoimem : Ioi (t - cc) ∈ 𝓝[<] (t + cc) :=
        mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith))
      have hqlim : Tendsto (globalCurve I L A₁) (𝓝[<] (t + cc)) (𝓝 q) := by
        have hshift : Tendsto (fun s : ℝ => -(s - t) + cc) (𝓝[<] (t + cc))
            (𝓝[C.target] 0) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · have hcont : Continuous (fun s : ℝ => -(s - t) + cc) := by fun_prop
            have h := (hcont.tendsto (t + cc)).mono_left
              (nhdsWithin_le_nhds (s := Iio (t + cc)))
            simpa using h
          · filter_upwards [self_mem_nhdsWithin, hIoimem] with s hs1 hs2
            have h1 : s < t + cc := hs1
            have h2 : t - cc < s := hs2
            exact h2ccε ⟨by linarith, by linarith⟩
        refine (hCq.comp hshift).congr' ?_
        filter_upwards [self_mem_nhdsWithin, hIoimem] with s hs1 hs2
        have h1 : s < t + cc := hs1
        have h2 : t - cc < s := hs2
        exact (hval s ⟨h2, h1⟩).symm
      have hs₀ : t + cc ∉ Dom I L A₁ := by
        intro hmem
        have h2 : Tendsto (globalCurve I L A₁) (𝓝[<] (t + cc))
            (𝓝 (globalCurve I L A₁ (t + cc))) :=
          (hcurve.continuousAt hmem).mono_left nhdsWithin_le_nhds
        have heq := tendsto_nhds_unique hqlim h2
        exact hcurve.notMem_boundary hmem (by rw [← heq]; exact hqb)
      have hDeq : Dom I L A₁ = Ioo (-ε₁) (t + cc) := by
        refine Subset.antisymm (fun s hs => ⟨hDIoi hs, ?_⟩) (fun x hx => ?_)
        · by_contra hcon
          push Not at hcon
          exact hs₀ (hDoc.out (hsubIoo (show t + cc / 2 ∈ Ioo (t - cc) (t + cc) from
            ⟨by linarith, by linarith⟩)) hs ⟨by linarith, hcon⟩)
        · rcases lt_or_ge x ε₁ with h | h
          · exact hsub0 ⟨hx.1, h⟩
          · rcases lt_or_ge (t - cc) x with h' | h'
            · exact hsubIoo ⟨h', hx.2⟩
            · exact hDoc.out h0 htD ⟨by linarith, by linarith⟩
      -- three compact pieces
      have hIcc1 : Icc (0 : ℝ) ε₁ ⊆ A₀.target := by
        rw [hA₀t]
        intro v hv
        exact ⟨hv.1, by linarith [hv.2]⟩
      have hK1 : IsCompact (A₀.invFun '' Icc 0 ε₁) :=
        isCompact_Icc.image_of_continuousOn (A₀.continuousOn_invFun.mono hIcc1)
      have hmax0t : max 0 t ∈ Dom I L A₁ := by
        rcases le_total t 0 with h | h
        · rw [max_eq_left h]; exact h0
        · rw [max_eq_right h]; exact htD
      have hIcc2 : Icc (0 : ℝ) (max 0 t) ⊆ Dom I L A₁ := hDoc.out h0 hmax0t
      have hK2 : IsCompact (globalCurve I L A₁ '' Icc 0 (max 0 t)) :=
        isCompact_Icc.image_of_continuousOn fun s hs =>
          (hcurve.continuousAt (hIcc2 hs)).continuousWithinAt
      have hIcc3 : Icc (0 : ℝ) cc ⊆ C.target := by
        rw [hCt]
        intro v hv
        exact ⟨hv.1, by linarith [hv.2, hccmem.2]⟩
      have hK3 : IsCompact (C.invFun '' Icc 0 cc) :=
        isCompact_Icc.image_of_continuousOn (C.continuousOn_invFun.mono hIcc3)
      have hcover : insert q (insert p (globalCurve I L A₁ '' Dom I L A₁)) =
          A₀.invFun '' Icc 0 ε₁ ∪ globalCurve I L A₁ '' Icc 0 (max 0 t) ∪
            C.invFun '' Icc 0 cc := by
        refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
        · rcases hx with rfl | hx
          · exact Or.inr ⟨0, ⟨le_rfl, hcc0.le⟩, hqinv⟩
          rcases hx with rfl | hx
          · exact Or.inl (Or.inl ⟨0, ⟨le_rfl, hε₁.le⟩, hpinv⟩)
          obtain ⟨s, hs, rfl⟩ := hx
          rw [hDeq] at hs
          rcases le_or_gt s 0 with h | h
          · refine Or.inl (Or.inl ⟨s + ε₁, ⟨by linarith [hs.1], by linarith⟩, ?_⟩)
            rw [← hA₁inv, heq0 ⟨hs.1, by linarith⟩]
          · rcases le_or_gt s (max 0 t) with h' | h'
            · exact Or.inl (Or.inr ⟨s, ⟨h.le, h'⟩, rfl⟩)
            · have hst : t < s := lt_of_le_of_lt (le_max_right 0 t) h'
              refine Or.inr ⟨-(s - t) + cc, ⟨by linarith [hs.2], by linarith⟩, ?_⟩
              exact (hval s ⟨by linarith, hs.2⟩).symm
        · rcases hx with hx | hx
          · rcases hx with hx | hx
            · obtain ⟨v, hv, rfl⟩ := hx
              rcases eq_or_lt_of_le hv.1 with hz | hz
              · rw [← hz, hpinv]
                exact mem_insert_iff.2 (Or.inr (mem_insert _ _))
              · refine mem_insert_iff.2 (Or.inr (mem_insert_iff.2 (Or.inr ?_)))
                exact hA₀cover _ ⟨hz, by linarith [hv.2]⟩
            · obtain ⟨s, hs, rfl⟩ := hx
              exact mem_insert_iff.2 (Or.inr (mem_insert_iff.2 (Or.inr ⟨s, hIcc2 hs, rfl⟩)))
          · obtain ⟨v, hv, rfl⟩ := hx
            rcases eq_or_lt_of_le hv.1 with hz | hz
            · rw [← hz, hqinv]
              exact mem_insert _ _
            · refine mem_insert_iff.2 (Or.inr (mem_insert_iff.2 (Or.inr
                ⟨t + cc - v, hsubIoo ⟨by linarith [hv.2], by linarith⟩, ?_⟩)))
              rw [hval _ ⟨by linarith [hv.2], by linarith⟩]
              congr 1
              ring
      have hcpt : IsCompact (insert q (insert p (globalCurve I L A₁ '' Dom I L A₁))) := by
        rw [hcover]
        exact (hK1.union hK2).union hK3
      -- openness at `q`
      have hWopen : IsOpen (C.source ∩ C.toFun ⁻¹' Iio (2 * cc)) :=
        C.continuousOn_toFun.isOpen_inter_preimage C.open_source isOpen_Iio
      have hqW : q ∈ C.source ∩ C.toFun ⁻¹' Iio (2 * cc) :=
        ⟨hqC, by rw [Set.mem_preimage, hqC0]; exact show (0:ℝ) < 2 * cc by linarith⟩
      have hWsub : C.source ∩ C.toFun ⁻¹' Iio (2 * cc) ⊆
          insert q (insert p (globalCurve I L A₁ '' Dom I L A₁)) := by
        intro x hx
        have hv : C.toFun x ∈ Ico 0 ε := by rw [← hCt]; exact C.map_source hx.1
        have hvlt : C.toFun x < 2 * cc := hx.2
        have h1 : C.invFun (C.toFun x) = x := C.left_inv hx.1
        rcases eq_or_lt_of_le hv.1 with hz | hz
        · rw [← hz, hqinv] at h1
          exact mem_insert_iff.2 (Or.inl h1.symm)
        · refine mem_insert_iff.2 (Or.inr (mem_insert_iff.2 (Or.inr
            ⟨t + cc - C.toFun x, hsubIoo ⟨by linarith, by linarith⟩, ?_⟩)))
          rw [hval _ ⟨by linarith, by linarith⟩]
          rw [show -(t + cc - C.toFun x - t) + cc = C.toFun x from by ring]
          exact h1
      have hopen2 : IsOpen (insert q (insert p (globalCurve I L A₁ '' Dom I L A₁))) := by
        have heq2 : insert q (insert p (globalCurve I L A₁ '' Dom I L A₁)) =
            (C.source ∩ C.toFun ⁻¹' Iio (2 * cc)) ∪
              insert p (globalCurve I L A₁ '' Dom I L A₁) := by
          refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
          · rcases hx with rfl | hx
            · exact Or.inl hqW
            · exact Or.inr hx
          · rcases hx with hx | hx
            · exact hWsub hx
            · exact mem_insert_iff.2 (Or.inr hx)
        rw [heq2]
        exact hWopen.union hRopen
      rcases isClopen_iff.1 ⟨hcpt.isClosed, hopen2⟩ with hemp | huniv
      · exact absurd hemp (Set.nonempty_iff_ne_empty.1 ⟨q, mem_insert _ _⟩)
      · exact hnc (isCompact_univ_iff.1 (by rw [← huniv]; exact hcpt))
  rcases isClopen_iff.1 ⟨hRclosed, hRopen⟩ with hemp | huniv
  · exact absurd hemp (Set.nonempty_iff_ne_empty.1 ⟨p, mem_insert _ _⟩)
  · exact huniv

end BoundarySurj

/-! ## From a bijective parametrization to a diffeomorphism -/

section Inverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The inverse of an injective onto parametrization is `C^∞` as soon as it is locally given by a
`C^∞` function.**  The hypothesis `hloc` asks, at each parameter `u`, for an open neighbourhood `V`
of the point `Γ u` and a `C^∞` function `ψ` on `V` which reads off *a* parameter of each point of
`V`; injectivity then forces `ψ` to be the inverse there.  For a unit-speed curve the local `ψ` is
the coordinate of a smooth arc, and at the boundary point it is the coordinate of the arc issuing
from it. -/
theorem exists_inverse_coord' {Γ : ℝ → M} {T : Set ℝ} (hinj : InjOn Γ T) (hsurj : Γ '' T = univ)
    (hloc : ∀ u ∈ T, ∃ (V : Set M) (ψ : M → ℝ), IsOpen V ∧ Γ u ∈ V ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ V ∧ ∀ x ∈ V, ∃ w ∈ T, Γ w = x ∧ ψ x = w) :
    ∃ θ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ θ ∧ (∀ x, θ x ∈ T) ∧ (∀ x, Γ (θ x) = x) ∧
      ∀ u ∈ T, θ (Γ u) = u := by
  classical
  have hex : ∀ x : M, ∃ u, u ∈ T ∧ Γ u = x := by
    intro x
    have hx : x ∈ Γ '' T := by rw [hsurj]; exact mem_univ x
    obtain ⟨u, hu, hxu⟩ := hx
    exact ⟨u, hu, hxu⟩
  refine ⟨fun x => (hex x).choose, ?_, fun x => (hex x).choose_spec.1,
    fun x => (hex x).choose_spec.2, fun u hu => ?_⟩
  swap
  · exact hinj (hex (Γ u)).choose_spec.1 hu (hex (Γ u)).choose_spec.2
  set θ : M → ℝ := fun x => (hex x).choose with hθdef
  have hθT : ∀ x, θ x ∈ T := fun x => (hex x).choose_spec.1
  have hθΓ : ∀ x, Γ (θ x) = x := fun x => (hex x).choose_spec.2
  have hΓθ : ∀ u ∈ T, θ (Γ u) = u := fun u hu => hinj (hθT _) hu (hθΓ _)
  intro x
  obtain ⟨V, ψ, hVopen, hΓV, hψ, hval⟩ := hloc (θ x) (hθT x)
  rw [hθΓ x] at hΓV
  have heq : ∀ y ∈ V, θ y = ψ y := by
    intro y hy
    obtain ⟨w, hwT, hwy, hψw⟩ := hval y hy
    rw [hψw, ← hwy, hΓθ w hwT]
  refine (hψ.contMDiffAt (hVopen.mem_nhds hΓV)).congr_of_eventuallyEq ?_
  filter_upwards [hVopen.mem_nhds hΓV] with y hy using heq y hy

end Inverse

/-! ## The shape of a half-open interval of times, and its parametrization by `Ici 0` -/

section HalfLineParam

/-- **The two shapes of a set of times issuing from `0`.**  A nonempty order-connected subset of
`Ici 0` containing `0`, containing a positive number, and open away from `0`, is `Ici 0` or `Ico 0
b`.  The `Icc 0 b` shape is excluded by openness away from `0`, which would otherwise make the
supremum an attained maximum with a whole ball around it. -/
theorem shape_of_halfline {T : Set ℝ} (h0 : (0 : ℝ) ∈ T) (hTI : T ⊆ Ici 0)
    (hToc : T.OrdConnected) (hTopen : IsOpen (T \ {0})) (hne : ∃ c, 0 < c ∧ c ∈ T) :
    T = Ici 0 ∨ ∃ b, 0 < b ∧ T = Ico 0 b := by
  obtain ⟨c, hc0, hcT⟩ := hne
  by_cases hbdd : BddAbove T
  · refine Or.inr ⟨sSup T, lt_of_lt_of_le hc0 (le_csSup hbdd hcT), ?_⟩
    refine Subset.antisymm (fun x hx => ⟨hTI hx, ?_⟩) fun x hx => ?_
    · rcases eq_or_lt_of_le (le_csSup hbdd hx) with heq | hlt
      · exfalso
        have hx0 : x ≠ 0 := by
          intro h
          have h1 := le_csSup hbdd hcT
          rw [← heq, h] at h1
          linarith
        obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hTopen x ⟨hx, hx0⟩
        have hmem : x + δ / 2 ∈ T \ {0} := by
          refine hball ?_
          rw [Metric.mem_ball, Real.dist_eq, show x + δ / 2 - x = δ / 2 from by ring,
            abs_of_pos (by linarith)]
          linarith
        have h2 := le_csSup hbdd hmem.1
        rw [← heq] at h2
        linarith
      · exact hlt
    · obtain ⟨z, hzT, hxz⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ hx.2
      exact hToc.out h0 hzT ⟨hx.1, hxz.le⟩
  · refine Or.inl (Subset.antisymm hTI fun x hx => ?_)
    obtain ⟨z, hzT, hxz⟩ := exists_gt_of_not_bddAbove hbdd x
    exact hToc.out h0 hzT ⟨hx, hxz.le⟩

/-- **Every set of times of the two shapes above is parametrized by `Ici 0`**, by an explicit pair
of mutually inverse `C^∞` maps fixing `0`: the identity in the unbounded case, and the Möbius map `u
↦ b u / (1 + u)` with inverse `v ↦ v / (b - v)` in the bounded case.  As in the boundaryless case,
both halves are written down, so no inverse function theorem at the endpoint is needed. -/
theorem exists_param_halfline {T : Set ℝ} (hT : T = Ici 0 ∨ ∃ b, 0 < b ∧ T = Ico 0 b) :
    ∃ f g : ℝ → ℝ, ContDiffOn ℝ ∞ f (Ici 0) ∧ ContDiffOn ℝ ∞ g T ∧
      (∀ u ∈ Ici (0 : ℝ), f u ∈ T) ∧ (∀ v ∈ T, 0 ≤ g v) ∧
      (∀ u ∈ Ici (0 : ℝ), g (f u) = u) ∧ (∀ v ∈ T, f (g v) = v) ∧ f 0 = 0 := by
  rcases hT with rfl | ⟨b, hb, rfl⟩
  · exact ⟨id, id, contDiffOn_id, contDiffOn_id, fun u hu => hu, fun v hv => hv,
      fun _ _ => rfl, fun _ _ => rfl, rfl⟩
  · have hb' : b ≠ 0 := ne_of_gt hb
    refine ⟨fun u => b * u / (1 + u), fun v => v / (b - v), ?_, ?_, ?_, ?_, ?_, ?_, by simp⟩
    · intro u hu
      have hu' : (0 : ℝ) ≤ u := hu
      have hden : (1 : ℝ) + u ≠ 0 := ne_of_gt (by linarith)
      exact (ContDiffAt.div (contDiff_const.mul contDiff_id).contDiffAt
        (contDiff_const.add contDiff_id).contDiffAt hden).contDiffWithinAt
    · intro v hv
      have hvb : b - v ≠ 0 := ne_of_gt (by linarith [hv.2])
      exact (ContDiffAt.div contDiff_id.contDiffAt
        (contDiff_const.sub contDiff_id).contDiffAt hvb).contDiffWithinAt
    · intro u hu
      have hu' : (0 : ℝ) ≤ u := hu
      have hden : (0 : ℝ) < 1 + u := by linarith
      refine ⟨div_nonneg (by positivity) hden.le, ?_⟩
      rw [div_lt_iff₀ hden]
      nlinarith
    · intro v hv
      have hvb : (0 : ℝ) < b - v := by linarith [hv.2]
      exact div_nonneg hv.1 hvb.le
    · intro u hu
      have hu' : (0 : ℝ) ≤ u := hu
      have hden : (1 : ℝ) + u ≠ 0 := ne_of_gt (by linarith)
      have h1 : b - b * u / (1 + u) = b / (1 + u) := by
        rw [eq_div_iff hden]
        field_simp
        ring
      show b * u / (1 + u) / (b - b * u / (1 + u)) = u
      rw [h1, div_eq_iff (div_ne_zero hb' hden)]
      field_simp
    · intro v hv
      have hvb : (0 : ℝ) < b - v := by linarith [hv.2]
      have hvb' : b - v ≠ 0 := ne_of_gt hvb
      have h1 : (1 : ℝ) + v / (b - v) = b / (b - v) := by
        rw [eq_div_iff hvb']
        field_simp
        ring
      show b * (v / (b - v)) / (1 + v / (b - v)) = v
      rw [h1, div_eq_iff (div_ne_zero hb' hvb')]
      field_simp

end HalfLineParam

/-! ## The case with a boundary point: the classification -/

section BoundaryMain

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] [PreconnectedSpace M]
  {p : M}

include hE

/-- **A connected, σ-compact smooth one-manifold with a boundary point, which is not compact, is
parametrized by a half-open interval of times issuing from that point.**

There are a map `Γ : ℝ → M` and a set of times `T`, equal to `Ici 0` or to `Ico 0 b`, such that `Γ 0
= p`, `Γ` is `C^∞` on `T`, injective on `T` and onto `M`, no value other than `Γ 0` is a boundary
point, and the inverse `θ : M → ℝ` is `C^∞` on all of `M`.

The construction.  A unit-speed arc `A₀` issues from `p` with half-open target `Ico 0 ε₀`; its
restriction to `Ioo 0 (2 ε₁)` recentred at `ε₁ = ε₀/2` (`SmoothArc.shrink`) is a *centred*
unit-speed arc `A₁` with symmetric open target, so the maximal unit-speed curve `globalCurve` from
`A₁` is available.  Its interval `Dom` of reached times has `-ε₁` as its left end, *not attained*
(`left_notMem_dom`), because the curve would otherwise take the value `p`, and no value of a
unit-speed curve is a boundary point.  Shifting time by `ε₁` and adjoining the single time `0`,
where the value is `p`, gives `Γ` and `T`.  Injectivity is `injOn_dom_halfline`, surjectivity is
`insert_image_dom_eq_univ` -- the only step that uses non-compactness -- and the inverse coordinate
is `exists_inverse_coord'`, whose local data is `A₀.toFun` near `p` and the coordinate of a local
arc elsewhere. -/
theorem exists_ray_of_mem_boundary (hp : p ∈ I.boundary M) (hnc : ¬ CompactSpace M) :
    ∃ (Γ : ℝ → M) (T : Set ℝ), (T = Ici 0 ∨ ∃ b, 0 < b ∧ T = Ico 0 b) ∧ Γ 0 = p ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ Γ T ∧ InjOn Γ T ∧ Γ '' T = univ ∧
      (∀ u ∈ T, u ≠ 0 → Γ u ∉ I.boundary M) ∧
      ∃ θ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ θ ∧ (∀ x, θ x ∈ T) ∧ (∀ x, Γ (θ x) = x) ∧
        ∀ u ∈ T, θ (Γ u) = u := by
  obtain ⟨L⟩ := nonempty_lengthElement I hE M
  obtain ⟨A₀, ε₀, hε₀, hpmem, hp0, hA₀t, hA₀⟩ := exists_unitSpeed_of_mem_boundary I hE L hp
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = ε₀ / 2 := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by rw [hε₁def]; linarith
  have hε : 2 * ε₁ ≤ ε₀ := by rw [hε₁def]; linarith
  have h2ε₁ : (0 : ℝ) < 2 * ε₁ := by linarith
  have hIoosub : Ioo (0 : ℝ) (2 * ε₁) ⊆ A₀.target := by
    rw [hA₀t]
    intro v hv
    exact ⟨hv.1.le, by linarith [hv.2]⟩
  obtain ⟨A₁, hA₁def⟩ : ∃ A₁ : SmoothArc I ∞ M, A₁ = A₀.shrink h2ε₁ hIoosub ε₁ := ⟨_, rfl⟩
  have hA₁t : A₁.target = Ioo (-ε₁) ε₁ := by
    rw [hA₁def, SmoothArc.shrink_target, show (0 : ℝ) - ε₁ = -ε₁ from by ring,
      show 2 * ε₁ - ε₁ = ε₁ from by ring]
  have hA₁ : UnitSpeed L A₁ := by
    rw [hA₁def]; exact A₀.unitSpeed_shrink hA₀ h2ε₁ hIoosub ε₁
  have hA₁inv : ∀ s, A₁.invFun s = A₀.invFun (s + ε₁) := by
    intro s; rw [hA₁def]; rfl
  -- the maximal curve
  have hcurve : IsUnitSpeedCurveOn L (globalCurve I L A₁) (Dom I L A₁) :=
    isUnitSpeedCurveOn_globalCurve I
  have hDoc : (Dom I L A₁).OrdConnected := ordConnected_dom I
  obtain ⟨hsub0, heq0⟩ := subset_dom_halfline I hε₁ hA₁t hA₁
  have h0 : (0 : ℝ) ∈ Dom I L A₁ := hsub0 ⟨by linarith, hε₁⟩
  have hDIoi : Dom I L A₁ ⊆ Ioi (-ε₁) :=
    dom_subset_Ioi I hε₁ hε hpmem hp0 hA₀t hp hA₁t hA₁ hA₁inv
  have hinj : InjOn (globalCurve I L A₁) (Dom I L A₁) := injOn_dom_halfline I hE hp
  have huniv : insert p (globalCurve I L A₁ '' Dom I L A₁) = univ :=
    insert_image_dom_eq_univ I hE hε₁ hε hpmem hp0 hA₀t hp hA₁t hA₁ hA₁inv hnc
  have hpinv : A₀.invFun 0 = p := by rw [← hp0, A₀.left_inv hpmem]
  -- the set of times
  obtain ⟨T, hTdef⟩ : ∃ T : Set ℝ, T = insert 0 {u : ℝ | u - ε₁ ∈ Dom I L A₁} := ⟨_, rfl⟩
  have hTmem : ∀ u : ℝ, u ∈ T ↔ (u = 0 ∨ u - ε₁ ∈ Dom I L A₁) := by
    intro u
    rw [hTdef]
    exact Set.mem_insert_iff
  have hTpos : ∀ u : ℝ, u - ε₁ ∈ Dom I L A₁ → 0 < u := by
    intro u hu
    have h := hDIoi hu
    rw [mem_Ioi] at h
    linarith
  have hTI : T ⊆ Ici 0 := by
    intro u hu
    rcases (hTmem u).1 hu with rfl | hu'
    · exact mem_Ici.2 le_rfl
    · exact mem_Ici.2 (hTpos u hu').le
  have h0T : (0 : ℝ) ∈ T := (hTmem 0).2 (Or.inl rfl)
  have hε₁T : ε₁ ∈ T := (hTmem ε₁).2 (Or.inr (by rw [sub_self]; exact h0))
  have hIcoT : Ico (0 : ℝ) (2 * ε₁) ⊆ T := by
    intro v hv
    rcases eq_or_lt_of_le hv.1 with hz | hz
    · rw [← hz]; exact h0T
    · exact (hTmem v).2 (Or.inr (hsub0 ⟨by linarith, by linarith [hv.2]⟩))
  have hTdiff : T \ {0} = {u : ℝ | u - ε₁ ∈ Dom I L A₁} := by
    refine Subset.antisymm (fun u hu => ?_) fun u hu => ?_
    · rcases (hTmem u).1 hu.1 with rfl | hu'
      · exact absurd rfl hu.2
      · exact hu'
    · refine ⟨(hTmem u).2 (Or.inr hu), ?_⟩
      intro hu0
      have h1 : (0 : ℝ) < u := hTpos u hu
      rw [show u = 0 from hu0] at h1
      linarith
  have hTopen : IsOpen (T \ {0}) := by
    rw [hTdiff]
    exact (isOpen_dom I).preimage (continuous_id.sub continuous_const)
  have hkey : ∀ b ∈ T, ∀ c, 0 < c → c ≤ b → c ∈ T := by
    intro b hb c hc0 hcb
    have hbS : b - ε₁ ∈ Dom I L A₁ := by
      rcases (hTmem b).1 hb with rfl | hbS
      · exact absurd hcb (by linarith)
      · exact hbS
    refine (hTmem c).2 (Or.inr ?_)
    rcases lt_or_ge (c - ε₁) ε₁ with h | h
    · exact hsub0 ⟨by linarith, h⟩
    · exact hDoc.out h0 hbS ⟨by linarith, by linarith⟩
  have hToc : T.OrdConnected := by
    constructor
    intro a ha b hb c hc
    rcases eq_or_lt_of_le (le_trans (mem_Ici.1 (hTI ha)) hc.1) with h | h
    · rw [← h]; exact h0T
    · exact hkey b hb c h hc.2
  have hTshape := shape_of_halfline h0T hTI hToc hTopen ⟨ε₁, hε₁, hε₁T⟩
  -- the parametrization
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : ℝ → M,
      Γ = fun u => if u ≤ 0 then p else globalCurve I L A₁ (u - ε₁) := ⟨_, rfl⟩
  have hΓ0 : Γ 0 = p := by rw [hΓdef]; simp
  have hΓpos : ∀ u : ℝ, 0 < u → Γ u = globalCurve I L A₁ (u - ε₁) := by
    intro u hu
    rw [hΓdef]
    exact if_neg (by linarith : ¬ u ≤ 0)
  have hΓsmall : ∀ u ∈ Ico (0 : ℝ) (2 * ε₁), Γ u = A₀.invFun u := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h, hΓ0, hpinv]
    · rw [hΓpos u h, ← heq0 ⟨by linarith, by linarith [hu.2]⟩, hA₁inv]
      congr 1
      ring
  have hΓbdry : ∀ u ∈ T, u ≠ 0 → Γ u ∉ I.boundary M := by
    intro u hu hu0
    have hu' : u - ε₁ ∈ Dom I L A₁ := by
      rcases (hTmem u).1 hu with rfl | hu'
      · exact absurd rfl hu0
      · exact hu'
    rw [hΓpos u (hTpos u hu')]
    exact hcurve.notMem_boundary hu'
  have hΓimage : Γ '' T = insert p (globalCurve I L A₁ '' Dom I L A₁) := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · obtain ⟨u, hu, rfl⟩ := hx
      rcases (hTmem u).1 hu with rfl | hu'
      · rw [hΓ0]; exact mem_insert _ _
      · rw [hΓpos u (hTpos u hu')]
        exact mem_insert_iff.2 (Or.inr ⟨u - ε₁, hu', rfl⟩)
    · rcases hx with rfl | hx
      · exact ⟨0, h0T, hΓ0⟩
      · obtain ⟨s, hs, rfl⟩ := hx
        have hsT : s + ε₁ - ε₁ ∈ Dom I L A₁ := by rw [add_sub_cancel_right]; exact hs
        refine ⟨s + ε₁, (hTmem _).2 (Or.inr hsT), ?_⟩
        rw [hΓpos _ (hTpos _ hsT), add_sub_cancel_right]
  have hΓsurj : Γ '' T = univ := by rw [hΓimage]; exact huniv
  have hΓinj : InjOn Γ T := by
    intro u₁ h₁ u₂ h₂ heq
    rcases (hTmem u₁).1 h₁ with rfl | h₁'
    · rcases (hTmem u₂).1 h₂ with rfl | h₂'
      · rfl
      · exfalso
        rw [hΓ0, hΓpos u₂ (hTpos u₂ h₂')] at heq
        exact hcurve.notMem_boundary h₂' (by rw [← heq]; exact hp)
    · rcases (hTmem u₂).1 h₂ with rfl | h₂'
      · exfalso
        rw [hΓ0, hΓpos u₁ (hTpos u₁ h₁')] at heq
        exact hcurve.notMem_boundary h₁' (by rw [heq]; exact hp)
      · rw [hΓpos u₁ (hTpos u₁ h₁'), hΓpos u₂ (hTpos u₂ h₂')] at heq
        have h := hinj h₁' h₂' heq
        linarith
  -- smoothness of the parametrization
  have hΓsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ Γ T := by
    intro u hu
    rcases eq_or_lt_of_le (mem_Ici.1 (hTI hu)) with h | h
    · have hIcosub : Ico (0 : ℝ) (2 * ε₁) ⊆ A₀.target := by
        rw [hA₀t]
        intro v hv
        exact ⟨hv.1, by linarith [hv.2]⟩
      have h1 : ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ A₀.invFun (Ico 0 (2 * ε₁)) 0 :=
        (A₀.contMDiffOn_invFun.mono hIcosub) 0 ⟨le_rfl, by linarith⟩
      have hsubT : T ∩ Iio (2 * ε₁) ⊆ Ico (0 : ℝ) (2 * ε₁) := fun v hv => ⟨hTI hv.1, hv.2⟩
      have h2 : ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ Γ (T ∩ Iio (2 * ε₁)) 0 :=
        (h1.mono hsubT).congr (fun v hv => hΓsmall v (hsubT hv))
          (hΓsmall 0 ⟨le_rfl, by linarith⟩)
      have h3 : T ∩ Iio (2 * ε₁) ∈ 𝓝[T] (0 : ℝ) :=
        inter_mem_nhdsWithin T (Iio_mem_nhds (by linarith))
      rw [← h]
      exact h2.mono_of_mem_nhdsWithin h3
    · have hu' : u - ε₁ ∈ Dom I L A₁ := by
        rcases (hTmem u).1 hu with rfl | hu'
        · exact absurd h (by linarith)
        · exact hu'
      have hshift : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun v : ℝ => v - ε₁) u :=
        (contDiff_id.sub contDiff_const).contMDiff.contMDiffAt
      have hg := hcurve.contMDiffOn.contMDiffAt ((isOpen_dom I).mem_nhds hu')
      have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun v => globalCurve I L A₁ (v - ε₁)) u :=
        hg.comp u hshift
      refine (hcomp.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [Ioi_mem_nhds h] with v hv
      exact hΓpos v hv
  -- the inverse coordinate
  have hloc : ∀ u ∈ T, ∃ (V : Set M) (ψ : M → ℝ), IsOpen V ∧ Γ u ∈ V ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ψ V ∧ ∀ x ∈ V, ∃ w ∈ T, Γ w = x ∧ ψ x = w := by
    intro u hu
    rcases eq_or_lt_of_le (mem_Ici.1 (hTI hu)) with h | h
    · refine ⟨A₀.source ∩ A₀.toFun ⁻¹' Iio (2 * ε₁), A₀.toFun,
        A₀.continuousOn_toFun.isOpen_inter_preimage A₀.open_source isOpen_Iio, ?_,
        A₀.contMDiffOn_toFun.mono inter_subset_left, ?_⟩
      · rw [← h, hΓ0]
        exact ⟨hpmem, by rw [Set.mem_preimage, hp0]; exact show (0 : ℝ) < 2 * ε₁ by linarith⟩
      · intro x hx
        have hv : A₀.toFun x ∈ Ico 0 ε₀ := by rw [← hA₀t]; exact A₀.map_source hx.1
        have hvlt : A₀.toFun x < 2 * ε₁ := hx.2
        refine ⟨A₀.toFun x, hIcoT ⟨hv.1, hvlt⟩, ?_, rfl⟩
        rw [hΓsmall _ ⟨hv.1, hvlt⟩, A₀.left_inv hx.1]
    · have hu' : u - ε₁ ∈ Dom I L A₁ := by
        rcases (hTmem u).1 hu with rfl | hu'
        · exact absurd h (by linarith)
        · exact hu'
      obtain ⟨A, k, η, -, hη, hIoo, hdesc⟩ := hcurve (u - ε₁) hu'
      have htmem : u - ε₁ ∈ Ioo (u - ε₁ - η) (u - ε₁ + η) := ⟨by linarith, by linarith⟩
      refine ⟨A.invFun '' (Ioo (u - ε₁ - η - k) (u - ε₁ + η - k) ∩ A.target),
        fun x => A.toFun x + k + ε₁, A.isOpen_image isOpen_Ioo, ?_, ?_, ?_⟩
      · rw [hΓpos u h]
        exact ⟨u - ε₁ - k, ⟨⟨by linarith, by linarith⟩, (hdesc _ htmem).1⟩,
          ((hdesc _ htmem).2).symm⟩
      · have hsub : A.invFun '' (Ioo (u - ε₁ - η - k) (u - ε₁ + η - k) ∩ A.target) ⊆ A.source := by
          rintro y ⟨v, ⟨-, hvT⟩, rfl⟩
          exact A.map_target hvT
        exact ((A.contMDiffOn_toFun.mono hsub).add contMDiffOn_const).add contMDiffOn_const
      · rintro x ⟨v, ⟨hvV, hvT⟩, rfl⟩
        have hmem : v + k ∈ Ioo (u - ε₁ - η) (u - ε₁ + η) :=
          ⟨by linarith [hvV.1], by linarith [hvV.2]⟩
        have hvD : v + k + ε₁ - ε₁ ∈ Dom I L A₁ := by
          rw [add_sub_cancel_right]
          exact hIoo hmem
        refine ⟨v + k + ε₁, (hTmem _).2 (Or.inr hvD), ?_, ?_⟩
        · rw [hΓpos _ (hTpos _ hvD), add_sub_cancel_right, (hdesc _ hmem).2]
          congr 1
          ring
        · show A.toFun (A.invFun v) + k + ε₁ = v + k + ε₁
          rw [A.right_inv hvT]
  obtain ⟨θ, hθsm, hθT, hθΓ, hΓθ⟩ := exists_inverse_coord' I hΓinj hΓsurj hloc
  exact ⟨Γ, T, hTshape, hΓ0, hΓsmooth, hΓinj, hΓsurj, hΓbdry, θ, hθsm, hθT, hθΓ, hΓθ⟩

/-- **Milnor's Appendix, the third case (book p. 54): a connected, σ-compact smooth one-manifold
with a boundary point, which is not compact, is diffeomorphic to the closed half-line.**

Precisely: let `E` be a real normed space with `Module.finrank ℝ E = 1`, let `I : ModelWithCorners ℝ
E H`, and let `M` be a Hausdorff, σ-compact, preconnected `C^∞` manifold charted on `H` with a point
`p ∈ I.boundary M` and `¬ CompactSpace M`.  Then `M` is `C^∞`-diffeomorphic to `Ici (0 : ℝ)`, which
carries its one-chart manifold-with-boundary structure over Mathlib's model `𝓡∂ 1`.

The diffeomorphism is `u ↦ Γ (f u)`, with `Γ` the arc-length parametrization by a half-open interval
of times issuing from `p` (`exists_ray_of_mem_boundary`) and `f` the explicit reparametrization of
`exists_param_halfline`; its inverse is `x ↦ max (g (θ x)) 0`.  Nonemptiness of `M` is automatic
from the boundary point. -/
theorem nonempty_diffeomorphIci (hp : p ∈ I.boundary M) (hnc : ¬ CompactSpace M) :
    Nonempty (Diffeomorph (𝓡∂ 1) I (Ici (0 : ℝ)) M ∞) := by
  obtain ⟨Γ, T, hTshape, hΓ0, hΓsm, hΓinj, hΓsurj, hΓbdry, θ, hθsm, hθT, hθΓ, hΓθ⟩ :=
    exists_ray_of_mem_boundary I hE hp hnc
  obtain ⟨f, g, hf, hg, hfT, hgpos, hgf, hfg, hf0⟩ := exists_param_halfline hTshape
  have h1 : ContMDiff (𝓡∂ 1) I ∞ (fun u : Ici (0 : ℝ) => Γ (f u)) := by
    have hfm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ f (Ici 0) := contMDiffOn_iff_contDiffOn.2 hf
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun u : ℝ => Γ (f u)) (Ici 0) :=
      hΓsm.comp hfm fun u hu => hfT u hu
    exact hcomp.comp_contMDiff contMDiff_subtypeVal_Ici fun u => u.2
  have h2 : ContMDiff I (𝓡∂ 1) ∞ (fun x : M => iciProj (g (θ x))) := by
    have hgm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ g T := contMDiffOn_iff_contDiffOn.2 hg
    have hgθ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => g (θ x)) :=
      hgm.comp_contMDiff hθsm fun x => hθT x
    exact contMDiffOn_iciProj.comp_contMDiff hgθ fun x => hgpos _ (hθT x)
  exact ⟨⟨{ toFun := fun u => Γ (f u)
            invFun := fun x => iciProj (g (θ x))
            left_inv := fun u => by
              show iciProj (g (θ (Γ (f u)))) = u
              rw [hΓθ _ (hfT _ u.2), hgf _ u.2]
              exact Subtype.ext (max_eq_left u.2)
            right_inv := fun x => by
              show Γ (f ((iciProj (g (θ x)) : Ici (0 : ℝ)) : ℝ)) = x
              rw [coe_iciProj, max_eq_left (hgpos _ (hθT x)), hfg _ (hθT x), hθΓ x] }, h1, h2⟩⟩

/-- **The boundary of a non-compact connected σ-compact smooth one-manifold with a boundary point is
that point alone.**  Every point of `M` is a value of the parametrization, and the only value which
is a boundary point is `Γ 0 = p`. -/
theorem boundary_eq_singleton (hp : p ∈ I.boundary M) (hnc : ¬ CompactSpace M) :
    I.boundary M = {p} := by
  obtain ⟨Γ, T, -, hΓ0, -, -, hΓsurj, hΓbdry, -⟩ :=
    exists_ray_of_mem_boundary I hE hp hnc
  refine Subset.antisymm (fun q hq => ?_) ?_
  · obtain ⟨u, hu, rfl⟩ : q ∈ Γ '' T := by rw [hΓsurj]; exact mem_univ q
    by_cases hu0 : u = 0
    · rw [hu0, hΓ0]
      exact rfl
    · exact absurd hq (hΓbdry u hu hu0)
  · intro q hq
    rw [show q = p from hq]
    exact hp

/-- **The half-line case, in the direction `M → Ici (0 : ℝ)`.**  Same hypotheses as
`nonempty_diffeomorphIci`. -/
theorem nonempty_diffeomorphIci' (hp : p ∈ I.boundary M) (hnc : ¬ CompactSpace M) :
    Nonempty (Diffeomorph I (𝓡∂ 1) M (Ici (0 : ℝ)) ∞) :=
  (nonempty_diffeomorphIci I hE hp hnc).map Diffeomorph.symm

end BoundaryMain

end Milnor.OneManifold.Smooth
