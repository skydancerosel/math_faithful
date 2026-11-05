import Milnor.Appendix.Smooth.LengthElement
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Milnor's Appendix, smooth version: unit-speed arcs exist

Milnor, *Topology from the Differentiable Viewpoint*, Appendix (book p. 54), classifies the
connected one-manifolds.  This file is **Stage 4** of the plan `Exposition/PlanOneManifold.md`: it
proves **Milnor's Lemma 1.1**, the statement his text disposes of with "by a straightforward change
of variables", that every point of a one-manifold lies on a *unit-speed* arc.

The input is the smooth arcs of `Milnor/Appendix/Smooth/SmoothArc.lean` (Stage 1) and the length
element of `Milnor/Appendix/Smooth/LengthElement.lean` (Stage 3); the output is the same arcs
reparametrized so that the length element, read in the new parameter, is identically `1`.  The
reparametrization is by arc length: the new parameter of the point at old parameter `u` is
`σ u = ∫₀ᵘ ρ`, where `ρ` is the length element read in the old parameter.

## What is proved

Three groups of statements.

**Two general lemmas isolated for the endpoints**, which are the two places the plan warns about:

* `continuousOn_leftInvOn_of_isCompact`: the inverse of a continuous injection on a compact set is
  continuous on the image.  Proved by the closed-map argument rather than by a case analysis at the
  endpoints, and it is what keeps the endpoint of a half-open target painless.
* `hasDerivWithinAt_of_leftInvOn`: **the one-sided inverse function rule.**  If `g` inverts `f` on
  `t`, is continuous there, and `f` has a nonzero derivative *within* `s` at `g v`, then `g` has
  derivative `1/f'` within `t` at `v`.  Both derivatives may be one-sided; the proof is the identity
  `slope g v w = (slope f (g v) (g w))⁻¹` pushed through the filter `𝓝[t \ {v}] v`.  Mathlib's
  `HasFDerivAt.of_local_left_inverse` is the two-sided statement and does not apply at an endpoint.

**Arc length on a compact interval** (pure real analysis, no manifolds).  For a positive `C^∞`
density `ρ` on `Icc a b` and a base point `c`, the primitive `arcParam ρ c v = ∫ x in c..v, ρ x`:

* `hasDerivWithinAt_arcParam`, `derivWithin_arcParam`: the fundamental theorem of calculus, valid at
  the *endpoints* of `Icc a b` as a one-sided statement -- Mathlib's
  `intervalIntegral.integral_hasDerivWithinAt_right` with the `FTCFilter` instance for `Icc`.
* `contDiffOn_arcParam`: the primitive of a `C^∞` function is `C^∞`, by
  `contDiffOn_infty_iff_derivWithin` on a set with unique derivatives.
* `strictMonoOn_arcParam`, `image_arcParam`: a positive density makes the primitive strictly
  increasing, and the image of `Icc a b` is `Icc (σ a) (σ b)`.
* `arcParamInv` and the six lemmas about it: the inverse is defined on `Icc (σ a) (σ b)`, strictly
  increasing, **continuous**, **differentiable with derivative `1/ρ`**, and **`C^∞`** -- at the
  endpoints included.

**Unit-speed arcs.**

* `UnitSpeed L A`: the length element `L`, read in the parameter of the smooth arc `A`, is
  identically `1` on `A.target`.
* `exists_reparam`: **the reparametrization theorem.**  Given a smooth arc `A`, a compact interval
  `Icc a b ⊆ A.target` containing `0`, and a "window" `J ⊆ Icc a b` whose preimage in `M` is open
  and whose arc-length image is a legitimate arc target, there is a *unit-speed* smooth arc with
  source
  `A.source ∩ A.toFun ⁻¹' J`, target `σ '' J` and coordinate `σ ∘ A.toFun`.
* `exists_unitSpeed_of_mem_boundary`, `exists_unitSpeed_of_notMem_boundary`, `exists_unitSpeed`:
  **every point of the manifold lies in the source of a unit-speed smooth arc sending it to `0`**,
  with target `Ico 0 ε` at a boundary point and `Ioo (-ε) ε` elsewhere.  This is the conclusion
  Stage 5 consumes.

## The two soft spots, and how they were handled

The plan flags the one-sided smooth inverse at a boundary endpoint as the second soft spot of the
programme, and offers a fallback: extend the density across the endpoint by derivative surgery and
invert on an open interval.  **The fallback was not needed.**  Two devices did the job directly.

*The window.*  All the analysis is done on a **compact** interval `Icc a b` sitting inside the arc's
target, and only at the end is the arc restricted to a relatively open window `J` inside it.  This
costs nothing -- the conclusion only asks for *some* `ε` -- and it buys two things: the `FTCFilter`
instance for `Icc` makes the fundamental theorem of calculus available at the endpoints, and
compactness of `Icc a b` gives the continuity of the inverse for free.

*The bootstrap.*  Smoothness of the inverse is obtained exactly as the plan prescribes, by induction
on the order: `g` is continuous, hence `C⁰`; and if `g` is `Cᵏ` then `derivWithin g` is `(ρ ∘ g)⁻¹`,
which is `Cᵏ` because `ρ` is `C^∞` and does not vanish, so `g` is `Cᵏ⁺¹`.  The inductive step is
`contDiffOn_succ_iff_derivWithin`, which needs unique derivatives on the target -- supplied by
convexity of `Icc (σ a) (σ b)`, and one level up by `uniqueDiffOn_of_ordConnected_nontrivial`, the
same fact for an arbitrary arc target.

## Hypotheses

The real-analysis lemmas are about `ℝ` alone.  For the arcs, `M` is a manifold charted on a model
with corners `I : ModelWithCorners ℝ E H`; `UnitSpeed`, `arcLength` and `exists_reparam` assume
nothing beyond the arcs they are handed -- no dimension, Hausdorffness or compactness hypothesis, no
boundarylessness -- and `exists_reparam` is stated for `C^∞`, which is what Stage 3's length element
is.  The three existence theorems need, exactly as Stage 1 does, `Module.finrank ℝ E = 1` and
`IsManifold I ∞ M`; they take the length element as an argument, so it is Stage 3's
`nonempty_lengthElement` -- and only that -- which needs `T2Space M` and `SigmaCompactSpace M`.  All
three shapes of the model range allowed by Stage 0 stay alive, and the manifold may have boundary.

## References

* Milnor, *Topology from the Differentiable Viewpoint*, Appendix, p. 54.
* `Exposition/PlanOneManifold.md`, Stage 4.
-/

open Set Filter Topology MeasureTheory

open scoped ContDiff Manifold

noncomputable section

namespace Milnor.OneManifold.Smooth

/-! ## Unique differentiability on an interval of reals -/

/-- **An order-connected set of reals with two distinct points has unique derivatives.**  It is
convex with nonempty interior, so `uniqueDiffOn_convex` applies.  This is exactly the shape of the
target of an arc, and it is what makes `derivWithin` unambiguous at an *endpoint* -- the case that
occurs for an arc starting at a boundary point. -/
theorem uniqueDiffOn_of_ordConnected_nontrivial {T : Set ℝ} (hoc : T.OrdConnected)
    (hnt : T.Nontrivial) : UniqueDiffOn ℝ T := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hnt
  refine uniqueDiffOn_convex (convex_iff_ordConnected.2 hoc) ?_
  rcases hxy.lt_or_gt with h | h
  · exact ⟨(x + y) / 2, mem_interior.2 ⟨Ioo x y, Ioo_subset_Icc_self.trans (hoc.out hx hy),
      isOpen_Ioo, by constructor <;> linarith⟩⟩
  · exact ⟨(x + y) / 2, mem_interior.2 ⟨Ioo y x, Ioo_subset_Icc_self.trans (hoc.out hy hx),
      isOpen_Ioo, by constructor <;> linarith⟩⟩

/-! ## Two lemmas about one-sided inverses -/

section Inverses

/-- **The inverse of a continuous injection on a compact set is continuous on the image.**  Here `g`
is any left inverse of `f` on the compact set `K`; the hypothesis `hg` forces `f` to be injective on
`K`.  The proof is the closed-map argument: `g ⁻¹' C ∩ f '' K = f '' (K ∩ C)`, and the right-hand
side is the continuous image of a compact set, hence closed.

In this file `K` is a compact interval sitting inside the target of an arc, and this lemma is what
makes the continuity of the arc-length inverse painless *at an endpoint*, where the usual
open-neighbourhood arguments fail. -/
theorem continuousOn_leftInvOn_of_isCompact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {K : Set X} {f : X → Y} {g : Y → X} (hK : IsCompact K) (hf : ContinuousOn f K)
    (hg : ∀ u ∈ K, g (f u) = u) : ContinuousOn g (f '' K) := by
  rw [continuousOn_iff_isClosed]
  intro C hC
  refine ⟨f '' (K ∩ C), ?_, ?_⟩
  · exact ((hK.inter_right hC).image_of_continuousOn (hf.mono inter_subset_left)).isClosed
  · apply Subset.antisymm
    · rintro v ⟨hvC, u, hu, rfl⟩
      refine ⟨⟨u, ⟨hu, ?_⟩, rfl⟩, ⟨u, hu, rfl⟩⟩
      have hmem : g (f u) ∈ C := hvC
      rwa [hg u hu] at hmem
    · rintro v ⟨⟨u, hu, rfl⟩, -⟩
      refine ⟨?_, ⟨u, hu.1, rfl⟩⟩
      change g (f u) ∈ C
      rw [hg u hu.1]
      exact hu.2

/-- **The one-sided inverse function rule.**  Let `g` map `t` into `s`, invert `f` on `t`, and be
continuous within `t` at `v ∈ t`; let `f` have the nonzero derivative `d` within `s` at `g v`.  Then
`g` has derivative `d⁻¹` within `t` at `v`.

Neither `s` nor `t` is assumed open, and both `v` and `g v` may be endpoints, so both derivatives
may be one-sided; this is the statement Mathlib's `HasFDerivAt.of_local_left_inverse` does *not*
give.  The proof is elementary: for `w ∈ t \ {v}` the two slopes are reciprocal,
`slope g v w = (slope f (g v) (g w))⁻¹`, because `f (g w) = w` and `f (g v) = v`; continuity of `g`
pushes the filter `𝓝[t \ {v}] v` forward into `𝓝[s \ {g v}] (g v)`, where the slope of `f` tends to
`d`; and inversion is continuous away from `0`.

This discharges the plan's "second soft spot" without the fallback. -/
theorem hasDerivWithinAt_of_leftInvOn {f g : ℝ → ℝ} {s t : Set ℝ} {v d : ℝ} (hv : v ∈ t)
    (hmaps : MapsTo g t s) (hinv : ∀ w ∈ t, f (g w) = w) (hgc : ContinuousWithinAt g t v)
    (hf : HasDerivWithinAt f d s (g v)) (hd : d ≠ 0) : HasDerivWithinAt g d⁻¹ t v := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hf ⊢
  have hne : ∀ w ∈ t, w ≠ v → g w ≠ g v := by
    intro w hw hwv h
    exact hwv (by rw [← hinv w hw, h, hinv v hv])
  -- `g` pushes the punctured filter at `v` forward to the punctured filter at `g v`
  have hgt : Tendsto g (𝓝[t \ {v}] v) (𝓝[s \ {g v}] (g v)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hgc.mono_left (nhdsWithin_mono v sdiff_subset), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact ⟨hmaps hw.1, hne w hw.1 (by simpa using hw.2)⟩
  -- the reciprocal of the slope of `f` tends to `d⁻¹`
  have h2 : Tendsto (fun w => (slope f (g v) (g w))⁻¹) (𝓝[t \ {v}] v) (𝓝 d⁻¹) :=
    (hf.comp hgt).inv₀ hd
  refine Filter.Tendsto.congr' ?_ h2
  filter_upwards [self_mem_nhdsWithin] with w hw
  rw [slope_def_field, slope_def_field, hinv w hw.1, hinv v hv, inv_div]

end Inverses

/-! ## Arc length on a compact interval -/

section ArcParam

variable {ρ : ℝ → ℝ} {a b c : ℝ}

/-- **The arc-length parameter of a density.**  For a density `ρ` on the line and a base point `c`,
`arcParam ρ c v = ∫ x in c..v, ρ x` is the length of the stretch from `c` to `v`.  All the
statements below are relative to a compact interval `Icc a b` on which `ρ` is positive and `C^∞`. -/
def arcParam (ρ : ℝ → ℝ) (c : ℝ) : ℝ → ℝ := fun v => ∫ x in c..v, ρ x

/-- The arc-length parameter vanishes at its base point. -/
@[simp] theorem arcParam_self (ρ : ℝ → ℝ) (c : ℝ) : arcParam ρ c c = 0 :=
  intervalIntegral.integral_same

/-- A density continuous on an interval is interval-integrable between any two of its points. -/
theorem intervalIntegrable_of_mem_Icc (hρ : ContinuousOn ρ (Icc a b)) (hc : c ∈ Icc a b) {u : ℝ}
    (hu : u ∈ Icc a b) : IntervalIntegrable ρ volume c u :=
  (hρ.mono (ordConnected_Icc.uIcc_subset hc hu)).intervalIntegrable

/-- **The fundamental theorem of calculus on a compact interval, endpoints included.**  The
arc-length parameter has the density as its derivative *within* `Icc a b`; at `a` and at `b` this is
a one-sided derivative, which is what Mathlib's `FTCFilter` instance for `Icc` delivers. -/
theorem hasDerivWithinAt_arcParam (hρ : ContinuousOn ρ (Icc a b)) (hc : c ∈ Icc a b) {u : ℝ}
    (hu : u ∈ Icc a b) : HasDerivWithinAt (arcParam ρ c) (ρ u) (Icc a b) u := by
  have : Fact (u ∈ Icc a b) := ⟨hu⟩
  exact intervalIntegral.integral_hasDerivWithinAt_right
    (intervalIntegrable_of_mem_Icc hρ hc hu)
    ⟨Icc a b, self_mem_nhdsWithin, hρ.aestronglyMeasurable measurableSet_Icc⟩ (hρ u hu)

/-- The arc-length parameter is continuous on `Icc a b`. -/
theorem continuousOn_arcParam (hρ : ContinuousOn ρ (Icc a b)) (hc : c ∈ Icc a b) :
    ContinuousOn (arcParam ρ c) (Icc a b) :=
  fun _ hu => (hasDerivWithinAt_arcParam hρ hc hu).continuousWithinAt

/-- The derivative of the arc-length parameter within `Icc a b` is the density. -/
theorem derivWithin_arcParam (hab : a < b) (hρ : ContinuousOn ρ (Icc a b)) (hc : c ∈ Icc a b)
    {u : ℝ} (hu : u ∈ Icc a b) : derivWithin (arcParam ρ c) (Icc a b) u = ρ u :=
  (hasDerivWithinAt_arcParam hρ hc hu).derivWithin (uniqueDiffOn_Icc hab u hu)

/-- **The primitive of a `C^∞` density is `C^∞`**, endpoints included.  By
`contDiffOn_infty_iff_derivWithin` on `Icc a b`, which has unique derivatives; the derivative is the
density by the fundamental theorem of calculus. -/
theorem contDiffOn_arcParam (hab : a < b) (hρ : ContDiffOn ℝ ∞ ρ (Icc a b)) (hc : c ∈ Icc a b) :
    ContDiffOn ℝ ∞ (arcParam ρ c) (Icc a b) := by
  have hρc : ContinuousOn ρ (Icc a b) := hρ.continuousOn
  rw [contDiffOn_infty_iff_derivWithin (uniqueDiffOn_Icc hab)]
  refine ⟨fun u hu => (hasDerivWithinAt_arcParam hρc hc hu).differentiableWithinAt, ?_⟩
  exact hρ.congr fun u hu => derivWithin_arcParam hab hρc hc hu

/-- **A positive density makes the arc-length parameter strictly increasing.**  The increment is the
integral of the density over the intervening stretch, which is positive. -/
theorem strictMonoOn_arcParam (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ u ∈ Icc a b, 0 < ρ u)
    (hc : c ∈ Icc a b) : StrictMonoOn (arcParam ρ c) (Icc a b) := by
  intro u hu v hv huv
  have hsub : (∫ x in c..v, ρ x) - ∫ x in c..u, ρ x = ∫ x in u..v, ρ x :=
    intervalIntegral.integral_interval_sub_left (intervalIntegrable_of_mem_Icc hρ hc hv)
      (intervalIntegrable_of_mem_Icc hρ hc hu)
  have hposint : 0 < ∫ x in u..v, ρ x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (intervalIntegrable_of_mem_Icc hρ hu hv)
      (fun x hx => hpos x (ordConnected_Icc.out hu hv ⟨hx.1.le, hx.2.le⟩)) huv
  have hlt : (0 : ℝ) < arcParam ρ c v - arcParam ρ c u := by
    change (0 : ℝ) < (∫ x in c..v, ρ x) - ∫ x in c..u, ρ x
    rw [hsub]; exact hposint
  linarith

/-- The arc-length parameter carries `Icc a b` onto `Icc (σ a) (σ b)`: the intermediate value
theorem for a continuous increasing function. -/
theorem image_arcParam (hab : a ≤ b) (hρ : ContinuousOn ρ (Icc a b))
    (hpos : ∀ u ∈ Icc a b, 0 < ρ u) (hc : c ∈ Icc a b) :
    arcParam ρ c '' Icc a b = Icc (arcParam ρ c a) (arcParam ρ c b) :=
  (continuousOn_arcParam hρ hc).image_Icc_of_monotoneOn hab
    (strictMonoOn_arcParam hρ hpos hc).monotoneOn

/-- **The inverse of the arc-length parameter** on the compact interval `Icc a b`: the length `v`
names the unique point of `Icc a b` at (signed) distance `v` from the base point. -/
def arcParamInv (ρ : ℝ → ℝ) (c a b : ℝ) : ℝ → ℝ := Function.invFunOn (arcParam ρ c) (Icc a b)

section Inv

variable (hab : a ≤ b) (hρ : ContinuousOn ρ (Icc a b)) (hpos : ∀ u ∈ Icc a b, 0 < ρ u)
  (hc : c ∈ Icc a b)

include hab hρ hpos hc

omit hab in
/-- The inverse undoes the arc-length parameter on `Icc a b`. -/
theorem arcParamInv_arcParam {u : ℝ} (hu : u ∈ Icc a b) :
    arcParamInv ρ c a b (arcParam ρ c u) = u :=
  (strictMonoOn_arcParam hρ hpos hc).injOn.leftInvOn_invFunOn hu

/-- The inverse of the arc-length parameter maps `Icc (σ a) (σ b)` into `Icc a b`. -/
theorem mapsTo_arcParamInv :
    MapsTo (arcParamInv ρ c a b) (Icc (arcParam ρ c a) (arcParam ρ c b)) (Icc a b) := by
  rw [← image_arcParam hab hρ hpos hc]
  exact (surjOn_image _ _).mapsTo_invFunOn

/-- The arc-length parameter undoes its inverse on `Icc (σ a) (σ b)`. -/
theorem arcParam_arcParamInv {v : ℝ} (hv : v ∈ Icc (arcParam ρ c a) (arcParam ρ c b)) :
    arcParam ρ c (arcParamInv ρ c a b v) = v := by
  rw [← image_arcParam hab hρ hpos hc] at hv
  exact (surjOn_image _ _).rightInvOn_invFunOn hv

/-- The inverse of the arc-length parameter is strictly increasing. -/
theorem strictMonoOn_arcParamInv :
    StrictMonoOn (arcParamInv ρ c a b) (Icc (arcParam ρ c a) (arcParam ρ c b)) := by
  intro v hv w hw hvw
  refine ((strictMonoOn_arcParam hρ hpos hc).lt_iff_lt (mapsTo_arcParamInv hab hρ hpos hc hv)
    (mapsTo_arcParamInv hab hρ hpos hc hw)).1 ?_
  rw [arcParam_arcParamInv hab hρ hpos hc hv, arcParam_arcParamInv hab hρ hpos hc hw]
  exact hvw

/-- **The inverse of the arc-length parameter is continuous**, endpoints included: it inverts a
continuous injection on the *compact* set `Icc a b`. -/
theorem continuousOn_arcParamInv :
    ContinuousOn (arcParamInv ρ c a b) (Icc (arcParam ρ c a) (arcParam ρ c b)) := by
  rw [← image_arcParam hab hρ hpos hc]
  exact continuousOn_leftInvOn_of_isCompact isCompact_Icc (continuousOn_arcParam hρ hc)
    fun _ hu => arcParamInv_arcParam hρ hpos hc hu

/-- **The inverse of the arc-length parameter is differentiable with derivative `1/ρ`**, at every
point of `Icc (σ a) (σ b)` including the two endpoints, where the derivative is one-sided.  This is
`hasDerivWithinAt_of_leftInvOn` fed with the fundamental theorem of calculus. -/
theorem hasDerivWithinAt_arcParamInv {v : ℝ} (hv : v ∈ Icc (arcParam ρ c a) (arcParam ρ c b)) :
    HasDerivWithinAt (arcParamInv ρ c a b) (ρ (arcParamInv ρ c a b v))⁻¹
      (Icc (arcParam ρ c a) (arcParam ρ c b)) v :=
  hasDerivWithinAt_of_leftInvOn hv (mapsTo_arcParamInv hab hρ hpos hc)
    (fun _ hw => arcParam_arcParamInv hab hρ hpos hc hw)
    (continuousOn_arcParamInv hab hρ hpos hc v hv)
    (hasDerivWithinAt_arcParam hρ hc (mapsTo_arcParamInv hab hρ hpos hc hv))
    (hpos _ (mapsTo_arcParamInv hab hρ hpos hc hv)).ne'

end Inv

/-- The two ends of the arc-length image of a nondegenerate interval are distinct. -/
theorem arcParam_lt_arcParam (hab : a < b) (hρ : ContinuousOn ρ (Icc a b))
    (hpos : ∀ u ∈ Icc a b, 0 < ρ u) (hc : c ∈ Icc a b) : arcParam ρ c a < arcParam ρ c b :=
  strictMonoOn_arcParam hρ hpos hc (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab

/-- The derivative of the inverse of the arc-length parameter, within `Icc (σ a) (σ b)`. -/
theorem derivWithin_arcParamInv (hab : a < b) (hρ : ContinuousOn ρ (Icc a b))
    (hpos : ∀ u ∈ Icc a b, 0 < ρ u) (hc : c ∈ Icc a b) {v : ℝ}
    (hv : v ∈ Icc (arcParam ρ c a) (arcParam ρ c b)) :
    derivWithin (arcParamInv ρ c a b) (Icc (arcParam ρ c a) (arcParam ρ c b)) v =
      (ρ (arcParamInv ρ c a b v))⁻¹ :=
  (hasDerivWithinAt_arcParamInv hab.le hρ hpos hc hv).derivWithin
    (uniqueDiffOn_Icc (arcParam_lt_arcParam hab hρ hpos hc) v hv)

/-- **The inverse of the arc-length parameter is `C^∞`**, endpoints included.  This is the bootstrap
the plan prescribes: the inverse is continuous, hence `C⁰`; and if it is `Cᵏ` then its derivative
`(ρ ∘ g)⁻¹` is `Cᵏ` -- because `ρ` is `C^∞` and nowhere zero on `Icc a b` -- so the inverse is
`Cᵏ⁺¹`.  Unique differentiability of `Icc (σ a) (σ b)`, which is where the endpoints are handled, is
what lets `contDiffOn_succ_iff_derivWithin` be used. -/
theorem contDiffOn_arcParamInv (hab : a < b) (hρ : ContDiffOn ℝ ∞ ρ (Icc a b))
    (hpos : ∀ u ∈ Icc a b, 0 < ρ u) (hc : c ∈ Icc a b) :
    ContDiffOn ℝ ∞ (arcParamInv ρ c a b) (Icc (arcParam ρ c a) (arcParam ρ c b)) := by
  have hρc : ContinuousOn ρ (Icc a b) := hρ.continuousOn
  have huniq : UniqueDiffOn ℝ (Icc (arcParam ρ c a) (arcParam ρ c b)) :=
    uniqueDiffOn_Icc (arcParam_lt_arcParam hab hρc hpos hc)
  have hmaps := mapsTo_arcParamInv hab.le hρc hpos hc
  have hdiff : DifferentiableOn ℝ (arcParamInv ρ c a b)
      (Icc (arcParam ρ c a) (arcParam ρ c b)) := fun _ hv =>
    (hasDerivWithinAt_arcParamInv hab.le hρc hpos hc hv).differentiableWithinAt
  have key : ∀ k : ℕ, ContDiffOn ℝ (k : WithTop ℕ∞) (arcParamInv ρ c a b)
      (Icc (arcParam ρ c a) (arcParam ρ c b)) := by
    intro k
    induction k with
    | zero =>
        rw [Nat.cast_zero, contDiffOn_zero]
        exact continuousOn_arcParamInv hab.le hρc hpos hc
    | succ k ih =>
        have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
        rw [hcast, contDiffOn_succ_iff_derivWithin huniq]
        refine ⟨hdiff, fun hω => absurd hω (by simp), ?_⟩
        refine ContDiffOn.congr ?_ fun v hv => derivWithin_arcParamInv hab hρc hpos hc hv
        exact ((hρ.of_le (mod_cast le_top)).comp ih hmaps).inv fun v hv => (hpos _ (hmaps hv)).ne'
  exact contDiffOn_infty.2 key

end ArcParam

/-! ## Unit-speed arcs -/

section UnitSpeed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

/-- **The arc length along a smooth arc**, measured from the parameter `0`: the primitive of the
length element read in the arc's own parameter. -/
def arcLength (L : LengthElement I n M) (A : SmoothArc I n M) : ℝ → ℝ :=
  arcParam (L.fn A.toRealChart) 0

/-- Arc length vanishes at the base parameter `0`. -/
@[simp] theorem arcLength_zero (L : LengthElement I n M) (A : SmoothArc I n M) :
    arcLength L A 0 = 0 := arcParam_self _ _

/-- The length element read in the arc's parameter is positive on the arc's target. -/
theorem lengthElement_pos (L : LengthElement I n M) (A : SmoothArc I n M) {u : ℝ}
    (hu : u ∈ A.target) : 0 < L.fn A.toRealChart u := L.pos A.toRealChart u hu

/-- The length element read in the arc's parameter is `Cⁿ` on the arc's target. -/
theorem lengthElement_contDiffOn (L : LengthElement I n M) (A : SmoothArc I n M) :
    ContDiffOn ℝ n (L.fn A.toRealChart) A.target := L.contDiffOn A.toRealChart

/-- Arc length is strictly increasing along a compact interval inside the arc's target. -/
theorem strictMonoOn_arcLength (L : LengthElement I n M) (A : SmoothArc I n M) {a b : ℝ}
    (h0 : (0 : ℝ) ∈ Icc a b) (hsub : Icc a b ⊆ A.target) :
    StrictMonoOn (arcLength L A) (Icc a b) :=
  strictMonoOn_arcParam ((lengthElement_contDiffOn L A).mono hsub).continuousOn
    (fun _ hu => lengthElement_pos L A (hsub hu)) h0

/-- Arc length is continuous along a compact interval inside the arc's target. -/
theorem continuousOn_arcLength (L : LengthElement I n M) (A : SmoothArc I n M) {a b : ℝ}
    (h0 : (0 : ℝ) ∈ Icc a b) (hsub : Icc a b ⊆ A.target) :
    ContinuousOn (arcLength L A) (Icc a b) :=
  continuousOn_arcParam ((lengthElement_contDiffOn L A).mono hsub).continuousOn h0

/-- **A smooth arc has unit speed** for the length element `L` when `L`, read in the arc's own
parameter, is identically `1`.  Equivalently the arc is parametrized by arc length: the length of
the stretch between two parameters is their difference.  This is the property that makes the
transition between two arcs affine, which is what Stage 5 needs. -/
def UnitSpeed (L : LengthElement I n M) (A : SmoothArc I n M) : Prop :=
  ∀ u ∈ A.target, L.fn A.toRealChart u = 1

/-- **The arc-length reparametrization of a smooth arc.**  Let `A` be a smooth arc, let `Icc a b` be
a compact interval inside its target containing `0`, and let `J ⊆ Icc a b` be a *window*: a set
whose preimage in `M` is open and whose arc-length image is a legitimate arc target (order-connected
with at least two points).  Then the reparametrized arc -- coordinate `σ ∘ A.toFun` with
`σ = arcLength L A`, source `A.source ∩ A.toFun ⁻¹' J`, target `σ '' J` -- is a smooth arc, and it
has **unit speed**.

Unit speed is the cocycle rule of the length element applied to the pair (new arc, old arc): the
transition from the new parameter back to the old one is the inverse `g` of `σ`, whose derivative is
`1/ρ`, so the new density is `ρ · |1/ρ| = 1`.  All of this holds at an endpoint of a half-open
target, which is the point of the stage.

The hypothesis `hbdry` transports the arc's boundary law to the window; the two existence theorems
below verify it in a few lines each, because in the two shapes that occur the window's arc-length
image has the same "endpoint attained or not" pattern as the original target. -/
theorem exists_reparam (L : LengthElement I ∞ M) (A : SmoothArc I ∞ M) {a b : ℝ} (hab : a < b)
    (h0 : (0 : ℝ) ∈ Icc a b) (hsub : Icc a b ⊆ A.target) {J : Set ℝ} (hJsub : J ⊆ Icc a b)
    (hJopen : IsOpen (A.source ∩ A.toFun ⁻¹' J))
    (hJoc : (arcLength L A '' J).OrdConnected) (hJnt : (arcLength L A '' J).Nontrivial)
    (hbdry : ∀ x ∈ A.source, A.toFun x ∈ J →
      (x ∈ I.boundary M ↔ arcLength L A (A.toFun x) ∉ interior (arcLength L A '' J))) :
    ∃ A₁ : SmoothArc I ∞ M, A₁.source = A.source ∩ A.toFun ⁻¹' J ∧
      A₁.target = arcLength L A '' J ∧ (∀ x, A₁.toFun x = arcLength L A (A.toFun x)) ∧
      UnitSpeed L A₁ := by
  set ρ : ℝ → ℝ := L.fn A.toRealChart with hρdef
  set σ : ℝ → ℝ := arcLength L A with hσdef
  set g : ℝ → ℝ := arcParamInv ρ 0 a b with hgdef
  -- the density is positive and `C^∞` on the compact interval
  have hpos : ∀ u ∈ Icc a b, 0 < ρ u := fun u hu => lengthElement_pos L A (hsub hu)
  have hρsm : ContDiffOn ℝ ∞ ρ (Icc a b) := (lengthElement_contDiffOn L A).mono hsub
  have hρc : ContinuousOn ρ (Icc a b) := hρsm.continuousOn
  -- arc length on the compact interval
  have hσmono : StrictMonoOn σ (Icc a b) := strictMonoOn_arcParam hρc hpos h0
  have hσc : ContinuousOn σ (Icc a b) := continuousOn_arcParam hρc h0
  have hσsm : ContDiffOn ℝ ∞ σ (Icc a b) := contDiffOn_arcParam hab hρsm h0
  have hσimg : σ '' Icc a b = Icc (σ a) (σ b) := image_arcParam hab.le hρc hpos h0
  have hJimg : σ '' J ⊆ Icc (σ a) (σ b) := by rw [← hσimg]; exact Set.image_mono hJsub
  -- the inverse of arc length
  have hginv : ∀ u ∈ Icc a b, g (σ u) = u := fun _ hu => arcParamInv_arcParam hρc hpos h0 hu
  have hgmaps : MapsTo g (Icc (σ a) (σ b)) (Icc a b) := mapsTo_arcParamInv hab.le hρc hpos h0
  have hgσ : ∀ v ∈ Icc (σ a) (σ b), σ (g v) = v := fun _ hv =>
    arcParam_arcParamInv hab.le hρc hpos h0 hv
  have hgc : ContinuousOn g (Icc (σ a) (σ b)) := continuousOn_arcParamInv hab.le hρc hpos h0
  have hgsm : ContDiffOn ℝ ∞ g (Icc (σ a) (σ b)) := contDiffOn_arcParamInv hab hρsm hpos h0
  -- the inverse carries the new target into the window
  have hgJ : ∀ v ∈ σ '' J, g v ∈ J := by
    rintro v ⟨u, hu, rfl⟩
    rwa [hginv u (hJsub hu)]
  have hgA : ∀ v ∈ σ '' J, g v ∈ A.target := fun v hv => hsub (hJsub (hgJ v hv))
  have huniq : UniqueDiffOn ℝ (σ '' J) := uniqueDiffOn_of_ordConnected_nontrivial hJoc hJnt
  -- the reparametrized arc, named so that its fields can be referred to
  obtain ⟨A₁, hA₁src, hA₁tgt, hA₁to, hA₁inv⟩ :
      ∃ A₁ : SmoothArc I ∞ M, A₁.source = A.source ∩ A.toFun ⁻¹' J ∧ A₁.target = σ '' J ∧
        (∀ x, A₁.toFun x = σ (A.toFun x)) ∧ ∀ v, A₁.invFun v = A.invFun (g v) :=
    ⟨{ toFun := fun x => σ (A.toFun x)
       invFun := fun v => A.invFun (g v)
       source := A.source ∩ A.toFun ⁻¹' J
       target := σ '' J
       map_source' := fun x hx => ⟨A.toFun x, hx.2, rfl⟩
       map_target' := fun v hv => ⟨A.map_target (hgA v hv), by
         change A.toFun (A.invFun (g v)) ∈ J
         rw [A.right_inv (hgA v hv)]
         exact hgJ v hv⟩
       left_inv' := fun x hx => by rw [hginv _ (hJsub hx.2), A.left_inv hx.1]
       right_inv' := fun v hv => by
         rw [A.right_inv (hgA v hv)]; exact hgσ v (hJimg hv)
       open_source := hJopen
       ordConnected_target := hJoc
       nontrivial_target := hJnt
       bddAbove_target := BddAbove.mono hJimg bddAbove_Icc
       bddBelow_target := BddBelow.mono hJimg bddBelow_Icc
       continuousOn_toFun :=
         hσc.comp (A.continuousOn_toFun.mono inter_subset_left) fun x hx => hJsub hx.2
       continuousOn_invFun := A.continuousOn_invFun.comp (hgc.mono hJimg) hgA
       bdry := fun x hx => hbdry x hx.1 hx.2
       contMDiffOn_toFun := (contMDiffOn_iff_contDiffOn.2 hσsm).comp
         (A.contMDiffOn_toFun.mono inter_subset_left) fun x hx => hJsub hx.2
       contMDiffOn_invFun := A.contMDiffOn_invFun.comp
         (contMDiffOn_iff_contDiffOn.2 (hgsm.mono hJimg)) hgA }, rfl, rfl, fun _ => rfl,
      fun _ => rfl⟩
  refine ⟨A₁, hA₁src, hA₁tgt, hA₁to, ?_⟩
  -- unit speed, by the cocycle rule of the length element
  intro v hv
  have hvJ : v ∈ σ '' J := hA₁tgt ▸ hv
  have hvsrc : A₁.invFun v ∈ A.source := by
    rw [hA₁inv]; exact A.map_target (hgA v hvJ)
  rw [L.cocycle A₁.toRealChart A.toRealChart v hv hvsrc]
  simp only [SmoothArc.toRealChart_toFun, SmoothArc.toRealChart_invFun]
  have hfst : A.toFun (A₁.invFun v) = g v := by
    rw [hA₁inv]; exact A.right_inv (hgA v hvJ)
  -- the transition back to the old parameter is the inverse of arc length
  have hEqOn : ∀ s ∈ A₁.target, A.toFun (A₁.invFun s) = g s := by
    intro s hs
    rw [hA₁inv]
    exact A.right_inv (hgA s (hA₁tgt ▸ hs))
  have hderiv : HasDerivWithinAt g (ρ (g v))⁻¹ A₁.target v :=
    (hasDerivWithinAt_arcParamInv hab.le hρc hpos h0 (hJimg hvJ)).mono (hA₁tgt ▸ hJimg)
  have htrans : transDeriv A₁.toRealChart A.toRealChart v = (ρ (g v))⁻¹ := by
    change derivWithin (fun s => A.toFun (A₁.invFun s)) A₁.target v = (ρ (g v))⁻¹
    rw [derivWithin_congr hEqOn (hEqOn v hv)]
    exact hderiv.derivWithin (uniqueDiffOn_target A₁.toArc v hv)
  rw [hfst, htrans, abs_inv, abs_of_pos (hpos _ (hJsub (hgJ v hvJ)))]
  exact mul_inv_cancel₀ (hpos _ (hJsub (hgJ v hvJ))).ne'

end UnitSpeed

/-! ## Existence of unit-speed arcs -/

section Existence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

include hE

/-- **A unit-speed smooth arc starting at a boundary point.**  Every boundary point `p` of a `C^∞`
one-manifold lies in the source of a smooth arc of **unit speed** whose target is the half-open
interval `Ico 0 ε` and which sends `p` to `0`.  This is the unit-speed refinement of Stage 1's
`exists_smoothArc_of_mem_boundary`, and it is Milnor's Lemma 1.1 at a boundary point.

The window is `J = Ico 0 (ε/2)`, cut out of the compact interval `Icc 0 (ε/2)` inside the arc's
target `Ico 0 ε`; its arc-length image is `Ico 0 (σ (ε/2))`, again half-open, so the boundary law
transports: both sides say that the old parameter is `0`.

Hypotheses: `Module.finrank ℝ E = 1`, `IsManifold I ∞ M`, and a length element, which Stage 3
produces from Hausdorffness and σ-compactness.  No Hausdorffness or compactness is used here. -/
theorem exists_unitSpeed_of_mem_boundary (L : LengthElement I ∞ M) {p : M}
    (hp : p ∈ I.boundary M) :
    ∃ (A : SmoothArc I ∞ M) (ε : ℝ), 0 < ε ∧ p ∈ A.source ∧ A.toFun p = 0 ∧
      A.target = Ico 0 ε ∧ UnitSpeed L A := by
  obtain ⟨A, ε, hε, hpA, hp0, htgt⟩ :=
    exists_smoothArc_of_mem_boundary I (n := ∞) hE (by simp) hp
  have hab : (0 : ℝ) < ε / 2 := by positivity
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (ε / 2) := ⟨le_rfl, hab.le⟩
  have hsub : Icc (0 : ℝ) (ε / 2) ⊆ A.target := by
    rw [htgt]; exact fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  set σ : ℝ → ℝ := arcLength L A with hσdef
  have hmono : StrictMonoOn σ (Icc (0 : ℝ) (ε / 2)) := strictMonoOn_arcLength L A h0 hsub
  have hcont : ContinuousOn σ (Icc (0 : ℝ) (ε / 2)) := continuousOn_arcLength L A h0 hsub
  set δ : ℝ := σ (ε / 2) with hδdef
  have hσ0 : σ 0 = 0 := arcLength_zero L A
  have hδpos : 0 < δ := by
    have := hmono h0 (right_mem_Icc.2 hab.le) hab
    rwa [hσ0] at this
  -- the window and its arc-length image
  have hJimg : σ '' Ico (0 : ℝ) (ε / 2) = Ico 0 δ := by
    rw [hcont.image_Ico_of_strictMonoOn hab.le hmono, hσ0]
  have hJsub : Ico (0 : ℝ) (ε / 2) ⊆ Icc (0 : ℝ) (ε / 2) := Ico_subset_Icc_self
  -- the preimage of the window is open, because the arc's coordinate is nonnegative
  have hpre : A.source ∩ A.toFun ⁻¹' Ico (0 : ℝ) (ε / 2) =
      A.source ∩ A.toFun ⁻¹' Iio (ε / 2) := by
    ext x
    refine ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, ?_, hx.2⟩⟩
    have := A.map_source hx.1
    rw [htgt] at this
    exact this.1
  have hJopen : IsOpen (A.source ∩ A.toFun ⁻¹' Ico (0 : ℝ) (ε / 2)) := by
    rw [hpre]
    exact A.continuousOn_toFun.isOpen_inter_preimage A.open_source isOpen_Iio
  -- the boundary law: on both sides, the point is a boundary point iff its old parameter is `0`
  have hbdry : ∀ x ∈ A.source, A.toFun x ∈ Ico (0 : ℝ) (ε / 2) →
      (x ∈ I.boundary M ↔ σ (A.toFun x) ∉ interior (σ '' Ico (0 : ℝ) (ε / 2))) := by
    intro x hx hxJ
    have hxIcc : A.toFun x ∈ Icc (0 : ℝ) (ε / 2) := hJsub hxJ
    have hleft : x ∈ I.boundary M ↔ A.toFun x = 0 := by
      rw [A.bdry x hx, htgt, interior_Ico]
      refine ⟨fun h => ?_, fun h => by rw [h]; simp⟩
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at h
      rcases h with h | h
      · exact le_antisymm h hxJ.1
      · exact absurd (lt_of_lt_of_le hxJ.2 (by linarith)) (not_lt.2 h)
    have hright : σ (A.toFun x) ∉ interior (σ '' Ico (0 : ℝ) (ε / 2)) ↔ A.toFun x = 0 := by
      rw [hJimg, interior_Ico]
      have hmem : σ (A.toFun x) ∈ Ico 0 δ := by rw [← hJimg]; exact ⟨A.toFun x, hxJ, rfl⟩
      refine ⟨fun h => ?_, fun h => by rw [h, hσ0]; simp⟩
      rw [mem_Ioo, not_and_or, not_lt, not_lt] at h
      rcases h with h | h
      · have : σ (A.toFun x) = σ 0 := by rw [hσ0]; exact le_antisymm h hmem.1
        exact hmono.injOn hxIcc h0 this
      · exact absurd hmem.2 (not_lt.2 h)
    rw [hleft, hright]
  obtain ⟨A₁, hsrc, htgt₁, htofun, hunit⟩ :=
    exists_reparam L A hab h0 hsub hJsub hJopen (by rw [hJimg]; exact ordConnected_Ico)
      (by rw [hJimg]; exact ⟨0, ⟨le_rfl, hδpos⟩, δ / 2, ⟨by positivity, by linarith⟩,
        by intro h; linarith⟩) hbdry
  refine ⟨A₁, δ, hδpos, ?_, ?_, ?_, hunit⟩
  · rw [hsrc]
    refine ⟨hpA, ?_⟩
    change A.toFun p ∈ Ico (0 : ℝ) (ε / 2)
    rw [hp0]
    exact ⟨le_rfl, hab⟩
  · rw [htofun, hp0]
    exact arcLength_zero L A
  · rw [htgt₁, hJimg]

/-- **A unit-speed smooth arc around an interior point.**  Every point `y` of a `C^∞` one-manifold
that is *not* a boundary point lies in the source of a smooth arc of **unit speed** whose target is
the open interval `Ioo (-ε) ε` and which sends `y` to `0`.  This is the unit-speed refinement of
Stage 1's `exists_smoothArc_of_notMem_boundary`.

Here the window has to be chosen in the *new* parameter, because arc length need not be symmetric:
with `Icc a b = Icc (-ε/2) (ε/2)` inside the arc's target and `δ = min (σ b) (-(σ a))`, the window
is `J = Ioo a b ∩ σ ⁻¹' Ioo (-δ) δ`, whose arc-length image is exactly `Ioo (-δ) δ`.  The boundary
law is vacuous on both sides: the arc's source has no boundary point, and the new target is open.

Hypotheses: `Module.finrank ℝ E = 1`, `IsManifold I ∞ M`, and a length element.  No Hausdorffness or
compactness is used here. -/
theorem exists_unitSpeed_of_notMem_boundary (L : LengthElement I ∞ M) {y : M}
    (hy : y ∉ I.boundary M) :
    ∃ (A : SmoothArc I ∞ M) (ε : ℝ), 0 < ε ∧ y ∈ A.source ∧ A.toFun y = 0 ∧
      A.target = Ioo (-ε) ε ∧ UnitSpeed L A := by
  obtain ⟨A, ε, hε, hyA, hy0, htgt, -, hsrcint⟩ :=
    exists_smoothArc_of_notMem_boundary I (n := ∞) hE (by simp) hy
  have hab : -(ε / 2) < ε / 2 := by linarith
  have h0 : (0 : ℝ) ∈ Icc (-(ε / 2)) (ε / 2) := ⟨by linarith, by linarith⟩
  have hsub : Icc (-(ε / 2)) (ε / 2) ⊆ A.target := by
    rw [htgt]; exact fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set σ : ℝ → ℝ := arcLength L A with hσdef
  have hmono : StrictMonoOn σ (Icc (-(ε / 2)) (ε / 2)) := strictMonoOn_arcLength L A h0 hsub
  have hcont : ContinuousOn σ (Icc (-(ε / 2)) (ε / 2)) := continuousOn_arcLength L A h0 hsub
  have hσ0 : σ 0 = 0 := arcLength_zero L A
  have hlow : σ (-(ε / 2)) < 0 := by
    have := hmono (left_mem_Icc.2 hab.le) h0 (by linarith)
    rwa [hσ0] at this
  have hhigh : 0 < σ (ε / 2) := by
    have := hmono h0 (right_mem_Icc.2 hab.le) (by linarith)
    rwa [hσ0] at this
  set δ : ℝ := min (σ (ε / 2)) (-(σ (-(ε / 2)))) with hδdef
  have hδpos : 0 < δ := lt_min hhigh (by linarith)
  have hδsub : Ioo (-δ) δ ⊆ Ioo (σ (-(ε / 2))) (σ (ε / 2)) := by
    intro v hv
    have h1 : δ ≤ -(σ (-(ε / 2))) := min_le_right _ _
    have h2 : δ ≤ σ (ε / 2) := min_le_left _ _
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  -- the window, cut out in the new parameter
  set J : Set ℝ := Ioo (-(ε / 2)) (ε / 2) ∩ σ ⁻¹' Ioo (-δ) δ with hJdef
  have hJsub : J ⊆ Icc (-(ε / 2)) (ε / 2) := fun t ht => Ioo_subset_Icc_self ht.1
  have hJimg : σ '' J = Ioo (-δ) δ := by
    refine Subset.antisymm (fun v hv => by obtain ⟨u, hu, rfl⟩ := hv; exact hu.2) ?_
    intro v hv
    have hvimg : v ∈ σ '' Ioo (-(ε / 2)) (ε / 2) := by
      rw [hcont.image_Ioo_of_strictMonoOn hab.le hmono]
      exact hδsub hv
    obtain ⟨u, hu, rfl⟩ := hvimg
    exact ⟨u, ⟨hu, hv⟩, rfl⟩
  -- the preimage of the window is open
  have hUopen : IsOpen (A.source ∩ A.toFun ⁻¹' Ioo (-(ε / 2)) (ε / 2)) :=
    A.continuousOn_toFun.isOpen_inter_preimage A.open_source isOpen_Ioo
  have hpre : A.source ∩ A.toFun ⁻¹' J =
      (A.source ∩ A.toFun ⁻¹' Ioo (-(ε / 2)) (ε / 2)) ∩
        (fun x => σ (A.toFun x)) ⁻¹' Ioo (-δ) δ := by
    ext x
    exact ⟨fun hx => ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩, fun hx => ⟨hx.1.1, hx.1.2, hx.2⟩⟩
  have hJopen : IsOpen (A.source ∩ A.toFun ⁻¹' J) := by
    rw [hpre]
    refine ContinuousOn.isOpen_inter_preimage ?_ hUopen isOpen_Ioo
    exact hcont.comp (A.continuousOn_toFun.mono inter_subset_left)
      fun x hx => Ioo_subset_Icc_self hx.2
  -- the boundary law is vacuous on both sides
  have hbdry : ∀ x ∈ A.source, A.toFun x ∈ J →
      (x ∈ I.boundary M ↔ σ (A.toFun x) ∉ interior (σ '' J)) := by
    intro x hx hxJ
    have hxnot : x ∉ I.boundary M := by
      rw [← I.compl_boundary] at hsrcint
      exact hsrcint hx
    have hmem : σ (A.toFun x) ∈ interior (σ '' J) := by
      rw [hJimg, interior_Ioo]
      exact hxJ.2
    exact iff_of_false hxnot (not_not_intro hmem)
  obtain ⟨A₁, hsrc, htgt₁, htofun, hunit⟩ :=
    exists_reparam L A hab h0 hsub hJsub hJopen (by rw [hJimg]; exact ordConnected_Ioo)
      (by rw [hJimg]; exact ⟨0, ⟨by linarith, hδpos⟩, δ / 2, ⟨by linarith, by linarith⟩,
        by intro h; linarith⟩) hbdry
  refine ⟨A₁, δ, hδpos, ?_, ?_, ?_, hunit⟩
  · rw [hsrc]
    refine ⟨hyA, ?_, ?_⟩
    · show A.toFun y ∈ Ioo (-(ε / 2)) (ε / 2)
      rw [hy0]
      exact ⟨by linarith, by linarith⟩
    · change σ (A.toFun y) ∈ Ioo (-δ) δ
      rw [hy0, hσ0]
      exact ⟨by linarith, hδpos⟩
  · rw [htofun, hy0]
    exact arcLength_zero L A
  · rw [htgt₁, hJimg]

/-- **Milnor's Lemma 1.1 (p. 54): every point of a one-manifold lies on a unit-speed arc.**  For a
`C^∞` one-manifold with a length element, every point `p` lies in the source of a smooth arc of unit
speed sending `p` to `0`, whose target is `Ico 0 ε` if `p` is a boundary point and `Ioo (-ε) ε`
otherwise.

This is the conclusion Stage 4 exists to produce, and the input to Stage 5: two unit-speed arcs have
`|derivative| = 1` transition, hence affine transition, which is what makes Milnor's extension
construction a genuine extension.

Hypotheses: `Module.finrank ℝ E = 1`, `IsManifold I ∞ M`, and a length element -- which Stage 3's
`nonempty_lengthElement` supplies for any Hausdorff σ-compact one-manifold, with or without
boundary. -/
theorem exists_unitSpeed (L : LengthElement I ∞ M) (p : M) :
    ∃ (A : SmoothArc I ∞ M) (ε : ℝ), 0 < ε ∧ p ∈ A.source ∧ A.toFun p = 0 ∧
      (A.target = Ico 0 ε ∨ A.target = Ioo (-ε) ε) ∧ UnitSpeed L A := by
  by_cases hp : p ∈ I.boundary M
  · obtain ⟨A, ε, hε, h1, h2, h3, h4⟩ := exists_unitSpeed_of_mem_boundary I hE L hp
    exact ⟨A, ε, hε, h1, h2, Or.inl h3, h4⟩
  · obtain ⟨A, ε, hε, h1, h2, h3, h4⟩ := exists_unitSpeed_of_notMem_boundary I hE L hp
    exact ⟨A, ε, hε, h1, h2, Or.inr h3, h4⟩

end Existence

end Milnor.OneManifold.Smooth
