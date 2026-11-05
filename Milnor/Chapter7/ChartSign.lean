import Milnor.Chapter7.MoveAux
import Milnor.Chapter7.CancelMap
import Milnor.Chapter7.PontFrame
import Milnor.Chapter7.OrientTransport
import Milnor.Chapter6.LevelMap

/-!
# The chart sign of a frame (Milnor §7, p. 50)

**Stage 1 of `Exposition/PlanMod2.md`**, the formalization of Milnor's remark at the end of §7
(book p. 50): *for a connected non-orientable manifold, two smooth maps `M → Sᵐ` are smoothly
homotopic if and only if they have the same degree modulo 2.*

The point of this file.  The existing theory of framed `0`-manifolds attaches to a frame `v` at a
point `x` the sign `frameSign hM oM v x` (`Chapter7/Hopf0.lean`), which is defined relative to an
orientation `oM` of the whole of `M`.  On a non-orientable manifold there is no such `oM`, so the
local lemmas of the chapter (moving a point inside a chart ball, cancelling two points, adding a
point) have to be restated with a sign that mentions no orientation.  That sign is the **chart
sign**: read the frame in one chart and take the sign of the determinant.  Precisely,

* `chartSign hM x_c x v` is the sign of the determinant of `chartFrameCLM hM x_c x v`, the frame
  `v` at `x` expressed in the chart centred at `x_c` (`Chapter7/MoveAux.lean`);
* `selfSign hM x v = chartSign hM x x v` reads the frame in the chart at `x` itself;
* `jacSign hM x_c x` is the sign of the determinant of the derivative at `x` of the chart centred
  at `x_c`.

None of the three mentions an orientation of `M`.  They are related by
`chartSign = jacSign * selfSign` (`chartSign_eq_jacSign_mul_selfSign`), with `jacSign hM x x = 1`,
and each is `1` or `-1` (never `0`) as soon as the frame is tangent and independent and the point
lies in the chart's source — that last is `Milnor.Framed.chartFrameCLM_bijective`
(`Chapter7/MoveAux.lean`), which needs nothing but the membership `x ∈ source`, invertibility of a
chart derivative being `Milnor.bijective_mfd_extChartAt`.

**The replacement of the orientation.**  The bridge to the oriented theory is
`frameSign_eq_orEps_mul_selfSign`:
`frameSign hM oM v x = orEps hM oM x * selfSign hM x v`,
where `orEps hM oM x` is the sign of the identity of `ℝᵐ` read against `stdOr m` and `oM.or x`.
*The sign of a frame relative to an orientation of the manifold is thus the sign of the determinant
of the frame read in one chart, times a factor depending only on the point* — and the chart sign
mentions no orientation at all.  This is what lets the cancellation machinery of the chapter run on
a non-orientable manifold: the only thing the local proofs ever compare is a product of two such
signs, and the point-dependent factor cancels.  At the level of a whole chart ball the same holds
with the hub's factor: under the old positivity hypothesis
`hpos : orSign (oM.or x) (oM.or x_c) dφ_{x_c}|_x = 1` we get
`frameSign hM oM v x = orEps hM oM x_c * chartSign hM x_c x v`
(`frameSign_eq_orEps_hub_mul_chartSign`), so equality of frame signs at two points of such a ball
is exactly equality of their chart signs relative to the hub
(`frameSign_eq_iff_chartSign_eq`).  Every oriented statement is therefore re-derivable from its
chart-sign form; `exists_frame_of_frameSign` is the demonstration, re-proving the oriented
`Milnor.Framed.exists_frame_of_sign` of `Chapter7/Reach.lean` from its sign-free version
`exists_frame_of_selfSign`.

The two other results of the stage are sign-free replacements of oriented lemmas:

* `exists_frame_of_selfSign`: at *every* point of `M` there are frames of both chart signs — no
  orientation, and no case split on a global reference sign;
* `exists_frame_transport`: given a frame at `x` and a second point `y` in the source of the same
  chart, a frame at `y` which is *the same frame read in that chart*, hence has the same chart
  sign.  It is built from the inverse of the chart derivative at `y`, which
  `Milnor.isInvertible_mfd_extChartAt` supplies with no hypothesis beyond `y ∈ source`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M)

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "EK" => EuclideanSpace ℝ (Fin (K + 1))

/-! ### The three signs -/

/-- **The chart sign of a frame.**  The sign of the determinant of the frame `v` at `x` read in the
chart centred at `x_c`, that is of `chartFrameCLM hM x_c x v`, the composite of `basisCLM` of the
chart coordinates of `v` with the derivative *at `x`* of `φ = extChartAt x_c`.  No orientation of
`M` occurs. -/
def chartSign (x_c x : M) (v : Fin m → EK) : ℤ :=
  sgn (LinearMap.det ((chartFrameCLM hM x_c x v : Em →L[ℝ] Em) : Em →ₗ[ℝ] Em))

/-- **The self sign of a frame**: its chart sign read in the chart at the point itself.  This is
the intrinsic, orientation-free substitute for `frameSign`. -/
def selfSign (x : M) (v : Fin m → EK) : ℤ := chartSign hM x x v

/-- **The Jacobian sign of a chart**: the sign of the determinant of the derivative at `x` of the
chart centred at `x_c`.  This is the `±1` cocycle through which chart signs at different hubs are
compared. -/
def jacSign (x_c x : M) : ℤ :=
  letI := hM.chartedSpace
  haveI := hM.isManifold
  sgn (LinearMap.det ((mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) x_c) x : Em →L[ℝ] Em) :
    Em →ₗ[ℝ] Em))

/-- **The orientation factor at a point.**  The sign of the identity of `ℝᵐ` read from the standard
orientation to the orientation `oM.or x`; it is `±1` and depends only on `x`, not on any frame.
It is the whole of the difference between `frameSign` and `selfSign`. -/
def orEps (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m) (x : M) : ℤ :=
  letI := hM.chartedSpace
  orSign (stdOr m) (oM.or x) (ContinuousLinearMap.id ℝ Em)

/-! ### Unfolding lemmas -/

/-- The definition of `chartFrameCLM`, spelled out. -/
theorem chartFrameCLM_eq (x_c x : M) (v : Fin m → EK) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    chartFrameCLM hM x_c x v = (mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) x_c) x).comp
      (basisCLM (fun i => chartCoord hM x (v i))) := rfl

/-- The chart sign is the sign of a determinant, by definition. -/
theorem chartSign_eq_sgn_det (x_c x : M) (v : Fin m → EK) :
    chartSign hM x_c x v =
      sgn (LinearMap.det ((chartFrameCLM hM x_c x v : Em →L[ℝ] Em) : Em →ₗ[ℝ] Em)) := rfl

/-- The self sign is the chart sign at the point itself, by definition. -/
theorem selfSign_eq_chartSign (x : M) (v : Fin m → EK) :
    selfSign hM x v = chartSign hM x x v := rfl

/-- The orientation factor is the sign of the identity, by definition. -/
theorem orEps_eq (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m) (x : M) :
    letI := hM.chartedSpace;
    orEps hM oM x = orSign (stdOr m) (oM.or x) (ContinuousLinearMap.id ℝ Em) := rfl

/-- The frame sign is the sign of the chart coordinates of the frame, by definition. -/
theorem frameSign_eq_orSign (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m)
    (v : Fin m → EK) (x : M) :
    letI := hM.chartedSpace;
    frameSign hM oM v x = orSign (stdOr m) (oM.or x) (basisCLM (fun i => chartCoord hM x (v i))) :=
  rfl

/-! ### The signs as values of `orSign`

Every `orSign` computation of the chapter transfers verbatim to the chart sign, because a sign
between *equal* orientations is the sign of a determinant (`orSign_self_eq_sgn_det`); the hub
orientation is simply taken to be `stdOr m`. -/

/-- The chart sign is the sign of `chartFrameCLM` from the standard orientation to itself. -/
theorem chartSign_eq_orSign (x_c x : M) (v : Fin m → EK) :
    chartSign hM x_c x v = orSign (stdOr m) (stdOr m) (chartFrameCLM hM x_c x v) :=
  (orSign_self_eq_sgn_det finrank_E (stdOr m) (chartFrameCLM hM x_c x v)).symm

/-- The Jacobian sign of a chart is the sign of its derivative between *any* orientation and
itself; the orientation cancels. -/
theorem jacSign_eq_orSign (a : Orientation ℝ Em (Fin m)) (x_c x : M) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    jacSign hM x_c x =
      orSign a a (mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) x_c) x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  exact (orSign_self_eq_sgn_det finrank_E a _).symm

/-- In the chart at the point itself the frame is read by `basisCLM` alone: the chart derivative
there is the identity. -/
theorem chartFrameCLM_self (x : M) (v : Fin m → EK) :
    chartFrameCLM hM x x v = basisCLM (fun i => chartCoord hM x (v i)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rw [chartFrameCLM_eq, mfd_extChartAt_self, ContinuousLinearMap.id_comp]

/-- The self sign is the sign of the determinant of the chart coordinates of the frame. -/
theorem selfSign_eq_sgn_det (x : M) (v : Fin m → EK) :
    selfSign hM x v = sgn (LinearMap.det
      ((basisCLM (fun i => chartCoord hM x (v i)) : Em →L[ℝ] Em) : Em →ₗ[ℝ] Em)) := by
  rw [selfSign_eq_chartSign, chartSign_eq_sgn_det, chartFrameCLM_self]

/-- The self sign as a value of `orSign` between two copies of the standard orientation. -/
theorem selfSign_eq_orSign (x : M) (v : Fin m → EK) :
    selfSign hM x v =
      orSign (stdOr m) (stdOr m) (basisCLM (fun i => chartCoord hM x (v i))) := by
  rw [selfSign_eq_chartSign, chartSign_eq_orSign, chartFrameCLM_self]

/-! ### The algebra of the three signs -/

/-- **The cocycle formula.**  The chart sign at the hub `x_c` is the self sign times the Jacobian
sign of the chart at the point: `chartSign = jacSign * selfSign`. -/
theorem chartSign_eq_jacSign_mul_selfSign (x_c x : M) (v : Fin m → EK) :
    chartSign hM x_c x v = jacSign hM x_c x * selfSign hM x v := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h := orSign_comp finrank_E finrank_E (stdOr m) (stdOr m) (stdOr m)
    (basisCLM (fun i => chartCoord hM x (v i)))
    (mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) x_c) x)
  rw [chartSign_eq_orSign, chartFrameCLM_eq, h, ← jacSign_eq_orSign hM (stdOr m) x_c x,
    ← selfSign_eq_orSign]

/-- The chart at `x` has Jacobian sign `1` at `x` itself. -/
theorem jacSign_self (x : M) : jacSign hM x x = 1 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rw [jacSign_eq_orSign hM (stdOr m) x x, mfd_extChartAt_self]
  exact orSign_id _

/-- The chart sign at the point itself is the self sign. -/
theorem chartSign_self (x : M) (v : Fin m → EK) : chartSign hM x x v = selfSign hM x v := rfl

/-! ### Values `±1` -/

/-- The Jacobian sign of a chart is `1` or `-1` at every point of its source. -/
theorem jacSign_mem {x_c x : M}
    (hx : letI := hM.chartedSpace; x ∈ (extChartAt 𝓘(ℝ, Em) x_c).source) :
    jacSign hM x_c x = 1 ∨ jacSign hM x_c x = -1 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rw [jacSign_eq_orSign hM (stdOr m) x_c x]
  exact orSign_eq_one_or_neg_one finrank_E finrank_E _ _ (bijective_mfd_extChartAt hx)

/-- The Jacobian sign of a chart is never `0` on its source. -/
theorem jacSign_ne_zero {x_c x : M}
    (hx : letI := hM.chartedSpace; x ∈ (extChartAt 𝓘(ℝ, Em) x_c).source) :
    jacSign hM x_c x ≠ 0 := by
  rcases jacSign_mem hM hx with h | h <;> rw [h] <;> decide

/-- The Jacobian sign of a chart squares to `1` on its source. -/
theorem jacSign_mul_self {x_c x : M}
    (hx : letI := hM.chartedSpace; x ∈ (extChartAt 𝓘(ℝ, Em) x_c).source) :
    jacSign hM x_c x * jacSign hM x_c x = 1 := by
  rcases jacSign_mem hM hx with h | h <;> rw [h] <;> decide

/-- **The self sign of a frame is never `0`**: an independent tangent frame has independent chart
coordinates. -/
theorem selfSign_ne_zero {x : M} {v : Fin m → EK} (hvT : ∀ i, v i ∈ tangentM hM x)
    (hv : LinearIndependent ℝ v) : selfSign hM x v ≠ 0 := by
  rw [selfSign_eq_orSign, orSign_ne_zero_iff finrank_E finrank_E]
  exact basisCLM_bijective (linearIndependent_chartCoord hM hvT hv)

/-- **The self sign of a frame is `1` or `-1`.** -/
theorem selfSign_mem {x : M} {v : Fin m → EK} (hvT : ∀ i, v i ∈ tangentM hM x)
    (hv : LinearIndependent ℝ v) : selfSign hM x v = 1 ∨ selfSign hM x v = -1 := by
  rw [selfSign_eq_orSign]
  exact orSign_eq_one_or_neg_one finrank_E finrank_E _ _
    (basisCLM_bijective (linearIndependent_chartCoord hM hvT hv))

/-- The self sign squares to `1`. -/
theorem selfSign_mul_self {x : M} {v : Fin m → EK} (hvT : ∀ i, v i ∈ tangentM hM x)
    (hv : LinearIndependent ℝ v) : selfSign hM x v * selfSign hM x v = 1 := by
  rcases selfSign_mem hM hvT hv with h | h <;> rw [h] <;> decide

/-- **A chart sign is never `0`.** -/
theorem chartSign_ne_zero {x_c x : M}
    (hx : letI := hM.chartedSpace; x ∈ (extChartAt 𝓘(ℝ, Em) x_c).source)
    {v : Fin m → EK} (hvT : ∀ i, v i ∈ tangentM hM x) (hv : LinearIndependent ℝ v) :
    chartSign hM x_c x v ≠ 0 := by
  rw [chartSign_eq_orSign, orSign_ne_zero_iff finrank_E finrank_E]
  exact chartFrameCLM_bijective hx hvT hv

/-- **A chart sign is `1` or `-1`.** -/
theorem chartSign_mem {x_c x : M}
    (hx : letI := hM.chartedSpace; x ∈ (extChartAt 𝓘(ℝ, Em) x_c).source)
    {v : Fin m → EK} (hvT : ∀ i, v i ∈ tangentM hM x) (hv : LinearIndependent ℝ v) :
    chartSign hM x_c x v = 1 ∨ chartSign hM x_c x v = -1 := by
  rw [chartSign_eq_orSign]
  exact orSign_eq_one_or_neg_one finrank_E finrank_E _ _
    (chartFrameCLM_bijective hx hvT hv)

/-- A chart sign squares to `1`. -/
theorem chartSign_mul_self {x_c x : M}
    (hx : letI := hM.chartedSpace; x ∈ (extChartAt 𝓘(ℝ, Em) x_c).source)
    {v : Fin m → EK} (hvT : ∀ i, v i ∈ tangentM hM x) (hv : LinearIndependent ℝ v) :
    chartSign hM x_c x v * chartSign hM x_c x v = 1 := by
  rcases chartSign_mem hM hx hvT hv with h | h <;> rw [h] <;> decide

/-- Frames read alike in a chart have the same chart sign. -/
theorem chartSign_eq_of_chartFrameCLM_eq {x_c x y : M} {v v' : Fin m → EK}
    (h : chartFrameCLM hM x_c y v' = chartFrameCLM hM x_c x v) :
    chartSign hM x_c y v' = chartSign hM x_c x v := by
  rw [chartSign_eq_sgn_det, chartSign_eq_sgn_det, h]

/-! ### The bridge to the oriented sign

The orientation enters `frameSign` at one point only, so it contributes one factor `±1` per point.
-/

/-- The orientation factor is `1` or `-1`. -/
theorem orEps_mem (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m) (x : M) :
    orEps hM oM x = 1 ∨ orEps hM oM x = -1 := by
  letI := hM.chartedSpace
  rw [orEps_eq]
  exact orSign_eq_one_or_neg_one finrank_E finrank_E _ _ Function.bijective_id

/-- The orientation factor squares to `1`. -/
theorem orEps_mul_self (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m) (x : M) :
    orEps hM oM x * orEps hM oM x = 1 := by
  rcases orEps_mem hM oM x with h | h <;> rw [h] <;> decide

/-- **The bridge.**  The sign of a frame relative to an orientation of `M` is the sign of the
determinant of the frame read in the chart at the point, times a factor `orEps hM oM x` depending
only on the point.  The second factor mentions no frame, the first mentions no orientation. -/
theorem frameSign_eq_orEps_mul_selfSign
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m) (v : Fin m → EK) (x : M) :
    frameSign hM oM v x = orEps hM oM x * selfSign hM x v := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h := orSign_comp finrank_E finrank_E (stdOr m) (stdOr m) (oM.or x)
    (basisCLM (fun i => chartCoord hM x (v i))) (ContinuousLinearMap.id ℝ Em)
  rw [ContinuousLinearMap.id_comp] at h
  rw [frameSign_eq_orSign, h, ← orEps_eq, ← selfSign_eq_orSign]

/-- The bridge, read the other way: the self sign is the frame sign corrected by the orientation
factor at the point. -/
theorem selfSign_eq_orEps_mul_frameSign
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m) (v : Fin m → EK) (x : M) :
    selfSign hM x v = orEps hM oM x * frameSign hM oM v x := by
  rw [frameSign_eq_orEps_mul_selfSign, ← mul_assoc, orEps_mul_self, one_mul]

/-- At a single point, equality of frame signs and equality of self signs are the same thing. -/
theorem frameSign_eq_iff_selfSign_eq
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m) {v v' : Fin m → EK} (x : M) :
    frameSign hM oM v x = frameSign hM oM v' x ↔ selfSign hM x v = selfSign hM x v' := by
  constructor
  · intro h
    rw [selfSign_eq_orEps_mul_frameSign hM oM v x, selfSign_eq_orEps_mul_frameSign hM oM v' x, h]
  · intro h
    rw [frameSign_eq_orEps_mul_selfSign, frameSign_eq_orEps_mul_selfSign, h]

/-- **The `hpos` dictionary.**  If the chart at `x_c` carries the orientation at `y` to the
orientation at `x_c` — the hypothesis `hpos` of the existing local lemmas — then the orientation
factors at `y` and at `x_c` differ by the Jacobian sign of the chart.  So on such a ball the
point-dependent factor is the hub's factor times a cocycle, and nothing else. -/
theorem orEps_eq_of_orSign_chart_eq_one (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m)
    {x_c y : M}
    (hpos : letI := hM.chartedSpace; haveI := hM.isManifold;
      orSign (oM.or y) (oM.or x_c)
        (mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) x_c) y) = 1) :
    orEps hM oM y = orEps hM oM x_c * jacSign hM x_c y := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h1 := orSign_comp finrank_E finrank_E (stdOr m) (oM.or y) (oM.or x_c)
    (ContinuousLinearMap.id ℝ Em) (mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) x_c) y)
  rw [ContinuousLinearMap.comp_id, hpos, one_mul] at h1
  have h2 := orSign_comp finrank_E finrank_E (stdOr m) (stdOr m) (oM.or x_c)
    (mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) x_c) y) (ContinuousLinearMap.id ℝ Em)
  rw [ContinuousLinearMap.id_comp] at h2
  rw [orEps_eq, ← h1, h2, ← orEps_eq, ← jacSign_eq_orSign hM (stdOr m) x_c y]

/-- **The bridge at the hub.**  Under the positivity hypothesis `hpos` at `x`, the frame sign of
`v` at `x` is the chart sign of `v` relative to the hub `x_c`, times the orientation factor *at the
hub* — a single factor for the whole ball. -/
theorem frameSign_eq_orEps_hub_mul_chartSign
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m) {x_c x : M}
    (hpos : letI := hM.chartedSpace; haveI := hM.isManifold;
      orSign (oM.or x) (oM.or x_c)
        (mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) x_c) x) = 1) (v : Fin m → EK) :
    frameSign hM oM v x = orEps hM oM x_c * chartSign hM x_c x v := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h := orSign_comp finrank_E finrank_E (stdOr m) (stdOr m) (oM.or x_c)
    (chartFrameCLM hM x_c x v) (ContinuousLinearMap.id ℝ Em)
  rw [ContinuousLinearMap.id_comp] at h
  rw [← orSign_chartFrameCLM oM hpos v, h, ← orEps_eq, ← chartSign_eq_orSign]

/-- The bridge at the hub, read the other way. -/
theorem chartSign_eq_orEps_hub_mul_frameSign
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m) {x_c x : M}
    (hpos : letI := hM.chartedSpace; haveI := hM.isManifold;
      orSign (oM.or x) (oM.or x_c)
        (mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) x_c) x) = 1) (v : Fin m → EK) :
    chartSign hM x_c x v = orEps hM oM x_c * frameSign hM oM v x := by
  rw [frameSign_eq_orEps_hub_mul_chartSign hM oM hpos, ← mul_assoc, orEps_mul_self, one_mul]

/-- **The sign hypothesis of the local lemmas, restated.**  For two points of a chart ball on
which the chart is positive, the two frames have the same frame sign if and only if they have the
same chart sign relative to the hub.  This is what makes the hypothesis `hsign` of `exists_move`,
`exists_cancel` and `cancel_step` orientation-free. -/
theorem frameSign_eq_iff_chartSign_eq (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m)
    {x_c x y : M}
    (hposx : letI := hM.chartedSpace; haveI := hM.isManifold;
      orSign (oM.or x) (oM.or x_c)
        (mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) x_c) x) = 1)
    (hposy : letI := hM.chartedSpace; haveI := hM.isManifold;
      orSign (oM.or y) (oM.or x_c)
        (mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) x_c) y) = 1)
    (v v' : Fin m → EK) :
    frameSign hM oM v x = frameSign hM oM v' y ↔
      chartSign hM x_c x v = chartSign hM x_c y v' := by
  rw [frameSign_eq_orEps_hub_mul_chartSign hM oM hposx, frameSign_eq_orEps_hub_mul_chartSign hM oM hposy]
  constructor
  · intro h
    have h2 : orEps hM oM x_c * (orEps hM oM x_c * chartSign hM x_c x v) =
        orEps hM oM x_c * (orEps hM oM x_c * chartSign hM x_c y v') := by rw [h]
    rwa [← mul_assoc, ← mul_assoc, orEps_mul_self, one_mul, one_mul] at h2
  · intro h; rw [h]

/-! ### Frames of prescribed chart sign -/

/-- **At every point there are frames of both self signs.**  This is the sign-free version of
`Milnor.Framed.exists_frame_of_sign`: no orientation of `M`, and no case split on a global
reference sign.  The standard frame has self sign `1`, the frame reflected by `Tcan w₀ (-1/2)` has
self sign `-1`. -/
theorem exists_frame_of_selfSign (hm : 0 < m) (x : M) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∃ v : Fin m → EK, (∀ i, v i ∈ tangentM hM x) ∧ LinearIndependent ℝ v ∧
      selfSign hM x v = s := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨ι, hι⟩ : ∃ ι : Em →L[ℝ] EK,
      mfd 𝓘(ℝ, Em) 𝓘(ℝ, EK) (Subtype.val : M → EK) x = ι := ⟨_, rfl⟩
  have hιinj : Function.Injective ι := hι ▸ injective_mfd_val hM x
  have hιmem : ∀ u, ι u ∈ tangentM hM x := fun u => by
    rw [← hι]; exact LinearMap.mem_range_self _ _
  have hιcc : ∀ u, chartCoord hM x (ι u) = u := fun u => by
    rw [← hι]; exact chartCoord_mfd_val hM x u
  -- a frame from a tuple `e` of `ℝᵐ`, with self sign the determinant sign of `e`
  have key : ∀ e : Fin m → Em, LinearIndependent ℝ e →
      ∃ v : Fin m → EK, (∀ i, v i ∈ tangentM hM x) ∧ LinearIndependent ℝ v ∧
        selfSign hM x v = sgn (LinearMap.det ((basisCLM e : Em →L[ℝ] Em) : Em →ₗ[ℝ] Em)) := by
    intro e he
    refine ⟨fun i => ι (e i), fun i => hιmem _, ?_, ?_⟩
    · exact he.map' (ι : Em →ₗ[ℝ] EK) (LinearMap.ker_eq_bot.2 hιinj)
    · have hcc : (fun i => chartCoord hM x (ι (e i))) = e := funext fun i => hιcc (e i)
      calc selfSign hM x (fun i => ι (e i))
          = sgn (LinearMap.det ((basisCLM (fun i => chartCoord hM x (ι (e i))) : Em →L[ℝ] Em) :
              Em →ₗ[ℝ] Em)) := selfSign_eq_sgn_det hM x _
        _ = sgn (LinearMap.det ((basisCLM e : Em →L[ℝ] Em) : Em →ₗ[ℝ] Em)) := by rw [hcc]
  rcases hs with rfl | rfl
  · -- the standard frame
    obtain ⟨v, h1, h2, h3⟩ := key _ (linearIndependent_single (m := m))
    refine ⟨v, h1, h2, ?_⟩
    rw [h3, basisCLM_single_eq_id, ContinuousLinearMap.coe_id, LinearMap.det_id]
    exact sgn_one
  · -- the reflected frame
    set w₀ : Em := EuclideanSpace.single ⟨0, hm⟩ 1 with hw₀
    have hw₀n : ‖w₀‖ = 1 := by simp [hw₀]
    have hT : Function.Bijective (Tcan w₀ (-1 / 2)) := Tcan_bijective hw₀n (by norm_num)
    have he' : LinearIndependent ℝ
        (fun i : Fin m => Tcan w₀ (-1 / 2) (EuclideanSpace.single i (1 : ℝ))) :=
      (linearIndependent_single (m := m)).map'
        ((Tcan w₀ (-1 / 2) : Em →L[ℝ] Em) : Em →ₗ[ℝ] Em) (LinearMap.ker_eq_bot.2 hT.1)
    obtain ⟨v, h1, h2, h3⟩ := key _ he'
    refine ⟨v, h1, h2, ?_⟩
    have hbe' : basisCLM (fun i : Fin m => Tcan w₀ (-1 / 2) (EuclideanSpace.single i (1 : ℝ))) =
        Tcan w₀ (-1 / 2) := by
      have h := basisCLM_comp_eq (T := Tcan w₀ (-1 / 2))
        (a := fun i : Fin m => EuclideanSpace.single i (1 : ℝ))
        (b := fun i : Fin m => Tcan w₀ (-1 / 2) (EuclideanSpace.single i (1 : ℝ)))
        (fun i => rfl)
      rw [basisCLM_single_eq_id, ContinuousLinearMap.comp_id] at h
      exact h.symm
    rw [h3, hbe', det_Tcan hw₀n, show (2 : ℝ) * (-1 / 2) = -1 by norm_num]
    exact sgn_neg (by norm_num)

/-- **At every point of a chart there are frames of both chart signs** relative to that chart's
centre.  Immediate from `exists_frame_of_selfSign` and the cocycle formula, because the Jacobian
sign is `±1`. -/
theorem exists_frame_of_chartSign (hm : 0 < m) {x_c x : M}
    (hx : letI := hM.chartedSpace; x ∈ (extChartAt 𝓘(ℝ, Em) x_c).source) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    ∃ v : Fin m → EK, (∀ i, v i ∈ tangentM hM x) ∧ LinearIndependent ℝ v ∧
      chartSign hM x_c x v = s := by
  have hj : jacSign hM x_c x * s = 1 ∨ jacSign hM x_c x * s = -1 := by
    rcases jacSign_mem hM hx with h | h <;> rcases hs with rfl | rfl <;> rw [h] <;> decide
  obtain ⟨v, h1, h2, h3⟩ := exists_frame_of_selfSign hM hm x hj
  refine ⟨v, h1, h2, ?_⟩
  rw [chartSign_eq_jacSign_mul_selfSign, h3, ← mul_assoc, jacSign_mul_self hM hx, one_mul]

/-- **The oriented statement, re-derived.**  `Milnor.Framed.exists_frame_of_sign` (frames of both
`frameSign`s at a point) follows from the sign-free `exists_frame_of_selfSign` through the bridge:
nothing downstream of the oriented theory has to change. -/
theorem exists_frame_of_frameSign (hm : 0 < m)
    (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, Em) M m) (x : M) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    ∃ v : Fin m → EK, (∀ i, v i ∈ tangentM hM x) ∧ LinearIndependent ℝ v ∧
      frameSign hM oM v x = s := by
  have hε : orEps hM oM x * s = 1 ∨ orEps hM oM x * s = -1 := by
    rcases orEps_mem hM oM x with h | h <;> rcases hs with rfl | rfl <;> rw [h] <;> decide
  obtain ⟨v, h1, h2, h3⟩ := exists_frame_of_selfSign hM hm x hε
  refine ⟨v, h1, h2, ?_⟩
  rw [frameSign_eq_orEps_mul_selfSign, h3, ← mul_assoc, orEps_mul_self, one_mul]

/-! ### Transporting a frame inside one chart -/

/-- **A frame at `y` reading exactly like a given frame at `x` in the chart at `c`.**  For two
points of the source of one chart and a tangent independent frame `v` at `x`, there is a tangent
independent frame `v'` at `y` with `chartFrameCLM hM c y v' = chartFrameCLM hM c x v`; in
particular the two have the same chart sign (`exists_frame_transport_chartSign`).  It is built by
applying the inverse of the chart derivative at `y` to the columns of the frame read at `x`;
invertibility comes from `Milnor.isInvertible_mfd_extChartAt`, so no orientation and no positivity
hypothesis is needed. -/
theorem exists_frame_transport {c x y : M}
    (hx : letI := hM.chartedSpace; x ∈ (extChartAt 𝓘(ℝ, Em) c).source)
    (hy : letI := hM.chartedSpace; y ∈ (extChartAt 𝓘(ℝ, Em) c).source)
    {v : Fin m → EK} (hvT : ∀ i, v i ∈ tangentM hM x) (hv : LinearIndependent ℝ v) :
    ∃ v' : Fin m → EK, (∀ i, v' i ∈ tangentM hM y) ∧ LinearIndependent ℝ v' ∧
      chartFrameCLM hM c y v' = chartFrameCLM hM c x v := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨B, hBdef⟩ : ∃ B : Em →L[ℝ] Em, chartFrameCLM hM c x v = B := ⟨_, rfl⟩
  have hBbij : Function.Bijective B := hBdef ▸ chartFrameCLM_bijective hx hvT hv
  obtain ⟨D, hDdef⟩ : ∃ D : Em →L[ℝ] Em,
      mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) c) y = D := ⟨_, rfl⟩
  have hDbij : Function.Bijective D := hDdef ▸ bijective_mfd_extChartAt hy
  -- the columns of `D⁻¹ ∘ B`
  obtain ⟨τ, hτdef⟩ : ∃ τ : Fin m → Em,
      (fun i => Function.invFun D (B (EuclideanSpace.single i (1 : ℝ)))) = τ := ⟨_, rfl⟩
  have hDτ : ∀ i, D (τ i) = B (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    rw [← hτdef]
    exact Function.invFun_eq (hDbij.2 _)
  have hBcol : basisCLM (fun i => B (EuclideanSpace.single i (1 : ℝ))) = B := by
    have h := basisCLM_comp_eq (T := B) (a := fun i : Fin m => EuclideanSpace.single i (1 : ℝ))
      (b := fun i : Fin m => B (EuclideanSpace.single i (1 : ℝ))) (fun i => rfl)
    rw [basisCLM_single_eq_id, ContinuousLinearMap.comp_id] at h
    exact h.symm
  have hBτ : D.comp (basisCLM τ) = B := by rw [basisCLM_comp_eq hDτ, hBcol]
  have hcoe : ∀ a, D (basisCLM τ a) = B a := fun a => by rw [← hBτ]; rfl
  have hinjτ : Function.Injective (basisCLM τ) := fun a a' h =>
    hBbij.1 (by rw [← hcoe a, ← hcoe a', h])
  have hindτ : LinearIndependent ℝ τ := by
    have h := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.linearIndependent
    have h2 := h.map' (basisCLM τ : Em →ₗ[ℝ] Em) (LinearMap.ker_eq_bot.2 hinjτ)
    have h3 : (⇑(basisCLM τ : Em →ₗ[ℝ] Em) ∘
        ⇑(EuclideanSpace.basisFun (Fin m) ℝ).toBasis) = τ := by
      funext i; simp [basisCLM_single]
    rw [h3] at h2
    exact h2
  refine ⟨fun i => mfd 𝓘(ℝ, Em) 𝓘(ℝ, EK) (Subtype.val : M → EK) y (τ i), fun i => ?_, ?_, ?_⟩
  · exact LinearMap.mem_range_self _ _
  · exact hindτ.map' _ (LinearMap.ker_eq_bot.2 (injective_mfd_val hM y))
  · have hcc : (fun i => chartCoord hM y
        (mfd 𝓘(ℝ, Em) 𝓘(ℝ, EK) (Subtype.val : M → EK) y (τ i))) = τ :=
      funext fun i => chartCoord_mfd_val hM y (τ i)
    calc chartFrameCLM hM c y (fun i => mfd 𝓘(ℝ, Em) 𝓘(ℝ, EK) (Subtype.val : M → EK) y (τ i))
        = (mfd 𝓘(ℝ, Em) 𝓘(ℝ, Em) (extChartAt 𝓘(ℝ, Em) c) y).comp
            (basisCLM (fun i => chartCoord hM y
              (mfd 𝓘(ℝ, Em) 𝓘(ℝ, EK) (Subtype.val : M → EK) y (τ i)))) := rfl
      _ = D.comp (basisCLM τ) := by rw [hcc, hDdef]
      _ = chartFrameCLM hM c x v := by rw [hBτ, hBdef]

/-- **A frame at `y` with the same chart sign as a given frame at `x`**, both read in the chart at
`c`.  The sign form of `exists_frame_transport`. -/
theorem exists_frame_transport_chartSign {c x y : M}
    (hx : letI := hM.chartedSpace; x ∈ (extChartAt 𝓘(ℝ, Em) c).source)
    (hy : letI := hM.chartedSpace; y ∈ (extChartAt 𝓘(ℝ, Em) c).source)
    {v : Fin m → EK} (hvT : ∀ i, v i ∈ tangentM hM x) (hv : LinearIndependent ℝ v) :
    ∃ v' : Fin m → EK, (∀ i, v' i ∈ tangentM hM y) ∧ LinearIndependent ℝ v' ∧
      chartSign hM c y v' = chartSign hM c x v := by
  obtain ⟨v', h1, h2, h3⟩ := exists_frame_transport hM hx hy hvT hv
  exact ⟨v', h1, h2, chartSign_eq_of_chartFrameCLM_eq hM h3⟩

end Framed

end Milnor
