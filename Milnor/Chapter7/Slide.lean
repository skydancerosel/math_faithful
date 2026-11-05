import Milnor.Chapter7.Reach
import Milnor.Chapter7.BallChainSign

/-!
# Sliding a framed point along a chain of balls, and the frame flip (Milnor §7, p. 50)

**Stage 6 of `Exposition/PlanMod2.md`**, the formalization of Milnor's remark at the end of §7
(book p. 50): *for a connected non-orientable manifold, two smooth maps `M → Sᵐ` are smoothly
homotopic if and only if they have the same degree modulo `2`.*  Milnor's one-clause reason is that
a framed point slid around an orientation-reversing loop comes back with its frame reversed, so that
only the parity of the number of points of a framed `0`-manifold survives.  This file carries the
point along a chain of balls and performs the flip.

Four things are proved.

* **The slide** (`Milnor.Framed.exists_slide`).  Let `F` be a framed `0`-manifold, `x₀ ∈ F.N` one of
  its points, and let `c` be a chain of chart balls from `x₀` to `y` none of whose balls meets the
  *other* points of `F.N` (the Stage 4 predicate `Milnor.ChartChain.IsBallIn` with avoided set
  `F.N \ {x₀}`).  Then `F` is framed cobordant to a framed `0`-manifold whose point set is
  `(F.N \ {x₀}) ∪ {y}`, whose frames away from `x₀` are those of `F`, and whose **self sign** at `y`
  is `Milnor.chainSign c` times the self sign of `F` at `x₀`.  This is the "carry the chain" form of
  reach announced in plan §2.3, and the sign bookkeeping is the dictionary of plan §2.4.

* **Reach with some frame** (`Milnor.Framed.exists_reach_any`): every point of the connected
  component of `x₀` in `M ∖ (F.N ∖ {x₀})` is reached, with *some* frame, from the slide and the
  Stage 4 avoidance theorem `Milnor.exists_isBallIn_avoiding` applied inside that component.

* **The flip** (`Milnor.Framed.exists_flip`): if the chain is a *loop* at `x₀` of chain sign `-1`,
  the slide returns the point to itself — the point set and every other frame are literally
  unchanged — and reverses the self sign at `x₀`.

* **Frames are free** (`Milnor.Framed.exists_frame_free`, `Milnor.Framed.exists_reach_free`): with a
  reversing loop available, the frame at a point may be replaced by *any* tangent independent frame,
  and the point may simultaneously be moved anywhere in its component.  `exists_reach_free` is the
  drop-in, sign-free replacement for the oriented `Milnor.Framed.exists_reach`.

## What the induction needs beyond the plan's description

The plan describes each step of the induction as one application of the restated
`Milnor.Framed.exists_move`.  That is not literally possible: a `Milnor.BallHop` only asks its two
endpoints to lie in the chart ball of radius `rad`, whereas `exists_move` needs them in the ball of
radius `R/4` for a radius `R` whose *closed* ball lies in the chart's target.  A single ball hop is
therefore too coarse to be performed by one move, and each hop has to be subdivided.  The sign then
has to be shown not to notice the subdivision, and that is done here by

* `Milnor.exists_isOpen_jacSign_mul_jacSign_eq`, an open-set form of the Stage 4 transition cocycle
  lemma `Milnor.eventually_jacSign_mul_jacSign_eq`: near any point `q` of the source of the chart at
  `p` there is an open set on which `jacSign p · * jacSign q ·` is constant; and
* `Milnor.Framed.chartSign_hub_change`, which turns that constancy into the statement that on such
  an open set *equality of chart signs at the hub `q` is equality of chart signs at the hub `p`*.

So the invariant carried by the subdivided hop is `chartSign hM p · ·` for the hop's own hub `p`
(this is plan §2.2's "local orientation at the hub", read arithmetically), it is preserved by every
small move, and `Milnor.Framed.exists_slide_ball` performs the whole hop by the clopen argument of
`exists_reach` run inside the hop's ball, which is preconnected by
`Milnor.isPreconnected_chartBall`.  Passing from the hub-relative invariant to the self sign and the
hop sign is `Milnor.Framed.selfSign_eq_of_chartSign_eq`.

## Hypotheses

`0 < m` throughout, as in the rest of the local theory; `IsCompact M` and `M.Nonempty`, which the
Theorem-B machinery behind `exists_move` needs.  **No orientation of `M` occurs anywhere**, and no
hypothesis on the dimension beyond `0 < m`: the conditions `2 ≤ m` and connectedness of `M` belong
to Stage 5, which produces the reversing loop.  Here the reversing loop is a *hypothesis*, spelled
out as `∃ c : ChartChain 𝓘(ℝ, Eᵐ) x₀ x₀, c.IsBallIn (F.N \ {x₀})ᶜ ∧ chainSign c = -1`.  That is
definitionally `Milnor.HasReversingBallLoop 𝓘(ℝ, Eᵐ) (F.N ∖ {x₀}) x₀` of `Chapter7/Puncture.lean`,
so a loop produced by Stage 5's punctured dichotomy is accepted with no glue at all; this file does
not import `Puncture.lean`, everything in it being independent of how the loop is obtained.
Hausdorffness is never invoked: `Milnor.BallHop.RunsIn` is used only
through `Milnor.BallHop.RunsIn.subset`, a statement about the closed chart ball rather than about
the topological closure, and each application of `exists_move` gets the closure condition it needs
from the good ball of `Milnor.Framed.exists_goodBall_free`.  (`M` is a subset of a Euclidean space,
so `T2Space M` would in any case be free.)

## The bridge of the two Jacobian signs

`Milnor.jacSign` (Stage 4, for an abstract manifold) and `Milnor.Framed.jacSign` (Stage 1, for a
slice submanifold of a Euclidean space) are the same expression; `Milnor.Framed.jacSign_eq_jacSign`
records this, and `Milnor.Framed.ballU_eq_chartBall` does the same for the two notations for a chart
ball.  Both are `rfl`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

/-! ### The transition cocycle as an open set

The Stage 4 lemma `Milnor.eventually_jacSign_mul_jacSign_eq` says that the product of the Jacobian
signs of two charts is locally constant.  The form needed below is an honest open set carrying that
constancy.
-/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {m : ℕ}

/-- **An open set on which the transition sign is constant.**  For `q` in the source of the chart
centred at `p` there is an open neighbourhood `V` of `q`, inside both chart sources, on which
`jacSign I p z * jacSign I q z` has the constant value `jacSign I p q` (the value at `z = q`,
where `jacSign I q q = 1`).  This is `Milnor.eventually_jacSign_mul_jacSign_eq` with the filter
replaced by a set, which is the form in which the slide below uses it. -/
theorem exists_isOpen_jacSign_mul_jacSign_eq [I.Boundaryless] (hm : finrank ℝ E = m) {p q : M}
    (hqp : q ∈ (extChartAt I p).source) :
    ∃ V : Set M, IsOpen V ∧ q ∈ V ∧ V ⊆ (extChartAt I p).source ∧
      V ⊆ (extChartAt I q).source ∧
      ∀ z ∈ V, jacSign I p z * jacSign I q z = jacSign I p q := by
  have h1 : {z : M | z ∈ (extChartAt I p).source ∧ z ∈ (extChartAt I q).source ∧
      jacSign I p z * jacSign I q z = jacSign I p q} ∈ 𝓝 q := by
    filter_upwards [(isOpen_extChartAt_source (I := I) p).mem_nhds hqp,
      (isOpen_extChartAt_source (I := I) q).mem_nhds (mem_extChartAt_source q),
      eventually_jacSign_mul_jacSign_eq (I := I) (m := m) hm hqp (mem_extChartAt_source q)]
      with z hz1 hz2 hz3
    exact ⟨hz1, hz2, by rw [hz3, jacSign_self, mul_one]⟩
  obtain ⟨V, hVs, hVo, hqV⟩ := mem_nhds_iff.1 h1
  exact ⟨V, hVo, hqV, fun z hz => (hVs hz).1, fun z hz => (hVs hz).2.1,
    fun z hz => (hVs hz).2.2⟩

end Abstract

open Sphere

namespace Framed

/-! ### The two bridges, and the change of hub -/

section Bridge

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M)

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "EK" => EuclideanSpace ℝ (Fin (K + 1))

/-- **The two Jacobian signs agree.**  Stage 1's `Milnor.Framed.jacSign`, for a slice submanifold of
a Euclidean space, and Stage 4's `Milnor.jacSign`, for an abstract manifold, are literally the same
expression. -/
theorem jacSign_eq_jacSign (x_c x : M) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    jacSign hM x_c x = _root_.Milnor.jacSign 𝓘(ℝ, Em) x_c x := rfl

/-- **The two notations for a chart ball agree.**  `Milnor.Framed.ballU` of `Chapter7/Glue.lean` and
`Milnor.chartBall` of `Chapter7/OrientBall.lean` are the same set. -/
theorem ballU_eq_chartBall (x_c : M) (R : ℝ) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ballU hM x_c R = _root_.Milnor.chartBall 𝓘(ℝ, Em) x_c R := rfl

/-- **Changing the hub of a chart sign comparison.**  On a set `V` inside the source of the chart at
`q` on which the transition sign `jacSign hM p · * jacSign hM q ·` is constant — such a set is
produced by `Milnor.exists_isOpen_jacSign_mul_jacSign_eq` — two frames at two points of `V` have
equal chart signs at the hub `p` as soon as they have equal chart signs at the hub `q`.

This is the reason the sign does not notice a hop being subdivided: a small move inside a ball
centred at `q` preserves the chart sign at `q`, and hence, on such a `V`, the chart sign at the
hub `p` of the big ball as well.  The proof is the cocycle formula
`Milnor.Framed.chartSign_eq_jacSign_mul_selfSign` together with `jacSign² = 1`; nothing is assumed
about the frames. -/
theorem chartSign_hub_change {p q : M} {V : Set M}
    (hVq : letI := hM.chartedSpace; V ⊆ (extChartAt 𝓘(ℝ, Em) q).source)
    (hVjac : ∀ z ∈ V, jacSign hM p z * jacSign hM q z = jacSign hM p q)
    {y₁ y₂ : M} (h1 : y₁ ∈ V) (h2 : y₂ ∈ V) {v₁ v₂ : Fin m → EK}
    (h : chartSign hM q y₂ v₂ = chartSign hM q y₁ v₁) :
    chartSign hM p y₂ v₂ = chartSign hM p y₁ v₁ := by
  have e1 : jacSign hM p y₁ * jacSign hM q y₁ = jacSign hM p y₂ * jacSign hM q y₂ := by
    rw [hVjac y₁ h1, hVjac y₂ h2]
  have s1 : jacSign hM q y₁ * jacSign hM q y₁ = 1 := jacSign_mul_self hM (hVq h1)
  have s2 : jacSign hM q y₂ * jacSign hM q y₂ = 1 := jacSign_mul_self hM (hVq h2)
  have key : jacSign hM p y₂ = jacSign hM p y₁ * jacSign hM q y₁ * jacSign hM q y₂ := by
    linear_combination (-jacSign hM p y₂) * s2 + (-jacSign hM q y₂) * e1
  rw [chartSign_eq_jacSign_mul_selfSign, chartSign_eq_jacSign_mul_selfSign] at h ⊢
  linear_combination selfSign hM y₂ v₂ * key +
    (jacSign hM p y₁ * jacSign hM q y₁) * h + (jacSign hM p y₁ * selfSign hM y₁ v₁) * s1

/-- **From the hub-relative sign to the self sign and the hop sign.**  If two frames at `x` and `z`
have the same chart sign at a hub `p` whose chart contains `z`, then their self signs differ by
`jacSign hM p x * jacSign hM p z`, which is the sign of a hop through the chart at `p`
(`Milnor.hopSign`).  This is the "slide bookkeeping" line of plan §2.4. -/
theorem selfSign_eq_of_chartSign_eq {p x z : M}
    (hzp : letI := hM.chartedSpace; z ∈ (extChartAt 𝓘(ℝ, Em) p).source)
    {v v' : Fin m → EK} (h : chartSign hM p z v' = chartSign hM p x v) :
    selfSign hM z v' = jacSign hM p x * jacSign hM p z * selfSign hM x v := by
  have sz : jacSign hM p z * jacSign hM p z = 1 := jacSign_mul_self hM hzp
  rw [chartSign_eq_jacSign_mul_selfSign, chartSign_eq_jacSign_mul_selfSign] at h
  linear_combination (-selfSign hM z v') * sz + jacSign hM p z * h

end Bridge

/-! ### The slide -/

section Slide

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} (hMc : IsCompact M) (hne : M.Nonempty)

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "EK" => EuclideanSpace ℝ (Fin (K + 1))

/-- **Agreement composes along a moving point.**  If `F₁` agrees with `F` away from `x₀` and `F₂`
agrees with `F₁` away from `z`, then `F₂` agrees with `F` away from `x₀`, provided `F₁` still
carries all the points of `F` other than `x₀` and `z` is not one of them.  This is how the
`Milnor.Framed.AgreesOff` clause is threaded through the induction on the chain, where the
distinguished point travels from hop to hop while the other points stay put. -/
theorem AgreesOff.trans' {F F₁ F₂ : FramedSub hM 0 m} {x₀ z : M} (h₁ : AgreesOff F F₁ x₀)
    (hN₁ : F.N \ {x₀} ⊆ F₁.N) (hz : z ∉ F.N \ {x₀}) (h₂ : AgreesOff F₁ F₂ z) :
    AgreesOff F F₂ x₀ := by
  intro i a ha hax ha₂
  have haP : a ∈ F.N \ {x₀} := ⟨ha, hax⟩
  have ha₁ : a ∈ F₁.N := hN₁ haP
  have haz : a ≠ z := fun h => hz (h ▸ haP)
  rw [h₂ i a ha₁ haz ha₂, h₁ i a ha hax ha₁]

/-- **The framed `0`-manifolds reached from `F` by moving its point `x` to `z` without changing the
chart sign at the hub `p`.**  The auxiliary predicate of the clopen argument in
`Milnor.Framed.exists_slide_ball`: there is a framed `0`-manifold framed cobordant to `F` whose
point set is `F.N` with `x` replaced by `z`, whose frames away from `x` are those of `F`, and whose
frame at `z`, read in the chart centred at `p`, has the same determinant sign as the frame of `F` at
`x` read in that same chart. -/
def SlidesTo (F : FramedSub hM 0 m) {x : M} (hx : x ∈ F.N) (p z : M) : Prop :=
  ∃ F' : FramedSub hM 0 m, F'.N = (F.N \ {x}) ∪ {z} ∧ AgreesOff F F' x ∧
    FramedCobordant hM F F' ∧ ∃ hz : z ∈ F'.N,
      chartSign hM p z (fun i => F'.v i ⟨z, hz⟩) = chartSign hM p x (fun i => F.v i ⟨x, hx⟩)

include hMc hne in
/-- **Sliding a framed point across one chart ball.**  Let `p` be the centre of a chart ball of
radius `rad` whose ball lies in the target of the chart at `p`, let the ball contain no point of
`F.N` other than `x`, and let `x` and `z` both lie in it.  Then `F` can be slid from `x` to `z`
keeping the chart sign at `p`: the conclusion is `Milnor.Framed.SlidesTo F hx p z`.

This is the step of the slide, and it is where the work is.  A single ball hop is too coarse to be
performed by one application of `Milnor.Framed.exists_move`, which wants both endpoints in the ball
of a quarter of a radius whose *closed* ball lies in the chart's target; so the ball is crossed by
the clopen argument of `Milnor.Framed.exists_reach`, run inside it.  The ball is preconnected
(`Milnor.isPreconnected_chartBall`); each small move is `Milnor.Framed.move_in_ball` inside a good
ball centred at a point `q` of the big ball, and the arriving frame is supplied by
`Milnor.Framed.exists_frame_transport_chartSign`, so that the chart sign at `q` is preserved; and
the good ball is chosen inside the open set of `Milnor.exists_isOpen_jacSign_mul_jacSign_eq`, on
which preserving the chart sign at `q` is preserving the chart sign at `p`
(`Milnor.Framed.chartSign_hub_change`).  No orientation and no separation hypothesis occurs. -/
theorem exists_slide_ball (hm : 0 < m) (F : FramedSub hM 0 m) {x : M} (hx : x ∈ F.N) {p : M}
    {rad : ℝ}
    (hrad : letI := hM.chartedSpace;
      ball (extChartAt 𝓘(ℝ, Em) p p) rad ⊆ (extChartAt 𝓘(ℝ, Em) p).target)
    (hxU : x ∈ ballU hM p rad) (hU : ballU hM p rad ⊆ (F.N \ {x})ᶜ) {z : M}
    (hzU : z ∈ ballU hM p rad) : SlidesTo F hx p z := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hUo : IsOpen (ballU hM p rad) := isOpen_ballU p rad
  have hUsrc : ballU hM p rad ⊆ (extChartAt 𝓘(ℝ, Em) p).source := fun _ hq => (mem_ballU.1 hq).1
  have hUconn : IsPreconnected (ballU hM p rad) := by
    rw [ballU_eq_chartBall]; exact isPreconnected_chartBall hrad
  -- the starting point slides to itself
  have hxS : SlidesTo F hx p x := by
    refine ⟨F, ?_, fun i a ha _ ha' => rfl, FramedCobordant.refl' hMc hne F, hx, rfl⟩
    exact (Set.sdiff_union_of_subset (Set.singleton_subset_iff.2 hx)).symm
  -- the local step: everything near a point `q` of the ball slides to and from `q`
  have hstep : ∀ q ∈ ballU hM p rad, ∃ R : ℝ, 0 < R ∧ ballU hM q R ⊆ ballU hM p rad ∧
      ∀ y₁ ∈ ballU hM q (R / 4), ∀ y₂ ∈ ballU hM q (R / 4),
        SlidesTo F hx p y₁ → SlidesTo F hx p y₂ := by
    intro q hqU
    obtain ⟨V, hVo, hqV, -, hVq, hVjac⟩ :=
      exists_isOpen_jacSign_mul_jacSign_eq (I := 𝓘(ℝ, Em)) (m := m) finrank_E (hUsrc hqU)
    obtain ⟨R, hR, hRsub, hmove⟩ :=
      move_in_ball hMc hne hm F (x₀ := x) q (hU hqU) (hUo.inter hVo) ⟨hqU, hqV⟩
    have hsub4 : ballU hM q (R / 4) ⊆ ballU hM q R := fun a ha => by
      rw [mem_ballU] at ha ⊢; exact ⟨ha.1, by linarith [ha.2]⟩
    refine ⟨R, hR, fun a ha => (hRsub ha).1, ?_⟩
    intro y₁ hy₁ y₂ hy₂ hy₁S
    obtain ⟨F', hN', hoff, hcob, hy₁', hsign₁⟩ := hy₁S
    have hy₁R : y₁ ∈ ballU hM q R := hsub4 hy₁
    have hy₂R : y₂ ∈ ballU hM q R := hsub4 hy₂
    obtain ⟨v₂, hv₂T, hv₂, hv₂s⟩ := exists_frame_transport_chartSign hM (mem_ballU.1 hy₁R).1
      (mem_ballU.1 hy₂R).1 (fun i => F'.tangent i ⟨y₁, hy₁'⟩) (F'.indep ⟨y₁, hy₁'⟩)
    obtain ⟨F'', hN'', hoff'', hv'', hcob'⟩ :=
      hmove y₁ hy₁ y₂ hy₂ F' hN' hoff hy₁' v₂ hv₂T hv₂ hv₂s
    have hy₂'' : y₂ ∈ F''.N := by rw [hN'']; exact Or.inr rfl
    refine ⟨F'', hN'', hoff'', hcob.trans hcob', hy₂'', ?_⟩
    have hfun : (fun i => F''.v i ⟨y₂, hy₂''⟩) = v₂ := funext fun i => hv'' i hy₂''
    rw [hfun]
    exact (chartSign_hub_change hM hVq hVjac (hRsub hy₁R).2 (hRsub hy₂R).2 hv₂s).trans hsign₁
  -- the clopen argument inside the ball
  have hu : IsOpen {a | a ∈ ballU hM p rad ∧ SlidesTo F hx p a} := by
    rw [isOpen_iff_forall_mem_open]
    rintro a ⟨haU, haS⟩
    obtain ⟨R, hR, hRsub, hkey⟩ := hstep a haU
    refine ⟨ballU hM a (R / 4), ?_, isOpen_ballU a (R / 4), x_c_mem_ballU a (by positivity)⟩
    intro b hb
    have hsub4 : ballU hM a (R / 4) ⊆ ballU hM a R := fun c hc => by
      rw [mem_ballU] at hc ⊢; exact ⟨hc.1, by linarith [hc.2]⟩
    exact ⟨hRsub (hsub4 hb), hkey a (x_c_mem_ballU a (by positivity)) b hb haS⟩
  have hv : IsOpen (ballU hM p rad ∩ (closure {a | SlidesTo F hx p a})ᶜ) :=
    hUo.inter isClosed_closure.isOpen_compl
  have hcover : ballU hM p rad ⊆ {a | a ∈ ballU hM p rad ∧ SlidesTo F hx p a} ∪
      (ballU hM p rad ∩ (closure {a | SlidesTo F hx p a})ᶜ) := by
    intro a haU
    by_cases hacl : a ∈ closure {b | SlidesTo F hx p b}
    · left
      obtain ⟨R, hR, -, hkey⟩ := hstep a haU
      obtain ⟨b, hbU, hbS⟩ := mem_closure_iff.1 hacl (ballU hM a (R / 4)) (isOpen_ballU _ _)
        (x_c_mem_ballU a (by positivity))
      exact ⟨haU, hkey b hbU a (x_c_mem_ballU a (by positivity)) hbS⟩
    · right; exact ⟨haU, hacl⟩
  have hdisj : Disjoint {a | a ∈ ballU hM p rad ∧ SlidesTo F hx p a}
      (ballU hM p rad ∩ (closure {a | SlidesTo F hx p a})ᶜ) := by
    rw [Set.disjoint_left]
    rintro a ⟨-, haS⟩ ⟨-, hacl⟩
    exact hacl (subset_closure haS)
  exact (hUconn.subset_left_of_subset_union hu hv hdisj hcover ⟨x, hxU, hxU, hxS⟩ hzU).2

include hMc hne in
/-- **The induction behind `Milnor.Framed.exists_slide`.**  The set `P` of the other points of the
framed `0`-manifold is held fixed along the chain — that is what makes the induction go through —
and the distinguished point travels.  Each hop is `Milnor.Framed.exists_slide_ball`, and the sign is
multiplied by the sign of the hop (`Milnor.hopSign`), so along the chain by
`Milnor.chainSign`. -/
theorem exists_slide_aux (hm : 0 < m) {P : Set M} {x y : M}
    (c : letI := hM.chartedSpace; haveI := hM.isManifold; ChartChain 𝓘(ℝ, Em) x y)
    (hc : letI := hM.chartedSpace; haveI := hM.isManifold; c.IsBallIn Pᶜ) :
    ∀ (F : FramedSub hM 0 m) (hx : x ∈ F.N), F.N \ {x} = P →
      ∃ F' : FramedSub hM 0 m, F'.N = P ∪ {y} ∧ AgreesOff F F' x ∧ FramedCobordant hM F F' ∧
        ∀ hy : y ∈ F'.N, selfSign hM y (fun i => F'.v i ⟨y, hy⟩) =
          (letI := hM.chartedSpace; haveI := hM.isManifold; _root_.Milnor.chainSign c) *
            selfSign hM x (fun i => F.v i ⟨x, hx⟩) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hc' : _root_.Milnor.ChartChain.IsBallIn (I := 𝓘(ℝ, Em)) Pᶜ c := hc
  clear hc
  induction hc' with
  | nil a =>
      intro F hx hFP
      refine ⟨F, ?_, fun i b hb _ hb' => rfl, FramedCobordant.refl' hMc hne F, fun hy => ?_⟩
      · rw [← hFP]; exact (Set.sdiff_union_of_subset (Set.singleton_subset_iff.2 hx)).symm
      · rw [_root_.Milnor.chainSign_nil, one_mul]
  | @cons x z y b hb cc hcc ih =>
      intro F hx hFP
      -- the hop's ball avoids the other points, so its far end is not one of them
      have hbU : ballU hM b.hub b.rad ⊆ (F.N \ {x})ᶜ := by
        rw [hFP, ballU_eq_chartBall]; exact hb.subset
      have hzP : z ∉ P := by
        have h := hbU b.mem_right
        rw [hFP] at h; exact h
      -- cross the hop
      obtain ⟨F₁, hN₁, hoff₁, hcob₁, hz₁, hsign₁⟩ :=
        exists_slide_ball hMc hne hm F hx b.ball_subset b.mem_left hbU b.mem_right
      rw [hFP] at hN₁
      have hF₁P : F₁.N \ {z} = P := by
        rw [hN₁, Set.union_sdiff_distrib, Set.sdiff_singleton_eq_self hzP, Set.sdiff_self,
          Set.union_empty]
      -- the rest of the chain
      obtain ⟨F₂, hN₂, hoff₂, hcob₂, hsign₂⟩ := ih F₁ hz₁ hF₁P
      refine ⟨F₂, hN₂, hoff₁.trans' ?_ ?_ hoff₂, hcob₁.trans hcob₂, fun hy => ?_⟩
      · rw [hFP, hN₁]; exact Set.subset_union_left
      · rw [hFP]; exact hzP
      · have hkey : selfSign hM z (fun i => F₁.v i ⟨z, hz₁⟩) =
            _root_.Milnor.hopSign b.toChartHop * selfSign hM x (fun i => F.v i ⟨x, hx⟩) := by
          rw [selfSign_eq_of_chartSign_eq hM (p := b.hub)
            (chartBall_subset_source b.mem_right) hsign₁]
          rfl
        rw [hsign₂ hy, hkey, _root_.Milnor.chainSign_cons]
        ring

include hMc hne in
/-- **Sliding a framed point along a chain of balls** (plan §2.3, "carry the chain").  Let `F` be a
framed `0`-manifold, `x₀ ∈ F.N`, and let `c` be a chain of chart balls from `x₀` to `y` none of
whose balls meets any other point of `F.N`.  Then `F` is framed cobordant to a framed `0`-manifold
`F'` with

* point set `(F.N ∖ {x₀}) ∪ {y}`: the point has moved to the far end of the chain;
* the same frames as `F` at every other point (`Milnor.Framed.AgreesOff`);
* self sign at `y` equal to `Milnor.chainSign c` times the self sign of `F` at `x₀`.

No orientation of `M` occurs, and the only hypothesis on the dimension is `0 < m`. -/
theorem exists_slide (hm : 0 < m) (F : FramedSub hM 0 m) {x₀ y : M} (hx₀ : x₀ ∈ F.N)
    (c : letI := hM.chartedSpace; haveI := hM.isManifold; ChartChain 𝓘(ℝ, Em) x₀ y)
    (hc : letI := hM.chartedSpace; haveI := hM.isManifold; c.IsBallIn (F.N \ {x₀})ᶜ) :
    ∃ F' : FramedSub hM 0 m, F'.N = (F.N \ {x₀}) ∪ {y} ∧ AgreesOff F F' x₀ ∧
      FramedCobordant hM F F' ∧
      ∀ hy : y ∈ F'.N, selfSign hM y (fun i => F'.v i ⟨y, hy⟩) =
        (letI := hM.chartedSpace; haveI := hM.isManifold; _root_.Milnor.chainSign c) *
          selfSign hM x₀ (fun i => F.v i ⟨x₀, hx₀⟩) :=
  exists_slide_aux hMc hne hm c hc F hx₀ rfl

include hMc hne in
/-- **Reaching any point of the component, with some frame.**  If `y` lies in the connected
component `Milnor.compl' F.N x₀` of `x₀` in `M ∖ (F.N ∖ {x₀})`, then `F` is framed cobordant to a
framed `0`-manifold whose point set is `F.N` with `x₀` replaced by `y` and whose other frames are
unchanged.  Nothing is claimed about the frame at `y`; that is the price of dropping the
orientation, and `Milnor.Framed.exists_reach_free` pays it back with a reversing loop.

The component is open (`Milnor.isOpen_compl'`) and preconnected (it is a connected component) and
misses the other points of `F.N`, so Stage 4's `Milnor.exists_isBallIn_avoiding` joins `x₀` to `y`
by a chain of balls avoiding them; then `Milnor.Framed.exists_slide` slides. -/
theorem exists_reach_any (hm : 0 < m) (F : FramedSub hM 0 m) {x₀ : M} (hx₀ : x₀ ∈ F.N) {y : M}
    (hy : y ∈ compl' F.N x₀) :
    ∃ F' : FramedSub hM 0 m, F'.N = (F.N \ {x₀}) ∪ {y} ∧ AgreesOff F F' x₀ ∧
      FramedCobordant hM F F' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI := locallyConnectedSpace_M (hM := hM)
  obtain ⟨c, -, -, hc⟩ := exists_isBallIn_avoiding (I := 𝓘(ℝ, Em))
    (isOpen_compl' F.finite_N x₀) isPreconnected_connectedComponentIn
    (Set.disjoint_left.2 fun a ha => compl'_subset F.N x₀ ha) mem_compl'_self hy
  obtain ⟨F', hN', hoff, hcob, -⟩ := exists_slide hMc hne hm F hx₀ c hc
  exact ⟨F', hN', hoff, hcob⟩

/-! ### The flip, and the freedom of the frames -/

include hMc hne in
/-- **The frame flip.**  Let `c` be a *loop* of chart balls at `x₀`, none of its balls meeting any
other point of `F.N`, whose chain sign is `-1` — a reversing ball loop in the sense of the plan,
`HasReversingBallLoop hM (F.N ∖ {x₀}) x₀`.  Then `F` is framed cobordant to a framed `0`-manifold
with **the same point set**, the same frames at every other point, and the self sign at `x₀`
reversed.

This is Milnor's clause "sliding a point around an orientation-reversing loop changes the sign of
its frame".  The point set is literally unchanged because the loop returns `x₀` to itself and no
ball of it ever meets another point of `F.N`. -/
theorem exists_flip (hm : 0 < m) (F : FramedSub hM 0 m) {x₀ : M} (hx₀ : x₀ ∈ F.N)
    (c : letI := hM.chartedSpace; haveI := hM.isManifold; ChartChain 𝓘(ℝ, Em) x₀ x₀)
    (hc : letI := hM.chartedSpace; haveI := hM.isManifold; c.IsBallIn (F.N \ {x₀})ᶜ)
    (hs : letI := hM.chartedSpace; haveI := hM.isManifold; _root_.Milnor.chainSign c = -1) :
    ∃ F' : FramedSub hM 0 m, F'.N = F.N ∧ AgreesOff F F' x₀ ∧ FramedCobordant hM F F' ∧
      ∀ h : x₀ ∈ F'.N, selfSign hM x₀ (fun i => F'.v i ⟨x₀, h⟩) =
        -selfSign hM x₀ (fun i => F.v i ⟨x₀, hx₀⟩) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨F', hN', hoff, hcob, hsign⟩ := exists_slide hMc hne hm F hx₀ c hc
  refine ⟨F', ?_, hoff, hcob, fun h => ?_⟩
  · rw [hN']; exact Set.sdiff_union_of_subset (Set.singleton_subset_iff.2 hx₀)
  · rw [hsign h, hs, neg_one_mul]

include hMc hne in
/-- **The frame at a point of a framed `0`-manifold is free.**  With a reversing ball loop at `x₀`
avoiding the other points of `F.N`, the frame of `F` at `x₀` may be replaced by *any* tangent
independent frame `v` at `x₀`, up to framed cobordism, the point set and the other frames being
unchanged.

Compare the two self signs (both are `1` or `-1`, `Milnor.Framed.selfSign_mem`); if they differ,
flip with `Milnor.Framed.exists_flip`; then change the frame within its class, which is
`Milnor.Framed.move_in_ball` with the two points equal. -/
theorem exists_frame_free (hm : 0 < m) (F : FramedSub hM 0 m) {x₀ : M} (hx₀ : x₀ ∈ F.N)
    (hloop : letI := hM.chartedSpace; haveI := hM.isManifold;
      ∃ c : ChartChain 𝓘(ℝ, Em) x₀ x₀, c.IsBallIn (F.N \ {x₀})ᶜ ∧ _root_.Milnor.chainSign c = -1)
    {v : Fin m → EK} (hvT : ∀ i, v i ∈ tangentM hM x₀) (hv : LinearIndependent ℝ v) :
    ∃ F' : FramedSub hM 0 m, F'.N = F.N ∧ AgreesOff F F' x₀ ∧
      (∀ i (h : x₀ ∈ F'.N), F'.v i ⟨x₀, h⟩ = v i) ∧ FramedCobordant hM F F' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  -- a framed `0`-manifold with the same points as `F` whose self sign at `x₀` is that of `v`
  obtain ⟨F₁, hN₁, hoff₁, hcob₁, hs₁⟩ : ∃ F₁ : FramedSub hM 0 m, F₁.N = F.N ∧
      AgreesOff F F₁ x₀ ∧ FramedCobordant hM F F₁ ∧
      ∀ h : x₀ ∈ F₁.N, selfSign hM x₀ (fun i => F₁.v i ⟨x₀, h⟩) = selfSign hM x₀ v := by
    by_cases heq : selfSign hM x₀ (fun i => F.v i ⟨x₀, hx₀⟩) = selfSign hM x₀ v
    · exact ⟨F, rfl, fun i a ha _ ha' => rfl, FramedCobordant.refl' hMc hne F, fun _ => heq⟩
    · obtain ⟨c, hc, hcs⟩ := hloop
      obtain ⟨F₁, hN₁, hoff₁, hcob₁, hsign⟩ := exists_flip hMc hne hm F hx₀ c hc hcs
      refine ⟨F₁, hN₁, hoff₁, hcob₁, fun h => ?_⟩
      rw [hsign h]
      rcases selfSign_mem hM (fun i => F.tangent i ⟨x₀, hx₀⟩) (F.indep ⟨x₀, hx₀⟩) with h0 | h0 <;>
        rcases selfSign_mem hM hvT hv with h1 | h1 <;> rw [h0, h1] <;>
        first
          | rfl
          | exact absurd (by rw [h0, h1] : selfSign hM x₀ (fun i => F.v i ⟨x₀, hx₀⟩) =
              selfSign hM x₀ v) heq
  -- change the frame inside a ball centred at `x₀`, the two points being equal
  have hx₀P : x₀ ∉ F.N \ {x₀} := fun h => h.2 rfl
  obtain ⟨R, hR, -, hmove⟩ :=
    move_in_ball hMc hne hm F (x₀ := x₀) x₀ hx₀P isOpen_univ (Set.mem_univ x₀)
  have hx₀B : x₀ ∈ ballU hM x₀ (R / 4) := x_c_mem_ballU x₀ (by positivity)
  have hx₀₁ : x₀ ∈ F₁.N := by rw [hN₁]; exact hx₀
  obtain ⟨F₂, hN₂, hoff₂, hv₂, hcob₂⟩ :=
    hmove x₀ hx₀B x₀ hx₀B F₁ (by rw [hN₁]; exact (Set.sdiff_union_of_subset
      (Set.singleton_subset_iff.2 hx₀)).symm) hoff₁ hx₀₁ v hvT hv
      (by rw [chartSign_self, chartSign_self, hs₁ hx₀₁])
  refine ⟨F₂, ?_, hoff₂, hv₂, hcob₁.trans hcob₂⟩
  rw [hN₂]; exact Set.sdiff_union_of_subset (Set.singleton_subset_iff.2 hx₀)

include hMc hne in
/-- **Reach, free of signs** — the drop-in replacement for the oriented
`Milnor.Framed.exists_reach`.  With a reversing ball loop at `x₀` avoiding the other points of
`F.N`, the point `x₀` of `F` may be moved to *any* point `y` of its component
`Milnor.compl' F.N x₀` and given *any* tangent independent frame `v` at `y`, up to framed
cobordism, the other points and frames being unchanged.  No orientation, and no hypothesis relating
the frame at `y` to the frame at `x₀`.

The loop is needed at `x₀` only: join `x₀` to `y` by a chain of balls avoiding the other points
(`Milnor.exists_isBallIn_avoiding`), flip at `x₀` if the chain's sign does not already carry the
self sign of `F` at `x₀` to that of `v` at `y`, slide along the chain
(`Milnor.Framed.exists_slide`), and finish with an in-class change of frame at `y`
(`Milnor.Framed.move_in_ball` with the two points equal). -/
theorem exists_reach_free (hm : 0 < m) (F : FramedSub hM 0 m) {x₀ : M} (hx₀ : x₀ ∈ F.N)
    (hloop : letI := hM.chartedSpace; haveI := hM.isManifold;
      ∃ c : ChartChain 𝓘(ℝ, Em) x₀ x₀, c.IsBallIn (F.N \ {x₀})ᶜ ∧ _root_.Milnor.chainSign c = -1)
    {y : M} (hy : y ∈ compl' F.N x₀) {v : Fin m → EK} (hvT : ∀ i, v i ∈ tangentM hM y)
    (hv : LinearIndependent ℝ v) :
    ∃ F' : FramedSub hM 0 m, F'.N = (F.N \ {x₀}) ∪ {y} ∧ AgreesOff F F' x₀ ∧
      (∀ i (hy' : y ∈ F'.N), F'.v i ⟨y, hy'⟩ = v i) ∧ FramedCobordant hM F F' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI := locallyConnectedSpace_M (hM := hM)
  -- a chain of balls from `x₀` to `y` avoiding the other points
  obtain ⟨c, -, -, hc⟩ := exists_isBallIn_avoiding (I := 𝓘(ℝ, Em))
    (isOpen_compl' F.finite_N x₀) isPreconnected_connectedComponentIn
    (Set.disjoint_left.2 fun a ha => compl'_subset F.N x₀ ha) mem_compl'_self hy
  have hcmem : _root_.Milnor.chainSign c = 1 ∨ _root_.Milnor.chainSign c = -1 :=
    _root_.Milnor.chainSign_eq_one_or_neg_one (I := 𝓘(ℝ, Em)) finrank_E c
  have hcs : _root_.Milnor.chainSign c * _root_.Milnor.chainSign c = 1 := by
    rcases hcmem with h | h <;> rw [h] <;> decide
  -- flip at `x₀` if the chain's sign does not carry the self sign of `F` to that of `v`
  obtain ⟨F₁, hN₁, hoff₁, hcob₁, hs₁⟩ : ∃ F₁ : FramedSub hM 0 m, F₁.N = F.N ∧
      AgreesOff F F₁ x₀ ∧ FramedCobordant hM F F₁ ∧
      ∀ h : x₀ ∈ F₁.N, selfSign hM x₀ (fun i => F₁.v i ⟨x₀, h⟩) =
        _root_.Milnor.chainSign c * selfSign hM y v := by
    by_cases heq : selfSign hM x₀ (fun i => F.v i ⟨x₀, hx₀⟩) =
        _root_.Milnor.chainSign c * selfSign hM y v
    · exact ⟨F, rfl, fun i a ha _ ha' => rfl, FramedCobordant.refl' hMc hne F, fun _ => heq⟩
    · obtain ⟨c₀, hc₀, hc₀s⟩ := hloop
      obtain ⟨F₁, hN₁, hoff₁, hcob₁, hsign⟩ := exists_flip hMc hne hm F hx₀ c₀ hc₀ hc₀s
      refine ⟨F₁, hN₁, hoff₁, hcob₁, fun h => ?_⟩
      rw [hsign h]
      have hmem' : _root_.Milnor.chainSign c * selfSign hM y v = 1 ∨
          _root_.Milnor.chainSign c * selfSign hM y v = -1 := by
        rcases hcmem with h1 | h1 <;> rcases selfSign_mem hM hvT hv with h2 | h2 <;>
          rw [h1, h2] <;> decide
      rcases selfSign_mem hM (fun i => F.tangent i ⟨x₀, hx₀⟩) (F.indep ⟨x₀, hx₀⟩) with h0 | h0 <;>
        rcases hmem' with h1 | h1 <;> rw [h0, h1] <;>
        first
          | rfl
          | exact absurd (by rw [h0, h1] : selfSign hM x₀ (fun i => F.v i ⟨x₀, hx₀⟩) =
              _root_.Milnor.chainSign c * selfSign hM y v) heq
  -- slide along the chain
  have hx₀₁ : x₀ ∈ F₁.N := by rw [hN₁]; exact hx₀
  have hc₁ : _root_.Milnor.ChartChain.IsBallIn (I := 𝓘(ℝ, Em)) (F₁.N \ {x₀})ᶜ c := by
    rw [hN₁]; exact hc
  obtain ⟨F₂, hN₂, hoff₂, hcob₂, hs₂⟩ := exists_slide hMc hne hm F₁ hx₀₁ c hc₁
  rw [hN₁] at hN₂
  have hy₂ : y ∈ F₂.N := by rw [hN₂]; exact Or.inr rfl
  have hs₂' : selfSign hM y (fun i => F₂.v i ⟨y, hy₂⟩) = selfSign hM y v := by
    rw [hs₂ hy₂, hs₁ hx₀₁, ← mul_assoc, hcs, one_mul]
  -- change the frame at `y` within its class
  have hyP : y ∉ F.N \ {x₀} := compl'_subset F.N x₀ hy
  obtain ⟨R, hR, -, hmove⟩ :=
    move_in_ball hMc hne hm F (x₀ := x₀) y hyP isOpen_univ (Set.mem_univ y)
  have hyB : y ∈ ballU hM y (R / 4) := x_c_mem_ballU y (by positivity)
  obtain ⟨F₃, hN₃, hoff₃, hv₃, hcob₃⟩ :=
    hmove y hyB y hyB F₂ hN₂
      (hoff₁.trans' (by rw [hN₁]; exact Set.sdiff_subset) (fun h => h.2 rfl) hoff₂) hy₂ v hvT hv
      (by rw [chartSign_self, chartSign_self, hs₂'])
  exact ⟨F₃, hN₃, hoff₃, hv₃, (hcob₁.trans hcob₂).trans hcob₃⟩

end Slide

end Framed

end Milnor
