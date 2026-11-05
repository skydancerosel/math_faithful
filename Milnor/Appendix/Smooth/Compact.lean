import Milnor.Appendix.Smooth.Affine
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Milnor's Appendix, smooth version: the compact case with boundary

Milnor, *Topology from the Differentiable Viewpoint*, Appendix (book p. 54), classifies the
connected one-manifolds into four cases.  This file is **Stage 6** of the plan
`Exposition/PlanOneManifold.md`, and it is the first stage whose conclusion is one of Milnor's four
cases: **a compact connected smooth one-manifold with a boundary point is diffeomorphic to
`Icc (0 : ℝ) 1`, and its boundary consists of exactly two points.**

## What is proved

**The exhausting arc.**

* `exists_closed_unitSpeedArc`: the finite-cover induction of Milnor's Step 2, run with *unit-speed*
  arcs.  From a boundary point `p` of a compact Hausdorff `C^∞` one-manifold there is a unit-speed
  smooth arc `A` with `Milnor.OneManifold.IsFrom A.toArc p` whose target attains its supremum.
* `exists_unitSpeedArc_component`: unwinding that, a unit-speed smooth arc starting at `p` with
  coordinate `0`, with target `Icc 0 ℓ` for some `ℓ > 0`, whose source is **the whole connected
  component of `p`**, and which identifies the boundary inside that component as `{p, A.invFun ℓ}`.
* `exists_unitSpeedArc_of_preconnected`: if the manifold is moreover preconnected, the source is all
  of `M` and the boundary is `{p, A.invFun ℓ}`.

**The rescaling and the diffeomorphism.**

* `SmoothArc.equivIcc`: the bijection `x ↦ A.toFun x / ℓ` of `M` with `Icc (0 : ℝ) 1`, with inverse
  `t ↦ A.invFun (ℓ * t)`, for a smooth arc whose source is everything and whose target is `Icc 0 ℓ`.
* `SmoothArc.diffeomorphIcc`: that bijection **as a `Mathlib` `Diffeomorph I (𝓡∂ 1) M (Icc 0 1) ∞`**.
  The two `simp` lemmas `SmoothArc.coe_diffeomorphIcc` and `SmoothArc.diffeomorphIcc_symm_apply`
  say in so many words that the diffeomorphism *is* the arc, rescaled by `1/ℓ`.
* `nonempty_diffeomorphIcc`: **a compact preconnected Hausdorff `C^∞` one-manifold with a boundary
  point is diffeomorphic to `Icc (0 : ℝ) 1`.**  This is Milnor's second case.

**The boundary.**

* `boundary_eq_pair`: the boundary is exactly `{p, q}` with `q ≠ p`, and `q` is the far endpoint of
  the exhausting arc.  This is **Milnor's own corollary**, and it is strictly stronger than
  `Milnor.OneManifold.even_ncard_boundary` in this case: it *identifies* the two boundary points
  instead of merely counting them modulo `2`.
* `ncard_boundary_eq_two`: the boundary has cardinality exactly `2`.

## What had to be restated, and why

`Milnor.OneManifold.exists_closed_arc` -- the finite-cover induction -- **cannot be reused**, for
three independent reasons, so its statement is restated here (as `exists_closed_unitSpeedArc`) with
its proof structure copied line for line.  Nothing in `Milnor/Appendix/OneManifold.lean` is edited.

1. *Its conclusion is a topological `Arc`.*  The induction is a loop that feeds its own output back
   in, so the object it carries has to be the object the next step consumes.  Stage 6 needs a
   `SmoothArc` of unit speed at every turn of the loop, and no theorem about topological arcs can
   produce one.
2. *Its extension step is the wrong theorem.*  The plan (Stage 6) says the existing induction can be
   used "with unit-speed arcs and smoothness added".  It cannot, because
   `Milnor.OneManifold.exists_extension` does not record that the extended arc's coordinate agrees
   with the old one; Stage 5 therefore restated it as
   `Milnor.OneManifold.Smooth.exists_extension_unitSpeed`, and that is the theorem the loop here
   calls.
3. *Its hypothesis `BoundaryCompatible φ B` is not available in this generality.*  It asks for a
   homeomorphism `φ : H ≃ₜ Ici (0 : ℝ)` of the model space with a half-line, which Stage 0 supplies
   only when the model range is a half-line (`Milnor.OneManifold.Smooth.boundaryCompatible`).  Stage
   0 allows the model range to be a compact interval as well -- a one-manifold with corners -- and
   in that shape there is no such `φ`.  The smooth route needs none: Stage 4's
   `exists_unitSpeed_of_mem_boundary` and `exists_unitSpeed_of_notMem_boundary` cover all three
   shapes of the model range uniformly.

Everything *below* the induction is reused verbatim from `Milnor/Appendix/OneManifold.lean`: the
whole `Arc` API, `IsFrom` and all five of its lemmas (in particular
`Milnor.OneManifold.IsFrom.source_eq_of_mem` and
`Milnor.OneManifold.IsFrom.boundary_inter_component`, which are what make the source the whole
component and identify the two boundary points), and `exists_mem_closure_of_ne`.

## Hypotheses, and which step uses what

`E` is a real normed space with `Module.finrank ℝ E = 1`, `I : ModelWithCorners ℝ E H`, and `M` is a
`C^∞` manifold charted on `H` (`IsManifold I ∞ M`).  Beyond that:

* `T2Space M` is used twice: by Stage 3 to build a length element, and by Stage 5's extension
  theorem (through the `overlap`/`trans` API of the existing file, which is stated for Hausdorff
  spaces).
* `CompactSpace M` is used three times, and **σ-compactness would not do for any of them**: to
  extract a *finite* subcover of `M` by sources of unit-speed arcs, which is what makes the
  induction terminate; to know that `connectedComponent p` is compact, which is what forbids a
  proper open sub-arc from exhausting it; and, through `CompactSpace.sigmaCompact`, to feed Stage 3.
  Only the last of the three is a σ-compactness use in disguise: a length element exists on any
  Hausdorff σ-compact one-manifold (`Milnor.OneManifold.Smooth.nonempty_lengthElement`), so that
  step could be relaxed, but the other two are genuinely compactness.
* **Connectedness is needed only for the last two conclusions, and then only preconnectedness.**
  `exists_closed_unitSpeedArc` and `exists_unitSpeedArc_component` assume nothing about
  connectedness: they produce an arc whose source is exactly the connected component of `p`, which
  is the honest statement, and which is what the eventual assembly (Stage 9, components of a
  possibly disconnected compact one-manifold) will want.  `PreconnectedSpace M` is added only to
  turn `connectedComponent p = univ`, and `Nonempty M` is not needed on top of it because the
  boundary point `p` is an argument.
* No boundarylessness anywhere, and no second-countability hypothesis: in the compact case
  σ-compactness is automatic, which is the reason this case needs no countability assumption at all
  (see `Exposition/PlanOneManifold.md` §7.1).

## What the conversion to a `Diffeomorph` costs

Almost nothing, thanks to Mathlib's two bridges.  `contMDiff_iff_comp_subtypeVal_Icc` reduces
smoothness of the map *into* `Icc 0 1` to continuity plus smoothness of its real-valued composite,
which is the arc's own coordinate divided by `ℓ`; and `contMDiffOn_comp_projIcc_iff` reduces
smoothness of the map *out of* `Icc 0 1` to smoothness on the real interval `Icc 0 1` of its
composite with `Set.projIcc`, which there is `u ↦ A.invFun (ℓ * u)` -- the arc's own parametrization,
smooth on `Icc 0 ℓ` by the arc's `contMDiffOn_invFun` field.  Neither bridge needs `IsManifold` on
`M`, and neither needs boundarylessness.  The only real work is bookkeeping: `Set.projIcc` has to be
discharged on the interval, and the two membership side conditions `A.toFun x / ℓ ∈ Icc 0 1` and
`ℓ * t ∈ Icc 0 ℓ` have to be checked.

## References

* Milnor, *Topology from the Differentiable Viewpoint*, Appendix, p. 54 (Step 2 and the corollary
  that a compact one-manifold with boundary has exactly two boundary points per component).
* `Exposition/PlanOneManifold.md`, Stage 6 and §6.
-/

open Set Filter Topology

open scoped ContDiff Manifold

noncomputable section

namespace Milnor.OneManifold.Smooth

/-! ## The finite-cover induction, restated for unit-speed arcs -/

section Induction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [CompactSpace M] [IsManifold I ∞ M]

include hE

/-- **Milnor's Step 2, for unit-speed arcs**: starting from a boundary point `p` of a compact
Hausdorff `C^∞` one-manifold, a unit-speed smooth arc can be extended until its target attains its
supremum.

This is `Milnor.OneManifold.exists_closed_arc` restated for `SmoothArc`s of unit speed; see the
module docstring for the three reasons the topological theorem cannot be applied instead.  The proof
is the original one line for line: cover `M` by the sources of unit-speed arcs (Stage 4's
`exists_unitSpeed`, one arc per point), take a *finite* subcover indexed by a `Finset s`, start from
a unit-speed arc at `p` with half-open target (Stage 4's `exists_unitSpeed_of_mem_boundary`), and
induct on the number of members of the subcover not yet swallowed.  At each step, if the supremum is
not attained then the source is a proper open subset of the component of `p` -- proper because the
component is compact, so a surjection onto it would give a compact target -- hence it has a limit
point `x` outside itself, and the arc of the subcover containing `x` extends it by Stage 5's
`exists_extension_unitSpeed`, swallowing at least one more member.

Hypotheses: `Module.finrank ℝ E = 1`; `IsManifold I ∞ M`; `T2Space M` (for Stage 5); `CompactSpace M`
(for the finite subcover and for compactness of the component); and a length element `L`, which
`nonempty_lengthElement` supplies. -/
theorem exists_closed_unitSpeedArc (L : LengthElement I ∞ M) {p : M} (hp : p ∈ I.boundary M) :
    ∃ A : SmoothArc I ∞ M, UnitSpeed L A ∧ IsFrom A.toArc p ∧ sSup A.target ∈ A.target := by
  classical
  -- Cover `M` by the sources of unit-speed arcs, one arc per point, and take a finite subcover.
  have hcov : ∀ y : M, ∃ A : SmoothArc I ∞ M, UnitSpeed L A ∧ y ∈ A.source := fun y => by
    obtain ⟨A, -, -, hyA, -, -, hu⟩ := exists_unitSpeed I hE L y
    exact ⟨A, hu, hyA⟩
  choose 𝒜 h𝒜u h𝒜 using hcov
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => (𝒜 y).source)
    (fun y => (𝒜 y).open_source) (fun y _ => mem_iUnion.2 ⟨y, h𝒜 y⟩)
  -- The initial arc: unit speed, half-open target, starting at `p`.
  obtain ⟨A₀, ε, hε, hpA, hp0, hT, hu₀⟩ := exists_unitSpeed_of_mem_boundary I hE L hp
  have hfrom₀ : IsFrom A₀.toArc p := ⟨hpA, hp0, by rw [hT]; exact ⟨le_rfl, hε⟩,
    by rw [hT]; exact Ico_subset_Ici_self⟩
  suffices key : ∀ n : ℕ, ∀ A : SmoothArc I ∞ M, UnitSpeed L A → IsFrom A.toArc p →
      (s.filter fun y => ¬ (𝒜 y).source ⊆ A.source).card = n →
      ∃ A' : SmoothArc I ∞ M, UnitSpeed L A' ∧ IsFrom A'.toArc p ∧ sSup A'.target ∈ A'.target from
    key _ A₀ hu₀ hfrom₀ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hAu hA hn
  by_cases hc : sSup A.target ∈ A.target
  · exact ⟨A, hAu, hA, hc⟩
  set c := sSup A.target with hcdef
  have hT : A.target = Ico 0 c :=
    hA.target_eq.resolve_right (fun h => hc (by rw [h]; exact ⟨hA.pos.le, le_rfl⟩))
  -- The source cannot already be the whole component: the component is compact.
  have hne : A.source ≠ connectedComponent p := by
    intro h
    have hcomp : IsCompact A.source := by rw [h]; exact isClosed_connectedComponent.isCompact
    have hcT : IsCompact A.target := by
      rw [← A.image_source]; exact hcomp.image_of_continuousOn A.continuousOn_toFun
    exact hc (hcT.isClosed.csSup_mem A.nontrivial_target.nonempty A.bddAbove_target)
  obtain ⟨x, hxcl, hxA⟩ :=
    exists_mem_closure_of_ne A.open_source hA.1 hA.source_subset_component hne
  obtain ⟨y, hys, hxy⟩ := mem_iUnion₂.1 (hs (mem_univ x))
  obtain ⟨Ã, hÃu, -, -, h1, h2, h3, h4, hAsub, hysub⟩ :=
    exists_extension_unitSpeed L A (𝒜 y) hAu (h𝒜u y) hA.pos hA.1 hA.2.1 hT hxy hxA hxcl
  have hfrom : IsFrom Ã.toArc p := ⟨h1, h2, h3, h4⟩
  have hsub : (s.filter fun z => ¬ (𝒜 z).source ⊆ Ã.source) ⊆
      (s.filter fun z => ¬ (𝒜 z).source ⊆ A.source) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, fun h => hz.2 (h.trans hAsub)⟩
  have hcard : (s.filter fun z => ¬ (𝒜 z).source ⊆ Ã.source).card < n := by
    rw [← hn]
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset hsub).2 ⟨y, ?_, ?_⟩
    · rw [Finset.mem_filter]; exact ⟨hys, fun h => hxA (h hxy)⟩
    · rw [Finset.mem_filter]; exact fun h => h.2 hysub
  exact ih _ hcard Ã hÃu hfrom rfl

/-- **A unit-speed arc from a boundary point that exhausts its component.**  For a compact Hausdorff
`C^∞` one-manifold and a boundary point `p`, there is a unit-speed smooth arc `A` and a length
`ℓ > 0` such that `A` sends `p` to `0`, has target exactly `Icc 0 ℓ`, has source exactly the
connected component of `p`, and meets the boundary inside that component in exactly the two points
`p` and `A.invFun ℓ`.

This is the conclusion Stage 6 exists to produce.  Once `exists_closed_unitSpeedArc` has been run,
everything here is read off the reused `IsFrom` API of `Milnor/Appendix/OneManifold.lean`:
`IsFrom.target_eq_Icc` gives the shape of the target, `IsFrom.source_eq_of_mem` gives the source
(the source is compact, hence clopen in the component, hence all of it), and
`IsFrom.boundary_inter_component` gives the two boundary points.

**Connectedness is not assumed**; the honest conclusion is about the component of `p`. -/
theorem exists_unitSpeedArc_component (L : LengthElement I ∞ M) {p : M} (hp : p ∈ I.boundary M) :
    ∃ (A : SmoothArc I ∞ M) (ℓ : ℝ), 0 < ℓ ∧ UnitSpeed L A ∧ p ∈ A.source ∧ A.toFun p = 0 ∧
      A.target = Icc 0 ℓ ∧ A.source = connectedComponent p ∧
      I.boundary M ∩ connectedComponent p = {p, A.invFun ℓ} := by
  obtain ⟨A, hAu, hA, hc⟩ := exists_closed_unitSpeedArc I hE L hp
  exact ⟨A, sSup A.target, hA.pos, hAu, hA.1, hA.2.1, hA.target_eq_Icc hc,
    hA.source_eq_of_mem hc, hA.boundary_inter_component hc⟩

/-- **A unit-speed arc from a boundary point that exhausts the manifold.**  The preconnected case of
`exists_unitSpeedArc_component`: when `M` is preconnected the component of `p` is all of `M`, so the
arc's source is `univ` and the boundary of `M` is exactly `{p, A.invFun ℓ}`.

`PreconnectedSpace M` is all that is needed -- `Nonempty M` comes free with the boundary point `p`
-- and it is used only here and downstream, never in the induction. -/
theorem exists_unitSpeedArc_of_preconnected [PreconnectedSpace M] (L : LengthElement I ∞ M) {p : M}
    (hp : p ∈ I.boundary M) :
    ∃ (A : SmoothArc I ∞ M) (ℓ : ℝ), 0 < ℓ ∧ UnitSpeed L A ∧ p ∈ A.source ∧ A.toFun p = 0 ∧
      A.target = Icc 0 ℓ ∧ A.source = univ ∧ I.boundary M = {p, A.invFun ℓ} := by
  obtain ⟨A, ℓ, hℓ, hAu, hpA, hp0, htgt, hsrc, hbdry⟩ :=
    exists_unitSpeedArc_component I hE L hp
  have huniv : connectedComponent p = univ := PreconnectedSpace.connectedComponent_eq_univ p
  refine ⟨A, ℓ, hℓ, hAu, hpA, hp0, htgt, by rw [hsrc, huniv], ?_⟩
  rw [← hbdry, huniv, inter_univ]

end Induction

/-! ## Rescaling an exhausting arc to a diffeomorphism with `Icc 0 1` -/

section Rescale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

namespace SmoothArc

variable (A : SmoothArc I ∞ M) {ℓ : ℝ}

/-- The rescaled coordinate of an exhausting arc lands in the unit interval: if the arc's source is
everything and its target is `Icc 0 ℓ`, then `A.toFun x / ℓ ∈ Icc 0 1` for every `x`. -/
theorem toFun_div_mem_unitIcc (hℓ : 0 < ℓ) (hsrc : A.source = univ) (htgt : A.target = Icc 0 ℓ)
    (x : M) : A.toFun x / ℓ ∈ Icc (0 : ℝ) 1 := by
  have hx : A.toFun x ∈ Icc (0 : ℝ) ℓ := by
    rw [← htgt]; exact A.map_source (by rw [hsrc]; trivial)
  exact ⟨div_nonneg hx.1 hℓ.le, (div_le_one hℓ).2 hx.2⟩

/-- The rescaled parameter of an exhausting arc lands in its target: if the arc's target is
`Icc 0 ℓ` with `ℓ > 0`, then `ℓ * t ∈ A.target` for every `t` in the unit interval. -/
theorem mul_mem_target (hℓ : 0 < ℓ) (htgt : A.target = Icc 0 ℓ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ℓ * t ∈ A.target := by
  rw [htgt]
  refine ⟨mul_nonneg hℓ.le ht.1, ?_⟩
  calc ℓ * t ≤ ℓ * 1 := mul_le_mul_of_nonneg_left ht.2 hℓ.le
    _ = ℓ := mul_one ℓ

/-- **The arc, rescaled: the underlying bijection with the unit interval.**  For a smooth arc whose
source is all of `M` and whose target is `Icc 0 ℓ` with `ℓ > 0`, the map `x ↦ A.toFun x / ℓ` is a
bijection of `M` onto `Icc (0 : ℝ) 1`, with inverse `t ↦ A.invFun (ℓ * t)`.  Both inverse laws are
the arc's own two inverse laws, after cancelling `ℓ`. -/
def equivIcc (hℓ : 0 < ℓ) (hsrc : A.source = univ) (htgt : A.target = Icc 0 ℓ) :
    M ≃ Icc (0 : ℝ) 1 where
  toFun x := ⟨A.toFun x / ℓ, A.toFun_div_mem_unitIcc hℓ hsrc htgt x⟩
  invFun t := A.invFun (ℓ * t)
  left_inv x := by
    have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
    show A.invFun (ℓ * (A.toFun x / ℓ)) = x
    rw [show ℓ * (A.toFun x / ℓ) = A.toFun x by field_simp]
    exact A.left_inv (by rw [hsrc]; trivial)
  right_inv t := by
    have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
    apply Subtype.ext
    show A.toFun (A.invFun (ℓ * (t : ℝ))) / ℓ = (t : ℝ)
    rw [A.right_inv (A.mul_mem_target hℓ htgt t.2)]
    field_simp

/-- The bijection of `SmoothArc.equivIcc` is the arc's coordinate divided by the arc's length. -/
@[simp] theorem coe_equivIcc (hℓ : 0 < ℓ) (hsrc : A.source = univ) (htgt : A.target = Icc 0 ℓ)
    (x : M) : ((A.equivIcc hℓ hsrc htgt x : Icc (0 : ℝ) 1) : ℝ) = A.toFun x / ℓ := rfl

/-- The inverse of `SmoothArc.equivIcc` is the arc's parametrization, run at speed `ℓ`. -/
@[simp] theorem equivIcc_symm_apply (hℓ : 0 < ℓ) (hsrc : A.source = univ)
    (htgt : A.target = Icc 0 ℓ) (t : Icc (0 : ℝ) 1) :
    (A.equivIcc hℓ hsrc htgt).symm t = A.invFun (ℓ * (t : ℝ)) := rfl

/-- **The arc, rescaled: the diffeomorphism.**  For a smooth arc of a `C^∞` one-manifold whose
source is all of `M` and whose target is `Icc 0 ℓ` with `ℓ > 0`, the rescaled coordinate
`x ↦ A.toFun x / ℓ` is a `C^∞` diffeomorphism of `M` onto `Icc (0 : ℝ) 1`, with `Mathlib`'s model
with corners `𝓡∂ 1` on the interval.

Smoothness in both directions is the two `Mathlib` bridges of `Mathlib/Geometry/Manifold/Instances/`
`Icc.lean`.  Forwards, `contMDiff_iff_comp_subtypeVal_Icc` asks for continuity plus smoothness of
the real-valued composite `x ↦ A.toFun x / ℓ`, which is the arc's `contMDiffOn_toFun` field (on
`A.source = univ`, hence globally) followed by division by a constant.  Backwards,
`contMDiffOn_comp_projIcc_iff` asks for smoothness *on the interval* `Icc 0 1` of
`u ↦ A.invFun (ℓ * u)`, which is the arc's `contMDiffOn_invFun` field (on `A.target = Icc 0 ℓ`)
precomposed with `u ↦ ℓ * u`; `Set.projIcc` is the identity on `Icc 0 1`, which is the only
bookkeeping.

No hypothesis beyond `ChartedSpace H M` is used -- in particular not `IsManifold I ∞ M`, not
Hausdorffness and not compactness; those are what produce the arc, not what turns it into a
diffeomorphism. -/
def diffeomorphIcc (hℓ : 0 < ℓ) (hsrc : A.source = univ) (htgt : A.target = Icc 0 ℓ) :
    Diffeomorph I (𝓡∂ 1) M (Icc (0 : ℝ) 1) ∞ where
  toEquiv := A.equivIcc hℓ hsrc htgt
  contMDiff_toFun := by
    have hA : ContMDiff I 𝓘(ℝ, ℝ) ∞ A.toFun := by
      rw [← contMDiffOn_univ, ← hsrc]; exact A.contMDiffOn_toFun
    have hdiv : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => A.toFun x / ℓ) :=
      ((contDiff_id.div_const ℓ).contMDiff).comp hA
    rw [contMDiff_iff_comp_subtypeVal_Icc]
    exact ⟨hdiv.continuous.subtype_mk _, hdiv⟩
  contMDiff_invFun := by
    have hmul : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun u : ℝ => ℓ * u) (Icc 0 1) :=
      ((contDiff_const.mul contDiff_id).contMDiff).contMDiffOn
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun u : ℝ => A.invFun (ℓ * u)) (Icc 0 1) :=
      A.contMDiffOn_invFun.comp hmul fun u hu => A.mul_mem_target hℓ htgt hu
    rw [← contMDiffOn_comp_projIcc_iff]
    refine hcomp.congr fun u hu => ?_
    have hproj : ((Set.projIcc (0 : ℝ) 1 (by norm_num) u : Icc (0 : ℝ) 1) : ℝ) = u := by
      rw [Set.coe_projIcc, min_eq_right hu.2, max_eq_right hu.1]
    simp only [Function.comp_apply, equivIcc_symm_apply, hproj]

/-- The diffeomorphism of `SmoothArc.diffeomorphIcc` is the arc's coordinate divided by the arc's
length: a reader can see that it *is* the arc, rescaled. -/
@[simp] theorem coe_diffeomorphIcc (hℓ : 0 < ℓ) (hsrc : A.source = univ)
    (htgt : A.target = Icc 0 ℓ) (x : M) :
    ((A.diffeomorphIcc hℓ hsrc htgt x : Icc (0 : ℝ) 1) : ℝ) = A.toFun x / ℓ := rfl

/-- The inverse of `SmoothArc.diffeomorphIcc` is the arc's parametrization, run at speed `ℓ`. -/
@[simp] theorem diffeomorphIcc_symm_apply (hℓ : 0 < ℓ) (hsrc : A.source = univ)
    (htgt : A.target = Icc 0 ℓ) (t : Icc (0 : ℝ) 1) :
    (A.diffeomorphIcc hℓ hsrc htgt).symm t = A.invFun (ℓ * (t : ℝ)) := rfl

end SmoothArc

end Rescale

/-! ## The classification in the compact case with boundary -/

section Classification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [CompactSpace M] [PreconnectedSpace M] [IsManifold I ∞ M]

include hE

/-- **Milnor's Appendix, the second case (book p. 54): a compact connected smooth one-manifold with
a boundary point is diffeomorphic to `Icc (0 : ℝ) 1`.**

Precisely: let `E` be a real normed space of dimension one, `I : ModelWithCorners ℝ E H`, and `M` a
compact, Hausdorff, preconnected `C^∞` manifold charted on `H`.  If `M` has a boundary point, then
`M` is `C^∞`-diffeomorphic to `Icc (0 : ℝ) 1` with `Mathlib`'s model `𝓡∂ 1`.

The diffeomorphism is exhibited, not merely asserted: it is `SmoothArc.diffeomorphIcc` applied to
the exhausting unit-speed arc of `exists_unitSpeedArc_of_preconnected`, that is, the arc-length
coordinate measured from the boundary point `p` and divided by the total length `ℓ`.

Hypotheses: `Module.finrank ℝ E = 1`, `IsManifold I ∞ M`, `T2Space M`, `CompactSpace M`,
`PreconnectedSpace M`, and a boundary point.  No boundarylessness, no second-countability (compact
plus Hausdorff gives it), and no orientability.  The length element is built internally from
`T2Space M` and `CompactSpace.sigmaCompact`. -/
theorem nonempty_diffeomorphIcc {p : M} (hp : p ∈ I.boundary M) :
    Nonempty (Diffeomorph I (𝓡∂ 1) M (Icc (0 : ℝ) 1) ∞) := by
  obtain ⟨L⟩ := nonempty_lengthElement I hE M
  obtain ⟨A, ℓ, hℓ, -, -, -, htgt, hsrc, -⟩ := exists_unitSpeedArc_of_preconnected I hE L hp
  exact ⟨A.diffeomorphIcc hℓ hsrc htgt⟩

/-- **Milnor's corollary: the boundary of a compact connected smooth one-manifold with boundary
consists of exactly two points**, the given one and the far endpoint of the exhausting arc.

This is strictly stronger than the existing `Milnor.OneManifold.even_ncard_boundary` in this case:
that theorem says the boundary is finite of even cardinality, by a parity argument on a fixed-point
free involution; this one *identifies* the two points, `p` and `A.invFun ℓ`, as the two ends of a
single arc-length parametrization of `M`.

Hypotheses as in `nonempty_diffeomorphIcc`. -/
theorem boundary_eq_pair {p : M} (hp : p ∈ I.boundary M) :
    ∃ q, q ∈ I.boundary M ∧ q ≠ p ∧ I.boundary M = {p, q} := by
  obtain ⟨L⟩ := nonempty_lengthElement I hE M
  obtain ⟨A, ℓ, hℓ, -, hpA, hp0, htgt, hsrc, hbdry⟩ :=
    exists_unitSpeedArc_of_preconnected I hE L hp
  have hℓt : ℓ ∈ A.target := by rw [htgt]; exact ⟨hℓ.le, le_rfl⟩
  refine ⟨A.invFun ℓ, ?_, ?_, hbdry⟩
  · exact (Set.ext_iff.1 hbdry _).2 (mem_insert_of_mem _ rfl)
  · intro h
    have hv := congrArg A.toFun h
    rw [A.right_inv hℓt, hp0] at hv
    exact hℓ.ne' hv

/-- **The boundary of a compact connected smooth one-manifold with boundary has cardinality exactly
two.**  The numerical form of `boundary_eq_pair`, for comparison with the existing
`Milnor.OneManifold.even_ncard_boundary`, which in this case only gives "finite and even". -/
theorem ncard_boundary_eq_two {p : M} (hp : p ∈ I.boundary M) : (I.boundary M).ncard = 2 := by
  obtain ⟨q, -, hqp, hbdry⟩ := boundary_eq_pair I hE hp
  rw [hbdry]
  exact Set.ncard_pair (Ne.symm hqp)

end Classification

end Milnor.OneManifold.Smooth
