import Milnor.Chapter7.Slide
import Milnor.Chapter7.Cancel
import Milnor.Chapter7.Puncture

/-!
# Cancelling *any* two neighbouring framed points (Milnor §7, p. 50)

**Stage 7 of `Exposition/PlanMod2.md`**, the sign-free cancellation.  Milnor's remark at the end of
§7 (book p. 50) is that on a connected non-orientable manifold the signed count of a framed
`0`-manifold degenerates to a count modulo `2`, because a framed point carried around an
orientation-reversing loop comes back with its frame reversed.  Stage 6 (`Chapter7/Slide.lean`)
performed that carrying; this file removes the signs from the cancellation machinery of
`Chapter7/CancelStep.lean`, so that *any* two distinct neighbouring points of a framed `0`-manifold
cancel, not only a pair of opposite signs.

Three things are proved.

* **Frames are free at two points** (`Milnor.Framed.framedCobordant_of_frames_free`): if two framed
  `0`-manifolds have the same point set and the same frames away from two distinct points `u ≠ z`,
  they are framed cobordant — with *no* condition relating the frames at `u` and at `z`.  This is
  `Milnor.Framed.framedCobordant_of_frames` (`Chapter7/CancelStep.lean`) with its two sign
  hypotheses deleted, and it is proved in the same way, with Stage 6's
  `Milnor.Framed.exists_frame_free` in place of the oriented `Milnor.Framed.exists_reach`.

* **The sign-free cancel step** (`Milnor.Framed.cancel_step_free`): if `x₀ ≠ z` are points of `F.N`
  and `z` lies in the closure of the component of `x₀` in `M ∖ (F.N ∖ {x₀})`, then `F` is framed
  cobordant to `F` with `x₀` and `z` removed.  This is `Milnor.Framed.cancel_step` with its
  opposite-sign hypothesis `hsign` deleted and replaced by the availability of reversing ball loops.

* **The neighbour pair** (`Milnor.Framed.exists_neighbour_pair`): a framed `0`-manifold of a
  connected `M` with two distinct points has two distinct points one of which is in the closure of
  the component of the other.  This is `Milnor.Framed.exists_opposite_neighbour`
  (`Chapter7/Main.lean`) with the signs deleted; the partition fed to the neighbour lemma is
  `{x} ⊔ (F.N ∖ {x})` instead of a partition by sign.

## The reversing loop as a hypothesis

As the plan prescribes, the reversing loop is carried as a hypothesis in the uniform shape

```
hflip : ∀ P : Set M, P.Finite → ∀ x ∉ P, HasReversingBallLoop 𝓘(ℝ, Eᵐ) P x
```

so that Stage 9 can discharge it *once*, from Stage 5's punctured dichotomy
`Milnor.hasReversingBallLoop_of_not_isOrientable`, which proves exactly this for a connected
non-orientable manifold of dimension at least two.  Nothing in this file assumes `2 ≤ m`, and no
orientation of `M` occurs anywhere; `0 < m`, `IsCompact M` and `M.Nonempty` are the only standing
hypotheses, the last two being what the Theorem-B machinery behind the moves needs.  `P` is always
instantiated to the set of the *other* points of a framed `0`-manifold, which is finite by
`Milnor.Framed.FramedSub.finite_N`.

## One simplification over the plan

The plan prescribes choosing, on arrival at the point `u` next to `z`, a frame whose chart sign in
the chart at `z` is the negative of the chart sign of `F`'s frame at `z`, and then splitting on
`chartSign hM z u v = 1` as `Milnor.Framed.cancel_step` splits on `s = ε`.  Neither is necessary.
The frames that `Milnor.Framed.exists_cancel_chartSign` needs at `u` and `z` — the standard frames
of the cancelling map, of chart signs `1` and `-1` — are installed by
`framedCobordant_of_frames_free`, which is indifferent to the frames it starts from; so the frame
carried to `u` may be *any* tangent independent frame there, and the roles of `u` and `z` in the
cancelling pair need not be exchanged.  `cancel_step_free` is therefore shorter than the
`cancel_step` it replaces, and this is the precise sense in which "cancel a plus against a minus"
becomes "cancel any two points".
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} (hMc : IsCompact M) (hne : M.Nonempty)

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "EK" => EuclideanSpace ℝ (Fin (K + 1))

/-! ### Changing two frames, with no condition on the signs -/

include hMc hne in
/-- **Changing the frames at two distinct points to anything.**  If `F₀` differs from `F₁` only in
the frames at two distinct points `u` and `z`, then `F₁` and `F₀` are framed cobordant — no relation
between the old and the new frames at `u` and at `z` is required.

This is `Milnor.Framed.framedCobordant_of_frames` with both sign hypotheses deleted; a reversing
ball loop at each of the two points, avoiding the other points of the framed set, replaces them.
The proof is the same: change the frame at `u`, then the frame at `z`, each time by Stage 6's
`Milnor.Framed.exists_frame_free`, and observe with `Milnor.Framed.FramedSub.ext'` that the result
is `F₀`. -/
theorem framedCobordant_of_frames_free (hm : 0 < m)
    (hflip : letI := hM.chartedSpace; haveI := hM.isManifold;
      ∀ P : Set M, P.Finite → ∀ x ∉ P, HasReversingBallLoop 𝓘(ℝ, Em) P x)
    {F₁ F₀ : FramedSub hM 0 m} {u z : M} (hu : u ∈ F₁.N) (hz : z ∈ F₁.N) (huz : u ≠ z)
    (hN : F₀.N = F₁.N)
    (hoff : ∀ i x (hx : x ∈ F₁.N), x ≠ u → x ≠ z → ∀ hx' : x ∈ F₀.N,
      F₀.v i ⟨x, hx'⟩ = F₁.v i ⟨x, hx⟩) :
    FramedCobordant hM F₁ F₀ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hu₀ : u ∈ F₀.N := hN ▸ hu
  have hz₀ : z ∈ F₀.N := hN ▸ hz
  -- change the frame at `u` to `F₀`'s
  obtain ⟨F₂, hN₂, hoff₂, hv₂, hcob₂⟩ := exists_frame_free hMc hne hm F₁ hu
    (hflip (F₁.N \ {u}) F₁.finite_N.sdiff u (fun h => h.2 rfl))
    (fun i => F₀.tangent i ⟨u, hu₀⟩) (F₀.indep ⟨u, hu₀⟩)
  have hz₂ : z ∈ F₂.N := hN₂ ▸ hz
  -- change the frame at `z` to `F₀`'s
  obtain ⟨F₃, hN₃, hoff₃, hv₃, hcob₃⟩ := exists_frame_free hMc hne hm F₂ hz₂
    (hflip (F₂.N \ {z}) F₂.finite_N.sdiff z (fun h => h.2 rfl))
    (fun i => F₀.tangent i ⟨z, hz₀⟩) (F₀.indep ⟨z, hz₀⟩)
  -- `F₃ = F₀`
  have heq : F₃ = F₀ := by
    refine FramedSub.ext' hM (by rw [hN₃, hN₂, hN]) ?_
    intro i x hx₃ hx₀'
    by_cases hxz : x = z
    · subst hxz; exact hv₃ i hx₃
    · have hx₂ : x ∈ F₂.N := hN₃ ▸ hx₃
      rw [hoff₃ i x hx₂ hxz hx₃]
      by_cases hxu : x = u
      · subst hxu; exact hv₂ i hx₂
      · have hx₁ : x ∈ F₁.N := hN₂ ▸ hx₂
        rw [hoff₂ i x hx₁ hxu hx₂, hoff i x hx₁ hxu hxz hx₀']
  rw [← heq]
  exact hcob₂.trans hcob₃

/-! ### The sign-free cancel step -/

include hMc hne in
/-- **Cancelling any neighbouring pair of framed points.**  Let `F` be a framed `0`-manifold, let
`x₀ ≠ z` be two of its points, and let `z` lie in the closure of the connected component
`Milnor.compl' F.N x₀` of `x₀` in `M ∖ (F.N ∖ {x₀})`.  Then `F` is framed cobordant to a framed
`0`-manifold whose point set is `F.N` with `x₀` and `z` removed and whose remaining frames are those
of `F`.

This is `Milnor.Framed.cancel_step` with its hypothesis that the signs at `x₀` and `z` be opposite
deleted, and the availability of reversing ball loops put in its place.  The proof follows the
oriented one: take a good chart ball of radius `R` about `z` whose closure misses the other points of
`F.N` (`Milnor.Framed.exists_goodBall_free`), pick a point `u` of the component of `x₀` inside the
ball of radius `R/4` (possible since `z` is in the closure of that component), move `x₀` to `u` by
Stage 6's `Milnor.Framed.exists_reach_free` carrying an arbitrary frame, place `u` and `z` at the
positions `c₀ ± a • w₀` of a common chart ball, and cancel with
`Milnor.Framed.exists_cancel_chartSign`, the two standard frames it requires being installed by
`framedCobordant_of_frames_free`.  No sign is ever compared, and no case split on a sign occurs. -/
theorem cancel_step_free (hm : 0 < m) (F : FramedSub hM 0 m) {x₀ z : M} (hx₀ : x₀ ∈ F.N)
    (hz : z ∈ F.N) (hxz : x₀ ≠ z) (hnb : z ∈ closure (compl' F.N x₀))
    (hflip : letI := hM.chartedSpace; haveI := hM.isManifold;
      ∀ P : Set M, P.Finite → ∀ x ∉ P, HasReversingBallLoop 𝓘(ℝ, Em) P x) :
    ∃ F'' : FramedSub hM 0 m, F''.N = F.N \ {x₀, z} ∧
      (∀ i x (hx : x ∈ F.N), x ≠ x₀ → x ≠ z → ∀ hx' : x ∈ F''.N,
        F''.v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩) ∧
      FramedCobordant hM F F'' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set φ := extChartAt 𝓘(ℝ, Em) z with hφdef
  -- a good ball around `z` whose closure misses the other points of `F.N`
  obtain ⟨R, hR, hRt, hcl, -⟩ :=
    exists_goodBall_free (hM := hM) z (P := F.N \ {z}) (F.finite_N.sdiff) (fun h => h.2 rfl)
      isOpen_univ (mem_univ z)
  -- a point `u` of the component of `x₀`, close to `z`
  obtain ⟨u, huU, huC⟩ := mem_closure_iff.1 hnb (ballU hM z (R / 4)) (isOpen_ballU _ _)
    (x_c_mem_ballU z (by positivity))
  have hsub4 : ballU hM z (R / 4) ⊆ ballU hM z R := fun q hq => by
    rw [mem_ballU] at hq ⊢; exact ⟨hq.1, by linarith [hq.2]⟩
  have huR : u ∈ ballU hM z R := hsub4 huU
  have huNz : u ∉ F.N \ {z} := hcl u (subset_closure huR)
  have hux₀ : u ≠ x₀ := by
    rintro rfl
    exact huNz ⟨hx₀, hxz⟩
  have huz : u ≠ z := by
    rintro rfl
    exact compl'_subset F.N x₀ huC ⟨hz, fun h => hxz h.symm⟩
  have huN : u ∉ F.N := fun h => huNz ⟨h, huz⟩
  -- move `x₀` to `u`, carrying an arbitrary frame
  obtain ⟨v, hvT, hv, -⟩ := exists_frame_of_selfSign hM hm u (Or.inl rfl)
  obtain ⟨F₁, hN₁, hoff₁, -, hcob₁⟩ := exists_reach_free hMc hne hm F hx₀
    (hflip (F.N \ {x₀}) F.finite_N.sdiff x₀ (fun h => h.2 rfl)) huC hvT hv
  have hu₁ : u ∈ F₁.N := by rw [hN₁]; exact Or.inr rfl
  have hz₁ : z ∈ F₁.N := by rw [hN₁]; exact Or.inl ⟨hz, fun h => hxz h.symm⟩
  have hFU₁ : ∀ x ∈ F₁.N, x ≠ u → x ≠ z → x ∉ closure (ballU hM z R) := by
    intro x hx hxu hxz' hxc
    rw [hN₁] at hx
    rcases hx with ⟨hxF, -⟩ | hxu'
    · exact hcl x hxc ⟨hxF, hxz'⟩
    · exact hxu hxu'
  -- the chart positions of `u` and `z` as `c₀ ± a • w₀`
  have huU' := mem_ballU.1 huU
  set c := φ z with hcdef
  set p := φ u with hpdef
  have hpc : p ≠ c := fun h => huz (φ.injOn huU'.1 (mem_extChartAt_source z) h)
  have hpc' : 0 < ‖p - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hpc)
  set a : ℝ := ‖p - c‖ / 2 with hadef
  have ha : 0 < a := by positivity
  set w₀ : Em := ‖p - c‖⁻¹ • (p - c) with hw₀def
  have hw₀ : ‖w₀‖ = 1 := by
    rw [hw₀def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpc'.ne']
  set c₀ : Em := c + a • w₀ with hc₀def
  have haw : (2 * a) • w₀ = p - c := by
    rw [hadef, hw₀def, smul_smul]
    rw [show 2 * (‖p - c‖ / 2) * ‖p - c‖⁻¹ = 1 by field_simp, one_smul]
  have hφu : φ u = c₀ + a • w₀ := by
    rw [hc₀def, add_assoc, ← add_smul, show a + a = 2 * a by ring, haw]
    simp [hpdef, hcdef]
  have hφz : φ z = c₀ - a • w₀ := by
    rw [hc₀def]; simp [hcdef]
  have hc₀ : ‖c₀ - c‖ < R / 8 := by
    rw [hc₀def, add_sub_cancel_left, norm_smul, hw₀, mul_one, Real.norm_eq_abs, abs_of_pos ha,
      hadef]
    linarith [huU'.2]
  have haR : 8 * a ≤ R := by
    rw [hadef]; linarith [huU'.2]
  have hz_src : z ∈ φ.source := mem_extChartAt_source z
  -- cancel the pair `u`, `z`
  obtain ⟨F₀, F', hN₀, hoff₀, -, -, hN', hoff', hcob'⟩ :=
    exists_cancel_chartSign hMc hne hm F₁ z hR hRt hc₀ hw₀ ha haR hu₁ hz₁ huU'.1 hz_src hφu hφz
      hFU₁
  have hcob₀ : FramedCobordant hM F₁ F₀ :=
    framedCobordant_of_frames_free hMc hne hm hflip hu₁ hz₁ huz hN₀ hoff₀
  refine ⟨F', ?_, ?_, hcob₁.trans (hcob₀.trans hcob')⟩
  · rw [hN', hN₁]
    ext q
    simp only [Set.mem_sdiff, mem_union, mem_singleton_iff, mem_insert_iff]
    constructor
    · rintro ⟨⟨hq, hqx⟩ | rfl, hq'⟩
      · exact ⟨hq, fun h => h.elim hqx (fun h' => hq' (Or.inr h'))⟩
      · exact absurd (Or.inl rfl) hq'
    · rintro ⟨hq, hq'⟩
      refine ⟨Or.inl ⟨hq, fun h => hq' (Or.inl h)⟩, ?_⟩
      rintro (h | h)
      · exact huN (h ▸ hq)
      · exact hq' (Or.inr h)
  · intro i x hx hxx₀ hxz' hx''
    have hx₁ : x ∈ F₁.N := by rw [hN₁]; exact Or.inl ⟨hx, hxx₀⟩
    have hxu : x ≠ u := fun h => huN (h ▸ hx)
    rw [hoff' i x hx₁ hxu hxz' hx'', hoff₁ i x hx hxx₀ hx₁]

/-! ### A neighbouring pair of points -/

/-- **Two distinct points of a framed `0`-manifold, one in the closure of the component of the
other.**  If `F.N` has two distinct points and `M` is connected, then some point `x₀` of `F.N` has a
point `z ≠ x₀` of `F.N` in the closure of the connected component `Milnor.compl' F.N x₀` of `x₀` in
`M ∖ (F.N ∖ {x₀})` — that is, a pair on which `cancel_step_free` can be run.

This is `Milnor.Framed.exists_opposite_neighbour` with the signs deleted.  With no signs to sort the
points by, the partition of `F.N` handed to the neighbour lemma `Milnor.Framed.exists_neighbour_M` is
simply `{x} ⊔ (F.N ∖ {x})` for one chosen point `x`, which is a partition into two nonempty parts
exactly because `F.N` has a second point. -/
theorem exists_neighbour_pair (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    (F : FramedSub hM 0 m) {x y : M} (hx : x ∈ F.N) (hy : y ∈ F.N) (hxy : x ≠ y) :
    ∃ x₀ ∈ F.N, ∃ z ∈ F.N, x₀ ≠ z ∧ z ∈ closure (compl' F.N x₀) := by
  letI := hM.chartedSpace
  obtain ⟨x₀, hx₀B, z, hzB, hnb⟩ := exists_neighbour_M (hM := hM) hconn F.finite_N
    (B := {x}) (Set.singleton_subset_iff.2 hx) ⟨x, rfl⟩ ⟨y, hy, fun h => hxy h.symm⟩
  refine ⟨x₀, ?_, z, hzB.1, ?_, hnb⟩
  · rw [show x₀ = x from hx₀B]; exact hx
  · intro h; exact hzB.2 (h ▸ hx₀B)

end Framed

end Milnor
