import Milnor.Appendix.OneManifold

/-!
# Milnor's Appendix Lemma 1: the overlap of two arcs has at most two components

Milnor, *Topology from the Differentiable Viewpoint*, Appendix (book p. 54), Lemma 1: if two
arc-length parametrizations of a 1-manifold overlap, the set of parameters where they overlap has
at most two components, and on each component the transition is `t ↦ ±t + c`.

This file is **Stage 2** of `Exposition/PlanOneManifold.md`, and it proves the *topological half*
of that lemma: **no smoothness and no arc length are used anywhere**, only that the two arcs are
homeomorphisms from open subsets of a Hausdorff space onto bounded intervals of `ℝ`, in the sense
of `Milnor.OneManifold.Arc` from `Milnor/Appendix/OneManifold.lean`.  The affine form of the
transition — the half of the lemma that genuinely needs unit speed — is left to a later stage.

`Milnor/Appendix/OneManifold.lean` already contains all the hard analysis: the end lemma
(`Milnor.OneManifold.end_lemma`) and its two corollaries, the monotone/antitone dichotomy for a
continuous injection on an interval, the one-sided limits of a monotone transition at an unattained
end, the packaged dichotomy `end_right` / `end_left`, and the two lemmas
`not_upper_of_sSup_mem` / `not_lower_of_sInf_mem` saying that a component cannot run off an end
that `A'` attains.  (The two "clash" lemmas `clash_upper` / `clash_lower` turn out not to be needed
here: once a component is known to run off *both* ends of `A'.target`, its transition image is
already all of `A'.target`, and injectivity of the transition rules out any second component
directly.)

What that file proves about the *shape* of the overlap, however, is
`Milnor.OneManifold.overlap_ordConnected`: the overlap is a single interval — under the extra
hypothesis that the first arc starts at a *boundary* point with coordinate `0`.  That hypothesis
excludes the circle by fiat: for a circle covered by a long arc `A` and a short arc `A'` across the
gap, the overlap really does have two components.  Here that hypothesis is dropped, and the true
statement is proved instead.

## Main results

Throughout, `A` and `A'` are arcs of a Hausdorff space `M` relative to a set `B`,
`S = overlap A A'` is the set of `A`-coordinates of the common source, and the *components* of `S`
are its hulls `hull S t₀` (`Milnor.OneManifold.hull`), the maximal intervals it contains.  The
existing file shows that they cover `S`, are order-connected, are pairwise equal or disjoint, and
are relatively open in `A.target`, so they are indeed the connected components of `S`; that
identification is nowhere needed below, and everything is stated about hulls.

* `Milnor.OneManifold.IsInnerHull A A' t₀`: both ends of the component of `t₀` lie in the interior
  of `A.target`.
* `Milnor.OneManifold.image_trans_hull_eq_of_isInnerHull`: an inner component is carried by the
  transition map *onto* the whole of `A'.target`.
* `Milnor.OneManifold.hull_eq_of_isInnerHull`, `overlap_eq_hull_of_isInnerHull`,
  `ordConnected_overlap_of_isInnerHull`: an inner component is the *only* component, so the overlap
  is then a single interval.
* `Milnor.OneManifold.sInf_eq_or_sSup_eq_of_not_isInnerHull`: any other component reaches an end of
  `A.target`.
* `Milnor.OneManifold.hull_eq_of_three`, `exists_pair_hull`, `encard_hulls_le_two`: **at most two
  components**, because the two ends of `A.target` cannot be reached twice.
* `Milnor.OneManifold.sInf_eq_and_sSup_eq_of_hull_ne`: two distinct components reach *opposite*
  ends of `A.target`, which is Milnor's picture of the two-component (circle) case.

Byproducts of the inner case, recording that it is the case in which `A'` is swallowed by `A`:
`Milnor.OneManifold.target_eq_Ioo_of_isInnerHull` (then `A'.target` is an open interval),
`notMem_boundary_of_isInnerHull` and its contrapositive `not_isInnerHull_of_mem_boundary` (an inner
component forces `A'` to contain no point of `B`, so an arc `A'` that does contain one never yields
an inner component) and `source_subset_of_isInnerHull` (then `A'.source ⊆ A.source`).

No boundary hypothesis, no charts, no compactness and no `BoundaryCompatible` are used.  The
hypotheses are exactly: `M` Hausdorff (already needed for `end_lemma`, through uniqueness of
limits) and the two arcs' data, of which boundedness and nontriviality of the two targets are used
essentially — they are fields of `Arc`, so nothing new is assumed.
-/

open Set

noncomputable section

namespace Milnor
namespace OneManifold

/-! ### Two disjoint intervals of `ℝ` cannot share an end

`Milnor.OneManifold.inter_nonempty_of_sInf_eq` already says this when the common infimum is
attained by neither of them.  The remaining case is elementary: if one of the two *does* attain it,
it is the minimum, and since that interval has a second point the other interval has to enter it.
-/

section Intervals

/-- Two disjoint nontrivial intervals of `ℝ` that are bounded below have different infima. -/
theorem sInf_ne_sInf_of_disjoint {I₁ I₂ : Set ℝ} (h₁ : I₁.OrdConnected) (h₂ : I₂.OrdConnected)
    (hn₁ : I₁.Nontrivial) (hn₂ : I₂.Nontrivial) (hb₁ : BddBelow I₁) (hb₂ : BddBelow I₂)
    (hd : Disjoint I₁ I₂) : sInf I₁ ≠ sInf I₂ := by
  -- the case in which the first of the two intervals attains the common infimum
  have key : ∀ J₁ J₂ : Set ℝ, J₁.OrdConnected → J₁.Nontrivial → BddBelow J₁ → J₂.Nonempty →
      BddBelow J₂ → Disjoint J₁ J₂ → sInf J₁ = sInf J₂ → sInf J₁ ∈ J₁ → False := by
    intro J₁ J₂ hJo hJn hJb hKn hKb hJd heq hmem
    obtain ⟨v, hv, hvne⟩ := hJn.exists_ne (sInf J₁)
    have hlt : sInf J₁ < v := lt_of_le_of_ne (csInf_le hJb hv) (Ne.symm hvne)
    obtain ⟨u, hu, huv⟩ := exists_lt_of_csInf_lt hKn (by rw [← heq]; exact hlt)
    have hune : sInf J₁ ≠ u := fun h => hJd.notMem_of_mem_left hmem (h ▸ hu)
    have hlu : sInf J₁ < u := lt_of_le_of_ne (by rw [heq]; exact csInf_le hKb hu) hune
    exact hJd.notMem_of_mem_left (hJo.out hmem hv ⟨hlu.le, huv.le⟩) hu
  intro heq
  by_cases hm₁ : sInf I₁ ∈ I₁
  · exact key I₁ I₂ h₁ hn₁ hb₁ hn₂.nonempty hb₂ hd heq hm₁
  by_cases hm₂ : sInf I₂ ∈ I₂
  · exact key I₂ I₁ h₂ hn₂ hb₂ hn₁.nonempty hb₁ hd.symm heq.symm hm₂
  obtain ⟨u, hu₁, hu₂⟩ :=
    inter_nonempty_of_sInf_eq h₁ h₂ hn₁.nonempty hn₂.nonempty hb₁ hb₂ heq hm₁ hm₂
  exact hd.notMem_of_mem_left hu₁ hu₂

/-- Two disjoint nontrivial intervals of `ℝ` that are bounded above have different suprema. -/
theorem sSup_ne_sSup_of_disjoint {I₁ I₂ : Set ℝ} (h₁ : I₁.OrdConnected) (h₂ : I₂.OrdConnected)
    (hn₁ : I₁.Nontrivial) (hn₂ : I₂.Nontrivial) (hb₁ : BddAbove I₁) (hb₂ : BddAbove I₂)
    (hd : Disjoint I₁ I₂) : sSup I₁ ≠ sSup I₂ := by
  -- the case in which the first of the two intervals attains the common supremum
  have key : ∀ J₁ J₂ : Set ℝ, J₁.OrdConnected → J₁.Nontrivial → BddAbove J₁ → J₂.Nonempty →
      BddAbove J₂ → Disjoint J₁ J₂ → sSup J₁ = sSup J₂ → sSup J₁ ∈ J₁ → False := by
    intro J₁ J₂ hJo hJn hJb hKn hKb hJd heq hmem
    obtain ⟨v, hv, hvne⟩ := hJn.exists_ne (sSup J₁)
    have hlt : v < sSup J₁ := lt_of_le_of_ne (le_csSup hJb hv) hvne
    obtain ⟨u, hu, huv⟩ := exists_lt_of_lt_csSup hKn (by rw [← heq]; exact hlt)
    have hune : u ≠ sSup J₁ := fun h => hJd.notMem_of_mem_left hmem (h ▸ hu)
    have hlu : u < sSup J₁ := lt_of_le_of_ne (by rw [heq]; exact le_csSup hKb hu) hune
    exact hJd.notMem_of_mem_left (hJo.out hv hmem ⟨huv.le, hlu.le⟩) hu
  intro heq
  by_cases hm₁ : sSup I₁ ∈ I₁
  · exact key I₁ I₂ h₁ hn₁ hb₁ hn₂.nonempty hb₂ hd heq hm₁
  by_cases hm₂ : sSup I₂ ∈ I₂
  · exact key I₂ I₁ h₂ hn₂ hb₂ hn₁.nonempty hb₁ hd.symm heq.symm hm₂
  obtain ⟨u, hu₁, hu₂⟩ :=
    inter_nonempty_of_sSup_eq h₁ h₂ hn₁.nonempty hn₂.nonempty hb₁ hb₂ heq hm₁ hm₂
  exact hd.notMem_of_mem_left hu₁ hu₂

end Intervals

/-! ### The components of the overlap, with no hypothesis on either arc

The existing file proves the facts below only after normalizing `A` to an arc that starts at a
boundary point with `A.target = Ico 0 c`; the normalization is never used, only the two endpoints
`sInf A.target` and `sSup A.target`, so the proofs carry over verbatim.
-/

section Components

variable {M : Type*} [TopologicalSpace M] [T2Space M] {B : Set M} (A A' : Arc M B)

local notation "S" => overlap A A'
local notation "τ" => trans A A'

/-- Every component of the overlap is bounded above, the target of `A` being bounded. -/
theorem bddAbove_hull_overlap (t₀ : ℝ) : BddAbove (hull S t₀) :=
  A.bddAbove_target.mono ((hull_subset S t₀).trans (overlap_subset A A'))

/-- Every component of the overlap is bounded below, the target of `A` being bounded. -/
theorem bddBelow_hull_overlap (t₀ : ℝ) : BddBelow (hull S t₀) :=
  A.bddBelow_target.mono ((hull_subset S t₀).trans (overlap_subset A A'))

/-- A component of the overlap starts no lower than the target of `A` does. -/
theorem sInf_target_le_sInf_hull {t₀ : ℝ} (ht₀ : t₀ ∈ S) : sInf A.target ≤ sInf (hull S t₀) :=
  csInf_le_csInf A.bddBelow_target ⟨t₀, mem_hull_self ht₀⟩
    ((hull_subset S t₀).trans (overlap_subset A A'))

/-- A component of the overlap ends no higher than the target of `A` does. -/
theorem sSup_hull_le_sSup_target {t₀ : ℝ} (ht₀ : t₀ ∈ S) : sSup (hull S t₀) ≤ sSup A.target :=
  csSup_le_csSup A.bddAbove_target ⟨t₀, mem_hull_self ht₀⟩
    ((hull_subset S t₀).trans (overlap_subset A A'))

/-- Every component of the overlap has more than one point: the overlap is relatively open in the
target of `A`, which is an interval with more than one point, so a point of the overlap has a
neighbour in the overlap on at least one side. -/
theorem hull_overlap_nontrivial {t₀ : ℝ} (ht₀ : t₀ ∈ S) : (hull S t₀).Nontrivial := by
  have hm := mem_hull_self ht₀
  have ht₀T : t₀ ∈ A.target := overlap_subset A A' ht₀
  rcases lt_or_eq_of_le (le_csSup A.bddAbove_target ht₀T) with h | h
  · obtain ⟨v, hv, hlt⟩ := exists_gt_mem_hull A A' hm h
    exact ⟨v, hv, t₀, hm, hlt.ne'⟩
  · obtain ⟨v, hv, hlt⟩ := exists_lt_mem_hull A A' hm (by rw [h]; exact A.sInf_lt_sSup)
    exact ⟨v, hv, t₀, hm, hlt.ne⟩

/-- If a component of the overlap ends strictly below the end of the target of `A`, its own end is
not in the overlap: otherwise the component could be continued past it. -/
theorem sSup_hull_notMem_overlap {t₀ : ℝ} (ht₀ : t₀ ∈ S)
    (hlt : sSup (hull S t₀) < sSup A.target) : sSup (hull S t₀) ∉ S := by
  intro hmem
  have hb := bddAbove_hull_overlap A A' t₀
  obtain ⟨v, hv, hlt'⟩ := exists_gt_mem_hull A A' (sSup_mem_hull ht₀ hb hmem) hlt
  exact lt_irrefl _ (hlt'.trans_le (le_csSup hb hv))

/-- If a component of the overlap starts strictly above the start of the target of `A`, its own
start is not in the overlap. -/
theorem sInf_hull_notMem_overlap {t₀ : ℝ} (ht₀ : t₀ ∈ S)
    (hlt : sInf A.target < sInf (hull S t₀)) : sInf (hull S t₀) ∉ S := by
  intro hmem
  have hb := bddBelow_hull_overlap A A' t₀
  obtain ⟨v, hv, hlt'⟩ := exists_lt_mem_hull A A' (sInf_mem_hull ht₀ hb hmem) hlt
  exact lt_irrefl _ ((csInf_le hb hv).trans_lt hlt')

/-- Two different components of the overlap start at different points. -/
theorem sInf_hull_ne {t₁ t₂ : ℝ} (h₁ : t₁ ∈ S) (h₂ : t₂ ∈ S) (hne : hull S t₁ ≠ hull S t₂) :
    sInf (hull S t₁) ≠ sInf (hull S t₂) :=
  sInf_ne_sInf_of_disjoint (hull_ordConnected S t₁) (hull_ordConnected S t₂)
    (hull_overlap_nontrivial A A' h₁) (hull_overlap_nontrivial A A' h₂)
    (bddBelow_hull_overlap A A' t₁) (bddBelow_hull_overlap A A' t₂)
    (hull_eq_or_disjoint.resolve_left hne)

/-- Two different components of the overlap end at different points. -/
theorem sSup_hull_ne {t₁ t₂ : ℝ} (h₁ : t₁ ∈ S) (h₂ : t₂ ∈ S) (hne : hull S t₁ ≠ hull S t₂) :
    sSup (hull S t₁) ≠ sSup (hull S t₂) :=
  sSup_ne_sSup_of_disjoint (hull_ordConnected S t₁) (hull_ordConnected S t₂)
    (hull_overlap_nontrivial A A' h₁) (hull_overlap_nontrivial A A' h₂)
    (bddAbove_hull_overlap A A' t₁) (bddAbove_hull_overlap A A' t₂)
    (hull_eq_or_disjoint.resolve_left hne)

end Components

/-! ### Inner components

A component of the overlap is *inner* when neither of its two ends is an end of `A.target`.  Such a
component runs off *both* ends of `A'.target`, so the transition carries it onto all of
`A'.target`; by injectivity of the transition there is then nothing left for a second component.
-/

section Inner

variable {M : Type*} [TopologicalSpace M] [T2Space M] {B : Set M} (A A' : Arc M B)

local notation "S" => overlap A A'
local notation "τ" => trans A A'

/-- A component of the overlap is **inner** when both of its ends lie in the interior of the target
of `A`, i.e. when neither end is an end of `A.target`. -/
def IsInnerHull (t₀ : ℝ) : Prop :=
  sInf (hull S t₀) ∈ interior A.target ∧ sSup (hull S t₀) ∈ interior A.target

/-- Being inner, spelled out with the two endpoints of the target of `A`. -/
theorem isInnerHull_iff {t₀ : ℝ} (ht₀ : t₀ ∈ S) :
    IsInnerHull A A' t₀ ↔
      sInf A.target < sInf (hull S t₀) ∧ sSup (hull S t₀) < sSup A.target := by
  have hlt : sInf (hull S t₀) < sSup (hull S t₀) := by
    obtain ⟨a, ha, b, hb, hab⟩ := hull_overlap_nontrivial A A' ht₀
    have hI := bddBelow_hull_overlap A A' t₀
    have hS := bddAbove_hull_overlap A A' t₀
    rcases lt_or_gt_of_ne hab with h | h
    · exact (csInf_le hI ha).trans_lt (h.trans_le (le_csSup hS hb))
    · exact (csInf_le hI hb).trans_lt (h.trans_le (le_csSup hS ha))
  simp only [IsInnerHull, A.interior_target, mem_Ioo]
  exact ⟨fun h => ⟨h.1.1, h.2.2⟩, fun h => ⟨⟨h.1, hlt.trans h.2⟩, ⟨h.1.trans hlt, h.2⟩⟩⟩

/-- **An inner component runs off both ends of `A'.target`.**  Its two ends lie in `A.target` but
not in the overlap, so `Milnor.OneManifold.end_right` and `Milnor.OneManifold.end_left` apply; the
transition is strictly monotone or strictly antitone on the component, and either way one of the
two ends supplies the upper conclusion and the other the lower one. -/
theorem upper_lower_of_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hin : IsInnerHull A A' t₀) :
    (∀ t ∈ A'.target, t < sSup (τ '' hull S t₀)) ∧
      (∀ t ∈ A'.target, sInf (τ '' hull S t₀) < t) := by
  obtain ⟨hlow, hupp⟩ := (isInnerHull_iff A A' ht₀).1 hin
  have hR := end_right A A' ht₀ (bddAbove_hull_overlap A A' t₀) (interior_subset hin.2)
    (sSup_hull_notMem_overlap A A' ht₀ hupp)
  have hL := end_left A A' ht₀ (bddBelow_hull_overlap A A' t₀) (interior_subset hin.1)
    (sInf_hull_notMem_overlap A A' ht₀ hlow)
  rcases strictMonoOn_or_strictAntiOn_of_ordConnected (hull_ordConnected S t₀)
      (hull_overlap_nontrivial A A' ht₀) ((trans_continuousOn A A').mono (hull_subset S t₀))
      ((trans_injOn A A').mono (hull_subset S t₀)) with hm | ha
  · exact ⟨hR.1 hm, hL.1 hm⟩
  · exact ⟨hL.2 ha, hR.2 ha⟩

/-- If the overlap has an inner component, the target of `A'` does not attain its supremum. -/
theorem sSup_target'_notMem_of_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hin : IsInnerHull A A' t₀) :
    sSup A'.target ∉ A'.target := fun hmax =>
  not_upper_of_sSup_mem A A' (hull_subset S t₀) ⟨t₀, mem_hull_self ht₀⟩ hmax
    (upper_lower_of_isInnerHull A A' ht₀ hin).1

/-- If the overlap has an inner component, the target of `A'` does not attain its infimum. -/
theorem sInf_target'_notMem_of_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hin : IsInnerHull A A' t₀) :
    sInf A'.target ∉ A'.target := fun hmin =>
  not_lower_of_sInf_mem A A' (hull_subset S t₀) ⟨t₀, mem_hull_self ht₀⟩ hmin
    (upper_lower_of_isInnerHull A A' ht₀ hin).2

/-- If the overlap has an inner component, the target of `A'` is an *open* interval. -/
theorem target_eq_Ioo_of_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hin : IsInnerHull A A' t₀) :
    A'.target = Ioo (sInf A'.target) (sSup A'.target) := by
  refine Subset.antisymm (fun t ht => ⟨?_, ?_⟩) A'.Ioo_subset_target
  · refine lt_of_le_of_ne (csInf_le A'.bddBelow_target ht) fun h => ?_
    exact sInf_target'_notMem_of_isInnerHull A A' ht₀ hin (by rw [h]; exact ht)
  · refine lt_of_le_of_ne (le_csSup A'.bddAbove_target ht) fun h => ?_
    exact sSup_target'_notMem_of_isInnerHull A A' ht₀ hin (by rw [← h]; exact ht)

/-- If the overlap has an inner component, the target of `A'` is its own interior. -/
theorem interior_target_eq_of_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hin : IsInnerHull A A' t₀) :
    interior A'.target = A'.target :=
  A'.interior_target.trans (target_eq_Ioo_of_isInnerHull A A' ht₀ hin).symm

/-- If the overlap has an inner component, no point of the source of `A'` belongs to `B`: the arc
`A'` contains no boundary point.  (This is why the inner case is invisible in
`Milnor.OneManifold.overlap_ordConnected`, which starts `A` at a boundary point.) -/
theorem notMem_boundary_of_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hin : IsInnerHull A A' t₀)
    {x : M} (hx : x ∈ A'.source) : x ∉ B := by
  intro hxB
  rw [A'.bdry x hx, interior_target_eq_of_isInnerHull A A' ht₀ hin] at hxB
  exact hxB (A'.map_source hx)

/-- Contrapositive of the preceding lemma: as soon as `A'` contains a boundary point, no component
of the overlap is inner, so every component reaches an end of `A.target`. -/
theorem not_isInnerHull_of_mem_boundary {t₀ : ℝ} (ht₀ : t₀ ∈ S) {x : M} (hx : x ∈ A'.source)
    (hxB : x ∈ B) : ¬IsInnerHull A A' t₀ := fun hin =>
  notMem_boundary_of_isInnerHull A A' ht₀ hin hx hxB

/-- **The transition carries an inner component onto the whole of `A'.target`.**  The image is an
interval whose infimum and supremum are those of `A'.target`, and neither is attained, while
`A'.target` is the open interval between them. -/
theorem image_trans_hull_eq_of_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hin : IsInnerHull A A' t₀) :
    τ '' hull S t₀ = A'.target := by
  obtain ⟨hU, hD⟩ := upper_lower_of_isInnerHull A A' ht₀ hin
  have hsub : τ '' hull S t₀ ⊆ A'.target := image_trans_subset A A' (hull_subset S t₀)
  have hoc : (τ '' hull S t₀).OrdConnected :=
    ordConnected_image_trans A A' (hull_subset S t₀) (hull_ordConnected S t₀)
  have hne : (τ '' hull S t₀).Nonempty := ⟨τ t₀, t₀, mem_hull_self ht₀, rfl⟩
  have hsup : sSup (τ '' hull S t₀) = sSup A'.target :=
    le_antisymm (csSup_le_csSup A'.bddAbove_target hne hsub)
      (csSup_le A'.nontrivial_target.nonempty fun t ht => (hU t ht).le)
  have hinf : sInf (τ '' hull S t₀) = sInf A'.target :=
    le_antisymm (le_csInf A'.nontrivial_target.nonempty fun t ht => (hD t ht).le)
      (csInf_le_csInf A'.bddBelow_target hne hsub)
  refine Subset.antisymm hsub fun t ht => ?_
  rw [target_eq_Ioo_of_isInnerHull A A' ht₀ hin] at ht
  obtain ⟨u, hu, hut⟩ := exists_lt_of_csInf_lt hne (by rw [hinf]; exact ht.1)
  obtain ⟨v, hv, htv⟩ := exists_lt_of_lt_csSup hne (by rw [hsup]; exact ht.2)
  exact hoc.out hu hv ⟨hut.le, htv.le⟩

/-- **An inner component is the only component.**  Any point of the overlap has the same transition
value as a point of the inner component, because the transition is already onto `A'.target` there;
the transition is injective on the overlap, so the two points coincide. -/
theorem hull_eq_of_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hin : IsInnerHull A A' t₀) {t : ℝ}
    (ht : t ∈ S) : hull S t = hull S t₀ := by
  have h : τ t ∈ τ '' hull S t₀ := by
    rw [image_trans_hull_eq_of_isInnerHull A A' ht₀ hin]; exact trans_mem_target A A' ht
  obtain ⟨s, hs, hst⟩ := h
  have hts : s = t := trans_injOn A A' (hull_subset S t₀ hs) ht hst
  exact hull_eq_of_mem (hts ▸ hs)

/-- If the overlap has an inner component, it *is* that component. -/
theorem overlap_eq_hull_of_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hin : IsInnerHull A A' t₀) :
    S = hull S t₀ := by
  refine Subset.antisymm (fun t ht => ?_) (hull_subset S t₀)
  rw [← hull_eq_of_isInnerHull A A' ht₀ hin ht]
  exact mem_hull_self ht

/-- If the overlap has an inner component, the overlap is an interval.  This is
`Milnor.OneManifold.overlap_ordConnected` in the case that lemma's boundary hypothesis excludes. -/
theorem ordConnected_overlap_of_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hin : IsInnerHull A A' t₀) :
    (overlap A A').OrdConnected := by
  rw [overlap_eq_hull_of_isInnerHull A A' ht₀ hin]
  exact hull_ordConnected S t₀

/-- If the overlap has an inner component then `A'` is swallowed by `A`. -/
theorem source_subset_of_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hin : IsInnerHull A A' t₀) :
    A'.source ⊆ A.source := by
  intro y hy
  have h : A'.toFun y ∈ τ '' hull S t₀ := by
    rw [image_trans_hull_eq_of_isInnerHull A A' ht₀ hin]; exact A'.map_source hy
  obtain ⟨s, hs, hsy⟩ := h
  have hmem := invFun_mem_of_mem_overlap A A' (hull_subset S t₀ hs)
  have hys : A.invFun s = y := A'.injOn hmem.2 hy hsy
  exact hys ▸ hmem.1

end Inner

/-! ### At most two components

A component that is not inner has one of its ends at an end of `A.target`; two different components
cannot use the same end, since they are disjoint nontrivial intervals; and a third component would
have to be inner, hence the only one.
-/

section Counting2

variable {M : Type*} [TopologicalSpace M] [T2Space M] {B : Set M} (A A' : Arc M B)

local notation "S" => overlap A A'

/-- A component of the overlap that is not inner reaches an end of the target of `A`. -/
theorem sInf_eq_or_sSup_eq_of_not_isInnerHull {t₀ : ℝ} (ht₀ : t₀ ∈ S)
    (h : ¬ IsInnerHull A A' t₀) :
    sInf (hull S t₀) = sInf A.target ∨ sSup (hull S t₀) = sSup A.target := by
  rw [isInnerHull_iff A A' ht₀, not_and_or, not_lt, not_lt] at h
  rcases h with h | h
  · exact Or.inl (le_antisymm h (sInf_target_le_sInf_hull A A' ht₀))
  · exact Or.inr (le_antisymm (sSup_hull_le_sSup_target A A' ht₀) h)

/-- **Milnor's Appendix Lemma 1, topological half: the overlap of two arcs has at most two
components.**  Of any three points of the overlap, two lie in the same component.

Indeed, if the three components were distinct then none could be inner (an inner one is the only
one), so each would reach an end of `A.target`; but there are only two ends, and two different
components cannot reach the same one. -/
theorem hull_eq_of_three {t₁ t₂ t₃ : ℝ} (h₁ : t₁ ∈ S) (h₂ : t₂ ∈ S) (h₃ : t₃ ∈ S) :
    hull S t₁ = hull S t₂ ∨ hull S t₁ = hull S t₃ ∨ hull S t₂ = hull S t₃ := by
  by_contra hcon
  rw [not_or, not_or] at hcon
  obtain ⟨h12, h13, h23⟩ := hcon
  have hn₁ : ¬ IsInnerHull A A' t₁ := fun hin =>
    h12 (hull_eq_of_isInnerHull A A' h₁ hin h₂).symm
  have hn₂ : ¬ IsInnerHull A A' t₂ := fun hin =>
    h12 (hull_eq_of_isInnerHull A A' h₂ hin h₁)
  have hn₃ : ¬ IsInnerHull A A' t₃ := fun hin =>
    h13 (hull_eq_of_isInnerHull A A' h₃ hin h₁)
  rcases sInf_eq_or_sSup_eq_of_not_isInnerHull A A' h₁ hn₁ with l₁ | r₁
  · rcases sInf_eq_or_sSup_eq_of_not_isInnerHull A A' h₂ hn₂ with l₂ | r₂
    · exact sInf_hull_ne A A' h₁ h₂ h12 (l₁.trans l₂.symm)
    · rcases sInf_eq_or_sSup_eq_of_not_isInnerHull A A' h₃ hn₃ with l₃ | r₃
      · exact sInf_hull_ne A A' h₁ h₃ h13 (l₁.trans l₃.symm)
      · exact sSup_hull_ne A A' h₂ h₃ h23 (r₂.trans r₃.symm)
  · rcases sInf_eq_or_sSup_eq_of_not_isInnerHull A A' h₂ hn₂ with l₂ | r₂
    · rcases sInf_eq_or_sSup_eq_of_not_isInnerHull A A' h₃ hn₃ with l₃ | r₃
      · exact sInf_hull_ne A A' h₂ h₃ h23 (l₂.trans l₃.symm)
      · exact sSup_hull_ne A A' h₁ h₃ h13 (r₁.trans r₃.symm)
    · exact sSup_hull_ne A A' h₁ h₂ h12 (r₁.trans r₂.symm)

/-- **At most two components**, in the form of two sets exhausting them. -/
theorem exists_pair_hull : ∃ C₁ C₂ : Set ℝ, ∀ t ∈ S, hull S t = C₁ ∨ hull S t = C₂ := by
  by_cases hS : (overlap A A').Nonempty
  · obtain ⟨t₁, ht₁⟩ := hS
    by_cases hall : ∀ t ∈ S, hull S t = hull S t₁
    · exact ⟨hull S t₁, hull S t₁, fun t ht => Or.inl (hall t ht)⟩
    · obtain ⟨t₂, ht₂, hne⟩ : ∃ t ∈ S, hull S t ≠ hull S t₁ := by
        by_contra hc
        exact hall fun t ht => by by_contra h; exact hc ⟨t, ht, h⟩
      refine ⟨hull S t₁, hull S t₂, fun t ht => ?_⟩
      rcases hull_eq_of_three A A' ht₁ ht₂ ht with h | h | h
      · exact absurd h.symm hne
      · exact Or.inl h.symm
      · exact Or.inr h.symm
  · exact ⟨∅, ∅, fun t ht => absurd (Set.nonempty_of_mem ht) hS⟩

/-- **At most two components**, as a bound on the number of hulls. -/
theorem encard_hulls_le_two : ((fun t => hull S t) '' S).encard ≤ 2 := by
  obtain ⟨C₁, C₂, hC⟩ := exists_pair_hull A A'
  have hsub : (fun t => hull S t) '' S ⊆ {C₁, C₂} := by
    rintro _ ⟨t, ht, rfl⟩
    exact hC t ht
  refine (Set.encard_le_encard hsub).trans ?_
  refine (Set.encard_insert_le _ _).trans ?_
  rw [Set.encard_singleton]
  exact le_of_eq one_add_one_eq_two

/-- **The two-component case is Milnor's picture:** two different components of the overlap reach
*opposite* ends of the target of `A`. -/
theorem sInf_eq_and_sSup_eq_of_hull_ne {t₁ t₂ : ℝ} (h₁ : t₁ ∈ S) (h₂ : t₂ ∈ S)
    (hne : hull S t₁ ≠ hull S t₂) :
    (sInf (hull S t₁) = sInf A.target ∧ sSup (hull S t₂) = sSup A.target) ∨
      (sSup (hull S t₁) = sSup A.target ∧ sInf (hull S t₂) = sInf A.target) := by
  have hn₁ : ¬ IsInnerHull A A' t₁ := fun hin =>
    hne (hull_eq_of_isInnerHull A A' h₁ hin h₂).symm
  have hn₂ : ¬ IsInnerHull A A' t₂ := fun hin =>
    hne (hull_eq_of_isInnerHull A A' h₂ hin h₁)
  rcases sInf_eq_or_sSup_eq_of_not_isInnerHull A A' h₁ hn₁ with l₁ | r₁
  · rcases sInf_eq_or_sSup_eq_of_not_isInnerHull A A' h₂ hn₂ with l₂ | r₂
    · exact absurd (l₁.trans l₂.symm) (sInf_hull_ne A A' h₁ h₂ hne)
    · exact Or.inl ⟨l₁, r₂⟩
  · rcases sInf_eq_or_sSup_eq_of_not_isInnerHull A A' h₂ hn₂ with l₂ | r₂
    · exact Or.inr ⟨r₁, l₂⟩
    · exact absurd (r₁.trans r₂.symm) (sSup_hull_ne A A' h₁ h₂ hne)

end Counting2

end OneManifold
end Milnor
