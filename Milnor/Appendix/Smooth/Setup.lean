import Milnor.Appendix.OneManifold

/-!
# Milnor's Appendix, smooth version: the one-dimensional model, and the boundary for free

Milnor, *Topology from the Differentiable Viewpoint*, Appendix (book p. 54), classifies the
connected one-manifolds.  This file is **Stage 0** of the plan
`Exposition/PlanOneManifold.md`, which builds that classification on top of the topological
Appendix of `Milnor/Appendix/OneManifold.lean`.

Throughout, `M` is a manifold charted on a model with corners `I : ModelWithCorners ℝ E H` whose
model vector space `E` is one-dimensional: `Module.finrank ℝ E = 1`.  Nothing here assumes that
`I` is boundaryless, that `M` is Hausdorff, or that `M` is compact.

## What is proved

* `Milnor.OneManifold.Smooth.closed_convex_cases`: a closed convex subset of `ℝ` with nonempty
  interior is `univ`, `Ici a`, `Iic a`, or a nondegenerate `Icc a b`.
* `Milnor.OneManifold.Smooth.modelCoord`: a *normalised* linear identification `E ≃L[ℝ] ℝ`, chosen
  (this is where the sign is fixed) so that the model range `Set.range I`, read through it, is
  `univ`, a half-line `Ici a`, or a nondegenerate compact interval `Icc a b` -- never `Iic a`.
  `modelRange_cases` records exactly these **three cases**, which recur below; the third of them is
  a "one-manifold with corners", and it is allowed throughout.
* `uniqueDiffOn_modelRange`, `derivWithin_modelRange_eq`: derivatives along the model range are
  unique, so `derivWithin` is unambiguous even at an endpoint of the range.
* `chartCoord`: the real coordinate attached to an arbitrary chart of `M`.
* `mem_boundary_iff_chartCoord_mem_frontier`: **the boundary is chart-independent** -- for a `C¹`
  manifold, a point of the source of *any* chart of the atlas is a boundary point exactly when its
  real coordinate lies on the frontier of the model range.  This is Mathlib's
  `ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas`, transported to the real coordinate.
* `boundaryCompatible`: the hypothesis `Milnor.OneManifold.BoundaryCompatible`, which the
  topological Appendix has to *assume*, is a **theorem** for a `C¹` one-manifold whose model range
  is a half-line, with the boundary taken to be Mathlib's `I.boundary M`.
* `exists_boundaryModel`, `exists_interiorModel`: the two normalised local models.  Every boundary
  point has a chart-derived partial homeomorphism onto `Ico 0 ε` sending it to `0`, smooth both
  ways; every interior point one onto `Ioo (-ε) ε` sending it to `0`.  Stage 1 turns these into
  smooth arcs.

## Which of the three model-range cases each statement covers

Every statement that does not mention the shape of the model range covers **all three** cases
(`univ`, `Ici a`, `Icc a b`); the four purely real-analytic lemmas
`exists_lt_mem_of_nonempty_interior`, `closed_convex_cases`, `exists_sign_of_mem_frontier` and
`finiteDimensional_of_finrank_eq_one` are about `ℝ` and `E` alone.  The case-restricted statements,
flagged again in their own docstrings, are:

* line case: `boundary_eq_empty_of_modelRange_eq_univ`;
* half-line case only (the shape the topological Appendix is built for): `modelCoord_sub_nonneg`,
  `symm_mem_range_of_le`, `halfLineHomeomorph`, `coord_halfLineHomeomorph`, `boundaryCompatible`
  and `mem_boundary_iff_chartCoord_eq_of_modelRange_eq_Ici`;
* compact-interval case only: `mem_boundary_iff_chartCoord_mem_of_modelRange_eq_Icc`.

`exists_boundaryModel` and `exists_interiorModel` cover all three cases: the boundary model is
vacuously true in the line case, and in the compact-interval case the normalisation reflects the
coordinate when the point is the *upper* endpoint.

## The three risks the plan flags, and how they are handled

1. *The model range may be a compact interval, so a "one-manifold with corners" must be allowed.*
   `modelRange_cases` keeps `Icc a b` as a case throughout, and no later statement excludes it.
   Only `halfLineHomeomorph` and `boundaryCompatible` are restricted to the half-line, because the
   topological Appendix's datum `H ≃ₜ [0, ∞)` simply does not exist otherwise; the local models of
   `exists_boundaryModel` and `exists_interiorModel` handle the compact interval as well.
2. *Charts at interior points may have to be shrunk away from the model's own endpoints.*
   `exists_isOpen_chartCoord_image` shows a chart's coordinate image is `W ∩ modelRange` with `W`
   open, and `exists_interiorModel` intersects `W` with `interior (modelRange)` before choosing
   `ε`; that intersection is precisely the shrinking.
3. *The sign of the identification of `E` with `ℝ` must be handled.*  Two independent places.
   Globally, `IsAdapted` and `exists_isAdapted` compose with the negation of `ℝ` when needed, so a
   half-line model range is always `[a, ∞)` and never `(-∞, a]`.  Locally, at a boundary point of a
   *compact-interval* model the point may be the upper endpoint, so `exists_sign_of_mem_frontier`
   produces a sign `σ = ±1` and `exists_boundaryModel` carries it into the conclusion.

## References

* Milnor, *Topology from the Differentiable Viewpoint*, Appendix, p. 54.
* `Exposition/PlanOneManifold.md`, Stage 0.
-/

open Set Filter Topology

open scoped ContDiff Manifold

noncomputable section

namespace Milnor.OneManifold.Smooth

/-! ## The three shapes of a closed convex subset of the line -/

/-- A set with nonempty interior in `ℝ` contains two distinct points. -/
theorem exists_lt_mem_of_nonempty_interior {s : Set ℝ} (hi : (interior s).Nonempty) :
    ∃ u ∈ s, ∃ v ∈ s, u < v := by
  obtain ⟨p, hp⟩ := hi
  obtain ⟨l, u, hplu, hlu⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 (isOpen_interior.mem_nhds hp)
  have hl : l < p := hplu.1
  have hu : p < u := hplu.2
  refine ⟨(l + p) / 2, interior_subset (hlu ⟨by linarith, by linarith⟩), p, interior_subset hp,
    by linarith⟩

/-- **The three (four, before normalisation) shapes of a model range.** A closed convex subset of
the line with nonempty interior is the whole line, a closed half-line in one of the two directions,
or a nondegenerate compact interval.  Applied below to `Set.range I` read in a linear coordinate;
the `Iic` alternative is what the normalisation of `modelCoord` removes. -/
theorem closed_convex_cases {s : Set ℝ} (hc : Convex ℝ s) (hcl : IsClosed s)
    (hi : (interior s).Nonempty) :
    s = univ ∨ (∃ a, s = Ici a) ∨ (∃ a, s = Iic a) ∨ ∃ a b, a < b ∧ s = Icc a b := by
  have hoc : s.OrdConnected := convex_iff_ordConnected.1 hc
  obtain ⟨u, hu, v, hv, huv⟩ := exists_lt_mem_of_nonempty_interior hi
  have hne : s.Nonempty := ⟨u, hu⟩
  by_cases hb : BddBelow s
  · by_cases ha : BddAbove s
    · have hI := hcl.csInf_mem hne hb
      have hS := hcl.csSup_mem hne ha
      refine Or.inr (Or.inr (Or.inr ⟨sInf s, sSup s, ?_, Subset.antisymm ?_ ?_⟩))
      · exact (csInf_le hb hu).trans_lt (huv.trans_le (le_csSup ha hv))
      · exact fun t ht => ⟨csInf_le hb ht, le_csSup ha ht⟩
      · exact fun t ht => hoc.out hI hS ht
    · have hI := hcl.csInf_mem hne hb
      refine Or.inr (Or.inl ⟨sInf s, Subset.antisymm (fun t ht => csInf_le hb ht) fun t ht => ?_⟩)
      obtain ⟨b, hbs, htb⟩ := not_bddAbove_iff.1 ha t
      exact hoc.out hI hbs ⟨ht, htb.le⟩
  · by_cases ha : BddAbove s
    · have hS := hcl.csSup_mem hne ha
      refine Or.inr (Or.inr (Or.inl
        ⟨sSup s, Subset.antisymm (fun t ht => le_csSup ha ht) fun t ht => ?_⟩))
      obtain ⟨a, has, hat⟩ := not_bddBelow_iff.1 hb t
      exact hoc.out has hS ⟨hat.le, ht⟩
    · refine Or.inl (eq_univ_of_forall fun t => ?_)
      obtain ⟨a, has, hat⟩ := not_bddBelow_iff.1 hb t
      obtain ⟨b, hbs, htb⟩ := not_bddAbove_iff.1 ha t
      exact hoc.out has hbs ⟨hat.le, htb.le⟩

/-- **The normalisation at an endpoint, on the line.** Let `R` be one of the three normalised shapes
of a model range, let `W` be open, and let `p ∈ W` be a point of the frontier of `R`. Then there are
a sign `σ = ±1` and an `ε > 0` such that the affine reflection `t ↦ σ (t - p)`

* is `≥ 0` on all of `R`, so that after the reflection `p` is the *lower* end of `R`;
* separates `p` from the other endpoint of `R`, if there is one: a frontier point of `R` whose
  reflected coordinate is `< ε` must be `p` itself;
* carries `W ∩ R` onto a set containing `[0, ε)`.

The three cases behave as follows.  `R = univ` cannot occur, since `frontier univ = ∅`.  `R = Ici a`
forces `p = a` and `σ = 1`.  `R = Icc a b` allows `p = a`, with `σ = 1`, and `p = b`, with
`σ = -1`; that last alternative is exactly why the sign has to be carried around, and `ε ≤ b - a`
is what keeps the *other* endpoint out of the normalised range. -/
theorem exists_sign_of_mem_frontier {R W : Set ℝ}
    (hR : R = univ ∨ (∃ a, R = Ici a) ∨ ∃ a b, a < b ∧ R = Icc a b) (hW : IsOpen W) {p : ℝ}
    (hpW : p ∈ W) (hp : p ∈ frontier R) :
    ∃ σ ε : ℝ, (σ = 1 ∨ σ = -1) ∧ 0 < ε ∧ (∀ t ∈ R, 0 ≤ σ * (t - p)) ∧
      (∀ t ∈ R, σ * (t - p) < ε → t ∈ frontier R → t = p) ∧
      Ico 0 ε ⊆ (fun t => σ * (t - p)) '' (W ∩ R) := by
  obtain ⟨l, u, hplu, hluW⟩ := mem_nhds_iff_exists_Ioo_subset.1 (hW.mem_nhds hpW)
  have hl : l < p := hplu.1
  have hu : p < u := hplu.2
  set δ := min (p - l) (u - p) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδl : δ ≤ p - l := min_le_left _ _
  have hδu : δ ≤ u - p := min_le_right _ _
  have hδW : ∀ t : ℝ, p - δ < t → t < p + δ → t ∈ W := fun t h1 h2 =>
    hluW ⟨by linarith, by linarith⟩
  rcases hR with hRu | ⟨a, hRa⟩ | ⟨a, b, hab, hRab⟩
  · rw [hRu, frontier_univ] at hp
    exact hp.elim
  · subst hRa
    rw [frontier_Ici, mem_singleton_iff] at hp
    subst hp
    refine ⟨1, δ, Or.inl rfl, hδ, fun t ht => by simpa using by linarith [mem_Ici.1 ht], ?_, ?_⟩
    · intro t _ _ hfr
      rw [frontier_Ici, mem_singleton_iff] at hfr
      exact hfr
    · intro s hs
      refine ⟨s + p, ⟨hδW _ (by linarith [hs.1]) (by linarith [hs.2]), ?_⟩, by ring⟩
      exact mem_Ici.2 (by linarith [hs.1])
  · subst hRab
    rw [frontier_Icc hab.le, mem_insert_iff, mem_singleton_iff] at hp
    set ε := min δ (b - a) with hεdef
    have hε : 0 < ε := lt_min hδ (by linarith)
    have hεδ : ε ≤ δ := min_le_left _ _
    have hεab : ε ≤ b - a := min_le_right _ _
    rcases hp with hp | hp
    · subst hp
      refine ⟨1, ε, Or.inl rfl, hε, fun t ht => by simpa using (mem_Icc.1 ht).1, ?_, ?_⟩
      · intro t ht hlt hfr
        rw [frontier_Icc hab.le, mem_insert_iff, mem_singleton_iff] at hfr
        rcases hfr with h | h
        · exact h
        · rw [h] at hlt; simp only [one_mul] at hlt; linarith
      · intro s hs
        refine ⟨s + p, ⟨hδW _ (by linarith [hs.1]) (by linarith [hs.2]), ?_⟩, by ring⟩
        exact mem_Icc.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · subst hp
      refine ⟨-1, ε, Or.inr rfl, hε, fun t ht => by simpa using (mem_Icc.1 ht).2, ?_, ?_⟩
      · intro t ht hlt hfr
        rw [frontier_Icc hab.le, mem_insert_iff, mem_singleton_iff] at hfr
        rcases hfr with h | h
        · rw [h] at hlt; simp only [neg_mul, one_mul, neg_sub] at hlt; linarith
        · exact h
      · intro s hs
        refine ⟨p - s, ⟨hδW _ (by linarith [hs.1, hs.2]) (by linarith [hs.1]), ?_⟩, by ring⟩
        exact mem_Icc.2 ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-! ## A normalised linear coordinate on a one-dimensional model space -/

section Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- A real normed space of dimension one is finite-dimensional. -/
theorem finiteDimensional_of_finrank_eq_one (hE : Module.finrank ℝ E = 1) :
    FiniteDimensional ℝ E :=
  FiniteDimensional.of_finrank_pos (by rw [hE]; norm_num)

/-- A linear identification `L : E ≃L[ℝ] ℝ` is *adapted* to the model with corners `I` when the
model range `Set.range I`, read through `L`, is the whole line, a half-line of the form `[a, ∞)`,
or a nondegenerate compact interval `[a, b]`.  Adaptedness is exactly the normalisation that
removes the fourth possibility `(-∞, a]`, i.e. it **fixes the sign** of the identification. -/
def IsAdapted (I : ModelWithCorners ℝ E H) (L : E ≃L[ℝ] ℝ) : Prop :=
  L '' Set.range I = univ ∨ (∃ a, L '' Set.range I = Ici a) ∨
    ∃ a b, a < b ∧ L '' Set.range I = Icc a b

/-- An adapted linear identification exists: take any linear identification `E ≃L[ℝ] ℝ` and, if the
model range comes out as a half-line `(-∞, a]`, compose with the negation of `ℝ`. -/
theorem exists_isAdapted (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1) :
    ∃ L : E ≃L[ℝ] ℝ, IsAdapted I L := by
  have := finiteDimensional_of_finrank_eq_one hE
  set L₀ : E ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (hE.trans (Module.finrank_self ℝ).symm)
  have hcoe : ⇑L₀.toHomeomorph = ⇑L₀ := rfl
  have hconv : Convex ℝ (L₀ '' Set.range I) :=
    I.convex_range.is_linear_image ⟨fun x y => map_add L₀ x y, fun c x => map_smul L₀ c x⟩
  have hcl : IsClosed (L₀ '' Set.range I) := by
    rw [← hcoe]
    exact L₀.toHomeomorph.isClosed_image.2 I.isClosed_range
  have hi : (interior (L₀ '' Set.range I)).Nonempty := by
    rw [← hcoe, ← L₀.toHomeomorph.image_interior]
    exact I.nonempty_interior.image _
  rcases closed_convex_cases hconv hcl hi with h | ⟨a, h⟩ | ⟨a, h⟩ | ⟨a, b, hab, h⟩
  · exact ⟨L₀, Or.inl h⟩
  · exact ⟨L₀, Or.inr (Or.inl ⟨a, h⟩)⟩
  · refine ⟨L₀.trans (ContinuousLinearEquiv.neg ℝ), Or.inr (Or.inl ⟨-a, ?_⟩)⟩
    ext t
    simp only [mem_image, mem_Ici]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : L₀ v ∈ L₀ '' Set.range I := ⟨v, hv, rfl⟩
      rw [h, mem_Iic] at hv'
      simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.neg_apply]
      linarith
    · intro ht
      have hmt : -t ∈ L₀ '' Set.range I := by rw [h, mem_Iic]; linarith
      obtain ⟨v, hv, hvt⟩ := hmt
      refine ⟨v, hv, ?_⟩
      simp only [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.neg_apply, hvt]
      ring
  · exact ⟨L₀, Or.inr (Or.inr ⟨a, b, hab, h⟩)⟩

variable (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1)

/-- **The normalised real coordinate on the model space.** A linear identification of the
one-dimensional space `E` with `ℝ`, chosen adapted to `I`: the model range, read through it, is the
whole line, a half-line `[a, ∞)`, or a nondegenerate compact interval `[a, b]`.  The choice is what
fixes the sign, so that a half-line never comes out as `(-∞, a]`. -/
def modelCoord : E ≃L[ℝ] ℝ := (exists_isAdapted I hE).choose

/-- The normalised coordinate is adapted to `I`; see `modelRange_cases`. -/
theorem modelCoord_isAdapted : IsAdapted I (modelCoord I hE) := (exists_isAdapted I hE).choose_spec

/-- **The model range in the normalised real coordinate**: the image of `Set.range I` under
`modelCoord`. -/
def modelRange : Set ℝ := modelCoord I hE '' Set.range I

/-- **The three cases for the model range.** After the normalised identification of `E` with `ℝ`,
the model range is all of `ℝ` (a boundaryless one-manifold), a closed half-line `[a, ∞)`
(a one-manifold with boundary), or a nondegenerate compact interval `[a, b]` (a one-manifold with
*corners*, which the plan insists must be allowed).  The `(-∞, a]` case is excluded by the
normalisation. -/
theorem modelRange_cases : modelRange I hE = univ ∨ (∃ a, modelRange I hE = Ici a) ∨
    ∃ a b, a < b ∧ modelRange I hE = Icc a b := modelCoord_isAdapted I hE

/-- The normalised coordinate of a point of the model space lies in the model range. -/
theorem modelCoord_mem_modelRange (y : H) : modelCoord I hE (I y) ∈ modelRange I hE :=
  ⟨I y, mem_range_self y, rfl⟩

/-- Membership in the model range: a real number lies in the model range exactly when the point of
`E` it names lies in `Set.range I`. -/
theorem mem_modelRange_iff {t : ℝ} :
    t ∈ modelRange I hE ↔ (modelCoord I hE).symm t ∈ Set.range I := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    rwa [ContinuousLinearEquiv.symm_apply_apply]
  · intro ht
    exact ⟨(modelCoord I hE).symm t, ht, ContinuousLinearEquiv.apply_symm_apply _ _⟩

/-- The model range is convex. (All three cases.) -/
theorem convex_modelRange : Convex ℝ (modelRange I hE) :=
  I.convex_range.is_linear_image
    ⟨fun x y => map_add (modelCoord I hE) x y, fun c x => map_smul (modelCoord I hE) c x⟩

/-- The model range is closed; this is Mathlib's `ModelWithCorners.isClosed_range` read in the
normalised coordinate. (All three cases.) -/
theorem isClosed_modelRange : IsClosed (modelRange I hE) := by
  have hcoe : ⇑(modelCoord I hE).toHomeomorph = ⇑(modelCoord I hE) := rfl
  rw [modelRange, ← hcoe]
  exact (modelCoord I hE).toHomeomorph.isClosed_image.2 I.isClosed_range

/-- The model range has nonempty interior. (All three cases.) -/
theorem nonempty_interior_modelRange : (interior (modelRange I hE)).Nonempty := by
  have hcoe : ⇑(modelCoord I hE).toHomeomorph = ⇑(modelCoord I hE) := rfl
  rw [modelRange, ← hcoe, ← (modelCoord I hE).toHomeomorph.image_interior]
  exact I.nonempty_interior.image _

/-- The model range is order-connected: it is an interval. (All three cases.) -/
theorem ordConnected_modelRange : (modelRange I hE).OrdConnected :=
  convex_iff_ordConnected.1 (convex_modelRange I hE)

/-- **Derivatives along the model range are unique.** This is `uniqueDiffOn_convex` applied to the
convexity and nonempty interior of the model range, and it is what makes `derivWithin` well behaved
at a boundary point, where the range is only one-sided. (All three cases.) -/
theorem uniqueDiffOn_modelRange : UniqueDiffOn ℝ (modelRange I hE) :=
  uniqueDiffOn_convex (convex_modelRange I hE) (nonempty_interior_modelRange I hE)

/-- At every point of the model range, including an endpoint, the derivative within the range is
unique. (All three cases.) -/
theorem uniqueDiffWithinAt_modelRange {t : ℝ} (ht : t ∈ modelRange I hE) :
    UniqueDiffWithinAt ℝ (modelRange I hE) t := uniqueDiffOn_modelRange I hE t ht

/-- Consequence of uniqueness of derivatives: at a point of the model range -- in particular at an
endpoint -- a function has at most one derivative within the range. (All three cases.) -/
theorem hasDerivWithinAt_modelRange_unique {f : ℝ → ℝ} {c c' t : ℝ} (ht : t ∈ modelRange I hE)
    (h : HasDerivWithinAt f c (modelRange I hE) t)
    (h' : HasDerivWithinAt f c' (modelRange I hE) t) : c = c' :=
  (uniqueDiffWithinAt_modelRange I hE ht).eq_deriv _ h h'

/-- Consequence of uniqueness of derivatives: `derivWithin` along the model range computes the
derivative, at an endpoint of the range as well as at an interior point. (All three cases.) -/
theorem derivWithin_modelRange_eq {f : ℝ → ℝ} {c t : ℝ} (ht : t ∈ modelRange I hE)
    (h : HasDerivWithinAt f c (modelRange I hE) t) :
    derivWithin f (modelRange I hE) t = c :=
  h.derivWithin (uniqueDiffWithinAt_modelRange I hE ht)

end Model

/-! ## The real coordinate attached to a chart -/

section Charts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (hE : Module.finrank ℝ E = 1)
  {M : Type*} [TopologicalSpace M]

/-- **The real coordinate attached to a chart.** For a chart `e` of `M`, the extended chart
`e.extend I` read in the normalised linear coordinate of `E`; concretely `modelCoord ∘ I ∘ e`.
(All three model-range cases.) -/
def chartCoord (e : OpenPartialHomeomorph M H) (x : M) : ℝ := modelCoord I hE (e.extend I x)

/-- The chart coordinate is literally `modelCoord ∘ I ∘ e`. -/
theorem chartCoord_apply (e : OpenPartialHomeomorph M H) (x : M) :
    chartCoord I hE e x = modelCoord I hE (I (e x)) := rfl

/-- The chart coordinate of any point takes its value in the model range. -/
theorem chartCoord_mem_modelRange {e : OpenPartialHomeomorph M H} (x : M) :
    chartCoord I hE e x ∈ modelRange I hE := modelCoord_mem_modelRange I hE (e x)

/-- The chart coordinate is continuous on the source of the chart. -/
theorem continuousOn_chartCoord (e : OpenPartialHomeomorph M H) :
    ContinuousOn (chartCoord I hE e) e.source := by
  have h : ContinuousOn (e.extend I) (e.extend I).source := e.continuousOn_extend
  rw [e.extend_source] at h
  exact (modelCoord I hE).continuous.comp_continuousOn h

/-- The chart coordinate is injective on the source of the chart: it is a genuine coordinate. -/
theorem injOn_chartCoord (e : OpenPartialHomeomorph M H) :
    Set.InjOn (chartCoord I hE e) e.source := by
  intro x hx y hy hxy
  have h2 : (e.extend I) x = (e.extend I) y := (modelCoord I hE).injective hxy
  calc x = (e.extend I).symm ((e.extend I) x) := (e.extend_left_inv hx).symm
    _ = (e.extend I).symm ((e.extend I) y) := by rw [h2]
    _ = y := e.extend_left_inv hy

/-- **The image of a chart in the real coordinate is relatively open in the model range.** It is the
intersection of the model range with an open subset of `ℝ`. This is the precise sense in which a
chart covers "an interval's worth" of the model, and it is what the local models below shrink.
(All three model-range cases.) -/
theorem exists_isOpen_chartCoord_image (e : OpenPartialHomeomorph M H) :
    ∃ W : Set ℝ, IsOpen W ∧ chartCoord I hE e '' e.source = W ∩ modelRange I hE := by
  have hcoe : ⇑(modelCoord I hE).toHomeomorph = ⇑(modelCoord I hE) := rfl
  refine ⟨modelCoord I hE '' (I.symm ⁻¹' e.target), ?_, ?_⟩
  · rw [← hcoe]
    exact (modelCoord I hE).toHomeomorph.isOpen_image.2
      (e.open_target.preimage I.continuous_symm)
  · have h1 : chartCoord I hE e '' e.source = modelCoord I hE '' (e.extend I).target := by
      rw [e.extend_target_eq_image_source, ← Set.image_comp]; rfl
    rw [h1, e.extend_target, Set.image_inter (modelCoord I hE).injective, modelRange]

variable [ChartedSpace H M] {n : WithTop ℕ∞}

/-- **Smoothness of the chart coordinate, composed with a smooth real function.** For a chart in the
maximal `Cⁿ` atlas and a `Cⁿ` function `g : ℝ → ℝ`, the map `g ∘ chartCoord` is `Cⁿ` on the source of
the chart, as a map of manifolds into `ℝ` with its trivial model. (All three model-range cases.) -/
theorem contMDiffOn_comp_chartCoord {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) {g : ℝ → ℝ} (hg : ContDiff ℝ n g) :
    ContMDiffOn I 𝓘(ℝ, ℝ) n (fun y => g (chartCoord I hE e y)) e.source := by
  have h1 : ContMDiffOn I 𝓘(ℝ, E) n (e.extend I) e.source := e.contMDiffOn_extend he
  have hA : ContDiff ℝ n (fun v : E => g (modelCoord I hE v)) := hg.comp (modelCoord I hE).contDiff
  exact hA.contMDiff.comp_contMDiffOn h1

/-- **Smoothness of the chart coordinate.** For a chart in the maximal `Cⁿ` atlas, the real
coordinate is `Cⁿ` on the source of the chart. (All three model-range cases.) -/
theorem contMDiffOn_chartCoord {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) :
    ContMDiffOn I 𝓘(ℝ, ℝ) n (chartCoord I hE e) e.source :=
  contMDiffOn_comp_chartCoord I hE he contDiff_id

variable [IsManifold I n M]

/-! ## The boundary is chart-independent -/

/-- **The interior, tested in an arbitrary chart.** For a `C¹` manifold, a point in the source of
*any* chart of the atlas is an interior point exactly when its real coordinate lies in the interior
of the model range. This is Mathlib's `ModelWithCorners.isInteriorPoint_iff_of_mem_atlas`,
transported to the real coordinate. (All three model-range cases.) -/
theorem mem_interior_iff_chartCoord_mem_interior (hn : n ≠ 0)
    {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) {x : M} (hx : x ∈ e.source) :
    x ∈ I.interior M ↔ chartCoord I hE e x ∈ interior (modelRange I hE) := by
  have hcoe : ⇑(modelCoord I hE).toHomeomorph = ⇑(modelCoord I hE) := rfl
  have himg : modelCoord I hE '' interior (Set.range I) = interior (modelRange I hE) := by
    rw [modelRange, ← hcoe, (modelCoord I hE).toHomeomorph.image_interior]
  have hdef : x ∈ I.interior M ↔ I.IsInteriorPoint x := Iff.rfl
  have key : x ∈ I.interior M ↔ I (e x) ∈ interior (Set.range I) :=
    hdef.trans ((I.isInteriorPoint_iff_of_mem_atlas hn he hx).trans
      ⟨fun h => e.interior_extend_target_subset_interior_range h,
        fun h => e.mem_interior_extend_target (e.map_source hx) h⟩)
  rw [chartCoord_apply, ← himg]
  refine key.trans ⟨fun h => ⟨I (e x), h, rfl⟩, ?_⟩
  rintro ⟨v, hv, hveq⟩
  rwa [(modelCoord I hE).injective hveq] at hv

/-- **The boundary is chart-independent.** For a `C¹` manifold, a point in the source of *any* chart
of the atlas is a boundary point exactly when its real coordinate lies on the frontier of the model
range, that is, is an endpoint of the model range. This is the form the project uses; it is
Mathlib's `ModelWithCorners.isBoundaryPoint_iff_of_mem_atlas` read in the real coordinate, and it is
the statement the topological Appendix has to assume. (All three model-range cases.) -/
theorem mem_boundary_iff_chartCoord_mem_frontier (hn : n ≠ 0)
    {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) {x : M} (hx : x ∈ e.source) :
    x ∈ I.boundary M ↔ chartCoord I hE e x ∈ frontier (modelRange I hE) := by
  have hcompl : x ∈ I.boundary M ↔ x ∉ I.interior M := by
    rw [← I.compl_interior, mem_compl_iff]
  rw [hcompl, mem_interior_iff_chartCoord_mem_interior I hE hn he hx,
    (isClosed_modelRange I hE).frontier_eq]
  exact ⟨fun h => ⟨chartCoord_mem_modelRange I hE x, h⟩, fun h => h.2⟩

/-- **The line case.** If the model range is all of `ℝ`, the manifold has empty boundary: this is the
boundaryless case.  Unlike the two statements above, this needs no differentiability at all, since
`Set.range I` is then the whole of `E` and the frontier of the model range is empty. -/
theorem boundary_eq_empty_of_modelRange_eq_univ (h : modelRange I hE = univ) :
    I.boundary M = ∅ := by
  have hran : Set.range I = univ := by
    refine eq_univ_of_forall fun v => ?_
    have hv := (mem_modelRange_iff I hE (t := modelCoord I hE v)).1 (by rw [h]; trivial)
    rwa [ContinuousLinearEquiv.symm_apply_apply] at hv
  ext x
  simp only [mem_empty_iff_false, iff_false]
  intro hx
  have hfr : (extChartAt I x) x ∈ frontier (Set.range I) := hx
  rw [hran, frontier_univ] at hfr
  exact hfr

/-- **The half-line case.** If the model range is `[a, ∞)`, then a point in the source of any chart
of the atlas is a boundary point exactly when its real coordinate equals `a`. -/
theorem mem_boundary_iff_chartCoord_eq_of_modelRange_eq_Ici (hn : n ≠ 0) {a : ℝ}
    (h : modelRange I hE = Ici a) {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) {x : M}
    (hx : x ∈ e.source) : x ∈ I.boundary M ↔ chartCoord I hE e x = a := by
  rw [mem_boundary_iff_chartCoord_mem_frontier I hE hn he hx, h, frontier_Ici, mem_singleton_iff]

/-- **The compact-interval case** (a one-manifold with corners). If the model range is `[a, b]` with
`a < b`, then a point in the source of any chart of the atlas is a boundary point exactly when its
real coordinate is `a` or `b`. -/
theorem mem_boundary_iff_chartCoord_mem_of_modelRange_eq_Icc (hn : n ≠ 0) {a b : ℝ} (hab : a < b)
    (h : modelRange I hE = Icc a b) {e : OpenPartialHomeomorph M H} (he : e ∈ atlas H M) {x : M}
    (hx : x ∈ e.source) :
    x ∈ I.boundary M ↔ chartCoord I hE e x = a ∨ chartCoord I hE e x = b := by
  rw [mem_boundary_iff_chartCoord_mem_frontier I hE hn he hx, h, frontier_Icc hab.le]
  simp only [mem_insert_iff, mem_singleton_iff]

/-! ## `Milnor.OneManifold.BoundaryCompatible` comes for free -/

/-- **The half-line case.** When the model range is `[a, ∞)`, the translated coordinate
`modelCoord (I y) - a` of a point of the model space is nonnegative. -/
theorem modelCoord_sub_nonneg {a : ℝ} (h : modelRange I hE = Ici a) (y : H) :
    0 ≤ modelCoord I hE (I y) - a := by
  have hy := modelCoord_mem_modelRange I hE y
  rw [h, mem_Ici] at hy
  linarith

/-- **The half-line case.** When the model range is `[a, ∞)`, every real number `≥ a` is the
normalised coordinate of a point of the model space. -/
theorem symm_mem_range_of_le {a : ℝ} (h : modelRange I hE = Ici a) {t : ℝ} (ht : a ≤ t) :
    (modelCoord I hE).symm t ∈ Set.range I :=
  (mem_modelRange_iff I hE).1 (by rw [h, mem_Ici]; exact ht)

/-- **The half-line case.** When the model range is the half-line `[a, ∞)`, the model space `H` is
homeomorphic to `[0, ∞)` by `y ↦ modelCoord (I y) - a`. This is exactly the datum `φ` that the
topological Appendix of `Milnor/Appendix/OneManifold.lean` takes as a hypothesis. -/
def halfLineHomeomorph {a : ℝ} (h : modelRange I hE = Ici a) : H ≃ₜ Ici (0 : ℝ) where
  toFun y := ⟨modelCoord I hE (I y) - a, Set.mem_Ici.2 (modelCoord_sub_nonneg I hE h y)⟩
  invFun t := I.symm ((modelCoord I hE).symm ((t : ℝ) + a))
  left_inv y := by
    show I.symm ((modelCoord I hE).symm (modelCoord I hE (I y) - a + a)) = y
    rw [show modelCoord I hE (I y) - a + a = modelCoord I hE (I y) by ring,
      ContinuousLinearEquiv.symm_apply_apply, I.left_inv]
  right_inv t := by
    have ht : (0 : ℝ) ≤ (t : ℝ) := t.2
    refine Subtype.ext ?_
    show modelCoord I hE (I (I.symm ((modelCoord I hE).symm ((t : ℝ) + a)))) - a = (t : ℝ)
    rw [I.right_inv (symm_mem_range_of_le I hE h (by linarith)),
      ContinuousLinearEquiv.apply_symm_apply]
    ring
  continuous_toFun :=
    (((modelCoord I hE).continuous.comp I.continuous).sub continuous_const).subtype_mk _
  continuous_invFun :=
    I.continuous_symm.comp ((modelCoord I hE).symm.continuous.comp
      (continuous_subtype_val.add continuous_const))

/-- The real coordinate of the topological Appendix, computed for `halfLineHomeomorph`: it is the
chart coordinate translated so that the boundary of the model sits at `0`. (Half-line case.) -/
theorem coord_halfLineHomeomorph {a : ℝ} (h : modelRange I hE = Ici a) (y : H) :
    coord (halfLineHomeomorph I hE h) y = modelCoord I hE (I y) - a := rfl

/-- **`Milnor.OneManifold.BoundaryCompatible` is a theorem, not a hypothesis, for smooth
one-manifolds.** For a `C¹` manifold `M` charted on a one-dimensional model whose model range is a
half-line `[a, ∞)`, Mathlib's boundary `I.boundary M` satisfies the compatibility hypothesis that the
topological Appendix must assume: *every* chart of the atlas sends exactly the boundary points to
coordinate `0`.

Hypotheses: `Module.finrank ℝ E = 1`, `IsManifold I n M` with `n ≠ 0` (that is, `C¹` at least), and
`modelRange I hE = Ici a`. Nothing else: no Hausdorffness, no compactness, no σ-compactness, and no
maximality of the atlas -- Mathlib's chart-independence theorem already quantifies over
`atlas H M`, which is exactly the quantifier in `BoundaryCompatible`. (Half-line case; in the other
two cases no such `φ` exists, since the model space is then not homeomorphic to `[0, ∞)`.) -/
theorem boundaryCompatible (hn : n ≠ 0) {a : ℝ} (h : modelRange I hE = Ici a) :
    BoundaryCompatible (halfLineHomeomorph I hE h) (I.boundary M) := by
  intro e he x hx
  rw [coord_halfLineHomeomorph I hE h,
    mem_boundary_iff_chartCoord_eq_of_modelRange_eq_Ici I hE hn h he hx, chartCoord_apply]
  constructor
  · intro hc; rw [hc]; ring
  · intro hc; linarith

/-! ## The two normalised local models -/

/-- **The normalised local model at a boundary point.** Every boundary point `x` of a `Cⁿ`
one-manifold (`n ≠ 0`) has, for some `ε > 0`, a partial homeomorphism `f` from an *open*
neighbourhood of `x` contained in the source of the preferred chart at `x` onto `Ico 0 ε`, with
`f x = 0`, which is `Cⁿ` in both directions and which recognises the boundary: a point of the source
is a boundary point exactly when its coordinate is `0`.  The map `f` is affine in the chart
coordinate, `f = σ (chartCoord - chartCoord x)` with `σ = ±1`.  Stage 1 turns this into a smooth arc.

All three model-range cases are covered.  In the line case there is no boundary point, so the
statement is vacuous.  In the half-line case `σ = 1`.  In the compact-interval case `σ = 1` at the
lower endpoint of the model and `σ = -1` at the upper one -- this is why the sign is part of the
conclusion. -/
theorem exists_boundaryModel (hn : n ≠ 0) {x : M} (hx : x ∈ I.boundary M) :
    ∃ (ε : ℝ) (f : PartialHomeomorph M ℝ) (σ : ℝ), 0 < ε ∧ (σ = 1 ∨ σ = -1) ∧
      IsOpen f.source ∧ x ∈ f.source ∧ f.source ⊆ (chartAt H x).source ∧
      Set.EqOn f (fun y => σ * (chartCoord I hE (chartAt H x) y -
        chartCoord I hE (chartAt H x) x)) f.source ∧
      f x = 0 ∧ f.target = Ico 0 ε ∧ (∀ y ∈ f.source, y ∈ I.boundary M ↔ f y = 0) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) n f f.source ∧ ContMDiffOn 𝓘(ℝ, ℝ) I n f.symm f.target := by
  have hxs : x ∈ (chartAt H x).source := mem_chart_source H x
  obtain ⟨W, hWopen, hWimg⟩ := exists_isOpen_chartCoord_image I hE (chartAt H x)
  set κ : M → ℝ := chartCoord I hE (chartAt H x) with hκdef
  set p : ℝ := κ x with hpdef
  have hpW : p ∈ W := by
    have hmem : p ∈ κ '' (chartAt H x).source := ⟨x, hxs, rfl⟩
    rw [hWimg] at hmem
    exact hmem.1
  have hpfr : p ∈ frontier (modelRange I hE) :=
    (mem_boundary_iff_chartCoord_mem_frontier I hE hn (chart_mem_atlas H x) hxs).1 hx
  obtain ⟨σ, ε, hσ, hε, hnonneg, hsep, hsurj⟩ :=
    exists_sign_of_mem_frontier (modelRange_cases I hE) hWopen hpW hpfr
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  -- the normalised coordinate `G`, its inverse `F` and the shrunken source `V`
  set G : M → ℝ := fun y => σ * (κ y - p) with hGdef
  set F : ℝ → M := fun t =>
    ((chartAt H x).extend I).symm ((modelCoord I hE).symm (σ * t + p)) with hFdef
  set V : Set M := (chartAt H x).source ∩ G ⁻¹' Iio ε with hVdef
  have hG : ∀ y, G y = σ * (κ y - p) := fun y => by rw [hGdef]
  have hF : ∀ t, F t = ((chartAt H x).extend I).symm ((modelCoord I hE).symm (σ * t + p)) :=
    fun t => by rw [hFdef]
  have hκmem : ∀ y, κ y ∈ modelRange I hE := fun y => chartCoord_mem_modelRange I hE y
  have hGnonneg : ∀ y, 0 ≤ G y := fun y => by rw [hG]; exact hnonneg _ (hκmem y)
  have hGx : G x = 0 := by rw [hG, hpdef]; ring
  have hκG : ∀ y, σ * G y + p = κ y := by
    intro y
    rw [hG]
    rcases hσ with h | h <;> rw [h] <;> ring
  -- `V` is an open neighbourhood of `x` inside the chart
  have hGcont : ContinuousOn G (chartAt H x).source := by
    rw [hGdef]
    exact continuousOn_const.mul ((continuousOn_chartCoord I hE (chartAt H x)).sub
      continuousOn_const)
  have hVopen : IsOpen V := by
    rw [hVdef]; exact hGcont.isOpen_inter_preimage (chartAt H x).open_source isOpen_Iio
  have hxV : x ∈ V := ⟨hxs, by rw [mem_preimage, hGx]; exact hε⟩
  have hVsub : V ⊆ (chartAt H x).source := fun _ hy => hy.1
  -- the image of `V` is exactly `Ico 0 ε`
  have hGsurj : Ico 0 ε ⊆ G '' (chartAt H x).source := by
    intro s hs
    obtain ⟨t, htW, hts⟩ := hsurj hs
    rw [← hWimg] at htW
    obtain ⟨y, hy, hyt⟩ := htW
    exact ⟨y, hy, by rw [hG, hyt]; exact hts⟩
  have hVimg : G '' V = Ico 0 ε := by
    rw [hVdef, Set.image_inter_preimage]
    refine Subset.antisymm ?_ fun t ht => ⟨hGsurj ht, ht.2⟩
    rintro t ⟨⟨y, _, rfl⟩, ht⟩
    exact ⟨hGnonneg y, ht⟩
  have hexV : ∀ t ∈ Ico 0 ε, ∃ y, y ∈ V ∧ G y = t := by
    intro t ht
    rw [← hVimg] at ht
    obtain ⟨y, hy, hyt⟩ := ht
    exact ⟨y, hy, hyt⟩
  -- `F` inverts `G`
  have hFG : ∀ y ∈ (chartAt H x).source, F (G y) = y := by
    intro y hy
    rw [hF, hκG y, hκdef]
    show ((chartAt H x).extend I).symm
      ((modelCoord I hE).symm (modelCoord I hE (((chartAt H x).extend I) y))) = y
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (chartAt H x).extend_left_inv hy
  have hFmem : ∀ t ∈ Ico 0 ε, F t ∈ V ∧ G (F t) = t := by
    intro t ht
    obtain ⟨y, hyV, hyt⟩ := hexV t ht
    rw [← hyt, hFG y hyV.1]
    exact ⟨hyV, rfl⟩
  -- the inner map lands in the target of the extended chart
  have hinner : ∀ t ∈ Ico 0 ε,
      (modelCoord I hE).symm (σ * t + p) ∈ ((chartAt H x).extend I).target := by
    intro t ht
    obtain ⟨y, hyV, hyt⟩ := hexV t ht
    rw [← hyt, hκG y, hκdef]
    show (modelCoord I hE).symm (modelCoord I hE (((chartAt H x).extend I) y)) ∈ _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ((chartAt H x).extend I).map_source
      (by rw [OpenPartialHomeomorph.extend_source]; exact hyV.1)
  -- the fields of the partial homeomorphism
  have hmapsrc : ∀ y ∈ V, G y ∈ Ico 0 ε := fun y hy => by rw [← hVimg]; exact ⟨y, hy, rfl⟩
  have hFcont : ContinuousOn F (Ico 0 ε) := by
    refine ((chartAt H x).continuousOn_extend_symm.comp ?_ hinner).congr fun t _ => hF t
    exact ((modelCoord I hE).symm.continuous.comp
      ((continuous_const.mul continuous_id).add continuous_const)).continuousOn
  refine ⟨ε,
    { toFun := G
      invFun := F
      source := V
      target := Ico 0 ε
      map_source' := hmapsrc
      map_target' := fun t ht => (hFmem t ht).1
      left_inv' := fun y hy => hFG y hy.1
      right_inv' := fun t ht => (hFmem t ht).2
      continuousOn_toFun := hGcont.mono hVsub
      continuousOn_invFun := hFcont },
    σ, hε, hσ, hVopen, hxV, hVsub, fun y _ => hG y, hGx, rfl, ?_, ?_, ?_⟩
  · -- the boundary law
    intro y hy
    rw [mem_boundary_iff_chartCoord_mem_frontier I hE hn (chart_mem_atlas H x) hy.1]
    constructor
    · intro hfr
      have hlt : σ * (κ y - p) < ε := by
        have h2 := hy.2
        rw [mem_preimage, hG] at h2
        exact h2
      have hyp := hsep (κ y) (hκmem y) hlt hfr
      show G y = 0
      rw [hG, hyp]; ring
    · intro h0
      have hκy : κ y = p := by
        have h1 : σ * (κ y - p) = 0 := by rw [← hG]; exact h0
        rcases mul_eq_zero.1 h1 with h | h
        · exact absurd h hσ0
        · linarith
      show κ y ∈ frontier (modelRange I hE)
      rw [hκy]; exact hpfr
  · -- smoothness of the coordinate
    refine ContMDiffOn.mono ?_ hVsub
    exact contMDiffOn_comp_chartCoord I hE (IsManifold.chart_mem_maximalAtlas x)
      (contDiff_const.mul (contDiff_id.sub contDiff_const))
  · -- smoothness of the inverse
    refine ContMDiffOn.congr ?_ fun t _ => hF t
    refine (contMDiffOn_extChartAt_symm x).comp ?_ hinner
    exact (((modelCoord I hE).symm.contDiff.comp
      ((contDiff_const.mul contDiff_id).add contDiff_const)).contMDiff).contMDiffOn

/-- **The normalised local model at an interior point.** Every interior point `x` of a `Cⁿ`
one-manifold (`n ≠ 0`) has, for some `ε > 0`, a partial homeomorphism `f` from an *open*
neighbourhood of `x` contained in the source of the preferred chart at `x` onto the **open**
interval `Ioo (-ε) ε`, with `f x = 0`, which is `Cⁿ` in both directions and whose source contains no
boundary point at all.  Here `f` is just the chart coordinate translated to vanish at `x`; no sign is
needed, because the target is symmetric.  What *is* needed is to **shrink the chart away from the
endpoints of the model range**, and that is exactly where `ε` comes from.  Stage 1 turns this into a
smooth arc.  (All three model-range cases.) -/
theorem exists_interiorModel (hn : n ≠ 0) {x : M} (hx : x ∈ I.interior M) :
    ∃ (ε : ℝ) (f : PartialHomeomorph M ℝ), 0 < ε ∧
      IsOpen f.source ∧ x ∈ f.source ∧ f.source ⊆ (chartAt H x).source ∧
      Set.EqOn f (fun y => chartCoord I hE (chartAt H x) y -
        chartCoord I hE (chartAt H x) x) f.source ∧
      f x = 0 ∧ f.target = Ioo (-ε) ε ∧ f.source ⊆ I.interior M ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) n f f.source ∧ ContMDiffOn 𝓘(ℝ, ℝ) I n f.symm f.target := by
  have hxs : x ∈ (chartAt H x).source := mem_chart_source H x
  obtain ⟨W, hWopen, hWimg⟩ := exists_isOpen_chartCoord_image I hE (chartAt H x)
  set κ : M → ℝ := chartCoord I hE (chartAt H x) with hκdef
  set p : ℝ := κ x with hpdef
  have hpW : p ∈ W := by
    have hmem : p ∈ κ '' (chartAt H x).source := ⟨x, hxs, rfl⟩
    rw [hWimg] at hmem
    exact hmem.1
  have hpint : p ∈ interior (modelRange I hE) :=
    (mem_interior_iff_chartCoord_mem_interior I hE hn (chart_mem_atlas H x) hxs).1 hx
  -- shrink the chart away from the endpoints of the model range
  obtain ⟨l, u, hplu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.1
    ((hWopen.inter isOpen_interior).mem_nhds ⟨hpW, hpint⟩)
  have hl : l < p := hplu.1
  have hu : p < u := hplu.2
  set ε := min (p - l) (u - p) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by linarith)
  have hεl : ε ≤ p - l := min_le_left _ _
  have hεu : ε ≤ u - p := min_le_right _ _
  have hshrink : ∀ t : ℝ, p - ε < t → t < p + ε → t ∈ W ∩ interior (modelRange I hE) :=
    fun t h1 h2 => hsub ⟨by linarith, by linarith⟩
  set G : M → ℝ := fun y => κ y - p with hGdef
  set F : ℝ → M := fun t => ((chartAt H x).extend I).symm ((modelCoord I hE).symm (t + p))
    with hFdef
  set V : Set M := (chartAt H x).source ∩ G ⁻¹' Ioo (-ε) ε with hVdef
  have hG : ∀ y, G y = κ y - p := fun y => by rw [hGdef]
  have hF : ∀ t, F t = ((chartAt H x).extend I).symm ((modelCoord I hE).symm (t + p)) :=
    fun t => by rw [hFdef]
  have hGx : G x = 0 := by rw [hG, hpdef]; ring
  have hκG : ∀ y, G y + p = κ y := fun y => by rw [hG]; ring
  have hGcont : ContinuousOn G (chartAt H x).source := by
    rw [hGdef]; exact (continuousOn_chartCoord I hE (chartAt H x)).sub continuousOn_const
  have hVopen : IsOpen V := by
    rw [hVdef]; exact hGcont.isOpen_inter_preimage (chartAt H x).open_source isOpen_Ioo
  have hxV : x ∈ V := ⟨hxs, by rw [mem_preimage, hGx]; exact ⟨by linarith, hε⟩⟩
  have hVsub : V ⊆ (chartAt H x).source := fun _ hy => hy.1
  -- `V` has interior coordinates, hence contains no boundary point
  have hVκ : ∀ y ∈ V, κ y ∈ W ∩ interior (modelRange I hE) := by
    intro y hy
    have h2 : G y ∈ Ioo (-ε) ε := hy.2
    rw [← hκG y]
    exact hshrink _ (by linarith [h2.1]) (by linarith [h2.2])
  have hVint : V ⊆ I.interior M := fun y hy =>
    (mem_interior_iff_chartCoord_mem_interior I hE hn (chart_mem_atlas H x) hy.1).2
      (hVκ y hy).2
  -- the image of `V` is exactly `Ioo (-ε) ε`
  have hGsurj : Ioo (-ε) ε ⊆ G '' (chartAt H x).source := by
    intro s hs
    have hts : s + p ∈ W ∩ modelRange I hE :=
      ⟨(hshrink (s + p) (by linarith [hs.1]) (by linarith [hs.2])).1,
        interior_subset (hshrink (s + p) (by linarith [hs.1]) (by linarith [hs.2])).2⟩
    rw [← hWimg] at hts
    obtain ⟨y, hy, hyt⟩ := hts
    exact ⟨y, hy, by rw [hG, hyt]; ring⟩
  have hVimg : G '' V = Ioo (-ε) ε := by
    rw [hVdef, Set.image_inter_preimage]
    exact Subset.antisymm inter_subset_right fun t ht => ⟨hGsurj ht, ht⟩
  have hexV : ∀ t ∈ Ioo (-ε) ε, ∃ y, y ∈ V ∧ G y = t := by
    intro t ht
    rw [← hVimg] at ht
    obtain ⟨y, hy, hyt⟩ := ht
    exact ⟨y, hy, hyt⟩
  have hFG : ∀ y ∈ (chartAt H x).source, F (G y) = y := by
    intro y hy
    rw [hF, hκG y, hκdef]
    show ((chartAt H x).extend I).symm
      ((modelCoord I hE).symm (modelCoord I hE (((chartAt H x).extend I) y))) = y
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (chartAt H x).extend_left_inv hy
  have hFmem : ∀ t ∈ Ioo (-ε) ε, F t ∈ V ∧ G (F t) = t := by
    intro t ht
    obtain ⟨y, hyV, hyt⟩ := hexV t ht
    rw [← hyt, hFG y hyV.1]
    exact ⟨hyV, rfl⟩
  have hinner : ∀ t ∈ Ioo (-ε) ε,
      (modelCoord I hE).symm (t + p) ∈ ((chartAt H x).extend I).target := by
    intro t ht
    obtain ⟨y, hyV, hyt⟩ := hexV t ht
    rw [← hyt, hκG y, hκdef]
    show (modelCoord I hE).symm (modelCoord I hE (((chartAt H x).extend I) y)) ∈ _
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact ((chartAt H x).extend I).map_source
      (by rw [OpenPartialHomeomorph.extend_source]; exact hyV.1)
  have hmapsrc : ∀ y ∈ V, G y ∈ Ioo (-ε) ε := fun y hy => by rw [← hVimg]; exact ⟨y, hy, rfl⟩
  have hFcont : ContinuousOn F (Ioo (-ε) ε) := by
    refine ((chartAt H x).continuousOn_extend_symm.comp ?_ hinner).congr fun t _ => hF t
    exact ((modelCoord I hE).symm.continuous.comp
      (continuous_id.add continuous_const)).continuousOn
  refine ⟨ε,
    { toFun := G
      invFun := F
      source := V
      target := Ioo (-ε) ε
      map_source' := hmapsrc
      map_target' := fun t ht => (hFmem t ht).1
      left_inv' := fun y hy => hFG y hy.1
      right_inv' := fun t ht => (hFmem t ht).2
      continuousOn_toFun := hGcont.mono hVsub
      continuousOn_invFun := hFcont },
    hε, hVopen, hxV, hVsub, fun y _ => hG y, hGx, rfl, hVint, ?_, ?_⟩
  · refine ContMDiffOn.mono ?_ hVsub
    exact contMDiffOn_comp_chartCoord I hE (IsManifold.chart_mem_maximalAtlas x)
      (contDiff_id.sub contDiff_const)
  · refine ContMDiffOn.congr ?_ fun t _ => hF t
    refine (contMDiffOn_extChartAt_symm x).comp ?_ hinner
    exact (((modelCoord I hE).symm.contDiff.comp
      (contDiff_id.add contDiff_const)).contMDiff).contMDiffOn

end Charts

end Milnor.OneManifold.Smooth
