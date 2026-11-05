import Mathlib

/-!
# Milnor's Appendix: classifying compact 1-manifolds (the boundary count)

Milnor, *Topology from the Differentiable Viewpoint*, Appendix, proves that every compact
connected 1-manifold is diffeomorphic to `S¹` or `[0,1]`; the book uses only the corollary that a
compact 1-manifold with boundary has an *even number of boundary points* (§2 Lemma 5, §4 homotopy
lemma, §5 Lemma 1, §6).  We prove that corollary, for *topological* 1-manifolds with boundary, from
the same idea (parametrize as far as possible from a boundary point), but with two simplifications
that make the argument formalizable with little infrastructure:

* charts are only required to be homeomorphisms onto intervals ("arcs"), so no arc-length
  reparametrization and no differentiability is used;
* the parametrization is only ever started from a *boundary* point, so the two-component
  ("circle") case of Milnor's Lemma never occurs, and no maximality principle is needed: a finite
  cover by chart arcs and an induction on the number of charts not yet absorbed suffice.

The main statement is `Milnor.OneManifold.even_ncard_boundary`.
-/

open Set Filter Topology

noncomputable section

namespace Milnor
namespace OneManifold

variable {M : Type*} [TopologicalSpace M] {B : Set M}

/-- An *arc* of the space `M` relative to the "boundary set" `B`: a homeomorphism from an open
subset of `M` onto an interval of `ℝ`, under which `B` corresponds to the endpoints of the
interval (the points of the target not in its interior). -/
structure Arc (M : Type*) [TopologicalSpace M] (B : Set M) where
  toFun : M → ℝ
  invFun : ℝ → M
  source : Set M
  target : Set ℝ
  map_source' : ∀ x ∈ source, toFun x ∈ target
  map_target' : ∀ t ∈ target, invFun t ∈ source
  left_inv' : ∀ x ∈ source, invFun (toFun x) = x
  right_inv' : ∀ t ∈ target, toFun (invFun t) = t
  open_source : IsOpen source
  ordConnected_target : target.OrdConnected
  nontrivial_target : target.Nontrivial
  bddAbove_target : BddAbove target
  bddBelow_target : BddBelow target
  continuousOn_toFun : ContinuousOn toFun source
  continuousOn_invFun : ContinuousOn invFun target
  bdry : ∀ x ∈ source, x ∈ B ↔ toFun x ∉ interior target

namespace Arc

variable (A : Arc M B)

theorem map_source {x : M} (hx : x ∈ A.source) : A.toFun x ∈ A.target := A.map_source' x hx
theorem map_target {t : ℝ} (ht : t ∈ A.target) : A.invFun t ∈ A.source := A.map_target' t ht
theorem left_inv {x : M} (hx : x ∈ A.source) : A.invFun (A.toFun x) = x := A.left_inv' x hx
theorem right_inv {t : ℝ} (ht : t ∈ A.target) : A.toFun (A.invFun t) = t := A.right_inv' t ht

theorem injOn : InjOn A.toFun A.source := fun x hx y hy h => by
  rw [← A.left_inv hx, ← A.left_inv hy, h]

theorem injOn_invFun : InjOn A.invFun A.target := fun s hs t ht h => by
  rw [← A.right_inv hs, ← A.right_inv ht, h]

theorem image_source : A.toFun '' A.source = A.target := by
  ext t; constructor
  · rintro ⟨x, hx, rfl⟩; exact A.map_source hx
  · intro ht; exact ⟨A.invFun t, A.map_target ht, A.right_inv ht⟩

theorem image_target : A.invFun '' A.target = A.source := by
  ext x; constructor
  · rintro ⟨t, ht, rfl⟩; exact A.map_target ht
  · intro hx; exact ⟨A.toFun x, A.map_source hx, A.left_inv hx⟩

/-- The image of an open subset of the source is relatively open in the target. -/
theorem image_open {V : Set M} (hV : IsOpen V) (hVs : V ⊆ A.source) :
    ∃ W : Set ℝ, IsOpen W ∧ A.toFun '' V = W ∩ A.target := by
  obtain ⟨W, hW, hWV⟩ := (continuousOn_iff'.1 A.continuousOn_invFun) V hV
  refine ⟨W, hW, ?_⟩
  rw [← hWV]; ext t; constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa [A.left_inv (hVs hx)] using hx, A.map_source (hVs hx)⟩
  · rintro ⟨hx, ht⟩
    exact ⟨A.invFun t, hx, A.right_inv ht⟩

theorem source_nonempty : A.source.Nonempty := by
  obtain ⟨t, ht, -⟩ := A.nontrivial_target
  exact ⟨A.invFun t, A.map_target ht⟩

theorem isPreconnected_source : IsPreconnected A.source := by
  rw [← A.image_target]
  exact A.ordConnected_target.isPreconnected.image _ A.continuousOn_invFun

theorem target_subset_Icc : A.target ⊆ Icc (sInf A.target) (sSup A.target) := fun t ht =>
  ⟨csInf_le A.bddBelow_target ht, le_csSup A.bddAbove_target ht⟩

theorem Ioo_subset_target : Ioo (sInf A.target) (sSup A.target) ⊆ A.target := by
  intro t ht
  obtain ⟨a, ha, hat⟩ := exists_lt_of_csInf_lt A.nontrivial_target.nonempty ht.1
  obtain ⟨b, hb, htb⟩ := exists_lt_of_lt_csSup A.nontrivial_target.nonempty ht.2
  exact A.ordConnected_target.out ha hb ⟨hat.le, htb.le⟩

theorem sInf_lt_sSup : sInf A.target < sSup A.target := by
  obtain ⟨a, ha, b, hb, hab⟩ := A.nontrivial_target
  rcases lt_or_gt_of_ne hab with h | h
  · exact (csInf_le A.bddBelow_target ha).trans_lt (h.trans_le (le_csSup A.bddAbove_target hb))
  · exact (csInf_le A.bddBelow_target hb).trans_lt (h.trans_le (le_csSup A.bddAbove_target ha))

theorem interior_target : interior A.target = Ioo (sInf A.target) (sSup A.target) := by
  apply Subset.antisymm
  · calc interior A.target ⊆ interior (Icc (sInf A.target) (sSup A.target)) :=
          interior_mono A.target_subset_Icc
      _ = Ioo _ _ := interior_Icc
  · exact interior_maximal A.Ioo_subset_target isOpen_Ioo

/-- A point of the target which is not interior is the infimum or the supremum. -/
theorem eq_sInf_or_eq_sSup_of_notMem_interior {t : ℝ} (ht : t ∈ A.target)
    (h : t ∉ interior A.target) : t = sInf A.target ∨ t = sSup A.target := by
  rw [A.interior_target, mem_Ioo, not_and_or, not_lt, not_lt] at h
  rcases h with h | h
  · exact Or.inl (le_antisymm h (csInf_le A.bddBelow_target ht))
  · exact Or.inr (le_antisymm (le_csSup A.bddAbove_target ht) h)

/-- Negating the coordinate. -/
def neg (A : Arc M B) : Arc M B where
  toFun x := -A.toFun x
  invFun t := A.invFun (-t)
  source := A.source
  target := -A.target
  map_source' x hx := by simpa using A.map_source hx
  map_target' t ht := A.map_target ht
  left_inv' x hx := by simpa using A.left_inv hx
  right_inv' t ht := by
    show -A.toFun (A.invFun (-t)) = t
    rw [A.right_inv ht, neg_neg]
  open_source := A.open_source
  ordConnected_target := ⟨fun a ha b hb t ht =>
    A.ordConnected_target.out hb ha ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩⟩
  nontrivial_target := by
    obtain ⟨a, ha, b, hb, hab⟩ := A.nontrivial_target
    exact ⟨-a, by simpa using ha, -b, by simpa using hb, by simpa using hab⟩
  bddAbove_target := by
    obtain ⟨m, hm⟩ := A.bddBelow_target
    exact ⟨-m, fun t ht => by have := hm ht; linarith⟩
  bddBelow_target := by
    obtain ⟨m, hm⟩ := A.bddAbove_target
    exact ⟨-m, fun t ht => by have := hm ht; linarith⟩
  continuousOn_toFun := A.continuousOn_toFun.neg
  continuousOn_invFun := A.continuousOn_invFun.comp continuous_neg.continuousOn (fun t ht => ht)
  bdry x hx := by
    rw [A.bdry x hx]
    have h := (Homeomorph.neg ℝ).preimage_interior A.target
    have e : (⇑(Homeomorph.neg ℝ) : ℝ → ℝ) = fun x => -x := rfl
    rw [e] at h
    show A.toFun x ∉ interior A.target ↔ -A.toFun x ∉ interior ((fun x : ℝ => -x) ⁻¹' A.target)
    rw [← h]; simp

@[simp] theorem neg_toFun (x : M) : A.neg.toFun x = -A.toFun x := rfl
@[simp] theorem neg_invFun (t : ℝ) : A.neg.invFun t = A.invFun (-t) := rfl
@[simp] theorem neg_source : A.neg.source = A.source := rfl
@[simp] theorem neg_target : A.neg.target = -A.target := rfl

end Arc

/-! ### Arcs from the charts of a charted space modelled on the half-line -/

section Charts

variable {H : Type*} [TopologicalSpace H] (φ : H ≃ₜ Ici (0 : ℝ)) [ChartedSpace H M]

/-- The real coordinate of a point of the model half-line. -/
def coord (h : H) : ℝ := (φ h : ℝ)

theorem coord_nonneg (h : H) : 0 ≤ coord φ h := (φ h).2

theorem continuous_coord : Continuous (coord φ) := continuous_subtype_val.comp φ.continuous

theorem coord_injective : Function.Injective (coord φ) := fun a b h =>
  φ.injective (Subtype.ext h)

/-- The point of `H` with a given nonnegative coordinate (`max t 0` for a total function). -/
def ofCoord (t : ℝ) : H := φ.symm ⟨max t 0, Set.mem_Ici.2 (le_max_right _ _)⟩

theorem continuous_ofCoord : Continuous (ofCoord φ) :=
  φ.symm.continuous.comp (Continuous.subtype_mk (continuous_id.max continuous_const) _)

theorem coord_ofCoord {t : ℝ} (ht : 0 ≤ t) : coord φ (ofCoord φ t) = t := by
  simp [coord, ofCoord, max_eq_left ht]

theorem ofCoord_coord (h : H) : ofCoord φ (coord φ h) = h := by
  simp only [ofCoord, coord]
  exact (congrArg φ.symm (Subtype.ext (max_eq_left (Set.mem_Ici.1 (φ h).2)))).trans
    (φ.symm_apply_apply h)

/-- The boundary hypothesis: every chart sends exactly the points of `B` to coordinate `0`. -/
def BoundaryCompatible (B : Set M) : Prop :=
  ∀ e ∈ atlas H M, ∀ x ∈ e.source, x ∈ B ↔ coord φ (e x) = 0

variable {φ}

/-- Given a chart `e`, a point `y` in its source, and an interval `J ⊆ Ici 0` such that
the points of `H` with coordinate in `J` lie in the target of `e`, the restriction of `e` to the
preimage of `J` is an arc. -/
def arcOfChart (hB : BoundaryCompatible φ B) (e : OpenPartialHomeomorph M H) (he : e ∈ atlas H M)
    (J : Set ℝ) (hJ0 : J ⊆ Ici 0) (hJ : ∀ t ∈ J, ofCoord φ t ∈ e.target)
    (hJopen : IsOpen (coord φ ⁻¹' J))
    (hJc : J.OrdConnected) (hJn : J.Nontrivial) (hJa : BddAbove J) (hJb : BddBelow J)
    (hJi : ∀ t ∈ J, t = 0 ↔ t ∉ interior J) : Arc M B where
  toFun x := coord φ (e x)
  invFun t := e.symm (ofCoord φ t)
  source := e.source ∩ e ⁻¹' (coord φ ⁻¹' J)
  target := J
  map_source' x hx := hx.2
  map_target' t ht := by
    refine ⟨e.map_target (hJ t ht), ?_⟩
    show coord φ (e (e.symm (ofCoord φ t))) ∈ J
    rw [e.right_inv (hJ t ht), coord_ofCoord φ (hJ0 ht)]; exact ht
  left_inv' x hx := by
    show e.symm (ofCoord φ (coord φ (e x))) = x
    rw [ofCoord_coord, e.left_inv hx.1]
  right_inv' t ht := by
    show coord φ (e (e.symm (ofCoord φ t))) = t
    rw [e.right_inv (hJ t ht), coord_ofCoord φ (hJ0 ht)]
  open_source := e.continuousOn.isOpen_inter_preimage e.open_source hJopen
  ordConnected_target := hJc
  nontrivial_target := hJn
  bddAbove_target := hJa
  bddBelow_target := hJb
  continuousOn_toFun := ((continuous_coord φ).comp_continuousOn e.continuousOn).mono
    inter_subset_left
  continuousOn_invFun := e.continuousOn_symm.comp (continuous_ofCoord φ).continuousOn hJ
  bdry x hx := by
    rw [hB e he x hx.1]
    exact hJi _ hx.2

theorem arcOfChart_source (hB : BoundaryCompatible φ B) (e : OpenPartialHomeomorph M H)
    (he : e ∈ atlas H M) (J : Set ℝ) (hJ0 hJ hJopen hJc hJn hJa hJb hJi) :
    (arcOfChart hB e he J hJ0 hJ hJopen hJc hJn hJa hJb hJi).source =
      e.source ∩ e ⁻¹' (coord φ ⁻¹' J) := rfl

theorem arcOfChart_target (hB : BoundaryCompatible φ B) (e : OpenPartialHomeomorph M H)
    (he : e ∈ atlas H M) (J : Set ℝ) (hJ0 hJ hJopen hJc hJn hJa hJb hJi) :
    (arcOfChart hB e he J hJ0 hJ hJopen hJc hJn hJa hJb hJi).target = J := rfl

theorem arcOfChart_toFun (hB : BoundaryCompatible φ B) (e : OpenPartialHomeomorph M H)
    (he : e ∈ atlas H M) (J : Set ℝ) (hJ0 hJ hJopen hJc hJn hJa hJb hJi) (x : M) :
    (arcOfChart hB e he J hJ0 hJ hJopen hJc hJn hJa hJb hJi).toFun x = coord φ (e x) := rfl

/-- Around a point `y`, the chart at `y` provides a radius `ε` such that every point of the
model with coordinate within `ε` of that of `y` lies in the chart's target. -/
theorem exists_radius (y : M) : ∃ ε > 0, ∀ t : ℝ, |t - coord φ (chartAt H y y)| < ε →
    ofCoord φ t ∈ (chartAt H y).target := by
  have h0 : ofCoord φ (coord φ (chartAt H y y)) ∈ (chartAt H y).target := by
    rw [ofCoord_coord]; exact mem_chart_target H y
  have : ofCoord φ ⁻¹' (chartAt H y).target ∈ 𝓝 (coord φ (chartAt H y y)) :=
    (continuous_ofCoord φ).continuousAt.preimage_mem_nhds
      ((chartAt H y).open_target.mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 this
  exact ⟨ε, hε, fun t ht => hball (by rwa [Metric.mem_ball, Real.dist_eq])⟩

/-- An arc starting at a boundary point: its target is `Ico 0 ε` and the point has coordinate `0`.
-/
theorem exists_arc_of_mem_boundary (hB : BoundaryCompatible φ B) {p : M} (hp : p ∈ B) :
    ∃ (A : Arc M B) (ε : ℝ), 0 < ε ∧ p ∈ A.source ∧ A.toFun p = 0 ∧ A.target = Ico 0 ε := by
  set e := chartAt H p with he_def
  have he : e ∈ atlas H M := chart_mem_atlas H p
  have hp0 : coord φ (e p) = 0 := (hB e he p (mem_chart_source H p)).1 hp
  obtain ⟨ε, hε, hball⟩ := exists_radius (φ := φ) p
  rw [hp0] at hball
  have hJ0 : Ico 0 ε ⊆ Ici (0 : ℝ) := Ico_subset_Ici_self
  have hJ : ∀ t ∈ Ico (0 : ℝ) ε, ofCoord φ t ∈ e.target := fun t ht =>
    hball t (by rw [sub_zero, abs_of_nonneg ht.1]; exact ht.2)
  have hJopen : IsOpen (coord φ ⁻¹' Ico 0 ε) := by
    have : coord φ ⁻¹' Ico 0 ε = coord φ ⁻¹' Iio ε := by
      ext h; simp [coord_nonneg φ h]
    rw [this]; exact isOpen_Iio.preimage (continuous_coord φ)
  have hJi : ∀ t ∈ Ico (0 : ℝ) ε, t = 0 ↔ t ∉ interior (Ico 0 ε) := by
    intro t ht; rw [interior_Ico, mem_Ioo, not_and_or, not_lt, not_lt]
    constructor
    · rintro rfl; exact Or.inl le_rfl
    · rintro (h | h)
      · exact le_antisymm h ht.1
      · exact absurd ht.2 (not_lt.2 h)
  have hJn : (Ico (0 : ℝ) ε).Nontrivial :=
    ⟨0, ⟨le_rfl, hε⟩, ε / 2, ⟨by positivity, by linarith⟩, by linarith⟩
  refine ⟨arcOfChart hB e he (Ico 0 ε) hJ0 hJ hJopen ordConnected_Ico
    hJn bddAbove_Ico bddBelow_Ico hJi, ε, hε, ?_, ?_, rfl⟩
  · exact ⟨mem_chart_source H p, by show coord φ (e p) ∈ Ico 0 ε; rw [hp0]; exact ⟨le_rfl, hε⟩⟩
  · exact hp0

/-- An arc around an interior point: its target is an open interval of positive reals. -/
theorem exists_arc_of_notMem_boundary (hB : BoundaryCompatible φ B) {y : M} (hy : y ∉ B) :
    ∃ A : Arc M B, y ∈ A.source ∧ interior A.target = A.target := by
  set e := chartAt H y with he_def
  have he : e ∈ atlas H M := chart_mem_atlas H y
  set t₀ := coord φ (e y) with ht₀
  have hy0 : t₀ ≠ 0 := fun h => hy ((hB e he y (mem_chart_source H y)).2 h)
  have hpos : 0 < t₀ := lt_of_le_of_ne (coord_nonneg φ _) (Ne.symm hy0)
  obtain ⟨ε, hε, hball⟩ := exists_radius (φ := φ) y
  set δ := min ε t₀ with hδ
  have hδpos : 0 < δ := lt_min hε hpos
  have hδε : δ ≤ ε := min_le_left _ _
  have hδt : δ ≤ t₀ := min_le_right _ _
  have hJ0 : Ioo (t₀ - δ) (t₀ + δ) ⊆ Ici (0 : ℝ) := fun t ht => by
    simp only [mem_Ici]; linarith [ht.1]
  have hJ : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), ofCoord φ t ∈ e.target := fun t ht =>
    hball t (by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2])
  have hJopen : IsOpen (coord φ ⁻¹' Ioo (t₀ - δ) (t₀ + δ)) :=
    isOpen_Ioo.preimage (continuous_coord φ)
  have hJi : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), t = 0 ↔ t ∉ interior (Ioo (t₀ - δ) (t₀ + δ)) := by
    intro t ht; rw [interior_Ioo]
    constructor
    · rintro rfl; linarith [ht.1]
    · intro h; exact absurd ht h
  have hJn : (Ioo (t₀ - δ) (t₀ + δ)).Nontrivial :=
    ⟨t₀, ⟨by linarith, by linarith⟩, t₀ + δ / 2, ⟨by linarith, by linarith⟩, by linarith⟩
  refine ⟨arcOfChart hB e he _ hJ0 hJ hJopen ordConnected_Ioo
    hJn bddAbove_Ioo bddBelow_Ioo hJi, ?_, interior_Ioo⟩
  exact ⟨mem_chart_source H y, by
    show coord φ (e y) ∈ Ioo (t₀ - δ) (t₀ + δ); rw [← ht₀]; constructor <;> linarith⟩

/-- Boundary points are isolated in `B`: the arc from `p` meets `B` only at `p`. -/
theorem boundary_inter_source_eq {A : Arc M B} {p : M} {ε : ℝ} (hε : 0 < ε)
    (hp : A.toFun p = 0) (hpA : p ∈ A.source) (hT : A.target = Ico 0 ε) :
    B ∩ A.source = {p} := by
  ext x; constructor
  · rintro ⟨hxB, hxA⟩
    have h := (A.bdry x hxA).1 hxB
    rw [hT, interior_Ico, mem_Ioo, not_and_or, not_lt, not_lt] at h
    have hx0 : A.toFun x = 0 := by
      have hxt := A.map_source hxA; rw [hT] at hxt
      rcases h with h | h
      · exact le_antisymm h hxt.1
      · exact absurd hxt.2 (not_lt.2 h)
    rw [mem_singleton_iff, ← A.left_inv hxA, ← A.left_inv hpA, hx0, hp]
  · rintro rfl
    exact ⟨(A.bdry _ hpA).2 (by rw [hp, hT, interior_Ico]; simp), hpA⟩

theorem isClosed_boundary (hB : BoundaryCompatible φ B) : IsClosed B := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨A, hyA, hint⟩ := exists_arc_of_notMem_boundary hB hy
  refine ⟨A.source, fun x hx hxB => ?_, A.open_source, hyA⟩
  have hm := A.map_source hx
  rw [← hint] at hm
  exact (A.bdry x hx).1 hxB hm

theorem finite_boundary [CompactSpace M] (hB : BoundaryCompatible φ B) : B.Finite := by
  have hc : IsCompact B := (isClosed_boundary hB).isCompact
  choose A ε hε hpA hp hT using fun p : B => exists_arc_of_mem_boundary hB p.2
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover (fun p : B => (A p).source)
    (fun p => (A p).open_source) (fun p hp => mem_iUnion.2 ⟨⟨p, hp⟩, hpA ⟨p, hp⟩⟩)
  refine (s.finite_toSet.image (fun p : B => (p : M))).subset fun x hx => ?_
  obtain ⟨p, hps, hxp⟩ := mem_iUnion₂.1 (hs hx)
  have : x ∈ B ∩ (A p).source := ⟨hx, hxp⟩
  rw [boundary_inter_source_eq (hε p) (hp p) (hpA p) (hT p), mem_singleton_iff] at this
  subst this
  exact ⟨p, hps, rfl⟩

end Charts

/-! ### Hulls: maximal intervals inside a subset of `ℝ` -/

section Hull

/-- The *hull* of a point `t₀` in a set `S ⊆ ℝ`: the largest interval inside `S` containing `t₀`.
-/
def hull (S : Set ℝ) (t₀ : ℝ) : Set ℝ := {t | uIcc t t₀ ⊆ S}

theorem mem_hull {S : Set ℝ} {t₀ t : ℝ} : t ∈ hull S t₀ ↔ uIcc t t₀ ⊆ S := Iff.rfl

theorem hull_subset (S : Set ℝ) (t₀ : ℝ) : hull S t₀ ⊆ S := fun _ h => h left_mem_uIcc

theorem mem_hull_self {S : Set ℝ} {t₀ : ℝ} (h : t₀ ∈ S) : t₀ ∈ hull S t₀ := by
  rw [mem_hull, uIcc_self, singleton_subset_iff]; exact h

theorem hull_ordConnected (S : Set ℝ) (t₀ : ℝ) : (hull S t₀).OrdConnected := by
  refine ⟨fun a ha b hb t ht => ?_⟩
  rw [mem_hull]
  rcases le_total t t₀ with h | h
  · exact (uIcc_subset_uIcc (mem_uIcc.2 (Or.inl ⟨ht.1, h⟩)) right_mem_uIcc).trans ha
  · exact (uIcc_subset_uIcc (mem_uIcc.2 (Or.inr ⟨h, ht.2⟩)) right_mem_uIcc).trans hb

theorem hull_eq_of_mem {S : Set ℝ} {t₀ t : ℝ} (ht : t ∈ hull S t₀) : hull S t = hull S t₀ := by
  ext u; constructor
  · intro hu
    exact (uIcc_subset_uIcc_union_uIcc (b := t)).trans (union_subset hu ht)
  · intro hu
    rw [mem_hull] at ht ⊢
    exact (uIcc_subset_uIcc_union_uIcc (b := t₀)).trans (union_subset hu (by
      rw [uIcc_comm]; exact ht))

theorem hull_eq_or_disjoint {S : Set ℝ} {t₁ t₂ : ℝ} :
    hull S t₁ = hull S t₂ ∨ Disjoint (hull S t₁) (hull S t₂) := by
  by_cases h : (hull S t₁ ∩ hull S t₂).Nonempty
  · obtain ⟨u, hu₁, hu₂⟩ := h
    exact Or.inl ((hull_eq_of_mem hu₁).symm.trans (hull_eq_of_mem hu₂))
  · exact Or.inr (disjoint_iff_inter_eq_empty.2 (not_nonempty_iff_eq_empty.1 h))

/-- If `S` is relatively open in an interval `J`, its hulls are relatively open in `J`. -/
theorem hull_relOpen {S W J : Set ℝ} (hW : IsOpen W) (hS : S = W ∩ J) (hJ : J.OrdConnected)
    {t₀ t : ℝ} (ht : t ∈ hull S t₀) :
    ∃ ε > 0, ∀ u ∈ J, |u - t| < ε → u ∈ hull S t₀ := by
  have htS : t ∈ S := hull_subset S t₀ ht
  have htW : t ∈ W := by rw [hS] at htS; exact htS.1
  have htJ : t ∈ J := by rw [hS] at htS; exact htS.2
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW t htW
  refine ⟨ε, hε, fun u hu hut => ?_⟩
  have h1 : uIcc u t ⊆ S := by
    intro v hv
    rw [hS]
    refine ⟨hball ?_, hJ.uIcc_subset hu htJ hv⟩
    rw [Metric.mem_ball, Real.dist_eq]
    rcases le_total u t with h | h
    · rw [uIcc_of_le h] at hv
      rw [abs_lt] at hut ⊢; constructor <;> linarith [hv.1, hv.2]
    · rw [uIcc_of_ge h] at hv
      rw [abs_lt] at hut ⊢; constructor <;> linarith [hv.1, hv.2]
  exact (uIcc_subset_uIcc_union_uIcc (b := t)).trans (union_subset h1 ht)

/-- If the supremum of a hull belongs to `S`, it belongs to the hull. -/
theorem sSup_mem_hull {S : Set ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hb : BddAbove (hull S t₀))
    (hS : sSup (hull S t₀) ∈ S) : sSup (hull S t₀) ∈ hull S t₀ := by
  have hmem := mem_hull_self ht₀
  have hle : t₀ ≤ sSup (hull S t₀) := le_csSup hb hmem
  rw [mem_hull, uIcc_of_ge hle]
  intro v hv
  rcases eq_or_lt_of_le hv.2 with h | h
  · rw [h]; exact hS
  · obtain ⟨c, hc, hvc⟩ := exists_lt_of_lt_csSup ⟨t₀, hmem⟩ h
    exact hull_subset S t₀ ((hull_ordConnected S t₀).out hmem hc ⟨hv.1, hvc.le⟩)

theorem sInf_mem_hull {S : Set ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hb : BddBelow (hull S t₀))
    (hS : sInf (hull S t₀) ∈ S) : sInf (hull S t₀) ∈ hull S t₀ := by
  have hmem := mem_hull_self ht₀
  have hle : sInf (hull S t₀) ≤ t₀ := csInf_le hb hmem
  rw [mem_hull, uIcc_of_le hle]
  intro v hv
  rcases eq_or_lt_of_le hv.1 with h | h
  · rw [← h]; exact hS
  · obtain ⟨c, hc, hvc⟩ := exists_lt_of_csInf_lt ⟨t₀, hmem⟩ h
    exact hull_subset S t₀ ((hull_ordConnected S t₀).out hc hmem ⟨hvc.le, hv.2⟩)

/-- Two hulls with the same supremum, not attained, intersect (hence coincide). -/
theorem hull_eq_of_sSup_eq {S : Set ℝ} {t₁ t₂ : ℝ} (h₁ : t₁ ∈ S) (h₂ : t₂ ∈ S)
    (hb₁ : BddAbove (hull S t₁)) (hb₂ : BddAbove (hull S t₂))
    (heq : sSup (hull S t₁) = sSup (hull S t₂)) (hn₁ : sSup (hull S t₁) ∉ hull S t₁)
    (hn₂ : sSup (hull S t₂) ∉ hull S t₂) : hull S t₁ = hull S t₂ := by
  rcases hull_eq_or_disjoint (S := S) (t₁ := t₁) (t₂ := t₂) with h | hdisj
  · exact h
  exfalso
  have hm₁ := mem_hull_self h₁
  have hm₂ := mem_hull_self h₂
  have hlt₁ : t₁ < sSup (hull S t₁) :=
    lt_of_le_of_ne (le_csSup hb₁ hm₁) (fun h => hn₁ (by rw [← h]; exact hm₁))
  have hlt₂ : t₂ < sSup (hull S t₂) :=
    lt_of_le_of_ne (le_csSup hb₂ hm₂) (fun h => hn₂ (by rw [← h]; exact hm₂))
  rcases le_total t₁ t₂ with h | h
  · obtain ⟨c, hc, hc'⟩ := exists_lt_of_lt_csSup ⟨t₁, hm₁⟩ (by rw [heq]; exact hlt₂)
    exact hdisj.notMem_of_mem_left ((hull_ordConnected S t₁).out hm₁ hc ⟨h, hc'.le⟩) hm₂
  · obtain ⟨c, hc, hc'⟩ := exists_lt_of_lt_csSup ⟨t₂, hm₂⟩ (by rw [← heq]; exact hlt₁)
    exact hdisj.notMem_of_mem_right ((hull_ordConnected S t₂).out hm₂ hc ⟨h, hc'.le⟩) hm₁

theorem hull_eq_of_sInf_eq {S : Set ℝ} {t₁ t₂ : ℝ} (h₁ : t₁ ∈ S) (h₂ : t₂ ∈ S)
    (hb₁ : BddBelow (hull S t₁)) (hb₂ : BddBelow (hull S t₂))
    (heq : sInf (hull S t₁) = sInf (hull S t₂)) (hn₁ : sInf (hull S t₁) ∉ hull S t₁)
    (hn₂ : sInf (hull S t₂) ∉ hull S t₂) : hull S t₁ = hull S t₂ := by
  rcases hull_eq_or_disjoint (S := S) (t₁ := t₁) (t₂ := t₂) with h | hdisj
  · exact h
  exfalso
  have hm₁ := mem_hull_self h₁
  have hm₂ := mem_hull_self h₂
  have hlt₁ : sInf (hull S t₁) < t₁ :=
    lt_of_le_of_ne (csInf_le hb₁ hm₁) (fun h => hn₁ (by rw [h]; exact hm₁))
  have hlt₂ : sInf (hull S t₂) < t₂ :=
    lt_of_le_of_ne (csInf_le hb₂ hm₂) (fun h => hn₂ (by rw [h]; exact hm₂))
  rcases le_total t₁ t₂ with h | h
  · obtain ⟨c, hc, hc'⟩ := exists_lt_of_csInf_lt ⟨t₂, hm₂⟩ (by rw [← heq]; exact hlt₁)
    exact hdisj.notMem_of_mem_right ((hull_ordConnected S t₂).out hc hm₂ ⟨hc'.le, h⟩) hm₁
  · obtain ⟨c, hc, hc'⟩ := exists_lt_of_csInf_lt ⟨t₁, hm₁⟩ (by rw [heq]; exact hlt₂)
    exact hdisj.notMem_of_mem_left ((hull_ordConnected S t₁).out hc hm₁ ⟨hc'.le, h⟩) hm₂

end Hull

/-! ### Continuous injective maps on intervals are strictly monotone -/

section Monotone

theorem strictMonoOn_or_strictAntiOn_of_ordConnected {C : Set ℝ} {f : ℝ → ℝ}
    (hC : C.OrdConnected) (hn : C.Nontrivial) (hf : ContinuousOn f C) (hi : InjOn f C) :
    StrictMonoOn f C ∨ StrictAntiOn f C := by
  obtain ⟨a, ha, b, hb, hab⟩ := hn
  wlog hlt : a < b generalizing a b
  · exact this b hb a ha hab.symm (lt_of_le_of_ne (not_lt.1 hlt) hab.symm)
  have key : ∀ x ∈ C, ∀ y ∈ C, x < y →
      (f a < f b → f x < f y) ∧ (f b < f a → f y < f x) := by
    intro x hx y hy hxy
    set l := min a x with hl
    set r := max b y with hr
    have hlC : l ∈ C := by rcases min_choice a x with h | h <;> rw [hl, h] <;> assumption
    have hrC : r ∈ C := by rcases max_choice b y with h | h <;> rw [hr, h] <;> assumption
    have hlr : l ≤ r := (min_le_left _ _).trans (hlt.le.trans (le_max_left _ _))
    have hsub : Icc l r ⊆ C := hC.out hlC hrC
    have haI : a ∈ Icc l r := ⟨min_le_left _ _, hlt.le.trans (le_max_left _ _)⟩
    have hbI : b ∈ Icc l r := ⟨(min_le_left _ _).trans hlt.le, le_max_left _ _⟩
    have hxI : x ∈ Icc l r := ⟨min_le_right _ _, hxy.le.trans (le_max_right _ _)⟩
    have hyI : y ∈ Icc l r := ⟨(min_le_right _ _).trans hxy.le, le_max_right _ _⟩
    rcases ContinuousOn.strictMonoOn_of_injOn_Icc' hlr (hf.mono hsub) (hi.mono hsub) with h | h
    · exact ⟨fun _ => h hxI hyI hxy, fun hba => absurd (h haI hbI hlt) (not_lt.2 hba.le)⟩
    · exact ⟨fun hab' => absurd (h haI hbI hlt) (not_lt.2 hab'.le), fun _ => h hxI hyI hxy⟩
  rcases lt_or_gt_of_ne (hi.ne ha hb hab) with h | h
  · exact Or.inl fun x hx y hy hxy => (key x hx y hy hxy).1 h
  · exact Or.inr fun x hx y hy hxy => (key x hx y hy hxy).2 h

/-- A monotone function on a set `C ⊆ Iio β` with `sSup C = β` tends to `sSup (f '' C)` at `β`
within `C`. -/
theorem tendsto_sSup_of_monotoneOn {C : Set ℝ} {f : ℝ → ℝ} {β : ℝ} (hf : MonotoneOn f C)
    (hne : C.Nonempty) (hβ : sSup C = β) (hC : C ⊆ Iio β) (hb : BddAbove (f '' C)) :
    Tendsto f (𝓝[C] β) (𝓝 (sSup (f '' C))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨_, ⟨c₁, hc₁, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (hne.image f)
    (show sSup (f '' C) - ε < sSup (f '' C) by linarith)
  have hc₁β : c₁ < β := hC hc₁
  refine ⟨β - c₁, by linarith, fun s hs hsβ => ?_⟩
  have hs1 : s < β := hC hs
  rw [Real.dist_eq, abs_lt] at hsβ
  have hcs : c₁ ≤ s := by linarith [hsβ.1]
  have h1 : f c₁ ≤ f s := hf hc₁ hs hcs
  have h2 : f s ≤ sSup (f '' C) := le_csSup hb ⟨s, hs, rfl⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

theorem tendsto_sInf_of_antitoneOn {C : Set ℝ} {f : ℝ → ℝ} {β : ℝ} (hf : AntitoneOn f C)
    (hne : C.Nonempty) (hβ : sSup C = β) (hC : C ⊆ Iio β) (hb : BddBelow (f '' C)) :
    Tendsto f (𝓝[C] β) (𝓝 (sInf (f '' C))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨_, ⟨c₁, hc₁, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne.image f)
    (show sInf (f '' C) < sInf (f '' C) + ε by linarith)
  have hc₁β : c₁ < β := hC hc₁
  refine ⟨β - c₁, by linarith, fun s hs hsβ => ?_⟩
  have hs1 : s < β := hC hs
  rw [Real.dist_eq, abs_lt] at hsβ
  have hcs : c₁ ≤ s := by linarith [hsβ.1]
  have h1 : f s ≤ f c₁ := hf hc₁ hs hcs
  have h2 : sInf (f '' C) ≤ f s := csInf_le hb ⟨s, hs, rfl⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

theorem tendsto_sInf_of_monotoneOn {C : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (hf : MonotoneOn f C)
    (hne : C.Nonempty) (hα : sInf C = α) (hC : C ⊆ Ioi α) (hb : BddBelow (f '' C)) :
    Tendsto f (𝓝[C] α) (𝓝 (sInf (f '' C))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨_, ⟨c₁, hc₁, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne.image f)
    (show sInf (f '' C) < sInf (f '' C) + ε by linarith)
  have hc₁α : α < c₁ := hC hc₁
  refine ⟨c₁ - α, by linarith, fun s hs hsα => ?_⟩
  have hs1 : α < s := hC hs
  rw [Real.dist_eq, abs_lt] at hsα
  have hcs : s ≤ c₁ := by linarith [hsα.2]
  have h1 : f s ≤ f c₁ := hf hs hc₁ hcs
  have h2 : sInf (f '' C) ≤ f s := csInf_le hb ⟨s, hs, rfl⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

theorem tendsto_sSup_of_antitoneOn {C : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (hf : AntitoneOn f C)
    (hne : C.Nonempty) (hα : sInf C = α) (hC : C ⊆ Ioi α) (hb : BddAbove (f '' C)) :
    Tendsto f (𝓝[C] α) (𝓝 (sSup (f '' C))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨_, ⟨c₁, hc₁, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup (hne.image f)
    (show sSup (f '' C) - ε < sSup (f '' C) by linarith)
  have hc₁α : α < c₁ := hC hc₁
  refine ⟨c₁ - α, by linarith, fun s hs hsα => ?_⟩
  have hs1 : α < s := hC hs
  rw [Real.dist_eq, abs_lt] at hsα
  have hcs : s ≤ c₁ := by linarith [hsα.2]
  have h1 : f c₁ ≤ f s := hf hs hc₁ hcs
  have h2 : f s ≤ sSup (f '' C) := le_csSup hb ⟨s, hs, rfl⟩
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

end Monotone

/-! ### The transition map between two arcs -/

section Transition

variable [T2Space M] (A A' : Arc M B)

/-- The coordinates (in `A`) of the overlap of the two arcs. -/
def overlap : Set ℝ := A.toFun '' (A.source ∩ A'.source)

/-- The transition map, from `A`-coordinates to `A'`-coordinates. -/
def trans (s : ℝ) : ℝ := A'.toFun (A.invFun s)

theorem overlap_subset : overlap A A' ⊆ A.target := by
  rintro _ ⟨x, hx, rfl⟩; exact A.map_source hx.1

theorem invFun_mem_of_mem_overlap {s : ℝ} (hs : s ∈ overlap A A') :
    A.invFun s ∈ A.source ∩ A'.source := by
  obtain ⟨x, hx, rfl⟩ := hs
  rw [A.left_inv hx.1]; exact hx

theorem trans_mem_target {s : ℝ} (hs : s ∈ overlap A A') : trans A A' s ∈ A'.target :=
  A'.map_source (invFun_mem_of_mem_overlap A A' hs).2

theorem trans_mem_overlap {s : ℝ} (hs : s ∈ overlap A A') :
    trans A A' s ∈ overlap A' A :=
  ⟨A.invFun s, (invFun_mem_of_mem_overlap A A' hs).symm, rfl⟩

theorem invFun_eq_of_mem_overlap {s : ℝ} (hs : s ∈ overlap A A') :
    A'.invFun (trans A A' s) = A.invFun s :=
  A'.left_inv (invFun_mem_of_mem_overlap A A' hs).2

theorem trans_injOn : InjOn (trans A A') (overlap A A') := fun s hs t ht h => by
  have h1 := invFun_mem_of_mem_overlap A A' hs
  have h2 := invFun_mem_of_mem_overlap A A' ht
  exact A.injOn_invFun (overlap_subset A A' hs) (overlap_subset A A' ht)
    (A'.injOn h1.2 h2.2 h)

theorem trans_continuousOn : ContinuousOn (trans A A') (overlap A A') :=
  A'.continuousOn_toFun.comp (A.continuousOn_invFun.mono (overlap_subset A A'))
    (fun s hs => (invFun_mem_of_mem_overlap A A' hs).2)

/-- The overlap is relatively open in the target of `A`. -/
theorem overlap_relOpen : ∃ W : Set ℝ, IsOpen W ∧ overlap A A' = W ∩ A.target :=
  A.image_open (A.open_source.inter A'.open_source) inter_subset_left

/-- **The end lemma.** If `C ⊆ overlap`, `β ∈ A.target` is a limit point of `C` not in the
overlap, and the transition map tends to `L` at `β` along `C`, then `L` is not in the target of
`A'`.  (Geometrically: the point `A.invFun β` of `A` is not in `A'`, so the `A'`-coordinates of
nearby points of the overlap must leave the target of `A'`.) -/
theorem end_lemma {C : Set ℝ} (hC : C ⊆ overlap A A') {β L : ℝ} (hβ : β ∈ A.target)
    (hβS : β ∉ overlap A A') [NeBot (𝓝[C] β)] (hL : Tendsto (trans A A') (𝓝[C] β) (𝓝 L)) :
    L ∉ A'.target := by
  intro hLt
  set y := A.invFun β with hy
  have hyA : y ∈ A.source := A.map_target hβ
  have hyA' : y ∉ A'.source := fun h => hβS ⟨y, ⟨hyA, h⟩, A.right_inv hβ⟩
  have h1 : Tendsto A.invFun (𝓝[C] β) (𝓝 y) :=
    ((A.continuousOn_invFun β hβ).mono (hC.trans (overlap_subset A A'))).tendsto
  have h2 : Tendsto (fun s => A'.invFun (trans A A' s)) (𝓝[C] β) (𝓝 (A'.invFun L)) := by
    refine (A'.continuousOn_invFun L hLt).tendsto.comp ?_
    exact tendsto_nhdsWithin_iff.2 ⟨hL, eventually_nhdsWithin_of_forall fun s hs =>
      trans_mem_target A A' (hC hs)⟩
  have h3 : Tendsto A.invFun (𝓝[C] β) (𝓝 (A'.invFun L)) :=
    h2.congr' (eventually_nhdsWithin_of_forall fun s hs => invFun_eq_of_mem_overlap A A' (hC hs))
  have := tendsto_nhds_unique h1 h3
  exact hyA' (this ▸ A'.map_target hLt)

/-- Consequence of the end lemma for a limit that is an upper bound of the image: it is a
strict upper bound of the whole target of `A'`. -/
theorem lt_of_end_lemma_upper {C : Set ℝ} (hC : C ⊆ overlap A A') (hne : C.Nonempty)
    {β L : ℝ} (hβ : β ∈ A.target) (hβS : β ∉ overlap A A') [NeBot (𝓝[C] β)]
    (hL : Tendsto (trans A A') (𝓝[C] β) (𝓝 L)) (hup : ∀ s ∈ C, trans A A' s ≤ L) :
    ∀ t ∈ A'.target, t < L := by
  intro t ht
  by_contra h; push_neg at h
  obtain ⟨c, hc⟩ := hne
  exact end_lemma A A' hC hβ hβS hL
    (A'.ordConnected_target.out (trans_mem_target A A' (hC hc)) ht ⟨hup c hc, h⟩)

theorem lt_of_end_lemma_lower {C : Set ℝ} (hC : C ⊆ overlap A A') (hne : C.Nonempty)
    {β L : ℝ} (hβ : β ∈ A.target) (hβS : β ∉ overlap A A') [NeBot (𝓝[C] β)]
    (hL : Tendsto (trans A A') (𝓝[C] β) (𝓝 L)) (hlow : ∀ s ∈ C, L ≤ trans A A' s) :
    ∀ t ∈ A'.target, L < t := by
  intro t ht
  by_contra h; push_neg at h
  obtain ⟨c, hc⟩ := hne
  exact end_lemma A A' hC hβ hβS hL
    (A'.ordConnected_target.out ht (trans_mem_target A A' (hC hc)) ⟨h, hlow c hc⟩)

end Transition

/-! ### Two disjoint intervals cannot share an unattained endpoint -/

section TwoIntervals

theorem inter_nonempty_of_sSup_eq {I₁ I₂ : Set ℝ} (h₁ : I₁.OrdConnected) (h₂ : I₂.OrdConnected)
    (hn₁ : I₁.Nonempty) (hn₂ : I₂.Nonempty) (hb₁ : BddAbove I₁) (hb₂ : BddAbove I₂)
    (heq : sSup I₁ = sSup I₂) (hs₁ : sSup I₁ ∉ I₁) (hs₂ : sSup I₂ ∉ I₂) : (I₁ ∩ I₂).Nonempty := by
  obtain ⟨a, ha⟩ := hn₁
  obtain ⟨b, hb⟩ := hn₂
  rcases le_total a b with hab | hab
  · have hbL : b < sSup I₁ := by
      rw [heq]; exact lt_of_le_of_ne (le_csSup hb₂ hb) (fun h => hs₂ (h ▸ hb))
    obtain ⟨a', ha', hba'⟩ := exists_lt_of_lt_csSup ⟨a, ha⟩ hbL
    exact ⟨b, h₁.out ha ha' ⟨hab, hba'.le⟩, hb⟩
  · have haL : a < sSup I₂ := by
      rw [← heq]; exact lt_of_le_of_ne (le_csSup hb₁ ha) (fun h => hs₁ (h ▸ ha))
    obtain ⟨b', hb', hab'⟩ := exists_lt_of_lt_csSup ⟨b, hb⟩ haL
    exact ⟨a, ha, h₂.out hb hb' ⟨hab, hab'.le⟩⟩

theorem inter_nonempty_of_sInf_eq {I₁ I₂ : Set ℝ} (h₁ : I₁.OrdConnected) (h₂ : I₂.OrdConnected)
    (hn₁ : I₁.Nonempty) (hn₂ : I₂.Nonempty) (hb₁ : BddBelow I₁) (hb₂ : BddBelow I₂)
    (heq : sInf I₁ = sInf I₂) (hs₁ : sInf I₁ ∉ I₁) (hs₂ : sInf I₂ ∉ I₂) : (I₁ ∩ I₂).Nonempty := by
  obtain ⟨a, ha⟩ := hn₁
  obtain ⟨b, hb⟩ := hn₂
  rcases le_total a b with hab | hab
  · have haL : sInf I₂ < a := by
      rw [← heq]; exact lt_of_le_of_ne (csInf_le hb₁ ha) (fun h => hs₁ (h ▸ ha))
    obtain ⟨b', hb', hb'a⟩ := exists_lt_of_csInf_lt ⟨b, hb⟩ haL
    exact ⟨a, ha, h₂.out hb' hb ⟨hb'a.le, hab⟩⟩
  · have hbL : sInf I₁ < b := by
      rw [heq]; exact lt_of_le_of_ne (csInf_le hb₂ hb) (fun h => hs₂ (h ▸ hb))
    obtain ⟨a', ha', ha'b⟩ := exists_lt_of_csInf_lt ⟨a, ha⟩ hbL
    exact ⟨b, h₁.out ha' ha ⟨ha'b.le, hab⟩, hb⟩

end TwoIntervals

/-! ### The overlap of an arc from a boundary point with any arc is an interval -/

section Counting

variable [T2Space M] (A A' : Arc M B) {p : M} {c : ℝ}

local notation "S" => overlap A A'
local notation "τ" => trans A A'

theorem image_trans_subset {C : Set ℝ} (hC : C ⊆ S) : τ '' C ⊆ A'.target := by
  rintro _ ⟨s, hs, rfl⟩; exact trans_mem_target A A' (hC hs)

theorem bddAbove_image_trans {C : Set ℝ} (hC : C ⊆ S) : BddAbove (τ '' C) :=
  A'.bddAbove_target.mono (image_trans_subset A A' hC)

theorem bddBelow_image_trans {C : Set ℝ} (hC : C ⊆ S) : BddBelow (τ '' C) :=
  A'.bddBelow_target.mono (image_trans_subset A A' hC)

theorem ordConnected_image_trans {C : Set ℝ} (hC : C ⊆ S) (hCo : C.OrdConnected) :
    (τ '' C).OrdConnected :=
  (hCo.isPreconnected.image _ ((trans_continuousOn A A').mono hC)).ordConnected

/-- Two distinct hulls cannot both send an end to a strict upper bound of `A'.target`. -/
theorem clash_upper {t₁ t₂ : ℝ} (h₁ : t₁ ∈ S) (h₂ : t₂ ∈ S) (hne : hull S t₁ ≠ hull S t₂)
    (hU₁ : ∀ t ∈ A'.target, t < sSup (τ '' hull S t₁))
    (hU₂ : ∀ t ∈ A'.target, t < sSup (τ '' hull S t₂)) : False := by
  have hn₁ : (τ '' hull S t₁).Nonempty := ⟨_, t₁, mem_hull_self h₁, rfl⟩
  have hn₂ : (τ '' hull S t₂).Nonempty := ⟨_, t₂, mem_hull_self h₂, rfl⟩
  have hL : ∀ C : Set ℝ, C ⊆ S → (τ '' C).Nonempty →
      (∀ t ∈ A'.target, t < sSup (τ '' C)) → sSup (τ '' C) = sSup A'.target := by
    intro C hC hne hU
    apply le_antisymm (csSup_le_csSup A'.bddAbove_target hne (image_trans_subset A A' hC))
    exact csSup_le A'.nontrivial_target.nonempty fun t ht => (hU t ht).le
  have hnot : ∀ C : Set ℝ, C ⊆ S → (∀ t ∈ A'.target, t < sSup (τ '' C)) →
      sSup (τ '' C) ∉ τ '' C := fun C hC hU h => lt_irrefl _ (hU _ (image_trans_subset A A' hC h))
  obtain ⟨_, ⟨s₁, hs₁, rfl⟩, s₂, hs₂, heq⟩ := inter_nonempty_of_sSup_eq
    (ordConnected_image_trans A A' (hull_subset S t₁) (hull_ordConnected S t₁))
    (ordConnected_image_trans A A' (hull_subset S t₂) (hull_ordConnected S t₂)) hn₁ hn₂
    (bddAbove_image_trans A A' (hull_subset S t₁)) (bddAbove_image_trans A A' (hull_subset S t₂))
    ((hL _ (hull_subset S t₁) hn₁ hU₁).trans (hL _ (hull_subset S t₂) hn₂ hU₂).symm)
    (hnot _ (hull_subset S t₁) hU₁) (hnot _ (hull_subset S t₂) hU₂)
  have := trans_injOn A A' (hull_subset S t₁ hs₁) (hull_subset S t₂ hs₂) heq.symm
  subst this
  exact hne ((hull_eq_of_mem hs₁).symm.trans (hull_eq_of_mem hs₂))

theorem clash_lower {t₁ t₂ : ℝ} (h₁ : t₁ ∈ S) (h₂ : t₂ ∈ S) (hne : hull S t₁ ≠ hull S t₂)
    (hD₁ : ∀ t ∈ A'.target, sInf (τ '' hull S t₁) < t)
    (hD₂ : ∀ t ∈ A'.target, sInf (τ '' hull S t₂) < t) : False := by
  have hn₁ : (τ '' hull S t₁).Nonempty := ⟨_, t₁, mem_hull_self h₁, rfl⟩
  have hn₂ : (τ '' hull S t₂).Nonempty := ⟨_, t₂, mem_hull_self h₂, rfl⟩
  have hL : ∀ C : Set ℝ, C ⊆ S → (τ '' C).Nonempty →
      (∀ t ∈ A'.target, sInf (τ '' C) < t) → sInf (τ '' C) = sInf A'.target := by
    intro C hC hne hD
    apply le_antisymm
    · exact le_csInf A'.nontrivial_target.nonempty fun t ht => (hD t ht).le
    · exact csInf_le_csInf A'.bddBelow_target hne (image_trans_subset A A' hC)
  have hnot : ∀ C : Set ℝ, C ⊆ S → (∀ t ∈ A'.target, sInf (τ '' C) < t) →
      sInf (τ '' C) ∉ τ '' C := fun C hC hD h => lt_irrefl _ (hD _ (image_trans_subset A A' hC h))
  obtain ⟨_, ⟨s₁, hs₁, rfl⟩, s₂, hs₂, heq⟩ := inter_nonempty_of_sInf_eq
    (ordConnected_image_trans A A' (hull_subset S t₁) (hull_ordConnected S t₁))
    (ordConnected_image_trans A A' (hull_subset S t₂) (hull_ordConnected S t₂)) hn₁ hn₂
    (bddBelow_image_trans A A' (hull_subset S t₁)) (bddBelow_image_trans A A' (hull_subset S t₂))
    ((hL _ (hull_subset S t₁) hn₁ hD₁).trans (hL _ (hull_subset S t₂) hn₂ hD₂).symm)
    (hnot _ (hull_subset S t₁) hD₁) (hnot _ (hull_subset S t₂) hD₂)
  have := trans_injOn A A' (hull_subset S t₁ hs₁) (hull_subset S t₂ hs₂) heq.symm
  subst this
  exact hne ((hull_eq_of_mem hs₁).symm.trans (hull_eq_of_mem hs₂))

theorem not_lower_of_sInf_mem {C : Set ℝ} (hC : C ⊆ S) (hne : C.Nonempty)
    (hmin : sInf A'.target ∈ A'.target) (hD : ∀ t ∈ A'.target, sInf (τ '' C) < t) : False := by
  have h1 := hD _ hmin
  have h2 : sInf A'.target ≤ sInf (τ '' C) :=
    csInf_le_csInf A'.bddBelow_target (hne.image _) (image_trans_subset A A' hC)
  exact lt_irrefl _ (h2.trans_lt h1)

theorem not_upper_of_sSup_mem {C : Set ℝ} (hC : C ⊆ S) (hne : C.Nonempty)
    (hmax : sSup A'.target ∈ A'.target) (hU : ∀ t ∈ A'.target, t < sSup (τ '' C)) : False := by
  have h1 := hU _ hmax
  have h2 : sSup (τ '' C) ≤ sSup A'.target :=
    csSup_le_csSup A'.bddAbove_target (hne.image _) (image_trans_subset A A' hC)
  exact lt_irrefl _ (h1.trans_le h2)

/-- The right end of a hull whose supremum lies in `A.target` but not in the overlap. -/
theorem end_right {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hb : BddAbove (hull S t₀))
    (hβ : sSup (hull S t₀) ∈ A.target) (hβS : sSup (hull S t₀) ∉ S) :
    (StrictMonoOn τ (hull S t₀) → ∀ t ∈ A'.target, t < sSup (τ '' hull S t₀)) ∧
    (StrictAntiOn τ (hull S t₀) → ∀ t ∈ A'.target, sInf (τ '' hull S t₀) < t) := by
  have hCS : hull S t₀ ⊆ S := hull_subset S t₀
  have hne : (hull S t₀).Nonempty := ⟨t₀, mem_hull_self ht₀⟩
  have hβC : sSup (hull S t₀) ∉ hull S t₀ := fun h => hβS (hCS h)
  have hCI : hull S t₀ ⊆ Iio (sSup (hull S t₀)) := fun s hs =>
    lt_of_le_of_ne (le_csSup hb hs) (fun h => hβC (h ▸ hs))
  haveI : NeBot (𝓝[hull S t₀] sSup (hull S t₀)) :=
    mem_closure_iff_nhdsWithin_neBot.1 (csSup_mem_closure hne hb)
  constructor
  · intro hm
    exact lt_of_end_lemma_upper A A' hCS hne hβ hβS
      (tendsto_sSup_of_monotoneOn hm.monotoneOn hne rfl hCI (bddAbove_image_trans A A' hCS))
      (fun s hs => le_csSup (bddAbove_image_trans A A' hCS) ⟨s, hs, rfl⟩)
  · intro ha
    exact lt_of_end_lemma_lower A A' hCS hne hβ hβS
      (tendsto_sInf_of_antitoneOn ha.antitoneOn hne rfl hCI (bddBelow_image_trans A A' hCS))
      (fun s hs => csInf_le (bddBelow_image_trans A A' hCS) ⟨s, hs, rfl⟩)

theorem end_left {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hb : BddBelow (hull S t₀))
    (hα : sInf (hull S t₀) ∈ A.target) (hαS : sInf (hull S t₀) ∉ S) :
    (StrictMonoOn τ (hull S t₀) → ∀ t ∈ A'.target, sInf (τ '' hull S t₀) < t) ∧
    (StrictAntiOn τ (hull S t₀) → ∀ t ∈ A'.target, t < sSup (τ '' hull S t₀)) := by
  have hCS : hull S t₀ ⊆ S := hull_subset S t₀
  have hne : (hull S t₀).Nonempty := ⟨t₀, mem_hull_self ht₀⟩
  have hαC : sInf (hull S t₀) ∉ hull S t₀ := fun h => hαS (hCS h)
  have hCI : hull S t₀ ⊆ Ioi (sInf (hull S t₀)) := fun s hs =>
    lt_of_le_of_ne (csInf_le hb hs) (fun h => hαC (h ▸ hs))
  haveI : NeBot (𝓝[hull S t₀] sInf (hull S t₀)) :=
    mem_closure_iff_nhdsWithin_neBot.1 (csInf_mem_closure hne hb)
  constructor
  · intro hm
    exact lt_of_end_lemma_lower A A' hCS hne hα hαS
      (tendsto_sInf_of_monotoneOn hm.monotoneOn hne rfl hCI (bddBelow_image_trans A A' hCS))
      (fun s hs => csInf_le (bddBelow_image_trans A A' hCS) ⟨s, hs, rfl⟩)
  · intro ha
    exact lt_of_end_lemma_upper A A' hCS hne hα hαS
      (tendsto_sSup_of_antitoneOn ha.antitoneOn hne rfl hCI (bddAbove_image_trans A A' hCS))
      (fun s hs => le_csSup (bddAbove_image_trans A A' hCS) ⟨s, hs, rfl⟩)

variable (hc : 0 < c) (hpA : p ∈ A.source) (hp0 : A.toFun p = 0) (hAt : A.target = Ico 0 c)

include hpA hp0 hAt in
theorem p_mem_boundary : p ∈ B := by
  rw [A.bdry p hpA, hp0, hAt, interior_Ico]; simp

include hpA hp0 in
theorem p_mem_source'_of_zero_mem (h : (0 : ℝ) ∈ S) : p ∈ A'.source := by
  obtain ⟨x, hx, hx0⟩ := h
  have : x = p := by
    rw [← A.left_inv hx.1, ← A.left_inv hpA, hx0, hp0]
  rw [← this]; exact hx.2

include hpA hp0 hAt in
theorem trans_zero_eq_sInf_or_sSup (h : (0 : ℝ) ∈ S) :
    τ 0 = sInf A'.target ∨ τ 0 = sSup A'.target := by
  have hp' := p_mem_source'_of_zero_mem A A' hpA hp0 h
  have hτ : τ 0 = A'.toFun p := by
    show A'.toFun (A.invFun 0) = A'.toFun p
    rw [← hp0, A.left_inv hpA]
  rw [hτ]
  exact A'.eq_sInf_or_eq_sSup_of_notMem_interior (A'.map_source hp')
    ((A'.bdry p hp').1 (p_mem_boundary A hpA hp0 hAt))

theorem exists_gt_mem_hull {t₀ t : ℝ} (ht : t ∈ hull S t₀) (hlt : t < sSup A.target) :
    ∃ v ∈ hull S t₀, t < v := by
  obtain ⟨W, hW, hSW⟩ := overlap_relOpen A A'
  obtain ⟨ε, hε, hball⟩ := hull_relOpen hW hSW A.ordConnected_target ht
  have htT : t ∈ A.target := overlap_subset A A' (hull_subset S t₀ ht)
  obtain ⟨w, hw, htw⟩ := exists_lt_of_lt_csSup A.nontrivial_target.nonempty hlt
  have hvt : t < min w (t + ε / 2) := lt_min htw (by linarith)
  have hvT : min w (t + ε / 2) ∈ A.target :=
    A.ordConnected_target.out htT hw ⟨hvt.le, min_le_left _ _⟩
  refine ⟨min w (t + ε / 2), hball _ hvT ?_, hvt⟩
  rw [abs_lt]; constructor
  · linarith
  · linarith [min_le_right w (t + ε / 2)]

theorem exists_lt_mem_hull {t₀ t : ℝ} (ht : t ∈ hull S t₀) (hlt : sInf A.target < t) :
    ∃ v ∈ hull S t₀, v < t := by
  obtain ⟨W, hW, hSW⟩ := overlap_relOpen A A'
  obtain ⟨ε, hε, hball⟩ := hull_relOpen hW hSW A.ordConnected_target ht
  have htT : t ∈ A.target := overlap_subset A A' (hull_subset S t₀ ht)
  obtain ⟨w, hw, hwt⟩ := exists_lt_of_csInf_lt A.nontrivial_target.nonempty hlt
  have hvt : max w (t - ε / 2) < t := max_lt hwt (by linarith)
  have hvT : max w (t - ε / 2) ∈ A.target :=
    A.ordConnected_target.out hw htT ⟨le_max_left _ _, hvt.le⟩
  refine ⟨max w (t - ε / 2), hball _ hvT ?_, hvt⟩
  rw [abs_lt]; constructor
  · linarith [le_max_right w (t - ε / 2)]
  · linarith

include hc hAt in
theorem sSup_target_eq : sSup A.target = c := by rw [hAt, csSup_Ico hc]

include hc hAt in
theorem sInf_target_eq : sInf A.target = 0 := by rw [hAt, csInf_Ico hc]

include hc hAt in
theorem sSup_hull_notMem {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hlt : sSup (hull S t₀) < c) :
    sSup (hull S t₀) ∉ S := by
  intro hmem
  have hb : BddAbove (hull S t₀) :=
    A.bddAbove_target.mono ((hull_subset S t₀).trans (overlap_subset A A'))
  have hC := sSup_mem_hull ht₀ hb hmem
  obtain ⟨v, hv, hlt'⟩ := exists_gt_mem_hull A A' hC (by rwa [sSup_target_eq A hc hAt])
  exact lt_irrefl _ (hlt'.trans_le (le_csSup hb hv))

include hc hAt in
theorem sInf_hull_notMem {t₀ : ℝ} (ht₀ : t₀ ∈ S) (hlt : 0 < sInf (hull S t₀)) :
    sInf (hull S t₀) ∉ S := by
  intro hmem
  have hb : BddBelow (hull S t₀) :=
    A.bddBelow_target.mono ((hull_subset S t₀).trans (overlap_subset A A'))
  have hC := sInf_mem_hull ht₀ hb hmem
  obtain ⟨v, hv, hlt'⟩ := exists_lt_mem_hull A A' hC (by rwa [sInf_target_eq A hc hAt])
  exact lt_irrefl _ ((csInf_le hb hv).trans_lt hlt')

include hc hAt in
theorem hull_nontrivial {t₀ : ℝ} (ht₀ : t₀ ∈ S) : (hull S t₀).Nontrivial := by
  have hm := mem_hull_self ht₀
  have ht₀T : t₀ ∈ A.target := overlap_subset A A' ht₀
  rw [hAt] at ht₀T
  obtain ⟨v, hv, hlt⟩ := exists_gt_mem_hull A A' hm
    (by rw [sSup_target_eq A hc hAt]; exact ht₀T.2)
  exact ⟨v, hv, t₀, hm, hlt.ne'⟩

include hc hpA hp0 hAt in
/-- **The overlap is an interval.** -/
theorem overlap_ordConnected : (overlap A A').OrdConnected := by
  by_contra hnot
  rw [ordConnected_iff] at hnot
  push_neg at hnot
  obtain ⟨t₁, h₁, t₂, h₂, h₁₂, hnsub⟩ := hnot
  rw [not_subset] at hnsub
  obtain ⟨u, hu, huS⟩ := hnsub
  have hu₁ : t₁ < u := lt_of_le_of_ne hu.1 (fun h => huS (h ▸ h₁))
  have hu₂ : u < t₂ := lt_of_le_of_ne hu.2 (fun h => huS (h ▸ h₂))
  have hbdd : ∀ t, BddAbove (hull S t) ∧ BddBelow (hull S t) := fun t =>
    ⟨A.bddAbove_target.mono ((hull_subset S t).trans (overlap_subset A A')),
     A.bddBelow_target.mono ((hull_subset S t).trans (overlap_subset A A'))⟩
  have hT : ∀ t ∈ S, t ∈ Ico 0 c := fun t ht => hAt ▸ overlap_subset A A' ht
  have hC₁u : ∀ t ∈ hull S t₁, t < u := fun t ht => by
    by_contra h; push_neg at h
    exact huS (ht (mem_uIcc.2 (Or.inr ⟨hu₁.le, h⟩)))
  have hC₂u : ∀ t ∈ hull S t₂, u < t := fun t ht => by
    by_contra h; push_neg at h
    exact huS (ht (mem_uIcc.2 (Or.inl ⟨h, hu₂.le⟩)))
  have hne : hull S t₁ ≠ hull S t₂ := fun h =>
    lt_irrefl u ((hC₂u t₁ (h ▸ mem_hull_self h₁)).trans (hC₁u t₁ (mem_hull_self h₁)))
  -- the right end of `hull S t₁`
  have hβ₁ : sSup (hull S t₁) ∈ A.target := by
    rw [hAt]; constructor
    · exact (hT t₁ h₁).1.trans (le_csSup (hbdd t₁).1 (mem_hull_self h₁))
    · exact (csSup_le ⟨t₁, mem_hull_self h₁⟩ fun t ht => (hC₁u t ht).le).trans_lt
        (hu₂.trans (hT t₂ h₂).2)
  have hβ₁S : sSup (hull S t₁) ∉ S :=
    sSup_hull_notMem A A' hc hAt h₁ (by rw [hAt] at hβ₁; exact hβ₁.2)
  have hR₁ := end_right A A' h₁ (hbdd t₁).1 hβ₁ hβ₁S
  -- the left end of `hull S t₂`
  have hα₂pos : 0 < sInf (hull S t₂) :=
    (hT t₁ h₁).1.trans_lt (hu₁.trans_le (le_csInf ⟨t₂, mem_hull_self h₂⟩
      fun t ht => (hC₂u t ht).le))
  have hα₂ : sInf (hull S t₂) ∈ A.target := by
    rw [hAt]
    exact ⟨hα₂pos.le, (csInf_le (hbdd t₂).2 (mem_hull_self h₂)).trans_lt (hT t₂ h₂).2⟩
  have hα₂S : sInf (hull S t₂) ∉ S := sInf_hull_notMem A A' hc hAt h₂ hα₂pos
  have hL₂ := end_left A A' h₂ (hbdd t₂).2 hα₂ hα₂S
  have hmono := fun t (ht : t ∈ S) => strictMonoOn_or_strictAntiOn_of_ordConnected
    (hull_ordConnected S t) (hull_nontrivial A A' hc hAt ht)
    ((trans_continuousOn A A').mono (hull_subset S t)) ((trans_injOn A A').mono (hull_subset S t))
  -- the left end of `hull S t₁`: not in the overlap, or the corner `0`
  have hα₁nn : 0 ≤ sInf (hull S t₁) :=
    le_csInf ⟨t₁, mem_hull_self h₁⟩ fun t ht => (hT t (hull_subset S t₁ ht)).1
  have hα₁ : sInf (hull S t₁) ∈ A.target := by
    rw [hAt]
    exact ⟨hα₁nn, (csInf_le (hbdd t₁).2 (mem_hull_self h₁)).trans_lt (hT t₁ h₁).2⟩
  have hleft₁ : sInf (hull S t₁) ∉ S ∨ (0 : ℝ) ∈ S := by
    by_cases h : sInf (hull S t₁) ∈ S
    · right
      by_contra h0
      have hpos : 0 < sInf (hull S t₁) := lt_of_le_of_ne hα₁nn (fun h' => h0 (h' ▸ h))
      exact sInf_hull_notMem A A' hc hAt h₁ hpos h
    · exact Or.inl h
  rcases hmono t₁ h₁ with hm₁ | ha₁
  · have hU₁ := hR₁.1 hm₁
    rcases hleft₁ with hα₁S | h0
    · have hD₁ := (end_left A A' h₁ (hbdd t₁).2 hα₁ hα₁S).1 hm₁
      rcases hmono t₂ h₂ with hm₂ | ha₂
      · exact clash_lower A A' h₁ h₂ hne hD₁ (hL₂.1 hm₂)
      · exact clash_upper A A' h₁ h₂ hne hU₁ (hL₂.2 ha₂)
    · rcases trans_zero_eq_sInf_or_sSup A A' hpA hp0 hAt h0 with hmin | hmax
      · have hmin' : sInf A'.target ∈ A'.target := by
          rw [← hmin]; exact trans_mem_target A A' h0
        rcases hmono t₂ h₂ with hm₂ | ha₂
        · exact not_lower_of_sInf_mem A A' (hull_subset S t₂) ⟨t₂, mem_hull_self h₂⟩ hmin'
            (hL₂.1 hm₂)
        · exact clash_upper A A' h₁ h₂ hne hU₁ (hL₂.2 ha₂)
      · have hmax' : sSup A'.target ∈ A'.target := by
          rw [← hmax]; exact trans_mem_target A A' h0
        exact not_upper_of_sSup_mem A A' (hull_subset S t₁) ⟨t₁, mem_hull_self h₁⟩ hmax' hU₁
  · have hD₁ := hR₁.2 ha₁
    rcases hleft₁ with hα₁S | h0
    · have hU₁ := (end_left A A' h₁ (hbdd t₁).2 hα₁ hα₁S).2 ha₁
      rcases hmono t₂ h₂ with hm₂ | ha₂
      · exact clash_lower A A' h₁ h₂ hne hD₁ (hL₂.1 hm₂)
      · exact clash_upper A A' h₁ h₂ hne hU₁ (hL₂.2 ha₂)
    · rcases trans_zero_eq_sInf_or_sSup A A' hpA hp0 hAt h0 with hmin | hmax
      · have hmin' : sInf A'.target ∈ A'.target := by
          rw [← hmin]; exact trans_mem_target A A' h0
        exact not_lower_of_sInf_mem A A' (hull_subset S t₁) ⟨t₁, mem_hull_self h₁⟩ hmin' hD₁
      · have hmax' : sSup A'.target ∈ A'.target := by
          rw [← hmax]; exact trans_mem_target A A' h0
        rcases hmono t₂ h₂ with hm₂ | ha₂
        · exact clash_lower A A' h₁ h₂ hne hD₁ (hL₂.1 hm₂)
        · exact not_upper_of_sSup_mem A A' (hull_subset S t₂) ⟨t₂, mem_hull_self h₂⟩ hmax'
            (hL₂.2 ha₂)

end Counting

/-! ### Extending an arc from a boundary point across another arc -/

section Extend

variable [T2Space M]

theorem interior_eq_Ioo_of_ordConnected {s : Set ℝ} (h : s.OrdConnected) (hn : s.Nonempty)
    (ha : BddAbove s) (hb : BddBelow s) : interior s = Ioo (sInf s) (sSup s) := by
  apply Subset.antisymm
  · calc interior s ⊆ interior (Icc (sInf s) (sSup s)) :=
          interior_mono fun t ht => ⟨csInf_le hb ht, le_csSup ha ht⟩
      _ = Ioo _ _ := interior_Icc
  · refine interior_maximal (fun t ht => ?_) isOpen_Ioo
    obtain ⟨a, ha', hat⟩ := exists_lt_of_csInf_lt hn ht.1
    obtain ⟨b, hb', htb⟩ := exists_lt_of_lt_csSup hn ht.2
    exact h.out ha' hb' ⟨hat.le, htb.le⟩

theorem overlap_neg_right (A A' : Arc M B) : overlap A A'.neg = overlap A A' := rfl

theorem overlap_neg_left (A A' : Arc M B) : overlap A'.neg A = -overlap A' A := by
  ext t
  simp only [overlap, Arc.neg_toFun, Arc.neg_source, Set.mem_neg, mem_image]
  constructor
  · rintro ⟨y, hy, h⟩; exact ⟨y, hy, by linarith⟩
  · rintro ⟨y, hy, h⟩; exact ⟨y, hy, by linarith⟩

variable (A A' : Arc M B) {p x : M} {c : ℝ}

/-- The extension, in the normalized situation where the `A'`-coordinate of `x` is the supremum
of the overlap seen from `A'`. -/
theorem exists_extension_aux (hc : 0 < c) (hpA : p ∈ A.source) (hp0 : A.toFun p = 0)
    (hAt : A.target = Ico 0 c) (hx' : x ∈ A'.source) (hxA : x ∉ A.source)
    (hlt : ∀ t ∈ overlap A' A, t < A'.toFun x)
    (happ : ∀ ε > 0, ∃ t ∈ overlap A' A, A'.toFun x - ε < t) :
    ∃ Ã : Arc M B, p ∈ Ã.source ∧ Ã.toFun p = 0 ∧ (0 : ℝ) ∈ Ã.target ∧ Ã.target ⊆ Ici 0 ∧
      A.source ⊆ Ã.source ∧ A'.source ⊆ Ã.source := by
  classical
  -- notation
  set S := overlap A A' with hS
  set S' := overlap A' A with hS'
  set d := A'.toFun x with hd
  set τ := trans A A' with hτ
  set σ := trans A' A with hσ
  have hSo : S.OrdConnected := overlap_ordConnected A A' hc hpA hp0 hAt
  have hSc : S ⊆ Ico 0 c := fun t ht => hAt ▸ overlap_subset A A' ht
  have hS'T : S' ⊆ A'.target := overlap_subset A' A
  have hdT : d ∈ A'.target := A'.map_source hx'
  have hdS' : d ∉ S' := fun h => lt_irrefl _ (hlt d h)
  have hστ : ∀ s ∈ S, σ (τ s) = s := fun s hs => by
    have h1 := invFun_eq_of_mem_overlap A A' hs
    show A.toFun (A'.invFun (trans A A' s)) = s
    rw [h1, A.right_inv (overlap_subset A A' hs)]
  have hτσ : ∀ t ∈ S', τ (σ t) = t := fun t ht => by
    have h1 := invFun_eq_of_mem_overlap A' A ht
    show A'.toFun (A.invFun (trans A' A t)) = t
    rw [h1, A'.right_inv (overlap_subset A' A ht)]
  have hτS : τ '' S = S' := by
    ext t; constructor
    · rintro ⟨s, hs, rfl⟩; exact trans_mem_overlap A A' hs
    · intro ht; exact ⟨σ t, trans_mem_overlap A' A ht, hτσ t ht⟩
  have hσS' : σ '' S' = S := by
    ext s; constructor
    · rintro ⟨t, ht, rfl⟩; exact trans_mem_overlap A' A ht
    · intro hs; exact ⟨τ s, trans_mem_overlap A A' hs, hστ s hs⟩
  obtain ⟨t₁, ht₁, -⟩ := happ 1 one_pos
  have hS'ne : S'.Nonempty := ⟨t₁, ht₁⟩
  have hSne : S.Nonempty := ⟨σ t₁, trans_mem_overlap A' A ht₁⟩
  have hhull : ∀ t ∈ S, hull S t = S := fun t ht => by
    ext u; exact ⟨fun hu => hull_subset S t hu, fun hu => hSo.uIcc_subset hu ht⟩
  have hSn : S.Nontrivial := by
    obtain ⟨s, hs⟩ := hSne
    have := hull_nontrivial A A' hc hAt hs
    rwa [hhull s hs] at this
  have hS'o : S'.OrdConnected := by
    rw [← hτS]; exact ordConnected_image_trans A A' subset_rfl hSo
  have hhull' : ∀ t ∈ S', hull S' t = S' := fun t ht => by
    ext u; exact ⟨fun hu => hull_subset S' t hu, fun hu => hS'o.uIcc_subset hu ht⟩
  have hS'n : S'.Nontrivial := by
    obtain ⟨a, ha, b, hb, hab⟩ := hSn
    exact ⟨τ a, trans_mem_overlap A A' ha, τ b, trans_mem_overlap A A' hb,
      fun h => hab (trans_injOn A A' ha hb h)⟩
  have hsupS' : sSup S' = d := by
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hS'ne (fun t ht => (hlt t ht).le)
      fun w hw => ?_
    obtain ⟨t, ht, hwt⟩ := happ (d - w) (by linarith)
    exact ⟨t, ht, by linarith⟩
  have hS'lt : S' ⊆ Iio d := fun t ht => hlt t ht
  have hS'b : BddAbove S' := A'.bddAbove_target.mono hS'T
  have hSb : BddAbove S := A.bddAbove_target.mono (overlap_subset A A')
  have hSbb : BddBelow S := A.bddBelow_target.mono (overlap_subset A A')
  have hS'bb : BddBelow S' := A'.bddBelow_target.mono hS'T
  have hinfS : 0 ≤ sInf S := le_csInf hSne fun t ht => (hSc ht).1
  -- `σ` is increasing on `S'`, and `sSup S = c`
  have hσmono : StrictMonoOn σ S' := by
    rcases strictMonoOn_or_strictAntiOn_of_ordConnected hS'o hS'n
      (trans_continuousOn A' A) (trans_injOn A' A) with h | h
    · exact h
    · exfalso
      have hR := end_right A' A ht₁ (by rw [hhull' t₁ ht₁]; exact hS'b)
        (by rw [hhull' t₁ ht₁, hsupS']; exact hdT) (by rw [hhull' t₁ ht₁, hsupS']; exact hdS')
      rw [hhull' t₁ ht₁, hσS'] at hR
      have := hR.2 h 0 (by rw [hAt]; exact ⟨le_rfl, hc⟩)
      exact lt_irrefl _ (hinfS.trans_lt this)
  have hsupS : sSup S = c := by
    have hR := end_right A' A ht₁ (by rw [hhull' t₁ ht₁]; exact hS'b)
      (by rw [hhull' t₁ ht₁, hsupS']; exact hdT) (by rw [hhull' t₁ ht₁, hsupS']; exact hdS')
    rw [hhull' t₁ ht₁, hσS'] at hR
    have h1 := hR.1 hσmono
    apply le_antisymm (csSup_le hSne fun t ht => (hSc ht).2.le)
    refine le_of_forall_lt fun t htc => ?_
    rcases lt_or_ge t 0 with h | h
    · exact h.trans_le (le_csSup_of_le hSb hSne.some_mem (hSc hSne.some_mem).1)
    · exact h1 t (by rw [hAt]; exact ⟨h, htc⟩)
  have hτmono : StrictMonoOn τ S := by
    intro s₁ hs₁ s₂ hs₂ hlt'
    by_contra h; push_neg at h
    have := hσmono.monotoneOn (trans_mem_overlap A A' hs₂) (trans_mem_overlap A A' hs₁) h
    rw [hστ s₁ hs₁, hστ s₂ hs₂] at this
    exact absurd hlt' (not_lt.2 this)
  have hSlt : S ⊆ Iio c := fun t ht => (hSc ht).2
  have hinfSlt : sInf S < c := (csInf_le hSbb hSne.some_mem).trans_lt (hSc hSne.some_mem).2
  -- everything in `A'.target` below `d` is in the overlap
  have hbelow : ∀ t ∈ A'.target, t < d → t ∈ S' := by
    intro t ht htd
    by_cases hinf : sInf S ∈ S
    · have h0 : sInf S = 0 := by
        by_contra hne
        have hpos : 0 < sInf S := lt_of_le_of_ne hinfS (Ne.symm hne)
        have hh := sInf_hull_notMem A A' hc hAt hinf (by rwa [hhull _ hinf])
        rw [hhull _ hinf] at hh
        exact hh hinf
      rw [h0] at hinf
      have hτ0 : τ 0 ∈ S' := trans_mem_overlap A A' hinf
      have hmin : τ 0 = sInf A'.target := by
        rcases trans_zero_eq_sInf_or_sSup A A' hpA hp0 hAt hinf with h | h
        · rw [← hτ] at h; exact h
        · exfalso
          rw [← hτ] at h
          obtain ⟨a, ha, b, hb, hab⟩ := hSn
          have hpos : ∃ s ∈ S, 0 < s := by
            rcases eq_or_ne a 0 with rfl | ha0
            · exact ⟨b, hb, lt_of_le_of_ne (hSc hb).1 hab⟩
            · exact ⟨a, ha, lt_of_le_of_ne (hSc ha).1 (Ne.symm ha0)⟩
          obtain ⟨s, hs, hs0⟩ := hpos
          have h1 : τ 0 < τ s := hτmono hinf hs hs0
          have h2 : τ s < d := hlt _ (trans_mem_overlap A A' hs)
          have h3 : d ≤ sSup A'.target := le_csSup A'.bddAbove_target hdT
          rw [h] at h1; linarith
      have h1 : τ 0 ≤ t := by rw [hmin]; exact csInf_le A'.bddBelow_target ht
      obtain ⟨b, hb, htb⟩ := exists_lt_of_lt_csSup hS'ne (by rw [hsupS']; exact htd)
      exact hS'o.out hτ0 hb ⟨h1, htb.le⟩
    · have hL := end_left A A' hSne.some_mem (by rw [hhull _ hSne.some_mem]; exact hSbb)
        (by rw [hhull _ hSne.some_mem, hAt]; exact ⟨hinfS, hinfSlt⟩)
        (by rw [hhull _ hSne.some_mem]; exact hinf)
      rw [hhull _ hSne.some_mem, hτS] at hL
      have h1 := hL.1 hτmono t ht
      obtain ⟨a, ha, hat⟩ := exists_lt_of_csInf_lt hS'ne h1
      obtain ⟨b, hb, htb⟩ := exists_lt_of_lt_csSup hS'ne (by rw [hsupS']; exact htd)
      exact hS'o.out ha hb ⟨hat.le, htb.le⟩
  have hF2 : ∀ y ∈ A.source, y ∈ A'.source → A'.toFun y < d := fun y hy hy' =>
    hlt _ ⟨y, ⟨hy', hy⟩, rfl⟩
  have hF1 : ∀ y ∈ A'.source, y ∉ A.source → d ≤ A'.toFun y := by
    intro y hy hyA
    by_contra h; push_neg at h
    obtain ⟨z, hz, hzy⟩ := hbelow _ (A'.map_source hy) h
    exact hyA (A'.injOn hz.1 hy hzy ▸ hz.2)
  have hF3 : ∀ t ∈ A'.target, d ≤ t → A'.invFun t ∉ A.source := by
    intro t ht hdt hmem
    have : t ∈ S' := ⟨A'.invFun t, ⟨A'.map_target ht, hmem⟩, A'.right_inv ht⟩
    exact lt_irrefl _ ((hlt t this).trans_le hdt)
  -- the limits at the seam
  have hL1 : Tendsto σ (𝓝[S'] d) (𝓝 c) := by
    have := tendsto_sSup_of_monotoneOn hσmono.monotoneOn hS'ne hsupS' hS'lt
      (by rw [hσS']; exact hSb)
    rwa [hσS', hsupS] at this
  have hL2 : Tendsto τ (𝓝[S] c) (𝓝 d) := by
    have := tendsto_sSup_of_monotoneOn hτmono.monotoneOn hSne hsupS hSlt
      (by rw [hτS]; exact hS'b)
    rwa [hτS, hsupS'] at this
  -- the new arc
  set F : M → ℝ := fun y => if y ∈ A.source then A.toFun y else c + (A'.toFun y - d) with hF
  set G : ℝ → M := fun t => if t < c then A.invFun t else A'.invFun (d + (t - c)) with hG
  set T : Set ℝ := {t | 0 ≤ t ∧ (t < c ∨ d + (t - c) ∈ A'.target)} with hT
  set c'' : ℝ := c + (sSup A'.target - d) with hc''
  have hcc'' : c ≤ c'' := by
    have := le_csSup A'.bddAbove_target hdT; rw [hc'']; linarith
  have hF_A : ∀ y ∈ A.source, F y = A.toFun y := fun y hy => by simp [hF, hy]
  have hF_A' : ∀ y, y ∉ A.source → F y = c + (A'.toFun y - d) := fun y hy => by simp [hF, hy]
  have hG_lt : ∀ t, t < c → G t = A.invFun t := fun t ht => by simp [hG, ht]
  have hG_ge : ∀ t, c ≤ t → G t = A'.invFun (d + (t - c)) := fun t ht => by
    simp [hG, not_lt.2 ht]
  have hTlt : ∀ t, 0 ≤ t → t < c → t ∈ T := fun t h0 hc' => ⟨h0, Or.inl hc'⟩
  have hTge : ∀ t ∈ T, c ≤ t → d + (t - c) ∈ A'.target := fun t ht hct => by
    rcases ht.2 with h | h
    · exact absurd h (not_lt.2 hct)
    · exact h
  have hTof : ∀ t, c ≤ t → d + (t - c) ∈ A'.target → t ∈ T := fun t hct h =>
    ⟨hc.le.trans hct, Or.inr h⟩
  have hIoo : Ioo 0 c'' ⊆ T := by
    intro t ht
    rcases lt_or_ge t c with h | h
    · exact hTlt t ht.1.le h
    · refine hTof t h ?_
      rcases eq_or_lt_of_le h with h' | h'
      · rw [← h']; simpa using hdT
      · have h1 : d < d + (t - c) := by linarith
        have h2 : d + (t - c) < sSup A'.target := by rw [hc''] at ht; linarith [ht.2]
        obtain ⟨b, hb, hb'⟩ := exists_lt_of_lt_csSup A'.nontrivial_target.nonempty h2
        exact A'.ordConnected_target.out hdT hb ⟨h1.le, hb'.le⟩
  have hIcc : T ⊆ Icc 0 c'' := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    rcases ht.2 with h | h
    · exact h.le.trans hcc''
    · have := le_csSup A'.bddAbove_target h; rw [hc'']; linarith
  have hTo : T.OrdConnected := by
    refine ⟨fun a ha b hb t ht => ⟨ha.1.trans ht.1, ?_⟩⟩
    rcases lt_or_ge t c with h | h
    · exact Or.inl h
    · right
      have hbc : c ≤ b := h.trans ht.2
      have hb' := hTge b hb hbc
      exact A'.ordConnected_target.out hdT hb' ⟨by linarith, by linarith [ht.2]⟩
  have hTn : T.Nontrivial := ⟨0, hTlt 0 le_rfl hc, c / 2, hTlt _ (by positivity) (by linarith),
    by linarith⟩
  have hint : interior T = Ioo 0 c'' := by
    apply Subset.antisymm
    · calc interior T ⊆ interior (Icc 0 c'') := interior_mono hIcc
        _ = Ioo 0 c'' := interior_Icc
    · exact interior_maximal hIoo isOpen_Ioo
  -- continuity of `F`
  set Gf : ℝ → ℝ := fun t => if t < d then σ t else c + (t - d) with hGf_def
  have hFG : ∀ y ∈ A'.source, F y = Gf (A'.toFun y) := by
    intro y hy
    by_cases hyA : y ∈ A.source
    · rw [hF_A y hyA]
      have := hF2 y hyA hy
      simp only [hGf_def, if_pos this]
      show A.toFun y = A.toFun (A'.invFun (A'.toFun y))
      rw [A'.left_inv hy]
    · rw [hF_A' y hyA]
      simp only [hGf_def, if_neg (not_lt.2 (hF1 y hy hyA))]
  have hGf : ContinuousOn Gf A'.target := by
    intro t ht
    rcases lt_trichotomy t d with htd | rfl | htd
    · have hS'mem : S' ∈ 𝓝[A'.target] t :=
        mem_nhdsWithin.2 ⟨Iio d, isOpen_Iio, htd, fun u hu => hbelow u hu.2 (mem_Iio.1 hu.1)⟩
      have hσc : ContinuousWithinAt σ A'.target t :=
        ((trans_continuousOn A' A) t (hbelow t ht htd)).mono_of_mem_nhdsWithin hS'mem
      refine hσc.congr_of_eventuallyEq ?_ (by simp [hGf_def, htd, hσ])
      exact eventually_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htd))
        fun u hu => by simp [hGf_def, mem_Iio.1 hu, hσ]
    · have hsplit : A'.target = (A'.target ∩ Iio d) ∪ (A'.target ∩ Ici d) := by
        rw [← inter_union_distrib_left, Iio_union_Ici, inter_univ]
      rw [hsplit]
      refine ContinuousWithinAt.union ?_ ?_
      · show Tendsto Gf (𝓝[A'.target ∩ Iio d] d) (𝓝 (Gf d))
        have hGd : Gf d = c := by simp [hGf_def]
        rw [hGd]
        refine (hL1.mono_left (nhdsWithin_mono d fun u hu => hbelow u hu.1 (mem_Iio.1 hu.2))).congr' ?_
        exact eventually_nhdsWithin_of_forall fun u hu => by simp [hGf_def, mem_Iio.1 hu.2, hσ]
      · have hcont : ContinuousWithinAt (fun t : ℝ => c + (t - d)) (A'.target ∩ Ici d) d :=
          (by fun_prop : Continuous fun t : ℝ => c + (t - d)).continuousWithinAt
        refine hcont.congr (fun u hu => ?_) (by simp [hGf_def])
        simp [hGf_def, not_lt.2 (mem_Ici.1 hu.2)]
    · have hcont : ContinuousWithinAt (fun t : ℝ => c + (t - d)) A'.target t :=
        (by fun_prop : Continuous fun t : ℝ => c + (t - d)).continuousWithinAt
      refine hcont.congr_of_eventuallyEq ?_ (by simp [hGf_def, not_lt.2 htd.le])
      exact eventually_of_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds htd))
        fun u hu => by simp [hGf_def, not_lt.2 (le_of_lt (mem_Ioi.1 hu))]
  have hFcont : ContinuousOn F (A.source ∪ A'.source) := by
    refine ContinuousOn.union_of_isOpen ?_ ?_ A.open_source A'.open_source
    · exact A.continuousOn_toFun.congr fun y hy => hF_A y hy
    · exact (hGf.comp A'.continuousOn_toFun fun y hy => A'.map_source hy).congr
        fun y hy => hFG y hy
  -- continuity of `G`
  have hGge : ∀ t ∈ T ∩ Ici c, ContinuousWithinAt G (T ∩ Ici c) t := by
    intro t ht
    have hmaps : MapsTo (fun u : ℝ => d + (u - c)) (T ∩ Ici c) A'.target :=
      fun u hu => hTge u hu.1 (mem_Ici.1 hu.2)
    have hcont : ContinuousWithinAt (fun u : ℝ => d + (u - c)) (T ∩ Ici c) t :=
      (by fun_prop : Continuous fun u : ℝ => d + (u - c)).continuousWithinAt
    have hg : ContinuousWithinAt A'.invFun A'.target (d + (t - c)) :=
      A'.continuousOn_invFun _ (hmaps ht)
    have := ContinuousWithinAt.comp (g := A'.invFun) (f := fun u : ℝ => d + (u - c)) hg hcont hmaps
    exact this.congr (fun u hu => hG_ge u (mem_Ici.1 hu.2)) (hG_ge t (mem_Ici.1 ht.2))
  have hGcont : ContinuousOn G T := by
    intro t ht
    rcases lt_trichotomy t c with htc | htc | htc
    · have hmem : A.target ∈ 𝓝[T] t :=
        mem_nhdsWithin.2 ⟨Iio c, isOpen_Iio, htc, fun u hu => by
          rw [hAt]; exact ⟨hu.2.1, mem_Iio.1 hu.1⟩⟩
      have hA : ContinuousWithinAt A.invFun T t :=
        (A.continuousOn_invFun t (by rw [hAt]; exact ⟨ht.1, htc⟩)).mono_of_mem_nhdsWithin hmem
      refine hA.congr_of_eventuallyEq ?_ (hG_lt t htc)
      exact eventually_of_mem (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htc))
        fun u hu => hG_lt u (mem_Iio.1 hu)
    · rw [htc] at ht ⊢
      have hsplit : T = (T ∩ Iio c) ∪ (T ∩ Ici c) := by
        rw [← inter_union_distrib_left, Iio_union_Ici, inter_univ]
      rw [hsplit]
      refine ContinuousWithinAt.union ?_ (hGge c ⟨ht, mem_Ici.2 le_rfl⟩)
      show Tendsto G (𝓝[T ∩ Iio c] c) (𝓝 (G c))
      have hGc : G c = x := by
        rw [hG_ge c le_rfl]
        simp only [sub_self, add_zero]; exact A'.left_inv hx'
      rw [hGc]
      have h1 : Tendsto (fun s => A'.invFun (τ s)) (𝓝[S] c) (𝓝 x) := by
        have := (A'.continuousOn_invFun d hdT).tendsto.comp
          (tendsto_nhdsWithin_iff.2 ⟨hL2, eventually_nhdsWithin_of_forall
            fun s hs => trans_mem_target A A' hs⟩)
        rwa [A'.left_inv hx'] at this
      have h2 : Tendsto A.invFun (𝓝[S] c) (𝓝 x) :=
        h1.congr' (eventually_nhdsWithin_of_forall fun s hs => invFun_eq_of_mem_overlap A A' hs)
      have hSmem : S ∈ 𝓝[T ∩ Iio c] c := by
        refine mem_nhdsWithin.2 ⟨Ioi (sInf S), isOpen_Ioi, hinfSlt, fun u hu => ?_⟩
        obtain ⟨a, ha, hau⟩ := exists_lt_of_csInf_lt hSne (mem_Ioi.1 hu.1)
        obtain ⟨b, hb, hub⟩ := exists_lt_of_lt_csSup hSne (by rw [hsupS]; exact mem_Iio.1 hu.2.2)
        exact hSo.out ha hb ⟨hau.le, hub.le⟩
      refine (h2.mono_left (nhdsWithin_le_of_mem hSmem)).congr' ?_
      exact eventually_nhdsWithin_of_forall fun u hu => (hG_lt u (mem_Iio.1 hu.2)).symm
    · have hmem : T ∩ Ici c ∈ 𝓝[T] t :=
        mem_nhdsWithin.2 ⟨Ioi c, isOpen_Ioi, htc, fun u hu => ⟨hu.2, mem_Ici.2 (le_of_lt (mem_Ioi.1 hu.1))⟩⟩
      exact (hGge t ⟨ht, mem_Ici.2 htc.le⟩).mono_of_mem_nhdsWithin hmem
  -- the remaining obligations
  have hms : ∀ y ∈ A.source ∪ A'.source, F y ∈ T := by
    intro y hy
    by_cases hyA : y ∈ A.source
    · rw [hF_A y hyA]
      have := A.map_source hyA; rw [hAt] at this
      exact hTlt _ this.1 this.2
    · have hy' : y ∈ A'.source := hy.resolve_left hyA
      rw [hF_A' y hyA]
      have h1 := hF1 y hy' hyA
      refine hTof _ (by linarith) ?_
      have : d + (c + (A'.toFun y - d) - c) = A'.toFun y := by ring
      rw [this]; exact A'.map_source hy'
  have hmt : ∀ t ∈ T, G t ∈ A.source ∪ A'.source := by
    intro t ht
    rcases lt_or_ge t c with h | h
    · rw [hG_lt t h]; exact Or.inl (A.map_target (by rw [hAt]; exact ⟨ht.1, h⟩))
    · rw [hG_ge t h]; exact Or.inr (A'.map_target (hTge t ht h))
  have hli : ∀ y ∈ A.source ∪ A'.source, G (F y) = y := by
    intro y hy
    by_cases hyA : y ∈ A.source
    · have hlt' : F y < c := by
        rw [hF_A y hyA]; have := A.map_source hyA; rw [hAt] at this; exact this.2
      rw [hG_lt _ hlt', hF_A y hyA, A.left_inv hyA]
    · have hy' : y ∈ A'.source := hy.resolve_left hyA
      have hge : c ≤ F y := by rw [hF_A' y hyA]; linarith [hF1 y hy' hyA]
      rw [hG_ge _ hge, hF_A' y hyA]
      have : d + (c + (A'.toFun y - d) - c) = A'.toFun y := by ring
      rw [this]; exact A'.left_inv hy'
  have hri : ∀ t ∈ T, F (G t) = t := by
    intro t ht
    rcases lt_or_ge t c with h | h
    · have hmem : A.invFun t ∈ A.source := A.map_target (by rw [hAt]; exact ⟨ht.1, h⟩)
      rw [hG_lt t h, hF_A _ hmem, A.right_inv (by rw [hAt]; exact ⟨ht.1, h⟩)]
    · have hmem := hTge t ht h
      have hnot : A'.invFun (d + (t - c)) ∉ A.source := hF3 _ hmem (by linarith)
      rw [hG_ge t h, hF_A' _ hnot, A'.right_inv hmem]; ring
  have hbd : ∀ y ∈ A.source ∪ A'.source, y ∈ B ↔ F y ∉ interior T := by
    intro y hy
    rw [hint]
    by_cases hyA : y ∈ A.source
    · rw [hF_A y hyA, A.bdry y hyA, hAt, interior_Ico]
      have := A.map_source hyA; rw [hAt] at this
      constructor
      · intro h1 h2; exact h1 ⟨h2.1, this.2⟩
      · intro h1 h2; exact h1 ⟨h2.1, h2.2.trans_le hcc''⟩
    · have hy' : y ∈ A'.source := hy.resolve_left hyA
      rw [hF_A' y hyA, A'.bdry y hy', A'.interior_target]
      have h1 := hF1 y hy' hyA
      have h2 : sInf A'.target < A'.toFun y :=
        (csInf_le A'.bddBelow_target (hS'T ht₁)).trans_lt ((hlt t₁ ht₁).trans_le h1)
      constructor
      · intro h3 h4
        apply h3
        refine ⟨h2, ?_⟩
        rw [hc''] at h4; linarith [h4.2]
      · intro h3 h4
        apply h3
        refine ⟨by linarith, ?_⟩
        rw [hc'']; linarith [h4.2]
  let Ã : Arc M B :=
    { toFun := F
      invFun := G
      source := A.source ∪ A'.source
      target := T
      map_source' := hms
      map_target' := hmt
      left_inv' := hli
      right_inv' := hri
      open_source := A.open_source.union A'.open_source
      ordConnected_target := hTo
      nontrivial_target := hTn
      bddAbove_target := ⟨c'', fun t ht => (hIcc ht).2⟩
      bddBelow_target := ⟨0, fun t ht => (hIcc ht).1⟩
      continuousOn_toFun := hFcont
      continuousOn_invFun := hGcont
      bdry := hbd }
  exact ⟨Ã, Or.inl hpA, (hF_A p hpA).trans hp0, hTlt 0 le_rfl hc, fun t ht => ht.1,
    subset_union_left, subset_union_right⟩

end Extend

/-! ### Removing the normalization -/

section Extend2

variable [T2Space M] (A A' : Arc M B) {p x : M} {c : ℝ}

theorem exists_extension (hc : 0 < c) (hpA : p ∈ A.source) (hp0 : A.toFun p = 0)
    (hAt : A.target = Ico 0 c) (hx' : x ∈ A'.source) (hxA : x ∉ A.source)
    (hxcl : x ∈ closure A.source) :
    ∃ Ã : Arc M B, p ∈ Ã.source ∧ Ã.toFun p = 0 ∧ (0 : ℝ) ∈ Ã.target ∧ Ã.target ⊆ Ici 0 ∧
      A.source ⊆ Ã.source ∧ A'.source ⊆ Ã.source := by
  set S' := overlap A' A with hS'
  set d := A'.toFun x with hd
  have hdS' : d ∉ S' := by
    rintro ⟨z, hz, hzx⟩
    exact hxA (A'.injOn hz.1 hx' hzx ▸ hz.2)
  have hxcl' : x ∈ closure (A'.source ∩ A.source) := by
    rw [mem_closure_iff_nhds] at hxcl ⊢
    intro N hN
    obtain ⟨z, hz⟩ := hxcl (N ∩ A'.source) (inter_mem hN (A'.open_source.mem_nhds hx'))
    exact ⟨z, hz.1.1, hz.1.2, hz.2⟩
  have hdcl : d ∈ closure S' :=
    ((A'.continuousOn_toFun x hx').mono inter_subset_left).mem_closure_image hxcl'
  have hS'ne : S'.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hdcl
    exact hdcl
  have hS'o : S'.OrdConnected := by
    have := overlap_ordConnected A A' hc hpA hp0 hAt
    have hτS : trans A A' '' overlap A A' = S' := by
      ext t; constructor
      · rintro ⟨s, hs, rfl⟩; exact trans_mem_overlap A A' hs
      · intro ht
        refine ⟨trans A' A t, trans_mem_overlap A' A ht, ?_⟩
        have h1 := invFun_eq_of_mem_overlap A' A ht
        show A'.toFun (A.invFun (trans A' A t)) = t
        rw [h1, A'.right_inv (overlap_subset A' A ht)]
    rw [← hτS]; exact ordConnected_image_trans A A' subset_rfl this
  have hS'a : BddAbove S' := A'.bddAbove_target.mono (overlap_subset A' A)
  have hS'b : BddBelow S' := A'.bddBelow_target.mono (overlap_subset A' A)
  have happ : ∀ ε > 0, ∃ t ∈ S', |t - d| < ε := fun ε hε => by
    obtain ⟨t, ht, hlt⟩ := Metric.mem_closure_iff.1 hdcl ε hε
    exact ⟨t, ht, by rwa [Real.dist_eq, abs_sub_comm] at hlt⟩
  have hdich : (∀ t ∈ S', t < d) ∨ (∀ t ∈ S', d < t) := by
    by_contra h
    push_neg at h
    obtain ⟨⟨a, ha, hda⟩, b, hb, hbd⟩ := h
    exact hdS' (hS'o.out hb ha ⟨hbd, hda⟩)
  rcases hdich with hlt | hgt
  · exact exists_extension_aux A A' hc hpA hp0 hAt hx' hxA hlt fun ε hε => by
      obtain ⟨t, ht, h⟩ := happ ε hε
      exact ⟨t, ht, by rw [abs_lt] at h; linarith [h.1]⟩
  · have hneg := exists_extension_aux A A'.neg hc hpA hp0 hAt hx' hxA
      (by
        rw [overlap_neg_left]
        intro t ht
        rw [Set.mem_neg] at ht
        have := hgt _ ht
        show t < -A'.toFun x
        linarith)
      (by
        intro ε hε
        obtain ⟨t, ht, h⟩ := happ ε hε
        refine ⟨-t, by rw [overlap_neg_left, Set.mem_neg, neg_neg]; exact ht, ?_⟩
        show -A'.toFun x - ε < -t
        rw [abs_lt] at h; linarith [h.2])
    obtain ⟨Ã, h1, h2, h3, h4, h5, h6⟩ := hneg
    exact ⟨Ã, h1, h2, h3, h4, h5, h6⟩

end Extend2

/-! ### The finite-cover induction and the main theorem -/

section Main

variable [T2Space M]

/-- An arc "from `p`": `p` is its left endpoint, with coordinate `0`. -/
def IsFrom (A : Arc M B) (p : M) : Prop :=
  p ∈ A.source ∧ A.toFun p = 0 ∧ (0 : ℝ) ∈ A.target ∧ A.target ⊆ Ici 0

theorem IsFrom.sInf_target {A : Arc M B} {p : M} (h : IsFrom A p) : sInf A.target = 0 :=
  le_antisymm (csInf_le A.bddBelow_target h.2.2.1) (le_csInf ⟨0, h.2.2.1⟩ fun t ht => h.2.2.2 ht)

theorem IsFrom.pos {A : Arc M B} {p : M} (h : IsFrom A p) : 0 < sSup A.target := by
  have := A.sInf_lt_sSup; rwa [h.sInf_target] at this

theorem IsFrom.target_eq {A : Arc M B} {p : M} (h : IsFrom A p) :
    A.target = Ico 0 (sSup A.target) ∨ A.target = Icc 0 (sSup A.target) := by
  have h1 : Ioo 0 (sSup A.target) ⊆ A.target := by
    have := A.Ioo_subset_target; rwa [h.sInf_target] at this
  have h2 : A.target ⊆ Icc 0 (sSup A.target) := by
    have := A.target_subset_Icc; rwa [h.sInf_target] at this
  by_cases hc : sSup A.target ∈ A.target
  · right; apply Subset.antisymm h2
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · rw [h']; exact hc
    · rcases eq_or_lt_of_le ht.1 with h'' | h''
      · rw [← h'']; exact h.2.2.1
      · exact h1 ⟨h'', h'⟩
  · left; apply Subset.antisymm
    · intro t ht; exact ⟨(h2 ht).1, lt_of_le_of_ne (h2 ht).2 (fun h' => hc (h' ▸ ht))⟩
    · intro t ht
      rcases eq_or_lt_of_le ht.1 with h'' | h''
      · rw [← h'']; exact h.2.2.1
      · exact h1 ⟨h'', ht.2⟩

theorem IsFrom.target_eq_Icc {A : Arc M B} {p : M} (h : IsFrom A p)
    (hc : sSup A.target ∈ A.target) : A.target = Icc 0 (sSup A.target) := by
  rcases h.target_eq with h' | h'
  · exfalso
    set c := sSup A.target with hcdef
    rw [h'] at hc; exact lt_irrefl _ hc.2
  · exact h'

theorem IsFrom.source_subset_component {A : Arc M B} {p : M} (h : IsFrom A p) :
    A.source ⊆ connectedComponent p :=
  A.isPreconnected_source.subset_connectedComponent h.1

theorem IsFrom.source_eq_of_mem {A : Arc M B} {p : M} (h : IsFrom A p)
    (hc : sSup A.target ∈ A.target) : A.source = connectedComponent p := by
  have hT := h.target_eq_Icc hc
  have hcT : IsCompact A.target := by rw [hT]; exact isCompact_Icc
  have hcomp : IsCompact A.source := by
    rw [← A.image_target]; exact hcT.image_of_continuousOn A.continuousOn_invFun
  have hclopen : IsClopen A.source := ⟨hcomp.isClosed, A.open_source⟩
  exact Subset.antisymm h.source_subset_component (hclopen.connectedComponent_subset h.1)

theorem IsFrom.boundary_inter_component {A : Arc M B} {p : M} (h : IsFrom A p)
    (hc : sSup A.target ∈ A.target) :
    B ∩ connectedComponent p = {p, A.invFun (sSup A.target)} := by
  have hT := h.target_eq_Icc hc
  rw [← h.source_eq_of_mem hc]
  set c := sSup A.target with hcdef
  ext x; constructor
  · rintro ⟨hxB, hxA⟩
    have hb := (A.bdry x hxA).1 hxB
    rw [hT, interior_Icc, mem_Ioo, not_and_or, not_lt, not_lt] at hb
    have hxt := A.map_source hxA; rw [hT] at hxt
    rcases hb with h0 | h0
    · left
      have hx0 : A.toFun x = 0 := le_antisymm h0 hxt.1
      rw [← A.left_inv hxA, hx0, ← h.2.1, A.left_inv h.1]
    · right
      have hx0 : A.toFun x = sSup A.target := le_antisymm hxt.2 h0
      rw [mem_singleton_iff, ← A.left_inv hxA, hx0]
  · rintro (rfl | hx)
    · exact ⟨(A.bdry _ h.1).2 (by rw [h.2.1, hT, interior_Icc]; simp), h.1⟩
    · rw [mem_singleton_iff] at hx; subst hx
      refine ⟨(A.bdry _ (A.map_target hc)).2 ?_, A.map_target hc⟩
      rw [A.right_inv hc, hT, interior_Icc]; simp

/-- A proper open subset of a component that contains the base point has a limit point outside
itself. -/
theorem exists_mem_closure_of_ne {U : Set M} {p : M} (hU : IsOpen U) (hpU : p ∈ U)
    (hUK : U ⊆ connectedComponent p) (hne : U ≠ connectedComponent p) :
    ∃ x, x ∈ closure U ∧ x ∉ U := by
  by_contra hcon
  push_neg at hcon
  have hK := isPreconnected_connectedComponent (x := p)
  have h := hK U (closure U)ᶜ hU isClosed_closure.isOpen_compl
    (fun k _ => by
      by_cases hkc : k ∈ closure U
      · exact Or.inl (hcon k hkc)
      · exact Or.inr hkc)
    ⟨p, mem_connectedComponent, hpU⟩
    (by
      obtain ⟨k, hk, hkU⟩ := not_subset.1 (fun h => hne (Subset.antisymm hUK h))
      exact ⟨k, hk, fun hkc => hkU (hcon k hkc)⟩)
  obtain ⟨x, -, hx1, hx2⟩ := h
  exact hx2 (subset_closure hx1)

variable {H : Type*} [TopologicalSpace H] (φ : H ≃ₜ Ici (0 : ℝ)) [ChartedSpace H M]

/-- **Milnor's Appendix, the essential part.** Starting from a boundary point `p`, an arc can be
extended until it is closed; its source is then the whole component of `p`. -/
theorem exists_closed_arc [CompactSpace M] (hB : BoundaryCompatible φ B) {p : M} (hp : p ∈ B) :
    ∃ A : Arc M B, IsFrom A p ∧ sSup A.target ∈ A.target := by
  classical
  have hcov : ∀ y : M, ∃ A : Arc M B, y ∈ A.source := fun y => by
    by_cases hy : y ∈ B
    · obtain ⟨A, ε, -, hyA, -, -⟩ := exists_arc_of_mem_boundary hB hy; exact ⟨A, hyA⟩
    · obtain ⟨A, hyA, -⟩ := exists_arc_of_notMem_boundary hB hy; exact ⟨A, hyA⟩
  choose 𝒜 h𝒜 using hcov
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => (𝒜 y).source)
    (fun y => (𝒜 y).open_source) (fun y _ => mem_iUnion.2 ⟨y, h𝒜 y⟩)
  obtain ⟨A₀, ε, hε, hpA, hp0, hT⟩ := exists_arc_of_mem_boundary hB hp
  have hfrom₀ : IsFrom A₀ p := ⟨hpA, hp0, by rw [hT]; exact ⟨le_rfl, hε⟩,
    by rw [hT]; exact Ico_subset_Ici_self⟩
  suffices key : ∀ n : ℕ, ∀ A : Arc M B, IsFrom A p →
      (s.filter fun y => ¬ (𝒜 y).source ⊆ A.source).card = n →
      ∃ A' : Arc M B, IsFrom A' p ∧ sSup A'.target ∈ A'.target from key _ A₀ hfrom₀ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA hn
  by_cases hc : sSup A.target ∈ A.target
  · exact ⟨A, hA, hc⟩
  set c := sSup A.target with hcdef
  have hT : A.target = Ico 0 c :=
    hA.target_eq.resolve_right (fun h => hc (by rw [h]; exact ⟨hA.pos.le, le_rfl⟩))
  have hne : A.source ≠ connectedComponent p := by
    intro h
    have hcomp : IsCompact A.source := by rw [h]; exact isClosed_connectedComponent.isCompact
    have hcT : IsCompact A.target := by
      rw [← A.image_source]; exact hcomp.image_of_continuousOn A.continuousOn_toFun
    exact hc (hcT.isClosed.csSup_mem A.nontrivial_target.nonempty A.bddAbove_target)
  obtain ⟨x, hxcl, hxA⟩ :=
    exists_mem_closure_of_ne A.open_source hA.1 hA.source_subset_component hne
  obtain ⟨y, hys, hxy⟩ := mem_iUnion₂.1 (hs (mem_univ x))
  obtain ⟨Ã, h1, h2, h3, h4, hAsub, hysub⟩ :=
    exists_extension A (𝒜 y) hA.pos hA.1 hA.2.1 hT hxy hxA hxcl
  have hfrom : IsFrom Ã p := ⟨h1, h2, h3, h4⟩
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
  exact ih _ hcard Ã hfrom rfl

/-- Every boundary point `p` has a partner: the other endpoint of its component. -/
theorem exists_partner [CompactSpace M] (hB : BoundaryCompatible φ B) {p : M} (hp : p ∈ B) :
    ∃ q, q ∈ B ∧ q ≠ p ∧ B ∩ connectedComponent p = {p, q} := by
  obtain ⟨A, hA, hc⟩ := exists_closed_arc φ hB hp
  have heq := hA.boundary_inter_component hc
  refine ⟨A.invFun (sSup A.target), ?_, ?_, heq⟩
  · have hmem : A.invFun (sSup A.target) ∈ B ∩ connectedComponent p := by rw [heq]; simp
    exact hmem.1
  · intro h
    have := congrArg A.toFun h
    rw [A.right_inv hc, hA.2.1] at this
    exact hA.pos.ne' this

/-- A finite set with a fixed-point-free involution has even cardinality. -/
theorem even_ncard_of_involution {α : Type*} {s : Set α} (hs : s.Finite) (ι : α → α)
    (hmem : ∀ a ∈ s, ι a ∈ s) (hinv : ∀ a ∈ s, ι (ι a) = a) (hne : ∀ a ∈ s, ι a ≠ a) :
    Even s.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card s hs]
  have h := Finset.prod_involution (s := hs.toFinset) (f := fun _ => (-1 : ℤ)) (fun a _ => ι a)
    (fun a _ => by simp) (fun a ha _ => hne a (hs.mem_toFinset.1 ha))
    (fun a ha => hs.mem_toFinset.2 (hmem a (hs.mem_toFinset.1 ha)))
    (fun a ha => hinv a (hs.mem_toFinset.1 ha))
  rw [Finset.prod_const] at h
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 h

/-- **The boundary of a compact 1-manifold has an even number of points.** -/
theorem even_ncard_boundary [CompactSpace M] (hB : BoundaryCompatible φ B) :
    B.Finite ∧ Even B.ncard := by
  refine ⟨finite_boundary hB, ?_⟩
  classical
  rcases B.eq_empty_or_nonempty with hBe | ⟨p₀, hp₀⟩
  · rw [hBe]; simp
  haveI : Nonempty M := ⟨p₀⟩
  have hpart := fun p (hp : p ∈ B) => exists_partner φ hB hp
  choose! ι hιB hιne hιeq using hpart
  refine even_ncard_of_involution (finite_boundary hB) ι hιB ?_ hιne
  intro p hp
  have hq := hιB p hp
  have hK : connectedComponent (ι p) = connectedComponent p := by
    have : ι p ∈ B ∩ connectedComponent p := by rw [hιeq p hp]; simp
    exact (connectedComponent_eq this.2).symm
  have h1 := hιeq (ι p) hq
  rw [hK, hιeq p hp] at h1
  have : ι (ι p) ∈ ({p, ι p} : Set M) := by rw [h1]; simp
  rcases this with h | h
  · exact h
  · rw [mem_singleton_iff] at h
    exact absurd h (hιne (ι p) hq)

end Main

end OneManifold
end Milnor
