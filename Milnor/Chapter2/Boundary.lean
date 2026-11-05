import Milnor.Chapter2.Submanifold
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §2, "Manifolds with boundary" (pp. 12–13):
the infrastructure.

> Consider first the closed half-space `Hᵐ = {(x₁, …, xₘ) ∈ ℝᵐ | xₘ ≥ 0}`. The boundary `∂Hᵐ` is
> defined to be the hyperplane `ℝᵐ⁻¹ × 0 ⊆ ℝᵐ`.
>
> **Definition.** A subset `X ⊆ ℝᵏ` is called a smooth `m`-manifold with boundary if each `x ∈ X`
> has a neighborhood `U ∩ X` diffeomorphic to an open subset `V ∩ Hᵐ` of `Hᵐ`. The boundary `∂X`
> is the set of all points in `X` which correspond to points of `∂Hᵐ` under such a diffeomorphism.
>
> It is not hard to show that `∂X` is a well-defined smooth manifold of dimension `m - 1`. The
> interior `X ∖ ∂X` is a smooth manifold of dimension `m`.

Mathlib's manifolds with boundary are `IsManifold I n X` for a model with corners `I` whose
range is not all of the model vector space. We build such a model, `halfSpaceModel Z`, whose
model space is the half-space `{(t, z) ∈ ℝ × Z | 0 ≤ t}` (Milnor's `Hᵐ` with the distinguished
coordinate written first), and the analogue of the slice charts of
`Milnor.Chapter2.Submanifold`:

* `HalfSliceChart I Z X B`: a diffeomorphism `Φ` from an open subset of `M` onto an open subset
  of `ℝ × Z` under which `X` corresponds to `{0 ≤ t}` and `B` to `{t = 0}`;
* `IsHalfSliceSubmanifold I Z X B`: every point of `X` lies in the domain of such a chart;
* the induced charted space and manifold structure on `X`, modelled on `halfSpaceModel Z`;
* `IsHalfSliceSubmanifold.boundary_eq`: Mathlib's boundary of `X` is `B`;
* `IsHalfSliceSubmanifold.contMDiff_val`: the inclusion `X → M` is smooth.

The "well-definedness" of the boundary that Milnor mentions is built into the definition here:
every chart in the family is required to send `B`, and only `B`, to `{t = 0}`. For the manifolds
with boundary that arise in the book (Lemmas 3 and 4) the family is constructed with this
property, so no invariance-of-domain argument is needed.
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

/-! ### The half-space model -/

section model

variable (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The closed half-space `{(t, z) ∈ ℝ × Z | 0 ≤ t}`. -/
abbrev HalfSpace : Type _ := {p : ℝ × Z // 0 ≤ p.1}

instance : Inhabited (HalfSpace Z) := ⟨⟨(0, 0), le_rfl⟩⟩

theorem HalfSpace.ext {p q : HalfSpace Z} (h : p.1 = q.1) : p = q := Subtype.ext h

/-- The model with corners `(ℝ × Z, HalfSpace Z)`: the identity on the half-space, with inverse
`(t, z) ↦ (max t 0, z)`. -/
def halfSpaceModel : ModelWithCorners ℝ (ℝ × Z) (HalfSpace Z) where
  toFun := Subtype.val
  invFun p := ⟨(max p.1 0, p.2), le_max_right _ _⟩
  source := univ
  target := {p | 0 ≤ p.1}
  map_source' x _ := x.2
  map_target' _ _ := mem_univ _
  left_inv' := fun ⟨p, hp⟩ _ => by
    apply Subtype.ext
    show (max p.1 0, p.2) = p
    rw [max_eq_left hp]
  right_inv' p hp := by
    show (max p.1 0, p.2) = p
    rw [max_eq_left hp]
  source_eq := rfl
  convex_range' := by
    simp only [instIsRCLikeNormedField, ↓reduceDIte]
    apply Convex.convex_isRCLikeNormedField
    have : range (Subtype.val : HalfSpace Z → ℝ × Z) = (LinearMap.fst ℝ ℝ Z) ⁻¹' Ici 0 := by
      rw [Subtype.range_coe_subtype]
      rfl
    rw [this]
    exact (convex_Ici 0).linear_preimage _
  nonempty_interior' := by
    refine ⟨(1, 0), mem_interior.2 ⟨{p | 0 < p.1}, ?_, isOpen_lt continuous_const continuous_fst,
      by simp⟩⟩
    rintro p hp
    exact ⟨⟨p, le_of_lt hp⟩, rfl⟩
  continuous_toFun := continuous_subtype_val
  continuous_invFun := ((continuous_fst.max continuous_const).prodMk continuous_snd).subtype_mk _

variable {Z}

@[simp] theorem halfSpaceModel_apply (p : HalfSpace Z) : halfSpaceModel Z p = p.1 := rfl

theorem halfSpaceModel_symm_apply (p : ℝ × Z) :
    ((halfSpaceModel Z).symm p).1 = (max p.1 0, p.2) := rfl

theorem halfSpaceModel_symm_apply_of_nonneg {p : ℝ × Z} (hp : 0 ≤ p.1) :
    ((halfSpaceModel Z).symm p).1 = p := by
  rw [halfSpaceModel_symm_apply, max_eq_left hp]

theorem range_halfSpaceModel : range (halfSpaceModel Z) = {p : ℝ × Z | 0 ≤ p.1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.2
  · intro hp
    exact ⟨⟨p, hp⟩, rfl⟩

theorem interior_range_halfSpaceModel :
    interior (range (halfSpaceModel Z)) = {p : ℝ × Z | 0 < p.1} := by
  rw [range_halfSpaceModel]
  have : {p : ℝ × Z | 0 ≤ p.1} = Prod.fst ⁻¹' Ici 0 := rfl
  rw [this, ← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst, interior_Ici]
  rfl

theorem frontier_range_halfSpaceModel :
    frontier (range (halfSpaceModel Z)) = {p : ℝ × Z | p.1 = 0} := by
  rw [frontier, interior_range_halfSpaceModel, range_halfSpaceModel]
  have hcl : closure {p : ℝ × Z | 0 ≤ p.1} = {p : ℝ × Z | 0 ≤ p.1} :=
    (isClosed_Ici.preimage continuous_fst).closure_eq
  rw [hcl]
  ext p
  simp only [mem_diff, mem_setOf_eq, not_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · intro h; exact ⟨le_of_eq h.symm, le_of_eq h⟩

end model

/-! ### Half-slice charts -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A **half-slice chart** for `X ⊆ M` with boundary `B ⊆ X`: a diffeomorphism `Φ` from an open
subset of `M` onto an open subset of `ℝ × Z` such that, on its domain, `X` corresponds to
`{0 ≤ t}` and `B` to `{t = 0}`. It comes with a base point `x₀ ∈ X` in its domain. -/
structure HalfSliceChart (X B : Set M) where
  Φ : PartialDiffeomorph I 𝓘(ℝ, ℝ × Z) M (ℝ × Z) ∞
  x₀ : M
  x₀_mem : x₀ ∈ X
  x₀_source : x₀ ∈ Φ.source
  half : ∀ p ∈ Φ.source, p ∈ X ↔ 0 ≤ (Φ p).1
  bdry : ∀ p ∈ Φ.source, p ∈ B ↔ (Φ p).1 = 0

/-- `X` is a manifold with boundary `B`, modelled on the half-space over `Z`, if every point of `X`
lies in the domain of a half-slice chart. -/
def IsHalfSliceSubmanifold (X B : Set M) : Prop :=
  ∀ p ∈ X, ∃ σ : HalfSliceChart I Z X B, p ∈ σ.Φ.source

variable {I Z}

namespace HalfSliceChart

variable {X B : Set M} (σ : HalfSliceChart I Z X B)

theorem symm_mem {p : ℝ × Z} (hp : p ∈ σ.Φ.target) (h0 : 0 ≤ p.1) : σ.Φ.invFun p ∈ X := by
  have h1 : σ.Φ.invFun p ∈ σ.Φ.source := σ.Φ.invFun_mem hp
  rw [σ.half _ h1, σ.Φ.apply_invFun hp]
  exact h0

open Classical in
/-- The induced chart, as a map `X → HalfSpace Z` (junk outside the source). -/
def chartFun (q : X) : HalfSpace Z :=
  if h : q.1 ∈ σ.Φ.source then ⟨σ.Φ q.1, (σ.half _ h).1 q.2⟩ else default

open Classical in
/-- The inverse of the induced chart, as a map `HalfSpace Z → X` (junk outside the target). -/
def invChart (h : HalfSpace Z) : X :=
  if hh : h.1 ∈ σ.Φ.target then ⟨σ.Φ.invFun h.1, σ.symm_mem hh h.2⟩ else ⟨σ.x₀, σ.x₀_mem⟩

theorem chartFun_of_mem {q : X} (h : q.1 ∈ σ.Φ.source) : (σ.chartFun q).1 = σ.Φ q.1 := by
  simp [chartFun, h]

theorem invChart_of_mem {h : HalfSpace Z} (hh : h.1 ∈ σ.Φ.target) :
    (σ.invChart h : M) = σ.Φ.invFun h.1 := by
  simp [invChart, hh]

/-- The chart of `X` induced by a half-slice chart. -/
def toChart : OpenPartialHomeomorph X (HalfSpace Z) where
  toFun := σ.chartFun
  invFun := σ.invChart
  source := {q | q.1 ∈ σ.Φ.source}
  target := {h | h.1 ∈ σ.Φ.target}
  map_source' q hq := by
    show (σ.chartFun q).1 ∈ σ.Φ.target
    rw [σ.chartFun_of_mem hq]
    exact σ.Φ.apply_mem hq
  map_target' h hh := by
    show (σ.invChart h : M) ∈ σ.Φ.source
    rw [σ.invChart_of_mem hh]
    exact σ.Φ.invFun_mem hh
  left_inv' q hq := by
    apply Subtype.ext
    have h1 : (σ.chartFun q).1 ∈ σ.Φ.target := by
      rw [σ.chartFun_of_mem hq]; exact σ.Φ.apply_mem hq
    rw [σ.invChart_of_mem h1, σ.chartFun_of_mem hq, σ.Φ.invFun_apply hq]
  right_inv' h hh := by
    apply HalfSpace.ext
    have h1 : (σ.invChart h : M) ∈ σ.Φ.source := by
      rw [σ.invChart_of_mem hh]; exact σ.Φ.invFun_mem hh
    rw [σ.chartFun_of_mem h1, σ.invChart_of_mem hh, σ.Φ.apply_invFun hh]
  open_source := σ.Φ.open_source.preimage continuous_subtype_val
  open_target := σ.Φ.open_target.preimage continuous_subtype_val
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_restrict]
    have hfun : {q : X | q.1 ∈ σ.Φ.source}.domRestrict σ.chartFun =
        fun q => ⟨σ.Φ q.1.1, (σ.half _ q.2).1 q.1.2⟩ := by
      funext q
      apply HalfSpace.ext
      exact σ.chartFun_of_mem q.2
    rw [hfun]
    apply Continuous.subtype_mk
    exact σ.Φ.contMDiffOn.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) fun q => q.2
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict]
    have hfun : {h : HalfSpace Z | h.1 ∈ σ.Φ.target}.domRestrict σ.invChart =
        fun h => ⟨σ.Φ.invFun h.1.1, σ.symm_mem h.2 h.1.2⟩ := by
      funext h
      apply Subtype.ext
      exact σ.invChart_of_mem h.2
    rw [hfun]
    apply Continuous.subtype_mk
    exact σ.Φ.contMDiffOn_invFun.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) fun h => h.2

@[simp] theorem toChart_source : σ.toChart.source = {q | q.1 ∈ σ.Φ.source} := rfl
@[simp] theorem toChart_target : σ.toChart.target = {h | h.1 ∈ σ.Φ.target} := rfl
theorem toChart_apply {q : X} (hq : q.1 ∈ σ.Φ.source) : (σ.toChart q).1 = σ.Φ q.1 :=
  σ.chartFun_of_mem hq
theorem toChart_symm_apply {h : HalfSpace Z} (hh : h.1 ∈ σ.Φ.target) :
    (σ.toChart.symm h : M) = σ.Φ.invFun h.1 := σ.invChart_of_mem hh

end HalfSliceChart

namespace IsHalfSliceSubmanifold

variable {X B : Set M} (hX : IsHalfSliceSubmanifold I Z X B)

/-- The charted-space structure on a half-slice submanifold. -/
def chartedSpace : ChartedSpace (HalfSpace Z) X where
  atlas := {e | ∃ σ : HalfSliceChart I Z X B, e = σ.toChart}
  chartAt p := (hX p.1 p.2).choose.toChart
  mem_chart_source p := (hX p.1 p.2).choose_spec
  chart_mem_atlas _ := ⟨_, rfl⟩

theorem chartAt_eq (p : X) :
    @chartAt (HalfSpace Z) _ X _ hX.chartedSpace p = (hX p.1 p.2).choose.toChart := rfl

/-- The transition map between two half-slice charts, read in the model, is smooth on the
half-space. -/
theorem contDiffOn_trans (σ₁ σ₂ : HalfSliceChart I Z X B) :
    ContDiffOn ℝ ∞
      (halfSpaceModel Z ∘ (σ₁.toChart.symm ≫ₕ σ₂.toChart) ∘ (halfSpaceModel Z).symm)
      ((halfSpaceModel Z).symm ⁻¹' (σ₁.toChart.symm ≫ₕ σ₂.toChart).source ∩
        range (halfSpaceModel Z)) := by
  set T := (halfSpaceModel Z).symm ⁻¹' (σ₁.toChart.symm ≫ₕ σ₂.toChart).source ∩
    range (halfSpaceModel Z) with hT
  have hT' : ∀ u ∈ T, 0 ≤ u.1 ∧ u ∈ σ₁.Φ.target ∧ σ₁.Φ.invFun u ∈ σ₂.Φ.source := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    rw [range_halfSpaceModel] at hu2
    have hu2' : 0 ≤ u.1 := hu2
    rw [mem_preimage, OpenPartialHomeomorph.trans_source] at hu1
    obtain ⟨h1, h2⟩ := hu1
    have h1' : u ∈ σ₁.Φ.target := by
      have := h1
      rw [OpenPartialHomeomorph.symm_source, HalfSliceChart.toChart_target, mem_setOf_eq,
        halfSpaceModel_symm_apply_of_nonneg hu2'] at this
      exact this
    refine ⟨hu2', h1', ?_⟩
    have := h2
    rw [mem_preimage, HalfSliceChart.toChart_source, mem_setOf_eq] at this
    have hsymm : ((σ₁.toChart.symm ((halfSpaceModel Z).symm u)) : M) = σ₁.Φ.invFun u := by
      rw [σ₁.toChart_symm_apply]
      · rw [halfSpaceModel_symm_apply_of_nonneg hu2']
      · rw [halfSpaceModel_symm_apply_of_nonneg hu2']; exact h1'
    rwa [hsymm] at this
  have h1 : ContMDiffOn 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, ℝ × Z) ∞ (σ₂.Φ ∘ σ₁.Φ.invFun)
      (σ₁.Φ.target ∩ σ₁.Φ.invFun ⁻¹' σ₂.Φ.source) :=
    σ₂.Φ.contMDiffOn.comp (σ₁.Φ.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right
  rw [contMDiffOn_iff_contDiffOn] at h1
  refine (h1.mono fun u hu => ⟨(hT' u hu).2.1, (hT' u hu).2.2⟩).congr fun u hu => ?_
  obtain ⟨hu0, hu1, hu2⟩ := hT' u hu
  simp only [Function.comp_apply, OpenPartialHomeomorph.trans_apply, halfSpaceModel_apply]
  have hsymm : ((σ₁.toChart.symm ((halfSpaceModel Z).symm u)) : M) = σ₁.Φ.invFun u := by
    rw [σ₁.toChart_symm_apply]
    · rw [halfSpaceModel_symm_apply_of_nonneg hu0]
    · rw [halfSpaceModel_symm_apply_of_nonneg hu0]; exact hu1
  rw [σ₂.toChart_apply (by rw [hsymm]; exact hu2), hsymm]

/-- A half-slice submanifold is a smooth manifold with corners (with boundary). -/
theorem isManifold : letI := hX.chartedSpace; IsManifold (halfSpaceModel Z) ∞ X := by
  letI := hX.chartedSpace
  refine isManifold_of_contDiffOn (halfSpaceModel Z) ∞ X ?_
  intro e e' he he'
  obtain ⟨σ₁, rfl⟩ := he
  obtain ⟨σ₂, rfl⟩ := he'
  exact IsHalfSliceSubmanifold.contDiffOn_trans σ₁ σ₂

/-- The boundary of a half-slice submanifold, in Mathlib's sense, is `B`. -/
theorem boundary_eq : letI := hX.chartedSpace; (halfSpaceModel Z).boundary X = {q | q.1 ∈ B} := by
  letI := hX.chartedSpace
  ext q
  set σ := (hX q.1 q.2).choose with hσ
  have hqσ : q.1 ∈ σ.Φ.source := (hX q.1 q.2).choose_spec
  show (halfSpaceModel Z).IsBoundaryPoint q ↔ q.1 ∈ B
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_halfSpaceModel, mem_setOf_eq,
    extChartAt, hX.chartAt_eq, ← hσ]
  have : ((σ.toChart.extend (halfSpaceModel Z)) q) = σ.Φ q.1 := by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, halfSpaceModel_apply,
      σ.toChart_apply hqσ]
  rw [this]
  exact (σ.bdry q.1 hqσ).symm

/-- The inclusion of a half-slice submanifold is smooth. -/
theorem contMDiff_val :
    letI := hX.chartedSpace; ContMDiff (halfSpaceModel Z) I ∞ (Subtype.val : X → M) := by
  letI := hX.chartedSpace
  haveI := hX.isManifold
  intro q
  set σ := (hX q.1 q.2).choose with hσ
  have hqσ : q.1 ∈ σ.Φ.source := (hX q.1 q.2).choose_spec
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  simp only [extChartAt]
  rw [hX.chartAt_eq, ← hσ]
  set u₀ : ℝ × Z := σ.Φ q.1 with hu₀
  have hu₀t : u₀ ∈ σ.Φ.target := σ.Φ.apply_mem hqσ
  have hpt : (σ.toChart.extend (halfSpaceModel Z)) q = u₀ := by
    rw [OpenPartialHomeomorph.extend_coe, Function.comp_apply, halfSpaceModel_apply,
      σ.toChart_apply hqσ]
  rw [hpt]
  -- The smooth map `extChartAt I q ∘ Φ⁻¹` on an open set around `u₀`.
  have hU : IsOpen (σ.Φ.target ∩ σ.Φ.invFun ⁻¹' (extChartAt I q.1).source) :=
    σ.Φ.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage σ.Φ.open_target
      (isOpen_extChartAt_source q.1)
  have hu₀U : u₀ ∈ σ.Φ.target ∩ σ.Φ.invFun ⁻¹' (extChartAt I q.1).source := by
    refine ⟨hu₀t, ?_⟩
    show σ.Φ.invFun u₀ ∈ (extChartAt I q.1).source
    rw [hu₀, σ.Φ.invFun_apply hqσ]
    exact mem_extChartAt_source q.1
  have h1 : ContMDiffOn 𝓘(ℝ, ℝ × Z) 𝓘(ℝ, E) ∞ (extChartAt I q.1 ∘ σ.Φ.invFun)
      (σ.Φ.target ∩ σ.Φ.invFun ⁻¹' (extChartAt I q.1).source) :=
    (contMDiffOn_extChartAt (n := ∞)).comp (σ.Φ.contMDiffOn_invFun.mono inter_subset_left)
      (by
        intro w hw
        rw [extChartAt_source] at hw
        exact hw.2)
  rw [contMDiffOn_iff_contDiffOn] at h1
  have h2 : ContDiffAt ℝ ∞ (extChartAt I q.1 ∘ σ.Φ.invFun) u₀ := h1.contDiffAt (hU.mem_nhds hu₀U)
  refine h2.contDiffWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (σ.Φ.open_target.mem_nhds hu₀t)]
      with u hu hu'
    rw [range_halfSpaceModel] at hu
    have hu0 : 0 ≤ u.1 := hu
    show extChartAt I q.1 ((σ.toChart.extend (halfSpaceModel Z)).symm u : X) =
      extChartAt I q.1 (σ.Φ.invFun u)
    rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply]
    rw [σ.toChart_symm_apply (by rw [halfSpaceModel_symm_apply_of_nonneg hu0]; exact hu'),
      halfSpaceModel_symm_apply_of_nonneg hu0]
  · show extChartAt I q.1 ((σ.toChart.extend (halfSpaceModel Z)).symm u₀ : X) =
      extChartAt I q.1 (σ.Φ.invFun u₀)
    have hu0 : 0 ≤ u₀.1 := (σ.half _ hqσ).1 q.2
    rw [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply]
    rw [σ.toChart_symm_apply (by rw [halfSpaceModel_symm_apply_of_nonneg hu0]; exact hu₀t),
      halfSpaceModel_symm_apply_of_nonneg hu0]

end IsHalfSliceSubmanifold

end Milnor
