import Milnor.Chapter1.InverseFunction
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §2, Lemma 1 (p. 11): the infrastructure.

# Submanifolds given by slice charts

Milnor's Lemma 1 says that `f⁻¹(y)` is a smooth manifold of dimension `m - n` when `y` is a
regular value. His proof produces, around each point `x ∈ f⁻¹(y)`, a diffeomorphism `F` from a
neighbourhood `U` of `x` onto an open set `V ⊆ N × ℝᵐ⁻ⁿ` under which "`f⁻¹(y)` corresponds to
the hyperplane `y × ℝᵐ⁻ⁿ ∩ V`". He then says "This proves that `f⁻¹(y)` is a smooth manifold of
dimension `m - n`", which for a subset of `ℝᵏ` is immediate from the definition.

For Mathlib's abstract manifolds one must actually build the charted-space structure on the
subset. This file does that once and for all:

* `SliceChart I Z W S`: a diffeomorphism `φ` from an open subset of `M` onto an open subset of
  `Z × W`, under which `S` corresponds to `Z × {0}` (Milnor's `F`, with `Z = ℝᵐ⁻ⁿ` and `W = N`
  read in a chart);
* `IsSliceSubmanifold I Z W S`: every point of `S` lies in the domain of a slice chart;
* `SliceChart.toChart`: the induced chart of `S`, namely `p ↦ (φ p).1`;
* `IsSliceSubmanifold.chartedSpace`, `IsSliceSubmanifold.isManifold`: `S`, with its subspace
  topology, is a smooth manifold modelled on `Z`;
* `IsSliceSubmanifold.contMDiff_val`: the inclusion `S → M` is smooth.

The construction uses Mathlib's `PartialDiffeomorph` (from the file on local diffeomorphisms),
which is exactly "a diffeomorphism between open subsets".
-/

open Set Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

section restr

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {n : WithTop ℕ∞}

theorem _root_.PartialDiffeomorph.invFun_apply (Φ : PartialDiffeomorph I J M N n) {x : M}
    (hx : x ∈ Φ.source) : Φ.invFun (Φ x) = x :=
  Φ.toPartialEquiv.left_inv hx

theorem _root_.PartialDiffeomorph.apply_invFun (Φ : PartialDiffeomorph I J M N n) {y : N}
    (hy : y ∈ Φ.target) : Φ (Φ.invFun y) = y :=
  Φ.toPartialEquiv.right_inv hy

theorem _root_.PartialDiffeomorph.invFun_mem (Φ : PartialDiffeomorph I J M N n) {y : N}
    (hy : y ∈ Φ.target) : Φ.invFun y ∈ Φ.source :=
  Φ.toPartialEquiv.map_target hy

theorem _root_.PartialDiffeomorph.apply_mem (Φ : PartialDiffeomorph I J M N n) {x : M}
    (hx : x ∈ Φ.source) : Φ x ∈ Φ.target :=
  Φ.toPartialEquiv.map_source hx

/-- Restriction of a partial diffeomorphism to an open subset of its source. -/
def _root_.PartialDiffeomorph.restrOpen (Φ : PartialDiffeomorph I J M N n) (s : Set M)
    (hs : IsOpen s) : PartialDiffeomorph I J M N n where
  toFun := Φ.toFun
  invFun := Φ.invFun
  source := Φ.source ∩ s
  target := Φ.toFun '' (Φ.source ∩ s)
  map_source' := fun _ hx => mem_image_of_mem _ hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Φ.invFun_apply hx.1]
    exact hx
  left_inv' := fun _ hx => Φ.invFun_apply hx.1
  right_inv' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Φ.invFun_apply hx.1]
  open_source := Φ.open_source.inter hs
  open_target :=
    (Φ.toOpenPartialHomeomorph.isOpen_image_iff_of_subset_source inter_subset_left).2
      (Φ.open_source.inter hs)
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono (by
    rintro _ ⟨x, hx, rfl⟩
    exact Φ.apply_mem hx.1)

@[simp] theorem _root_.PartialDiffeomorph.restrOpen_source (Φ : PartialDiffeomorph I J M N n)
    (s : Set M) (hs : IsOpen s) : (Φ.restrOpen s hs).source = Φ.source ∩ s := rfl

@[simp] theorem _root_.PartialDiffeomorph.restrOpen_apply (Φ : PartialDiffeomorph I J M N n)
    (s : Set M) (hs : IsOpen s) (x : M) : (Φ.restrOpen s hs) x = Φ x := rfl

end restr

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A **slice chart** for `S ⊆ M`: a diffeomorphism `φ` from an open subset of `M` onto an open
subset of `Z × W` such that, on its domain, `S` corresponds exactly to `Z × {0}`. It comes with a
base point `x₀ ∈ S` in its domain. -/
structure SliceChart (S : Set M) where
  φ : PartialDiffeomorph I 𝓘(ℝ, Z × W) M (Z × W) ∞
  x₀ : M
  x₀_mem : x₀ ∈ S
  x₀_source : x₀ ∈ φ.source
  slice : ∀ p ∈ φ.source, p ∈ S ↔ (φ p).2 = 0

/-- `S` is a submanifold modelled on `Z` if every point of `S` lies in the domain of a slice
chart. -/
def IsSliceSubmanifold (S : Set M) : Prop :=
  ∀ p ∈ S, ∃ σ : SliceChart I Z W S, p ∈ σ.φ.source

variable {I Z W}

namespace SliceChart

variable {S : Set M} (σ : SliceChart I Z W S)

theorem symm_mem (z : Z) (hz : (z, (0 : W)) ∈ σ.φ.target) : σ.φ.invFun (z, 0) ∈ S := by
  have h1 : σ.φ.invFun (z, 0) ∈ σ.φ.source := σ.φ.invFun_mem hz
  rw [σ.slice _ h1, σ.φ.apply_invFun hz]

open Classical in
/-- The inverse of the induced chart, as a map `Z → S` (with a junk value outside the target). -/
def invChart (z : Z) : S :=
  if h : (z, (0 : W)) ∈ σ.φ.target then ⟨σ.φ.invFun (z, 0), σ.symm_mem z h⟩ else ⟨σ.x₀, σ.x₀_mem⟩

theorem invChart_of_mem {z : Z} (h : (z, (0 : W)) ∈ σ.φ.target) :
    (σ.invChart z : M) = σ.φ.invFun (z, 0) := by
  simp [invChart, h]

theorem mk_zero_mem_target {p : M} (hp : p ∈ σ.φ.source) (hpS : p ∈ S) :
    ((σ.φ p).1, (0 : W)) ∈ σ.φ.target := by
  have h2 : (σ.φ p).2 = 0 := (σ.slice p hp).1 hpS
  have : ((σ.φ p).1, (0 : W)) = σ.φ p := Prod.ext rfl h2.symm
  rw [this]
  exact σ.φ.apply_mem hp

/-- The chart of `S` induced by a slice chart: `p ↦ (φ p).1`. -/
def toChart : OpenPartialHomeomorph S Z where
  toFun q := (σ.φ q.1).1
  invFun := σ.invChart
  source := {q | q.1 ∈ σ.φ.source}
  target := {z | (z, (0 : W)) ∈ σ.φ.target}
  map_source' q hq := σ.mk_zero_mem_target hq q.2
  map_target' z hz := by
    show (σ.invChart z : M) ∈ σ.φ.source
    rw [σ.invChart_of_mem hz]
    exact σ.φ.invFun_mem hz
  left_inv' q hq := by
    apply Subtype.ext
    rw [σ.invChart_of_mem (σ.mk_zero_mem_target hq q.2)]
    have h2 : (σ.φ q.1).2 = 0 := (σ.slice q.1 hq).1 q.2
    have : ((σ.φ q.1).1, (0 : W)) = σ.φ q.1 := Prod.ext rfl h2.symm
    rw [this]
    exact σ.φ.invFun_apply hq
  right_inv' z hz := by
    show (σ.φ (σ.invChart z : M)).1 = z
    rw [σ.invChart_of_mem hz, σ.φ.apply_invFun hz]
  open_source := σ.φ.open_source.preimage continuous_subtype_val
  open_target := σ.φ.open_target.preimage (continuous_id.prodMk continuous_const)
  continuousOn_toFun := by
    have h1 : ContinuousOn (fun q : S => σ.φ q.1) {q | q.1 ∈ σ.φ.source} :=
      σ.φ.contMDiffOn.continuousOn.comp continuous_subtype_val.continuousOn fun q hq => hq
    exact continuous_fst.comp_continuousOn h1
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict]
    have hfun : {z | (z, (0 : W)) ∈ σ.φ.target}.domRestrict σ.invChart =
        fun z => ⟨σ.φ.invFun (z.1, 0), σ.symm_mem z.1 z.2⟩ := by
      funext z
      apply Subtype.ext
      exact σ.invChart_of_mem z.2
    rw [hfun]
    apply Continuous.subtype_mk
    exact σ.φ.contMDiffOn_invFun.continuousOn.comp_continuous
      (continuous_subtype_val.prodMk continuous_const) fun z => z.2

@[simp] theorem toChart_source : σ.toChart.source = {q | q.1 ∈ σ.φ.source} := rfl
@[simp] theorem toChart_target : σ.toChart.target = {z | (z, (0 : W)) ∈ σ.φ.target} := rfl
@[simp] theorem toChart_apply (q : S) : σ.toChart q = (σ.φ q.1).1 := rfl
theorem toChart_symm_apply {z : Z} (hz : (z, (0 : W)) ∈ σ.φ.target) :
    (σ.toChart.symm z : M) = σ.φ.invFun (z, 0) := σ.invChart_of_mem hz

end SliceChart

namespace IsSliceSubmanifold

variable {S : Set M} (hS : IsSliceSubmanifold I Z W S)

/-- The charted-space structure on a slice submanifold. -/
def chartedSpace : ChartedSpace Z S where
  atlas := {e | ∃ σ : SliceChart I Z W S, e = σ.toChart}
  chartAt p := (hS p.1 p.2).choose.toChart
  mem_chart_source p := (hS p.1 p.2).choose_spec
  chart_mem_atlas _ := ⟨_, rfl⟩

theorem chartAt_eq (p : S) :
    @chartAt Z _ S _ hS.chartedSpace p = (hS p.1 p.2).choose.toChart := rfl

theorem mem_atlas_iff (e : OpenPartialHomeomorph S Z) :
    e ∈ @atlas Z _ S _ hS.chartedSpace ↔ ∃ σ : SliceChart I Z W S, e = σ.toChart := Iff.rfl

/-- The transition map between two slice charts, `z ↦ (φ₂ (φ₁⁻¹ (z, 0))).1`, is smooth. -/
theorem contDiffOn_trans (σ₁ σ₂ : SliceChart I Z W S) :
    ContDiffOn ℝ ∞ (σ₁.toChart.symm ≫ₕ σ₂.toChart) (σ₁.toChart.symm ≫ₕ σ₂.toChart).source := by
  set T := (σ₁.toChart.symm ≫ₕ σ₂.toChart).source with hT
  have hT' : ∀ z ∈ T, (z, (0 : W)) ∈ σ₁.φ.target ∧ σ₁.φ.invFun (z, 0) ∈ σ₂.φ.source := by
    intro z hz
    rw [hT, OpenPartialHomeomorph.trans_source] at hz
    obtain ⟨hz1, hz2⟩ := hz
    refine ⟨hz1, ?_⟩
    have := hz2
    rw [mem_preimage, SliceChart.toChart_source, mem_setOf_eq] at this
    rwa [σ₁.toChart_symm_apply hz1] at this
  -- The composite `φ₂ ∘ φ₁⁻¹` is smooth on `φ₁.target ∩ φ₁⁻¹ ⁻¹' φ₂.source`.
  have h1 : ContMDiffOn 𝓘(ℝ, Z × W) 𝓘(ℝ, Z × W) ∞ (σ₂.φ ∘ σ₁.φ.invFun)
      (σ₁.φ.target ∩ σ₁.φ.invFun ⁻¹' σ₂.φ.source) :=
    σ₂.φ.contMDiffOn.comp (σ₁.φ.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right
  rw [contMDiffOn_iff_contDiffOn] at h1
  have h2 : ContDiffOn ℝ ∞ (fun z : Z => (z, (0 : W))) T :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have h3 : ContDiffOn ℝ ∞ (fun z : Z => σ₂.φ (σ₁.φ.invFun (z, 0))) T :=
    h1.comp h2 fun z hz => hT' z hz
  have h4 : ContDiffOn ℝ ∞ (fun z : Z => (σ₂.φ (σ₁.φ.invFun (z, 0))).1) T :=
    contDiff_fst.comp_contDiffOn h3
  refine h4.congr fun z hz => ?_
  rw [OpenPartialHomeomorph.trans_apply, SliceChart.toChart_apply, σ₁.toChart_symm_apply (hT' z hz).1]

/-- A slice submanifold is a smooth manifold. -/
theorem isManifold : letI := hS.chartedSpace; IsManifold 𝓘(ℝ, Z) ∞ S := by
  letI := hS.chartedSpace
  refine isManifold_of_contDiffOn 𝓘(ℝ, Z) ∞ S ?_
  intro e e' he he'
  obtain ⟨σ₁, rfl⟩ := he
  obtain ⟨σ₂, rfl⟩ := he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.inter_univ, Set.preimage_id_eq, id_eq, CompTriple.comp_eq]
  exact IsSliceSubmanifold.contDiffOn_trans σ₁ σ₂

/-- The inclusion of a slice submanifold is smooth. -/
theorem contMDiff_val : letI := hS.chartedSpace; ContMDiff 𝓘(ℝ, Z) I ∞ (Subtype.val : S → M) := by
  letI := hS.chartedSpace
  haveI := hS.isManifold
  intro p
  set σ := (hS p.1 p.2).choose with hσ
  have hpσ : p.1 ∈ σ.φ.source := (hS p.1 p.2).choose_spec
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  -- The chart of `S` at `p` is `σ.toChart`; the composite is `extChartAt I p ∘ φ⁻¹ ∘ (·, 0)`
  -- near `(φ p).1`.
  have hchart : extChartAt 𝓘(ℝ, Z) p = σ.toChart.toPartialEquiv := by
    rw [extChartAt, hS.chartAt_eq, ← hσ, OpenPartialHomeomorph.extend,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl]
  rw [hchart]
  simp only [modelWithCornersSelf_coe, Set.range_id]
  rw [contDiffWithinAt_univ]
  -- Smoothness of `extChartAt I p ∘ φ⁻¹` near `(z₀, 0)`.
  set z₀ := (σ.φ p.1).1 with hz₀
  have hz₀mem : (z₀, (0 : W)) ∈ σ.φ.target := σ.mk_zero_mem_target hpσ p.2
  have hU : IsOpen (σ.φ.target ∩ σ.φ.invFun ⁻¹' (extChartAt I p.1).source) :=
    σ.φ.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage σ.φ.open_target
      (isOpen_extChartAt_source p.1)
  have hz₀U : (z₀, (0 : W)) ∈ σ.φ.target ∩ σ.φ.invFun ⁻¹' (extChartAt I p.1).source := by
    refine ⟨hz₀mem, ?_⟩
    show σ.φ.invFun (z₀, 0) ∈ (extChartAt I p.1).source
    have h2 : (σ.φ p.1).2 = 0 := (σ.slice p.1 hpσ).1 p.2
    have : (z₀, (0 : W)) = σ.φ p.1 := Prod.ext rfl h2.symm
    rw [this, σ.φ.invFun_apply hpσ]
    exact mem_extChartAt_source p.1
  have h1 : ContMDiffOn 𝓘(ℝ, Z × W) 𝓘(ℝ, E) ∞ (extChartAt I p.1 ∘ σ.φ.invFun)
      (σ.φ.target ∩ σ.φ.invFun ⁻¹' (extChartAt I p.1).source) :=
    (contMDiffOn_extChartAt (n := ∞)).comp (σ.φ.contMDiffOn_invFun.mono inter_subset_left)
      (by
        intro w hw
        rw [extChartAt_source] at hw
        exact hw.2)
  rw [contMDiffOn_iff_contDiffOn] at h1
  have h2' : ContDiffAt ℝ ∞ (extChartAt I p.1 ∘ σ.φ.invFun) (z₀, (0 : W)) :=
    h1.contDiffAt (hU.mem_nhds hz₀U)
  have h3 : ContDiffAt ℝ ∞ (fun z : Z => (z, (0 : W))) z₀ :=
    (contDiff_id.prodMk contDiff_const).contDiffAt
  have h2 := h2'.comp z₀ h3
  refine h2.congr_of_eventuallyEq ?_
  have hopen : IsOpen {z : Z | (z, (0 : W)) ∈ σ.φ.target} :=
    σ.φ.open_target.preimage (continuous_id.prodMk continuous_const)
  filter_upwards [hopen.mem_nhds hz₀mem] with z hz
  show extChartAt I p.1 ((σ.toChart.symm z : S) : M) = extChartAt I p.1 (σ.φ.invFun (z, 0))
  rw [σ.toChart_symm_apply hz]

end IsSliceSubmanifold

end Milnor
