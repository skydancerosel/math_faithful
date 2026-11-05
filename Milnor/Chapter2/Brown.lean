import Milnor.Chapter3.Sard
import Milnor.Chapter1.Counting

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §2, pp. 10–11.

# The theorem of Sard and Brown

> More generally consider a smooth map `f : M → N`, from a manifold of dimension `m` to a manifold
> of dimension `n`. Let `C` be the set of all `x ∈ M` such that `dfₓ : TMₓ → TN_{f(x)}` has rank
> less than `n` (i.e. is not onto). Then `C` will be called the set of critical points, `f(C)` the
> set of critical values, and the complement `N ∖ f(C)` the set of regular values of `f`. (This
> agrees with our previous definitions in the case `m = n`.) Since `M` can be covered by a
> countable collection of neighborhoods each diffeomorphic to an open subset of `ℝᵐ`, we have
>
> **Corollary (A. B. Brown).** The set of regular values of a smooth map `f : M → N` is everywhere
> dense in `N`.

The hypothesis hidden in "can be covered by a countable collection" is that `M` is second
countable, which we assume. The proof: given a nonempty open `W ⊆ N`, take a chart `ψ` of `N`
meeting `W`, and countably many charts `φᵢ` of `M` covering `M`. In each pair of charts `f` becomes
a smooth map `ψ ∘ f ∘ φᵢ⁻¹` between open subsets of Euclidean spaces, whose critical points
correspond to those of `f` (chain rule; the chart derivatives are isomorphisms). By Sard's theorem
each `ψ(f(C) ∩ ψ.source)` is a countable union of null sets, hence null, hence cannot contain the
nonempty open set `ψ(W ∩ ψ.source)`.
-/

open Set Filter Topology Function MeasureTheory Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G} [I.Boundaryless] [J.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {f : M → N}

variable (I J) in
/-- Milnor's `C` on a manifold: the set of points where `dfₓ` is not onto (p. 10). -/
def critPoints (f : M → N) : Set M := {x | ¬ Surjective (mfderiv I J f x)}

omit [MeasurableSpace F] [BorelSpace F] in
/-- The regular values are the complement of the critical values. -/
theorem regularValues_eq_compl_image_critPoints (f : M → N) :
    regularValues I J f = (f '' critPoints I J f)ᶜ := by
  ext y
  simp only [regularValues, IsRegularValue, IsRegularPoint, critPoints, mem_setOf_eq,
    mem_compl_iff, mem_image, not_exists, not_and]
  constructor
  · intro h x hx hfx
    exact hx (h x hfx)
  · intro h x hfx
    by_contra hx
    exact h x hx hfx

omit [MeasurableSpace F] [BorelSpace F] in
/-- The derivative of a chart of `N` at a point of its source is injective (it has the derivative
of the inverse chart as a left inverse). -/
theorem mfderiv_extChartAt_injective {y₁ y : N} (hy : y ∈ (extChartAt J y₁).source) :
    Injective (mfderiv J 𝓘(ℝ, F) (extChartAt J y₁) y) := by
  set ψ := extChartAt J y₁ with hψ
  have hψ' : MDifferentiableAt J 𝓘(ℝ, F) ψ y :=
    mdifferentiableAt_extChartAt (by rwa [extChartAt_source] at hy)
  have hψs : MDifferentiableAt 𝓘(ℝ, F) J ψ.symm (ψ y) :=
    mdifferentiableOn_extChartAt_symm.mdifferentiableAt
      ((isOpen_extChartAt_target y₁).mem_nhds (ψ.map_source hy))
  have hcomp : mfderiv J J (ψ.symm ∘ ψ) y =
      (mfderiv 𝓘(ℝ, F) J ψ.symm (ψ y)).comp (mfderiv J 𝓘(ℝ, F) ψ y) :=
    mfderiv_comp y hψs hψ'
  have hid : mfderiv J J (ψ.symm ∘ ψ) y = mfderiv J J id y := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [(isOpen_extChartAt_source y₁).mem_nhds hy] with z hz
    exact ψ.left_inv hz
  rw [mfderiv_id] at hid
  have key : ∀ v, mfderiv 𝓘(ℝ, F) J ψ.symm (ψ y) (mfderiv J 𝓘(ℝ, F) ψ y v) = v := fun v =>
    DFunLike.congr_fun (hcomp.symm.trans hid) v
  intro v w hvw
  have h1 := key v
  have h2 := key w
  rw [← h1, ← h2, hvw]

omit [MeasurableSpace F] [BorelSpace F] in
/-- A critical point of `f` is, in charts, a critical point of the chart representation of `f`.
Chain rule: `d(ψ ∘ f ∘ φ⁻¹) = dψ ∘ df ∘ d(φ⁻¹)` with `dψ` injective. -/
theorem mem_critSet_of_mem_critPoints (hf : ContMDiff I J ∞ f) {x₀ : M} {y₁ : N} {x : M}
    (hx : x ∈ critPoints I J f) (hxφ : x ∈ (extChartAt I x₀).source)
    (hyψ : f x ∈ (extChartAt J y₁).source) :
    extChartAt I x₀ x ∈ Sard.critSet (extChartAt J y₁ ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' (f ⁻¹' (extChartAt J y₁).source)) := by
  set φ := extChartAt I x₀ with hφ
  set ψ := extChartAt J y₁ with hψ
  have hxx : φ.symm (φ x) = x := φ.left_inv hxφ
  refine ⟨⟨φ.map_source hxφ, by rw [mem_preimage, hxx]; exact hyψ⟩, fun hsurj => hx ?_⟩
  -- Differentiability of the three factors.
  have hφ' : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ x) :=
    mdifferentiableOn_extChartAt_symm.mdifferentiableAt
      ((isOpen_extChartAt_target x₀).mem_nhds (φ.map_source hxφ))
  have hf' : MDifferentiableAt I J f (φ.symm (φ x)) := by
    rw [hxx]; exact hf.mdifferentiableAt (by simp)
  have hψ' : MDifferentiableAt J 𝓘(ℝ, F) ψ (f (φ.symm (φ x))) := by
    rw [hxx]; exact mdifferentiableAt_extChartAt (by rwa [extChartAt_source] at hyψ)
  -- Chain rule.
  have hchain : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (ψ ∘ f ∘ φ.symm) (φ x) =
      (mfderiv J 𝓘(ℝ, F) ψ (f (φ.symm (φ x)))).comp
        ((mfderiv I J f (φ.symm (φ x))).comp (mfderiv 𝓘(ℝ, E) I φ.symm (φ x))) := by
    rw [mfderiv_comp (φ x) hψ' (hf'.comp (φ x) hφ'), mfderiv_comp (φ x) hf' hφ']
    rfl
  rw [← mfderiv_eq_fderiv, hchain] at hsurj
  -- Extract surjectivity of the middle factor.
  have hinj : Injective (mfderiv J 𝓘(ℝ, F) ψ (f (φ.symm (φ x)))) := by
    rw [hxx]; exact mfderiv_extChartAt_injective hyψ
  have hsurj' : Surjective ((mfderiv I J f (φ.symm (φ x))).comp
      (mfderiv 𝓘(ℝ, E) I φ.symm (φ x))) := by
    intro w
    obtain ⟨v, hv⟩ := hsurj (mfderiv J 𝓘(ℝ, F) ψ (f (φ.symm (φ x))) w)
    exact ⟨v, hinj hv⟩
  have : Surjective (mfderiv I J f (φ.symm (φ x))) := by
    rw [ContinuousLinearMap.coe_comp] at hsurj'
    exact hsurj'.of_comp
  rw [hxx] at this
  exact this

omit [MeasurableSpace F] [BorelSpace F] in
/-- **Brown's theorem** (Milnor p. 11): the regular values of a smooth map `f : M → N` between
manifolds without boundary, `M` second countable, are dense in `N`. -/
theorem dense_regularValues [SecondCountableTopology M] (hf : ContMDiff I J ∞ f) :
    Dense (regularValues I J f) := by
  borelize F
  rw [regularValues_eq_compl_image_critPoints, dense_iff_inter_open]
  rintro W hW ⟨y₁, hy₁⟩
  by_contra hcon
  rw [not_nonempty_iff_eq_empty] at hcon
  have hWsub : W ⊆ f '' critPoints I J f := fun y hy => by
    by_contra h
    exact (eq_empty_iff_forall_notMem.1 hcon) y ⟨hy, h⟩
  set ψ := extChartAt J y₁ with hψ
  -- Countably many charts cover `M`.
  obtain ⟨s, hs_count, hs_cover⟩ := TopologicalSpace.countable_cover_nhds
    (f := fun x : M => (chartAt H x).source)
    fun x => (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  -- A Haar measure on `F`.
  let μ : Measure F := (Module.Basis.ofVectorSpace ℝ F).addHaar
  -- Sard's theorem in each pair of charts.
  have hnull : ∀ x₀ : M, μ ((ψ ∘ f ∘ (extChartAt I x₀).symm) ''
      Sard.critSet (ψ ∘ f ∘ (extChartAt I x₀).symm)
        ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' (f ⁻¹' ψ.source))) = 0 := by
    intro x₀
    have hU : IsOpen ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' (f ⁻¹' ψ.source)) :=
      (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage (isOpen_extChartAt_target x₀)
        (hf.continuous.isOpen_preimage _ (isOpen_extChartAt_source y₁))
    have hsmooth := (contMDiffOn_iff.1 (hf.contMDiffOn (s := univ))).2 x₀ y₁
    rw [univ_inter] at hsmooth
    exact sard μ hU hsmooth
  -- `ψ(W ∩ ψ.source)` is contained in the countable union of these null sets.
  have hincl : ψ '' (W ∩ ψ.source) ⊆ ⋃ x₀ ∈ s, (ψ ∘ f ∘ (extChartAt I x₀).symm) ''
      Sard.critSet (ψ ∘ f ∘ (extChartAt I x₀).symm)
        ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' (f ⁻¹' ψ.source)) := by
    rintro _ ⟨y, ⟨hyW, hyψ⟩, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hWsub hyW
    have hxs : x ∈ ⋃ x₀ ∈ s, (chartAt H x₀).source := by rw [hs_cover]; exact mem_univ x
    obtain ⟨x₀, hx₀s, hxx₀⟩ := mem_iUnion₂.1 hxs
    have hxφ : x ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hxx₀
    refine mem_iUnion₂.2 ⟨x₀, hx₀s, extChartAt I x₀ x,
      mem_critSet_of_mem_critPoints hf hx hxφ hyψ, ?_⟩
    show ψ (f ((extChartAt I x₀).symm (extChartAt I x₀ x))) = ψ (f x)
    rw [(extChartAt I x₀).left_inv hxφ]
  -- But `ψ(W ∩ ψ.source)` is a neighbourhood of `ψ y₁`, hence has positive measure.
  have hnhds : ψ '' (W ∩ ψ.source) ∈ 𝓝 (ψ y₁) :=
    extChartAt_image_nhds_mem_nhds_of_boundaryless
      (inter_mem (hW.mem_nhds hy₁) (extChartAt_source_mem_nhds y₁))
  have hpos : 0 < μ (ψ '' (W ∩ ψ.source)) :=
    Measure.measure_pos_of_nonempty_interior (μ := μ) ⟨_, mem_interior_iff_mem_nhds.2 hnhds⟩
  have hzero : μ (ψ '' (W ∩ ψ.source)) = 0 :=
    measure_mono_null hincl ((measure_biUnion_null_iff hs_count).2 fun x₀ _ => hnull x₀)
  exact hpos.ne' hzero

end Milnor
