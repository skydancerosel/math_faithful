import Milnor.Chapter2.Brown

/-!
Milnor, *Morse Theory*, §6, p. 33.

# Sard's theorem on a manifold (Theorem 6.1)

Milnor, p. 33, paraphrased: if `M₁` and `M₂` are manifolds with countable bases, of the same
dimension, and `f : M₁ → M₂` is of class `C¹`, then the image of the set of critical points
(the points where the Jacobian of `f` is singular) has measure `0` in `M₂`.  Milnor does not
prove it; he cites de Rham, *Variétés différentiables*, p. 10.

## What is proved here

Milnor uses Theorem 6.1 only once, for the endpoint map `E : N → ℝⁿ` of the normal bundle
(Corollary 6.2, `Morse/Chapter4/Focal.lean`), and the target is a vector space.  We prove that
case, for smooth maps; the version on an open subset `U` is used for the maps
`(q, v) ↦ −∇F(q) + v`, defined only over the domain of a local extension `F`, in the proof of
Corollary 6.8 (`Morse/Chapter4/Approximation.lean`):

* `Morse.measure_image_inter_critPoints_eq_zero`: let `M` be a second countable smooth manifold
  without boundary modelled on a finite-dimensional real space `E`, `F` a finite-dimensional
  real normed space with a Haar measure `μ`, `U ⊆ M` open and `f : M → F` smooth on `U`.  Then
  `μ (f (U ∩ C)) = 0`, `C` being the set of points where `df` is not surjective
  (`Milnor.critPoints`).
* `Morse.measure_image_critPoints_eq_zero`: the case `U = M`.

The dimensions need not be equal.  The proof is the one the companion project gives for the
theorem of A. B. Brown (`Milnor.dense_regularValues`, which only records density of the regular
values): cover `U` by countably many charts and apply the Euclidean Sard theorem
(`Milnor.sard`) to `f` read in each chart.  The critical points of `f` in a chart are critical
points of the chart representative by the chain rule, the derivative of a chart being an
isomorphism.

## Gaps in Milnor's text

* "`C¹`" would need the full strength of Sard's theorem in equal dimensions; the companion
  project proves Sard's theorem for smooth (`C^∞`) maps only.  Every map to which Milnor applies
  Theorem 6.1 is smooth, so nothing is lost.
* "Measure `0` in `M₂`" needs `M₂` to carry a measure class; for `M₂ = ℝⁿ` (the only case used)
  it is the Lebesgue measure, and the statement holds for every Haar measure.
* The countable basis of `M₁` is what allows the countable chart cover; for the normal bundle it
  is automatic, `N` being a subset of `ℝ²ⁿ`.
-/

open Set Filter Topology Function MeasureTheory Module
open scoped ContDiff Manifold

noncomputable section

namespace Morse

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {f : M → F}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- A critical point of `f` lying in the source of the chart at `x₀` is, in that chart, a critical
point of the chart representative `f ∘ φ⁻¹` (chain rule; the derivative of the inverse chart is
an isomorphism).  Local version of `Milnor.mem_critSet_of_mem_critPoints`. -/
theorem mem_critSet_of_mem_critPoints_of_mdifferentiableAt {U : Set M} {x₀ x : M}
    (hfx : MDifferentiableAt I 𝓘(ℝ, F) f x) (hxU : x ∈ U)
    (hx : x ∈ Milnor.critPoints I 𝓘(ℝ, F) f) (hxφ : x ∈ (extChartAt I x₀).source) :
    extChartAt I x₀ x ∈ Milnor.Sard.critSet (f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' U) := by
  set φ := extChartAt I x₀ with hφ
  have hxx : φ.symm (φ x) = x := φ.left_inv hxφ
  refine ⟨⟨φ.map_source hxφ, by rw [mem_preimage, hxx]; exact hxU⟩, fun hsurj => hx ?_⟩
  have hφ' : MDifferentiableAt 𝓘(ℝ, E) I φ.symm (φ x) :=
    mdifferentiableOn_extChartAt_symm.mdifferentiableAt
      ((isOpen_extChartAt_target x₀).mem_nhds (φ.map_source hxφ))
  have hf' : MDifferentiableAt I 𝓘(ℝ, F) f (φ.symm (φ x)) := by rwa [hxx]
  have hchain : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (f ∘ φ.symm) (φ x) =
      (mfderiv I 𝓘(ℝ, F) f (φ.symm (φ x))).comp (mfderiv 𝓘(ℝ, E) I φ.symm (φ x)) :=
    mfderiv_comp (φ x) hf' hφ'
  rw [← mfderiv_eq_fderiv, hchain] at hsurj
  have : Surjective (mfderiv I 𝓘(ℝ, F) f (φ.symm (φ x))) :=
    Function.Surjective.of_comp (g := mfderiv 𝓘(ℝ, E) I φ.symm (φ x)) hsurj
  rw [hxx] at this
  exact this

variable [MeasurableSpace F] [BorelSpace F]

/-- **Sard's theorem on a manifold** (Milnor, Theorem 6.1, p. 33, for smooth maps into a vector
space).  If `M` is second countable and `f : M → F` is smooth on the open set `U ⊆ M`, the image of
the critical points of `f` in `U` is a null set for every Haar measure on `F`. -/
theorem measure_image_inter_critPoints_eq_zero (μ : Measure F) [μ.IsAddHaarMeasure]
    [SecondCountableTopology M] {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U) :
    μ (f '' (U ∩ Milnor.critPoints I 𝓘(ℝ, F) f)) = 0 := by
  -- Countably many charts cover `U`.
  obtain ⟨t, -, ht_count, ht_cover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x : M => (chartAt H x).source) (s := U)
    fun x _ => mem_nhdsWithin_of_mem_nhds
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  -- Sard's theorem in each chart.
  have hnull : ∀ x₀ : M, μ ((f ∘ (extChartAt I x₀).symm) ''
      Milnor.Sard.critSet (f ∘ (extChartAt I x₀).symm)
        ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' U)) = 0 := by
    intro x₀
    have hU' : IsOpen ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' U) :=
      (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage (isOpen_extChartAt_target x₀) hU
    have hsmooth := (contMDiffOn_iff.1 hf).2 x₀ (f x₀)
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_source, preimage_univ,
      inter_univ, PartialEquiv.refl_coe, CompTriple.comp_eq] at hsmooth
    exact Milnor.sard μ hU' hsmooth
  refine measure_mono_null ?_ ((measure_biUnion_null_iff ht_count).2 fun x₀ _ => hnull x₀)
  rintro _ ⟨x, ⟨hxU, hx⟩, rfl⟩
  obtain ⟨x₀, hx₀t, hxx₀⟩ := mem_iUnion₂.1 (ht_cover hxU)
  have hxφ : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  have hfx : MDifferentiableAt I 𝓘(ℝ, F) f x :=
    ((hf x hxU).contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
  refine mem_iUnion₂.2 ⟨x₀, hx₀t, extChartAt I x₀ x,
    mem_critSet_of_mem_critPoints_of_mdifferentiableAt hfx hxU hx hxφ, ?_⟩
  simp only [comp_apply, (extChartAt I x₀).left_inv hxφ]

/-- **Sard's theorem on a manifold**, global form: for `f : M → F` smooth on a second countable
manifold, the critical values form a null set for every Haar measure on `F`. -/
theorem measure_image_critPoints_eq_zero (μ : Measure F) [μ.IsAddHaarMeasure]
    [SecondCountableTopology M] (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) :
    μ (f '' Milnor.critPoints I 𝓘(ℝ, F) f) = 0 := by
  have h := measure_image_inter_critPoints_eq_zero μ isOpen_univ hf.contMDiffOn
  rwa [univ_inter] at h

end Morse
