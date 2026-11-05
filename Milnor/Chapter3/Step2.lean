import Milnor.Chapter3.Straighten
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §3, Step 2 (p. 18).

# Step 2: `f(Cₖ ∖ Cₖ₊₁)` has measure zero, for `k ≥ 1`

> For each `x̄ ∈ Cₖ ∖ Cₖ₊₁` there is some `(k+1)`-st derivative `∂^{k+1} f_r / ∂x_{s₁} ⋯ ∂x_{s_{k+1}}`
> which is not zero. Thus the function `w(x) = ∂^k f_r / ∂x_{s₂} ⋯ ∂x_{s_{k+1}}` vanishes at `x̄` but
> `∂w/∂x_{s₁}` does not. […] the map `h(x) = (w(x), x₂, …, xₙ)` carries some neighborhood `V` of
> `x̄` diffeomorphically onto an open set `V'`. Note that `h` carries `Cₖ ∩ V` into the hyperplane
> `0 × ℝⁿ⁻¹`. Again we consider `g = f ∘ h⁻¹ : V' → ℝᵖ`. Let `ḡ` denote the restriction of `g` to
> `(0 × ℝⁿ⁻¹) ∩ V'`. By induction, the set of critical values of `ḡ` has measure zero in `ℝᵖ`. But
> each point in `h(Cₖ ∩ V)` is certainly a critical point of `ḡ` (since all derivatives of order
> `≤ k` vanish). Therefore `ḡ h(Cₖ ∩ V) = f(Cₖ ∩ V)` has measure zero.

Coordinate-free: with `m = (m₀, m₁, …, mₖ)` vectors and `ℓ₀` a functional with
`ℓ₀(D^{k+1}f(x̄)(m)) ≠ 0`, take `w(x) = ℓ₀(Dᵏf(x)(m₁, …, mₖ))`. Then `w = 0` on `Cₖ`, and
`dw_x̄(m₀) = ℓ₀(D^{k+1}f(x̄)(m)) ≠ 0` (`iteratedFDeriv_succ_apply_left`).

This file also contains the countable-cover lemma that turns "each point of `S` has a
neighbourhood `V` with `f(T ∩ V)` null" into "`f(T ∩ S)` is null", which Milnor uses at the end of
each of Steps 1 and 2 ("Since `Cₖ ∖ Cₖ₊₁` is covered by countably many such sets `V` …").
-/

open Set Filter Topology Function MeasureTheory Module
open scoped ContDiff

noncomputable section

namespace Milnor

namespace Sard

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- If every point of `S` has a neighbourhood `V` with `μ (f '' (T ∩ V)) = 0`, then
`μ (f '' (T ∩ S)) = 0`. (Countably many such `V` cover `S`, since `E` is second countable.) -/
theorem measure_image_eq_zero_of_locally (μ : Measure F) {f : E → F} {S T : Set E}
    (h : ∀ x ∈ S, ∃ V ∈ 𝓝 x, μ (f '' (T ∩ V)) = 0) : μ (f '' (T ∩ S)) = 0 := by
  choose! V hV hVnull using h
  obtain ⟨t, htS, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin (s := S) (f := V)
    fun x hx => mem_nhdsWithin_of_mem_nhds (hV x hx)
  have hsub : f '' (T ∩ S) ⊆ ⋃ x ∈ t, f '' (T ∩ V x) := by
    rintro _ ⟨z, ⟨hzT, hzS⟩, rfl⟩
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcover hzS)
    exact mem_iUnion₂.2 ⟨x, hxt, mem_image_of_mem _ ⟨hzT, hzx⟩⟩
  refine measure_mono_null hsub ?_
  exact (measure_biUnion_null_iff htc).2 fun x hx => hVnull x (htS hx)

/-- A point of `Cₖ` (`k ≥ 1`) has vanishing derivative. -/
theorem fderiv_eq_zero_of_mem_vanishSet {f : E → F} {U : Set E} {k : ℕ} (hk : 1 ≤ k) {x : E}
    (hx : x ∈ vanishSet f U k) : fderiv ℝ f x = 0 := by
  have h := congrArg norm (hx.2 1 le_rfl hk)
  rwa [norm_iteratedFDeriv_one, norm_zero, norm_eq_zero] at h

/-- A point where the derivative vanishes is critical (for a nontrivial target). -/
theorem mem_critSet_of_fderiv_eq_zero [Nontrivial F] {f : E → F} {U : Set E} {x : E} (hx : x ∈ U)
    (h : fderiv ℝ f x = 0) : x ∈ critSet f U := by
  refine ⟨hx, fun hsurj => ?_⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  obtain ⟨v, hv⟩ := hsurj y
  rw [h] at hv
  exact hy (by simpa using hv.symm)

/-- `Dᵏf` is smooth on `U` when `f` is. -/
theorem contDiffOn_iteratedFDeriv {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) : ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k f) U := fun x hx =>
  ((hf.contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right (m := ∞) (i := k)
    (mod_cast le_top)).contDiffWithinAt

/-- **Step 2, local form** (Milnor p. 18). Assuming Sard's theorem in dimension `n - 1`, every
`x̄ ∈ Cₖ ∖ Cₖ₊₁` (`k ≥ 1`) has a neighbourhood `V` such that `f(Cₖ ∩ V)` has measure zero. -/
theorem step2_local (ih : SardStatement.{u} (finrank ℝ E - 1)) [Nontrivial F]
    (μ : Measure F) [μ.IsAddHaarMeasure] {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) {k : ℕ} (hk : 1 ≤ k) {x₀ : E}
    (hx₀ : x₀ ∈ vanishSet f U k \ vanishSet f U (k + 1)) :
    ∃ V ∈ 𝓝 x₀, μ (f '' (vanishSet f U k ∩ V)) = 0 := by
  have hx₀U : x₀ ∈ U := hx₀.1.1
  -- Some `(k+1)`-st derivative does not vanish at `x₀`.
  have hD : iteratedFDeriv ℝ (k + 1) f x₀ ≠ 0 := by
    intro h0
    apply hx₀.2
    refine ⟨hx₀U, fun j hj hjk => ?_⟩
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact hx₀.1.2 j hj (by omega)
    · have : j = k + 1 := by omega
      rw [this]; exact h0
  obtain ⟨m, hm⟩ : ∃ m : Fin (k + 1) → E, iteratedFDeriv ℝ (k + 1) f x₀ m ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (ContinuousMultilinearMap.ext h)
  obtain ⟨ℓ₀, -, hℓ₀⟩ := exists_dual_vector ℝ (iteratedFDeriv ℝ (k + 1) f x₀ m)
    (norm_ne_zero_iff.2 hm)
  have hℓ₀' : ℓ₀ (iteratedFDeriv ℝ (k + 1) f x₀ m) ≠ 0 := by
    rw [hℓ₀]; exact_mod_cast norm_ne_zero_iff.2 hm
  -- The function `w(x) = ℓ₀ (Dᵏf(x)(m₁, …, mₖ))`.
  set A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F →L[ℝ] ℝ :=
    ℓ₀.comp (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) F (Fin.tail m)) with hA
  set w : E → ℝ := fun x => A (iteratedFDeriv ℝ k f x) with hw_def
  have hw_smooth : ContDiffOn ℝ ∞ w U :=
    A.contDiff.comp_contDiffOn (contDiffOn_iteratedFDeriv hU hf k)
  have hw_deriv : fderiv ℝ w x₀ ≠ 0 := by
    have hDk : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x₀ :=
      ((contDiffOn_iteratedFDeriv hU hf k).contDiffAt (hU.mem_nhds hx₀U)).differentiableAt
        (by simp)
    have hcomp : HasFDerivAt w (A.comp (fderiv ℝ (iteratedFDeriv ℝ k f) x₀)) x₀ :=
      A.hasFDerivAt.comp x₀ hDk.hasFDerivAt
    rw [hcomp.fderiv]
    intro h0
    have := congrArg (fun L : E →L[ℝ] ℝ => L (m 0)) h0
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, hA,
      ContinuousMultilinearMap.apply_apply] at this
    rw [← iteratedFDeriv_succ_apply_left] at this
    exact hℓ₀' this
  have hw_zero : ∀ x ∈ vanishSet f U k, w x = 0 := fun x hx => by
    simp [hw_def, hx.2 k hk le_rfl]
  -- Straighten `w` near `x₀`.
  obtain ⟨S⟩ := exists_straightening hU hw_smooth hx₀U hw_deriv
  -- The restriction `ḡ` of `g = f ∘ G` to the hyperplane `{0} × K`.
  set V₀ : Set S.K := {z | ((0 : ℝ), z) ∈ S.V'} with hV₀
  have hV₀_open : IsOpen V₀ := S.isOpen_V'.preimage (continuous_const.prodMk continuous_id)
  set incl : S.K → ℝ × S.K := fun z => ((0 : ℝ), z) with hincl
  set gbar : S.K → F := fun z => f (S.G (incl z)) with hgbar
  have hgbar_smooth : ContDiffOn ℝ ∞ gbar V₀ := by
    have h1 : ContDiffOn ℝ ∞ incl V₀ := (contDiff_const.prodMk contDiff_id).contDiffOn
    have h2 : ContDiffOn ℝ ∞ (S.G ∘ incl) V₀ := S.contDiffOn_G.comp h1 fun z hz => hz
    exact hf.comp h2 fun z hz => S.V_subset (S.mapsTo_G hz)
  -- Induction hypothesis for `ḡ`.
  have hK : finrank ℝ S.K = finrank ℝ E - 1 := by have := S.finrank_K; omega
  have hnull : μ (gbar '' critSet gbar V₀) = 0 := ih S.K hK F μ V₀ hV₀_open gbar hgbar_smooth
  -- `f(Cₖ ∩ V) ⊆ ḡ(critical points of ḡ)`.
  refine ⟨S.V, S.isOpen_V.mem_nhds S.mem_V, measure_mono_null ?_ hnull⟩
  rintro _ ⟨x, ⟨hxC, hxV⟩, rfl⟩
  have hHx : S.H x = incl (S.H x).2 := by
    rw [hincl]
    ext
    · rw [S.H_fst, hw_zero x hxC]
    · rfl
  have hz : (S.H x).2 ∈ V₀ := by
    show incl (S.H x).2 ∈ S.V'
    rw [← hHx]
    exact S.mapsTo_H hxV
  refine ⟨(S.H x).2, ?_, ?_⟩
  · -- `(H x).2` is a critical point of `ḡ`, since `df_x = 0`.
    have hGx : S.G (incl (S.H x).2) = x := by rw [← hHx]; exact S.left_inv x hxV
    have hdf : fderiv ℝ f x = 0 := fderiv_eq_zero_of_mem_vanishSet hk hxC
    have hGdiff : DifferentiableAt ℝ (S.G ∘ incl) (S.H x).2 := by
      have h1 : DifferentiableAt ℝ incl (S.H x).2 :=
        (differentiableAt_const _).prodMk differentiableAt_id
      have h2 : DifferentiableAt ℝ S.G (incl (S.H x).2) :=
        (S.contDiffOn_G.contDiffAt (S.isOpen_V'.mem_nhds hz)).differentiableAt (by simp)
      exact h2.comp _ h1
    have hfdiff : DifferentiableAt ℝ f (S.G (incl (S.H x).2)) := by
      rw [hGx]
      exact (hf.contDiffAt (hU.mem_nhds hxC.1)).differentiableAt (by simp)
    have hchain : fderiv ℝ gbar (S.H x).2 =
        (fderiv ℝ f (S.G (incl (S.H x).2))).comp (fderiv ℝ (S.G ∘ incl) (S.H x).2) :=
      fderiv_comp _ hfdiff hGdiff
    rw [hGx, hdf] at hchain
    refine mem_critSet_of_fderiv_eq_zero hz ?_
    rw [hchain]
    simp
  · show f (S.G (incl (S.H x).2)) = f x
    rw [← hHx, S.left_inv x hxV]

end Sard

end Milnor
