import Morse.Chapter1.ManifoldSubmanifold

/-!
Milnor, *Morse Theory*, §22, Lemma 22.4 (pp. 119–121): a `C²`-small perturbation of a function
does not lower the index of its critical points near a compact set.

# Jiggling a function does not lower the index

## Milnor's text, paraphrased

(p. 119) Let `K` be a compact subset of an open set `U ⊆ ℝⁿ` and `f : U → ℝ` smooth, all of whose
critical points in `K` have index `≥ λ₀`.  **Lemma 22.4**: if `g : U → ℝ` is smooth and
`|∂g/∂xᵢ − ∂f/∂xᵢ| < ε`, `|∂²g/∂xᵢ∂xⱼ − ∂²f/∂xᵢ∂xⱼ| < ε` uniformly on `K`, for `ε` small enough,
then all critical points of `g` in `K` have index `≥ λ₀`.  (pp. 120–121) Milnor's proof: the
`λ`-th eigenvalue of the Hessian depends continuously on the matrix; with
`k_f = Σ|∂f/∂xᵢ|` the function `max(k_f, −e^{λ₀}_f)` is positive on `K`, hence `≥ δ > 0`, and "a
uniform continuity argument which will be left to the reader" finishes.

## What is formalized

* `Morse.lemma_22_4`: **Lemma 22.4**, in any finite-dimensional real normed space `E`, with the
  closeness of first and second derivatives measured by the operator norms of
  `dg − df` and `d²g − d²f` (equivalent to Milnor's partial derivatives up to constants), with
  `f` only `C²` and no regularity hypothesis on `g`.
* `Morse.lemma_22_4_add`: the same for `g = f + h`, closeness measured by `‖dh‖`, `‖d²h‖` (as
  `iteratedFDeriv`), the form in which approximation theorems (Corollary 6.8) deliver `g`.
* `Morse.lemma_22_4_submanifold`: **the version on a manifold** used in Lemma 22.5: for a slice
  submanifold `N ⊆ V`, `F : V → ℝ` smooth and `K ⊆ N` compact such that the critical points of
  `F|N` in `K` have index `≥ λ₀`, there is `δ > 0` such that for every linear `a : V → ℝ` with
  `‖a‖ < δ`, the critical points of `(F + a)|N` in `K` have index `≥ λ₀`.  (This is the
  perturbation by which `Morse.ae_isMorseFunction_add_inner_comp` produces Morse functions.)

## The proof

Not through eigenvalues: a critical point `x` of `f` with index `≥ λ₀` has a subspace `W`,
`dim W ≥ λ₀`, with `d²f_x(v, v) ≤ −μ‖v‖²` on `W` for some `μ > 0`
(`Morse.exists_negDef_margin`: compactness of the unit sphere of `W`); any bilinear form within
`μ` of `d²f_x` is still negative definite on `W`, so has index `≥ λ₀`
(`Morse.le_index_of_norm_sub_lt`).  At a non-critical point `x`, `dg_y ≠ 0` for `y` near `x` and
`dg` close to `df`.  Both conditions are open in `(ε, y)`, and the compactness of `K`
(`IsCompact.eventually_forall_of_forall_eventually`) gives a single `ε`.

## What Milnor leaves implicit

* The "uniform continuity argument" is the compactness argument above; no continuity of
  eigenvalues (Milnor's main text) or Courant–Fischer (his footnote) is needed, only the
  characterisation of the index as the largest dimension of a negative definite subspace
  (`Morse.index_isGreatest`).
* On a manifold, derivatives are only defined in charts: Milnor applies 22.4 "in a coordinate
  neighbourhood" of each point of a compact set; the version on a submanifold covers `K` by
  finitely many chart balls, and uses that the index at a critical point can be computed in any
  chart (`Morse.IsSmoothCoord.index_eq`).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold

noncomputable section

namespace Morse

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A negative definite form has a margin**: if `H(v, v) < 0` for `0 ≠ v ∈ W`, then
`H(v, v) ≤ −μ‖v‖²` on `W` for some `μ > 0`. -/
theorem exists_negDef_margin (H : E →L[ℝ] E →L[ℝ] ℝ) (W : Submodule ℝ E)
    (hW : ∀ v ∈ W, v ≠ 0 → H v v < 0) : ∃ μ > 0, ∀ v ∈ W, H v v ≤ -μ * ‖v‖ ^ 2 := by
  set S : Set E := (W : Set E) ∩ sphere 0 1 with hS_def
  have hSc : IsCompact S :=
    (isCompact_sphere 0 1).inter_left W.closed_of_finiteDimensional
  have hcont : Continuous fun v : E => H v v := by fun_prop
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun v hv => ?_⟩
    by_cases hv0 : v = 0
    · simp [hv0]
    exfalso
    have hmem : ‖v‖⁻¹ • v ∈ S :=
      ⟨W.smul_mem _ hv, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv0)]⟩
    rw [hS] at hmem
    exact hmem
  obtain ⟨v₀, hv₀S, hmax⟩ := hSc.exists_isMaxOn hS hcont.continuousOn
  have hv₀0 : v₀ ≠ 0 := by
    intro h
    have := hv₀S.2
    rw [h, mem_sphere, dist_self] at this
    exact zero_ne_one this
  refine ⟨-H v₀ v₀, by linarith [hW v₀ hv₀S.1 hv₀0], fun v hv => ?_⟩
  by_cases hv0 : v = 0
  · simp [hv0]
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hmem : ‖v‖⁻¹ • v ∈ S :=
    ⟨W.smul_mem _ hv, by simp [norm_smul, inv_mul_cancel₀ hn.ne']⟩
  have h1 : H (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) ≤ H v₀ v₀ := hmax hmem
  have h2 : H (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = (‖v‖ ^ 2)⁻¹ * H v v := by
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [h2] at h1
  have h3 : H v v ≤ ‖v‖ ^ 2 * H v₀ v₀ := by
    have hp : 0 < ‖v‖ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left h1 hp.le
    rwa [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] at this
  linarith

/-- **Forms near a form of index `≥ λ` have index `≥ λ`**: if `H` is negative definite with margin
`μ` on `W`, every `H'` with `‖H' − H‖ < μ` is negative definite on `W`, so
`dim W ≤ index H'`. -/
theorem le_index_of_norm_sub_lt {H H' : E →L[ℝ] E →L[ℝ] ℝ} {W : Submodule ℝ E} {μ : ℝ}
    (hμ : ∀ v ∈ W, H v v ≤ -μ * ‖v‖ ^ 2) (h : ‖H' - H‖ < μ) : finrank ℝ W ≤ index H' := by
  refine finrank_le_index_of_negDef H' fun v hv hv0 => ?_
  have hn : 0 < ‖v‖ ^ 2 := by positivity
  have h1 : |(H' - H) v v| ≤ ‖H' - H‖ * ‖v‖ ^ 2 := by
    rw [← Real.norm_eq_abs, sq, ← mul_assoc]
    exact (H' - H).le_opNorm₂ v v
  have h2 : (H' - H) v v = H' v v - H v v := by simp
  rw [h2] at h1
  have h3 : ‖H' - H‖ * ‖v‖ ^ 2 < μ * ‖v‖ ^ 2 := mul_lt_mul_of_pos_right h hn
  linarith [(abs_le.1 h1).2, hμ v hv]

/-- **Lemma 22.4** (Milnor, p. 119).  Let `K ⊆ U ⊆ E` with `K` compact and `U` open, and
`f : E → ℝ` of class `C²` on `U`, all of whose critical points in `K` have index `≥ λ₀`.  Then
there is `ε > 0` such that every `g` with `‖dg − df‖ < ε` and `‖d²g − d²f‖ < ε` at each point of
`K` has all its critical points in `K` of index `≥ λ₀`. -/
theorem lemma_22_4 {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {f : E → ℝ}
    (hf : ContDiffOn ℝ 2 f U) {l₀ : ℕ}
    (hidx : ∀ x ∈ K, IsCriticalPoint f x → l₀ ≤ index (hessian f x)) :
    ∃ ε > 0, ∀ g : E → ℝ, (∀ x ∈ K, ‖fderiv ℝ g x - fderiv ℝ f x‖ < ε) →
      (∀ x ∈ K, ‖hessian g x - hessian f x‖ < ε) →
      ∀ x ∈ K, IsCriticalPoint g x → l₀ ≤ index (hessian g x) := by
  -- the property, for a given `ε` and point `y`
  set P : ℝ → E → Prop := fun ε y => ∀ g : E → ℝ, ‖fderiv ℝ g y - fderiv ℝ f y‖ < ε →
    ‖hessian g y - hessian f y‖ < ε → IsCriticalPoint g y → l₀ ≤ index (hessian g y) with hP
  have hmono : ∀ ε ε' y, ε' ≤ ε → P ε y → P ε' y := fun ε ε' y h hPy g h1 h2 =>
    hPy g (h1.trans_le h) (h2.trans_le h)
  have hDf : ContinuousOn (fderiv ℝ f) U := hf.continuousOn_fderiv_of_isOpen hU (by norm_num)
  have hD2f : ContinuousOn (hessian f) U := by
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
    exact h1.continuousOn_fderiv_of_isOpen hU le_rfl
  have hloc : ∀ x ∈ K, ∀ᶠ z : ℝ × E in 𝓝 (0, x), P z.1 z.2 := by
    intro x hx
    have hxU : U ∈ 𝓝 x := hU.mem_nhds (hKU hx)
    by_cases hcrit : fderiv ℝ f x = 0
    · -- a critical point: a negative definite subspace with a margin
      have hfx : IsCriticalPoint f x := by
        have hd : DifferentiableAt ℝ f x :=
          (hf.contDiffAt hxU).differentiableAt (by norm_num)
        have := hd.hasFDerivAt
        rwa [hcrit] at this
      obtain ⟨W, hWdim, hW⟩ := exists_negDef_finrank_eq_index (hessian f x)
      obtain ⟨μ, hμ, hμW⟩ := exists_negDef_margin _ W hW
      have hnear : ∀ᶠ y in 𝓝 x, ‖hessian f y - hessian f x‖ < μ / 2 := by
        have := (hD2f.continuousAt hxU).eventually (Metric.ball_mem_nhds (hessian f x)
          (half_pos hμ))
        filter_upwards [this] with y hy
        rwa [dist_eq_norm] at hy
      filter_upwards [prod_mem_nhds (Iio_mem_nhds (half_pos hμ)) hnear] with z hz
      intro g _ h2 _
      have h3 : ‖hessian g z.2 - hessian f x‖ < μ := by
        calc ‖hessian g z.2 - hessian f x‖
            ≤ ‖hessian g z.2 - hessian f z.2‖ + ‖hessian f z.2 - hessian f x‖ := by
              rw [← sub_add_sub_cancel (hessian g z.2) (hessian f z.2) (hessian f x)]
              exact norm_add_le _ _
          _ < μ / 2 + μ / 2 := add_lt_add (h2.trans hz.1) hz.2
          _ = μ := by ring
      calc l₀ ≤ index (hessian f x) := hidx x hx hfx
        _ = finrank ℝ W := hWdim.symm
        _ ≤ index (hessian g z.2) := le_index_of_norm_sub_lt hμW h3
    · -- a regular point: `dg ≠ 0` nearby
      set η := ‖fderiv ℝ f x‖ / 2 with hη_def
      have hη : 0 < η := half_pos (norm_pos_iff.2 hcrit)
      have hnear : ∀ᶠ y in 𝓝 x, ‖fderiv ℝ f y - fderiv ℝ f x‖ < η := by
        have := (hDf.continuousAt hxU).eventually (Metric.ball_mem_nhds (fderiv ℝ f x) hη)
        filter_upwards [this] with y hy
        rwa [dist_eq_norm] at hy
      filter_upwards [prod_mem_nhds (Iio_mem_nhds hη) hnear] with z hz
      intro g h1 _ hg
      exfalso
      have h0 : fderiv ℝ g z.2 = 0 := hg.fderiv_eq
      rw [h0, zero_sub, norm_neg] at h1
      have h4 : ‖fderiv ℝ f x‖ ≤ ‖fderiv ℝ f z.2‖ + ‖fderiv ℝ f z.2 - fderiv ℝ f x‖ := by
        have := norm_sub_le (fderiv ℝ f z.2) (fderiv ℝ f z.2 - fderiv ℝ f x)
        rwa [sub_sub_cancel] at this
      have h5 : ‖fderiv ℝ f z.2‖ < η := h1.trans hz.1
      have h6 : ‖fderiv ℝ f z.2 - fderiv ℝ f x‖ < η := hz.2
      linarith
  have hall := hK.eventually_forall_of_forall_eventually hloc
  obtain ⟨ε, hεK, hε⟩ := ((hall.filter_mono (nhdsWithin_le_nhds (s := Ioi 0))).and
    self_mem_nhdsWithin).exists
  exact ⟨ε, hε, fun g h1 h2 x hx => hεK x hx g (h1 x hx) (h2 x hx)⟩

omit [FiniteDimensional ℝ E] in
/-- `df` and `d²f` of a sum at a point where both summands are `C²`. -/
theorem fderiv_hessian_add {f h : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hh : ContDiffAt ℝ 2 h x) :
    fderiv ℝ (f + h) x - fderiv ℝ f x = fderiv ℝ h x ∧
      hessian (f + h) x - hessian f x = hessian h x := by
  have hfd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hhd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ h y :=
    (hh.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
  have hev : fderiv ℝ (f + h) =ᶠ[𝓝 x] fderiv ℝ f + fderiv ℝ h := by
    filter_upwards [hfd, hhd] with y h1 h2
    exact fderiv_add h1 h2
  refine ⟨by rw [hev.eq_of_nhds]; simp, ?_⟩
  have hf1 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh1 : DifferentiableAt ℝ (fderiv ℝ h) x :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [hessian, hessian, hessian, hev.fderiv_eq, fderiv_add hf1 hh1]
  simp

/-- **Lemma 22.4 for a perturbation `g = f + h`**, closeness measured by the first two
derivatives of `h` (as `iteratedFDeriv`, the form of Corollary 6.8). -/
theorem lemma_22_4_add {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {f : E → ℝ}
    (hf : ContDiffOn ℝ 2 f U) {l₀ : ℕ}
    (hidx : ∀ x ∈ K, IsCriticalPoint f x → l₀ ≤ index (hessian f x)) :
    ∃ ε > 0, ∀ h : E → ℝ, ContDiffOn ℝ 2 h U →
      (∀ x ∈ K, ‖iteratedFDeriv ℝ 1 h x‖ < ε) → (∀ x ∈ K, ‖iteratedFDeriv ℝ 2 h x‖ < ε) →
      ∀ x ∈ K, IsCriticalPoint (f + h) x → l₀ ≤ index (hessian (f + h) x) := by
  obtain ⟨ε, hε, H⟩ := lemma_22_4 hU hK hKU hf hidx
  refine ⟨ε, hε, fun h hh h1 h2 => H (f + h) (fun x hx => ?_) (fun x hx => ?_)⟩
  · have hxU : U ∈ 𝓝 x := hU.mem_nhds (hKU hx)
    rw [(fderiv_hessian_add (hf.contDiffAt hxU) (hh.contDiffAt hxU)).1,
      ← norm_iteratedFDeriv_one]
    exact h1 x hx
  · have hxU : U ∈ 𝓝 x := hU.mem_nhds (hKU hx)
    rw [(fderiv_hessian_add (hf.contDiffAt hxU) (hh.contDiffAt hxU)).2, hessian,
      ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact h2 x hx

end Euclidean

/-! ### On a submanifold -/

section Submanifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

/-- **Lemma 22.4 in one slice chart**: near a point `z₀` of the chart, small linear
perturbations do not lower the index of critical points lying in `K`. -/
theorem exists_perturb_slice (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) {F : V → ℝ}
    (hF : ContDiff ℝ ∞ F) {K : Set N} (hK : IsCompact K) {l₀ : ℕ}
    (hidx : letI := hN.chartedSpace;
      ∀ q ∈ K, IsCriticalPointM Z (F ∘ Subtype.val) q → l₀ ≤ indexM Z (F ∘ Subtype.val) q)
    {z₀ : Z} (hz₀ : z₀ ∈ σ.toChart.target) :
    letI := hN.chartedSpace
    ∃ r > 0, ∃ δ > 0, ∀ a : V →L[ℝ] ℝ, ‖a‖ < δ → ∀ q ∈ K, q.1 ∈ σ.φ.source →
      (σ.φ q).1 ∈ ball z₀ r → IsCriticalPointM Z ((fun x => F x + a x) ∘ Subtype.val) q →
      l₀ ≤ indexM Z ((fun x => F x + a x) ∘ Subtype.val) q := by
  let _ := hN.chartedSpace
  have := hN.isManifold
  set T := σ.toChart.target with hT_def
  have hTo : IsOpen T := isOpen_toChart_target σ
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 hTo z₀ hz₀
  set r := ε₀ / 2 with hr_def
  have hr : 0 < r := half_pos hε₀
  have hcb : closedBall z₀ r ⊆ T := (closedBall_subset_ball (by linarith)).trans hball
  have hsp : ContDiffOn ℝ ∞ (sliceParam σ) T := contDiffOn_sliceParam σ
  -- the compact set of the chart where the hypothesis applies
  set Kz := closedBall z₀ r ∩ sliceParam σ ⁻¹' (Subtype.val '' K) with hKz_def
  have hKzc : IsCompact Kz := by
    have hcl : IsClosed (Subtype.val '' K) :=
      (hK.image continuous_subtype_val).isClosed
    have : IsClosed Kz :=
      (hsp.continuousOn.mono hcb).preimage_isClosed_of_isClosed isClosed_closedBall hcl
    exact (isCompact_closedBall z₀ r).of_isClosed_subset this inter_subset_left
  have hKzT : Kz ⊆ T := inter_subset_left.trans hcb
  -- the point of `N` with chart value `z`
  have hpt : ∀ z ∈ Kz, (σ.toChart.symm z) ∈ K ∧ (σ.toChart.symm z).1 ∈ σ.φ.source ∧
      (σ.φ (σ.toChart.symm z)).1 = z := by
    intro z hz
    have hzT := hKzT hz
    refine ⟨?_, σ.toChart.map_target hzT, σ.toChart.right_inv hzT⟩
    obtain ⟨k, hk, hkz⟩ := hz.2
    have : k = σ.toChart.symm z := Subtype.ext (by rw [hkz, val_toChart_symm σ hzT])
    exact this ▸ hk
  have hFd : ∀ G : V → ℝ, ContDiff ℝ ∞ G → ∀ x, DifferentiableAt ℝ G x := fun G hG x =>
    (hG.differentiable (by simp)) x
  obtain ⟨ε, hε, H⟩ := lemma_22_4_add hTo hKzc hKzT (f := F ∘ sliceParam σ)
    (hF.comp_contDiffOn hsp |>.of_le (by norm_cast)) (l₀ := l₀) (fun z hz hcrit => by
      obtain ⟨hzK, hzs, hzφ⟩ := hpt z hz
      have hc := (isCriticalPointM_comp_val_iff_sliceParam hN σ hzs (hFd F hF _)).2
        (by rwa [hzφ])
      rw [← hzφ, index_hessian_comp_sliceParam hN σ hzs (hF.contDiffAt.of_le (by norm_cast)) hc]
      exact hidx _ hzK hc)
  -- bounds for the first two derivatives of the parametrization on the closed ball
  have hbd : ∀ i : ℕ, ∃ C, ∀ z ∈ closedBall z₀ r, ‖iteratedFDeriv ℝ i (sliceParam σ) z‖ ≤ C := by
    intro i
    have hcont : ContinuousOn (iteratedFDeriv ℝ i (sliceParam σ)) T :=
      (hsp.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top)
        hTo.uniqueDiffOn).congr fun u hu => (iteratedFDerivWithin_of_isOpen i hTo hu).symm
    exact (isCompact_closedBall z₀ r).exists_bound_of_continuousOn (hcont.mono hcb)
  obtain ⟨C₁, hC₁⟩ := hbd 1
  obtain ⟨C₂, hC₂⟩ := hbd 2
  set C := |C₁| + |C₂| + 1 with hC_def
  have hC : 0 < C := by positivity
  refine ⟨r, hr, ε / C, div_pos hε hC, fun a ha q hqK hqs hqb hcrit => ?_⟩
  have hFa : ContDiff ℝ ∞ (fun x => F x + a x) := hF.add a.contDiff
  set z := (σ.φ q).1 with hz_def
  have hzT : z ∈ T := toChart_apply_mem_target σ hqs
  have hzK : z ∈ Kz := ⟨ball_subset_closedBall hqb, q, hqK, (sliceParam_toChart σ hqs).symm⟩
  have hc' := (isCriticalPointM_comp_val_iff_sliceParam hN σ hqs (hFd _ hFa _)).1 hcrit
  rw [← index_hessian_comp_sliceParam hN σ hqs (hFa.contDiffAt.of_le (by norm_cast)) hcrit]
  -- the perturbation in the chart
  have hsum : (fun x => F x + a x) ∘ sliceParam σ = F ∘ sliceParam σ + a ∘ sliceParam σ := rfl
  have hder : ∀ i, (i = 1 ∨ i = 2) → ∀ z ∈ Kz, ‖iteratedFDeriv ℝ i (a ∘ sliceParam σ) z‖ < ε := by
    intro i hi z hz
    have hzT := hKzT hz
    have hsm : ContDiffAt ℝ ∞ (sliceParam σ) z := hsp.contDiffAt (hTo.mem_nhds hzT)
    rw [a.iteratedFDeriv_comp_left hsm (by exact_mod_cast le_top)]
    have hCi : ‖iteratedFDeriv ℝ i (sliceParam σ) z‖ ≤ C := by
      rcases hi with rfl | rfl
      · exact (hC₁ z hz.1).trans (by linarith [le_abs_self C₁, abs_nonneg C₂])
      · exact (hC₂ z hz.1).trans (by linarith [le_abs_self C₂, abs_nonneg C₁])
    calc _ ≤ ‖a‖ * ‖iteratedFDeriv ℝ i (sliceParam σ) z‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ ‖a‖ * C := mul_le_mul_of_nonneg_left hCi (norm_nonneg _)
      _ < ε / C * C := mul_lt_mul_of_pos_right ha hC
      _ = ε := div_mul_cancel₀ ε hC.ne'
  rw [hsum] at hc' ⊢
  exact H (a ∘ sliceParam σ) (a.contDiff.comp_contDiffOn hsp |>.of_le (by norm_cast))
    (hder 1 (Or.inl rfl)) (hder 2 (Or.inr rfl)) z hzK hc'

/-- **Lemma 22.4 on a submanifold** (for linear perturbations): let `N ⊆ V` be a slice
submanifold, `F : V → ℝ` smooth and `K ⊆ N` compact, such that every critical point of `F|N` in
`K` has index `≥ λ₀`.  Then there is `δ > 0` such that for every linear form `a` on `V` with
`‖a‖ < δ`, every critical point of `(F + a)|N` in `K` has index `≥ λ₀`.  (Cover `K` by finitely
many slice-chart balls and apply `Morse.lemma_22_4_add` in each.) -/
theorem lemma_22_4_submanifold {F : V → ℝ} (hF : ContDiff ℝ ∞ F) {K : Set N}
    (hK : IsCompact K) {l₀ : ℕ}
    (hidx : letI := hN.chartedSpace;
      ∀ q ∈ K, IsCriticalPointM Z (F ∘ Subtype.val) q → l₀ ≤ indexM Z (F ∘ Subtype.val) q) :
    letI := hN.chartedSpace
    ∃ δ > 0, ∀ a : V →L[ℝ] ℝ, ‖a‖ < δ → ∀ q ∈ K,
      IsCriticalPointM Z ((fun x => F x + a x) ∘ Subtype.val) q →
      l₀ ≤ indexM Z ((fun x => F x + a x) ∘ Subtype.val) q := by
  let _ := hN.chartedSpace
  set Q : ℝ → N → Prop := fun δ q => q ∈ K → ∀ a : V →L[ℝ] ℝ, ‖a‖ < δ →
    IsCriticalPointM Z ((fun x => F x + a x) ∘ Subtype.val) q →
    l₀ ≤ indexM Z ((fun x => F x + a x) ∘ Subtype.val) q with hQ
  have hloc : ∀ q ∈ K, ∀ᶠ z : ℝ × N in 𝓝 (0, q), Q z.1 z.2 := by
    intro q _
    obtain ⟨σ, hσ⟩ := hN q.1 q.2
    obtain ⟨r, hr, δ, hδ, H⟩ := exists_perturb_slice hN σ hF hK hidx
      (toChart_apply_mem_target σ hσ)
    have hO : {q' : N | q'.1 ∈ σ.φ.source ∧ (σ.φ q').1 ∈ ball (σ.φ q).1 r} ∈ 𝓝 q := by
      have hopen : IsOpen {q' : N | q'.1 ∈ σ.φ.source ∧ (σ.φ q').1 ∈ ball (σ.φ q).1 r} :=
        σ.toChart.continuousOn_toFun.isOpen_inter_preimage σ.toChart.open_source isOpen_ball
      exact hopen.mem_nhds ⟨hσ, mem_ball_self hr⟩
    filter_upwards [prod_mem_nhds (Iio_mem_nhds hδ) hO] with z hz
    intro hzK a ha hc
    exact H a (ha.trans hz.1) z.2 hzK hz.2.1 hz.2.2 hc
  have hall := hK.eventually_forall_of_forall_eventually hloc
  obtain ⟨δ, hδK, hδ⟩ := ((hall.filter_mono (nhdsWithin_le_nhds (s := Ioi 0))).and
    self_mem_nhdsWithin).exists
  exact ⟨δ, hδ, fun a ha q hq hc => hδK q hq hq a ha hc⟩

end Submanifold

end Morse
