import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_11
import RoundTrip.Bridge

open Set Filter Topology Function MeasureTheory
open scoped ContDiff Manifold

namespace RoundTrip.V7_11

/-- The project's statement (universes instantiated at 0): for paths `c : ℝ → V` in a normed space
(`Morse.pathLength c a b = ∫ ‖c'‖`, `Morse.IsAdmissible`: continuous, differentiable off a
countable set, integrable speed): `‖c b − c a‖ ≤ L(c)`, additivity of length, a path of length `0`
is constant, length of a concatenation, length of the reversed path. -/
def A : Prop :=
  type_of% @Morse.IsAdmissible.norm_sub_le_pathLength.{0} ∧
    type_of% @Morse.IsAdmissible.pathLength_add.{0} ∧
    type_of% @Morse.IsAdmissible.eq_of_pathLength_eq_zero.{0} ∧
    type_of% @Morse.pathLength_concat.{0} ∧
    type_of% @Morse.pathLength_reverse.{0}

theorem A_holds : A :=
  ⟨@Morse.IsAdmissible.norm_sub_le_pathLength, @Morse.IsAdmissible.pathLength_add,
    @Morse.IsAdmissible.eq_of_pathLength_eq_zero, @Morse.pathLength_concat,
    @Morse.pathLength_reverse⟩

/-! ## Part (ii) of B holds on every manifold (affine reparametrization) -/

section Reparam

open Bundle

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M]
  [IsManifold 𝓘(ℝ, Rn n) ∞ M]

theorem contMDiff_aff (a b : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => a + s * (b - a)) :=
  (contDiff_const.add (contDiff_id.mul contDiff_const)).contMDiff

theorem contMDiff_aff_inv (a b : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ => (x - a) / (b - a)) :=
  ((contDiff_id.sub contDiff_const).div_const _).contMDiff

omit [IsManifold 𝓘(ℝ, Rn n) ∞ M] in
theorem isPW_reparam_iff {pth : ℝ → M} {a b : ℝ} (hab : a < b) :
    IsPW (n := n) pth a b ↔ IsPW (n := n) (fun s => pth (a + s * (b - a))) 0 1 := by
  have hba : 0 < b - a := sub_pos.2 hab
  constructor
  · rintro ⟨k, t, h0, hk, hlt, hsm⟩
    refine ⟨k, fun i => (t i - a) / (b - a), by simp [h0], by simp [hk, hba.ne'],
      fun i hi => div_lt_div_of_pos_right (by linarith [hlt i hi]) hba, fun i hi => ?_⟩
    have hmaps : MapsTo (fun s : ℝ => a + s * (b - a))
        (Icc ((t i - a) / (b - a)) ((t (i + 1) - a) / (b - a))) (Icc (t i) (t (i + 1))) := by
      intro s hs
      have h1 := mul_le_mul_of_nonneg_right hs.1 hba.le
      have h2 := mul_le_mul_of_nonneg_right hs.2 hba.le
      rw [div_mul_cancel₀ _ hba.ne'] at h1 h2
      exact ⟨by linarith, by linarith⟩
    exact (hsm i hi).comp (contMDiff_aff a b).contMDiffOn hmaps
  · rintro ⟨k, t, h0, hk, hlt, hsm⟩
    refine ⟨k, fun i => a + t i * (b - a), by simp [h0], by simp [hk], fun i hi => ?_,
      fun i hi => ?_⟩
    · have := mul_lt_mul_of_pos_right (hlt i hi) hba
      linarith
    · have hmaps : MapsTo (fun x : ℝ => (x - a) / (b - a))
          (Icc (a + t i * (b - a)) (a + t (i + 1) * (b - a))) (Icc (t i) (t (i + 1))) := by
        intro x hx
        constructor
        · rw [le_div_iff₀ hba]; linarith [hx.1]
        · rw [div_le_iff₀ hba]; linarith [hx.2]
      refine ((hsm i hi).comp (contMDiff_aff_inv a b).contMDiffOn hmaps).congr fun x _ => ?_
      simp only [Function.comp_apply]
      congr 1
      field_simp
      ring

omit [IsManifold 𝓘(ℝ, Rn n) ∞ M] in
theorem mfderiv_reparam (pth : ℝ → M) {a b : ℝ} (hab : a < b) (s : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) (fun s => pth (a + s * (b - a))) s (1 : ℝ) : Rn n) =
      (b - a) • (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pth (a + s * (b - a)) (1 : ℝ) : Rn n) := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hφ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => a + s * (b - a)) s :=
    ((contMDiff_aff a b) s).mdifferentiableAt (by simp)
  have hφd : HasDerivAt (fun s : ℝ => a + s * (b - a)) (b - a) s := by
    simpa using ((hasDerivAt_id s).mul_const (b - a)).const_add a
  by_cases hd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pth (a + s * (b - a))
  · have e : (fun s => pth (a + s * (b - a))) = pth ∘ (fun s : ℝ => a + s * (b - a)) := rfl
    have hφ1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => a + s * (b - a)) s (1 : ℝ) =
        (b - a) • (1 : ℝ) := by
      rw [mfderiv_eq_fderiv]
      change deriv (fun s : ℝ => a + s * (b - a)) s = (b - a) • (1 : ℝ)
      rw [hφd.deriv, smul_eq_mul, mul_one]
    rw [e, mfderiv_comp s hd hφ]
    change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pth (a + s * (b - a)))
      ((mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => a + s * (b - a)) s) (1 : ℝ)) = _
    rw [hφ1]
    exact (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pth (a + s * (b - a))).map_smul (b - a) (1 : ℝ)
  · have hnd : ¬ MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) (fun s => pth (a + s * (b - a))) s := by
      intro h
      apply hd
      have hψ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun x : ℝ => (x - a) / (b - a))
          (a + s * (b - a)) := ((contMDiff_aff_inv a b) _).mdifferentiableAt (by simp)
      have hψs : (fun x : ℝ => (x - a) / (b - a)) (a + s * (b - a)) = s := by
        field_simp; ring
      have h' : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) (fun s => pth (a + s * (b - a)))
          ((fun x : ℝ => (x - a) / (b - a)) (a + s * (b - a))) := by rw [hψs]; exact h
      have hc := h'.comp (a + s * (b - a)) hψ
      have e : (fun s => pth (a + s * (b - a))) ∘ (fun x : ℝ => (x - a) / (b - a)) = pth := by
        funext x
        simp only [Function.comp_apply]
        congr 1
        field_simp
        ring
      rwa [e] at hc
    rw [mfderiv_zero_of_not_mdifferentiableAt hnd, mfderiv_zero_of_not_mdifferentiableAt hd]
    show (0 : Rn n) = (b - a) • (0 : Rn n)
    rw [smul_zero]

variable [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

omit [IsManifold 𝓘(ℝ, Rn n) ∞ M] in
theorem arcLen_reparam (pth : ℝ → M) {a b : ℝ} (hab : a < b) :
    arcLen (n := n) (fun s => pth (a + s * (b - a))) 0 1 = arcLen (n := n) pth a b := by
  have hba : 0 < b - a := sub_pos.2 hab
  set f : ℝ → ℝ := fun t =>
    ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pth t (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pth t))‖ with hf
  have h1 : ∀ s : ℝ, ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) (fun s => pth (a + s * (b - a))) s (1 : ℝ) :
      TangentSpace 𝓘(ℝ, Rn n) (pth (a + s * (b - a))))‖ = (b - a) * f (a + (b - a) * s) := by
    intro s
    have e := mfderiv_reparam (n := n) pth hab s
    rw [mul_comm (b - a) s]
    change @Norm.norm (TangentSpace 𝓘(ℝ, Rn n) (pth (a + s * (b - a)))) _
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) (fun s => pth (a + s * (b - a))) s (1 : ℝ)) = _
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hba]
  unfold arcLen
  simp_rw [h1]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_mul f hba.ne' a,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hba.ne', one_mul, mul_zero, add_zero, mul_one,
    add_sub_cancel]

omit [IsManifold 𝓘(ℝ, Rn n) ∞ M] in
/-- **Part (ii) of B holds outright, on every manifold** (no metric property used). -/
theorem B_part_ii (pth : ℝ → M) (a b : ℝ) (hab : a < b) :
    (IsPW (n := n) pth a b ↔ IsPW (n := n) (fun s => pth (a + s * (b - a))) 0 1) ∧
      arcLen (n := n) (fun s => pth (a + s * (b - a))) 0 1 = arcLen (n := n) pth a b :=
  ⟨isPW_reparam_iff hab, arcLen_reparam pth hab⟩

end Reparam

/-! ## Part (i) of B holds on every Riemannian manifold (integrable speed) -/

section Speed

open Bundle

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M]
  [IsManifold 𝓘(ℝ, Rn n) ∞ M] [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, Rn n) ∞ (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- On a smooth piece `[c, d]` the speed is integrable: it agrees on `(c, d)` with the norm of the
one-sided velocity, which is continuous on `[c, d]` (smoothness of `tangentMapWithin` and of the
metric, `ContMDiffOn.inner_bundle`). -/
theorem intervalIntegrable_speed_piece {pth : ℝ → M} {c d : ℝ} (hcd : c < d)
    (h : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ pth (Icc c d)) :
    IntervalIntegrable (speed (n := n) pth) volume c d := by
  set σ : ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ :=
    fun t => (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm (t, 1) with hσ
  have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun t : ℝ => ((t, 1) : ℝ × ℝ)) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  rw [modelWithCornersSelf_prod] at h1
  have hσs : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞ σ :=
    (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓘(ℝ, ℝ))).comp h1
  have hT := h.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    ((uniqueDiffOn_Icc hcd).uniqueMDiffOn)
  have hF0 := hT.comp hσs.contMDiffOn (fun t ht => ht)
  set v : ℝ → Rn n := fun t => mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pth (Icc c d) t (1 : ℝ) with hv
  have hF : ContMDiffOn 𝓘(ℝ, ℝ) ((𝓘(ℝ, Rn n)).prod 𝓘(ℝ, Rn n)) ∞
      (fun t => (⟨pth t, v t⟩ : TotalSpace (Rn n) (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)))
      (Icc c d) := hF0
  have hinner := ContMDiffOn.inner_bundle (F := Rn n)
    (E := fun x : M => TangentSpace 𝓘(ℝ, Rn n) x) (b := pth)
    (v := fun t => (v t : TangentSpace 𝓘(ℝ, Rn n) (pth t)))
    (w := fun t => (v t : TangentSpace 𝓘(ℝ, Rn n) (pth t))) hF hF
  have hcont : ContinuousOn
      (fun t => @Norm.norm (TangentSpace 𝓘(ℝ, Rn n) (pth t)) _ (v t)) (Icc c d) := by
    have : (fun t => @Norm.norm (TangentSpace 𝓘(ℝ, Rn n) (pth t)) _ (v t)) =
        fun t => Real.sqrt (@inner ℝ (TangentSpace 𝓘(ℝ, Rn n) (pth t)) _ (v t) (v t)) := by
      funext t
      exact norm_eq_sqrt_real_inner _
    rw [this]
    exact Real.continuous_sqrt.comp_continuousOn hinner.continuousOn
  have hint : IntervalIntegrable
      (fun t => @Norm.norm (TangentSpace 𝓘(ℝ, Rn n) (pth t)) _ (v t)) volume c d :=
    hcont.intervalIntegrable_of_Icc hcd.le
  refine hint.congr_uIoo fun t ht => ?_
  rw [uIoo_of_le hcd.le] at ht
  simp only [speed, hv]
  rw [mfderivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- **Part (i) of B holds outright, on every Riemannian manifold.** -/
theorem B_part_i (pth : ℝ → M) (a b : ℝ) (hab : a ≤ b) (h : IsPW (n := n) pth a b) :
    IntervalIntegrable (speed (n := n) pth) volume a b ∧ 0 ≤ arcLen (n := n) pth a b := by
  refine ⟨?_, intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _⟩
  obtain ⟨k, t, h0, hk, hlt, hsm⟩ := h
  rw [← h0, ← hk]
  exact IntervalIntegrable.trans_iterate fun i hi =>
    intervalIntegrable_speed_piece (hlt i hi) (hsm i hi)

end Speed

/-- **B holds outright** (both parts, on every abstract Riemannian manifold): B only asserts that
the arc length of piecewise smooth paths is well defined and invariant under the affine
reparametrization `[0, 1] → [a, b]`. -/
theorem B_holds : B := fun _ _ _ _ _ _ _ _ _ =>
  ⟨fun pth a b hab h => B_part_i pth a b hab h, fun pth a b hab => B_part_ii pth a b hab⟩

/-- `A → B` holds, vacuously (B is proved outright; A is not used). -/
theorem A_to_B : A → B := fun _ => B_holds

/-! ## `B → A`, vacuously: A is elementary real analysis, re-proved outright here (without A's
theorems or lemmas built on them), so that the implication is recorded; B is not used. -/

theorem A_outright : A := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro V _ _ c a b _ h
    rw [← h.integral_deriv]
    exact intervalIntegral.norm_integral_le_integral_norm h.le
  · intro V _ _ c a b h m hm
    exact intervalIntegral.integral_add_adjacent_intervals (h.mono le_rfl hm.1 hm.2).integrable
      (h.mono hm.1 hm.2 le_rfl).integrable
  · intro V _ _ c a b _ h h0 t ht
    have hadd : ∀ {a' b' : ℝ}, a ≤ a' → a' ≤ b' → b' ≤ b → ∀ m ∈ Icc a' b',
        Morse.pathLength c a' m + Morse.pathLength c m b' = Morse.pathLength c a' b' :=
      fun ha hab hb m hm => intervalIntegral.integral_add_adjacent_intervals
        ((h.mono ha hab hb).mono le_rfl hm.1 hm.2).integrable
        ((h.mono ha hab hb).mono hm.1 hm.2 le_rfl).integrable
    have h1 : ‖c t - c a‖ ≤ Morse.pathLength c a t := by
      rw [← (h.mono le_rfl ht.1 ht.2).integral_deriv]
      exact intervalIntegral.norm_integral_le_integral_norm ht.1
    have h2 := hadd le_rfl (ht.1.trans ht.2) le_rfl t ht
    have h3 := (h.mono ht.1 ht.2 le_rfl).pathLength_nonneg
    have h4 : Morse.pathLength c a t ≤ 0 := by rw [← h0, ← h2]; linarith
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (h1.trans h4))
  · intro V _ _ c₁ c₂ a m b h₁ h₂
    set c := fun t => if t ≤ m then c₁ t else c₂ t with hc
    have hd₁ : ∀ t < m, deriv c t = deriv c₁ t := fun t ht => by
      have hev : c =ᶠ[𝓝 t] c₁ := by
        filter_upwards [Iio_mem_nhds ht] with x hx
        simp only [hc, if_pos (le_of_lt (mem_Iio.1 hx))]
      exact hev.deriv_eq
    have hd₂ : ∀ t, m < t → deriv c t = deriv c₂ t := fun t ht => by
      have hev : c =ᶠ[𝓝 t] c₂ := by
        filter_upwards [Ioi_mem_nhds ht] with x hx
        simp only [hc, if_neg (not_le.2 (mem_Ioi.1 hx))]
      exact hev.deriv_eq
    have hm : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ m := (countable_singleton m).ae_notMem volume
    have hI₁ : Morse.pathLength c a m = Morse.pathLength c₁ a m := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hm] with t htm ht
      rw [uIoc_of_le h₁.le] at ht
      rw [hd₁ t (lt_of_le_of_ne ht.2 htm)]
    have hI₂ : Morse.pathLength c m b = Morse.pathLength c₂ m b := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with t ht
      rw [uIoc_of_le h₂.le] at ht
      rw [hd₂ t ht.1]
    have hint₁ : IntervalIntegrable (fun t => ‖deriv c t‖) volume a m :=
      h₁.integrable.congr_uIoo fun t ht => by
        rw [uIoo_of_le h₁.le] at ht
        simp only [hd₁ t ht.2]
    have hint₂ : IntervalIntegrable (fun t => ‖deriv c t‖) volume m b :=
      h₂.integrable.congr_uIoo fun t ht => by
        rw [uIoo_of_le h₂.le] at ht
        simp only [hd₂ t ht.1]
    rw [← hI₁, ← hI₂, Morse.pathLength, Morse.pathLength, Morse.pathLength,
      intervalIntegral.integral_add_adjacent_intervals hint₁ hint₂]
  · intro V _ _ c a b
    have hd : ∀ t, deriv (fun t => c (a + b - t)) t = -deriv c (a + b - t) := fun t => by
      have := deriv_comp_const_sub (f := c) (a := a + b) (x := t)
      simpa using this
    simp only [Morse.pathLength, hd, norm_neg]
    rw [intervalIntegral.integral_comp_sub_left (fun t => ‖deriv c t‖) (a + b)]
    simp only [add_sub_cancel_left, add_sub_cancel_right]

/-- `B → A`, vacuously (A proved outright; B is not used). -/
theorem B_to_A : B → A := fun _ => A_outright

/-! ## The embedded special case: B holds on `↥N`, and the vocabulary agrees -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- **Vocabulary: B's piecewise smooth paths in `↥N` are the project's** (`IsPiecewiseSmooth` of
the path read in `V`). -/
theorem isPW_iff {pth : ℝ → Bridge.Sub hN} {a b : ℝ} :
    IsPW (n := n) pth a b ↔ Morse.IsPiecewiseSmooth (incl hN ∘ pth) a b := by
  constructor
  · intro h
    exact isPiecewiseSmooth_of_isPW h
  · intro h
    have h' := isPW_lift (n := n) h (fun t _ => (pth t).2) (pth a)
    have e : lift (incl hN ∘ pth) (pth a) = pth := by
      funext t
      exact lift_of_mem (pth a) (pth t).2
    rw [e] at h'
    exact h'

/-- **Vocabulary: B's speed and arc length are the project's** (`‖c'‖` and `Morse.pathLength`). -/
theorem speed_eq (pth : ℝ → Bridge.Sub hN) (t : ℝ) :
    speed (n := n) pth t = ‖deriv (incl hN ∘ pth) t‖ := norm_mfderiv_curve pth t

theorem arcLen_eq' (pth : ℝ → Bridge.Sub hN) (a b : ℝ) :
    arcLen (n := n) pth a b = Morse.pathLength (incl hN ∘ pth) a b := arcLen_eq pth a b

/-- Part (i) of B on `↥N`: piecewise smooth paths have integrable speed and nonnegative length
(`Morse.IsPiecewiseSmooth.isAdmissible`). -/
theorem B_part_i (pth : ℝ → Bridge.Sub hN) (a b : ℝ) (hab : a ≤ b) (h : IsPW (n := n) pth a b) :
    IntervalIntegrable (speed (n := n) pth) volume a b ∧ 0 ≤ arcLen (n := n) pth a b := by
  have e : speed (n := n) pth = fun t => ‖deriv (incl hN ∘ pth) t‖ := funext (speed_eq pth)
  refine ⟨?_, arcLen_nonneg hab⟩
  rw [e]
  exact (isPW_iff.1 h).isAdmissible.integrable

end Emb

/-- B on embedded manifolds: `M = ↥N` with the induced metric. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    (∀ (pth : ℝ → Bridge.Sub hN) (a b : ℝ), a ≤ b → IsPW (n := n) pth a b →
      IntervalIntegrable (speed (n := n) pth) volume a b ∧ 0 ≤ arcLen (n := n) pth a b) ∧
    ∀ (pth : ℝ → Bridge.Sub hN) (a b : ℝ), a < b →
      (IsPW (n := n) pth a b ↔ IsPW (n := n) (fun s => pth (a + s * (b - a))) 0 1) ∧
      arcLen (n := n) (fun s => pth (a + s * (b - a))) 0 1 = arcLen (n := n) pth a b

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN)

/-- **B holds on embedded manifolds** (outright: A is not used). -/
theorem B_emb_holds : B_emb := fun _ _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun pth a b hab h => Emb.B_part_i pth a b hab h, fun pth a b hab => B_part_ii pth a b hab⟩

theorem A_to_B_emb : A → B_emb := fun _ => B_emb_holds

#rt_check RoundTrip.V7_11.A_to_B [Morse.IsAdmissible.norm_sub_le_pathLength,
  Morse.IsAdmissible.pathLength_add, Morse.IsAdmissible.eq_of_pathLength_eq_zero,
  Morse.pathLength_concat, Morse.pathLength_reverse]
#rt_check RoundTrip.V7_11.B_to_A [Morse.IsAdmissible.norm_sub_le_pathLength,
  Morse.IsAdmissible.pathLength_add, Morse.IsAdmissible.eq_of_pathLength_eq_zero,
  Morse.pathLength_concat, Morse.pathLength_reverse]
#rt_overlap RoundTrip.V7_11.B_to_A [Morse.IsAdmissible.norm_sub_le_pathLength,
  Morse.IsAdmissible.pathLength_add, Morse.IsAdmissible.eq_of_pathLength_eq_zero,
  Morse.pathLength_concat, Morse.pathLength_reverse]
#rt_check RoundTrip.V7_11.A_to_B_emb [Morse.IsAdmissible.norm_sub_le_pathLength,
  Morse.IsAdmissible.pathLength_add, Morse.IsAdmissible.eq_of_pathLength_eq_zero,
  Morse.pathLength_concat, Morse.pathLength_reverse]

end RoundTrip.V7_11
