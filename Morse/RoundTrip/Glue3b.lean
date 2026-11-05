import Morse
import RoundTrip.Blind.V7_14
/-!
# Round-trip glue for batch p3b (Milnor §10): a flat counter-model

`E2 = ℝ²` as a manifold (one chart, the identity) with the CONSTANT Riemannian metric
`G v w = ⟪v, w⟫ − 3/4 v₁ w₁` and the flat connection `∇_v σ = dσ(v)`.  We check that it satisfies
the blind formalizations' hypotheses (`IsLC`: smooth, symmetric, and compatible in Milnor's sense,
the latter via: every operation obeying Milnor's axioms (a)–(c) along a curve is `d/dt`), compute
its geodesics (straight lines), `expMap q w = q + w`, normal balls (`IsNormBall` for the
coordinate balls) and arc lengths of straight segments.

This model separates the Riemannian norm `‖w‖_G` from the blind files' `nrm q w`, which (because
`nrm` is elaborated without the `RiemannianBundle` instance) is the Euclidean norm of the model
vector `w ∈ ℝⁿ`.  The definitions used are those of `RoundTrip.Blind.V7_14`; the other blind
files of §10 (V7_12, V7_13, …) contain verbatim copies, so the lemmas transfer by unfolding.
-/

open Bundle Set
open scoped ContDiff Manifold

namespace RoundTrip.Glue.Flat

attribute [-instance] TopCat.of.chartedSpace

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- the constant bilinear form `G v w = ⟪v,w⟫ - 3/4 v₁ w₁` -/
noncomputable def G0 : E2 →L[ℝ] E2 →L[ℝ] ℝ := innerSL ℝ

noncomputable def G : E2 →L[ℝ] E2 →L[ℝ] ℝ :=
  G0 - (3 / 4 : ℝ) • (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (EuclideanSpace.proj (1 : Fin 2)) (EuclideanSpace.proj (1 : Fin 2))

lemma G_apply (v w : E2) : G v w = inner ℝ v w - 3 / 4 * (v 1 * w 1) := by
  simp [G, G0]
  rfl

lemma G_self (v : E2) : G v v = v 0 ^ 2 + v 1 ^ 2 / 4 := by
  rw [G_apply, real_inner_self_eq_norm_sq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

lemma norm_sq_le_G (v : E2) : ‖v‖ ^ 2 ≤ 4 * G v v := by
  rw [G_self, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

lemma G_pos (v : E2) (hv : v ≠ 0) : 0 < G v v := by
  have h : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith [norm_sq_le_G v]

lemma G_symm (v w : E2) : G v w = G w v := by
  rw [G_apply, G_apply, real_inner_comm]; ring

set_option backward.isDefEq.respectTransparency false in
noncomputable def metric :
    ContMDiffRiemannianMetric 𝓘(ℝ, E2) ∞ E2 (fun (x : E2) ↦ TangentSpace 𝓘(ℝ, E2) x) where
  inner _ := G
  symm _ v w := G_symm v w
  pos _ v hv := G_pos v hv
  isVonNBounded _ := by
    change Bornology.IsVonNBounded ℝ {v : E2 | G v v < 1}
    refine (NormedSpace.isVonNBounded_ball ℝ E2 2).subset fun v hv => ?_
    simp only [Set.mem_ofPred_eq] at hv
    simp only [Metric.mem_ball, dist_zero_right]
    have := norm_sq_le_G v
    nlinarith [norm_nonneg v]
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := G)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]

/-- The custom Riemannian structure. -/
@[reducible] noncomputable def rb : RiemannianBundle (fun (x : E2) ↦ TangentSpace 𝓘(ℝ, E2) x) :=
  ⟨metric.toRiemannianMetric⟩

theorem rbSmooth :
    letI := rb
    IsContMDiffRiemannianBundle 𝓘(ℝ, E2) ∞ E2 (fun (x : E2) ↦ TangentSpace 𝓘(ℝ, E2) x) :=
  letI := rb
  ⟨metric.inner, metric.contMDiff, fun _ _ _ ↦ rfl⟩

lemma inner_rb (x : E2) (v w : TangentSpace 𝓘(ℝ, E2) x) :
    letI := rb
    inner ℝ v w = G v w := rfl

lemma norm_rb (x : E2) (v : TangentSpace 𝓘(ℝ, E2) x) :
    letI := rb
    ‖v‖ = Real.sqrt (G v v) := by
  let _ := rb
  rw [norm_eq_sqrt_real_inner]
  rfl


/-! ### The flat connection `∇_v σ = dσ(v)` -/

/-- A section of `TE2`, read as a map `E2 → E2`. -/
def flat (σ : Π x : E2, TangentSpace 𝓘(ℝ, E2) x) : E2 → E2 := σ

noncomputable def covFun (σ : Π x : E2, TangentSpace 𝓘(ℝ, E2) x) (x : E2) :
    TangentSpace 𝓘(ℝ, E2) x →L[ℝ] TangentSpace 𝓘(ℝ, E2) x :=
  fderiv ℝ (flat σ) x

set_option backward.isDefEq.respectTransparency false in
lemma differentiableAt_of_mdiff {σ : Π x : E2, TangentSpace 𝓘(ℝ, E2) x} {x : E2}
    (h : MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, E2).tangent
      (fun y => (⟨y, σ y⟩ : TangentBundle 𝓘(ℝ, E2) E2)) x) :
    DifferentiableAt ℝ (flat σ) x := by
  have h2 := ((contMDiff_snd_tangentBundle_modelSpace E2 𝓘(ℝ, E2) (n := 1)).mdifferentiable
    one_ne_zero).mdifferentiableAt.comp x h
  exact h2.differentiableAt

set_option backward.isDefEq.respectTransparency false in
lemma isCov : IsCovariantDerivativeOn E2 covFun Set.univ where
  add {σ σ' x} hσ hσ' _ := by
    simp only [covFun]
    exact fderiv_add (differentiableAt_of_mdiff hσ) (differentiableAt_of_mdiff hσ')
  leibniz {σ g x} hσ hg _ := by
    simp only [covFun]
    have e1 : flat (g • σ) = fun y => g y • flat σ y := rfl
    have e2 : mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℝ) g x = fderiv ℝ g x := mfderiv_eq_fderiv
    have h3 := fderiv_smul hg.differentiableAt (differentiableAt_of_mdiff hσ)
    erw [e1, h3]
    congr 2
    exact e2.symm

noncomputable def cov : CovariantDerivative 𝓘(ℝ, E2) E2 (TangentSpace 𝓘(ℝ, E2) : E2 → Type) :=
  ⟨covFun, isCov⟩

set_option backward.isDefEq.respectTransparency false in
lemma cov_smooth : ContMDiffCovariantDerivativeOn E2 ∞ cov.toFun Set.univ where
  contMDiff {σ} hσ := by
    intro x _
    have hσ' : ContDiff ℝ (∞ + 1) σ := by
      rw [← contDiffOn_univ]
      exact contMDiffOn_vectorSpace_iff_contDiffOn.1 hσ
    apply ContMDiffAt.contMDiffWithinAt
    rw [contMDiffAt_section]
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]
    exact (hσ'.fderiv_right le_rfl).contMDiff.contMDiffAt


/-! ### B's notions for the flat model -/

section BNotions
open RoundTrip.V7_14

/-- A field along a curve, read as a map `ℝ → E2`. -/
def vec {c : ℝ → E2} (V : (t : ℝ) → TangentSpace 𝓘(ℝ, E2) (c t)) : ℝ → E2 := V

set_option backward.isDefEq.respectTransparency false in
lemma smoothAlong_iff {c : ℝ → E2} {s : Set ℝ} {V : FA 2 c} :
    IsSmoothAlong c s V ↔ ContDiffOn ℝ ∞ c s ∧ ContDiffOn ℝ ∞ (vec V) s := by
  unfold IsSmoothAlong
  constructor
  · intro h
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have := (Bundle.contMDiffWithinAt_totalSpace.1 (h t ht)).1
      exact this.contDiffWithinAt
    · have := (Bundle.contMDiffWithinAt_totalSpace.1 (h t ht)).2
      simp only [trivializationAt_model_space_apply] at this
      exact this.contDiffWithinAt
  · rintro ⟨hc, hV⟩ t ht
    refine Bundle.contMDiffWithinAt_totalSpace.2 ⟨(hc t ht).contMDiffWithinAt, ?_⟩
    simp only [trivializationAt_model_space_apply]
    exact (hV t ht).contMDiffWithinAt

set_option backward.isDefEq.respectTransparency false in
lemma smoothVF_iff {X : VF 2 E2} : IsSmoothVF X ↔ ContDiff ℝ ∞ (flat X) := by
  unfold IsSmoothVF
  rw [← contMDiffOn_univ, ← contDiffOn_univ]
  exact contMDiffOn_vectorSpace_iff_contDiffOn

set_option backward.isDefEq.respectTransparency false in
lemma vel_eq (c : ℝ → E2) (s : Set ℝ) (t : ℝ) : vec (vel (n := 2) c s) t = derivWithin c s t := by
  simp only [vec, vel]
  rw [mfderivWithin_eq_fderivWithin]
  rfl

/-- `D/dt` along `c` is the ordinary derivative, for every operation satisfying Milnor's axioms. -/
lemma flatD {c : ℝ → E2} {s : Set ℝ} {D : FA 2 c → FA 2 c}
    (hD : IsCovDerivAlong cov c s D) (hc : ContDiffOn ℝ ∞ c s) {V : FA 2 c}
    (hV : IsSmoothAlong c s V) {t : ℝ} (ht : t ∈ s) :
    vec (D V) t = derivWithin (vec V) s t := by
  obtain ⟨hadd, hsmul, hY⟩ := hD
  have hV' := (smoothAlong_iff.1 hV).2
  set e : Fin 2 → E2 := fun i => EuclideanSpace.single i 1
  set f : Fin 2 → ℝ → ℝ := fun i t => vec V t i
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) s := fun i =>
    ((EuclideanSpace.proj i : E2 →L[ℝ] ℝ).contDiff.comp_contDiffOn hV')
  let Ei : Fin 2 → FA 2 c := fun i _ => e i
  have hEi : ∀ i, IsSmoothAlong c s (Ei i) := fun i =>
    smoothAlong_iff.2 ⟨hc, contDiffOn_const⟩
  have hfE : ∀ i, IsSmoothAlong c s (fun t => f i t • Ei i t) := fun i =>
    smoothAlong_iff.2 ⟨hc, (hf i).smul contDiffOn_const⟩
  have hDE : ∀ i, D (Ei i) t = 0 := fun i => by
    have h1 := hY (fun _ => e i) (smoothVF_iff.2 contDiff_const) t ht
    refine h1.trans ?_
    have h2 : fderiv ℝ (fun _ : E2 => e i) (c t) = 0 := by simp
    show (fderiv ℝ (fun _ : E2 => e i) (c t)) (vel c s t : E2) = 0
    rw [h2]
    rfl
  have hsplit : V = fun t => f 0 t • Ei 0 t + f 1 t • Ei 1 t := by
    have key : ∀ v : E2, v = v 0 • e 0 + v 1 • e 1 := by
      intro v; ext i; fin_cases i <;> simp [e]
    funext t
    exact key (vec V t)
  have hdiff : ∀ i, DifferentiableWithinAt ℝ (f i) s t := fun i =>
    ((hf i) t ht).differentiableWithinAt (by simp)
  rw [hsplit]
  simp only [vec]
  rw [hadd _ _ (hfE 0) (hfE 1) t ht, hsmul _ (hf 0) _ (hEi 0) t ht, hsmul _ (hf 1) _ (hEi 1) t ht,
    hDE 0, hDE 1]
  show _ = derivWithin (fun t => f 0 t • e 0 + f 1 t • e 1) s t
  rw [derivWithin_fun_add ((hdiff 0).smul_const _) ((hdiff 1).smul_const _),
    derivWithin_smul_const (hdiff 0), derivWithin_smul_const (hdiff 1)]
  simp [Ei]
  rfl

lemma isSymm : IsSymm (n := 2) (M := E2) cov := by
  intro X Y _ _ p
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_eq_lieBracketWithin]
  have := congrFun (VectorField.lieBracketWithin_univ (𝕜 := ℝ) (V := flat X) (W := flat Y)) p
  erw [this]
  rfl

lemma const_of_derivWithin_zero {s : Set ℝ} (hs : IsIntv s) {F : ℝ → E2}
    (hF : ContDiffOn ℝ ∞ F s) (h0 : ∀ t ∈ s, derivWithin F s t = 0) :
    ∀ t ∈ s, ∀ t' ∈ s, F t = F t' := by
  intro t ht t' ht'
  refine hs.1.convex.is_const_of_fderivWithin_eq_zero (hF.differentiableOn (by simp))
    (fun x hx => ?_) ht ht'
  refine ContinuousLinearMap.ext_ring ?_
  rw [zero_apply]
  exact h0 x hx

lemma contDiffOn_of_smoothCurve {c : ℝ → E2} {s : Set ℝ} (hc : IsSmoothCurve (n := 2) c s) :
    ContDiffOn ℝ ∞ c s :=
  contMDiffOn_iff_contDiffOn.1 hc

lemma vec_const_of_parallel {s : Set ℝ} (hs : IsIntv s) {c : ℝ → E2} (hc : ContDiffOn ℝ ∞ c s)
    {Q : FA 2 c} (hQ : IsParallel cov c s Q) : ∀ t ∈ s, ∀ t' ∈ s, vec Q t = vec Q t' := by
  obtain ⟨hQs, D, hD, hD0⟩ := hQ
  refine const_of_derivWithin_zero hs (smoothAlong_iff.1 hQs).2 fun x hx => ?_
  rw [← flatD hD hc hQs hx]
  exact hD0 x hx

lemma isCompat : letI := rb; IsCompat (n := 2) (M := E2) cov := by
  letI := rb
  intro s hs c hc P P' hP hP' t ht t' ht'
  have hc' := contDiffOn_of_smoothCurve hc
  show G (vec P t) (vec P' t) = G (vec P t') (vec P' t')
  rw [vec_const_of_parallel hs hc' hP t ht t' ht', vec_const_of_parallel hs hc' hP' t ht t' ht']

lemma isLC : letI := rb; IsLC (n := 2) (M := E2) cov :=
  ⟨cov_smooth, isSymm, isCompat⟩

/-- `D/dt := d/dt` satisfies Milnor's axioms along any smooth curve. -/
lemma isCovDerivAlong_deriv {c : ℝ → E2} {s : Set ℝ} (hs : IsIntv s) (hc : ContDiffOn ℝ ∞ c s) :
    IsCovDerivAlong (n := 2) cov c s (fun V t => derivWithin (vec V) s t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V W hV hW t ht
    have hV' := (smoothAlong_iff.1 hV).2
    have hW' := (smoothAlong_iff.1 hW).2
    show derivWithin (fun t => vec V t + vec W t) s t = derivWithin (vec V) s t + derivWithin (vec W) s t
    exact derivWithin_fun_add ((hV' t ht).differentiableWithinAt (by simp))
      ((hW' t ht).differentiableWithinAt (by simp))
  · intro f hf V hV t ht
    have hV' := (smoothAlong_iff.1 hV).2
    show derivWithin (fun t => f t • vec V t) s t =
      derivWithin f s t • vec V t + f t • derivWithin (vec V) s t
    rw [derivWithin_fun_smul ((hf t ht).differentiableWithinAt (by simp))
      ((hV' t ht).differentiableWithinAt (by simp)), add_comm]
  · intro Y hY t ht
    have hY' := smoothVF_iff.1 hY
    show derivWithin (fun t => flat Y (c t)) s t = fderiv ℝ (flat Y) (c t) (vec (vel c s) t)
    rw [vel_eq]
    exact (((hY'.differentiable (by simp)) (c t)).hasFDerivAt.comp_hasDerivWithinAt t
      ((hc t ht).differentiableWithinAt (by simp)).hasDerivWithinAt).derivWithin (hs.2 t ht)

lemma hasDerivAt_affine (q w : E2) (t : ℝ) : HasDerivAt (fun t : ℝ => q + t • w) w t := by
  simpa using ((hasDerivAt_id t).smul_const w).const_add q

lemma affine_isGeodesic (q w : E2) {s : Set ℝ} (hs : IsIntv s) :
    IsGeodesic (n := 2) cov (fun t => q + t • w) s := by
  have hc : ContDiff ℝ ∞ (fun t : ℝ => q + t • w) := by fun_prop
  have hvel : ∀ t ∈ s, vec (vel (n := 2) (fun t => q + t • w) s) t = w := by
    intro t ht
    rw [vel_eq]
    exact (hasDerivAt_affine q w t).hasDerivWithinAt.derivWithin (hs.2 t ht)
  have hsm : IsSmoothAlong (fun t => q + t • w) s (vel (n := 2) (fun t => q + t • w) s) :=
    smoothAlong_iff.2 ⟨hc.contDiffOn, (contDiffOn_const (c := w)).congr hvel⟩
  refine ⟨hs, hc.contMDiff.contMDiffOn, hsm, hsm, _, isCovDerivAlong_deriv hs hc.contDiffOn,
    fun t ht => ?_⟩
  show derivWithin (vec (vel (n := 2) (fun t => q + t • w) s)) s t = 0
  rw [derivWithin_congr hvel (hvel t ht)]
  simp

lemma isIntv_Icc : IsIntv (Set.Icc (0 : ℝ) 1) := ⟨Set.ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩

lemma geo_eq {γ : ℝ → E2} {q w : E2} (hγ : IsGeodesic (n := 2) cov γ (Set.Icc 0 1))
    (hI : InitData (n := 2) γ (Set.Icc 0 1) q w) : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t = q + t • w := by
  obtain ⟨hs, hc, hv, hpar⟩ := hγ
  have hc' := contDiffOn_of_smoothCurve hc
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have hvc := vec_const_of_parallel hs hc' hpar
  have hw : vec (vel (n := 2) γ (Set.Icc 0 1)) 0 = w := eq_of_heq hI.2
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1, derivWithin γ (Set.Icc 0 1) t = w := by
    intro t ht
    rw [← vel_eq, hvc t ht 0 h0mem, hw]
  have hF : ContDiffOn ℝ ∞ (fun t => γ t - (q + t • w)) (Set.Icc 0 1) :=
    hc'.sub (by fun_prop)
  have hF0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, derivWithin (fun t => γ t - (q + t • w)) (Set.Icc 0 1) t = 0 := by
    intro t ht
    rw [derivWithin_fun_sub ((hc' t ht).differentiableWithinAt (by simp))
      (hasDerivAt_affine q w t).differentiableAt.differentiableWithinAt, hd t ht,
      (hasDerivAt_affine q w t).hasDerivWithinAt.derivWithin (hs.2 t ht), sub_self]
  intro t ht
  have := const_of_derivWithin_zero hs hF hF0 t ht 0 h0mem
  rw [hI.1] at this
  simp only [zero_smul, add_zero, sub_self] at this
  exact sub_eq_zero.1 this

lemma expDefined (q w : E2) : ExpDefined (n := 2) cov q w := by
  refine ⟨_, affine_isGeodesic q w isIntv_Icc, by simp, heq_of_eq ?_⟩
  show vec (vel (n := 2) (fun t => q + t • w) (Set.Icc 0 1)) 0 = w
  rw [vel_eq]
  exact (hasDerivAt_affine q w 0).hasDerivWithinAt.derivWithin (isIntv_Icc.2 0 (by simp))

lemma expMap_eq (q w : E2) : expMap (n := 2) cov q w = q + w := by
  unfold expMap
  rw [dif_pos (expDefined q w)]
  have h := (expDefined q w).choose_spec
  rw [geo_eq h.1 h.2 1 (by simp), one_smul]

lemma tball_eq (q : E2) (ε : ℝ) : tball (n := 2) q ε = Metric.ball 0 ε := by
  ext w
  simp [tball, nrm]

lemma isNormBall (q : E2) {ε : ℝ} (_hε : 0 < ε) :
    IsNormBall (n := 2) cov q ε (Metric.ball q ε) := by
  have he : (fun w : E2 => expMap (n := 2) cov q w) = fun w => q + w := funext (expMap_eq q)
  refine ⟨Metric.isOpen_ball, fun w _ => expDefined q w, ?_, ?_, ?_, fun y => y - q, ?_, ?_⟩
  · rw [he]; exact (add_right_injective q).injOn
  · rw [he, tball_eq]
    ext y
    simp only [Set.mem_image, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨w, hw, rfl⟩; simpa [dist_eq_norm] using hw
    · intro hy; exact ⟨y - q, by simpa [dist_eq_norm] using hy, by abel⟩
  · rw [he]; exact (contDiff_const.add contDiff_id).contMDiff.contMDiffOn
  · exact (contDiff_id.sub contDiff_const).contMDiff.contMDiffOn
  · intro w _; rw [expMap_eq]; simp

lemma isPW_affine (q w : E2) {a b : ℝ} (hab : a < b) : IsPW (n := 2) (fun t => q + t • w) a b := by
  refine ⟨1, fun i => if i = 0 then a else b, by simp, by simp, ?_, ?_⟩
  · intro i hi
    obtain rfl : i = 0 := by omega
    simpa using hab
  · intro i _
    exact (by fun_prop : ContDiff ℝ ∞ (fun t : ℝ => q + t • w)).contMDiff.contMDiffOn

set_option backward.isDefEq.respectTransparency false in
lemma arcLen_affine (q w : E2) (a b : ℝ) :
    letI := rb
    arcLen (n := 2) (fun t => q + t • w) a b = (b - a) * Real.sqrt (G w w) := by
  letI := rb
  have h : ∀ t : ℝ, ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) (fun t : ℝ => q + t • w) t (1 : ℝ) :
      TangentSpace 𝓘(ℝ, E2) (q + t • w))‖ = Real.sqrt (G w w) := by
    intro t
    rw [norm_rb]
    have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E2) (fun t : ℝ => q + t • w) t (1 : ℝ) = w := by
      rw [mfderiv_eq_fderiv]
      exact (hasDerivAt_affine q w t).deriv
    rw [hd]
  unfold arcLen
  simp only [h, intervalIntegral.integral_const, smul_eq_mul]

end BNotions


lemma G_single1 (a : ℝ) : G (EuclideanSpace.single 1 a) (EuclideanSpace.single 1 a) = a ^ 2 / 4 := by
  rw [G_self]; simp

end RoundTrip.Glue.Flat
