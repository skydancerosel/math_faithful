import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_42

open Matrix Set Filter Topology Function Module
open scoped ContDiff Manifold Morse.MatrixInner

noncomputable section

namespace RoundTrip.V3_42

/-- The project's statement (no universe parameters), on the matrix model of `ℂPⁿ` with the
slice-submanifold structure `CP.isSliceSubmanifold.chartedSpace`: Milnor's formula on `U_k`
(`height_param`), the critical points are the `p_k = param k 0`, non-degenerate of index
`2 #{c_j < c_k}`, `f` is Morse, `k ↦ #{c_j < c_k}` is a bijection of `{0,…,n}`, and
`C_λ = 1` for `λ = 0, 2, …, 2n`, `0` otherwise. -/
def A : Prop :=
  type_of% @Morse.CP.height_param ∧ type_of% @Morse.CP.isCriticalPointM_height_iff ∧
    type_of% @Morse.CP.isNondegenerate_indexM_height ∧
    type_of% @Morse.CP.isNondegenerate_of_isCriticalPointM ∧ type_of% @Morse.CP.bijective_rank ∧
    type_of% @Morse.CP.critCount_height

theorem A_holds : A :=
  ⟨@Morse.CP.height_param, @Morse.CP.isCriticalPointM_height_iff,
    @Morse.CP.isNondegenerate_indexM_height, @Morse.CP.isNondegenerate_of_isCriticalPointM,
    @Morse.CP.bijective_rank, @Morse.CP.critCount_height⟩

/-! ### Glue: the quotient model of `ℂPⁿ` and the matrix model -/

section Glue

variable {n : ℕ}

/-- The matrix model of `ℂPⁿ`. -/
abbrev Gr (n : ℕ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := Morse.grassmannian (Fin (n + 1)) 1

/-- `z ↦ z zᴴ`. -/
def toMat (z : Fin (n + 1) → ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.of fun a b => z a * star (z b)

theorem mul_star_eq (w : ℂ) : w * star w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem sum_mul_star (z : Sph n) : ∑ a, z.1 a * star (z.1 a) = 1 := by
  simp only [mul_star_eq, ← Complex.ofReal_sum, z.2, Complex.ofReal_one]

theorem toMat_mem (z : Sph n) : toMat z.1 ∈ Gr n := by
  refine ⟨?_, ?_, ?_⟩
  · ext a b; simp [toMat, mul_comm]
  · ext a b
    simp only [toMat, mul_apply, of_apply]
    have : ∀ c, z.1 a * star (z.1 c) * (z.1 c * star (z.1 b)) =
        z.1 a * star (z.1 b) * (z.1 c * star (z.1 c)) := fun c => by ring
    simp only [this, ← Finset.mul_sum, sum_mul_star z, mul_one]
  · simp only [trace, diag, toMat, of_apply, sum_mul_star z, Nat.cast_one]

theorem toMat_smul (z : Fin (n + 1) → ℂ) (c : ℂ) (hc : ‖c‖ = 1) : toMat (c • z) = toMat z := by
  have hc' : c * star c = 1 := by rw [mul_star_eq, hc]; simp
  ext a b
  simp only [toMat, of_apply, Pi.smul_apply, smul_eq_mul, star_mul']
  calc c * z a * (star c * star (z b)) = (c * star c) * (z a * star (z b)) := by ring
    _ = _ := by rw [hc', one_mul]

/-- The class of `z` ↦ the projection `z zᴴ`. -/
def Emap : CPn n → Gr n :=
  Quot.lift (fun z : Sph n => (⟨toMat z.1, toMat_mem z⟩ : Gr n)) (by
    rintro z w ⟨c, hc, hw⟩
    apply Subtype.ext
    simp only [hw, toMat_smul _ c hc])

@[simp] theorem Emap_cls (z : Sph n) : (Emap (cls z) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) = toMat z.1 :=
  rfl

theorem continuous_toMat : Continuous (toMat : (Fin (n + 1) → ℂ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  have : (toMat : (Fin (n + 1) → ℂ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      fun z => Morse.CP.ofCLM (fun a b => z a * star (z b)) := rfl
  rw [this]
  refine Morse.CP.ofCLM.continuous.comp (continuous_pi fun a => continuous_pi fun b => ?_)
  exact (continuous_apply a).mul (continuous_star.comp (continuous_apply b))

theorem continuous_Emap : Continuous (Emap (n := n)) :=
  continuous_quot_lift _ ((continuous_toMat.comp continuous_subtype_val).subtype_mk _)

theorem toMat_inj {z w : Sph n} (h : toMat z.1 = toMat w.1) : ∃ c : ℂ, ‖c‖ = 1 ∧ w.1 = c • z.1 := by
  have hz : ∃ a, z.1 a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := sum_mul_star z
    simp [hcon] at this
  obtain ⟨a, ha⟩ := hz
  have hab : ∀ b, z.1 b * star (z.1 a) = w.1 b * star (w.1 a) := fun b => by
    have := congrFun (congrFun h b) a
    simpa [toMat] using this
  have hnorm : ‖w.1 a‖ = ‖z.1 a‖ := by
    have := hab a
    rw [mul_star_eq, mul_star_eq] at this
    have h2 : ‖z.1 a‖ ^ 2 = ‖w.1 a‖ ^ 2 := by exact_mod_cast this
    exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2).symm
  have hwa : w.1 a ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hnorm; exact ha (norm_eq_zero.1 hnorm.symm)
  refine ⟨star (z.1 a) / star (w.1 a), ?_, ?_⟩
  · rw [norm_div, norm_star, norm_star, hnorm, div_self (norm_ne_zero_iff.2 ha)]
  · funext b
    have hs : star (w.1 a) ≠ 0 := star_ne_zero.2 hwa
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    rw [← hab b, mul_comm]

theorem Emap_injective : Injective (Emap (n := n)) := by
  intro x y h
  induction x using Quot.ind with
  | mk z =>
  induction y using Quot.ind with
  | mk w =>
  have h' : toMat z.1 = toMat w.1 := congrArg Subtype.val h
  exact Quot.sound (toMat_inj h')

theorem isCompact_sph : IsCompact {z : Fin (n + 1) → ℂ | ∑ j, ‖z j‖ ^ 2 = 1} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_eq (continuous_finsetSum _ fun j _ => (continuous_apply j).norm.pow 2)
      continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Fin (n + 1) → ℂ)) (r := 1)).subset fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    have h1 : ‖z j‖ ^ 2 ≤ 1 := by
      rw [← (hz : ∑ j, ‖z j‖ ^ 2 = 1)]
      exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    nlinarith [norm_nonneg (z j)]

instance : CompactSpace (Sph n) := isCompact_iff_compactSpace.1 isCompact_sph

instance : CompactSpace (CPn n) :=
  Quot.compactSpace (r := Rel n)


/-- The conversion `ℝ^{2n}` (Euclidean, B's model) `≃ Fin n × Fin 2 → ℝ` (the project's model). -/
abbrev eqv (n : ℕ) : Model n ≃L[ℝ] Morse.CP.Model n := EuclideanSpace.equiv (Fin n × Fin 2) ℝ

theorem ccoord_eq (k : Fin (n + 1)) (z : Fin (n + 1) → ℂ) (i : Fin n) :
    ccoord k z i = Morse.CP.coordC k (toMat z) i := by
  have hre : (toMat z k k).re = ‖z k‖ ^ 2 := by
    simp only [toMat, of_apply, mul_star_eq, Complex.ofReal_re]
  rw [Morse.CP.coordC, hre, Real.sqrt_sq (norm_nonneg _), ccoord]
  simp only [toMat, of_apply]
  by_cases hz : z k = 0
  · simp [hz]
  · have hn : (‖z k‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
    field_simp
    rw [mul_assoc, mul_star_eq]
    push_cast
    ring

theorem phi_eq (k : Fin (n + 1)) (x : CPn n) :
    phi k x = (eqv n).symm (Morse.CP.coord k (Emap x).1) := by
  induction x using Quot.ind with
  | mk z =>
  change phiS k z = (eqv n).symm (Morse.CP.coord k (toMat z.1))
  simp only [phiS, ccoord_eq]
  rfl

theorem toMat_kk_re (z : Fin (n + 1) → ℂ) (k : Fin (n + 1)) : (toMat z k k).re = ‖z k‖ ^ 2 := by
  simp only [toMat, of_apply, mul_star_eq, Complex.ofReal_re]

theorem mem_U_iff (k : Fin (n + 1)) (x : CPn n) : x ∈ U k ↔ 0 < ((Emap x).1 k k).re := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Emap_cls, toMat_kk_re]
    exact pow_pos (norm_pos_iff.2 hw) 2
  · induction x using Quot.ind with
    | mk z =>
    intro h
    change 0 < (toMat z.1 k k).re at h
    rw [toMat_kk_re] at h
    refine ⟨z, fun h0 => ?_, rfl⟩
    rw [h0, norm_zero] at h
    simp at h

theorem mem_ball_iff (y : Model n) : y ∈ Metric.ball (0 : Model n) 1 ↔ Morse.CP.nsq (eqv n y) < 1 := by
  rw [Metric.mem_ball, dist_zero_right, EuclideanSpace.norm_eq, Real.sqrt_lt' one_pos, one_pow]
  simp only [Morse.CP.nsq, Real.norm_eq_abs, sq_abs]
  rfl

theorem continuous_kk (k : Fin (n + 1)) : Continuous fun x : CPn n => ((Emap x).1 k k).re :=
  Complex.continuous_re.comp (((continuous_apply k).comp (continuous_apply k)).comp
    (continuous_subtype_val.comp continuous_Emap))

theorem isOpen_U (k : Fin (n + 1)) : IsOpen (U k : Set (CPn n)) := by
  have : (U k : Set (CPn n)) = (fun x : CPn n => ((Emap x).1 k k).re) ⁻¹' Ioi 0 := by
    ext x; exact mem_U_iff k x
  rw [this]
  exact isOpen_Ioi.preimage (continuous_kk k)

/-- `param k` as a map into the matrix model (junk value outside the closed ball). -/
def Pk (k : Fin (n + 1)) (z : Morse.CP.Model n) : Gr n :=
  if h : Morse.CP.nsq z ≤ 1 then ⟨Morse.CP.param k z, Morse.CP.param_mem k h⟩
  else ⟨Morse.CP.param k 0, Morse.CP.param_zero_mem k⟩

theorem Pk_val (k : Fin (n + 1)) {z : Morse.CP.Model n} (hz : Morse.CP.nsq z < 1) :
    (Pk k z).1 = Morse.CP.param k z := by
  rw [Pk, dif_pos hz.le]

theorem continuousOn_Pk (k : Fin (n + 1)) :
    ContinuousOn (Pk k) {z : Morse.CP.Model n | Morse.CP.nsq z < 1} := by
  refine (Topology.IsInducing.subtypeVal).continuousOn_iff.2 ?_
  refine (Morse.CP.contDiffOn_param k).continuousOn.congr fun z hz => ?_
  exact Pk_val k hz

variable (hvec : type_of% @Morse.CP.exists_vec_of_mem)
  (hcp : type_of% @Morse.CP.coord_param)
  (hpc : type_of% @Morse.CP.nsq_coord_lt_and_param_coord)
  (hdiag : type_of% @Morse.CP.exists_re_diag_pos)

include hvec in
theorem Emap_surjective : Surjective (Emap (n := n)) := by
  rintro ⟨P, hP⟩
  obtain ⟨f, hf1, hf⟩ := hvec hP
  have hf1' : ∑ j, ‖f j‖ ^ 2 = 1 := by simpa [Complex.normSq_eq_norm_sq] using hf1
  refine ⟨cls ⟨f, hf1'⟩, Subtype.ext ?_⟩
  ext a b
  change toMat f a b = P a b
  rw [hf a b]
  rfl

/-- The homeomorphism between the quotient model and the matrix model of `ℂPⁿ`. -/
def EH : CPn n ≃ₜ Gr n :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective Emap ⟨Emap_injective, Emap_surjective hvec⟩) continuous_Emap

theorem EH_apply (x : CPn n) : EH hvec x = Emap x := rfl

/-- Milnor's coordinates on `U_k`, as a chart of the quotient model with values in `ℝ^{2n}`. -/
def chart (k : Fin (n + 1)) : OpenPartialHomeomorph (CPn n) (Model n) where
  toFun := phi k
  invFun y := (EH hvec).symm (Pk k (eqv n y))
  source := U k
  target := Metric.ball 0 1
  map_source' x hx := by
    rw [mem_ball_iff, phi_eq, ContinuousLinearEquiv.apply_symm_apply]
    exact (hpc k (Emap x).2 ((mem_U_iff k x).1 hx)).1
  map_target' y hy := by
    rw [mem_ball_iff] at hy
    rw [mem_U_iff, ← EH_apply hvec, Homeomorph.apply_symm_apply, Pk_val k hy,
      Morse.CP.param_kk k hy.le, Complex.ofReal_re]
    linarith
  left_inv' x hx := by
    obtain ⟨h1, h2⟩ := hpc k (Emap x).2 ((mem_U_iff k x).1 hx)
    change (EH hvec).symm (Pk k (eqv n (phi k x))) = x
    rw [phi_eq, ContinuousLinearEquiv.apply_symm_apply]
    have : Pk k (Morse.CP.coord k (Emap x).1) = EH hvec x := by
      apply Subtype.ext
      rw [Pk_val k h1, h2]
      rfl
    rw [this, Homeomorph.symm_apply_apply]
  right_inv' y hy := by
    rw [mem_ball_iff] at hy
    change phi k ((EH hvec).symm (Pk k (eqv n y))) = y
    rw [phi_eq, ← EH_apply hvec, Homeomorph.apply_symm_apply, Pk_val k hy, hcp k hy,
      ContinuousLinearEquiv.symm_apply_apply]
  open_source := isOpen_U k
  open_target := Metric.isOpen_ball
  continuousOn_toFun := by
    have : (phi k : CPn n → Model n) =
        fun x => (eqv n).symm (Morse.CP.coord k (Emap x).1) := funext (phi_eq k)
    change ContinuousOn (phi k) (U k)
    rw [this]
    refine (eqv n).symm.continuous.comp_continuousOn ?_
    refine (Morse.CP.contDiffOn_coord k).continuousOn.comp
      (continuous_subtype_val.comp continuous_Emap).continuousOn fun x hx => ?_
    exact (mem_U_iff k x).1 hx
  continuousOn_invFun := by
    refine (EH hvec).symm.continuous.comp_continuousOn ?_
    refine (continuousOn_Pk k).comp (eqv n).continuous.continuousOn fun y hy => ?_
    exact (mem_ball_iff y).1 hy

include hdiag in
theorem exists_mem_U (x : CPn n) : ∃ k, x ∈ U k := by
  obtain ⟨k, hk⟩ := hdiag (Emap x).2
  exact ⟨k, (mem_U_iff k x).2 hk⟩

/-- The smooth structure on the quotient model given by Milnor's charts. -/
@[instance_reducible]
def cs : ChartedSpace (Model n) (CPn n) where
  atlas := range (chart hvec hcp hpc)
  chartAt x := chart hvec hcp hpc (exists_mem_U hdiag x).choose
  mem_chart_source x := (exists_mem_U hdiag x).choose_spec
  chart_mem_atlas _ := ⟨_, rfl⟩

theorem chart_symm_val (k : Fin (n + 1)) {y : Model n} (hy : y ∈ Metric.ball (0 : Model n) 1) :
    (Emap ((chart hvec hcp hpc k).symm y)).1 = Morse.CP.param k (eqv n y) := by
  change (Emap ((EH hvec).symm (Pk k (eqv n y)))).1 = _
  rw [← EH_apply hvec, Homeomorph.apply_symm_apply, Pk_val k ((mem_ball_iff y).1 hy)]

theorem isManifold : letI := cs (n := n) hvec hcp hpc hdiag; IsManifold 𝓘(ℝ, Model n) ∞ (CPn n) := by
  letI := cs (n := n) hvec hcp hpc hdiag
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  obtain ⟨k, rfl⟩ := he
  obtain ⟨j, rfl⟩ := he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, inter_univ,
    preimage_id, Function.comp_id, Function.id_comp]
  have hsrc : ∀ y ∈ ((chart hvec hcp hpc k).symm.trans (chart hvec hcp hpc j)).source,
      y ∈ Metric.ball (0 : Model n) 1 ∧ 0 < (Morse.CP.param k (eqv n y) j j).re := by
    intro y hy
    rw [OpenPartialHomeomorph.trans_source] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy1' : y ∈ Metric.ball (0 : Model n) 1 := hy1
    refine ⟨hy1', ?_⟩
    have := (mem_U_iff j _).1 hy2
    rwa [chart_symm_val hvec hcp hpc k hy1'] at this
  have hsm : ContDiffOn ℝ ∞ (fun y : Model n =>
      (eqv n).symm (Morse.CP.coord j (Morse.CP.param k (eqv n y))))
      ((chart hvec hcp hpc k).symm.trans (chart hvec hcp hpc j)).source := by
    refine (eqv n).symm.contDiff.comp_contDiffOn ?_
    refine (Morse.CP.contDiffOn_coord j).comp ?_ fun y hy => (hsrc y hy).2
    refine (Morse.CP.contDiffOn_param k).comp (eqv n).contDiff.contDiffOn fun y hy => ?_
    exact (mem_ball_iff y).1 (hsrc y hy).1
  refine hsm.congr fun y hy => ?_
  change phi j ((chart hvec hcp hpc k).symm y) = _
  rw [phi_eq, chart_symm_val hvec hcp hpc k (hsrc y hy).1]

theorem isMilnorChart (k : Fin (n + 1)) :
    letI := cs (n := n) hvec hcp hpc hdiag; IsMilnorChart n k := by
  letI := cs (n := n) hvec hcp hpc hdiag
  haveI := isManifold (n := n) hvec hcp hpc hdiag
  have hmem : chart hvec hcp hpc k ∈ IsManifold.maximalAtlas 𝓘(ℝ, Model n) ∞ (CPn n) :=
    IsManifold.subset_maximalAtlas ⟨k, rfl⟩
  exact ⟨(Morse.isSmoothCoord_of_mem_maximalAtlas hmem).toPartialDiffeomorph, rfl, rfl,
    fun _ _ => rfl⟩

end Glue

/-! ### Glue for Milnor's function -/

section FGlue

variable {n : ℕ}

theorem fC_eq (c : Fin (n + 1) → ℝ) (x : CPn n) : fC c x = Morse.CP.height c (Emap x).1 := by
  induction x using Quot.ind with
  | mk z =>
  change ∑ j, c j * ‖z.1 j‖ ^ 2 = ∑ j, c j * (toMat z.1 j j).re
  simp only [toMat_kk_re]

theorem pt_mem (k : Fin (n + 1)) : pt k ∈ (U k : Set (CPn n)) :=
  ⟨⟨Pi.single k 1, single_mem k⟩, by simp, rfl⟩

theorem phi_pt (k : Fin (n + 1)) : phi k (pt k : CPn n) = 0 := by
  change phiS k ⟨Pi.single k 1, single_mem k⟩ = 0
  have h : ∀ j, ccoord k (Pi.single k (1 : ℂ) : Fin (n + 1) → ℂ) j = 0 := fun j => by
    simp [ccoord, Fin.succAbove_ne k j]
  simp only [phiS, h, Complex.zero_re, Complex.zero_im, ite_self]
  rfl

theorem pt_injective : Injective (pt : Fin (n + 1) → CPn n) := by
  intro j k h
  have h1 := congrArg (fun x => (Emap x).1 k k) h
  simp only [pt, Emap_cls, toMat, of_apply] at h1
  by_contra hne
  simp [Ne.symm hne] at h1

/-- The Euclidean conversion as a chart of `ℝ^{2n}`. -/
abbrev eqvH (n : ℕ) : OpenPartialHomeomorph (Model n) (Morse.CP.Model n) :=
  (eqv n).toHomeomorph.toOpenPartialHomeomorph

variable [cs : ChartedSpace (Model n) (CPn n)] [IsManifold 𝓘(ℝ, Model n) ∞ (CPn n)]

/-- In a smooth structure where Milnor's coordinates on `U_k` are a diffeomorphism `Φ` onto the
ball, `Φ` followed by the conversion to the project's model is a smooth coordinate system. -/
theorem isSmoothCoord_psi
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model n) 𝓘(ℝ, Model n) (CPn n) (Model n) ∞) :
    Morse.IsSmoothCoord (Model n) (Φ.toOpenPartialHomeomorph.trans (eqvH n)) :=
  (Morse.isSmoothCoord_toOpenPartialHomeomorph Φ).trans (eqv n).contDiff.contDiffOn
    (eqv n).symm.contDiff.contDiffOn

variable {k : Fin (n + 1)} {Φ : PartialDiffeomorph 𝓘(ℝ, Model n) 𝓘(ℝ, Model n) (CPn n) (Model n) ∞}
  (hsrc : Φ.source = U k) (htgt : Φ.target = Metric.ball (0 : Model n) 1)
  (hΦ : ∀ x ∈ U k, Φ x = phi k x)
include hsrc htgt hΦ

theorem psi_source : (Φ.toOpenPartialHomeomorph.trans (eqvH n)).source = U k := by
  rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source, preimage_univ,
    inter_univ]
  exact hsrc

theorem psi_apply {x : CPn n} (hx : x ∈ U k) :
    (Φ.toOpenPartialHomeomorph.trans (eqvH n)) x = Morse.CP.coord k (Emap x).1 := by
  change eqv n (Φ x) = _
  rw [hΦ x hx, phi_eq, ContinuousLinearEquiv.apply_symm_apply]

theorem psi_target :
    (Φ.toOpenPartialHomeomorph.trans (eqvH n)).target = {w | Morse.CP.nsq w < 1} := by
  rw [OpenPartialHomeomorph.trans_target]
  ext w
  simp only [Homeomorph.toOpenPartialHomeomorph_target, mem_inter_iff, mem_univ, true_and,
    mem_preimage, mem_ofPred_eq]
  change (eqv n).symm w ∈ Φ.target ↔ _
  rw [htgt, mem_ball_iff, ContinuousLinearEquiv.apply_symm_apply]

theorem Emap_psi_symm {w : Morse.CP.Model n} (hw : Morse.CP.nsq w < 1) :
    (Emap ((Φ.toOpenPartialHomeomorph.trans (eqvH n)).symm w)).1 = Morse.CP.param k w := by
  set ψ := Φ.toOpenPartialHomeomorph.trans (eqvH n)
  have hwt : w ∈ ψ.target := by rw [psi_target hsrc htgt hΦ]; exact hw
  have hx : ψ.symm w ∈ U k := psi_source hsrc htgt hΦ ▸ ψ.map_target hwt
  have h1 : ψ (ψ.symm w) = w := ψ.right_inv hwt
  rw [psi_apply hsrc htgt hΦ hx] at h1
  obtain ⟨-, h2⟩ := Morse.CP.nsq_coord_lt_and_param_coord k (Emap (ψ.symm w)).2
    ((mem_U_iff k _).1 hx)
  rw [h1] at h2
  exact h2.symm

/-- On the target, `f ∘ ψ⁻¹` is Milnor's model `c_k + Σ (c_j − c_k)(x_j² + y_j²)` (A's
`height_param`). -/
theorem fC_psi_symm (hhp : type_of% @Morse.CP.height_param) (c : Fin (n + 1) → ℝ)
    {w : Morse.CP.Model n} (hw : Morse.CP.nsq w < 1) :
    fC c ((Φ.toOpenPartialHomeomorph.trans (eqvH n)).symm w) = Morse.CP.model c k w := by
  set ψ := Φ.toOpenPartialHomeomorph.trans (eqvH n)
  have hwt : w ∈ ψ.target := by rw [psi_target hsrc htgt hΦ]; exact hw
  have hx : ψ.symm w ∈ U k := psi_source hsrc htgt hΦ ▸ ψ.map_target hwt
  have h1 : ψ (ψ.symm w) = w := ψ.right_inv hwt
  rw [psi_apply hsrc htgt hΦ hx] at h1
  obtain ⟨-, h2⟩ := Morse.CP.nsq_coord_lt_and_param_coord k (Emap (ψ.symm w)).2
    ((mem_U_iff k _).1 hx)
  rw [h1] at h2
  rw [fC_eq, ← h2, hhp c k hw.le]

theorem fC_eventuallyEq (hhp : type_of% @Morse.CP.height_param) (c : Fin (n + 1) → ℝ)
    {x : CPn n} (hx : x ∈ U k) :
    fC c ∘ (Φ.toOpenPartialHomeomorph.trans (eqvH n)).symm
      =ᶠ[𝓝 ((Φ.toOpenPartialHomeomorph.trans (eqvH n)) x)] Morse.CP.model c k := by
  set ψ := Φ.toOpenPartialHomeomorph.trans (eqvH n)
  have hxs : x ∈ ψ.source := by rw [psi_source hsrc htgt hΦ]; exact hx
  filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hxs)] with w hw
  rw [psi_target hsrc htgt hΦ] at hw
  exact fC_psi_symm hsrc htgt hΦ hhp c hw

theorem contMDiffAt_fC (hhp : type_of% @Morse.CP.height_param) (c : Fin (n + 1) → ℝ)
    {x : CPn n} (hx : x ∈ U k) : ContMDiffAt 𝓘(ℝ, Model n) 𝓘(ℝ) ∞ (fC c) x := by
  set ψ := Φ.toOpenPartialHomeomorph.trans (eqvH n)
  have hy := isSmoothCoord_psi Φ
  have hxs : x ∈ ψ.source := by rw [psi_source hsrc htgt hΦ]; exact hx
  have hψ : ContMDiffAt 𝓘(ℝ, Model n) 𝓘(ℝ, Morse.CP.Model n) ∞ ψ x :=
    (hy.contMDiffOn x hxs).contMDiffAt (ψ.open_source.mem_nhds hxs)
  have hm : ContMDiffAt 𝓘(ℝ, Morse.CP.Model n) 𝓘(ℝ) ∞ (Morse.CP.model c k) (ψ x) := by
    have : ContDiff ℝ ∞ (Morse.CP.model c k) := by unfold Morse.CP.model; fun_prop
    exact this.contMDiff.contMDiffAt
  refine (hm.comp x hψ).congr_of_eventuallyEq ?_
  filter_upwards [ψ.open_source.mem_nhds hxs] with x' hx'
  have hx'U : x' ∈ U k := psi_source hsrc htgt hΦ ▸ hx'
  have := fC_psi_symm hsrc htgt hΦ hhp c (w := ψ x') (by
    have := ψ.map_source hx'
    rwa [psi_target hsrc htgt hΦ] at this)
  rw [ψ.left_inv hx'] at this
  exact this

end FGlue

variable {n : ℕ}

theorem exists_U (x : CPn n) : ∃ k, x ∈ U k :=
  exists_mem_U Morse.CP.exists_re_diag_pos x

/-- A ⇒ B. In any smooth structure in which Milnor's coordinates are diffeomorphisms onto the
ball, compute in the coordinate system `ψ_k = Φ_k` (followed by the conversion to the project's
model): there `f = Milnor's model` by A's `height_param`; critical points, non-degeneracy and index
are then those of the quadratic model (project lemmas outside A), and the count uses A's
`bijective_rank`. A's statements about the slice-submanifold structure of the matrix model
(`isCriticalPointM_height_iff`, `isNondegenerate_indexM_height`, `critCount_height`, …) are not
used: B's smooth structure is not that one. -/
theorem A_to_B : A → B := by
  rintro ⟨hhp, -, -, -, hbij, -⟩ n c hc cs hman hmil
  choose Φ hsrc htgt hΦ using hmil
  have hsc := fun k => isSmoothCoord_psi (Φ k)
  have hcont : ContMDiff 𝓘(ℝ, Model n) 𝓘(ℝ) ∞ (fC c) := fun x => by
    obtain ⟨k, hk⟩ := exists_U x
    exact contMDiffAt_fC (hsrc k) (htgt k) (hΦ k) hhp c hk
  -- critical points in `U_k`
  have hcritU : ∀ k, ∀ x ∈ U k, Morse.IsCriticalPointM (Model n) (fC c) x ↔ x = pt k := by
    intro k x hx
    have hxs : x ∈ ((Φ k).toOpenPartialHomeomorph.trans (eqvH n)).source := by
      rw [psi_source (hsrc k) (htgt k) (hΦ k)]; exact hx
    rw [(hsc k).isCriticalPointM_iff hxs ((hcont x).mdifferentiableAt (by simp))]
    constructor
    · intro h
      have h' : Morse.IsCriticalPoint (Morse.CP.model c k) _ :=
        HasFDerivAt.congr_of_eventuallyEq h (fC_eventuallyEq (hsrc k) (htgt k) (hΦ k) hhp c hx).symm
      rw [Morse.CP.isCriticalPoint_model_iff hc] at h'
      have hpt : pt k ∈ ((Φ k).toOpenPartialHomeomorph.trans (eqvH n)).source := by
        rw [psi_source (hsrc k) (htgt k) (hΦ k)]; exact pt_mem k
      refine ((Φ k).toOpenPartialHomeomorph.trans (eqvH n)).injOn hxs hpt ?_
      rw [h']
      change (0 : Morse.CP.Model n) = eqv n (Φ k (pt k))
      rw [hΦ k _ (pt_mem k), phi_pt, map_zero]
    · rintro rfl
      have h0 : ((Φ k).toOpenPartialHomeomorph.trans (eqvH n)) (pt k) = 0 := by
        change eqv n (Φ k (pt k)) = 0
        rw [hΦ k _ (pt_mem k), phi_pt, map_zero]
      have h' : Morse.IsCriticalPoint (Morse.CP.model c k) 0 :=
        (Morse.CP.isCriticalPoint_model_iff hc k 0).2 rfl
      rw [← h0] at h'
      exact HasFDerivAt.congr_of_eventuallyEq h' (fC_eventuallyEq (hsrc k) (htgt k) (hΦ k) hhp c hx)
  have hcrit : ∀ x, Morse.IsCriticalPointM (Model n) (fC c) x ↔ ∃ k, x = pt k := by
    intro x
    constructor
    · intro h
      obtain ⟨k, hk⟩ := exists_U x
      exact ⟨k, (hcritU k x hk).1 h⟩
    · rintro ⟨k, rfl⟩
      exact (hcritU k _ (pt_mem k)).2 rfl
  have hpt : ∀ k, Morse.IsNondegenerateCriticalPointM (Model n) (fC c) (pt k) ∧
      Morse.indexM (Model n) (fC c) (pt k) = 2 * rk c k := by
    intro k
    have hxs : pt k ∈ ((Φ k).toOpenPartialHomeomorph.trans (eqvH n)).source := by
      rw [psi_source (hsrc k) (htgt k) (hΦ k)]; exact pt_mem k
    have h0 : ((Φ k).toOpenPartialHomeomorph.trans (eqvH n)) (pt k) = 0 := by
      change eqv n (Φ k (pt k)) = 0
      rw [hΦ k _ (pt_mem k), phi_pt, map_zero]
    have hev := fC_eventuallyEq (hsrc k) (htgt k) (hΦ k) hhp c (pt_mem k)
    rw [h0] at hev
    have hf2 : ContMDiffAt 𝓘(ℝ, Model n) 𝓘(ℝ) 2 (fC c) (pt k) :=
      (hcont (pt k)).of_le (WithTop.coe_le_coe.2 le_top)
    have hcr : Morse.IsCriticalPointM (Model n) (fC c) (pt k) := (hcritU k _ (pt_mem k)).2 rfl
    refine ⟨?_, ?_⟩
    · rw [(hsc k).isNondegenerateCriticalPointM_iff hxs hf2, h0]
      refine ⟨HasFDerivAt.congr_of_eventuallyEq ((Morse.CP.isCriticalPoint_model_iff hc k 0).2 rfl) hev, ?_⟩
      rw [Morse.hessian_congr hev]
      exact Morse.CP.isNondegenerate_hessian_model hc k 0
    · rw [← (hsc k).index_eq hxs hf2 hcr, h0, Morse.hessian_congr hev]
      exact Morse.CP.index_hessian_model k 0
  refine ⟨hcont, ?_, hcritU, hcrit, hpt, ?_⟩
  · -- Milnor's formula on `U_k`
    intro k x hx
    have hxs : x ∈ ((Φ k).toOpenPartialHomeomorph.trans (eqvH n)).source := by
      rw [psi_source (hsrc k) (htgt k) (hΦ k)]; exact hx
    have hmt := ((Φ k).toOpenPartialHomeomorph.trans (eqvH n)).map_source hxs
    rw [psi_target (hsrc k) (htgt k) (hΦ k)] at hmt
    have h := fC_psi_symm (hsrc k) (htgt k) (hΦ k) hhp c hmt
    rw [((Φ k).toOpenPartialHomeomorph.trans (eqvH n)).left_inv hxs,
      psi_apply (hsrc k) (htgt k) (hΦ k) hx] at h
    rw [h, Morse.CP.model, Morse.CP.wform_apply, phi_eq, Fintype.sum_prod_type]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.sum_univ_two, Morse.CP.weight]
    change _ = (c (k.succAbove j) - c k) *
      (Morse.CP.coord k (Emap x).1 (j, 0) ^ 2 + Morse.CP.coord k (Emap x).1 (j, 1) ^ 2)
    ring
  · -- the count
    intro l
    have hset : {x : CPn n | Morse.IsCriticalPointM (Model n) (fC c) x ∧
        Morse.indexM (Model n) (fC c) x = l} = pt '' {k | 2 * rk c k = l} := by
      ext x
      constructor
      · rintro ⟨hx, hi⟩
        obtain ⟨k, rfl⟩ := (hcrit x).1 hx
        exact ⟨k, by rw [← hi, (hpt k).2]; rfl, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨(hcrit _).2 ⟨k, rfl⟩, (hpt k).2.trans hk⟩
    rw [hset, Set.ncard_image_of_injective _ pt_injective]
    obtain ⟨hinj, hsurj⟩ := hbij hc
    split_ifs with hl
    · obtain ⟨⟨m, hm⟩, hl2⟩ := hl
      obtain ⟨k, hk⟩ := hsurj ⟨m, by omega⟩
      have hk' : Morse.CP.rank c k = m := congrArg Fin.val hk
      rw [Set.ncard_eq_one]
      refine ⟨k, Set.eq_singleton_iff_unique_mem.2 ⟨?_, fun j hj => hinj (Fin.ext ?_)⟩⟩
      · change 2 * Morse.CP.rank c k = l; omega
      · change 2 * Morse.CP.rank c j = l at hj
        change Morse.CP.rank c j = Morse.CP.rank c k
        omega
    · rw [Set.ncard_eq_zero]
      refine Set.eq_empty_of_forall_notMem fun k hk => hl ⟨⟨Morse.CP.rank c k, ?_⟩, ?_⟩
      · change 2 * Morse.CP.rank c k = l at hk; omega
      · have := Morse.CP.rank_lt (c := c) k
        change 2 * Morse.CP.rank c k = l at hk; omega

#rt_check RoundTrip.V3_42.A_to_B [Morse.CP.height_param, Morse.CP.isCriticalPointM_height_iff, Morse.CP.isNondegenerate_indexM_height, Morse.CP.isNondegenerate_of_isCriticalPointM, Morse.CP.bijective_rank, Morse.CP.critCount_height]

/-! ### Glue for B ⇒ A: the matrix model with its slice structure, and the transport -/

section SliceGlue

variable {n : ℕ}

/-- Local corestriction to a slice submanifold (pointwise version of
`Milnor.IsSliceSubmanifold.contMDiff_codRestrict`). -/
theorem contMDiffAt_codRestrict {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {S : Set V} (hS : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W S)
    {F : E' → V} {x : E'} (hF : ContMDiffAt 𝓘(ℝ, E') 𝓘(ℝ, V) ∞ F x) (hFS : ∀ x, F x ∈ S) :
    letI := hS.chartedSpace
    ContMDiffAt 𝓘(ℝ, E') 𝓘(ℝ, Z) ∞ (fun x => (⟨F x, hFS x⟩ : S)) x := by
  letI := hS.chartedSpace
  haveI := hS.isManifold
  rw [contMDiffAt_iff_target]
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.2 hF.continuousAt, ?_⟩
  set σ := (hS (F x) (hFS x)).choose with hσ
  have hmem : F x ∈ σ.φ.source := (hS (F x) (hFS x)).choose_spec
  have hchart : extChartAt 𝓘(ℝ, Z) (⟨F x, hFS x⟩ : S) = σ.toChart.toPartialEquiv :=
    hS.extChartAt_eq ⟨F x, hFS x⟩
  rw [hchart]
  have hφ : ContMDiffAt 𝓘(ℝ, V) 𝓘(ℝ, Z × W) ∞ σ.φ (F x) :=
    (σ.φ.contMDiffOn (F x) hmem).contMDiffAt (σ.φ.open_source.mem_nhds hmem)
  have h1 : ContMDiffAt 𝓘(ℝ, E') 𝓘(ℝ, Z × W) ∞ (σ.φ ∘ F) x := hφ.comp x hF
  have hfst : ContMDiff 𝓘(ℝ, Z × W) 𝓘(ℝ, Z) ∞ (Prod.fst : Z × W → Z) :=
    (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Z × W → Z)).contMDiff
  exact hfst.contMDiffAt.comp x h1

theorem continuous_kkG (k : Fin (n + 1)) : Continuous fun P : Gr n => (P.1 k k).re := by
  have h : Continuous fun P : Gr n => P.1 k k :=
    (continuous_apply k).comp ((continuous_apply k).comp continuous_subtype_val)
  exact Complex.continuous_re.comp h

/-- Milnor's coordinates on `U_k` of the matrix model. -/
def chiG (k : Fin (n + 1)) : OpenPartialHomeomorph (Gr n) (Morse.CP.Model n) where
  toFun P := Morse.CP.coord k P.1
  invFun := Pk k
  source := {P | 0 < (P.1 k k).re}
  target := {w | Morse.CP.nsq w < 1}
  map_source' P hP := (Morse.CP.nsq_coord_lt_and_param_coord k P.2 hP).1
  map_target' w hw := by
    change 0 < ((Pk k w).1 k k).re
    rw [Pk_val k hw, Morse.CP.param_kk k (le_of_lt hw), Complex.ofReal_re]
    have : Morse.CP.nsq w < 1 := hw
    linarith
  left_inv' P hP := by
    obtain ⟨h1, h2⟩ := Morse.CP.nsq_coord_lt_and_param_coord k P.2 hP
    exact Subtype.ext ((Pk_val k h1).trans h2)
  right_inv' w hw := by
    change Morse.CP.coord k (Pk k w).1 = w
    rw [Pk_val k hw]
    exact Morse.CP.coord_param k hw
  open_source := isOpen_Ioi.preimage (continuous_kkG k)
  open_target := isOpen_lt Morse.CP.contDiff_nsq.continuous continuous_const
  continuousOn_toFun := (Morse.CP.contDiffOn_coord k).continuousOn.comp
    continuous_subtype_val.continuousOn fun P hP => hP
  continuousOn_invFun := continuousOn_Pk k

theorem isSmoothCoord_chiG (k : Fin (n + 1)) :
    letI := (Morse.CP.isSliceSubmanifold (n := n)).chartedSpace
    Morse.IsSmoothCoord (Morse.CP.Model n) (chiG (n := n) k) := by
  letI := (Morse.CP.isSliceSubmanifold (n := n)).chartedSpace
  haveI := (Morse.CP.isSliceSubmanifold (n := n)).isManifold
  constructor
  · have hv := (Morse.CP.isSliceSubmanifold (n := n)).contMDiff_val
    refine ((Morse.CP.contDiffOn_coord k).contMDiffOn.comp hv.contMDiffOn fun P hP => hP)
  · intro w hw
    have hw' : Morse.CP.nsq w < 1 := hw
    have hO : IsOpen {w : Morse.CP.Model n | Morse.CP.nsq w < 1} :=
      isOpen_lt Morse.CP.contDiff_nsq.continuous continuous_const
    have hF : ContMDiffAt 𝓘(ℝ, Morse.CP.Model n) 𝓘(ℝ, Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) ∞
        (fun w => (Pk k w).1) w := by
      refine ContDiffAt.contMDiffAt ?_
      refine ((Morse.CP.contDiffOn_param k).contDiffAt (hO.mem_nhds hw')).congr_of_eventuallyEq ?_
      filter_upwards [hO.mem_nhds hw'] with w' hw'' using Pk_val k hw''
    exact (contMDiffAt_codRestrict Morse.CP.isSliceSubmanifold hF (fun w => (Pk k w).2)).contMDiffWithinAt

end SliceGlue

/-! ### B ⇒ A -/

section Transport

variable {n : ℕ}

/-- The Milnor structure on the quotient model (the glue above, with the project's lemmas). -/
abbrev csM (n : ℕ) : ChartedSpace (Model n) (CPn n) :=
  cs (n := n) Morse.CP.exists_vec_of_mem Morse.CP.coord_param
    Morse.CP.nsq_coord_lt_and_param_coord Morse.CP.exists_re_diag_pos

theorem isManifold_csM : letI := csM n; IsManifold 𝓘(ℝ, Model n) ∞ (CPn n) :=
  isManifold (n := n) Morse.CP.exists_vec_of_mem Morse.CP.coord_param
    Morse.CP.nsq_coord_lt_and_param_coord Morse.CP.exists_re_diag_pos

theorem isMilnorChart_csM (k : Fin (n + 1)) : letI := csM n; IsMilnorChart n k :=
  isMilnorChart (n := n) Morse.CP.exists_vec_of_mem Morse.CP.coord_param
    Morse.CP.nsq_coord_lt_and_param_coord Morse.CP.exists_re_diag_pos k

/-- **The transport**: critical points, non-degeneracy and index of `f` on the quotient model
(Milnor structure) and of `height c` on the matrix model (slice structure) correspond under
`x ↦ x xᴴ`; both are computed in Milnor's coordinates on `U_k`. -/
theorem transport (c : Fin (n + 1) → ℝ)
    (hcont : letI := csM n; ContMDiff 𝓘(ℝ, Model n) 𝓘(ℝ) ∞ (fC c)) (x : CPn n) :
    letI := csM n
    letI := (Morse.CP.isSliceSubmanifold (n := n)).chartedSpace
    (Morse.IsCriticalPointM (Morse.CP.Model n) (Morse.CP.height c ∘ Subtype.val) (Emap x) ↔
      Morse.IsCriticalPointM (Model n) (fC c) x) ∧
    (Morse.IsCriticalPointM (Model n) (fC c) x →
      (Morse.IsNondegenerate (Morse.hessianM (Morse.CP.Model n) (Morse.CP.height c ∘ Subtype.val)
          (Emap x)) ↔ Morse.IsNondegenerate (Morse.hessianM (Model n) (fC c) x)) ∧
      Morse.indexM (Morse.CP.Model n) (Morse.CP.height c ∘ Subtype.val) (Emap x) =
        Morse.indexM (Model n) (fC c) x) := by
  letI := csM n
  haveI := isManifold_csM (n := n)
  letI := (Morse.CP.isSliceSubmanifold (n := n)).chartedSpace
  haveI := (Morse.CP.isSliceSubmanifold (n := n)).isManifold
  obtain ⟨k, hk⟩ := exists_U x
  obtain ⟨Φ, hsrc, htgt, hΦ⟩ := isMilnorChart_csM (n := n) k
  set ψ := Φ.toOpenPartialHomeomorph.trans (eqvH n) with hψ
  have hy := isSmoothCoord_psi Φ
  have hχ := isSmoothCoord_chiG (n := n) k
  have hxs : x ∈ ψ.source := by rw [psi_source hsrc htgt hΦ]; exact hk
  have hxG : Emap x ∈ (chiG k).source := (mem_U_iff k x).1 hk
  have hval : chiG k (Emap x) = ψ x := (psi_apply hsrc htgt hΦ hk).symm
  have hev : (Morse.CP.height c ∘ Subtype.val) ∘ (chiG k).symm =ᶠ[𝓝 (chiG k (Emap x))]
      fC c ∘ ψ.symm := by
    rw [hval]
    filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hxs)] with w hw
    rw [psi_target hsrc htgt hΦ] at hw
    change Morse.CP.height c (Pk k w).1 = fC c (ψ.symm w)
    rw [Pk_val k hw, fC_eq, Emap_psi_symm hsrc htgt hΦ hw]
  have hFG : ContMDiff 𝓘(ℝ, Morse.CP.Model n) 𝓘(ℝ) ∞
      (Morse.CP.height c ∘ Subtype.val : Gr n → ℝ) :=
    Morse.contMDiff_comp_val Morse.CP.isSliceSubmanifold (Morse.CP.contDiff_height c)
  have hcrit : Morse.IsCriticalPointM (Morse.CP.Model n) (Morse.CP.height c ∘ Subtype.val) (Emap x) ↔
      Morse.IsCriticalPointM (Model n) (fC c) x := by
    rw [hχ.isCriticalPointM_iff hxG ((hFG _).mdifferentiableAt (by simp)),
      hy.isCriticalPointM_iff hxs ((hcont x).mdifferentiableAt (by simp)), ← hval]
    exact ⟨fun h => HasFDerivAt.congr_of_eventuallyEq h hev.symm,
      fun h => HasFDerivAt.congr_of_eventuallyEq h hev⟩
  refine ⟨hcrit, fun hc' => ?_⟩
  have hcG := hcrit.2 hc'
  have h2G : ContMDiffAt 𝓘(ℝ, Morse.CP.Model n) 𝓘(ℝ) 2 (Morse.CP.height c ∘ Subtype.val) (Emap x) :=
    (hFG _).of_le (WithTop.coe_le_coe.2 le_top)
  have h2C : ContMDiffAt 𝓘(ℝ, Model n) 𝓘(ℝ) 2 (fC c) x :=
    (hcont x).of_le (WithTop.coe_le_coe.2 le_top)
  have hH : Morse.hessian ((Morse.CP.height c ∘ Subtype.val) ∘ (chiG k).symm) (chiG k (Emap x)) =
      Morse.hessian (fC c ∘ ψ.symm) (ψ x) := by rw [Morse.hessian_congr hev, hval]
  refine ⟨?_, ?_⟩
  · rw [← hχ.isNondegenerate_iff hxG h2G hcG, ← hy.isNondegenerate_iff hxs h2C hc', hH]
  · rw [← hχ.index_eq hxG h2G hcG, ← hy.index_eq hxs h2C hc', hH]

theorem Emap_pt (k : Fin (n + 1)) : (Emap (pt k : CPn n)).1 = Morse.CP.param k 0 := by
  change toMat (Pi.single k 1) = Morse.CP.param k 0
  rw [show Morse.CP.param k (0 : Morse.CP.Model n) = toMat (Morse.CP.vec k 0) from rfl,
    Morse.CP.vec_zero]

/-- A's `height_param`, re-proved outright (an algebraic identity on the closed ball, including
the sphere `nsq z = 1`, which lies outside Milnor's `U_k`; B is not needed). -/
theorem height_param' {n : ℕ} (c : Fin (n + 1) → ℝ) (k : Fin (n + 1)) {z : Morse.CP.Model n}
    (hz : Morse.CP.nsq z ≤ 1) :
    Morse.CP.height c (Morse.CP.param k z) = Morse.CP.model c k z := by
  have hd : ∀ a, (Morse.CP.param k z a a).re = Complex.normSq (Morse.CP.vec k z a) := fun a => by
    simp only [Morse.CP.param, of_apply, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]
  have hr : ∑ p : Fin n × Fin 2, Morse.CP.weight c k p * z p * z p =
      ∑ i, (c (k.succAbove i) - c k) * Complex.normSq (Morse.CP.cz z i) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.sum_univ_two, Morse.CP.weight, Morse.CP.cz, Complex.normSq_mk]
    ring
  simp only [Morse.CP.height, hd, Morse.CP.model, Morse.CP.wform_apply, hr]
  rw [Fin.sum_univ_succAbove _ k]
  simp only [Morse.CP.vec, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    Complex.normSq_ofReal, Real.mul_self_sqrt (sub_nonneg.2 hz)]
  rw [Morse.CP.nsq_eq, mul_sub, mul_one, Finset.mul_sum]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

end Transport

/-- B ⇒ A. B is applied to the Milnor structure on the quotient model (built by the glue from the
project's V3_41 lemmas, so B's hypotheses are satisfiable), and its conclusions are transported to
the matrix model with its slice structure (`transport`): this gives A's critical points, indices,
Morse property and Morse numbers; `bijective_rank` follows from B's count. Only `height_param`
(pure algebra) is re-proved outright. -/
theorem B_to_A : B → A := by
  intro hB
  have hB' := fun (n : ℕ) (c : Fin (n + 1) → ℝ) (hc : Injective c) =>
    hB n c hc (csM n) isManifold_csM isMilnorChart_csM
  refine ⟨height_param', ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hc q
    obtain ⟨h0, -, -, h3, -, -⟩ := hB' n c hc
    obtain ⟨x, rfl⟩ := Emap_surjective Morse.CP.exists_vec_of_mem q
    rw [(transport c h0 x).1, h3 x]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, Emap_pt k⟩
    · rintro ⟨k, hk⟩; exact ⟨k, Emap_injective (Subtype.ext (hk.trans (Emap_pt k).symm))⟩
  · intro n c hc k
    obtain ⟨h0, -, -, -, h4, -⟩ := hB' n c hc
    have hq : (⟨Morse.CP.param k 0, Morse.CP.param_zero_mem k⟩ : Gr n) = Emap (pt k) :=
      Subtype.ext (Emap_pt k).symm
    rw [hq]
    have T := (transport c h0 (pt k)).2 (h4 k).1.1
    exact ⟨T.1.2 (h4 k).1.2, T.2.trans (h4 k).2⟩
  · intro n c hc q hq
    obtain ⟨h0, -, -, h3, h4, -⟩ := hB' n c hc
    obtain ⟨x, rfl⟩ := Emap_surjective Morse.CP.exists_vec_of_mem q
    have hx := (transport c h0 x).1.1 hq
    obtain ⟨k, rfl⟩ := (h3 x).1 hx
    exact ((transport c h0 (pt k)).2 hx).1.2 (h4 k).1.2
  · intro n c hc
    letI := csM n
    obtain ⟨h0, -, -, h3, h4, h5⟩ := hB' n c hc
    refine Finite.injective_iff_bijective.1 fun j k hjk => ?_
    have h : Morse.CP.rank c j = Morse.CP.rank c k := congrArg Fin.val hjk
    have hl : Even (2 * Morse.CP.rank c j) ∧ 2 * Morse.CP.rank c j ≤ 2 * n := by
      have := Morse.CP.rank_lt (c := c) j
      exact ⟨even_two_mul _, by omega⟩
    have h1 := h5 (2 * Morse.CP.rank c j)
    rw [if_pos hl, Set.ncard_eq_one] at h1
    obtain ⟨a, ha⟩ := h1
    have hj : pt j ∈ {x : CPn n | Morse.IsCriticalPointM (Model n) (fC c) x ∧
        Morse.indexM (Model n) (fC c) x = 2 * Morse.CP.rank c j} :=
      ⟨(h3 _).2 ⟨j, rfl⟩, (h4 j).2⟩
    have hk : pt k ∈ {x : CPn n | Morse.IsCriticalPointM (Model n) (fC c) x ∧
        Morse.indexM (Model n) (fC c) x = 2 * Morse.CP.rank c j} :=
      ⟨(h3 _).2 ⟨k, rfl⟩, (h4 k).2.trans (by change 2 * Morse.CP.rank c k = _; rw [h])⟩
    rw [ha] at hj hk
    exact pt_injective (hj.trans hk.symm)
  · intro n c hc l
    letI := csM n
    letI := (Morse.CP.isSliceSubmanifold (n := n)).chartedSpace
    obtain ⟨h0, -, -, -, -, h5⟩ := hB' n c hc
    rw [Morse.critCount]
    have hset : {q : Gr n | Morse.IsCriticalPointM (Morse.CP.Model n)
        (Morse.CP.height c ∘ Subtype.val) q ∧
        Morse.indexM (Morse.CP.Model n) (Morse.CP.height c ∘ Subtype.val) q = l} =
        Emap '' {x : CPn n | Morse.IsCriticalPointM (Model n) (fC c) x ∧
          Morse.indexM (Model n) (fC c) x = l} := by
      ext q
      constructor
      · rintro ⟨hq, hi⟩
        obtain ⟨x, rfl⟩ := Emap_surjective Morse.CP.exists_vec_of_mem q
        have hx := (transport c h0 x).1.1 hq
        exact ⟨x, ⟨hx, ((transport c h0 x).2 hx).2.symm.trans hi⟩, rfl⟩
      · rintro ⟨x, ⟨hx, hi⟩, rfl⟩
        exact ⟨(transport c h0 x).1.2 hx, ((transport c h0 x).2 hx).2.trans hi⟩
    rw [hset, Set.ncard_image_of_injective _ Emap_injective]
    exact h5 l

#rt_check RoundTrip.V3_42.B_to_A [Morse.CP.height_param, Morse.CP.isCriticalPointM_height_iff, Morse.CP.isNondegenerate_indexM_height, Morse.CP.isNondegenerate_of_isCriticalPointM, Morse.CP.bijective_rank, Morse.CP.critCount_height]
#rt_overlap RoundTrip.V3_42.B_to_A [Morse.CP.height_param, Morse.CP.isCriticalPointM_height_iff, Morse.CP.isNondegenerate_indexM_height, Morse.CP.isNondegenerate_of_isCriticalPointM, Morse.CP.bijective_rank, Morse.CP.critCount_height]

end RoundTrip.V3_42
