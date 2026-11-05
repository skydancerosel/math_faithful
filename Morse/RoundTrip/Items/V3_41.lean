import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_41

open Matrix Set Filter Topology Function Module
open scoped ContDiff Manifold Morse.MatrixInner

noncomputable section

namespace RoundTrip.V3_41

/-- The project's statement (no universe parameters): the matrix model of `ℂPⁿ`
(`grassmannian (Fin (n+1)) 1`, the projections `z zᴴ`) with Milnor's coordinates `coord k` and
their inverse `param k`: every point is `f fᴴ` for a unit vector `f`; `coord k ∘ param k = id` on
the open unit ball; on `U_k = {Re P_kk > 0}`, `coord k` lands in the ball and `param k ∘ coord k = id`;
the `U_k` cover; `ℂPⁿ` is a `2n`-dimensional slice submanifold of `Mₙ₊₁(ℂ)`, with a slice chart at
each point of `U_k` parametrized by `z ↦ param k (coord k x + z)`; `ℂPⁿ` is compact. -/
def A : Prop :=
  type_of% @Morse.CP.exists_vec_of_mem ∧ type_of% @Morse.CP.coord_param ∧
    type_of% @Morse.CP.nsq_coord_lt_and_param_coord ∧ type_of% @Morse.CP.exists_re_diag_pos ∧
    type_of% @Morse.CP.isSliceSubmanifold ∧ type_of% @Morse.CP.exists_sliceChart ∧
    type_of% @Morse.CP.isCompact

theorem A_holds : A :=
  ⟨@Morse.CP.exists_vec_of_mem, @Morse.CP.coord_param, @Morse.CP.nsq_coord_lt_and_param_coord,
    @Morse.CP.exists_re_diag_pos, @Morse.CP.isSliceSubmanifold, @Morse.CP.exists_sliceChart,
    @Morse.CP.isCompact⟩

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

/-- A ⇒ B: the charts are built from A's inverse pair `coord k`/`param k` (`coord_param`,
`nsq_coord_lt_and_param_coord`) transported along the homeomorphism `z ↦ z zᴴ` of the quotient
model onto the matrix model (surjective by `exists_vec_of_mem`); the `U_k` cover by
`exists_re_diag_pos`. Smoothness of the transition maps uses the project's `contDiffOn_coord`,
`contDiffOn_param` (outside A). A's slice-submanifold structure, slice charts and compactness are
not used. -/
theorem A_to_B : A → B := by
  rintro ⟨hvec, hcp, hpc, hdiag, -, -, -⟩ n
  exact ⟨cs (n := n) hvec hcp hpc hdiag, isManifold (n := n) hvec hcp hpc hdiag,
    isMilnorChart (n := n) hvec hcp hpc hdiag⟩

#rt_check RoundTrip.V3_41.A_to_B [Morse.CP.exists_vec_of_mem, Morse.CP.coord_param, Morse.CP.nsq_coord_lt_and_param_coord, Morse.CP.exists_re_diag_pos, Morse.CP.isSliceSubmanifold, Morse.CP.exists_sliceChart, Morse.CP.isCompact]

/-! B ⇒ A is not proved: B (a smooth structure on the quotient model in which Milnor's coordinates
are diffeomorphisms onto the ball) says nothing about the matrix model of A (points = projections
`f fᴴ`, the slice-submanifold structure of `grassmannian (Fin (n+1)) 1 ⊆ Mₙ₊₁(ℂ)`, its slice charts,
compactness). A is a theorem, so the implication holds, but only by re-proving A outright. -/

end RoundTrip.V3_41
