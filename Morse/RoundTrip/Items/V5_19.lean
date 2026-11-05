import Morse
import RoundTrip.Check
import RoundTrip.Blind.V5_19

/-! Round trip V5_19 (Milnor §7, Theorem 7.4).  No direction is proved.  A ⇒ B fails
exactly on Hypothesis (N), which B (as Milnor's statement) does not assume and Milnor derives from
the triangulability of algebraic varieties: `A_to_B_of_N` proves B from A's abstract clause plus
(N), with the glue below (B's `ℂPⁿ` compact and Hausdorff, the affine chart `V − P ≅ affPart`).
B ⇒ A fails genuinely (B is only about algebraic `V` and cells). -/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold unitInterval

noncomputable section

namespace RoundTrip.V5_19

/-- The project's statement (universes instantiated at 0): Theorem 7.4 for the abstract pair
(compact `X`, closed `A`, `X − A ≅ M` a closed complex submanifold with `‖e⁻¹ y‖ → ∞` at `A`,
Hypothesis (N)), as `PushesInto P A univ` for every compact `P` embedded in a space of dimension
`< k`; and for closed `V ⊆ ℂPⁿ` (trace-one Hermitian projections) with `P = {Z₀ = 0}`, `V − P` a
complex submanifold of complex dimension `k`, under Hypothesis (N): cubes `Iʳ`, embedded `P`,
and the bijectivity/surjectivity of `π_i(V ∩ P, x) → π_i(V, x)`. -/
def A : Prop :=
  type_of% @Morse.theorem_7_4_of_section.{0, 0, 0} ∧ type_of% @Morse.theorem_7_4 ∧
    type_of% @Morse.theorem_7_4_of_embedding.{0, 0} ∧ type_of% @Morse.theorem_7_4_bijective ∧
    type_of% @Morse.theorem_7_4_surjective

theorem A_holds : A :=
  ⟨@Morse.theorem_7_4_of_section, @Morse.theorem_7_4, @Morse.theorem_7_4_of_embedding,
    @Morse.theorem_7_4_bijective, @Morse.theorem_7_4_surjective⟩

/-! ### Glue: B's `ℂPⁿ` (unit sphere modulo `S¹`) -/

section Glue

variable {n : ℕ}

theorem rel_equiv (n : ℕ) : Equivalence (Rel n) where
  refl z := ⟨1, by simp, by simp⟩
  symm := by
    rintro z w ⟨c, hc, h⟩
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    exact ⟨c⁻¹, by simp [hc], by rw [h, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
  trans := by
    rintro z w u ⟨c, hc, h⟩ ⟨c', hc', h'⟩
    exact ⟨c' * c, by simp [hc, hc'], by rw [h', h, smul_smul]⟩

theorem cls_eq_iff {z w : Sph n} : cls z = cls w ↔ Rel n z w :=
  ⟨fun h => (rel_equiv n).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem continuous_cls : Continuous (cls : Sph n → CPn n) := continuous_quot_mk

theorem norm_le_one (z : Sph n) (j : Fin (n + 1)) : ‖z.1 j‖ ≤ 1 := by
  have h : ‖z.1 j‖ ^ 2 ≤ ∑ i, ‖z.1 i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖z.1 i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  rw [z.2] at h
  nlinarith [norm_nonneg (z.1 j)]

theorem isCompact_sph : IsCompact {z : Fin (n + 1) → ℂ | ∑ j, ‖z j‖ ^ 2 = 1} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_eq (continuous_finsetSum _ fun j _ =>
      (continuous_norm.comp (continuous_apply j)).pow 2) continuous_const
  · refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun z hz => ?_
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    exact fun j => norm_le_one ⟨z, hz⟩ j

instance : CompactSpace (Sph n) := isCompact_iff_compactSpace.1 isCompact_sph

/-- `z ↦ (z_i z̄_j)`, constant on classes and injective on `ℂPⁿ`. -/
def gram (z : Sph n) : Fin (n + 1) → Fin (n + 1) → ℂ := fun i j => z.1 i * star (z.1 j)

theorem gram_rel {z w : Sph n} (h : Rel n z w) : gram z = gram w := by
  obtain ⟨c, hc, hw⟩ := h
  have hcc : star c * c = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  funext i j
  simp only [gram, hw, Pi.smul_apply, smul_eq_mul, star_mul']
  calc z.1 i * star (z.1 j) = (star c * c) * (z.1 i * star (z.1 j)) := by rw [hcc, one_mul]
    _ = c * z.1 i * (star c * star (z.1 j)) := by ring

theorem rel_of_gram {z w : Sph n} (h : gram z = gram w) : Rel n z w := by
  obtain ⟨j, hj⟩ : ∃ j, z.1 j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have := z.2
    simp [hcon] at this
  have hjj := congrFun (congrFun h j) j
  simp only [gram] at hjj
  have hn : ‖z.1 j‖ = ‖w.1 j‖ := by
    have h1 : z.1 j * star (z.1 j) = ((‖z.1 j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2 : w.1 j * star (w.1 j) = ((‖w.1 j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1, h2] at hjj
    have := Complex.ofReal_injective hjj
    nlinarith [norm_nonneg (z.1 j), norm_nonneg (w.1 j)]
  have hwj : w.1 j ≠ 0 := by
    intro h0; rw [h0, norm_zero, norm_eq_zero] at hn; exact hj hn
  have hsw : star (w.1 j) ≠ 0 := star_ne_zero.2 hwj
  refine ⟨star (z.1 j) / star (w.1 j), ?_, ?_⟩
  · rw [norm_div, norm_star, norm_star, hn, div_self (norm_ne_zero_iff.2 hwj)]
  · funext i
    have hij := congrFun (congrFun h i) j
    simp only [gram] at hij
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    rw [← hij]
    ring

/-- The Gram map on `ℂPⁿ`. -/
def gramQ : CPn n → (Fin (n + 1) → Fin (n + 1) → ℂ) := Quot.lift gram fun _ _ h => gram_rel h

instance : T2Space (CPn n) := by
  refine T2Space.of_injective_continuous (f := gramQ) ?_ ?_
  · intro x y hxy
    obtain ⟨z, rfl⟩ := Quot.exists_rep x
    obtain ⟨w, rfl⟩ := Quot.exists_rep y
    exact Quot.sound (rel_of_gram hxy)
  · exact continuous_quot_lift _ (continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply i).comp continuous_subtype_val).mul
        (((continuous_apply j).comp continuous_subtype_val).star))

/-- `|Σ a_j z_j|`, constant on classes. -/
def nrm (a : Fin (n + 1) → ℂ) : CPn n → ℝ :=
  Quot.lift (fun z : Sph n => ‖∑ j, a j * z.1 j‖) fun z w h => by
    obtain ⟨c, hc, hw⟩ := h
    simp only [hw, Pi.smul_apply, smul_eq_mul]
    have : ∑ j, a j * (c * z.1 j) = c * ∑ j, a j * z.1 j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, norm_mul, hc, one_mul]

theorem continuous_nrm (a : Fin (n + 1) → ℂ) : Continuous (nrm a) :=
  continuous_quot_lift _ (continuous_norm.comp (continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)))

theorem hyperplane_eq (a : Fin (n + 1) → ℂ) : hyperplane a = {x | nrm a x = 0} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ‖∑ j, a j * z.1 j‖ = 0
    rw [show ∑ j, a j * z.1 j = 0 from hz, norm_zero]
  · intro hx
    obtain ⟨z, rfl⟩ := Quot.exists_rep x
    exact ⟨z, norm_eq_zero.1 hx, rfl⟩

/-- `[z] ↦ z / Σ a_j z_j` (the affine chart of `ℂPⁿ − P`), constant on classes. -/
def affQ (a : Fin (n + 1) → ℂ) : CPn n → Cn (n + 1) :=
  Quot.lift (fun z : Sph n => (∑ j, a j * z.1 j)⁻¹ • WithLp.toLp 2 z.1) fun z w h => by
    obtain ⟨c, hc, hw⟩ := h
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    simp only [hw]
    have : ∑ j, a j * (c • z.1) j = c * ∑ j, a j * z.1 j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [this, WithLp.toLp_smul, smul_smul, mul_inv, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc0,
      mul_one]

/-- Homogeneous polynomials scale: `F(c v) = c^d F(v)`. -/
theorem eval_smul_of_isHomogeneous {m d : ℕ} {F : MvPolynomial (Fin m) ℂ} (hF : F.IsHomogeneous d)
    (c : ℂ) (v : Fin m → ℂ) : MvPolynomial.eval (c • v) F = c ^ d * MvPolynomial.eval v F := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have : d = ∑ i, s i := by
    rw [hF.degree_eq_sum_deg_support hs, ← Finsupp.degree_eq_sum]
    rfl
  rw [← this]
  ring

/-- The zero set of homogeneous polynomials is a cone. -/
theorem eval_smul_eq_zero {m : ℕ} {S : Set (MvPolynomial (Fin m) ℂ)}
    (hS : ∀ F ∈ S, ∃ d, F.IsHomogeneous d) (c : ℂ) {v : Fin m → ℂ}
    (hv : ∀ F ∈ S, MvPolynomial.eval v F = 0) : ∀ F ∈ S, MvPolynomial.eval (c • v) F = 0 := by
  intro F hF
  obtain ⟨d, hd⟩ := hS F hF
  rw [eval_smul_of_isHomogeneous hd, hv F hF, mul_zero]

variable (S : Set (MvPolynomial (Fin (n + 1)) ℂ)) (a : Fin (n + 1) → ℂ)

/-- `V ∩ P` as a subset of `V`. -/
abbrev Sec : Set (projZero S) := Subtype.val ⁻¹' hyperplane a

theorem ne_zero_of_mem_affPart {w : Cn (n + 1)} (hw : w ∈ affPart S a) : w ≠ 0 := by
  rintro rfl
  have := hw.1
  simp at this

/-- `w ↦ [w / ‖w‖]`. -/
def nz (w : Cn (n + 1)) (hw : w ≠ 0) : Sph n :=
  ⟨fun j => ((‖w‖⁻¹ : ℝ) : ℂ) * w j, by
    have h := EuclideanSpace.norm_sq_eq w
    have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, mul_pow,
      ← Finset.mul_sum]
    rw [← h, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hn)]⟩

theorem compactSpace_projZero : CompactSpace (projZero S) := by
  refine isCompact_iff_compactSpace.1 ((IsClosed.isCompact ?_).image continuous_cls)
  have : {z : Sph n | ∀ F ∈ S, MvPolynomial.eval z.1 F = 0} =
      ⋂ F ∈ S, {z : Sph n | MvPolynomial.eval z.1 F = 0} := by ext; simp
  rw [this]
  exact isClosed_biInter fun F _ => isClosed_eq
    ((MvPolynomial.continuous_eval F).comp continuous_subtype_val) continuous_const

theorem isClosed_sec : IsClosed (Sec S a) := by
  rw [Sec, hyperplane_eq]
  exact (isClosed_eq (continuous_nrm a) continuous_const).preimage continuous_subtype_val

theorem isClosed_affPart : IsClosed (affPart S a) := by
  have : affPart S a = {w : Cn (n + 1) | ∑ j, a j * w j = 1} ∩
      ⋂ F ∈ S, {w : Cn (n + 1) | MvPolynomial.eval (fun j => w j) F = 0} := by
    ext w; simp [affPart]
  rw [this]
  have hc : Continuous fun w : Cn (n + 1) => fun j => w j :=
    continuous_pi fun j => PiLp.continuous_apply 2 _ j
  refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_biInter fun F _ =>
    isClosed_eq ((MvPolynomial.continuous_eval F).comp hc) continuous_const)
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (PiLp.continuous_apply 2 _ j)

theorem nrm_cls_nz {w : Cn (n + 1)} (hw : w ∈ affPart S a) :
    nrm a (cls (nz w (ne_zero_of_mem_affPart S a hw))) ≠ 0 := by
  change ‖∑ j, a j * (((‖w‖⁻¹ : ℝ) : ℂ) * w j)‖ ≠ 0
  have : ∑ j, a j * (((‖w‖⁻¹ : ℝ) : ℂ) * w j) = ((‖w‖⁻¹ : ℝ) : ℂ) * ∑ j, a j * w j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, hw.1, mul_one, Complex.norm_real, norm_ne_zero_iff]
  exact inv_ne_zero (norm_ne_zero_iff.2 (ne_zero_of_mem_affPart S a hw))

/-- **`V − P ≅ affPart S a`**, the affine chart. -/
def affHomeo (hS : ∀ F ∈ S, ∃ d, F.IsHomogeneous d) : affPart S a ≃ₜ ((Sec S a)ᶜ : Set (projZero S)) where
  toFun w := ⟨⟨cls (nz w.1 (ne_zero_of_mem_affPart S a w.2)), nz w.1 _, by
      intro F hF
      exact eval_smul_eq_zero hS (((‖w.1‖⁻¹ : ℝ) : ℂ)) (v := fun j => w.1 j) w.2.2 F hF, rfl⟩,
    fun h => nrm_cls_nz S a w.2 (by rw [Sec, mem_preimage, hyperplane_eq] at h; exact h)⟩
  invFun y := ⟨affQ a y.1.1, by
    obtain ⟨z, hz, hzy⟩ := y.1.2
    have hs : ∑ j, a j * z.1 j ≠ 0 := fun h0 => y.2 (by
      change y.1.1 ∈ hyperplane a
      rw [← hzy]; exact ⟨z, h0, rfl⟩)
    rw [← hzy]
    change (∑ j, a j * z.1 j)⁻¹ • WithLp.toLp 2 z.1 ∈ affPart S a
    refine ⟨?_, ?_⟩
    · simp only [PiLp.smul_apply, smul_eq_mul]
      have : ∑ j, a j * ((∑ j, a j * z.1 j)⁻¹ * z.1 j) = (∑ j, a j * z.1 j)⁻¹ * ∑ j, a j * z.1 j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, inv_mul_cancel₀ hs]
    · exact eval_smul_eq_zero hS (∑ j, a j * z.1 j)⁻¹ hz⟩
  left_inv w := by
    obtain ⟨w, hw⟩ := w
    have hw0 := ne_zero_of_mem_affPart S a hw
    have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
    refine Subtype.ext ?_
    change (∑ j, a j * (((‖w‖⁻¹ : ℝ) : ℂ) * w j))⁻¹ • WithLp.toLp 2 (fun j => ((‖w‖⁻¹ : ℝ) : ℂ) * w j) = w
    have : ∑ j, a j * (((‖w‖⁻¹ : ℝ) : ℂ) * w j) = ((‖w‖⁻¹ : ℝ) : ℂ) * ∑ j, a j * w j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hw.1, mul_one]
    ext j
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast inv_ne_zero hn), one_mul]
  right_inv y := by
    obtain ⟨⟨x, hx⟩, hxs⟩ := y
    obtain ⟨z, rfl⟩ := Quot.exists_rep x
    have hs : ∑ j, a j * z.1 j ≠ 0 := fun h0 => hxs (by
      change Quot.mk _ z ∈ hyperplane a
      exact ⟨z, h0, rfl⟩)
    refine Subtype.ext (Subtype.ext ?_)
    change cls (nz _ _) = cls z
    rw [cls_eq_iff]
    refine (rel_equiv n).symm ⟨((‖∑ j, a j * z.1 j‖ : ℝ) : ℂ) * (∑ j, a j * z.1 j)⁻¹, ?_, ?_⟩
    · rw [norm_mul, Complex.norm_real, norm_norm, norm_inv, mul_inv_cancel₀ (norm_ne_zero_iff.2 hs)]
    · have hz1 : ‖(WithLp.toLp 2 z.1 : Cn (n + 1))‖ = 1 := by
        have h := EuclideanSpace.norm_sq_eq (WithLp.toLp 2 z.1 : Cn (n + 1))
        simp only at h
        rw [z.2] at h
        nlinarith [norm_nonneg (WithLp.toLp 2 z.1 : Cn (n + 1))]
      funext j
      change ((‖affQ a (Quot.mk _ z)‖⁻¹ : ℝ) : ℂ) * (affQ a (Quot.mk _ z)) j = _
      change ((‖(∑ j, a j * z.1 j)⁻¹ • (WithLp.toLp 2 z.1 : Cn (n + 1))‖⁻¹ : ℝ) : ℂ) *
        ((∑ j, a j * z.1 j)⁻¹ • (WithLp.toLp 2 z.1 : Cn (n + 1))) j = _
      rw [norm_smul, hz1, mul_one, norm_inv, inv_inv]
      simp only [PiLp.smul_apply, smul_eq_mul, Pi.smul_apply]
      ring
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.subtype_mk (continuous_cls.comp ?_) _) _
    refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
    refine (Complex.continuous_ofReal.comp ((continuous_norm.comp continuous_subtype_val).inv₀
      fun w => norm_ne_zero_iff.2 (ne_zero_of_mem_affPart S a w.2))).mul ?_
    exact (PiLp.continuous_apply 2 _ j).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    have hW : IsOpen {x : CPn n | nrm a x ≠ 0} :=
      isOpen_ne_fun (continuous_nrm a) continuous_const
    have hon : ContinuousOn (affQ a) {x : CPn n | nrm a x ≠ 0} := by
      refine ((isQuotientMap_quot_mk : IsQuotientMap (Quot.mk (Rel n))).continuousOn_isOpen_iff
        (g := affQ a) hW).2 ?_
      have hcs : Continuous fun z : Sph n => ∑ j, a j * z.1 j :=
        continuous_finsetSum _ fun j _ => continuous_const.mul
          ((continuous_apply j).comp continuous_subtype_val)
      refine ContinuousOn.smul (hcs.continuousOn.inv₀ fun z hz => ?_)
        ((PiLp.continuous_toLp 2 _).comp continuous_subtype_val).continuousOn
      intro h0
      apply hz
      change ‖∑ j, a j * z.1 j‖ = 0
      rw [h0, norm_zero]
    refine hon.comp_continuous (continuous_subtype_val.comp continuous_subtype_val) fun y => ?_
    have : y.1.1 ∉ hyperplane a := y.2
    rw [hyperplane_eq] at this
    exact this

end Glue

/-- In a Hausdorff `X`, a homeomorphism `e : M ≃ₜ X − A` with `M` closed in a Euclidean space is
proper, so `‖e⁻¹ y‖ → ∞` as `y → A`. -/
theorem hinf_of_t2 {X : Type} [TopologicalSpace X] [T2Space X] {A : Set X} {N : ℕ}
    {M : Set (Rn N)} (hcl : IsClosed M) (e : M ≃ₜ (Aᶜ : Set X)) :
    ∀ x ∈ A, ∀ R : ℝ, ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ Aᶜ, R ≤ ‖((e.symm ⟨y, hy⟩ : M) : Rn N)‖ := by
  intro x hx R
  have hK : IsCompact ((Subtype.val : M → Rn N) ⁻¹' closedBall 0 R) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_closedBall 0 R)
  have hC : IsCompact ((Subtype.val : (Aᶜ : Set X) → X) '' (e '' ((Subtype.val : M → Rn N) ⁻¹'
      closedBall 0 R))) :=
    (hK.image e.continuous).image continuous_subtype_val
  have hxC : x ∉ (Subtype.val : (Aᶜ : Set X) → X) '' (e '' ((Subtype.val : M → Rn N) ⁻¹'
      closedBall 0 R)) := by
    rintro ⟨y, -, rfl⟩
    exact y.2 hx
  filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hxC] with y hyC hy
  by_contra hlt
  replace hlt := not_le.1 hlt
  refine hyC ⟨e (e.symm ⟨y, hy⟩), ⟨e.symm ⟨y, hy⟩, ?_, rfl⟩, by simp⟩
  simp only [mem_preimage, mem_closedBall, dist_zero_right]
  exact hlt.le

local notation "𝔼" n:max => EuclideanSpace ℝ (Fin n)

/-- A's abstract Theorem 7.4 (its first clause), for cells `Dʳ`, model dimension `D = 2k` as a
variable, `hinf` from `T2Space`. -/
theorem relPiZero_of_A (hA : A) {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {Aset : Set X} (hAc : IsClosed Aset) {N D w k : ℕ} (M : Set (𝔼 N))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, 𝔼 N) (𝔼 D) (𝔼 w) M)
    {J : 𝔼 N →L[ℝ] 𝔼 N} (hJ : Morse.IsOrthComplexStructure J) (hc : Morse.IsComplexSubmanifold hM J)
    (hcl : IsClosed M) (hD : D = 2 * k) (e : M ≃ₜ (Asetᶜ : Set X)) (hN : Morse.HypothesisN Aset)
    {r : ℕ} (hrk : r < k) : RelPiZero X Aset r := by
  subst hD
  have hpush := hA.1 hM hAc hcl hJ hc e (hinf_of_t2 hcl e) hN (P := Cell r) (E := 𝔼 r)
    (by rw [finrank_euclideanSpace_fin]; exact hrk) (ι := Subtype.val) continuous_subtype_val
    Subtype.val_injective
  intro f hf
  obtain ⟨g, hg, ⟨F⟩⟩ := hpush f fun _ => trivial
  refine ⟨g, hg, ⟨Morse.Homotopy.homotopyRelMono F ?_⟩⟩
  rintro _ ⟨x, rfl⟩
  exact hf x

/-- **A ⇒ B under Hypothesis (N).**  For B's projective algebraic sets (unit sphere modulo `S¹`,
any hyperplane `Σ a_j z_j = 0`), A's abstract Theorem 7.4 applies with `X = V` (compact, Hausdorff),
`A = V ∩ P` (closed), `M = θ(affPart)` (closed, a complex submanifold by B's hypothesis) and the
affine chart `V − P ≅ affPart` (`affHomeo`), as soon as Hypothesis (N) holds for `(V, V ∩ P)`.
B does not assume (N): Milnor derives it from the triangulability of algebraic varieties. -/
theorem A_to_B_of_N (hA : A) (n k : ℕ) (S : Set (MvPolynomial (Fin (n + 1)) ℂ))
    (a : Fin (n + 1) → ℂ) (hS : ∀ F ∈ S, ∃ d, F.IsHomogeneous d) (hk : IsCplxSubmfd (affPart S a) k)
    (hN : Morse.HypothesisN (Subtype.val ⁻¹' hyperplane a : Set (projZero S))) (r : ℕ)
    (hrk : r < k) : RelPiZero (projZero S) (Subtype.val ⁻¹' hyperplane a) r := by
  obtain ⟨K, d, m, θ, J, hM, hJ, -, hc, hd⟩ := hk
  have := compactSpace_projZero S
  have hcl : IsClosed (θ '' affPart S a) :=
    θ.toHomeomorph.isClosedMap _ (isClosed_affPart S a)
  let e : (θ '' affPart S a) ≃ₜ ((Sec S a)ᶜ : Set (projZero S)) :=
    (θ.toHomeomorph.image (affPart S a)).symm.trans (affHomeo S a hS)
  exact relPiZero_of_A hA (isClosed_sec S a) (θ '' affPart S a) hM
    (J := (J.toContinuousLinearEquiv : Rn (K + 1) →L[ℝ] Rn (K + 1)))
    ⟨fun v => hJ v, fun v w => J.inner_map_map v w⟩ (fun q v hv => hc q v hv) hcl hd e hN hrk

#rt_check RoundTrip.V5_19.A_to_B_of_N [Morse.theorem_7_4_of_section, Morse.theorem_7_4, Morse.theorem_7_4_of_embedding, Morse.theorem_7_4_bijective, Morse.theorem_7_4_surjective]

end RoundTrip.V5_19

end
