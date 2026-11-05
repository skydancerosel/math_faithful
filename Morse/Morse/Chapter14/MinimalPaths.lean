import Morse.Chapter13.SUInstance

/-!
Milnor, *Morse Theory*, §23, Lemma 23.1 (pp. 126–128); Exposition/Chapter14.md, §2.

# The minimal geodesics from `I` to `−I` in `SU(2m)` as a subspace of the path space

## Milnor's text, paraphrased

(p. 127) The minimal geodesics from `I` to `−I` in `SU(2m)` are the `t ↦ exp(tA)` with
`A = iπ(2P − I)`, `P` the Hermitian projection onto an `m`-dimensional subspace; **Lemma 23.1**:
the space `Ω^d` of minimal geodesics is homeomorphic to `G_m(ℂ^{2m})`.  (Exposition: "the topology
is handled by Lemma 2.3, with `ρ` the distance of `SU(2m)`.")

## What is formalized

`Morse.lemma_23_1` (`Morse/Chapter12/SUMinimal.lean`) identifies the set `Morse.minVel ι` of
initial velocities (`A ∈ 𝔰𝔲(2m)`, `A² = −π²I`) with the Grassmannian.  Here the initial velocities
are identified with `Ω^d = Morse.minPaths`, the paths of least energy in Milnor's path space with
Milnor's metric `d` (`Morse.PathSp`):

* `Morse.exp_half_smul_of_mem_minVel`: **`exp(A/2) = A/π`** for `A ∈ minVel` (on `Eigen(±iπ)`,
  `e^{±iπ/2} = ±i`), so a minimal geodesic remembers its velocity at its midpoint.
* `Morse.expPath_mem_minPaths`: `t ↦ exp(tA)`, `A ∈ minVel`, has least energy
  `(π√(2m))² = ρ(I, −I)²` (`Morse.pi_sq_le_energy`);
  `Morse.exists_minVel_of_mem_minPaths`: conversely **every path of least energy agrees on
  `[0, 1]` with some `t ↦ exp(tA)`, `A ∈ minVel`**.
* `Morse.continuous_expPath`: **`A ↦ (t ↦ exp tA)` is continuous for Milnor's metric**.
* `Morse.minPathsHomotopyEquiv`: **`minVel ≃ Ω^d` up to homotopy**, `A ↦ (t ↦ exp tA)` with
  homotopy inverse `γ ↦ π γ(1/2)` (`Morse.minVelToPaths`, `Morse.pathsToMinVel`);
  `Morse.minVelHomeomorph`: **`minVel ≅ Ω^d` as a homeomorphism onto the separation quotient**
  (paths agreeing on `[0, 1]` identified).  With `Morse.lemma_23_1` this is Milnor's
  `Ω^d ≅ G_m(ℂ^{2m})`.

## What Milnor leaves implicit

* **Continuity for Milnor's metric.** `d` has a uniform part and an `L²` part on the speeds.  On
  minimal geodesics the speed is constant, `‖A‖ = π√(2m)` (`Morse.norm_of_mem_minVel`,
  `Morse.speed_exp_smul`), so the `L²` part vanishes identically on `Ω^d`, and the uniform part
  (measured with the Riemannian distance `ρ`, not the norm) is controlled by pointwise
  convergence at bounded energy (`Morse.PathSp.eventually_supDist_le_of_tendsto_apply`, the
  argument of Lemma A of Exposition/Chapter13.md for the sphere).  The inverse only needs the
  value at `t = 1/2`, and `ρ` dominates the norm.
* **"Homeomorphic."** Paths here are functions on `ℝ` whose values off `[0, 1]` play no role, so
  Milnor's pseudometric does not separate paths agreeing on `[0, 1]`; the homeomorphism is with
  the separation quotient, and for homotopy groups the homotopy equivalence is what is used.
* **That minimal paths are the `exp(tA)` with `A² = −π²I`** (rather than merely geodesics):
  a path of least energy is a geodesic (Corollary 12.3), hence `exp(tA)` with `exp A = −I`; its
  energy `‖A‖²` is at most that of a known minimal geodesic, `π²·2m`, and `‖A‖ ≥ π√(2m)` for
  every geodesic, so it is minimal and all `k_j = ±1`.
-/

open Matrix Set Filter Topology Module Finset
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff ENNReal

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `exp(A/2) = A/π` for `A ∈ minVel`. -/
theorem exp_half_smul_of_mem_minVel [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A ∈ minVel ι) :
    NormedSpace.exp ((1 / 2 : ℝ) • A) = (Real.pi⁻¹ : ℝ) • A := by
  have hexp := exp_eq_neg_one_of_sq hA.1.1 hA.2
  obtain ⟨T, k, hT, -, -, hAeq⟩ := exists_unitary_suDiag hA.1 hexp
  have hpm : ∀ i, k i = 1 ∨ k i = -1 := (sq_conj_suDiag_iff hT k).1 (hAeq ▸ hA.2)
  have hT' := mul_conjTranspose_eq_one hT
  have hinv : T⁻¹ = Tᴴ := Matrix.inv_eq_left_inv hT
  have hD : NormedSpace.exp ((1 / 2 : ℝ) • suDiag k) = (Real.pi⁻¹ : ℝ) • suDiag k := by
    have e1 : (1 / 2 : ℝ) • suDiag k =
        diagonal fun j => ((Real.pi * k j / 2 : ℝ) : ℂ) * Complex.I := by
      rw [suDiag, ← diagonal_smul]
      congr 1; funext j
      simp only [Pi.smul_apply, Complex.real_smul]
      push_cast; ring
    rw [e1, exp_diagonal_mul_I, suDiag, ← diagonal_smul]
    congr 1; funext j
    simp only [Pi.smul_apply, Complex.real_smul]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    rcases hpm j with h | h <;> rw [h]
    · push_cast
      rw [show (Real.pi : ℂ) * 1 / 2 * Complex.I = (Real.pi / 2 : ℂ) * Complex.I by ring,
        Complex.exp_mul_I, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
      field_simp
      push_cast; ring
    · push_cast
      rw [show (Real.pi : ℂ) * -1 / 2 * Complex.I = (-(Real.pi / 2) : ℂ) * Complex.I by ring,
        Complex.exp_mul_I, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_neg,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      field_simp
      push_cast; ring
  have e2 : (1 / 2 : ℝ) • A = T * ((1 / 2 : ℝ) • suDiag k) * T⁻¹ := by
    rw [hinv, hAeq, Matrix.mul_smul, Matrix.smul_mul]
  rw [e2, Matrix.exp_conj T _ ⟨⟨T, Tᴴ, hT', hT⟩, rfl⟩, hD, hinv, hAeq, Matrix.mul_smul,
    Matrix.smul_mul]

theorem continuous_matrix_exp : Continuous (NormedSpace.exp : Matrix ι ι ℂ → Matrix ι ι ℂ) :=
  continuous_iff_continuousAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt

variable [Nonempty ι] {m : ℕ}

omit [Nonempty ι] in
/-- `‖A‖ = π√(2m)` on `minVel`: every minimal geodesic has length `π√(2m)`. -/
theorem norm_of_mem_minVel (hcard : Fintype.card ι = 2 * m) {A : Matrix ι ι ℂ}
    (hA : A ∈ minVel ι) : ‖A‖ = Real.pi * Real.sqrt (2 * m) := by
  have hexp := exp_eq_neg_one_of_sq hA.1.1 hA.2
  obtain ⟨T, k, hT, hk, -, hAeq⟩ := exists_unitary_suDiag hA.1 hexp
  have hpm := (sq_conj_suDiag_iff hT k).1 (hAeq ▸ hA.2)
  rw [hAeq, norm_eq_pi_sqrt hT]
  have h1 := (sum_sq_eq_card_iff hk).2 hpm
  have h2 : (∑ j, (k j : ℝ) ^ 2) = (Fintype.card ι : ℝ) := by exact_mod_cast h1
  rw [h2, hcard]
  push_cast
  ring_nf

omit [Nonempty ι] in
/-- The speed of `t ↦ exp(tA)` is `‖A‖` everywhere, for skew-Hermitian `A`. -/
theorem speed_exp_smul {A : Matrix ι ι ℂ} (hA : Aᴴ = -A) (t : ℝ) :
    PathSp.speed (fun s : ℝ => NormedSpace.exp (s • A)) t = ‖A‖ := by
  rw [PathSp.speed, (hasDerivAt_exp_smul_const A t).deriv]
  have hu : (NormedSpace.exp (t • A))ᴴ * NormedSpace.exp (t • A) = 1 :=
    exp_conjTranspose_mul_exp_of_skew (by rw [conjTranspose_smul, star_trivial, hA, smul_neg])
  rw [← mulLeftIso_apply _ hu, LinearIsometryEquiv.norm_map]

/-- Every path from `I` to `−I` in `SU(2m)` has energy `≥ (π√(2m))² = ρ(I, −I)²`. -/
theorem pi_sq_le_energy (hcard : Fintype.card ι = 2 * m) {γ : ℝ → Matrix ι ι ℂ}
    (hγ : γ ∈ pathSpace (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    (Real.pi * Real.sqrt (2 * m)) ^ 2 ≤ energy γ 0 1 := by
  have h1 := riemDist_le_pathLength (N := (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)))
    hγ.1 hγ.2.1
  rw [hγ.2.2.1, hγ.2.2.2, riemDist_one_neg_one hcard] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff hγ.1.isAdmissible.pathLength_nonneg).1 h1
  have h3 := pathLength_sq_le_energy hγ.1
  rw [sub_zero, one_mul] at h3
  calc _ ≤ pathLength γ 0 1 ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    _ ≤ _ := h3

/-- The geodesic `t ↦ exp(tA)` of `A ∈ minVel`, as a point of `Ω(SU(2m); I, −I)`. -/
def expPath (A : minVel ι) : PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1) :=
  ⟨fun s : ℝ => NormedSpace.exp (s • (A : Matrix ι ι ℂ)),
    mem_pathSpace_exp A.2.1 (exp_eq_neg_one_of_sq A.2.1.1 A.2.2)⟩

theorem expPath_apply (A : minVel ι) (s : ℝ) :
    (expPath A : ℝ → Matrix ι ι ℂ) s = NormedSpace.exp (s • (A : Matrix ι ι ℂ)) := rfl

theorem energy_expPath (hcard : Fintype.card ι = 2 * m) (A : minVel ι) :
    energy (expPath A) 0 1 = (Real.pi * Real.sqrt (2 * m)) ^ 2 := by
  change energy (fun s : ℝ => NormedSpace.exp (s • (A : Matrix ι ι ℂ))) 0 1 = _
  rw [energy_exp_smul A.2.1.1, norm_of_mem_minVel hcard A.2]

/-- **`t ↦ exp(tA)`, `A ∈ minVel`, is a path of least energy** (a point of `Ω^d`). -/
theorem expPath_mem_minPaths (hcard : Fintype.card ι = 2 * m) (A : minVel ι) :
    expPath A ∈ minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1) := fun γ' =>
  (energy_expPath hcard A).trans_le (pi_sq_le_energy hcard γ'.mem)

/-- **`A ↦ (t ↦ exp tA)` is continuous for Milnor's metric**: the speeds are all `π√(2m)`, so
the `L²` term vanishes, and the uniform term is controlled by pointwise convergence at bounded
energy (`Morse.PathSp.eventually_supDist_le_of_tendsto_apply`). -/
theorem continuous_expPath (hcard : Fintype.card ι = 2 * m) :
    Continuous (expPath (ι := ι)) := by
  refine continuous_iff_continuousAt.2 fun A => ?_
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0, ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr' : 0 < r := ENNReal.ofReal_pos.1 hr
  have h1 := PathSp.eventually_supDist_le_of_tendsto_apply
    (isSliceSubmanifold_specialUnitaryGroup (ι := ι))
    (C := (Real.pi * Real.sqrt (2 * m)) ^ 2) (l := 𝓝 A)
    (αs := fun B : minVel ι => (expPath B : ℝ → Matrix ι ι ℂ))
    (Eventually.of_forall fun B => ⟨(expPath B).mem, (energy_expPath hcard B).le⟩)
    (expPath A).mem (energy_expPath hcard A).le (fun s _ =>
      ((continuous_matrix_exp.comp (continuous_const_smul s)).comp
        continuous_subtype_val).tendsto A) hr'
  filter_upwards [h1] with B hB
  have hl2 : PathSp.l2Dist (expPath B : ℝ → Matrix ι ι ℂ) (expPath A) = 0 := by
    simp only [PathSp.l2Dist, expPath, speed_exp_smul B.2.1.1, speed_exp_smul A.2.1.1,
      norm_of_mem_minVel hcard B.2, norm_of_mem_minVel hcard A.2, sub_self]
    simp
  rw [PathSp.edist_def, hl2, ENNReal.ofReal_zero, add_zero]
  exact hB.trans hrε.le

omit [Nonempty ι] in
/-- `suDiag(1, …, 1, −1, …, −1) ∈ minVel`. -/
theorem suDiag_kHalf_mem_minVel (hcard : Fintype.card ι = 2 * m) :
    suDiag (kHalf hcard) ∈ minVel ι := by
  refine ⟨by simpa using conj_suDiag_mem (sum_kHalf hcard) (T := 1) (by simp), ?_⟩
  simpa using (sq_conj_suDiag_iff (T := 1) (by simp) (kHalf hcard)).2 (kHalf_pm hcard)

/-- **Every path of least energy from `I` to `−I` in `SU(2m)` is `t ↦ exp(tA)` on `[0, 1]` for
some `A ∈ minVel`** (it is a geodesic, Corollary 12.3, hence `exp(tA)` with `exp A = −I`; its
energy `‖A‖²` is at most `π²·2m`, so it is a minimal geodesic, so `A² = −π²I`). -/
theorem exists_minVel_of_mem_minPaths (hcard : Fintype.card ι = 2 * m)
    {γ : PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)}
    (hγ : γ ∈ minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    ∃ A ∈ minVel ι, EqOn γ (fun s : ℝ => NormedSpace.exp (s • A)) (Icc 0 1) := by
  have hgeo := isUnbrokenGeodesic_of_minimal (hN := isSliceSubmanifold_specialUnitaryGroup)
    γ.mem (fun γ' hγ' => hγ ⟨γ', hγ'⟩)
  obtain ⟨A, hA, heq⟩ := eqOn_exp_smul_of_isUnbrokenGeodesic_su γ.mem hgeo
  have hexp : NormedSpace.exp A = -1 := by
    have := heq ⟨zero_le_one, le_rfl⟩
    rw [γ.mem.2.2.2] at this
    simpa using this.symm
  refine ⟨A, ⟨hA, ?_⟩, heq⟩
  rw [← isMinimalGeodesic_exp_iff hcard hA hexp]
  have hE := hγ (expPath ⟨_, suDiag_kHalf_mem_minVel hcard⟩)
  rw [energy_expPath hcard, energy_congr heq, energy_exp_smul hA.1] at hE
  have hle : ‖A‖ ≤ Real.pi * Real.sqrt (2 * m) :=
    (pow_le_pow_iff_left₀ (norm_nonneg A) (by positivity) two_ne_zero).1 hE
  refine ⟨zero_le_one, ⟨univ, subset_univ _,
    (isMatrixGroup_specialUnitaryGroup (ι := ι)).isGeodesicOn_exp_smul hA⟩,
    fun c a b hc hcN ha hb => ?_⟩
  have h1 := riemDist_le_pathLength (N := (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) hc hcN
  simp only [ha, hb, zero_smul, NormedSpace.exp_zero, one_smul, hexp] at h1
  rw [riemDist_one_neg_one hcard] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff hc.isAdmissible.pathLength_nonneg).1 h1
  rw [pathLength_exp_smul hA.1]
  linarith

/-- For `γ ∈ Ω^d` equal to `exp(tA)` on `[0, 1]`: `A = π γ(1/2)`. -/
theorem pi_smul_apply_half {A : Matrix ι ι ℂ} (hA : A ∈ minVel ι) {γ : ℝ → Matrix ι ι ℂ}
    (heq : EqOn γ (fun s : ℝ => NormedSpace.exp (s • A)) (Icc 0 1)) :
    (Real.pi : ℝ) • γ (1 / 2) = A := by
  rw [heq ⟨by norm_num, by norm_num⟩]
  simp only
  rw [exp_half_smul_of_mem_minVel hA, smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul]

omit [Nonempty ι] in
theorem continuous_apply_half :
    Continuous fun γ : PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1) =>
      (γ : ℝ → Matrix ι ι ℂ) (1 / 2) :=
  (continuous_eval_const (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).comp
    (continuous_subtype_val.comp PathSp.continuous_toPathC)

/-- `A ↦ (t ↦ exp tA)`, `minVel → Ω^d`. -/
def minVelToPaths (hcard : Fintype.card ι = 2 * m) :
    C(minVel ι, minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :=
  ⟨fun A => ⟨expPath A, expPath_mem_minPaths hcard A⟩, (continuous_expPath hcard).subtype_mk _⟩

/-- The initial velocity, `Ω^d → minVel`, `γ ↦ π γ(1/2)`. -/
def pathsToMinVel (hcard : Fintype.card ι = 2 * m) :
    C(minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1), minVel ι) where
  toFun γ := ⟨(Real.pi : ℝ) • (γ.1 : ℝ → Matrix ι ι ℂ) (1 / 2), by
    obtain ⟨A, hA, heq⟩ := exists_minVel_of_mem_minPaths hcard γ.2
    rw [pi_smul_apply_half hA heq]
    exact hA⟩
  continuous_toFun :=
    ((continuous_apply_half.comp continuous_subtype_val).const_smul (Real.pi : ℝ)).subtype_mk
      (fun γ => _)

theorem pathsToMinVel_minVelToPaths (hcard : Fintype.card ι = 2 * m) (A : minVel ι) :
    pathsToMinVel hcard (minVelToPaths hcard A) = A :=
  Subtype.ext (pi_smul_apply_half (γ := fun s : ℝ => NormedSpace.exp (s • (A : Matrix ι ι ℂ)))
    A.2 fun _ _ => rfl)

theorem edist_minVelToPaths_pathsToMinVel (hcard : Fintype.card ι = 2 * m)
    (γ : minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    edist (minVelToPaths hcard (pathsToMinVel hcard γ)) γ = 0 := by
  obtain ⟨A, hA, heq⟩ := exists_minVel_of_mem_minPaths hcard γ.2
  rw [Subtype.edist_eq]
  refine PathSp.edist_eq_zero_of_eqOn fun t ht => ?_
  change NormedSpace.exp (t • ((Real.pi : ℝ) • (γ.1 : ℝ → Matrix ι ι ℂ) (1 / 2))) =
    (γ.1 : ℝ → Matrix ι ι ℂ) t
  rw [pi_smul_apply_half hA heq, heq ht]

/-- **Lemma 23.1 for the path space, up to homotopy**: `A ↦ (t ↦ exp tA)` is a homotopy
equivalence `minVel ≃ Ω^d`, with homotopy inverse `γ ↦ π γ(1/2)`. -/
def minPathsHomotopyEquiv (hcard : Fintype.card ι = 2 * m) :
    ContinuousMap.HomotopyEquiv (minVel ι)
      (minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) where
  toFun := minVelToPaths hcard
  invFun := pathsToMinVel hcard
  left_inv := by
    have : (pathsToMinVel hcard).comp (minVelToPaths hcard) = ContinuousMap.id _ := by
      ext A : 1
      exact pathsToMinVel_minVelToPaths hcard A
    rw [this]
  right_inv := by
    classical
    refine ⟨{
      toFun := fun x => if (x.1 : ℝ) < 1 then minVelToPaths hcard (pathsToMinVel hcard x.2)
        else x.2
      continuous_toFun := PathSp.continuous_of_edist_eq_zero continuous_snd fun x => ?_
      map_zero_left := fun γ => by simp
      map_one_left := fun γ => by simp }⟩
    split_ifs
    · exact edist_minVelToPaths_pathsToMinVel hcard x.2
    · exact edist_self _

/-- **Lemma 23.1 for the path space** (Milnor p. 128): `A ↦ (t ↦ exp tA)` is a homeomorphism of
`minVel` onto `Ω^d`, up to the identification of paths agreeing on `[0, 1]` (the separation
quotient of Milnor's pseudometric). -/
def minVelHomeomorph (hcard : Fintype.card ι = 2 * m) :
    minVel ι ≃ₜ SeparationQuotient
      (minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) where
  toFun A := SeparationQuotient.mk (minVelToPaths hcard A)
  invFun := SeparationQuotient.lift (pathsToMinVel hcard) fun _ _ h =>
    (h.map (pathsToMinVel hcard).continuous).eq
  left_inv A := by
    simp only [SeparationQuotient.lift_mk]
    exact pathsToMinVel_minVelToPaths hcard A
  right_inv := SeparationQuotient.surjective_mk.forall.2 fun γ => by
    simp only [SeparationQuotient.lift_mk]
    exact SeparationQuotient.mk_eq_mk.2
      (EMetric.inseparable_iff.2 (edist_minVelToPaths_pathsToMinVel hcard γ))
  continuous_toFun := SeparationQuotient.continuous_mk.comp (minVelToPaths hcard).continuous
  continuous_invFun := SeparationQuotient.continuous_lift (pathsToMinVel hcard).continuous

end Morse
