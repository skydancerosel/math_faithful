import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_25

open Matrix Set Filter Topology Module
open scoped ContDiff

namespace RoundTrip.V15_25

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The project's statement (universes instantiated at `0`, any finite index type, any sequence
`J` with `J_1, …, J_k` anticommuting complex structures, any `p ∈ Ω_k(n)` with
`minVelO J k p = {A ∈ 𝒯_p | A² = −I}` non-empty (hypothesis `A₀ ∈ minVelO`)), for the stratum `S` of
`p` in `Ω_k(n)` (project's induced metric, Frobenius norm): `−p ∈ S`; the Riemannian distance from
`p` to `−p` in `S` is `π√n`; every path from `p` to `−p` in `S` has energy `≥ π²n`; the semicircles
`t ↦ p exp(πtA)`, `A ∈ minVelO`, have least energy; every path of least energy is one of them on
`[0, 1]`; and the midpoint of `t ↦ p exp(πtA)` is `pA` when `A² = −I`. -/
def A : Prop :=
  type_of% @Morse.neg_mem_omegaStratum.{0} ∧ type_of% @Morse.riemDist_omegaStratum.{0} ∧
    type_of% @Morse.pi_sq_card_le_energy.{0} ∧ type_of% @Morse.omegaPath_mem_minPaths.{0} ∧
    type_of% @Morse.exists_minVelO_of_mem_minPaths.{0} ∧ type_of% @Morse.omegaGeo_half.{0}

theorem A_holds : A :=
  ⟨@Morse.neg_mem_omegaStratum.{0}, @Morse.riemDist_omegaStratum.{0},
    @Morse.pi_sq_card_le_energy.{0}, @Morse.omegaPath_mem_minPaths.{0},
    @Morse.exists_minVelO_of_mem_minPaths.{0}, @Morse.omegaGeo_half.{0}⟩

/-! ## Vocabulary -/

section Vocab
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isACFam_iff (Js : ℕ → Mat ι) (m : ℕ) : IsACFam Js m ↔ Morse.IsAnticommFamily Js m :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.cs, h.anti⟩⟩

theorem omegaK_eq_omega (Js : ℕ → Mat ι) (k : ℕ) : OmegaK Js k = Morse.Omega Js k := by
  cases k with
  | zero => rfl
  | succ k =>
    ext J
    simp only [OmegaK, Morse.Omega, IsCplxStr, Morse.IsComplexStructure, AntiComm,
      Set.mem_ofPred_eq]
    refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun _ =>
      ⟨fun h => by rw [h, neg_neg], fun h => by rw [h, neg_neg]⟩)

theorem omegaK_subset_orth (Js : ℕ → Mat ι) (k : ℕ) : OmegaK Js k ⊆ Orth ι := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact fun J hJ => hJ.1.1

theorem orth_iff {X : Mat ι} : X ∈ Orth ι ↔ Xᵀ * X = 1 := by
  rw [Orth, SetLike.mem_coe, mem_orthogonalGroup_iff']

theorem orth_iff' {X : Mat ι} : X ∈ Orth ι ↔ X * Xᵀ = 1 := by
  rw [Orth, SetLike.mem_coe, mem_orthogonalGroup_iff]

/-- The family where `J_k` is replaced by a point `x ∈ Ω_k(n)` (Milnor's `J_1, …, J_{k-1}, x`). -/
def famAt (Js : ℕ → Mat ι) (k : ℕ) (x : Mat ι) : ℕ → Mat ι := Function.update Js k x

theorem omega_famAt (Js : ℕ → Mat ι) (k : ℕ) (x : Mat ι) :
    Morse.Omega (famAt Js k x) k = Morse.Omega Js k := by
  cases k with
  | zero => rfl
  | succ k =>
    ext J
    simp only [Morse.Omega, Set.mem_ofPred_eq, famAt]
    refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun h => ?_)
    rw [Function.update_of_ne (by omega)]

theorem tanAlg_famAt (Js : ℕ → Mat ι) (k : ℕ) (x y : Mat ι) :
    Morse.tanAlg (famAt Js k x) k y = Morse.tanAlg Js k y := by
  ext A
  simp only [Morse.mem_tanAlg, famAt]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ =>
    forall_congr' fun h => ?_))
  rw [Function.update_of_ne (by omega)]

theorem omegaStratum_famAt (Js : ℕ → Mat ι) (k : ℕ) (x p : Mat ι) :
    Morse.omegaStratum (famAt Js k x) k p = Morse.omegaStratum Js k p := by
  ext y
  simp only [Morse.omegaStratum, Set.mem_ofPred_eq, omega_famAt]
  rw [tanAlg_famAt, tanAlg_famAt]

/-- For `x ∈ Ω_k(n)` (`J_1, …, J_{k-1}` anticommuting complex structures), `J_1, …, J_{k-1}, x` is
an anticommuting family (`k ≥ 1`; for `k = 0` the empty family). -/
theorem isAnticommFamily_famAt {Js : ℕ → Mat ι} {k : ℕ} (hJ : IsACFam Js (k - 1)) {x : Mat ι}
    (hx : x ∈ OmegaK Js k) : Morse.IsAnticommFamily (famAt Js k x) k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨fun α h1 h2 => absurd h2 (by omega), fun α _ h1 h2 _ _ _ => absurd h2 (by omega)⟩
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hx' := hx
  simp only [Nat.add_sub_cancel] at hJ
  refine ⟨fun α h1 h2 => ?_, fun α β h1 h2 h3 h4 hne => ?_⟩
  · by_cases hα : α = k + 1
    · subst hα; simp only [famAt, Function.update_self]; exact hx.1
    · simp only [famAt, Function.update_of_ne hα]; exact hJ.1 α h1 (by omega)
  · by_cases hα : α = k + 1
    · subst hα
      simp only [famAt, Function.update_self, Function.update_of_ne (Ne.symm hne)]
      have := hx.2 β h3 (by omega)
      exact this
    · by_cases hβ : β = k + 1
      · subst hβ
        simp only [famAt, Function.update_self, Function.update_of_ne hα]
        have := hx.2 α h1 (by omega)
        rw [this, neg_neg]
      · simp only [famAt, Function.update_of_ne hα, Function.update_of_ne hβ]
        exact hJ.2 α β h1 (by omega) h3 (by omega) hne

end Vocab

/-! ## Calculus on `Mₙ(ℝ)` (Frobenius normed algebra; same topology, hence same derivatives, as
the blind files' elementwise norm) -/

section Calc
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem contDiffOn_frob_of_elem {c : ℝ → Mat ι} {s : Set ℝ}
    (hc : @ContDiffOn ℝ _ ℝ _ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace ∞ c s) :
    ContDiffOn ℝ ∞ c s :=
  @ContDiff.comp_contDiffOn ℝ ℝ (Mat ι) (Mat ι) _ _ _ Matrix.normedAddCommGroup
    Matrix.normedSpace _ _ ∞ s _ c
    (@ContinuousLinearMap.contDiff ℝ (Mat ι) (Mat ι) _ Matrix.normedAddCommGroup
      Matrix.normedSpace _ _ ∞ (ContinuousLinearMap.id ℝ (Mat ι))) hc

theorem contDiffOn_elem_of_frob {c : ℝ → Mat ι} {s : Set ℝ} (hc : ContDiffOn ℝ ∞ c s) :
    @ContDiffOn ℝ _ ℝ _ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace ∞ c s :=
  @ContDiff.comp_contDiffOn ℝ ℝ (Mat ι) (Mat ι) _ _ _ _ _ Matrix.normedAddCommGroup
    Matrix.normedSpace ∞ s _ c
    (@ContinuousLinearMap.contDiff ℝ (Mat ι) (Mat ι) _ _ _ Matrix.normedAddCommGroup
      Matrix.normedSpace ∞ (ContinuousLinearMap.id ℝ (Mat ι))) hc

theorem contDiff_elem_of_frob {c : ℝ → Mat ι} (hc : ContDiff ℝ ∞ c) :
    @ContDiff ℝ _ ℝ _ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace ∞ c :=
  (@contDiffOn_univ ℝ _ ℝ _ _ (Mat ι) Matrix.normedAddCommGroup Matrix.normedSpace c ∞).1
    (contDiffOn_elem_of_frob hc.contDiffOn)

/-- The transpose, as a continuous linear map. -/
def trCLM : Mat ι →L[ℝ] Mat ι where
  toFun := Matrix.transpose
  map_add' := transpose_add
  map_smul' := transpose_smul
  cont := continuous_id.matrix_transpose

theorem hasDerivWithinAt_tr {c : ℝ → Mat ι} {v : Mat ι} {s : Set ℝ} {t : ℝ}
    (h : HasDerivWithinAt c v s t) : HasDerivWithinAt (fun u => (c u)ᵀ) vᵀ s t :=
  (trCLM (ι := ι)).hasFDerivAt.comp_hasDerivWithinAt t h

theorem hasDerivAt_tr {c : ℝ → Mat ι} {v : Mat ι} {t : ℝ}
    (h : HasDerivAt c v t) : HasDerivAt (fun u => (c u)ᵀ) vᵀ t :=
  (trCLM (ι := ι)).hasFDerivAt.comp_hasDerivAt t h

theorem eq_of_hasDerivWithinAt_eqOn {F G : ℝ → Mat ι} {F' G' : Mat ι} {s : Set ℝ} {t : ℝ}
    (hs : UniqueDiffWithinAt ℝ s t) (ht : t ∈ s) (hF : HasDerivWithinAt F F' s t)
    (hG : HasDerivWithinAt G G' s t) (h : EqOn F G s) : F' = G' :=
  hs.eq_deriv _ (hF.congr_of_mem (fun y hy => (h hy).symm) ht) hG

theorem frob_eq_inner (X Y : Mat ι) : frob X Y = ⟪X, Y⟫ := by
  rw [Morse.inner_def, frob, ← trace_transpose, transpose_mul, transpose_transpose,
    trace_mul_comm]
  rfl

theorem inner_sym_skew {S K : Mat ι} (hS : Sᵀ = S) (hK : Kᵀ = -K) : ⟪S, K⟫ = 0 :=
  Morse.inner_eq_zero_of_hermitian_of_skew (by rwa [conjTranspose_eq_transpose_of_trivial])
    (by rwa [conjTranspose_eq_transpose_of_trivial])

/-- In `O(n)`: a tangent vector at `p` is `p·S` with `S = pᵀv` skew. -/
theorem skew_of_mem_tanSet_orth {p v : Mat ι} (hv : v ∈ TanSet (Orth ι) p) :
    (pᵀ * v)ᵀ = -(pᵀ * v) := by
  obtain ⟨c, -, hcN, hc0, hcv⟩ := hv
  have h1 : HasDerivAt (fun s => (c s)ᵀ * c s) (vᵀ * c 0 + (c 0)ᵀ * v) 0 :=
    (hasDerivAt_tr hcv).mul hcv
  have h2 : (fun s => (c s)ᵀ * c s) = fun _ => (1 : Mat ι) := funext fun s => orth_iff.1 (hcN s)
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const 0 _)
  rw [hc0] at h3
  rw [transpose_mul, transpose_transpose, eq_neg_iff_add_eq_zero, h3]

/-- For `x ∈ Ω_k(n)` and `A ∈ 𝒯_x`, `xA` is a tangent vector of `Ω_k(n)` at `x` (the curve
`s ↦ x exp(sA)`). -/
theorem mul_mem_tanSet {Js : ℕ → Mat ι} {k : ℕ} {x A : Mat ι} (hx : x ∈ OmegaK Js k)
    (hA : A ∈ Morse.tanAlg Js k x) : x * A ∈ TanSet (OmegaK Js k) x := by
  refine ⟨fun s => x * NormedSpace.exp (s • A), contDiff_elem_of_frob
    (contDiff_const.mul (Morse.contDiff_exp_smul A)), fun s => ?_, by simp, ?_⟩
  · rw [omegaK_eq_omega] at hx ⊢
    exact Morse.mul_exp_mem_omega hx ((Morse.tanAlg Js k x).smul_mem s hA)
  · have := Morse.hasDerivAt_mul_exp_smul x A 0
    simpa using this

end Calc



/-! ## Dictionary for paths (adapted from `Items/V14_15.lean`): blind piecewise smooth paths on
`[0, 1]` are the project's, and `lenM` is the project's `pathLength` -/

section PathDict
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem le_of_strictSeq {t : ℕ → ℝ} {k : ℕ} (ht : ∀ i < k, t i < t (i + 1)) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ k) : t i ≤ t j := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (Nat.lt_succ_iff.1 h) (by omega)).trans (ht j (by omega)).le
    · rw [le_antisymm hij h]

theorem isPiecewiseSmooth_of_isPWOn {c : ℝ → Mat ι} (h : IsPWOn c) :
    Morse.IsPiecewiseSmooth c 0 1 := by
  obtain ⟨k, t, h0, hk, hlt, hsm⟩ := h
  have hsm' : ∀ i < k, ContDiffOn ℝ ∞ c (Icc (t i) (t (i + 1))) :=
    fun i hi => contDiffOn_frob_of_elem (hsm i hi)
  refine ⟨zero_le_one, ?_, (Finset.range (k + 1)).image t, ?_⟩
  · have key : ∀ j ≤ k, ContinuousOn c (Icc (t 0) (t j)) := by
      intro j
      induction j with
      | zero => intro _; rw [Icc_self]; exact continuousOn_singleton _ _
      | succ j ih =>
        intro hj
        rw [← Icc_union_Icc_eq_Icc (le_of_strictSeq hlt (Nat.zero_le j) (by omega))
          (hlt j (by omega)).le]
        exact (ih (by omega)).union_of_isClosed (hsm' j (by omega)).continuousOn isClosed_Icc
          isClosed_Icc
    rw [← h0, ← hk]
    exact key k le_rfl
  · intro s u has hsu hub hB
    have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
    classical
    set m := Nat.find hP
    have hm : s < t m ∧ m ≤ k := Nat.find_spec hP
    have hm0 : m ≠ 0 := by
      intro h; have := hm.1; rw [h, h0] at this; linarith
    have hi : t (m - 1) ≤ s := by
      by_contra hcon
      exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
        ⟨lt_of_not_ge hcon, by omega⟩
    have hu : u ≤ t m := by
      by_contra hcon
      exact hB (t m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩)
        ⟨hm.1, lt_of_not_ge hcon⟩
    have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
    refine (hsm' (m - 1) (by omega)).mono ?_
    rw [hm1]
    exact Icc_subset_Icc hi hu

theorem isPWOn_of_isPiecewiseSmooth {c : ℝ → Mat ι} (hc : Morse.IsPiecewiseSmooth c 0 1) :
    IsPWOn c := by
  obtain ⟨hab, -, B, hB⟩ := hc
  suffices hsub : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t k = 1 ∧ (∀ i < k, t i < t (i + 1)) ∧
      ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ 1 ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) by
    obtain ⟨k, t, h0, hk, hlt, hgood⟩ := hsub
    refine ⟨k, t, h0, hk, hlt, fun i hi => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hgood i hi
    exact contDiffOn_elem_of_frob (hB _ _ h1 (hlt i hi) h2 h3)
  have hlt : (0 : ℝ) < 1 := zero_lt_one
  classical
  set S : Finset ℝ := insert 0 (insert 1 (B.filter (· ∈ Ioo (0 : ℝ) 1)))
  have hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
  have hbS : (1 : ℝ) ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨0, haS, 1, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else 1
  have ht : ∀ j (h : j < m), t j = e ⟨j, h⟩ := fun j h => dif_pos h
  refine ⟨m - 1, t, ?_, ?_, ?_, ?_⟩
  · rw [ht 0 (by omega), Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (Finset.min'_le _ _ haS) ((hS _ (Finset.min'_mem _ _)).1)
  · rw [ht (m - 1) (by omega), Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm ((hS _ (Finset.max'_mem _ _)).2) (Finset.le_max' _ _ hbS)
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    refine ⟨(hS _ (Finset.orderEmbOfFin_mem _ _ _)).1, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2,
      fun x hx hxi => ?_⟩
    have hxS : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hx, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).1.trans_lt hxi.1,
        hxi.2.trans_le (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2⟩))
    obtain ⟨j, rfl⟩ : x ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    have h1 := e.lt_iff_lt.1 hxi.1
    have h2 := e.lt_iff_lt.1 hxi.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega

theorem frob_self_eq (X : Mat ι) : frob X X = ‖X‖ ^ 2 := by
  rw [frob_eq_inner, real_inner_self_eq_norm_sq]

theorem lenM_eq (c : ℝ → Mat ι) : lenM c = Morse.pathLength c 0 1 := by
  unfold lenM Morse.pathLength
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [frob_self_eq, Real.sqrt_sq (norm_nonneg _)]

/-- A blind path in `N` from `p` to `q` is in the project's path space. -/
theorem mem_pathSpace_of_isPathIn {N : Set (Mat ι)} {w : ℝ → Mat ι} (hw : IsPathIn N w) :
    w ∈ Morse.pathSpace N (w 0) (w 1) :=
  ⟨isPiecewiseSmooth_of_isPWOn hw.1, hw.2, rfl, rfl⟩

theorem isPathIn_of_mem_pathSpace {N : Set (Mat ι)} {w : ℝ → Mat ι} {p q : Mat ι}
    (hw : w ∈ Morse.pathSpace N p q) : IsPathIn N w :=
  ⟨isPWOn_of_isPiecewiseSmooth hw.1, hw.2.1⟩

end PathDict

/-! ## Great circles are geodesics of subsets of `O(n)` (from `Items/V15_7.lean`) -/

section Circ
open scoped Matrix.Norms.Elementwise
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem frob_eq_sum (X Y : Mat ι) : frob X Y = ∑ i, ∑ j, X i j * Y i j := by
  simp [frob, Matrix.trace, Matrix.mul_apply]

/-- In a subset of `O(n)` every tangent vector at `p` is `frob`-orthogonal to `p` (`O(n)` lies on
the sphere `tr(ppᵀ) = n`). -/
theorem frob_tan_eq_zero {N : Set (Mat ι)} (hN : N ⊆ Orth ι) {p v : Mat ι}
    (hv : v ∈ TanSet N p) : frob p v = 0 := by
  obtain ⟨c, -, hcN, hc0, hcv⟩ := hv
  have hent : ∀ i j, HasDerivAt (fun s => c s i j) (v i j) 0 := fun i j =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hcv i) j
  have hf : HasDerivAt (fun s => ∑ i, ∑ j, c s i j * c s i j)
      (∑ i, ∑ j, (v i j * c 0 i j + c 0 i j * v i j)) 0 :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => (hent i j).mul (hent i j)
  have hconst : (fun s => ∑ i, ∑ j, c s i j * c s i j) = fun _ => (Fintype.card ι : ℝ) := by
    funext s
    have h1 : c s * (c s)ᵀ = 1 := by
      have := hN (hcN s)
      rw [SetLike.mem_coe, mem_orthogonalGroup_iff] at this
      simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
    have h2 := congrArg Matrix.trace h1
    rw [trace_one] at h2
    rw [← h2]
    simp [Matrix.trace, Matrix.mul_apply]
  rw [hconst] at hf
  have h0 := hf.unique (hasDerivAt_const 0 _)
  rw [frob_eq_sum, ← hc0]
  have : ∑ i, ∑ j, (v i j * c 0 i j + c 0 i j * v i j) = 2 * ∑ i, ∑ j, c 0 i j * v i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  linarith

/-- The great circle `t ↦ cos(πt)·P + sin(πt)·Q`. -/
noncomputable def circ (P Q : Mat ι) (t : ℝ) : Mat ι :=
  Real.cos (Real.pi * t) • P + Real.sin (Real.pi * t) • Q

theorem circ_contDiff (P Q : Mat ι) (m : WithTop ℕ∞) : ContDiff ℝ m (circ P Q) := by
  unfold circ; fun_prop

theorem circ_hasDerivAt (P Q : Mat ι) (t : ℝ) :
    HasDerivAt (circ P Q) ((-(Real.pi * Real.sin (Real.pi * t))) • P +
      (Real.pi * Real.cos (Real.pi * t)) • Q) t := by
  have hl : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi t := by
    simpa using (hasDerivAt_id t).const_mul Real.pi
  have hc := (Real.hasDerivAt_cos (Real.pi * t)).comp t hl
  have hs := (Real.hasDerivAt_sin (Real.pi * t)).comp t hl
  have h := (hc.smul_const P).add (hs.smul_const Q)
  have heq : (-(Real.pi * Real.sin (Real.pi * t))) • P + (Real.pi * Real.cos (Real.pi * t)) • Q =
      (-Real.sin (Real.pi * t) * Real.pi) • P + (Real.cos (Real.pi * t) * Real.pi) • Q := by
    module
  rw [heq]
  exact h

theorem deriv_circ (P Q : Mat ι) : deriv (circ P Q) =
    circ (Real.pi • Q) (-(Real.pi • P)) := by
  funext t
  refine (circ_hasDerivAt P Q t).deriv.trans ?_
  simp only [circ]
  module

theorem iteratedDeriv_two_circ (P Q : Mat ι) (t : ℝ) :
    iteratedDeriv 2 (circ P Q) t = (-(Real.pi ^ 2)) • circ P Q t := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  erw [deriv_circ, deriv_circ]
  simp only [circ]
  module

/-- A great circle through points of `N ⊆ O(n)` that stays in `N` is a geodesic of `N`: its
acceleration `-π²γ` is normal to `N`. -/
theorem isGeodOn_circ {N : Set (Mat ι)} (hN : N ⊆ Orth ι) (P Q : Mat ι)
    (hmem : ∀ t, circ P Q t ∈ N) : IsGeodOn N (circ P Q) 0 1 := by
  refine ⟨zero_lt_one, (circ_contDiff P Q _).contDiffOn, fun t _ => hmem t, fun t ht v hv => ?_⟩
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
    ((circ_contDiff P Q 2).contDiffAt) ht, iteratedDeriv_two_circ]
  have h := frob_tan_eq_zero hN hv
  rw [frob_eq_sum] at h ⊢
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, h, mul_zero]


end Circ

/-! ## Paths in `Ω_k(n)` from `p` stay in the stratum of `p` (it is open and closed in `Ω_k(n)`) -/

section Conn
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_stratum_of_path {Js : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily Js k)
    {p : Mat ι} (hp : p ∈ Morse.Omega Js k) {w : ℝ → Mat ι} (hc : ContinuousOn w (Icc 0 1))
    (hΩ : ∀ t ∈ Icc (0 : ℝ) 1, w t ∈ Morse.Omega Js k) (h0 : w 0 = p) :
    ∀ t ∈ Icc (0 : ℝ) 1, w t ∈ Morse.omegaStratum Js k p := by
  set C := Morse.omegaStratum Js k p
  set u : Set (Mat ι) := {y | ∀ᶠ z in 𝓝 y, z ∈ Morse.Omega Js k → z ∈ C}
  have hu : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hv : IsOpen Cᶜ := (Morse.isClosed_omegaStratum hJ p).isOpen_compl
  have hpre : IsPreconnected (w '' Icc 0 1) := isPreconnected_Icc.image w hc
  have hsub : w '' Icc 0 1 ⊆ u ∪ Cᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases hC : w t ∈ C
    · exact Or.inl (Morse.eventually_mem_omegaStratum hJ hC)
    · exact Or.inr hC
  have hdisj : w '' Icc 0 1 ∩ (u ∩ Cᶜ) = ∅ := by
    ext y
    simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨t, ht, rfl⟩ hy hyC
    exact hyC (hy.self_of_nhds (hΩ t ht))
  rcases isPreconnected_iff_subset_of_disjoint.1 hpre u Cᶜ hu hv hsub hdisj with h | h
  · intro t ht
    exact (h ⟨t, ht, rfl⟩ : w t ∈ u).self_of_nhds (hΩ t ht)
  · exfalso
    have : w 0 ∈ Cᶜ := h ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
    rw [h0] at this
    exact this ⟨hp, rfl⟩

end Conn

section Elem
open scoped Matrix.Norms.Elementwise
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem iteratedDerivWithin_two_eq (γ : ℝ → Mat ι) (s : Set ℝ) (t : ℝ) :
    iteratedDerivWithin 2 γ s t = derivWithin (derivWithin γ s) s t := by
  rw [iteratedDerivWithin_eq_iterate]; rfl

end Elem

/-! ## Blind geodesics of `Ω_k(n)` on `[0, 1]` are the project's unbroken geodesics of the stratum -/

section GeoConv
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isUnbrokenGeodesic_of_isGeodOn {Js : ℕ → Mat ι} {k : ℕ}
    (hJ : Morse.IsAnticommFamily Js k) {p : Mat ι} {γ : ℝ → Mat ι}
    (hγ : IsGeodOn (OmegaK Js k) γ 0 1)
    (hS : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Morse.omegaStratum Js k p) :
    Morse.IsUnbrokenGeodesic (Morse.isSliceSubmanifold_omegaStratum hJ p) γ := by
  obtain ⟨-, hsm, hmem, hnorm⟩ := hγ
  have hsm' : ContDiffOn ℝ ∞ γ (Icc 0 1) := contDiffOn_frob_of_elem hsm
  refine ⟨hsm', ⟨isOpen_Ioo, fun t ht => hS t (Ioo_subset_Icc_self ht),
    hsm'.mono Ioo_subset_Icc_self, fun t ht => ?_⟩⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hT := Morse.isTotGeo_omegaStratum hJ p
  rw [hT.mem_tangentSubspace_iff] at hu
  have hx : γ t ∈ OmegaK Js k := hmem t htI
  have hxo : γ t * (γ t)ᴴ = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial]
    exact orth_iff'.1 (omegaK_subset_orth Js k hx)
  have hu' : u = γ t * ((γ t)ᴴ * u) := by rw [← Matrix.mul_assoc, hxo, Matrix.one_mul]
  have hv : u ∈ TanSet (OmegaK Js k) (γ t) := by
    rw [hu']; exact mul_mem_tanSet hx hu
  have hn := hnorm t htI u hv
  rw [iteratedDerivWithin_two_eq] at hn
  change frob (derivWithin (derivWithin γ (Icc 0 1)) (Icc 0 1) t) u = 0 at hn
  have e : derivWithin (derivWithin γ (Icc 0 1)) (Icc 0 1) t = deriv (deriv γ) t := by
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)
  rw [e, frob_eq_inner, real_inner_comm] at hn
  exact hn

end GeoConv

/-! ## A ⇒ B -/

section Main
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem transpose_cs {J : Mat ι} (hJ : IsCplxStr J) : Jᵀ = -J := by
  have h1 : Jᵀ * J = 1 := orth_iff.1 hJ.1
  calc Jᵀ = Jᵀ * (-(J * J)) := by rw [hJ.2, neg_neg, Matrix.mul_one]
    _ = -J := by rw [Matrix.mul_neg, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem semiGeo_eq_omegaGeo (p A : Mat ι) : semiGeo p A = Morse.omegaGeo p A := by
  funext t
  simp only [semiGeo, Morse.omegaGeo, mexp, smul_smul, mul_comm]

theorem semiGeo_eq_circ {p A : Mat ι} (hA : A * A = -1) : semiGeo p A = circ p (p * A) := by
  funext t
  simp only [semiGeo, circ, mexp, Morse.exp_smul_of_mul_self_eq_neg_one hA, Matrix.mul_add,
    Matrix.mul_smul, Matrix.mul_one]

/-- A lower bound for the blind lengths from the project's Riemannian distance. -/
theorem le_lenM_of_riemDist {N : Set (Mat ι)} {p q : Mat ι} {L : ℝ}
    (hd : Morse.riemDist (N := N) p q = ENNReal.ofReal L) {w : ℝ → Mat ι} (hw : IsPathIn N w)
    (h0 : w 0 = p) (h1 : w 1 = q) : L ≤ lenM w := by
  have hps := isPiecewiseSmooth_of_isPWOn hw.1
  have h := Morse.riemDist_le_pathLength (N := N) hps hw.2
  rw [h0, h1, hd] at h
  rw [lenM_eq]
  exact (ENNReal.ofReal_le_ofReal_iff hps.isAdmissible.pathLength_nonneg).1 h

theorem lenM_semiGeo {Js : ℕ → Mat ι} {k : ℕ} {p A : Mat ι} (hpo : pᵀ * p = 1)
    (hA : A ∈ Morse.minVelO Js k p) :
    lenM (semiGeo p A) = Real.pi * Real.sqrt (Fintype.card ι) := by
  have hpo' : pᴴ * p = 1 := by rwa [conjTranspose_eq_transpose_of_trivial]
  have hsk : (Real.pi • A)ᴴ = -(Real.pi • A) := by
    rw [conjTranspose_smul, star_trivial, hA.1.1, smul_neg]
  rw [lenM_eq, semiGeo_eq_omegaGeo]
  unfold Morse.omegaGeo
  rw [Morse.IsTotGeo.pathLength_mul_exp_smul hpo' hsk, Morse.norm_pi_smul_of_minVelO hA]

/-- A ⇒ B. Let `p = J_k`. For a complex structure `A ∈ 𝒯_p` (`A ∈ minVelO`): `t ↦ p exp(πtA)` is the
great circle `cos(πt)p + sin(πt)pA`, a geodesic of every subset of `O(n)` containing it
(acceleration `−π²γ`, normal to the sphere containing `O(n)`); its length is `π√n`; every blind
path from `p` to `−p` has length `≥ π√n`, in `O(n)` by A's `riemDist_omegaStratum` for `k = 0`
(`Ω_0(n) = O(n)` is its own stratum), in `Ω_k(n)` by A's `riemDist_omegaStratum` for `k` (the path
stays in the stratum of `p`, which is open and closed in `Ω_k(n)`); the midpoint is A's
`omegaGeo_half`. Conversely, a blind minimal geodesic `γ` of `Ω_k(n)` from `p` to `−p` stays in the
stratum, is an unbroken geodesic and a minimal path there, hence of least energy
(`Morse.energy_le_of_isMinimalPath`); A's `exists_minVelO_of_mem_minPaths` then gives the complex
structure `A` — its hypothesis `minVelO ≠ ∅` (which B does not assume) is supplied by `γ` itself:
`γ = p exp(tV)` (`Morse.IsTotGeo.eqOn_of_isUnbrokenGeodesic`) with `exp V = −I`, and
`exp(V/2) ∈ minVelO`. -/
theorem A_to_B : A → B := by
  rintro ⟨-, hriem, -, -, hexmin, hhalf⟩ n k Js hk hJ
  have hJ' : Morse.IsAnticommFamily Js k := (isACFam_iff Js k).1 hJ
  have hp : Js k ∈ Morse.Omega Js k := hJ'.mem_omega hk
  have hpO : Js k ∈ Orth (Fin n) := omegaK_subset_orth Js k (by rw [omegaK_eq_omega]; exact hp)
  have hpo : (Js k)ᵀ * Js k = 1 := orth_iff.1 hpO
  have hk0 : k ≠ 0 := by omega
  refine ⟨fun A hAcs hAk hAα => ?_, fun γ hγmin h0 h1 => ?_⟩
  · have hA2 : A * A = -1 := hAcs.2
    have hAT : A ∈ Morse.tanAlg Js k (Js k) :=
      ⟨by rw [conjTranspose_eq_transpose_of_trivial]; exact transpose_cs hAcs, fun _ => hAk,
        fun α h1 h2 => (hAα α h1 (by omega)).eq⟩
    have hAmin : A ∈ Morse.minVelO Js k (Js k) := ⟨hAT, hA2⟩
    have hmemΩ : ∀ t, semiGeo (Js k) A t ∈ OmegaK Js k := fun t => by
      rw [omegaK_eq_omega]
      exact Morse.mul_exp_mem_omega hp ((Morse.tanAlg Js k (Js k)).smul_mem _ hAT)
    have hs0 : semiGeo (Js k) A 0 = Js k := by simp [semiGeo]
    have hs1 : semiGeo (Js k) A 1 = -Js k := by
      simp only [semiGeo, mexp, mul_one, Morse.exp_pi_smul hA2, Matrix.mul_neg, Matrix.mul_one]
    have hgeoN : ∀ N : Set (Mat (Fin n)), N ⊆ Orth (Fin n) → (∀ t, semiGeo (Js k) A t ∈ N) →
        IsGeodOn N (semiGeo (Js k) A) 0 1 := fun N hN hm => by
      rw [semiGeo_eq_circ hA2]
      exact isGeodOn_circ hN _ _ (by rw [← semiGeo_eq_circ hA2]; exact hm)
    have hlen := lenM_semiGeo hpo hAmin
    refine ⟨hs0, hs1, hgeoN _ (omegaK_subset_orth Js k) hmemΩ,
      ⟨hgeoN _ le_rfl (fun t => omegaK_subset_orth Js k (hmemΩ t)), fun w hw hw0 hw1 => ?_⟩,
      ⟨hgeoN _ (omegaK_subset_orth Js k) hmemΩ, fun w hw hw0 hw1 => ?_⟩, ?_⟩
    · -- minimal in `O(n)`: A at `k = 0`
      rw [hs0] at hw0; rw [hs1] at hw1
      have hJ0 : Morse.IsAnticommFamily Js 0 :=
        ⟨fun α h1 h2 => absurd h2 (by omega), fun α _ h1 h2 _ _ _ => absurd h2 (by omega)⟩
      have hp0 : Js k ∈ Morse.Omega Js 0 := hpO
      have hA0 : A ∈ Morse.minVelO Js 0 (Js k) :=
        ⟨⟨hAT.1, fun h => absurd rfl h, fun α h1 h2 => absurd h2 (by omega)⟩, hA2⟩
      have hd := hriem hJ0 hp0 hA0
      rw [Morse.omegaStratum_zero] at hd
      rw [hlen]
      exact le_lenM_of_riemDist hd hw hw0 hw1
    · -- minimal in `Ω_k(n)`: A at `k`, on the stratum of `J_k`
      rw [hs0] at hw0; rw [hs1] at hw1
      have hd := hriem hJ' hp hAmin
      have hps := isPiecewiseSmooth_of_isPWOn hw.1
      have hS := mem_stratum_of_path hJ' hp hps.2.1
        (fun t ht => by rw [← omegaK_eq_omega]; exact hw.2 t ht) hw0
      rw [hlen]
      exact le_lenM_of_riemDist hd ⟨hw.1, hS⟩ hw0 hw1
    · rw [semiGeo_eq_omegaGeo]; exact hhalf hA2
  · -- the converse
    obtain ⟨hgeo, hmin⟩ := hγmin
    have hsm' : ContDiffOn ℝ ∞ γ (Icc 0 1) := contDiffOn_frob_of_elem hgeo.2.1
    have hS := mem_stratum_of_path hJ' hp hsm'.continuousOn
      (fun t ht => by rw [← omegaK_eq_omega]; exact hgeo.2.2.1 t ht) h0
    have hpath : γ ∈ Morse.pathSpace (Morse.omegaStratum Js k (Js k)) (Js k) (-Js k) :=
      ⟨Morse.IsPiecewiseSmooth.of_contDiffOn hsm' zero_le_one subset_rfl, hS, h0, h1⟩
    have hunb := isUnbrokenGeodesic_of_isGeodOn hJ' hgeo hS
    have hminpath : Morse.IsMinimalPath (Morse.omegaStratum Js k (Js k)) γ (Js k) (-Js k) := by
      refine ⟨hpath, fun c hc => ?_⟩
      have hcΩ : IsPathIn (OmegaK Js k) c := ⟨isPWOn_of_isPiecewiseSmooth hc.1,
        fun t ht => by rw [omegaK_eq_omega]; exact (hc.2.1 t ht).1⟩
      have := hmin c hcΩ (by rw [hc.2.2.1, h0]) (by rw [hc.2.2.2, h1])
      rwa [lenM_eq, lenM_eq] at this
    have hmP : (⟨γ, hpath⟩ : Morse.PathSp (Morse.omegaStratum Js k (Js k)) (Js k) (-Js k)) ∈
        Morse.minPaths (Morse.omegaStratum Js k (Js k)) (Js k) (-Js k) :=
      fun γ' => Morse.energy_le_of_isMinimalPath (Morse.isSliceSubmanifold_omegaStratum hJ' (Js k))
        hminpath hunb γ'.2
    -- a minimal direction, from the midpoint of `γ`
    obtain ⟨V, hV, heq⟩ :=
      (Morse.isTotGeo_omegaStratum hJ' (Js k)).eqOn_of_isUnbrokenGeodesic hpath hunb
    have hexpV : NormedSpace.exp V = -1 := by
      have e1 : γ 1 = Js k * NormedSpace.exp ((1 : ℝ) • V) := heq ⟨zero_le_one, le_rfl⟩
      rw [h1, one_smul] at e1
      have e2 := congrArg ((Js k)ᵀ * ·) e1
      simpa only [← Matrix.mul_assoc, hpo, Matrix.one_mul, Matrix.mul_neg] using e2.symm
    set E := NormedSpace.exp ((1 / 2 : ℝ) • V) with hEdef
    have hEE : E * E = -1 := by
      have := Morse.exp_half_mul_exp_half V 1
      rw [one_smul, hexpV] at this
      rw [hEdef, ← this]
    have hVsk : ((1 / 2 : ℝ) • V)ᴴ = -((1 / 2 : ℝ) • V) := by
      rw [conjTranspose_smul, star_trivial, hV.1, smul_neg]
    have hEo : Eᴴ * E = 1 := Morse.exp_conjTranspose_mul_exp_of_skew hVsk
    have hEsk : Eᴴ = -E := by
      calc Eᴴ = Eᴴ * (-(E * E)) := by rw [hEE, neg_neg, Matrix.mul_one]
        _ = -E := by rw [Matrix.mul_neg, ← Matrix.mul_assoc, hEo, Matrix.one_mul]
    have hEneg : NormedSpace.exp (-((1 / 2 : ℝ) • V)) = -E := by
      calc NormedSpace.exp (-((1 / 2 : ℝ) • V))
          = NormedSpace.exp (-((1 / 2 : ℝ) • V)) * (-(E * E)) := by rw [hEE, neg_neg, Matrix.mul_one]
        _ = -E := by
          rw [Matrix.mul_neg, ← Matrix.mul_assoc, hEdef, Morse.exp_neg_mul_exp, Matrix.one_mul]
    have hEp : E * Js k = -(Js k * E) := by
      have hc : (-((1 / 2 : ℝ) • V)) * Js k = -(Js k * (-((1 / 2 : ℝ) • V))) := by
        rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, smul_mul_assoc, hV.2.1 hk0, mul_smul_comm,
          smul_neg, neg_neg]
      have := Morse.mul_exp_eq_exp_neg_mul hc
      rw [neg_neg, hEneg] at this
      rw [← this, Matrix.mul_neg]
    have hEα : ∀ α, 1 ≤ α → α < k → E * Js α = Js α * E := fun α h1 h2 =>
      (((show Commute V (Js α) from hV.2.2 α h1 h2).smul_left (1 / 2 : ℝ)).exp_left).eq
    have hA₀ : E ∈ Morse.minVelO Js k (Js k) := ⟨⟨hEsk, fun _ => hEp, hEα⟩, hEE⟩
    obtain ⟨A, hA, heqA⟩ := hexmin hJ' hp hA₀ hmP
    have hAsk : Aᵀ = -A := by
      have := hA.1.1; rwa [conjTranspose_eq_transpose_of_trivial] at this
    refine ⟨A, ⟨orth_iff.2 (by rw [hAsk, Matrix.neg_mul, hA.2, neg_neg]), hA.2⟩,
      fun α h1 h2 => hA.1.2.2 α h1 (by omega), hA.1.2.1 hk0, fun t ht => ?_⟩
    rw [semiGeo_eq_omegaGeo]
    exact heqA ht

#rt_check RoundTrip.V15_25.A_to_B [Morse.neg_mem_omegaStratum, Morse.riemDist_omegaStratum,
  Morse.pi_sq_card_le_energy, Morse.omegaPath_mem_minPaths, Morse.exists_minVelO_of_mem_minPaths,
  Morse.omegaGeo_half]

end Main

/-! ## B ⇒ A, only vacuously: A re-proved outright (the project's proofs, copied) -/

section Outright
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem neg_mem' {J : ℕ → Mat ι} {k : ℕ} {p : Mat ι} (hJ : Morse.IsAnticommFamily J k) (hp : p ∈ Morse.Omega J k) {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ Morse.minVelO J k p) :
    -p ∈ Morse.omegaStratum J k p := by
  have := (Morse.isTotGeo_omegaStratum hJ p).mul_exp_mem p (Morse.self_mem_omegaStratum hp) _
    ((Morse.tanAlg J k p).smul_mem Real.pi hA₀.1)
  rwa [Morse.exp_pi_smul_of_minVelO hA₀, Matrix.mul_neg, Matrix.mul_one] at this

theorem riemDist' {J : ℕ → Mat ι} {k : ℕ} {p : Mat ι} (hJ : Morse.IsAnticommFamily J k) (hp : p ∈ Morse.Omega J k) {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ Morse.minVelO J k p) :
    Morse.riemDist (N := Morse.omegaStratum J k p) p (-p) =
      ENNReal.ofReal (Real.pi * Real.sqrt (Fintype.card ι)) := by
  set hN := Morse.isSliceSubmanifold_omegaStratum hJ p
  have hT := Morse.isTotGeo_omegaStratum hJ p
  have hpN := Morse.self_mem_omegaStratum hp
  have hpo := Morse.omega_orth hp
  have hγ := Morse.omegaGeo_mem_pathSpace hJ hp hA₀
  have hle : Morse.riemDist (N := Morse.omegaStratum J k p) p (-p) ≤
      ENNReal.ofReal (Real.pi * Real.sqrt (Fintype.card ι)) := by
    have h1 := Morse.riemDist_le_pathLength (N := Morse.omegaStratum J k p) hγ.1 hγ.2.1
    rw [hγ.2.2.1, hγ.2.2.2] at h1
    unfold Morse.omegaGeo at h1
    rw [Morse.IsTotGeo.pathLength_mul_exp_smul hpo
      ((Morse.tanAlg J k p).smul_mem Real.pi hA₀.1).1, Morse.norm_pi_smul_of_minVelO hA₀] at h1
    exact h1
  refine le_antisymm hle ?_
  have hne : Morse.riemDist (N := Morse.omegaStratum J k p) p (-p) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  obtain ⟨v, hv, hexpv, hρ, -⟩ := Morse.theorem_10_9 (hN := hN) (p := ⟨p, hpN⟩)
    (hT.isGeodesicallyComplete ⟨p, hpN⟩) (q := ⟨-p, neg_mem' hJ hp hA₀⟩) hne
  rw [hT.mem_tangentSubspace_iff] at hv
  have hv' : v = p * (pᴴ * v) := by
    rw [← Matrix.mul_assoc, Morse.mul_conjTranspose_eq_one hpo, Matrix.one_mul]
  have hexp : Morse.exp hN p v = p * NormedSpace.exp (pᴴ * v) := by
    conv_lhs => rw [hv']
    exact hT.exp_eq hpN hv
  change Morse.exp hN p v = -p at hexpv
  rw [hexp] at hexpv
  have hexpV : NormedSpace.exp (pᴴ * v) = -1 := by
    have := congrArg (pᴴ * ·) hexpv
    simpa only [← Matrix.mul_assoc, hpo, Matrix.one_mul, Matrix.mul_neg] using this
  have hnorm : ‖v‖ = ‖pᴴ * v‖ := by
    conv_lhs => rw [hv']
    exact (Morse.mulLeftIso p hpo).norm_map _
  change Morse.riemDist (N := Morse.omegaStratum J k p) p (-p) = ENNReal.ofReal ‖v‖ at hρ
  rw [hρ, hnorm]
  apply ENNReal.ofReal_le_ofReal
  have h2 := Morse.pi_sq_mul_card_le_norm_sq hv.1 hexpV
  have h3 : (Real.pi * Real.sqrt (Fintype.card ι)) ^ 2 ≤ ‖pᴴ * v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; exact h2
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h3

theorem pi_sq_card_le_energy' {J : ℕ → Mat ι} {k : ℕ} {p : Mat ι} (hJ : Morse.IsAnticommFamily J k) (hp : p ∈ Morse.Omega J k) {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ Morse.minVelO J k p) {γ : ℝ → Matrix ι ι ℝ}
    (hγ : γ ∈ Morse.pathSpace (Morse.omegaStratum J k p) p (-p)) :
    Real.pi ^ 2 * Fintype.card ι ≤ Morse.energy γ 0 1 := by
  have h1 := Morse.riemDist_le_pathLength (N := Morse.omegaStratum J k p) hγ.1 hγ.2.1
  rw [hγ.2.2.1, hγ.2.2.2, riemDist' hJ hp hA₀] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff hγ.1.isAdmissible.pathLength_nonneg).1 h1
  have h3 := Morse.pathLength_sq_le_energy hγ.1
  rw [sub_zero, one_mul] at h3
  calc Real.pi ^ 2 * Fintype.card ι = (Real.pi * Real.sqrt (Fintype.card ι)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    _ ≤ Morse.pathLength γ 0 1 ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    _ ≤ _ := h3

theorem omegaPath_mem_minPaths' {J : ℕ → Mat ι} {k : ℕ} {p : Mat ι} (hJ : Morse.IsAnticommFamily J k) (hp : p ∈ Morse.Omega J k) (A : Morse.minVelO J k p) :
    Morse.omegaPath hJ hp A ∈ Morse.minPaths (Morse.omegaStratum J k p) p (-p) := fun γ' => by
  change Morse.energy (Morse.omegaGeo p A) 0 1 ≤ _
  rw [Morse.energy_omegaGeo hp A.2]
  exact pi_sq_card_le_energy' hJ hp A.2 γ'.mem

theorem exists_minVelO_of_mem_minPaths' {J : ℕ → Mat ι} {k : ℕ} {p : Mat ι} (hJ : Morse.IsAnticommFamily J k) (hp : p ∈ Morse.Omega J k) {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ Morse.minVelO J k p)
    {γ : Morse.PathSp (Morse.omegaStratum J k p) p (-p)}
    (hγ : γ ∈ Morse.minPaths (Morse.omegaStratum J k p) p (-p)) :
    ∃ A ∈ Morse.minVelO J k p, EqOn γ (Morse.omegaGeo p A) (Icc 0 1) := by
  set hN := Morse.isSliceSubmanifold_omegaStratum hJ p
  have hT := Morse.isTotGeo_omegaStratum hJ p
  have hpo := Morse.omega_orth hp
  have hgeo := Morse.isUnbrokenGeodesic_of_minimal (hN := hN) γ.mem (fun γ' hγ' => hγ ⟨γ', hγ'⟩)
  obtain ⟨V, hV, heq⟩ := hT.eqOn_of_isUnbrokenGeodesic γ.mem hgeo
  have hexp : NormedSpace.exp V = -1 := by
    have h1 := heq ⟨zero_le_one, le_rfl⟩
    rw [γ.mem.2.2.2] at h1
    simp only [one_smul] at h1
    have := congrArg (pᴴ * ·) h1
    simpa only [← Matrix.mul_assoc, hpo, Matrix.one_mul, Matrix.mul_neg] using this.symm
  have hE := hγ (Morse.omegaPath hJ hp ⟨A₀, hA₀⟩)
  change Morse.energy γ 0 1 ≤ Morse.energy (Morse.omegaGeo p A₀) 0 1 at hE
  rw [Morse.energy_omegaGeo hp hA₀, Morse.energy_congr heq, Morse.IsTotGeo.energy_mul_exp_smul hpo hV.1] at hE
  have hsq := Morse.mul_self_eq_of_norm_sq_le hV.1 hexp hE
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ⟨Real.pi⁻¹ • V, ⟨(Morse.tanAlg J k p).smul_mem _ hV, ?_⟩, fun t ht => ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul, smul_smul]
    rw [show Real.pi⁻¹ * Real.pi⁻¹ * -(Real.pi ^ 2) = -1 by field_simp]
    simp
  · rw [heq ht]
    simp only [Morse.omegaGeo, smul_smul, mul_inv_cancel₀ hπ, one_smul]

theorem omegaGeo_half' {p A : Matrix ι ι ℝ} (hA : A * A = -1) : Morse.omegaGeo p A (1 / 2) = p * A := by
  simp only [Morse.omegaGeo, smul_smul]
  rw [Morse.exp_smul_of_mul_self_eq_neg_one hA, show 1 / 2 * Real.pi = Real.pi / 2 by ring,
    Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, zero_add, one_smul]

end Outright

/-- B ⇒ A, only vacuously: A is proved outright. B speaks only of the base point `J_k` with
`J_1, …, J_k` anticommuting (`k ≥ 1`, `ℝⁿ = Fin n`) and of blind length-minimal geodesics; A holds at
every `p ∈ Ω_k(n)` with `minVelO ≠ ∅` (including `k = 0`, `Ω_0 = O(n)`, which B does not cover), on
the project's stratum, path space and energy, and states the distance, the energy bound and the
least-energy characterization. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@fun ι _ _ J k p hJ hp A₀ hA₀ => neg_mem' hJ hp hA₀,
    @fun ι _ _ J k p hJ hp A₀ hA₀ => riemDist' hJ hp hA₀,
    @fun ι _ _ J k p hJ hp A₀ hA₀ γ hγ => pi_sq_card_le_energy' hJ hp hA₀ hγ,
    @fun ι _ _ J k p hJ hp A => omegaPath_mem_minPaths' hJ hp A,
    @fun ι _ _ J k p hJ hp A₀ hA₀ γ hγ => exists_minVelO_of_mem_minPaths' hJ hp hA₀ hγ,
    @fun ι _ _ p A hA => omegaGeo_half' hA⟩

#rt_check RoundTrip.V15_25.B_to_A [Morse.neg_mem_omegaStratum, Morse.riemDist_omegaStratum,
  Morse.pi_sq_card_le_energy, Morse.omegaPath_mem_minPaths, Morse.exists_minVelO_of_mem_minPaths,
  Morse.omegaGeo_half]
#rt_overlap RoundTrip.V15_25.B_to_A [Morse.neg_mem_omegaStratum, Morse.riemDist_omegaStratum,
  Morse.pi_sq_card_le_energy, Morse.omegaPath_mem_minPaths, Morse.exists_minVelO_of_mem_minPaths,
  Morse.omegaGeo_half]

end

end RoundTrip.V15_25
