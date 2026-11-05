import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_24

open Matrix Set Filter Topology Module
open scoped ContDiff

namespace RoundTrip.V15_24

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The project's statement (universes instantiated at `0`, any finite index type; no normal
form): for `V` skew with `exp V = −I`, every eigenvalue `λ` of `−V²` (`V²E = −λE`, `E ≠ 0`) is
`≥ π²`; hence `‖V‖² ≥ π²n` (Frobenius norm; `‖V‖` is the length of `t ↦ x exp(tV)`), with
equality only if `V² = −π²I`. -/
def A : Prop :=
  type_of% @Morse.pi_sq_le_of_sq_mul.{0} ∧ type_of% @Morse.pi_sq_mul_card_le_norm_sq.{0} ∧
    type_of% @Morse.mul_self_eq_of_norm_sq_le.{0}

theorem A_holds : A :=
  ⟨@Morse.pi_sq_le_of_sq_mul.{0}, @Morse.pi_sq_mul_card_le_norm_sq.{0},
    @Morse.mul_self_eq_of_norm_sq_le.{0}⟩

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
section Elem
open scoped Matrix.Norms.Elementwise
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem iteratedDerivWithin_two_eq (γ : ℝ → Mat ι) (s : Set ℝ) (t : ℝ) :
    iteratedDerivWithin 2 γ s t = derivWithin (derivWithin γ s) s t := by
  rw [iteratedDerivWithin_eq_iterate]; rfl

end Elem

/-! ## The distance from `I` to `−I` in `O(n)`, from A's bound (Hopf–Rinow: the project's proof of
`Morse.riemDist_omegaStratum`, run with A's `pi_sq_mul_card_le_norm_sq`) -/

section Dist
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem riemDist_of_hyp (hpi : type_of% @Morse.pi_sq_mul_card_le_norm_sq.{0})
    {J : ℕ → Mat ι} {k : ℕ} {p : Mat ι} (hJ : Morse.IsAnticommFamily J k) (hp : p ∈ Morse.Omega J k)
    {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ Morse.minVelO J k p) :
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
    (hT.isGeodesicallyComplete ⟨p, hpN⟩) (q := ⟨-p, Morse.neg_mem_omegaStratum hJ hp hA₀⟩) hne
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
  have h2 := hpi hv.1 hexpV
  have h3 : (Real.pi * Real.sqrt (Fintype.card ι)) ^ 2 ≤ ‖pᴴ * v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; exact h2
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h3

end Dist

/-! ## Block-diagonal computations (the normal form) -/

section Block
variable {m : ℕ}

theorem sig2_sq : sig2 * sig2 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sig2]

theorem sig2_T : sig2ᵀ = -sig2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sig2]

theorem trace_smul_sig2 (c : ℝ) : trace ((c • sig2) * (c • sig2)ᵀ) = 2 * c ^ 2 := by
  rw [transpose_smul, sig2_T, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_neg, sig2_sq, neg_neg,
    smul_smul, trace_smul, trace_one]
  simp; ring

theorem exp_blk (a : Fin m → ℝ) (θ : ℝ) :
    mexp (θ • blk (fun j => a j • sig2)) =
      blk (fun j => Real.cos (θ * a j) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin (θ * a j) • sig2) := by
  rw [blk, blk, ← blockDiagonal_smul, mexp, Matrix.exp_blockDiagonal]
  congr 1
  funext j
  have hpi : NormedSpace.exp (θ • fun j => a j • sig2) j =
      NormedSpace.exp ((θ • fun j => a j • sig2) j) := by
    open scoped Matrix.Norms.Operator in
      exact Pi.coe_exp (𝔸 := fun _ : Fin m => Matrix (Fin 2) (Fin 2) ℝ) _ j
  rw [hpi, Pi.smul_apply, smul_smul, Morse.exp_smul_of_mul_self_eq_neg_one sig2_sq]

theorem blk_eq_neg_one_iff (b : Fin m → Matrix (Fin 2) (Fin 2) ℝ) :
    blk b = -1 ↔ ∀ j, b j = -1 := by
  have h1 : (-1 : Mat (Fin 2 × Fin m)) = blk (fun _ => -1) := by
    rw [blk, show (fun _ : Fin m => (-1 : Matrix (Fin 2) (Fin 2) ℝ)) = -1 from rfl,
      blockDiagonal_neg, blockDiagonal_one]
  rw [h1]
  constructor
  · intro h j
    have := blockDiagonal_injective h
    exact congrFun this j
  · intro h
    congr 1
    funext j
    exact h j

theorem rot_eq_neg_one_iff (θ : ℝ) :
    Real.cos θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin θ • sig2 = -1 ↔ Real.cos θ = -1 := by
  constructor
  · intro h
    have := congrFun (congrFun h 0) 0
    simpa [sig2] using this
  · intro h
    have hs : Real.sin θ = 0 := by
      have := Real.sin_sq_add_cos_sq θ
      rw [h] at this
      nlinarith [sq_nonneg (Real.sin θ)]
    rw [h, hs]
    ext i j; fin_cases i <;> fin_cases j <;> simp [sig2]

theorem cos_pi_mul_eq_neg_one_iff (a : ℝ) :
    Real.cos (Real.pi * a) = -1 ↔ ∃ z : ℤ, Odd z ∧ a = z := by
  rw [Real.cos_eq_neg_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨2 * k + 1, odd_two_mul_add_one k, ?_⟩
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have : Real.pi * a = Real.pi * (2 * k + 1) := by rw [← hk]; ring
    have := mul_left_cancel₀ hπ this
    rw [this]; push_cast; ring
  · rintro ⟨z, ⟨k, rfl⟩, ha⟩
    refine ⟨k, ?_⟩
    rw [ha]; push_cast; ring

theorem odd_one_le {a : ℝ} (ha : 0 ≤ a) (h : ∃ z : ℤ, Odd z ∧ a = z) : 1 ≤ a := by
  obtain ⟨z, ⟨k, rfl⟩, rfl⟩ := h
  push_cast at ha ⊢
  rcases le_or_gt 0 k with hk | hk
  · have : (0 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  · have h1 : k ≤ -1 := by omega
    have : (k : ℝ) ≤ -1 := by exact_mod_cast h1
    linarith

end Block

/-! ## Conjugation by `P` -/

section Conj
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_conj {A P D : Mat ι} (hP : P ∈ Orth ι) (h : Pᵀ * A * P = D) : A = P * D * Pᵀ := by
  have h1 : Pᵀ * P = 1 := orth_iff.1 hP
  have h2 : P * Pᵀ = 1 := orth_iff'.1 hP
  rw [← h]
  simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem exp_conjP {P : Mat ι} (hP : P ∈ Orth ι) (D : Mat ι) (θ : ℝ) :
    mexp (θ • (P * D * Pᵀ)) = P * mexp (θ • D) * Pᵀ := by
  have h2 : P * Pᵀ = 1 := orth_iff'.1 hP
  have hg : (Pᵀ)ᴴ * Pᵀ = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]; exact h2
  have := Morse.exp_conj_orth hg (θ • D)
  rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at this
  rw [mexp, mexp, ← this, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_eq_neg_one_iff {P X : Mat ι} (hP : P ∈ Orth ι) : P * X * Pᵀ = -1 ↔ X = -1 := by
  have h1 : Pᵀ * P = 1 := orth_iff.1 hP
  have h2 : P * Pᵀ = 1 := orth_iff'.1 hP
  constructor
  · intro h
    have := congrArg (fun M => Pᵀ * M * P) h
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul] at this
    rwa [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
      h1] at this
  · rintro rfl
    rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, h2]

theorem frob_conj {P X : Mat ι} (hP : P ∈ Orth ι) : frob (P * X * Pᵀ) (P * X * Pᵀ) = frob X X := by
  have h1 : Pᵀ * P = 1 := orth_iff.1 hP
  have e : (P * X * Pᵀ) * (P * X * Pᵀ)ᵀ = P * (X * Xᵀ) * Pᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᵀ P, h1, Matrix.one_mul]
  unfold frob
  rw [e, trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem orth_exp_skew {X : Mat ι} (hX : Xᵀ = -X) (θ : ℝ) : mexp (θ • X) ∈ Orth ι := by
  rw [orth_iff, ← conjTranspose_eq_transpose_of_trivial]
  exact Morse.exp_conjTranspose_mul_exp_of_skew
    (by rw [conjTranspose_smul, star_trivial, conjTranspose_eq_transpose_of_trivial, hX, smul_neg])

/-- The path `t ↦ exp(πtX)`. -/
def expPath (X : Mat ι) : ℝ → Mat ι := fun t => mexp ((Real.pi * t) • X)

theorem expPath_eq (X : Mat ι) :
    expPath X = fun t => (1 : Mat ι) * NormedSpace.exp (t • (Real.pi • X)) := by
  funext t; simp only [expPath, mexp, Matrix.one_mul, smul_smul, mul_comm]

theorem lenM_expPath {X : Mat ι} (hX : Xᵀ = -X) : lenM (expPath X) = Real.pi * ‖X‖ := by
  have hsk : (Real.pi • X)ᴴ = -(Real.pi • X) := by
    rw [conjTranspose_smul, star_trivial, conjTranspose_eq_transpose_of_trivial, hX, smul_neg]
  rw [lenM_eq, expPath_eq, Morse.IsTotGeo.pathLength_mul_exp_smul (by simp) hsk, norm_smul,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

theorem contDiff_expPath (X : Mat ι) : ContDiff ℝ ∞ (expPath X) := by
  rw [expPath_eq]; exact contDiff_const.mul (Morse.contDiff_exp_smul _)

theorem isPathIn_expPath {X : Mat ι} (hX : Xᵀ = -X) : IsPathIn (Orth ι) (expPath X) :=
  isPathIn_of_mem_pathSpace (p := expPath X 0) (q := expPath X 1)
    ⟨Morse.IsPiecewiseSmooth.of_contDiff (contDiff_expPath X) zero_le_one,
      fun t _ => orth_exp_skew hX _, rfl, rfl⟩

/-- A lower bound for the blind lengths from the project's Riemannian distance. -/
theorem le_lenM_of_riemDist {N : Set (Mat ι)} {p q : Mat ι} {L : ℝ}
    (hd : Morse.riemDist (N := N) p q = ENNReal.ofReal L) {w : ℝ → Mat ι} (hw : IsPathIn N w)
    (h0 : w 0 = p) (h1 : w 1 = q) : L ≤ lenM w := by
  have hps := isPiecewiseSmooth_of_isPWOn hw.1
  have h := Morse.riemDist_le_pathLength (N := N) hps hw.2
  rw [h0, h1, hd] at h
  rw [lenM_eq]
  exact (ENNReal.ofReal_le_ofReal_iff hps.isAdmissible.pathLength_nonneg).1 h

end Conj

section Geo
open scoped Matrix.Norms.Elementwise
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem iteratedDerivWithin_two_expPath (X : Mat ι) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin 2 (expPath X) (Icc 0 1) t = deriv (deriv (expPath X)) t := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one)
    ((contDiff_elem_of_frob (contDiff_expPath X)).contDiffAt.of_le (WithTop.coe_le_coe.2 le_top)) ht,
    iteratedDeriv_succ, iteratedDeriv_one]
  rfl

end Geo

section Geo2
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `t ↦ exp(πtX)`, `X` skew, is a geodesic of `O(n)` (acceleration `γ(πX)²`, `(πX)²` symmetric). -/
theorem isGeodOn_expPath {X : Mat ι} (hX : Xᵀ = -X) : IsGeodOn (Orth ι) (expPath X) 0 1 := by
  refine ⟨zero_lt_one, contDiffOn_elem_of_frob (contDiff_expPath X).contDiffOn,
    fun t _ => orth_exp_skew hX _, fun t ht v hv => ?_⟩
  rw [iteratedDerivWithin_two_expPath X ht]
  have hexp : NormedSpace.exp (t • Real.pi • X) = expPath X t := by
    simp only [expPath, mexp, smul_smul, mul_comm]
  rw [expPath_eq, Morse.deriv_deriv_mul_exp_smul, Matrix.one_mul, hexp]
  have hγ : expPath X t ∈ Orth ι := orth_exp_skew hX _
  have hS := skew_of_mem_tanSet_orth hv
  have hγo' : expPath X t * (expPath X t)ᵀ = 1 := orth_iff'.1 hγ
  have hv' : v = expPath X t * ((expPath X t)ᵀ * v) := by
    rw [← Matrix.mul_assoc, hγo', Matrix.one_mul]
  have hγo : (expPath X t)ᴴ * expPath X t = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial]; exact orth_iff.1 hγ
  rw [frob_eq_inner, hv', Matrix.mul_assoc, Morse.inner_mul_left_of_unitary hγo]
  have hsym : ((Real.pi • X) * (Real.pi • X))ᵀ = (Real.pi • X) * (Real.pi • X) := by
    rw [transpose_mul, transpose_smul, hX, smul_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  exact inner_sym_skew hsym hS

end Geo2

/-! ## A ⇒ B -/

section Main
open scoped Morse.MatrixInner RealInnerProductSpace

/-- A ⇒ B. With `A = P·diag(a_jσ)·Pᵀ`: `exp(πA) = P·diag(cos(πa_j) + sin(πa_j)σ)·Pᵀ`, which is `−I`
iff every `cos(πa_j) = −1`, i.e. every `a_j` is an odd integer; `⟨A, A⟩ = tr(diag(a_jσ)diag(a_jσ)ᵀ)
= 2Σa_j²`; if all `a_j = 1` then `A² = P·diag(σ²)·Pᵀ = −I` (pure computation, not in A).
Minimality of `t ↦ exp(πtA)` (a geodesic of `O(n)`: its acceleration `γ(πA)²` is normal), whose
length is `π‖A‖ = π(2Σa_j²)^{1/2}`: if it is minimal, comparing with `t ↦ exp(πtA₁)`,
`A₁ = P·diag(σ)·Pᵀ` (length `π√(2m)`), gives `Σa_j² ≤ m` with all `a_j ≥ 1` odd, so all `a_j = 1`
(again not using A); conversely, if all `a_j = 1`, every path from `I` to `−I` in `O(2m)` has length
`≥ π√(2m)` — the distance `π√n` from `I` to `−I`, obtained by Hopf–Rinow (the project's argument
for `Morse.riemDist_omegaStratum` at `k = 0`) from **A's** bound `‖V‖² ≥ π²n` for the minimal
geodesic `t ↦ exp(tV)`, `exp V = −I`. -/
theorem A_to_B : A → B := by
  rintro ⟨-, hpi, -⟩ m A P a hP ha hPAP
  set D := blk (fun j => a j • sig2) with hD
  have hA : A = P * D * Pᵀ := eq_conj hP hPAP
  have hPP : Pᵀ * P = 1 := orth_iff.1 hP
  have skew_of : ∀ b : Fin m → ℝ, (P * blk (fun j => b j • sig2) * Pᵀ)ᵀ =
      -(P * blk (fun j => b j • sig2) * Pᵀ) := fun b => by
    have hBT : (blk (fun j => b j • sig2))ᵀ = -blk (fun j => b j • sig2) := by
      unfold blk
      rw [blockDiagonal_transpose, ← blockDiagonal_neg]
      congr 1; funext j
      simp [transpose_smul, sig2_T]
    rw [transpose_mul, transpose_mul, transpose_transpose, hBT]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hAT : Aᵀ = -A := by rw [hA]; exact skew_of a
  have key1 : ∀ (b : Fin m → ℝ),
      (mexp (Real.pi • (P * blk (fun j => b j • sig2) * Pᵀ)) = -1 ↔
        ∀ j, ∃ z : ℤ, Odd z ∧ b j = z) := by
    intro b
    rw [exp_conjP hP, conj_eq_neg_one_iff hP, exp_blk, blk_eq_neg_one_iff]
    exact forall_congr' fun j => (rot_eq_neg_one_iff _).trans (cos_pi_mul_eq_neg_one_iff _)
  have key2 : ∀ (b : Fin m → ℝ),
      frob (P * blk (fun j => b j • sig2) * Pᵀ) (P * blk (fun j => b j • sig2) * Pᵀ) =
        2 * ∑ j, b j ^ 2 := by
    intro b
    rw [frob_conj hP]
    unfold frob blk
    rw [blockDiagonal_transpose]; rw [← blockDiagonal_mul]; rw [trace_blockDiagonal]
    simp only [trace_smul_sig2, Finset.mul_sum]
  have key4 : (∀ j, a j = 1) → A * A = -1 := by
    intro h1
    have hDD : D * D = -1 := by
      rw [hD]; unfold blk; rw [← blockDiagonal_mul]
      have : (fun j => (a j • sig2) * (a j • sig2)) = (-1 : Fin m → Matrix (Fin 2) (Fin 2) ℝ) := by
        funext j; rw [h1 j, one_smul, sig2_sq]; rfl
      rw [this, blockDiagonal_neg, blockDiagonal_one]
    rw [hA, show P * D * Pᵀ * (P * D * Pᵀ) = P * (D * D) * Pᵀ by
      simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc Pᵀ P, hPP, Matrix.one_mul], hDD]
    exact (conj_eq_neg_one_iff hP).2 rfl
  refine ⟨by rw [hA]; exact key1 a, by rw [hA]; exact key2 a, fun hexp => ?_, key4⟩
  have hodd := (key1 a).1 (by rw [← hA]; exact hexp)
  change IsMinGeodIn _ (expPath A) ↔ _
  have hlen : lenM (expPath A) = Real.pi * ‖A‖ := lenM_expPath hAT
  have hn2 : ‖A‖ ^ 2 = 2 * ∑ j, a j ^ 2 := by rw [← frob_self_eq, hA, key2 a]
  have h0 : expPath A 0 = 1 := by simp [expPath]
  have h1 : expPath A 1 = -1 := by simp only [expPath, mul_one]; exact hexp
  constructor
  · rintro ⟨-, hmin⟩
    set A₁ := P * blk (fun j => (fun _ => (1 : ℝ)) j • sig2) * Pᵀ with hA₁
    have hA₁T : A₁ᵀ = -A₁ := skew_of _
    have hexp1 : mexp (Real.pi • A₁) = -1 :=
      (key1 (fun _ => 1)).2 (fun j => ⟨1, odd_one, by simp⟩)
    have hle := hmin (expPath A₁) (isPathIn_expPath hA₁T) (by rw [h0]; simp [expPath])
      (by rw [h1]; simp only [expPath, mul_one]; exact hexp1)
    rw [hlen, lenM_expPath hA₁T] at hle
    have hle1 : ‖A‖ ≤ ‖A₁‖ := le_of_mul_le_mul_left hle Real.pi_pos
    have hle2 : ‖A‖ ^ 2 ≤ ‖A₁‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle1 2
    rw [hn2, ← frob_self_eq, hA₁, key2] at hle2
    have hge : ∀ j, 1 ≤ a j := fun j => odd_one_le (ha j) (hodd j)
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ a i ^ 2 - 1 := fun i _ => by
      nlinarith [hge i]
    have hsum : ∑ i, (a i ^ 2 - 1) ≤ 0 := by
      rw [Finset.sum_sub_distrib]; simp only [one_pow, Finset.sum_const] at hle2 ⊢; linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hsum (Finset.sum_nonneg hnn))
    intro j
    have := hz j (Finset.mem_univ _)
    nlinarith [hge j]
  · intro hall
    refine ⟨isGeodOn_expPath hAT, fun w hw hw0 hw1 => ?_⟩
    have hA2 : A * A = -1 := key4 hall
    have hJ0 : Morse.IsAnticommFamily (fun _ => (0 : Mat (Fin 2 × Fin m))) 0 :=
      ⟨fun α h1 h2 => absurd h2 (by omega), fun α _ h1 h2 _ _ _ => absurd h2 (by omega)⟩
    have hp1 : (1 : Mat (Fin 2 × Fin m)) ∈ Morse.Omega (fun _ => (0 : Mat (Fin 2 × Fin m))) 0 :=
      (Matrix.orthogonalGroup (Fin 2 × Fin m) ℝ).one_mem
    have hA0 : A ∈ Morse.minVelO (fun _ => (0 : Mat (Fin 2 × Fin m))) 0 1 :=
      ⟨⟨by rw [conjTranspose_eq_transpose_of_trivial]; exact hAT, fun h => absurd rfl h,
        fun α h1 h2 => absurd h2 (by omega)⟩, hA2⟩
    have hd := riemDist_of_hyp hpi hJ0 hp1 hA0
    rw [Morse.omegaStratum_zero] at hd
    have hlow := le_lenM_of_riemDist hd hw (by rw [hw0, h0]) (by rw [hw1, h1])
    have hcard : (Fintype.card (Fin 2 × Fin m) : ℝ) = ‖A‖ ^ 2 := by
      rw [hn2]; simp [hall, Fintype.card_prod]
    rw [hlen]
    rwa [hcard, Real.sqrt_sq (norm_nonneg _)] at hlow

#rt_check RoundTrip.V15_24.A_to_B [Morse.pi_sq_le_of_sq_mul, Morse.pi_sq_mul_card_le_norm_sq,
  Morse.mul_self_eq_of_norm_sq_le]

end Main

/-! ## B ⇒ A, only vacuously: A re-proved outright (the project's proofs, copied) -/

section Outright
open scoped Morse.MatrixInner RealInnerProductSpace
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem pi_sq_le_of_sq_mul' {V E : Matrix ι ι ℝ} (hV : Vᴴ = -V)
    (hexp : NormedSpace.exp V = -1) (hE : E ≠ 0) {l : ℝ} (hl : V * (V * E) = -l • E) :
    Real.pi ^ 2 ≤ l := by
  have hEpos : 0 < ‖E‖ := norm_pos_iff.2 hE
  have hnorm : ‖V * E‖ ^ 2 = l * ‖E‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, Morse.inner_mul_left_adj, hV, Matrix.neg_mul, hl,
      inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hl0 : 0 ≤ l := by
    by_contra h
    push Not at h
    have : l * ‖E‖ ^ 2 < 0 := mul_neg_of_neg_of_pos h (by positivity)
    linarith [sq_nonneg ‖V * E‖]
  rcases eq_or_lt_of_le hl0 with hl0 | hlpos
  · exfalso
    have hVE : V * E = 0 := by
      rw [← hl0, zero_mul] at hnorm
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hnorm)
    have := Morse.eq_exp_smul_mul_of_hasDerivAt (V := V) (c := fun _ => E)
      (fun t => by rw [hVE]; exact hasDerivAt_const t E) 1
    rw [one_smul, hexp, Matrix.neg_mul, Matrix.one_mul] at this
    exact hE (by
      have h2 : (2 : ℝ) • E = 0 := by rw [two_smul]; nth_rewrite 1 [this]; exact neg_add_cancel E
      exact (smul_eq_zero.1 h2).resolve_left two_ne_zero)
  · set μ := Real.sqrt l with hμ
    have hμpos : 0 < μ := Real.sqrt_pos.2 hlpos
    have hμsq : μ * μ = l := Real.mul_self_sqrt hl0
    set c : ℝ → Matrix ι ι ℝ := fun t =>
      Real.cos (μ * t) • E + (Real.sin (μ * t) / μ) • (V * E) with hcdef
    have hc : ∀ t, HasDerivAt c (V * c t) t := fun t => by
      have h1 : HasDerivAt (fun t => Real.cos (μ * t)) (-Real.sin (μ * t) * μ) t := by
        have := ((hasDerivAt_id t).const_mul μ).cos
        refine this.congr_deriv ?_
        simp only [id, mul_one]
      have h2 : HasDerivAt (fun t => Real.sin (μ * t) / μ) (Real.cos (μ * t)) t := by
        have := (((hasDerivAt_id t).const_mul μ).sin).div_const μ
        refine this.congr_deriv ?_
        simp only [id, mul_one]
        field_simp
      refine ((h1.smul_const E).add (h2.smul_const (V * E))).congr_deriv ?_
      simp only [hcdef, Matrix.mul_add, Matrix.mul_smul, hl]
      rw [smul_smul, ← hμsq]
      field_simp
      module
    have h1 := Morse.eq_exp_smul_mul_of_hasDerivAt hc 1
    simp only [hcdef, one_smul, mul_one, mul_zero, Real.cos_zero, Real.sin_zero, zero_div,
      zero_smul, add_zero, hexp, Matrix.neg_mul, Matrix.one_mul] at h1
    have h2 := congrArg (fun M => ⟪E, M⟫) h1
    simp only [inner_add_right, real_inner_smul_right, Morse.inner_self_mul_skew hV,
      inner_neg_right, real_inner_self_eq_norm_sq, mul_zero, add_zero] at h2
    have hcos : Real.cos μ = -1 := by
      have hE2 : ‖E‖ ^ 2 ≠ 0 := by positivity
      field_simp at h2
      linarith
    have hμπ : Real.pi ≤ μ := by
      by_contra h
      push Not at h
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hμpos.le le_rfl h
      rw [Real.cos_pi] at this
      linarith
    calc Real.pi ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ Real.pi_pos.le hμπ 2
      _ = l := by rw [sq, hμsq]

theorem exists_eigen_ge' {V : Matrix ι ι ℝ} (hV : Vᴴ = -V) (hexp : NormedSpace.exp V = -1) :
    ∃ (U : Matrix ι ι ℝ) (l : ι → ℝ), Uᴴ * U = 1 ∧ Vᴴ * V = U * Matrix.diagonal l * Uᴴ ∧
      ∀ i, Real.pi ^ 2 ≤ l i := by
  set S := Vᴴ * V with hSdef
  have hS : S.IsHermitian := by
    rw [IsHermitian, hSdef, conjTranspose_mul, conjTranspose_conjTranspose]
  have hspec := hS.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at hspec
  set U : Matrix ι ι ℝ := (hS.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hU : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  set l := hS.eigenvalues
  have hD : Matrix.diagonal (RCLike.ofReal ∘ l) = Matrix.diagonal l := by
    congr 1
  rw [hD] at hspec
  refine ⟨U, l, hU, hspec, fun i => ?_⟩
  set E := U * single i i (1 : ℝ)
  have hE : E ≠ 0 := by
    intro h0
    have : Uᴴ * E = single i i (1 : ℝ) := by
      simp only [E, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [h0, Matrix.mul_zero] at this
    have h1 := congrFun (congrFun this i) i
    simp at h1
  have hDs : Matrix.diagonal l * single i i (1 : ℝ) = l i • single i i (1 : ℝ) := by
    ext a b
    simp only [diagonal_mul, Matrix.smul_apply, single_apply, smul_eq_mul]
    split_ifs with h1
    · rw [← h1.1]
    · rw [mul_zero, mul_zero]
  have hSE : S * E = l i • E := by
    calc S * E = U * Matrix.diagonal l * (Uᴴ * U) * single i i (1 : ℝ) := by
          rw [hspec, show E = U * single i i (1 : ℝ) from rfl]
          simp only [Matrix.mul_assoc]
      _ = l i • E := by
          rw [hU, Matrix.mul_one, Matrix.mul_assoc, hDs, Matrix.mul_smul]
  have hVV : V * (V * E) = -l i • E := by
    rw [← Matrix.mul_assoc, neg_smul, ← hSE, hSdef, hV, Matrix.neg_mul, Matrix.neg_mul, neg_neg]
  exact pi_sq_le_of_sq_mul' hV hexp hE hVV

theorem pi_sq_mul_card_le_norm_sq' {V : Matrix ι ι ℝ} (hV : Vᴴ = -V)
    (hexp : NormedSpace.exp V = -1) : Real.pi ^ 2 * Fintype.card ι ≤ ‖V‖ ^ 2 := by
  obtain ⟨U, l, hU, hspec, hl⟩ := exists_eigen_ge' hV hexp
  rw [Morse.norm_sq_eq_trace, hspec, trace_mul_cycle, hU, Matrix.one_mul, trace_diagonal]
  calc Real.pi ^ 2 * Fintype.card ι = ∑ _i : ι, Real.pi ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i, l i := Finset.sum_le_sum fun i _ => hl i

theorem mul_self_eq_of_norm_sq_le' {V : Matrix ι ι ℝ} (hV : Vᴴ = -V)
    (hexp : NormedSpace.exp V = -1) (hle : ‖V‖ ^ 2 ≤ Real.pi ^ 2 * Fintype.card ι) :
    V * V = -(Real.pi ^ 2) • (1 : Matrix ι ι ℝ) := by
  obtain ⟨U, l, hU, hspec, hl⟩ := exists_eigen_ge' hV hexp
  rw [Morse.norm_sq_eq_trace, hspec, trace_mul_cycle, hU, Matrix.one_mul, trace_diagonal] at hle
  have hsum : ∑ i, (l i - Real.pi ^ 2) ≤ 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hl i))).1
    (le_antisymm hsum (Finset.sum_nonneg fun i _ => sub_nonneg.2 (hl i)))
  have hlc : l = fun _ => Real.pi ^ 2 := funext fun i => by
    have := hzero i (Finset.mem_univ i); linarith
  have hS : Vᴴ * V = Real.pi ^ 2 • (1 : Matrix ι ι ℝ) := by
    rw [hspec, hlc, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Morse.mul_conjTranspose_eq_one hU]
  rw [hV, Matrix.neg_mul] at hS
  rw [← neg_neg (V * V), hS, neg_smul]

end Outright

/-- B ⇒ A, only vacuously: A is proved outright. B is about matrices given in the real normal form
`PᵀAP = diag(a_jσ)`; A's statements hold for every skew `V` with `exp V = −I` on any finite index
type, and deriving them from B would need the normal form theorem for skew matrices (absent from
the project and from Mathlib; cf. `Items/V15_2.lean`), as well as a description of the eigenvalues
of `−V²` (A's `pi_sq_le_of_sq_mul`), which B does not mention. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@fun ι _ _ V E hV hexp hE l hl => pi_sq_le_of_sq_mul' hV hexp hE hl,
    @fun ι _ _ V hV hexp => pi_sq_mul_card_le_norm_sq' hV hexp,
    @fun ι _ _ V hV hexp hle => mul_self_eq_of_norm_sq_le' hV hexp hle⟩

#rt_check RoundTrip.V15_24.B_to_A [Morse.pi_sq_le_of_sq_mul, Morse.pi_sq_mul_card_le_norm_sq,
  Morse.mul_self_eq_of_norm_sq_le]
#rt_overlap RoundTrip.V15_24.B_to_A [Morse.pi_sq_le_of_sq_mul, Morse.pi_sq_mul_card_le_norm_sq,
  Morse.mul_self_eq_of_norm_sq_le]

end

end RoundTrip.V15_24
