import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_15

open Matrix Set
open scoped ContDiff

namespace RoundTrip.V14_15

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The project's statement (universes of `ι` instantiated at `0`), on the embedded `SU(n) ⊆ Mₙ(ℂ)`
(Frobenius norm, induced metric): the length of `t ↦ exp tA`, `0 ≤ t ≤ 1`, is `‖A‖` for skew-Hermitian `A`
(any `n`); `‖T suDiag(k) Tᴴ‖² = π² Σ k_j²`; `π√n ≤ ‖A‖` for `A ∈ 𝔰𝔲(n)` with `exp A = −I`; the Riemannian
distance from `I` to `−I` in `SU(2m)` is `π√(2m)`; `(T suDiag(k) Tᴴ)² = −π²I` iff all `k_j = ±1`; and
`t ↦ exp tA` (`A ∈ 𝔰𝔲(2m)`, `exp A = −I`) is a minimal geodesic of `SU(2m)` iff `A² = −π²I`. -/
def A : Prop :=
  type_of% @Morse.pathLength_exp_smul.{0} ∧ type_of% @Morse.norm_conj_suDiag_sq.{0} ∧
    type_of% @Morse.pi_sqrt_card_le_norm.{0} ∧ type_of% @Morse.riemDist_one_neg_one.{0} ∧
    type_of% @Morse.sq_conj_suDiag_iff.{0} ∧ type_of% @Morse.isMinimalGeodesic_exp_iff.{0}

theorem A_holds : A :=
  ⟨@Morse.pathLength_exp_smul, @Morse.norm_conj_suDiag_sq, @Morse.pi_sqrt_card_le_norm,
    @Morse.riemDist_one_neg_one, @Morse.sq_conj_suDiag_iff, @Morse.isMinimalGeodesic_exp_iff⟩

/-! ## Dictionary (copied from `Items/V14_16.lean`): the blind matrix-level lengths (entrywise norm,
`Re tr(AB*)`) and the project's (Frobenius norm) -/

namespace Dict

variable {n : ℕ}

section
open scoped Matrix.Norms.Elementwise

/-- The two normed structures have the same topology: `id` is a continuous linear map either way. -/
theorem contDiffOn_frob_of_elem {c : ℝ → Mat n} {s : Set ℝ} (hc : ContDiffOn ℝ ∞ c s) :
    @ContDiffOn ℝ _ ℝ _ _ (Mat n) Morse.MatrixInner.normedAddCommGroup
      Morse.MatrixInner.normedSpace ∞ c s :=
  @ContDiff.comp_contDiffOn ℝ ℝ (Mat n) (Mat n) _ _ _ _ _ Morse.MatrixInner.normedAddCommGroup
    Morse.MatrixInner.normedSpace ∞ s _ c
  (@ContinuousLinearMap.contDiff ℝ (Mat n) (Mat n) _ _ _
    Morse.MatrixInner.normedAddCommGroup Morse.MatrixInner.normedSpace ∞
    (ContinuousLinearMap.id ℝ (Mat n))) hc

theorem contDiffOn_elem_of_frob {c : ℝ → Mat n} {s : Set ℝ}
    (hc : @ContDiffOn ℝ _ ℝ _ _ (Mat n) Morse.MatrixInner.normedAddCommGroup
      Morse.MatrixInner.normedSpace ∞ c s) : ContDiffOn ℝ ∞ c s :=
  @ContDiff.comp_contDiffOn ℝ ℝ (Mat n) (Mat n) _ _ _ Morse.MatrixInner.normedAddCommGroup
    Morse.MatrixInner.normedSpace _ _ ∞ s _ c
  (@ContinuousLinearMap.contDiff ℝ (Mat n) (Mat n) _ Morse.MatrixInner.normedAddCommGroup
    Morse.MatrixInner.normedSpace _ _ ∞
    (ContinuousLinearMap.id ℝ (Mat n))) hc

end

section
open scoped Morse.MatrixInner

theorem normM_eq (X : Mat n) : normM X = ‖X‖ := by
  rw [normM, ipM, ← Real.sqrt_sq (norm_nonneg X), ← real_inner_self_eq_norm_sq, Morse.inner_def,
    Matrix.trace_mul_comm]
  rfl

theorem arcLenM_eq (c : ℝ → Mat n) (a b : ℝ) : arcLenM c a b = Morse.pathLength c a b := by
  unfold arcLenM Morse.pathLength
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact normM_eq _

theorem le_of_strictSeq {t : ℕ → ℝ} {k : ℕ} (ht : ∀ i < k, t i < t (i + 1)) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ k) : t i ≤ t j := by
  induction j with
  | zero => rw [Nat.le_zero.1 hij]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (Nat.lt_succ_iff.1 h) (by omega)).trans (ht j (by omega)).le
    · rw [le_antisymm hij h]

/-- A blind piecewise smooth path in `G` is a project piecewise smooth path with values in `G`. -/
theorem isPiecewiseSmooth_of_isPWIn {G : Set (Mat n)} {c : ℝ → Mat n} {a b : ℝ}
    (h : IsPWIn G c a b) : Morse.IsPiecewiseSmooth c a b ∧ ∀ t ∈ Icc a b, c t ∈ G := by
  obtain ⟨hG, k, t, h0, hk, hlt, hsm⟩ := h
  have hsm' : ∀ i < k, ContDiffOn ℝ ∞ c (Icc (t i) (t (i + 1))) :=
    fun i hi => contDiffOn_frob_of_elem (hsm i hi)
  have hab : a ≤ b := h0 ▸ hk ▸ le_of_strictSeq hlt (Nat.zero_le k) le_rfl
  refine ⟨⟨hab, ?_, (Finset.range (k + 1)).image t, ?_⟩, hG⟩
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

/-- A project piecewise smooth path with values in `G` is a blind piecewise smooth path in `G`. -/
theorem isPWIn_of_isPiecewiseSmooth {G : Set (Mat n)} {c : ℝ → Mat n} {a b : ℝ}
    (hc : Morse.IsPiecewiseSmooth c a b) (hcG : ∀ t ∈ Icc a b, c t ∈ G) : IsPWIn G c a b := by
  obtain ⟨hab, -, B, hB⟩ := hc
  refine ⟨hcG, ?_⟩
  suffices hsub : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = a ∧ t k = b ∧ (∀ i < k, t i < t (i + 1)) ∧
      ∀ i < k, a ≤ t i ∧ t (i + 1) ≤ b ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) by
    obtain ⟨k, t, h0, hk, hlt, hgood⟩ := hsub
    refine ⟨k, t, h0, hk, hlt, fun i hi => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hgood i hi
    exact contDiffOn_elem_of_frob (hB _ _ h1 (hlt i hi) h2 h3)
  rcases eq_or_lt_of_le hab with rfl | hlt
  · exact ⟨0, fun _ => a, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  classical
  set S : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b)))
  have hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hbS : b ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨a, haS, b, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else b
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

theorem isPWIn_iff {G : Set (Mat n)} {c : ℝ → Mat n} {a b : ℝ} :
    IsPWIn G c a b ↔ Morse.IsPiecewiseSmooth c a b ∧ ∀ t ∈ Icc a b, c t ∈ G :=
  ⟨isPiecewiseSmooth_of_isPWIn, fun h => isPWIn_of_isPiecewiseSmooth h.1 h.2⟩

variable [NeZero n]

/-- **Dictionary: minimality.** For `A ∈ 𝔰𝔲(n)`, the blind minimality of `t ↦ exp tA` in `SU(n)` (matrix
level) is the project's `IsMinimalGeodesic`. -/
theorem isMinimalIn_iff {A : Mat n} (hA : A ∈ Morse.specialSkewHermitian (Fin n)) :
    IsMinimalIn (SUn n) (expCurve A) 0 1 ↔
      Morse.IsMinimalGeodesic Morse.isSliceSubmanifold_specialUnitaryGroup
        (fun t : ℝ => NormedSpace.exp (t • A)) 0 1 := by
  have hG := Morse.isMatrixGroup_specialUnitaryGroup (ι := Fin n)
  have hc : expCurve A = fun t : ℝ => NormedSpace.exp (t • A) := rfl
  constructor
  · rintro ⟨-, hmin⟩
    refine ⟨zero_le_one, ⟨univ, subset_univ _, hG.isGeodesicOn_exp_smul hA⟩, ?_⟩
    intro c a' b' hpw hcN ha hb
    have := hmin c a' b' hpw.1 (isPWIn_of_isPiecewiseSmooth hpw hcN) ha hb
    rwa [arcLenM_eq, arcLenM_eq] at this
  · rintro ⟨-, -, hmin⟩
    refine ⟨isPWIn_of_isPiecewiseSmooth
      (Morse.IsPiecewiseSmooth.of_contDiff (Morse.contDiff_exp_smul A) zero_le_one)
      (fun t _ => hG.exp_smul_mem hA t), ?_⟩
    intro pw a' b' hab hpw ha hb
    obtain ⟨hpw1, hpw2⟩ := isPiecewiseSmooth_of_isPWIn hpw
    rw [arcLenM_eq, arcLenM_eq]
    exact hmin pw a' b' hpw1 hpw2 ha hb

end

/-- For an idempotent matrix, the trace is the rank. -/
theorem trace_eq_rank {k : ℕ} {P : Mat k} (hP : P * P = P) : P.trace = (P.rank : ℂ) := by
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ he).trace, Matrix.rank]
  rfl

end Dict

open scoped Morse.MatrixInner

/-- The blind lengths of paths in `SU(n)` from `I` to `−I` are the project's `pathLengths`. -/
theorem pathLengths_eq (n : ℕ) :
    Morse.pathLengths (N := (specialUnitaryGroup (Fin n) ℂ : Set (Mat n))) 1 (-1) =
      ENNReal.ofReal '' {L | ∃ (pw : ℝ → Mat n) (a b : ℝ), a ≤ b ∧ IsPWIn (SUn n) pw a b ∧ pw a = 1 ∧
        pw b = -1 ∧ arcLenM pw a b = L} := by
  ext L
  constructor
  · rintro ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
    exact ⟨_, ⟨c, a, b, hc.1, Dict.isPWIn_of_isPiecewiseSmooth hc hcN, ha, hb, rfl⟩,
      by rw [Dict.arcLenM_eq]⟩
  · rintro ⟨_, ⟨pw, a, b, -, hpw, ha, hb, rfl⟩, rfl⟩
    obtain ⟨h1, h2⟩ := Dict.isPiecewiseSmooth_of_isPWIn hpw
    exact ⟨pw, a, b, h1, h2, ha, hb, by rw [Dict.arcLenM_eq]⟩

theorem riemDist_eq_distIn (m : ℕ) [NeZero (2 * m)] :
    Morse.riemDist (N := (specialUnitaryGroup (Fin (2 * m)) ℂ : Set (Mat (2 * m)))) 1 (-1) =
      ENNReal.ofReal (distIn (SUn (2 * m)) 1 (-1)) := by
  rw [Morse.riemDist, pathLengths_eq, distIn]
  refine (Monotone.map_csInf_of_continuousAt ENNReal.continuous_ofReal.continuousAt
    (fun _ _ h => ENNReal.ofReal_le_ofReal h) ?_ ?_).symm
  · -- a path: `t ↦ exp(t suDiag(k₀))`, `k₀ = (1,…,1,−1,…,−1)`
    have hcard : Fintype.card (Fin (2 * m)) = 2 * m := Fintype.card_fin _
    have hA₀ : Morse.suDiag (Morse.kHalf hcard) ∈ Morse.specialSkewHermitian (Fin (2 * m)) := by
      simpa using Morse.conj_suDiag_mem (Morse.sum_kHalf hcard) (T := 1) (by simp)
    have hexp₀ : NormedSpace.exp (Morse.suDiag (Morse.kHalf hcard)) = -1 := by
      simpa using Morse.exp_conj_suDiag (Morse.odd_kHalf hcard) (T := 1) (by simp)
    obtain ⟨h1, h2, h3, h4⟩ := Morse.mem_pathSpace_exp hA₀ hexp₀
    exact ⟨_, _, 0, 1, zero_le_one, Dict.isPWIn_of_isPiecewiseSmooth h1 h2, h3, h4, rfl⟩
  · refine ⟨0, ?_⟩
    rintro _ ⟨pw, a, b, hab, -, -, -, rfl⟩
    exact intervalIntegral.integral_nonneg hab fun _ _ => Real.sqrt_nonneg _

/-- `A`'s `sq_conj_suDiag_iff`, re-proved (the project's computation, copied). -/
theorem sq_conj_suDiag_iff' {ι : Type} [Fintype ι] [DecidableEq ι] {T : Matrix ι ι ℂ}
    (hT : Tᴴ * T = 1) (k : ι → ℤ) :
    (T * Morse.suDiag k * Tᴴ) * (T * Morse.suDiag k * Tᴴ) = -((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) ↔
      ∀ i, k i = 1 ∨ k i = -1 := by
  have hT' := Morse.mul_conjTranspose_eq_one hT
  have r : ∀ X : Matrix ι ι ℂ, Tᴴ * (T * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hT, Matrix.one_mul]
  have hsq : (T * Morse.suDiag k * Tᴴ) * (T * Morse.suDiag k * Tᴴ) =
      T * (Morse.suDiag k * Morse.suDiag k) * Tᴴ := by
    simp only [Matrix.mul_assoc, r]
  have hD : Morse.suDiag k * Morse.suDiag k =
      diagonal fun j => -((Real.pi : ℂ) ^ 2 * (k j : ℂ) ^ 2) := by
    rw [Morse.suDiag, diagonal_mul_diagonal]
    congr 1
    funext j
    linear_combination ((Real.pi : ℂ) ^ 2 * (k j : ℂ) ^ 2) * Complex.I_sq
  rw [hsq, hD]
  constructor
  · intro h i
    have h1 : Tᴴ * (T * (diagonal fun j => -((Real.pi : ℂ) ^ 2 * (k j : ℂ) ^ 2)) * Tᴴ) * T =
        Tᴴ * (-((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ)) * T := by rw [h]
    simp only [Matrix.mul_assoc, r, hT, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul] at h1
    have h2 := congrFun (congrFun h1 i) i
    simp only [diagonal_apply_eq, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h2
    have hpi : (Real.pi : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
    have h3 : (k i : ℂ) ^ 2 = 1 := by
      have := neg_inj.1 h2
      field_simp at this
      exact this
    have h4 : (k i) ^ 2 = 1 := by exact_mod_cast h3
    exact (Morse.sq_eq_one_iff' (a := k i)).1 h4
  · intro h
    have hD1 : (diagonal fun j => -((Real.pi : ℂ) ^ 2 * (k j : ℂ) ^ 2)) =
        -((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) := by
      rw [← diagonal_one, ← diagonal_smul]
      congr 1
      funext j
      rcases h j with hj | hj <;> simp [hj]
    rw [hD1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hT']

theorem milnorA_eq_suDiag {n : ℕ} (k : Fin n → ℤ) : milnorA k = Morse.suDiag k := by
  unfold milnorA diagI Morse.suDiag
  congr 1
  funext j
  push_cast
  ring

/-- `A`'s two `SU(2m)` conjuncts (`riemDist_one_neg_one`, `isMinimalGeodesic_exp_iff`) at the index type
`Fin (2m)` of `B`. -/
def A_fin : Prop :=
  (∀ (m : ℕ) [NeZero (2 * m)],
    Morse.riemDist (N := (specialUnitaryGroup (Fin (2 * m)) ℂ : Set (Mat (2 * m)))) 1 (-1) =
      ENNReal.ofReal (Real.pi * Real.sqrt (2 * m))) ∧
  (∀ (m : ℕ) [NeZero (2 * m)] (A : Mat (2 * m)), A ∈ Morse.specialSkewHermitian (Fin (2 * m)) →
    NormedSpace.exp A = -1 →
    (Morse.IsMinimalGeodesic Morse.isSliceSubmanifold_specialUnitaryGroup
        (fun t : ℝ => NormedSpace.exp (t • A)) 0 1 ↔
      A * A = -((Real.pi : ℂ) ^ 2) • (1 : Mat (2 * m))))

/-- `B`'s `SU(2m)` claims (iii), (iv) give `A_fin`. -/
theorem B_to_A_fin : B → A_fin := by
  rintro ⟨-, hiii, -, hiv⟩
  refine ⟨fun m _ => by rw [riemDist_eq_distIn, hiv m], fun m _ A hA hexp => ?_⟩
  obtain ⟨T, k, hT, hk, hsum, hAeq⟩ := Morse.exists_unitary_suDiag hA hexp
  have hTU : T ∈ Un (2 * m) := by
    show T ∈ Matrix.unitaryGroup (Fin (2 * m)) ℂ
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
    exact hT
  have h := hiii m T hTU k hk hsum A (by rw [hAeq, milnorA_eq_suDiag])
  rw [← Dict.isMinimalIn_iff hA, h, hAeq, sq_conj_suDiag_iff' hT]

/-! ## `B → A` for every index type -/

namespace Rx

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem R_mul (e : ι ≃ κ) (A B : Matrix ι ι ℂ) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B := by
  simp only [← Matrix.coe_reindexAlgEquiv ℂ ℂ e, map_mul]

theorem R_one (e : ι ≃ κ) : Matrix.reindex e e (1 : Matrix ι ι ℂ) = 1 := by
  simp only [← Matrix.coe_reindexAlgEquiv ℂ ℂ e, map_one]

theorem R_neg (e : ι ≃ κ) (A : Matrix ι ι ℂ) : Matrix.reindex e e (-A) = -Matrix.reindex e e A := by
  simp only [← Matrix.coe_reindexAlgEquiv ℂ ℂ e, map_neg]

theorem R_trace (e : ι ≃ κ) (A : Matrix ι ι ℂ) : trace (Matrix.reindex e e A) = trace A := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

theorem R_norm (e : ι ≃ κ) (A : Matrix ι ι ℂ) : ‖Matrix.reindex e e A‖ = ‖A‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, Morse.inner_def, Morse.inner_def, Matrix.conjTranspose_reindex,
    ← R_mul, R_trace]

/-- Reindexing, a linear isometry of `Mₙ(ℂ)` (Frobenius norm). -/
def L (e : ι ≃ κ) : Matrix ι ι ℂ ≃ₗᵢ[ℝ] Matrix κ κ ℂ :=
  { toLinearEquiv := Matrix.reindexLinearEquiv ℝ ℂ e e
    norm_map' := R_norm e }

theorem L_apply (e : ι ≃ κ) (A : Matrix ι ι ℂ) : L e A = Matrix.reindex e e A := rfl

theorem mem_SU (e : ι ≃ κ) {A : Matrix ι ι ℂ}
    (hA : A ∈ (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) :
    L e A ∈ (specialUnitaryGroup κ ℂ : Set (Matrix κ κ ℂ)) := by
  rw [SetLike.mem_coe, Matrix.mem_specialUnitaryGroup_iff] at hA ⊢
  obtain ⟨h1, h2⟩ := hA
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at h1
  refine ⟨?_, by rw [L_apply, Matrix.det_reindex_self, h2]⟩
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, L_apply, Matrix.conjTranspose_reindex,
    ← R_mul, h1, R_one]

theorem deriv_L (e : ι ≃ κ) (c : ℝ → Matrix ι ι ℂ) (t : ℝ) :
    deriv (fun s => L e (c s)) t = L e (deriv c t) := by
  by_cases h : DifferentiableAt ℝ c t
  · exact ((L e).toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      h.hasDerivAt).deriv
  · have h' : ¬ DifferentiableAt ℝ (fun s => L e (c s)) t := by
      intro h'
      apply h
      have := (L e).symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp t h'
      simpa [Function.comp_def] using this
    rw [deriv_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h', map_zero]

theorem pathLength_L (e : ι ≃ κ) (c : ℝ → Matrix ι ι ℂ) (a b : ℝ) :
    Morse.pathLength (fun s => L e (c s)) a b = Morse.pathLength c a b := by
  unfold Morse.pathLength
  congr 1
  funext t
  rw [deriv_L, LinearIsometryEquiv.norm_map]

theorem pathLengths_subset (e : ι ≃ κ) :
    Morse.pathLengths (N := (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) 1 (-1) ⊆
      Morse.pathLengths (N := (specialUnitaryGroup κ ℂ : Set (Matrix κ κ ℂ))) 1 (-1) := by
  rintro _ ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
  refine ⟨fun s => L e (c s), a, b, hc.comp_clm (L e).toContinuousLinearEquiv.toContinuousLinearMap,
    fun t ht => mem_SU e (hcN t ht), ?_, ?_, by rw [pathLength_L]⟩
  · simp only [ha, L_apply, R_one]
  · simp only [hb, L_apply, R_neg, R_one]

theorem riemDist_reindex (e : ι ≃ κ) :
    Morse.riemDist (N := (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) 1 (-1) =
      Morse.riemDist (N := (specialUnitaryGroup κ ℂ : Set (Matrix κ κ ℂ))) 1 (-1) := by
  unfold Morse.riemDist
  rw [Set.Subset.antisymm (pathLengths_subset e) (pathLengths_subset e.symm)]

end Rx

/-- `A`'s `pathLength_exp_smul`, re-proved (the project's argument, copied); `B` has it only for Milnor's
`A`. -/
theorem pathLength_exp_smul' : type_of% @Morse.pathLength_exp_smul.{0} := by
  intro ι _ _ A hA
  have h := Morse.pathLength_eq_of_norm_deriv (k := ‖A‖)
    (Morse.IsPiecewiseSmooth.of_contDiff (Morse.contDiff_exp_smul A) zero_le_one).isAdmissible
    (fun t _ _ => by
      rw [(hasDerivAt_exp_smul_const A t).deriv]
      have hu : (NormedSpace.exp (t • A))ᴴ * NormedSpace.exp (t • A) = 1 :=
        Morse.exp_conjTranspose_mul_exp_of_skew
          (by rw [conjTranspose_smul, star_trivial, hA, smul_neg])
      rw [← Morse.mulLeftIso_apply _ hu, LinearIsometryEquiv.norm_map])
  rw [h, sub_zero, mul_one]

/-- `A`'s `norm_conj_suDiag_sq`, re-proved. -/
theorem norm_conj_suDiag_sq' : type_of% @Morse.norm_conj_suDiag_sq.{0} := by
  intro ι _ _ T hT k
  rw [Morse.norm_conj_unitary hT, Morse.norm_suDiag_sq]

theorem norm_eq_pi_sqrt' {ι : Type} [Fintype ι] [DecidableEq ι] {T : Matrix ι ι ℂ}
    (hT : Tᴴ * T = 1) (k : ι → ℤ) :
    ‖T * Morse.suDiag k * Tᴴ‖ = Real.pi * Real.sqrt (∑ j, (k j : ℝ) ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_conj_suDiag_sq' hT, Real.sqrt_mul (by positivity),
    Real.sqrt_sq Real.pi_pos.le]

/-- `A`'s `pi_sqrt_card_le_norm`, re-proved (spectral decomposition `exists_unitary_suDiag`, outside the
item, and `Σ k_j² ≥ n` for odd `k_j`). -/
theorem pi_sqrt_card_le_norm' : type_of% @Morse.pi_sqrt_card_le_norm.{0} := by
  intro ι _ _ A hA hexp
  obtain ⟨T, k, hT, hk, -, rfl⟩ := Morse.exists_unitary_suDiag hA hexp
  rw [norm_eq_pi_sqrt' hT]
  exact Morse.pi_sqrt_card_le hk

/-- `A`'s `riemDist_one_neg_one`, from `B` (iv) by reindexing to `Fin (2m)`. -/
theorem riemDist_one_neg_one_of_B (hB : B) : type_of% @Morse.riemDist_one_neg_one.{0} := by
  intro ι _ _ _ m hcard
  have e : ι ≃ Fin (2 * m) := Fintype.equivFinOfCardEq hcard
  haveI : NeZero (2 * m) := ⟨by rw [← hcard]; exact Fintype.card_ne_zero⟩
  rw [Rx.riemDist_reindex e]
  exact (B_to_A_fin hB).1 m

/-- `A`'s `isMinimalGeodesic_exp_iff`, from the distance (`B` (iv)) by the length computation. -/
theorem isMinimalGeodesic_exp_iff_of_B (hB : B) : type_of% @Morse.isMinimalGeodesic_exp_iff.{0} := by
  intro ι _ _ _ m hcard A hA hexp
  have hG := Morse.isMatrixGroup_specialUnitaryGroup (ι := ι)
  have hρ := riemDist_one_neg_one_of_B hB hcard
  have hcard' : (Fintype.card ι : ℝ) = 2 * m := by exact_mod_cast hcard
  have hlen := pathLength_exp_smul' hA.1
  obtain ⟨T, k, hT, hk, -, hAeq⟩ := Morse.exists_unitary_suDiag hA hexp
  have hnorm : ‖A‖ = Real.pi * Real.sqrt (∑ j, (k j : ℝ) ^ 2) := by
    rw [hAeq]; exact norm_eq_pi_sqrt' hT k
  have hπ : 0 ≤ Real.pi * Real.sqrt (2 * m) := by positivity
  rw [hAeq, sq_conj_suDiag_iff' hT, ← Morse.sum_sq_eq_card_iff hk, ← hAeq]
  constructor
  · rintro ⟨-, -, hmin⟩
    -- `ofReal ‖A‖ ≤ ρ(I, −I) = π√(2m)`
    have hle : ENNReal.ofReal ‖A‖ ≤ ENNReal.ofReal (Real.pi * Real.sqrt (2 * m)) := by
      rw [← hρ]
      refine le_sInf ?_
      rintro _ ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
      rw [← hlen]
      exact ENNReal.ofReal_le_ofReal (hmin c a b hc hcN (by rw [ha]; simp) (by rw [hb]; simp [hexp]))
    have h1 := (ENNReal.ofReal_le_ofReal_iff hπ).1 hle
    have hge := Morse.pi_sqrt_card_le hk
    rw [← hnorm, hcard'] at hge
    have h3 : Real.pi * Real.sqrt (∑ j, (k j : ℝ) ^ 2) = Real.pi * Real.sqrt (2 * m) := by
      rw [← hnorm]; linarith
    have heq : Real.sqrt (∑ j, (k j : ℝ) ^ 2) = Real.sqrt (Fintype.card ι) := by
      rw [hcard']; exact mul_left_cancel₀ Real.pi_ne_zero h3
    have h4 := congrArg (· ^ 2) heq
    simp only [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (k j : ℝ)),
      Real.sq_sqrt (Nat.cast_nonneg _)] at h4
    exact_mod_cast h4
  · intro hsq
    refine ⟨zero_le_one, ⟨univ, subset_univ _, hG.isGeodesicOn_exp_smul hA⟩,
      fun c a b hc hcN ha hb => ?_⟩
    have h1 := Morse.riemDist_le_pathLength (N := (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) hc hcN
    simp only [ha, hb, zero_smul, NormedSpace.exp_zero, one_smul, hexp] at h1
    rw [hρ] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff hc.isAdmissible.pathLength_nonneg).1 h1
    rw [hlen, hnorm]
    have h5 : (∑ j, (k j : ℝ) ^ 2) = 2 * m := by
      rw [← hcard']; exact_mod_cast hsq
    rw [h5]
    exact h2

/-- `B → A`: `A`'s distance and minimality conjuncts from `B`'s `SU(2m)` claims (reindexed to any index
type); the other conjuncts are not in `B` (only for Milnor's `A`) and are proved outright. -/
theorem B_to_A : B → A := fun hB =>
  ⟨pathLength_exp_smul', norm_conj_suDiag_sq', pi_sqrt_card_le_norm', riemDist_one_neg_one_of_B hB,
    @sq_conj_suDiag_iff', isMinimalGeodesic_exp_iff_of_B hB⟩

/-! ## `A → B` on the `SU(2m)` part

`A → B` fails because of `U(n)` (`B`'s (ii) and the `U(n)` distance): the lower bound `π√n` for the length
of every path from `I` to `−I` in `U(n)` is neither in `A` nor in the project. The rest of `B` follows. -/

/-- `B` without its `U(n)` claims: (i) the length, (iii) minimality in `SU(2m)`, (iv) the `SU(2m)` distance. -/
def B_SU : Prop :=
  (∀ (n : ℕ), ∀ T ∈ Un n, ∀ k : Fin n → ℤ, (∀ j, Odd (k j)) → ∀ A : Mat n, A = T * milnorA k * Tᴴ →
    arcLenM (expCurve A) 0 1 = Real.pi * Real.sqrt (∑ j, ((k j : ℝ)) ^ 2)) ∧
  (∀ (m : ℕ), ∀ T ∈ Un (2 * m), ∀ k : Fin (2 * m) → ℤ, (∀ j, Odd (k j)) → ∑ j, k j = 0 →
    ∀ A : Mat (2 * m), A = T * milnorA k * Tᴴ →
      (IsMinimalIn (SUn (2 * m)) (expCurve A) 0 1 ↔ ∀ j, k j = 1 ∨ k j = -1)) ∧
  (∀ m : ℕ, distIn (SUn (2 * m)) 1 (-1) = Real.pi * Real.sqrt (2 * (m : ℝ)))

theorem B_to_B_SU : B → B_SU := fun h =>
  ⟨fun n T hT k hk A hA => (h.1 n T hT k hk A hA).1, h.2.1, h.2.2.2⟩

theorem unitary_of_mem {n : ℕ} {T : Mat n} (hT : T ∈ Un n) : Tᴴ * T = 1 := by
  have : T ∈ Matrix.unitaryGroup (Fin n) ℂ := hT
  rwa [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose] at this

theorem conj_skew {n : ℕ} (T : Mat n) (k : Fin n → ℤ) :
    (T * Morse.suDiag k * Tᴴ)ᴴ = -(T * Morse.suDiag k * Tᴴ) := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Morse.suDiag,
    diagonal_conjTranspose, Matrix.mul_assoc]
  have : star (fun j => ((Real.pi : ℂ) * k j) * Complex.I) = -(fun j => ((Real.pi : ℂ) * k j) * Complex.I) := by
    funext j
    simp [Complex.conj_ofReal, mul_comm]
  rw [this, Pi.neg_def, ← diagonal_neg, Matrix.neg_mul, Matrix.mul_neg]

instance : IsEmpty (Fin (2 * 0)) := (inferInstance : IsEmpty (Fin 0))

theorem arcLenM_zero (c : ℝ → Mat (2 * 0)) (a b : ℝ) : arcLenM c a b = 0 := by
  unfold arcLenM
  have : ∀ t, normM (deriv c t) = 0 := fun t => by
    rw [Subsingleton.elim (deriv c t) 0]; simp [normM, ipM]
  simp [this]

open scoped Matrix.Norms.Elementwise in
theorem isPWIn_zero (c : ℝ → Mat (2 * 0)) : IsPWIn (SUn (2 * 0)) c 0 1 := by
  refine ⟨fun t _ => ?_, 1, fun i => i, by simp, by simp, fun i hi => by simp, fun i _ => ?_⟩
  · rw [Subsingleton.elim (c t) 1]; exact (Matrix.specialUnitaryGroup _ ℂ).one_mem
  · have : c = fun _ => 0 := funext fun _ => Subsingleton.elim _ _
    rw [this]; exact contDiffOn_const

theorem A_to_B_SU : A → B_SU := by
  rintro ⟨hlen, hnorm, -, hdist, hsq, hmin⟩
  refine ⟨fun n T hT k _ A hA => ?_, fun m T hT k hk hsum A hAeq => ?_, fun m => ?_⟩
  · have hT' := unitary_of_mem hT
    rw [milnorA_eq_suDiag] at hA
    rw [Dict.arcLenM_eq, show expCurve A = fun t : ℝ => NormedSpace.exp (t • A) from rfl,
      hlen (hA ▸ conj_skew T k), hA, ← Real.sqrt_sq (norm_nonneg _), hnorm hT',
      Real.sqrt_mul (by positivity), Real.sqrt_sq Real.pi_pos.le]
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨fun _ j => isEmptyElim j, fun _ => ⟨isPWIn_zero _, fun pw a' b' _ _ _ _ => by
        rw [arcLenM_zero, arcLenM_zero]⟩⟩
    · haveI : NeZero (2 * m) := ⟨by omega⟩
      have hT' := unitary_of_mem hT
      rw [milnorA_eq_suDiag] at hAeq
      have hA : A ∈ Morse.specialSkewHermitian (Fin (2 * m)) := hAeq ▸ Morse.conj_suDiag_mem hsum hT'
      have hexp : NormedSpace.exp A = -1 := hAeq ▸ Morse.exp_conj_suDiag hk hT'
      rw [Dict.isMinimalIn_iff hA, hmin (Fintype.card_fin _) hA hexp, hAeq, hsq hT']
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.cast_zero, mul_zero, Real.sqrt_zero]
      refine le_antisymm (csInf_le ⟨0, ?_⟩ ⟨fun _ => 1, 0, 1, zero_le_one, isPWIn_zero _, rfl,
        Subsingleton.elim _ _, arcLenM_zero _ _ _⟩) (Real.sInf_nonneg ?_)
      · rintro _ ⟨pw, a, b, hab, -, -, -, rfl⟩
        exact intervalIntegral.integral_nonneg hab fun _ _ => Real.sqrt_nonneg _
      · rintro _ ⟨pw, a, b, hab, -, -, -, rfl⟩
        exact intervalIntegral.integral_nonneg hab fun _ _ => Real.sqrt_nonneg _
    · haveI : NeZero (2 * m) := ⟨by omega⟩
      have h := hdist (ι := Fin (2 * m)) (Fintype.card_fin _)
      rw [riemDist_eq_distIn] at h
      have h0 : 0 ≤ distIn (SUn (2 * m)) 1 (-1) := by
        refine Real.sInf_nonneg ?_
        rintro _ ⟨pw, a, b, hab, -, -, -, rfl⟩
        exact intervalIntegral.integral_nonneg hab fun _ _ => Real.sqrt_nonneg _
      exact (ENNReal.ofReal_eq_ofReal_iff h0 (by positivity)).1 h

#rt_check RoundTrip.V14_15.A_to_B_SU [Morse.pathLength_exp_smul, Morse.norm_conj_suDiag_sq, Morse.pi_sqrt_card_le_norm, Morse.riemDist_one_neg_one, Morse.sq_conj_suDiag_iff, Morse.isMinimalGeodesic_exp_iff]
#rt_check RoundTrip.V14_15.B_to_A [Morse.pathLength_exp_smul, Morse.norm_conj_suDiag_sq, Morse.pi_sqrt_card_le_norm, Morse.riemDist_one_neg_one, Morse.sq_conj_suDiag_iff, Morse.isMinimalGeodesic_exp_iff]
#rt_overlap RoundTrip.V14_15.B_to_A [Morse.pathLength_exp_smul, Morse.norm_conj_suDiag_sq, Morse.pi_sqrt_card_le_norm, Morse.riemDist_one_neg_one, Morse.sq_conj_suDiag_iff, Morse.isMinimalGeodesic_exp_iff]
#rt_check RoundTrip.V14_15.B_to_A_fin [Morse.pathLength_exp_smul, Morse.norm_conj_suDiag_sq, Morse.pi_sqrt_card_le_norm, Morse.riemDist_one_neg_one, Morse.sq_conj_suDiag_iff, Morse.isMinimalGeodesic_exp_iff]
#rt_overlap RoundTrip.V14_15.B_to_A_fin [Morse.pathLength_exp_smul, Morse.norm_conj_suDiag_sq, Morse.pi_sqrt_card_le_norm, Morse.riemDist_one_neg_one, Morse.sq_conj_suDiag_iff, Morse.isMinimalGeodesic_exp_iff]

end

end RoundTrip.V14_15
