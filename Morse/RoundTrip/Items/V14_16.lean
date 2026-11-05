import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_16

open Matrix Set
open scoped ContDiff

namespace RoundTrip.V14_16

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Dictionary: the blind matrix-level lengths (entrywise norm, `Re tr(AB*)`) and the project's
(Frobenius norm) -/

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

theorem grass_eq (m : ℕ) : Grass (2 * m) m = Morse.grassmannian (Fin (2 * m)) m := by
  ext P
  simp only [Grass, Morse.grassmannian, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [trace_eq_rank h2, h3]⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [trace_eq_rank h2] at h3
    exact_mod_cast h3

theorem mem_suAlg_iff {k : ℕ} {A : Mat k} : A ∈ suAlg k ↔ A ∈ Morse.specialSkewHermitian (Fin k) :=
  Iff.rfl

open scoped Morse.MatrixInner in
/-- The blind velocities of minimal geodesics are the project's `minVel`, given `mem_minVel_iff`. -/
theorem minVelIn_eq {m : ℕ} [NeZero (2 * m)]
    (hmem : ∀ {A : Mat (2 * m)}, A ∈ Morse.minVel (Fin (2 * m)) ↔
      A ∈ Morse.specialSkewHermitian (Fin (2 * m)) ∧ NormedSpace.exp A = -1 ∧
        Morse.IsMinimalGeodesic Morse.isSliceSubmanifold_specialUnitaryGroup
          (fun t : ℝ => NormedSpace.exp (t • A)) 0 1) :
    minVelIn (SUn (2 * m)) (suAlg (2 * m)) = Morse.minVel (Fin (2 * m)) := by
  ext A
  rw [hmem]
  constructor
  · rintro ⟨hA, hexp, hmin⟩
    exact ⟨hA, hexp, (isMinimalIn_iff hA).1 hmin⟩
  · rintro ⟨hA, hexp, hmin⟩
    exact ⟨hA, hexp, (isMinimalIn_iff hA).2 hmin⟩

/-! ### `m = 0`: both spaces are points -/

instance : IsEmpty (Fin (2 * 0)) := (inferInstance : IsEmpty (Fin 0))

theorem arcLenM_zero (c : ℝ → Mat 0) (a b : ℝ) : arcLenM c a b = 0 := by
  unfold arcLenM
  have : ∀ t, normM (deriv c t) = 0 := fun t => by
    rw [Subsingleton.elim (deriv c t) 0]; simp [normM, ipM]
  simp [this]

open scoped Matrix.Norms.Elementwise in
theorem zero_mem_minVelIn : (0 : Mat (2 * 0)) ∈ minVelIn (SUn (2 * 0)) (suAlg (2 * 0)) := by
  refine ⟨(suAlg _).zero_mem, Subsingleton.elim _ _, ⟨fun t _ => ?_, 1, fun i => i, by simp,
    by simp, fun i hi => by simp, fun i _ => ?_⟩, fun pw a' b' _ _ _ _ => ?_⟩
  · rw [Subsingleton.elim (expCurve 0 t) 1]; exact (Matrix.specialUnitaryGroup _ ℂ).one_mem
  · have : expCurve (0 : Mat (2 * 0)) = fun _ => 0 := funext fun _ => Subsingleton.elim _ _
    rw [this]; exact contDiffOn_const
  · rw [arcLenM_zero, arcLenM_zero]

theorem zero_mem_grass : (0 : Mat (2 * 0)) ∈ Grass (2 * 0) 0 :=
  ⟨by simp, by simp, Matrix.rank_zero⟩

end Dict


/-- The project's statement (universes `0`; `minVel`, `grassmannian` are vocabulary): `A² = −π²I` gives
`exp A = −I` for skew-Hermitian `A`; `A ∈ minVel` iff `t ↦ exp tA` is a minimal geodesic from `I` to `−I`
in `SU(2m)`; and the definition `lemma_23_1`, read as `Nonempty` of its type: `minVel ι ≃ₜ grassmannian ι m`
for every index type of cardinality `2m`. -/
def A : Prop :=
  type_of% @Morse.exp_eq_neg_one_of_sq.{0} ∧ type_of% @Morse.mem_minVel_iff.{0} ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}, Fintype.card ι = 2 * m →
      Nonempty (Morse.minVel ι ≃ₜ Morse.grassmannian ι m)

theorem A_holds : A :=
  ⟨@Morse.exp_eq_neg_one_of_sq, @Morse.mem_minVel_iff, fun hcard => ⟨Morse.lemma_23_1 hcard⟩⟩

theorem A_to_B : A → B := by
  rintro ⟨-, hmem, hhom⟩ m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · let _ : Unique ↥(minVelIn (SUn (2 * 0)) (suAlg (2 * 0))) :=
      uniqueOfSubsingleton ⟨0, Dict.zero_mem_minVelIn⟩
    let _ : Unique ↥(Grass (2 * 0) 0) := uniqueOfSubsingleton ⟨0, Dict.zero_mem_grass⟩
    exact ⟨Homeomorph.homeomorphOfUnique _ _⟩
  · haveI : NeZero (2 * m) := ⟨by omega⟩
    have h1 := Dict.minVelIn_eq (m := m) (fun {A} => hmem (Fintype.card_fin _) (A := A))
    obtain ⟨φ⟩ := hhom (ι := Fin (2 * m)) (Fintype.card_fin _)
    exact ⟨(Homeomorph.setCongr h1).trans (φ.trans (Homeomorph.setCongr (Dict.grass_eq m).symm))⟩

/-! ## `B → A` -/

namespace Rx

variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Reindexing `ι ≃ κ` as a homeomorphism `Mat_ι(ℂ) ≃ₜ Mat_κ(ℂ)`. -/
def R (e : ι ≃ κ) : Matrix ι ι ℂ ≃ₜ Matrix κ κ ℂ where
  toEquiv := Matrix.reindex e e
  continuous_toFun := continuous_id.matrix_submatrix _ _
  continuous_invFun := continuous_id.matrix_submatrix _ _

theorem R_apply (e : ι ≃ κ) (A : Matrix ι ι ℂ) : R e A = Matrix.reindex e e A := rfl

theorem R_mul (e : ι ≃ κ) (A B : Matrix ι ι ℂ) : R e (A * B) = R e A * R e B := by
  simp only [R_apply, ← Matrix.coe_reindexAlgEquiv ℂ ℂ e, map_mul]

theorem R_one (e : ι ≃ κ) : R e (1 : Matrix ι ι ℂ) = 1 := by
  simp only [R_apply, ← Matrix.coe_reindexAlgEquiv ℂ ℂ e, map_one]

theorem R_smul (e : ι ≃ κ) (c : ℂ) (A : Matrix ι ι ℂ) : R e (c • A) = c • R e A := by
  simp only [R_apply, ← Matrix.coe_reindexAlgEquiv ℂ ℂ e, map_smul]

theorem R_sub (e : ι ≃ κ) (A B : Matrix ι ι ℂ) : R e (A - B) = R e A - R e B := by
  simp only [R_apply, ← Matrix.coe_reindexAlgEquiv ℂ ℂ e, map_sub]

theorem R_conjTranspose (e : ι ≃ κ) (A : Matrix ι ι ℂ) : (R e A)ᴴ = R e Aᴴ :=
  Matrix.conjTranspose_reindex e e A

theorem R_trace (e : ι ≃ κ) (A : Matrix ι ι ℂ) : trace (R e A) = trace A := by
  simp only [R_apply, Matrix.trace, Matrix.reindex_apply, Matrix.diag, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

theorem R_neg (e : ι ≃ κ) (A : Matrix ι ι ℂ) : R e (-A) = -R e A := by
  simp only [R_apply, ← Matrix.coe_reindexAlgEquiv ℂ ℂ e, map_neg]

theorem mem_minVel_R (e : ι ≃ κ) (A : Matrix ι ι ℂ) :
    A ∈ Morse.minVel ι ↔ R e A ∈ Morse.minVel κ := by
  have hinj := (R e).injective
  show (Aᴴ = -A ∧ trace A = 0) ∧ A * A = -((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) ↔
    ((R e A)ᴴ = -(R e A) ∧ trace (R e A) = 0) ∧
      R e A * R e A = -((Real.pi : ℂ) ^ 2) • (1 : Matrix κ κ ℂ)
  rw [R_conjTranspose, R_trace, ← R_neg, ← R_mul, ← R_one e, ← R_smul]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨by rw [h1], h2⟩, by rw [h3]⟩,
    fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨hinj h1, h2⟩, hinj h3⟩⟩

theorem mem_grassmannian_R (e : ι ≃ κ) (m : ℕ) (P : Matrix ι ι ℂ) :
    P ∈ Morse.grassmannian ι m ↔ R e P ∈ Morse.grassmannian κ m := by
  have hinj := (R e).injective
  show Pᴴ = P ∧ P * P = P ∧ trace P = m ↔ (R e P)ᴴ = R e P ∧ R e P * R e P = R e P ∧ trace (R e P) = m
  rw [R_conjTranspose, R_trace, ← R_mul]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨by rw [h1], by rw [h2], h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨hinj h1, hinj h2, h3⟩⟩

end Rx

/-- `A`'s first conjunct, re-proved outright (the project's spectral argument, copied): it is not in `B`. -/
theorem exp_eq_neg_one_of_sq' : type_of% @Morse.exp_eq_neg_one_of_sq.{0} := by
  intro ι _ _ A hA hsq
  have hH : (Complex.I • A).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, hA, Complex.star_def, Complex.conj_I, neg_smul,
      smul_neg, neg_neg]
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  set ev := hH.eigenvalues
  have hU : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hU' := Morse.mul_conjTranspose_eq_one hU
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at hspec
  set D : Matrix ι ι ℂ := Matrix.diagonal fun j => ((-ev j : ℝ) : ℂ) * Complex.I with hDdef
  have hAD : A = U * D * Uᴴ := by
    have e1 : A = (-Complex.I) • (Complex.I • A) := by
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    have e2 : D = (-Complex.I) • Matrix.diagonal (RCLike.ofReal ∘ ev) := by
      rw [hDdef, ← diagonal_smul]
      congr 1
      funext j
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_neg, neg_mul]
      exact congrArg Neg.neg (mul_comm _ _)
    rw [e2, Matrix.mul_smul, Matrix.smul_mul, ← hspec, ← e1]
  have r : ∀ X : Matrix ι ι ℂ, Uᴴ * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hD2 : D * D = -((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) := by
    have h1 : Uᴴ * (A * A) * U = Uᴴ * (-((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ)) * U := by
      rw [hsq]
    rw [hAD] at h1
    simpa only [Matrix.mul_assoc, r, hU, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul] using h1
  have hev : ∀ j, ∃ k : ℤ, Odd k ∧ -ev j = Real.pi * k := by
    intro j
    have h1 := congrFun (congrFun hD2 j) j
    simp only [hDdef, diagonal_mul_diagonal, diagonal_apply_eq, Matrix.smul_apply, one_apply_eq,
      smul_eq_mul, mul_one] at h1
    push_cast at h1
    have h2 : ((ev j : ℂ)) ^ 2 = (Real.pi : ℂ) ^ 2 := by
      linear_combination (-1 : ℂ) * h1 + (ev j : ℂ) ^ 2 * Complex.I_sq
    have h3 : ev j ^ 2 = Real.pi ^ 2 := by exact_mod_cast h2
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h | h
    · exact ⟨-1, by decide, by rw [h]; push_cast; ring⟩
    · exact ⟨1, by decide, by rw [h]; push_cast; ring⟩
  have hexpD : NormedSpace.exp D = -1 := by
    rw [hDdef]
    exact (Morse.exp_diagonal_eq_neg_one_iff _).2 hev
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hU
  rw [hAD, ← hinv, Matrix.exp_conj U _ ⟨⟨U, Uᴴ, hU', hU⟩, rfl⟩, hexpD, hinv, Matrix.mul_neg,
    Matrix.mul_one, Matrix.neg_mul, hU']

/-- `A`'s second conjunct, re-proved outright from the project's `isMinimalGeodesic_exp_iff` (item V14_15,
outside this item): it is not in `B`. -/
theorem mem_minVel_iff' : type_of% @Morse.mem_minVel_iff.{0} := by
  intro ι _ _ _ m hcard A
  constructor
  · rintro ⟨hA, hsq⟩
    have hexp := exp_eq_neg_one_of_sq' hA.1 hsq
    exact ⟨hA, hexp, (Morse.isMinimalGeodesic_exp_iff hcard hA hexp).2 hsq⟩
  · rintro ⟨hA, hexp, hmin⟩
    exact ⟨hA, (Morse.isMinimalGeodesic_exp_iff hcard hA hexp).1 hmin⟩

open scoped Morse.MatrixInner in
/-- `B` gives `A`'s third conjunct (the homeomorphism `minVel ι ≃ₜ grassmannian ι m`, read as `Nonempty`)
for every index type, by reindexing to `Fin (2m)`; the first two conjuncts are not in `B` and are proved
outright. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨exp_eq_neg_one_of_sq', mem_minVel_iff', ?_⟩
  intro ι _ _ m hcard
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.1 (by simpa using hcard)
    have h0 : (0 : Matrix ι ι ℂ) ∈ Morse.minVel ι := by
      refine ⟨(Morse.specialSkewHermitian ι).zero_mem, Subsingleton.elim _ _⟩
    have h0' : (0 : Matrix ι ι ℂ) ∈ Morse.grassmannian ι 0 := ⟨by simp, by simp, by simp⟩
    let _ : Unique ↥(Morse.minVel ι) := uniqueOfSubsingleton ⟨0, h0⟩
    let _ : Unique ↥(Morse.grassmannian ι 0) := uniqueOfSubsingleton ⟨0, h0'⟩
    exact ⟨Homeomorph.homeomorphOfUnique _ _⟩
  · haveI : NeZero (2 * m) := ⟨by omega⟩
    have e : ι ≃ Fin (2 * m) := Fintype.equivFinOfCardEq hcard
    have h1 := Dict.minVelIn_eq (m := m) (fun {A} => mem_minVel_iff' (Fintype.card_fin _) (A := A))
    obtain ⟨φ⟩ := hB m
    exact ⟨((Rx.R e).subtype (Rx.mem_minVel_R e)).trans ((Homeomorph.setCongr h1.symm).trans
      (φ.trans ((Homeomorph.setCongr (Dict.grass_eq m)).trans
        ((Rx.R e).subtype (Rx.mem_grassmannian_R e m)).symm)))⟩
end

#rt_check RoundTrip.V14_16.A_to_B [Morse.exp_eq_neg_one_of_sq, Morse.mem_minVel_iff, Morse.lemma_23_1]
#rt_check RoundTrip.V14_16.B_to_A [Morse.exp_eq_neg_one_of_sq, Morse.mem_minVel_iff, Morse.lemma_23_1]
#rt_overlap RoundTrip.V14_16.B_to_A [Morse.exp_eq_neg_one_of_sq, Morse.mem_minVel_iff, Morse.lemma_23_1]

end RoundTrip.V14_16
