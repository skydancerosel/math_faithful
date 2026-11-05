import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_7

namespace RoundTrip.V14_7

/-- The project's statement (no universe parameters; `Morse.conjParams` is vocabulary): the set
`Morse.conjParams e` of conjugate parameters **in `(0,1)`** is finite for every `e`, and for
`e = (πd)²`, `d ≥ 1`, it is `{1/d, …, (d−1)/d}`, of cardinality `d − 1`. -/
def A : Prop :=
  type_of% @Morse.conjParams_finite ∧ type_of% @Morse.conjParams_sq ∧
    type_of% @Morse.ncard_conjParams_sq

theorem A_holds : A := ⟨Morse.conjParams_finite, Morse.conjParams_sq, Morse.ncard_conjParams_sq⟩

/-! ### Vocabulary: the project's `conjParams` is the blind one restricted to `(0,1)` -/

theorem conjParams_inter (e : ℝ) : conjParams e ∩ Set.Ioo 0 1 = Morse.conjParams e := by
  ext t
  simp only [conjParams, Morse.conjParams, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨ht0, he, s, rfl⟩, -, ht1⟩
    exact ⟨he, ht0, ht1, s, by ring⟩
  · rintro ⟨he, ht0, ht1, s, rfl⟩
    exact ⟨⟨ht0, he, s, by ring⟩, ht0, ht1⟩

/-- `B`'s first claim, outright: for `e > 0`, the positive integer multiples of `π/√e`. -/
theorem conjParams_pos (e : ℝ) (he : 0 < e) :
    conjParams e = {t | ∃ s : ℕ, 0 < s ∧ t = s * Real.pi / Real.sqrt e} := by
  have hse : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  ext t
  simp only [conjParams, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ht0, -, s, rfl⟩
    have hs : (0 : ℝ) < s := by
      have : 0 < (s : ℝ) * (Real.pi / Real.sqrt e) := ht0
      exact pos_of_mul_pos_left this (by positivity)
    have hs' : 0 < s := by exact_mod_cast hs
    refine ⟨s.toNat, by omega, ?_⟩
    have : ((s.toNat : ℕ) : ℝ) = (s : ℝ) := by
      have : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hs'.le
      exact_mod_cast this
    rw [this]; ring
  · rintro ⟨s, hs, rfl⟩
    refine ⟨by positivity, he, s, by push_cast; ring⟩

/-- The eigenvalue of a pair is `(π d)²` with `d = (k_j − k_l)/2`. -/
theorem pair_eigen (a b x : ℤ) (h : a - b = 2 * x) :
    Real.pi ^ 2 / 4 * ((a : ℝ) - b) ^ 2 = (Real.pi * x) ^ 2 := by
  have : (a : ℝ) - b = 2 * x := by exact_mod_cast h
  rw [this]; ring

theorem A_to_B : A → B := by
  rintro ⟨-, -, hA3⟩
  refine ⟨conjParams_pos, fun n k hk _ j l hlt => ⟨?_, ?_⟩⟩
  · -- the conjugate parameters `2s/(k_j − k_l)`
    obtain ⟨x, hx⟩ := hk j
    obtain ⟨y, hy⟩ := hk l
    have hd : (0 : ℝ) < (k j : ℝ) - k l := by
      have : ((k l : ℤ) : ℝ) < (k j : ℝ) := by exact_mod_cast hlt
      linarith
    have he : 0 < Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2 := by positivity
    rw [conjParams_pos _ he]
    have hsq : Real.sqrt (Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2) =
        Real.pi * ((k j : ℝ) - k l) / 2 := by
      rw [show Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2 = (Real.pi * ((k j : ℝ) - k l) / 2) ^ 2
        by ring]
      exact Real.sqrt_sq (by positivity)
    ext t
    simp only [Set.mem_ofPred_eq, hsq]
    refine exists_congr fun s => and_congr_right fun _ => ?_
    rw [show (s : ℝ) * Real.pi / (Real.pi * ((k j : ℝ) - k l) / 2) = 2 * s / ((k j : ℝ) - k l) by
      field_simp]
  · -- the count, from the project's `ncard_conjParams_sq`
    obtain ⟨x, hx⟩ := hk j
    obtain ⟨y, hy⟩ := hk l
    set d : ℕ := (x - y).toNat with hd
    have hd' : (d : ℤ) = x - y := Int.toNat_of_nonneg (by omega)
    have hd0 : 0 < d := by omega
    rw [conjParams_inter, pair_eigen (k j) (k l) d (by omega)]
    have := hA3 d hd0
    rw [show ((d : ℤ) : ℝ) = (d : ℝ) by norm_cast, this]
    push_cast [Nat.one_le_iff_ne_zero.2 hd0.ne']
    omega

/-- `k = (1, 1 − 2d, 1, 2d − 3)`: odd, of sum `0`, with `k_0 − k_1 = 2d`. -/
def kd (d : ℤ) : Fin 4 → ℤ := ![1, 1 - 2 * d, 1, 2 * d - 3]

theorem B_to_A : B → A := by
  rintro ⟨hB1, hB2⟩
  refine ⟨fun e => ?_, fun d hd => ?_, fun d hd => ?_⟩
  · -- finiteness: by `B`'s description, a subset of `{sπ/√e : s < ⌈√e/π⌉ + 1}`
    rcases le_or_gt e 0 with he | he
    · have : Morse.conjParams e = ∅ :=
        Set.eq_empty_of_forall_notMem fun t ht => not_lt.2 he ht.1
      rw [this]; exact Set.finite_empty
    · rw [← conjParams_inter, hB1 e he]
      have hse : 0 < Real.sqrt e := Real.sqrt_pos.2 he
      refine ((Finset.range (⌈Real.sqrt e / Real.pi⌉₊ + 1)).image
        fun s : ℕ => (s : ℝ) * Real.pi / Real.sqrt e).finite_toSet.subset ?_
      rintro t ⟨⟨s, -, rfl⟩, -, ht1⟩
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
      refine ⟨s, ?_, rfl⟩
      rw [div_lt_one hse] at ht1
      have : (s : ℝ) < Real.sqrt e / Real.pi := by
        rw [lt_div_iff₀ Real.pi_pos]; linarith
      have := this.trans_le (Nat.le_ceil _)
      have : s < ⌈Real.sqrt e / Real.pi⌉₊ := by exact_mod_cast this
      omega
  · -- `conjParams ((πd)²) = {s/d : 0 < s < d}`, from `B`'s description
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hpd : 0 < Real.pi * d := mul_pos Real.pi_pos hdR
    rw [← conjParams_inter, hB1 _ (by positivity), Real.sqrt_sq hpd.le]
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo, Finset.coe_image,
      Finset.coe_Ioo, Set.mem_image]
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, -, ht1⟩
      have e1 : (s : ℝ) * Real.pi / (Real.pi * d) = s / d := by field_simp
      rw [e1] at ht1 ⊢
      rw [div_lt_one hdR] at ht1
      exact ⟨s, ⟨hs, by exact_mod_cast ht1⟩, rfl⟩
    · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
      refine ⟨⟨s, hs0, by field_simp⟩, by positivity, ?_⟩
      rw [div_lt_one hdR]; exact_mod_cast hs1
  · -- the count, from `B`'s claim (iii) for `k = (1, 1 − 2d, 1, 2d − 3)`, `j = 0`, `l = 1`
    have hodd : ∀ i, Odd (kd d i) := by
      intro i
      fin_cases i <;> simp [kd]
      · exact ⟨-d, by ring⟩
      · exact ⟨d - 2, by ring⟩
    have hsum : ∑ i, kd d i = 0 := by simp [kd, Fin.sum_univ_four]; ring
    have hlt : kd d 1 < kd d 0 := by simp [kd]; omega
    have h := (hB2 4 (kd d) hodd hsum 0 1 hlt).2
    rw [conjParams_inter, pair_eigen (kd d 0) (kd d 1) d (by simp [kd])] at h
    simp only [kd, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [show ((d : ℤ) : ℝ) = (d : ℝ) by norm_cast] at h
    have : (1 - (1 - 2 * (d : ℤ))) / 2 - 1 = (d : ℤ) - 1 := by omega
    rw [this] at h
    omega

#rt_check RoundTrip.V14_7.A_to_B [Morse.conjParams_finite, Morse.conjParams_sq, Morse.ncard_conjParams_sq]
#rt_check RoundTrip.V14_7.B_to_A [Morse.conjParams_finite, Morse.conjParams_sq, Morse.ncard_conjParams_sq]
#rt_overlap RoundTrip.V14_7.B_to_A [Morse.conjParams_finite, Morse.conjParams_sq, Morse.ncard_conjParams_sq]
#rt_overlap RoundTrip.V14_7.A_to_B [Morse.conjParams_finite, Morse.conjParams_sq, Morse.ncard_conjParams_sq]

end RoundTrip.V14_7
