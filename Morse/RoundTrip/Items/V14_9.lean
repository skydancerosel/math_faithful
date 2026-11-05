import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_9

open Finset

namespace RoundTrip.V14_9

/-- The project's statement (universe of `ι` instantiated at `0`; `Morse.bottIndex`,
`Morse.pairSpectrum`, `Morse.suSpectrum` are vocabulary): for odd `b < a`, twice the number of
conjugate parameters in `(0,1)` of `π²(a − b)²/4` is `a − b − 2`; and for any finite index type
and odd `k` (no condition on `Σ k_i`), the index of Milnor's spectrum `suSpectrum k`
(`π²(k_i − k_j)²/4`, `k_i > k_j`, each twice) is `bottIndex k`. -/
def A : Prop :=
  type_of% @Morse.two_mul_ncard_conjParams ∧ type_of% @Morse.spectralIndex_suSpectrum.{0}

theorem A_holds : A := ⟨@Morse.two_mul_ncard_conjParams, @Morse.spectralIndex_suSpectrum.{0}⟩

/-! ### Vocabulary -/

theorem conjParams_inter (e : ℝ) : conjParams e ∩ Set.Ioo 0 1 = Morse.conjParams e := by
  ext t
  simp only [conjParams, Morse.conjParams, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨ht0, he, s, rfl⟩, -, ht1⟩
    exact ⟨he, ht0, ht1, s, by ring⟩
  · rintro ⟨he, ht0, ht1, s, rfl⟩
    exact ⟨⟨ht0, he, s, by ring⟩, ht0, ht1⟩

theorem mem_conjParams_iff {e t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    t ∈ conjParams e ↔ t ∈ Morse.conjParams e := by
  rw [← conjParams_inter]
  exact ⟨fun h => ⟨h, ht⟩, fun h => h.1⟩

/-- For `0 < t < 1` the blind multiplicity is the project's `conjMult`. -/
theorem specMult_eq {κ : Type} [Fintype κ] (e : κ → ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    specMult e t = Morse.conjMult e t := by
  classical
  rw [specMult, Morse.conjMult]
  have : {i | t ∈ conjParams (e i)} =
      ((Finset.univ.filter fun i => t ∈ Morse.conjParams (e i) : Finset κ) : Set κ) := by
    ext i
    simp [mem_conjParams_iff ht]
  rw [this, Set.ncard_coe_finset]

theorem specIndex_eq_spectralIndex {κ : Type} [Fintype κ] (e : κ → ℝ) :
    specIndex e = Morse.spectralIndex e := by
  classical
  rw [specIndex, Morse.spectralIndex, finsum_mem_def]
  congr 1
  funext t
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem ht, specMult_eq e ht]
  · rw [Set.indicator_of_notMem ht, Morse.conjMult]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    exact ht ⟨hi.2.1, hi.2.2.1⟩

theorem bottFormula_eq {n : ℕ} (k : Fin n → ℤ) : bottFormula k = Morse.bottIndex k := by
  rw [bottFormula, Morse.bottIndex, Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]

theorem milnorA_eq_suDiag {n : ℕ} (k : Fin n → ℤ) : milnorA k = Morse.suDiag k := by
  unfold milnorA diagI Morse.suDiag
  congr 1
  funext j
  push_cast
  rfl

theorem Kop_eq_jacobiMat {n : ℕ} (A W : Mat n) : Kop A W = Morse.jacobiMat A W := by
  unfold Kop Morse.jacobiMat
  rw [← Complex.coe_smul]
  push_cast
  rfl

theorem ncard_conjParams_zero : (Morse.conjParams 0).ncard = 0 := by
  have : Morse.conjParams 0 = ∅ := Set.eq_empty_of_forall_notMem fun t ht => lt_irrefl _ ht.1
  rw [this, Set.ncard_empty]

/-! ### Milnor's list of pairs `j < l` versus the ordered pairs `k_j > k_l` -/

/-- A symmetric function vanishing when `k_j = k_l` has the same sum over the pairs `j < l` and
over the ordered pairs with `k_j > k_l`. -/
theorem sum_pairs_eq {n : ℕ} (k : Fin n → ℤ) (g : Fin n → Fin n → ℕ)
    (hsym : ∀ j l, g j l = g l j) (h0 : ∀ j l, k j = k l → g j l = 0) :
    ∑ p : Pairs n, g p.1.1 p.1.2 = ∑ p : {p : Fin n × Fin n // k p.2 < k p.1}, g p.1.1 p.1.2 := by
  classical
  refine Finset.sum_bij_ne_zero
    (fun p _ hp => if h : k p.1.2 < k p.1.1 then ⟨p.1, h⟩ else
      ⟨p.1.swap, lt_of_le_of_ne (not_lt.1 h) fun heq => hp (h0 _ _ heq)⟩)
    (fun _ _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨⟨a1, a2⟩, ha⟩ _ _ ⟨⟨b1, b2⟩, hb⟩ _ _ hab
    change a1 < a2 at ha
    change b1 < b2 at hb
    apply Subtype.ext
    split_ifs at hab with h1 h2 h2 <;>
      simp only [Subtype.mk.injEq, Prod.mk.injEq, Prod.swap_prod_mk] at hab
    · exact Prod.ext hab.1 hab.2
    · obtain ⟨rfl, rfl⟩ := hab; exact absurd ha (lt_asymm hb)
    · obtain ⟨rfl, rfl⟩ := hab; exact absurd ha (lt_asymm hb)
    · exact Prod.ext hab.2 hab.1
  · rintro ⟨⟨b1, b2⟩, hb⟩ _ hne
    change k b2 < k b1 at hb
    have hne' : b1 ≠ b2 := fun h => by rw [h] at hb; exact lt_irrefl _ hb
    rcases lt_or_gt_of_ne hne' with h | h
    · exact ⟨⟨(b1, b2), h⟩, Finset.mem_univ _, hne, by simp [hb]⟩
    · refine ⟨⟨(b2, b1), h⟩, Finset.mem_univ _, by rw [hsym]; exact hne, ?_⟩
      simp [not_lt.2 hb.le]
  · rintro ⟨⟨a1, a2⟩, ha⟩ _ _
    simp only
    split_ifs with h
    · rfl
    · exact hsym _ _

/-! ### Eigenbases of `K_A` on `𝔰𝔲(n)` -/

section Eigen

variable {n : ℕ} (k : Fin n → ℤ)

/-- The eigenvalue `π²(k_j − k_l)²/4` attached to the entry `(j, l)`. -/
noncomputable def lam (j l : Fin n) : ℝ := Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2

theorem lam_symm (j l : Fin n) : lam k j l = lam k l j := by unfold lam; ring

theorem Kop_apply (W : Mat n) (j l : Fin n) :
    Kop (milnorA k) W j l = (lam k j l : ℂ) * W j l := by
  rw [Kop_eq_jacobiMat, milnorA_eq_suDiag, Morse.jacobiMat_suDiag_apply]
  rfl

/-- A non-zero entry `(j, l)` of an eigenvector of `K_A` forces its eigenvalue to be `λ_{jl}`. -/
theorem eigen_entry {W : Mat n} {μ : ℝ} (h : Kop (milnorA k) W = μ • W) {j l : Fin n}
    (hW : W j l ≠ 0) : μ = lam k j l := by
  have h1 := congrFun (congrFun h j) l
  rw [Kop_apply, Matrix.smul_apply, Complex.real_smul] at h1
  have h2 := mul_right_cancel₀ hW h1
  exact_mod_cast h2.symm

theorem jacSin_zero_iff {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j l : Fin n) :
    Morse.jacSin ((Real.pi * k j - Real.pi * k l) / 2) t = 0 ↔
      t ∈ Morse.conjParams (lam k j l) := by
  rcases lt_trichotomy (k l) (k j) with h | h | h
  · exact Morse.jacSin_eq_zero_iff_mem_conjParams k h ht
  · have hl : lam k j l = 0 := by simp [lam, h]
    rw [hl, h, sub_self, zero_div, Morse.jacSin_of_eq_zero]
    constructor
    · intro h0; exact absurd h0 ht.1.ne'
    · intro hm; exact absurd hm.1 (lt_irrefl _)
  · rw [show (Real.pi * k j - Real.pi * k l) / 2 = -((Real.pi * k l - Real.pi * k j) / 2) by ring,
      Morse.jacSin_neg, lam_symm]
    exact Morse.jacSin_eq_zero_iff_mem_conjParams k h ht

/-- `W ∈ 𝔰𝔲(n)` lies in the project's `hadKer (πk) t` iff its non-zero entries all have `t` as a
conjugate parameter of their eigenvalue. -/
theorem mem_hadKer_iff {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {W : Mat n} (hW : W ∈ suAlg n) :
    W ∈ Morse.hadKer (fun j => Real.pi * k j) t ↔
      ∀ j l, W j l ≠ 0 → t ∈ Morse.conjParams (lam k j l) := by
  rw [Morse.mem_hadKer]
  have hW' : W ∈ Morse.specialSkewHermitian (Fin n) := hW
  simp only [hW', true_and]
  constructor
  · intro h j l hne
    have h1 := congrFun (congrFun h j) l
    simp only [Morse.hadSin_apply, Matrix.zero_apply] at h1
    rcases mul_eq_zero.1 h1 with h0 | h0
    · exact (jacSin_zero_iff k ht j l).1 (by exact_mod_cast h0)
    · exact absurd h0 hne
  · intro h
    ext j l
    simp only [Morse.hadSin_apply, Matrix.zero_apply]
    by_cases hne : W j l = 0
    · rw [hne, mul_zero]
    · rw [(jacSin_zero_iff k ht j l).2 (h j l hne), Complex.ofReal_zero, zero_mul]

/-- **The multiplicity count for an arbitrary eigenbasis**: the eigenvectors whose eigenvalue
has `t` as a conjugate parameter form a basis of `hadKer (πk) t`. -/
theorem card_eq_finrank {κ : Type} [Fintype κ] (b : κ → Mat n) (e : κ → ℝ)
    (hb : ∀ i, b i ∈ suAlg n) (hli : LinearIndependent ℝ b)
    (hspan : ∀ W ∈ suAlg n, W ∈ Submodule.span ℝ (Set.range b))
    (heig : ∀ i, Kop (milnorA k) (b i) = e i • b i) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    Nat.card {i // t ∈ Morse.conjParams (e i)} =
      Module.finrank ℝ (Morse.hadKer (fun j => Real.pi * k j) t) := by
  classical
  set bS : {i // t ∈ Morse.conjParams (e i)} → Mat n := fun i => b i.1
  have hliS : LinearIndependent ℝ bS := hli.comp _ Subtype.val_injective
  have hmemS : ∀ i, bS i ∈ Morse.hadKer (fun j => Real.pi * k j) t := by
    intro i
    rw [mem_hadKer_iff k ht (hb i.1)]
    intro j l hne
    rw [← eigen_entry k (heig i.1) hne]
    exact i.2
  have hspanEq : Submodule.span ℝ (Set.range bS) = Morse.hadKer (fun j => Real.pi * k j) t := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmemS i
    · intro W hW
      have hWsu : W ∈ suAlg n := hW.1
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan W hWsu)
      have hrest : ∑ i ∈ univ.filter (fun i => ¬ t ∈ Morse.conjParams (e i)), c i • b i = 0 := by
        ext j l
        rw [Matrix.sum_apply, Matrix.zero_apply]
        by_cases hP : t ∈ Morse.conjParams (lam k j l)
        · refine Finset.sum_eq_zero fun i hi => ?_
          rw [Matrix.smul_apply]
          by_cases hne : b i j l = 0
          · rw [hne, smul_zero]
          · exact absurd (by rw [eigen_entry k (heig i) hne]; exact hP) (mem_filter.1 hi).2
        · have hWjl : W j l = 0 := by
            by_contra hne
            exact hP ((mem_hadKer_iff k ht hWsu).1 hW j l hne)
          have hSjl : ∀ i, t ∈ Morse.conjParams (e i) → b i j l = 0 := by
            intro i hi
            by_contra hne
            rw [eigen_entry k (heig i) hne] at hi
            exact hP hi
          have h1 := congrFun (congrFun hc j) l
          rw [Matrix.sum_apply, hWjl,
            ← Finset.sum_filter_add_sum_filter_not univ (fun i => t ∈ Morse.conjParams (e i))]
            at h1
          have h2 : ∑ i ∈ univ.filter (fun i => t ∈ Morse.conjParams (e i)), (c i • b i) j l = 0 :=
            Finset.sum_eq_zero fun i hi => by
              rw [Matrix.smul_apply, hSjl i (mem_filter.1 hi).2, smul_zero]
          rw [h2, zero_add] at h1
          exact h1
      have hW' : W = ∑ i ∈ univ.filter (fun i => t ∈ Morse.conjParams (e i)), c i • b i := by
        rw [← hc, ← Finset.sum_filter_add_sum_filter_not univ
          (fun i => t ∈ Morse.conjParams (e i)), hrest, add_zero]
      rw [hW']
      exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨i, (mem_filter.1 hi).2⟩, rfl⟩)
  rw [← hspanEq, finrank_span_eq_card hliS, Nat.card_eq_fintype_card]

/-- Hence the multiplicity of `t` for any eigenbasis is the one for Milnor's spectrum. -/
theorem specMult_eigenbasis {κ : Type} [Fintype κ] (b : κ → Mat n) (e : κ → ℝ)
    (hb : ∀ i, b i ∈ suAlg n) (hli : LinearIndependent ℝ b)
    (hspan : ∀ W ∈ suAlg n, W ∈ Submodule.span ℝ (Set.range b))
    (heig : ∀ i, Kop (milnorA k) (b i) = e i • b i) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    specMult e t = specMult (Morse.suSpectrum k) t := by
  classical
  rw [specMult_eq e ht, specMult_eq (Morse.suSpectrum k) ht, ← Morse.finrank_hadKer k ht,
    ← card_eq_finrank k b e hb hli hspan heig ht, Morse.conjMult, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

end Eigen

theorem A_to_B : A → B := by
  rintro ⟨hA1, hA2⟩ n k hk _
  have hsu : (specIndex (Morse.suSpectrum k) : ℤ) = bottFormula k := by
    rw [specIndex_eq_spectralIndex, bottFormula_eq]
    exact hA2 hk
  refine ⟨fun j l hlt => ?_, ?_, fun κ _ b e hb hli hspan heig => ?_⟩
  · rw [conjParams_inter]
    exact hA1 (hk j) (hk l) hlt
  · rw [← hsu, specIndex_eq_spectralIndex, specIndex_eq_spectralIndex,
      Morse.spectralIndex_eq, Morse.spectralIndex_eq]
    congr 1
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [milnorSpec, Morse.suSpectrum, Morse.pairSpectrum, Fin.sum_univ_two,
      ncard_conjParams_zero, Finset.sum_const_zero, add_zero]
    exact sum_pairs_eq k (fun j l => (Morse.conjParams (lam k j l)).ncard +
        (Morse.conjParams (lam k j l)).ncard)
      (fun j l => by simp only [lam_symm k j l])
      (fun j l h => by simp [lam, h, ncard_conjParams_zero])
  · rw [← hsu, specIndex, specIndex]
    congr 1
    exact finsum_mem_congr rfl fun t ht => specMult_eigenbasis k b e hb hli hspan heig ht

/-- `k = (a, b, 1, −(a + b) − 1)`: odd, of sum `0`. -/
def kab (a b : ℤ) : Fin 4 → ℤ := ![a, b, 1, -(a + b) - 1]

theorem B_to_A : B → A := by
  intro hB
  have h2 : ∀ {a b : ℤ}, Odd a → Odd b → b < a →
      2 * ((Morse.conjParams (Real.pi ^ 2 / 4 * ((a : ℝ) - b) ^ 2)).ncard : ℤ) = a - b - 2 := by
    intro a b ha hb hlt
    have hodd : ∀ i, Odd (kab a b i) := by
      intro i
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      fin_cases i <;> simp [kab]
      · exact ⟨x, hx⟩
      · exact ⟨y, hy⟩
      · exact ⟨-(x + y) - 1, by rw [hx, hy]; ring⟩
    have hsum : ∑ i, kab a b i = 0 := by simp [kab, Fin.sum_univ_four]
    have h := (hB 4 (kab a b) hodd hsum).1 0 1 (by simpa [kab] using hlt)
    rw [conjParams_inter] at h
    simpa [kab] using h
  refine ⟨@h2, fun {ι} _ k hk => ?_⟩
  rw [Morse.spectralIndex_eq, Morse.bottIndex_eq_sum_subtype, Fintype.sum_prod_type,
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Morse.suSpectrum, Morse.pairSpectrum, Fin.sum_univ_two, Nat.cast_add]
  rw [← two_mul]
  exact h2 (hk _) (hk _) p.2

#rt_check RoundTrip.V14_9.A_to_B [Morse.two_mul_ncard_conjParams, Morse.spectralIndex_suSpectrum]
#rt_check RoundTrip.V14_9.B_to_A [Morse.two_mul_ncard_conjParams, Morse.spectralIndex_suSpectrum]
#rt_overlap RoundTrip.V14_9.B_to_A [Morse.two_mul_ncard_conjParams, Morse.spectralIndex_suSpectrum]
#rt_overlap RoundTrip.V14_9.A_to_B [Morse.two_mul_ncard_conjParams, Morse.spectralIndex_suSpectrum]

end RoundTrip.V14_9
