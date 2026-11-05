import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_8

namespace RoundTrip.V3_8

/-- The project's statement (Lemma 5.1 and Milnor's induction), universe instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.IsSubadditive.le_sum.{0}) ∧ (type_of% @Morse.IsAdditive.eq_sum.{0}) ∧
    (type_of% @Morse.le_sum_of_chain.{0})

theorem A_holds : A :=
  ⟨@Morse.IsSubadditive.le_sum.{0}, @Morse.IsAdditive.eq_sum.{0}, @Morse.le_sum_of_chain.{0}⟩

/-- `B` is false: for `n = 0` it claims `S(X₀, X₀) ≤ 0` (empty sum) for every subadditive `S`,
but `S ≡ 1` is subadditive (`1 ≤ 1 + 1`). -/
theorem not_B : ¬ B := by
  intro hB
  have h := (hB Unit (fun _ _ => True) (fun _ _ => 1) (fun _ => ∅) 0
    (fun _ _ _ _ => subset_rfl) (fun _ _ _ _ => trivial)).1
    (fun _ _ _ _ _ _ _ _ => by norm_num)
  simp at h

/-- With `B` false, `B → A` is vacuous. -/
theorem B_to_A : B → A := fun hB => absurd hB not_B

/-- `B` for chains of positive length (`0 < n`), the case Milnor means. -/
def Bpos : Prop :=
  ∀ (α : Type) (dom : Set α → Set α → Prop) (S : Set α → Set α → ℤ) (X : ℕ → Set α) (n : ℕ),
    0 < n →
    (∀ i j, i ≤ j → j ≤ n → X i ⊆ X j) → (∀ i j, i ≤ j → j ≤ n → dom (X j) (X i)) →
    (Subadditive dom S → S (X n) (X 0) ≤ ∑ i ∈ Finset.Icc 1 n, S (X i) (X (i - 1))) ∧
    (Additive dom S → S (X n) (X 0) = ∑ i ∈ Finset.Icc 1 n, S (X i) (X (i - 1))) ∧
    (X 0 = ∅ → Subadditive dom S → S (X n) ∅ ≤ ∑ i ∈ Finset.Icc 1 n, S (X i) (X (i - 1)))

/-- `B` is exactly `Bpos` plus the false `n = 0` case. -/
theorem B_iff : B ↔ Bpos ∧
    ∀ (α : Type) (dom : Set α → Set α → Prop) (S : Set α → Set α → ℤ) (X : ℕ → Set α),
      (∀ i j, i ≤ j → j ≤ 0 → X i ⊆ X j) → (∀ i j, i ≤ j → j ≤ 0 → dom (X j) (X i)) →
      (Subadditive dom S → S (X 0) (X 0) ≤ 0) ∧ (Additive dom S → S (X 0) (X 0) = 0) ∧
      (X 0 = ∅ → Subadditive dom S → S (X 0) ∅ ≤ 0) := by
  constructor
  · intro hB
    exact ⟨fun α dom S X n _ h1 h2 => hB α dom S X n h1 h2, fun α dom S X h1 h2 => by
      simpa using hB α dom S X 0 h1 h2⟩
  · rintro ⟨hP, h0⟩ α dom S X n h1 h2
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using h0 α dom S X h1 h2
    · exact hP α dom S X n hn h1 h2

theorem sum_Icc_eq_sum_range (g : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, g i = ∑ k ∈ Finset.range n, g (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem A_to_Bpos : A → Bpos := by
  intro hA α dom S X n hn hX hdom
  have chain := @hA.2.2 (Set α)
  have key : ∀ T : Set α → Set α → ℤ,
      (∀ m, 0 < m → m < n → T (X (m + 1)) (X 0) ≤ T (X m) (X 0) + T (X (m + 1)) (X m)) →
      T (X n) (X 0) ≤ ∑ i ∈ Finset.Icc 1 n, T (X i) (X (i - 1)) := by
    intro T hT
    rw [sum_Icc_eq_sum_range]
    exact chain (fun a b => T b a) X hn hT
  have hsub : Subadditive dom S →
      S (X n) (X 0) ≤ ∑ i ∈ Finset.Icc 1 n, S (X i) (X (i - 1)) := by
    intro h
    refine key S fun m hm hmn => ?_
    have := h (X (m + 1)) (X m) (X 0) (hX 0 m (by omega) (by omega))
      (hX m (m + 1) (by omega) (by omega)) (hdom 0 (m + 1) (by omega) (by omega))
      (hdom m (m + 1) (by omega) (by omega)) (hdom 0 m (by omega) (by omega))
    linarith
  refine ⟨hsub, fun h => le_antisymm (hsub fun X Y Z a b c d e => (h X Y Z a b c d e).le) ?_,
    fun h0 h => h0 ▸ hsub h⟩
  have := key (fun a b => -S a b) fun m hm hmn => by
    have := h (X (m + 1)) (X m) (X 0) (hX 0 m (by omega) (by omega))
      (hX m (m + 1) (by omega) (by omega)) (hdom 0 (m + 1) (by omega) (by omega))
      (hdom m (m + 1) (by omega) (by omega)) (hdom 0 m (by omega) (by omega))
    linarith
  simp only [Finset.sum_neg_distrib] at this
  linarith


/-! ### `Bpos ⇒ A`: Lemma 5.1 for chains of positive length gives back all three statements of `A`,
including Milnor's induction `le_sum_of_chain`, whose hypothesis (subadditivity only on the triples
`X₀ ⊆ X_m ⊆ X_{m+1}`) is weaker than subadditivity: the missing values of `S` are chosen so that
subadditivity holds on the whole chain. -/

/-- The index of a set `Iic i ⊆ ℕ`. -/
noncomputable def idx (P : Set ℕ) : ℕ :=
  open Classical in if h : ∃ i, P = Set.Iic i then h.choose else 0

theorem idx_Iic (i : ℕ) : idx (Set.Iic i) = i := by
  have h : ∃ j, Set.Iic i = Set.Iic j := ⟨i, rfl⟩
  rw [idx, dif_pos h]
  exact (Set.Iic_inj.1 h.choose_spec).symm

/-- `Bpos` for a chain indexed by `0, …, n` given by its values `w i j = S(X_j, X_i)`. -/
theorem transfer (hB : Bpos) (w : ℕ → ℕ → ℤ) {n : ℕ} (hn : 0 < n) :
    ((∀ a b c, a ≤ b → b ≤ c → c ≤ n → w a c ≤ w a b + w b c) →
      w 0 n ≤ ∑ k ∈ Finset.range n, w k (k + 1)) ∧
    ((∀ a b c, a ≤ b → b ≤ c → c ≤ n → w a c = w a b + w b c) →
      w 0 n = ∑ k ∈ Finset.range n, w k (k + 1)) := by
  let dom : Set ℕ → Set ℕ → Prop := fun P Q => ∃ i j, i ≤ n ∧ j ≤ n ∧ P = Set.Iic j ∧ Q = Set.Iic i
  let S : Set ℕ → Set ℕ → ℤ := fun P Q => w (idx Q) (idx P)
  have h := hB ℕ dom S (fun i => Set.Iic i) n hn (fun i j hij _ => Set.Iic_subset_Iic.2 hij)
    (fun i j hij hjn => ⟨i, j, by omega, hjn, rfl, rfl⟩)
  simp only [S, idx_Iic, sum_Icc_eq_sum_range, Nat.add_sub_cancel] at h
  -- reduce `Subadditive dom S` to the chain inequality
  have red : ∀ (R : ℤ → ℤ → Prop), (∀ a b c, a ≤ b → b ≤ c → c ≤ n → R (w a c) (w a b + w b c)) →
      ∀ X Y Z : Set ℕ, Z ⊆ Y → Y ⊆ X → dom X Z → dom X Y → dom Y Z →
        R (S X Z) (S X Y + S Y Z) := by
    rintro R hR X Y Z hZY hYX ⟨a, c, -, hc, rfl, rfl⟩ ⟨b, c', -, -, hc', rfl⟩ -
    obtain rfl : c = c' := Set.Iic_inj.1 hc'
    simp only [S, idx_Iic]
    rw [add_comm]
    exact hR a b c (Set.Iic_subset_Iic.1 hZY) (Set.Iic_subset_Iic.1 hYX) hc
  exact ⟨fun hw => h.1 (red (· ≤ ·) hw), fun hw => h.2.1 (red (· = ·) hw)⟩

theorem Bpos_to_A : Bpos → A := by
  intro hB
  refine ⟨fun {ι} _ {S} hS {X} {n} hX hn => ?_, fun {ι} _ {S} hS {X} {n} hX hn => ?_,
    fun {ι} S X {n} hn hS => ?_⟩
  · exact (transfer hB (fun i j => S (X i) (X j)) hn).1 fun a b c hab hbc hcn =>
      hS (Morse.chain_le hX hab (hbc.trans hcn)) (Morse.chain_le hX hbc hcn)
  · exact (transfer hB (fun i j => S (X i) (X j)) hn).2 fun a b c hab hbc hcn =>
      hS (Morse.chain_le hX hab (hbc.trans hcn)) (Morse.chain_le hX hbc hcn)
  · -- `t c = S(X₀, X_c)`, `s a = S(X_a, X_{a+1})`; other values: `t c - t a`
    let w : ℕ → ℕ → ℤ := fun a c =>
      if a = 0 then (if c = 0 then 0 else S (X 0) (X c))
      else if c = a then 0
      else if c = a + 1 then S (X a) (X (a + 1))
      else S (X 0) (X c) - S (X 0) (X a)
    have h := (transfer hB w hn).1 ?_
    · have e1 : w 0 n = S (X 0) (X n) := by simp only [w]; simp [hn.ne']
      have e2 : ∀ k, w k (k + 1) = S (X k) (X (k + 1)) := by
        intro k
        simp only [w]
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp
        · simp [hk.ne']
      rw [e1] at h
      simpa only [e2] using h
    · intro a b c hab hbc hcn
      simp only [w]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rcases Nat.eq_zero_or_pos b with rfl | hb
        · simp
        · rcases Nat.eq_zero_or_pos c with rfl | hc
          · omega
          · simp only [if_true, hb.ne', hc.ne', if_false]
            by_cases hcb : c = b
            · subst hcb; simp
            · by_cases hcb1 : c = b + 1
              · subst hcb1; simp only [if_false, if_true, hcb]; exact hS b hb (by omega)
              · simp only [hcb, hcb1, if_false]; linarith
      · simp only [ha.ne', (show b ≠ 0 by omega), (show c ≠ 0 by omega), if_false]
        by_cases hba : b = a
        · subst hba; simp
        by_cases hcb : c = b
        · subst hcb; simp
        have hca : c ≠ a := by omega
        have hca1 : c ≠ a + 1 := by omega
        simp only [hba, hcb, hca, hca1, if_false]
        by_cases hba1 : b = a + 1
        · subst hba1
          by_cases hcb1 : c = a + 1 + 1
          · subst hcb1; simp only [if_true]
            have := hS (a + 1) (by omega) (by omega)
            have := hS a ha (by omega)
            linarith
          · simp only [hcb1, if_false, if_true]
            have := hS a ha (by omega)
            linarith
        · simp only [hba1, if_false]
          by_cases hcb1 : c = b + 1
          · subst hcb1; simp only [if_true]
            have := hS b (by omega) (by omega)
            linarith
          · simp only [hcb1, if_false]; linarith

#rt_check RoundTrip.V3_8.Bpos_to_A [Morse.IsSubadditive.le_sum, Morse.IsAdditive.eq_sum,
  Morse.le_sum_of_chain]
#rt_check RoundTrip.V3_8.B_to_A [Morse.IsSubadditive.le_sum, Morse.IsAdditive.eq_sum,
  Morse.le_sum_of_chain]
#rt_check RoundTrip.V3_8.A_to_Bpos [Morse.IsSubadditive.le_sum, Morse.IsAdditive.eq_sum,
  Morse.le_sum_of_chain]
#rt_overlap RoundTrip.V3_8.B_to_A [Morse.IsSubadditive.le_sum, Morse.IsAdditive.eq_sum,
  Morse.le_sum_of_chain]

#rt_overlap RoundTrip.V3_8.Bpos_to_A [Morse.IsSubadditive.le_sum, Morse.IsAdditive.eq_sum,
  Morse.le_sum_of_chain]

end RoundTrip.V3_8
