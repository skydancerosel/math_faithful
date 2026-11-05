import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_8

open Matrix

namespace RoundTrip.V15_8

/-- The project's statement (universes instantiated at `0`): for any finite index types, if
`J_1, …, J_k` and `J'_1, …, J'_k` are anticommuting families, so is `J_α ⊕ J'_α`; and, for ANY
sequences `J, J'` (no hypothesis) and any `k` (including `k = 0`), `P ∈ Ω_k(n)`, `P' ∈ Ω_k(n')`
give `P ⊕ P' ∈ Ω_k(n + n')` for the structures `J_α ⊕ J'_α`. -/
def A : Prop :=
  type_of% @Morse.IsAnticommFamily.fromBlocks.{0, 0} ∧ type_of% @Morse.fromBlocks_mem_omega.{0, 0}

theorem A_holds : A := ⟨@Morse.IsAnticommFamily.fromBlocks.{0, 0}, @Morse.fromBlocks_mem_omega.{0, 0}⟩

/-! Vocabulary. -/

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

/-- `IsACFam F (k - 1)` and `F k ∈ Ω_k` give `IsACFam F k`. -/
theorem isACFam_succ {F : ℕ → Mat ι} {k : ℕ} (hk : 1 ≤ k) (h : IsACFam F (k - 1))
    (hk' : F k ∈ OmegaK F k) : IsACFam F k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hc, ha⟩ := hk'
  simp only [Nat.add_sub_cancel] at h
  refine ⟨fun α h1 h2 => ?_, fun α β h1 h2 h3 h4 hab => ?_⟩
  · rcases lt_or_eq_of_le h2 with hlt | rfl
    · exact h.1 α h1 (by omega)
    · exact hc
  · rcases lt_or_eq_of_le h2 with hlt | rfl
    · rcases lt_or_eq_of_le h4 with hlt' | rfl
      · exact h.2 α β h1 (by omega) h3 (by omega) hab
      · have := ha α h1 (by omega)
        unfold AntiComm at this ⊢
        rw [this, neg_neg]
    · rcases lt_or_eq_of_le h4 with hlt' | rfl
      · exact ha β h3 (by omega)
      · exact absurd rfl hab

end Vocab

/-- A ⇒ B. (0) is A's `IsAnticommFamily.fromBlocks` at `k - 1`; (1) is A's `fromBlocks_mem_omega`
with `P' = J'_k ∈ Ω_k(n')`; (2), the embedding, is not in A and is proved outright: `J ↦ J ⊕ J'_k`
is continuous with the continuous left inverse `M ↦ M₁₁`. -/
theorem A_to_B : A → B := by
  rintro ⟨hfb, hmem⟩
  intro n n' k Js Js' hk hJ hJ'
  have hJ'' := (isACFam_iff Js' k).1 hJ'
  refine ⟨?_, fun J hJk => ?_, ?_⟩
  · exact (isACFam_iff _ _).2 (hfb ((isACFam_iff Js _).1 hJ) (hJ''.mono (Nat.sub_le k 1)))
  · rw [omegaK_eq_omega] at hJk ⊢
    exact hmem hJk (hJ''.mem_omega hk)
  · have hf : Topology.IsEmbedding (fun J : Mat (Fin n) => dsum J (Js' k)) :=
      Function.LeftInverse.isEmbedding (f := fun M : Mat (Fin n ⊕ Fin n') => M.toBlocks₁₁)
        (fun J => by simp [dsum])
        (continuous_pi fun i => continuous_pi fun j =>
          (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i)))
        (by unfold dsum; fun_prop)
    exact hf.comp Topology.IsEmbedding.subtypeVal

section Transport
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem reindex_fromBlocks (e : ι ≃ Fin (Fintype.card ι)) (e' : κ ≃ Fin (Fintype.card κ))
    (X : Mat ι) (Y : Mat κ) :
    reindex (Equiv.sumCongr e e').symm (Equiv.sumCongr e e').symm
      (dsum (reindex e e X) (reindex e' e' Y)) = Matrix.fromBlocks X 0 0 Y := by
  ext (i | i) (j | j) <;> simp [dsum]

end Transport

/-- B ⇒ A. First conjunct from B, transported from `Fin` to arbitrary finite index types: B's (0)
gives the `J_α ⊕ J'_α`, `α < k`, and B's (1) at `J = J_k ∈ Ω_k(n)` gives that `J_k ⊕ J'_k` is a
complex structure anticommuting with them. Second conjunct outright (B cannot give it: it has no
hypothesis on the families, allows any `P' ∈ Ω_k(n')` rather than `J'_k`, and covers `k = 0`). -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro ι _ _ κ _ _ J J' k h h'
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨fun α h1 h2 => by omega, fun α β h1 h2 => by omega⟩
    set e := Fintype.equivFin ι
    set e' := Fintype.equivFin κ
    have hr := h.reindex e
    have hr' := h'.reindex e'
    obtain ⟨h0, h1, -⟩ := hB _ _ k (fun α => reindex e e (J α)) (fun α => reindex e' e' (J' α))
      hk ((isACFam_iff _ _).2 (hr.mono (Nat.sub_le k 1))) ((isACFam_iff _ _).2 hr')
    have hmemk : reindex e e (J k) ∈ OmegaK (fun α => reindex e e (J α)) k := by
      rw [omegaK_eq_omega]; exact hr.mem_omega hk
    have hF := (isACFam_iff _ _).1 (isACFam_succ hk h0 (h1 _ hmemk))
    have := hF.reindex (Equiv.sumCongr e e').symm
    simpa only [reindex_fromBlocks] using this
  · intro ι _ _ κ _ _ J J' k P P' hP hP'
    cases k with
    | zero =>
      change _ ∈ orthogonalGroup _ ℝ
      have h1 : Pᵀ * P = 1 := (mem_orthogonalGroup_iff' ι ℝ).1 hP
      have h2 : P'ᵀ * P' = 1 := (mem_orthogonalGroup_iff' κ ℝ).1 hP'
      rw [mem_orthogonalGroup_iff', fromBlocks_transpose, fromBlocks_multiply]
      simp [h1, h2, ← fromBlocks_one]
    | succ k =>
      obtain ⟨hc, ha⟩ := hP
      obtain ⟨hc', ha'⟩ := hP'
      have hT : Pᵀ = -P := by
        have := hc.1; rw [mem_orthogonalGroup_iff'] at this
        calc Pᵀ = Pᵀ * P * (-P) := by rw [Matrix.mul_neg, Matrix.mul_assoc, hc.2]; simp
          _ = -P := by rw [this, Matrix.one_mul]
      have hT' : P'ᵀ = -P' := by
        have := hc'.1; rw [mem_orthogonalGroup_iff'] at this
        calc P'ᵀ = P'ᵀ * P' * (-P') := by rw [Matrix.mul_neg, Matrix.mul_assoc, hc'.2]; simp
          _ = -P' := by rw [this, Matrix.one_mul]
      refine ⟨⟨?_, ?_⟩, fun α h1 h2 => ?_⟩
      · rw [mem_orthogonalGroup_iff', fromBlocks_transpose, fromBlocks_multiply]
        simp [hT, hT', hc.2, hc'.2, ← fromBlocks_one]
      · rw [fromBlocks_multiply]
        simp [hc.2, hc'.2, ← fromBlocks_one, fromBlocks_neg]
      · simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
          ha α h1 h2, ha' α h1 h2, fromBlocks_neg, neg_zero]

#rt_check RoundTrip.V15_8.A_to_B [Morse.IsAnticommFamily.fromBlocks, Morse.fromBlocks_mem_omega]
#rt_check RoundTrip.V15_8.B_to_A [Morse.IsAnticommFamily.fromBlocks, Morse.fromBlocks_mem_omega]
#rt_overlap RoundTrip.V15_8.B_to_A [Morse.IsAnticommFamily.fromBlocks, Morse.fromBlocks_mem_omega]

end RoundTrip.V15_8
