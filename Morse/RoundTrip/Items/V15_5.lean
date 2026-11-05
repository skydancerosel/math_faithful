import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_5

open Matrix

namespace RoundTrip.V15_5

/-- The project's statement (universe instantiated at `0`): for an arbitrary sequence `J` and
`k ≥ 0`, `P, J' ∈ Ω_{k+1}(n)` ⇒ `-(P J' P) ∈ Ω_{k+1}(n)` (`-(PJ'P) = P J'⁻¹ P` for a complex
structure `J'`). -/
def A : Prop := type_of% @Morse.reflection_mem_omega.{0}

theorem A_holds : A := @Morse.reflection_mem_omega.{0}

/-! Vocabulary. -/

theorem omegaK_eq_omega {ι : Type} [Fintype ι] [DecidableEq ι] (Js : ℕ → Mat ι) (k : ℕ) :
    OmegaK Js k = Morse.Omega Js k := by
  cases k with
  | zero => rfl
  | succ k =>
    ext J
    simp only [OmegaK, Morse.Omega, IsCplxStr, Morse.IsComplexStructure, AntiComm,
      Set.mem_ofPred_eq]
    refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun _ =>
      ⟨fun h => by rw [h, neg_neg], fun h => by rw [h, neg_neg]⟩)

theorem isACFam_zero {ι : Type} [Fintype ι] [DecidableEq ι] (Js : ℕ → Mat ι) : IsACFam Js 0 :=
  ⟨fun α h1 h2 => absurd h2 (by omega), fun α _ h1 h2 _ _ _ => absurd h2 (by omega)⟩

/-- For a complex structure, `X⁻¹ = -X`; so Milnor's reflection `p X⁻¹ p` is `-(p X p)`. -/
theorem inv_eq_neg {ι : Type} [Fintype ι] [DecidableEq ι] {X : Mat ι} (hX : X * X = -1) :
    X⁻¹ = -X :=
  Matrix.inv_eq_right_inv (by rw [Matrix.mul_neg, hX, neg_neg])

theorem reflO_eq {ι : Type} [Fintype ι] [DecidableEq ι] {p X : Mat ι} (hX : X * X = -1) :
    reflO p X = -(p * X * p) := by
  rw [reflO, inv_eq_neg hX, Matrix.mul_neg, Matrix.neg_mul]

section Reindex
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem reindex_mul' (e : ι ≃ κ) (X Y : Mat ι) :
    reindex e e (X * Y) = reindex e e X * reindex e e Y := by
  simpa only [coe_reindexAlgEquiv] using map_mul (reindexAlgEquiv ℝ ℝ e) X Y

theorem reindex_isCS (e : ι ≃ κ) {J : Mat ι} (hJ : Morse.IsComplexStructure J) :
    Morse.IsComplexStructure (reindex e e J) := by
  obtain ⟨hO, hJ2⟩ := hJ
  rw [mem_orthogonalGroup_iff'] at hO
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff', transpose_reindex, ← reindex_mul', hO]
    ext i j
    simp [one_apply]
  · rw [← reindex_mul', hJ2]
    ext i j
    simp [one_apply]

end Reindex

/-- A ⇒ B, first conjunct: the reflection `p X⁻¹ p` preserves `Ω_k(n)`. For `k ≥ 1` this is A
(`X⁻¹ = -X`); for `k = 0` (`Ω_0 = O(n)`, not covered by A) it is closure of `O(n)` under products
and inverses (outright). -/
theorem A_to_B1 (hA : A) :
    ∀ (n k : ℕ) (Js : ℕ → Mat (Fin n)), IsACFam Js (k - 1) →
      ∀ p ∈ OmegaK Js k, ∀ X ∈ OmegaK Js k, reflO p X ∈ OmegaK Js k := by
  intro n k Js _ p hp X hX
  cases k with
  | zero =>
    have hX' := hX
    rw [OmegaK, Orth, SetLike.mem_coe, mem_orthogonalGroup_iff'] at hX'
    have hinv : X⁻¹ = Xᵀ := Matrix.inv_eq_left_inv hX'
    have hXT : Xᵀ ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
      rw [mem_orthogonalGroup_iff', transpose_transpose]
      exact mul_eq_one_comm.1 hX'
    rw [reflO, hinv]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hp hXT) hp
  | succ k =>
    rw [omegaK_eq_omega] at hp hX ⊢
    rw [reflO_eq hX.1.2]
    exact hA hp hX

/-- B ⇒ A. The complex-structure part: B at `k = 1` (no anticommutation hypothesis) on
`Fin (card ι)`, transported along a reindexing, with `p X⁻¹ p = -(p X p)`. The anticommutation
with `J_1, …, J_k` is checked by hand (word algebra): A holds for an arbitrary sequence `J`, while B
assumes `J_1, …, J_{k-1}` anticommuting complex structures, so B cannot be applied at `k ≥ 2` for
a general `J`. -/
theorem B_to_A : B → A := by
  intro hB ι _ _ J k P J' hP hJ'
  obtain ⟨hPc, hPa⟩ := hP
  obtain ⟨hc, ha⟩ := hJ'
  refine ⟨?_, fun α h1 h2 => ?_⟩
  · set e := Fintype.equivFin ι
    have h := (hB (Fintype.card ι) 1 (fun _ => 0) (isACFam_zero _)).1 (reindex e e P)
      (by rw [omegaK_eq_omega]; exact ⟨reindex_isCS e hPc, fun α h1 h2 =>
        (Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le h1 h2)).elim⟩)
      (reindex e e J')
      (by rw [omegaK_eq_omega]; exact ⟨reindex_isCS e hc, fun α h1 h2 =>
        (Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le h1 h2)).elim⟩)
    rw [omegaK_eq_omega] at h
    have hcs := reindex_isCS e.symm h.1
    rw [reflO_eq (reindex_isCS e hc).2, ← reindex_mul', ← reindex_mul'] at hcs
    have hneg : reindex e.symm e.symm (-reindex e e (P * J' * P)) = -(P * J' * P) := by
      ext i j; simp
    rwa [hneg] at hcs
  · have h3 := hPa α h1 h2
    have h4 := ha α h1 h2
    word_simp [h3, h4]

#rt_check RoundTrip.V15_5.A_to_B1 [Morse.reflection_mem_omega]
#rt_check RoundTrip.V15_5.B_to_A [Morse.reflection_mem_omega]
#rt_overlap RoundTrip.V15_5.B_to_A [Morse.reflection_mem_omega]

end RoundTrip.V15_5
