import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_1

open Matrix

namespace RoundTrip.V15_1

/-- The project's statement (universes instantiated at `0`): a complex structure is the same as a
skew `J` with `J² = -1` (both directions); a complex structure on `ℝ^n` forces `n` even; and
`tr(JᵀJ) = n`. -/
def A : Prop :=
  type_of% @Morse.isComplexStructure_iff.{0} ∧ type_of% @Morse.IsComplexStructure.even_card.{0} ∧
    type_of% @Morse.IsComplexStructure.trace_transpose_mul_self.{0}

theorem A_holds : A :=
  ⟨@Morse.isComplexStructure_iff.{0}, @Morse.IsComplexStructure.even_card.{0},
    @Morse.IsComplexStructure.trace_transpose_mul_self.{0}⟩

/-! Vocabulary: the two notions of complex structure and of `Ω_k(n)` agree. -/

theorem isCplxStr_iff {ι : Type} [Fintype ι] [DecidableEq ι] (J : Mat ι) :
    IsCplxStr J ↔ Morse.IsComplexStructure J := Iff.rfl

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

/-! Reindexing a matrix along `e : ι ≃ κ` preserves complex structures. -/

section Reindex
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem reindex_mul' (e : ι ≃ κ) (X Y : Mat ι) :
    reindex e e (X * Y) = reindex e e X * reindex e e Y := by
  simpa only [coe_reindexAlgEquiv] using map_mul (reindexAlgEquiv ℝ ℝ e) X Y

theorem reindex_isCplxStr (e : ι ≃ κ) {J : Mat ι} (hJ : Morse.IsComplexStructure J) :
    IsCplxStr (reindex e e J) := by
  obtain ⟨hO, hJ2⟩ := hJ
  rw [mem_orthogonalGroup_iff'] at hO
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff', transpose_reindex, ← reindex_mul', hO]
    simp
  · rw [← reindex_mul', hJ2]
    ext i j
    simp [one_apply]

end Reindex

/-- A ⇒ B: the forward half of `isComplexStructure_iff`; `Ω_1(n)` is definitional. -/
theorem A_to_B : A → B := by
  rintro ⟨hiff, -, -⟩
  refine ⟨fun n _ J hJ => (hiff.1 hJ).1, fun n Js => ?_⟩
  ext J
  simp only [OmegaK, Set.mem_ofPred_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, fun α h1 h2 => by omega⟩⟩

/-- B ⇒ A. The forward half of `isComplexStructure_iff` is B's `J* = -J`, transported from
`Fin (card ι)` to an arbitrary finite type `ι`; it needs `card ι` even (A's `even_card`, which is
not in B and is proved outright, `det(J)² = (-1)ⁿ`). The converse half (skew with `J² = -1` ⇒
orthogonal) and `tr(JᵀJ) = n` are not in B either and are proved outright (one line each). -/
theorem B_to_A : B → A := by
  rintro ⟨hB, -⟩
  -- `even_card`, outright
  have hev : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {J : Mat ι},
      Morse.IsComplexStructure J → Even (Fintype.card ι) := by
    intro ι _ _ J h
    have := congrArg det h.2
    rw [det_mul, det_neg, det_one, mul_one] at this
    rcases Nat.even_or_odd (Fintype.card ι) with he | ho
    · exact he
    · rw [ho.neg_one_pow] at this
      nlinarith [mul_self_nonneg (det J)]
  refine ⟨@fun ι _ _ J => ⟨fun hJ => ⟨?_, hJ.2⟩, fun ⟨hT, hJ⟩ => ⟨?_, hJ⟩⟩,
    @fun ι _ _ J hJ => hev hJ, @fun ι _ _ J hJ => ?_⟩
  · -- forward half, from B on `Fin (card ι)`
    set e := Fintype.equivFin ι
    have h := hB (Fintype.card ι) (hev hJ) (reindex e e J) (reindex_isCplxStr e hJ)
    have hneg : reindex e e (-J) = -(reindex e e J) := by ext; simp
    rw [transpose_reindex, ← hneg] at h
    exact (reindex e e).injective h
  · -- converse half, outright
    rw [mem_orthogonalGroup_iff', hT, Matrix.neg_mul, hJ, neg_neg]
  · -- `tr(JᵀJ) = n`, outright
    have : Jᵀ * J = 1 := by simpa [mem_orthogonalGroup_iff'] using hJ.1
    rw [this, trace_one]

#rt_check RoundTrip.V15_1.A_to_B [Morse.isComplexStructure_iff, Morse.IsComplexStructure.even_card,
  Morse.IsComplexStructure.trace_transpose_mul_self]
#rt_check RoundTrip.V15_1.B_to_A [Morse.isComplexStructure_iff, Morse.IsComplexStructure.even_card,
  Morse.IsComplexStructure.trace_transpose_mul_self]
#rt_overlap RoundTrip.V15_1.B_to_A [Morse.isComplexStructure_iff,
  Morse.IsComplexStructure.even_card, Morse.IsComplexStructure.trace_transpose_mul_self]

end RoundTrip.V15_1
