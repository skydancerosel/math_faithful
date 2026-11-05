import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_4

open Matrix

namespace RoundTrip.V15_4

/-- The project's statement (universes instantiated at `0`), for an arbitrary sequence
`J : ℕ → M_n(ℝ)` (no anticommutation hypothesis): `Ω_{k+1} ⊆ Ω_k`, `Ω_k` closed, `Ω_k` compact,
and, for an anticommuting family `J_1, …, J_k` of complex structures, `J_k ∈ Ω_k` (`k ≥ 1`). -/
def A : Prop :=
  type_of% @Morse.omega_succ_subset.{0} ∧ type_of% @Morse.isClosed_omega.{0} ∧
    type_of% @Morse.isCompact_omega.{0} ∧ type_of% @Morse.IsAnticommFamily.mem_omega.{0}

theorem A_holds : A :=
  ⟨@Morse.omega_succ_subset.{0}, @Morse.isClosed_omega.{0}, @Morse.isCompact_omega.{0},
    @Morse.IsAnticommFamily.mem_omega.{0}⟩

/-! Vocabulary: B's `Ω_k(n)` is the project's (the anticommutation is written in the other order). -/

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

/-- The empty family is anticommuting (B's hypothesis for `k = 0, 1`). -/
theorem isACFam_zero {ι : Type} [Fintype ι] [DecidableEq ι] (Js : ℕ → Mat ι) : IsACFam Js 0 :=
  ⟨fun α h1 h2 => absurd h2 (by omega), fun α _ h1 h2 _ _ _ => absurd h2 (by omega)⟩

/-! Reindexing along `e : ι ≃ κ`. -/

section Reindex
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem reindex_mul' (e : ι ≃ κ) (X Y : Mat ι) :
    reindex e e (X * Y) = reindex e e X * reindex e e Y := by
  simpa only [coe_reindexAlgEquiv] using map_mul (reindexAlgEquiv ℝ ℝ e) X Y

theorem reindex_mem_orth (e : ι ≃ κ) {X : Mat ι} (hX : X ∈ Orth ι) : reindex e e X ∈ Orth κ := by
  rw [Orth, SetLike.mem_coe, mem_orthogonalGroup_iff'] at hX ⊢
  rw [transpose_reindex, ← reindex_mul', hX]
  ext i j
  simp [one_apply]

theorem reindex_isCS (e : ι ≃ κ) {J : Mat ι} (hJ : Morse.IsComplexStructure J) :
    Morse.IsComplexStructure (reindex e e J) := by
  refine ⟨reindex_mem_orth e hJ.1, ?_⟩
  rw [← reindex_mul', hJ.2]
  ext i j
  simp [one_apply]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem eq_image_reindex (e : ι ≃ κ) {S : Set (Mat ι)} {T : Set (Mat κ)}
    (h1 : ∀ X ∈ S, reindex e e X ∈ T) (h2 : ∀ Y ∈ T, reindex e.symm e.symm Y ∈ S) :
    S = reindex e.symm e.symm '' T := by
  ext X
  refine ⟨fun hX => ⟨reindex e e X, h1 X hX, ?_⟩, fun ⟨Y, hY, hYX⟩ => hYX ▸ h2 Y hY⟩
  ext i j
  simp

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem continuous_reindex (e : κ ≃ ι) : Continuous (fun X : Mat κ => reindex e e X) := by
  simp only [reindex_apply]
  exact continuous_id.matrix_submatrix _ _

end Reindex

/-- A ⇒ B: the chain is iterated `omega_succ_subset`, compactness is `isCompact_omega`; the two
definitional conjuncts are unfolded. (B's anticommutation hypothesis is not needed.) -/
theorem A_to_B : A → B := by
  rintro ⟨hsucc, -, hcpt, -⟩ n k Js -
  refine ⟨rfl, fun hk => ?_, fun j hj => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    ext J
    simp only [OmegaK, Set.mem_ofPred_eq, Nat.add_sub_cancel]
  · rw [omegaK_eq_omega, omegaK_eq_omega]
    obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
    clear hj
    induction d with
    | zero => exact le_rfl
    | succ d ih => exact (hsucc Js (j + d)).trans ih
  · rw [omegaK_eq_omega]
    exact hcpt Js k

/-- B ⇒ A. Compactness: B at `k = 0` (`O(n)` compact) and `k = 1` (the complex structures form a
compact set), whose anticommutation hypotheses are empty, transported from `Fin (card ι)` to `ι`;
for `k ≥ 2` and an arbitrary sequence `J`, `Ω_k = Ω_1 ∩ {anticommutation equations}` is a closed
subset of `Ω_1` (outright). Closedness follows from compactness (Hausdorff). The chain for an
arbitrary sequence and `J_k ∈ Ω_k` are definitional (outright): B states the chain only under its
anticommutation hypothesis, and does not state `J_k ∈ Ω_k`. -/
theorem B_to_A : B → A := by
  intro hB
  have hcpt : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (J : ℕ → Mat ι) (k : ℕ),
      IsCompact (Morse.Omega J k) := by
    intro ι _ _ J k
    set e := Fintype.equivFin ι
    have hB0 := (hB (Fintype.card ι) 0 (fun _ => 0) (isACFam_zero _)).2.2.2
    have hB1 := (hB (Fintype.card ι) 1 (fun _ => 0) (isACFam_zero _)).2.2.2
    rw [omegaK_eq_omega] at hB0 hB1
    cases k with
    | zero =>
      have : Morse.Omega J 0 = reindex e.symm e.symm '' Morse.Omega (fun _ => 0) 0 :=
        eq_image_reindex e (fun X hX => reindex_mem_orth e hX)
          (fun Y hY => reindex_mem_orth e.symm hY)
      rw [this]
      exact hB0.image (continuous_reindex e.symm)
    | succ k =>
      have hS : {X : Mat ι | Morse.IsComplexStructure X} =
          reindex e.symm e.symm '' Morse.Omega (fun _ => 0) 1 :=
        eq_image_reindex e (fun X hX => ⟨reindex_isCS e hX, fun α h1 h2 =>
          (Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le h1 h2)).elim⟩)
          (fun Y hY => reindex_isCS e.symm hY.1)
      have hcl : IsClosed {X : Mat ι | ∀ α, 1 ≤ α → α ≤ k → J α * X = -(X * J α)} := by
        simp only [Set.ofPred_forall]
        exact isClosed_iInter fun α => isClosed_iInter fun _ => isClosed_iInter fun _ =>
          isClosed_eq (by fun_prop) (by fun_prop)
      have : Morse.Omega J (k + 1) = {X : Mat ι | Morse.IsComplexStructure X} ∩
          {X : Mat ι | ∀ α, 1 ≤ α → α ≤ k → J α * X = -(X * J α)} := by
        ext X; rfl
      rw [this, hS]
      exact (hB1.image (continuous_reindex e.symm)).inter_right hcl
  refine ⟨@fun ι _ _ J k => ?_, @fun ι _ _ J k => (hcpt J k).isClosed, @fun ι _ _ J k => hcpt J k,
    @fun ι _ _ J k h hk => ?_⟩
  · -- the chain, definitional
    cases k with
    | zero => exact fun X hX => hX.1.1
    | succ k => exact fun X hX => ⟨hX.1, fun α h1 h2 => hX.2 α h1 (h2.trans (Nat.le_succ k))⟩
  · -- `J_k ∈ Ω_k`, definitional
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact ⟨h.cs _ hk le_rfl, fun α h1 h2 => h.anti α (k + 1) h1 (by omega) hk le_rfl (by omega)⟩

#rt_check RoundTrip.V15_4.A_to_B [Morse.omega_succ_subset, Morse.isClosed_omega,
  Morse.isCompact_omega, Morse.IsAnticommFamily.mem_omega]
#rt_check RoundTrip.V15_4.B_to_A [Morse.omega_succ_subset, Morse.isClosed_omega,
  Morse.isCompact_omega, Morse.IsAnticommFamily.mem_omega]
#rt_overlap RoundTrip.V15_4.B_to_A [Morse.omega_succ_subset, Morse.isClosed_omega,
  Morse.isCompact_omega, Morse.IsAnticommFamily.mem_omega]

end RoundTrip.V15_4
