import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_41

open Matrix Set Function
open scoped Morse.MatrixInner

noncomputable section

namespace RoundTrip.V15_41

/-! ### Proof terms appearing inside the project's statements

The types of `Morse.omegaPhi_stab` and `Morse.omegaPhi_bottJ_mem_omegaComp` contain the proof terms
`Morse.isAnticommFamily_bottJ r` and `Morse.stab_mem_omega hk J'.2` (as arguments of `omegaPhi` and
of the subtype constructor), which are themselves item theorems; stating `A` with `type_of%` would
make every direction depend on them. `A` below is the same statement with these proof terms
replaced by `hbJ r` and `stab_mem_omega'` (definitionally equal by proof irrelevance; `A_holds`
checks it against the project's theorems). `stab_mem_omega'` is the project's proof, copied. -/

/-- `J_1, …, J_8` on `ℝ^{16r}` are anticommuting (the project's `isAnticommFamily_bott16r`,
outside the item). -/
theorem hbJ (r : ℕ) : Morse.IsAnticommFamily (Morse.bottJ r) 8 := Morse.isAnticommFamily_bott16r r

theorem stab_mem_omega' {r k : ℕ} (hk : k ≤ 8) {J : Matrix (Morse.I16 × Fin r) (Morse.I16 × Fin r) ℝ}
    (hJ : J ∈ Morse.Omega (Morse.bottJ r) k) : Morse.stab r k J ∈ Morse.Omega (Morse.bottJ (r + 1)) k := by
  have h := Morse.mem_omega_reindex (Morse.stabEquiv r)
    (Morse.fromBlocks_mem_omega hJ (Morse.bott16_basePt_mem hk))
  have hfam : (fun α => reindex (Morse.stabEquiv r) (Morse.stabEquiv r)
      (fromBlocks (Morse.bottJ r α) 0 0 (Morse.bott16 α))) = Morse.bottJ (r + 1) :=
    funext fun α => Morse.reindex_fromBlocks_bottJ r α
  rwa [hfam] at h

open Morse in
/-- The project's statement (no universe parameters; `bottJ`, `stabEquiv`, `stab` are vocabulary):
(1) `J_1, …, J_8 = J'_α ⊕ ⋯ ⊕ J'_α` are anticommuting complex structures on `ℝ^{16r}`;
(2) `J ↦ J ⊕ J'_k` maps `Ω_k(16r)` into `Ω_k(16r + 16)` (`k ≤ 8`); (3) `J_k ⊕ J'_k = J_k`;
(4) `φ_{r+1}(J' ⊕ J'_{k+1})(t) = φ_r(J')(t) ⊕ (cos(πt)J'_k + sin(πt)J'_{k+1})` for all `t`;
(5) for `k = 2, 6` the component label `tr(J_kᴴ X i)` is unchanged by `X ↦ X ⊕ J'_{k+1}`;
(6) for `k = 2, 6` the base point `J_{k+1}` lies in the component `Ω_{k+1}(16r)^{(0)}`.
All for Milnor's explicit structures `J'_α = bott16 α`. -/
def A : Prop :=
  (∀ r : ℕ, IsAnticommFamily (bottJ r) 8) ∧
  (∀ {r k : ℕ}, k ≤ 8 → ∀ {J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ},
    J ∈ Omega (bottJ r) k → Morse.stab r k J ∈ Omega (bottJ (r + 1)) k) ∧
  (∀ r k : ℕ, Morse.stab r k (basePt (bottJ r) k) = basePt (bottJ (r + 1)) k) ∧
  (∀ {r k : ℕ} (hk : k + 1 ≤ 8) (J' : Omega (bottJ r) (k + 1)) (t : ℝ),
    (omegaPhi ((hbJ (r + 1)).mono hk)
        ⟨Morse.stab r (k + 1) J', stab_mem_omega' hk J'.2⟩ : ℝ → Matrix _ _ ℝ) t =
      reindex (stabEquiv r) (stabEquiv r)
        (fromBlocks ((omegaPhi ((hbJ r).mono hk) J' : ℝ → Matrix _ _ ℝ) t) 0 0
          (Real.cos (Real.pi * t) • basePt bott16 k +
            Real.sin (Real.pi * t) • bott16 (k + 1)))) ∧
  (∀ {r k : ℕ}, k = 2 ∨ k = 6 → ∀ X : Matrix (I16 × Fin r) (I16 × Fin r) ℝ,
    trace ((basePt (bottJ (r + 1)) k)ᴴ * Morse.stab r (k + 1) X * iWordM (bottJ (r + 1)) k) =
      trace ((basePt (bottJ r) k)ᴴ * X * iWordM (bottJ r) k)) ∧
  (∀ (r : ℕ) {k : ℕ} (hk : k = 2 ∨ k = 6),
    (omegaPhi ((hbJ r).mono (by omega : k + 1 ≤ 8))
      ⟨basePt (bottJ r) (k + 1), basePt_mem_omega ((hbJ r).mono
        (by omega : k + 1 ≤ 8))⟩ : PathSp _ _ _) ∈
      omegaComp (bottJ r) k (iWordM (bottJ r) k) (Real.pi * milnorM (k + 1) * (0 : ℤ) / 2))

theorem A_holds : A :=
  ⟨Morse.isAnticommFamily_bottJ, @Morse.stab_mem_omega, Morse.stab_basePt, @Morse.omegaPhi_stab,
    @Morse.omegaLabel_stab, @Morse.omegaPhi_bottJ_mem_omegaComp⟩

/-! ### Glue: Milnor's `ℝ¹⁶` index type `I16` versus the blind file's `Fin 16` -/

section Glue

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem isACFam_iff (Js : ℕ → Mat ι) (m : ℕ) :
    IsACFam Js m ↔ Morse.IsAnticommFamily Js m :=
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

theorem mem_omega_reindex_symm (e : ι ≃ κ) (J : ℕ → Mat ι) (k : ℕ) {Y : Mat κ}
    (hY : Y ∈ Morse.Omega (fun α => reindex e e (J α)) k) :
    reindex e.symm e.symm Y ∈ Morse.Omega J k := by
  have h := Morse.mem_omega_reindex e.symm hY
  have hJ : (fun α => reindex e.symm e.symm (reindex e e (J α))) = J := by
    funext α; simp [reindex_apply, submatrix_submatrix]
  rwa [hJ] at h

/-- `I16 ≃ Fin 16`. -/
def σ : Morse.I16 ≃ Fin 16 := Fintype.equivFinOfCardEq (by decide)

/-- `I16 × Fin r ≃ Fin 16 × Fin r`. -/
def T (r : ℕ) : Morse.I16 × Fin r ≃ Fin 16 × Fin r := σ.prodCongr (Equiv.refl _)

/-- Milnor's `J'_α` on `Fin 16`. -/
def Js16 : ℕ → Mat (Fin 16) := fun α => reindex σ σ (Morse.bott16 α)

theorem isACFam_Js16 : IsACFam Js16 8 :=
  (isACFam_iff _ _).2 (Morse.isAnticommFamily_bott16.reindex σ)

theorem bJ_eq (r α : ℕ) : bJ Js16 r α = reindex (T r) (T r) (Morse.bottJ r α) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [bJ, Js16, T, Morse.bottJ, blockDiagonal_apply]

theorem bpt_eq (k : ℕ) : bpt Js16 k = reindex σ σ (Morse.basePt Morse.bott16 k) := by
  unfold bpt Morse.basePt
  split_ifs
  · simp [reindex_apply, submatrix_one_equiv]
  · rfl

/-- The blind `X ⊕ F` is the project's `stab`, after `I16 ≃ Fin 16`. -/
theorem stab_eq (r k : ℕ) (J : Matrix (Morse.I16 × Fin r) (Morse.I16 × Fin r) ℝ) :
    stab (bpt Js16 k) (reindex (T r) (T r) J) = reindex (T (r + 1)) (T (r + 1)) (Morse.stab r k J) := by
  rw [bpt_eq]
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [stab, Morse.stab, reindex_apply, submatrix_apply, Matrix.of_apply, T,
    Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map, Equiv.refl_symm, Equiv.refl_apply]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [Morse.stabEquiv_symm_last]
    | cast j => simp [Morse.stabEquiv_symm_last, Morse.stabEquiv_symm_castSucc]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [Morse.stabEquiv_symm_last, Morse.stabEquiv_symm_castSucc]
    | cast j => simp [Morse.stabEquiv_symm_castSucc]

end Glue

/-! ### `A`'s remaining conjuncts, re-proved (the project's proofs, copied: `B` says nothing about
`φ_r` outside `[0, 1]`, nor about the component labels and `Ω^{(0)}` of the case `k ≡ 2 (mod 4)`). -/

section Outright

open Morse

theorem stab_basePt_zero (r : ℕ) : Morse.stab r 0 (basePt (bottJ r) 0) = basePt (bottJ (r + 1)) 0 := by
  unfold Morse.stab basePt
  simp only [↓reduceIte]
  rw [fromBlocks_one, reindex_apply, submatrix_one_equiv]

theorem trace_stab' (hsb : ∀ r k, Morse.stab r k (basePt (bottJ r) k) = basePt (bottJ (r + 1)) k)
    {r k : ℕ} (hk : k ≠ 0) (X : Matrix (I16 × Fin r) (I16 × Fin r) ℝ) :
    trace ((basePt (bottJ (r + 1)) k)ᴴ * Morse.stab r (k + 1) X * iWordM (bottJ (r + 1)) k) =
      trace ((basePt (bottJ r) k)ᴴ * X * iWordM (bottJ r) k) +
        trace ((bott16 k)ᴴ * bott16 (k + 1) * iWordM bott16 k) := by
  have hw : iWordM (bottJ (r + 1)) k = reindex (stabEquiv r) (stabEquiv r)
      (fromBlocks (iWordM (bottJ r) k) 0 0 (iWordM bott16 k)) := by
    simp only [iWordM, ← reindex_fromBlocks_bottJ]
    induction (List.range (k - 1)) with
    | nil => simp [fromBlocks_one, submatrix_one_equiv]
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
      simp
  rw [← hsb, hw]
  simp only [Morse.stab, basePt, if_neg hk, if_neg (Nat.succ_ne_zero k)]
  rw [conjTranspose_reindex, reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv,
    submatrix_mul_equiv, ← reindex_apply, trace_reindex_equiv, fromBlocks_conjTranspose,
    fromBlocks_multiply, fromBlocks_multiply]
  simp [trace, Fintype.sum_sum_type]

theorem omegaPhi_bottJ_mem_omegaComp' (r : ℕ) {k : ℕ} (hk : k = 2 ∨ k = 6) :
    (omegaPhi ((hbJ r).mono (by omega : k + 1 ≤ 8))
      ⟨basePt (bottJ r) (k + 1), basePt_mem_omega ((hbJ r).mono
        (by omega : k + 1 ≤ 8))⟩ : PathSp _ _ _) ∈
      omegaComp (bottJ r) k (iWordM (bottJ r) k) (Real.pi * milnorM (k + 1) * (0 : ℤ) / 2) := by
  have hJ := (hbJ r).mono (by omega : k + 1 ≤ 8)
  have h := omegaPhi_mem_omegaComp hJ (isCentralI_iWordM hJ hk)
    ⟨basePt (bottJ r) (k + 1), basePt_mem_omega hJ⟩
  have htr : trace ((basePt (bottJ r) k)ᴴ * basePt (bottJ r) (k + 1) * iWordM (bottJ r) k) = 0 := by
    rcases hk with rfl | rfl
    · simp only [basePt, iWordM_two, bottJ, if_neg (by norm_num : (2 : ℕ) ≠ 0),
        if_neg (by norm_num : (2 + 1 : ℕ) ≠ 0), blockDiagonal_conjTranspose, ← blockDiagonal_mul,
        trace_blockDiagonal]
      simp [trace_bott16_two]
    · simp only [basePt, iWordM_six, bottJ, if_neg (by norm_num : (6 : ℕ) ≠ 0),
        if_neg (by norm_num : (6 + 1 : ℕ) ≠ 0), blockDiagonal_conjTranspose, ← blockDiagonal_mul,
        trace_blockDiagonal]
      simp [trace_bott16_six]
  rw [htr] at h
  simpa using h

end Outright

/-- `B ⇒ A`. `B` at Milnor's family `J'_α = bott16 α` (transported along `I16 ≃ Fin 16`) gives
(1) (`B` (1), first part), (2) (`B` (2), membership, via `stab_eq`) and (3) for `k ≠ 0` (`B` (1),
second part: `J_k^{(r+1)} = J_k^{(r)} ⊕ J'_k`); `k = 0` of (3) (`I ⊕ I = I`) is direct. (4) is an
identity for all real `t` between the formulas `cos(πt)J_k + sin(πt)J'` (the project's
`omegaPhi_apply`, outside the item): `B` (3) only says that the limit map exists and is compatible
with the stages on `[0, 1]`, so (4) is re-proved directly from (3). (5), (6) (the component label of
the case `k ≡ 2 (mod 4)` and `J_{k+1} ∈ Ω^{(0)}`) are not in `B` and are re-proved outright. -/
theorem B_to_A : B → A := by
  intro hB
  obtain ⟨hB1, hB1', hB2, -⟩ := hB Js16 isACFam_Js16
  -- (1)
  have h1 : ∀ r, Morse.IsAnticommFamily (Morse.bottJ r) 8 := by
    intro r
    have h := ((isACFam_iff _ _).1 (hB1 r)).reindex (T r).symm
    have hJ : (fun α => reindex (T r).symm (T r).symm (bJ Js16 r α)) = Morse.bottJ r := by
      funext α; rw [bJ_eq]; simp [reindex_apply, submatrix_submatrix]
    rwa [hJ] at h
  -- (2)
  have h2 : ∀ {r k : ℕ}, k ≤ 8 → ∀ {J : Matrix (Morse.I16 × Fin r) (Morse.I16 × Fin r) ℝ},
      J ∈ Morse.Omega (Morse.bottJ r) k → Morse.stab r k J ∈ Morse.Omega (Morse.bottJ (r + 1)) k := by
    intro r k hk J hJ
    have hX : reindex (T r) (T r) J ∈ OmegaK (bJ Js16 r) k := by
      rw [omegaK_eq_omega, show bJ Js16 r = fun α => reindex (T r) (T r) (Morse.bottJ r α) from
        funext (bJ_eq r)]
      exact Morse.mem_omega_reindex (T r) hJ
    have h := (hB2 k r hk).1 _ hX
    rw [stab_eq, omegaK_eq_omega, show bJ Js16 (r + 1) =
      fun α => reindex (T (r + 1)) (T (r + 1)) (Morse.bottJ (r + 1) α) from funext (bJ_eq (r + 1))] at h
    have h' := mem_omega_reindex_symm (T (r + 1)) (Morse.bottJ (r + 1)) k h
    simpa [reindex_apply, submatrix_submatrix] using h'
  -- (3)
  have h3 : ∀ r k : ℕ, Morse.stab r k (Morse.basePt (Morse.bottJ r) k) =
      Morse.basePt (Morse.bottJ (r + 1)) k := by
    intro r k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact stab_basePt_zero r
    · have h := hB1' r k
      have hk0 : k ≠ 0 := by omega
      have e1 : Js16 k = bpt Js16 k := by simp [bpt, hk0]
      rw [bJ_eq, bJ_eq, e1, stab_eq] at h
      have h' := (reindex (T (r + 1)) (T (r + 1))).injective h
      simp only [Morse.basePt, if_neg hk0]
      exact h'.symm
  refine ⟨h1, h2, h3, ?_, ?_, omegaPhi_bottJ_mem_omegaComp'⟩
  · -- (4), from (3) and the formula for `φ`
    intro r k hk J' t
    rw [Morse.omegaPhi_apply, Morse.omegaPhi_apply, ← h3]
    simp only [Morse.stab, Morse.basePt, if_neg (Nat.succ_ne_zero k)]
    rw [Morse.smul_reindex_add, fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
    simp
  · -- (5)
    intro r k hk X
    rw [trace_stab' h3 (by omega), add_eq_left]
    rcases hk with rfl | rfl
    · rw [Morse.iWordM_two, Morse.conjTranspose_real]; exact Morse.trace_bott16_two
    · rw [Morse.iWordM_six, Morse.conjTranspose_real]; exact Morse.trace_bott16_six

#rt_check RoundTrip.V15_41.B_to_A [Morse.isAnticommFamily_bottJ, Morse.stab_mem_omega, Morse.stab_basePt, Morse.omegaPhi_stab, Morse.omegaLabel_stab, Morse.omegaPhi_bottJ_mem_omegaComp]
#rt_overlap RoundTrip.V15_41.B_to_A [Morse.isAnticommFamily_bottJ, Morse.stab_mem_omega, Morse.stab_basePt, Morse.omegaPhi_stab, Morse.omegaLabel_stab, Morse.omegaPhi_bottJ_mem_omegaComp]

end RoundTrip.V15_41
