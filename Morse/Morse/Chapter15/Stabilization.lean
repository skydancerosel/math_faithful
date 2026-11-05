import Morse.Chapter15.BottChain

/-!
Milnor, *Morse Theory*, §24, p. 138 ("it is not difficult to see that the inclusions give rise,
in the limit, to inclusions `Ω_{k+1} → ΩΩ_k`"); Exposition/Chapter15.md, §3 and §6
("Passing to the limit").

# Stabilization `Ω_k(16r) → Ω_k(16r + 16)` and its compatibility with `φ_r`

## Milnor's text, paraphrased

(p. 138) `Ω_k(n)` is imbedded in `Ω_k(n + n')` by `J ↦ J ⊕ J'_k`, and the inclusions
`φ : Ω_{k+1}(n) → Ω(Ω_k(n); J_k, −J_k)` are compatible with these imbeddings, giving
`Ω_{k+1} → ΩΩ_k` in the limit.  (Exposition §3) `φ_{r+1}(J' ⊕ J'_{k+1}) = φ_r(J') ⊕ δ_k`,
`δ_k(t) = cos(πt) J'_k + sin(πt) J'_{k+1}`; (§6) the integer `c` does not change.

## What is formalized

For Milnor's structures `Morse.bottJ r` on `ℝ^{16r}` (`r` copies of `J'_α` on `ℝ¹⁶`):

* `Morse.stabEquiv r`: `ℝ^{16r} ⊕ ℝ¹⁶ ≅ ℝ^{16(r+1)}` (the last block), and
  `Morse.reindex_fromBlocks_bottJ`: **`J_α ⊕ J'_α = J_α`** at stage `r + 1`.
* `Morse.stab r k J = J ⊕ J'_k` (`J ⊕ I` for `k = 0`), `Morse.stab_mem_omega`
  (`Ω_k(16r) → Ω_k(16r + 16)`), `Morse.stab_basePt` (`J_k ↦ J_k`).
* **`Morse.omegaPhi_stab`**: `φ_{r+1}(J' ⊕ J'_{k+1})(t) = φ_r(J')(t) ⊕ δ_k(t)`.
* `Morse.trace_stab`: the trace defining the component label is additive, and
  **`Morse.omegaLabel_stab`**: for `k = 2, 6` the label `−tr(J_kᵀJ'·i)` does not change under
  `J' ↦ J' ⊕ J'_{k+1}` (`Morse.trace_bott16_two`, `Morse.trace_bott16_six`).

## Not formalized here

The colimit spaces `Ω_k = ⋃_r Ω_k(16r)` with their colimit topology, and the statement that the
stabilization maps are bijective on `π_i` in a range growing with `r` (this needs the naturality
of the isomorphisms of `Morse.bott_chain` under stabilization, including the loop-space
identification `π_j Ω(N; p, q) ≅ π_{j+1}N`).
-/

open Matrix Set Function
open scoped Morse.MatrixInner

noncomputable section

namespace Morse

/-- `ℝ^{16r} ⊕ ℝ¹⁶ ≅ ℝ^{16(r+1)}`: the added block is the last one. -/
def stabEquiv (r : ℕ) : (I16 × Fin r) ⊕ I16 ≃ I16 × Fin (r + 1) where
  toFun
    | Sum.inl x => (x.1, x.2.castSucc)
    | Sum.inr x => (x, Fin.last r)
  invFun x := Fin.lastCases (Sum.inr x.1) (fun i => Sum.inl (x.1, i)) x.2
  left_inv := by
    rintro (⟨x, i⟩ | x)
    · simp
    · simp
  right_inv := by
    rintro ⟨x, i⟩
    induction i using Fin.lastCases with
    | last => simp
    | cast i => simp

theorem stabEquiv_symm_castSucc (r : ℕ) (x : I16) (i : Fin r) :
    (stabEquiv r).symm (x, i.castSucc) = Sum.inl (x, i) := by
  simp [stabEquiv]

theorem stabEquiv_symm_last (r : ℕ) (x : I16) :
    (stabEquiv r).symm (x, Fin.last r) = Sum.inr x := by
  simp [stabEquiv]

/-- `M ⊕ ⋯ ⊕ M` (`r` copies) `⊕ M` is `M ⊕ ⋯ ⊕ M` (`r + 1` copies). -/
theorem reindex_fromBlocks_blockDiagonal (r : ℕ) (M : Matrix I16 I16 ℝ) :
    reindex (stabEquiv r) (stabEquiv r)
        (fromBlocks (blockDiagonal fun _ : Fin r => M) 0 0 M) =
      blockDiagonal fun _ : Fin (r + 1) => M := by
  ext ⟨x, i⟩ ⟨y, j⟩
  rw [reindex_apply, submatrix_apply]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [stabEquiv_symm_last, blockDiagonal_apply]
    | cast j =>
      simp [stabEquiv_symm_last, stabEquiv_symm_castSucc, blockDiagonal_apply,
        (Fin.castSucc_ne_last j).symm]
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      simp [stabEquiv_symm_last, stabEquiv_symm_castSucc, blockDiagonal_apply,
        Fin.castSucc_ne_last i]
    | cast j =>
      simp [stabEquiv_symm_castSucc, blockDiagonal_apply, Fin.castSucc_inj]

/-- **`J_α ⊕ J'_α = J_α`** (Milnor's structures at stages `r` and `r + 1`). -/
theorem reindex_fromBlocks_bottJ (r α : ℕ) :
    reindex (stabEquiv r) (stabEquiv r) (fromBlocks (bottJ r α) 0 0 (bott16 α)) =
      bottJ (r + 1) α :=
  reindex_fromBlocks_blockDiagonal r (bott16 α)

/-- **Milnor's stabilization** `J ↦ J ⊕ J'_k` (`J ↦ J ⊕ I` for `k = 0`). -/
def stab (r k : ℕ) (J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ) :
    Matrix (I16 × Fin (r + 1)) (I16 × Fin (r + 1)) ℝ :=
  reindex (stabEquiv r) (stabEquiv r) (fromBlocks J 0 0 (basePt bott16 k))

theorem mem_omega_reindex {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : n ≃ m) {J : ℕ → Matrix n n ℝ} {k : ℕ} {X : Matrix n n ℝ} (hX : X ∈ Omega J k) :
    reindex e e X ∈ Omega (fun α => reindex e e (J α)) k := by
  set f := reindexAlgEquiv ℝ ℝ e with hfdef
  have hf : ∀ A : Matrix n n ℝ, reindex e e A = f A := fun A => rfl
  have horth : ∀ A : Matrix n n ℝ, A ∈ orthogonalGroup n ℝ →
      reindex e e A ∈ orthogonalGroup m ℝ := fun A hA => by
    rw [mem_orthogonalGroup_iff'] at hA ⊢
    rw [transpose_reindex, hf, hf, ← map_mul, hA, map_one]
  cases k with
  | zero => exact horth X hX
  | succ k =>
    obtain ⟨⟨hXo, hXsq⟩, ha⟩ := hX
    refine ⟨⟨horth X hXo, by rw [hf, ← map_mul, hXsq, map_neg, map_one]⟩, fun α h1 h2 => ?_⟩
    simp only [hf]
    rw [← map_mul, ← map_mul, ha α h1 h2, map_neg, map_mul]

theorem bott16_basePt_mem {k : ℕ} (hk : k ≤ 8) : basePt bott16 k ∈ Omega bott16 k :=
  basePt_mem_omega (isAnticommFamily_bott16.mono hk)

/-- **`Ω_k(16r) → Ω_k(16r + 16)`**, `J ↦ J ⊕ J'_k` (Milnor p. 138). -/
theorem stab_mem_omega {r k : ℕ} (hk : k ≤ 8) {J : Matrix (I16 × Fin r) (I16 × Fin r) ℝ}
    (hJ : J ∈ Omega (bottJ r) k) : stab r k J ∈ Omega (bottJ (r + 1)) k := by
  have h := mem_omega_reindex (stabEquiv r) (fromBlocks_mem_omega hJ (bott16_basePt_mem hk))
  have hfam : (fun α => reindex (stabEquiv r) (stabEquiv r)
      (fromBlocks (bottJ r α) 0 0 (bott16 α))) = bottJ (r + 1) :=
    funext fun α => reindex_fromBlocks_bottJ r α
  rwa [hfam] at h

/-- **The base point is preserved**: `J_k ⊕ J'_k = J_k`. -/
theorem stab_basePt (r k : ℕ) : stab r k (basePt (bottJ r) k) = basePt (bottJ (r + 1)) k := by
  unfold stab basePt
  split_ifs with hk
  · rw [fromBlocks_one, reindex_apply, submatrix_one_equiv]
  · exact reindex_fromBlocks_bottJ r k

theorem smul_reindex_add {n m : Type*} (e : n ≃ m) (c d : ℝ) (A B : Matrix n n ℝ) :
    c • reindex e e A + d • reindex e e B = reindex e e (c • A + d • B) := by
  ext i j; simp [reindex_apply]

/-- **Compatibility of `φ_r` with stabilization** (Milnor p. 138; exposition §3):
`φ_{r+1}(J' ⊕ J'_{k+1})(t) = φ_r(J')(t) ⊕ δ_k(t)`, `δ_k(t) = cos(πt) J'_k + sin(πt) J'_{k+1}`. -/
theorem omegaPhi_stab {r k : ℕ} (hk : k + 1 ≤ 8) (J' : Omega (bottJ r) (k + 1)) (t : ℝ) :
    (omegaPhi ((isAnticommFamily_bottJ (r + 1)).mono hk)
        ⟨stab r (k + 1) J', stab_mem_omega hk J'.2⟩ : ℝ → Matrix _ _ ℝ) t =
      reindex (stabEquiv r) (stabEquiv r)
        (fromBlocks ((omegaPhi ((isAnticommFamily_bottJ r).mono hk) J' : ℝ → Matrix _ _ ℝ) t) 0 0
          (Real.cos (Real.pi * t) • basePt bott16 k +
            Real.sin (Real.pi * t) • bott16 (k + 1))) := by
  rw [omegaPhi_apply, omegaPhi_apply, ← stab_basePt]
  simp only [stab, basePt, if_neg (Nat.succ_ne_zero k)]
  rw [smul_reindex_add, fromBlocks_smul, fromBlocks_smul, fromBlocks_add]
  simp

theorem trace_reindex_equiv {n m : Type*} [Fintype n] [Fintype m] (e : n ≃ m)
    (A : Matrix n n ℝ) : trace (reindex e e A) = trace A := by
  simp only [trace, diag, reindex_apply, submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => A i i)

/-- The label trace is additive under stabilization. -/
theorem trace_stab {r k : ℕ} (hk : k ≠ 0) (X : Matrix (I16 × Fin r) (I16 × Fin r) ℝ) :
    trace ((basePt (bottJ (r + 1)) k)ᴴ * stab r (k + 1) X * iWordM (bottJ (r + 1)) k) =
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
  rw [← stab_basePt, hw]
  simp only [stab, basePt, if_neg hk, if_neg (Nat.succ_ne_zero k)]
  rw [conjTranspose_reindex, reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv,
    submatrix_mul_equiv, ← reindex_apply, trace_reindex_equiv, fromBlocks_conjTranspose,
    fromBlocks_multiply, fromBlocks_multiply]
  simp [trace, Fintype.sum_sum_type]

/-- **The component label does not change under stabilization** (`k = 2, 6`; exposition §6:
"`δ_k` has `c = 0`"). -/
theorem omegaLabel_stab {r k : ℕ} (hk : k = 2 ∨ k = 6)
    (X : Matrix (I16 × Fin r) (I16 × Fin r) ℝ) :
    trace ((basePt (bottJ (r + 1)) k)ᴴ * stab r (k + 1) X * iWordM (bottJ (r + 1)) k) =
      trace ((basePt (bottJ r) k)ᴴ * X * iWordM (bottJ r) k) := by
  rw [trace_stab (by omega), add_eq_left]
  rcases hk with rfl | rfl
  · rw [iWordM_two, conjTranspose_real]; exact trace_bott16_two
  · rw [iWordM_six, conjTranspose_real]; exact trace_bott16_six

end Morse
