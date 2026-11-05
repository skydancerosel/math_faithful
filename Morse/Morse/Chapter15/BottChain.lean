import Morse.Chapter15.FiniteStageTwo

/-!
Milnor, *Morse Theory*, §24, Theorem 24.5 and the proof of Theorem 24.7 (pp. 138, 142, 147–148),
at a finite stage `n = 16r`; Exposition/Chapter15.md, §3 and §6.

# The chain `π_{j+1}Ω_8(16r) ≅ π_{j+2}Ω_7(16r) ≅ ⋯ ≅ π_{j+9}O(16r)`

## Milnor's text, paraphrased

(p. 142) Theorem 24.5 applied eight times: `π_iO ≅ π_{i−1}Ω_1 ≅ ⋯ ≅ π_{i−8}Ω_8`, and
`Ω_8 ≅ O` gives Bott periodicity `π_{i}O ≅ π_{i+8}O`.  (p. 139) `n = 16r`, with the structures
`J_α = J'_α ⊕ ⋯ ⊕ J'_α` of §3.

## What is formalized

* `Morse.bottJ r`: Milnor's structures `J_α = J'_α ⊕ ⋯ ⊕ J'_α` on `ℝ^{16r}` (`r` copies of the
  Kronecker words `Morse.bott16`), eight anticommuting complex structures.
* `Morse.trace_bott16_two`, `Morse.trace_bott16_six`, `Morse.omegaPhi_bottJ_mem_omegaComp`:
  **the base point `J_{k+1}` lies in `Ω_{k+1}(16r)^{(0)}`** for `k = 2, 6` (the trace of
  `J_kᵀJ_{k+1}J_1⋯J_{k−1}` vanishes: in each slot of the Kronecker word some letter is
  traceless; the exposition's "`tr ω_{k+1} = 0`").
* **`Morse.bott_chain`**: for `2j + 12 ≤ r`,
  `π_{j+1}(Ω_8(16r), J_8) ≃ π_{j+9}(O(16r), I)` (as sets), the composite of the eight
  isomorphisms of Theorem 24.5 at the finite stage `n = 16r` (`Morse.omega_pi_equiv` for
  `k ≢ 2 (mod 4)`, `Morse.omega_pi_equiv_two` for `k = 2, 6`, `Morse.theorem_24_3` for `k = 0`),
  each at the base points `J_k`.

## Not formalized here

The identification `Ω_8(16r) ≅ O(r)` (Lemma 24.6), which turns `Morse.bott_chain` into
`π_{j+1}O(r) ≅ π_{j+9}O(16r)`, is `Morse.omegaEightHomeomorph` with
`Morse.bott_periodicity_finite` (`Morse/Chapter15/OmegaEight.lean`); Theorem 24.7 in the stable
range is `Morse.theorem_24_7` (`Morse/Chapter15/StablePeriodicity.lean`).  Not formalized: the
colimits `Ω_k = ⋃_r Ω_k(16r)`.
-/

open Matrix Set Filter Topology Module Function
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

/-- **Milnor's structures on `ℝ^{16r}`**: `J_α = J'_α ⊕ ⋯ ⊕ J'_α` (`r` copies). -/
def bottJ (r : ℕ) : ℕ → Matrix (I16 × Fin r) (I16 × Fin r) ℝ :=
  fun α => Matrix.blockDiagonal fun _ : Fin r => bott16 α

theorem isAnticommFamily_bottJ (r : ℕ) : IsAnticommFamily (bottJ r) 8 :=
  isAnticommFamily_bott16r r

theorem card_bottJ (r : ℕ) : Fintype.card (I16 × Fin r) = 16 * r := by
  simp [Fintype.card_prod]

theorem trace_bott16_two : trace ((bott16 2)ᵀ * bott16 3 * bott16 1) = 0 := by
  simp only [bott16, transpose_kronecker', ← mul_kronecker_mul,
    trace_kronecker]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, σ₂, τ₂, κ₂]

theorem trace_bott16_six : trace ((bott16 6)ᵀ * bott16 7 *
    (bott16 1 * bott16 2 * bott16 3 * bott16 4 * bott16 5)) = 0 := by
  simp only [bott16, transpose_kronecker', ← mul_kronecker_mul,
    trace_kronecker]
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply, σ₂, τ₂, κ₂]

/-- **The base point of `Ω_{k+1}(16r)` lies in `Ω_{k+1}(16r)^{(0)}`** (`k = 2, 6`). -/
theorem omegaPhi_bottJ_mem_omegaComp (r : ℕ) {k : ℕ} (hk : k = 2 ∨ k = 6) :
    (omegaPhi ((isAnticommFamily_bottJ r).mono (by omega : k + 1 ≤ 8))
      ⟨basePt (bottJ r) (k + 1), basePt_mem_omega ((isAnticommFamily_bottJ r).mono
        (by omega : k + 1 ≤ 8))⟩ : PathSp _ _ _) ∈
      omegaComp (bottJ r) k (iWordM (bottJ r) k) (Real.pi * milnorM (k + 1) * (0 : ℤ) / 2) := by
  have hJ := (isAnticommFamily_bottJ r).mono (by omega : k + 1 ≤ 8)
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

/-- **Bott's chain at the finite stage `n = 16r`** (Theorem 24.5 eight times, Milnor p. 142):
for `2j + 12 ≤ r`, `π_{j+1}(Ω_8(16r), J_8) ≃ π_{j+9}(O(16r), I)` (as sets). -/
theorem bott_chain (r j : ℕ) (hr : 2 * j + 12 ≤ r) :
    Nonempty (π_ (j + 1) (Omega (bottJ r) 8)
        ⟨basePt (bottJ r) 8, basePt_mem_omega (isAnticommFamily_bottJ r)⟩ ≃
      π_ (j + 9) (orthogonalGroup (I16 × Fin r) ℝ : Set (Matrix (I16 × Fin r) (I16 × Fin r) ℝ))
        ⟨1, (orthogonalGroup (I16 × Fin r) ℝ).one_mem⟩) := by
  have hJ := isAnticommFamily_bottJ r
  have hc := card_bottJ r
  have hd : ∀ m : ℕ, 0 < m → m ∣ 16 → Fintype.card (I16 × Fin r) / m = (16 / m) * r := by
    intro m hm hm16
    obtain ⟨q, hq⟩ := hm16
    rw [hc, hq, Nat.mul_div_cancel_left _ hm, mul_assoc, Nat.mul_div_cancel_left _ hm]
  have m8 : Fintype.card (I16 × Fin r) / milnorM (7 + 1) = r := by
    rw [show milnorM (7 + 1) = 16 from rfl, hd 16 (by norm_num) dvd_rfl]; simp
  have m7 : Fintype.card (I16 × Fin r) / milnorM (6 + 1) = 2 * r := by
    rw [show milnorM (6 + 1) = 8 from rfl, hd 8 (by norm_num) (by norm_num)]
  have m6 : Fintype.card (I16 × Fin r) / milnorM (5 + 1) = 2 * r := by
    rw [show milnorM (5 + 1) = 8 from rfl, hd 8 (by norm_num) (by norm_num)]
  have m5 : Fintype.card (I16 × Fin r) / milnorM (4 + 1) = 2 * r := by
    rw [show milnorM (4 + 1) = 8 from rfl, hd 8 (by norm_num) (by norm_num)]
  have m4 : Fintype.card (I16 × Fin r) / milnorM (3 + 1) = 2 * r := by
    rw [show milnorM (3 + 1) = 8 from rfl, hd 8 (by norm_num) (by norm_num)]
  have m3 : Fintype.card (I16 × Fin r) / milnorM (2 + 1) = 4 * r := by
    rw [show milnorM (2 + 1) = 4 from rfl, hd 4 (by norm_num) (by norm_num)]
  have m2 : Fintype.card (I16 × Fin r) / milnorM (1 + 1) = 4 * r := by
    rw [show milnorM (1 + 1) = 4 from rfl, hd 4 (by norm_num) (by norm_num)]
  -- `Ω_8 → Ω_7`
  obtain ⟨e8⟩ := omega_pi_equiv (k := 7) hJ (by norm_num) (by norm_num) (r₀ := 1) (Or.inl rfl)
    (i := j + 1) (by rw [m8]; omega) ⟨basePt (bottJ r) 8, basePt_mem_omega hJ⟩
  -- `Ω_7 → Ω_6`, `k = 6`
  have hJ7 : IsAnticommFamily (bottJ r) (6 + 1) := hJ.mono (by norm_num)
  obtain ⟨e7⟩ := omega_pi_equiv_two (k := 6) hJ7 (by norm_num) (by norm_num) (by norm_num)
    (isCentralI_iWordM hJ7 (Or.inr rfl)) 0 (j := j + 1) (by rw [m7]; simp; omega)
    ⟨basePt (bottJ r) 7, basePt_mem_omega hJ7⟩
    (omegaPhi_bottJ_mem_omegaComp r (Or.inr rfl))
  -- `Ω_6 → Ω_5`, `Ω_5 → Ω_4`, `Ω_4 → Ω_3`
  obtain ⟨e6⟩ := omega_pi_equiv (k := 5) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (i := j + 3) (by rw [m6]; omega)
    ⟨basePt (bottJ r) 6, basePt_mem_omega (hJ.mono (by norm_num))⟩
  obtain ⟨e5⟩ := omega_pi_equiv (k := 4) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (i := j + 4) (by rw [m5]; omega)
    ⟨basePt (bottJ r) 5, basePt_mem_omega (hJ.mono (by norm_num))⟩
  obtain ⟨e4⟩ := omega_pi_equiv (k := 3) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (i := j + 5) (by rw [m4]; omega)
    ⟨basePt (bottJ r) 4, basePt_mem_omega (hJ.mono (by norm_num))⟩
  -- `Ω_3 → Ω_2`, `k = 2`
  have hJ3 : IsAnticommFamily (bottJ r) (2 + 1) := hJ.mono (by norm_num)
  obtain ⟨e3⟩ := omega_pi_equiv_two (k := 2) hJ3 (by norm_num) (by norm_num) (by norm_num)
    (isCentralI_iWordM hJ3 (Or.inl rfl)) 0 (j := j + 5) (by rw [m3]; simp; omega)
    ⟨basePt (bottJ r) 3, basePt_mem_omega hJ3⟩
    (omegaPhi_bottJ_mem_omegaComp r (Or.inl rfl))
  -- `Ω_2 → Ω_1`
  obtain ⟨e2⟩ := omega_pi_equiv (k := 1) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (i := j + 7) (by rw [m2]; omega)
    ⟨basePt (bottJ r) 2, basePt_mem_omega (hJ.mono (by norm_num))⟩
  -- `Ω_1 → O(16r)`, Theorem 24.3
  obtain ⟨e1⟩ := (theorem_24_3 (hJ.mono (by norm_num)) (i := j + 8) (by rw [hc]; omega)
    ⟨basePt (bottJ r) 1, basePt_mem_omega (hJ.mono (by norm_num))⟩).2
  exact ⟨e8.trans (e7.trans (e6.trans (e5.trans (e4.trans (e3.trans (e2.trans e1))))))⟩

end Morse
