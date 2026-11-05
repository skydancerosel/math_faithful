import Morse.Chapter15.OmegaEight
import Morse.Chapter14.Periodicity
import Morse.Homotopy.BundlesOrthogonal

/-!
Milnor, *Morse Theory*, §24, Theorem 24.7 (p. 142), and §23, the periodicity theorem (p. 129),
in the stable range; Exposition/Chapter15.md, §4, Theorem 24.7, and Exposition/Chapter14.md, §3.

# Bott periodicity `π_i O(n) ≅ π_{i+8} O(n')` in the stable range

## Milnor's text, paraphrased

(p. 142) **Theorem 24.7 (Bott).** `π_iO ≅ π_{i+8}O` for `i ≥ 0`: Theorem 24.5 applied eight
times and `Ω_8 ≅ O`.  (p. 129) For the unitary group, `π_{i−1}U ≅ π_{i+1}U`.  Here `O` and `U`
are the direct limits, whose homotopy groups are the stable values `π_iO(n)` for `n > i + 1` and
`π_iU(n)` for `2n > i` (stability, p. 138 and Lemma 23.4).

## What is formalized

* `Morse.bott_chain_of_le`: the chain `π_i Ω_8(16r) ≃ π_{i+8} O(16r)` of `Morse.bott_chain`,
  now **including `i = 0`** (the `k = 2, 6` steps `Morse.omega_pi_equiv_two` are only used in
  degrees `≥ 1`: `π_{i+1}Ω_7` and `π_{i+5}Ω_3`), for `2i + 7 ≤ r`.
* `Morse.bott_periodicity_finite_of_le`: `π_i O(r) ≃ π_{i+8} O(16r)` for `2i + 7 ≤ r`, `i ≥ 0`.
* **`Morse.theorem_24_7`**: for all `i ≥ 0`, `n ≥ i + 2`, `n' ≥ i + 10`,
  `π_i(O(n), I) ≃ π_{i+8}(O(n'), I)` (as sets): the stable groups `π_iO(n)` (`i < n − 1`) and
  `π_{i+8}O(n')` (`i + 8 < n' − 1`) correspond.  Stability
  (`Morse.Homotopy.nonempty_pi_unitary_equiv_stable`) moves both sides to `n = r = 2i + 7` and
  `n' = 16r`.
* **`Morse.periodicity_theorem_stable`** (the unitary analogue): for `i < 2n` and `i + 2 < 2n'`,
  `π_i(U(n), I) ≃ π_{i+2}(U(n'), I)`.

## What Milnor leaves implicit

The bounds: `O(n) → O(n + 1)` is bijective on `π_i` for `i + 2 ≤ n` (fibration
`O(n) → O(n + 1) → Sⁿ`), and the finite-stage chain needs `2i + 7 ≤ r` (Theorem 24.5 at `k = 2, 6`
loses a factor of 4 in the dimension bound, Exposition §6).  The bijections are of pointed sets;
upgrading the chain to group isomorphisms would need each step of Theorem 24.5 as a group map,
which is not done here.
-/

open Matrix Set Function Topology
open scoped Topology.Homotopy

noncomputable section

namespace Morse

namespace Homotopy

variable {𝕜 : Type*} [RCLike 𝕜]

theorem unitaryCongr_one {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (e : ι ≃ ι') : unitaryCongr (𝕜 := 𝕜) e 1 = 1 :=
  Subtype.ext (by simp [unitaryCongr])

/-- Reindexing the coordinates: `π_i U(ι) ≃ π_i U(ι')`. -/
def piUnitaryCongr {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (e : ι ≃ ι') (i : ℕ) : π_ i (unitaryGroup ι 𝕜) 1 ≃ π_ i (unitaryGroup ι' 𝕜) 1 :=
  piEquivOfHomeomorph (unitaryCongr e) (unitaryCongr_one e) i

/-- **Stability** (`𝕜 = ℝ`, `d = 1`: `i + 2 ≤ m`; `𝕜 = ℂ`, `d = 2`: `i < 2m`):
`π_i U(m) ≃ π_i U(m')` for `m ≤ m'`. -/
theorem nonempty_pi_unitary_equiv_of_le {d : ℕ} (hS : SphereConnected 𝕜 d) {m m' i : ℕ}
    (hmm : m ≤ m') (hi : i + 2 ≤ d * m + d - 1) :
    Nonempty (π_ i (unitaryGroup (Fin m) 𝕜) 1 ≃ π_ i (unitaryGroup (Fin m') 𝕜) 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmm
  have e₁ := Equiv.ofBijective _
    (bijective_homotopyGroupMap_unitaryIncl (k := k) hS hi (1 : unitaryGroup (Fin m) 𝕜))
  rw [show unitaryInclC (𝕜 := 𝕜) m k 1 = 1 from map_one (unitaryIncl 𝕜 (Fin m) (Fin k))] at e₁
  exact ⟨e₁.trans (piUnitaryCongr finSumFinEquiv i)⟩

/-- **Stability, both directions**: `π_i U(m) ≃ π_i U(m')` when both are in the stable range. -/
theorem nonempty_pi_unitary_equiv_stable {d : ℕ} (hS : SphereConnected 𝕜 d) {m m' i : ℕ}
    (hm : i + 2 ≤ d * m + d - 1) (hm' : i + 2 ≤ d * m' + d - 1) :
    Nonempty (π_ i (unitaryGroup (Fin m) 𝕜) 1 ≃ π_ i (unitaryGroup (Fin m') 𝕜) 1) := by
  rcases le_total m m' with h | h
  · exact nonempty_pi_unitary_equiv_of_le hS h hm
  · obtain ⟨e⟩ := nonempty_pi_unitary_equiv_of_le hS h hm'
    exact ⟨e.symm⟩

end Homotopy

/-- **Bott's chain at the finite stage `n = 16r`, all degrees** (Theorem 24.5 eight times, Milnor
p. 142): for `2i + 7 ≤ r`, `π_i(Ω_8(16r), J_8) ≃ π_{i+8}(O(16r), I)` (as sets), `i ≥ 0`. -/
theorem bott_chain_of_le (r i : ℕ) (hr : 2 * i + 7 ≤ r) :
    Nonempty (π_ i (Omega (bottJ r) 8)
        ⟨basePt (bottJ r) 8, basePt_mem_omega (isAnticommFamily_bottJ r)⟩ ≃
      π_ (i + 8) (orthogonalGroup (I16 × Fin r) ℝ : Set (Matrix (I16 × Fin r) (I16 × Fin r) ℝ))
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
  -- `Ω_8 → Ω_7`, degree `i ≥ 0`
  obtain ⟨e8⟩ := omega_pi_equiv (k := 7) hJ (by norm_num) (by norm_num) (r₀ := 1) (Or.inl rfl)
    (i := i) (by rw [m8]; omega) ⟨basePt (bottJ r) 8, basePt_mem_omega hJ⟩
  -- `Ω_7 → Ω_6`, `k = 6`, degree `i + 1 ≥ 1`
  have hJ7 : IsAnticommFamily (bottJ r) (6 + 1) := hJ.mono (by norm_num)
  obtain ⟨e7⟩ := omega_pi_equiv_two (k := 6) hJ7 (by norm_num) (by norm_num) (by norm_num)
    (isCentralI_iWordM hJ7 (Or.inr rfl)) 0 (j := i) (by rw [m7]; simp; omega)
    ⟨basePt (bottJ r) 7, basePt_mem_omega hJ7⟩
    (omegaPhi_bottJ_mem_omegaComp r (Or.inr rfl))
  -- `Ω_6 → Ω_5`, `Ω_5 → Ω_4`, `Ω_4 → Ω_3`
  obtain ⟨e6⟩ := omega_pi_equiv (k := 5) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (i := i + 2) (by rw [m6]; omega)
    ⟨basePt (bottJ r) 6, basePt_mem_omega (hJ.mono (by norm_num))⟩
  obtain ⟨e5⟩ := omega_pi_equiv (k := 4) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (i := i + 3) (by rw [m5]; omega)
    ⟨basePt (bottJ r) 5, basePt_mem_omega (hJ.mono (by norm_num))⟩
  obtain ⟨e4⟩ := omega_pi_equiv (k := 3) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (i := i + 4) (by rw [m4]; omega)
    ⟨basePt (bottJ r) 4, basePt_mem_omega (hJ.mono (by norm_num))⟩
  -- `Ω_3 → Ω_2`, `k = 2`, degree `i + 5 ≥ 1`
  have hJ3 : IsAnticommFamily (bottJ r) (2 + 1) := hJ.mono (by norm_num)
  obtain ⟨e3⟩ := omega_pi_equiv_two (k := 2) hJ3 (by norm_num) (by norm_num) (by norm_num)
    (isCentralI_iWordM hJ3 (Or.inl rfl)) 0 (j := i + 4) (by rw [m3]; simp; omega)
    ⟨basePt (bottJ r) 3, basePt_mem_omega hJ3⟩
    (omegaPhi_bottJ_mem_omegaComp r (Or.inl rfl))
  -- `Ω_2 → Ω_1`
  obtain ⟨e2⟩ := omega_pi_equiv (k := 1) (hJ.mono (by norm_num)) (by norm_num) (by norm_num)
    (r₀ := 1) (Or.inl rfl) (i := i + 6) (by rw [m2]; omega)
    ⟨basePt (bottJ r) 2, basePt_mem_omega (hJ.mono (by norm_num))⟩
  -- `Ω_1 → O(16r)`, Theorem 24.3
  obtain ⟨e1⟩ := (theorem_24_3 (hJ.mono (by norm_num)) (i := i + 7) (by rw [hc]; omega)
    ⟨basePt (bottJ r) 1, basePt_mem_omega (hJ.mono (by norm_num))⟩).2
  exact ⟨e8.trans (e7.trans (e6.trans (e5.trans (e4.trans (e3.trans (e2.trans e1))))))⟩

/-- **Bott periodicity at a finite stage, all degrees** (Theorem 24.7, `n = 16r`): for
`2i + 7 ≤ r`, `π_i(O(r), I) ≃ π_{i+8}(O(16r), I)` (as sets), including `i = 0`. -/
theorem bott_periodicity_finite_of_le (r i : ℕ) (hr : 2 * i + 7 ≤ r) :
    Nonempty (π_ i (orthogonalGroup (Fin r) ℝ : Set (Matrix (Fin r) (Fin r) ℝ))
        ⟨1, (orthogonalGroup (Fin r) ℝ).one_mem⟩ ≃
      π_ (i + 8) (orthogonalGroup (I16 × Fin r) ℝ :
        Set (Matrix (I16 × Fin r) (I16 × Fin r) ℝ))
        ⟨1, (orthogonalGroup (I16 × Fin r) ℝ).one_mem⟩) := by
  obtain ⟨e⟩ := bott_chain_of_le r i hr
  exact ⟨(Morse.Homotopy.piEquivOfHomeomorph (omegaEightHomeomorph r)
    (omegaEightHomeomorph_basePt r) i).symm.trans e⟩

/-- **Theorem 24.7 (Bott)** (Milnor p. 142), `π_iO ≅ π_{i+8}O`, in the stable range: for every
`i ≥ 0`, `n ≥ i + 2` and `n' ≥ i + 10`, `π_i(O(n), I) ≃ π_{i+8}(O(n'), I)` (as sets). -/
theorem theorem_24_7 {i n n' : ℕ} (hn : i + 2 ≤ n) (hn' : i + 10 ≤ n') :
    Nonempty (π_ i (orthogonalGroup (Fin n) ℝ) 1 ≃ π_ (i + 8) (orthogonalGroup (Fin n') ℝ) 1) := by
  set r := 2 * i + 7
  obtain ⟨e₁⟩ := Homotopy.nonempty_pi_unitary_equiv_stable Homotopy.sphereConnected_real
    (m := n) (m' := r) (i := i) (by omega) (by omega)
  obtain ⟨e₂⟩ := bott_periodicity_finite_of_le r i le_rfl
  have e₃ := Homotopy.piUnitaryCongr (𝕜 := ℝ)
    (Fintype.equivFinOfCardEq (card_bottJ r)) (i + 8)
  obtain ⟨e₄⟩ := Homotopy.nonempty_pi_unitary_equiv_stable Homotopy.sphereConnected_real
    (m := 16 * r) (m' := n') (i := i + 8) (by omega) (by omega)
  exact ⟨e₁.trans (e₂.trans (e₃.trans e₄))⟩

/-- **The unitary periodicity theorem in the stable range** (Milnor p. 129, `π_{i−1}U ≅ π_{i+1}U`):
for `i < 2n` and `i + 2 < 2n'`, `π_i(U(n), I) ≃ π_{i+2}(U(n'), I)` (as sets). -/
theorem periodicity_theorem_stable {i n n' : ℕ} (hn : i < 2 * n) (hn' : i + 2 < 2 * n') :
    Nonempty (π_ i (unitaryGroup (Fin n) ℂ) 1 ≃ π_ (i + 2) (unitaryGroup (Fin n') ℂ) 1) := by
  obtain ⟨e₁⟩ := Homotopy.nonempty_pi_unitary_equiv_stable Homotopy.sphereConnected_complex
    (m := n) (m' := i + 1) (i := i) (by omega) (by omega)
  obtain ⟨e₂⟩ := nonempty_equiv_pi_unitary_two_mul (m := i + 1) (j := i) (by omega)
  have e₃ := Homotopy.piUnitaryCongr (𝕜 := ℂ) (finSumFinEquiv (m := i + 1) (n := i + 1)) (i + 2)
  obtain ⟨e₄⟩ := Homotopy.nonempty_pi_unitary_equiv_stable Homotopy.sphereConnected_complex
    (m := i + 1 + (i + 1)) (m' := n') (i := i + 2) (by omega) (by omega)
  exact ⟨e₁.trans (e₂.trans (e₃.trans e₄))⟩

end Morse
