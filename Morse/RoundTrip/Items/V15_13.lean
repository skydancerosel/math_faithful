import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_13

open Matrix Module

namespace RoundTrip.V15_13

/-- The declarations of this item (`Morse.IsMinimalCliffordModule`, `Morse.milnorM`) are both
definitions: there is no listed theorem, so the project's formal statement is the empty
conjunction. -/
def A : Prop := True

theorem A_holds : A := trivial

/-- B ⇒ A, trivially. -/
theorem B_to_A : B → A := fun _ => trivial

/-! `A → B` is not proved: it would mean proving B outright, and B's claims for `k > 8` (existence
of minimal spaces for every `k`, that all minimal spaces have the same dimension, and
`m_k = 16 m_{k-8}`) need Clifford periodicity (`C_{k+8} ≅ C_k ⊗ ℝ(16)` and its consequence for
irreducible modules), which is neither in Mathlib nor in the project (the project's docstring:
"Not formalized: … the case `k > 8`"; `milnorM (k + 8) = 16 * milnorM k` is its *definition*).

### Vocabulary check (not part of `A`)

The blind notions agree with the project's definitions, and B holds for `k ≤ 8`. -/

section Vocab
variable {n : ℕ}

/-- The project's `IsMinimalCliffordModule` on `ℝⁿ` (for the endomorphisms `v ↦ J_α v`), together
with the anticommuting-family hypothesis, is exactly the blind `IsMinACSp`. -/
theorem isMinACSp_iff (Js : ℕ → Mat (Fin n)) (k : ℕ) :
    IsMinACSp Js k ↔ Morse.IsAnticommFamily Js k ∧
      Morse.IsMinimalCliffordModule (fun α => Matrix.toLinAlgEquiv' (Js α)) k := by
  have hinv : ∀ W : Submodule ℝ (Fin n → ℝ),
      ((∀ α, 1 ≤ α → α ≤ k → ∀ v ∈ W, Js α *ᵥ v ∈ W) ↔
        ∀ α, 1 ≤ α → α ≤ k → ∀ w ∈ W, Matrix.toLinAlgEquiv' (Js α) w ∈ W) := fun W => by
    simp only [Matrix.toLinAlgEquiv'_apply]
  constructor
  · rintro ⟨hne, hJ, hmin⟩
    refine ⟨⟨hJ.1, hJ.2⟩, ?_, fun W hW => hmin W ((hinv W).2 hW)⟩
    obtain ⟨i⟩ := hne
    exact ⟨⟨0, Pi.single i 1, fun h => by
      have := congrFun h i
      simp at this⟩⟩
  · rintro ⟨hJ, hnt, hmin⟩
    refine ⟨?_, ⟨hJ.cs, hJ.anti⟩, fun W hW => hmin W ((hinv W).1 hW)⟩
    by_contra h
    rw [not_nonempty_iff] at h
    obtain ⟨x, y, hxy⟩ := hnt
    exact hxy (funext fun i => (IsEmpty.false i).elim)

/-- For `k ≤ 8`, `ℝ^{m_k}` (with the project's explicit structures) is a minimal space. -/
theorem exists_min (k : ℕ) (hk : k ≤ 8) :
    ∃ Js : ℕ → Mat (Fin (Morse.milnorM k)), IsMinACSp Js k := by
  obtain ⟨J, hJ⟩ := Morse.exists_isAnticommFamily_fin hk
  refine ⟨J, (isMinACSp_iff J k).2 ⟨hJ, ?_⟩⟩
  exact Morse.isMinimal_of_finrank_eq_milnorM hk hJ.isClifford_toLin'
    (by rw [Module.finrank_fin_fun])

/-- For `k ≤ 8`, every minimal space has dimension `m_k` (the project's
`finrank_eq_milnorM_of_isMinimal`). -/
theorem eq_milnorM {k : ℕ} (hk : k ≤ 8) {Js : ℕ → Mat (Fin n)} (h : IsMinACSp Js k) :
    n = Morse.milnorM k := by
  obtain ⟨hJ, hmin⟩ := (isMinACSp_iff Js k).1 h
  have := Morse.finrank_eq_milnorM_of_isMinimal hk hJ.isClifford_toLin' hmin
  rwa [Module.finrank_fin_fun] at this

/-- **The blind `m_k` is the project's `milnorM k` for `k ≤ 8`.** -/
theorem mk_eq_milnorM {k : ℕ} (hk : k ≤ 8) : mk k = Morse.milnorM k := by
  have hmem : Morse.milnorM k ∈ {n : ℕ | ∃ Js : ℕ → Mat (Fin n), IsMinACSp Js k} :=
    exists_min k hk
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ fun m hm => ?_)
  obtain ⟨Js, hJs⟩ := hm
  exact (eq_milnorM hk hJs).ge

end Vocab

/-- B restricted to `k ≤ 8` (existence, uniqueness of the dimension, the table
`1, 2, 4, 4, 8, 8, 8, 8, 16`) holds, from the project's results. -/
theorem B_le_eight :
    (∀ k : ℕ, k ≤ 8 → ∃ (n : ℕ) (Js : ℕ → Mat (Fin n)), IsMinACSp Js k) ∧
    (∀ (k n : ℕ) (Js : ℕ → Mat (Fin n)), k ≤ 8 → IsMinACSp Js k → n = mk k) ∧
    mk 0 = 1 ∧ mk 1 = 2 ∧ mk 2 = 4 ∧ mk 3 = 4 ∧ mk 4 = 8 ∧ mk 5 = 8 ∧ mk 6 = 8 ∧ mk 7 = 8 ∧
      mk 8 = 16 := by
  refine ⟨fun k hk => ⟨_, exists_min k hk⟩, fun k n Js hk h => by
    rw [mk_eq_milnorM hk]; exact eq_milnorM hk h, ?_⟩
  simp only [mk_eq_milnorM (by norm_num : (0 : ℕ) ≤ 8), mk_eq_milnorM (by norm_num : (1 : ℕ) ≤ 8),
    mk_eq_milnorM (by norm_num : (2 : ℕ) ≤ 8), mk_eq_milnorM (by norm_num : (3 : ℕ) ≤ 8),
    mk_eq_milnorM (by norm_num : (4 : ℕ) ≤ 8), mk_eq_milnorM (by norm_num : (5 : ℕ) ≤ 8),
    mk_eq_milnorM (by norm_num : (6 : ℕ) ≤ 8), mk_eq_milnorM (by norm_num : (7 : ℕ) ≤ 8),
    mk_eq_milnorM (le_refl 8)]
  decide

#rt_check RoundTrip.V15_13.B_to_A [Morse.IsMinimalCliffordModule, Morse.milnorM]
#rt_overlap RoundTrip.V15_13.B_to_A [Morse.IsMinimalCliffordModule, Morse.milnorM]

end RoundTrip.V15_13
