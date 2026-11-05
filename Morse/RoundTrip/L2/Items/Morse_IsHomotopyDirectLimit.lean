import Morse
import RoundTrip.L2.Blind.Morse_IsHomotopyDirectLimit

/-! Layer-2 check of `Morse.IsHomotopyDirectLimit` (the projection `X_Σ → X` is a homotopy
equivalence, for any sequence `A`) against the blind textbook definition (`A` is increasing AND the
projection is a homotopy equivalence). They agree for increasing sequences, Milnor's standing
hypothesis `X₀ ⊆ X₁ ⊆ ⋯`; for a non-increasing sequence the blind notion is false by fiat while
the project's can hold (`A₀ = X = pt`, `Aₙ = ∅` for `n ≥ 1`: `X_Σ = pt × [0,1]`). Every use of
`Morse.IsHomotopyDirectLimit` in the project carries a separate `Monotone A` hypothesis. -/

namespace RoundTrip.L2.Morse_IsHomotopyDirectLimit

open scoped unitInterval

/-- The projection from any subset of `X × ℝ`. -/
def projOn {X : Type} [TopologicalSpace X] (S : Set (X × ℝ)) : C(S, X) :=
  ⟨fun z => z.1.1, continuous_fst.comp continuous_subtype_val⟩

theorem tele_eq {X : Type} (A : ℕ → Set X) : Morse.telescope A = tele A := by
  ext z
  exact Morse.mem_telescope

/-- Without monotonicity: the project's notion is the second conjunct of the blind one. -/
theorem P_iff_proj {X : Type} [TopologicalSpace X] (A : ℕ → Set X) :
    Morse.IsHomotopyDirectLimit A ↔ IsHE (proj A) := by
  change Morse.IsHomotopyEquiv (projOn (Morse.telescope A)) ↔ IsHE (projOn (tele A))
  rw [tele_eq]
  rfl

theorem T_imp_P {X : Type} [TopologicalSpace X] (A : ℕ → Set X) :
    T A → Morse.IsHomotopyDirectLimit A :=
  fun h => (P_iff_proj A).2 h.2

/-- Agreement for increasing sequences (Milnor's hypothesis `X₀ ⊆ X₁ ⊆ ⋯`). -/
theorem agree_of {X : Type} [TopologicalSpace X] (A : ℕ → Set X) (hA : Monotone A) :
    Morse.IsHomotopyDirectLimit A ↔ T A := by
  rw [P_iff_proj]
  exact ⟨fun h => ⟨hA, h⟩, fun h => h.2⟩

/-- The non-increasing sequence `A₀ = univ`, `Aₙ = ∅` (`n ≥ 1`) in a point. -/
def A₀ : ℕ → Set Unit := fun n => if n = 0 then Set.univ else ∅

theorem mem_A₀ {n : ℕ} {x : Unit} (h : x ∈ A₀ n) : n = 0 := by
  by_contra hn
  simp [A₀, hn] at h

theorem not_monotone : ¬ Monotone A₀ := by
  intro h
  have := h (Nat.zero_le 1) (show () ∈ A₀ 0 by simp [A₀])
  exact absurd (mem_A₀ this) one_ne_zero

theorem P_A₀ : Morse.IsHomotopyDirectLimit A₀ := by
  have hmem : ∀ z ∈ Morse.telescope A₀, 0 ≤ z.2 ∧ z.2 ≤ 1 := by
    intro z hz
    obtain ⟨n, hx, h1, h2⟩ := Morse.mem_telescope.1 hz
    obtain rfl := mem_A₀ hx
    simpa using And.intro h1 h2
  have hin : ∀ (x : Unit) (τ : ℝ), 0 ≤ τ → τ ≤ 1 → (x, τ) ∈ Morse.telescope A₀ :=
    fun x τ h0 h1 => Morse.mem_telescope.2 ⟨0, by simp [A₀], by simpa using h0, by simpa using h1⟩
  let g : C(Unit, Morse.telescope A₀) :=
    ContinuousMap.const _ ⟨((), 0), hin () 0 le_rfl zero_le_one⟩
  refine ⟨g, ?_, ?_⟩
  · let H : C(I × Morse.telescope A₀, Morse.telescope A₀) :=
      ⟨fun p => ⟨((p.2 : Unit × ℝ).1, (p.1 : ℝ) * (p.2 : Unit × ℝ).2),
        hin _ _ (mul_nonneg p.1.2.1 (hmem _ p.2.2).1)
          (mul_le_one₀ p.1.2.2 (hmem _ p.2.2).1 (hmem _ p.2.2).2)⟩, by fun_prop⟩
    refine ⟨{ toContinuousMap := H, map_zero_left := fun z => ?_, map_one_left := fun z => ?_ }⟩
    · apply Subtype.ext
      simp [H, g]
    · apply Subtype.ext
      simp [H]
  · exact .refl _

theorem differ : Morse.IsHomotopyDirectLimit A₀ ∧ ¬ T A₀ :=
  ⟨P_A₀, fun h => not_monotone h.1⟩

end RoundTrip.L2.Morse_IsHomotopyDirectLimit
