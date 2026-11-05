import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_8

/-! # Round trip for VA_8 (Milnor, Appendix p. 150: Example 3)

`A` is the conjunction of the types of `Morse.isClosed_example3Set`, `Morse.iUnion_example3Set`
and `Morse.example3` (no universe parameters: the space is `unitInterval`).

Glue: the blind `Xi i = {x | x = 0 ∨ 1/(i+1) ≤ x}` is the project's `example3Set i` (`x = 0` in
`unitInterval` vs `(x : ℝ) = 0`); the blind telescope `tel S` and the project's `telescope S` are
equal subsets of `X × ℝ`, related by `Homeomorph.setCongr`, and
`IsHDL S ↔ Monotone S ∧ Morse.IsHomotopyDirectLimit S` (as in Items/VA_4.lean).
Monotonicity, which `B` lists and `A` does not, is the project lemma
`Morse.monotone_example3Set` (not one of the item's theorems). -/

namespace RoundTrip.VA_8

open Set

/-- `A`: the three listed theorems. -/
def A : Prop :=
  (type_of% @Morse.isClosed_example3Set) ∧ (type_of% @Morse.iUnion_example3Set) ∧
    (type_of% @Morse.example3)

theorem A_holds : A :=
  ⟨Morse.isClosed_example3Set, Morse.iUnion_example3Set, Morse.example3⟩

/-! ### Glue -/

section Glue

variable {X : Type} [TopologicalSpace X]

omit [TopologicalSpace X] in
theorem tel_eq_telescope (S : ℕ → Set X) : tel S = Morse.telescope S := by
  ext z
  simp only [tel, Morse.telescope, mem_iUnion, mem_prod, mem_Icc]; rfl

/-- The identity homeomorphism `tel S ≃ₜ telescope S`. -/
noncomputable def telHomeo (S : ℕ → Set X) : ↥(tel S) ≃ₜ ↥(Morse.telescope S) :=
  Homeomorph.setCongr (tel_eq_telescope S)

theorem telProj_eq (S : ℕ → Set X) :
    telProj S = (Morse.telescopeProj S).comp (telHomeo S : C(↥(tel S), ↥(Morse.telescope S))) :=
  rfl

theorem isHE_iff {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (f : C(P, Q)) :
    IsHE f ↔ Morse.IsHomotopyEquiv f :=
  ⟨fun ⟨g, h₁, h₂⟩ => ⟨g, h₂, h₁⟩, fun ⟨g, h₁, h₂⟩ => ⟨g, h₂, h₁⟩⟩

theorem isHomotopyEquiv_comp_homeo_iff {P P' Q : Type} [TopologicalSpace P] [TopologicalSpace P']
    [TopologicalSpace Q] (f : C(P, Q)) (e : P' ≃ₜ P) :
    Morse.IsHomotopyEquiv (f.comp (e : C(P', P))) ↔ Morse.IsHomotopyEquiv f := by
  constructor
  · intro h
    have h' := (Morse.IsHomotopyEquiv.of_homeomorph e.symm).comp h
    have : (f.comp (e : C(P', P))).comp (e.symm : C(P, P')) = f := by
      ext x; simp
    rwa [this] at h'
  · intro h
    exact (Morse.IsHomotopyEquiv.of_homeomorph e).comp h

theorem isHDL_iff (S : ℕ → Set X) :
    IsHDL S ↔ Monotone S ∧ Morse.IsHomotopyDirectLimit S := by
  unfold IsHDL Morse.IsHomotopyDirectLimit
  rw [isHE_iff, telProj_eq, isHomotopyEquiv_comp_homeo_iff]

end Glue

/-- The blind sets are the project's sets. -/
theorem Xi_eq : Xi = Morse.example3Set := by
  funext i
  ext x
  simp only [Xi, Morse.example3Set, mem_ofPred_eq]
  rw [← Set.Icc.coe_eq_zero]

/-! ### The round trip -/

/-- `A ⇒ B`: closedness, union and `¬ IsHDL` from `A`; monotonicity is the project lemma
`Morse.monotone_example3Set`. -/
theorem A_to_B : A → B := by
  rintro ⟨h₁, h₂, h₃⟩
  rw [B, Xi_eq]
  refine ⟨h₁, Morse.monotone_example3Set, h₂, ?_⟩
  rw [isHDL_iff]
  exact fun h => h₃ h.2

/-- `B ⇒ A`: all three clauses from `B` (the last one using `B`'s monotonicity). -/
theorem B_to_A : B → A := by
  rw [B, Xi_eq]
  rintro ⟨h₁, hm, h₂, h₃⟩
  rw [isHDL_iff] at h₃
  exact ⟨h₁, h₂, fun h => h₃ ⟨hm, h⟩⟩

#rt_check RoundTrip.VA_8.A_to_B [Morse.isClosed_example3Set, Morse.iUnion_example3Set, Morse.example3]
#rt_check RoundTrip.VA_8.B_to_A [Morse.isClosed_example3Set, Morse.iUnion_example3Set, Morse.example3]
#rt_overlap RoundTrip.VA_8.B_to_A [Morse.isClosed_example3Set, Morse.iUnion_example3Set, Morse.example3]
#rt_overlap RoundTrip.VA_8.A_to_B [Morse.isClosed_example3Set, Morse.iUnion_example3Set, Morse.example3]

end RoundTrip.VA_8
