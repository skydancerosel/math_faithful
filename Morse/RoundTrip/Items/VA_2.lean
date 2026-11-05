import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_2

/-! # Round trip for VA_2 (Milnor, Appendix p. 149: the telescope, homotopy direct limits)

The item lists four definitions (`Morse.telescope`, `Morse.stripMap`, `Morse.telescopeProj`,
`Morse.IsHomotopyDirectLimit`) and one theorem, `Morse.mem_telescope_iff` (property (T1): for a
monotone sequence, `(x, τ) ∈ X_Σ ↔ ∃ n ≤ τ, x ∈ X_n`), so `A` is the type of that theorem
(universe instantiated at `0`).

Both `A` and `B` are provable outright, so the round trip is vacuous; the substance of the item is
the vocabulary check below: the blind telescope `tel S` is the project's `telescope S`, the blind
projection is `telescopeProj` (transported along the identity homeomorphism `tel S ≃ₜ telescope S`),
and `IsHDL S ↔ Monotone S ∧ Morse.IsHomotopyDirectLimit S`. The only difference: the project's
`IsHomotopyDirectLimit` does not require the sequence to be increasing, the blind `IsHDL` does
(Milnor's standing assumption `X₀ ⊂ X₁ ⊂ ⋯`). -/

namespace RoundTrip.VA_2

open Set

/-- `A`: the type of `Morse.mem_telescope_iff` at universe `0`. -/
def A : Prop := type_of% @Morse.mem_telescope_iff.{0}

/-- (T1), proved directly (without the item's theorem). -/
theorem A_holds : A := by
  intro X S hS z
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := mem_iUnion.1 hz
    exact ⟨n, hn.1, hn.2.1⟩
  · rintro ⟨n, hx, hn⟩
    have h0 : 0 ≤ z.2 := le_trans (Nat.cast_nonneg n) hn
    exact mem_iUnion.2 ⟨⌊z.2⌋₊, hS (Nat.le_floor hn) hx, Nat.floor_le h0,
      (Nat.lt_floor_add_one z.2).le⟩

/-! ### Vocabulary check -/

section Vocab

variable {X : Type} [TopologicalSpace X]

omit [TopologicalSpace X] in
/-- The blind telescope is the project's telescope. -/
theorem tel_eq_telescope (S : ℕ → Set X) : tel S = Morse.telescope S := by
  ext z
  simp only [tel, Morse.telescope, mem_iUnion, mem_prod, mem_Icc]; rfl

/-- The identity homeomorphism `tel S ≃ₜ telescope S`. -/
noncomputable def telHomeo (S : ℕ → Set X) : ↥(tel S) ≃ₜ ↥(Morse.telescope S) :=
  Homeomorph.setCongr (tel_eq_telescope S)

/-- The blind projection is the project's projection, transported along `telHomeo`. -/
theorem telProj_eq (S : ℕ → Set X) :
    telProj S = (Morse.telescopeProj S).comp (telHomeo S : C(↥(tel S), ↥(Morse.telescope S))) :=
  rfl

theorem isHE_iff {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (f : C(P, Q)) :
    IsHE f ↔ Morse.IsHomotopyEquiv f :=
  ⟨fun ⟨g, h₁, h₂⟩ => ⟨g, h₂, h₁⟩, fun ⟨g, h₁, h₂⟩ => ⟨g, h₂, h₁⟩⟩

/-- Precomposition with a homeomorphism preserves and reflects homotopy equivalences. -/
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

/-- `IsHDL S ↔ Monotone S ∧ IsHomotopyDirectLimit S`: the blind notion adds monotonicity. -/
theorem isHDL_iff (S : ℕ → Set X) :
    IsHDL S ↔ Monotone S ∧ Morse.IsHomotopyDirectLimit S := by
  unfold IsHDL Morse.IsHomotopyDirectLimit
  rw [isHE_iff, telProj_eq, isHomotopyEquiv_comp_homeo_iff]

end Vocab

/-- `B` holds outright (with `tel S = ⋃ …` and the reformulation of `IsHDL`). -/
theorem B_holds : B := by
  intro X _ S
  refine ⟨?_, ?_⟩
  · ext z
    simp only [tel, mem_iUnion, mem_prod, mem_Icc]; rfl
  · constructor
    · rintro ⟨hm, g, h₁, h₂⟩
      exact ⟨hm, ⟨telProj S, g, h₂, h₁⟩, fun _ => rfl⟩
    · rintro ⟨hm, e, he⟩
      refine ⟨hm, e.invFun, ?_, ?_⟩
      · have : e.toFun = telProj S := ContinuousMap.ext he
        have h := e.right_inv
        rwa [this] at h
      · have : e.toFun = telProj S := ContinuousMap.ext he
        have h := e.left_inv
        rwa [this] at h

/-- `A ⇒ B`: vacuous (`B` holds outright; `A` is about monotone sequences only and says
nothing about the shape of `tel S` for a general `S`). -/
theorem A_to_B : A → B := fun _ => B_holds

/-- `B ⇒ A`: vacuous (`A` is proved outright; `B` does not contain (T1)). -/
theorem B_to_A : B → A := fun _ => A_holds

#rt_check RoundTrip.VA_2.A_to_B [Morse.mem_telescope_iff]
#rt_check RoundTrip.VA_2.B_to_A [Morse.mem_telescope_iff]
#rt_overlap RoundTrip.VA_2.B_to_A [Morse.mem_telescope_iff]
#rt_check RoundTrip.VA_2.isHDL_iff [Morse.mem_telescope_iff]

end RoundTrip.VA_2
