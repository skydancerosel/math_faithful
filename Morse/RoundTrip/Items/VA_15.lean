import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_15

/-! # Round trip for VA_15 (Milnor, Appendix p. 150: Theorem A, exactly as stated)

The item lists the definition `Morse.mappingTelescopeMap` and two theorems:
`Morse.mapsTo_mappingTelescopeMap` (the map of mapping telescopes of the inclusions induced by `f`
preserves the truncations) and `Morse.theoremA_general` (Theorem A with no closedness hypothesis).
`A` is the conjunction of their types, universes at `0`.

`B` is Theorem A as Milnor states it, with Mathlib's `ContinuousMap.HomotopyEquiv` structures
(`∃ e : X_i ≃ₕ Y_i` with underlying map `f|X_i`, conclusion `∃ e : X ≃ₕ Y` with underlying map
`f`).

* `A ⇒ B`: `A`'s second clause, after the vocabulary glue (`IsHDL S ↔ Monotone S ∧
  IsHomotopyDirectLimit S`; `∃ e : P ≃ₕ Q, ⇑e = g ↔ IsHomotopyEquiv g`).
* `B ⇒ A`: `B` gives `A`'s second clause; the first clause (a two-line bookkeeping lemma about the
  mapping telescope, not in `B`) is proved outright. -/

namespace RoundTrip.VA_15

open Set

/-- `A`: the two listed theorems, universes at `0`. -/
def A : Prop :=
  (type_of% @Morse.mapsTo_mappingTelescopeMap.{0, 0}) ∧
    (type_of% @Morse.theoremA_general.{0, 0})

theorem A_holds : A := ⟨@Morse.mapsTo_mappingTelescopeMap, @Morse.theoremA_general⟩

/-! ### Glue -/

section Glue

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

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

/-- "`g` underlies a `HomotopyEquiv`" is the project's `IsHomotopyEquiv g`. -/
theorem exists_he_iff {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (g : C(P, Q)) :
    (∃ e : ContinuousMap.HomotopyEquiv P Q, ∀ x, e x = g x) ↔ Morse.IsHomotopyEquiv g := by
  constructor
  · rintro ⟨e, he⟩
    have : e.toFun = g := ContinuousMap.ext he
    rw [← this]
    exact Morse.IsHomotopyEquiv.of_homotopyEquiv e
  · intro h
    obtain ⟨e, he⟩ := h.exists_homotopyEquiv
    exact ⟨e, fun x => by rw [← he]⟩

end Glue

/-! ### The round trip -/

/-- `A ⇒ B`: `A`'s second clause (Theorem A without closedness). -/
theorem A_to_B : A → B := by
  rintro ⟨-, hA⟩ X Y _ _ S T hS hT f hf
  rw [isHDL_iff] at hS hT
  choose h hfe using hf
  rw [exists_he_iff]
  exact hA hS.1 hT.1 hS.2 hT.2 f (fun n x hx => h n x hx)
    fun n => (exists_he_iff (resC f (h n))).1 (hfe n)

/-- `B ⇒ A`: the second clause from `B`; the first (truncations are preserved) outright. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro X _ S Y _ T hS hT f hf m z hz
    obtain ⟨n, k, t, rfl⟩ := Morse.MappingTelescope.exists_mk _ z
    exact hz
  · intro X _ S Y _ T hS hT hX hY f hf hfe
    have := hB X Y S T ((isHDL_iff S).2 ⟨hS, hX⟩) ((isHDL_iff T).2 ⟨hT, hY⟩) f
      (fun i => ⟨fun x hx => hf i hx, (exists_he_iff _).2 (hfe i)⟩)
    exact (exists_he_iff f).1 this

#rt_check RoundTrip.VA_15.A_to_B [Morse.mapsTo_mappingTelescopeMap, Morse.theoremA_general]
#rt_check RoundTrip.VA_15.B_to_A [Morse.mapsTo_mappingTelescopeMap, Morse.theoremA_general]
#rt_overlap RoundTrip.VA_15.B_to_A [Morse.mapsTo_mappingTelescopeMap, Morse.theoremA_general]

end RoundTrip.VA_15
