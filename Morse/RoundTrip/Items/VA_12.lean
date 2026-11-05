import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_12

/-! # Round trip for VA_12 (Milnor, Appendix p. 150: Theorem A, as proved)

`A` is the type of `Morse.theoremA` (universes at `0`): Theorem A with the extra hypothesis that
the `Y_i` are **closed** (Milnor's proof pastes his map `G : Y_Σ → X_Σ` strip by strip).
`B` is Theorem A exactly as Milnor states it (no closedness).

* `B ⇒ A`: immediate (`A` has more hypotheses), after the vocabulary glue of VA_2/VA_4
  (`IsHDL S ↔ Monotone S ∧ IsHomotopyDirectLimit S`, `IsHE ↔ IsHomotopyEquiv`,
  `resC = restrictTo`).
* `A ⇒ B`: closedness is removable. Apply the hypothesis `A` to the mapping telescopes of the
  inclusions `X_i ⊆ X_{i+1}`, whose truncations are always closed, and compare them with `X`, `Y`
  (also by `A`, for the closed truncations of `X_Σ`). This is the project's proof of
  `Morse.theoremA_general` with every use of `Morse.theoremA` replaced by the hypothesis. -/

namespace RoundTrip.VA_12

open Set

/-- `A`: the type of `Morse.theoremA`, universes at `0`. -/
def A : Prop := type_of% @Morse.theoremA.{0, 0}

theorem A_holds : A := @Morse.theoremA

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

theorem resC_eq (f : C(X, Y)) {P : Set X} {Q : Set Y} (h : ∀ x ∈ P, f x ∈ Q) :
    resC f h = Morse.restrictTo f (fun x hx => h x hx) :=
  rfl

end Glue

/-! ### `A ⇒ B`: Theorem A without closedness, from Theorem A with closed `Y_i` -/

section General

variable (hThA : A)
include hThA

/-- `Morse.isHomotopyEquiv_telescopeComparison`, with `Morse.theoremA` replaced by `A`. -/
theorem he_telescopeComparison {X : Type} [TopologicalSpace X] {S : ℕ → Set X}
    (hS : Monotone S) : Morse.IsHomotopyEquiv (Morse.telescopeComparison hS) := by
  have hmaps : ∀ m, MapsTo (Morse.telescopeComparison hS) (Morse.MappingTelescope.trunc _ m)
      (Morse.truncation S m) := by
    intro m z hz
    obtain ⟨n, k, t, rfl⟩ := Morse.MappingTelescope.exists_mk _ z
    exact hz
  refine hThA (Morse.MappingTelescope.monotone_trunc _) Morse.monotone_truncation
    Morse.isClosed_truncation (Morse.MappingTelescope.isHomotopyDirectLimit_trunc _)
    Morse.isHomotopyDirectLimit_truncation _ hmaps fun m => ?_
  set R := Morse.restrictTo (Morse.telescopeComparison hS) (hmaps m)
  have hR : R.comp (Morse.MappingTelescope.levelIncl _ m) = Morse.truncIncl S m := rfl
  have h1 : R.Homotopic ((Morse.truncIncl S m).comp
      (Morse.MappingTelescope.levelRetract _ m)) := by
    have := (ContinuousMap.Homotopic.refl R).comp
      (Morse.MappingTelescope.levelIncl_comp_levelRetract (Morse.subspaceFunctor hS) m).symm
    rwa [ContinuousMap.comp_id, ← ContinuousMap.comp_assoc, hR] at this
  exact ((Morse.MappingTelescope.isHomotopyEquiv_levelRetract _ m).comp
    (Morse.isHomotopyEquiv_truncIncl hS m)).of_homotopic h1.symm

theorem he_telescopeProj' {X : Type} [TopologicalSpace X] {S : ℕ → Set X}
    (hS : Monotone S) (hX : Morse.IsHomotopyDirectLimit S) :
    Morse.IsHomotopyEquiv (Morse.telescopeProj' hS) :=
  (he_telescopeComparison hThA hS).comp hX

/-- `Morse.theoremA_general`, with `Morse.theoremA` replaced by `A`. -/
theorem general {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {S : ℕ → Set X}
    {T : ℕ → Set Y} (hS : Monotone S) (hT : Monotone T) (hX : Morse.IsHomotopyDirectLimit S)
    (hY : Morse.IsHomotopyDirectLimit T) (f : C(X, Y)) (hf : ∀ n, MapsTo f (S n) (T n))
    (hfe : ∀ n, Morse.IsHomotopyEquiv (Morse.restrictTo f (hf n))) : Morse.IsHomotopyEquiv f := by
  have hΦ : Morse.IsHomotopyEquiv (Morse.mappingTelescopeMap hS hT f hf) := by
    refine hThA (Morse.MappingTelescope.monotone_trunc _) (Morse.MappingTelescope.monotone_trunc _)
      (Morse.MappingTelescope.isClosed_trunc _)
      (Morse.MappingTelescope.isHomotopyDirectLimit_trunc _)
      (Morse.MappingTelescope.isHomotopyDirectLimit_trunc _) _
      (Morse.mapsTo_mappingTelescopeMap hS hT f hf)
      fun m => ?_
    have hR : (Morse.restrictTo (Morse.mappingTelescopeMap hS hT f hf)
          (Morse.mapsTo_mappingTelescopeMap hS hT f hf m)).comp
          (Morse.MappingTelescope.levelIncl (Morse.subspaceFunctor hS) m) =
        (Morse.MappingTelescope.levelIncl (Morse.subspaceFunctor hT) m).comp
          (Morse.restrictTo f (hf m)) :=
      ContinuousMap.ext fun k => Subtype.ext rfl
    have h1 := (ContinuousMap.Homotopic.refl (Morse.restrictTo
      (Morse.mappingTelescopeMap hS hT f hf) (Morse.mapsTo_mappingTelescopeMap hS hT f hf m))).comp
        (Morse.MappingTelescope.levelIncl_comp_levelRetract (Morse.subspaceFunctor hS) m).symm
    rw [ContinuousMap.comp_id, ← ContinuousMap.comp_assoc, hR] at h1
    have hcomp : Morse.IsHomotopyEquiv
        ((Morse.MappingTelescope.levelIncl (Morse.subspaceFunctor hT) m).comp
          ((Morse.restrictTo f (hf m)).comp
            (Morse.MappingTelescope.levelRetract (Morse.subspaceFunctor hS) m))) :=
      ((Morse.MappingTelescope.isHomotopyEquiv_levelRetract _ m).comp (hfe m)).comp
        (Morse.MappingTelescope.isHomotopyEquiv_levelIncl _ m)
    exact hcomp.of_homotopic h1.symm
  have hcomm : f.comp (Morse.telescopeProj' hS) =
      (Morse.telescopeProj' hT).comp (Morse.mappingTelescopeMap hS hT f hf) :=
    Morse.MappingTelescope.ext _ fun n x t => rfl
  obtain ⟨s, hs₁, hs₂⟩ := he_telescopeProj' hThA hS hX
  have h1 : Morse.IsHomotopyEquiv
      (((Morse.telescopeProj' hT).comp (Morse.mappingTelescopeMap hS hT f hf)).comp s) :=
    (Morse.IsHomotopyEquiv.of_inverse hs₁ hs₂).comp
      (hΦ.comp (he_telescopeProj' hThA hT hY))
  refine h1.of_homotopic ?_
  rw [← hcomm, ContinuousMap.comp_assoc]
  have := (ContinuousMap.Homotopic.refl f).comp hs₂
  rwa [ContinuousMap.comp_id] at this

end General

/-! ### The round trip -/

/-- `A ⇒ B`: by the mapping-telescope argument above (uses `A` three times). -/
theorem A_to_B : A → B := by
  intro hThA X Y _ _ S T hS hT f hf
  rw [isHDL_iff] at hS hT
  choose h hfe using hf
  rw [isHE_iff]
  exact general hThA hS.1 hT.1 hS.2 hT.2 f (fun n x hx => h n x hx)
    fun n => (isHE_iff _).1 (hfe n)

/-- `B ⇒ A`: `A` only adds the closedness hypothesis. -/
theorem B_to_A : B → A := by
  intro hB X _ S Y _ T hS hT _ hX hY f hf hfe
  have := hB X Y S T ((isHDL_iff S).2 ⟨hS, hX⟩) ((isHDL_iff T).2 ⟨hT, hY⟩) f
    (fun i => ⟨fun x hx => hf i hx, (isHE_iff _).2 (hfe i)⟩)
  exact (isHE_iff f).1 this

#rt_check RoundTrip.VA_12.A_to_B [Morse.theoremA]
#rt_check RoundTrip.VA_12.B_to_A [Morse.theoremA]
#rt_overlap RoundTrip.VA_12.A_to_B [Morse.theoremA]
#rt_overlap RoundTrip.VA_12.B_to_A [Morse.theoremA]

end RoundTrip.VA_12
