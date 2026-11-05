import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_4

/-! # Round trip for VA_4 (Milnor, Appendix p. 150: `f_Σ`, and "clearly sufficient")

`A` is the conjunction of the types (universes at `0`) of `Morse.telescopeProj_comp_telescopeMap`
(`p_Y ∘ f_Σ = f ∘ p_X`) and `Morse.IsHomotopyEquiv.of_telescopeMap` (if `X`, `Y` are homotopy
direct limits and `f_Σ` is a homotopy equivalence, so is `f`).

Glue: the blind telescope `tel S` and the project's `telescope S` are equal subsets of `X × ℝ`
(propositionally, not definitionally), so the types are related by the identity homeomorphism
`Homeomorph.setCongr`; `fSig` and `telProj` are `telescopeMap` and `telescopeProj` transported
along it; `IsHDL S ↔ Monotone S ∧ IsHomotopyDirectLimit S`; `IsHE ↔ IsHomotopyEquiv` (conjuncts
swapped).

Difference: the project's homotopy-direct-limit notion (hence `of_telescopeMap`) does not require
the sequences to be increasing, while the blind `IsHDL` does. So `B` gives `A`'s second clause only
for monotone sequences (`B_to_A_mono`); the general case is a 2-out-of-3 argument that does not
use the telescope at all, proved outright in `B_to_A`. -/

namespace RoundTrip.VA_4

open Set

/-- `A`: the two listed theorems, universes at `0`. -/
def A : Prop :=
  (type_of% @Morse.telescopeProj_comp_telescopeMap.{0, 0}) ∧
  (type_of% @Morse.IsHomotopyEquiv.of_telescopeMap.{0, 0})

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

theorem fSig_eq (f : C(X, Y)) {S : ℕ → Set X} {T : ℕ → Set Y} (h : ∀ i, ∀ x ∈ S i, f x ∈ T i) :
    fSig f h = ((telHomeo T).symm : C(↥(Morse.telescope T), ↥(tel T))).comp
      ((Morse.telescopeMap f (fun i _ hx => h i _ hx)).comp
        (telHomeo S : C(↥(tel S), ↥(Morse.telescope S)))) :=
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

theorem isHomotopyEquiv_homeo_comp_iff {P Q Q' : Type} [TopologicalSpace P] [TopologicalSpace Q']
    [TopologicalSpace Q] (f : C(P, Q)) (e : Q ≃ₜ Q') :
    Morse.IsHomotopyEquiv ((e : C(Q, Q')).comp f) ↔ Morse.IsHomotopyEquiv f := by
  constructor
  · intro h
    have h' := h.comp (Morse.IsHomotopyEquiv.of_homeomorph e.symm)
    have : (e.symm : C(Q', Q)).comp ((e : C(Q, Q')).comp f) = f := by
      ext x; simp
    rwa [this] at h'
  · intro h
    exact h.comp (Morse.IsHomotopyEquiv.of_homeomorph e)

theorem isHDL_iff (S : ℕ → Set X) :
    IsHDL S ↔ Monotone S ∧ Morse.IsHomotopyDirectLimit S := by
  unfold IsHDL Morse.IsHomotopyDirectLimit
  rw [isHE_iff, telProj_eq, isHomotopyEquiv_comp_homeo_iff]

theorem isHE_fSig_iff (f : C(X, Y)) {S : ℕ → Set X} {T : ℕ → Set Y}
    (h : ∀ i, ∀ x ∈ S i, f x ∈ T i) :
    IsHE (fSig f h) ↔ Morse.IsHomotopyEquiv (Morse.telescopeMap f (fun i _ hx => h i _ hx)) := by
  rw [isHE_iff, fSig_eq, isHomotopyEquiv_homeo_comp_iff, isHomotopyEquiv_comp_homeo_iff]

end Glue

/-! ### The round trip -/

/-- `A ⇒ B` (uses `A`'s second clause; the first two clauses of `B` are `rfl`). -/
theorem A_to_B : A → B := by
  rintro ⟨-, hA⟩ X Y _ _ S T f h
  refine ⟨fun _ => rfl, rfl, ?_⟩
  intro hS hT hf
  rw [isHDL_iff] at hS hT
  rw [isHE_fSig_iff] at hf
  exact (isHE_iff f).2 (hA hS.2 hT.2 hf)

/-- `B ⇒ A` on the common domain (increasing sequences): `B`'s third clause gives
`of_telescopeMap`. -/
theorem B_to_A_mono (hB : B) {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {S : ℕ → Set X} {T : ℕ → Set Y} (hSm : Monotone S) (hTm : Monotone T) {f : C(X, Y)}
    {hf : ∀ n, MapsTo f (S n) (T n)} (hX : Morse.IsHomotopyDirectLimit S)
    (hY : Morse.IsHomotopyDirectLimit T) (h : Morse.IsHomotopyEquiv (Morse.telescopeMap f hf)) :
    Morse.IsHomotopyEquiv f := by
  have hf' : ∀ i, ∀ x ∈ S i, f x ∈ T i := fun i x hx => hf i hx
  have := (hB X Y S T f hf').2.2 ((isHDL_iff S).2 ⟨hSm, hX⟩) ((isHDL_iff T).2 ⟨hTm, hY⟩)
    ((isHE_fSig_iff f hf').2 h)
  exact (isHE_iff f).1 this

/-- `B ⇒ A`. The first clause is `B`'s second clause transported (both are `rfl`). For the second
clause, `B` covers only increasing sequences (its `IsHDL` includes `Monotone`), while `A` allows
arbitrary ones; the general case is Milnor's 2-out-of-3 argument, re-proved here outright
(`f ≃ f ∘ p_X ∘ s = p_Y ∘ f_Σ ∘ s` with `s` a homotopy inverse of `p_X`). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨@fun _ _ _ _ _ _ _ _ => rfl, ?_⟩
  intro X S _ Y _ T f hf hX hY h
  obtain ⟨s, hs₁, hs₂⟩ := hX
  have hs : Morse.IsHomotopyEquiv s := ⟨Morse.telescopeProj S, hs₂, hs₁⟩
  have h1 : Morse.IsHomotopyEquiv
      ((Morse.telescopeProj T).comp ((Morse.telescopeMap f hf).comp s)) :=
    (hs.comp h).comp hY
  have heq : (Morse.telescopeProj T).comp ((Morse.telescopeMap f hf).comp s) =
      f.comp ((Morse.telescopeProj S).comp s) := rfl
  rw [heq] at h1
  have h2 : (f.comp ((Morse.telescopeProj S).comp s)).Homotopic f := by
    have := (ContinuousMap.Homotopic.refl f).comp hs₂
    rwa [ContinuousMap.comp_id] at this
  exact h1.of_homotopic h2

#rt_check RoundTrip.VA_4.A_to_B [Morse.telescopeProj_comp_telescopeMap, Morse.IsHomotopyEquiv.of_telescopeMap]
#rt_check RoundTrip.VA_4.B_to_A [Morse.telescopeProj_comp_telescopeMap, Morse.IsHomotopyEquiv.of_telescopeMap]
#rt_check RoundTrip.VA_4.B_to_A_mono [Morse.telescopeProj_comp_telescopeMap, Morse.IsHomotopyEquiv.of_telescopeMap]
#rt_overlap RoundTrip.VA_4.B_to_A [Morse.telescopeProj_comp_telescopeMap, Morse.IsHomotopyEquiv.of_telescopeMap]
#rt_overlap RoundTrip.VA_4.B_to_A_mono [Morse.telescopeProj_comp_telescopeMap, Morse.IsHomotopyEquiv.of_telescopeMap]

end RoundTrip.VA_4
