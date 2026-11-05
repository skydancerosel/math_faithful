import Morse
import RoundTrip.Check
import RoundTrip.Blind.V2_1

open scoped unitInterval

namespace RoundTrip.V2_1

/-- The project's statement (`IsStrongDeformationRetract.exists_homotopyEquiv`), universe
instantiated at `0`. (`Morse.sublevel` and `Morse.IsStrongDeformationRetract` are vocabulary.) -/
def A : Prop := type_of% @Morse.IsStrongDeformationRetract.exists_homotopyEquiv.{0}

theorem A_holds : A := @Morse.IsStrongDeformationRetract.exists_homotopyEquiv.{0}

/-! ### Vocabulary: Milnor's `r_t` (blind `DefRetract`) is the project's `IsStrongDeformationRetract`. -/

theorem isSDR_of_defRetract {Y : Type} [TopologicalSpace Y] {S : Set Y} (h : DefRetract S) :
    Morse.IsStrongDeformationRetract S := by
  obtain ⟨r, hc, h0, h1, hS⟩ := h
  refine ⟨⟨r 1, hc.comp (continuous_const.prodMk continuous_id)⟩, h1,
    ⟨{ toFun := fun z => r z.1 z.2
       continuous_toFun := hc
       map_zero_left := h0
       map_one_left := fun _ => rfl
       prop' := ?_ }⟩⟩
  intro t x hx
  simp [hS x hx t]

theorem defRetract_of_isSDR {Y : Type} [TopologicalSpace Y] {S : Set Y}
    (h : Morse.IsStrongDeformationRetract S) : DefRetract S := by
  obtain ⟨r, hr, ⟨H⟩⟩ := h
  refine ⟨fun t x => H (t, x), H.continuous, fun x => H.apply_zero x, fun x => ?_,
    fun a ha t => H.eq_fst t ha⟩
  change H (1, x) ∈ S
  rw [H.apply_one]
  exact hr x

theorem defRetract_iff {Y : Type} [TopologicalSpace Y] (S : Set Y) :
    DefRetract S ↔ Morse.IsStrongDeformationRetract S :=
  ⟨isSDR_of_defRetract, defRetract_of_isSDR⟩

theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun M f a => rfl, fun X _ S hS => ?_⟩
  -- view `S` inside `univ`
  have hS' : Morse.IsStrongDeformationRetract ((↑) ⁻¹' S : Set (Set.univ : Set X)) := by
    obtain ⟨r, hc, h0, h1, hfix⟩ := hS
    refine isSDR_of_defRetract ⟨fun t x => ⟨r t x.1, trivial⟩, ?_, fun x => ?_, fun x => h1 x.1,
      fun a ha t => Subtype.ext (hfix a.1 ha t)⟩
    · exact (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    · exact Subtype.ext (h0 x.1)
  obtain ⟨e, he⟩ := hA (T := X) (A := S) (B := Set.univ) (Set.subset_univ S) hS'
  refine ⟨e.trans (Homeomorph.Set.univ X).toHomotopyEquiv, fun x => ?_⟩
  change (Homeomorph.Set.univ X) (e x) = x.1
  rw [show (e x) = Set.inclusion (Set.subset_univ S) x from congrFun he x]
  rfl

theorem B_to_A : B → A := by
  intro hB T _ S Bs hAB h
  obtain ⟨k, hk⟩ := hB.2 Bs ((↑) ⁻¹' S) (defRetract_of_isSDR h)
  let φ : S ≃ₜ ((↑) ⁻¹' S : Set Bs) :=
    { toFun := fun a => ⟨⟨a.1, hAB a.2⟩, a.2⟩
      invFun := fun b => ⟨b.1.1, b.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := ((continuous_subtype_val).subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨φ.toHomotopyEquiv.trans k, funext fun a => ?_⟩
  change k (φ a) = Set.inclusion hAB a
  rw [hk]
  rfl

#rt_check RoundTrip.V2_1.A_to_B [Morse.IsStrongDeformationRetract.exists_homotopyEquiv]
#rt_check RoundTrip.V2_1.B_to_A [Morse.IsStrongDeformationRetract.exists_homotopyEquiv]
#rt_overlap RoundTrip.V2_1.B_to_A [Morse.IsStrongDeformationRetract.exists_homotopyEquiv]

end RoundTrip.V2_1
