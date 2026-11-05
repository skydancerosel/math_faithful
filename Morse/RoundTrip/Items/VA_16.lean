import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_16

/-! # Round trip for VA_16 (Milnor, Appendix p. 150: monotone unions, final step of Thm 17.3)

`A` is the conjunction of the types (universes `0`) of `Morse.nonempty_homotopyEquiv_telescope`
(subspace form: `X = hdl{X_i}`, closed `Y_i ⊆ Y`, `f : X → Y` restricting to homotopy
equivalences `X_i → Y_i` ⇒ `X ≃ₕ Y_Σ`, the TELESCOPE of the `Y_i`), `Morse.isHomotopyEquiv_compareMap`
(Milnor's `G` from a mapping telescope `K_Σ` to `X_Σ` is a homotopy equivalence) and
`Morse.nonempty_homotopyEquiv_mappingTelescope` (mapping-telescope form: `X = hdl{X_n}`,
`g_n : X_n → K_n` homotopy equivalences with homotopy-commutative squares ⇒ `X ≃ₕ` the mapping
telescope of the `K_n`). `Morse.compareMap` is vocabulary.

`B` (abstract complete Riemannian manifold, `p, q` non-conjugate, admissible levels `a_i`): for
EVERY Hausdorff Mathlib CW complex `Y` with exhausting increasing subcomplexes `K_i` and strictly
commutative homotopy equivalences `e_i : Ω^{a_i} → K_i`: `Ω = hdl{Ω^{a_i}}` (Example 1),
`Y = hdl{K_i}` (Example 2), and the limit map `Ω → Y` exists and is a homotopy equivalence
(Theorem A).

* `A ⇒ B` fails genuinely. `B` consists of Example 1 for the blind `Ω`, Example 2 for Mathlib CW
  complexes, and Theorem A for the limit map; none of them is in `A`. `A` deliberately stops at the
  telescope `K_Σ` (or the mapping telescope) instead of the union `K` with its CW topology, because
  Example 2 (Whitehead's theorem in Milnor) is not formalized in the project; and `A`'s conclusions
  are `Nonempty (X ≃ₕ K_Σ)`, not that the limit map is a homotopy equivalence.
* `B ⇒ A` only vacuously: `A` is re-proved outright from the non-listed `Morse.theoremA_telescope`
  and `Morse.theoremA` (the project's route); `B` is about one space `Ω` and Mathlib CW complexes,
  not about telescopes of arbitrary spaces. -/

namespace RoundTrip.VA_16

open Set CategoryTheory

/-- `A`: the three listed theorems, universes at `0`. -/
def A : Prop :=
  (type_of% @Morse.nonempty_homotopyEquiv_telescope.{0, 0}) ∧
    (type_of% @Morse.isHomotopyEquiv_compareMap.{0, 0}) ∧
      (type_of% @Morse.nonempty_homotopyEquiv_mappingTelescope.{0, 0})

section Outright

variable {X : Type} [TopologicalSpace X] {S : ℕ → Set X}

/-- `Morse.isHomotopyEquiv_compareMap` at universe `0`, by the project's proof (Theorem A for the
closed truncations). -/
theorem he_compareMap (F : ℕ ⥤ TopCat.{0}) (hS : Monotone S) (g' : ∀ n, C(F.obj n, S n))
    (hg' : ∀ n, Morse.IsHomotopyEquiv (g' n))
    (H : ∀ n, ((Morse.up hS n).comp (g' n)).Homotopy
      ((g' (n + 1)).comp (Morse.tmap F (Nat.le_add_right n 1)))) :
    Morse.IsHomotopyEquiv (Morse.compareMap F hS g' H) := by
  refine Morse.theoremA (Morse.MappingTelescope.monotone_trunc F) Morse.monotone_truncation
    Morse.isClosed_truncation (Morse.MappingTelescope.isHomotopyDirectLimit_trunc F)
    Morse.isHomotopyDirectLimit_truncation _ (Morse.compareMap_mapsTo F hS g' H) fun m => ?_
  set R := Morse.restrictTo (Morse.compareMap F hS g' H) (Morse.compareMap_mapsTo F hS g' H m)
  have hR : R.comp (Morse.MappingTelescope.levelIncl F m) = (Morse.truncIncl S m).comp (g' m) :=
    ContinuousMap.ext fun k => Subtype.ext (Morse.compareMap_mk_zero F hS g' H m k)
  have h1 : R.Homotopic
      (((Morse.truncIncl S m).comp (g' m)).comp (Morse.MappingTelescope.levelRetract F m)) := by
    have := (ContinuousMap.Homotopic.refl R).comp
      (Morse.MappingTelescope.levelIncl_comp_levelRetract F m).symm
    rwa [ContinuousMap.comp_id, ← ContinuousMap.comp_assoc, hR] at this
  exact (((Morse.MappingTelescope.isHomotopyEquiv_levelRetract F m).comp (hg' m)).comp
    (Morse.isHomotopyEquiv_truncIncl hS m)).of_homotopic h1.symm

theorem he_mappingTelescope (F : ℕ ⥤ TopCat.{0}) (hS : Monotone S)
    (hX : Morse.IsHomotopyDirectLimit S) (g : ∀ n, C(S n, F.obj n))
    (hg : ∀ n, Morse.IsHomotopyEquiv (g n))
    (hsq : ∀ n, ((Morse.tmap F (Nat.le_add_right n 1)).comp (g n)).Homotopic
      ((g (n + 1)).comp (Morse.up hS n))) :
    Nonempty (ContinuousMap.HomotopyEquiv X (Morse.MappingTelescope F)) := by
  choose g' hg'₁ hg'₂ using hg
  have hsq' : ∀ n, ((Morse.up hS n).comp (g' n)).Homotopic
      ((g' (n + 1)).comp (Morse.tmap F (Nat.le_add_right n 1))) := fun n =>
    Morse.homotopic_inverse_square (hsq n) (hg'₂ n) (hg'₁ (n + 1))
  have hΨ := he_compareMap F hS g'
    (fun n => Morse.IsHomotopyEquiv.of_inverse (hg'₁ n) (hg'₂ n)) fun n => (hsq' n).some
  obtain ⟨e₁⟩ := hΨ.nonempty
  obtain ⟨e₂⟩ := hX.nonempty
  exact ⟨(e₁.trans e₂).symm⟩

theorem A_holds' : A := by
  refine ⟨?_, @fun X _ S F hS g' hg' H => he_compareMap F hS g' hg' H,
    @fun X _ S F hS hX g hg hsq => he_mappingTelescope F hS hX g hg hsq⟩
  intro X _ S Y _ T hS hT hTc hX f hf hfe
  obtain ⟨e₁⟩ := hX.nonempty
  obtain ⟨e₂⟩ := (Morse.theoremA_telescope hS hT hTc f hf hfe).nonempty
  exact ⟨e₁.symm.trans e₂⟩

end Outright

/-- `B ⇒ A`: vacuous (`A` holds outright). -/
theorem B_to_A : B → A := fun _ => A_holds'

#rt_check RoundTrip.VA_16.B_to_A [Morse.nonempty_homotopyEquiv_telescope, Morse.isHomotopyEquiv_compareMap, Morse.nonempty_homotopyEquiv_mappingTelescope]
#rt_overlap RoundTrip.VA_16.B_to_A [Morse.nonempty_homotopyEquiv_telescope, Morse.isHomotopyEquiv_compareMap, Morse.nonempty_homotopyEquiv_mappingTelescope]

end RoundTrip.VA_16
