import Morse
import RoundTrip.L2.Blind.Morse_formIndex
namespace RoundTrip.L2.Morse_formIndex

open Module

/-- The project's index (supremum over the *finite dimensional* negative definite subspaces of
their `finrank`) equals the textbook one (supremum over *all* negative definite subspaces of
their rank, read in `ℕ∞`): an infinite dimensional negative definite subspace contains finite
dimensional ones of every dimension. -/
theorem agree {M : Type*} [AddCommGroup M] [Module ℝ M] (B : LinearMap.BilinForm ℝ M) :
    Morse.formIndex B = T B := by
  apply le_antisymm
  · refine Morse.formIndex_le fun S hS hneg => ?_
    refine le_iSup₂_of_le (f := fun (S : Submodule ℝ M) (_ : IsNegDef B S) =>
      (Module.rank ℝ S).toENat) S hneg ?_
    rw [← Module.finrank_eq_rank]
    simp
  · refine iSup₂_le fun S hneg => ?_
    refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
    have hn' : (n : Cardinal) ≤ Module.rank ℝ S := by
      have := (Cardinal.enat_gc (n : ℕ∞) (Module.rank ℝ S)).2 hn
      simpa using this
    obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_rank hn'
    let g : Fin n → M := fun i => (f i : M)
    have hg : LinearIndependent ℝ g := hf.map' S.subtype S.ker_subtype
    let S' : Submodule ℝ M := Submodule.span ℝ (Set.range g)
    have : FiniteDimensional ℝ S' := FiniteDimensional.span_of_finite ℝ (Set.finite_range g)
    have hS'S : S' ≤ S := Submodule.span_le.2 (Set.range_subset_iff.2 fun i => (f i).2)
    have hneg' : Morse.IsNegDefOn B S' := fun x hx hx0 => hneg x (hS'S hx) hx0
    have h := Morse.le_formIndex hneg'
    rwa [finrank_span_eq_card hg, Fintype.card_fin] at h

end RoundTrip.L2.Morse_formIndex
