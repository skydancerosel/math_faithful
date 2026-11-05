import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_16

open Module
open scoped ContDiff Manifold

namespace RoundTrip.V3_16

/-- The project's statement: the one listed theorem (`Morse.critCount` is a definition),
universes instantiated at `0`. -/
def A : Prop := type_of% @Morse.finsum_neg_one_pow_indexM_eq_sum_critCount.{0, 0}

theorem A_holds : A := @Morse.finsum_neg_one_pow_indexM_eq_sum_critCount.{0, 0}

/-- Vocabulary check: B's `Cnum` is the project's `critCount` (`Morse.critCount`, a listed
definition), by `rfl`: both are the `ncard` of the same set. -/
theorem Cnum_eq_critCount {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (l : ℕ) :
    Cnum E f l = Morse.critCount E f l := rfl

/-- `B` holds outright: a Morse function on a compact manifold has finitely many critical
points (`IsMorseFunction.finite_setOf_isCriticalPointM`, Corollary 2.3), and the index is at most
the dimension (`indexM_le_finrank`). Neither uses the listed theorem. -/
theorem B_holds : B := by
  intro E _ _ _ M _ _ _ _ _ f hf hnd
  have hg : Morse.IsMorseFunction E f := ⟨hf, fun p hp ↦ (hnd p hp).2⟩
  have hfin := hg.finite_setOf_isCriticalPointM
  refine ⟨hfin, fun l ↦ hfin.subset fun p hp ↦ hp.1, fun l hl ↦ ?_⟩
  unfold Cnum
  convert Set.ncard_empty M
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ h
  have := Morse.indexM_le_finrank (E := E) f p
  omega

theorem A_to_B : A → B := fun _ ↦ B_holds

#rt_check RoundTrip.V3_16.A_to_B [Morse.finsum_neg_one_pow_indexM_eq_sum_critCount]

end RoundTrip.V3_16
