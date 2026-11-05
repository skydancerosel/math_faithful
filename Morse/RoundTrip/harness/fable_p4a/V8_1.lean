import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_1

namespace RoundTrip.«V8_1»

/-- The project's statement (universes instantiated at 0). The listed declarations are the
definitions `pathSpace`, `prj`, `pathTangent` and two near-definitional theorems:
`mem_pathTangent` (the unfolding of `pathTangent`: piecewise smooth, tangent to `N` along `c` on
`[0, 1]`, vanishing at `0` and `1`) and `mem_pathTangent_congr` (`TΩ_c` depends only on
`c|[0,1]`). -/
def A : Prop :=
  type_of% @Morse.mem_pathTangent.{0,0,0} ∧
    type_of% @Morse.mem_pathTangent_congr.{0,0,0}

theorem A_holds : A := ⟨@Morse.mem_pathTangent, @Morse.mem_pathTangent_congr⟩

/-- `A` holds outright: `mem_pathTangent` is `Iff.rfl` and `mem_pathTangent_congr` follows
by rewriting `c t = c' t` in the tangency condition. -/
theorem A_outright : A := by
  refine ⟨?_, ?_⟩
  · intro V _ _ _ Z _ _ W _ _ N hN c X
    exact Iff.rfl
  · intro V _ _ _ Z _ _ W _ _ N hN c c' X h hX
    exact ⟨hX.1, fun t ht => by rw [← h t ht]; exact hX.2.1 t ht, hX.2.2⟩

/-- Vacuous: `A` is provable outright, the hypothesis `B` is not used. -/
theorem B_to_A : B → A := fun _ => A_outright

/-! `A → B` is not proved; see `V8_1.json`. -/

#rt_check RoundTrip.«V8_1».B_to_A [Morse.mem_pathTangent, Morse.mem_pathTangent_congr]
#rt_overlap RoundTrip.«V8_1».B_to_A [Morse.mem_pathTangent, Morse.mem_pathTangent_congr]

end RoundTrip.«V8_1»
