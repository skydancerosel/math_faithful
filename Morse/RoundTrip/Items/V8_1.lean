import Morse
import RoundTrip.Check
import RoundTrip.Blind.«V8_1»

namespace RoundTrip.«V8_1»

/-- The project's statement (universes instantiated at 0; `pathSpace`, `prj`, `pathTangent` are
definitions — `pathTangent hN c` is a `Submodule ℝ (ℝ → V)`, so "`TΩ_ω` is a vector space" is
built into the definition, not stated by a theorem): membership in `TΩ_c` unfolds to "piecewise
smooth `X : ℝ → V`, tangent (`P_{c(t)} X(t) = X(t)`) on `[0, 1]`, `X 0 = X 1 = 0`", and `TΩ_c`
depends only on `c|[0, 1]`. -/
def A : Prop :=
  type_of% @Morse.mem_pathTangent.{0,0,0} ∧
    type_of% @Morse.mem_pathTangent_congr.{0,0,0}

theorem A_holds : A := ⟨@Morse.mem_pathTangent, @Morse.mem_pathTangent_congr⟩

/-- B ⇒ A holds only because A is provable outright: the first clause is `Iff.rfl` (the membership
condition is the carrier of the `Submodule`), the second is immediate from it. B (about abstract
manifolds) is not used and could not be. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨fun _ => Iff.rfl, ?_⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ c c' X h hX
  exact ⟨hX.1, fun t ht => by rw [← h t ht]; exact hX.2.1 t ht, hX.2.2⟩

#rt_check RoundTrip.«V8_1».B_to_A [Morse.mem_pathTangent, Morse.mem_pathTangent_congr]
#rt_overlap RoundTrip.«V8_1».B_to_A [Morse.mem_pathTangent, Morse.mem_pathTangent_congr]

/-! A ⇒ B is not proved; see `V8_1.json`. -/

end RoundTrip.«V8_1»
