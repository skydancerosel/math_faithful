import Morse
import RoundTrip.L2.Blind.Morse_Homology_TopTriple__
namespace RoundTrip.L2.Morse_Homology_TopTriple__

open CategoryTheory Limits

universe w v u

/-- The blind textbook map on textbook objects (pair boundary of `(X, Y)` followed by
`H_n(Y) → H_n(Y, Z)`) is the project's `TopTriple.δ` (connecting map of
`0 → C(Y,Z) → C(X,Z) → C(X,Y) → 0`), via the project's `TopTriple.δ_eq`. -/
theorem delta_eq_deltaTB (Tri : Morse.Homology.TopTriple.{w}) {C : Type u} [Category.{v} C]
    [Abelian C] [HasCoproducts.{w} C] (R : C) (n : ℕ) :
    Tri.δ R n = deltaTB R n Tri.pairXY Tri.pairYZ rfl := by
  rw [Morse.Homology.TopTriple.δ_eq]
  exact congrArg (pairDelta R n Tri.pairXY ≫ ·) (Category.id_comp (jMap R n Tri.pairYZ)).symm

/-- The literal-equality conditions of the blind `T` hold definitionally (the project's
relative homology objects *are* the textbook `H(C(X)/C(A))`), so `T` is `deltaTB`, which is the
project's `δ`: equal outright. -/
theorem agree (Tri : Morse.Homology.TopTriple.{w}) {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (n : ℕ) :
    Tri.δ R n = T Tri R n := by
  unfold T
  rw [dif_pos ⟨rfl, rfl, rfl⟩, delta_eq_deltaTB]
  show _ = 𝟙 _ ≫ deltaTB R n Tri.pairXY Tri.pairYZ rfl ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

end RoundTrip.L2.Morse_Homology_TopTriple__
