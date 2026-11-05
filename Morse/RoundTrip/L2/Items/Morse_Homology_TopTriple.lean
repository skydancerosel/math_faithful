import Morse
import RoundTrip.L2.Blind.Morse_Homology_TopTriple
namespace RoundTrip.L2.Morse_Homology_TopTriple

open CategoryTheory

universe w

/-- The project's triples carry an extra field `k : Z ⟶ X` with `fac : i ≫ j = k`; it is
determined by the other data, so forgetting it is an equivalence with the blind triples. -/
def equiv : Morse.Homology.TopTriple.{w} ≃ T.{w} where
  toFun t := ⟨t.X, t.Y, t.Z, t.j, t.i, t.isEmbedding_j, t.isEmbedding_i⟩
  invFun s := ⟨s.X, s.Y, s.Z, s.incZY, s.incYX, s.incZY ≫ s.incYX, rfl, s.isEmbedding_incZY,
    s.isEmbedding_incYX⟩
  left_inv t := by
    obtain ⟨X, Y, Z, i, j, k, fac, hi, hj⟩ := t
    subst fac
    rfl
  right_inv _ := rfl

theorem agree : Nonempty (Morse.Homology.TopTriple.{w} ≃ T.{w}) := ⟨equiv⟩

/-- The equivalence preserves the three pairs (the pair `(X, Z)` up to the equation `fac`). -/
theorem equiv_pairXY (t : Morse.Homology.TopTriple.{w}) :
    Triple.pairXY (equiv t) = t.pairXY := rfl

theorem equiv_pairYZ (t : Morse.Homology.TopTriple.{w}) :
    Triple.pairYZ (equiv t) = t.pairYZ := rfl

theorem equiv_pairXZ (t : Morse.Homology.TopTriple.{w}) :
    Triple.pairXZ (equiv t) = t.pairXZ := by
  obtain ⟨X, Y, Z, i, j, k, fac, hi, hj⟩ := t
  subst fac
  rfl

end RoundTrip.L2.Morse_Homology_TopTriple
