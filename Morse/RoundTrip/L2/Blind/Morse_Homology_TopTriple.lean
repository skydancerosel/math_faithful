import Morse
/-! Layer-2 blind definition of Morse_Homology_TopTriple. Textbook: Milnor, *Morse Theory*, §5,
p. 30 (a triple `X ⊃ Y ⊃ Z`), Hatcher, *Algebraic Topology*, ch. 2.1 (triples `(X, A, B)`,
`B ⊂ A ⊂ X`): three spaces with subspace inclusions `Z ⊆ Y ⊆ X`.
Choices: following Mathlib's `TopPair` (a pair is an embedding `A ⟶ X` in `TopCat`, not a literal
subset), a triple is three spaces `X Y Z : TopCat` with composable topological embeddings
`Z ⟶ Y ⟶ X` (each one a homeomorphism onto its image with the subspace topology). A literal
subset triple `Z ⊆ Y ⊆ X` is the special case of the subtype inclusions; every triple is
isomorphic to one of those. No closedness/openness or other condition on the subspaces. -/
namespace RoundTrip.L2.Morse_Homology_TopTriple

open CategoryTheory

universe w

/-- A triple of spaces `Z ⊆ Y ⊆ X`, as composable embeddings `Z ⟶ Y ⟶ X`. -/
structure Triple : Type (w + 1) where
  /-- The big space `X`. -/
  X : TopCat.{w}
  /-- The middle space `Y`. -/
  Y : TopCat.{w}
  /-- The small space `Z`. -/
  Z : TopCat.{w}
  /-- The inclusion `Y ⊆ X`. -/
  incYX : Y ⟶ X
  /-- The inclusion `Z ⊆ Y`. -/
  incZY : Z ⟶ Y
  isEmbedding_incYX : Topology.IsEmbedding incYX
  isEmbedding_incZY : Topology.IsEmbedding incZY

/-- The textbook notion: the type of triples of spaces `Z ⊆ Y ⊆ X`. -/
def T : Type (w + 1) := Triple.{w}

/-- The pair `(X, Y)` of a triple (Mathlib `TopPair`). -/
def Triple.pairXY (t : Triple.{w}) : TopPair.{w} := TopPair.of t.incYX t.isEmbedding_incYX

/-- The pair `(Y, Z)` of a triple (Mathlib `TopPair`). -/
def Triple.pairYZ (t : Triple.{w}) : TopPair.{w} := TopPair.of t.incZY t.isEmbedding_incZY

/-- The pair `(X, Z)` of a triple (Mathlib `TopPair`). -/
def Triple.pairXZ (t : Triple.{w}) : TopPair.{w} :=
  TopPair.of (t.incZY ≫ t.incYX) (t.isEmbedding_incYX.comp t.isEmbedding_incZY)

end RoundTrip.L2.Morse_Homology_TopTriple
