import Morse
/-! Layer-2 blind definition of Morse_Homology_TopTriple__ (the connecting homomorphism `δ` of a
triple). Textbook: Milnor, *Morse Theory*, §5, p. 30, and Hatcher, *Algebraic Topology*, ch. 2.1
(exact sequence of a triple `Z ⊆ Y ⊆ X`): `∂ : H_{n+1}(X, Y) → H_n(Y, Z)` is the composite
`H_{n+1}(X, Y) --∂--> H_n(Y) --j_*--> H_n(Y, Z)` of the boundary map of the pair `(X, Y)` (the
connecting map of the short exact sequence `0 → C(Y) → C(X) → C(X, Y) → 0`: lift a relative
cycle to `C(X)`, take its boundary, a cycle of `Y`) and the map induced by `(Y, ∅) → (Y, Z)`.
(Equivalently, the connecting map of `0 → C(Y,Z) → C(X,Z) → C(X,Y) → 0`; same map, no sign.)
Textbook ingredients defined here from scratch: singular chains = Mathlib's
`AlgebraicTopology.singularChainComplexFunctor` at `R`; `C(X, A) = cokernel (C(A) → C(X))` in
`ChainComplex C ℕ`; `H_n` = Mathlib's `HomologicalComplex.homology`; pair boundary = Mathlib's
`ShortComplex.ShortExact.δ` for the cokernel sequence of the mono `C(A) → C(X)`. The textbook map
on textbook objects is `deltaTB` below.
Encoding of `T` (the signature's source/target are the project's `relHomology` objects of the
project's pairs `T.pairXY = (X, Y)`, `T.pairYZ = (Y, Z)`, used as opaque setting): `T` is `deltaTB`
transported along *literal equalities* (`eqToHom`): it is used when `T.pairXY.snd = T.pairYZ.fst`
(the middle space `Y` of the two pairs is the same) and the project's
`(relHomology R (n+1)).obj T.pairXY`, `(relHomology R n).obj T.pairYZ` are equal to the textbook
objects `H_{n+1}(C(X)/C(Y))`, `H_n(C(Y)/C(Z))` built here. Otherwise (the project's relative
homology objects are not literally the textbook ones, so no canonical comparison exists), `T` is
the junk value `0`; then compare `deltaTB` with the project's `δ` through an identification of the
relative homologies instead. -/
namespace RoundTrip.L2.Morse_Homology_TopTriple__

open CategoryTheory Limits

universe w v u

section
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Singular chains `X ↦ C_*(X; R)`. -/
noncomputable abbrev chains (R : C) : TopCat.{w} ⥤ ChainComplex C ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor C).obj R

/-- Relative singular chains `C_*(X, A; R) = C_*(X; R) / C_*(A; R)` of a pair `P = (X, A)`. -/
noncomputable def relCh (R : C) (P : TopPair.{w}) : ChainComplex C ℕ :=
  cokernel ((chains R).map P.map)

/-- Relative singular homology `H_n(X, A; R)`. -/
noncomputable def relH (R : C) (n : ℕ) (P : TopPair.{w}) : C :=
  (relCh R P).homology n

/-- The short exact sequence `0 → C(A) → C(X) → C(X, A) → 0` of a pair. -/
noncomputable def pairSES (R : C) (P : TopPair.{w}) : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.cokernelSequence ((chains R).map P.map)

instance mono_chains_map (R : C) (P : TopPair.{w}) : Mono ((chains R).map P.map) := by
  have : Mono P.map := (TopCat.mono_iff_injective _).2 P.isEmbedding_map.injective
  infer_instance

lemma pairSES_shortExact (R : C) (P : TopPair.{w}) : (pairSES R P).ShortExact := by
  unfold pairSES
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
    (inferInstanceAs (Mono ((chains R).map P.map))) inferInstance

/-- The boundary map `∂ : H_{n+1}(X, A) → H_n(A)` of a pair. -/
noncomputable def pairDelta (R : C) (n : ℕ) (P : TopPair.{w}) :
    relH R (n + 1) P ⟶ ((chains R).obj P.snd).homology n :=
  (pairSES_shortExact R P).δ (n + 1) n (by simp)

/-- The map `j_* : H_n(Y) → H_n(Y, Z)` induced by the quotient `C(Y) → C(Y)/C(Z)`. -/
noncomputable def jMap (R : C) (n : ℕ) (Q : TopPair.{w}) :
    ((chains R).obj Q.fst).homology n ⟶ relH R n Q :=
  HomologicalComplex.homologyMap (cokernel.π ((chains R).map Q.map)) n

/-- The textbook connecting map of the triple given by the pairs `P = (X, Y)` and `Q = (Y, Z)`
(with `P.snd = Q.fst = Y`): `H_{n+1}(X, Y) → H_n(Y) → H_n(Y, Z)`. -/
noncomputable def deltaTB (R : C) (n : ℕ) (P Q : TopPair.{w}) (h : P.snd = Q.fst) :
    relH R (n + 1) P ⟶ relH R n Q :=
  pairDelta R n P ≫ eqToHom (by rw [h]) ≫ jMap R n Q

end

open Classical in
/-- The textbook notion: the connecting homomorphism `∂ : H_{n+1}(X, Y) → H_n(Y, Z)` of the
triple, i.e. `deltaTB` read on the project's relative homology objects when these are literally
the textbook ones (junk `0` otherwise; see the header). -/
noncomputable def T (Tri : Morse.Homology.TopTriple.{w}) {C : Type u} [Category.{v} C] [Abelian C]
    [HasCoproducts.{w} C] (R : C) (n : ℕ) :
    (Morse.Homology.relHomology R (n + 1)).obj Tri.pairXY ⟶
      (Morse.Homology.relHomology R n).obj Tri.pairYZ :=
  if h : Tri.pairXY.snd = Tri.pairYZ.fst ∧
      (Morse.Homology.relHomology R (n + 1)).obj Tri.pairXY = relH R (n + 1) Tri.pairXY ∧
      (Morse.Homology.relHomology R n).obj Tri.pairYZ = relH R n Tri.pairYZ then
    eqToHom h.2.1 ≫ deltaTB R n Tri.pairXY Tri.pairYZ h.1 ≫ eqToHom h.2.2.symm
  else 0

end RoundTrip.L2.Morse_Homology_TopTriple__
