import Morse.Homology.Relative
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

/-!
# The exact sequence of a triple

For a triple of spaces `Z ⊆ Y ⊆ X`, the inclusions of pairs `(Y, Z) ⟶ (X, Z) ⟶ (X, Y)` induce a
short exact sequence of relative singular chain complexes
`0 ⟶ C(Y, Z) ⟶ C(X, Z) ⟶ C(X, Y) ⟶ 0`, and hence the **long exact sequence of the triple**
`⋯ ⟶ H_{n+1}(X, Y) ⟶∂ H_n(Y, Z) ⟶ H_n(X, Z) ⟶ H_n(X, Y) ⟶∂ H_{n-1}(Y, Z) ⟶ ⋯ ⟶ H_0(X, Y) ⟶ 0`.
This is the form of the exact sequence used by Milnor in §5 (the Morse inequalities), and it
contains the sequence of the pair `(X, Y)` (the case `Z = ∅`).

## The mathematics

The short exact sequence is the third isomorphism theorem `(C(X)/C(Z)) / (C(Y)/C(Z)) ≅ C(X)/C(Y)`.
In an abelian category it is the end of Mathlib's exact sequence
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0` of a composition
(`CategoryTheory.kernelCokernelCompSequence_exact`): when `g` is a monomorphism, `ker g = 0`, and
what remains is the short exact sequence `0 ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`
(`Morse.Homology.cokernel_comp_shortExact`).  It is applied to `f = C(Z) ⟶ C(Y)` and
`g = C(Y) ⟶ C(X)`.

## Design

A triple is a structure `Morse.Homology.TopTriple` with two embeddings `i : Z ⟶ Y` and
`j : Y ⟶ X` in `TopCat`, together with a morphism `k : Z ⟶ X` and a proof of `i ≫ j = k`: this
lets the pair `(X, Z)` be literally the pair one wants (for subsets `A ⊆ B ⊆ D` of a space,
`Morse.Homology.TopTriple.ofSubsets` has `(X, Z) = subsetPair (hAB.trans hBD)`).  The maps of the
sequence are the maps of relative chains (resp. homology) induced by the two inclusions of pairs
`TopTriple.map₁ : (Y, Z) ⟶ (X, Z)` and `TopTriple.map₂ : (X, Z) ⟶ (X, Y)`.

## Main results

* `Morse.Homology.cokernel_comp_shortExact`: `0 ⟶ coker f ⟶ coker h ⟶ coker g ⟶ 0` is short
  exact for `f ≫ g = h` with `g` a monomorphism, in any abelian category.
* `Morse.Homology.TopTriple.shortComplex_shortExact`: `0 ⟶ C(Y, Z) ⟶ C(X, Z) ⟶ C(X, Y) ⟶ 0`.
* `Morse.Homology.TopTriple.δ`: `∂ : H_{n+1}(X, Y) ⟶ H_n(Y, Z)`, with exactness at every place
  (`TopTriple.exact₁`, `TopTriple.exact₂`, `TopTriple.exact₃`, `TopTriple.epi_map₂_zero`), and
  `TopTriple.δ_eq`: it is the boundary of the pair `(X, Y)` followed by `H_n(Y) ⟶ H_n(Y, Z)`.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w v u

namespace Morse.Homology

/-! ### Cokernels of a composition -/

section Cokernels

variable {D : Type*} [Category* D] [Abelian D]

/-- For `f : A ⟶ B` and a monomorphism `g : B ⟶ C`,
`0 ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0` is short exact (the third isomorphism theorem). -/
lemma cokernel_comp_shortExact' {A B C : D} (f : A ⟶ B) (g : B ⟶ C) [Mono g] :
    (ShortComplex.mk (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
      (cokernel.map (f ≫ g) g f (𝟙 _) (by simp)) (by ext; simp)).ShortExact := by
  have hS := kernelCokernelCompSequence_exact f g
  refine ShortComplex.ShortExact.mk' (hS.exact 3) ?_ ?_
  · exact (hS.exact 2).mono_g ((isZero_kernel_of_mono g).eq_of_src _ _)
  · exact epi_of_epi_fac (f := cokernel.π (f ≫ g)) (h := cokernel.π g) (by simp)

/-- For `f : A ⟶ B`, a monomorphism `g : B ⟶ C` and `h = f ≫ g`,
`0 ⟶ coker f ⟶ coker h ⟶ coker g ⟶ 0` is short exact. -/
lemma cokernel_comp_shortExact {A B C : D} (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (fac : f ≫ g = h)
    [Mono g] :
    (ShortComplex.mk (cokernel.map f h (𝟙 _) g (by simp [fac]))
      (cokernel.map h g f (𝟙 _) (by simp [fac])) (by ext; simp)).ShortExact := by
  subst fac
  exact cokernel_comp_shortExact' f g

end Cokernels

/-! ### Triples of spaces -/

/-- A **triple of spaces** `Z ⊆ Y ⊆ X`: embeddings `i : Z ⟶ Y` and `j : Y ⟶ X` in `TopCat`,
together with a morphism `k : Z ⟶ X` equal to `i ≫ j` (the field `k` lets the pair `(X, Z)` be
chosen definitionally convenient). -/
structure TopTriple where
  /-- The big space `X`. -/
  X : TopCat.{w}
  /-- The middle space `Y`. -/
  Y : TopCat.{w}
  /-- The small space `Z`. -/
  Z : TopCat.{w}
  /-- The inclusion `Z ⟶ Y`. -/
  i : Z ⟶ Y
  /-- The inclusion `Y ⟶ X`. -/
  j : Y ⟶ X
  /-- The inclusion `Z ⟶ X`. -/
  k : Z ⟶ X
  /-- The inclusion `Z ⟶ X` is the composite of `Z ⟶ Y` and `Y ⟶ X`. -/
  fac : i ≫ j = k
  /-- `Z ⟶ Y` is an embedding. -/
  isEmbedding_i : Topology.IsEmbedding i
  /-- `Y ⟶ X` is an embedding. -/
  isEmbedding_j : Topology.IsEmbedding j

namespace TopTriple

variable (T : TopTriple.{w})

lemma isEmbedding_k : Topology.IsEmbedding T.k := by
  rw [← T.fac]
  exact T.isEmbedding_j.comp T.isEmbedding_i

/-- The pair `(Y, Z)`. -/
def pairYZ : TopPair.{w} := TopPair.of T.i T.isEmbedding_i

/-- The pair `(X, Z)`. -/
def pairXZ : TopPair.{w} := TopPair.of T.k T.isEmbedding_k

/-- The pair `(X, Y)`. -/
def pairXY : TopPair.{w} := TopPair.of T.j T.isEmbedding_j

/-- The inclusion of pairs `(Y, Z) ⟶ (X, Z)`. -/
def map₁ : T.pairYZ ⟶ T.pairXZ :=
  TopPair.ofHom (X := T.pairYZ) (Y := T.pairXZ) T.j (𝟙 T.Z) (by
    change 𝟙 T.Z ≫ T.k = T.i ≫ T.j
    rw [Category.id_comp, T.fac])

/-- The inclusion of pairs `(X, Z) ⟶ (X, Y)`. -/
def map₂ : T.pairXZ ⟶ T.pairXY :=
  TopPair.ofHom (X := T.pairXZ) (Y := T.pairXY) (𝟙 T.X) T.i (by
    change T.i ≫ T.j = T.k ≫ 𝟙 T.X
    rw [Category.comp_id, T.fac])

@[simp] lemma pairYZ_map : T.pairYZ.map = T.i := rfl
@[simp] lemma pairXZ_map : T.pairXZ.map = T.k := rfl
@[simp] lemma pairXY_map : T.pairXY.map = T.j := rfl
@[simp] lemma map₁_fst : TopPair.Hom.fst T.map₁ = T.j := rfl
@[simp] lemma map₁_snd : TopPair.Hom.snd T.map₁ = 𝟙 T.Z := rfl
@[simp] lemma map₂_fst : TopPair.Hom.fst T.map₂ = 𝟙 T.X := rfl
@[simp] lemma map₂_snd : TopPair.Hom.snd T.map₂ = T.i := rfl

/-- The triple `A ⊆ B ⊆ D` of subsets of a space `E`; its pairs are `subsetPair hAB`,
`subsetPair (hAB.trans hBD)` and `subsetPair hBD`. -/
@[simps]
def ofSubsets {E : Type w} [TopologicalSpace E] {A B D : Set E} (hAB : A ⊆ B) (hBD : B ⊆ D) :
    TopTriple.{w} where
  X := TopCat.of D
  Y := TopCat.of B
  Z := TopCat.of A
  i := subsetInclusion hAB
  j := subsetInclusion hBD
  k := subsetInclusion (hAB.trans hBD)
  fac := rfl
  isEmbedding_i := Topology.IsEmbedding.inclusion hAB
  isEmbedding_j := Topology.IsEmbedding.inclusion hBD

section Subsets

variable {E : Type w} [TopologicalSpace E] {A B D : Set E} (hAB : A ⊆ B) (hBD : B ⊆ D)

lemma ofSubsets_pairYZ : (ofSubsets hAB hBD).pairYZ = subsetPair hAB := rfl
lemma ofSubsets_pairXZ : (ofSubsets hAB hBD).pairXZ = subsetPair (hAB.trans hBD) := rfl
lemma ofSubsets_pairXY : (ofSubsets hAB hBD).pairXY = subsetPair hBD := rfl

end Subsets

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)

instance : Mono ((singularChains R).map T.j) :=
  have : Mono T.j := (TopCat.mono_iff_injective _).2 T.isEmbedding_j.injective
  inferInstance

lemma relChains_map_map₁_comp_map₂ :
    (relChains R).map T.map₁ ≫ (relChains R).map T.map₂ = 0 := by
  rw [← CategoryTheory.Functor.map_comp]
  apply relChains_hom_ext R (X := T.pairYZ)
  rw [relπ_relChains_map, comp_zero]
  exact map_relπ R T.pairXY

/-- The short complex of relative chains `C(Y, Z) ⟶ C(X, Z) ⟶ C(X, Y)` of a triple. -/
@[simps]
def shortComplex : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk ((relChains R).map T.map₁) ((relChains R).map T.map₂)
    (T.relChains_map_map₁_comp_map₂ R)

lemma singularChains_map_fac :
    (singularChains R).map T.i ≫ (singularChains R).map T.j = (singularChains R).map T.k := by
  rw [← CategoryTheory.Functor.map_comp, T.fac]

/-- The map `C(Y, Z) ⟶ C(X, Z)` is the map of cokernels induced by `C(Y) ⟶ C(X)`. -/
lemma relChains_map_map₁_eq : (relChains R).map T.map₁ =
    cokernel.map ((singularChains R).map T.i) ((singularChains R).map T.k) (𝟙 _)
      ((singularChains R).map T.j) (by simp [T.singularChains_map_fac R]) := by
  apply relChains_hom_ext R (X := T.pairYZ)
  rw [relπ_relChains_map]
  exact (cokernel.π_desc _ _ _).symm

/-- The map `C(X, Z) ⟶ C(X, Y)` is the map of cokernels induced by the identity of `C(X)`. -/
lemma relChains_map_map₂_eq : (relChains R).map T.map₂ =
    cokernel.map ((singularChains R).map T.k) ((singularChains R).map T.j)
      ((singularChains R).map T.i) (𝟙 _) (by simp [T.singularChains_map_fac R]) := by
  apply relChains_hom_ext R (X := T.pairXZ)
  rw [relπ_relChains_map]
  change (singularChains R).map (𝟙 T.X) ≫ cokernel.π ((singularChains R).map T.j) =
    cokernel.π ((singularChains R).map T.k) ≫ cokernel.map _ _ _ _ _
  rw [cokernel.π_desc, CategoryTheory.Functor.map_id]

/-- **The short exact sequence of a triple**: `0 ⟶ C(Y, Z) ⟶ C(X, Z) ⟶ C(X, Y) ⟶ 0`. -/
lemma shortComplex_shortExact : (T.shortComplex R).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ (cokernel_comp_shortExact _ _ _
    (T.singularChains_map_fac R))
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact (Category.id_comp _).trans ((T.relChains_map_map₁_eq R).trans (Category.comp_id _).symm)
  · exact (Category.id_comp _).trans ((T.relChains_map_map₂_eq R).trans (Category.comp_id _).symm)

/-- The connecting morphism `∂ : H_{n+1}(X, Y) ⟶ H_n(Y, Z)` of a triple. -/
def δ (n : ℕ) : (relHomology R (n + 1)).obj T.pairXY ⟶ (relHomology R n).obj T.pairYZ :=
  (T.shortComplex_shortExact R).δ (n + 1) n rfl

@[reassoc (attr := simp)]
lemma δ_comp (n : ℕ) : T.δ R n ≫ (relHomology R n).map T.map₁ = 0 :=
  (T.shortComplex_shortExact R).δ_comp (n + 1) n rfl

@[reassoc (attr := simp)]
lemma comp_δ (n : ℕ) : (relHomology R (n + 1)).map T.map₂ ≫ T.δ R n = 0 :=
  (T.shortComplex_shortExact R).comp_δ (n + 1) n rfl

@[reassoc (attr := simp)]
lemma map₁_comp_map₂ (n : ℕ) : (relHomology R n).map T.map₁ ≫ (relHomology R n).map T.map₂ = 0 := by
  rw [← CategoryTheory.Functor.map_comp, relHomology_map, CategoryTheory.Functor.map_comp,
    relChains_map_map₁_comp_map₂, homologyMap_zero]
  rfl

/-- **Exactness at `H_n(Y, Z)`**: `H_{n+1}(X, Y) ⟶∂ H_n(Y, Z) ⟶ H_n(X, Z)`. -/
lemma exact₁ (n : ℕ) : (ShortComplex.mk _ _ (T.δ_comp R n)).Exact :=
  (T.shortComplex_shortExact R).homology_exact₁ (n + 1) n rfl

/-- **Exactness at `H_n(X, Z)`**: `H_n(Y, Z) ⟶ H_n(X, Z) ⟶ H_n(X, Y)`. -/
lemma exact₂ (n : ℕ) : (ShortComplex.mk _ _ (T.map₁_comp_map₂ R n)).Exact :=
  (T.shortComplex_shortExact R).homology_exact₂ n

/-- **Exactness at `H_{n+1}(X, Y)`**: `H_{n+1}(X, Z) ⟶ H_{n+1}(X, Y) ⟶∂ H_n(Y, Z)`. -/
lemma exact₃ (n : ℕ) : (ShortComplex.mk _ _ (T.comp_δ R n)).Exact :=
  (T.shortComplex_shortExact R).homology_exact₃ (n + 1) n rfl

/-- **The end of the sequence**: `H_0(X, Z) ⟶ H_0(X, Y)` is an epimorphism. -/
instance epi_map₂_zero : Epi ((relHomology R 0).map T.map₂) := by
  have := (T.shortComplex_shortExact R).epi_g
  exact epi_homologyMap_of_epi_of_not_rel ((T.shortComplex R).g) 0 (fun _ h ↦ by simp at h)

/-- The morphism from the short exact sequence of the pair `(X, Y)` to that of the triple:
`(C(Y) ⟶ C(X) ⟶ C(X, Y)) ⟶ (C(Y, Z) ⟶ C(X, Z) ⟶ C(X, Y))`. -/
@[simps]
def fromPair : (relShortComplex R).obj T.pairXY ⟶ T.shortComplex R where
  τ₁ := relπ R T.pairYZ
  τ₂ := relπ R T.pairXZ
  τ₃ := 𝟙 _
  comm₁₂ := relπ_relChains_map R T.map₁
  comm₂₃ := by
    change relπ R T.pairXZ ≫ (relChains R).map T.map₂ = relπ R T.pairXY ≫ 𝟙 _
    rw [relπ_relChains_map, Category.comp_id]
    change (singularChains R).map (𝟙 T.X) ≫ cokernel.π ((singularChains R).map T.j) =
      cokernel.π ((singularChains R).map T.j)
    rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The boundary of a triple** is the boundary of the pair `(X, Y)` followed by the projection
`H_n(Y) ⟶ H_n(Y, Z)`. -/
lemma δ_eq (n : ℕ) : T.δ R n = relδ R T.pairXY n ≫ homologyMap (relπ R T.pairYZ) n := by
  have := HomologySequence.δ_naturality (T.fromPair R) (relShortComplex_shortExact R T.pairXY)
    (T.shortComplex_shortExact R) (n + 1) n rfl
  have h₃ : homologyMap (T.fromPair R).τ₃ (n + 1) = 𝟙 _ := by
    rw [fromPair_τ₃]
    exact homologyMap_id _ _
  refine Eq.trans ?_ this.symm
  change T.δ R n = homologyMap (T.fromPair R).τ₃ (n + 1) ≫ T.δ R n
  rw [h₃]
  exact (Category.id_comp _).symm

end TopTriple

end Morse.Homology
