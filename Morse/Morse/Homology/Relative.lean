import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Topology.Category.TopPair

/-!
# Relative singular homology and the exact sequence of a pair

Mathlib has the singular chain complex `C(X; R)` of a topological space with coefficients in an
object `R` of a preadditive category `C` with coproducts
(`AlgebraicTopology.singularChainComplexFunctor`), the category `TopPair` of pairs of spaces
(embeddings `A ↪ X` in `TopCat`), and the long exact homology sequence of a short exact sequence
of chain complexes in an abelian category (`CategoryTheory.ShortComplex.ShortExact.δ`), but not
relative singular homology.  This file defines it and proves its first properties, for an
abelian category `C` with coproducts (for instance `ModuleCat R` for a commutative ring `R`, with
coefficients `R` itself).

## The mathematics

For a pair `(X, A)`, the inclusion `A ↪ X` is injective, hence a monomorphism in `TopCat`, and the
singular chain functor sends it to a monomorphism `C(A) ⟶ C(X)` of chain complexes (Mathlib's
instance `PreservesMonomorphisms`: a singular simplex of `A` is determined by its image in `X`).
The *relative chain complex* is its cokernel, `C(X, A) = C(X) / C(A)`, so that
`0 ⟶ C(A) ⟶ C(X) ⟶ C(X, A) ⟶ 0` is a short exact sequence of chain complexes, natural in the
pair.  Relative homology is `H_n(X, A) = H_n(C(X, A))`, and the homology sequence of the short
exact sequence is the long exact sequence of the pair,
`⋯ ⟶ H_{n+1}(X, A) ⟶∂ H_n(A) ⟶ H_n(X) ⟶ H_n(X, A) ⟶∂ H_{n-1}(A) ⟶ ⋯ ⟶ H_0(X, A) ⟶ 0`.

## Design

* Everything is functorial on Mathlib's `TopPair`: a map of pairs is a morphism of `TopPair` (a
  commutative square), and functoriality is that of the functors `relChains R` and
  `relHomology R n`.  The coefficients are an object `R` of an abelian category `C` with
  coproducts, as for Mathlib's singular homology; the instance `C = ModuleCat 𝕜`, `R = 𝕜` is the
  one used for the Morse inequalities (`Morse/Homology/TripleFiltration.lean`).
* The general construction is `Morse.Homology.cokernelSequence`, the functor
  `Arrow D ⥤ ShortComplex D`, `f ↦ (f, coker f)`, for an abelian category `D`; it is short exact
  on monomorphisms.  The relative short complex is the composite
  `TopPair ⥤ Arrow TopCat ⥤ Arrow (ChainComplex C ℕ) ⥤ ShortComplex (ChainComplex C ℕ)`, and the
  relative chain complex is its third object, so that `(relChains R).obj X` is *definitionally*
  `cokernel ((singularChains R).map X.map)` (`Morse.Homology.relChains_obj`) and the projection
  `C(X) ⟶ C(X, A)` is `cokernel.π` (`Morse.Homology.relπ`).  A map out of `C(X, A)` is
  determined by its composite with `relπ` (`Morse.Homology.relChains_hom_ext`), and the map of
  relative chains induced by a map of pairs is characterized by `Morse.Homology.relπ_relChains_map`.
* The connecting morphism and the exactness statements are Mathlib's
  (`CategoryTheory.ShortComplex.ShortExact.δ`, `homology_exact₁/₂/₃`), specialized; with the
  homological grading `ComplexShape.down ℕ`, the connecting morphism
  `∂ : H_{n+1}(X, A) ⟶ H_n(A)` is `Morse.Homology.relδ`.
* Pairs of subsets `A ⊆ B` of a space `E` (Milnor's `(M^b, M^a)`) are `Morse.Homology.subsetPair`,
  with inclusions of pairs `Morse.Homology.subsetPairHom` and maps of pairs induced by continuous
  maps `Morse.Homology.subsetPairMap`.

## Main definitions and results

* `Morse.Homology.singularChains R`: Mathlib's singular chain functor `TopCat ⥤ ChainComplex C ℕ`
  with coefficients `R`; `C(A) ⟶ C(X)` is a monomorphism for every pair.
* `Morse.Homology.relShortComplex R`: the short exact sequence `0 ⟶ C(A) ⟶ C(X) ⟶ C(X, A) ⟶ 0`
  (`Morse.Homology.relShortComplex_shortExact`), a functor on `TopPair`.
* `Morse.Homology.relChains R` and `Morse.Homology.relHomology R n`: relative chains and relative
  homology, functors on `TopPair`; `Morse.Homology.relπ R X : C(X) ⟶ C(X, A)`, and
  `Morse.Homology.homologyToRelHomology`, the natural map `H_n(X) ⟶ H_n(X, A)`.
* `Morse.Homology.relδ R X n : H_{n+1}(X, A) ⟶ H_n(A)` and the exactness of the long exact
  sequence at every place: `relHomology_exact₁` (at `H_n(A)`), `relHomology_exact₂` (at `H_n(X)`),
  `relHomology_exact₃` (at `H_{n+1}(X, A)`), and `epi_homologyMap_relπ_zero`
  (`H_0(X) ⟶ H_0(X, A) ⟶ 0`).  Naturality of `∂` for maps of pairs: `relδ_naturality`, and
  `relδNatTrans`, `∂` as a natural transformation.
* `Morse.Homology.isIso_homologyMap_relπ_of_isEmpty`, `Morse.Homology.relHomologyInclIso`:
  `H_n(X) ≅ H_n(X, ∅)`, naturally.
* `Morse.Homology.isZero_relHomology_of_isIso`: `H_n(X, A) = 0` when `A ↪ X` is a homeomorphism,
  for instance `H_n(X, X) = 0` (`isZero_relHomology_diag`);
  `Morse.Homology.isZero_relHomology_of_isIso_homologyMap`: `H_n(X, A) = 0` when `A ↪ X` induces
  isomorphisms in homology.
* `Morse.Homology.quasiIso_relChains_map`, `Morse.Homology.isIso_relHomology_map`: the five lemma
  for maps of pairs.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex

universe w v u

namespace Morse.Homology

/-! ### The short exact sequence of a monomorphism and its cokernel -/

section CokernelSequence

variable (D : Type*) [Category* D] [Abelian D]

/-- The functor `Arrow D ⥤ ShortComplex D` sending `f : A ⟶ B` to `A ⟶ B ⟶ coker f`. -/
@[simps]
def cokernelSequence : Arrow D ⥤ ShortComplex D where
  obj f := ShortComplex.mk f.hom (cokernel.π f.hom) (cokernel.condition f.hom)
  map {f g} φ :=
    { τ₁ := φ.left
      τ₂ := φ.right
      τ₃ := (coker D).map φ
      comm₁₂ := φ.w
      comm₂₃ := by simp }

variable {D}

/-- `0 ⟶ A ⟶ B ⟶ coker f ⟶ 0` is short exact when `f : A ⟶ B` is a monomorphism. -/
lemma cokernelSequence_shortExact (f : Arrow D) [Mono f.hom] :
    ((cokernelSequence D).obj f).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel f.hom) (inferInstanceAs (Mono f.hom))
    (inferInstanceAs (Epi (cokernel.π f.hom)))

end CokernelSequence

/-! ### Singular chains of a pair -/

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)

/-- The singular chain complex functor `X ↦ C(X; R)` with coefficients in `R : C` (Mathlib's
`AlgebraicTopology.singularChainComplexFunctor`). -/
abbrev singularChains : TopCat.{w} ⥤ ChainComplex C ℕ :=
  (singularChainComplexFunctor C).obj R

/-- The inclusion of a pair is a monomorphism in `TopCat`. -/
instance (X : TopPair.{w}) : Mono X.map :=
  (TopCat.mono_iff_injective _).2 X.isEmbedding_map.injective

/-- The map `C(A) ⟶ C(X)` induced by the inclusion of a pair is a monomorphism (in each degree, a
singular simplex of `A` is determined by its image in `X`). -/
instance (X : TopPair.{w}) : Mono ((singularChains R).map X.map) := inferInstance

/-- The map `C_n(A) ⟶ C_n(X)` is a monomorphism in each degree `n`. -/
instance (X : TopPair.{w}) (n : ℕ) : Mono (((singularChains R).map X.map).f n) := inferInstance

/-- The short complex `C(A) ⟶ C(X) ⟶ C(X, A)` of a pair `(X, A)`, where `C(X, A)` is the cokernel
of `C(A) ⟶ C(X)`; it is short exact (`Morse.Homology.relShortComplex_shortExact`) and natural in
the pair. -/
def relShortComplex : TopPair.{w} ⥤ ShortComplex (ChainComplex C ℕ) :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ (singularChains R).mapArrow ⋙ cokernelSequence _

@[simp]
lemma relShortComplex_obj_X₁ (X : TopPair.{w}) :
    ((relShortComplex R).obj X).X₁ = (singularChains R).obj X.snd := rfl

@[simp]
lemma relShortComplex_obj_X₂ (X : TopPair.{w}) :
    ((relShortComplex R).obj X).X₂ = (singularChains R).obj X.fst := rfl

@[simp]
lemma relShortComplex_obj_f (X : TopPair.{w}) :
    ((relShortComplex R).obj X).f = (singularChains R).map X.map := rfl

@[simp]
lemma relShortComplex_map_τ₁ {X Y : TopPair.{w}} (φ : X ⟶ Y) :
    ((relShortComplex R).map φ).τ₁ = (singularChains R).map (TopPair.Hom.snd φ) := rfl

@[simp]
lemma relShortComplex_map_τ₂ {X Y : TopPair.{w}} (φ : X ⟶ Y) :
    ((relShortComplex R).map φ).τ₂ = (singularChains R).map (TopPair.Hom.fst φ) := rfl

/-- **The short exact sequence of a pair**: `0 ⟶ C(A) ⟶ C(X) ⟶ C(X, A) ⟶ 0`. -/
lemma relShortComplex_shortExact (X : TopPair.{w}) : ((relShortComplex R).obj X).ShortExact :=
  have : Mono (Arrow.mk ((singularChains R).map X.map)).hom := by dsimp; infer_instance
  cokernelSequence_shortExact (D := ChainComplex C ℕ) (Arrow.mk ((singularChains R).map X.map))

/-- The **relative singular chain complex** `C(X, A; R) = C(X; R) / C(A; R)`, as a functor on
pairs. -/
def relChains : TopPair.{w} ⥤ ChainComplex C ℕ := relShortComplex R ⋙ ShortComplex.π₃

lemma relChains_obj (X : TopPair.{w}) :
    (relChains R).obj X = cokernel ((singularChains R).map X.map) := rfl

/-- The projection `C(X) ⟶ C(X, A)`. -/
def relπ (X : TopPair.{w}) : (singularChains R).obj X.fst ⟶ (relChains R).obj X :=
  cokernel.π ((singularChains R).map X.map)

@[simp]
lemma relShortComplex_obj_X₃ (X : TopPair.{w}) :
    ((relShortComplex R).obj X).X₃ = (relChains R).obj X := rfl

@[simp]
lemma relShortComplex_obj_g (X : TopPair.{w}) : ((relShortComplex R).obj X).g = relπ R X := rfl

@[simp]
lemma relShortComplex_map_τ₃ {X Y : TopPair.{w}} (φ : X ⟶ Y) :
    ((relShortComplex R).map φ).τ₃ = (relChains R).map φ := rfl

instance (X : TopPair.{w}) : Epi (relπ R X) :=
  inferInstanceAs (Epi (cokernel.π ((singularChains R).map X.map)))

@[reassoc (attr := simp)]
lemma map_relπ (X : TopPair.{w}) : (singularChains R).map X.map ≫ relπ R X = 0 :=
  cokernel.condition _

/-- The map of relative chains induced by a map of pairs is induced by the map of the big
spaces. -/
@[reassoc (attr := simp)]
lemma relπ_relChains_map {X Y : TopPair.{w}} (φ : X ⟶ Y) :
    relπ R X ≫ (relChains R).map φ = (singularChains R).map (TopPair.Hom.fst φ) ≫ relπ R Y :=
  (((relShortComplex R).map φ).comm₂₃).symm

/-- Maps of relative chains out of `C(X, A)` are determined by their composition with the
projection `C(X) ⟶ C(X, A)`. -/
@[ext]
lemma relChains_hom_ext {X : TopPair.{w}} {K : ChainComplex C ℕ} {f g : (relChains R).obj X ⟶ K}
    (h : relπ R X ≫ f = relπ R X ≫ g) : f = g :=
  coequalizer.hom_ext h

/-- **Relative singular homology** `H_n(X, A; R)`, as a functor on pairs. -/
def relHomology (n : ℕ) : TopPair.{w} ⥤ C :=
  relChains R ⋙ homologyFunctor C _ n

lemma relHomology_obj (n : ℕ) (X : TopPair.{w}) :
    (relHomology R n).obj X = ((relChains R).obj X).homology n := rfl

lemma relHomology_map (n : ℕ) {X Y : TopPair.{w}} (φ : X ⟶ Y) :
    (relHomology R n).map φ = homologyMap ((relChains R).map φ) n := rfl

/-! ### The long exact sequence of a pair -/

section LongExactSequence

variable (X : TopPair.{w})

/-- The **connecting morphism** `∂ : H_{n+1}(X, A) ⟶ H_n(A)` of the pair `(X, A)` (Mathlib's
connecting morphism of the short exact sequence `0 ⟶ C(A) ⟶ C(X) ⟶ C(X, A) ⟶ 0`). -/
def relδ (n : ℕ) :
    ((relChains R).obj X).homology (n + 1) ⟶ ((singularChains R).obj X.snd).homology n :=
  (relShortComplex_shortExact R X).δ (n + 1) n rfl

@[reassoc (attr := simp)]
lemma relδ_comp (n : ℕ) : relδ R X n ≫ homologyMap ((singularChains R).map X.map) n = 0 :=
  (relShortComplex_shortExact R X).δ_comp (n + 1) n rfl

@[reassoc (attr := simp)]
lemma comp_relδ (n : ℕ) : homologyMap (relπ R X) (n + 1) ≫ relδ R X n = 0 :=
  (relShortComplex_shortExact R X).comp_δ (n + 1) n rfl

@[reassoc (attr := simp)]
lemma homologyMap_map_comp_relπ (n : ℕ) :
    homologyMap ((singularChains R).map X.map) n ≫ homologyMap (relπ R X) n = 0 := by
  rw [← homologyMap_comp, map_relπ, homologyMap_zero]

/-- **Exactness at `H_n(A)`**: `H_{n+1}(X, A) ⟶∂ H_n(A) ⟶ H_n(X)`. -/
lemma relHomology_exact₁ (n : ℕ) :
    (ShortComplex.mk _ _ (relδ_comp R X n)).Exact :=
  (relShortComplex_shortExact R X).homology_exact₁ (n + 1) n rfl

/-- **Exactness at `H_n(X)`**: `H_n(A) ⟶ H_n(X) ⟶ H_n(X, A)`. -/
lemma relHomology_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (homologyMap_map_comp_relπ R X n)).Exact :=
  (relShortComplex_shortExact R X).homology_exact₂ n

/-- **Exactness at `H_{n+1}(X, A)`**: `H_{n+1}(X) ⟶ H_{n+1}(X, A) ⟶∂ H_n(A)`. -/
lemma relHomology_exact₃ (n : ℕ) :
    (ShortComplex.mk _ _ (comp_relδ R X n)).Exact :=
  (relShortComplex_shortExact R X).homology_exact₃ (n + 1) n rfl

/-- **The long exact sequence of a pair** around degree `n`, as an exact sequence of six objects
`H_{n+1}(A) ⟶ H_{n+1}(X) ⟶ H_{n+1}(X, A) ⟶∂ H_n(A) ⟶ H_n(X) ⟶ H_n(X, A)`
(Mathlib's `ComposableArrows` form, convenient for the four and five lemmas). -/
lemma relHomologySequence_exact (n : ℕ) :
    (HomologySequence.composableArrows₅ (relShortComplex_shortExact R X) (n + 1) n rfl).Exact :=
  HomologySequence.composableArrows₅_exact _ (n + 1) n rfl

/-- **The end of the long exact sequence**: `H_0(X) ⟶ H_0(X, A)` is an epimorphism (the next term,
`H_{-1}(A)`, is zero). -/
instance epi_homologyMap_relπ_zero : Epi (homologyMap (relπ R X) 0) :=
  epi_homologyMap_of_epi_of_not_rel _ _ (fun _ h ↦ by simp at h)

/-- **Naturality of the connecting morphism** for maps of pairs `φ : (X, A) ⟶ (Y, B)`:
`∂ ∘ φ_* = (φ|_A)_* ∘ ∂`. -/
@[reassoc]
lemma relδ_naturality {X Y : TopPair.{w}} (φ : X ⟶ Y) (n : ℕ) :
    relδ R X n ≫ homologyMap ((singularChains R).map (TopPair.Hom.snd φ)) n =
      homologyMap ((relChains R).map φ) (n + 1) ≫ relδ R Y n :=
  HomologySequence.δ_naturality ((relShortComplex R).map φ)
    (relShortComplex_shortExact R X) (relShortComplex_shortExact R Y) (n + 1) n rfl

/-- The connecting morphism `H_i(X, A) ⟶ H_j(A)` for `j + 1 = i`, as a natural transformation
of functors on pairs (this is the form used by `TopPair.HomologyPretheory`). -/
@[simps]
def relδNatTrans (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    relHomology R i ⟶ TopPair.proj₂ ⋙ (singularHomologyFunctor C j).obj R where
  app X := (relShortComplex_shortExact R X).δ i j hij
  naturality _ _ φ := (HomologySequence.δ_naturality ((relShortComplex R).map φ)
    (relShortComplex_shortExact R _) (relShortComplex_shortExact R _) i j hij).symm

lemma relδNatTrans_app_succ (n : ℕ) (X : TopPair.{w}) :
    (relδNatTrans R (n + 1) n rfl).app X = relδ R X n := rfl

/-- If `H_n(A) ⟶ H_n(X)` is an epimorphism and `H_{n-1}(A) ⟶ H_{n-1}(X)` is a monomorphism, then
`H_n(X, A) = 0`. -/
lemma isZero_relHomology_of_epi_of_mono (n : ℕ)
    (h₁ : Epi (homologyMap ((singularChains R).map X.map) n))
    (h₂ : ∀ m, m + 1 = n → Mono (homologyMap ((singularChains R).map X.map) m)) :
    IsZero ((relHomology R n).obj X) :=
  (exactAt_iff_isZero_homology _ _).1 ((relShortComplex_shortExact R X).exactAt_X₃ n h₁ h₂)

/-- If `A ↪ X` induces isomorphisms `H_*(A) ≅ H_*(X)` (for instance if it is a homotopy
equivalence), then `H_n(X, A) = 0`. -/
lemma isZero_relHomology_of_isIso_homologyMap
    (h : ∀ n, IsIso (homologyMap ((singularChains R).map X.map) n)) (n : ℕ) :
    IsZero ((relHomology R n).obj X) :=
  isZero_relHomology_of_epi_of_mono R X n inferInstance (fun _ _ ↦ inferInstance)

/-- If `H_{n+1}(X)` and `H_n(X)` vanish, then `∂ : H_{n+1}(X, A) ⟶ H_n(A)` is an isomorphism. -/
lemma isIso_relδ (n : ℕ) (h₁ : IsZero (((singularChains R).obj X.fst).homology (n + 1)))
    (h₀ : IsZero (((singularChains R).obj X.fst).homology n)) : IsIso (relδ R X n) :=
  (relShortComplex_shortExact R X).isIso_δ (n + 1) n rfl h₁ h₀

end LongExactSequence

/-- The projection `H_n(X) ⟶ H_n(X, A)`, natural in the pair. -/
@[simps]
def homologyToRelHomology (n : ℕ) :
    TopPair.proj₁ ⋙ (singularHomologyFunctor C n).obj R ⟶ relHomology R n where
  app X := homologyMap (relπ R X) n
  naturality X Y φ := by
    change homologyMap ((singularChains R).map (TopPair.Hom.fst φ)) n ≫ homologyMap (relπ R Y) n =
      homologyMap (relπ R X) n ≫ homologyMap ((relChains R).map φ) n
    rw [← homologyMap_comp, ← homologyMap_comp, relπ_relChains_map]

/-! ### The pair `(X, ∅)` -/

section Empty

/-- In each degree, the singular chains of an empty space vanish. -/
lemma isZero_singularChains_X_of_isEmpty (X : TopCat.{w}) [IsEmpty X] (n : ℕ) :
    IsZero (((singularChains R).obj X).X n) := by
  rw [IsZero.iff_id_eq_zero]
  refine SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X) fun x ↦ ?_
  have : Nonempty (stdSimplex ℝ (Fin (n + 1))) := inferInstance
  exact isEmptyElim ((X.toSSetObjEquiv _ x) this.some)

/-- The singular chain complex of an empty space is zero. -/
lemma isZero_singularChains_of_isEmpty (X : TopCat.{w}) [IsEmpty X] :
    IsZero ((singularChains R).obj X) := by
  rw [IsZero.iff_id_eq_zero]
  ext n
  exact (isZero_singularChains_X_of_isEmpty R X n).eq_of_src _ _

instance (X : TopCat.{w}) : IsEmpty (TopPair.ofTopCat X).snd := inferInstanceAs (IsEmpty PEmpty)

instance (X : TopCat.{w}) : IsEmpty (TopPair.incl.obj X).snd := inferInstanceAs (IsEmpty PEmpty)

/-- If `A = ∅`, the projection `C(X) ⟶ C(X, A)` is an isomorphism. -/
instance isIso_relπ_of_isEmpty (X : TopPair.{w}) [IsEmpty X.snd] : IsIso (relπ R X) :=
  cokernel.π_of_zero ((isZero_singularChains_of_isEmpty R X.snd).eq_of_src _ _)

/-- **`H_n(X, ∅) = H_n(X)`**: if `A = ∅`, the projection `H_n(X) ⟶ H_n(X, A)` is an
isomorphism. -/
instance isIso_homologyMap_relπ_of_isEmpty (X : TopPair.{w}) [IsEmpty X.snd] (n : ℕ) :
    IsIso (homologyMap (relπ R X) n) := inferInstance

/-- **`H_n(X) ≅ H_n(X, ∅)`**, naturally in `X` (the isomorphism required by
`TopPair.HomologyPretheory`). -/
def relHomologyInclIso (n : ℕ) :
    (singularHomologyFunctor C n).obj R ≅ TopPair.incl ⋙ relHomology R n :=
  NatIso.ofComponents
    (fun X ↦ @asIso _ _ _ _ (homologyMap (relπ R (TopPair.incl.obj X)) n)
      (isIso_homologyMap_relπ_of_isEmpty R (TopPair.incl.obj X) n))
    (fun f ↦ (homologyToRelHomology R n).naturality (TopPair.incl.map f))

@[simp]
lemma relHomologyInclIso_hom_app (n : ℕ) (X : TopCat.{w}) :
    (relHomologyInclIso R n).hom.app X =
      homologyMap (relπ R (TopPair.incl.obj X)) n := rfl

end Empty

/-! ### The pair `(X, X)` -/

/-- If `A ↪ X` is an isomorphism (for instance the pair `(X, X)`), then `C(X, A) = 0`. -/
lemma isZero_relChains_of_isIso (X : TopPair.{w}) [IsIso X.map] : IsZero ((relChains R).obj X) :=
  isZero_cokernel_of_epi ((singularChains R).map X.map)

/-- **`H_n(X, X) = 0`**: if `A ↪ X` is an isomorphism, then `H_n(X, A) = 0`. -/
lemma isZero_relHomology_of_isIso (X : TopPair.{w}) [IsIso X.map] (n : ℕ) :
    IsZero ((relHomology R n).obj X) :=
  (homologyFunctor C _ n).map_isZero (isZero_relChains_of_isIso R X)

/-- **`H_n(X, X) = 0`**. -/
lemma isZero_relHomology_diag (X : TopCat.{w}) (n : ℕ) :
    IsZero ((relHomology R n).obj (TopPair.diag.obj X)) :=
  have : IsIso (TopPair.diag.obj X).map := inferInstanceAs (IsIso (𝟙 X))
  isZero_relHomology_of_isIso R _ n

/-! ### The five lemma for maps of pairs -/

/-- A map of pairs `φ : (X, A) ⟶ (Y, B)` such that `A ⟶ B` and `X ⟶ Y` induce quasi-isomorphisms
of singular chains induces a quasi-isomorphism of relative chains. -/
lemma quasiIso_relChains_map {X Y : TopPair.{w}} (φ : X ⟶ Y)
    [QuasiIso ((singularChains R).map (TopPair.Hom.snd φ))]
    [QuasiIso ((singularChains R).map (TopPair.Hom.fst φ))] :
    QuasiIso ((relChains R).map φ) :=
  HomologySequence.quasiIso_τ₃ ((relShortComplex R).map φ) (relShortComplex_shortExact R X)
    (relShortComplex_shortExact R Y) (by dsimp; infer_instance) (by dsimp; infer_instance)

/-- A map of pairs inducing a quasi-isomorphism of relative chains induces isomorphisms in
relative homology. -/
lemma isIso_relHomology_map_of_quasiIso {X Y : TopPair.{w}} (φ : X ⟶ Y)
    [QuasiIso ((relChains R).map φ)] (n : ℕ) : IsIso ((relHomology R n).map φ) :=
  (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

/-- **The five lemma for maps of pairs**: if `φ : (X, A) ⟶ (Y, B)` induces isomorphisms
`H_*(A) ≅ H_*(B)` and `H_*(X) ≅ H_*(Y)` in all degrees, then it induces isomorphisms
`H_n(X, A) ≅ H_n(Y, B)`. -/
lemma isIso_relHomology_map {X Y : TopPair.{w}} (φ : X ⟶ Y)
    (h₁ : ∀ n, IsIso (homologyMap ((singularChains R).map (TopPair.Hom.snd φ)) n))
    (h₂ : ∀ n, IsIso (homologyMap ((singularChains R).map (TopPair.Hom.fst φ)) n)) (n : ℕ) :
    IsIso ((relHomology R n).map φ) := by
  have : QuasiIso ((singularChains R).map (TopPair.Hom.snd φ)) := by
    rw [quasiIso_iff]
    exact fun n ↦ (quasiIsoAt_iff_isIso_homologyMap _ n).2 (h₁ n)
  have : QuasiIso ((singularChains R).map (TopPair.Hom.fst φ)) := by
    rw [quasiIso_iff]
    exact fun n ↦ (quasiIsoAt_iff_isIso_homologyMap _ n).2 (h₂ n)
  have := quasiIso_relChains_map R φ
  exact isIso_relHomology_map_of_quasiIso R φ n

/-- **The five lemma for maps of pairs, in one degree**: `φ : (X, A) ⟶ (Y, B)` induces an
isomorphism `H_n(X, A) ≅ H_n(Y, B)` if `H_n(A) ⟶ H_n(B)` is an epimorphism,
`H_n(X) ⟶ H_n(Y)` an isomorphism, `H_{n-1}(A) ⟶ H_{n-1}(B)` an isomorphism and
`H_{n-1}(X) ⟶ H_{n-1}(Y)` a monomorphism. -/
lemma isIso_relHomology_map_of_degree {X Y : TopPair.{w}} (φ : X ⟶ Y) (n : ℕ)
    (h₁ : Epi (homologyMap ((singularChains R).map (TopPair.Hom.snd φ)) n))
    (h₂ : IsIso (homologyMap ((singularChains R).map (TopPair.Hom.fst φ)) n))
    (h₃ : ∀ m, m + 1 = n → IsIso (homologyMap ((singularChains R).map (TopPair.Hom.snd φ)) m))
    (h₄ : ∀ m, m + 1 = n → Mono (homologyMap ((singularChains R).map (TopPair.Hom.fst φ)) m)) :
    IsIso ((relHomology R n).map φ) :=
  HomologySequence.isIso_homologyMap_τ₃ ((relShortComplex R).map φ)
    (relShortComplex_shortExact R X) (relShortComplex_shortExact R Y) n h₁ h₂ h₃ h₄

/-! ### Pairs of subsets -/

section Subsets

variable {E : Type w} [TopologicalSpace E]

/-- The inclusion `A ↪ B` of subsets `A ⊆ B` of a space `E`, as a morphism of `TopCat`. -/
def subsetInclusion {A B : Set E} (h : A ⊆ B) : TopCat.of A ⟶ TopCat.of B :=
  TopCat.ofHom ⟨Set.inclusion h, continuous_inclusion h⟩

@[simp]
lemma subsetInclusion_apply {A B : Set E} (h : A ⊆ B) (x : A) :
    subsetInclusion h x = Set.inclusion h x := rfl

@[reassoc (attr := simp)]
lemma subsetInclusion_comp {A B D : Set E} (h : A ⊆ B) (h' : B ⊆ D) :
    subsetInclusion h ≫ subsetInclusion h' = subsetInclusion (h.trans h') := rfl

@[simp]
lemma subsetInclusion_refl (A : Set E) : subsetInclusion (subset_refl A) = 𝟙 (TopCat.of A) := rfl

/-- The pair `(B, A)` of subsets `A ⊆ B` of a space `E` (Milnor's `(M^b, M^a)`). -/
def subsetPair {A B : Set E} (h : A ⊆ B) : TopPair.{w} :=
  TopPair.of (subsetInclusion h) (Topology.IsEmbedding.inclusion h)

@[simp] lemma subsetPair_fst {A B : Set E} (h : A ⊆ B) : (subsetPair h).fst = TopCat.of B := rfl
@[simp] lemma subsetPair_snd {A B : Set E} (h : A ⊆ B) : (subsetPair h).snd = TopCat.of A := rfl
@[simp] lemma subsetPair_map {A B : Set E} (h : A ⊆ B) :
    (subsetPair h).map = subsetInclusion h := rfl

/-- The inclusion of pairs `(B, A) ⟶ (B', A')` for `A ⊆ A'` and `B ⊆ B'`. -/
def subsetPairHom {A B A' B' : Set E} (h : A ⊆ B) (h' : A' ⊆ B') (hA : A ⊆ A') (hB : B ⊆ B') :
    subsetPair h ⟶ subsetPair h' :=
  TopPair.ofHom (subsetInclusion hB) (subsetInclusion hA) rfl

@[simp]
lemma subsetPairHom_fst {A B A' B' : Set E} (h : A ⊆ B) (h' : A' ⊆ B') (hA : A ⊆ A')
    (hB : B ⊆ B') : TopPair.Hom.fst (subsetPairHom h h' hA hB) = subsetInclusion hB := rfl

@[simp]
lemma subsetPairHom_snd {A B A' B' : Set E} (h : A ⊆ B) (h' : A' ⊆ B') (hA : A ⊆ A')
    (hB : B ⊆ B') : TopPair.Hom.snd (subsetPairHom h h' hA hB) = subsetInclusion hA := rfl

/-- The map `A ⟶ A'` of subspaces induced by a continuous map `f : E → E'` with `f(A) ⊆ A'`. -/
def subsetMap {E' : Type w} [TopologicalSpace E'] (f : C(E, E')) {A : Set E} {A' : Set E'}
    (hA : Set.MapsTo f A A') : TopCat.of A ⟶ TopCat.of A' :=
  TopCat.ofHom ⟨hA.restrict f A A', f.continuous.restrict hA⟩

@[simp]
lemma subsetMap_apply {E' : Type w} [TopologicalSpace E'] (f : C(E, E')) {A : Set E}
    {A' : Set E'} (hA : Set.MapsTo f A A') (x : A) : (subsetMap f hA x : E') = f x := rfl

/-- The map of pairs `(B, A) ⟶ (B', A')` induced by a continuous map `f : E → E'` with
`f(A) ⊆ A'` and `f(B) ⊆ B'`. -/
def subsetPairMap {E' : Type w} [TopologicalSpace E'] (f : C(E, E')) {A B : Set E}
    {A' B' : Set E'} (h : A ⊆ B) (h' : A' ⊆ B') (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    subsetPair h ⟶ subsetPair h' :=
  TopPair.ofHom (subsetMap f hB) (subsetMap f hA) rfl

@[simp]
lemma subsetPairMap_fst {E' : Type w} [TopologicalSpace E'] (f : C(E, E')) {A B : Set E}
    {A' B' : Set E'} (h : A ⊆ B) (h' : A' ⊆ B') (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    TopPair.Hom.fst (subsetPairMap f h h' hA hB) = subsetMap f hB := rfl

@[simp]
lemma subsetPairMap_snd {E' : Type w} [TopologicalSpace E'] (f : C(E, E')) {A B : Set E}
    {A' B' : Set E'} (h : A ⊆ B) (h' : A' ⊆ B') (hA : Set.MapsTo f A A') (hB : Set.MapsTo f B B') :
    TopPair.Hom.snd (subsetPairMap f h h' hA hB) = subsetMap f hA := rfl

/-- Equal subsets give isomorphic pairs. -/
def subsetPairIsoOfEq {A B A' B' : Set E} (h : A ⊆ B) (h' : A' ⊆ B') (hA : A = A')
    (hB : B = B') : subsetPair h ≅ subsetPair h' :=
  eqToIso (by subst hA hB; rfl)

instance (B : Set E) : IsEmpty (subsetPair (Set.empty_subset B)).snd :=
  inferInstanceAs (IsEmpty (∅ : Set E))

instance (A : Set E) : IsIso (subsetPair (subset_refl A)).map :=
  inferInstanceAs (IsIso (𝟙 (TopCat.of A)))

end Subsets

end Morse.Homology
