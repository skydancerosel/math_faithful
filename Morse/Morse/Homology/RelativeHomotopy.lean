import Morse.Homology.Relative
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Contractible

/-!
# Homotopy invariance of relative singular homology

Mathlib proves that homotopic maps `f ≃ g : X ⟶ Y` induce chain-homotopic maps of singular chain
complexes (`TopCat.Homotopy.singularChainComplexFunctorObjMap`).  This file deduces:

* homotopy equivalences of spaces induce chain homotopy equivalences of singular chains, hence
  isomorphisms in homology (`Morse.Homology.singularChainsHomotopyEquiv`,
  `Morse.Homology.isIso_homologyMap_of_homotopyEquiv`);
* **homotopy invariance for pairs**: maps of pairs `f, g : (X, A) ⟶ (Y, B)` that are homotopic
  through maps of pairs (Mathlib's `TopPair.Homotopy`) induce the same maps
  `H_n(X, A) ⟶ H_n(Y, B)` (`Morse.Homology.relHomology_map_eq_of_homotopy`);
* a map of pairs whose two components are homotopy equivalences induces isomorphisms in relative
  homology (`Morse.Homology.isIso_relHomology_map_of_homotopyEquiv`);
* a contractible space has the homology of a point (`H_n = 0` for `n ≠ 0`,
  `Morse.Homology.isZero_homology_of_contractibleSpace`), so for a pair `(X, A)` with `X`
  contractible the boundary `H_{n+1}(X, A) ⟶ H_n(A)` is an isomorphism for `n ≠ 0`
  (`Morse.Homology.isIso_relδ_of_contractibleSpace`), as for `(Dⁿ, Sⁿ⁻¹)`.

## The proof of homotopy invariance for pairs

Mathlib's chain homotopy is built through several layers (singular simplicial sets, simplicial
homotopies, the alternating face map complex), and its naturality in the space is not available.
Instead of restricting it to the subspace, we use the cylinder of the pair,
`(X, A) × I = (X × I, A × I)` (`Morse.Homology.cylinder`), with its two ends
`ι₀, ι₁ : (X, A) ⟶ (X, A) × I` and its projection `π : (X, A) × I ⟶ (X, A)`:

1. `π : X × I ⟶ X` is a homotopy equivalence with inverse `ι₀` (the homotopy is the contraction
   `((x, s), t) ↦ (x, t s)` of the cylinder, `Morse.Homology.cylinderContraction`), and likewise
   for `A × I ⟶ A`; by the five lemma on the long exact sequences of the two pairs, `π` induces
   isomorphisms in relative homology (`Morse.Homology.isIso_relHomology_map_cylinderπ`).
2. Since `ι₀ ≫ π = 𝟙 = ι₁ ≫ π`, both `ι₀` and `ι₁` induce the inverse of `π_*`, so they induce the
   same map.
3. A homotopy of pairs `F` from `f` to `g` is a map of pairs `(X, A) × I ⟶ (Y, B)`
   (`Morse.Homology.cylinderHom`) with `ι₀ ≫ F = f` and `ι₁ ≫ F = g`.

This is the argument "use the five lemma on the long exact sequences of the pairs"; it needs only
the absolute homotopy invariance from Mathlib.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology HomologicalComplex MonoidalCategory
  CartesianMonoidalCategory TopCat

universe w v u

namespace Morse.Homology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)

/-! ### Homotopy equivalences -/

section HomotopyEquiv

/-- Maps `f : X ⟶ Y` and `g : Y ⟶ X` with homotopies `f ≫ g ≃ 𝟙` and `g ≫ f ≃ 𝟙` induce a
homotopy equivalence of singular chain complexes. -/
def singularChainsHomotopyEquivOfHomotopy {X Y : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ X)
    (H₁ : TopCat.Homotopy (f ≫ g) (𝟙 X)) (H₂ : TopCat.Homotopy (g ≫ f) (𝟙 Y)) :
    HomotopyEquiv ((singularChains R).obj X) ((singularChains R).obj Y) where
  hom := (singularChains R).map f
  inv := (singularChains R).map g
  homotopyHomInvId := (Homotopy.ofEq ((singularChains R).map_comp f g).symm).trans
    ((H₁.singularChainComplexFunctorObjMap R).trans (Homotopy.ofEq ((singularChains R).map_id X)))
  homotopyInvHomId := (Homotopy.ofEq ((singularChains R).map_comp g f).symm).trans
    ((H₂.singularChainComplexFunctorObjMap R).trans (Homotopy.ofEq ((singularChains R).map_id Y)))

/-- A homotopy equivalence of spaces induces a homotopy equivalence of singular chain
complexes. -/
def singularChainsHomotopyEquiv {X Y : TopCat.{w}} (e : ContinuousMap.HomotopyEquiv X Y) :
    HomotopyEquiv ((singularChains R).obj X) ((singularChains R).obj Y) :=
  singularChainsHomotopyEquivOfHomotopy R (TopCat.ofHom e.toFun) (TopCat.ofHom e.invFun)
    e.left_inv.some e.right_inv.some

@[simp]
lemma singularChainsHomotopyEquiv_hom {X Y : TopCat.{w}} (e : ContinuousMap.HomotopyEquiv X Y) :
    (singularChainsHomotopyEquiv R e).hom = (singularChains R).map (TopCat.ofHom e.toFun) := rfl

/-- A map which is a homotopy equivalence induces a quasi-isomorphism of singular chains. -/
lemma quasiIso_map_of_homotopyEquiv {X Y : TopCat.{w}} (f : X ⟶ Y)
    (e : ContinuousMap.HomotopyEquiv X Y) (he : ⇑e = ⇑f) : QuasiIso ((singularChains R).map f) := by
  have hf : f = TopCat.ofHom e.toFun := by ext x; exact (congrFun he x).symm
  subst hf
  exact (singularChainsHomotopyEquiv R e).quasiIso_hom

/-- **Homotopy invariance of singular homology**: a map which is a homotopy equivalence induces
isomorphisms `H_n(X) ≅ H_n(Y)`. -/
lemma isIso_homologyMap_of_homotopyEquiv {X Y : TopCat.{w}} (f : X ⟶ Y)
    (e : ContinuousMap.HomotopyEquiv X Y) (he : ⇑e = ⇑f) (n : ℕ) :
    IsIso (homologyMap ((singularChains R).map f) n) := by
  have := quasiIso_map_of_homotopyEquiv R f e he
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

/-- A map of pairs whose two components are homotopy equivalences induces isomorphisms
`H_n(X, A) ≅ H_n(Y, B)`. -/
lemma isIso_relHomology_map_of_homotopyEquiv {X Y : TopPair.{w}} (φ : X ⟶ Y)
    (e₁ : ContinuousMap.HomotopyEquiv X.snd Y.snd) (he₁ : ⇑e₁ = ⇑(TopPair.Hom.snd φ))
    (e₂ : ContinuousMap.HomotopyEquiv X.fst Y.fst) (he₂ : ⇑e₂ = ⇑(TopPair.Hom.fst φ)) (n : ℕ) :
    IsIso ((relHomology R n).map φ) :=
  isIso_relHomology_map R φ (isIso_homologyMap_of_homotopyEquiv R _ e₁ he₁)
    (isIso_homologyMap_of_homotopyEquiv R _ e₂ he₂) n

/-- **The homology of a contractible space** is that of a point: `H_n(X) = 0` for `n ≠ 0`. -/
lemma isZero_homology_of_contractibleSpace (X : TopCat.{w}) [ContractibleSpace X] {n : ℕ}
    (hn : n ≠ 0) : IsZero (((singularChains R).obj X).homology n) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv X (TopCat.of PUnit.{w + 1})
  have h := isIso_homologyMap_of_homotopyEquiv R (X := X) (Y := TopCat.of PUnit.{w + 1})
    (TopCat.ofHom e.toFun) e rfl n
  exact (isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R
    (TopCat.of PUnit.{w + 1}) hn).of_iso (@asIso _ _ _ _ _ h)

/-- For a pair `(X, A)` with `X` contractible, `∂ : H_{n+1}(X, A) ⟶ H_n(A)` is an isomorphism
for `n ≠ 0`. -/
lemma isIso_relδ_of_contractibleSpace (X : TopPair.{w}) [ContractibleSpace X.fst] {n : ℕ}
    (hn : n ≠ 0) : IsIso (relδ R X n) :=
  isIso_relδ R X n (isZero_homology_of_contractibleSpace R X.fst n.succ_ne_zero)
    (isZero_homology_of_contractibleSpace R X.fst hn)

end HomotopyEquiv

/-! ### The cylinder of a pair -/

section Cylinder

/-- The contraction `((z, s), t) ↦ (z, t s)` of the cylinder `Z × I`: a homotopy from
`π ≫ ι₀ : (z, s) ↦ (z, 0)` to the identity. -/
def cylinderContraction (Z : TopCat.{w}) : TopCat.Homotopy (fst Z I ≫ ι₀) (𝟙 (Z ⊗ I)) where
  toFun p := ((p.2.1 : Z), I.homeomorph.symm ⟨(p.1 : ℝ) * (I.homeomorph p.2.2 : ℝ),
    unitInterval.mul_mem p.1.2 (I.homeomorph p.2.2).2⟩)
  continuous_toFun := by
    refine Continuous.prodMk (continuous_fst.comp continuous_snd) ?_
    refine I.homeomorph.symm.continuous.comp (Continuous.subtype_mk ?_ _)
    exact (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp (I.homeomorph.continuous.comp
        (continuous_snd.comp continuous_snd)))
  map_zero_left x := by
    change ((x.1 : Z), I.homeomorph.symm _) = ((x.1 : Z), I.homeomorph.symm 0)
    congr 2
    exact Subtype.ext (zero_mul _)
  map_one_left x := by
    change ((x.1 : Z), I.homeomorph.symm _) = x
    have : (⟨(1 : ℝ) * (I.homeomorph x.2 : ℝ), unitInterval.mul_mem unitInterval.one_mem
        (I.homeomorph x.2).2⟩ : unitInterval) = I.homeomorph x.2 := Subtype.ext (one_mul _)
    simp only [Set.Icc.coe_one, this, Homeomorph.symm_apply_apply]
    rfl

/-- The projection `Z × I ⟶ Z` induces isomorphisms in singular homology. -/
lemma isIso_homologyMap_fst (Z : TopCat.{w}) (n : ℕ) :
    IsIso (homologyMap ((singularChains R).map (fst Z I)) n) := by
  have : QuasiIso ((singularChains R).map (fst Z I)) :=
    (singularChainsHomotopyEquivOfHomotopy R (fst Z I) ι₀ (cylinderContraction Z)
      (TopCat.Homotopy.refl (𝟙 Z))).quasiIso_hom
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

variable (X : TopPair.{w})

/-- The cylinder `(X × I, A × I)` of a pair `(X, A)`. -/
def cylinder : TopPair.{w} :=
  TopPair.of (X.map ▷ I) (by
    change Topology.IsEmbedding (Prod.map X.map (id : I → I))
    exact X.isEmbedding_map.prodMap Topology.IsEmbedding.id)

@[simp] lemma cylinder_fst : (cylinder X).fst = X.fst ⊗ I := rfl
@[simp] lemma cylinder_snd : (cylinder X).snd = X.snd ⊗ I := rfl
@[simp] lemma cylinder_map : (cylinder X).map = X.map ▷ I := rfl

/-- The end `ι₀ : (X, A) ⟶ (X, A) × I`, `x ↦ (x, 0)`. -/
def cylinderι₀ : X ⟶ cylinder X := TopPair.ofHom ι₀ ι₀ (ι₀_comp X.map)

/-- The end `ι₁ : (X, A) ⟶ (X, A) × I`, `x ↦ (x, 1)`. -/
def cylinderι₁ : X ⟶ cylinder X := TopPair.ofHom ι₁ ι₁ (ι₁_comp X.map)

/-- The projection `π : (X, A) × I ⟶ (X, A)`. -/
def cylinderπ : cylinder X ⟶ X :=
  TopPair.ofHom (X := cylinder X) (Y := X) (fst X.fst I) (fst X.snd I)
    (whiskerRight_fst X.map I).symm

@[simp] lemma cylinderπ_fst : TopPair.Hom.fst (cylinderπ X) = fst X.fst I := rfl
@[simp] lemma cylinderπ_snd : TopPair.Hom.snd (cylinderπ X) = fst X.snd I := rfl

@[reassoc (attr := simp)]
lemma cylinderι₀_π : cylinderι₀ X ≫ cylinderπ X = 𝟙 X :=
  MorphismProperty.Arrow.Hom.ext (ι₀_fst _) (ι₀_fst _)

@[reassoc (attr := simp)]
lemma cylinderι₁_π : cylinderι₁ X ≫ cylinderπ X = 𝟙 X :=
  MorphismProperty.Arrow.Hom.ext (ι₁_fst _) (ι₁_fst _)

/-- The projection of the cylinder of a pair induces isomorphisms in relative homology (the five
lemma, `π` being a homotopy equivalence on both spaces). -/
instance isIso_relHomology_map_cylinderπ (n : ℕ) : IsIso ((relHomology R n).map (cylinderπ X)) :=
  isIso_relHomology_map R _ (by rw [cylinderπ_snd]; exact isIso_homologyMap_fst R X.snd)
    (by rw [cylinderπ_fst]; exact isIso_homologyMap_fst R X.fst) n

/-- The two ends of the cylinder of a pair induce the same map in relative homology. -/
lemma relHomology_map_cylinderι₀_eq_ι₁ (n : ℕ) :
    (relHomology R n).map (cylinderι₀ X) = (relHomology R n).map (cylinderι₁ X) := by
  rw [IsIso.eq_inv_of_inv_hom_id (f := (relHomology R n).map (cylinderπ X))
      (g := (relHomology R n).map (cylinderι₀ X))
      (by rw [← Functor.map_comp, cylinderι₀_π, CategoryTheory.Functor.map_id]),
    IsIso.eq_inv_of_inv_hom_id (f := (relHomology R n).map (cylinderπ X))
      (g := (relHomology R n).map (cylinderι₁ X))
      (by rw [← Functor.map_comp, cylinderι₁_π, CategoryTheory.Functor.map_id])]

/-- A homotopy of maps of pairs, as a map out of the cylinder of the source pair. -/
def cylinderHom {Y : TopPair.{w}} {f g : X ⟶ Y} (F : TopPair.Homotopy f g) : cylinder X ⟶ Y :=
  TopPair.ofHom F.fst.h F.snd.h F.w.symm

@[reassoc (attr := simp)]
lemma cylinderι₀_cylinderHom {Y : TopPair.{w}} {f g : X ⟶ Y} (F : TopPair.Homotopy f g) :
    cylinderι₀ X ≫ cylinderHom X F = f :=
  MorphismProperty.Arrow.Hom.ext (TopCat.Homotopy.ι₀_h _) (TopCat.Homotopy.ι₀_h _)

@[reassoc (attr := simp)]
lemma cylinderι₁_cylinderHom {Y : TopPair.{w}} {f g : X ⟶ Y} (F : TopPair.Homotopy f g) :
    cylinderι₁ X ≫ cylinderHom X F = g :=
  MorphismProperty.Arrow.Hom.ext (TopCat.Homotopy.ι₁_h _) (TopCat.Homotopy.ι₁_h _)

end Cylinder

/-- **Homotopy invariance of relative singular homology**: maps of pairs which are homotopic
through maps of pairs induce the same maps `H_n(X, A) ⟶ H_n(Y, B)`. -/
theorem relHomology_map_eq_of_homotopy {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (F : TopPair.Homotopy f g) (n : ℕ) : (relHomology R n).map f = (relHomology R n).map g := by
  have h₀ := congrArg (relHomology R n).map (cylinderι₀_cylinderHom X F)
  have h₁ := congrArg (relHomology R n).map (cylinderι₁_cylinderHom X F)
  rw [Functor.map_comp] at h₀ h₁
  rw [← h₀, ← h₁, relHomology_map_cylinderι₀_eq_ι₁]

/-- Homotopy invariance of relative singular homology, for homotopic maps of pairs. -/
theorem relHomology_map_eq_of_homotopic {X Y : TopPair.{w}} {f g : X ⟶ Y}
    (h : TopPair.Homotopic f g) (n : ℕ) : (relHomology R n).map f = (relHomology R n).map g :=
  relHomology_map_eq_of_homotopy R h.some n

end Morse.Homology
