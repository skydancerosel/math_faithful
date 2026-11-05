import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Morse.Homology.ModuleComplex

/-!
# Singular chains, concretely

Mathlib builds the singular chain complex `C(X; R)` of a topological space
(`AlgebraicTopology.singularChainComplexFunctor`) as the alternating face map complex of the
simplicial object `n ↦ ∐_{σ ∈ Sing(X)ₙ} R`, a categorical coproduct indexed by the singular
simplicial set `TopCat.toSSet.obj X`.  For the chain-level constructions of subdivision and
excision it is much more convenient to have the textbook description: an `n`-chain is a finite
formal `R`-linear combination `∑ rᵢ σᵢ` of continuous maps `σᵢ : Δⁿ → X`, that is, an element of
the `Finsupp` module `C(Δⁿ, X) →₀ R`, and the boundary is the alternating sum of the faces,
`∂σ = ∑ᵢ (-1)ⁱ σ ∘ δⁱ`.  This file sets up this description and identifies it with Mathlib's.

## Construction

* `Morse.Homology.freeFunctor R : Type v ⥤ ModuleCat R`, `S ↦ S →₀ R` (a universe-polymorphic
  `ModuleCat.free`), and for a simplicial set `K` the *free chain complex*
  `Morse.Homology.freeChains R K`, the alternating face map complex of `K ⋙ freeFunctor R`.
  Its `n`-chains are `K _⦋n⦌ →₀ R`, and its differential is `Morse.Homology.bd R K n`,
  `x ↦ ∑ᵢ (-1)ⁱ dᵢ x` on simplices (`Morse.Homology.bd_single`); `∂ ∘ ∂ = 0`
  (`Morse.Homology.bd_bd`) comes for free from Mathlib's `alternatingFaceMapComplex`.
* `Morse.Homology.Simplex n` is the standard topological `n`-simplex
  `{t : Fin (n + 1) → ℝ | tᵢ ≥ 0, ∑ tᵢ = 1}` (Mathlib's `stdSimplex ℝ (Fin (n + 1))`), and
  `Morse.Homology.simplexMap f : C(Δᵐ, Δⁿ)` is the affine map sending the vertex `eᵢ` to `e_{f i}`.
* `Morse.Homology.sing X` is the singular simplicial set of a space `X` with `n`-simplices
  literally `C(Δⁿ, X)`; its faces are `σ ↦ σ ∘ δⁱ` (`Morse.Homology.sing_δ`).
* `Morse.Homology.singChains R X` is the singular chain complex, with `n`-chains
  `Morse.Homology.Chains R X n = C(Δⁿ, X) →₀ R` and differential `Morse.Homology.sbd X n`
  (`Morse.Homology.sbd_single`, `Morse.Homology.sbd_sbd`).  It is defined directly by
  `ChainComplex.of`, so that its modules of chains are *reducibly* the `Finsupp` modules (which
  makes elementwise reasoning painless), and it is the free chain complex of `sing X`
  (`Morse.Homology.freeChainsIso`, the identity in each degree).
* A continuous map `f` acts by `Morse.Homology.push f`, `σ ↦ f ∘ σ`, a chain map
  `Morse.Homology.pushHom f` (`Morse.Homology.push_sbd`); `Morse.Homology.singChainsFunctor R` is
  the singular chain functor `TopCat ⥤ ChainComplex (ModuleCat R) ℕ`.

## Comparison with Mathlib

`Morse.Homology.singChainsIso R` is a natural isomorphism of functors
`TopCat ⥤ ChainComplex (ModuleCat R) ℕ` between Mathlib's
`(singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)` and
`Morse.Homology.singChainsFunctor R`, for a commutative ring `R`.  It is assembled from three
natural isomorphisms: the components `TopCat.toSSetObjEquiv` between Mathlib's singular simplicial
set and `sing X` (naturality is definitional), the identification of the categorical coproduct
`∐_S R` with `S →₀ R` (Mathlib's `ModuleCat.finsuppCoconeIsColimit`), and
`Morse.Homology.freeChainsIso`.  On a summand it
sends the generator of the summand indexed by a simplex `x` to the chain `x` itself
(`Morse.Homology.ι_singChainsIso_hom_app_f`), so statements about singular chains proved with the
concrete model transfer to Mathlib's singular homology.
-/

open CategoryTheory Simplicial Opposite AlgebraicTopology Limits

noncomputable section

namespace Morse.Homology

universe u v w

/-! ### Free chain complexes of simplicial sets -/

section FreeChains

variable (R : Type u) [Ring R]

/-- The free module functor `Type v ⥤ ModuleCat R`, `S ↦ S →₀ R`, a universe-polymorphic version
of `ModuleCat.free`. -/
@[simps]
def freeFunctor : Type v ⥤ ModuleCat.{max u v} R where
  obj S := ModuleCat.of R (S →₀ R)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain R R f)
  map_id S := by ext : 1; exact Finsupp.lmapDomain_id R R
  map_comp f g := by ext : 1; exact Finsupp.lmapDomain_comp R R f g

/-- The chain complex of a simplicial set `K` with coefficients in `R`: the `n`-chains are the
finite formal `R`-linear combinations `K _⦋n⦌ →₀ R` of `n`-simplices, and the differential is the
alternating sum of the faces (`Morse.Homology.bd`). -/
def freeChainsFunctor : SSet.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℕ :=
  (SimplicialObject.whiskering _ _).obj (freeFunctor R) ⋙ alternatingFaceMapComplex _

/-- The chain complex of a simplicial set `K` with coefficients in `R`, with `n`-chains
`K _⦋n⦌ →₀ R`. -/
abbrev freeChains (K : SSet.{v}) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  (freeChainsFunctor R).obj K

lemma freeChains_X (K : SSet.{v}) (n : ℕ) :
    (freeChains R K).X n = ModuleCat.of R (K _⦋n⦌ →₀ R) := rfl

/-- The boundary map `∂ : Cₙ₊₁(K) → Cₙ(K)`, `x ↦ ∑ᵢ (-1)ⁱ dᵢ x` on simplices. -/
def bd (K : SSet.{v}) (n : ℕ) : (K _⦋n + 1⦌ →₀ R) →ₗ[R] (K _⦋n⦌ →₀ R) :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.lmapDomain R R (K.δ i)

lemma freeChains_d (K : SSet.{v}) (n : ℕ) :
    (freeChains R K).d (n + 1) n = ModuleCat.ofHom (bd R K n) := by
  change ((alternatingFaceMapComplex _).obj (K ⋙ freeFunctor R)).d (n + 1) n = _
  rw [alternatingFaceMapComplex_obj_d]
  ext : 1
  simp only [AlternatingFaceMapComplex.objD, ModuleCat.hom_sum, ModuleCat.hom_zsmul, bd]
  rfl

lemma freeChains_d_apply (K : SSet.{v}) (n : ℕ) (c : K _⦋n + 1⦌ →₀ R) :
    (freeChains R K).d (n + 1) n c = bd R K n c := by
  rw [freeChains_d]; rfl

@[simp]
lemma bd_single (K : SSet.{v}) (n : ℕ) (x : K _⦋n + 1⦌) (r : R) :
    bd R K n (Finsupp.single x r) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (K.δ i x) r := by
  simp [bd]

/-- `∂ ∘ ∂ = 0`. -/
@[simp]
lemma bd_bd (K : SSet.{v}) (n : ℕ) (c : K _⦋n + 2⦌ →₀ R) : bd R K n (bd R K (n + 1) c) = 0 := by
  have := (freeChains R K).d_comp_d (n + 2) (n + 1) n
  rw [freeChains_d, freeChains_d] at this
  exact congr($this c)

lemma bd_comp_bd (K : SSet.{v}) (n : ℕ) : bd R K n ∘ₗ bd R K (n + 1) = 0 :=
  LinearMap.ext (bd_bd R K n)

lemma freeChainsFunctor_map_f {K L : SSet.{v}} (g : K ⟶ L) (n : ℕ) :
    ((freeChainsFunctor R).map g).f n = ModuleCat.ofHom (Finsupp.lmapDomain R R (g.app _)) :=
  rfl

@[simp]
lemma freeChainsFunctor_map_single {K L : SSet.{v}} (g : K ⟶ L) (n : ℕ) (x : K _⦋n⦌) (r : R) :
    ((freeChainsFunctor R).map g).f n (Finsupp.single x r) = Finsupp.single (g.app _ x) r :=
  Finsupp.mapDomain_single

/-- A morphism of simplicial sets commutes with the boundary maps. -/
lemma lmapDomain_bd {K L : SSet.{v}} (g : K ⟶ L) (n : ℕ) (c : K _⦋n + 1⦌ →₀ R) :
    Finsupp.lmapDomain R R (g.app _) (bd R K n c) =
      bd R L n (Finsupp.lmapDomain R R (g.app _) c) := by
  have := ((freeChainsFunctor R).map g).comm (n + 1) n
  rw [freeChains_d, freeChains_d] at this
  exact congr($this.symm c)

end FreeChains

/-! ### The standard simplex -/

/-- The standard topological `n`-simplex `Δⁿ = {t : Fin (n + 1) → ℝ | tᵢ ≥ 0, ∑ tᵢ = 1}`. -/
abbrev Simplex (n : ℕ) : Set (Fin (n + 1) → ℝ) := stdSimplex ℝ (Fin (n + 1))

/-- The affine map `Δᵐ → Δⁿ` sending the vertex `eᵢ` to `e_{f i}`, for `f : Fin (m+1) → Fin (n+1)`
(Mathlib's `stdSimplex.map`). -/
def simplexMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) : C(Simplex m, Simplex n) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩

@[simp]
lemma simplexMap_apply {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) (t : Simplex m) :
    simplexMap f t = stdSimplex.map f t := rfl

@[simp]
lemma simplexMap_id (n : ℕ) : simplexMap (id : Fin (n + 1) → Fin (n + 1)) = ContinuousMap.id _ := by
  ext t : 1
  exact stdSimplex.map_id_apply t

lemma simplexMap_comp {l m n : ℕ} (f : Fin (l + 1) → Fin (m + 1)) (g : Fin (m + 1) → Fin (n + 1)) :
    simplexMap (g ∘ f) = (simplexMap g).comp (simplexMap f) := by
  ext t : 1
  exact (stdSimplex.map_comp_apply f g t).symm

/-- The `i`-th face map `δⁱ : Δⁿ → Δⁿ⁺¹`, onto the face opposite to the vertex `eᵢ`. -/
abbrev faceMap {n : ℕ} (i : Fin (n + 2)) : C(Simplex n, Simplex (n + 1)) :=
  simplexMap (Fin.succAbove i)

/-! ### The singular simplicial set, concretely -/

section Sing

variable (X : Type v) [TopologicalSpace X]

/-- The singular simplicial set of a topological space `X`, with `n`-simplices the continuous maps
`Δⁿ → X` and simplicial operators given by precomposition with the affine maps `simplexMap`.
(This is `TopCat.toSSet.obj X` up to the definitional isomorphism `TopCat.toSSetObjEquiv`.) -/
def sing : SSet.{v} where
  obj n := C(Simplex n.unop.len, X)
  map f := ↾fun σ ↦ σ.comp (simplexMap f.unop.toOrderHom)
  map_id n := by
    ext σ : 3
    change σ.comp (simplexMap id) = σ
    rw [simplexMap_id]; rfl
  map_comp f g := by
    ext σ : 3
    change σ.comp (simplexMap (f.unop.toOrderHom ∘ g.unop.toOrderHom)) =
      (σ.comp (simplexMap f.unop.toOrderHom)).comp (simplexMap g.unop.toOrderHom)
    rw [simplexMap_comp]; rfl

variable {X}

lemma sing_map {m n : SimplexCategory} (f : m ⟶ n) (σ : (sing X).obj (op n)) :
    (sing X).map f.op σ = ContinuousMap.comp σ (simplexMap f.toOrderHom) := rfl

@[simp]
lemma sing_δ {n : ℕ} (i : Fin (n + 2)) (σ : C(Simplex (n + 1), X)) :
    (sing X).δ i σ = σ.comp (faceMap i) := rfl

/-- The singular simplicial set as a functor `TopCat ⥤ SSet`. -/
@[simps]
def singFunctor : TopCat.{v} ⥤ SSet.{v} where
  obj X := sing X
  map f := { app _ := ↾fun σ ↦ f.hom.comp σ }

end Sing

/-! ### Singular chains -/

section SingChains

variable (R : Type u) [Ring R]

/-- Singular `n`-chains of `X` with coefficients in `R`: finite formal `R`-linear combinations of
continuous maps `Δⁿ → X`. -/
abbrev Chains (X : Type v) [TopologicalSpace X] (n : ℕ) : Type (max u v) :=
  C(Simplex n, X) →₀ R

variable {R}

/-- The singular boundary `∂ : Cₙ₊₁(X) → Cₙ(X)`, `∂σ = ∑ᵢ (-1)ⁱ σ ∘ δⁱ`. -/
abbrev sbd (X : Type v) [TopologicalSpace X] (n : ℕ) : Chains R X (n + 1) →ₗ[R] Chains R X n :=
  bd R (sing X) n

lemma sbd_single {X : Type v} [TopologicalSpace X] {n : ℕ} (σ : C(Simplex (n + 1), X)) (r : R) :
    sbd X n (Finsupp.single σ r) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (σ.comp (faceMap i)) r :=
  bd_single R (sing X) n σ r

/-- `∂ ∘ ∂ = 0` on singular chains. -/
@[simp]
lemma sbd_sbd {X : Type v} [TopologicalSpace X] {n : ℕ} (c : Chains R X (n + 2)) :
    sbd X n (sbd X (n + 1) c) = 0 :=
  bd_bd R (sing X) n c

variable (R) in
/-- The singular chain complex of a space `X`, with `n`-chains `C(Δⁿ, X) →₀ R` and differential
`∂σ = ∑ᵢ (-1)ⁱ σ ∘ δⁱ` (`Morse.Homology.sbd`). -/
abbrev singChains (X : Type v) [TopologicalSpace X] : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (Chains R X n)) (fun n ↦ ModuleCat.ofHom (sbd X n))
    (fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun c ↦ sbd_sbd c))

@[simp]
lemma singChains_d (X : Type v) [TopologicalSpace X] (n : ℕ) :
    (singChains R X).d (n + 1) n = ModuleCat.ofHom (sbd X n) := by
  simp

section Push

variable {X : Type v} {Y : Type w} {Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- The map of singular chains induced by a continuous map `f`: `σ ↦ f ∘ σ`. -/
def push (f : C(X, Y)) (n : ℕ) : Chains R X n →ₗ[R] Chains R Y n :=
  Finsupp.lmapDomain R R (f.comp ·)

@[simp]
lemma push_single (f : C(X, Y)) {n : ℕ} (σ : C(Simplex n, X)) (r : R) :
    push f n (Finsupp.single σ r) = Finsupp.single (f.comp σ) r :=
  Finsupp.mapDomain_single

@[simp]
lemma push_id (n : ℕ) (c : Chains R X n) : push (ContinuousMap.id X) n c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ r => simp

lemma push_comp (g : C(Y, Z)) (f : C(X, Y)) (n : ℕ) (c : Chains R X n) :
    push (g.comp f) n c = push g n (push f n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ r => simp [ContinuousMap.comp_assoc]

/-- Pushing forward commutes with the boundary. -/
lemma push_sbd (f : C(X, Y)) (n : ℕ) (c : Chains R X (n + 1)) :
    push f n (sbd X n c) = sbd Y n (push f (n + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single σ r => simp [sbd_single, ContinuousMap.comp_assoc]

end Push

/-- The chain map `C(X) ⟶ C(Y)` induced by a continuous map. -/
def pushHom {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    singChains R X ⟶ singChains R Y :=
  natHomMk (fun n ↦ ModuleCat.ofHom (push f n)) (fun n ↦ by
    rw [singChains_d, singChains_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun c ↦ (push_sbd f n c).symm))

lemma pushHom_f {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    (pushHom (R := R) f).f n = ModuleCat.ofHom (push f n) := rfl

variable (R) in
/-- The singular chain complex functor `X ↦ C(X; R)`, with `n`-chains `C(Δⁿ, X) →₀ R`.  (It is
reducible, so that `(singChainsFunctor R).obj X` is reducibly `singChains R X`.) -/
abbrev singChainsFunctor : TopCat.{v} ⥤ ChainComplex (ModuleCat.{max u v} R) ℕ where
  obj X := singChains R X
  map f := pushHom f.hom
  map_id X := by
    ext n : 1
    exact ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R X n) ↦ push_id n c)
  map_comp f g := by
    ext n : 1
    exact ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R _ n) ↦ push_comp g.hom f.hom n c)

lemma singChainsFunctor_obj (X : TopCat.{v}) : (singChainsFunctor R).obj X = singChains R X := rfl

lemma singChainsFunctor_map {X Y : TopCat.{v}} (f : X ⟶ Y) :
    (singChainsFunctor R).map f = pushHom f.hom := rfl

variable (R) in
/-- The singular chain complex `singChains R X` is the free chain complex of the singular
simplicial set `sing X` (the identity in each degree; the differentials agree by
`Morse.Homology.freeChains_d`). -/
def freeChainsIso : singFunctor.{v} ⋙ freeChainsFunctor R ≅ singChainsFunctor R :=
  NatIso.ofComponents
    (fun X ↦ HomologicalComplex.Hom.isoOfComponents (fun n ↦ Iso.refl _) (by
      rintro i j (rfl : j + 1 = i)
      simp only [Iso.refl_hom, ChainComplex.of_d]
      exact ModuleCat.hom_ext (LinearMap.ext fun c ↦ (freeChains_d_apply R (sing X) j c).symm)))
    (fun _ ↦ rfl)

end SingChains

/-! ### Comparison with Mathlib's singular chain complex -/

section Comparison

variable (R : Type u) [CommRing R]

/-- The coproduct `∐_S R` of copies of `R` in `ModuleCat R` is the free module `S →₀ R`. -/
def sigmaIsoFinsupp (S : Type u) :
    (∐ fun _ : S ↦ ModuleCat.of R R) ≅ ModuleCat.of R (S →₀ R) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (ModuleCat.finsuppCoconeIsColimit R R S)

@[reassoc (attr := simp)]
lemma ι_sigmaIsoFinsupp_hom (S : Type u) (s : S) :
    Sigma.ι (fun _ : S ↦ ModuleCat.of R R) s ≫ (sigmaIsoFinsupp R S).hom =
      ModuleCat.ofHom (Finsupp.lsingle s) :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (ModuleCat.finsuppCoconeIsColimit R R S) ⟨s⟩

/-- The coproduct `∐_S R` of copies of `R` in `ModuleCat R` is the free module `S →₀ R`,
naturally in the type `S`. -/
def sigmaConstIsoFree :
    (sigmaConst.obj (ModuleCat.of R R) : Type u ⥤ ModuleCat.{u} R) ≅ freeFunctor.{u, u} R :=
  NatIso.ofComponents (sigmaIsoFinsupp R)
    (fun {S T} f ↦ by
      apply Sigma.hom_ext
      intro s
      simp only [sigmaConst_obj_map, Sigma.ι_comp_map'_assoc, Category.id_comp]
      erw [ι_sigmaIsoFinsupp_hom, ι_sigmaIsoFinsupp_hom_assoc]
      ext : 1
      apply LinearMap.ext_ring
      exact Finsupp.mapDomain_single.symm)

@[reassoc (attr := simp)]
lemma ι_sigmaConstIsoFree_hom_app (S : Type u) (s : S) :
    Sigma.ι (fun _ : S ↦ ModuleCat.of R R) s ≫ (sigmaConstIsoFree R).hom.app S =
      ModuleCat.ofHom (Finsupp.lsingle s) :=
  ι_sigmaIsoFinsupp_hom R S s

/-- Mathlib's chain complex functor of simplicial sets with coefficients in `R`
(`SSet.chainComplexFunctor`) is isomorphic to `freeChainsFunctor R`. -/
def chainComplexFunctorIso :
    (SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R) ≅
      freeChainsFunctor.{u, u} R :=
  Functor.isoWhiskerRight ((SimplicialObject.whiskering _ _).mapIso (sigmaConstIsoFree R))
    (alternatingFaceMapComplex _)

/-- Mathlib's singular simplicial set functor is isomorphic to `singFunctor`, through
`TopCat.toSSetObjEquiv` (naturality holds by definition). -/
def toSSetIsoSing : TopCat.toSSet.{u} ≅ singFunctor.{u} :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (fun n ↦ (X.toSSetObjEquiv n).toIso) (fun _ ↦ rfl))
    (fun _ ↦ rfl)

/-- **Comparison with Mathlib**: Mathlib's singular chain complex functor with coefficients in
`R` is naturally isomorphic to `singChainsFunctor R`, whose `n`-chains are `C(Δⁿ, X) →₀ R`. -/
def singChainsIso :
    (singularChainComplexFunctor (ModuleCat.{u} R)).obj (ModuleCat.of R R) ≅
      singChainsFunctor.{u, u} R :=
  Functor.isoWhiskerRight toSSetIsoSing _ ≪≫
    Functor.isoWhiskerLeft singFunctor (chainComplexFunctorIso R) ≪≫ freeChainsIso R

/-- The comparison isomorphism `singChainsIso` sends the generator of the summand indexed by a
singular simplex `x` to the chain `x`, seen as a continuous map `Δⁿ → X`. -/
lemma ι_singChainsIso_hom_app_f (X : TopCat.{u}) (n : ℕ) (x : TopCat.toSSet.obj X _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) x ≫
        ((singChainsIso R).hom.app X).f n =
      (ModuleCat.ofHom (Finsupp.lsingle (R := R) (M := R) (X.toSSetObjEquiv _ x)) :
        ModuleCat.of R R ⟶ (singChains R X).X n) := by
  erw [SSet.ι_chainComplexMap_f_assoc]
  exact ι_sigmaConstIsoFree_hom_app R _ _

end Comparison

end Morse.Homology
