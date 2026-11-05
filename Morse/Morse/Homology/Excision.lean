import Morse.Homology.SmallChains
import Morse.Homology.Relative

/-!
# Excision for singular homology

**Theorem** (Hatcher, Thm. 2.20).  Let `A, B ⊆ X` be subspaces whose interiors cover `X`.  Then
the inclusion of pairs `(B, A ∩ B) ⟶ (X, A)` induces isomorphisms `H_n(B, A ∩ B) ≅ H_n(X, A)` for
all `n`.  Equivalently, for subspaces `Z ⊆ A ⊆ X` with `closure Z ⊆ interior A`, the inclusion
`(X ∖ Z, A ∖ Z) ⟶ (X, A)` induces isomorphisms `H_n(X ∖ Z, A ∖ Z) ≅ H_n(X, A)`.

The statements are about the relative singular homology `Morse.Homology.relHomology` of
`Morse/Homology/Relative.lean` (with coefficients `R` a commutative ring, i.e. the coefficient
object `ModuleCat.of R R`), for pairs of subsets of a space `E` (`Morse.Homology.subsetPair`),
with interiors and closures taken in the subspace `X ⊆ E`:

* `Morse.Homology.excision_of_union`: the `(B, A ∩ B) ⟶ (X, A)` form (and
  `Morse.Homology.excision_of_eq_inter`, for any `C = A ∩ B`);
* `Morse.Homology.excision`: the `(X ∖ Z, A ∖ Z) ⟶ (X, A)` form;
* `Morse.Homology.excision_of_closure_subset_interior`: the same, with closure and interior taken
  in the ambient space `E` (for instance for `X = E`, the pair `(E ∖ Z, A ∖ Z) ⟶ (E, A)`).

Here `(B, A)` for `A ⊆ B ⊆ E` is the pair `Morse.Homology.subsetPair` of
`Morse/Homology/Relative.lean`, and the maps of pairs are `Morse.Homology.subsetPairHom`.

## Proof

1. *Chain level* (`Morse.Homology.quasiIso_excisionMap`).  In the concrete singular chains of
   `Morse/Homology/Simplex.lean`, the map `C(B) / C(A ∩ B) ⟶ C(X) / C(A)` induced by the inclusion
   factors as
   `C(B) / C(A ∩ B) ≅ C^U(X) / C(A) ⟶ C(X) / C(A)`, where `U = {A, B}`.  The first map is an
   isomorphism (`Morse.Homology.isIso_excisionMapSmall`): in each degree, a chain of `U`-small
   simplices splits as a chain in `A` plus a chain in `B`, and a chain in `B` lies in `A` iff it
   lies in `A ∩ B`.  The second is a chain homotopy equivalence by the small chains theorem
   (`Morse.Homology.smallQuotHomotopyEquiv`).  This holds for any embedding `B ↪ X`
   (`Morse.Homology.quasiIso_excisionMap` is stated for an embedding with image `B`).
2. *Comparison* (`Morse.Homology.relChainsIsoQuot`).  For a pair `(X, A)` the relative chains of
   `Morse/Homology/Relative.lean`, the cokernel of Mathlib's `C(A) ⟶ C(X)`, are isomorphic to the
   concrete quotient `C(X) / C(A)` (the chains in `X` modulo those made of simplices in `A`),
   compatibly with maps of pairs (`Morse.Homology.relChainsIsoQuot_naturality`): through Mathlib's
   comparison `Morse.Homology.singChainsIso`, `0 ⟶ C(A) ⟶ C(X) ⟶ C(X) / C(A) ⟶ 0` is short exact,
   since a singular simplex of `X` with image in `A` lifts uniquely to `A`.
-/

open CategoryTheory Limits Set Topology

noncomputable section

namespace Morse.Homology

universe u v w

/-! ### Simplices and chains along an embedding -/

section Embedding

variable {R : Type u} [Ring R] {X : Type v} [TopologicalSpace X] {Y : Type w}
  [TopologicalSpace Y]

/-- A singular simplex of `X` whose image lies in the image of an embedding `j : Y → X` lifts
to `Y`. -/
lemma exists_comp_eq_of_range_subset {j : C(Y, X)} (hj : IsEmbedding j) {n : ℕ}
    (σ : C(Simplex n, X)) (hσ : range σ ⊆ range j) : ∃ τ : C(Simplex n, Y), j.comp τ = σ := by
  choose τ hτ using fun t ↦ hσ ⟨t, rfl⟩
  have hc : Continuous τ := hj.continuous_iff.2 (by
    convert σ.continuous using 1
    ext t
    exact hτ t)
  exact ⟨⟨τ, hc⟩, ContinuousMap.ext hτ⟩

lemma push_injective {j : C(Y, X)} (hj : Function.Injective j) (n : ℕ) :
    Function.Injective (push (R := R) j n) :=
  Finsupp.mapDomain_injective fun _ _ h ↦ ContinuousMap.ext fun t ↦
    hj (DFunLike.congr_fun h t)

/-- The image of `C(Y) ⟶ C(X)` for an embedding `j : Y → X` consists of the chains made of
simplices with image in `j(Y)`. -/
lemma range_push {j : C(Y, X)} (hj : IsEmbedding j) (n : ℕ) :
    LinearMap.range (push (R := R) j n) = Finsupp.supported R R (inSet (range j) n) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    refine Finsupp.supported_mono ?_ (mapDomain_mem_supported (f := (j.comp ·))
      ((Finsupp.mem_supported R c).2 (subset_univ _)))
    rintro _ ⟨τ, -, rfl⟩
    exact range_comp_subset_range τ j
  · rw [Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨τ, rfl⟩ := exists_comp_eq_of_range_subset hj σ hσ
    exact ⟨Finsupp.single τ 1, push_single j τ 1⟩

/-- A chain pushed forward along an injective map lies in a subset iff it lies in its preimage. -/
lemma push_mem_supported_iff {j : C(Y, X)} (hj : Function.Injective j) {n : ℕ} (S : Set X)
    (c : Chains R Y n) :
    push j n c ∈ Finsupp.supported R R (inSet S n) ↔
      c ∈ Finsupp.supported R R (inSet (j ⁻¹' S) n) := by
  classical
  have hinj : Function.Injective (j.comp · : C(Simplex n, Y) → C(Simplex n, X)) :=
    fun σ τ h ↦ ContinuousMap.ext fun t ↦ hj (DFunLike.congr_fun h t)
  rw [Finsupp.mem_supported, Finsupp.mem_supported, push, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_support_of_injective hinj, Finset.coe_image, image_subset_iff]
  refine forall₂_congr fun τ _ ↦ ?_
  simp only [mem_preimage, inSet, mem_ofPred_eq, ContinuousMap.coe_comp, range_comp,
    image_subset_iff]

end Embedding

/-! ### Excision at the chain level -/

section ChainLevel

variable (R : Type u) [Ring R] {X : Type v} [TopologicalSpace X] {Y : Type v}
  [TopologicalSpace Y]

/-- The cover `{A, B}` of `X`, indexed by `Bool`. -/
def coverOf (A B : Set X) : Bool → Set X := fun b ↦ cond b A B

lemma iUnion_interior_coverOf {A B : Set X} (h : interior A ∪ interior B = univ) :
    ⋃ b, interior (coverOf A B b) = univ := by
  rw [← h, union_eq_iUnion]
  congr 1
  ext b : 1
  cases b <;> rfl

lemma mem_smallSet_coverOf {A B : Set X} {n : ℕ} {σ : C(Simplex n, X)} :
    σ ∈ smallSet (coverOf A B) n ↔ σ ∈ inSet A n ∨ σ ∈ inSet B n := by
  constructor
  · rintro ⟨b, hb⟩
    cases b
    · exact Or.inr hb
    · exact Or.inl hb
  · rintro (h | h)
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩

variable (A : Set X) {j : C(Y, X)}

lemma push_mem_inSet_preimage {n : ℕ} (c : Chains R Y n)
    (hc : c ∈ Finsupp.supported R R (inSet (j ⁻¹' A) n)) :
    push j n c ∈ Finsupp.supported R R (inSet A n) := by
  refine Finsupp.supported_mono ?_ (mapDomain_mem_supported (f := (j.comp ·)) hc)
  rintro _ ⟨τ, hτ, rfl⟩
  rw [inSet, mem_ofPred_eq, ContinuousMap.coe_comp, range_comp]
  exact image_subset_iff.2 hτ

/-- **The excision map** `C(Y) / C(j⁻¹ A) ⟶ C(X) / C(A)` induced by a map `j : Y → X` (for an
embedding with image `B`, this is `C(B) / C(A ∩ B) ⟶ C(X) / C(A)`). -/
def excisionMap (j : C(Y, X)) :
    quotChains R (isPrecompClosed_inSet (j ⁻¹' A)) ⟶ quotChains R (isPrecompClosed_inSet A) :=
  quotientMap (pushHom j) (fun _ c hc ↦ push_mem_inSet_preimage R A c hc)

variable {B : Set X} (hj : IsEmbedding j) (hjB : range j = B)

include hj hjB in
lemma push_mem_smallSet (n : ℕ) (c : Chains R Y n) :
    push j n c ∈ Finsupp.supported R R (smallSet (coverOf A B) n) := by
  refine Finsupp.supported_mono (fun σ hσ ↦ mem_smallSet_coverOf.2 (Or.inr hσ)) ?_
  rw [← hjB, ← range_push hj]
  exact ⟨c, rfl⟩

/-- `C(Y) ⟶ C(X)` lands in the `{A, B}`-small chains when `j(Y) = B`. -/
def pushSmall : singChains R Y ⟶ smallChains R X (coverOf A B) :=
  natHomMk (fun n ↦ ModuleCat.ofHom ((push j n).codRestrict _ (push_mem_smallSet R A hj hjB n)))
    (fun n ↦ by
      rw [subcomplex_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R Y (n + 1)) ↦ Subtype.ext ?_)
      change (singChains R X).d (n + 1) n (push j (n + 1) c) =
        push j n ((singChains R Y).d (n + 1) n c)
      rw [singChains_d, singChains_d]
      exact (push_sbd j n c).symm)

lemma pushSmall_ι : pushSmall R A hj hjB ≫ smallChainsι R (coverOf A B) = pushHom j := rfl

/-- The map `C(Y) / C(j⁻¹ A) ⟶ C^{A,B}(X) / C(A)`. -/
def excisionMapSmall :
    quotChains R (isPrecompClosed_inSet (j ⁻¹' A)) ⟶
      smallQuotChains R (coverOf A B) (isPrecompClosed_inSet A) :=
  quotientMap (pushSmall R A hj hjB) (fun _ c hc ↦ push_mem_inSet_preimage R A c hc)

lemma excisionMapSmall_comp :
    excisionMapSmall R A hj hjB ≫ smallQuotMap R (coverOf A B) (isPrecompClosed_inSet A) =
      excisionMap R A j := by
  ext n : 1
  exact ModuleCat.hom_ext (Submodule.linearMap_qext _ rfl)

/-- `C(B) / C(A ∩ B) ⟶ C^{A,B}(X) / C(A)` is bijective in each degree. -/
lemma bijective_excisionMapSmall_f (n : ℕ) :
    Function.Bijective ((excisionMapSmall R A hj hjB).f n) := by
  classical
  constructor
  · -- injectivity: a chain in `B` whose image lies in `A` lies in `A ∩ B`
    rw [← LinearMap.ker_eq_bot (f := ((excisionMapSmall R A hj hjB).f n).hom),
      eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H c =>
      rw [LinearMap.mem_ker] at hx
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      have hx' : ((pushSmall R A hj hjB).f n c : supp R X (smallSet (coverOf A B)) n) ∈
          suppSmall R (coverOf A B) (inSet A) n :=
        (Submodule.Quotient.mk_eq_zero _).1 hx
      exact (push_mem_supported_iff hj.injective A c).1 hx'
  · -- surjectivity: a small chain is a chain in `A` plus a chain in `B`
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨x, hx⟩ := x
      let p : C(Simplex n, X) → Prop := fun σ ↦ σ ∈ inSet A n
      have hA : x.filter p ∈ Finsupp.supported R R (inSet A n) := by
        rw [Finsupp.mem_supported, Finsupp.support_filter, Finset.coe_filter]
        exact fun σ hσ ↦ hσ.2
      have hB : x.filter (fun σ ↦ ¬ p σ) ∈ Finsupp.supported R R (inSet B n) := by
        rw [Finsupp.mem_supported, Finsupp.support_filter, Finset.coe_filter]
        rintro σ ⟨hσx, hσA⟩
        rcases mem_smallSet_coverOf.1 (hx hσx) with h | h
        · exact absurd h hσA
        · exact h
      rw [← hjB, ← range_push (R := R) hj] at hB
      obtain ⟨c, hc⟩ := hB
      refine ⟨Submodule.Quotient.mk c, ?_⟩
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      rw [Submodule.Quotient.eq]
      change _ - _ ∈ (supp R X (inSet A) n).comap _
      rw [Submodule.mem_comap, map_sub]
      change push j n c - x ∈ _
      have hsplit := Finsupp.filter_add_filter_not x p
      have hdiff : Finsupp.filter (fun σ ↦ ¬p σ) x - x = -Finsupp.filter p x := by
        rw [eq_neg_iff_add_eq_zero]
        calc _ = (Finsupp.filter p x + Finsupp.filter (fun σ ↦ ¬p σ) x) - x := by abel
          _ = 0 := by rw [hsplit, sub_self]
      rw [hc, hdiff]
      exact neg_mem hA

instance isIso_excisionMapSmall : IsIso (excisionMapSmall R A hj hjB) := by
  have (n : ℕ) : IsIso ((excisionMapSmall R A hj hjB).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_excisionMapSmall_f R A hj hjB n)
  exact HomologicalComplex.Hom.isIso_of_components _

include hj hjB in
/-- **Excision at the chain level**: if the interiors of `A` and `B` cover `X` and `j : Y → X` is
an embedding with image `B`, then `C(Y) / C(j⁻¹ A) ⟶ C(X) / C(A)` is a quasi-isomorphism. -/
theorem quasiIso_excisionMap (h : interior A ∪ interior B = univ) :
    QuasiIso (excisionMap R A j) := by
  have := quasiIso_smallQuotMap R (iUnion_interior_coverOf h) (isPrecompClosed_inSet A)
  rw [← excisionMapSmall_comp R A hj hjB]
  infer_instance

end ChainLevel

/-! ### Relative chains as concrete quotients -/

section Bridge

variable (R : Type u) [CommRing R]

/-- The projection `C(X) ⟶ C(X) / C_S(X)` onto the concrete quotient by the chains made of
simplices in `S ⊆ X`. -/
abbrev quotπ {X : Type u} [TopologicalSpace X] (S : Set X) :
    singChains R X ⟶ quotChains R (isPrecompClosed_inSet S) :=
  quotientπ (singChains R X) (supp R X (inSet S)) (d_mem_supp R (isPrecompClosed_inSet S))

lemma pushHom_comp_quotπ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {j : C(Y, X)}
    (hj : IsEmbedding j) {S : Set X} (hS : range j = S) : pushHom j ≫ quotπ R S = 0 :=
  quotientπ_comp_eq_zero _ _ _ _ fun n c ↦ by
    subst hS
    exact (range_push (R := R) hj n).le ⟨c, rfl⟩

/-- The concrete short exact sequence `0 ⟶ C(A) ⟶ C(X) ⟶ C(X) / C(A) ⟶ 0` of a pair, with
`S ⊆ X` the image of `A`. -/
abbrev concreteRelShortComplex (P : TopPair.{u}) (S : Set P.fst) (hS : range P.map = S) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (pushHom (R := R) P.map.hom) (quotπ R S)
    (pushHom_comp_quotπ R P.isEmbedding_map hS)

lemma concreteRelShortComplex_shortExact (P : TopPair.{u}) (S : Set P.fst)
    (hS : range P.map = S) : (concreteRelShortComplex R P S hS).ShortExact :=
  shortExact_quotient _ _ _ _ (fun n ↦ push_injective P.isEmbedding_map.injective n)
    (fun n ↦ by subst hS; exact range_push P.isEmbedding_map n) _

lemma mathlibRelShortComplex_zero (P : TopPair.{u}) (S : Set P.fst) (hS : range P.map = S) :
    (singularChains (ModuleCat.of R R)).map P.map ≫ (singChainsIso R).hom.app P.fst ≫
      quotπ R S = 0 :=
  calc (singularChains (ModuleCat.of R R)).map P.map ≫ (singChainsIso R).hom.app P.fst ≫
        quotπ R S
      = ((singularChains (ModuleCat.of R R)).map P.map ≫ (singChainsIso R).hom.app P.fst) ≫
          quotπ R S := (Category.assoc _ _ _).symm
    _ = ((singChainsIso R).hom.app P.snd ≫ pushHom (R := R) P.map.hom) ≫ quotπ R S := by
          rw [(singChainsIso R).hom.naturality P.map]
    _ = (singChainsIso R).hom.app P.snd ≫ (pushHom (R := R) P.map.hom ≫ quotπ R S) :=
          Category.assoc _ _ _
    _ = 0 := by rw [pushHom_comp_quotπ R P.isEmbedding_map hS, comp_zero]

/-- The short exact sequence of a pair, with Mathlib's singular chains and the concrete
quotient. -/
abbrev mathlibRelShortComplex (P : TopPair.{u}) (S : Set P.fst) (hS : range P.map = S) :
    ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk ((singularChains (ModuleCat.of R R)).map P.map)
    ((singChainsIso R).hom.app P.fst ≫ quotπ R S) (mathlibRelShortComplex_zero R P S hS)

/-- The two short complexes of a pair are isomorphic, through `Morse.Homology.singChainsIso`. -/
def mathlibRelShortComplexIso (P : TopPair.{u}) (S : Set P.fst) (hS : range P.map = S) :
    mathlibRelShortComplex R P S hS ≅ concreteRelShortComplex R P S hS :=
  ShortComplex.isoMk ((singChainsIso R).app P.snd) ((singChainsIso R).app P.fst) (Iso.refl _)
    ((singChainsIso R).hom.naturality P.map).symm (Category.comp_id _).symm

lemma mathlibRelShortComplex_shortExact (P : TopPair.{u}) (S : Set P.fst)
    (hS : range P.map = S) : (mathlibRelShortComplex R P S hS).ShortExact :=
  ShortComplex.shortExact_of_iso (mathlibRelShortComplexIso R P S hS).symm
    (concreteRelShortComplex_shortExact R P S hS)

/-- The concrete quotient `C(X) / C(A)` is a cokernel of Mathlib's `C(A) ⟶ C(X)`. -/
def isColimitMathlibRelShortComplex (P : TopPair.{u}) (S : Set P.fst) (hS : range P.map = S) :
    IsColimit (CokernelCofork.ofπ _ (mathlibRelShortComplex_zero R P S hS)) :=
  have := (mathlibRelShortComplex_shortExact R P S hS).epi_g
  (mathlibRelShortComplex_shortExact R P S hS).exact.gIsCokernel

/-- **Relative chains are concrete quotients**: for a pair `(X, A)` with `A` embedded in `X` as
`S ⊆ X`, the relative chains `C(X, A)` (the cokernel of `C(A) ⟶ C(X)`, `Morse.Homology.relChains`)
are isomorphic to the quotient of the concrete singular chains of `X` by the chains made of
simplices in `S`. -/
def relChainsIsoQuot (P : TopPair.{u}) (S : Set P.fst) (hS : range P.map = S) :
    (relChains (ModuleCat.of R R)).obj P ≅ quotChains R (isPrecompClosed_inSet S) :=
  (cokernelIsCokernel ((singularChains (ModuleCat.of R R)).map P.map)).coconePointUniqueUpToIso
    (isColimitMathlibRelShortComplex R P S hS)

lemma relπ_relChainsIsoQuot_hom (P : TopPair.{u}) (S : Set P.fst) (hS : range P.map = S) :
    relπ (ModuleCat.of R R) P ≫ (relChainsIsoQuot R P S hS).hom =
      (singChainsIso R).hom.app P.fst ≫ quotπ R S :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom
    (isColimitMathlibRelShortComplex R P S hS) WalkingParallelPair.one

/-- The identification of relative chains with concrete quotients is compatible with maps of
pairs. -/
lemma relChainsIsoQuot_naturality {P P' : TopPair.{u}} (φ : P ⟶ P') (S : Set P.fst)
    (hS : range P.map = S) (S' : Set P'.fst) (hS' : range P'.map = S')
    (hφ : ∀ n, ∀ c ∈ supp R P.fst (inSet S) n,
      (pushHom (R := R) (TopPair.Hom.fst φ).hom).f n c ∈ supp R P'.fst (inSet S') n) :
    (relChains (ModuleCat.of R R)).map φ ≫ (relChainsIsoQuot R P' S' hS').hom =
      (relChainsIsoQuot R P S hS).hom ≫ quotientMap (pushHom (TopPair.Hom.fst φ).hom) hφ := by
  apply relChains_hom_ext
  calc relπ (ModuleCat.of R R) P ≫ (relChains (ModuleCat.of R R)).map φ ≫
        (relChainsIsoQuot R P' S' hS').hom
      = (singularChains (ModuleCat.of R R)).map (TopPair.Hom.fst φ) ≫
          relπ (ModuleCat.of R R) P' ≫ (relChainsIsoQuot R P' S' hS').hom := by
        rw [relπ_relChains_map_assoc]
    _ = ((singularChains (ModuleCat.of R R)).map (TopPair.Hom.fst φ) ≫
          (singChainsIso R).hom.app P'.fst) ≫ quotπ R S' := by
        rw [relπ_relChainsIsoQuot_hom, Category.assoc]
    _ = ((singChainsIso R).hom.app P.fst ≫ pushHom (R := R) (TopPair.Hom.fst φ).hom) ≫
          quotπ R S' := by
        rw [(singChainsIso R).hom.naturality (TopPair.Hom.fst φ)]
    _ = (singChainsIso R).hom.app P.fst ≫ quotπ R S ≫
          quotientMap (pushHom (TopPair.Hom.fst φ).hom) hφ := by
        rw [Category.assoc]
        rfl
    _ = relπ (ModuleCat.of R R) P ≫ (relChainsIsoQuot R P S hS).hom ≫
          quotientMap (pushHom (TopPair.Hom.fst φ).hom) hφ := by
        rw [← Category.assoc (relπ _ P), relπ_relChainsIsoQuot_hom, Category.assoc]

end Bridge

/-! ### Excision -/

section Excision

variable (R : Type u) [CommRing R] {E : Type u} [TopologicalSpace E]

/-- **Excision**, general form: let `A, B ⊆ X` be subsets of a space `E` whose interiors in `X`
cover `X`, and let `C = A ∩ B`.  Then the inclusion of pairs `(B, C) ⟶ (X, A)` induces
isomorphisms in relative singular homology in all degrees. -/
theorem excision_of_eq_inter {X A B C : Set E} (hAX : A ⊆ X) (hBX : B ⊆ X) (hCB : C ⊆ B)
    (hCA : C ⊆ A) (hC : A ∩ B = C)
    (h : interior ((↑) ⁻¹' A : Set X) ∪ interior ((↑) ⁻¹' B : Set X) = univ) (n : ℕ) :
    IsIso ((relHomology (ModuleCat.of R R) n).map (subsetPairHom hCB hAX hCA hBX)) := by
  let j : C(B, X) := (subsetInclusion hBX).hom
  have hj : IsEmbedding j := IsEmbedding.inclusion hBX
  have hjB : range j = (↑) ⁻¹' B := by
    change range (Set.inclusion hBX) = _
    rw [range_inclusion]
    rfl
  have hS₂ : range (subsetPair hAX).map = ((↑) ⁻¹' A : Set X) := by
    change range (Set.inclusion hAX) = _
    rw [range_inclusion]
    rfl
  have hS₁ : range (subsetPair hCB).map = j ⁻¹' ((↑) ⁻¹' A : Set X) := by
    change range (Set.inclusion hCB) = _
    rw [range_inclusion]
    ext b
    change (b : E) ∈ C ↔ (b : E) ∈ A
    rw [← hC]
    exact ⟨fun hb ↦ hb.1, fun hb ↦ ⟨hb, b.2⟩⟩
  have hq := quasiIso_excisionMap R ((↑) ⁻¹' A : Set X) hj hjB h
  have hw := relChainsIsoQuot_naturality R (subsetPairHom hCB hAX hCA hBX) _ hS₁ _ hS₂
    (fun _ c hc ↦ push_mem_inSet_preimage R _ c hc)
  have e : Arrow.mk ((relChains (ModuleCat.of R R)).map (subsetPairHom hCB hAX hCA hBX)) ≅
      Arrow.mk (excisionMap R ((↑) ⁻¹' A : Set X) j) :=
    Arrow.isoMk (relChainsIsoQuot R (subsetPair hCB) _ hS₁)
      (relChainsIsoQuot R (subsetPair hAX) _ hS₂) hw.symm
  have : QuasiIso ((relChains (ModuleCat.of R R)).map (subsetPairHom hCB hAX hCA hBX)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ e).2 hq
  exact isIso_relHomology_map_of_quasiIso _ _ n

/-- **Excision** (Hatcher, Thm. 2.20): if `A, B ⊆ X` are subsets of a space `E` whose interiors
in `X` cover `X`, the inclusion of pairs `(B, A ∩ B) ⟶ (X, A)` induces isomorphisms
`H_n(B, A ∩ B) ≅ H_n(X, A)` in all degrees. -/
theorem excision_of_union {X A B : Set E} (hAX : A ⊆ X) (hBX : B ⊆ X)
    (h : interior ((↑) ⁻¹' A : Set X) ∪ interior ((↑) ⁻¹' B : Set X) = univ) (n : ℕ) :
    IsIso ((relHomology (ModuleCat.of R R) n).map
      (subsetPairHom inter_subset_right hAX inter_subset_left hBX)) :=
  excision_of_eq_inter R hAX hBX inter_subset_right inter_subset_left rfl h n

/-- **Excision** (Hatcher, Thm. 2.20): if `Z ⊆ A ⊆ X` (subsets of a space `E`) and the closure of
`Z` in `X` is contained in the interior of `A` in `X`, then the inclusion of pairs
`(X ∖ Z, A ∖ Z) ⟶ (X, A)` induces isomorphisms `H_n(X ∖ Z, A ∖ Z) ≅ H_n(X, A)` in all
degrees. -/
theorem excision {X A Z : Set E} (hAX : A ⊆ X)
    (h : closure ((↑) ⁻¹' Z : Set X) ⊆ interior ((↑) ⁻¹' A : Set X)) (n : ℕ) :
    IsIso ((relHomology (ModuleCat.of R R) n).map
      (subsetPairHom (sdiff_subset_sdiff_left hAX : A \ Z ⊆ X \ Z) hAX sdiff_subset
        sdiff_subset)) := by
  refine excision_of_eq_inter R hAX sdiff_subset _ _ ?_ ?_ n
  · ext x
    simp only [mem_inter_iff, mem_sdiff]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, hAX h.1, h.2⟩⟩
  · have hB : ((↑) ⁻¹' (X \ Z) : Set X) = ((↑) ⁻¹' Z : Set X)ᶜ := by
      ext x
      simp
    rw [hB, interior_compl, eq_univ_iff_forall]
    intro x
    by_cases hx : x ∈ closure ((↑) ⁻¹' Z : Set X)
    · exact Or.inl (h hx)
    · exact Or.inr hx

/-- **Excision**, with closure and interior taken in the ambient space: if `Z ⊆ A ⊆ X` are subsets
of a space `E` with `closure Z ⊆ interior A`, then `(X ∖ Z, A ∖ Z) ⟶ (X, A)` induces isomorphisms
`H_n(X ∖ Z, A ∖ Z) ≅ H_n(X, A)` in all degrees (for instance for `X = E`). -/
theorem excision_of_closure_subset_interior {X A Z : Set E} (hAX : A ⊆ X)
    (h : closure Z ⊆ interior A) (n : ℕ) :
    IsIso ((relHomology (ModuleCat.of R R) n).map
      (subsetPairHom (sdiff_subset_sdiff_left hAX : A \ Z ⊆ X \ Z) hAX sdiff_subset
        sdiff_subset)) :=
  excision R hAX ((continuous_subtype_val.closure_preimage_subset Z).trans
    ((preimage_mono h).trans (preimage_interior_subset_interior_preimage continuous_subtype_val)))
    n

end Excision

end Morse.Homology
