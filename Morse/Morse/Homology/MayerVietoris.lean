import Morse.Homology.Excision
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Homology.HomologySequence

/-!
# The Mayer–Vietoris sequence

Let `A, B ⊆ X` be subspaces whose interiors cover `X`.  The **Mayer–Vietoris sequence** is the
long exact sequence
`⋯ ⟶ H_n(A ∩ B) ⟶ H_n(A) ⊞ H_n(B) ⟶ H_n(X) ⟶∂ H_{n-1}(A ∩ B) ⟶ ⋯`,
where the first map is `(i_*, -i'_*)` (induced by the inclusions of `A ∩ B` in `A` and `B`), the
second is `j_* + j'_*` (induced by the inclusions of `A` and `B` in `X`).

## Proof

Inside the concrete singular chains of `X`, the chains in `A ∩ B`, in `A`, in `B`, and the
`{A, B}`-small chains form subcomplexes `C(A ∩ B)`, `C(A)`, `C(B)`, `C^U(X)`, and
`0 ⟶ C(A ∩ B) ⟶ C(A) ⊞ C(B) ⟶ C^U(X) ⟶ 0` (with maps `x ↦ (x, -x)` and `(y, z) ↦ y + z`) is a
short exact sequence of complexes (`Morse.Homology.mvShortComplex_shortExact`): a chain lying both
in `A` and in `B` lies in `A ∩ B`, and a `U`-small chain is a chain in `A` plus a chain in `B`.
Its homology sequence is the Mayer–Vietoris sequence, once `H(C^U(X))` is identified with `H(X)`
by the small chains theorem (`Morse.Homology.quasiIso_smallChainsι`).

The homology of the concrete subcomplexes is then identified with Mathlib's singular homology of
the subspaces: the singular chains of a subspace `S` are the chains of `X` made of simplices in
`S` (`Morse.Homology.subspaceChainsIso`, `Morse.Homology.mathlibChainsIso`), and homology
commutes with biproducts (it is an additive functor).

## Main results

All homology groups are Mathlib's singular homology with coefficients in a commutative ring `R`,
`((singularChains (ModuleCat.of R R)).obj Y).homology n`, of the subspaces `TopCat.of S`.

* `Morse.Homology.mvShortComplex_shortExact`: the Mayer–Vietoris short exact sequence of chain
  complexes;
* `Morse.Homology.mvMap₁ : H_n(A ∩ B) ⟶ H_n(A) ⊞ H_n(B)`, `(i_*, -i'_*)`, and
  `Morse.Homology.mvMap₂ : H_n(A) ⊞ H_n(B) ⟶ H_n(X)`, `j_* + j'_*`; the connecting morphism
  `Morse.Homology.mvδ : H_{n+1}(X) ⟶ H_n(A ∩ B)`;
* **exactness** at `H_n(A ∩ B)` (`Morse.Homology.mv_exact₁`), at `H_n(A) ⊞ H_n(B)`
  (`Morse.Homology.mv_exact₂`) and at `H_{n+1}(X)` (`Morse.Homology.mv_exact₃`), when the
  interiors of `A` and `B` cover `X`.
-/

open CategoryTheory Limits Set Topology HomologicalComplex

noncomputable section

namespace Morse.Homology

universe u v

/-! ### Chains in a subset, as a subcomplex -/

section Subcomplexes

variable (R : Type u) [Ring R] {X : Type v} [TopologicalSpace X]

/-- The subcomplex `C(S) ⊆ C(X)` of the singular chains of `X` made of simplices in `S`. -/
abbrev chainsIn (S : Set X) : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  suppChains R (isPrecompClosed_inSet S)

/-- The inclusion `C(S) ⊆ C(T)` of subcomplexes, for `S ⊆ T`. -/
def chainsInIncl {S T : Set X} (h : S ⊆ T) : chainsIn R S ⟶ chainsIn R T :=
  subcomplexMap (𝟙 _) (fun _ _ hx ↦ Finsupp.supported_mono (fun _ hσ ↦ hσ.trans h) hx)

lemma chainsInIncl_f_apply {S T : Set X} (h : S ⊆ T) (n : ℕ) (x : supp R X (inSet S) n) :
    (((chainsInIncl R h).f n x : supp R X (inSet T) n) : Chains R X n) = x := rfl

lemma chainsInIncl_comp {S T W : Set X} (h : S ⊆ T) (h' : T ⊆ W) :
    chainsInIncl R h ≫ chainsInIncl R h' = chainsInIncl R (h.trans h') := rfl

/-- The inclusion `C(S) ⊆ C^U(X)` for `S` a member of the cover `U = {A, B}`. -/
def chainsInToSmall {S A B : Set X} (h : S = A ∨ S = B) :
    chainsIn R S ⟶ smallChains R X (coverOf A B) :=
  subcomplexMap (𝟙 _) (fun _ _ hx ↦ Finsupp.supported_mono
    (fun σ hσ ↦ mem_smallSet_coverOf.2 (by rcases h with rfl | rfl <;> simp [hσ])) hx)

lemma chainsInToSmall_f_apply {S A B : Set X} (h : S = A ∨ S = B) (n : ℕ)
    (x : supp R X (inSet S) n) :
    (((chainsInToSmall R h).f n x : supp R X (smallSet (coverOf A B)) n) : Chains R X n) = x :=
  rfl

end Subcomplexes

/-! ### The Mayer–Vietoris short exact sequence -/

section ShortExact

variable (R : Type u) [Ring R] {X : Type v} [TopologicalSpace X] (A B : Set X)

/-- The Mayer–Vietoris short complex `C(A ∩ B) ⟶ C(A) ⊞ C(B) ⟶ C^U(X)`, `x ↦ (x, -x)`,
`(y, z) ↦ y + z`, for the cover `U = {A, B}`. -/
abbrev mvShortComplex : ShortComplex (ChainComplex (ModuleCat.{max u v} R) ℕ) :=
  ShortComplex.mk
    (biprod.lift (chainsInIncl R (inter_subset_left : A ∩ B ⊆ A))
      (-chainsInIncl R (inter_subset_right : A ∩ B ⊆ B)))
    (biprod.desc (chainsInToSmall R (S := A) (A := A) (B := B) (Or.inl rfl))
      (chainsInToSmall R (S := B) (A := A) (B := B) (Or.inr rfl))) (by
      rw [biprod.lift_desc, Preadditive.neg_comp, ← sub_eq_add_neg, sub_eq_zero]
      rfl)

/-- Elements of a biproduct of complexes are determined by their two components. -/
lemma biprod_X_eq_add {K L : ChainComplex (ModuleCat.{max u v} R) ℕ} (n : ℕ) (y : (K ⊞ L).X n) :
    y = (biprod.inl : K ⟶ K ⊞ L).f n ((biprod.fst : K ⊞ L ⟶ K).f n y) +
      (biprod.inr : L ⟶ K ⊞ L).f n ((biprod.snd : K ⊞ L ⟶ L).f n y) := by
  have h := congr($(biprod_total_f K L n).hom y)
  rw [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  exact h.symm

lemma mv_fst_f (n : ℕ) (x : supp R X (inSet (A ∩ B)) n) :
    (biprod.fst : chainsIn R A ⊞ chainsIn R B ⟶ _).f n ((mvShortComplex R A B).f.f n x) =
      (chainsInIncl R (inter_subset_left : A ∩ B ⊆ A)).f n x := by
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f]
  simp [mvShortComplex]

lemma mv_snd_f (n : ℕ) (x : supp R X (inSet (A ∩ B)) n) :
    (biprod.snd : chainsIn R A ⊞ chainsIn R B ⟶ _).f n ((mvShortComplex R A B).f.f n x) =
      -(chainsInIncl R (inter_subset_right : A ∩ B ⊆ B)).f n x := by
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f]
  simp [mvShortComplex]

lemma mv_g_inl (n : ℕ) (a : supp R X (inSet A) n) :
    (mvShortComplex R A B).g.f n ((biprod.inl : chainsIn R A ⟶ chainsIn R A ⊞ chainsIn R B).f n a) =
      (chainsInToSmall R (S := A) (A := A) (B := B) (Or.inl rfl)).f n a := by
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f]
  simp [mvShortComplex]

lemma mv_g_inr (n : ℕ) (b : supp R X (inSet B) n) :
    (mvShortComplex R A B).g.f n ((biprod.inr : chainsIn R B ⟶ chainsIn R A ⊞ chainsIn R B).f n b) =
      (chainsInToSmall R (S := B) (A := A) (B := B) (Or.inr rfl)).f n b := by
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f]
  simp [mvShortComplex]

lemma inSet_inter (n : ℕ) : inSet (A ∩ B) n = inSet A n ∩ inSet B n := by
  ext σ
  exact subset_inter_iff

/-- **The Mayer–Vietoris short exact sequence** `0 ⟶ C(A ∩ B) ⟶ C(A) ⊞ C(B) ⟶ C^U(X) ⟶ 0`. -/
theorem mvShortComplex_shortExact : (mvShortComplex R A B).ShortExact := by
  classical
  refine shortExact_of_degreewise_shortExact _ fun n ↦ ?_
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- exactness at `C(A) ⊞ C(B)`: a chain in `A` which is also a chain in `B` is in `A ∩ B`
    rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    change (mvShortComplex R A B).g.f n y = 0 at hy
    set a := (biprod.fst : chainsIn R A ⊞ chainsIn R B ⟶ _).f n y
    set b := (biprod.snd : chainsIn R A ⊞ chainsIn R B ⟶ _).f n y
    have hy' := biprod_X_eq_add R n y
    rw [hy', map_add, mv_g_inl, mv_g_inr] at hy
    have hab : (a : Chains R X n) + (b : Chains R X n) = 0 := congr_arg Subtype.val hy
    have ha : (a : Chains R X n) ∈ supp R X (inSet (A ∩ B)) n := by
      rw [supp, inSet_inter, Finsupp.supported_inter]
      refine Submodule.mem_inf.2 ⟨a.2, ?_⟩
      rw [eq_neg_of_add_eq_zero_left hab]
      exact neg_mem b.2
    refine ⟨(⟨a, ha⟩ : supp R X (inSet (A ∩ B)) n), ?_⟩
    change (mvShortComplex R A B).f.f n ⟨a, ha⟩ = y
    rw [biprod_X_eq_add R n ((mvShortComplex R A B).f.f n ⟨a, ha⟩), mv_fst_f, mv_snd_f, hy']
    congr 2
    apply Subtype.ext
    change -(a : Chains R X n) = b
    rw [eq_neg_of_add_eq_zero_left hab, neg_neg]
  · -- injectivity of `C(A ∩ B) ⟶ C(A) ⊞ C(B)`
    rw [ModuleCat.mono_iff_injective]
    intro x x' h
    change (mvShortComplex R A B).f.f n x = (mvShortComplex R A B).f.f n x' at h
    have h₁ := mv_fst_f R A B n x
    have h₂ := mv_fst_f R A B n x'
    rw [h] at h₁
    have h₃ := congr_arg Subtype.val (h₁.symm.trans h₂)
    exact Subtype.ext h₃
  · -- surjectivity of `C(A) ⊞ C(B) ⟶ C^U(X)`: a small chain is a chain in `A` plus one in `B`
    rw [ModuleCat.epi_iff_surjective]
    rintro ⟨z, hz⟩
    let p : C(Simplex n, X) → Prop := fun σ ↦ σ ∈ inSet A n
    have hA : z.filter p ∈ supp R X (inSet A) n := by
      rw [supp, Finsupp.mem_supported, Finsupp.support_filter, Finset.coe_filter]
      exact fun σ hσ ↦ hσ.2
    have hB : z.filter (fun σ ↦ ¬ p σ) ∈ supp R X (inSet B) n := by
      rw [supp, Finsupp.mem_supported, Finsupp.support_filter, Finset.coe_filter]
      rintro σ ⟨hσz, hσA⟩
      rcases mem_smallSet_coverOf.1 (hz hσz) with h | h
      · exact absurd h hσA
      · exact h
    refine ⟨(biprod.inl : chainsIn R A ⟶ chainsIn R A ⊞ chainsIn R B).f n ⟨_, hA⟩ +
      (biprod.inr : chainsIn R B ⟶ chainsIn R A ⊞ chainsIn R B).f n ⟨_, hB⟩, ?_⟩
    change (mvShortComplex R A B).g.f n _ = _
    rw [map_add, mv_g_inl, mv_g_inr]
    exact Subtype.ext (Finsupp.filter_add_filter_not z p)

end ShortExact

/-! ### Chains of a subspace -/

section Subspace

variable (R : Type u) [Ring R] {X : Type v} [TopologicalSpace X]

/-- The inclusion of a subspace, as a continuous map. -/
abbrev subtypeValC (S : Set X) : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩

lemma push_subtypeVal_mem (S : Set X) (n : ℕ) (c : Chains R S n) :
    push (subtypeValC S) n c ∈ supp R X (inSet S) n := by
  have h := (range_push (R := R) (j := subtypeValC S) IsEmbedding.subtypeVal n).le ⟨c, rfl⟩
  rwa [show range (subtypeValC S) = S from Subtype.range_coe] at h

/-- The singular chains of a subspace `S ⊆ X` are the chains of `X` made of simplices in `S`:
the chain map `C(S) ⟶ C_S(X)` induced by the inclusion (an isomorphism,
`Morse.Homology.subspaceChainsIso`). -/
def subspaceChainsHom (S : Set X) : singChains R S ⟶ chainsIn R S :=
  natHomMk (fun n ↦ ModuleCat.ofHom ((push (subtypeValC S) n).codRestrict _
      (push_subtypeVal_mem R S n)))
    (fun n ↦ by
      rw [subcomplex_d]
      refine ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R S (n + 1)) ↦ Subtype.ext ?_)
      change (singChains R X).d (n + 1) n (push (subtypeValC S) (n + 1) c) =
        push (subtypeValC S) n ((singChains R S).d (n + 1) n c)
      rw [singChains_d, singChains_d]
      exact (push_sbd _ n c).symm)

lemma subspaceChainsHom_f_apply (S : Set X) (n : ℕ) (c : Chains R S n) :
    (((subspaceChainsHom R S).f n c : supp R X (inSet S) n) : Chains R X n) =
      push (subtypeValC S) n c := rfl

lemma bijective_subspaceChainsHom_f (S : Set X) (n : ℕ) :
    Function.Bijective ((subspaceChainsHom R S).f n) := by
  refine ⟨fun c c' h ↦ push_injective (R := R) Subtype.val_injective n
    (congr_arg Subtype.val h), fun ⟨x, hx⟩ ↦ ?_⟩
  have hx' : x ∈ LinearMap.range (push (R := R) (subtypeValC S) n) := by
    rw [range_push IsEmbedding.subtypeVal n, show range (subtypeValC S) = S from
      Subtype.range_coe]
    exact hx
  obtain ⟨c, rfl⟩ := hx'
  exact ⟨c, rfl⟩

instance (S : Set X) : IsIso (subspaceChainsHom R S) := by
  have (n : ℕ) : IsIso ((subspaceChainsHom R S).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_subspaceChainsHom_f R S n)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Chains of a subspace**: `C(S) ≅ C_S(X)`. -/
def subspaceChainsIso (S : Set X) : singChains R S ≅ chainsIn R S :=
  asIso (subspaceChainsHom R S)

lemma pushHom_inclusion_subspaceChainsHom {S T : Set X} (h : S ⊆ T) :
    pushHom (R := R) ⟨Set.inclusion h, continuous_inclusion h⟩ ≫ subspaceChainsHom R T =
      subspaceChainsHom R S ≫ chainsInIncl R h := by
  ext n : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R S n) ↦ Subtype.ext ?_)
  change push (subtypeValC T) n (push ⟨Set.inclusion h, continuous_inclusion h⟩ n c) =
    push (subtypeValC S) n c
  rw [← push_comp]
  rfl

lemma subspaceChainsHom_toSmall {S A B : Set X} (hS : S = A ∨ S = B) :
    subspaceChainsHom R S ≫ chainsInToSmall R hS ≫ smallChainsι R (coverOf A B) =
      pushHom (subtypeValC S) := by
  ext n : 1
  exact ModuleCat.hom_ext (LinearMap.ext fun (c : Chains R S n) ↦ rfl)

end Subspace

/-! ### Transport of exactness along isomorphisms -/

lemma exact_mk_of_iso {C : Type*} [Category* C] [HasZeroMorphisms C] {T : ShortComplex C}
    (hT : T.Exact) {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} (w : f ≫ g = 0)
    (e₁ : T.X₁ ≅ X₁) (e₂ : T.X₂ ≅ X₂) (e₃ : T.X₃ ≅ X₃) (h₁ : e₁.hom ≫ f = T.f ≫ e₂.hom)
    (h₂ : e₂.hom ≫ g = T.g ≫ e₃.hom) : (ShortComplex.mk f g w).Exact :=
  (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂)).1 hT

/-! ### The Mayer–Vietoris sequence in singular homology -/

section Sequence

variable (R : Type u) [CommRing R] {X : Type u} [TopologicalSpace X] (A B : Set X)

/-- Mathlib's singular chains of a subspace `S ⊆ X` are isomorphic to the chains of `X` made of
simplices in `S`. -/
def mathlibChainsIso (S : Set X) :
    (singularChains (ModuleCat.of R R)).obj (TopCat.of S) ≅ chainsIn R S :=
  (singChainsIso R).app (TopCat.of S) ≪≫ subspaceChainsIso R S

lemma mathlibChainsIso_hom (S : Set X) : (mathlibChainsIso R S).hom =
    (singChainsIso R).hom.app (TopCat.of S) ≫ subspaceChainsHom R S := rfl

/-- The inclusion `S ↪ X` of a subspace, as a morphism of `TopCat`. -/
abbrev topVal (S : Set X) : TopCat.of S ⟶ TopCat.of X := TopCat.ofHom (subtypeValC S)

lemma mathlibChainsIso_incl {S T : Set X} (h : S ⊆ T) :
    (singularChains (ModuleCat.of R R)).map (subsetInclusion h) ≫ (mathlibChainsIso R T).hom =
      (mathlibChainsIso R S).hom ≫ chainsInIncl R h := by
  rw [mathlibChainsIso_hom, mathlibChainsIso_hom, ← Category.assoc,
    (singChainsIso R).hom.naturality (subsetInclusion h), Category.assoc, Category.assoc]
  congr 1
  exact pushHom_inclusion_subspaceChainsHom R h

lemma mathlibChainsIso_val {S : Set X} (hS : S = A ∨ S = B) :
    (singularChains (ModuleCat.of R R)).map (topVal S) ≫ (singChainsIso R).hom.app (TopCat.of X) =
      (mathlibChainsIso R S).hom ≫ chainsInToSmall R hS ≫ smallChainsι R (coverOf A B) := by
  rw [mathlibChainsIso_hom, (singChainsIso R).hom.naturality (topVal S), Category.assoc,
    subspaceChainsHom_toSmall]
  rfl

lemma mathlibChainsIso_inv_incl {S T : Set X} (h : S ⊆ T) :
    (mathlibChainsIso R S).inv ≫ (singularChains (ModuleCat.of R R)).map (subsetInclusion h) =
      chainsInIncl R h ≫ (mathlibChainsIso R T).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← mathlibChainsIso_incl, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

lemma mathlibChainsIso_inv_val {S : Set X} (hS : S = A ∨ S = B) :
    (mathlibChainsIso R S).inv ≫ (singularChains (ModuleCat.of R R)).map (topVal S) =
      chainsInToSmall R hS ≫ smallChainsι R (coverOf A B) ≫
        ((singChainsIso R).app (TopCat.of X)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← Category.assoc, Iso.eq_comp_inv, Category.assoc]
  exact mathlibChainsIso_val R A B hS

variable {A B} (h : interior A ∪ interior B = univ) (n : ℕ)

include h in
lemma isIso_homologyMap_smallChainsι (n : ℕ) :
    IsIso (homologyMap (smallChainsι R (coverOf A B)) n) := by
  have := quasiIso_smallChainsι R (iUnion_interior_coverOf h)
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

/-- Homology preserves binary biproducts (it is an additive functor). -/
instance (n : ℕ) :
    PreservesBinaryBiproducts (homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

variable (A B)

/-- `H_n(C(A ∩ B)) ≅ H_n(A ∩ B)`. -/
def mvIso₁ : (chainsIn R (A ∩ B)).homology n ≅
    ((singularChains (ModuleCat.of R R)).obj (TopCat.of ↥(A ∩ B))).homology n :=
  ((homologyFunctor _ _ n).mapIso (mathlibChainsIso R (A ∩ B))).symm

/-- `H_n(C(A) ⊞ C(B)) ≅ H_n(A) ⊞ H_n(B)`. -/
def mvIso₂ : (chainsIn R A ⊞ chainsIn R B).homology n ≅
    ((singularChains (ModuleCat.of R R)).obj (TopCat.of A)).homology n ⊞
      ((singularChains (ModuleCat.of R R)).obj (TopCat.of B)).homology n :=
  (homologyFunctor _ _ n).mapBiprod (chainsIn R A) (chainsIn R B) ≪≫
    biprod.mapIso ((homologyFunctor _ _ n).mapIso (mathlibChainsIso R A)).symm
      ((homologyFunctor _ _ n).mapIso (mathlibChainsIso R B)).symm

/-- `H_n(C^U(X)) ≅ H_n(X)`, by the small chains theorem. -/
def mvIso₃ : (smallChains R X (coverOf A B)).homology n ≅
    ((singularChains (ModuleCat.of R R)).obj (TopCat.of X)).homology n :=
  have := isIso_homologyMap_smallChainsι R h n
  asIso (homologyMap (smallChainsι R (coverOf A B)) n) ≪≫
    ((homologyFunctor _ _ n).mapIso ((singChainsIso R).app (TopCat.of X))).symm

/-- The map `H_n(A ∩ B) ⟶ H_n(A) ⊞ H_n(B)` of the Mayer–Vietoris sequence, `(i_*, -i'_*)`. -/
abbrev mvMap₁ : ((singularChains (ModuleCat.of R R)).obj (TopCat.of ↥(A ∩ B))).homology n ⟶
    ((singularChains (ModuleCat.of R R)).obj (TopCat.of A)).homology n ⊞
      ((singularChains (ModuleCat.of R R)).obj (TopCat.of B)).homology n :=
  biprod.lift
    (homologyMap ((singularChains (ModuleCat.of R R)).map (subsetInclusion inter_subset_left)) n)
    (-homologyMap ((singularChains (ModuleCat.of R R)).map (subsetInclusion inter_subset_right)) n)

/-- The map `H_n(A) ⊞ H_n(B) ⟶ H_n(X)` of the Mayer–Vietoris sequence, `j_* + j'_*`. -/
abbrev mvMap₂ : ((singularChains (ModuleCat.of R R)).obj (TopCat.of A)).homology n ⊞
      ((singularChains (ModuleCat.of R R)).obj (TopCat.of B)).homology n ⟶
    ((singularChains (ModuleCat.of R R)).obj (TopCat.of X)).homology n :=
  biprod.desc (homologyMap ((singularChains (ModuleCat.of R R)).map (topVal A)) n)
    (homologyMap ((singularChains (ModuleCat.of R R)).map (topVal B)) n)

lemma mvIso₁_hom : (mvIso₁ R A B n).hom = homologyMap (mathlibChainsIso R (A ∩ B)).inv n := rfl

lemma mvIso₂_hom : (mvIso₂ R A B n).hom =
    biprod.lift (homologyMap (biprod.fst ≫ (mathlibChainsIso R A).inv) n)
      (homologyMap (biprod.snd ≫ (mathlibChainsIso R B).inv) n) := by
  apply biprod.hom_ext
  · rw [biprod.lift_fst, mvIso₂]
    erw [Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_fst, Functor.mapBiprod_hom,
      biprod.lift_fst_assoc]
    rw [homologyMap_comp]
    rfl
  · rw [biprod.lift_snd, mvIso₂]
    erw [Iso.trans_hom, Category.assoc, biprod.mapIso_hom, biprod.map_snd, Functor.mapBiprod_hom,
      biprod.lift_snd_assoc]
    rw [homologyMap_comp]
    rfl

lemma mvIso₃_hom : (mvIso₃ R A B h n).hom =
    homologyMap (smallChainsι R (coverOf A B) ≫ ((singChainsIso R).app (TopCat.of X)).inv) n := by
  rw [homologyMap_comp]
  rfl

lemma mvIso₁_hom_comp_mvMap₁ :
    (mvIso₁ R A B n).hom ≫ mvMap₁ R A B n =
      homologyMap (mvShortComplex R A B).f n ≫ (mvIso₂ R A B n).hom := by
  rw [mvIso₁_hom, mvIso₂_hom]
  apply biprod.hom_ext
  · rw [Category.assoc, Category.assoc, biprod.lift_fst, biprod.lift_fst, ← homologyMap_comp,
      ← homologyMap_comp, mathlibChainsIso_inv_incl, biprod.lift_fst_assoc]
  · rw [Category.assoc, Category.assoc, biprod.lift_snd, biprod.lift_snd, Preadditive.comp_neg,
      ← homologyMap_comp, ← homologyMap_comp, mathlibChainsIso_inv_incl, biprod.lift_snd_assoc,
      Preadditive.neg_comp, homologyMap_neg]

lemma mvIso₂_hom_comp_mvMap₂ :
    (mvIso₂ R A B n).hom ≫ mvMap₂ R A B n =
      homologyMap (mvShortComplex R A B).g n ≫ (mvIso₃ R A B h n).hom := by
  rw [mvIso₂_hom, mvIso₃_hom, biprod.lift_desc, ← homologyMap_comp, ← homologyMap_comp,
    ← homologyMap_add, ← homologyMap_comp, Category.assoc, Category.assoc,
    mathlibChainsIso_inv_val R A B (Or.inl rfl), mathlibChainsIso_inv_val R A B (Or.inr rfl),
    ← Category.assoc biprod.fst, ← Category.assoc biprod.snd, ← Preadditive.add_comp,
    ← biprod.desc_eq]

/-- The **Mayer–Vietoris connecting morphism** `∂ : H_{n+1}(X) ⟶ H_n(A ∩ B)`. -/
def mvδ : ((singularChains (ModuleCat.of R R)).obj (TopCat.of X)).homology (n + 1) ⟶
    ((singularChains (ModuleCat.of R R)).obj (TopCat.of ↥(A ∩ B))).homology n :=
  (mvIso₃ R A B h (n + 1)).inv ≫
    (mvShortComplex_shortExact R A B).δ (n + 1) n
      (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl) ≫
    (mvIso₁ R A B n).hom

lemma mvMap₁_comp_mvMap₂ : mvMap₁ R A B n ≫ mvMap₂ R A B n = 0 := by
  rw [biprod.lift_desc, Preadditive.neg_comp, ← sub_eq_add_neg, sub_eq_zero, ← homologyMap_comp,
    ← homologyMap_comp, ← Functor.map_comp, ← Functor.map_comp]
  rfl

lemma mvMap₂_comp_mvδ : mvMap₂ R A B (n + 1) ≫ mvδ R A B h n = 0 := by
  rw [(Iso.eq_inv_comp _).2 (mvIso₂_hom_comp_mvMap₂ R A B h (n + 1)), mvδ, Category.assoc,
    Category.assoc, Iso.hom_inv_id_assoc, (mvShortComplex_shortExact R A B).comp_δ_assoc,
    zero_comp, comp_zero]

lemma mvδ_comp_mvMap₁ : mvδ R A B h n ≫ mvMap₁ R A B n = 0 := by
  rw [mvδ, Category.assoc, Category.assoc, mvIso₁_hom_comp_mvMap₁,
    (mvShortComplex_shortExact R A B).δ_comp_assoc, zero_comp, comp_zero]

include h in
/-- **The Mayer–Vietoris sequence, exactness at `H_n(A) ⊞ H_n(B)`**: if the interiors of `A` and
`B` cover `X`, then `H_n(A ∩ B) ⟶ H_n(A) ⊞ H_n(B) ⟶ H_n(X)` is exact. -/
theorem mv_exact₂ :
    (ShortComplex.mk (mvMap₁ R A B n) (mvMap₂ R A B n) (mvMap₁_comp_mvMap₂ R A B n)).Exact :=
  exact_mk_of_iso ((mvShortComplex_shortExact R A B).homology_exact₂ n) _ (mvIso₁ R A B n)
    (mvIso₂ R A B n) (mvIso₃ R A B h n) (mvIso₁_hom_comp_mvMap₁ R A B n)
    (mvIso₂_hom_comp_mvMap₂ R A B h n)

/-- **The Mayer–Vietoris sequence, exactness at `H_{n+1}(X)`**: if the interiors of `A` and `B`
cover `X`, then `H_{n+1}(A) ⊞ H_{n+1}(B) ⟶ H_{n+1}(X) ⟶∂ H_n(A ∩ B)` is exact. -/
theorem mv_exact₃ :
    (ShortComplex.mk (mvMap₂ R A B (n + 1)) (mvδ R A B h n) (mvMap₂_comp_mvδ R A B h n)).Exact :=
  exact_mk_of_iso ((mvShortComplex_shortExact R A B).homology_exact₃ (n + 1) n rfl) _
    (mvIso₂ R A B (n + 1)) (mvIso₃ R A B h (n + 1)) (mvIso₁ R A B n)
    (mvIso₂_hom_comp_mvMap₂ R A B h (n + 1)) (by rw [mvδ, Iso.hom_inv_id_assoc])

/-- **The Mayer–Vietoris sequence, exactness at `H_n(A ∩ B)`**: if the interiors of `A` and `B`
cover `X`, then `H_{n+1}(X) ⟶∂ H_n(A ∩ B) ⟶ H_n(A) ⊞ H_n(B)` is exact. -/
theorem mv_exact₁ :
    (ShortComplex.mk (mvδ R A B h n) (mvMap₁ R A B n) (mvδ_comp_mvMap₁ R A B h n)).Exact :=
  exact_mk_of_iso ((mvShortComplex_shortExact R A B).homology_exact₁ (n + 1) n rfl) _
    (mvIso₃ R A B h (n + 1)) (mvIso₁ R A B n) (mvIso₂ R A B n)
    (by rw [mvδ, Iso.hom_inv_id_assoc]) (mvIso₁_hom_comp_mvMap₁ R A B n)

end Sequence

end Morse.Homology
