import Morse.Homology.CellExcision
import Morse.Homology.Triple

/-!
# The homology of disks and spheres

Let `Dⁿ` be the closed unit ball and `Sⁿ⁻¹` the unit sphere of `ℝⁿ = EuclideanSpace ℝ (Fin n)`
(`S⁻¹ = ∅`).  With coefficients in a commutative ring `R` (the coefficient object
`ModuleCat.of R R`), this file proves:

* `H_i(Dⁿ, Sⁿ⁻¹; R) ≅ R` for `i = n` and `= 0` for `i ≠ n` (`relHomologyDiskPairIso`,
  `isZero_relHomology_diskPair`); over a field, `dim H_i(Dⁿ, Sⁿ⁻¹; 𝕜) = [i = n]`
  (`finrank_relHomology_diskPair`);
* `H_0(Sⁿ; R) ≅ R` and `H_n(Sⁿ; R) ≅ R` for `n ≥ 1`, `H_0(S⁰; R) ≅ R ⊞ R`, and `H_i(Sⁿ; R) = 0`
  for `i ≠ 0, n` (`sphereHomologyZeroIso`, `sphereHomologyTopIso`, `sphereHomologyZeroIsoBiprod`,
  `isZero_sphereHomology`); over a field, `dim H_i(Sⁿ; 𝕜) = [i = 0] + [i = n]`
  (`finrank_sphereHomology`).

## Cells and spheres in an arbitrary space

All of this is proved for *embedded* cells and spheres in a Hausdorff space `E`, in any universe
(that of the coefficient ring, as required by excision).  If `χ : ℝᵏ → E` is continuous and
injective on `Dᵏ`, the pair `(χ(Dᵏ), χ(Sᵏ⁻¹))` (`Morse.Homology.cellPair χ`) has `H_k ≅ R`
(`cellPairIso`) and `H_i = 0` for `i ≠ k` (`isZero_relHomology_cellPair`); if `χ` is continuous
and injective on `Sⁿ`, then `χ(Sⁿ)` has the homology of `Sⁿ` (`homologyImageSphereZeroIso`,
`homologyImageSphereTopIso`, `isZero_homology_imageSphere`, `finrank_homology_imageSphere`).  The
statements for `ℝⁿ` are the case `χ = id`.  Mathlib's disk pair `(𝔻ⁿ, ∂𝔻ⁿ)`
(`TopCat.disk`, `TopCat.diskBoundary`, in any universe; `Morse.Homology.topDiskPair`) is
homeomorphic to every cell pair (`diskToCell`, `isIso_relHomology_map_diskToCell`), which gives
its homology in any universe (`relHomologyTopDiskPairIso`, `isZero_relHomology_topDiskPair`).

## Proof

By induction on `k`.

1. *Base case*: `(χ(D⁰), χ(S⁻¹)) = (pt, ∅)`; `H_0(pt) ≅ R` by Mathlib's augmentation
   `TopCat.singularHomology₀ε` (an isomorphism for path-connected spaces), and `H_i(pt) = 0` for
   `i ≠ 0`.
2. *The boundary of a triple*: let `q = χ(-eₖ₊₁)` be the image of the south pole.  The cell
   `χ(Dᵏ⁺¹)` contracts onto `q` (`isStrongDeformationRetract_singleton_image`), so
   `H_*(χ(Dᵏ⁺¹), {q}) = 0`, and in the triple `{q} ⊆ χ(Sᵏ) ⊆ χ(Dᵏ⁺¹)` the boundary
   `H_{i+1}(χ(Dᵏ⁺¹), χ(Sᵏ)) ⟶ H_i(χ(Sᵏ), {q})` is an isomorphism (`isIso_cellTriple_δ`), while
   `H_0(χ(Dᵏ⁺¹), χ(Sᵏ)) = 0`.
3. *The sphere lemma* (`sphereRelIso`): `Sᵏ` is the union of the lower and upper hemispheres
   `D₋` and `D₊`, the graphs of `∓√(1 - ‖z‖²)` over `Dᵏ` (`hemisphere`), and `D₊` is a `k`-cell
   attached to `D₋` along the equator (`sphere_eq_union_hemisphere`, `hemisphere_one_mem_iff`).
   As `D₋` contracts onto `q`, `H_i(χ(Sᵏ), {q}) ≅ H_i(χ(Sᵏ), χ(D₋))`, which is
   `H_i(χ(D₊), χ(Sᵏ⁻¹))` by excision for an attached cell
   (`Morse.Homology.isIso_relHomology_map_cellPair`): the homology of the `k`-cell
   `χ ∘ hemisphere 1` modulo its boundary, known by induction.

The absolute homology of spheres comes from the long exact sequence of `(χ(Sⁿ), {q})`, which
splits because a point is a retract: `H_i(X) ≅ H_i(A) ⊞ H_i(X, A)` for a retract `A` of `X`
(`homologyIsoBiprodOfRetraction`; for `A` a point, `H_i(X, A)` is the reduced homology).
-/

noncomputable section

open CategoryTheory Limits Set Metric Function HomologicalComplex Module

universe w v u

namespace Morse.Homology

/-! ### Hemispheres -/

section Hemisphere

variable {n : ℕ}

/-- The graph `z ↦ (z, s √(1 - ‖z‖²))` over the closed unit ball of `ℝⁿ`, in `ℝⁿ⁺¹`: for `s = 1`
the upper and for `s = -1` the lower hemisphere of the unit sphere `Sⁿ`. -/
def hemisphere (s : ℝ) (z : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ ↦ ℝ) z.ofLp (s * √(1 - ‖z‖ ^ 2)))

@[simp]
lemma hemisphere_castSucc (s : ℝ) (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    hemisphere s z i.castSucc = z i := by
  simp [hemisphere]

@[simp]
lemma hemisphere_last (s : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    hemisphere s z (Fin.last n) = s * √(1 - ‖z‖ ^ 2) := by
  simp [hemisphere]

/-- The hemisphere parametrizations are continuous. -/
lemma continuous_hemisphere (s : ℝ) : Continuous (hemisphere (n := n) s) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
  induction i using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last]
    exact continuous_const.mul (Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_norm.pow 2)))
  | cast i =>
    simp only [Fin.snoc_castSucc]
    exact (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)

/-- The hemisphere parametrizations are injective (the first `n` coordinates are kept). -/
lemma hemisphere_injective (s : ℝ) : Injective (hemisphere (n := n) s) := by
  intro z w h
  ext i
  rw [← hemisphere_castSucc s z i, ← hemisphere_castSucc s w i, h]

/-- `‖(z, t)‖² = ‖z‖² + t²` in `ℝⁿ⁺¹`. -/
lemma norm_sq_hemisphere (s : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    ‖hemisphere s z‖ ^ 2 = ‖z‖ ^ 2 + (s * √(1 - ‖z‖ ^ 2)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq (hemisphere s z), Fin.sum_univ_castSucc]
  simp only [hemisphere_castSucc, hemisphere_last]
  rw [← EuclideanSpace.real_norm_sq_eq z]

/-- For `s = ±1`, the graph of `s √(1 - ‖z‖²)` over the closed unit ball lies in the unit
sphere. -/
lemma hemisphere_mem_sphere {s : ℝ} (hs : s ^ 2 = 1) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    hemisphere s z ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  rw [mem_closedBall_zero_iff] at hz
  have h1 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    norm_sq_hemisphere, mul_pow, hs, one_mul, Real.sq_sqrt h1]
  ring

lemma mapsTo_hemisphere {s : ℝ} (hs : s ^ 2 = 1) :
    MapsTo (hemisphere (n := n) s) (closedBall 0 1) (sphere 0 1) :=
  fun _ hz ↦ hemisphere_mem_sphere hs hz

/-- The unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` is the union of its lower and upper hemispheres. -/
lemma sphere_eq_union_hemisphere :
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 =
      hemisphere (-1) '' closedBall 0 1 ∪ hemisphere 1 '' closedBall 0 1 := by
  apply Subset.antisymm
  · intro x hx
    set z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Fin.init x.ofLp) with hz_def
    have hnorm : ‖z‖ ^ 2 = 1 - x (Fin.last n) ^ 2 := by
      have h := EuclideanSpace.real_norm_sq_eq x
      rw [Fin.sum_univ_castSucc, mem_sphere_zero_iff_norm.1 hx] at h
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [z, Fin.init]
      linarith
    have hz : z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      rw [mem_closedBall_zero_iff, ← sq_le_one_iff₀ (norm_nonneg z), hnorm]
      nlinarith [sq_nonneg (x (Fin.last n))]
    have hsqrt : √(1 - ‖z‖ ^ 2) = |x (Fin.last n)| := by
      rw [hnorm, sub_sub_cancel, Real.sqrt_sq_eq_abs]
    have key : ∀ s : ℝ, s * |x (Fin.last n)| = x (Fin.last n) → hemisphere s z = x := by
      intro s hs
      ext i
      induction i using Fin.lastCases with
      | last => rw [hemisphere_last, hsqrt, hs]
      | cast i => rw [hemisphere_castSucc]; rfl
    rcases le_or_gt 0 (x (Fin.last n)) with h | h
    · exact Or.inr ⟨z, hz, key 1 (by rw [one_mul, abs_of_nonneg h])⟩
    · exact Or.inl ⟨z, hz, key (-1) (by rw [abs_of_neg h]; ring)⟩
  · rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact hemisphere_mem_sphere (by norm_num) hz
    · exact hemisphere_mem_sphere (by norm_num) hz

/-- A point of the upper hemisphere lies in the lower one exactly on the equator. -/
lemma hemisphere_one_mem_iff {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    hemisphere 1 z ∈ hemisphere (-1) '' closedBall 0 1 ↔ ‖z‖ = 1 := by
  rw [mem_closedBall_zero_iff] at hz
  constructor
  · rintro ⟨w, -, hw⟩
    have hwz : w = z := by
      ext i
      rw [← hemisphere_castSucc (-1) w i, hw, hemisphere_castSucc]
    subst hwz
    have h := congrArg (fun x ↦ x (Fin.last n)) hw
    simp only [hemisphere_last, one_mul, neg_one_mul] at h
    have h0 : √(1 - ‖w‖ ^ 2) = 0 := by linarith
    rw [Real.sqrt_eq_zero'] at h0
    nlinarith [norm_nonneg w]
  · intro h
    refine ⟨z, mem_closedBall_zero_iff.2 hz, ?_⟩
    ext i
    induction i using Fin.lastCases with
    | last => simp [h]
    | cast i => simp

end Hemisphere

/-! ### Splitting off a retract -/

section Retract

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)

/-- If the inclusion `A ↪ X` of a pair has a retraction `r`, the long exact sequence of the pair
splits into split short exact sequences `0 ⟶ H_n(A) ⟶ H_n(X) ⟶ H_n(X, A) ⟶ 0`, so that
`H_n(X) ≅ H_n(A) ⊞ H_n(X, A)`.  For `A` a point this is the splitting of the homology of a pointed
space into the homology of a point and its reduced homology. -/
def homologyIsoBiprodOfRetraction (X : TopPair.{w}) (r : X.fst ⟶ X.snd) (hr : X.map ≫ r = 𝟙 X.snd)
    (n : ℕ) : ((singularChains R).obj X.fst).homology n ≅
      ((singularChains R).obj X.snd).homology n ⊞ (relHomology R n).obj X :=
  have hS := relHomology_exact₂ R X n
  have hr' : homologyMap ((singularChains R).map X.map) n ≫
      homologyMap ((singularChains R).map r) n = 𝟙 _ := by
    rw [← homologyMap_comp, ← Functor.map_comp, hr, CategoryTheory.Functor.map_id, homologyMap_id]
  have hg : Epi (homologyMap (relπ R X) n) := by
    cases n with
    | zero => exact epi_homologyMap_relπ_zero R X
    | succ m =>
      have hm : homologyMap ((singularChains R).map X.map) m ≫
          homologyMap ((singularChains R).map r) m = 𝟙 _ := by
        rw [← homologyMap_comp, ← Functor.map_comp, hr, CategoryTheory.Functor.map_id,
          homologyMap_id]
      have : Mono (homologyMap ((singularChains R).map X.map) m) := mono_of_mono_fac hm
      have hδ : relδ R X m = 0 := (cancel_mono (homologyMap ((singularChains R).map X.map) m)).1
        (by rw [relδ_comp, zero_comp])
      exact (relHomology_exact₃ R X m).epi_f hδ
  (ShortComplex.Splitting.ofExactOfRetraction _ hS _ hr' hg).isoBinaryBiproduct

end Retract

/-! ### The homology of a point -/

section Point

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] (R : C)
  {E : Type w} [TopologicalSpace E]

/-- A point has no homology in positive degrees. -/
lemma isZero_homology_singleton (q : E) {n : ℕ} (hn : n ≠ 0) :
    IsZero (((singularChains R).obj (TopCat.of ({q} : Set E))).homology n) :=
  isZero_homology_of_contractibleSpace R (TopCat.of ({q} : Set E)) hn

/-- `H_0` of a point is `R` (the augmentation). -/
def homologyZeroSingletonIso (q : E) :
    ((singularChains R).obj (TopCat.of ({q} : Set E))).homology 0 ≅ R := by
  have : PathConnectedSpace (TopCat.of ({q} : Set E)) :=
    inferInstanceAs (PathConnectedSpace ({q} : Set E))
  -- elaborated without the expected type, so that the instance arguments are the canonical ones
  let e := asIso (TopCat.singularHomology₀ε (TopCat.of ({q} : Set E)) R)
  exact e

/-- Equal subsets have the same singular homology. -/
def homologyIsoOfEq {A B : Set E} (h : A = B) (n : ℕ) :
    ((singularChains R).obj (TopCat.of A)).homology n ≅
      ((singularChains R).obj (TopCat.of B)).homology n := by
  subst h
  exact Iso.refl _

/-- The constant retraction `B ⟶ {q}` of the pair `(B, {q})`. -/
def retractionSingleton {q : E} {B : Set E} (h : {q} ⊆ B) :
    (subsetPair h).fst ⟶ (subsetPair h).snd :=
  TopCat.ofHom (ContinuousMap.const _ ⟨q, rfl⟩)

/-- The constant map `B ⟶ {q}` is a retraction of the inclusion `{q} ⟶ B`. -/
lemma map_retractionSingleton {q : E} {B : Set E} (h : {q} ⊆ B) :
    (subsetPair h).map ≫ retractionSingleton h = 𝟙 _ := by
  have : Subsingleton (subsetPair h).snd := inferInstanceAs (Subsingleton ({q} : Set E))
  ext x
  exact Subsingleton.elim _ _

/-- **Reduced homology**: for a point `q ∈ B`, `H_n(B) ≅ H_n({q}) ⊞ H_n(B, {q})`. -/
def homologyIsoBiprodSingleton {q : E} {B : Set E} (h : {q} ⊆ B) (n : ℕ) :
    ((singularChains R).obj (TopCat.of B)).homology n ≅
      ((singularChains R).obj (TopCat.of ({q} : Set E))).homology n ⊞
        (relHomology R n).obj (subsetPair h) :=
  homologyIsoBiprodOfRetraction R (subsetPair h) (retractionSingleton h)
    (map_retractionSingleton h) n

end Point

/-! ### Dimension counts over a field -/

section Finrank

variable {𝕜 : Type u} [Field 𝕜]

/-- A module isomorphic to `𝕜` has dimension `1`. -/
lemma finrank_eq_one_of_iso {M : ModuleCat.{u} 𝕜} (e : M ≅ ModuleCat.of 𝕜 𝕜) : finrank 𝕜 M = 1 :=
  e.toLinearEquiv.finrank_eq.trans (finrank_self 𝕜)

/-- A zero module has dimension `0`. -/
lemma finrank_eq_zero_of_isZero {M : ModuleCat.{u} 𝕜} (h : IsZero M) : finrank 𝕜 M = 0 :=
  have := ModuleCat.isZero_iff_subsingleton.1 h
  finrank_zero_of_subsingleton

/-- A module isomorphic to `𝕜` is finite-dimensional. -/
lemma finite_of_iso {M : ModuleCat.{u} 𝕜} (e : M ≅ ModuleCat.of 𝕜 𝕜) : Module.Finite 𝕜 M :=
  Module.Finite.equiv e.symm.toLinearEquiv

/-- A zero module is finite-dimensional. -/
lemma finite_of_isZero {M : ModuleCat.{u} 𝕜} (h : IsZero M) : Module.Finite 𝕜 M :=
  have := ModuleCat.isZero_iff_subsingleton.1 h
  Module.Finite.of_finite

/-- Dimension is additive on biproducts of finite-dimensional modules. -/
lemma finrank_biprod (M N : ModuleCat.{u} 𝕜) [Module.Finite 𝕜 M] [Module.Finite 𝕜 N] :
    finrank 𝕜 ↑(M ⊞ N) = finrank 𝕜 M + finrank 𝕜 N :=
  (ModuleCat.biprodIsoProd M N).toLinearEquiv.finrank_eq.trans finrank_prod

/-- A biproduct of finite-dimensional modules is finite-dimensional. -/
lemma finite_biprod (M N : ModuleCat.{u} 𝕜) [Module.Finite 𝕜 M] [Module.Finite 𝕜 N] :
    Module.Finite 𝕜 ↑(M ⊞ N) :=
  Module.Finite.equiv (ModuleCat.biprodIsoProd M N).symm.toLinearEquiv

/-- A module which is `𝕜` when `P` holds and `0` otherwise is finite-dimensional, of dimension
`if P then 1 else 0`. -/
lemma finite_and_finrank_eq_ite {M : ModuleCat.{u} 𝕜} {P : Prop} [Decidable P]
    (h₁ : P → (M ≅ ModuleCat.of 𝕜 𝕜)) (h₀ : ¬P → IsZero M) :
    Module.Finite 𝕜 M ∧ finrank 𝕜 M = if P then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos hP]
    exact ⟨finite_of_iso (h₁ hP), finrank_eq_one_of_iso (h₁ hP)⟩
  · rw [if_neg hP]
    exact ⟨finite_of_isZero (h₀ hP), finrank_eq_zero_of_isZero (h₀ hP)⟩

end Finrank

/-! ### Cells -/

section Cells

variable (R : Type u) [CommRing R] {E : Type u} [TopologicalSpace E] [T2Space E]

/-- `H_n(χ(D), {χ(z₀)}) = 0`: a cell contracts onto any of its points. -/
lemma isZero_relHomology_cell_singleton {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ProperSpace V] {χ : V → E} (hχ : ContinuousOn χ (closedBall 0 1))
    (hinj : InjOn χ (closedBall 0 1)) {z₀ : V} (hz₀ : z₀ ∈ closedBall (0 : V) 1)
    (h : {χ z₀} ⊆ χ '' closedBall 0 1) (n : ℕ) :
    IsZero ((relHomology (ModuleCat.of R R) n).obj (subsetPair h)) :=
  isZero_relHomology_of_isStrongDeformationRetract _ h
    (isStrongDeformationRetract_singleton_image hχ hinj hz₀) n

section Zero

variable (χ : EuclideanSpace ℝ (Fin 0) → E)

omit [TopologicalSpace E] [T2Space E] in
lemma image_closedBall_fin_zero : χ '' closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1 = {χ 0} := by
  ext x
  constructor
  · rintro ⟨z, -, rfl⟩
    rw [Subsingleton.elim z 0]
    rfl
  · rintro rfl
    exact ⟨0, mem_closedBall_self zero_le_one, rfl⟩

omit [TopologicalSpace E] [T2Space E] in
lemma image_sphere_fin_zero : χ '' sphere (0 : EuclideanSpace ℝ (Fin 0)) 1 = ∅ := by
  rw [sphere_eq_empty_of_subsingleton one_ne_zero, image_empty]

/-- For `k = 0`, `(χ(D⁰), χ(S⁻¹)) = ({χ(0)}, ∅)`, so that `H_i(χ(D⁰), χ(S⁻¹)) ≅ H_i(pt)`. -/
def relHomologyCellPairZeroIso (i : ℕ) :
    (relHomology (ModuleCat.of R R) i).obj (cellPair χ) ≅
      ((singularChains (ModuleCat.of R R)).obj (TopCat.of ({χ 0} : Set E))).homology i := by
  let e₁ := (relHomology (ModuleCat.of R R) i).mapIso
    (subsetPairIsoOfEq (image_mono (f := χ) sphere_subset_closedBall) (empty_subset {χ 0})
      (image_sphere_fin_zero χ) (image_closedBall_fin_zero χ))
  let e₂ := asIso (homologyMap (relπ (ModuleCat.of R R) (subsetPair (empty_subset {χ 0}))) i)
  exact e₁ ≪≫ e₂.symm

end Zero

section Sphere

variable {n : ℕ} {χ : EuclideanSpace ℝ (Fin (n + 1)) → E}

omit [T2Space E] in
lemma continuousOn_comp_hemisphere {s : ℝ} (hs : s ^ 2 = 1) (hχ : ContinuousOn χ (sphere 0 1)) :
    ContinuousOn (χ ∘ hemisphere s) (closedBall 0 1) :=
  hχ.comp (continuous_hemisphere s).continuousOn (mapsTo_hemisphere hs)

omit [TopologicalSpace E] [T2Space E] in
lemma injOn_comp_hemisphere {s : ℝ} (hs : s ^ 2 = 1) (hinj : InjOn χ (sphere 0 1)) :
    InjOn (χ ∘ hemisphere s) (closedBall 0 1) :=
  hinj.comp (hemisphere_injective s).injOn (mapsTo_hemisphere hs)

/-- The south pole `-eₙ₊₁ = hemisphere (-1) 0` lies on the sphere. -/
lemma hemisphere_neg_one_zero_mem_sphere :
    hemisphere (-1) (0 : EuclideanSpace ℝ (Fin n)) ∈
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  hemisphere_mem_sphere (by norm_num) (mem_closedBall_self zero_le_one)

omit [TopologicalSpace E] [T2Space E] in
lemma singleton_subset_image_sphere :
    {χ (hemisphere (-1) 0)} ⊆ χ '' sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  singleton_subset_iff.2 (mem_image_of_mem χ hemisphere_neg_one_zero_mem_sphere)

/-- The pair `(χ(Sⁿ), {q})`, where `q = χ(-eₙ₊₁)` is the image of the south pole. -/
abbrev spherePointPair (χ : EuclideanSpace ℝ (Fin (n + 1)) → E) : TopPair.{u} :=
  subsetPair (singleton_subset_image_sphere (χ := χ))

omit [TopologicalSpace E] [T2Space E] in
lemma lowerHemisphere_subset :
    (χ ∘ hemisphere (-1)) '' closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ χ '' sphere 0 1 := by
  rw [image_comp]
  exact image_mono (mapsTo_hemisphere (by norm_num)).image_subset

omit [TopologicalSpace E] [T2Space E] in
lemma singleton_subset_lowerHemisphere :
    {χ (hemisphere (-1) 0)} ⊆
      (χ ∘ hemisphere (-1)) '' closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  singleton_subset_iff.2 ⟨0, mem_closedBall_self zero_le_one, rfl⟩

omit [TopologicalSpace E] [T2Space E] in
lemma image_sphere_eq_union :
    χ '' sphere 0 1 = (χ ∘ hemisphere (-1)) '' closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ∪
      (χ ∘ hemisphere 1) '' closedBall 0 1 := by
  rw [sphere_eq_union_hemisphere, image_union, image_comp, image_comp]

omit [TopologicalSpace E] [T2Space E] in
lemma upperHemisphere_mem_iff (hinj : InjOn χ (sphere 0 1)) :
    ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      (χ ∘ hemisphere 1) z ∈ (χ ∘ hemisphere (-1)) '' closedBall 0 1 ↔ ‖z‖ = 1 := by
  intro z hz
  rw [image_comp, Function.comp_apply, hinj.mem_image_iff
    (mapsTo_hemisphere (by norm_num)).image_subset (hemisphere_mem_sphere (by norm_num) hz),
    hemisphere_one_mem_iff hz]

/-- The lower hemisphere `χ(D₋)` is closed in `χ(Sⁿ)` (it is compact). -/
lemma isClosed_lowerHemisphere (hχ : ContinuousOn χ (sphere 0 1)) :
    IsClosed ((↑) ⁻¹' ((χ ∘ hemisphere (-1)) '' closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
      Set ↥(χ '' sphere 0 1)) :=
  ((isCompact_closedBall _ 1).image_of_continuousOn
    (continuousOn_comp_hemisphere (by norm_num) hχ)).isClosed.preimage continuous_subtype_val

/-- **The sphere lemma.** For `χ` continuous and injective on `Sⁿ`, with `q = χ(-eₙ₊₁)`,
`H_i(χ(Sⁿ), {q}) ≅ H_i(χ(D₊), χ(Sⁿ⁻¹))`, where `D₊` is the upper hemisphere, an `n`-cell
`χ ∘ hemisphere 1` attached along the equator to the lower hemisphere `χ(D₋)`:
`(χ(Sⁿ), {q}) ⟶ (χ(Sⁿ), χ(D₋))` is an isomorphism since `D₋` contracts onto `q`, and
`(χ(D₊), χ(Sⁿ⁻¹)) ⟶ (χ(Sⁿ), χ(D₋))` is one by excision for an attached cell. -/
def sphereRelIso (hχ : ContinuousOn χ (sphere 0 1)) (hinj : InjOn χ (sphere 0 1)) (i : ℕ) :
    (relHomology (ModuleCat.of R R) i).obj (spherePointPair χ) ≅
      (relHomology (ModuleCat.of R R) i).obj (cellPair (χ ∘ hemisphere 1)) := by
  have h₁ := isIso_relHomology_map_of_isStrongDeformationRetract_snd (ModuleCat.of R R)
    singleton_subset_lowerHemisphere lowerHemisphere_subset
    (isStrongDeformationRetract_singleton_image (continuousOn_comp_hemisphere (by norm_num) hχ)
      (injOn_comp_hemisphere (by norm_num) hinj) (mem_closedBall_self zero_le_one)) i
  have h₂ := isIso_relHomology_map_cellPair R lowerHemisphere_subset (isClosed_lowerHemisphere hχ)
    (continuousOn_comp_hemisphere (by norm_num) hχ) (injOn_comp_hemisphere (by norm_num) hinj)
    (upperHemisphere_mem_iff hinj) image_sphere_eq_union i
  exact asIso ((relHomology (ModuleCat.of R R) i).map
      (subsetPairHom (singleton_subset_lowerHemisphere.trans lowerHemisphere_subset)
        lowerHemisphere_subset singleton_subset_lowerHemisphere (subset_refl _))) ≪≫
    (asIso ((relHomology (ModuleCat.of R R) i).map
      (subsetPairHom (image_mono (f := χ ∘ hemisphere 1) sphere_subset_closedBall)
        lowerHemisphere_subset (image_sphere_subset (upperHemisphere_mem_iff hinj))
        (subset_union_right.trans image_sphere_eq_union.symm.subset)))).symm

/-- The triple `{q} ⊆ χ(Sⁿ) ⊆ χ(Dⁿ⁺¹)`, `q = χ(-eₙ₊₁)`. -/
abbrev cellTriple (χ : EuclideanSpace ℝ (Fin (n + 1)) → E) : TopTriple.{u} :=
  TopTriple.ofSubsets (singleton_subset_image_sphere (χ := χ))
    (image_mono (f := χ) sphere_subset_closedBall)

/-- In the triple `{q} ⊆ χ(Sⁿ) ⊆ χ(Dⁿ⁺¹)`, the boundary `H_{i+1}(χ(Dⁿ⁺¹), χ(Sⁿ)) ⟶ H_i(χ(Sⁿ), {q})`
is an isomorphism, the cell `χ(Dⁿ⁺¹)` contracting onto `q`. -/
lemma isIso_cellTriple_δ (hχ : ContinuousOn χ (closedBall 0 1)) (hinj : InjOn χ (closedBall 0 1))
    (i : ℕ) : IsIso ((cellTriple χ).δ (ModuleCat.of R R) i) :=
  ((cellTriple χ).shortComplex_shortExact (ModuleCat.of R R)).isIso_δ (i + 1) i rfl
    (isZero_relHomology_cell_singleton R hχ hinj
      (sphere_subset_closedBall hemisphere_neg_one_zero_mem_sphere) _ (i + 1))
    (isZero_relHomology_cell_singleton R hχ hinj
      (sphere_subset_closedBall hemisphere_neg_one_zero_mem_sphere) _ i)

end Sphere

/-- **The homology of a cell modulo its boundary in the top degree**: if `χ` is continuous and
injective on the closed unit ball `Dᵏ` of `ℝᵏ`, then `H_k(χ(Dᵏ), χ(Sᵏ⁻¹); R) ≅ R`.  By induction
on `k`: for `k = 0` the pair is `(pt, ∅)`; for `k + 1`, the boundary of the triple
`{q} ⊆ χ(Sᵏ) ⊆ χ(Dᵏ⁺¹)` and the sphere lemma give
`H_{k+1}(χ(Dᵏ⁺¹), χ(Sᵏ)) ≅ H_k(χ(Sᵏ), {q}) ≅ H_k(χ(D₊), χ(Sᵏ⁻¹))`, and `χ ∘ hemisphere 1` is a
`k`-cell. -/
def cellPairIso : (k : ℕ) → (χ : EuclideanSpace ℝ (Fin k) → E) →
    ContinuousOn χ (closedBall 0 1) → InjOn χ (closedBall 0 1) →
    ((relHomology (ModuleCat.of R R) k).obj (cellPair χ) ≅ ModuleCat.of R R)
  | 0, χ, _, _ => relHomologyCellPairZeroIso R χ 0 ≪≫ homologyZeroSingletonIso _ (χ 0)
  | k + 1, χ, hχ, hinj =>
    @asIso _ _ _ _ ((cellTriple χ).δ (ModuleCat.of R R) k) (isIso_cellTriple_δ R hχ hinj k) ≪≫
      sphereRelIso R (hχ.mono sphere_subset_closedBall) (hinj.mono sphere_subset_closedBall) k ≪≫
      cellPairIso k (χ ∘ hemisphere 1)
        (continuousOn_comp_hemisphere (by norm_num) (hχ.mono sphere_subset_closedBall))
        (injOn_comp_hemisphere (by norm_num) (hinj.mono sphere_subset_closedBall))

/-- **The homology of a cell modulo its boundary vanishes outside the top degree**: if `χ` is
continuous and injective on `Dᵏ`, then `H_i(χ(Dᵏ), χ(Sᵏ⁻¹); R) = 0` for `i ≠ k`. -/
theorem isZero_relHomology_cellPair : ∀ (k : ℕ) (χ : EuclideanSpace ℝ (Fin k) → E),
    ContinuousOn χ (closedBall 0 1) → InjOn χ (closedBall 0 1) → ∀ i, i ≠ k →
      IsZero ((relHomology (ModuleCat.of R R) i).obj (cellPair χ))
  | 0, χ, _, _, i, hi =>
    (isZero_homology_singleton (ModuleCat.of R R) (χ 0) hi).of_iso
      (relHomologyCellPairZeroIso R χ i)
  | k + 1, χ, hχ, hinj, 0, _ =>
    @IsZero.of_epi _ _ _ _ _ ((relHomology (ModuleCat.of R R) 0).map (cellTriple χ).map₂)
      ((cellTriple χ).epi_map₂_zero (ModuleCat.of R R))
      (isZero_relHomology_cell_singleton R hχ hinj
        (sphere_subset_closedBall hemisphere_neg_one_zero_mem_sphere) _ 0)
  | k + 1, χ, hχ, hinj, i + 1, hi =>
    (isZero_relHomology_cellPair k (χ ∘ hemisphere 1)
        (continuousOn_comp_hemisphere (by norm_num) (hχ.mono sphere_subset_closedBall))
        (injOn_comp_hemisphere (by norm_num) (hinj.mono sphere_subset_closedBall)) i
        (by omega)).of_iso
      (@asIso _ _ _ _ ((cellTriple χ).δ (ModuleCat.of R R) i) (isIso_cellTriple_δ R hχ hinj i) ≪≫
        sphereRelIso R (hχ.mono sphere_subset_closedBall) (hinj.mono sphere_subset_closedBall) i)

/-- **The dimension of the homology of a cell modulo its boundary**, over a field:
`dim H_i(χ(Dᵏ), χ(Sᵏ⁻¹); 𝕜)` is `1` for `i = k` and `0` otherwise. -/
theorem finrank_relHomology_cellPair (𝕜 : Type u) [Field 𝕜] {k : ℕ}
    {χ : EuclideanSpace ℝ (Fin k) → E} (hχ : ContinuousOn χ (closedBall 0 1))
    (hinj : InjOn χ (closedBall 0 1)) (i : ℕ) :
    finrank 𝕜 ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj (cellPair χ)) = if i = k then 1 else 0 := by
  split_ifs with h
  · subst h
    exact finrank_eq_one_of_iso (cellPairIso 𝕜 i χ hχ hinj)
  · exact finrank_eq_zero_of_isZero (isZero_relHomology_cellPair 𝕜 k χ hχ hinj i h)

/-! ### Embedded spheres -/

section ImageSphere

variable {n : ℕ} {χ : EuclideanSpace ℝ (Fin (n + 1)) → E} (hχ : ContinuousOn χ (sphere 0 1))
  (hinj : InjOn χ (sphere 0 1))

include hχ hinj

/-- `H_n(χ(Sⁿ), {q}; R) ≅ R` for an embedded sphere `χ(Sⁿ)` and `q = χ(-eₙ₊₁)`. -/
def spherePointPairIso :
    (relHomology (ModuleCat.of R R) n).obj (spherePointPair χ) ≅ ModuleCat.of R R :=
  sphereRelIso R hχ hinj n ≪≫ cellPairIso R n (χ ∘ hemisphere 1)
    (continuousOn_comp_hemisphere (by norm_num) hχ) (injOn_comp_hemisphere (by norm_num) hinj)

/-- `H_i(χ(Sⁿ), {q}; R) = 0` for `i ≠ n`. -/
theorem isZero_relHomology_spherePointPair {i : ℕ} (hi : i ≠ n) :
    IsZero ((relHomology (ModuleCat.of R R) i).obj (spherePointPair χ)) :=
  (isZero_relHomology_cellPair R n (χ ∘ hemisphere 1)
    (continuousOn_comp_hemisphere (by norm_num) hχ) (injOn_comp_hemisphere (by norm_num) hinj) i
    hi).of_iso (sphereRelIso R hχ hinj i)

/-- `H_0(χ(Sⁿ); R) ≅ R` for `n ≠ 0` (an embedded sphere of positive dimension is connected). -/
def homologyImageSphereZeroIso (hn : n ≠ 0) :
    ((singularChains (ModuleCat.of R R)).obj (TopCat.of ↥(χ '' sphere 0 1))).homology 0 ≅
      ModuleCat.of R R :=
  homologyIsoBiprodSingleton (ModuleCat.of R R) singleton_subset_image_sphere 0 ≪≫
    (isoBiprodZero (isZero_relHomology_spherePointPair R hχ hinj (Ne.symm hn))).symm ≪≫
    homologyZeroSingletonIso _ _

/-- `H_n(χ(Sⁿ); R) ≅ R` for `n ≠ 0`. -/
def homologyImageSphereTopIso (hn : n ≠ 0) :
    ((singularChains (ModuleCat.of R R)).obj (TopCat.of ↥(χ '' sphere 0 1))).homology n ≅
      ModuleCat.of R R :=
  homologyIsoBiprodSingleton (ModuleCat.of R R) singleton_subset_image_sphere n ≪≫
    (isoZeroBiprod (isZero_homology_singleton _ _ hn)).symm ≪≫ spherePointPairIso R hχ hinj

/-- `H_i(χ(Sⁿ); R) = 0` for `i ≠ 0, n`. -/
theorem isZero_homology_imageSphere {i : ℕ} (h0 : i ≠ 0) (hn : i ≠ n) :
    IsZero (((singularChains (ModuleCat.of R R)).obj (TopCat.of ↥(χ '' sphere 0 1))).homology i) :=
  ((biprod_isZero_iff _ _).2 ⟨isZero_homology_singleton _ _ h0,
    isZero_relHomology_spherePointPair R hχ hinj hn⟩).of_iso
      (homologyIsoBiprodSingleton _ singleton_subset_image_sphere i)

/-- **The Betti numbers of an embedded sphere**: over a field `𝕜`,
`dim H_i(χ(Sⁿ); 𝕜) = [i = 0] + [i = n]` (so `2` for `i = n = 0`). -/
theorem finrank_homology_imageSphere (𝕜 : Type u) [Field 𝕜] (i : ℕ) :
    finrank 𝕜 (((singularChains (ModuleCat.of 𝕜 𝕜)).obj
      (TopCat.of ↥(χ '' sphere 0 1))).homology i) =
      (if i = 0 then 1 else 0) + (if i = n then 1 else 0) := by
  obtain ⟨h₁, h₁'⟩ := finite_and_finrank_eq_ite (𝕜 := 𝕜) (P := i = 0)
    (M := ((singularChains (ModuleCat.of 𝕜 𝕜)).obj
      (TopCat.of ({χ (hemisphere (-1) 0)} : Set E))).homology i)
    (fun h ↦ by subst h; exact homologyZeroSingletonIso _ _)
    (fun h ↦ isZero_homology_singleton _ _ h)
  obtain ⟨h₂, h₂'⟩ := finite_and_finrank_eq_ite (𝕜 := 𝕜) (P := i = n)
    (M := (relHomology (ModuleCat.of 𝕜 𝕜) i).obj (spherePointPair χ))
    (fun h ↦ by subst h; exact spherePointPairIso 𝕜 hχ hinj)
    (fun h ↦ isZero_relHomology_spherePointPair 𝕜 hχ hinj h)
  rw [(homologyIsoBiprodSingleton (ModuleCat.of 𝕜 𝕜) singleton_subset_image_sphere
    i).toLinearEquiv.finrank_eq, finrank_biprod, h₁', h₂']

end ImageSphere

/-- `H_0(χ(S⁰); R) ≅ R ⊞ R`: an embedded `0`-sphere is two points. -/
def homologyImageSphereZeroIsoBiprod {χ : EuclideanSpace ℝ (Fin 1) → E}
    (hχ : ContinuousOn χ (sphere 0 1)) (hinj : InjOn χ (sphere 0 1)) :
    ((singularChains (ModuleCat.of R R)).obj (TopCat.of ↥(χ '' sphere 0 1))).homology 0 ≅
      ModuleCat.of R R ⊞ ModuleCat.of R R :=
  homologyIsoBiprodSingleton (ModuleCat.of R R) singleton_subset_image_sphere 0 ≪≫
    biprod.mapIso (homologyZeroSingletonIso _ _) (spherePointPairIso R hχ hinj)

end Cells

/-! ### The disk and the sphere of `ℝⁿ` -/

section Euclidean

variable (R : Type) [CommRing R]

/-- The pair `(Dⁿ, Sⁿ⁻¹)` of the closed unit ball and the unit sphere of `ℝⁿ`
(`EuclideanSpace ℝ (Fin n)`); `S⁻¹ = ∅`. -/
abbrev diskPair (n : ℕ) : TopPair.{0} :=
  subsetPair (sphere_subset_closedBall : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ closedBall 0 1)

/-- `(Dⁿ, Sⁿ⁻¹)` is the cell pair of the identity. -/
def diskPairIsoCellPair (n : ℕ) : diskPair n ≅ cellPair (id : EuclideanSpace ℝ (Fin n) → _) :=
  subsetPairIsoOfEq _ _ (image_id _).symm (image_id _).symm

/-- **`H_n(Dⁿ, Sⁿ⁻¹; R) ≅ R`.** -/
def relHomologyDiskPairIso (n : ℕ) :
    (relHomology (ModuleCat.of R R) n).obj (diskPair n) ≅ ModuleCat.of R R :=
  (relHomology (ModuleCat.of R R) n).mapIso (diskPairIsoCellPair n) ≪≫
    cellPairIso R n id continuousOn_id (injOn_id _)

/-- **`H_i(Dⁿ, Sⁿ⁻¹; R) = 0` for `i ≠ n`.** -/
theorem isZero_relHomology_diskPair {n i : ℕ} (h : i ≠ n) :
    IsZero ((relHomology (ModuleCat.of R R) i).obj (diskPair n)) :=
  (isZero_relHomology_cellPair R n id continuousOn_id (injOn_id _) i h).of_iso
    ((relHomology (ModuleCat.of R R) i).mapIso (diskPairIsoCellPair n))

/-- **`dim H_i(Dⁿ, Sⁿ⁻¹; 𝕜) = [i = n]`** over a field `𝕜`. -/
theorem finrank_relHomology_diskPair (𝕜 : Type) [Field 𝕜] (n i : ℕ) :
    finrank 𝕜 ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj (diskPair n)) = if i = n then 1 else 0 := by
  rw [((relHomology (ModuleCat.of 𝕜 𝕜) i).mapIso (diskPairIsoCellPair n)).toLinearEquiv.finrank_eq]
  exact finrank_relHomology_cellPair 𝕜 (k := n) continuousOn_id (injOn_id _) i

variable {n : ℕ}

/-- The singular homology `H_i(Sⁿ; R)` of the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`. -/
abbrev sphereHomology (n i : ℕ) : ModuleCat.{0} R :=
  ((singularChains (ModuleCat.of R R)).obj
    (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))).homology i

/-- **`H_0(Sⁿ; R) ≅ R` for `n ≥ 1`.** -/
def sphereHomologyZeroIso (hn : n ≠ 0) : sphereHomology R n 0 ≅ ModuleCat.of R R :=
  homologyIsoOfEq _ (image_id _).symm 0 ≪≫
    homologyImageSphereZeroIso R continuousOn_id (injOn_id _) hn

/-- **`H_n(Sⁿ; R) ≅ R` for `n ≥ 1`.** -/
def sphereHomologyTopIso (hn : n ≠ 0) : sphereHomology R n n ≅ ModuleCat.of R R :=
  homologyIsoOfEq _ (image_id _).symm n ≪≫
    homologyImageSphereTopIso R continuousOn_id (injOn_id _) hn

/-- **`H_0(S⁰; R) ≅ R ⊞ R`.** -/
def sphereHomologyZeroIsoBiprod : sphereHomology R 0 0 ≅ ModuleCat.of R R ⊞ ModuleCat.of R R :=
  homologyIsoOfEq _ (image_id _).symm 0 ≪≫
    homologyImageSphereZeroIsoBiprod R continuousOn_id (injOn_id _)

/-- **`H_i(Sⁿ; R) = 0` for `i ≠ 0, n`.** -/
theorem isZero_sphereHomology {i : ℕ} (h0 : i ≠ 0) (hn : i ≠ n) :
    IsZero (sphereHomology R n i) :=
  (isZero_homology_imageSphere R continuousOn_id (injOn_id _) h0 hn).of_iso
    (homologyIsoOfEq _ (image_id _).symm i)

/-- **The Betti numbers of `Sⁿ`**: `dim H_i(Sⁿ; 𝕜) = [i = 0] + [i = n]`. -/
theorem finrank_sphereHomology (𝕜 : Type) [Field 𝕜] (n i : ℕ) :
    finrank 𝕜 (sphereHomology 𝕜 n i) = (if i = 0 then 1 else 0) + (if i = n then 1 else 0) := by
  rw [(homologyIsoOfEq (ModuleCat.of 𝕜 𝕜) (image_id _).symm i).toLinearEquiv.finrank_eq]
  exact finrank_homology_imageSphere (n := n) continuousOn_id (injOn_id _) 𝕜 i

end Euclidean

/-! ### Mathlib's disk `𝔻ⁿ`, in any universe -/

section TopDisk

/-- The inclusion `∂𝔻ⁿ ⟶ 𝔻ⁿ` of Mathlib's disk boundary is an embedding. -/
lemma isEmbedding_diskBoundaryInclusion (n : ℕ) :
    Topology.IsEmbedding (TopCat.diskBoundaryInclusion.{u} n) := by
  have h : ⇑(TopCat.diskBoundaryInclusion.{u} n) =
      ULift.up ∘ Set.inclusion sphere_subset_closedBall ∘ ULift.down := by
    funext x
    rfl
  rw [h]
  exact Homeomorph.ulift.symm.isEmbedding.comp
    ((Topology.IsEmbedding.inclusion _).comp Homeomorph.ulift.isEmbedding)

/-- The pair `(𝔻ⁿ, ∂𝔻ⁿ)` of Mathlib's `n`-disk and its boundary (`TopCat.disk`,
`TopCat.diskBoundary`: the closed unit ball and the unit sphere of `ℝⁿ`, lifted to the universe
`u`), as in Mathlib's CW complexes and in `Morse/Chapter2/Attaching.lean`. -/
abbrev topDiskPair (n : ℕ) : TopPair.{u} :=
  TopPair.of (TopCat.diskBoundaryInclusion.{u} n) (isEmbedding_diskBoundaryInclusion n)

/-- A continuous bijection from a compact space to a Hausdorff space, as a homotopy
equivalence. -/
def homotopyEquivOfBijective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] (f : C(X, Y)) (hf : Bijective f) :
    ContinuousMap.HomotopyEquiv X Y :=
  (f.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hf)).toHomotopyEquiv

@[simp]
lemma coe_homotopyEquivOfBijective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] (f : C(X, Y)) (hf : Bijective f) :
    ⇑(homotopyEquivOfBijective f hf) = f := rfl

variable {E : Type u} [TopologicalSpace E] {k : ℕ} {χ : EuclideanSpace ℝ (Fin k) → E}

/-- `χ` restricted to the closed unit ball, as a map `𝔻ᵏ → χ(Dᵏ)`. -/
def diskToCellFst (hχ : ContinuousOn χ (closedBall 0 1)) :
    C(ULift.{u} (closedBall (0 : EuclideanSpace ℝ (Fin k)) 1), ↥(χ '' closedBall 0 1)) :=
  ⟨fun x ↦ ⟨χ x.down.1, mem_image_of_mem χ x.down.2⟩,
    (hχ.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
      fun x ↦ x.down.2).subtype_mk _⟩

/-- `χ` restricted to the unit sphere, as a map `∂𝔻ᵏ → χ(Sᵏ⁻¹)`. -/
def diskToCellSnd (hχ : ContinuousOn χ (closedBall 0 1)) :
    C(ULift.{u} (sphere (0 : EuclideanSpace ℝ (Fin k)) 1), ↥(χ '' sphere 0 1)) :=
  ⟨fun x ↦ ⟨χ x.down.1, mem_image_of_mem χ x.down.2⟩,
    ((hχ.mono sphere_subset_closedBall).comp_continuous
      (continuous_subtype_val.comp continuous_uliftDown) fun x ↦ x.down.2).subtype_mk _⟩

/-- The map of pairs `(𝔻ᵏ, ∂𝔻ᵏ) ⟶ (χ(Dᵏ), χ(Sᵏ⁻¹))` induced by `χ`. -/
def diskToCell (hχ : ContinuousOn χ (closedBall 0 1)) : topDiskPair.{u} k ⟶ cellPair χ :=
  TopPair.ofHom (X := topDiskPair.{u} k) (Y := cellPair χ) (TopCat.ofHom (diskToCellFst hχ))
    (TopCat.ofHom (diskToCellSnd hχ)) rfl

variable [T2Space E]

/-- If `χ` is continuous and injective on `Dᵏ`, then `(𝔻ᵏ, ∂𝔻ᵏ) ⟶ (χ(Dᵏ), χ(Sᵏ⁻¹))` is a
homeomorphism of pairs, hence induces isomorphisms in relative homology. -/
theorem isIso_relHomology_map_diskToCell {C : Type v} [Category.{w} C] [Abelian C]
    [HasCoproducts.{u} C] (R : C) (hχ : ContinuousOn χ (closedBall 0 1))
    (hinj : InjOn χ (closedBall 0 1)) (i : ℕ) :
    IsIso ((relHomology R i).map (diskToCell hχ)) := by
  have hbij₁ : Bijective (diskToCellSnd hχ) := by
    refine ⟨fun x y h ↦ ?_, fun y ↦ ?_⟩
    · have := hinj (sphere_subset_closedBall x.down.2) (sphere_subset_closedBall y.down.2)
        (congrArg Subtype.val h)
      exact ULift.ext _ _ (Subtype.ext this)
    · obtain ⟨z, hz, hzy⟩ := y.2
      exact ⟨ULift.up ⟨z, hz⟩, Subtype.ext hzy⟩
  have hbij₂ : Bijective (diskToCellFst hχ) := by
    refine ⟨fun x y h ↦ ?_, fun y ↦ ?_⟩
    · exact ULift.ext _ _ (Subtype.ext (hinj x.down.2 y.down.2 (congrArg Subtype.val h)))
    · obtain ⟨z, hz, hzy⟩ := y.2
      exact ⟨ULift.up ⟨z, hz⟩, Subtype.ext hzy⟩
  let e₁ := homotopyEquivOfBijective (diskToCellSnd hχ) hbij₁
  let e₂ := homotopyEquivOfBijective (diskToCellFst hχ) hbij₂
  exact isIso_relHomology_map_of_homotopyEquiv R (diskToCell hχ) e₁ rfl e₂ rfl i

end TopDisk

section TopDiskHomology

variable (R : Type u) [CommRing R]

/-- **`H_n(𝔻ⁿ, ∂𝔻ⁿ; R) ≅ R`**, in any universe. -/
def relHomologyTopDiskPairIso (n : ℕ) :
    (relHomology (ModuleCat.of R R) n).obj (topDiskPair.{u} n) ≅ ModuleCat.of R R :=
  have := isIso_relHomology_map_diskToCell (ModuleCat.of R R)
    (E := ULift.{u} (EuclideanSpace ℝ (Fin n))) (χ := ULift.up) continuous_uliftUp.continuousOn
    ULift.up_injective.injOn n
  asIso ((relHomology (ModuleCat.of R R) n).map (diskToCell continuous_uliftUp.continuousOn)) ≪≫
    cellPairIso R n ULift.up continuous_uliftUp.continuousOn ULift.up_injective.injOn

/-- **`H_i(𝔻ⁿ, ∂𝔻ⁿ; R) = 0` for `i ≠ n`**, in any universe. -/
theorem isZero_relHomology_topDiskPair {n i : ℕ} (h : i ≠ n) :
    IsZero ((relHomology (ModuleCat.of R R) i).obj (topDiskPair.{u} n)) :=
  have := isIso_relHomology_map_diskToCell (ModuleCat.of R R)
    (E := ULift.{u} (EuclideanSpace ℝ (Fin n))) (χ := ULift.up) continuous_uliftUp.continuousOn
    ULift.up_injective.injOn i
  (isZero_relHomology_cellPair R n ULift.up continuous_uliftUp.continuousOn
    ULift.up_injective.injOn i h).of_iso
    (asIso ((relHomology (ModuleCat.of R R) i).map (diskToCell continuous_uliftUp.continuousOn)))

/-- **`dim H_i(𝔻ⁿ, ∂𝔻ⁿ; 𝕜) = [i = n]`** over a field `𝕜`, in any universe. -/
theorem finrank_relHomology_topDiskPair (𝕜 : Type u) [Field 𝕜] (n i : ℕ) :
    finrank 𝕜 ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj (topDiskPair.{u} n)) =
      if i = n then 1 else 0 := by
  split_ifs with h
  · subst h
    exact finrank_eq_one_of_iso (relHomologyTopDiskPairIso 𝕜 i)
  · exact finrank_eq_zero_of_isZero (isZero_relHomology_topDiskPair 𝕜 h)

end TopDiskHomology

end Morse.Homology
