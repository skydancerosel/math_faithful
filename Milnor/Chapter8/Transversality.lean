import Milnor.Chapter8.LocalSlice
import Milnor.Chapter7.TubeData
import Milnor.Chapter2.Brown

/-!
# Transversality (Milnor §8, Problem 16)

Two submanifolds `N, N'` of `M` meet *transversally* if at every common point `x` the tangent
spaces `TNₓ` and `TN'ₓ` span `TMₓ`; by a dimension count this forces `N ∩ N' = ∅` when
`n + n' < m`. The problem asks to show that a framed submanifold `N` can be moved by a small
deformation so as to meet a given `N'` transversally, and that a transversal intersection is a
smooth manifold.

As in Chapter 7, `M ⊆ ℝᴷ⁺¹` is a slice submanifold modelled on `ℝᵐ`, `N, N' ⊆ M` are slice
submanifolds of `M` modelled on `ℝⁿ`, `ℝⁿ'` (with normal models `ℝᵖ`, `ℝᵖ'`), and tangent spaces
are subspaces of `ℝᴷ⁺¹` (`tangentM`, `tangentN`).

## Main results

* `Transverse hM hN hN'`: `TNₓ ⊔ TN'ₓ = TMₓ` for all `x ∈ N ∩ N'`;
* `inter_eq_empty_of_transverse`: Milnor's parenthetical remark;
* `isSliceSubmanifold_inter`, `tangentN_inter`: a transversal intersection is a slice
  submanifold of `M` of codimension `p + p'`, with `T(N ∩ N')ₓ = TNₓ ∩ TN'ₓ`;
* `exists_transverse_deformation`: given the product neighbourhood `G : N × ℝᵖ → M` of a framed
  submanifold (`TubeData`), for arbitrarily small `u` the submanifold `G(N × {u})` meets `N'`
  transversally; `x ↦ G(x, u)` is injective and `δ`-close to the inclusion.

## Proofs

* Intersection. Near `x ∈ N ∩ N'` take slice charts `σ` of `N` and `σ'` of `N'`; the pair of
  normal coordinates `z ↦ ((σ z).2, (σ' z).2) ∈ ℝᵖ × ℝᵖ' ≅ ℝᵖ⁺ᵖ'` has zero set `N ∩ N'`. Its
  derivative is `(D, D')`, where `D`, `D'` are surjective with kernels the chart-level tangent
  spaces of `N`, `N'` (`LocalSlice`). Transversality says `ker D ⊔ ker D' = ℝᵐ`, which makes
  `(D, D')` surjective, with kernel `ker D ⊓ ker D'`. Then `LocalSlice` applies to `N ∩ N'`.
  Chart-level and ambient tangent spaces correspond under the injective map `d(val_M)`.
* Deformation. The fibre coordinate `π = pr₂ ∘ G⁻¹ : V → ℝᵖ` is a submersion on the image `V` of
  the tube, and `G(N × {u}) = π⁻¹(u)` for `‖u‖ < ε`; so `G(N × {u})` is a slice submanifold with
  tangent space `ker dπ`. Transversality at `z ∈ G(N × {u}) ∩ N'` follows from
  `dπ_z (TN'_z) = ℝᵖ`, i.e. from `z` being a regular point of `π` restricted to the open subset
  `N' ∩ V` of `N'`. By Brown's theorem such regular values `u` are dense. Closeness to the
  inclusion follows from `G(x, 0) = x` and compactness of `N`.

The auxiliary lemmas live in `Milnor.Problems.Transversality`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Problems

open Framed

namespace Transversality

/-! ### Linear algebra -/

section linalg

variable {V P P' Q : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup P] [Module ℝ P]
  [AddCommGroup P'] [Module ℝ P'] [AddCommGroup Q] [Module ℝ Q]

/-- If `A ∘ B` is surjective then `ker A ⊔ range B = ⊤`. -/
theorem ker_sup_range_eq_top_of_surjective_comp {A : V →ₗ[ℝ] P} {B : Q →ₗ[ℝ] V}
    (h : Surjective (A.comp B)) : LinearMap.ker A ⊔ LinearMap.range B = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨q, hq⟩ := h (A v)
  have hv : v = (v - B q) + B q := by abel
  rw [hv]
  refine Submodule.add_mem_sup ?_ ⟨q, rfl⟩
  rw [LinearMap.mem_ker, map_sub]
  rw [LinearMap.comp_apply] at hq
  rw [hq, sub_self]

/-- If `A, B` are surjective with `ker A ⊔ ker B = ⊤`, then `(A, B)` is surjective. -/
theorem surjective_prod_of_ker_sup {A : V →ₗ[ℝ] P} {B : V →ₗ[ℝ] P'} (hA : Surjective A)
    (hB : Surjective B) (h : LinearMap.ker A ⊔ LinearMap.ker B = ⊤) :
    Surjective (A.prod B) := by
  rintro ⟨a, b⟩
  obtain ⟨u, rfl⟩ := hA a
  obtain ⟨v, rfl⟩ := hB b
  have huv : u - v ∈ LinearMap.ker A ⊔ LinearMap.ker B := by rw [h]; exact Submodule.mem_top
  obtain ⟨k, hk, k', hk', hkk⟩ := Submodule.mem_sup.1 huv
  have h1 : u - k = v + k' := by
    rw [eq_sub_iff_add_eq] at hkk
    rw [← hkk]
    abel
  refine ⟨u - k, Prod.ext ?_ ?_⟩
  · show A (u - k) = A u
    rw [map_sub, LinearMap.mem_ker.1 hk, sub_zero]
  · show B (u - k) = B v
    rw [h1, map_add, LinearMap.mem_ker.1 hk', add_zero]

end linalg

section prodMk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {V V' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V']

/-- The derivative of a pair of maps into normed spaces. -/
theorem hasMFDerivAt_prodMk_space {f : X → V} {g : X → V'} {x : X} {f' : E →L[ℝ] V}
    {g' : E →L[ℝ] V'} (hf : HasMFDerivAt I 𝓘(ℝ, V) f x f') (hg : HasMFDerivAt I 𝓘(ℝ, V') g x g') :
    HasMFDerivAt I 𝓘(ℝ, V × V') (fun y => (f y, g y)) x (f'.prod g') :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

end prodMk

/-! ### Normal coordinates of slice charts and local defining functions of intersections -/

section chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  {Z W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [I.Boundaryless] [IsManifold I ∞ X] in
/-- The derivative of the normal coordinate `z ↦ (σ.φ z).2` of a slice chart. -/
theorem hasMFDerivAt_sliceSnd {S : Set X} (σ : SliceChart I Z W S) {y : X}
    (hy : y ∈ σ.φ.source) :
    HasMFDerivAt I 𝓘(ℝ, W) (fun z => (σ.φ z).2) y
      ((ContinuousLinearMap.snd ℝ Z W).comp (mfd I 𝓘(ℝ, Z × W) σ.φ y) :) := by
  have hφ : MDifferentiableAt I 𝓘(ℝ, Z × W) σ.φ y := σ.φ.mdifferentiableAt (by simp) hy
  exact (hasFDerivAt_snd (p := σ.φ y)).hasMFDerivAt.comp y (hasMFDerivAt_mfd hφ)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]
  [IsManifold I ∞ X] in
/-- The normal coordinate of a slice chart is a submersion. -/
theorem surjective_sliceSnd {S : Set X} (σ : SliceChart I Z W S) {y : X}
    (hy : y ∈ σ.φ.source) :
    Surjective ((ContinuousLinearMap.snd ℝ Z W).comp (mfd I 𝓘(ℝ, Z × W) σ.φ y)) := by
  let e : E ≃L[ℝ] Z × W :=
    (PartialDiffeomorph.isLocalDiffeomorphAt I 𝓘(ℝ, Z × W) ∞ σ.φ hy).mfderivToContinuousLinearEquiv
      (by simp)
  intro b
  refine ⟨e.symm (0, b), ?_⟩
  have h : mfd I 𝓘(ℝ, Z × W) σ.φ y (e.symm (0, b)) = (0, b) := e.apply_symm_apply (0, b)
  show (mfd I 𝓘(ℝ, Z × W) σ.φ y (e.symm (0, b))).2 = b
  rw [h]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W]
  [IsManifold I ∞ X] in
/-- The normal coordinate of a slice chart is smooth on the chart domain. -/
theorem contMDiffOn_sliceSnd {S : Set X} (σ : SliceChart I Z W S) :
    ContMDiffOn I 𝓘(ℝ, W) ∞ (fun z => (σ.φ z).2) σ.φ.source :=
  contDiff_snd.contMDiff.comp_contMDiffOn σ.φ.contMDiffOn

/-- The kernel of the derivative of the normal coordinate of a slice chart of `S` is the
chart-level tangent space of `S`. -/
theorem ker_sliceSnd_eq_range {S : Set X} (hS : IsSliceSubmanifold I Z W S)
    (hZ : finrank ℝ Z + finrank ℝ W = finrank ℝ E) (σ : SliceChart I Z W S) {y : X}
    (hy : y ∈ σ.φ.source) (hyS : y ∈ S) :
    letI := hS.chartedSpace;
    LinearMap.ker (((ContinuousLinearMap.snd ℝ Z W).comp (mfd I 𝓘(ℝ, Z × W) σ.φ y) : E →L[ℝ] W) :
      E →ₗ[ℝ] W) =
      LinearMap.range ((mfd 𝓘(ℝ, Z) I (Subtype.val : S → X) ⟨y, hyS⟩ : Z →L[ℝ] E) : Z →ₗ[ℝ] E) := by
  letI := hS.chartedSpace
  have hD := hasMFDerivAt_sliceSnd σ hy
  have h := hS.range_mfderiv_val_eq_ker (F := W) hZ ⟨y, hyS⟩ σ.φ.open_source hy
    (contMDiffOn_sliceSnd σ) (fun z hz hzS => (σ.slice z hz).1 hzS)
    (by rw [hD.mfderiv]; exact surjective_sliceSnd σ hy)
  rw [h, HasMFDerivAt.mfd_eq hD]

/-- **Local defining functions for an intersection.** If `S, S'` are slice submanifolds whose
chart-level tangent spaces span `E` at the points of `S ∩ S'`, then near `x ∈ S ∩ S'` the pair of
normal coordinates of slice charts of `S` and `S'` (identified with `P` by `e`) is a submersion
with zero set `S ∩ S'`, whose kernel is the intersection of the chart-level tangent spaces. -/
theorem exists_local_inter {Z' W' P : Type*} [NormedAddCommGroup Z'] [NormedSpace ℝ Z']
    [FiniteDimensional ℝ Z'] [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {S S' : Set X} (hS : IsSliceSubmanifold I Z W S) (hS' : IsSliceSubmanifold I Z' W' S')
    (hZ : finrank ℝ Z + finrank ℝ W = finrank ℝ E)
    (hZ' : finrank ℝ Z' + finrank ℝ W' = finrank ℝ E) (e : (W × W') ≃L[ℝ] P)
    (htr : letI := hS.chartedSpace; letI := hS'.chartedSpace;
      ∀ (y : X) (hy : y ∈ S) (hy' : y ∈ S'),
        LinearMap.range ((mfd 𝓘(ℝ, Z) I (Subtype.val : S → X) ⟨y, hy⟩ : Z →L[ℝ] E) :
          Z →ₗ[ℝ] E) ⊔
        LinearMap.range ((mfd 𝓘(ℝ, Z') I (Subtype.val : S' → X) ⟨y, hy'⟩ : Z' →L[ℝ] E) :
          Z' →ₗ[ℝ] E) = ⊤)
    {x : X} (hx : x ∈ S ∩ S') :
    letI := hS.chartedSpace; letI := hS'.chartedSpace;
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ g : X → P, ContMDiffOn I 𝓘(ℝ, P) ∞ g U ∧
      (∀ y ∈ U, y ∈ S ∩ S' ↔ g y = 0) ∧
      ∀ y ∈ U, ∀ hy : y ∈ S ∩ S', Surjective (mfderiv I 𝓘(ℝ, P) g y) ∧
        LinearMap.ker ((mfd I 𝓘(ℝ, P) g y : E →L[ℝ] P) : E →ₗ[ℝ] P) =
          LinearMap.range ((mfd 𝓘(ℝ, Z) I (Subtype.val : S → X) ⟨y, hy.1⟩ : Z →L[ℝ] E) :
            Z →ₗ[ℝ] E) ⊓
          LinearMap.range ((mfd 𝓘(ℝ, Z') I (Subtype.val : S' → X) ⟨y, hy.2⟩ : Z' →L[ℝ] E) :
            Z' →ₗ[ℝ] E) := by
  letI := hS.chartedSpace
  letI := hS'.chartedSpace
  obtain ⟨σ, hσ⟩ := hS x hx.1
  obtain ⟨σ', hσ'⟩ := hS' x hx.2
  refine ⟨σ.φ.source ∩ σ'.φ.source, σ.φ.open_source.inter σ'.φ.open_source, ⟨hσ, hσ'⟩,
    fun z => e ((σ.φ z).2, (σ'.φ z).2), ?_, ?_, ?_⟩
  · have h1 := (contMDiffOn_sliceSnd σ).mono (inter_subset_left (t := σ'.φ.source))
    have h2 := (contMDiffOn_sliceSnd σ').mono (inter_subset_right (s := σ.φ.source))
    exact e.contDiff.contMDiff.comp_contMDiffOn (h1.prodMk_space h2)
  · intro y hy
    rw [mem_inter_iff, σ.slice y hy.1, σ'.slice y hy.2, e.map_eq_zero_iff, Prod.mk_eq_zero]
  · intro y hy hyS
    obtain ⟨hyσ, hyσ'⟩ := hy
    obtain ⟨D, hDdef⟩ : ∃ D : E →L[ℝ] W,
        (ContinuousLinearMap.snd ℝ Z W).comp (mfd I 𝓘(ℝ, Z × W) σ.φ y) = D := ⟨_, rfl⟩
    obtain ⟨D', hD'def⟩ : ∃ D' : E →L[ℝ] W',
        (ContinuousLinearMap.snd ℝ Z' W').comp (mfd I 𝓘(ℝ, Z' × W') σ'.φ y) = D' := ⟨_, rfl⟩
    have hD := hasMFDerivAt_sliceSnd σ hyσ
    have hD' := hasMFDerivAt_sliceSnd σ' hyσ'
    have hk := ker_sliceSnd_eq_range hS hZ σ hyσ hyS.1
    have hk' := ker_sliceSnd_eq_range hS' hZ' σ' hyσ' hyS.2
    have hs := surjective_sliceSnd σ hyσ
    have hs' := surjective_sliceSnd σ' hyσ'
    rw [hDdef] at hD hk hs
    rw [hD'def] at hD' hk' hs'
    have hg : HasMFDerivAt I 𝓘(ℝ, P) (fun z => e ((σ.φ z).2, (σ'.φ z).2)) y
        (((e : W × W' →L[ℝ] P).comp (D.prod D') : E →L[ℝ] P) :) :=
      e.hasFDerivAt.hasMFDerivAt.comp y (hasMFDerivAt_prodMk_space hD hD')
    have htr' := htr y hyS.1 hyS.2
    rw [← hk, ← hk'] at htr'
    have hsurj := surjective_prod_of_ker_sup hs hs' htr'
    refine ⟨?_, ?_⟩
    · rw [hg.mfderiv]
      exact e.surjective.comp hsurj
    · rw [HasMFDerivAt.mfd_eq hg, ← hk, ← hk']
      ext v
      show e (D v, D' v) = 0 ↔ D v = 0 ∧ D' v = 0
      rw [e.map_eq_zero_iff, Prod.mk_eq_zero]

end chart

/-- `ℝᵖ × ℝᵖ' ≅ ℝᵖ⁺ᵖ'`. -/
def prodEquivEuclidean (p p' : ℕ) :
    (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p')) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + p')) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

end Transversality

open Transversality

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M)

namespace Transversality

/-! ### Ambient tangent spaces versus chart coordinates -/

/-- `TMₓ` is the image of `⊤` under `d(val_M)`. -/
theorem tangentM_eq_map_top (x : M) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    tangentM hM x = Submodule.map ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
        EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1))) ⊤ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rw [Submodule.map_top]
  rfl

/-- `TNₓ` is the image of the chart-level tangent space `range d(val_N)` under `d(val_M)`. -/
theorem tangentN_eq_map {n p : ℕ} {N : Set M}
    (hN : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin p)) N) (x : N) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := hN.chartedSpace;
    tangentN hM hN x = Submodule.map ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x.1 :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
        EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1)))
      (LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (Subtype.val : N → M) x : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := hN.chartedSpace
  haveI := hN.isManifold
  have h1 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))) (hM.contMDiff_val.mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x.1)
  have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (hN.contMDiff_val.mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (Subtype.val : N → M) x)
  have h3 : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (fun q : N => (q.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) x =
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x.1).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (Subtype.val : N → M) x) := HasMFDerivAt.mfd_eq (h1.comp x h2)
  unfold tangentN
  rw [h3, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]

end Transversality

variable {n p n' p' : ℕ} {N N' : Set M}
  (hN : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin p)) N)
  (hN' : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n'))
      (EuclideanSpace ℝ (Fin p')) N')

/-! ### Transversal intersections -/

/-- Transversal intersection (tangent spaces inside `ℝᴷ⁺¹`). -/
def Transverse : Prop :=
  ∀ (x : M) (hx : x ∈ N) (hx' : x ∈ N'),
    tangentN hM hN ⟨x, hx⟩ ⊔ tangentN hM hN' ⟨x, hx'⟩ = tangentM hM x

/-- Transversality in chart coordinates: the chart-level tangent spaces span `ℝᵐ`. -/
theorem Transversality.transverse_iff :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := hN.chartedSpace;
    letI := hN'.chartedSpace;
    Transverse hM hN hN' ↔ ∀ (x : M) (hx : x ∈ N) (hx' : x ∈ N'),
      LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (Subtype.val : N → M) ⟨x, hx⟩ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ⊔
      LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (Subtype.val : N' → M) ⟨x, hx'⟩ :
          EuclideanSpace ℝ (Fin n') →L[ℝ] EuclideanSpace ℝ (Fin m)) :
          EuclideanSpace ℝ (Fin n') →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) = ⊤ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := hN.chartedSpace
  letI := hN'.chartedSpace
  unfold Transverse
  refine forall_congr' fun x => forall_congr' fun hx => forall_congr' fun hx' => ?_
  rw [tangentN_eq_map hM hN, tangentN_eq_map hM hN', ← Submodule.map_sup,
    tangentM_eq_map_top hM]
  exact (Submodule.map_injective_of_injective (injective_mfderiv_val hM x)).eq_iff

/-- Milnor's parenthesis. -/
theorem inter_eq_empty_of_transverse (hnp : n + p = m) (hnp' : n' + p' = m)
    (htr : Transverse hM hN hN') (hlt : n + n' < m) : N ∩ N' = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hx'⟩
  have h := htr x hx hx'
  have h1 : finrank ℝ (tangentN hM hN ⟨x, hx⟩) ≤ n := by
    unfold tangentN
    exact (LinearMap.finrank_range_le _).trans_eq (finrank_euclideanSpace_fin)
  have h2 : finrank ℝ (tangentN hM hN' ⟨x, hx'⟩) ≤ n' := by
    unfold tangentN
    exact (LinearMap.finrank_range_le _).trans_eq (finrank_euclideanSpace_fin)
  have h3 := Submodule.finrank_add_le_finrank_add_finrank (tangentN hM hN ⟨x, hx⟩)
    (tangentN hM hN' ⟨x, hx'⟩)
  rw [h, finrank_tangentM hM] at h3
  omega

/-- **Problem 16, second part.** A transversal intersection is a smooth manifold. -/
theorem isSliceSubmanifold_inter (hnp : n + p = m) (hnp' : n' + p' = m) {r : ℕ}
    (hr : r + (p + p') = m) (htr : Transverse hM hN hN') :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin r))
      (EuclideanSpace ℝ (Fin (p + p'))) (N ∩ N') := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := hN.chartedSpace
  letI := hN'.chartedSpace
  refine IsSliceSubmanifold.of_locally_preimage (by simp [hr]) fun x hx => ?_
  obtain ⟨U, hU, hxU, g, hg, hgS, hloc⟩ := exists_local_inter hN hN' (by simp [hnp])
    (by simp [hnp']) (prodEquivEuclidean p p') ((transverse_iff hM hN hN').1 htr) hx
  exact ⟨U, hU, hxU, g, hg, hgS, fun y hy hyS => (hloc y hy hyS).1⟩

/-- The tangent space of `N ∩ N'`, for any slice-submanifold structure of the right dimension. -/
theorem Transversality.tangentN_inter_of (hnp : n + p = m) (hnp' : n' + p' = m) {r : ℕ}
    (hr : r + (p + p') = m) (htr : Transverse hM hN hN')
    (hS : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin r))
        (EuclideanSpace ℝ (Fin (p + p'))) (N ∩ N')) (x : ↥(N ∩ N')) :
    tangentN hM hS x = tangentN hM hN ⟨x.1, x.2.1⟩ ⊓ tangentN hM hN' ⟨x.1, x.2.2⟩ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := hN.chartedSpace
  letI := hN'.chartedSpace
  letI := hS.chartedSpace
  obtain ⟨U, hU, hxU, g, hg, hgS, hloc⟩ := exists_local_inter hN hN' (by simp [hnp])
    (by simp [hnp']) (prodEquivEuclidean p p') ((transverse_iff hM hN hN').1 htr) x.2
  obtain ⟨hsurj, hker⟩ := hloc x.1 hxU x.2
  have h1 := hS.range_mfderiv_val_eq_ker (by simp [hr]) x hU hxU hg
    (fun y hy hyS => (hgS y hy).1 hyS) hsurj
  rw [tangentN_eq_map hM hS x, tangentN_eq_map hM hN, tangentN_eq_map hM hN', h1, hker,
    Submodule.map_inf ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x.1 :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
        EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1)))
      (injective_mfderiv_val hM x.1)]

/-- The tangent space of a transversal intersection is the intersection of the tangent spaces. -/
theorem tangentN_inter (hnp : n + p = m) (hnp' : n' + p' = m) {r : ℕ} (hr : r + (p + p') = m)
    (htr : Transverse hM hN hN') (x : ↥(N ∩ N')) :
    tangentN hM (isSliceSubmanifold_inter hM hN hN' hnp hnp' hr htr) x =
      tangentN hM hN ⟨x.1, x.2.1⟩ ⊓ tangentN hM hN' ⟨x.1, x.2.2⟩ :=
  tangentN_inter_of hM hN hN' hnp hnp' hr htr _ x

/-! ### Deforming a framed submanifold inside its product neighbourhood -/

namespace Transversality

section deform

variable {hM} {hMc : IsCompact M} {hne : M.Nonempty} {F : FramedSub hM n p}
  (T : TubeData hMc hne F)

/-- The deformed submanifold `G(N × {u})` is the level set `{z ∈ V | (G⁻¹ z).2 = u}`. -/
theorem mem_range_tube_iff [Nonempty F.N] {u : EuclideanSpace ℝ (Fin p)} (hu : ‖u‖ < T.ε)
    (z : M) : z ∈ Set.range (fun x : F.N => T.G (x, u)) ↔ z ∈ T.V ∧ (T.Ginv z).2 = u := by
  constructor
  · rintro ⟨x, rfl⟩
    have hq : ((x, u) : F.N × EuclideanSpace ℝ (Fin p)) ∈ PN.tube F.N p T.ε := hu
    exact ⟨⟨(x, u), hq, rfl⟩, by rw [T.Ginv_G hq]⟩
  · rintro ⟨hz, hzu⟩
    refine ⟨(T.Ginv z).1, ?_⟩
    have h : ((T.Ginv z).1, u) = T.Ginv z := Prod.ext rfl hzu.symm
    show T.G ((T.Ginv z).1, u) = z
    rw [h, T.G_Ginv hz]

/-- The fibre coordinate `z ↦ (G⁻¹ z).2` is smooth on `V`. -/
theorem contMDiffAt_fib [Nonempty F.N] {z : M} (hz : z ∈ T.V) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun z => (T.Ginv z).2) z := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  exact contMDiffAt_snd.comp z (T.contMDiffAt_Ginv hz)

/-- `d(pr₂ ∘ G⁻¹) ∘ dG = pr₂` on the tube. -/
theorem mfd_fib_comp_G [Nonempty F.N] {q : F.N × EuclideanSpace ℝ (Fin p)}
    (hq : q ∈ PN.tube F.N p T.ε) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fun z => (T.Ginv z).2)
      (T.G q)).comp (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin m)) T.G q) =
      ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin p)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  have hz : T.G q ∈ T.V := ⟨q, hq, rfl⟩
  have h1 := hasMFDerivAt_mfd ((contMDiffAt_fib T hz).mdifferentiableAt (by simp))
  have h2 := hasMFDerivAt_mfd ((T.hG q).mdifferentiableAt (by simp))
  have h3 := h1.comp q h2
  have hev : (fun q' => (T.Ginv (T.G q')).2) =ᶠ[𝓝 q] Prod.snd := by
    filter_upwards [(PN.isOpen_tube T.ε).mem_nhds hq] with q' hq'
    rw [T.Ginv_G hq']
  have h4 := h3.congr_of_eventuallyEq hev.symm
  exact hasMFDerivAt_unique h4 (hasMFDerivAt_snd q)

/-- The fibre coordinate is a submersion on `V`. -/
theorem surjective_mfd_fib [Nonempty F.N] {z : M} (hz : z ∈ T.V) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun z => (T.Ginv z).2) z) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  intro b
  have h := mfd_fib_comp_G T (T.Ginv_mem hz)
  rw [T.G_Ginv hz] at h
  refine ⟨mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin m)) T.G (T.Ginv z) (0, b), ?_⟩
  exact DFunLike.congr_fun h (0, b)

/-- The derivative of `z ↦ (G⁻¹ z).2 - u`. -/
theorem hasMFDerivAt_fib_sub [Nonempty F.N] {z : M} (hz : z ∈ T.V)
    (u : EuclideanSpace ℝ (Fin p)) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun z => (T.Ginv z).2 - u) z
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun z => (T.Ginv z).2) z :) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h1 := hasMFDerivAt_mfd ((contMDiffAt_fib T hz).mdifferentiableAt (by simp))
  have h2 := h1.sub (hasMFDerivAt_const u z)
  exact h2.congr_mfderiv (sub_zero _)

/-- **The deformed submanifold.** For `‖u‖ < ε`, `G(N × {u})` is a slice submanifold of `M`. -/
theorem isSliceSubmanifold_range {u : EuclideanSpace ℝ (Fin p)} (hu : ‖u‖ < T.ε) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin p)) (Set.range fun x : F.N => T.G (x, u)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rcases isEmpty_or_nonempty F.N with hE | hE
  · rintro _ ⟨x, rfl⟩
    exact isEmptyElim x
  · refine IsSliceSubmanifold.of_locally_preimage (by simp [F.dim]) fun z hz => ?_
    refine ⟨T.V, T.isOpen_V, ((mem_range_tube_iff T hu z).1 hz).1,
      fun z => (T.Ginv z).2 - u, fun y hy => ?_, fun y hy => ?_, fun y hy _ => ?_⟩
    · exact ((contMDiffAt_fib T hy).sub contMDiffAt_const).contMDiffWithinAt
    · rw [mem_range_tube_iff T hu y, sub_eq_zero]
      exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
    · rw [(hasMFDerivAt_fib_sub T hy u).mfderiv]
      exact surjective_mfd_fib T hy

/-- The tangent space of the deformed submanifold is the kernel of the derivative of the fibre
coordinate. -/
theorem range_mfd_val_range_eq_ker [Nonempty F.N] {u : EuclideanSpace ℝ (Fin p)} (hu : ‖u‖ < T.ε)
    (hS : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin p)) (Set.range fun x : F.N => T.G (x, u)))
    (z : ↥(Set.range fun x : F.N => T.G (x, u))) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := hS.chartedSpace;
    LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (Subtype.val : ↥(Set.range fun x : F.N => T.G (x, u)) → M) z :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) =
      LinearMap.ker ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun z => (T.Ginv z).2) z.1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
        EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := hS.chartedSpace
  have hz := ((mem_range_tube_iff T hu z.1).1 z.2).1
  have h := hS.range_mfderiv_val_eq_ker (by simp [F.dim]) z T.isOpen_V hz
    (fun y hy => ((contMDiffAt_fib T hy).sub contMDiffAt_const).contMDiffWithinAt)
    (fun y _ hyS => by rw [sub_eq_zero]; exact ((mem_range_tube_iff T hu y).1 hyS).2)
    (by rw [(hasMFDerivAt_fib_sub T hz u).mfderiv]; exact surjective_mfd_fib T hz)
  rw [h, HasMFDerivAt.mfd_eq (hasMFDerivAt_fib_sub T hz u)]

end deform

end Transversality

variable (hMc : IsCompact M) (hne : M.Nonempty)

/-- **Problem 16, first part.** A framed submanifold can be deformed slightly (by an injective
smooth map within distance `δ` of the inclusion, inside its product neighbourhood) so as to meet
a given submanifold `N'` transversally. -/
theorem exists_transverse_deformation (F : FramedSub hM n p) (T : TubeData hMc hne F)
    (hN' : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n'))
        (EuclideanSpace ℝ (Fin p')) N')
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u : EuclideanSpace ℝ (Fin p), ‖u‖ < δ ∧ ‖u‖ < T.ε ∧
      ∃ hNu : (letI := hM.chartedSpace; haveI := hM.isManifold;
        IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℝ (Fin p)) (Set.range fun x : F.N => T.G (x, u))),
        Transverse hM hNu hN' ∧ Function.Injective (fun x : F.N => T.G (x, u)) ∧
        ∀ x : F.N, ‖(T.G (x, u)).1 - x.1.1‖ < δ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  letI := hN'.chartedSpace
  haveI := hN'.isManifold
  -- A radius `ρ₁` such that `G(N × {t})` is `δ`-close to `N` for `‖t‖ < ρ₁`.
  haveI : CompactSpace F.N := isCompact_iff_compactSpace.1 F.compact
  have hcont : Continuous fun q : EuclideanSpace ℝ (Fin p) × F.N =>
      ‖(T.G (q.2, q.1)).1 - q.2.1.1‖ :=
    ((continuous_subtype_val.comp (T.hG.continuous.comp continuous_swap)).sub
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).norm
  have hev : ∀ᶠ t in 𝓝 (0 : EuclideanSpace ℝ (Fin p)), ∀ x ∈ (univ : Set F.N),
      ‖(T.G (x, t)).1 - x.1.1‖ < δ := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun x _ => ?_
    exact (hcont.tendsto ((0 : EuclideanSpace ℝ (Fin p)), x)).eventually_lt_const
      (by simp [T.G_zero, hδ])
  obtain ⟨ρ₁, hρ₁, hclose⟩ := Metric.eventually_nhds_iff.1 hev
  rcases isEmpty_or_nonempty F.N with hE | hE
  · -- `N = ∅`: nothing to deform.
    refine ⟨0, by rw [norm_zero]; exact hδ, by rw [norm_zero]; exact T.hε,
      isSliceSubmanifold_range T (by rw [norm_zero]; exact T.hε), ?_, ?_, ?_⟩
    · intro z hz
      exact isEmptyElim hz.choose
    · intro x
      exact isEmptyElim x
    · intro x
      exact isEmptyElim x
  · -- Brown's theorem for the fibre coordinate on the open subset `N' ∩ V` of `N'`.
    let W : TopologicalSpace.Opens N' :=
      ⟨{y | y.1 ∈ T.V}, T.isOpen_V.preimage continuous_subtype_val⟩
    have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
        (fun y : W => (T.Ginv y.1.1).2) := fun y => by
      have h1 := contMDiffAt_fib T (z := y.1.1) y.2
      have h2 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
          (fun y : W => y.1.1) y := (hN'.contMDiff_val.comp contMDiff_subtype_val) y
      have h3 := h1.comp y h2
      exact h3
    have hρ0 : 0 < min (min δ T.ε) ρ₁ := lt_min (lt_min hδ T.hε) hρ₁
    obtain ⟨u, hureg, hu⟩ :=
      (dense_regularValues hf).exists_mem_open isOpen_ball (nonempty_ball.2 hρ0)
    rw [mem_ball_zero_iff] at hu
    have huδ : ‖u‖ < δ := hu.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have huε : ‖u‖ < T.ε := hu.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have huρ₁ : ‖u‖ < ρ₁ := hu.trans_le (min_le_right _ _)
    refine ⟨u, huδ, huε, isSliceSubmanifold_range T huε, ?_, ?_, ?_⟩
    · -- Transversality: `TN_u = ker dπ` and `dπ (TN') = ℝᵖ` since `u` is a regular value.
      refine (transverse_iff hM (isSliceSubmanifold_range T huε) hN').2 fun z hz hz' => ?_
      have hzV := ((mem_range_tube_iff T huε z).1 hz).1
      have hzu := ((mem_range_tube_iff T huε z).1 hz).2
      rw [range_mfd_val_range_eq_ker T huε (isSliceSubmanifold_range T huε) ⟨z, hz⟩]
      let y : W := ⟨⟨z, hz'⟩, hzV⟩
      have hreg : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
          (fun y : W => (T.Ginv y.1.1).2) y) := hureg y hzu
      have hval : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
          (Subtype.val : N' → M) y.1 := hN'.contMDiff_val.mdifferentiableAt (by simp)
      have hfib : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
          𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fun z => (T.Ginv z).2) z :=
        (contMDiffAt_fib T hzV).mdifferentiableAt (by simp)
      have h1 : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
          (fun y : W => (T.Ginv y.1.1).2) y =
          mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
            ((fun z => (T.Ginv z).2) ∘ (Subtype.val : N' → M)) y.1 :=
        mfd_comp_subtype_val W (hfib.comp y.1 hval)
      have h2 : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
          ((fun z => (T.Ginv z).2) ∘ (Subtype.val : N' → M)) y.1 =
          (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
            (fun z => (T.Ginv z).2) z).comp
          (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n')) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
            (Subtype.val : N' → M) ⟨z, hz'⟩) :=
        HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd hfib).comp y.1 (hasMFDerivAt_mfd hval))
      rw [h1, h2] at hreg
      exact ker_sup_range_eq_top_of_surjective_comp hreg
    · -- Injectivity: `G` is injective on the tube.
      intro x x' h
      have hx : ((x, u) : F.N × EuclideanSpace ℝ (Fin p)) ∈ PN.tube F.N p T.ε := huε
      have hx' : ((x', u) : F.N × EuclideanSpace ℝ (Fin p)) ∈ PN.tube F.N p T.ε := huε
      exact congrArg Prod.fst (T.hinj hx hx' h)
    · -- Closeness to the inclusion.
      intro x
      exact hclose (by rw [dist_zero_right]; exact huρ₁) x (mem_univ x)

end Problems

end Milnor
