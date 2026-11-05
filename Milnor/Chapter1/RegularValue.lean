import Milnor.Chapter1.InverseFunction
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Set.Card
import Mathlib.Topology.Separation.Hausdorff

/-!
Milnor, *Topology from the Differentiable Viewpoint*, §1, "Regular values" (pp. 7–8).

# Regular values

Milnor (p. 7) defines, for `f : M → N` smooth between manifolds *of the same dimension*:
* `x ∈ M` is a **regular point** of `f` if `dfₓ` is nonsingular;
* `y ∈ N` is a **regular value** if `f⁻¹(y)` contains only regular points;
* otherwise `x` is a **critical point** and `f x` a **critical value**.

He then removes the same-dimension restriction in §2 (p. 11): `x` is a regular point if
`dfₓ : TMₓ → TN_{f(x)}` is *surjective*. We adopt the §2 definition from the start; in the
same-dimension case surjectivity of a linear map is equivalent to bijectivity
(`IsRegularPoint.isInvertible_mfderiv`), so nothing is lost.

## Main results (Milnor p. 8)

* `IsRegularPoint.isLocalDiffeomorphAt`: at a regular point (same dimension), `f` maps a
  neighbourhood of `x` diffeomorphically onto an open set. This is the inverse function theorem
  on manifolds, proved in `Milnor.Chapter1.InverseFunction`.
* `IsRegularValue.finite_preimage`: if `M` is compact and `y` is a regular value, then `f⁻¹(y)`
  is finite.
* `IsRegularValue.eventually_ncard_preimage_eq`: `#f⁻¹(y')` is locally constant in `y`, i.e.
  `#f⁻¹(y') = #f⁻¹(y)` for all `y'` in a neighbourhood of a regular value `y`.

## Hypotheses made explicit

Milnor's manifolds are subsets of Euclidean space, hence automatically Hausdorff. Mathlib's
manifolds are abstract, so we assume `T2Space` where Milnor uses it silently:
* finiteness of `f⁻¹(y)` needs `N` to be `T1` (so that `{y}` is closed);
* local constancy needs `M` Hausdorff (to separate the finitely many preimages by disjoint
  open sets) and `N` Hausdorff (so that the compact set `f(M ∖ ⋃ Uᵢ)` is closed).
-/

open Set Filter Topology Manifold Module

noncomputable section

namespace Milnor

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞}

/-! ### Definitions -/

section defs

variable (I J)

/-- `x` is a **regular point** of `f` if the derivative `dfₓ` is surjective (Milnor p. 11;
for manifolds of the same dimension this is equivalent to `dfₓ` being nonsingular, Milnor p. 7).
-/
def IsRegularPoint (f : M → N) (x : M) : Prop :=
  Function.Surjective (mfderiv I J f x)

/-- `x` is a **critical point** of `f` if it is not a regular point. -/
def IsCriticalPoint (f : M → N) (x : M) : Prop :=
  ¬ IsRegularPoint I J f x

/-- `y` is a **regular value** of `f` if every point of `f⁻¹(y)` is a regular point. In particular
every point of `N` not in the image of `f` is a regular value. -/
def IsRegularValue (f : M → N) (y : N) : Prop :=
  ∀ x, f x = y → IsRegularPoint I J f x

/-- `y` is a **critical value** of `f` if it is the image of a critical point. -/
def IsCriticalValue (f : M → N) (y : N) : Prop :=
  ∃ x, f x = y ∧ IsCriticalPoint I J f x

end defs

variable {f : M → N} {x : M} {y : N}

/-- Milnor p. 8: "each `y ∈ N` is either a critical value or a regular value according as
`f⁻¹(y)` does or does not contain a critical point." -/
theorem isRegularValue_iff_not_isCriticalValue :
    IsRegularValue I J f y ↔ ¬ IsCriticalValue I J f y := by
  simp only [IsRegularValue, IsCriticalValue, IsCriticalPoint, not_exists, not_and, not_not]

/-- A point outside the image of `f` is (vacuously) a regular value. -/
theorem IsRegularValue.of_notMem_range (hy : y ∉ range f) : IsRegularValue I J f y :=
  fun x hx => (hy ⟨x, hx⟩).elim

/-! ### The same-dimension case -/

section sameDim

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- In the same-dimension case, a regular point has *invertible* derivative
(Milnor's original definition, p. 7). -/
theorem IsRegularPoint.isInvertible_mfderiv (hdim : finrank 𝕜 E = finrank 𝕜 F)
    (h : IsRegularPoint I J f x) : (mfderiv I J f x).IsInvertible := by
  let L : E →L[𝕜] F := mfderiv I J f x
  have hsurj : Function.Surjective L := h
  have hinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := (L : E →ₗ[𝕜] F)) hdim).2
      hsurj
  let e : E ≃L[𝕜] F :=
    (LinearEquiv.ofBijective (L : E →ₗ[𝕜] F) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  exact ⟨e, by ext v; rfl⟩

/-- Conversely, an invertible derivative makes `x` a regular point. -/
theorem IsRegularPoint.of_isInvertible_mfderiv (h : (mfderiv I J f x).IsInvertible) :
    IsRegularPoint I J f x := by
  obtain ⟨e, he⟩ := h
  rw [IsRegularPoint, ← he]
  exact e.surjective

variable [I.Boundaryless] [J.Boundaryless] [IsManifold I n M] [IsManifold J n N]

/-- Milnor p. 7: "if `x` is a regular point, it follows from the inverse function theorem that
`f` maps a neighborhood of `x` in `M` diffeomorphically onto an open set in `N`." -/
theorem IsRegularPoint.isLocalDiffeomorphAt (hdim : finrank 𝕜 E = finrank 𝕜 F)
    (hf : ContMDiff I J n f) (hn : n ≠ 0) (h : IsRegularPoint I J f x) :
    IsLocalDiffeomorphAt I J n f x :=
  haveI := FiniteDimensional.complete 𝕜 E
  Milnor.ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv hf hn (h.isInvertible_mfderiv hdim)

/-- Milnor p. 8: "if `M` is compact and `y ∈ N` is a regular value, then `f⁻¹(y)` is a finite
set (possibly empty)." -/
theorem IsRegularValue.finite_preimage [CompactSpace M] [T1Space N]
    (hdim : finrank 𝕜 E = finrank 𝕜 F) (hf : ContMDiff I J n f) (hn : n ≠ 0)
    (hy : IsRegularValue I J f y) : (f ⁻¹' {y}).Finite := by
  set s := f ⁻¹' {y} with hs_def
  have hs_mem : ∀ z, z ∈ s ↔ f z = y := fun z => by simp [s]
  -- `f⁻¹(y)` is closed in the compact space `M`, hence compact.
  have hs : IsCompact s := (isClosed_singleton.preimage hf.continuous).isCompact
  -- Every point of `f⁻¹(y)` has a neighbourhood on which `f` is injective.
  have key : ∀ x ∈ s, ∃ U ∈ 𝓝 x, InjOn f U := fun x hx => by
    have hloc := (hy x ((hs_mem x).1 hx)).isLocalDiffeomorphAt hdim hf hn
    refine ⟨hloc.localInverse.target,
      hloc.localInverse.open_target.mem_nhds hloc.localInverse_mem_target, ?_⟩
    intro a ha b hb hab
    rw [← hloc.localInverse_left_inv ha, ← hloc.localInverse_left_inv hb, hab]
  choose! U hU hUinj using key
  -- Finitely many of these neighbourhoods cover `f⁻¹(y)`, and each contains one point of it.
  obtain ⟨t, hts, hcover⟩ := hs.elim_nhds_subcover U hU
  refine t.finite_toSet.subset fun z hz => ?_
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcover hz)
  have hxs : x ∈ s := hts x hxt
  have hzx' : z = x :=
    hUinj x hxs hzx (mem_of_mem_nhds (hU x hxs)) (by rw [(hs_mem z).1 hz, (hs_mem x).1 hxs])
  rw [hzx']
  exact hxt

/-- Milnor p. 8: "`#f⁻¹(y)` is locally constant as a function of `y`". More precisely, if `y` is a
regular value then `#f⁻¹(y') = #f⁻¹(y)` for every `y'` in a neighbourhood of `y`.

(Milnor writes "where `y` ranges only through regular values", but his proof gives the equality
for *all* `y'` in the neighbourhood `V = V₁ ∩ ⋯ ∩ Vₖ ∖ f(M ∖ U₁ ∖ ⋯ ∖ Uₖ)`, and that is what we
prove.) -/
theorem IsRegularValue.eventually_ncard_preimage_eq [CompactSpace M] [T2Space M] [T2Space N]
    (hdim : finrank 𝕜 E = finrank 𝕜 F) (hf : ContMDiff I J n f) (hn : n ≠ 0)
    (hy : IsRegularValue I J f y) :
    ∀ᶠ y' in 𝓝 y, (f ⁻¹' {y'}).ncard = (f ⁻¹' {y}).ncard := by
  set s := f ⁻¹' {y} with hs_def
  have hs_mem : ∀ z, z ∈ s ↔ f z = y := fun z => by simp [s]
  have hs_fin : s.Finite := hy.finite_preimage hdim hf hn
  have : Finite s := hs_fin.to_subtype
  -- Local inverses of `f` at the points `x₁, …, xₖ` of `f⁻¹(y)`.
  have hloc : ∀ x ∈ s, IsLocalDiffeomorphAt I J n f x := fun x hx =>
    (hy x ((hs_mem x).1 hx)).isLocalDiffeomorphAt hdim hf hn
  let L : s → PartialDiffeomorph J I N M n := fun x => (hloc x.1 x.2).localInverse
  have hL_left : ∀ (x : s) {z}, z ∈ (L x).target → L x (f z) = z := fun x _ hz =>
    (hloc x.1 x.2).localInverse_left_inv hz
  have hL_right : ∀ (x : s) {z}, z ∈ (L x).source → f (L x z) = z := fun x _ hz =>
    (hloc x.1 x.2).localInverse_right_inv hz
  have hL_mem_target : ∀ x : s, x.1 ∈ (L x).target := fun x =>
    (hloc x.1 x.2).localInverse_mem_target
  have hL_mem_source : ∀ x : s, y ∈ (L x).source := fun x => by
    have := (hloc x.1 x.2).localInverse_mem_source
    rwa [(hs_mem x.1).1 x.2] at this
  -- Pairwise disjoint open neighbourhoods `W xᵢ` of the `xᵢ` (Milnor: "pairwise disjoint
  -- neighborhoods `U₁, …, Uₖ`"). This is where `M` Hausdorff is used.
  obtain ⟨W, hW, hWdisj⟩ := hs_fin.t2_separation
  -- `Uᵢ := (L xᵢ).target ∩ W xᵢ`, open, containing `xᵢ`, mapped diffeomorphically by `f`.
  let U : s → Set M := fun x => (L x).target ∩ W x.1
  have hU_open : ∀ x, IsOpen (U x) := fun x => (L x).open_target.inter (hW x.1).2
  have hxU : ∀ x : s, x.1 ∈ U x := fun x => ⟨hL_mem_target x, (hW x.1).1⟩
  -- `Vᵢ := f(Uᵢ) = (L xᵢ).source ∩ (L xᵢ)⁻¹(Uᵢ)`, open in `N`.
  let V' : s → Set N := fun x => (L x).source ∩ (L x) ⁻¹' (U x)
  have hV'_open : ∀ x, IsOpen (V' x) := fun x =>
    (L x).contMDiffOn.continuousOn.isOpen_inter_preimage (L x).open_source (hU_open x)
  have hyV' : ∀ x, y ∈ V' x := fun x => by
    refine ⟨hL_mem_source x, ?_⟩
    show L x y ∈ U x
    have : L x (f x.1) = x.1 := hL_left x (hL_mem_target x)
    rw [(hs_mem x.1).1 x.2] at this
    rw [this]
    exact hxU x
  -- `C := f(M ∖ ⋃ Uᵢ)` is compact, hence closed since `N` is Hausdorff.
  let C : Set N := f '' (⋃ x, U x)ᶜ
  have hC : IsClosed C :=
    ((isOpen_iUnion hU_open).isClosed_compl.isCompact.image hf.continuous).isClosed
  -- The neighbourhood `V := ⋂ Vᵢ ∖ C` of `y`.
  let V : Set N := (⋂ x, V' x) ∩ Cᶜ
  have hV_open : IsOpen V := (isOpen_iInter_of_finite hV'_open).inter hC.isOpen_compl
  have hyV : y ∈ V := by
    refine ⟨mem_iInter.2 hyV', fun hyC => ?_⟩
    obtain ⟨z, hz, hzy⟩ := hyC
    have hzs : z ∈ s := (hs_mem z).2 hzy
    exact hz (mem_iUnion.2 ⟨⟨z, hzs⟩, hxU ⟨z, hzs⟩⟩)
  -- On `V`, the fibre `f⁻¹(y')` is in bijection with `s = f⁻¹(y)` via `xᵢ ↦ (L xᵢ) y'`.
  filter_upwards [hV_open.mem_nhds hyV] with y' hy'
  obtain ⟨hy'V', hy'C⟩ := hy'
  have hy'x : ∀ x : s, y' ∈ V' x := fun x => mem_iInter.1 hy'V' x
  symm
  refine Set.ncard_congr (fun a ha => L ⟨a, ha⟩ y') ?_ ?_ ?_
  · intro a ha
    exact hL_right ⟨a, ha⟩ (hy'x ⟨a, ha⟩).1
  · intro a b ha hb hab
    have h1 : L ⟨a, ha⟩ y' ∈ W a := (hy'x ⟨a, ha⟩).2.2
    have h2 : L ⟨b, hb⟩ y' ∈ W b := (hy'x ⟨b, hb⟩).2.2
    rw [hab] at h1
    exact hWdisj.elim_set ha hb _ h1 h2
  · intro b hb
    have hb' : f b = y' := hb
    have hbU : b ∈ ⋃ x, U x := by
      by_contra hcon
      exact hy'C ⟨b, hcon, hb'⟩
    obtain ⟨x, hbx⟩ := mem_iUnion.1 hbU
    refine ⟨x.1, x.2, ?_⟩
    show L x y' = b
    rw [← hb']
    exact hL_left x hbx.1

/-- The strengthening needed in Chapter 4: near a regular value `y`, every `y'` is again a
regular value (its preimages are the points `(L xᵢ) y'`, at which `f` is a local
diffeomorphism), with the same number of preimages. -/
theorem IsRegularValue.eventually_isRegularValue_and_ncard [CompactSpace M] [T2Space M]
    [T2Space N] (hdim : finrank 𝕜 E = finrank 𝕜 F) (hf : ContMDiff I J n f) (hn : n ≠ 0)
    (hy : IsRegularValue I J f y) :
    ∀ᶠ y' in 𝓝 y, IsRegularValue I J f y' ∧ (f ⁻¹' {y'}).ncard = (f ⁻¹' {y}).ncard := by
  set s := f ⁻¹' {y} with hs_def
  have hs_mem : ∀ z, z ∈ s ↔ f z = y := fun z => by simp [s]
  have hs_fin : s.Finite := hy.finite_preimage hdim hf hn
  have : Finite s := hs_fin.to_subtype
  have hloc : ∀ x ∈ s, IsLocalDiffeomorphAt I J n f x := fun x hx =>
    (hy x ((hs_mem x).1 hx)).isLocalDiffeomorphAt hdim hf hn
  let L : s → PartialDiffeomorph J I N M n := fun x => (hloc x.1 x.2).localInverse
  have hL_left : ∀ (x : s) {z}, z ∈ (L x).target → L x (f z) = z := fun x _ hz =>
    (hloc x.1 x.2).localInverse_left_inv hz
  have hL_right : ∀ (x : s) {z}, z ∈ (L x).source → f (L x z) = z := fun x _ hz =>
    (hloc x.1 x.2).localInverse_right_inv hz
  have hL_mem_target : ∀ x : s, x.1 ∈ (L x).target := fun x =>
    (hloc x.1 x.2).localInverse_mem_target
  have hL_mem_source : ∀ x : s, y ∈ (L x).source := fun x => by
    have := (hloc x.1 x.2).localInverse_mem_source
    rwa [(hs_mem x.1).1 x.2] at this
  -- every point of `(L x).target` is a point where `f` is a local diffeomorphism
  have hL_reg : ∀ (x : s) {z}, z ∈ (L x).target → IsRegularPoint I J f z := fun x z hz => by
    have hspec := Classical.choose_spec (hloc x.1 x.2)
    have hzloc : IsLocalDiffeomorphAt I J n f z := ⟨Classical.choose (hloc x.1 x.2), hz, hspec.2⟩
    show Function.Surjective (mfderiv I J f z)
    rw [← hzloc.mfderivToContinuousLinearEquiv_coe hn]
    exact (hzloc.mfderivToContinuousLinearEquiv hn).surjective
  obtain ⟨W, hW, hWdisj⟩ := hs_fin.t2_separation
  let U : s → Set M := fun x => (L x).target ∩ W x.1
  have hU_open : ∀ x, IsOpen (U x) := fun x => (L x).open_target.inter (hW x.1).2
  have hxU : ∀ x : s, x.1 ∈ U x := fun x => ⟨hL_mem_target x, (hW x.1).1⟩
  let V' : s → Set N := fun x => (L x).source ∩ (L x) ⁻¹' (U x)
  have hV'_open : ∀ x, IsOpen (V' x) := fun x =>
    (L x).contMDiffOn.continuousOn.isOpen_inter_preimage (L x).open_source (hU_open x)
  have hyV' : ∀ x, y ∈ V' x := fun x => by
    refine ⟨hL_mem_source x, ?_⟩
    show L x y ∈ U x
    have : L x (f x.1) = x.1 := hL_left x (hL_mem_target x)
    rw [(hs_mem x.1).1 x.2] at this
    rw [this]
    exact hxU x
  let C : Set N := f '' (⋃ x, U x)ᶜ
  have hC : IsClosed C :=
    ((isOpen_iUnion hU_open).isClosed_compl.isCompact.image hf.continuous).isClosed
  let V : Set N := (⋂ x, V' x) ∩ Cᶜ
  have hV_open : IsOpen V := (isOpen_iInter_of_finite hV'_open).inter hC.isOpen_compl
  have hyV : y ∈ V := by
    refine ⟨mem_iInter.2 hyV', fun hyC => ?_⟩
    obtain ⟨z, hz, hzy⟩ := hyC
    have hzs : z ∈ s := (hs_mem z).2 hzy
    exact hz (mem_iUnion.2 ⟨⟨z, hzs⟩, hxU ⟨z, hzs⟩⟩)
  filter_upwards [hV_open.mem_nhds hyV] with y' hy'
  obtain ⟨hy'V', hy'C⟩ := hy'
  have hy'x : ∀ x : s, y' ∈ V' x := fun x => mem_iInter.1 hy'V' x
  -- every preimage of `y'` lies in some `U x`
  have hpre : ∀ b, f b = y' → ∃ x : s, b ∈ U x := fun b hb => by
    have hbU : b ∈ ⋃ x, U x := by
      by_contra hcon
      exact hy'C ⟨b, hcon, hb⟩
    exact mem_iUnion.1 hbU
  refine ⟨fun b hb => ?_, ?_⟩
  · obtain ⟨x, hbx⟩ := hpre b hb
    exact hL_reg x hbx.1
  symm
  refine Set.ncard_congr (fun a ha => L ⟨a, ha⟩ y') ?_ ?_ ?_
  · intro a ha
    exact hL_right ⟨a, ha⟩ (hy'x ⟨a, ha⟩).1
  · intro a b ha hb hab
    have h1 : L ⟨a, ha⟩ y' ∈ W a := (hy'x ⟨a, ha⟩).2.2
    have h2 : L ⟨b, hb⟩ y' ∈ W b := (hy'x ⟨b, hb⟩).2.2
    rw [hab] at h1
    exact hWdisj.elim_set ha hb _ h1 h2
  · intro b hb
    have hb' : f b = y' := hb
    obtain ⟨x, hbx⟩ := hpre b hb'
    refine ⟨x.1, x.2, ?_⟩
    show L x y' = b
    rw [← hb']
    exact hL_left x hbx.1

/-- The signed strengthening needed in Chapter 5: for a weight `φ : M → ℤ` which is locally
constant near each point of `f⁻¹(y)`, the weighted count `∑ φ` over `f⁻¹(y')` is constant for
`y'` near a regular value `y`. -/
theorem IsRegularValue.eventually_finsum_preimage_eq [CompactSpace M] [T2Space M]
    [T2Space N] (hdim : finrank 𝕜 E = finrank 𝕜 F) (hf : ContMDiff I J n f) (hn : n ≠ 0)
    (hy : IsRegularValue I J f y) {φ : M → ℤ}
    (hφ : ∀ x, f x = y → ∀ᶠ z in 𝓝 x, φ z = φ x) :
    ∀ᶠ y' in 𝓝 y, ∑ᶠ x ∈ f ⁻¹' {y'}, φ x = ∑ᶠ x ∈ f ⁻¹' {y}, φ x := by
  classical
  set s := f ⁻¹' {y} with hs_def
  have hs_mem : ∀ z, z ∈ s ↔ f z = y := fun z => by simp [s]
  have hs_fin : s.Finite := hy.finite_preimage hdim hf hn
  have : Finite s := hs_fin.to_subtype
  have hloc : ∀ x ∈ s, IsLocalDiffeomorphAt I J n f x := fun x hx =>
    (hy x ((hs_mem x).1 hx)).isLocalDiffeomorphAt hdim hf hn
  let L : s → PartialDiffeomorph J I N M n := fun x => (hloc x.1 x.2).localInverse
  have hL_left : ∀ (x : s) {z}, z ∈ (L x).target → L x (f z) = z := fun x _ hz =>
    (hloc x.1 x.2).localInverse_left_inv hz
  have hL_right : ∀ (x : s) {z}, z ∈ (L x).source → f (L x z) = z := fun x _ hz =>
    (hloc x.1 x.2).localInverse_right_inv hz
  have hL_mem_target : ∀ x : s, x.1 ∈ (L x).target := fun x =>
    (hloc x.1 x.2).localInverse_mem_target
  have hL_mem_source : ∀ x : s, y ∈ (L x).source := fun x => by
    have := (hloc x.1 x.2).localInverse_mem_source
    rwa [(hs_mem x.1).1 x.2] at this
  -- open neighbourhoods on which `φ` is constant
  have hO : ∀ x : s, ∃ O : Set M, IsOpen O ∧ x.1 ∈ O ∧ ∀ z ∈ O, φ z = φ x.1 := fun x => by
    obtain ⟨O, hO, hOopen, hxO⟩ := eventually_nhds_iff.1 (hφ x.1 ((hs_mem x.1).1 x.2))
    exact ⟨O, hOopen, hxO, hO⟩
  choose O hO_open hxO hOφ using hO
  obtain ⟨W, hW, hWdisj⟩ := hs_fin.t2_separation
  let U : s → Set M := fun x => (L x).target ∩ W x.1 ∩ O x
  have hU_open : ∀ x, IsOpen (U x) := fun x =>
    ((L x).open_target.inter (hW x.1).2).inter (hO_open x)
  have hxU : ∀ x : s, x.1 ∈ U x := fun x => ⟨⟨hL_mem_target x, (hW x.1).1⟩, hxO x⟩
  let V' : s → Set N := fun x => (L x).source ∩ (L x) ⁻¹' (U x)
  have hV'_open : ∀ x, IsOpen (V' x) := fun x =>
    (L x).contMDiffOn.continuousOn.isOpen_inter_preimage (L x).open_source (hU_open x)
  have hyV' : ∀ x, y ∈ V' x := fun x => by
    refine ⟨hL_mem_source x, ?_⟩
    show L x y ∈ U x
    have : L x (f x.1) = x.1 := hL_left x (hL_mem_target x)
    rw [(hs_mem x.1).1 x.2] at this
    rw [this]
    exact hxU x
  let C : Set N := f '' (⋃ x, U x)ᶜ
  have hC : IsClosed C :=
    ((isOpen_iUnion hU_open).isClosed_compl.isCompact.image hf.continuous).isClosed
  let V : Set N := (⋂ x, V' x) ∩ Cᶜ
  have hV_open : IsOpen V := (isOpen_iInter_of_finite hV'_open).inter hC.isOpen_compl
  have hyV : y ∈ V := by
    refine ⟨mem_iInter.2 hyV', fun hyC => ?_⟩
    obtain ⟨z, hz, hzy⟩ := hyC
    have hzs : z ∈ s := (hs_mem z).2 hzy
    exact hz (mem_iUnion.2 ⟨⟨z, hzs⟩, hxU ⟨z, hzs⟩⟩)
  filter_upwards [hV_open.mem_nhds hyV] with y' hy'
  obtain ⟨hy'V', hy'C⟩ := hy'
  have hy'x : ∀ x : s, y' ∈ V' x := fun x => mem_iInter.1 hy'V' x
  have hpre : ∀ b, f b = y' → ∃ x : s, b ∈ U x := fun b hb => by
    have hbU : b ∈ ⋃ x, U x := by
      by_contra hcon
      exact hy'C ⟨b, hcon, hb⟩
    exact mem_iUnion.1 hbU
  -- the bijection `s → f⁻¹(y')`, `x ↦ L x y'`, preserves `φ`
  symm
  refine finsum_mem_eq_of_bijOn (fun a => if ha : a ∈ s then L ⟨a, ha⟩ y' else a) ⟨?_, ?_, ?_⟩ ?_
  · intro a ha
    show (if ha : a ∈ s then L ⟨a, ha⟩ y' else a) ∈ f ⁻¹' {y'}
    rw [dif_pos ha]
    exact hL_right ⟨a, ha⟩ (hy'x ⟨a, ha⟩).1
  · intro a ha b hb hab
    change (if ha : a ∈ s then L ⟨a, ha⟩ y' else a) =
      (if hb : b ∈ s then L ⟨b, hb⟩ y' else b) at hab
    rw [dif_pos ha, dif_pos hb] at hab
    have h1 : L ⟨a, ha⟩ y' ∈ W a := (hy'x ⟨a, ha⟩).2.1.2
    have h2 : L ⟨b, hb⟩ y' ∈ W b := (hy'x ⟨b, hb⟩).2.1.2
    rw [hab] at h1
    exact hWdisj.elim_set ha hb _ h1 h2
  · intro b hb
    have hb' : f b = y' := hb
    obtain ⟨x, hbx⟩ := hpre b hb'
    refine ⟨x.1, x.2, ?_⟩
    show (if h : x.1 ∈ s then L ⟨x.1, h⟩ y' else x.1) = b
    rw [dif_pos x.2]
    show L x y' = b
    rw [← hb']
    exact hL_left x hbx.1.1
  · intro a ha
    show φ a = φ (if ha : a ∈ s then L ⟨a, ha⟩ y' else a)
    rw [dif_pos ha]
    exact (hOφ ⟨a, ha⟩ _ (hy'x ⟨a, ha⟩).2.2).symm

end sameDim

end Milnor
