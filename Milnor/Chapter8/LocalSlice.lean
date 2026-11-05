import Milnor.Chapter6.Opens
import Milnor.Chapter2.LevelSet

/-!
# Local zero sets of submersions are slice submanifolds

Milnor's Lemma 1 (p. 11) produces the submanifold structure on a *global* level set `f⁻¹(y)` of a
smooth map with regular value `y`. In practice (e.g. in Chapter 8) one often only knows that a
subset `S ⊆ M` is, near each of its points, the zero set of a submersion defined on an open set.
This file shows that such a set is again a slice submanifold, and that its tangent space at a
point is the kernel of the derivative of any such local defining function.

* `PartialDiffeomorph.ofOpens`: a partial diffeomorphism defined on an open subset `U` of `M`,
  regarded as a partial diffeomorphism defined on `M`;
* `IsSliceSubmanifold.of_locally_preimage`: local zero sets of submersions are slice
  submanifolds;
* `IsSliceSubmanifold.range_mfderiv_val_eq_ker`: their tangent space is the kernel of the
  derivative of the local defining function.

The proof of the first statement applies Milnor's Lemma 1 (`exists_sliceChart_preimage`) to the
restriction `g|_U : U → F`, for which `0` is a regular value, and transports the resulting slice
chart of `U` to `M`. The second statement is Milnor's Lemma 2: `g ∘ incl` vanishes near the
point, so the tangent space lies in the kernel, and both have dimension `dim M - dim F`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

section ofOpens

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [Nonempty N] {n : WithTop ℕ∞}

open Classical in
/-- Transport of a partial diffeomorphism defined on an open subset `U` of `M` to `M`. The source
is the image of the source under the inclusion `U → M`, the target is unchanged; outside `U` the
map takes an arbitrary (irrelevant) value. -/
def _root_.PartialDiffeomorph.ofOpens {U : TopologicalSpace.Opens M}
    (Φ : PartialDiffeomorph I J U N n) : PartialDiffeomorph I J M N n where
  toFun m := if h : m ∈ U then Φ ⟨m, h⟩ else Classical.arbitrary N
  invFun p := (Φ.invFun p : M)
  source := Subtype.val '' Φ.source
  target := Φ.target
  map_source' := by
    rintro _ ⟨u, hu, rfl⟩
    rw [dif_pos u.2]
    exact Φ.apply_mem hu
  map_target' p hp := ⟨Φ.invFun p, Φ.invFun_mem hp, rfl⟩
  left_inv' := by
    rintro _ ⟨u, hu, rfl⟩
    rw [dif_pos u.2]
    exact congrArg Subtype.val (Φ.invFun_apply hu)
  right_inv' p hp := by
    rw [dif_pos (Φ.invFun p).2]
    exact Φ.apply_invFun hp
  open_source := U.isOpen.isOpenMap_subtype_val _ Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := by
    rintro _ ⟨u, hu, rfl⟩
    refine ContMDiffAt.contMDiffWithinAt ?_
    rw [← contMDiffAt_subtype_iff]
    have h1 : (fun x : U => if h : (x : M) ∈ U then Φ ⟨x, h⟩ else Classical.arbitrary N) = Φ := by
      funext x
      rw [dif_pos x.2]
    rw [h1]
    exact Φ.contMDiffOn.contMDiffAt (Φ.open_source.mem_nhds hu)
  contMDiffOn_invFun :=
    (contMDiff_subtype_val (I := I) (U := U)).comp_contMDiffOn Φ.contMDiffOn_invFun

@[simp] theorem _root_.PartialDiffeomorph.ofOpens_source {U : TopologicalSpace.Opens M}
    (Φ : PartialDiffeomorph I J U N n) : Φ.ofOpens.source = Subtype.val '' Φ.source := rfl

@[simp] theorem _root_.PartialDiffeomorph.ofOpens_target {U : TopologicalSpace.Opens M}
    (Φ : PartialDiffeomorph I J U N n) : Φ.ofOpens.target = Φ.target := rfl

@[simp] theorem _root_.PartialDiffeomorph.ofOpens_apply {U : TopologicalSpace.Opens M}
    (Φ : PartialDiffeomorph I J U N n) (u : U) : Φ.ofOpens (u : M) = Φ u :=
  dif_pos u.2

theorem _root_.PartialDiffeomorph.ofOpens_invFun {U : TopologicalSpace.Opens M}
    (Φ : PartialDiffeomorph I J U N n) (p : N) : Φ.ofOpens.invFun p = (Φ.invFun p : M) := rfl

end ofOpens

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- **Local zero sets of submersions are slice submanifolds.** If near each of its points `x` the
set `S ⊆ M` is, inside an open neighbourhood `U` of `x`, the zero set of a map `g : M → F` which is
smooth on `U` and has surjective derivative along `S ∩ U`, then `S` is a slice submanifold
modelled on any `Z` of dimension `dim M - dim F`. -/
theorem IsSliceSubmanifold.of_locally_preimage (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    {S : Set M}
    (h : ∀ x ∈ S, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : M → F, ContMDiffOn I 𝓘(ℝ, F) ∞ g U ∧
      (∀ y ∈ U, y ∈ S ↔ g y = 0) ∧ ∀ y ∈ U, y ∈ S → Function.Surjective (mfderiv I 𝓘(ℝ, F) g y)) :
    IsSliceSubmanifold I Z F S := by
  intro x hx
  obtain ⟨U, hU, hxU, g, hg, hgS, hsurj⟩ := h x hx
  let U' : TopologicalSpace.Opens M := ⟨U, hU⟩
  -- The restriction `g' = g|_U` is smooth, with `0` as a regular value.
  have hg' : ContMDiff I 𝓘(ℝ, F) ∞ (fun u : U' => g u) := fun u =>
    contMDiffAt_subtype_iff.2 (hg.contMDiffAt (hU.mem_nhds u.2))
  have hreg : IsRegularValue I 𝓘(ℝ, F) (fun u : U' => g u) 0 := by
    intro u hu
    have hu' : (u : M) ∈ S := (hgS u u.2).2 hu
    have hdiff : MDifferentiableAt I 𝓘(ℝ, F) g u :=
      (hg.contMDiffAt (hU.mem_nhds u.2)).mdifferentiableAt (by simp)
    show Function.Surjective (mfd I 𝓘(ℝ, F) (g ∘ Subtype.val) u)
    rw [mfd_comp_subtype_val U' hdiff]
    exact hsurj u u.2 hu'
  have hx0 : (⟨x, hxU⟩ : U') ∈ (fun u : U' => g u) ⁻¹' {0} := (hgS x hxU).1 hx
  -- Milnor's Lemma 1 for `g'` gives a slice chart of `U`, which we transport to `M`.
  obtain ⟨σ', hσ', -⟩ := exists_sliceChart_preimage (Z := Z) hZ hg' hreg hx0
  have hxσ : x ∈ σ'.φ.ofOpens.source := ⟨⟨x, hxU⟩, hσ', rfl⟩
  refine ⟨⟨σ'.φ.ofOpens, x, hx, hxσ, ?_⟩, hxσ⟩
  rintro _ ⟨u, hu, rfl⟩
  rw [PartialDiffeomorph.ofOpens_apply]
  exact (hgS u u.2).trans (σ'.slice u hu)

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ Z] in
/-- **The tangent space of a local zero set is the kernel.** If `g : M → F` is smooth on an open
neighbourhood `U` of `x ∈ S`, vanishes on `S ∩ U`, and has surjective derivative at `x`, then the
tangent space of `S` at `x` (the range of the derivative of the inclusion) is the kernel of
`dg_x`. Valid for any slice-submanifold structure on `S` of dimension `dim M - dim F`. The
derivatives are written with `mfd` (i.e. `mfderiv` typed as maps between model spaces). -/
theorem IsSliceSubmanifold.range_mfderiv_val_eq_ker {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W]
    {S : Set M} (hS : IsSliceSubmanifold I Z W S) (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    (x : S) {U : Set M} (hU : IsOpen U) (hxU : x.1 ∈ U) {g : M → F}
    (hg : ContMDiffOn I 𝓘(ℝ, F) ∞ g U) (hgS : ∀ y ∈ U, y ∈ S → g y = 0)
    (hsurj : Function.Surjective (mfderiv I 𝓘(ℝ, F) g x.1)) :
    letI := hS.chartedSpace
    LinearMap.range (mfd 𝓘(ℝ, Z) I (Subtype.val : S → M) x : Z →ₗ[ℝ] E) =
      LinearMap.ker (mfd I 𝓘(ℝ, F) g x.1 : E →ₗ[ℝ] F) := by
  let := hS.chartedSpace
  have := hS.isManifold
  let Lι : Z →L[ℝ] E := mfd 𝓘(ℝ, Z) I (Subtype.val : S → M) x
  let Lg : E →L[ℝ] F := mfd I 𝓘(ℝ, F) g x.1
  have hval : MDifferentiableAt 𝓘(ℝ, Z) I (Subtype.val : S → M) x :=
    hS.contMDiff_val.mdifferentiableAt (by simp)
  have hgx : MDifferentiableAt I 𝓘(ℝ, F) g x.1 :=
    (hg.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt (by simp)
  have hcomp : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, F) (g ∘ Subtype.val) x =
      (mfderiv I 𝓘(ℝ, F) g x.1).comp (mfderiv 𝓘(ℝ, Z) I Subtype.val x) :=
    mfderiv_comp x hgx hval
  -- `g ∘ incl` vanishes near `x`, so `dg ∘ d(incl) = 0`.
  have hloc : g ∘ (Subtype.val : S → M) =ᶠ[𝓝 x] fun _ => (0 : F) := by
    filter_upwards [(hU.preimage continuous_subtype_val).mem_nhds hxU] with y hy
    exact hgS y.1 hy y.2
  have hzero : ∀ w : Z, Lg (Lι w) = 0 := by
    intro w
    have h1 : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, F) (g ∘ Subtype.val) x =
        mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, F) (fun _ : S => (0 : F)) x := hloc.mfderiv_eq
    rw [mfderiv_const, hcomp] at h1
    exact DFunLike.congr_fun h1 w
  have hle : LinearMap.range (Lι : Z →ₗ[ℝ] E) ≤ LinearMap.ker (Lg : E →ₗ[ℝ] F) := by
    rintro _ ⟨w, rfl⟩
    exact hzero w
  -- Dimension count: both subspaces have dimension `dim Z`.
  have hinj : Injective Lι := injective_mfderiv_val hS x
  have h1 : finrank ℝ (LinearMap.range (Lι : Z →ₗ[ℝ] E)) = finrank ℝ Z :=
    LinearMap.finrank_range_of_inj hinj
  have hsurj' : Surjective Lg := hsurj
  have h2 := LinearMap.finrank_range_add_finrank_ker (Lg : E →ₗ[ℝ] F)
  rw [LinearMap.range_eq_top.2 hsurj', finrank_top] at h2
  have h3 : finrank ℝ (LinearMap.ker (Lg : E →ₗ[ℝ] F)) = finrank ℝ Z := by omega
  exact Submodule.eq_of_le_of_finrank_eq hle (h1.trans h3.symm)

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ Z] in
/-- Elementwise form of `IsSliceSubmanifold.range_mfderiv_val_eq_ker`, stated with `mfderiv`: a
vector `v ∈ TMₓ` is tangent to `S` if and only if `dg_x v = 0`. -/
theorem IsSliceSubmanifold.mem_range_mfderiv_val_iff_of_local {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W]
    {S : Set M} (hS : IsSliceSubmanifold I Z W S) (hZ : finrank ℝ Z + finrank ℝ F = finrank ℝ E)
    (x : S) {U : Set M} (hU : IsOpen U) (hxU : x.1 ∈ U) {g : M → F}
    (hg : ContMDiffOn I 𝓘(ℝ, F) ∞ g U) (hgS : ∀ y ∈ U, y ∈ S → g y = 0)
    (hsurj : Function.Surjective (mfderiv I 𝓘(ℝ, F) g x.1)) (v : E) :
    letI := hS.chartedSpace
    (∃ w : Z, mfderiv 𝓘(ℝ, Z) I (Subtype.val : S → M) x w = v) ↔
      mfderiv I 𝓘(ℝ, F) g x.1 v = 0 := by
  let := hS.chartedSpace
  exact SetLike.ext_iff.1 (hS.range_mfderiv_val_eq_ker hZ x hU hxU hg hgS hsurj) v

end Milnor
