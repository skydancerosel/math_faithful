import Milnor.Chapter6.Radial
import Milnor.Chapter6.DetSign
import Milnor.Chapter6.Extend

/-!
# Tools for Milnor's Lemma 1 (§6): invariance of the index under diffeomorphisms

* `exists_region_fun`: a compact region `X = {G₀ ≥ 0} ∩ W` is `{G ≥ 0}` for a globally smooth
  `G` agreeing with `G₀` near `X`;
* `signAt_aff_sphere`: the map `u ↦ z + εu` from `Sⁿ` to the sphere of radius `ε` about `z`
  has sign `+1`;
* `nv0_smul`: normalization is invariant under positive rescaling;
* transfer of regular values along maps with surjective or invertible derivatives.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

section region

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A region function.**  Given an open `W`, a compact `X ⊆ W`, and `G₀` smooth on `W` with
`X = {x ∈ W | 0 ≤ G₀ x}`, there is a smooth `G` on `E` with `{G ≥ 0} = X` and `G = G₀` near
`X`. -/
theorem exists_region_fun {W : Set E} (hW : IsOpen W) {X : Set E} (hX : IsCompact X) (hXW : X ⊆ W)
    {G₀ : E → ℝ} (hG₀ : ContDiffOn ℝ ∞ G₀ W) (hXG : ∀ x ∈ W, x ∈ X ↔ 0 ≤ G₀ x) :
    ∃ G : E → ℝ, ContDiff ℝ ∞ G ∧ {x | 0 ≤ G x} = X ∧ ∀ᶠ x in 𝓝ˢ X, G x = G₀ x := by
  classical
  obtain ⟨χ, hχ0, hχ1, hχ01⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E) (n := ⊤)
    hW.isClosed_compl hX.isClosed (disjoint_compl_left_iff.2 hXW)
  set G : E → ℝ := fun x => if x ∈ W then χ x * G₀ x + (χ x - 1) else -1 with hG
  have hG1 : ∀ᶠ x in 𝓝ˢ X, G x = G₀ x := by
    filter_upwards [hW.mem_nhdsSet.2 hXW, hχ1] with x hx hχ
    simp only [hG, if_pos hx, hχ, one_mul, sub_self, add_zero]
  refine ⟨G, ?_, ?_, hG1⟩
  · rw [← contMDiff_iff_contDiff]
    intro x
    by_cases hx : x ∈ W
    · have h1 : G =ᶠ[𝓝 x] fun x => χ x * G₀ x + (χ x - 1) := by
        filter_upwards [hW.mem_nhds hx] with y hy
        simp only [hG, if_pos hy]
      refine ContMDiffAt.congr_of_eventuallyEq ?_ h1
      have hG₀' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ G₀ x := by
        rw [contMDiffAt_iff_contDiffAt]; exact hG₀.contDiffAt (hW.mem_nhds hx)
      exact (χ.contMDiff.contMDiffAt.mul hG₀').add (χ.contMDiff.contMDiffAt.sub contMDiffAt_const)
    · have h1 : G =ᶠ[𝓝 x] fun _ => -1 := by
        filter_upwards [eventually_nhdsSet_iff_forall.1 hχ0 x hx] with y hy
        by_cases hyW : y ∈ W
        · simp only [hG, if_pos hyW, hy, zero_mul, zero_add, zero_sub]
        · simp only [hG, if_neg hyW]
      exact ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const h1
  · ext x
    simp only [mem_setOf_eq]
    constructor
    · intro hx
      have hxW : x ∈ W := by
        by_contra h
        simp only [hG, if_neg h] at hx
        linarith
      simp only [hG, if_pos hxW] at hx
      rw [hXG x hxW]
      by_contra hneg
      push_neg at hneg
      have hχ := hχ01 x
      have h1 : χ x * G₀ x ≤ 0 := by nlinarith [hχ.1, hneg]
      have h2 : χ x = 1 := le_antisymm hχ.2 (by linarith)
      rw [h2, one_mul] at hx
      linarith
    · intro hx
      rw [hG1.self_of_nhdsSet x hx]
      exact (hXG x (hXW hx)).1 hx

end region

section regular

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {G'' : Type*} [TopologicalSpace G''] {K : ModelWithCorners ℝ F' G''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace G'' P] [IsManifold K ∞ P]

/-- A regular value of `f` is a regular value of `f ∘ φ` when `dφ` is surjective everywhere. -/
theorem IsRegularValue.comp_of_surjective {f : N → P} {φ : M → N}
    (hf : ∀ y, MDifferentiableAt J K f y) (hφ : ∀ x, MDifferentiableAt I J φ x)
    (hφs : ∀ x, Surjective (mfd I J φ x)) {y : P} (hy : IsRegularValue J K f y) :
    IsRegularValue I K (fun x => f (φ x)) y := by
  intro x hx
  have hchain : mfd I K (fun x => f (φ x)) x = (mfd J K f (φ x)).comp (mfd I J φ x) :=
    HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := J) (J := K) (hf (φ x))).comp x
      (hasMFDerivAt_mfd (I := I) (J := J) (hφ x)))
  show Surjective (mfd I K (fun x => f (φ x)) x)
  rw [hchain]
  exact (hy (φ x) hx).comp (hφs x)

/-- If `y` is a regular value of `h ∘ s` and `dh` is injective everywhere, then `h⁻¹ y`
(any preimage) is a regular value of `s`. -/
theorem IsRegularValue.of_comp_injective {h : N → P} {s : M → N}
    (hh : ∀ y, MDifferentiableAt J K h y) (hs : ∀ x, MDifferentiableAt I J s x)
    (hhi : ∀ y, Injective (mfd J K h y)) (hhinj : Injective h) {y : N}
    (hy : IsRegularValue I K (fun x => h (s x)) (h y)) : IsRegularValue I J s y := by
  intro x hx
  have hx' : h (s x) = h y := by rw [hx]
  have h1 := hy x hx'
  have hchain : mfd I K (fun x => h (s x)) x = (mfd J K h (s x)).comp (mfd I J s x) :=
    HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := J) (J := K) (hh (s x))).comp x
      (hasMFDerivAt_mfd (I := I) (J := J) (hs x)))
  show Surjective (mfd I J s x)
  have h2 : Surjective ((mfd J K h (s x)).comp (mfd I J s x)) := by rw [← hchain]; exact h1
  intro w
  obtain ⟨u, hu⟩ := h2 (mfd J K h (s x) w)
  exact ⟨u, hhi (s x) hu⟩

end regular

namespace Sphere

variable {n : ℕ}

theorem nv0_smul {c : ℝ} (hc : 0 < c) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    nv0 (c • y) = nv0 y := by
  by_cases hy : y = 0
  · simp [hy]
  · have hcy : c • y ≠ 0 := smul_ne_zero hc.ne' hy
    apply Subtype.ext
    rw [nv0_val hcy, nv0_val hy]
    simp only [normalize, norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_inv, smul_smul]
    congr 1
    field_simp

/-- The sphere-affine map `ψ : u ↦ z + εu`, as a map `Sⁿ → S_ε(z) = Gsph⁻¹(0)`. -/
def ψaff (z : EuclideanSpace ℝ (Fin (n + 1))) {ε : ℝ} (hε : 0 < ε) (u : Sph n) :
    (Gsph z ε) ⁻¹' {0} :=
  ⟨aff z ε u.1, by show Gsph z ε (aff z ε u.1) = 0; rw [Gsph_aff hε.ne']; exact u.2⟩

theorem ψaff_bijective (z : EuclideanSpace ℝ (Fin (n + 1))) {ε : ℝ} (hε : 0 < ε) :
    Bijective (ψaff z hε) := by
  constructor
  · intro u u' h
    have := congrArg Subtype.val h
    simp only [ψaff, aff, add_right_inj] at this
    exact Subtype.ext (smul_right_injective _ hε.ne' this)
  · intro q
    have hq : sphG (ε⁻¹ • (q.1 - z)) = 0 := q.2
    refine ⟨⟨ε⁻¹ • (q.1 - z), hq⟩, Subtype.ext ?_⟩
    show z + ε • (ε⁻¹ • (q.1 - z)) = q.1
    rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul, add_sub_cancel]

theorem contMDiff_ψaff (z : EuclideanSpace ℝ (Fin (n + 1))) {ε : ℝ} (hε : 0 < ε) :
    letI := (isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ)
      (contMDiff_Gsph z ε) (isRegularValue_Gsph hε)).chartedSpace
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (ψaff z hε) :=
  (isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ)
    (contMDiff_Gsph z ε) (isRegularValue_Gsph hε)).contMDiff_codRestrict
    ((contMDiff_aff z ε).comp contMDiff_val) _

/-- **The sign of `ψ` is `+1`.** -/
theorem signAt_ψaff (z : EuclideanSpace ℝ (Fin (n + 1))) {ε : ℝ} (hε : 0 < ε) (u : Sph n) :
    letI := (isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ)
      (contMDiff_Gsph z ε) (isRegularValue_Gsph hε)).chartedSpace
    signAt (sphOr n) (levelOrientM hE hZ (Orient.const (finBasisOfFinrankEq ℝ _ hE).orientation)
      (contMDiff_Gsph z ε) (isRegularValue_Gsph hε)) (ψaff z hε) u = 1 := by
  letI := (isSliceSubmanifold_preimage (Z := EuclideanSpace ℝ (Fin n)) (finrank_Z_add hE hZ)
    (contMDiff_Gsph z ε) (isRegularValue_Gsph hε)).chartedSpace
  set a₀ := (finBasisOfFinrankEq ℝ (EuclideanSpace ℝ (Fin (n + 1))) hE).orientation with ha₀
  set oE : Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin (n + 1))) (n + 1) :=
    Orient.const a₀ with hoE
  have hsphOr : sphOr n = levelOrientM hE hZ oE contMDiff_sphG isRegularValue_sphG :=
    levelOrient_eq_levelOrientM hE hZ a₀ contMDiff_sphG isRegularValue_sphG
  rw [hsphOr]
  have hmem : ∀ x, sphG x = 0 → Gsph z ε (aff z ε x) = 0 := fun x hx => by
    rw [Gsph_aff hε.ne']; exact hx
  have hdc : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) (Gsph z ε) (aff z ε u.1)).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (aff z ε) u.1) =
      (1 : ℝ) • mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, ℝ) sphG u.1 := by
    rw [one_smul]
    have h1 := HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      (J := 𝓘(ℝ, ℝ)) ((contMDiff_Gsph z ε).mdifferentiableAt (by simp) :
        MDifferentiableAt _ _ (Gsph z ε) (aff z ε u.1))).comp u.1
      (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
        (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) ((contMDiff_aff z ε).mdifferentiableAt (by simp))))
    have h2 : Gsph z ε ∘ aff z ε = sphG := funext fun x => Gsph_aff hε.ne' x
    rw [h2] at h1
    exact h1.symm
  have := signAt_levelOrientM_map hE hZ oE oE contMDiff_sphG isRegularValue_sphG (contMDiff_Gsph z ε)
    (isRegularValue_Gsph hε) (Φ := aff z ε) hmem ((contMDiff_aff z ε).comp contMDiff_val) u
    ((contMDiff_aff z ε).mdifferentiableAt (by simp)) ⟨1, one_pos, hdc⟩
  rw [signAt_aff hε a₀ u.1] at this
  exact this

end Sphere

end Milnor
