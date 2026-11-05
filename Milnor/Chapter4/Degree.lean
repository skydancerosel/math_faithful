import Milnor.Chapter4.Homotopy
import Milnor.Chapter4.Homogeneity

/-!
# The degree modulo 2 (Milnor, chapter 4)

* **Theorem B**: for `f : M → N` smooth, `M` compact without boundary, `N` connected without
  boundary, same dimension, the parity of `#f⁻¹(y)` is the same for all regular values `y`.
  Proof: move `y` to `z` by a diffeomorphism `h` isotopic to the identity (Homogeneity Lemma);
  `z` is a regular value of `h ∘ f`, which is homotopic to `f`, so the Homotopy Lemma applies.
* `degMod2 I J f ∈ ZMod 2` is this common parity.
* **Theorem A**: smoothly homotopic maps have the same degree.
* If `f` is not surjective its degree is `0`.
-/

open Set Module Filter Topology Function
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- The derivative of a diffeomorphism is surjective (it has a left inverse, and the two tangent
spaces have the same dimension). -/
theorem surjective_mfderiv_diffeomorph (h : N ≃ₘ⟮J, J⟯ N) (y : N) :
    Surjective (mfderiv J J h y) := by
  let L₂ : F →L[ℝ] F := mfderiv J J h y
  let L₁ : F →L[ℝ] F := mfderiv J J h.symm (h y)
  have hL₂ : HasMFDerivAt J J h y L₂ := (h.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  have hL₁ : HasMFDerivAt J J h.symm (h y) L₁ :=
    (h.symm.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp : HasMFDerivAt J J (h.symm ∘ h) y (L₁.comp L₂) := hL₁.comp y hL₂
  have hid : HasMFDerivAt J J (h.symm ∘ h) y (ContinuousLinearMap.id ℝ F) := by
    have : (h.symm ∘ h : N → N) = id := funext h.symm_apply_apply
    rw [this]; exact hasMFDerivAt_id (I := J) y
  have heq : L₁.comp L₂ = ContinuousLinearMap.id ℝ F := hasMFDerivAt_unique hcomp hid
  have hinj : Injective L₂ := by
    intro a b hab
    have ha := DFunLike.congr_fun heq a
    have hb := DFunLike.congr_fun heq b
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at ha hb
    rw [← ha, ← hb, hab]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (L₂ : F →ₗ[ℝ] F)) rfl).1 hinj

/-- Regular values are preserved by postcomposition with a diffeomorphism. -/
theorem IsRegularValue.diffeomorph_comp {f : M → N} (hf : ContMDiff I J ∞ f)
    (h : N ≃ₘ⟮J, J⟯ N) {y : N} (hy : IsRegularValue I J f y) :
    IsRegularValue I J (fun x => h (f x)) (h y) := by
  intro x hx
  have hfx : f x = y := h.injective hx
  have hsurj_f : Surjective (mfderiv I J f x) := hy x hfx
  have hsurj_h : Surjective (mfderiv J J h (f x)) := surjective_mfderiv_diffeomorph h (f x)
  show Surjective (mfderiv I J (h ∘ f) x)
  rw [mfderiv_comp x (h.contMDiff.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  intro w
  obtain ⟨v, hv⟩ := hsurj_h w
  obtain ⟨u, hu⟩ := hsurj_f v
  refine ⟨u, ?_⟩
  show mfderiv J J h (f x) (mfderiv I J f x u) = w
  rw [hu, hv]

theorem preimage_diffeomorph_comp {f : M → N} (h : N ≃ₘ⟮J, J⟯ N) {y z : N} (hyz : h y = z) :
    (fun x => h (f x)) ⁻¹' {z} = f ⁻¹' {y} := by
  ext x
  simp only [mem_preimage, mem_singleton_iff, ← hyz]
  exact h.injective.eq_iff

/-- **Theorem B** (Milnor p. 21): the parity of `#f⁻¹(y)` does not depend on the regular value
`y`, for `M` compact and `N` connected (both without boundary, same dimension). -/
theorem even_ncard_add_ncard_of_isRegularValue [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] [T2Space N] [PreconnectedSpace N]
    (hdim : finrank ℝ E = finrank ℝ F) {f : M → N} (hf : ContMDiff I J ∞ f) {y z : N}
    (hy : IsRegularValue I J f y) (hz : IsRegularValue I J f z) :
    Even ((f ⁻¹' {y}).ncard + (f ⁻¹' {z}).ncard) := by
  obtain ⟨h, Hm, hH, h0, h1, hyz, -⟩ := isotopic_of_preconnected (J := J) y z
  let F' : M × ℝ → N := fun q => Hm (f q.1, q.2)
  have hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F' :=
    hH.comp ((hf.comp contMDiff_fst).prodMk contMDiff_snd)
  have hF0 : (fun x => F' (x, 0)) = f := funext fun x => h0 (f x)
  have hF1 : (fun x => F' (x, 1)) = fun x => h (f x) := funext fun x => h1 (f x)
  have hz1 : IsRegularValue I J (fun x => F' (x, 1)) z := by
    rw [hF1]
    have := hy.diffeomorph_comp hf h
    rwa [hyz] at this
  have hz0 : IsRegularValue I J (fun x => F' (x, 0)) z := by rw [hF0]; exact hz
  have := homotopy_lemma hdim hF hz0 hz1
  rw [hF0, hF1, preimage_diffeomorph_comp h hyz, add_comm] at this
  exact this

theorem natCast_zmod_two_eq_of_even_add {a b : ℕ} (h : Even (a + b)) : (a : ZMod 2) = b := by
  rw [ZMod.natCast_eq_natCast_iff']
  obtain ⟨r, hr⟩ := h
  omega

open Classical in
/-- The **degree modulo 2** of `f : M → N`: the parity of `#f⁻¹(y)` for a regular value `y`
(any regular value gives the same answer by Theorem B, and regular values exist by Brown's
theorem when `N` is nonempty).  Defined as `0` if there is no regular value at all. -/
def degMod2 (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G) (f : M → N) : ZMod 2 :=
  if h : ∃ y, IsRegularValue I J f y then ((f ⁻¹' {Classical.choose h}).ncard : ZMod 2) else 0

/-- The degree is computed by any regular value. -/
theorem degMod2_eq [CompactSpace M] [T2Space M] [SecondCountableTopology M] [T2Space N]
    [PreconnectedSpace N] (hdim : finrank ℝ E = finrank ℝ F) {f : M → N}
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) :
    degMod2 I J f = ((f ⁻¹' {y}).ncard : ZMod 2) := by
  have hex : ∃ y, IsRegularValue I J f y := ⟨y, hy⟩
  rw [degMod2, dif_pos hex]
  exact natCast_zmod_two_eq_of_even_add
    (even_ncard_add_ncard_of_isRegularValue hdim hf (Classical.choose_spec hex) hy)

/-- Regular values of a smooth map from a compact manifold form an open set. -/
theorem isOpen_isRegularValue [CompactSpace M] [T2Space M] [T2Space N]
    (hdim : finrank ℝ E = finrank ℝ F) {f : M → N} (hf : ContMDiff I J ∞ f) :
    IsOpen {y | IsRegularValue I J f y} := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  exact (hy.eventually_isRegularValue_and_ncard hdim hf (by simp)).mono fun _ h => h.1

/-- Two smooth maps from a compact manifold to a nonempty manifold have a common regular value. -/
theorem exists_common_isRegularValue [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [T2Space N] [Nonempty N] (hdim : finrank ℝ E = finrank ℝ F) {f g : M → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g) :
    ∃ y, IsRegularValue I J f y ∧ IsRegularValue I J g y := by
  obtain ⟨y₀, hy₀⟩ := (dense_regularValues hf).nonempty
  obtain ⟨y, hyg, hyf⟩ := (dense_regularValues hg).exists_mem_open (isOpen_isRegularValue hdim hf)
    ⟨y₀, hy₀⟩
  exact ⟨y, hyf, hyg⟩

/-- **Theorem A** (Milnor p. 21): smoothly homotopic maps have the same degree modulo 2. -/
theorem degMod2_eq_of_homotopy [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [T2Space N] [PreconnectedSpace N] (hdim : finrank ℝ E = finrank ℝ F)
    {F' : M × ℝ → N} (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F') :
    degMod2 I J (fun x => F' (x, 0)) = degMod2 I J (fun x => F' (x, 1)) := by
  by_cases hN : Nonempty N
  · have hf₀ : ContMDiff I J ∞ (fun x => F' (x, 0)) := hF.comp (contMDiff_inl 0)
    have hf₁ : ContMDiff I J ∞ (fun x => F' (x, 1)) := hF.comp (contMDiff_inl 1)
    obtain ⟨y, hy0, hy1⟩ := exists_common_isRegularValue hdim hf₀ hf₁
    rw [degMod2_eq hdim hf₀ hy0, degMod2_eq hdim hf₁ hy1]
    exact natCast_zmod_two_eq_of_even_add (homotopy_lemma hdim hF hy0 hy1)
  · have h : ∀ f : M → N, ¬ ∃ y, IsRegularValue I J f y := fun f ⟨y, _⟩ => hN ⟨y⟩
    simp only [degMod2, dif_neg (h _)]

/-- A point outside the range is a regular value with empty preimage. -/
theorem degMod2_eq_zero_of_notMem_range [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [T2Space N] [PreconnectedSpace N] (hdim : finrank ℝ E = finrank ℝ F) {f : M → N}
    (hf : ContMDiff I J ∞ f) {y : N} (hy : y ∉ range f) : degMod2 I J f = 0 := by
  have hreg : IsRegularValue I J f y := fun x hx => (hy ⟨x, hx⟩).elim
  rw [degMod2_eq hdim hf hreg]
  have : f ⁻¹' {y} = ∅ := by
    ext x; simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    exact fun hx => hy ⟨x, hx⟩
  rw [this, Set.ncard_empty, Nat.cast_zero]

/-- **Corollary** (Milnor p. 21): a map of nonzero degree is surjective. -/
theorem surjective_of_degMod2_ne_zero [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [T2Space N] [PreconnectedSpace N] (hdim : finrank ℝ E = finrank ℝ F) {f : M → N}
    (hf : ContMDiff I J ∞ f) (hdeg : degMod2 I J f ≠ 0) : Surjective f := by
  intro y
  by_contra hy
  exact hdeg (degMod2_eq_zero_of_notMem_range hdim hf hy)

end Milnor
