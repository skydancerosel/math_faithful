import Milnor.Chapter4.Cylinder
import Milnor.Chapter2.Brown
import Milnor.Appendix.HalfSpace

/-!
# Milnor's Homotopy Lemma (§4, p. 21)

If `f, g : M → N` are smoothly homotopic and `y` is a regular value of both, then
`#f⁻¹(y) ≡ #g⁻¹(y) (mod 2)`.

A smooth homotopy is taken here to be a smooth map `F : M × ℝ → N` with `F(·, 0) = f` and
`F(·, 1) = g`; Milnor's homotopies on `M × [0,1]` extend to such maps after the reparametrization
of the entertaining edition, Chapter 4, §1, and the extension costs nothing here because the
level sets are only ever intersected with `M × [0,1]`.

Case 1 (`y` regular for `F` too) is Lemma 4 for the cylinder plus the Appendix; Case 2 reduces to
Case 1 by the local constancy of the count and Brown's theorem.
-/

open Set Module Filter Topology
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

/-- The inclusion `x ↦ (x, c)` of `M` into `M × ℝ` and its derivative. -/
theorem hasMFDerivAt_inl (c : ℝ) (x : M) :
    HasMFDerivAt I (I.prod 𝓘(ℝ, ℝ)) (fun x : M => (x, c)) x
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) :=
  (hasMFDerivAt_id (I := I) x).prodMk (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) c x)

theorem contMDiff_inl (c : ℝ) : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ (fun x : M => (x, c)) :=
  contMDiff_id.prodMk contMDiff_const

/-- The transversality condition of Lemma 4 at an end `t = c` of the cylinder, for a homotopy
whose value `y` is regular for `F` and for the end map `F(·, c)`. -/
theorem cylinder_transversality (hdim : finrank ℝ E = finrank ℝ F)
    {F' : M × ℝ → N} (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F') {y : N}
    (hy : IsRegularValue (I.prod 𝓘(ℝ, ℝ)) J F' y) {c : ℝ}
    (hyc : IsRegularValue I J (fun x => F' (x, c)) y) {x : M} (hx : F' (x, c) = y) :
    ∃ v : E × ℝ, mfderiv (I.prod 𝓘(ℝ, ℝ)) J F' (x, c) v = 0 ∧ v.2 ≠ 0 := by
  have hsurj : Function.Surjective (mfderiv (I.prod 𝓘(ℝ, ℝ)) J F' (x, c)) := hy (x, c) hx
  let L : E × ℝ →L[ℝ] F := mfderiv (I.prod 𝓘(ℝ, ℝ)) J F' (x, c)
  have hker : LinearMap.ker (L : E × ℝ →ₗ[ℝ] F) ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker (L : E × ℝ →ₗ[ℝ] F)
    rw [hbot, finrank_bot, add_zero] at h1
    have h2 : finrank ℝ (LinearMap.range (L : E × ℝ →ₗ[ℝ] F)) ≤ finrank ℝ F :=
      Submodule.finrank_le _
    rw [Module.finrank_prod, finrank_self] at h1
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hLv : L v = 0 := LinearMap.mem_ker.1 hv
  refine ⟨v, hLv, fun hv2 => hv0 ?_⟩
  -- the derivative of `F ∘ inl` is `L ∘ P` with `P = (id, 0)`
  let P : E →L[ℝ] E × ℝ := (ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)
  have hL : HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) J F' (x, c) L :=
    (hF.mdifferentiableAt (by simp)).hasMFDerivAt
  have hP : HasMFDerivAt I (I.prod 𝓘(ℝ, ℝ)) (fun x : M => (x, c)) x P := hasMFDerivAt_inl c x
  have hcomp : HasMFDerivAt I J (F' ∘ fun x : M => (x, c)) x (L.comp P) := hL.comp x hP
  have hPv : P v.1 = v := by
    ext
    · rfl
    · simp [P, hv2]
  have hLP : (L.comp P) v.1 = 0 := by rw [ContinuousLinearMap.comp_apply, hPv]; exact hLv
  have hd : mfderiv I J (fun x => F' (x, c)) x v.1 = 0 := by
    show mfderiv I J (F' ∘ fun x : M => (x, c)) x v.1 = 0
    rw [hcomp.mfderiv]; exact hLP
  obtain ⟨e, he⟩ := (hyc x hx).isInvertible_mfderiv hdim
  have hinj : Function.Injective (mfderiv I J (fun x => F' (x, c)) x) := by
    rw [← he]; exact e.injective
  have h0 : mfderiv I J (fun x => F' (x, c)) x 0 = 0 :=
    (mfderiv I J (fun x => F' (x, c)) x).map_zero
  have h1 : v.1 = 0 := hinj (hd.trans h0.symm)
  exact Prod.ext h1 hv2

/-- **Case 1 of the homotopy lemma**: `y` regular for the homotopy as well. -/
theorem homotopy_lemma_of_isRegularValue [CompactSpace M] [T2Space M] [T2Space N]
    (hdim : finrank ℝ E = finrank ℝ F)
    {F' : M × ℝ → N} (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F') {y : N}
    (hy : IsRegularValue (I.prod 𝓘(ℝ, ℝ)) J F' y)
    (hy0 : IsRegularValue I J (fun x => F' (x, 0)) y)
    (hy1 : IsRegularValue I J (fun x => F' (x, 1)) y) :
    Even (((fun x => F' (x, 0)) ⁻¹' {y}).ncard + ((fun x => F' (x, 1)) ⁻¹' {y}).ncard) := by
  classical
  have hZ : finrank ℝ ℝ + finrank ℝ F = finrank ℝ (E × ℝ) := by
    rw [Module.finrank_prod, finrank_self]; omega
  have hZ' : finrank ℝ (⊥ : Submodule ℝ ℝ) + 1 = finrank ℝ ℝ := by
    rw [finrank_bot, finrank_self]
  haveI : Subsingleton (⊥ : Submodule ℝ ℝ) := finrank_zero_iff.1 (by rw [finrank_bot])
  have hg₀ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (Prod.snd : M × ℝ → ℝ) := contMDiff_snd
  have hg₁ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : M × ℝ => 1 - p.2) :=
    contMDiff_const.sub contMDiff_snd
  have hd₀ : ∀ p : M × ℝ, HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (Prod.snd : M × ℝ → ℝ) p
      (ContinuousLinearMap.snd ℝ E ℝ) := fun p => hasMFDerivAt_snd (I := I) (I' := 𝓘(ℝ, ℝ)) p
  have hd₁ : ∀ p : M × ℝ, HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun p : M × ℝ => 1 - p.2) p
      ((0 : E × ℝ →L[ℝ] ℝ) - ContinuousLinearMap.snd ℝ E ℝ) := fun p =>
    (hasMFDerivAt_const (I := I.prod 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (1 : ℝ) p).sub
      (hasMFDerivAt_snd (I := I) (I' := 𝓘(ℝ, ℝ)) p)
  have hreg₀ : ∀ p : M × ℝ, F' p = y → (Prod.snd : M × ℝ → ℝ) p = 0 →
      ∃ v, mfderiv (I.prod 𝓘(ℝ, ℝ)) J F' p v = 0 ∧
        mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (Prod.snd : M × ℝ → ℝ) p v ≠ 0 := by
    rintro ⟨x, t⟩ hp ht
    simp only at ht; subst ht
    obtain ⟨v, hv, hv2⟩ := cylinder_transversality hdim hF hy hy0 hp
    refine ⟨v, hv, ?_⟩
    rw [(hd₀ (x, 0)).mfderiv]
    exact hv2
  have hreg₁ : ∀ p : M × ℝ, F' p = y → 1 - p.2 = 0 →
      ∃ v, mfderiv (I.prod 𝓘(ℝ, ℝ)) J F' p v = 0 ∧
        mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun p : M × ℝ => 1 - p.2) p v ≠ 0 := by
    rintro ⟨x, t⟩ hp ht
    have ht' : t = 1 := by simp only at ht; linarith
    subst ht'
    obtain ⟨v, hv, hv2⟩ := cylinder_transversality hdim hF hy hy1 hp
    refine ⟨v, hv, ?_⟩
    rw [(hd₁ (x, 1)).mfderiv]
    intro h
    apply hv2
    have h' : (0 : ℝ) - v.2 = 0 := h
    linarith
  have hdisj : ∀ p : M × ℝ, F' p = y → ¬ ((Prod.snd : M × ℝ → ℝ) p = 0 ∧ 1 - p.2 = 0) :=
    fun p _ h => by have h1 : p.2 = 0 := h.1; have h2 := h.2; linarith
  have hX := isHalfSliceSubmanifold_levelSet_two hZ hZ' hF hy hg₀ hg₁ hreg₀ hreg₁ hdisj
  letI := (isSliceSubmanifold_preimage hZ hF hy).chartedSpace
  haveI := (isSliceSubmanifold_preimage hZ hF hy).isManifold
  -- compactness
  have hcompact : IsCompact {q : F' ⁻¹' {y} | 0 ≤ (Prod.snd : M × ℝ → ℝ) q.1 ∧ 0 ≤ 1 - q.1.2} := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    have himg : Subtype.val '' {q : F' ⁻¹' {y} | 0 ≤ (Prod.snd : M × ℝ → ℝ) q.1 ∧ 0 ≤ 1 - q.1.2} =
        (univ ×ˢ Icc (0 : ℝ) 1) ∩ F' ⁻¹' {y} := by
      ext p; constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨mem_univ _, hq.1, by linarith [hq.2]⟩, q.2⟩
      · rintro ⟨⟨-, h1, h2⟩, hp⟩
        exact ⟨⟨p, hp⟩, ⟨h1, by linarith⟩, rfl⟩
    rw [himg]
    exact (isCompact_univ.prod isCompact_Icc).inter_right
      (isClosed_singleton.preimage hF.continuous)
  have hBX : {q : F' ⁻¹' {y} | (Prod.snd : M × ℝ → ℝ) q.1 = 0 ∨ 1 - q.1.2 = 0} ⊆
      {q : F' ⁻¹' {y} | 0 ≤ (Prod.snd : M × ℝ → ℝ) q.1 ∧ 0 ≤ 1 - q.1.2} := by
    rintro q (h | h)
    · have h' : q.1.2 = 0 := h
      exact ⟨le_of_eq h'.symm, by linarith⟩
    · have h' : 1 - q.1.2 = 0 := h
      exact ⟨by linarith, le_of_eq h'.symm⟩
  obtain ⟨-, heven⟩ := IsHalfSliceSubmanifold.even_ncard_boundary hX hcompact hBX
  -- the boundary is the disjoint union of the two ends
  set A₀ := (fun x : M => (x, (0 : ℝ))) '' ((fun x => F' (x, 0)) ⁻¹' {y}) with hA₀
  set A₁ := (fun x : M => (x, (1 : ℝ))) '' ((fun x => F' (x, 1)) ⁻¹' {y}) with hA₁
  have himg : Subtype.val '' {q : F' ⁻¹' {y} | (Prod.snd : M × ℝ → ℝ) q.1 = 0 ∨ 1 - q.1.2 = 0} =
      A₀ ∪ A₁ := by
    ext p; constructor
    · rintro ⟨q, hq, rfl⟩
      rcases hq with h | h
      · left
        have h' : q.1.2 = 0 := h
        refine ⟨q.1.1, ?_, ?_⟩
        · show F' (q.1.1, 0) = y
          have := q.2; rw [← h']; exact this
        · exact Prod.ext rfl h'.symm
      · right
        have h' : 1 - q.1.2 = 0 := h
        have h1 : q.1.2 = 1 := by linarith
        refine ⟨q.1.1, ?_, ?_⟩
        · show F' (q.1.1, 1) = y
          have := q.2; rw [← h1]; exact this
        · exact Prod.ext rfl h1.symm
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨⟨(x, 0), hx⟩, Or.inl rfl, rfl⟩
      · exact ⟨⟨(x, 1), hx⟩, Or.inr (by simp), rfl⟩
  have hinj₀ : Function.Injective (fun x : M => (x, (0 : ℝ))) := fun a b h => (Prod.mk.inj h).1
  have hinj₁ : Function.Injective (fun x : M => (x, (1 : ℝ))) := fun a b h => (Prod.mk.inj h).1
  have hf₀ : ContMDiff I J ∞ (fun x => F' (x, 0)) := hF.comp (contMDiff_inl 0)
  have hf₁ : ContMDiff I J ∞ (fun x => F' (x, 1)) := hF.comp (contMDiff_inl 1)
  have hfin₀ := hy0.finite_preimage hdim hf₀ (by simp)
  have hfin₁ := hy1.finite_preimage hdim hf₁ (by simp)
  have hdisjA : Disjoint A₀ A₁ := by
    rw [Set.disjoint_left]
    rintro _ ⟨x, -, rfl⟩ ⟨x', -, h⟩
    have := (Prod.mk.inj h).2
    norm_num at this
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg,
    Set.ncard_union_eq hdisjA (hfin₀.image _) (hfin₁.image _),
    Set.ncard_image_of_injective _ hinj₀, Set.ncard_image_of_injective _ hinj₁] at heven
  exact heven

/-- **Milnor's Homotopy Lemma** (§4, p. 21). -/
theorem homotopy_lemma [CompactSpace M] [T2Space M] [SecondCountableTopology M] [T2Space N]
    (hdim : finrank ℝ E = finrank ℝ F)
    {F' : M × ℝ → N} (hF : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F') {y : N}
    (hy0 : IsRegularValue I J (fun x => F' (x, 0)) y)
    (hy1 : IsRegularValue I J (fun x => F' (x, 1)) y) :
    Even (((fun x => F' (x, 0)) ⁻¹' {y}).ncard + ((fun x => F' (x, 1)) ⁻¹' {y}).ncard) := by
  have hf₀ : ContMDiff I J ∞ (fun x => F' (x, 0)) := hF.comp (contMDiff_inl 0)
  have hf₁ : ContMDiff I J ∞ (fun x => F' (x, 1)) := hF.comp (contMDiff_inl 1)
  have h0 := hy0.eventually_isRegularValue_and_ncard hdim hf₀ (by simp)
  have h1 := hy1.eventually_isRegularValue_and_ncard hdim hf₁ (by simp)
  obtain ⟨U, hUsub, hUopen, hyU⟩ := eventually_nhds_iff.1 (h0.and h1)
  obtain ⟨y', hy'reg, hy'U⟩ := (dense_regularValues hF).exists_mem_open hUopen ⟨y, hyU⟩
  obtain ⟨⟨hr0, hc0⟩, hr1, hc1⟩ := hUsub y' hy'U
  have := homotopy_lemma_of_isRegularValue hdim hF hy'reg hr0 hr1
  rwa [hc0, hc1] at this

end Milnor
