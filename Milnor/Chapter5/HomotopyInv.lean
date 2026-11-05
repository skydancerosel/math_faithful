import Milnor.Chapter5.LemmaOne
import Milnor.Chapter4.Homotopy

/-!
# Theorem A (chapter 5): homotopy invariance of the degree

If `F : M × ℝ → N` is a smooth homotopy from `f₀ = F(·,0)` to `f₁ = F(·,1)` and `y` is a
regular value of both, then `degAt f₀ y = degAt f₁ y` (Milnor p. 28).  This is Lemma 1 applied
to the cylinder `X = M × [0,1] = {g ≥ 0}` with `g(x, t) = t(1 - t)`: the sign of `(F, g)` at
`(x, 0)` is `sign df₀` and at `(x, 1)` it is `- sign df₁`.
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
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] {n : ℕ}

/-- The derivative of `Φ : M × ℝ → N` at `(x, c)` in block form. -/
theorem mfd_prod_apply {Φ : M × ℝ → N} (hΦ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ Φ) (x : M) (c : ℝ)
    (v : E) (t : ℝ) :
    mfd (I.prod 𝓘(ℝ, ℝ)) J Φ (x, c) (v, t) =
      mfd I J (fun x => Φ (x, c)) x v + t • mfd (I.prod 𝓘(ℝ, ℝ)) J Φ (x, c) (0, 1) := by
  have h1 : mfd I J (fun x => Φ (x, c)) x = (mfd (I.prod 𝓘(ℝ, ℝ)) J Φ (x, c)).comp
      ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) :=
    HasMFDerivAt.mfd_eq ((hasMFDerivAt_mfd (I := I.prod 𝓘(ℝ, ℝ)) (J := J)
      (hΦ.mdifferentiableAt (by simp))).comp x (hasMFDerivAt_inl c x))
  rw [h1]
  change mfd (I.prod 𝓘(ℝ, ℝ)) J Φ (x, c) (v, t) =
    mfd (I.prod 𝓘(ℝ, ℝ)) J Φ (x, c) (v, 0) + t • mfd (I.prod 𝓘(ℝ, ℝ)) J Φ (x, c) (0, 1)
  rw [← map_smul, ← map_add]
  congr 1
  ext <;> simp

/-- The derivative of the cylinder function `g(x, t) = t (1 - t)`. -/
theorem mfd_cyl (p : M × ℝ) (w : E × ℝ) :
    mfd (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (fun p : M × ℝ => p.2 * (1 - p.2)) p w = (1 - 2 * p.2) * w.2 := by
  have hφ : HasDerivAt (fun t : ℝ => t * (1 - t)) (1 - 2 * p.2) p.2 := by
    have := (hasDerivAt_id p.2).mul ((hasDerivAt_const p.2 (1 : ℝ)).sub (hasDerivAt_id p.2))
    exact this.congr_deriv (by simp only [Pi.sub_apply, id_eq]; ring)
  have h1 := hφ.hasFDerivAt.hasMFDerivAt.comp p (hasMFDerivAt_snd (I := I) (I' := 𝓘(ℝ, ℝ)) p)
  have h2 := HasMFDerivAt.mfd_eq h1
  show mfd (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ((fun t : ℝ => t * (1 - t)) ∘ Prod.snd) p w = _
  rw [h2]
  change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (1 - 2 * p.2)) w.2 = _
  simp [mul_comm]

/-- **Theorem A, case of a regular value of the homotopy.** -/
theorem degAt_eq_of_homotopy_of_isRegularValue [CompactSpace M] [T2Space M] [T2Space N]
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n) (oN : Orient J N n)
    {F' : M × ℝ → N} (hF' : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F') {y : N}
    (hy : IsRegularValue (I.prod 𝓘(ℝ, ℝ)) J F' y)
    (hy0 : IsRegularValue I J (fun x => F' (x, 0)) y)
    (hy1 : IsRegularValue I J (fun x => F' (x, 1)) y) :
    degAt oM oN (fun x => F' (x, 0)) y = degAt oM oN (fun x => F' (x, 1)) y := by
  classical
  set g : M × ℝ → ℝ := fun p => p.2 * (1 - p.2) with hg_def
  have hg : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ g :=
    contMDiff_snd.mul (contMDiff_const.sub contMDiff_snd)
  have hE' : finrank ℝ (E × ℝ) = n + 1 := finrank_prod_real hE
  have hdim : finrank ℝ E = finrank ℝ F := hE.trans hF.symm
  have hreg : ∀ p, F' p = y → g p = 0 → ∃ v, mfd (I.prod 𝓘(ℝ, ℝ)) J F' p v = 0 ∧
      mfd (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) g p v ≠ 0 := by
    rintro ⟨x, c⟩ hp hg0
    have hc : c = 0 ∨ c = 1 := by
      simp only [g] at hg0
      rcases mul_eq_zero.1 hg0 with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    have hyc : IsRegularValue I J (fun x => F' (x, c)) y := by
      rcases hc with rfl | rfl <;> assumption
    obtain ⟨v, hv, hv2⟩ := cylinder_transversality hdim hF' hy hyc hp
    refine ⟨v, hv, ?_⟩
    simp only [g]
    rw [mfd_cyl]
    rcases hc with rfl | rfl <;> (intro h; apply hv2; linarith)
  have hX : IsCompact {p : M × ℝ | F' p = y ∧ 0 ≤ g p} := by
    have : {p : M × ℝ | F' p = y ∧ 0 ≤ g p} = (univ ×ˢ Icc (0 : ℝ) 1) ∩ F' ⁻¹' {y} := by
      ext ⟨x, t⟩
      simp only [mem_setOf_eq, mem_inter_iff, mem_prod, mem_univ, true_and, mem_Icc,
        mem_preimage, mem_singleton_iff, g]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨?_, ?_⟩, h1⟩
        · by_contra h; push_neg at h; nlinarith
        · by_contra h; push_neg at h; nlinarith
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h3, by nlinarith⟩
    rw [this]
    exact (isCompact_univ.prod isCompact_Icc).inter_right
      (isClosed_singleton.preimage hF'.continuous)
  have hL := lemmaOne_ambient hE' hF (oM.prodReal hE) oN hF' hy hg hreg hX
  -- the boundary set splits into the two ends
  set A₀ : Set (M × ℝ) := (fun x => (x, (0 : ℝ))) '' ((fun x => F' (x, 0)) ⁻¹' {y}) with hA₀
  set A₁ : Set (M × ℝ) := (fun x => (x, (1 : ℝ))) '' ((fun x => F' (x, 1)) ⁻¹' {y}) with hA₁
  have hsplit : {p : M × ℝ | F' p = y ∧ g p = 0} = A₀ ∪ A₁ := by
    ext ⟨x, t⟩
    simp only [mem_setOf_eq, mem_union, A₀, A₁, mem_image, mem_preimage, mem_singleton_iff,
      Prod.mk.injEq, g]
    constructor
    · rintro ⟨h1, h2⟩
      rcases mul_eq_zero.1 h2 with h | h
      · left; exact ⟨x, by rw [← h]; exact h1, rfl, h.symm⟩
      · right
        have ht : t = 1 := by linarith
        exact ⟨x, by rw [← ht]; exact h1, rfl, ht.symm⟩
    · rintro (⟨x', hx', rfl, rfl⟩ | ⟨x', hx', rfl, rfl⟩)
      · exact ⟨hx', by ring⟩
      · exact ⟨hx', by ring⟩
  have hdisj : Disjoint A₀ A₁ := by
    rw [Set.disjoint_left]
    rintro p ⟨x, -, rfl⟩ ⟨x', -, h⟩
    simp at h
  have hf₀ : ContMDiff I J ∞ (fun x => F' (x, 0)) := hF'.comp (contMDiff_inl 0)
  have hf₁ : ContMDiff I J ∞ (fun x => F' (x, 1)) := hF'.comp (contMDiff_inl 1)
  have hfin0 : ((fun x => F' (x, 0)) ⁻¹' {y}).Finite := hy0.finite_preimage hdim hf₀ (by simp)
  have hfin1 : ((fun x => F' (x, 1)) ⁻¹' {y}).Finite := hy1.finite_preimage hdim hf₁ (by simp)
  have hinj0 : InjOn (fun x : M => (x, (0 : ℝ))) ((fun x => F' (x, 0)) ⁻¹' {y}) :=
    fun a _ b _ h => (Prod.mk.inj h).1
  have hinj1 : InjOn (fun x : M => (x, (1 : ℝ))) ((fun x => F' (x, 1)) ⁻¹' {y}) :=
    fun a _ b _ h => (Prod.mk.inj h).1
  rw [hsplit, finsum_mem_union hdisj (hfin0.image _) (hfin1.image _), finsum_mem_image hinj0,
    finsum_mem_image hinj1] at hL
  -- the signs at the two ends
  have hs : ∀ (c : ℝ) (x : M), signAt (oM.prodReal hE) (oN.prodReal hF) (pairMap F' g) (x, c) =
      signAt oM oN (fun x => F' (x, c)) x * sgn (1 - 2 * c) := by
    intro c x
    rw [signAt_prodReal hE hF oM oN (A := mfd I J (fun x => F' (x, c)) x)
      (w := mfd (I.prod 𝓘(ℝ, ℝ)) J F' (x, c) (0, 1)) (c := 1 - 2 * c) ?_]
    · rfl
    · intro v t
      rw [mfd_pairMap (hF'.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))]
      show (mfd (I.prod 𝓘(ℝ, ℝ)) J F' (x, c) (v, t), mfd (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) g (x, c) (v, t)) = _
      rw [mfd_prod_apply hF', mfd_cyl]
  have hs0 : ∀ x, signAt (oM.prodReal hE) (oN.prodReal hF) (pairMap F' g) (x, 0) =
      signAt oM oN (fun x => F' (x, 0)) x := fun x => by
    rw [hs 0 x]; norm_num [sgn_one]
  have hs1 : ∀ x, signAt (oM.prodReal hE) (oN.prodReal hF) (pairMap F' g) (x, 1) =
      -signAt oM oN (fun x => F' (x, 1)) x := fun x => by
    rw [hs 1 x, show (1 : ℝ) - 2 * 1 = -1 by norm_num, sgn_neg (by norm_num)]; ring
  simp only [hs0, hs1] at hL
  rw [finsum_mem_neg_distrib _ hfin1] at hL
  unfold degAt
  linarith

/-- **Theorem A** (Milnor p. 28): smoothly homotopic maps have the same degree at any common
regular value. -/
theorem degAt_eq_of_homotopy [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [T2Space N] (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n)
    (oN : Orient J N n) {F' : M × ℝ → N} (hF' : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F') {y : N}
    (hy0 : IsRegularValue I J (fun x => F' (x, 0)) y)
    (hy1 : IsRegularValue I J (fun x => F' (x, 1)) y) :
    degAt oM oN (fun x => F' (x, 0)) y = degAt oM oN (fun x => F' (x, 1)) y := by
  have hdim : finrank ℝ E = finrank ℝ F := hE.trans hF.symm
  have hf₀ : ContMDiff I J ∞ (fun x => F' (x, 0)) := hF'.comp (contMDiff_inl 0)
  have hf₁ : ContMDiff I J ∞ (fun x => F' (x, 1)) := hF'.comp (contMDiff_inl 1)
  have h0 := hy0.eventually_isRegularValue_and_ncard hdim hf₀ (by simp)
  have h0' := hy0.eventually_degAt_eq hE hF oM oN hf₀
  have h1 := hy1.eventually_isRegularValue_and_ncard hdim hf₁ (by simp)
  have h1' := hy1.eventually_degAt_eq hE hF oM oN hf₁
  obtain ⟨U, hUsub, hUopen, hyU⟩ := eventually_nhds_iff.1 ((h0.and h0').and (h1.and h1'))
  obtain ⟨y', hy'reg, hy'U⟩ := (dense_regularValues hF').exists_mem_open hUopen ⟨y, hyU⟩
  obtain ⟨⟨⟨hr0, -⟩, hd0⟩, ⟨hr1, -⟩, hd1⟩ := hUsub y' hy'U
  rw [← hd0, ← hd1]
  exact degAt_eq_of_homotopy_of_isRegularValue hE hF oM oN hF' hy'reg hr0 hr1

end Milnor
