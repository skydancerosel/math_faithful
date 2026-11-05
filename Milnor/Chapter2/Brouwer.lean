import Milnor.Chapter2.Corestrict
import Milnor.Chapter2.Retraction
import Milnor.Chapter2.Disk
import Milnor.Chapter2.WithBoundary
import Milnor.Chapter2.Brown
import Milnor.Appendix.HalfSpace

/-!
# Milnor's Lemmas 5 and 6 for the disk, and the smooth Brouwer fixed point theorem (§2, pp. 13–14)

Route (Milnor's): a smooth self-map `P` of the closed unit disk `D ⊆ E` without fixed points gives
the smooth retraction `f : D → ∂D` of Lemma 6 (`Milnor.Chapter2.Retraction`).  Pick a regular
value `y ∈ ∂D` of `f` (Brown).  By Lemma 4, `f⁻¹(y)` is a compact 1-manifold with boundary
`f⁻¹(y) ∩ ∂D = {y}`, which has one boundary point; but a compact 1-manifold with boundary has an
even number of boundary points (the Appendix).  Contradiction.

Two technical adjustments make the book's argument formal.  The retraction is extended to a smooth
map on all of `E` by composing with a smooth cutoff that is the identity on the disk and takes
values in a slightly larger ball on which the retraction formula is still defined; this avoids
manifolds-with-boundary as domains.  And the retraction is regarded as a map into the sphere
using the corestriction lemma of `Milnor.Chapter2.Corestrict`.
-/

open Set Metric Module Topology
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### A smooth cutoff: the identity on the unit ball, with values in the ball of radius `1 + δ` -/

/-- `cutoff δ x = (1 - ψ(‖x‖²)) x` with `ψ` a smooth transition from `0` (for `‖x‖ ≤ 1`) to `1`
(for `‖x‖ ≥ 1 + δ`). -/
def cutoff (δ : ℝ) (x : E) : E :=
  (1 - Real.smoothTransition ((‖x‖ ^ 2 - 1) / ((1 + δ) ^ 2 - 1))) • x

theorem cutoff_contDiff (δ : ℝ) : ContDiff ℝ ∞ (cutoff δ : E → E) := by
  unfold cutoff
  have h1 : ContDiff ℝ ∞ (fun x : E => (‖x‖ ^ 2 - 1) / ((1 + δ) ^ 2 - 1)) :=
    ((contDiff_norm_sq ℝ).sub contDiff_const).div_const _
  exact (contDiff_const.sub (Real.smoothTransition.contDiff.comp h1)).smul contDiff_id

theorem cutoff_eq_self {δ : ℝ} (hδ : 0 < δ) {x : E} (hx : ‖x‖ ≤ 1) : cutoff δ x = x := by
  unfold cutoff
  have h : (‖x‖ ^ 2 - 1) / ((1 + δ) ^ 2 - 1) ≤ 0 :=
    div_nonpos_iff.2 (Or.inr ⟨by nlinarith [norm_nonneg x], by nlinarith⟩)
  rw [Real.smoothTransition.zero_of_nonpos h, sub_zero, one_smul]

theorem norm_cutoff_le {δ : ℝ} (hδ : 0 < δ) (x : E) : ‖cutoff δ x‖ ≤ 1 + δ := by
  unfold cutoff
  rw [norm_smul, Real.norm_eq_abs]
  by_cases h : ‖x‖ ≤ 1 + δ
  · have h0 := Real.smoothTransition.nonneg ((‖x‖ ^ 2 - 1) / ((1 + δ) ^ 2 - 1))
    have h1 := Real.smoothTransition.le_one ((‖x‖ ^ 2 - 1) / ((1 + δ) ^ 2 - 1))
    rw [abs_of_nonneg (by linarith)]
    calc (1 - Real.smoothTransition ((‖x‖ ^ 2 - 1) / ((1 + δ) ^ 2 - 1))) * ‖x‖
        ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x)
      _ ≤ 1 + δ := by linarith
  · push_neg at h
    have : 1 ≤ (‖x‖ ^ 2 - 1) / ((1 + δ) ^ 2 - 1) := by
      rw [le_div_iff₀ (by nlinarith)]; nlinarith
    rw [Real.smoothTransition.one_of_one_le this, sub_self, abs_zero, zero_mul]; linarith

/-- Points of the closed ball of radius `1 + δ` are within `δ` of the unit ball. -/
theorem closedBall_subset_cthickening_closedBall {δ : ℝ} (hδ : 0 < δ) :
    closedBall (0 : E) (1 + δ) ⊆ cthickening δ (closedBall (0 : E) 1) := by
  intro y hy
  rw [mem_closedBall_zero_iff] at hy
  by_cases h1 : ‖y‖ ≤ 1
  · exact self_subset_cthickening _ (mem_closedBall_zero_iff.2 h1)
  · push_neg at h1
    set y' := ‖y‖⁻¹ • y with hy'
    have hy'D : y' ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall_zero_iff, hy', norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (by positivity)]
    refine closedBall_subset_cthickening hy'D δ ?_
    rw [mem_closedBall, dist_eq_norm, hy']
    have : y - ‖y‖⁻¹ • y = (1 - ‖y‖⁻¹) • y := by rw [sub_smul, one_smul]
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by
      rw [sub_nonneg]; exact inv_le_one_of_one_le₀ h1.le)]
    have hpos : 0 < ‖y‖ := by linarith
    calc (1 - ‖y‖⁻¹) * ‖y‖ = ‖y‖ - 1 := by field_simp
      _ ≤ δ := by linarith

/-! ### The smooth Brouwer fixed point theorem -/

/-- **Lemmas 5 and 6 and the smooth fixed point theorem.** A smooth self-map of the closed unit
ball of a finite-dimensional real inner product space has a fixed point. -/
theorem exists_fixedPoint_of_contDiff (P : E → E) (hP : ContDiff ℝ ∞ P)
    (hPD : ∀ x ∈ closedBall (0 : E) 1, P x ∈ closedBall (0 : E) 1) :
    ∃ x ∈ closedBall (0 : E) 1, P x = x := by
  classical
  by_contra hcon
  push_neg at hcon
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hpos
  · haveI : Subsingleton E := finrank_zero_iff.1 h0
    exact hcon 0 (mem_closedBall_self zero_le_one) (Subsingleton.elim _ _)
  -- the auxiliary model spaces: a hyperplane, a line and the zero subspace of `E`
  haveI : Nontrivial E := Module.finrank_pos_iff.1 hpos
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  set n := finrank ℝ E with hn
  have hZL : finrank ℝ (ℝ ∙ e) + finrank ℝ (ℝ ∙ e)ᗮ = finrank ℝ E :=
    Submodule.finrank_add_finrank_orthogonal _
  have hZSdim : finrank ℝ (ℝ ∙ e)ᗮ = n - 1 := by
    rw [finrank_span_singleton he] at hZL; omega
  have hZS : finrank ℝ (ℝ ∙ e)ᗮ + finrank ℝ ℝ = finrank ℝ E := by
    rw [hZSdim, finrank_self]; omega
  have hZ' : finrank ℝ (⊥ : Submodule ℝ E) + 1 = finrank ℝ (ℝ ∙ e) := by
    rw [finrank_bot, finrank_span_singleton he]
  haveI : Subsingleton (⊥ : Submodule ℝ E) := finrank_zero_iff.1 (by rw [finrank_bot])
  -- the sphere as a slice submanifold
  set S : Set E := diskFun ⁻¹' {0} with hSdef
  have hS : IsSliceSubmanifold 𝓘(ℝ, E) ((ℝ ∙ e)ᗮ) ℝ S :=
    isSliceSubmanifold_preimage hZS contMDiff_diskFun isRegularValue_diskFun
  letI := hS.chartedSpace
  haveI := hS.isManifold
  have hnormS : ∀ x ∈ S, ‖x‖ = 1 := fun x hx => by
    have h : (1 : ℝ) - ‖x‖ ^ 2 = 0 := hx
    have h2 : ‖x‖ ^ 2 = 1 := by linarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) two_ne_zero).1 h2
  -- the retraction, extended to all of `E` by the cutoff
  have hgood : IsOpen (Retraction.good P) := Retraction.isOpen_good hP.continuous
  have hDgood : closedBall (0 : E) 1 ⊆ Retraction.good P :=
    Retraction.closedBall_subset_good hPD hcon
  obtain ⟨δ, hδ, hthick⟩ :=
    (isCompact_closedBall (0 : E) 1).exists_cthickening_subset_open hgood hDgood
  have hball : closedBall (0 : E) (1 + δ) ⊆ Retraction.good P :=
    (closedBall_subset_cthickening_closedBall hδ).trans hthick
  have hρD : ∀ x ∈ closedBall (0 : E) 1, cutoff δ x = x := fun x hx =>
    cutoff_eq_self hδ (mem_closedBall_zero_iff.1 hx)
  have hρgood : ∀ x, cutoff δ x ∈ Retraction.good P := fun x =>
    hball (mem_closedBall_zero_iff.2 (norm_cutoff_le hδ x))
  set F : E → E := Retraction.retr P ∘ cutoff δ with hFdef
  have hFsmooth : ContDiff ℝ ∞ F :=
    (Retraction.contDiffOn_retr hP).comp_contDiff (cutoff_contDiff δ) hρgood
  have hFS : ∀ x, F x ∈ S := fun x => by
    show (1 : ℝ) - ‖Retraction.retr P (cutoff δ x)‖ ^ 2 = 0
    rw [Retraction.norm_retr (hρgood x)]; ring
  have hFid : ∀ x ∈ S, F x = x := fun x hx => by
    have hx1 : ‖x‖ = 1 := hnormS x hx
    have hxD : x ∈ closedBall (0 : E) 1 := mem_closedBall_zero_iff.2 hx1.le
    show Retraction.retr P (cutoff δ x) = x
    rw [hρD x hxD]
    exact Retraction.retr_eq_self (hDgood hxD) hx1 (mem_closedBall_zero_iff.1 (hPD x hxD))
  -- corestrict to the sphere
  set f : E → S := fun x => ⟨F x, hFS x⟩ with hfdef
  have hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, (ℝ ∙ e)ᗮ) ∞ f :=
    hS.contMDiff_codRestrict hFsmooth.contMDiff hFS
  have hfid : ∀ q : S, f q.1 = q := fun q => Subtype.ext (hFid q.1 q.2)
  -- a regular value (Brown)
  haveI : Nonempty S := ⟨f 0⟩
  obtain ⟨y, hy⟩ := (dense_regularValues hf).nonempty
  have hyreg : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ, (ℝ ∙ e)ᗮ) f y := hy
  -- the transversality condition of Lemma 4, from Lemma 2 and the chain rule
  have hreg : ∀ x, f x = y → diskFun x = 0 →
      ∃ v, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, (ℝ ∙ e)ᗮ) f x v = 0 ∧
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) diskFun x v ≠ 0 := by
    intro x hfx hgx
    have hxS : x ∈ S := hgx
    have hsurj : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, (ℝ ∙ e)ᗮ) f x) :=
      hyreg x hfx
    let L : E →L[ℝ] (ℝ ∙ e)ᗮ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, (ℝ ∙ e)ᗮ) f x
    have hL : L = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, (ℝ ∙ e)ᗮ) f x := rfl
    have hker : LinearMap.ker (L : E →ₗ[ℝ] (ℝ ∙ e)ᗮ) ≠ ⊥ := by
      intro hbot
      have h1 := LinearMap.finrank_range_add_finrank_ker (L : E →ₗ[ℝ] (ℝ ∙ e)ᗮ)
      rw [hbot, finrank_bot, add_zero] at h1
      have h2 : finrank ℝ (LinearMap.range (L : E →ₗ[ℝ] (ℝ ∙ e)ᗮ)) ≤
          finrank ℝ ((ℝ ∙ e)ᗮ) := Submodule.finrank_le _
      rw [hZSdim] at h2
      omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hLv : L v = 0 := LinearMap.mem_ker.1 hv
    refine ⟨v, hLv, fun hgv => ?_⟩
    obtain ⟨w, hw⟩ :=
      (mem_range_mfderiv_val_iff hZS contMDiff_diskFun isRegularValue_diskFun ⟨x, hxS⟩ v).2 hgv
    have hfval : (f ∘ (Subtype.val : S → E)) = id := funext fun q => hfid q
    have hchain : mfderiv 𝓘(ℝ, (ℝ ∙ e)ᗮ) 𝓘(ℝ, (ℝ ∙ e)ᗮ)
        (f ∘ (Subtype.val : S → E)) ⟨x, hxS⟩ =
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, (ℝ ∙ e)ᗮ) f x).comp
          (mfderiv 𝓘(ℝ, (ℝ ∙ e)ᗮ) 𝓘(ℝ, E) (Subtype.val : S → E) ⟨x, hxS⟩) :=
      mfderiv_comp (⟨x, hxS⟩ : S) (hf.mdifferentiableAt (by simp))
        (hS.contMDiff_val.mdifferentiableAt (by simp))
    rw [hfval, mfderiv_id] at hchain
    have h := DFunLike.congr_fun hchain w
    have h' : w = L (mfderiv 𝓘(ℝ, (ℝ ∙ e)ᗮ) 𝓘(ℝ, E) (Subtype.val : S → E) ⟨x, hxS⟩ w) := h
    rw [hw, hLv] at h'
    have hv : v = 0 := by
      rw [← hw, h']
      exact (mfderiv 𝓘(ℝ, (ℝ ∙ e)ᗮ) 𝓘(ℝ, E) (Subtype.val : S → E) ⟨x, hxS⟩).map_zero
    exact hv0 hv
  -- Lemma 4: the level set is a compact 1-manifold with boundary `{y}`
  have hX := isHalfSliceSubmanifold_levelSet hZL hZ' hf hyreg contMDiff_diskFun hreg
  letI := (isSliceSubmanifold_preimage hZL hf hyreg).chartedSpace
  haveI := (isSliceSubmanifold_preimage hZL hf hyreg).isManifold
  have hcompact : IsCompact {q : f ⁻¹' {y} | 0 ≤ diskFun q.1} := by
    rw [IsEmbedding.subtypeVal.isCompact_iff]
    have himg : Subtype.val '' {q : f ⁻¹' {y} | 0 ≤ diskFun q.1} =
        f ⁻¹' {y} ∩ closedBall (0 : E) 1 := by
      ext x; constructor
      · rintro ⟨q, hq, rfl⟩
        refine ⟨q.2, ?_⟩
        have h : (0 : ℝ) ≤ 1 - ‖(q : E)‖ ^ 2 := hq
        rw [mem_closedBall_zero_iff]
        nlinarith [norm_nonneg (q : E)]
      · rintro ⟨h2, h1⟩
        refine ⟨⟨x, h2⟩, ?_, rfl⟩
        show (0 : ℝ) ≤ 1 - ‖x‖ ^ 2
        have := mem_closedBall_zero_iff.1 h1
        nlinarith [norm_nonneg x]
    rw [himg]
    exact (isCompact_closedBall _ _).inter_left (isClosed_singleton.preimage hf.continuous)
  have hBX : {q : f ⁻¹' {y} | diskFun q.1 = 0} ⊆ {q : f ⁻¹' {y} | 0 ≤ diskFun q.1} :=
    fun q hq => le_of_eq (hq : diskFun q.1 = 0).symm
  obtain ⟨-, heven⟩ := IsHalfSliceSubmanifold.even_ncard_boundary hX hcompact hBX
  have hy0 : f y.1 = y := hfid y
  have hsingle : {q : f ⁻¹' {y} | diskFun q.1 = 0} = {⟨y.1, hy0⟩} := by
    ext q
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · intro hq
      have hqS : q.1 ∈ S := hq
      have h1 : f q.1 = ⟨q.1, hqS⟩ := hfid ⟨q.1, hqS⟩
      have h2 : f q.1 = y := q.2
      have h3 : (⟨q.1, hqS⟩ : S) = y := h1.symm.trans h2
      have h4 : q.1 = y.1 := congrArg Subtype.val h3
      exact Subtype.ext h4
    · rintro rfl
      exact y.2
  rw [hsingle, ncard_singleton] at heven
  exact Nat.not_even_one heven

/-! ### Smooth approximation on the disk (Stone–Weierstrass) -/

section Approx

variable (E)

/-- The functions on the closed unit ball that extend to smooth functions on `E`, as a subalgebra
of the continuous functions. -/
def smoothSubalgebra : Subalgebra ℝ C(closedBall (0 : E) 1, ℝ) where
  carrier := {g | ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ ∀ x : closedBall (0 : E) 1, g x = F x}
  mul_mem' := by
    rintro g₁ g₂ ⟨F₁, hF₁, h₁⟩ ⟨F₂, hF₂, h₂⟩
    exact ⟨fun x => F₁ x * F₂ x, hF₁.mul hF₂, fun x => by simp [h₁ x, h₂ x]⟩
  add_mem' := by
    rintro g₁ g₂ ⟨F₁, hF₁, h₁⟩ ⟨F₂, hF₂, h₂⟩
    exact ⟨fun x => F₁ x + F₂ x, hF₁.add hF₂, fun x => by simp [h₁ x, h₂ x]⟩
  algebraMap_mem' r := ⟨fun _ => r, contDiff_const, fun x => by simp⟩

theorem smoothSubalgebra_separatesPoints : (smoothSubalgebra E).SeparatesPoints := by
  intro x y hxy
  have hne : (y : E) - x ≠ 0 := sub_ne_zero.2 fun h => hxy (Subtype.ext h.symm)
  have hcont : Continuous fun z : closedBall (0 : E) 1 => ⟪(z : E), (y : E) - x⟫ :=
    continuous_subtype_val.inner continuous_const
  refine ⟨_, ⟨⟨fun z => ⟪(z : E), (y : E) - x⟫, hcont⟩,
    ⟨fun z => ⟪z, (y : E) - x⟫, contDiff_id.inner ℝ contDiff_const, fun _ => rfl⟩, rfl⟩, ?_⟩
  show ⟪(x : E), (y : E) - x⟫ ≠ ⟪(y : E), (y : E) - x⟫
  intro h
  have : ⟪(y : E) - x, (y : E) - x⟫ = 0 := by rw [inner_sub_left, h, sub_self]
  exact hne (inner_self_eq_zero.1 this)

/-- Every map continuous on the closed unit ball is uniformly approximable there by smooth maps
`E → E`. -/
theorem exists_contDiff_approx (G : E → E) (hG : ContinuousOn G (closedBall (0 : E) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : E → E, ContDiff ℝ ∞ P ∧ ∀ x ∈ closedBall (0 : E) 1, ‖P x - G x‖ < ε := by
  classical
  haveI : CompactSpace (closedBall (0 : E) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  set b := stdOrthonormalBasis ℝ E
  set N := finrank ℝ E with hN
  set ε' := ε / (N + 1) with hε'def
  have hε' : 0 < ε' := by positivity
  have hcoord : ∀ i : Fin N, ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧
      ∀ x : closedBall (0 : E) 1, ‖F x - ⟪b i, G x⟫‖ < ε' := by
    intro i
    have hc : Continuous fun x : closedBall (0 : E) 1 => ⟪b i, G x.1⟫ :=
      continuous_const.inner (hG.comp_continuous continuous_subtype_val fun x => x.2)
    obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints _
      (smoothSubalgebra_separatesPoints E) _ hc ε' hε'
    obtain ⟨F, hF, hgF⟩ := g.2
    exact ⟨F, hF, fun x => by rw [← hgF x]; exact hg x⟩
  choose F hF hFG using hcoord
  refine ⟨fun x => ∑ i, F i x • b i, ContDiff.sum fun i _ => (hF i).smul contDiff_const, ?_⟩
  intro x hx
  have hrepr : G x = ∑ i, ⟪b i, G x⟫ • b i := (b.sum_repr' (G x)).symm
  rw [hrepr, ← Finset.sum_sub_distrib]
  simp_rw [← sub_smul]
  have hN' : (N : ℝ) * ε' < ε := by
    rw [hε'def, mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith
  calc ‖∑ i, (F i x - ⟪b i, G x⟫) • b i‖ ≤ ∑ i, ‖(F i x - ⟪b i, G x⟫) • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖F i x - ⟪b i, G x⟫‖ := by simp [norm_smul, b.norm_eq_one]
    _ ≤ ∑ _i : Fin N, ε' := Finset.sum_le_sum fun i _ => (hFG i ⟨x, hx⟩).le
    _ = N * ε' := by simp
    _ < ε := hN'

end Approx

/-- **Brouwer's fixed point theorem** (Milnor §2, p. 14): a continuous self-map of the closed
unit ball of a finite-dimensional real inner product space has a fixed point. -/
theorem exists_fixedPoint (G : E → E) (hG : ContinuousOn G (closedBall (0 : E) 1))
    (hGD : ∀ x ∈ closedBall (0 : E) 1, G x ∈ closedBall (0 : E) 1) :
    ∃ x ∈ closedBall (0 : E) 1, G x = x := by
  by_contra hcon
  push_neg at hcon
  have hcont : ContinuousOn (fun x => ‖G x - x‖) (closedBall (0 : E) 1) :=
    (hG.sub continuousOn_id).norm
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_closedBall (0 : E) 1).exists_isMinOn
    (nonempty_closedBall.2 zero_le_one) hcont
  set μ := ‖G x₀ - x₀‖ with hμ
  have hμpos : 0 < μ := norm_pos_iff.2 (sub_ne_zero.2 (hcon x₀ hx₀))
  have hμle : ∀ x ∈ closedBall (0 : E) 1, μ ≤ ‖G x - x‖ := fun x hx => hmin hx
  obtain ⟨P₁, hP₁, hP₁G⟩ := exists_contDiff_approx E G hG (half_pos hμpos)
  set c : ℝ := 1 + μ / 2 with hc
  have hcpos : 0 < c := by positivity
  have hc1 : 1 ≤ c := by linarith
  set P : E → E := fun x => c⁻¹ • P₁ x with hPdef
  have hP : ContDiff ℝ ∞ P := contDiff_const.smul hP₁
  have hP₁le : ∀ x ∈ closedBall (0 : E) 1, ‖P₁ x‖ ≤ c := by
    intro x hx
    have h1 : ‖P₁ x‖ ≤ ‖G x‖ + ‖P₁ x - G x‖ := norm_le_insert' _ _
    have h2 : ‖G x‖ ≤ 1 := mem_closedBall_zero_iff.1 (hGD x hx)
    have h3 := hP₁G x hx
    linarith
  have hPD : ∀ x ∈ closedBall (0 : E) 1, P x ∈ closedBall (0 : E) 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    show ‖c⁻¹ • P₁ x‖ ≤ 1
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hcpos, inv_mul_le_iff₀ hcpos, mul_one]
    exact hP₁le x hx
  obtain ⟨x, hx, hPx⟩ := exists_fixedPoint_of_contDiff P hP hPD
  have hPP₁ : ‖P x - P₁ x‖ ≤ μ / 2 := by
    have : P x - P₁ x = (c⁻¹ - 1) • P₁ x := by rw [sub_smul, one_smul]
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by
      rw [sub_nonpos]; exact inv_le_one_of_one_le₀ hc1), neg_sub]
    calc (1 - c⁻¹) * ‖P₁ x‖ ≤ (1 - c⁻¹) * c :=
          mul_le_mul_of_nonneg_left (hP₁le x hx) (by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hc1)
      _ = μ / 2 := by field_simp; ring
  have h2 : ‖P x - G x‖ < μ := by
    calc ‖P x - G x‖ ≤ ‖P x - P₁ x‖ + ‖P₁ x - G x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < μ / 2 + μ / 2 := add_lt_add_of_le_of_lt hPP₁ (hP₁G x hx)
      _ = μ := by ring
  have h3 : ‖G x - x‖ = ‖P x - G x‖ := by
    rw [norm_sub_rev]; rw [hPx]
  have := hμle x hx
  linarith

end Milnor
