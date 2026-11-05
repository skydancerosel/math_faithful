import Milnor.Chapter5.HomotopyInv
import Milnor.Chapter5.Degree

/-!
# The local degree for maps with compact preimages

The local degree `degAt f y = ∑_{x ∈ f⁻¹(y)} signAt f x` of Chapter 5 was studied for maps
`f : M → N` with `M` compact.  The compactness of `M` enters the proofs only through the
compactness of certain preimages, so the results survive for non-compact `M` provided the
relevant preimages are compact.  This is what is needed for the Hopf invariant (Milnor §8,
Problem 14), which is a local degree of a map defined on an open subset of `S × S`.

## Main results

* `IsRegularValue.finite_preimage_of_isCompact`: a compact preimage of a regular value is finite.
* `IsRegularValue.eventually_degAt_eq_of_isCompact`: if some neighbourhood `V` of the regular
  value `y` has compact preimage, then nearby `y'` are regular values with the same local degree.
* `degAt_eq_of_homotopy_of_isRegularValue_of_isCompact`: homotopy invariance of `degAt` when `y`
  is regular for the homotopy on `M × [0,1]` and the part of `F⁻¹(y)` over `[0,1]` is compact.
  Lemma 1 needs a globally regular value of the homotopy; we obtain one by reparametrizing time
  by `τ(t) = (1 - cos πt)/2`, whose critical points are exactly the points where `τ ∈ {0, 1}`,
  where the regularity of the end maps takes over.
* `degAt_eq_of_homotopy_of_isCompact`: homotopy invariance of `degAt` at a common regular value
  of the end maps, provided the part of `F⁻¹(V)` over `[0,1]` is compact for a neighbourhood `V`
  of `y`.
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

/-- Finiteness of a compact preimage of a regular value (equal dimensions). -/
theorem IsRegularValue.finite_preimage_of_isCompact [T2Space M] [T1Space N]
    (hdim : finrank ℝ E = finrank ℝ F) {f : M → N} (hf : ContMDiff I J ∞ f) {y : N}
    (hy : IsRegularValue I J f y) (hK : IsCompact (f ⁻¹' {y})) : (f ⁻¹' {y}).Finite := by
  -- Every point of `f⁻¹(y)` has a neighbourhood on which `f` is injective.
  have key : ∀ x ∈ f ⁻¹' {y}, ∃ U ∈ 𝓝 x, InjOn f U := fun x hx => by
    have hloc := (hy x hx).isLocalDiffeomorphAt hdim hf (by simp)
    refine ⟨hloc.localInverse.target,
      hloc.localInverse.open_target.mem_nhds hloc.localInverse_mem_target, ?_⟩
    intro a ha b hb hab
    rw [← hloc.localInverse_left_inv ha, ← hloc.localInverse_left_inv hb, hab]
  choose! U hU hUinj using key
  -- Finitely many of these neighbourhoods cover `f⁻¹(y)`, and each contains one point of it.
  obtain ⟨t, hts, hcover⟩ := hK.elim_nhds_subcover U hU
  refine t.finite_toSet.subset fun z hz => ?_
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (hcover hz)
  have hxs : x ∈ f ⁻¹' {y} := hts x hxt
  have hfz : f z = y := hz
  have hfx : f x = y := hxs
  have hzx' : z = x :=
    hUinj x hxs hzx (mem_of_mem_nhds (hU x hxs)) (hfz.trans hfx.symm)
  rw [hzx']
  exact hxt

/-- Weighted local constancy near a regular value, when some neighbourhood `V` of `y` has
compact preimage: nearby values are regular, and the weighted count of their preimages is the
same (for a weight `φ` locally constant near each point of `f⁻¹(y)`). -/
theorem IsRegularValue.eventually_isRegularValue_and_finsum_preimage_eq_of_isCompact
    [T2Space M] [T2Space N] (hdim : finrank ℝ E = finrank ℝ F) {f : M → N}
    (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y) {V : Set N} (hV : V ∈ 𝓝 y)
    (hK : IsCompact (f ⁻¹' V)) {φ : M → ℤ} (hφ : ∀ x, f x = y → ∀ᶠ z in 𝓝 x, φ z = φ x) :
    ∀ᶠ y' in 𝓝 y, IsRegularValue I J f y' ∧
      ∑ᶠ x ∈ f ⁻¹' {y'}, φ x = ∑ᶠ x ∈ f ⁻¹' {y}, φ x := by
  classical
  set s := f ⁻¹' {y} with hs_def
  have hs_mem : ∀ z, z ∈ s ↔ f z = y := fun z => by simp [s]
  have hsK : IsCompact s :=
    hK.of_isClosed_subset (isClosed_singleton.preimage hf.continuous)
      (preimage_mono (singleton_subset_iff.2 (mem_of_mem_nhds hV)))
  have hs_fin : s.Finite := hy.finite_preimage_of_isCompact hdim hf hsK
  have : Finite s := hs_fin.to_subtype
  have hloc : ∀ x ∈ s, IsLocalDiffeomorphAt I J ∞ f x := fun x hx =>
    (hy x ((hs_mem x).1 hx)).isLocalDiffeomorphAt hdim hf (by simp)
  let L : s → PartialDiffeomorph J I N M ∞ := fun x => (hloc x.1 x.2).localInverse
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
    have hzloc : IsLocalDiffeomorphAt I J ∞ f z :=
      ⟨Classical.choose (hloc x.1 x.2), hz, hspec.2⟩
    show Function.Surjective (mfderiv I J f z)
    rw [← hzloc.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (hzloc.mfderivToContinuousLinearEquiv (by simp)).surjective
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
  -- `C := f(f⁻¹(V) ∖ ⋃ Uᵢ)` is compact, hence closed since `N` is Hausdorff.
  let C : Set N := f '' (f ⁻¹' V \ ⋃ x, U x)
  have hC : IsClosed C := ((hK.diff (isOpen_iUnion hU_open)).image hf.continuous).isClosed
  let Ω : Set N := (⋂ x, V' x) ∩ Cᶜ ∩ interior V
  have hΩ_open : IsOpen Ω :=
    ((isOpen_iInter_of_finite hV'_open).inter hC.isOpen_compl).inter isOpen_interior
  have hyΩ : y ∈ Ω := by
    refine ⟨⟨mem_iInter.2 hyV', fun hyC => ?_⟩, mem_interior_iff_mem_nhds.2 hV⟩
    obtain ⟨z, hz, hzy⟩ := hyC
    have hzs : z ∈ s := (hs_mem z).2 hzy
    exact hz.2 (mem_iUnion.2 ⟨⟨z, hzs⟩, hxU ⟨z, hzs⟩⟩)
  filter_upwards [hΩ_open.mem_nhds hyΩ] with y' hy'
  obtain ⟨⟨hy'V', hy'C⟩, hy'V⟩ := hy'
  have hy'x : ∀ x : s, y' ∈ V' x := fun x => mem_iInter.1 hy'V' x
  -- every preimage of `y'` lies in some `U x`
  have hpre : ∀ b, f b = y' → ∃ x : s, b ∈ U x := fun b hb => by
    have hbU : b ∈ ⋃ x, U x := by
      by_contra hcon
      have hbV : f b ∈ V := by rw [hb]; exact interior_subset hy'V
      exact hy'C ⟨b, ⟨hbV, hcon⟩, hb⟩
    exact mem_iUnion.1 hbU
  refine ⟨fun b hb => ?_, ?_⟩
  · obtain ⟨x, hbx⟩ := hpre b hb
    exact hL_reg x hbx.1.1
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

/-- **Proper local constancy.** If some neighbourhood `V` of `y` has compact preimage,
the local degree is locally constant near a regular value `y` (and nearby values are regular).
`V` need not be closed. -/
theorem IsRegularValue.eventually_degAt_eq_of_isCompact [T2Space M] [T2Space N]
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n) (oN : Orient J N n)
    {f : M → N} (hf : ContMDiff I J ∞ f) {y : N} (hy : IsRegularValue I J f y)
    {V : Set N} (hV : V ∈ 𝓝 y) (hK : IsCompact (f ⁻¹' V)) :
    ∀ᶠ y' in 𝓝 y, IsRegularValue I J f y' ∧ degAt oM oN f y' = degAt oM oN f y :=
  hy.eventually_isRegularValue_and_finsum_preimage_eq_of_isCompact (hE.trans hF.symm) hf hV hK
    fun x hx => eventually_signAt_eq hE hF oM oN hf (hy x hx)

omit [TopologicalSpace N] in
/-- The slice of a set of the form `{p | F' p ∈ S ∧ p.2 ∈ [0,1]}` at a time `c ∈ [0,1]`,
seen in `M`, is compact if that set is. -/
theorem isCompact_preimage_slice_of_isCompact {F' : M × ℝ → N} {S : Set N} {c : ℝ}
    (hK : IsCompact {p : M × ℝ | F' p ∈ S ∧ p.2 ∈ Icc (0 : ℝ) 1}) (hc : c ∈ Icc (0 : ℝ) 1) :
    IsCompact ((fun x => F' (x, c)) ⁻¹' S) := by
  have : (fun x => F' (x, c)) ⁻¹' S =
      Prod.fst '' ({p : M × ℝ | F' p ∈ S ∧ p.2 ∈ Icc (0 : ℝ) 1} ∩ {p | p.2 = c}) := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, c), ⟨⟨hx, hc⟩, rfl⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨⟨h1, -⟩, h2⟩, rfl⟩
      have h2' : b = c := h2
      subst h2'
      exact h1
  rw [this]
  exact (hK.inter_right (isClosed_eq continuous_snd continuous_const)).image continuous_fst

/-- **Proper homotopy invariance, case of a (global) regular value of the homotopy.** -/
theorem degAt_eq_of_homotopy_of_isRegularValue_of_isCompact' [T2Space M] [T2Space N]
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n) (oN : Orient J N n)
    {F' : M × ℝ → N} (hF' : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F') {y : N}
    (hy : IsRegularValue (I.prod 𝓘(ℝ, ℝ)) J F' y)
    (hy0 : IsRegularValue I J (fun x => F' (x, 0)) y)
    (hy1 : IsRegularValue I J (fun x => F' (x, 1)) y)
    (hK : IsCompact {p : M × ℝ | F' p = y ∧ p.2 ∈ Icc (0 : ℝ) 1}) :
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
    have : {p : M × ℝ | F' p = y ∧ 0 ≤ g p} = {p : M × ℝ | F' p = y ∧ p.2 ∈ Icc (0 : ℝ) 1} := by
      ext ⟨x, t⟩
      simp only [mem_ofPred_eq, mem_Icc, g]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_, ?_⟩
        · by_contra h
          have ht : t < 0 := not_le.1 h
          have : t * (1 - t) < 0 := mul_neg_of_neg_of_pos ht (by linarith)
          linarith
        · by_contra h
          have ht : 1 < t := not_le.1 h
          have : t * (1 - t) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
          linarith
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, mul_nonneg h2 (by linarith)⟩
    rw [this]
    exact hK
  have hL := lemmaOne_ambient hE' hF (oM.prodReal hE) oN hF' hy hg hreg hX
  -- the boundary set splits into the two ends
  set A₀ : Set (M × ℝ) := (fun x => (x, (0 : ℝ))) '' ((fun x => F' (x, 0)) ⁻¹' {y}) with hA₀
  set A₁ : Set (M × ℝ) := (fun x => (x, (1 : ℝ))) '' ((fun x => F' (x, 1)) ⁻¹' {y}) with hA₁
  have hsplit : {p : M × ℝ | F' p = y ∧ g p = 0} = A₀ ∪ A₁ := by
    ext ⟨x, t⟩
    simp only [mem_ofPred_eq, mem_union, A₀, A₁, mem_image, mem_preimage, mem_singleton_iff,
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
  have hfin0 : ((fun x => F' (x, 0)) ⁻¹' {y}).Finite :=
    hy0.finite_preimage_of_isCompact hdim hf₀
      (isCompact_preimage_slice_of_isCompact hK ⟨le_rfl, zero_le_one⟩)
  have hfin1 : ((fun x => F' (x, 1)) ⁻¹' {y}).Finite :=
    hy1.finite_preimage_of_isCompact hdim hf₁
      (isCompact_preimage_slice_of_isCompact hK ⟨zero_le_one, le_rfl⟩)
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
      show (mfd (I.prod 𝓘(ℝ, ℝ)) J F' (x, c) (v, t),
        mfd (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) g (x, c) (v, t)) = _
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

/-- **Proper homotopy invariance, regular case.** -/
theorem degAt_eq_of_homotopy_of_isRegularValue_of_isCompact [T2Space M] [T2Space N]
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n) (oN : Orient J N n)
    {F' : M × ℝ → N} (hF' : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F') {y : N}
    (hy : ∀ p : M × ℝ, F' p = y → p.2 ∈ Icc (0 : ℝ) 1 → IsRegularPoint (I.prod 𝓘(ℝ, ℝ)) J F' p)
    (hy0 : IsRegularValue I J (fun x => F' (x, 0)) y)
    (hy1 : IsRegularValue I J (fun x => F' (x, 1)) y)
    (hK : IsCompact {p : M × ℝ | F' p = y ∧ p.2 ∈ Icc (0 : ℝ) 1}) :
    degAt oM oN (fun x => F' (x, 0)) y = degAt oM oN (fun x => F' (x, 1)) y := by
  -- the time reparametrization `τ t = (1 - cos πt) / 2`
  obtain ⟨τ, hτ_def⟩ : ∃ τ : ℝ → ℝ, τ = fun t => (1 - Real.cos (Real.pi * t)) / 2 := ⟨_, rfl⟩
  have hτ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ τ := by
    rw [contMDiff_iff_contDiff, hτ_def]
    fun_prop
  have hτd : ∀ t, HasDerivAt τ (Real.pi * Real.sin (Real.pi * t) / 2) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi t := by
      simpa using (hasDerivAt_id t).const_mul Real.pi
    have h2 := ((h1.cos).const_sub 1).div_const 2
    rw [hτ_def]
    exact h2.congr_deriv (by ring)
  have hτmem : ∀ t, τ t ∈ Icc (0 : ℝ) 1 := by
    intro t
    rw [hτ_def]
    constructor
    · linarith [Real.cos_le_one (Real.pi * t)]
    · linarith [Real.neg_one_le_cos (Real.pi * t)]
  have hτ0 : τ 0 = 0 := by rw [hτ_def]; simp
  have hτ1 : τ 1 = 1 := by rw [hτ_def]; norm_num
  -- where `τ' t = 0`, `τ t ∈ {0, 1}`
  have hτcrit : ∀ t, Real.sin (Real.pi * t) = 0 → τ t = 0 ∨ τ t = 1 := by
    intro t ht
    have hc : (Real.cos (Real.pi * t) - 1) * (Real.cos (Real.pi * t) + 1) = 0 := by
      linear_combination Real.sin_sq_add_cos_sq (Real.pi * t) - Real.sin (Real.pi * t) * ht
    rw [hτ_def]
    rcases mul_eq_zero.1 hc with h | h
    · left; simp only; linarith
    · right; simp only; linarith
  -- the reparametrized homotopy
  obtain ⟨Φ, hΦ_def⟩ : ∃ Φ : M × ℝ → N, Φ = fun p => F' (p.1, τ p.2) := ⟨_, rfl⟩
  have hΦ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ Φ := by
    rw [hΦ_def]
    exact hF'.comp (contMDiff_fst.prodMk (hτ.comp contMDiff_snd))
  have hΦ0 : (fun x => Φ (x, 0)) = fun x => F' (x, 0) := by
    funext x; rw [hΦ_def]; simp only [hτ0]
  have hΦ1 : (fun x => Φ (x, 1)) = fun x => F' (x, 1) := by
    funext x; rw [hΦ_def]; simp only [hτ1]
  -- `y` is a regular value of `Φ`
  have hΦreg : IsRegularValue (I.prod 𝓘(ℝ, ℝ)) J Φ y := by
    rintro ⟨x, t⟩ hxt
    have hxt' : F' (x, τ t) = y := by rw [hΦ_def] at hxt; exact hxt
    have hD := (hasMFDerivAt_fst (I := I) (I' := 𝓘(ℝ, ℝ)) (x, t)).prodMk
      ((hτd t).hasFDerivAt.hasMFDerivAt.comp (x, t)
        (hasMFDerivAt_snd (I := I) (I' := 𝓘(ℝ, ℝ)) (x, t)))
    have hF'd := hasMFDerivAt_mfd (I := I.prod 𝓘(ℝ, ℝ)) (J := J) (x := (x, τ t))
      (hF'.mdifferentiableAt (by simp))
    have hΦd : HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) J Φ (x, t)
        (((mfd (I.prod 𝓘(ℝ, ℝ)) J F' (x, τ t)).comp ((ContinuousLinearMap.fst ℝ E ℝ).prod
          ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
            (Real.pi * Real.sin (Real.pi * t) / 2)).comp (ContinuousLinearMap.snd ℝ E ℝ))) :)) := by
      rw [hΦ_def]
      exact hF'd.comp (x, t) hD
    have hmfd : ∀ w : E × ℝ, mfd (I.prod 𝓘(ℝ, ℝ)) J Φ (x, t) w =
        mfd (I.prod 𝓘(ℝ, ℝ)) J F' (x, τ t) (w.1, Real.pi * Real.sin (Real.pi * t) / 2 * w.2) := by
      intro w
      rw [HasMFDerivAt.mfd_eq hΦd]
      simp [mul_comm]
    show Function.Surjective (mfd (I.prod 𝓘(ℝ, ℝ)) J Φ (x, t))
    intro z
    by_cases hsin : Real.sin (Real.pi * t) = 0
    · -- `τ t ∈ {0, 1}`: use the regularity of the end map
      have hreg' : IsRegularPoint I J (fun x => F' (x, τ t)) x := by
        rcases hτcrit t hsin with h | h
        · rw [h]; rw [h] at hxt'; exact hy0 x hxt'
        · rw [h]; rw [h] at hxt'; exact hy1 x hxt'
      obtain ⟨v, hv⟩ : ∃ v : E, mfd I J (fun x => F' (x, τ t)) x v = z := hreg' z
      refine ⟨(v, 0), ?_⟩
      rw [hmfd]
      simp only [mul_zero]
      rw [mfd_prod_apply hF', zero_smul, add_zero]
      exact hv
    · -- `τ' t ≠ 0`: use the regularity of `F'`
      have hne : Real.pi * Real.sin (Real.pi * t) / 2 ≠ 0 :=
        div_ne_zero (mul_ne_zero Real.pi_ne_zero hsin) two_ne_zero
      obtain ⟨⟨v, s⟩, hvs⟩ : ∃ w : E × ℝ, mfd (I.prod 𝓘(ℝ, ℝ)) J F' (x, τ t) w = z :=
        hy (x, τ t) hxt' (hτmem t) z
      refine ⟨(v, s / (Real.pi * Real.sin (Real.pi * t) / 2)), ?_⟩
      rw [hmfd]
      simp only
      rw [show Real.pi * Real.sin (Real.pi * t) / 2 * (s / (Real.pi * Real.sin (Real.pi * t) / 2))
        = s by field_simp]
      exact hvs
  -- compactness for `Φ`
  have hΦK : IsCompact {p : M × ℝ | Φ p = y ∧ p.2 ∈ Icc (0 : ℝ) 1} := by
    refine IsCompact.of_isClosed_subset
      ((hK.image continuous_fst).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1)))
      ((isClosed_eq hΦ.continuous continuous_const).inter
        (isClosed_Icc.preimage continuous_snd)) ?_
    rintro ⟨x, t⟩ ⟨h1, h2⟩
    have h1' : F' (x, τ t) = y := by rw [hΦ_def] at h1; exact h1
    exact ⟨⟨(x, τ t), ⟨h1', hτmem t⟩, rfl⟩, h2⟩
  have key := degAt_eq_of_homotopy_of_isRegularValue_of_isCompact' hE hF oM oN hΦ hΦreg
    (by rw [hΦ0]; exact hy0) (by rw [hΦ1]; exact hy1) hΦK
  rwa [hΦ0, hΦ1] at key

/-- **Proper homotopy invariance.** -/
theorem degAt_eq_of_homotopy_of_isCompact [T2Space M] [SecondCountableTopology M] [T2Space N]
    (hE : finrank ℝ E = n) (hF : finrank ℝ F = n) (oM : Orient I M n) (oN : Orient J N n)
    {F' : M × ℝ → N} (hF' : ContMDiff (I.prod 𝓘(ℝ, ℝ)) J ∞ F') {y : N}
    (hy0 : IsRegularValue I J (fun x => F' (x, 0)) y)
    (hy1 : IsRegularValue I J (fun x => F' (x, 1)) y)
    {V : Set N} (hV : V ∈ 𝓝 y) (hK : IsCompact {p : M × ℝ | F' p ∈ V ∧ p.2 ∈ Icc (0 : ℝ) 1}) :
    degAt oM oN (fun x => F' (x, 0)) y = degAt oM oN (fun x => F' (x, 1)) y := by
  have hf₀ : ContMDiff I J ∞ (fun x => F' (x, 0)) := hF'.comp (contMDiff_inl 0)
  have hf₁ : ContMDiff I J ∞ (fun x => F' (x, 1)) := hF'.comp (contMDiff_inl 1)
  have h0 := hy0.eventually_degAt_eq_of_isCompact hE hF oM oN hf₀ hV
    (isCompact_preimage_slice_of_isCompact hK ⟨le_rfl, zero_le_one⟩)
  have h1 := hy1.eventually_degAt_eq_of_isCompact hE hF oM oN hf₁ hV
    (isCompact_preimage_slice_of_isCompact hK ⟨zero_le_one, le_rfl⟩)
  have hV' : ∀ᶠ y' in 𝓝 y, y' ∈ V := hV
  obtain ⟨U, hUsub, hUopen, hyU⟩ := eventually_nhds_iff.1 ((h0.and h1).and hV')
  obtain ⟨y', hy'reg, hy'U⟩ := (dense_regularValues hF').exists_mem_open hUopen ⟨y, hyU⟩
  obtain ⟨⟨⟨hr0, hd0⟩, hr1, hd1⟩, hy'V⟩ := hUsub y' hy'U
  have hy'reg' : IsRegularValue (I.prod 𝓘(ℝ, ℝ)) J F' y' := hy'reg
  rw [← hd0, ← hd1]
  refine degAt_eq_of_homotopy_of_isRegularValue_of_isCompact hE hF oM oN hF'
    (fun p hp _ => hy'reg' p hp) hr0 hr1 ?_
  refine hK.of_isClosed_subset ((isClosed_eq hF'.continuous continuous_const).inter
    (isClosed_Icc.preimage continuous_snd)) ?_
  rintro p ⟨hp1, hp2⟩
  have hp1' : F' p = y' := hp1
  exact ⟨by rw [hp1']; exact hy'V, hp2⟩

end Milnor
