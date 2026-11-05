import Milnor.Chapter7.ProdNbhd

/-!
# The tube map of a framed submanifold of `M` (Milnor §7, Product Neighbourhood Theorem)

For a framed submanifold `(N, v)` of `M ⊆ ℝᴷ⁺¹`, the map
`G(x, t) = r(x + ∑ᵢ λ(t)ᵢ vᵢ(x))`, `r` the nearest-point retraction onto `M` and `λ` a smooth
clamp (the identity near `0`, bounded), is a smooth map `N × ℝᵖ → M` with `G(x, 0) = x` and
`dG_{(x,0)}(a, s) = dx(a) + ∑ sᵢ vᵢ(x)`, which is bijective.  This provides the hypotheses of the
abstract product neighbourhood theorem (`ProdNbhd.lean`).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

/-! ### Two calculus lemmas on manifolds -/

section calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Unfolding a manifold derivative into a vector space. -/
theorem hasMFDerivAt_iff_vec {f : M → V} {x : M} {f' : E →L[ℝ] V} :
    HasMFDerivAt I 𝓘(ℝ, V) f x f' ↔ ContinuousAt f x ∧
      HasFDerivWithinAt (fun z => f ((extChartAt I x).symm z)) f' (range I) (extChartAt I x x) := by
  unfold HasMFDerivAt writtenInExtChartAt
  simp only [Function.comp_def, extChartAt_self_apply, modelWithCornersSelf_coe, id_eq]
  exact Iff.rfl

/-- The product rule for a scalar function times a vector-valued function. -/
theorem HasMFDerivAt.smulVec {c : M → ℝ} {g : M → V} {x : M} {c' : E →L[ℝ] ℝ} {g' : E →L[ℝ] V}
    (hc : HasMFDerivAt I 𝓘(ℝ, ℝ) c x c') (hg : HasMFDerivAt I 𝓘(ℝ, V) g x g') :
    HasMFDerivAt I 𝓘(ℝ, V) (fun y => c y • g y) x (c x • g' + c'.smulRight (g x)) := by
  rw [hasMFDerivAt_iff_vec] at hc hg ⊢
  refine ⟨hc.1.smul hg.1, ?_⟩
  have := hc.2.smul hg.2
  rwa [extChartAt_to_inv] at this

/-- Derivative of a finite sum of vector-valued functions. -/
theorem hasMFDerivAt_finset_sum {ι : Type*} (s : Finset ι) {f : ι → M → V} {x : M}
    {f' : ι → E →L[ℝ] V} (h : ∀ i ∈ s, HasMFDerivAt I 𝓘(ℝ, V) (f i) x (f' i)) :
    HasMFDerivAt I 𝓘(ℝ, V) (fun y => ∑ i ∈ s, f i y) x (∑ i ∈ s, f' i) := by
  simp only [hasMFDerivAt_iff_vec] at h
  refine hasMFDerivAt_iff_vec.2 ⟨tendsto_finset_sum s fun i hi => (h i hi).1, ?_⟩
  have := HasFDerivWithinAt.sum fun i hi => (h i hi).2
  rw [Finset.sum_fn] at this
  exact this

/-- Smoothness of a finite sum of vector-valued functions. -/
theorem contMDiff_finset_sum' {ι : Type*} (s : Finset ι) {f : ι → M → V}
    (h : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, V) ∞ (f i)) :
    ContMDiff I 𝓘(ℝ, V) ∞ (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact contMDiff_const
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end calculus

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} (hMc : IsCompact M) (hne : M.Nonempty)
  {n p : ℕ} (F : FramedSub hM n p)

/-! ### The inclusion `N → ℝᴷ⁺¹` -/

/-- The inclusion of `N` in the ambient space. -/
def emb (F : FramedSub hM n p) (x : F.N) : EuclideanSpace ℝ (Fin (K + 1)) := x.1.1

theorem contMDiff_emb :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ (emb F) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  exact hM.contMDiff_val.comp F.hN.contMDiff_val

theorem mfd_emb (x : F.N) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (emb F) x =
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x.1).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (Subtype.val : F.N → M) x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  have h1 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))) (hM.contMDiff_val.mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x.1)
  have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (F.hN.contMDiff_val.mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (Subtype.val : F.N → M) x)
  exact HasMFDerivAt.mfd_eq (h1.comp x h2)

theorem injective_mfd_emb (x : F.N) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (emb F) x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  rw [mfd_emb F x]
  have h1 : Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) x.1) := injective_mfderiv_val hM x.1
  have h2 : Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (Subtype.val : F.N → M) x) := injective_mfderiv_val F.hN x
  exact h1.comp h2

theorem range_mfd_emb_le (x : F.N) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (emb F) x : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1))) ≤ tangentM hM x.1 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  rw [mfd_emb F x]
  unfold tangentM
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
  exact LinearMap.map_le_range

theorem tangentN_eq (x : F.N) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    tangentN hM F.hN x = LinearMap.range ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (emb F) x :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1))) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (K + 1))) := rfl

/-! ### The derivative of the tube map at `(x, 0)` -/

/-- `Dg x (a, s) = dx(a) + ∑ sᵢ vᵢ(x)`. -/
def Dg (x : F.N) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p) →L[ℝ]
    EuclideanSpace ℝ (Fin (K + 1)) :=
  letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
  (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (emb F) x).comp
    (ContinuousLinearMap.fst ℝ _ _) +
  ∑ i : Fin p, ((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ _ _)).smulRight (F.v i x)

theorem Dg_apply (x : F.N) (a : EuclideanSpace ℝ (Fin n)) (s : EuclideanSpace ℝ (Fin p)) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    Dg F x (a, s) = mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (emb F) x a + ∑ i : Fin p, s i • F.v i x := by
  simp [Dg]

theorem Dg_mem_tangentM (x : F.N) (w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) :
    Dg F x w ∈ tangentM hM x.1 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  obtain ⟨a, s⟩ := w
  rw [Dg_apply]
  refine Submodule.add_mem _ (range_mfd_emb_le F x ⟨a, rfl⟩) ?_
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (F.tangent i x)

theorem Dg_injective (x : F.N) : Injective (Dg F x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨a, s⟩ h
  rw [Dg_apply] at h
  -- the tangent part is orthogonal to the normal part
  have hperp : ⟪∑ i : Fin p, s i • F.v i x, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (emb F) x a⟫ = 0 := by
    rw [sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [real_inner_smul_left]
    have hn : ⟪F.v i x, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (emb F) x a⟫ = 0 := F.normal i x _ (by rw [tangentN_eq]; exact ⟨a, rfl⟩)
    rw [hn, mul_zero]
  have hzero : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (emb F) x a = 0 := by
    have h1 : ⟪mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (emb F) x a,
        mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (emb F) x a⟫ = 0 := by
      have h2 := congrArg (fun z => ⟪z, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (emb F) x a⟫) h
      simp only [inner_add_left, hperp, add_zero, inner_zero_left] at h2
      exact h2
    exact inner_self_eq_zero.1 h1
  have ha : a = 0 := injective_mfd_emb F x (by rw [hzero, map_zero])
  rw [hzero, zero_add] at h
  have hs : s = 0 := by
    have := (Fintype.linearIndependent_iff.1 (F.indep x)) s h
    ext i
    simp [this i]
  rw [ha, hs]; rfl

/-! ### The tube map -/

/-- The ambient tube map `x + ∑ λ(t)ᵢ vᵢ(x)`. -/
def Gamb (lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (q : F.N × EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin (K + 1)) :=
  emb F q.1 + ∑ i : Fin p, (lam q.2) i • F.v i q.1

/-- The tube map `r(x + ∑ λ(t)ᵢ vᵢ(x))` into `M`. -/
def Gx (lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (q : F.N × EuclideanSpace ℝ (Fin p)) : M :=
  Tub.tubr hM hMc hne (Gamb F lam q)

theorem Gamb_zero {lam} (hlam0 : lam 0 = 0) (x : F.N) : Gamb F lam (x, 0) = emb F x := by
  simp [Gamb, hlam0]

theorem Gx_zero {lam} (hlam0 : lam 0 = 0) (x : F.N) : Gx hMc hne F lam (x, 0) = x.1 := by
  unfold Gx
  rw [Gamb_zero F hlam0]
  exact tubr_mem_of_mem hM hMc hne x.1.2

theorem Gx_zero_injective {lam} (hlam0 : lam 0 = 0) (x x' : F.N)
    (h : Gx hMc hne F lam (x, 0) = Gx hMc hne F lam (x', 0)) : x = x' := by
  rw [Gx_zero hMc hne F hlam0, Gx_zero hMc hne F hlam0] at h
  exact Subtype.ext h

/-- A bound on the framing. -/
theorem exists_bound_v : ∃ C : ℝ, 0 < C ∧ ∀ i x, ‖F.v i x‖ ≤ C := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI : CompactSpace F.N := isCompact_iff_compactSpace.1 F.compact
  have hb : ∀ i, ∃ C, ∀ x, ‖F.v i x‖ ≤ C := fun i => by
    have hcont : ContinuousOn (fun x : F.N => ‖F.v i x‖) univ :=
      (F.smooth i).continuous.norm.continuousOn
    obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image hcont
    exact ⟨C, fun x => hC ⟨x, mem_univ _, rfl⟩⟩
  choose C hC using hb
  refine ⟨∑ i, max (C i) 0 + 1, ?_, fun i x => ?_⟩
  · have : 0 ≤ ∑ i, max (C i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
    linarith
  · have h1 : ‖F.v i x‖ ≤ max (C i) 0 := (hC i x).trans (le_max_left _ _)
    have h2 : max (C i) 0 ≤ ∑ j, max (C j) 0 :=
      Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i)
    linarith

/-! ### Smoothness and the derivative of the tube map -/

section smooth

variable {lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}

theorem contMDiff_Gamb (hlam : ContDiff ℝ ∞ lam) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ (Gamb F lam) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ (fun q : F.N × EuclideanSpace ℝ (Fin p) => emb F q.1) :=
    (contMDiff_emb F).comp contMDiff_fst
  have h2 : ∀ i : Fin p, ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞
      (fun q : F.N × EuclideanSpace ℝ (Fin p) => (lam q.2) i • F.v i q.1) := fun i => by
    have hc : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        𝓘(ℝ, ℝ) ∞ (fun q : F.N × EuclideanSpace ℝ (Fin p) => (lam q.2) i) :=
      (contMDiff_iff_contDiff.2 ((EuclideanSpace.proj i).contDiff.comp hlam)).comp contMDiff_snd
    exact hc.smul ((F.smooth i).comp contMDiff_fst)
  exact h1.add (contMDiff_finset_sum' Finset.univ fun i _ => h2 i)

theorem norm_sum_smul_le {C : ℝ} (hC : ∀ i x, ‖F.v i x‖ ≤ C) (t : EuclideanSpace ℝ (Fin p))
    (x : F.N) : ‖∑ i, t i • F.v i x‖ ≤ p * (‖t‖ * C) := by
  calc ‖∑ i, t i • F.v i x‖ ≤ ∑ i, ‖t i • F.v i x‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin p, ‖t‖ * C := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le t i) (hC i x) (norm_nonneg _) (norm_nonneg _)
    _ = p * (‖t‖ * C) := by simp

theorem Gamb_mem_Nε {C b : ℝ} (hC : ∀ i x, ‖F.v i x‖ ≤ C) (hb : ∀ t, ‖lam t‖ ≤ b) (hC0 : 0 ≤ C)
    (hbC : p * (b * C) < Tub.tubε hM hMc hne) (q : F.N × EuclideanSpace ℝ (Fin p)) :
    Gamb F lam q ∈ Tub.Nε hM hMc hne := by
  show infDist (Gamb F lam q) M < _
  calc infDist (Gamb F lam q) M ≤ dist (Gamb F lam q) (emb F q.1) :=
        infDist_le_dist_of_mem q.1.1.2
    _ = ‖∑ i, (lam q.2) i • F.v i q.1‖ := by
        rw [dist_eq_norm]; simp [Gamb]
    _ ≤ p * (‖lam q.2‖ * C) := norm_sum_smul_le F hC _ _
    _ ≤ p * (b * C) := by
        gcongr
        exact hb _
    _ < Tub.tubε hM hMc hne := hbC

theorem contMDiff_Gx (hlam : ContDiff ℝ ∞ lam) (hmem : ∀ q, Gamb F lam q ∈ Tub.Nε hM hMc hne) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ (Gx hMc hne F lam) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  intro q
  have h1 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
      (Tub.tubr hM hMc hne) (Gamb F lam q) :=
    (contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (n := ∞)
      (U := ⟨Tub.Nε hM hMc hne, Tub.isOpen_Nε hM hMc hne⟩) (f := Tub.tubr hM hMc hne)
      (x := ⟨Gamb F lam q, hmem q⟩)).1 ((contMDiff_tubr_opens hM hMc hne) ⟨_, hmem q⟩)
  exact h1.comp q ((contMDiff_Gamb F hlam) q)

/-- The derivative of the ambient tube map at `(x, 0)` (with `λ = id` near `0`). -/
theorem hasMFDerivAt_Gamb_zero (hlam_id : ∀ᶠ t in 𝓝 (0 : EuclideanSpace ℝ (Fin p)), lam t = t)
    (x : F.N) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Gamb F lam) (x, 0) (Dg F x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  have h1 : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (fun q : F.N × EuclideanSpace ℝ (Fin p) => emb F q.1) (x, 0)
      ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (emb F) x).comp
        (ContinuousLinearMap.fst ℝ _ _)) :=
    HasMFDerivAt.comp (x, 0) (g := emb F) (f := Prod.fst) (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
      ((contMDiff_emb F).mdifferentiableAt (by simp) : MDifferentiableAt _ _ (emb F) x))
      (hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (M := F.N) (M' := EuclideanSpace ℝ (Fin p)) (x, 0))
  have h2 : ∀ i : Fin p, HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (fun q : F.N × EuclideanSpace ℝ (Fin p) => q.2 i • F.v i q.1) (x, 0)
      (((EuclideanSpace.proj i).comp (ContinuousLinearMap.snd ℝ _ _)).smulRight (F.v i x)) := by
    intro i
    have hc : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        𝓘(ℝ, ℝ) (fun q : F.N × EuclideanSpace ℝ (Fin p) => q.2 i) (x, 0)
        ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp
          (ContinuousLinearMap.snd ℝ _ _)) :=
      have hproj : HasFDerivAt (fun t : EuclideanSpace ℝ (Fin p) => t i)
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
          ((x, (0 : EuclideanSpace ℝ (Fin p))).2) :=
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).hasFDerivAt
      HasMFDerivAt.comp (x, 0) (g := fun t : EuclideanSpace ℝ (Fin p) => t i) (f := Prod.snd)
        hproj.hasMFDerivAt (hasMFDerivAt_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (M := F.N) (M' := EuclideanSpace ℝ (Fin p)) (x, 0))
    have hg : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (fun q : F.N × EuclideanSpace ℝ (Fin p) => F.v i q.1) (x, 0)
        ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (F.v i) x).comp
          (ContinuousLinearMap.fst ℝ _ _)) :=
      HasMFDerivAt.comp (x, 0) (g := F.v i) (f := Prod.fst) (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
        ((F.smooth i).mdifferentiableAt (by simp) : MDifferentiableAt _ _ (F.v i) x))
        (hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (M := F.N) (M' := EuclideanSpace ℝ (Fin p)) (x, 0))
    have h := HasMFDerivAt.smulVec hc hg
    refine HasMFDerivAt.congr_mfderiv h ?_
    show (0 : ℝ) • ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (F.v i) x).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin p)))) +
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ _ _)).smulRight (F.v i x) =
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ _ _)).smulRight (F.v i x)
    rw [zero_smul, zero_add]
  have hsum := hasMFDerivAt_finset_sum (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
    𝓘(ℝ, EuclideanSpace ℝ (Fin p))) Finset.univ (fun i _ => h2 i)
  have hid : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (Gamb F id) (x, 0) (Dg F x) := h1.add hsum
  refine hid.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ q in 𝓝 ((x, (0 : EuclideanSpace ℝ (Fin p)))), lam q.2 = q.2 :=
    (continuous_snd.tendsto (x, (0 : EuclideanSpace ℝ (Fin p)))).eventually hlam_id
  filter_upwards [hev] with q hq
  simp only [Gamb, hq, id]

end smooth

/-! ### The retraction fixes tangent vectors -/

theorem mem_Nε_of_mem (y : M) : y.1 ∈ Tub.Nε hM hMc hne := by
  show infDist y.1 M < _
  rw [infDist_zero_of_mem y.2]
  exact Tub.tubε_pos hM hMc hne

theorem fderiv_tubr_of_mem (y : M) :
    ∀ w ∈ tangentM hM y, fderiv ℝ (fun z => (Tub.tubr hM hMc hne z).1) y.1 w = w := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hd : ContDiffAt ℝ ∞ (fun z => (Tub.tubr hM hMc hne z).1) y.1 :=
    (Tub.tubr_spec hM hMc hne).2.2.2.1 y.1 (mem_Nε_of_mem hMc hne y)
  have hval := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
    (hM.contMDiff_val.mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) y)
  have h1 := ((hd.differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt).comp y hval
  have heq : ((fun z => (Tub.tubr hM hMc hne z).1) ∘ (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1)))) =
      Subtype.val := funext fun z => (Tub.tubr_spec hM hMc hne).2.2.1 z.1 z.2
  rw [heq] at h1
  have h2 := hasMFDerivAt_unique h1 hval
  have h2' : (fderiv ℝ (fun z => (Tub.tubr hM hMc hne z).1) y.1).comp
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) y) =
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) y := h2
  intro w hw
  obtain ⟨a, rfl⟩ := hw
  have := congrArg (fun L : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (K + 1)) => L a) h2'
  simpa using this

/-! ### Bijectivity of the derivative at `(x, 0)` -/

section deriv

variable {lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)} (hlam : ContDiff ℝ ∞ lam)
  (hlam_id : ∀ᶠ t in 𝓝 (0 : EuclideanSpace ℝ (Fin p)), lam t = t)
  (hmem : ∀ q, Gamb F lam q ∈ Tub.Nε hM hMc hne)

include hlam hlam_id hmem in
theorem mfd_val_Gx_zero (x : F.N) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (fun q => (Gx hMc hne F lam q).1) (x, 0) =
      (fderiv ℝ (fun z => (Tub.tubr hM hMc hne z).1) (emb F x)).comp (Dg F x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  have hlam0 : lam 0 = 0 := hlam_id.self_of_nhds
  have hd : ContDiffAt ℝ ∞ (fun z => (Tub.tubr hM hMc hne z).1) (emb F x) :=
    (Tub.tubr_spec hM hMc hne).2.2.2.1 _ (mem_Nε_of_mem hMc hne x.1)
  have h3 : Gamb F lam (x, 0) = emb F x := Gamb_zero F hlam0 x
  have hd' : ContDiffAt ℝ ∞ (fun z => (Tub.tubr hM hMc hne z).1) (Gamb F lam (x, 0)) := by
    rw [h3]; exact hd
  have h1 := ((hd'.differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt)
  have h2 := hasMFDerivAt_Gamb_zero F hlam_id x
  have h4 := HasMFDerivAt.mfd_eq (h1.comp (x, 0) h2)
  rw [h3] at h4
  exact h4

include hlam hlam_id hmem in
theorem injective_mfd_Gx_zero (x : F.N) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    Injective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (Gx hMc hne F lam) (x, 0)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  have hval := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
    (hM.contMDiff_val.mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) (Gx hMc hne F lam (x, 0)))
  have hG := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    ((contMDiff_Gx hMc hne F hlam hmem).mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (Gx hMc hne F lam) (x, 0))
  have hchain := HasMFDerivAt.mfd_eq (hval.comp (x, 0) hG)
  have hchain' : mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (fun q => (Gx hMc hne F lam q).1) (x, 0) =
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) (Gx hMc hne F lam (x, 0))).comp
      (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (Gx hMc hne F lam) (x, 0)) := hchain
  rw [mfd_val_Gx_zero hMc hne F hlam hlam_id hmem x] at hchain'
  intro a b hab
  have h1 : (fderiv ℝ (fun z => (Tub.tubr hM hMc hne z).1) (emb F x)).comp (Dg F x) a =
      (fderiv ℝ (fun z => (Tub.tubr hM hMc hne z).1) (emb F x)).comp (Dg F x) b := by
    rw [hchain']
    simp only [ContinuousLinearMap.comp_apply, hab]
  simp only [ContinuousLinearMap.comp_apply, emb] at h1
  rw [fderiv_tubr_of_mem hMc hne x.1 _ (Dg_mem_tangentM F x a),
    fderiv_tubr_of_mem hMc hne x.1 _ (Dg_mem_tangentM F x b)] at h1
  exact Dg_injective F x h1

include hlam hlam_id hmem in
theorem bijective_mfd_Gx_zero (x : F.N) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (Gx hMc hne F lam) (x, 0)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  have hinj := injective_mfd_Gx_zero hMc hne F hlam hlam_id hmem x
  refine ⟨hinj, ?_⟩
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) =
      finrank ℝ (EuclideanSpace ℝ (Fin m)) := by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    exact F.dim
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj

end deriv

end Framed

end Milnor
