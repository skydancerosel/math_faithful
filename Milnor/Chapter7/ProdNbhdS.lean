import Milnor.Chapter7.ProdNbhdM
import Milnor.Chapter7.Equiv

/-!
# The tube map of a framed cobordism `S ⊆ M × ℝ`

The analogue of `ProdNbhdM.lean` for the `(n+1)`-dimensional framed submanifold `S` of
`M × ℝ`: the map `G(q, s) = r'(q + ∑ sᵢ uᵢ(q))` with `r' = r × id` the retraction of
`ℝᴷ⁺¹ × ℝ` onto `M × ℝ`.  Its derivative at `(q, 0)` is `(a, s) ↦ dq(a) + ∑ sᵢ uᵢ(q)`,
which is bijective.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} (hMc : IsCompact M) (hne : M.Nonempty)
  {n p : ℕ} {F₀ F₁ : FramedSub hM n p} (X : FramedCob hM F₀ F₁)

/-! ### The inclusion `S → ℝᴷ⁺¹ × ℝ` -/

/-- The inclusion of `S` in the ambient space. -/
def embS (X : FramedCob hM F₀ F₁) (q : X.S) : EuclideanSpace ℝ (Fin (K + 1)) × ℝ := embXR q.1

theorem contMDiff_embS :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := X.hS.chartedSpace;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞
      (embS X) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  exact (contMDiff_embXR hM).comp X.hS.contMDiff_val

/-- The derivative of `embXR`. -/
theorem hasMFDerivAt_embXR (q : M × ℝ) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (embXR (M := M)) q
      (((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) q.1).comp
        (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h1 := HasMFDerivAt.comp q (g := (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))))
    (f := Prod.fst) (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
      (hM.contMDiff_val.mdifferentiableAt (by simp) :
        MDifferentiableAt _ _ (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) q.1))
    (hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ)) (M := M) (M' := ℝ) q)
  have h2 := hasMFDerivAt_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ)) (M := M)
    (M' := ℝ) q
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact h1.prodMk h2

theorem injective_mfd_embS (q : X.S) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := X.hS.chartedSpace;
    Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (embS X) q) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  haveI := X.hS.isManifold
  have h1 := hasMFDerivAt_embXR (hM := hM) q.1
  have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
    (X.hS.contMDiff_val.mdifferentiableAt (by simp) : MDifferentiableAt _ _ (Subtype.val : X.S → M × ℝ) q)
  have h3 := HasMFDerivAt.mfd_eq (h1.comp q h2)
  have h4 : (embXR (M := M) ∘ (Subtype.val : X.S → M × ℝ)) = embS X := rfl
  rw [h4] at h3
  have h3' : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (embS X) q = (((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) q.1.1).comp
        (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          (Subtype.val : X.S → M × ℝ) q) := h3
  rw [h3']
  have hinj1 : Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) q.1.1) := injective_mfderiv_val hM q.1.1
  have hinj2 : Injective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) (Subtype.val : X.S → M × ℝ) q) :=
    injective_mfderiv_val X.hS q
  rw [ContinuousLinearMap.coe_comp]
  refine Injective.comp ?_ hinj2
  intro a b hab
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.mk.injEq] at hab
  exact Prod.ext (hinj1 hab.1) hab.2

theorem tangentS_fst_mem (q : X.S) {w : EuclideanSpace ℝ (Fin (K + 1)) × ℝ}
    (hw : w ∈ tangentS hM X.hS q) : w.1 ∈ tangentM hM q.1.1 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  haveI := X.hS.isManifold
  obtain ⟨a, rfl⟩ := hw
  have h1 := hasMFDerivAt_embXR (hM := hM) q.1
  have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
    (X.hS.contMDiff_val.mdifferentiableAt (by simp) : MDifferentiableAt _ _ (Subtype.val : X.S → M × ℝ) q)
  have h3 := HasMFDerivAt.mfd_eq (h1.comp q h2)
  have h4 : (embXR (M := M) ∘ (Subtype.val : X.S → M × ℝ)) = fun r : X.S => embXR r.1 := rfl
  rw [h4] at h3
  have h3' : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (fun r : X.S => embXR r.1) q =
      (((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) q.1.1).comp
        (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
          (Subtype.val : X.S → M × ℝ) q) := h3
  show (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
    (fun r : X.S => embXR r.1) q a).1 ∈ tangentM hM q.1.1
  rw [h3']
  exact ⟨_, rfl⟩

/-! ### The derivative of the tube map at `(q, 0)` -/

/-- `DgS q (a, s) = dq(a) + ∑ sᵢ uᵢ(q)`. -/
def DgS (q : X.S) : EuclideanSpace ℝ (Fin (n + 1)) × EuclideanSpace ℝ (Fin p) →L[ℝ]
    EuclideanSpace ℝ (Fin (K + 1)) × ℝ :=
  letI := hM.chartedSpace; haveI := hM.isManifold; letI := X.hS.chartedSpace;
  (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (embS X) q).comp
    (ContinuousLinearMap.fst ℝ _ _) +
  ∑ i : Fin p, ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.snd ℝ _ _)).smulRight (X.u i q)

theorem DgS_apply (q : X.S) (a : EuclideanSpace ℝ (Fin (n + 1))) (s : EuclideanSpace ℝ (Fin p)) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := X.hS.chartedSpace;
    DgS X q (a, s) = mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (embS X) q a + ∑ i : Fin p, s i • X.u i q := by
  simp [DgS]

theorem DgS_fst_mem_tangentM (q : X.S) (w : EuclideanSpace ℝ (Fin (n + 1)) × EuclideanSpace ℝ (Fin p)) :
    (DgS X q w).1 ∈ tangentM hM q.1.1 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  obtain ⟨a, s⟩ := w
  rw [DgS_apply]
  simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst]
  refine Submodule.add_mem _ (tangentS_fst_mem X q ⟨a, rfl⟩) ?_
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (X.tangent i q)

theorem DgS_injective (q : X.S) : Injective (DgS X q) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨a, s⟩ h
  rw [DgS_apply] at h
  have hperp : ipXR (∑ i : Fin p, s i • X.u i q) (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (embS X) q a) = 0 := by
    have hlin : ∀ (v v' : EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (w : EuclideanSpace ℝ (Fin (K + 1)) × ℝ),
        ipXR (v + v') w = ipXR v w + ipXR v' w := fun v v' w => by
      simp only [ipXR, Prod.fst_add, Prod.snd_add, inner_add_left]; ring
    have hsmul : ∀ (c : ℝ) (v w : EuclideanSpace ℝ (Fin (K + 1)) × ℝ),
        ipXR (c • v) w = c * ipXR v w := fun c v w => by
      simp only [ipXR, Prod.smul_fst, Prod.smul_snd, real_inner_smul_left, smul_eq_mul]; ring
    have hsum : ∀ (t : Finset (Fin p)) (w : EuclideanSpace ℝ (Fin (K + 1)) × ℝ),
        ipXR (∑ i ∈ t, s i • X.u i q) w = ∑ i ∈ t, s i * ipXR (X.u i q) w := by
      intro t w
      classical
      induction t using Finset.induction_on with
      | empty => simp [ipXR]
      | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hlin, hsmul, ih]
    rw [hsum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hn : ipXR (X.u i q) (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (embS X) q a) = 0 := X.normal i q _ ⟨a, rfl⟩
    rw [hn, mul_zero]
  have hzero : mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (embS X) q a = 0 := by
    set v := mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (embS X) q a with hv
    have hself : ipXR v v = 0 := by
      have h2 := congrArg (fun z => ipXR z v) h
      simp only [ipXR, Prod.fst_add, Prod.snd_add, inner_add_left, Prod.fst_zero, Prod.snd_zero,
        inner_zero_left] at h2 hperp ⊢
      linear_combination h2 - hperp
    simp only [ipXR, real_inner_self_eq_norm_sq] at hself
    have h1 : ‖v.1‖ = 0 := by nlinarith [sq_nonneg (‖v.1‖), sq_nonneg v.2, norm_nonneg v.1]
    have h2 : v.2 = 0 := by nlinarith [sq_nonneg (‖v.1‖), sq_nonneg v.2]
    exact Prod.ext (norm_eq_zero.1 h1) h2
  have ha : a = 0 := injective_mfd_embS X q (by rw [hzero, map_zero])
  rw [hzero, zero_add] at h
  have hs : s = 0 := by
    have := (Fintype.linearIndependent_iff.1 (X.indep q)) s h
    ext i
    simp [this i]
  rw [ha, hs]; rfl

/-! ### The tube map -/

/-- The ambient tube map. -/
def GambS (lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (q : X.S × EuclideanSpace ℝ (Fin p)) : EuclideanSpace ℝ (Fin (K + 1)) × ℝ :=
  embS X q.1 + ∑ i : Fin p, (lam q.2) i • X.u i q.1

/-- The tube map into `M × ℝ`. -/
def GxS (lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (q : X.S × EuclideanSpace ℝ (Fin p)) : M × ℝ :=
  (Tub.tubr hM hMc hne (GambS X lam q).1, (GambS X lam q).2)

theorem GambS_zero {lam} (hlam0 : lam 0 = 0) (q : X.S) : GambS X lam (q, 0) = embS X q := by
  simp [GambS, hlam0]

theorem GxS_zero {lam} (hlam0 : lam 0 = 0) (q : X.S) : GxS hMc hne X lam (q, 0) = q.1 := by
  unfold GxS
  rw [GambS_zero X hlam0]
  exact Prod.ext (tubr_mem_of_mem hM hMc hne q.1.1.2) rfl

theorem GxS_zero_injective {lam} (hlam0 : lam 0 = 0) (q q' : X.S)
    (h : GxS hMc hne X lam (q, 0) = GxS hMc hne X lam (q', 0)) : q = q' := by
  rw [GxS_zero hMc hne X hlam0, GxS_zero hMc hne X hlam0] at h
  exact Subtype.ext h

/-- A bound on the framing of `S`: `S` is not compact, but it is a product near the ends,
where the framing is the (bounded) framing of `N₀` resp. `N₁`, and compact in between. -/
theorem exists_bound_u : ∃ C : ℝ, 0 < C ∧ ∀ i q, ‖X.u i q‖ ≤ C := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  obtain ⟨C₀, hC₀, hv₀⟩ := exists_bound_v F₀
  obtain ⟨C₁, hC₁, hv₁⟩ := exists_bound_v F₁
  -- the compact middle region
  have hcpt : IsCompact {q : X.S | 0 ≤ q.1.2 ∧ q.1.2 ≤ 1} := by
    rw [Subtype.isCompact_iff]
    convert X.compact using 1
    ext q
    constructor
    · rintro ⟨⟨q', hq'⟩, ⟨h0, h1⟩, rfl⟩
      exact ⟨hq', h0, h1⟩
    · rintro ⟨hq, h0, h1⟩
      exact ⟨⟨q, hq⟩, ⟨h0, h1⟩, rfl⟩
  have hb : ∀ i, ∃ C, ∀ q : X.S, 0 ≤ q.1.2 → q.1.2 ≤ 1 → ‖X.u i q‖ ≤ C := fun i => by
    have hcont : ContinuousOn (fun q : X.S => ‖X.u i q‖) {q : X.S | 0 ≤ q.1.2 ∧ q.1.2 ≤ 1} :=
      (X.smooth i).continuous.norm.continuousOn
    obtain ⟨C, hC⟩ := hcpt.bddAbove_image hcont
    exact ⟨C, fun q h0 h1 => hC ⟨q, ⟨h0, h1⟩, rfl⟩⟩
  choose C hC using hb
  have hCc : 0 ≤ ∑ i, max (C i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
  have hnorm : ∀ v : EuclideanSpace ℝ (Fin (K + 1)),
      ‖((v, (0 : ℝ)) : EuclideanSpace ℝ (Fin (K + 1)) × ℝ)‖ = ‖v‖ := fun v => by
    rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]
  refine ⟨C₀ + C₁ + ∑ i, max (C i) 0 + 1, by linarith, fun i q => ?_⟩
  by_cases h0 : q.1.2 < X.ε
  · have hq : q.1.1 ∈ F₀.N := (X.end0 q.1 h0).1 q.2
    rw [X.u_end0 i q hq h0, hnorm]
    linarith [hv₀ i ⟨q.1.1, hq⟩]
  by_cases h1 : 1 - X.ε < q.1.2
  · have hq : q.1.1 ∈ F₁.N := (X.end1 q.1 h1).1 q.2
    rw [X.u_end1 i q hq h1, hnorm]
    linarith [hv₁ i ⟨q.1.1, hq⟩]
  have h0' := not_lt.1 h0
  have h1' := not_lt.1 h1
  have h2 := hC i q (by linarith [X.hε]) (by linarith [X.hε])
  have h3 : max (C i) 0 ≤ ∑ j, max (C j) 0 :=
    Finset.single_le_sum (fun j _ => le_max_right (C j) 0) (Finset.mem_univ i)
  linarith [le_max_left (C i) 0]

/-! ### Smoothness and the derivative of the tube map -/

section smooth

variable {lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}

theorem contMDiff_GambS (hlam : ContDiff ℝ ∞ lam) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := X.hS.chartedSpace;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞ (GambS X lam) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  haveI := X.hS.isManifold
  have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞
      (fun q : X.S × EuclideanSpace ℝ (Fin p) => embS X q.1) :=
    (contMDiff_embS X).comp contMDiff_fst
  have h2 : ∀ i : Fin p, ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) ∞
      (fun q : X.S × EuclideanSpace ℝ (Fin p) => (lam q.2) i • X.u i q.1) := fun i => by
    have hc : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        𝓘(ℝ, ℝ) ∞ (fun q : X.S × EuclideanSpace ℝ (Fin p) => (lam q.2) i) :=
      (contMDiff_iff_contDiff.2 ((EuclideanSpace.proj i).contDiff.comp hlam)).comp contMDiff_snd
    exact hc.smul ((X.smooth i).comp contMDiff_fst)
  exact h1.add (contMDiff_finset_sum' Finset.univ fun i _ => h2 i)

theorem norm_sum_smul_le' {C : ℝ} (hC : ∀ i q, ‖X.u i q‖ ≤ C) (t : EuclideanSpace ℝ (Fin p))
    (q : X.S) : ‖∑ i, t i • X.u i q‖ ≤ p * (‖t‖ * C) := by
  calc ‖∑ i, t i • X.u i q‖ ≤ ∑ i, ‖t i • X.u i q‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin p, ‖t‖ * C := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le t i) (hC i q) (norm_nonneg _) (norm_nonneg _)
    _ = p * (‖t‖ * C) := by simp

theorem GambS_fst_mem_Nε {C b : ℝ} (hC : ∀ i q, ‖X.u i q‖ ≤ C) (hb : ∀ t, ‖lam t‖ ≤ b)
    (hC0 : 0 ≤ C) (hbC : p * (b * C) < Tub.tubε hM hMc hne)
    (q : X.S × EuclideanSpace ℝ (Fin p)) : (GambS X lam q).1 ∈ Tub.Nε hM hMc hne := by
  show infDist (GambS X lam q).1 M < _
  calc infDist (GambS X lam q).1 M ≤ dist (GambS X lam q).1 q.1.1.1.1 :=
        infDist_le_dist_of_mem q.1.1.1.2
    _ ≤ ‖∑ i, (lam q.2) i • X.u i q.1‖ := by
        rw [dist_eq_norm]
        have : (GambS X lam q).1 - q.1.1.1.1 = (∑ i, (lam q.2) i • X.u i q.1).1 := by
          simp only [GambS, embS, embXR, Prod.fst_add, add_sub_cancel_left]
        rw [this]
        exact norm_fst_le _
    _ ≤ p * (‖lam q.2‖ * C) := norm_sum_smul_le' X hC _ _
    _ ≤ p * (b * C) := by
        gcongr
        exact hb _
    _ < Tub.tubε hM hMc hne := hbC

theorem contMDiff_GxS (hlam : ContDiff ℝ ∞ lam)
    (hmem : ∀ q, (GambS X lam q).1 ∈ Tub.Nε hM hMc hne) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := X.hS.chartedSpace;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) ∞ (GxS hMc hne X lam) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  haveI := X.hS.isManifold
  have hG := contMDiff_GambS X hlam
  have hfst : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) ∞ (fun q => (GambS X lam q).1) :=
    (contMDiff_iff_contDiff.2 contDiff_fst).comp hG
  have hsnd : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, ℝ) ∞ (fun q => (GambS X lam q).2) :=
    (contMDiff_iff_contDiff.2 contDiff_snd).comp hG
  have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ (fun q => Tub.tubr hM hMc hne (GambS X lam q).1) := by
    intro q
    have h1 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞
        (Tub.tubr hM hMc hne) (GambS X lam q).1 :=
      (contMDiffAt_subtype_iff (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (n := ∞)
        (U := ⟨Tub.Nε hM hMc hne, Tub.isOpen_Nε hM hMc hne⟩) (f := Tub.tubr hM hMc hne)
        (x := ⟨(GambS X lam q).1, hmem q⟩)).1 ((contMDiff_tubr_opens hM hMc hne) ⟨_, hmem q⟩)
    exact h1.comp q (hfst q)
  exact h1.prodMk hsnd

/-- The derivative of the ambient tube map at `(q, 0)` (with `λ = id` near `0`). -/
theorem hasMFDerivAt_GambS_zero
    (hlam_id : ∀ᶠ t in 𝓝 (0 : EuclideanSpace ℝ (Fin p)), lam t = t) (q : X.S) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := X.hS.chartedSpace;
    HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (GambS X lam) (q, 0) (DgS X q) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  haveI := X.hS.isManifold
  have h1 : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (fun r : X.S × EuclideanSpace ℝ (Fin p) => embS X r.1) (q, 0)
      ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
        (embS X) q).comp (ContinuousLinearMap.fst ℝ _ _)) :=
    HasMFDerivAt.comp (q, 0) (g := embS X) (f := Prod.fst)
      (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
        (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ))
        ((contMDiff_embS X).mdifferentiableAt (by simp) : MDifferentiableAt _ _ (embS X) q))
      (hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (M := X.S) (M' := EuclideanSpace ℝ (Fin p)) (q, 0))
  have h2 : ∀ i : Fin p, HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin p))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
      (fun r : X.S × EuclideanSpace ℝ (Fin p) => r.2 i • X.u i r.1) (q, 0)
      (((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ _ _)).smulRight (X.u i q)) := by
    intro i
    have hc : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        𝓘(ℝ, ℝ) (fun r : X.S × EuclideanSpace ℝ (Fin p) => r.2 i) (q, 0)
        ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp
          (ContinuousLinearMap.snd ℝ _ _)) :=
      have hproj : HasFDerivAt (fun t : EuclideanSpace ℝ (Fin p) => t i)
          (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ)
          ((q, (0 : EuclideanSpace ℝ (Fin p))).2) :=
        (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).hasFDerivAt
      HasMFDerivAt.comp (q, 0) (g := fun t : EuclideanSpace ℝ (Fin p) => t i) (f := Prod.snd)
        hproj.hasMFDerivAt (hasMFDerivAt_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
          (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (M := X.S) (M' := EuclideanSpace ℝ (Fin p)) (q, 0))
    have hg : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
        (fun r : X.S × EuclideanSpace ℝ (Fin p) => X.u i r.1) (q, 0)
        ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
          (X.u i) q).comp (ContinuousLinearMap.fst ℝ _ _)) :=
      HasMFDerivAt.comp (q, 0) (g := X.u i) (f := Prod.fst)
        (hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
          (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ))
          ((X.smooth i).mdifferentiableAt (by simp) : MDifferentiableAt _ _ (X.u i) q))
        (hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
          (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (M := X.S) (M' := EuclideanSpace ℝ (Fin p)) (q, 0))
    have h := HasMFDerivAt.smulVec hc hg
    refine HasMFDerivAt.congr_mfderiv h ?_
    show (0 : ℝ) • ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ)
        (X.u i) q).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)))) +
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ _ _)).smulRight (X.u i q) =
      ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ _ _)).smulRight (X.u i q)
    rw [zero_smul, zero_add]
  have hsum := hasMFDerivAt_finset_sum (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod
    𝓘(ℝ, EuclideanSpace ℝ (Fin p))) Finset.univ (fun i _ => h2 i)
  have hid : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (GambS X id) (q, 0) (DgS X q) := h1.add hsum
  refine hid.congr_of_eventuallyEq ?_
  have hev : ∀ᶠ r in 𝓝 ((q, (0 : EuclideanSpace ℝ (Fin p)))), lam r.2 = r.2 :=
    (continuous_snd.tendsto (q, (0 : EuclideanSpace ℝ (Fin p)))).eventually hlam_id
  filter_upwards [hev] with r hr
  simp only [GambS, hr, id]

end smooth

/-! ### The retraction `r × id` fixes vectors tangent to `M × ℝ` -/

theorem fderiv_tubr'_of_mem (z : M × ℝ) :
    ∀ w : EuclideanSpace ℝ (Fin (K + 1)) × ℝ, w.1 ∈ tangentM hM z.1 →
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (K + 1)) × ℝ => ((Tub.tubr hM hMc hne y.1).1, y.2))
        (embXR z) w = w := by
  intro w hw
  have hd : ContDiffAt ℝ ∞ (fun y => (Tub.tubr hM hMc hne y).1) z.1.1 :=
    (Tub.tubr_spec hM hMc hne).2.2.2.1 z.1.1 (mem_Nε_of_mem hMc hne z.1)
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (K + 1)) × ℝ => (Tub.tubr hM hMc hne y.1).1)
      ((fderiv ℝ (fun y => (Tub.tubr hM hMc hne y).1) z.1.1).comp
        (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin (K + 1))) ℝ)) (embXR z) :=
    HasFDerivAt.comp (embXR z) (g := fun y => (Tub.tubr hM hMc hne y).1) (f := Prod.fst)
      (hd.differentiableAt (by simp)).hasFDerivAt hasFDerivAt_fst
  have h2 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (K + 1)) × ℝ => y.2)
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (K + 1))) ℝ) (embXR z) := hasFDerivAt_snd
  rw [(h1.prodMk h2).fderiv]
  refine Prod.ext ?_ ?_
  · simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst']
    exact fderiv_tubr_of_mem hMc hne z.1 w.1 hw
  · simp

/-! ### Bijectivity of the derivative at `(q, 0)` -/

section deriv

variable {lam : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)} (hlam : ContDiff ℝ ∞ lam)
  (hlam_id : ∀ᶠ t in 𝓝 (0 : EuclideanSpace ℝ (Fin p)), lam t = t)
  (hmem : ∀ q, (GambS X lam q).1 ∈ Tub.Nε hM hMc hne)

include hlam hlam_id hmem in
theorem mfd_embXR_GxS_zero (q : X.S) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := X.hS.chartedSpace;
    mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (fun r => embXR (GxS hMc hne X lam r)) (q, 0) =
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (K + 1)) × ℝ => ((Tub.tubr hM hMc hne y.1).1, y.2))
        (embS X q)).comp (DgS X q) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  haveI := X.hS.isManifold
  have hlam0 : lam 0 = 0 := hlam_id.self_of_nhds
  have hd : ContDiffAt ℝ ∞ (fun y => (Tub.tubr hM hMc hne y).1) (embS X q).1 :=
    (Tub.tubr_spec hM hMc hne).2.2.2.1 _ (mem_Nε_of_mem hMc hne q.1.1)
  have hd' : ContDiffAt ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (K + 1)) × ℝ => ((Tub.tubr hM hMc hne y.1).1, y.2))
      (embS X q) :=
    (ContDiffAt.comp (embS X q) (g := fun y => (Tub.tubr hM hMc hne y).1) (f := Prod.fst)
      hd contDiffAt_fst).prodMk contDiffAt_snd
  have h3 : GambS X lam (q, 0) = embS X q := GambS_zero X hlam0 q
  have hd'' : ContDiffAt ℝ ∞
      (fun y : EuclideanSpace ℝ (Fin (K + 1)) × ℝ => ((Tub.tubr hM hMc hne y.1).1, y.2))
      (GambS X lam (q, 0)) := by
    rw [h3]; exact hd'
  have h1 := ((hd''.differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt)
  have h2 := hasMFDerivAt_GambS_zero X hlam_id q
  have h4 := HasMFDerivAt.mfd_eq (h1.comp (q, 0) h2)
  rw [h3] at h4
  exact h4

include hlam hlam_id hmem in
theorem injective_mfd_GxS_zero (q : X.S) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := X.hS.chartedSpace;
    Injective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) (GxS hMc hne X lam) (q, 0)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  haveI := X.hS.isManifold
  have hval := hasMFDerivAt_embXR (hM := hM) (GxS hMc hne X lam (q, 0))
  have hG := hasMFDerivAt_mfd
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
    ((contMDiff_GxS hMc hne X hlam hmem).mdifferentiableAt (by simp) :
      MDifferentiableAt _ _ (GxS hMc hne X lam) (q, 0))
  have hchain := HasMFDerivAt.mfd_eq (hval.comp (q, 0) hG)
  have hchain' : mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)) × ℝ) (fun r => embXR (GxS hMc hne X lam r)) (q, 0) =
      (((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) (GxS hMc hne X lam (q, 0)).1).comp
        (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)).comp
      (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) (GxS hMc hne X lam) (q, 0)) := hchain
  rw [mfd_embXR_GxS_zero hMc hne X hlam hlam_id hmem q] at hchain'
  intro a b hab
  have h1 : (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (K + 1)) × ℝ =>
        ((Tub.tubr hM hMc hne y.1).1, y.2)) (embS X q)).comp (DgS X q) a =
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (K + 1)) × ℝ =>
        ((Tub.tubr hM hMc hne y.1).1, y.2)) (embS X q)).comp (DgS X q) b := by
    rw [hchain']
    simp only [ContinuousLinearMap.comp_apply, hab]
  simp only [ContinuousLinearMap.comp_apply] at h1
  have he : embS X q = embXR q.1 := rfl
  rw [he, fderiv_tubr'_of_mem hMc hne q.1 _ (DgS_fst_mem_tangentM X q a),
    fderiv_tubr'_of_mem hMc hne q.1 _ (DgS_fst_mem_tangentM X q b)] at h1
  exact DgS_injective X q h1

include hlam hlam_id hmem in
theorem bijective_mfd_GxS_zero (q : X.S) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := X.hS.chartedSpace;
    Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) (GxS hMc hne X lam) (q, 0)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := X.hS.chartedSpace
  have hinj := injective_mfd_GxS_zero hMc hne X hlam hlam_id hmem q
  refine ⟨hinj, ?_⟩
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)) × EuclideanSpace ℝ (Fin p)) =
      finrank ℝ (EuclideanSpace ℝ (Fin m) × ℝ) := by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin, Module.finrank_self]
    have := F₀.dim
    omega
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj

end deriv

end Framed

end Milnor
