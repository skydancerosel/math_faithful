import Milnor.Chapter8.FramedOps
import Milnor.Chapter7.Lemma2
import Milnor.Chapter7.ThmAconv
import Milnor.Chapter7.CancelMap
import Milnor.Chapter7.MoveMap
import Milnor.Chapter7.Identify
import Milnor.Chapter7.Glue

/-!
# The cohomotopy group `Πᵖ(M)` (Milnor §8, Problem 17, second part)

> If `p ≥ m/2 + 1`, use the disjoint union operation to make `Πᵖ(M)` into an Abelian group.

Here `Πᵖ(M)` is `FramedClass hM hMc hne n p`, the set of framed cobordism classes of framed
submanifolds of `M` of dimension `n` and codimension `p` (`n + p = m`), and `p ≥ m/2 + 1` is
`hbig : m + 2 ≤ 2 * p`; it gives `n + 1 < p`, i.e. `2 (n + 1) < m + 1`, so framed
submanifolds and their cobordisms can be put in general position.

* **Disjoint representatives** (`exists_disjoint_rep`, `CGroup.exists_cobordant_disjoint`): write
  `F` as the Pontryagin manifold of a map `f` at the north pole (Theorem B); the image under `f` of
  another framed submanifold `G` is nowhere dense (Brown's theorem, `n < p`), so there is a regular
  value `z` near the north pole outside it, and moving the regular value along a rotation arc
  (`CGroup.exists_rotCob`, Lemma 2 with the underlying set of the cobordism controlled) gives
  `F ∼ f⁻¹(z)`, disjoint from `G`.
* **Well-definedness** (`framedCobordant_union_of_framedCobordant`): it suffices to move one
  component at a time (`CGroup.union_left_of_framedCobordant`).  If `F ∼ F₁` and `G` is disjoint
  from both, write `F`, `F₁` as Pontryagin manifolds of `f`, `f₁`, join `f` to `f₁` by a homotopy
  `H` (Theorem A), and choose a regular value `z` of `H` near the north pole outside the
  `(n+1)`-dimensional image `H(G × ℝ)`.  The chain `F ∼ f⁻¹(z) ∼ f₁⁻¹(z) ∼ f₁⁻¹(z) ∼ F₁`
  (rotation arc; Lemma 3 for `H`; Lemma 1, changing the scalar of the basis given by Theorem B;
  rotation arc) consists of cobordisms disjoint from `G × ℝ`,
  so their unions with the product cobordism `G × ℝ` (`FramedOps.framedCobordant_union`) give
  `F ⊔ G ∼ F₁ ⊔ G`.
* **The monoid laws** follow from the corresponding identities of disjoint unions
  (`CGroup.union_comm'`, `CGroup.union_assoc'`, `CGroup.union_empty'`).
* **Inverses** (`cohomotopyAdd_negFirst`): on a product neighbourhood `G : N × B_ε → M` of `F`,
  the maps `collapse(C_t(π₂ G⁻¹ z))` with `C_t(s) = (s₀² - a² ρ(t), s₁, …)` (`cancelΦ` of §7) form
  a homotopy whose Pontryagin manifold is empty at `t = 1` and is the union of the two parallel
  copies `G(N × {±a e₀})` at `t = 0` (`CGroup.pontryagin_can0_eq_union`: the framings agree
  because the derivatives agree, `CGroup.At_eq_of_mfd_eq`).  Translating and rescaling
  (`moveΦ` of §7, `CGroup.framedCobordant_fold`) shows that these copies are framed cobordant to
  `F` and to `F` with its first framing vector negated (`FramedSub.negFirst`).

The main results live in `Milnor.Problems`; the auxiliary constructions in
`Milnor.Problems.CGroup`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

namespace Problems

open Sphere Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} {n p : ℕ}

/-! ### The empty framed submanifold and the negated framing -/

/-- **The empty framed submanifold.** -/
def emptyFramedSub (hnp : n + p = m) : FramedSub hM n p where
  N := ∅
  hN := by intro q hq; exact absurd hq (notMem_empty q)
  dim := hnp
  compact := isCompact_empty
  v := fun _ _ => 0
  smooth := fun _ => by intro x; exact absurd x.2 (notMem_empty _)
  tangent := fun _ x => absurd x.2 (notMem_empty _)
  normal := fun _ x => absurd x.2 (notMem_empty _)
  indep := fun x => absurd x.2 (notMem_empty _)

@[simp] theorem emptyFramedSub_N (hnp : n + p = m) : (emptyFramedSub (hM := hM) hnp).N = ∅ := rfl

namespace CGroup

/-- The sign `-1` on the first index, `1` elsewhere. -/
def sgnFirst (hp : 1 ≤ p) (i : Fin p) : ℝ := if i = ⟨0, hp⟩ then -1 else 1

theorem sgnFirst_ne_zero (hp : 1 ≤ p) (i : Fin p) : sgnFirst hp i ≠ 0 := by
  unfold sgnFirst; split_ifs <;> norm_num

end CGroup

open CGroup

/-- **The framed submanifold with the first framing vector negated.** -/
def _root_.Milnor.Framed.FramedSub.negFirst (F : FramedSub hM n p) (hp : 1 ≤ p) :
    FramedSub hM n p where
  N := F.N
  hN := F.hN
  dim := F.dim
  compact := F.compact
  v i x := sgnFirst hp i • F.v i x
  smooth i := by
    letI := hM.chartedSpace
    haveI := hM.isManifold
    letI := F.hN.chartedSpace
    have h1 : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ (fun _ : F.N => sgnFirst hp i) :=
      contMDiff_const
    exact h1.smul (F.smooth i)
  tangent i x := Submodule.smul_mem _ _ (F.tangent i x)
  normal i x w hw := by
    rw [real_inner_smul_left, F.normal i x w hw, mul_zero]
  indep x := by
    have h := (F.indep x).units_smul (fun i => Units.mk0 (sgnFirst hp i) (sgnFirst_ne_zero hp i))
    convert h using 1
    funext i
    simp [Pi.smul_apply', Units.smul_def]

@[simp] theorem _root_.Milnor.Framed.FramedSub.negFirst_N (F : FramedSub hM n p) (hp : 1 ≤ p) :
    (F.negFirst hp).N = F.N := rfl

theorem _root_.Milnor.Framed.FramedSub.negFirst_v (F : FramedSub hM n p) (hp : 1 ≤ p) (i : Fin p)
    (x : F.N) : (F.negFirst hp).v i x = sgnFirst hp i • F.v i x := rfl

namespace CGroup

/-! ### Algebra of disjoint unions -/

theorem union_comm' (F G : FramedSub hM n p) (h : Disjoint F.N G.N) :
    F.union G h = G.union F h.symm := by
  refine FramedSub.ext' hM (Set.union_comm _ _) ?_
  intro i x hx hx'
  by_cases hxF : x ∈ F.N
  · rw [FramedSub.union_v_left i x hxF, FramedSub.union_v_right i x hxF]
  · have hxG : x ∈ G.N := Or.resolve_left hx hxF
    rw [FramedSub.union_v_right i x hxG, FramedSub.union_v_left i x hxG]

theorem union_assoc' (F G H : FramedSub hM n p) (hFG : Disjoint F.N G.N) (hGH : Disjoint G.N H.N)
    (h₁ : Disjoint (F.union G hFG).N H.N) (h₂ : Disjoint F.N (G.union H hGH).N) :
    (F.union G hFG).union H h₁ = F.union (G.union H hGH) h₂ := by
  refine FramedSub.ext' hM (Set.union_assoc _ _ _) ?_
  intro i x hx hx'
  by_cases hxF : x ∈ F.N
  · have e1 := FramedSub.union_v_left (F := F.union G hFG) (G := H) (h := h₁) i x (Or.inl hxF) hx
    have e2 := FramedSub.union_v_left (F := F) (G := G) (h := hFG) i x hxF (Or.inl hxF)
    have e3 := FramedSub.union_v_left (F := F) (G := G.union H hGH) (h := h₂) i x hxF hx'
    exact e1.trans (e2.trans e3.symm)
  · by_cases hxG : x ∈ G.N
    · have e1 := FramedSub.union_v_left (F := F.union G hFG) (G := H) (h := h₁) i x (Or.inr hxG) hx
      have e2 := FramedSub.union_v_right (F := F) (G := G) (h := hFG) i x hxG (Or.inr hxG)
      have e3 := FramedSub.union_v_right (F := F) (G := G.union H hGH) (h := h₂) i x
        (Or.inl hxG) hx'
      have e4 := FramedSub.union_v_left (F := G) (G := H) (h := hGH) i x hxG (Or.inl hxG)
      exact e1.trans (e2.trans (e3.trans e4).symm)
    · have hxH : x ∈ H.N := by
        have hx2 : x ∈ (F.N ∪ G.N) ∪ H.N := hx
        rcases hx2 with (h | h) | h
        · exact absurd h hxF
        · exact absurd h hxG
        · exact h
      have e1 := FramedSub.union_v_right (F := F.union G hFG) (G := H) (h := h₁) i x hxH hx
      have e3 := FramedSub.union_v_right (F := F) (G := G.union H hGH) (h := h₂) i x
        (Or.inr hxH) hx'
      have e4 := FramedSub.union_v_right (F := G) (G := H) (h := hGH) i x hxH (Or.inr hxH)
      exact e1.trans (e3.trans e4).symm

theorem union_empty' (F : FramedSub hM n p) (h : Disjoint F.N (emptyFramedSub (hM := hM) F.dim).N) :
    F.union (emptyFramedSub F.dim) h = F := by
  refine FramedSub.ext' hM (Set.union_empty _) ?_
  intro i x hx hx'
  exact FramedSub.union_v_left i x hx' hx

theorem eq_empty_of_N (F : FramedSub hM n p) (h : F.N = ∅) : F = emptyFramedSub F.dim :=
  FramedSub.ext' hM h (fun i x hx _ => by rw [h] at hx; exact absurd hx (notMem_empty x))

/-! ### Framed cobordisms with a controlled underlying set -/

/-- Transport of a framed cobordism with a property of its underlying set along equalities of the
ends. -/
theorem exists_framedCob_congr {A B A' B' : FramedSub hM n p} (hA : A = A') (hB : B = B')
    {P : Set (M × ℝ) → Prop} (h : ∃ X : FramedCob hM A B, P X.S) :
    ∃ X : FramedCob hM A' B', P X.S := by
  subst hA hB; exact h

variable (hMc : IsCompact M) (hne : M.Nonempty)

include hMc hne in
/-- **The product cobordism** `G × ℝ` of a framed submanifold. -/
theorem exists_framedCob_prod (G : FramedSub hM n p) :
    ∃ X : FramedCob hM G G, X.S = {q : M × ℝ | q.1 ∈ G.N} := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨k, hk, hkn, c, hc, hcb, hkG⟩ :=
    exists_map_of_framedSub hM hMc hne G _ (linearIndependent_single (m := p))
  have hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      ∞ (fun q : M × ℝ => k q.1) :=
    hk.comp contMDiff_fst
  have h := exists_framedCob_of_homotopy hM hMc hne G.dim (ε := 1 / 4) (by norm_num)
    (by norm_num) hH (isRegularValue_comp_fst hM hk hkn) (fun x t _ => rfl)
    (fun x t _ => rfl) hk hkn hk hkn _ hcb
  have hN : k ⁻¹' {north} = G.N := congrArg FramedSub.N hkG
  refine exists_framedCob_congr (P := fun S => S = {q : M × ℝ | q.1 ∈ G.N}) hkG hkG ?_
  obtain ⟨X, hX⟩ := h
  refine ⟨X, ?_⟩
  rw [hX, ← hN]
  rfl

/-! ### Images of low-dimensional manifolds (Brown's theorem) -/

/-- The image of `G × ℝ` under a smooth map `M × ℝ → Sᵖ` has dense complement when
`n + 1 < p`: by Brown's theorem regular values are dense, and a point of the image cannot be a
regular value for dimension reasons. -/
theorem dense_compl_range (G : FramedSub hM n p) (hdim : n + 1 < p) {H : M × ℝ → Sph p}
    (hH : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ H) :
    Dense (range (fun q : G.N × ℝ => H (q.1.1, q.2)))ᶜ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := G.hN.chartedSpace
  haveI := G.hN.isManifold
  have hg : ContMDiff ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun q : G.N × ℝ => H (q.1.1, q.2)) :=
    hH.comp ((G.hN.contMDiff_val.comp contMDiff_fst).prodMk contMDiff_snd)
  refine (dense_regularValues hg).mono ?_
  rintro y hy ⟨q, hq⟩
  have hs : Surjective (mfd ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fun q : G.N × ℝ => H (q.1.1, q.2)) q) := hy q hq
  obtain ⟨L, hL⟩ : ∃ L : EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin p),
      mfd ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun q : G.N × ℝ => H (q.1.1, q.2)) q = L := ⟨_, rfl⟩
  rw [hL] at hs
  have h1 := LinearMap.finrank_range_le
    (L : EuclideanSpace ℝ (Fin n) × ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
  have htop : LinearMap.range
      (L : EuclideanSpace ℝ (Fin n) × ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) = ⊤ :=
    LinearMap.range_eq_top.2 hs
  rw [htop, finrank_top] at h1
  simp only [finrank_euclideanSpace_fin, Module.finrank_prod, Module.finrank_self] at h1
  omega

/-- The image of a compact framed submanifold under a continuous map is closed. -/
theorem isClosed_image_N (G : FramedSub hM n p) {f : M → Sph p} (hf : Continuous f) :
    IsClosed (f '' G.N) :=
  (G.compact.image hf).isClosed

/-! ### The rotation homotopy with an explicit formula -/

section rot

variable {u v : EuclideanSpace ℝ (Fin (p + 1))} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u, v⟫ = 0)
  {f : M → Sph p}
  (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)

include hu hv huv hf in
theorem contMDiff_rotHom (θ₀ : ℝ) {ρ : ℝ → ℝ} (hρs : ContDiff ℝ ∞ ρ) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hρ's : ContDiff ℝ ∞ (fun t => θ₀ * ρ t) := contDiff_const.mul hρs
  have hfam : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (fun q : Sph p × ℝ => rotS u v (θ₀ * ρ q.2) q.1) :=
    contMDiff_rotS_family hu hv huv (ρ := fun t => θ₀ * ρ t) hρ's
  have hΨ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ)) ∞ (fun q : M × ℝ => (f q.1, q.2)) :=
    (hf.comp contMDiff_fst).prodMk contMDiff_snd
  have hF's : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ ((fun q : Sph p × ℝ => rotS u v (θ₀ * ρ q.2) q.1) ∘
        fun q : M × ℝ => (f q.1, q.2)) := hfam.comp hΨ
  have heq : ((fun q : Sph p × ℝ => rotS u v (θ₀ * ρ q.2) q.1) ∘
        fun q : M × ℝ => (f q.1, q.2)) = fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1) := by
    funext q; rfl
  rw [heq] at hF's
  exact hF's

include hu hv huv hf in
theorem isRegularValue_rotHom (θ₀ : ℝ) {ρ : ℝ → ℝ} (hρs : ContDiff ℝ ∞ ρ)
    (hρ01 : ∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1) (y : Sph p) (hθ₀ : 0 ≤ θ₀)
    (harc : letI := hM.chartedSpace; haveI := hM.isManifold; ∀ τ, 0 ≤ τ → τ ≤ θ₀ →
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
        (rotS u v τ y)) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) (rotS u v θ₀ y) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hF's := contMDiff_rotHom hu hv huv hf θ₀ hρs
  intro q hq
  have hq' : rotS u v (θ₀ * ρ q.2) (f q.1) = rotS u v θ₀ y := hq
  have hfq : f q.1 = rotS u v (θ₀ - θ₀ * ρ q.2) y := by
    have := congrArg (rotS u v (-(θ₀ * ρ q.2))) hq'
    rw [rotS_neg_rotS hu hv huv, rotS_add hu hv huv] at this
    rw [this]
    congr 1
    ring
  have hρb := hρ01 q.2
  have hreg : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
      (f q.1) := by
    rw [hfq]
    refine harc _ ?_ ?_
    · nlinarith [hρb.2, hθ₀]
    · nlinarith [hρb.1, hθ₀]
  have hr : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
    (rotS u v (θ₀ * ρ q.2)) := contMDiff_rotS hu hv huv _
  have hbij := mfd_rotS_bijective hu hv huv (θ₀ * ρ q.2) (f q.1)
  have hslice : Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun x => rotS u v (θ₀ * ρ q.2) (f x)) q.1) := by
    have h1 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      (hr.mdifferentiableAt (by simp) : MDifferentiableAt _ _ (rotS u v (θ₀ * ρ q.2)) (f q.1))
    have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      (hf.mdifferentiableAt (by simp) : MDifferentiableAt _ _ f q.1)
    have h3 := HasMFDerivAt.mfd_eq (h1.comp q.1 h2)
    have h4 : (rotS u v (θ₀ * ρ q.2) ∘ f) = fun x => rotS u v (θ₀ * ρ q.2) (f x) := rfl
    rw [h4] at h3
    rw [h3]
    exact hbij.2.comp (hreg q.1 rfl)
  have hpart : ∀ a, mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun x => rotS u v (θ₀ * ρ q.2) (f x)) q.1 a =
      mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) q (a, 0) := by
    intro a
    have h1 : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) (fun x : M => (x, q.2)) q.1
        ((ContinuousLinearMap.id ℝ _).prod (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)) :=
      (hasMFDerivAt_id (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) q.1).prodMk
        (hasMFDerivAt_const (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) (I' := 𝓘(ℝ, ℝ)) (c := q.2)
          (x := q.1))
    have h2 := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) (hF's.mdifferentiableAt (by simp) :
        MDifferentiableAt _ _ (fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) (q.1, q.2))
    have h3 := HasMFDerivAt.mfd_eq (h2.comp q.1 h1)
    have h4 : ((fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) ∘ fun x : M => (x, q.2)) =
        fun x => rotS u v (θ₀ * ρ q.2) (f x) := rfl
    rw [h4] at h3
    rw [h3]
    rfl
  show Surjective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
    𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) q)
  intro wv
  obtain ⟨a, ha⟩ := hslice wv
  exact ⟨(a, 0), by rw [← hpart]; exact ha⟩


include hu hv huv hf hMc hne in
/-- **Moving the regular value along a rotation arc, with the underlying set of the cobordism
controlled.**  If every point `r_τ(north)` of the arc (`0 ≤ τ ≤ θ₀`) is a regular value of `f`,
then the Pontryagin manifold of `f` at `r_{θ₀}(north)` (with the rotated basis) is framed
cobordant to the one at `north`, through a cobordism lying over `f⁻¹(arc)`. -/
theorem exists_rotCob (hnp : n + p = m)
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f north)
    {θ₀ : ℝ} (hθ₀ : 0 ≤ θ₀)
    (harc : letI := hM.chartedSpace; haveI := hM.isManifold; ∀ τ, 0 ≤ τ → τ ≤ θ₀ →
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
        (rotS u v τ north))
    {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ (hz : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f
        (rotS u v θ₀ north))
      (hb' : LinearIndependent ℝ (fun i => mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (rotS u v θ₀) north (b i))),
      ∃ X : FramedCob hM (pontryagin hM hMc hne hf hz hnp _ hb')
          (pontryagin hM hMc hne hf hy hnp b hb),
        X.S ⊆ {q : M × ℝ | ∃ τ, 0 ≤ τ ∧ τ ≤ θ₀ ∧ f q.1 = rotS u v τ north} := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hz := harc θ₀ hθ₀ le_rfl
  have hbij := mfd_rotS_bijective hu hv huv θ₀ north
  have hb' : LinearIndependent ℝ (fun i => mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (rotS u v θ₀) north (b i)) :=
    hb.map' (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (rotS u v θ₀) north :
      EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
      (LinearMap.ker_eq_bot.2 hbij.1)
  refine ⟨hz, hb', ?_⟩
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hε' : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨ρ, hρs, hρ0, hρ1, hρ01, -⟩ := exists_timeTransition hε hε'
  have hF' := contMDiff_rotHom hu hv huv hf θ₀ hρs
  have hzF := isRegularValue_rotHom hu hv huv hf θ₀ hρs hρ01 north hθ₀ harc
  have hr := contMDiff_rotS hu hv huv θ₀
  have hinj : ∀ q, rotS u v θ₀ (f q) = rotS u v θ₀ north → f q = north := fun q h => by
    have := congrArg (rotS u v (-θ₀)) h
    rwa [rotS_neg_rotS hu hv huv, rotS_neg_rotS hu hv huv] at this
  have hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun q => rotS u v θ₀ (f q)) := hr.comp hf
  have hzg : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun q => rotS u v θ₀ (f q)) (rotS u v θ₀ north) :=
    isRegularValue_comp hM hf hr north hy hbij hinj
  have hF0 : ∀ x t, t ≤ 1 / 4 → (fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) (x, t) = f x := by
    intro x t ht
    show rotS u v (θ₀ * ρ t) (f x) = f x
    rw [hρ0 t ht, mul_zero]
    exact rotS_zero hu hv huv (f x)
  have hF1 : ∀ x t, 1 - 1 / 4 ≤ t →
      (fun q : M × ℝ => rotS u v (θ₀ * ρ q.2) (f q.1)) (x, t) = rotS u v θ₀ (f x) := by
    intro x t ht
    show rotS u v (θ₀ * ρ t) (f x) = rotS u v θ₀ (f x)
    rw [hρ1 t ht, mul_one]
  obtain ⟨X, hX⟩ := exists_framedCob_of_homotopy hM hMc hne (g := fun x => rotS u v θ₀ (f x)) hnp
    hε hε' hF' hzF hF0 hF1 hf hz hg hzg _ hb'
  -- the Pontryagin manifold of `r ∘ f` at `r north` is that of `f` at `north`
  have hN : (fun q => rotS u v θ₀ (f q)) ⁻¹' {rotS u v θ₀ north} = f ⁻¹' {north} := by
    ext q
    constructor
    · intro h; exact hinj q h
    · intro h
      show rotS u v θ₀ (f q) = rotS u v θ₀ north
      have : f q = north := h
      rw [this]
  have heq : pontryagin hM hMc hne hg hzg hnp _ hb' =
      pontryagin hM hMc hne hf hy hnp b hb := by
    refine FramedSub.ext' hM hN ?_
    intro i x hx hx'
    have hfx : f x = north := hx'
    have h1 := pontV_comp hM hMc hne hf hr north hy hbij
      (fun i => mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (rotS u v θ₀)
        north (b i)) i x hfx hx hx'
    have h2 : (fun j => (LinearEquiv.ofBijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (rotS u v θ₀) north : EuclideanSpace ℝ (Fin p) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin p)) hbij).symm (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (rotS u v θ₀) north (b j))) = b := by
      funext j
      have h3 := (LinearEquiv.ofBijective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (rotS u v θ₀) north : EuclideanSpace ℝ (Fin p) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin p)) hbij).symm_apply_apply (b j)
      rw [LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe] at h3
      exact h3
    rw [h2] at h1
    exact h1
  refine exists_framedCob_congr (P := fun S => S ⊆ {q : M × ℝ | ∃ τ, 0 ≤ τ ∧ τ ≤ θ₀ ∧
    f q.1 = rotS u v τ north}) rfl heq ⟨X, ?_⟩
  rw [hX]
  intro q hq
  have hq' : rotS u v (θ₀ * ρ q.2) (f q.1) = rotS u v θ₀ north := hq
  have hfq : f q.1 = rotS u v (θ₀ - θ₀ * ρ q.2) north := by
    have := congrArg (rotS u v (-(θ₀ * ρ q.2))) hq'
    rw [rotS_neg_rotS hu hv huv, rotS_add hu hv huv] at this
    rw [this]
    congr 1
    ring
  have hρb := hρ01 q.2
  exact ⟨θ₀ - θ₀ * ρ q.2, by nlinarith [hρb.2], by nlinarith [hρb.1], hfq⟩

end rot

/-! ### Choosing a new regular value near the north pole -/

/-- A point of a dense set joined to the north pole by a rotation arc inside a given open
neighbourhood of the north pole. -/
theorem exists_arc (hp : 1 ≤ p) {U : Set (Sph p)} (hU : IsOpen U) (hnU : north ∈ U)
    {D : Set (Sph p)} (hD : Dense D) :
    ∃ u v : EuclideanSpace ℝ (Fin (p + 1)), ∃ θ₀ : ℝ, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ ⟪u, v⟫ = 0 ∧
      0 ≤ θ₀ ∧ rotS u v θ₀ north ∈ D ∧ ∀ τ, 0 ≤ τ → τ ≤ θ₀ → rotS u v τ north ∈ U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU north hnU
  obtain ⟨z, hzD, hzball⟩ := hD.exists_mem_open Metric.isOpen_ball ⟨north, Metric.mem_ball_self hδ⟩
  obtain ⟨u, v, θ₀, hu, hv, huv, hθ₀, -, hnz, hchord⟩ := exists_rotation_path hp north z
  have hnz' : rotS u v θ₀ north = z := Subtype.ext (by rw [rotS_val hu hv huv]; exact hnz)
  refine ⟨u, v, θ₀, hu, hv, huv, hθ₀, by rw [hnz']; exact hzD, fun τ h0 hτ => hball ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq, rotS_val hu hv huv]
  have hb := arc_bound hθ₀ hchord h0 hτ
  rw [← Subtype.dist_eq] at hb
  exact hb.trans_lt (Metric.mem_ball.1 hzball)

/-! ### Disjoint representatives -/

theorem range_comp_fst_eq_image (G : FramedSub hM n p) (f : M → Sph p) :
    range (fun q : G.N × ℝ => (fun q : M × ℝ => f q.1) (q.1.1, q.2)) = f '' G.N := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q.1.1, q.1.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨(⟨x, hx⟩, 0), rfl⟩

/-- The image of a framed submanifold of dimension `n < p` has dense open complement. -/
theorem dense_compl_image (G : FramedSub hM n p) (hdim : n + 1 < p) {f : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f) :
    Dense (f '' G.N)ᶜ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h := dense_compl_range G hdim (H := fun q : M × ℝ => f q.1) (hf.comp contMDiff_fst)
  rwa [range_comp_fst_eq_image] at h

theorem notMem_image_of_disjoint {F G : FramedSub hM n p} (h : Disjoint F.N G.N) {f : M → Sph p}
    {y : Sph p} (hfF : f ⁻¹' {y} = F.N) : y ∉ f '' G.N := by
  rintro ⟨x, hx, hfx⟩
  have hxF : x ∈ F.N := by rw [← hfF]; exact hfx
  exact Set.disjoint_left.1 h hxF hx

theorem disjoint_preimage_of_notMem {G : FramedSub hM n p} {f : M → Sph p} {z : Sph p}
    (hz : z ∉ f '' G.N) : Disjoint (f ⁻¹' {z}) G.N :=
  Set.disjoint_left.2 fun x hx hxG => hz ⟨x, hxG, hx⟩

include hMc hne in
/-- **Disjoint representatives** (`dim N < p`): every framed submanifold is framed cobordant to one
avoiding two given framed submanifolds.  Take the Theorem-B map `f`, a regular value `z` near the
north pole outside the (nowhere dense) images of the two submanifolds, and move the regular value
from `north` to `z` along a rotation arc. -/
theorem exists_cobordant_disjoint (hbig : m + 2 ≤ 2 * p) (F G₁ G₂ : FramedSub hM n p) :
    ∃ F' : FramedSub hM n p, FramedCobordant hM F F' ∧ Disjoint F'.N G₁.N ∧
      Disjoint F'.N G₂.N := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hnp := F.dim
  have hp : 1 ≤ p := by omega
  have hdim : n + 1 < p := by omega
  obtain ⟨f, hf, hy, c, hc, hcb, hfF⟩ :=
    exists_map_of_framedSub hM hMc hne F _ (linearIndependent_single (m := p))
  have hU := isOpen_regularValues_sph hM hMc hne hf
  have hD : Dense ((f '' G₁.N)ᶜ ∩ (f '' G₂.N)ᶜ) :=
    (dense_compl_image G₁ hdim hf).inter_of_isOpen_right (dense_compl_image G₂ hdim hf)
      (isClosed_image_N G₂ hf.continuous).isOpen_compl
  obtain ⟨u, v, θ₀, hu, hv, huv, hθ₀, ⟨hz₁, hz₂⟩, harc⟩ := exists_arc hp hU hy hD
  obtain ⟨hz, hb', X, -⟩ := exists_rotCob hMc hne hu hv huv hf F.dim hy hθ₀ harc hcb
  refine ⟨pontryagin hM hMc hne hf hz F.dim _ hb', ?_, disjoint_preimage_of_notMem hz₁,
    disjoint_preimage_of_notMem hz₂⟩
  have h : FramedCobordant hM _ _ := ⟨X⟩
  rw [hfF] at h
  exact h.symm

/-! ### Moving one component of a disjoint union -/

theorem det_smul_one_pos {d : ℝ} (hd : 0 < d) : 0 < (d • (1 : Matrix (Fin p) (Fin p) ℝ)).det := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  positivity

theorem mulTuple_smul_one (d : ℝ) (b : Fin p → EuclideanSpace ℝ (Fin p)) :
    GLp.mulTuple (d • (1 : Matrix (Fin p) (Fin p) ℝ)) b = fun j => d • b j := by
  funext j
  simp only [GLp.mulTuple, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

include hMc hne in
/-- **Moving one component of a disjoint union** (`p ≥ m/2 + 1`): if `F ∼ F₁` and `G` is disjoint
from both, then `F ⊔ G ∼ F₁ ⊔ G`.  Write `F`, `F₁` as Pontryagin manifolds of `f`, `f₁` at the north
pole, join `f` to `f₁` by a homotopy `H`, choose a common regular value `z` near the north pole not
in `H(G × ℝ)` (an `(n+1)`-dimensional image), and use the chain
`F ∼ f⁻¹(z) ∼ f₁⁻¹(z) ∼ f₁⁻¹(z) ∼ F₁` (rotation arc, Lemma 3, Lemma 1, rotation arc), each
cobordism being disjoint from `G × ℝ`, united with the product cobordism `G × ℝ`. -/
theorem union_left_of_framedCobordant (hbig : m + 2 ≤ 2 * p) {F F₁ : FramedSub hM n p}
    (hFF₁ : FramedCobordant hM F F₁) (G : FramedSub hM n p) (h : Disjoint F.N G.N)
    (h₁ : Disjoint F₁.N G.N) : FramedCobordant hM (F.union G h) (F₁.union G h₁) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  have hnp := F.dim
  have hp : 1 ≤ p := by omega
  have hdim : n + 1 < p := by omega
  obtain ⟨e₀, he₀⟩ := exists_posBasis hp (north : Sph p)
  obtain ⟨f, hf, hyf, c, hc, hcb, hfF⟩ :=
    exists_map_of_framedSub hM hMc hne F _ e₀.linearIndependent
  obtain ⟨f₁, hf₁, hyf₁, c₁, hc₁, hcb₁, hfF₁⟩ :=
    exists_map_of_framedSub hM hMc hne F₁ _ e₀.linearIndependent
  have hfN : f ⁻¹' {north} = F.N := congrArg FramedSub.N hfF
  have hf₁N : f₁ ⁻¹' {north} = F₁.N := congrArg FramedSub.N hfF₁
  -- a homotopy from `f` to `f₁`, constant near the ends
  have h1 : FramedCobordant hM F (pontryagin hM hMc hne hf hyf F.dim e₀ e₀.linearIndependent) := by
    have := framedCobordant_of_det_pos hM hMc hne F.dim hf hyf e₀.linearIndependent hcb
      (det_smul_one_pos hc) (mulTuple_smul_one c e₀)
    rwa [hfF] at this
  have h2 : FramedCobordant hM F₁
      (pontryagin hM hMc hne hf₁ hyf₁ F.dim e₀ e₀.linearIndependent) := by
    have := framedCobordant_of_det_pos hM hMc hne F.dim hf₁ hyf₁ e₀.linearIndependent hcb₁
      (det_smul_one_pos hc₁) (mulTuple_smul_one c₁ e₀)
    rwa [hfF₁] at this
  have hhom := smoothHomotopic_of_framedCobordant hM hMc hne F.dim hp hf hf₁ hyf hyf₁ e₀ he₀ e₀ he₀
    ((h1.symm.trans hFF₁).trans h2)
  obtain ⟨H, hH, hH0, hH1⟩ := hhom.exists_const_near_ends (ε := 1 / 4) (by norm_num) (by norm_num)
  -- the choice of the regular value
  have hU : IsOpen ({y | IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y} ∩ {y | IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f₁ y} ∩ (f '' G.N)ᶜ ∩ (f₁ '' G.N)ᶜ) :=
    (((isOpen_regularValues_sph hM hMc hne hf).inter
      (isOpen_regularValues_sph hM hMc hne hf₁)).inter
      (isClosed_image_N G hf.continuous).isOpen_compl).inter
      (isClosed_image_N G hf₁.continuous).isOpen_compl
  have hnU : north ∈ ({y | IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y} ∩ {y | IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f₁ y} ∩ (f '' G.N)ᶜ ∩ (f₁ '' G.N)ᶜ) :=
    ⟨⟨⟨hyf, hyf₁⟩, notMem_image_of_disjoint h hfN⟩, notMem_image_of_disjoint h₁ hf₁N⟩
  have hclosed : IsClosed (range (fun q : G.N × ℝ => H (q.1.1, q.2))) := by
    have hset : range (fun q : G.N × ℝ => H (q.1.1, q.2)) = H '' (G.N ×ˢ Icc (0 : ℝ) 1) := by
      ext y
      constructor
      · rintro ⟨⟨x, t⟩, rfl⟩
        by_cases ht0 : t < 0
        · refine ⟨(x.1, 0), ⟨x.2, by simp⟩, ?_⟩
          show H (x.1, 0) = H (x.1, t)
          rw [hH0 x.1 0 (by norm_num), hH0 x.1 t (by linarith)]
        · by_cases ht1 : 1 < t
          · refine ⟨(x.1, 1), ⟨x.2, by simp⟩, ?_⟩
            show H (x.1, 1) = H (x.1, t)
            rw [hH1 x.1 1 (by norm_num), hH1 x.1 t (by linarith)]
          · exact ⟨(x.1, t), ⟨x.2, ⟨not_lt.1 ht0, not_lt.1 ht1⟩⟩, rfl⟩
      · rintro ⟨⟨x, t⟩, ⟨hx, -⟩, rfl⟩
        exact ⟨(⟨x, hx⟩, t), rfl⟩
    rw [hset]
    exact ((G.compact.prod isCompact_Icc).image hH.continuous).isClosed
  have hD : Dense ({y | IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) H y} ∩ (range (fun q : G.N × ℝ => H (q.1.1, q.2)))ᶜ) :=
    (dense_regularValues hH).inter_of_isOpen_right (dense_compl_range G hdim hH)
      hclosed.isOpen_compl
  obtain ⟨u, v, θ₀, hu, hv, huv, hθ₀, ⟨hzH, hzR⟩, harc⟩ := exists_arc hp hU hnU hD
  have harcf : ∀ τ, 0 ≤ τ → τ ≤ θ₀ → IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f (rotS u v τ north) := fun τ h0 hτ => (harc τ h0 hτ).1.1.1
  have harcf₁ : ∀ τ, 0 ≤ τ → τ ≤ θ₀ → IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f₁ (rotS u v τ north) := fun τ h0 hτ => (harc τ h0 hτ).1.1.2
  have hAf : ∀ τ, 0 ≤ τ → τ ≤ θ₀ → rotS u v τ north ∉ f '' G.N :=
    fun τ h0 hτ => (harc τ h0 hτ).1.2
  have hAf₁ : ∀ τ, 0 ≤ τ → τ ≤ θ₀ → rotS u v τ north ∉ f₁ '' G.N :=
    fun τ h0 hτ => (harc τ h0 hτ).2
  -- the four cobordisms
  obtain ⟨hz, hb', X₁, hX₁⟩ := exists_rotCob hMc hne hu hv huv hf F.dim hyf hθ₀ harcf hcb
  obtain ⟨hz₁, hb'₁, X₄, hX₄⟩ := exists_rotCob hMc hne hu hv huv hf₁ F.dim hyf₁ hθ₀ harcf₁ hcb₁
  obtain ⟨X₂, hX₂⟩ := exists_framedCob_of_homotopy hM hMc hne F.dim (ε := 1 / 4) (by norm_num)
    (by norm_num) hH hzH hH0 hH1 hf hz hf₁ hz₁ _ hb'
  obtain ⟨X₃, hX₃⟩ := exists_framedCob_of_det_pos hM hMc hne F.dim hf₁ hz₁ hb'₁ hb'
    (det_smul_one_pos (div_pos hc hc₁)) (by
      rw [mulTuple_smul_one]
      funext j
      rw [← map_smul, smul_smul, div_mul_cancel₀ c hc₁.ne'])
  obtain ⟨Y, hY⟩ := exists_framedCob_prod hMc hne G
  obtain ⟨X₁', hX₁'⟩ := exists_framedCob_congr
    (P := fun S => S ⊆ {q : M × ℝ | ∃ τ, 0 ≤ τ ∧ τ ≤ θ₀ ∧ f q.1 = rotS u v τ north}) rfl hfF
    ⟨X₁, hX₁⟩
  obtain ⟨X₄', hX₄'⟩ := exists_framedCob_congr
    (P := fun S => S ⊆ {q : M × ℝ | ∃ τ, 0 ≤ τ ∧ τ ≤ θ₀ ∧ f₁ q.1 = rotS u v τ north}) rfl hfF₁
    ⟨X₄, hX₄⟩
  -- disjointness
  have hzf : rotS u v θ₀ north ∉ f '' G.N := hAf θ₀ hθ₀ le_rfl
  have hzf₁ : rotS u v θ₀ north ∉ f₁ '' G.N := hAf₁ θ₀ hθ₀ le_rfl
  have hd0 := disjoint_preimage_of_notMem hzf
  have hd1 := disjoint_preimage_of_notMem hzf₁
  have hS₁ : Disjoint X₁'.S Y.S := by
    rw [hY]
    refine Set.disjoint_left.2 fun q hq hqG => ?_
    obtain ⟨τ, h0, hτ, hfq⟩ := hX₁' hq
    exact hAf τ h0 hτ ⟨q.1, hqG, hfq⟩
  have hS₄ : Disjoint X₄'.S Y.S := by
    rw [hY]
    refine Set.disjoint_left.2 fun q hq hqG => ?_
    obtain ⟨τ, h0, hτ, hfq⟩ := hX₄' hq
    exact hAf₁ τ h0 hτ ⟨q.1, hqG, hfq⟩
  have hS₂ : Disjoint X₂.S Y.S := by
    rw [hX₂, hY]
    refine Set.disjoint_left.2 fun q hq hqG => hzR ⟨(⟨q.1, hqG⟩, q.2), ?_⟩
    exact hq
  have hS₃ : Disjoint X₃.S Y.S := by
    rw [hX₃, hY]
    exact Set.disjoint_left.2 fun q hq hqG => hzf₁ ⟨q.1, hqG, hq⟩
  have U₁ := framedCobordant_union X₁' Y hS₁ hd0 h
  have U₂ := framedCobordant_union X₂ Y hS₂ hd0 hd1
  have U₃ := framedCobordant_union X₃ Y hS₃ hd1 hd1
  have U₄ := framedCobordant_union X₄' Y hS₄ hd1 h₁
  exact ((U₁.symm.trans U₂).trans U₃).trans U₄

include hMc hne in
/-- **The disjoint union is compatible with framed cobordism** (`p ≥ m/2 + 1`). -/
theorem framedCobordant_union_of_framedCobordant' (hbig : m + 2 ≤ 2 * p)
    {F F₁ G G₁ : FramedSub hM n p} (hF : FramedCobordant hM F F₁) (hG : FramedCobordant hM G G₁)
    (h : Disjoint F.N G.N) (h₁ : Disjoint F₁.N G₁.N) :
    FramedCobordant hM (F.union G h) (F₁.union G₁ h₁) := by
  obtain ⟨G', hGG', hG'F, hG'F₁⟩ := exists_cobordant_disjoint hMc hne hbig G F F₁
  have s1 : FramedCobordant hM (F.union G h) (F.union G' hG'F.symm) := by
    rw [union_comm' F G h, union_comm' F G' hG'F.symm]
    exact union_left_of_framedCobordant hMc hne hbig hGG' F h.symm hG'F
  have s2 : FramedCobordant hM (F.union G' hG'F.symm) (F₁.union G' hG'F₁.symm) :=
    union_left_of_framedCobordant hMc hne hbig hF G' hG'F.symm hG'F₁.symm
  have s3 : FramedCobordant hM (F₁.union G' hG'F₁.symm) (F₁.union G₁ h₁) := by
    rw [union_comm' F₁ G' hG'F₁.symm, union_comm' F₁ G₁ h₁]
    exact union_left_of_framedCobordant hMc hne hbig (hGG'.symm.trans hG) F₁ hG'F₁ h₁.symm
  exact (s1.trans s2).trans s3

/-! ### Maps built on a product neighbourhood -/

section tube

variable {hMc : IsCompact M} {hne : M.Nonempty} {F : FramedSub hM n p}

open Classical in
/-- The family `(z, t) ↦ Φ(π₂ G⁻¹ z, t)` on the tube `V = G(N × B_ε)`, `south` elsewhere. -/
def tubeHom [Nonempty F.N] (T : TubeData hMc hne F)
    (Φ : EuclideanSpace ℝ (Fin p) × ℝ → Sph p) (q : M × ℝ) : Sph p :=
  if q.1 ∈ T.V then Φ ((T.Ginv q.1).2, q.2) else south

open Classical in
/-- The map `z ↦ Φ(π₂ G⁻¹ z)` on the tube `V = G(N × B_ε)`, `south` elsewhere. -/
def tubeMap [Nonempty F.N] (T : TubeData hMc hne F) (Φ : EuclideanSpace ℝ (Fin p) → Sph p)
    (z : M) : Sph p :=
  if z ∈ T.V then Φ (T.Ginv z).2 else south

variable [Nonempty F.N] (T : TubeData hMc hne F)

theorem tubeHom_apply (Φ : EuclideanSpace ℝ (Fin p) × ℝ → Sph p) (z : M) (t : ℝ) :
    tubeHom T Φ (z, t) = tubeMap T (fun s => Φ (s, t)) z := rfl

theorem tubeMap_of_mem (Φ : EuclideanSpace ℝ (Fin p) → Sph p) {z : M} (hz : z ∈ T.V) :
    tubeMap T Φ z = Φ (T.Ginv z).2 := by
  simp [tubeMap, hz]

theorem tubeMap_of_notMem (Φ : EuclideanSpace ℝ (Fin p) → Sph p) {z : M} (hz : z ∉ T.V) :
    tubeMap T Φ z = south := by
  simp [tubeMap, hz]

omit [Nonempty F.N] in
theorem G_mem_V {q : F.N × EuclideanSpace ℝ (Fin p)} (hq : q ∈ PN.tube F.N p T.ε) :
    T.G q ∈ T.V := ⟨q, hq, rfl⟩

theorem tubeMap_G (Φ : EuclideanSpace ℝ (Fin p) → Sph p) {q : F.N × EuclideanSpace ℝ (Fin p)}
    (hq : q ∈ PN.tube F.N p T.ε) : tubeMap T Φ (T.G q) = Φ q.2 := by
  rw [tubeMap_of_mem T Φ (G_mem_V T hq), T.Ginv_G hq]

theorem tubeMap_eq_north_iff {Φ : EuclideanSpace ℝ (Fin p) → Sph p} {z : M} :
    tubeMap T Φ z = north ↔ z ∈ T.V ∧ Φ (T.Ginv z).2 = north := by
  by_cases hz : z ∈ T.V
  · rw [tubeMap_of_mem T Φ hz]; exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
  · rw [tubeMap_of_notMem T Φ hz]
    exact ⟨fun h => absurd h south_ne_north, fun h => absurd h.1 hz⟩

/-- Smoothness of the tube family, when `Φ(s, t)` is `south` for `‖s‖ ≥ r₀`, `r₀ < ε`. -/
theorem contMDiff_tubeHom {Φ : EuclideanSpace ℝ (Fin p) × ℝ → Sph p}
    (hΦ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ Φ)
    {r₀ : ℝ} (hr₀ : r₀ < T.ε) (hsouth : ∀ s t, r₀ ≤ ‖s‖ → Φ (s, t) = south) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (tubeHom T Φ) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  haveI : CompactSpace F.N := isCompact_iff_compactSpace.1 F.compact
  obtain ⟨Cl, hCl⟩ : ∃ Cl : Set M,
      Cl = T.G '' (univ ×ˢ closedBall (0 : EuclideanSpace ℝ (Fin p)) r₀) := ⟨_, rfl⟩
  have hClc : IsCompact Cl := by
    rw [hCl]; exact (isCompact_univ.prod (isCompact_closedBall _ _)).image T.hG.continuous
  have hClV : Cl ⊆ T.V := by
    rw [hCl]
    rintro _ ⟨q, ⟨-, hq⟩, rfl⟩
    exact ⟨q, lt_of_le_of_lt (mem_closedBall_zero_iff.1 hq) hr₀, rfl⟩
  have hsouth' : ∀ z ∉ Cl, ∀ t, tubeHom T Φ (z, t) = south := by
    intro z hz t
    rw [tubeHom_apply]
    by_cases hzV : z ∈ T.V
    · rw [tubeMap_of_mem T _ hzV]
      apply hsouth
      by_contra hlt
      push Not at hlt
      apply hz
      rw [hCl]
      exact ⟨T.Ginv z, ⟨mem_univ _, mem_closedBall_zero_iff.2 hlt.le⟩, T.G_Ginv hzV⟩
    · exact tubeMap_of_notMem T _ hzV
  rintro ⟨z, t⟩
  by_cases hz : z ∈ T.V
  · have hGi : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) ∞
        (fun zt : M × ℝ => T.Ginv zt.1) (z, t) :=
      (T.contMDiffAt_Ginv hz).comp (z, t) contMDiffAt_fst
    have hs : ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ)) ∞
        (fun zt : M × ℝ => ((T.Ginv zt.1).2, zt.2)) (z, t) :=
      (contMDiffAt_snd.comp (z, t) hGi).prodMk contMDiffAt_snd
    have h1 := (hΦ ((T.Ginv z).2, t)).comp (z, t) hs
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [(T.isOpen_V.preimage continuous_fst).mem_nhds (show (z, t).1 ∈ T.V from hz)]
      with zt hzt
    show tubeMap T (fun s => Φ (s, zt.2)) zt.1 = Φ ((T.Ginv zt.1).2, zt.2)
    exact tubeMap_of_mem T _ hzt
  · have hzC : z ∉ Cl := fun h => hz (hClV h)
    refine (contMDiffAt_const (c := (south : Sph p))).congr_of_eventuallyEq ?_
    filter_upwards [(hClc.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds
      (show (z, t).1 ∈ Clᶜ from hzC)] with zt hzt
    exact hsouth' zt.1 hzt zt.2

/-- Smoothness of a tube map. -/
theorem contMDiff_tubeMap {Φ : EuclideanSpace ℝ (Fin p) → Sph p}
    (hΦ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ Φ)
    {r₀ : ℝ} (hr₀ : r₀ < T.ε) (hsouth : ∀ s, r₀ ≤ ‖s‖ → Φ s = south) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (tubeMap T Φ) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have h := (contMDiff_tubeHom T (Φ := fun q => Φ q.1) (hΦ.comp contMDiff_fst) hr₀
    (fun s _ hs => hsouth s hs)).comp
    (contMDiff_id.prodMk contMDiff_const : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) ∞ (fun z : M => (z, (0 : ℝ))))
  exact h

end tube

/-! ### Derivatives of tube maps -/

section tubeDeriv

variable {hMc : IsCompact M} {hne : M.Nonempty} {F : FramedSub hM n p} [Nonempty F.N]
  (T : TubeData hMc hne F)

/-- **The chain rule on the tube**: `d(tubeMap Φ)_{G q} ∘ dG_q = dΦ_{q₂} ∘ pr₂`. -/
theorem mfd_tubeMap_comp {Φ : EuclideanSpace ℝ (Fin p) → Sph p}
    (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (tubeMap T Φ))
    {q : F.N × EuclideanSpace ℝ (Fin p)} (hq : q ∈ PN.tube F.N p T.ε)
    (hΦ : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) Φ q.2) :
    letI := hM.chartedSpace; haveI := hM.isManifold; letI := F.hN.chartedSpace;
    (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (tubeMap T Φ) (T.G q)).comp
        (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin m)) T.G q) =
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) Φ q.2).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin p))) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  have h1 := (hasMFDerivAt_mfd (hk.mdifferentiableAt (by simp) : MDifferentiableAt
    𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (tubeMap T Φ) (T.G q))).comp q
    (hasMFDerivAt_mfd (T.hG.mdifferentiableAt (by simp) : MDifferentiableAt
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) T.G q))
  have h2 : HasMFDerivAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (fun q' : F.N × EuclideanSpace ℝ (Fin p) => Φ q'.2) q
      ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) Φ q.2).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin p)))) :=
    (hasMFDerivAt_mfd hΦ).comp q (hasMFDerivAt_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q)
  have hev : (tubeMap T Φ ∘ T.G) =ᶠ[𝓝 q] (fun q' : F.N × EuclideanSpace ℝ (Fin p) => Φ q'.2) := by
    filter_upwards [(PN.isOpen_tube (N := F.N) (p := p) T.ε).mem_nhds hq] with q' hq'
    exact tubeMap_G T Φ hq'
  exact hasMFDerivAt_unique h1 (h2.congr_of_eventuallyEq hev)

/-- **Regular values of tube maps**: `north` is a regular value of `tubeMap Φ` as soon as `dΦ` is
onto at the preimages of `north` in the ball. -/
theorem isRegularValue_tubeMap {Φ : EuclideanSpace ℝ (Fin p) → Sph p}
    (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (tubeMap T Φ))
    (hΦ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ Φ)
    (hreg : ∀ s, ‖s‖ < T.ε → Φ s = north →
      Surjective (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) Φ s)) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (tubeMap T Φ)
      north := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  intro z hz
  obtain ⟨hzV, hΦz⟩ := (tubeMap_eq_north_iff T).1 hz
  have hq := T.Ginv_mem hzV
  have hchain := mfd_tubeMap_comp T hk hq (hΦ.mdifferentiableAt (by simp))
  rw [T.G_Ginv hzV] at hchain
  have hsurj : Surjective ((mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) Φ
      (T.Ginv z).2).comp
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin p)))) :=
    (hreg _ hq hΦz).comp (fun s => ⟨(0, s), rfl⟩)
  rw [← hchain] at hsurj
  exact Surjective.of_comp hsurj

/-- **Regular values of tube families.** -/
theorem isRegularValue_tubeHom {Φ : EuclideanSpace ℝ (Fin p) × ℝ → Sph p}
    (hH : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
        (tubeHom T Φ))
    (hΦ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ Φ)
    (hreg : ∀ s t, ‖s‖ < T.ε → Φ (s, t) = north →
      Surjective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin p)) Φ (s, t))) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (tubeHom T Φ) north := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  rintro ⟨z, t⟩ hz
  have hz' : tubeMap T (fun s => Φ (s, t)) z = north := hz
  obtain ⟨hzV, hΦz⟩ := (tubeMap_eq_north_iff T).1 hz'
  have hq := T.Ginv_mem hzV
  obtain ⟨q, hqdef⟩ : ∃ q, T.Ginv z = q := ⟨_, rfl⟩
  rw [hqdef] at hq hΦz
  have hGq : T.G q = z := by rw [← hqdef]; exact T.G_Ginv hzV
  have hGt : HasMFDerivAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin p))).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (fun qt : (F.N × EuclideanSpace ℝ (Fin p)) × ℝ => (T.G qt.1, qt.2)) (q, t)
      (((mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin m)) T.G q).comp
          (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) ℝ)).prod
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) ℝ)) :=
    ((hasMFDerivAt_mfd (T.hG.mdifferentiableAt (by simp))).comp (q, t)
      (hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        (I' := 𝓘(ℝ, ℝ)) (q, t))).prodMk
      (hasMFDerivAt_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        (I' := 𝓘(ℝ, ℝ)) (q, t))
  have hH' := (hasMFDerivAt_mfd (hH.mdifferentiableAt (by simp) : MDifferentiableAt
    (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
    (tubeHom T Φ) (T.G q, t))).comp (q, t) hGt
  have hΦ' : HasMFDerivAt ((𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin p))).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (fun qt : (F.N × EuclideanSpace ℝ (Fin p)) × ℝ => Φ (qt.1.2, qt.2)) (q, t)
      ((mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) Φ
        (q.2, t)).comp (((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℝ (Fin p))).comp (ContinuousLinearMap.fst ℝ
            (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) ℝ)).prod
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) ℝ))) :=
    (hasMFDerivAt_mfd (hΦ.mdifferentiableAt (by simp))).comp (q, t)
      (((hasMFDerivAt_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q).comp (q, t)
        (hasMFDerivAt_fst (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
          (I' := 𝓘(ℝ, ℝ)) (q, t))).prodMk
        (hasMFDerivAt_snd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
          (I' := 𝓘(ℝ, ℝ)) (q, t)))
  have hev : (tubeHom T Φ ∘ fun qt : (F.N × EuclideanSpace ℝ (Fin p)) × ℝ => (T.G qt.1, qt.2))
      =ᶠ[𝓝 (q, t)] fun qt => Φ (qt.1.2, qt.2) := by
    filter_upwards [((PN.isOpen_tube (N := F.N) (p := p) T.ε).preimage continuous_fst).mem_nhds
      (show (q, t).1 ∈ PN.tube F.N p T.ε from hq)] with qt hqt
    show tubeMap T (fun s => Φ (s, qt.2)) (T.G qt.1) = Φ (qt.1.2, qt.2)
    exact tubeMap_G T _ hqt
  have heq := hasMFDerivAt_unique hH' (hΦ'.congr_of_eventuallyEq hev)
  have hsurj : Surjective ((mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) Φ (q.2, t)).comp (((ContinuousLinearMap.snd ℝ
        (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin p))).comp (ContinuousLinearMap.fst ℝ
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) ℝ)).prod
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) ℝ))) :=
    (hreg q.2 t hq hΦz).comp (fun st => ⟨((0, st.1), st.2), rfl⟩)
  have hsurj2 : Surjective (fun v => (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (tubeHom T Φ) (T.G q, t))
        ((((mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin m)) T.G q).comp
          (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) ℝ)).prod
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) ℝ))
          v)) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, (DFunLike.congr_fun heq x).trans hx⟩
  have h := Surjective.of_comp hsurj2
  rw [hGq] at h
  exact h

end tubeDeriv

/-! ### The framing depends only on the derivative -/

section atEq

variable {hMc : IsCompact M} {hne : M.Nonempty}

/-- Two maps with the same value and the same derivative at `x` have the same ambient derivative
`A = dF̃_x` (the ambient derivative kills the normal space of `M`). -/
theorem At_eq_of_mfd_eq {f g : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g)
    {y : Sph p} {x : M} (hfx : f x = y) (hgx : g x = y)
    (h : letI := hM.chartedSpace; haveI := hM.isManifold;
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x =
        mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g x) :
    At hM hMc hne f y x.1 = At hM hMc hne g y x.1 := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hsrcf : f ⟨x.1, x.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [Subtype.coe_eta, hfx]; exact mem_extChartAt_source y
  have hsrcg : g ⟨x.1, x.2⟩ ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) y).source := by
    rw [Subtype.coe_eta, hgx]; exact mem_extChartAt_source y
  have hf' := At_comp_mfd_val hM hMc hne hf x.2 hsrcf
  have hg' := At_comp_mfd_val hM hMc hne hg x.2 hsrcg
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨t, ht, nv, hnv, hvt⟩ :=
    Submodule.exists_add_mem_mem_orthogonal (K := tangentM hM ⟨x.1, x.2⟩) v
  obtain ⟨a, ha⟩ := LinearMap.mem_range.1 ht
  have hn0f : At hM hMc hne f y x.1 nv = 0 :=
    At_normal_eq_zero hM hMc hne hf x.2 hsrcf ((Submodule.mem_orthogonal' _ _).1 hnv)
  have hn0g : At hM hMc hne g y x.1 nv = 0 :=
    At_normal_eq_zero hM hMc hne hg x.2 hsrcg ((Submodule.mem_orthogonal' _ _).1 hnv)
  have ha' : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (Subtype.val : M → EuclideanSpace ℝ (Fin (K + 1))) ⟨x.1, x.2⟩) a = t := ha
  rw [hvt, map_add, map_add, hn0f, hn0g, add_zero, add_zero, ← ha']
  have e1 := congrArg (fun L => L a) hf'
  have e2 := congrArg (fun L => L a) hg'
  simp only [ContinuousLinearMap.comp_apply, Subtype.coe_eta] at e1 e2
  rw [e1, e2, hfx, hgx, h]

theorem pontV_eq_of_mfd_eq {f g : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g)
    {y : Sph p} {x : M} (hx : x ∈ f ⁻¹' {y}) (hx' : x ∈ g ⁻¹' {y})
    (h : letI := hM.chartedSpace; haveI := hM.isManifold;
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x =
        mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g x)
    (b : Fin p → EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    pontV hM hMc hne f y b i ⟨x, hx⟩ = pontV hM hMc hne g y b i ⟨x, hx'⟩ := by
  unfold pontV
  rw [At_eq_of_mfd_eq hf hg hx hx' h]

theorem pontryagin_v_eq_of_mfd_eq (hnp : n + p = m) {f g : M → Sph p}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g)
    (hyf : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f north)
    (hyg : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g north)
    (b : Fin p → EuclideanSpace ℝ (Fin p)) (hb : LinearIndependent ℝ b) {x : M}
    (hx : x ∈ (pontryagin hM hMc hne hf hyf hnp b hb).N)
    (hx' : x ∈ (pontryagin hM hMc hne hg hyg hnp b hb).N)
    (h : letI := hM.chartedSpace; haveI := hM.isManifold;
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f x =
        mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g x) (i : Fin p) :
    (pontryagin hM hMc hne hf hyf hnp b hb).v i ⟨x, hx⟩ =
      (pontryagin hM hMc hne hg hyg hnp b hb).v i ⟨x, hx'⟩ :=
  pontV_eq_of_mfd_eq hf hg hx hx' h b i

end atEq

/-! ### Identifying Pontryagin manifolds of tube maps -/

section ident

variable {hMc : IsCompact M} {hne : M.Nonempty} {F : FramedSub hM n p} [Nonempty F.N]
  (T : TubeData hMc hne F)

theorem tubeMap_preimage_north {Φ : EuclideanSpace ℝ (Fin p) → Sph p}
    {s₀ : EuclideanSpace ℝ (Fin p)}
    (hzero : ∀ s, ‖s‖ < T.ε → (Φ s = north ↔ s = s₀)) :
    tubeMap T Φ ⁻¹' {north} = {z | z ∈ T.V ∧ (T.Ginv z).2 = s₀} := by
  ext z
  simp only [mem_preimage, mem_singleton_iff, mem_ofPred_eq]
  rw [tubeMap_eq_north_iff]
  constructor
  · rintro ⟨hzV, h⟩; exact ⟨hzV, (hzero _ (T.Ginv_mem hzV)).1 h⟩
  · rintro ⟨hzV, h⟩; exact ⟨hzV, (hzero _ (T.Ginv_mem hzV)).2 h⟩

theorem setOf_Ginv_eq_zero : {z | z ∈ T.V ∧ (T.Ginv z).2 = 0} = F.N := by
  ext z
  constructor
  · rintro ⟨hzV, h⟩
    have h1 := T.G_Ginv hzV
    have h2 : T.Ginv z = ((T.Ginv z).1, 0) := Prod.ext rfl h
    rw [h2, T.G_zero] at h1
    rw [← h1]; exact (T.Ginv z).1.2
  · intro hz
    exact ⟨T.mem_V ⟨z, hz⟩, by rw [T.Ginv_of_mem ⟨z, hz⟩]⟩

theorem norm_smul_single (s : ℝ) (i : Fin p) :
    ‖s • EuclideanSpace.single i (1 : ℝ)‖ = |s| := by
  rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]

/-- **Identification of the Pontryagin manifold of a tube map**: if `Φ` vanishes only at `0` and
along the coordinate lines `Φ((s σᵢ) eᵢ) = collapse(s eᵢ)` (`σᵢ = ±1`), the Pontryagin manifold
of the tube map is `N` with the framing `σᵢ vᵢ`. -/
theorem pontryagin_tubeMap_eq (F' : FramedSub hM n p) (hN : F'.N = F.N) (sg : Fin p → ℝ)
    (hsg : ∀ i, |sg i| = 1)
    (hv : ∀ i (x : M) (hx : x ∈ F.N) (hx' : x ∈ F'.N), F'.v i ⟨x, hx'⟩ = sg i • F.v i ⟨x, hx⟩)
    {Φ : EuclideanSpace ℝ (Fin p) → Sph p}
    (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (tubeMap T Φ))
    (hzero : ∀ s, ‖s‖ < T.ε → (Φ s = north ↔ s = 0))
    {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) {c : ℝ} (hc : 0 < c)
    {δ : ℝ} (hδ : 0 < δ)
    (hline : ∀ i (s : ℝ), |s| < δ →
      Φ ((s * sg i) • EuclideanSpace.single i 1) = collapse hb c (s • EuclideanSpace.single i 1)) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    ∃ (hy : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (tubeMap T Φ) north) (hcb : LinearIndependent ℝ (fun i => c • b i)),
      pontryagin hM hMc hne hk hy F'.dim (fun i => c • b i) hcb = F' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hkN : tubeMap T Φ ⁻¹' {north} = F'.N := by
    rw [tubeMap_preimage_north T hzero, setOf_Ginv_eq_zero T, hN]
  have hδ' : 0 < min δ (min T.a₀ T.ε) := lt_min hδ (lt_min T.ha₀ T.hε)
  refine pontryagin_eq_of_collapse hM hMc hne F' hk hkN hb hc hδ' ?_
  intro x i s hs
  have hs1 : |s| < δ := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : |s| < T.a₀ := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_left _ _))
  have hs3 : |s| < T.ε := lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_right _ _))
  have hxF : x.1 ∈ F.N := hN ▸ x.2
  have hvx : F'.v i x = sg i • F.v i ⟨x.1, hxF⟩ := hv i x.1 hxF x.2
  have habs : |s * sg i| = |s| := by rw [abs_mul, hsg i, mul_one]
  have hG := T.G_line ⟨x.1, hxF⟩ i (s := s * sg i) (by rw [habs]; exact hs2.le)
  have hq : ((⟨x.1, hxF⟩ : F.N), (s * sg i) • EuclideanSpace.single i (1 : ℝ)) ∈
      PN.tube F.N p T.ε := by
    show ‖(s * sg i) • EuclideanSpace.single i (1 : ℝ)‖ < T.ε
    rw [norm_smul_single, habs]; exact hs3
  have heq : x.1.1 + s • F'.v i x = x.1.1 + (s * sg i) • F.v i ⟨x.1, hxF⟩ := by
    rw [hvx, smul_smul]
  rw [heq, ← hG, tubeMap_G T Φ hq]
  exact hline i s hs1

end ident

/-! ### Linear algebra of the folding maps -/

section linalg

theorem basisCLM_apply_single_eq (L : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    basisCLM (fun i => L (EuclideanSpace.single i 1)) = L := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin p) ℝ).toBasis.ext
  intro i
  simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    ContinuousLinearMap.coe_coe]
  rw [basisCLM_single]

theorem inner_single_smul_single (i j : Fin p) (s : ℝ) :
    ⟪EuclideanSpace.single i (1 : ℝ), s • EuclideanSpace.single j (1 : ℝ)⟫ =
      if i = j then s else 0 := by
  rw [EuclideanSpace.inner_single_left]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem norm_single_one (i : Fin p) : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by
  rw [PiLp.norm_single, norm_one]

/-- The reflection-type map `Tcan w (σ/2)` along the coordinate lines. -/
theorem Tcan_half_line (hp : 1 ≤ p) {σ : ℝ} (hσ : σ * σ = 1) (i : Fin p) (s : ℝ) :
    Tcan (EuclideanSpace.single ⟨0, hp⟩ (1 : ℝ)) (σ / 2)
      ((s * (if i = ⟨0, hp⟩ then σ else 1)) • EuclideanSpace.single i (1 : ℝ)) =
      s • EuclideanSpace.single i (1 : ℝ) := by
  rw [Tcan_apply, inner_single_smul_single]
  by_cases hi : i = ⟨0, hp⟩
  · subst hi
    simp only [if_true, smul_smul]
    rw [sub_self, add_zero]
    congr 1
    linear_combination s * hσ
  · have hi' : ¬ (⟨0, hp⟩ : Fin p) = i := fun h => hi h.symm
    simp only [hi, hi', if_false, mul_one, zero_smul, smul_zero, zero_add, sub_zero]

theorem norm_Tcan_ge {w : EuclideanSpace ℝ (Fin p)} (hw : ‖w‖ = 1) {l κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκl : κ ≤ 2 * |l|) (hκ1 : κ ≤ 1) (z : EuclideanSpace ℝ (Fin p)) :
    κ * ‖z‖ ≤ ‖Tcan w l z‖ := by
  have hww := Framed.inner_self_of_norm_one hw
  set a := ⟪w, z⟫ with ha
  set u := z - a • w with hu
  have hwu : ⟪w, u⟫ = 0 := by
    rw [hu, inner_sub_right, real_inner_smul_right, hww]; ring
  have hT : Tcan w l z = (2 * l * a) • w + u := by
    rw [Tcan_apply, smul_smul]
  have hz : z = a • w + u := by rw [hu]; abel
  have hN1 : ‖Tcan w l z‖ ^ 2 = (2 * l * a) ^ 2 + ‖u‖ ^ 2 := by
    rw [hT, norm_add_sq_real, norm_smul, real_inner_smul_left, hwu, Real.norm_eq_abs, hw, mul_one,
      sq_abs]
    ring
  have hN2 : ‖z‖ ^ 2 = a ^ 2 + ‖u‖ ^ 2 := by
    rw [hz, norm_add_sq_real, norm_smul, real_inner_smul_left, hwu, Real.norm_eq_abs, hw, mul_one,
      sq_abs]
    ring
  have hκ2 : κ ^ 2 ≤ (2 * l) ^ 2 := by
    have : (2 * l) ^ 2 = (2 * |l|) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
    rw [this]; exact pow_le_pow_left₀ hκ0 hκl 2
  have hκ3 : κ ^ 2 ≤ 1 := by nlinarith
  have h1 : (κ * ‖z‖) ^ 2 ≤ ‖Tcan w l z‖ ^ 2 := by
    rw [mul_pow, hN2, hN1]
    have := sq_nonneg a
    have := sq_nonneg ‖u‖
    nlinarith
  exact (pow_le_pow_iff_left₀ (mul_nonneg hκ0 (norm_nonneg _)) (norm_nonneg _) two_ne_zero).1 h1

end linalg

/-! ### The moving family -/

section movePath

/-- The first coordinate vector `e₀`. -/
def eZero (hp : 1 ≤ p) : EuclideanSpace ℝ (Fin p) := EuclideanSpace.single ⟨0, hp⟩ 1

theorem norm_eZero (hp : 1 ≤ p) : ‖eZero hp‖ = 1 := norm_single_one _

/-- The scale `σ (1/2 + (a - 1/2) ρ₀ t)`, from `σ/2` to `σ a`. -/
def lPath (a σ : ℝ) (ρ₀ : ℝ → ℝ) (t : ℝ) : ℝ := σ * (1 / 2 + (a - 1 / 2) * ρ₀ t)

/-- The frame `Tcan e₀ (l t)` of the moving family. -/
def τPath (hp : 1 ≤ p) (a σ : ℝ) (ρ₀ : ℝ → ℝ) (t : ℝ) : Fin p → EuclideanSpace ℝ (Fin p) :=
  fun i => Tcan (eZero hp) (lPath a σ ρ₀ t) (EuclideanSpace.single i 1)

/-- The centre `ρ₀ t σ a e₀` of the moving family. -/
def γPath (hp : 1 ≤ p) (a σ : ℝ) (ρ₀ : ℝ → ℝ) (t : ℝ) : EuclideanSpace ℝ (Fin p) :=
  (ρ₀ t * (σ * a)) • eZero hp

variable (hp : 1 ≤ p) {a σ : ℝ} {ρ₀ : ℝ → ℝ}

theorem basisCLM_τPath (t : ℝ) :
    basisCLM (τPath hp a σ ρ₀ t) = Tcan (eZero hp) (lPath a σ ρ₀ t) :=
  basisCLM_apply_single_eq _

theorem contDiff_basisCLM_τPath (hρ₀ : ContDiff ℝ ∞ ρ₀) :
    ContDiff ℝ ∞ (fun t => basisCLM (τPath hp a σ ρ₀ t)) := by
  have hfun : (fun t => basisCLM (τPath hp a σ ρ₀ t)) = fun t =>
      (2 * lPath a σ ρ₀ t) • projW (eZero hp) +
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p)) - projW (eZero hp)) := by
    funext t; rw [basisCLM_τPath]; rfl
  rw [hfun]
  have hl : ContDiff ℝ ∞ (lPath a σ ρ₀) :=
    contDiff_const.mul (contDiff_const.add (contDiff_const.mul hρ₀))
  exact ((contDiff_const.mul hl).smul contDiff_const).add contDiff_const

theorem contDiff_γPath (hρ₀ : ContDiff ℝ ∞ ρ₀) : ContDiff ℝ ∞ (γPath hp a σ ρ₀) :=
  (hρ₀.mul contDiff_const).smul contDiff_const

variable {hp} in
theorem abs_lPath (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hσ : σ * σ = 1) (hρ01 : ∀ t, 0 ≤ ρ₀ t ∧ ρ₀ t ≤ 1)
    (t : ℝ) : a ≤ |lPath a σ ρ₀ t| ∧ |lPath a σ ρ₀ t| ≤ 1 / 2 := by
  have hσ1 : |σ| = 1 := by
    have h : |σ| * |σ| = 1 := by rw [← abs_mul, hσ, abs_one]
    nlinarith [abs_nonneg σ]
  have h0 := (hρ01 t).1
  have h1 := (hρ01 t).2
  have hpos : 0 ≤ 1 / 2 + (a - 1 / 2) * ρ₀ t := by nlinarith
  rw [lPath, abs_mul, hσ1, one_mul, abs_of_nonneg hpos]
  constructor <;> nlinarith

theorem linearIndependent_τPath (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hσ : σ * σ = 1)
    (hρ01 : ∀ t, 0 ≤ ρ₀ t ∧ ρ₀ t ≤ 1) (t : ℝ) : LinearIndependent ℝ (τPath hp a σ ρ₀ t) := by
  have hl : lPath a σ ρ₀ t ≠ 0 := by
    intro h
    have := (abs_lPath ha ha2 hσ hρ01 t).1
    rw [h, abs_zero] at this
    linarith
  exact (linearIndependent_single (m := p)).map'
    (Tcan (eZero hp) (lPath a σ ρ₀ t) : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p))
    (LinearMap.ker_eq_bot.2 (Tcan_injective (norm_eZero hp) hl))

theorem norm_γPath_le (ha : 0 < a) (hσ : σ * σ = 1) (hρ01 : ∀ t, 0 ≤ ρ₀ t ∧ ρ₀ t ≤ 1) (t : ℝ) :
    ‖γPath hp a σ ρ₀ t‖ ≤ a := by
  have hσ1 : |σ| = 1 := by
    have h : |σ| * |σ| = 1 := by rw [← abs_mul, hσ, abs_one]
    nlinarith [abs_nonneg σ]
  rw [γPath, norm_smul, norm_eZero, mul_one, Real.norm_eq_abs, abs_mul, abs_mul, hσ1, one_mul,
    abs_of_pos ha, abs_of_nonneg (hρ01 t).1]
  nlinarith [(hρ01 t).2]

/-- The moving family is `south` far from the centre. -/
theorem moveΦ_south {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    {c ε₀ r₀ : ℝ} (hcs : ∀ z, ε₀ / 2 ≤ ‖z‖ → collapse hb c z = south) (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (har : 2 * a ≤ r₀) (hε₀ : ε₀ / 2 ≤ a * r₀) (hσ : σ * σ = 1)
    (hρ01 : ∀ t, 0 ≤ ρ₀ t ∧ ρ₀ t ≤ 1) (s : EuclideanSpace ℝ (Fin p)) (t : ℝ) (hs : r₀ ≤ ‖s‖) :
    moveΦ hb c (τPath hp a σ ρ₀) (γPath hp a σ ρ₀) (s, t) = south := by
  have hμ : ∀ t z, (2 * a) * ‖z‖ ≤ ‖basisCLM (τPath hp a σ ρ₀ t) z‖ := by
    intro t z
    rw [basisCLM_τPath]
    have hb' := abs_lPath ha (by linarith) hσ hρ01 t
    exact norm_Tcan_ge (norm_eZero hp) (by linarith) (by linarith [hb'.1]) (by linarith) z
  refine moveΦ_eq_south hb hcs hμ _ ?_
  have h1 := norm_γPath_le hp ha hσ hρ01 t
  have h2 : ‖s‖ - ‖γPath hp a σ ρ₀ t‖ ≤ ‖s - γPath hp a σ ρ₀ t‖ := norm_sub_norm_le _ _
  nlinarith

end movePath

section moveCob

variable (hp : 1 ≤ p)

/-- The folded collapse map `s ↦ collapse(Tcan e₀ (σ a) (s - σ a e₀))` (the end of the moving
family), written as a constant moving family. -/
def foldΦ {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b) (c a σ : ℝ)
    (s : EuclideanSpace ℝ (Fin p)) : Sph p :=
  moveΦ hb c (τPath hp a σ (fun _ => 1)) (γPath hp a σ (fun _ => 1)) (s, 0)

end moveCob

section congrFun

variable {hMc : IsCompact M} {hne : M.Nonempty}

theorem pontryagin_congr_fun {f g : M → Sph p} (h : f = g)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g) {y : Sph p}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    (hy' : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g y)
    (hnp : n + p = m) (b : Fin p → EuclideanSpace ℝ (Fin p)) (hb : LinearIndependent ℝ b) :
    pontryagin hM hMc hne hf hy hnp b hb = pontryagin hM hMc hne hg hy' hnp b hb := by
  subst h; rfl

end congrFun

/-! ### The folded map and the moving cobordism -/

section fold

variable (hp : 1 ≤ p) {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
  {c a σ : ℝ}

theorem contMDiff_foldΦ :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (foldΦ hp hb c a σ) :=
  (contMDiff_moveΦ hb c (contDiff_basisCLM_τPath hp contDiff_const)
    (contDiff_γPath hp contDiff_const)).comp (contMDiff_id.prodMk contMDiff_const)

theorem foldΦ_south {ε₀ r₀ : ℝ} (hcs : ∀ z, ε₀ / 2 ≤ ‖z‖ → collapse hb c z = south) (ha : 0 < a)
    (ha4 : a ≤ 1 / 4) (har : 2 * a ≤ r₀) (hε₀ : ε₀ / 2 ≤ a * r₀) (hσ : σ * σ = 1)
    (s : EuclideanSpace ℝ (Fin p)) (hs : r₀ ≤ ‖s‖) : foldΦ hp hb c a σ s = south :=
  moveΦ_south hp hb hcs ha ha4 har hε₀ hσ (fun _ => ⟨zero_le_one, le_rfl⟩) s 0 hs

theorem γPath_one_zero : γPath hp a σ (fun _ => 1) 0 = (σ * a) • eZero hp := by
  simp [γPath]

theorem lPath_one : lPath a σ (fun _ => 1) 0 = σ * a := by
  simp only [lPath]; ring

theorem foldΦ_eq_north_iff (hc : c ≠ 0) (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hσ : σ * σ = 1)
    (s : EuclideanSpace ℝ (Fin p)) : foldΦ hp hb c a σ s = north ↔ s = (σ * a) • eZero hp := by
  unfold foldΦ
  rw [moveΦ_eq_north_iff hb hc (linearIndependent_τPath hp ha ha2 hσ
    (fun _ => ⟨zero_le_one, le_rfl⟩)), γPath_one_zero]

theorem hasMFDerivAt_foldΦ :
    HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (foldΦ hp hb c a σ) ((σ * a) • eZero hp)
      ((c • basisCLM b).comp (Tcan (eZero hp) (σ * a))) := by
  have h := hasMFDerivAt_moveΦ_slice hb c (τPath hp a σ (fun _ => 1)) (γPath hp a σ (fun _ => 1)) 0
  rw [γPath_one_zero, basisCLM_τPath, lPath_one] at h
  exact h

end fold

section foldTube

variable {hMc : IsCompact M} {hne : M.Nonempty} {F : FramedSub hM n p} [Nonempty F.N]
  (T : TubeData hMc hne F) (hp : 1 ≤ p)

theorem isRegularValue_tubeMap_fold {b : Fin p → EuclideanSpace ℝ (Fin p)}
    (hb : LinearIndependent ℝ b) {c a σ : ℝ} (hc : 0 < c) (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (hσ : σ * σ = 1)
    (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
        (tubeMap T (foldΦ hp hb c a σ))) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (tubeMap T (foldΦ hp hb c a σ)) north := by
  refine isRegularValue_tubeMap T hk (contMDiff_foldΦ hp hb) fun s _ hs => ?_
  rw [(foldΦ_eq_north_iff hp hb hc.ne' ha ha2 hσ s).1 hs,
    HasMFDerivAt.mfd_eq (hasMFDerivAt_foldΦ hp hb (c := c) (a := a) (σ := σ))]
  have hl : σ * a ≠ 0 := by
    intro h
    rcases mul_eq_zero.1 h with h | h
    · rw [h, zero_mul] at hσ; norm_num at hσ
    · linarith
  have hsc : Surjective (c • basisCLM b) := by
    intro y
    obtain ⟨x, hx⟩ := (basisCLM_bijective hb).2 (c⁻¹ • y)
    exact ⟨x, by rw [smul_apply, hx, smul_inv_smul₀ hc.ne']⟩
  exact hsc.comp (Tcan_bijective (norm_eZero hp) hl).2

/-- **The moving cobordism**: the framed submanifold `(N, σᵢ vᵢ)` is framed cobordant to the
Pontryagin manifold of the folded tube map, a parallel copy of `N` at `σ a e₀`. -/
theorem framedCobordant_fold {c a r₀ ε₀ σ : ℝ} (hc : 0 < c)
    (hcs : ∀ z, ε₀ / 2 ≤ ‖z‖ → collapse (linearIndependent_single (m := p)) c z = south)
    (ha : 0 < a) (ha4 : a ≤ 1 / 4) (har : 2 * a ≤ r₀) (hr₀ : r₀ < T.ε) (hε₀ : ε₀ / 2 ≤ a * r₀)
    (hσ : σ * σ = 1) (F' : FramedSub hM n p) (hN : F'.N = F.N)
    (hv : ∀ i (x : M) (hx : x ∈ F.N) (hx' : x ∈ F'.N),
      F'.v i ⟨x, hx'⟩ = (if i = ⟨0, hp⟩ then σ else 1) • F.v i ⟨x, hx⟩)
    (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
        (tubeMap T (foldΦ hp (linearIndependent_single (m := p)) c a σ)))
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (tubeMap T (foldΦ hp (linearIndependent_single (m := p)) c a σ)) north)
    (hcb : LinearIndependent ℝ (fun i => c • EuclideanSpace.single i (1 : ℝ))) :
    FramedCobordant hM F' (pontryagin hM hMc hne hk hy F.dim _ hcb) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hb := linearIndependent_single (m := p)
  obtain ⟨ρ₀, hρs, hρ0, hρ1, hρ01, -⟩ :=
    exists_timeTransition (ε := 1 / 4) (by norm_num) (by norm_num)
  have hτ := contDiff_basisCLM_τPath hp (a := a) (σ := σ) hρs
  have hτi := linearIndependent_τPath hp ha (by linarith) hσ hρ01
  have hγ := contDiff_γPath hp (a := a) (σ := σ) hρs
  have hΦ : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin p)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (moveΦ hb c (τPath hp a σ ρ₀) (γPath hp a σ ρ₀)) :=
    contMDiff_moveΦ hb c hτ hγ
  have hsouth := moveΦ_south hp hb hcs ha ha4 har hε₀ hσ hρ01
  have hH := contMDiff_tubeHom T hΦ hr₀ hsouth
  have hHreg := isRegularValue_tubeHom T hH hΦ (fun s t _ hst => by
    rw [(moveΦ_eq_north_iff hb hc.ne' hτi _ s t).1 hst]
    exact surjective_mfderiv_moveΦ hb hc.ne' hτ hτi hγ t)
  have hslice : ∀ t₀ : ℝ, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun s => moveΦ hb c (τPath hp a σ ρ₀) (γPath hp a σ ρ₀) (s, t₀)) := fun t₀ =>
    hΦ.comp (contMDiff_id.prodMk contMDiff_const)
  have hk0 := contMDiff_tubeMap T (hslice 0) hr₀ (fun s hs => hsouth s 0 hs)
  have hk1 := contMDiff_tubeMap T (hslice 1) hr₀ (fun s hs => hsouth s 1 hs)
  have hγ0 : γPath hp a σ ρ₀ 0 = 0 := by simp [γPath, hρ0 0 (by norm_num)]
  have hl0 : lPath a σ ρ₀ 0 = σ / 2 := by
    simp only [lPath, hρ0 0 (by norm_num)]; ring
  have hzero0 : ∀ s, ‖s‖ < T.ε →
      (moveΦ hb c (τPath hp a σ ρ₀) (γPath hp a σ ρ₀) (s, 0) = north ↔ s = 0) := by
    intro s _
    rw [moveΦ_eq_north_iff hb hc.ne' hτi, hγ0]
  have hline0 : ∀ (i : Fin p) (s : ℝ), |s| < 1 →
      moveΦ hb c (τPath hp a σ ρ₀) (γPath hp a σ ρ₀)
        ((s * (if i = ⟨0, hp⟩ then σ else 1)) • EuclideanSpace.single i 1, 0) =
        collapse hb c (s • EuclideanSpace.single i 1) := by
    intro i s _
    show collapse hb c (basisCLM (τPath hp a σ ρ₀ 0)
      ((s * (if i = ⟨0, hp⟩ then σ else 1)) • EuclideanSpace.single i 1 - γPath hp a σ ρ₀ 0)) = _
    rw [basisCLM_τPath, hγ0, sub_zero, hl0]
    exact congrArg (collapse hb c) (Tcan_half_line hp hσ i s)
  have hsg : ∀ i : Fin p, |(if i = ⟨0, hp⟩ then σ else 1)| = 1 := by
    intro i
    split_ifs
    · have h : |σ| * |σ| = 1 := by rw [← abs_mul, hσ, abs_one]
      nlinarith [abs_nonneg σ]
    · exact abs_one
  obtain ⟨hy0, hcb0, hP0⟩ := pontryagin_tubeMap_eq T F' hN _ hsg hv hk0 hzero0 hb hc one_pos hline0
  have hfun1 : tubeMap T (fun s => moveΦ hb c (τPath hp a σ ρ₀) (γPath hp a σ ρ₀) (s, 1)) =
      tubeMap T (foldΦ hp hb c a σ) := by
    have hτ1 : τPath hp a σ ρ₀ 1 = τPath hp a σ (fun _ => 1) 0 := by
      funext i; simp only [τPath, lPath, hρ1 1 (by norm_num)]
    have hγ1 : γPath hp a σ ρ₀ 1 = γPath hp a σ (fun _ => 1) 0 := by
      simp only [γPath, hρ1 1 (by norm_num)]
    congr 1
    funext s
    show collapse hb c (basisCLM (τPath hp a σ ρ₀ 1) (s - γPath hp a σ ρ₀ 1)) =
      collapse hb c (basisCLM (τPath hp a σ (fun _ => 1) 0) (s - γPath hp a σ (fun _ => 1) 0))
    rw [hτ1, hγ1]
  have hy1 : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (tubeMap T (fun s => moveΦ hb c (τPath hp a σ ρ₀) (γPath hp a σ ρ₀) (s, 1))) north := by
    rw [hfun1]; exact hy
  have hcob := framedCobordant_of_homotopy hM hMc hne F.dim (ε := 1 / 4) (by norm_num)
    (by norm_num) hH hHreg
    (f := tubeMap T (fun s => moveΦ hb c (τPath hp a σ ρ₀) (γPath hp a σ ρ₀) (s, 0)))
    (g := tubeMap T (fun s => moveΦ hb c (τPath hp a σ ρ₀) (γPath hp a σ ρ₀) (s, 1)))
    (fun x t ht => by
      rw [tubeHom_apply]
      congr 1
      funext s
      refine moveΦ_congr_time hb c ?_ ?_ s
      · funext i; simp only [τPath, lPath, hρ0 t ht, hρ0 0 (by norm_num)]
      · simp only [γPath, hρ0 t ht, hρ0 0 (by norm_num)])
    (fun x t ht => by
      rw [tubeHom_apply]
      congr 1
      funext s
      refine moveΦ_congr_time hb c ?_ ?_ s
      · funext i; simp only [τPath, lPath, hρ1 t ht, hρ1 1 (by norm_num)]
      · simp only [γPath, hρ1 t ht, hρ1 1 (by norm_num)])
    hk0 hy0 hk1 hy1 _ hcb0
  rw [hP0, pontryagin_congr_fun hfun1 hk1 hk hy1 hy F.dim] at hcob
  exact hcob

end foldTube

/-! ### The cancelling family -/

section cancel

variable (hp : 1 ≤ p) {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
  {c a : ℝ}

/-- The time-`0` map of the cancelling family: `s ↦ collapse((s₀² - a²) e₀ + (s - s₀ e₀))`. -/
def can0 (c a : ℝ) (s : EuclideanSpace ℝ (Fin p)) : Sph p :=
  cancelΦ hb c (eZero hp) a (fun _ => 1) 0 (s, 0)

theorem contMDiff_can0 :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (can0 hp hb c a) :=
  (contMDiff_cancelΦ hb c (eZero hp) a contDiff_const 0).comp
    (contMDiff_id.prodMk contMDiff_const)

theorem can0_south {ε₀ r₀ : ℝ} (hcs : ∀ z, ε₀ / 2 ≤ ‖z‖ → collapse hb c z = south) (ha : 0 < a)
    (har : 2 * a ≤ r₀) (hε₀ : ε₀ / 2 ≤ min (r₀ / 2) (r₀ ^ 2 / 4)) (s : EuclideanSpace ℝ (Fin p))
    (hs : r₀ ≤ ‖s‖) : can0 hp hb c a s = south :=
  cancelΦ_eq_south hb hcs (norm_eZero hp) ha (fun _ => by norm_num) har hε₀ 0
    (by rwa [sub_zero])

theorem can0_eq_north_iff (hc : c ≠ 0) (s : EuclideanSpace ℝ (Fin p)) :
    can0 hp hb c a s = north ↔ s = (1 * a) • eZero hp ∨ s = (-1 * a) • eZero hp := by
  unfold can0
  rw [cancelΦ_eq_north_iff hb hc (norm_eZero hp)]
  constructor
  · rintro ⟨l, rfl, hl⟩
    have hl' : l ^ 2 = a ^ 2 := by simpa using hl
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hl' with h | h
    · left; rw [h, zero_add, one_mul]
    · right; rw [h, zero_add, neg_one_mul]
  · rintro (h | h)
    · exact ⟨1 * a, by rw [h, zero_add], by ring⟩
    · exact ⟨-1 * a, by rw [h, zero_add], by ring⟩

theorem hasMFDerivAt_can0 {σ : ℝ} (hσ : σ * σ = 1) :
    HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (can0 hp hb c a) ((σ * a) • eZero hp)
      ((c • basisCLM b).comp (Tcan (eZero hp) (σ * a))) := by
  have hl : (σ * a) ^ 2 = a ^ 2 * (fun _ => (1 : ℝ)) (0 : ℝ) := by
    simp only [mul_one]; linear_combination a ^ 2 * hσ
  have h := hasMFDerivAt_cancelΦ_slice hb c (norm_eZero hp) a (fun _ => 1) 0 0 hl
  rw [zero_add] at h
  exact h

end cancel

section cancelTube

variable {hMc : IsCompact M} {hne : M.Nonempty} {F : FramedSub hM n p} [Nonempty F.N]
  (T : TubeData hMc hne F) (hp : 1 ≤ p)

theorem surjective_scaled_Tcan {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    {c l : ℝ} (hc : c ≠ 0) (hl : l ≠ 0) :
    Surjective ((c • basisCLM b).comp (Tcan (eZero hp) l)) := by
  have hsc : Surjective (c • basisCLM b) := by
    intro y
    obtain ⟨x, hx⟩ := (basisCLM_bijective hb).2 (c⁻¹ • y)
    exact ⟨x, by rw [smul_apply, hx, smul_inv_smul₀ hc]⟩
  exact hsc.comp (Tcan_bijective (norm_eZero hp) hl).2

theorem isRegularValue_tubeMap_can0 {b : Fin p → EuclideanSpace ℝ (Fin p)}
    (hb : LinearIndependent ℝ b) {c a : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
        (tubeMap T (can0 hp hb c a))) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (tubeMap T (can0 hp hb c a)) north := by
  refine isRegularValue_tubeMap T hk (contMDiff_can0 hp hb) fun s _ hs => ?_
  rcases (can0_eq_north_iff hp hb hc.ne' s).1 hs with h | h
  · rw [h, HasMFDerivAt.mfd_eq (hasMFDerivAt_can0 hp hb (c := c) (a := a)
      (show (1 : ℝ) * 1 = 1 by norm_num))]
    exact surjective_scaled_Tcan hp hb hc.ne' (by positivity)
  · rw [h, HasMFDerivAt.mfd_eq (hasMFDerivAt_can0 hp hb (c := c) (a := a)
      (show (-1 : ℝ) * -1 = 1 by norm_num))]
    exact surjective_scaled_Tcan hp hb hc.ne' (by nlinarith)

/-- **The cancelling cobordism**: the Pontryagin manifold of the time-`0` map (two parallel
copies of `N`) is framed null-cobordant. -/
theorem framedCobordant_can0 {c a r₀ ε₀ : ℝ} (hc : 0 < c)
    (hcs : ∀ z, ε₀ / 2 ≤ ‖z‖ → collapse (linearIndependent_single (m := p)) c z = south)
    (ha : 0 < a) (har : 2 * a ≤ r₀) (hr₀ : r₀ < T.ε) (hε₀ : ε₀ / 2 ≤ min (r₀ / 2) (r₀ ^ 2 / 4))
    (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
        (tubeMap T (can0 hp (linearIndependent_single (m := p)) c a)))
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (tubeMap T (can0 hp (linearIndependent_single (m := p)) c a)) north)
    (hcb : LinearIndependent ℝ (fun i => c • EuclideanSpace.single i (1 : ℝ))) :
    FramedCobordant hM (pontryagin hM hMc hne hk hy F.dim _ hcb) (emptyFramedSub F.dim) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hb := linearIndependent_single (m := p)
  obtain ⟨ρ, hρs, hρ0, hρ1, hρb, hρ'⟩ := exists_rho (ε := 1 / 4) (by norm_num) (by norm_num)
  have hΦ := contMDiff_cancelΦ hb c (eZero hp) a hρs 0
  have hsouth : ∀ s t, r₀ ≤ ‖s‖ → cancelΦ hb c (eZero hp) a ρ 0 (s, t) = south :=
    fun s t hs => cancelΦ_eq_south hb hcs (norm_eZero hp) ha hρb har hε₀ 0 (by rwa [sub_zero])
  have hH := contMDiff_tubeHom T hΦ hr₀ hsouth
  have hHreg := isRegularValue_tubeHom T hH hΦ (fun s t _ hst => by
    obtain ⟨l, hs, hl⟩ := (cancelΦ_eq_north_iff hb hc.ne' (norm_eZero hp) a ρ 0 s t).1 hst
    rw [hs]
    exact surjective_mfderiv_cancelΦ hb hc.ne' (norm_eZero hp) ha hρs hρ' 0 hl)
  have hk1 := contMDiff_tubeMap T (hΦ.comp (contMDiff_id.prodMk contMDiff_const)) hr₀
    (fun s hs => hsouth s 1 hs)
  have hno : ∀ z, tubeMap T (fun s => cancelΦ hb c (eZero hp) a ρ 0 (s, 1)) z ≠ north := by
    intro z hz
    obtain ⟨-, h⟩ := (tubeMap_eq_north_iff T).1 hz
    obtain ⟨l, -, hl⟩ := (cancelΦ_eq_north_iff hb hc.ne' (norm_eZero hp) a ρ 0 _ 1).1 h
    rw [hρ1 1 (by norm_num)] at hl
    nlinarith [sq_nonneg l, sq_pos_of_pos ha]
  have hy1 : IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      (tubeMap T (fun s => cancelΦ hb c (eZero hp) a ρ 0 (s, 1))) north :=
    fun z hz => absurd hz (hno z)
  have hcob := framedCobordant_of_homotopy hM hMc hne F.dim (ε := 1 / 4) (by norm_num)
    (by norm_num) hH hHreg (f := tubeMap T (can0 hp hb c a))
    (g := tubeMap T (fun s => cancelΦ hb c (eZero hp) a ρ 0 (s, 1)))
    (fun x t ht => by
      rw [tubeHom_apply]
      congr 1
      funext s
      show cancelΦ hb c (eZero hp) a ρ 0 (s, t) = cancelΦ hb c (eZero hp) a (fun _ => 1) 0 (s, 0)
      simp only [cancelΦ, cancelG, hρ0 t ht])
    (fun x t ht => by
      rw [tubeHom_apply]
      congr 1
      funext s
      exact cancelΦ_congr_time hb c (eZero hp) a 0 (by rw [hρ1 t ht, hρ1 1 (by norm_num)]) s)
    hk hy hk1 hy1 _ hcb
  have hempty : pontryagin hM hMc hne hk1 hy1 F.dim _ hcb = emptyFramedSub F.dim := by
    refine eq_empty_of_N _ ?_
    ext z
    simp only [mem_empty_iff_false, iff_false]
    exact hno z
  rw [hempty] at hcob
  exact hcob

/-- Two maps with the same derivative of the local form at a point of the tube have the same
derivative. -/
theorem mfd_tubeMap_eq {Φ Ψ : EuclideanSpace ℝ (Fin p) → Sph p}
    (hkΦ : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (tubeMap T Φ))
    (hkΨ : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ (tubeMap T Ψ))
    {z : M} (hz : z ∈ T.V)
    {L : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}
    (hΦ : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) Φ
      (T.Ginv z).2 L)
    (hΨ : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) Ψ
      (T.Ginv z).2 L) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (tubeMap T Φ) z =
      mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) (tubeMap T Ψ) z := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := F.hN.chartedSpace
  haveI := F.hN.isManifold
  have hq := T.Ginv_mem hz
  have h1 := mfd_tubeMap_comp T hkΦ hq hΦ.mdifferentiableAt
  have h2 := mfd_tubeMap_comp T hkΨ hq hΨ.mdifferentiableAt
  rw [T.G_Ginv hz] at h1 h2
  rw [HasMFDerivAt.mfd_eq hΦ] at h1
  rw [HasMFDerivAt.mfd_eq hΨ] at h2
  have heq := h1.trans h2.symm
  have hsurj := (T.hbij _ hq).2
  refine ContinuousLinearMap.ext fun v => ?_
  obtain ⟨u, rfl⟩ := hsurj v
  exact DFunLike.congr_fun heq u

/-- **Splitting the time-`0` end** of the cancelling family into the two folded copies. -/
theorem pontryagin_can0_eq_union {c a : ℝ} (hc : 0 < c) (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (hk : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
        (tubeMap T (can0 hp (linearIndependent_single (m := p)) c a)))
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (tubeMap T (can0 hp (linearIndependent_single (m := p)) c a)) north)
    (hkP : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
        (tubeMap T (foldΦ hp (linearIndependent_single (m := p)) c a 1)))
    (hyP : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (tubeMap T (foldΦ hp (linearIndependent_single (m := p)) c a 1)) north)
    (hkM : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
        (tubeMap T (foldΦ hp (linearIndependent_single (m := p)) c a (-1))))
    (hyM : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
        (tubeMap T (foldΦ hp (linearIndependent_single (m := p)) c a (-1))) north)
    (hcb : LinearIndependent ℝ (fun i => c • EuclideanSpace.single i (1 : ℝ)))
    (hd : Disjoint (pontryagin hM hMc hne hkP hyP F.dim _ hcb).N
      (pontryagin hM hMc hne hkM hyM F.dim _ hcb).N) :
    pontryagin hM hMc hne hk hy F.dim _ hcb =
      (pontryagin hM hMc hne hkP hyP F.dim _ hcb).union
        (pontryagin hM hMc hne hkM hyM F.dim _ hcb) hd := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hb := linearIndependent_single (m := p)
  have hσP : (1 : ℝ) * 1 = 1 := by norm_num
  have hσM : (-1 : ℝ) * -1 = 1 := by norm_num
  have hmemP : ∀ z, z ∈ tubeMap T (foldΦ hp hb c a 1) ⁻¹' {north} ↔
      z ∈ T.V ∧ (T.Ginv z).2 = (1 * a) • eZero hp := by
    intro z
    show tubeMap T _ z = north ↔ _
    rw [tubeMap_eq_north_iff, foldΦ_eq_north_iff hp hb hc.ne' ha ha2 hσP]
  have hmemM : ∀ z, z ∈ tubeMap T (foldΦ hp hb c a (-1)) ⁻¹' {north} ↔
      z ∈ T.V ∧ (T.Ginv z).2 = (-1 * a) • eZero hp := by
    intro z
    show tubeMap T _ z = north ↔ _
    rw [tubeMap_eq_north_iff, foldΦ_eq_north_iff hp hb hc.ne' ha ha2 hσM]
  have hN : tubeMap T (can0 hp hb c a) ⁻¹' {north} =
      tubeMap T (foldΦ hp hb c a 1) ⁻¹' {north} ∪ tubeMap T (foldΦ hp hb c a (-1)) ⁻¹' {north} := by
    ext z
    rw [mem_union, hmemP, hmemM]
    show tubeMap T _ z = north ↔ _
    rw [tubeMap_eq_north_iff, can0_eq_north_iff hp hb hc.ne']
    tauto
  refine FramedSub.ext' hM hN ?_
  intro i x hx hx'
  by_cases hxP : x ∈ tubeMap T (foldΦ hp hb c a 1) ⁻¹' {north}
  · have hxV := (hmemP x).1 hxP
    have hmfd := mfd_tubeMap_eq T hk hkP hxV.1
      (by rw [hxV.2]; exact hasMFDerivAt_can0 hp hb hσP)
      (by rw [hxV.2]; exact hasMFDerivAt_foldΦ hp hb)
    have e1 := pontryagin_v_eq_of_mfd_eq F.dim hk hkP hy hyP _ hcb hx hxP hmfd i
    have e2 := FramedSub.union_v_left (F := pontryagin hM hMc hne hkP hyP F.dim _ hcb)
      (G := pontryagin hM hMc hne hkM hyM F.dim _ hcb) (h := hd) i x hxP hx'
    exact e1.trans e2.symm
  · have hxM : x ∈ tubeMap T (foldΦ hp hb c a (-1)) ⁻¹' {north} := by
      have hx2 := hx'
      rcases hx2 with h | h
      · exact absurd h hxP
      · exact h
    have hxV := (hmemM x).1 hxM
    have hmfd := mfd_tubeMap_eq T hk hkM hxV.1
      (by rw [hxV.2]; exact hasMFDerivAt_can0 hp hb hσM)
      (by rw [hxV.2]; exact hasMFDerivAt_foldΦ hp hb)
    have e1 := pontryagin_v_eq_of_mfd_eq F.dim hk hkM hy hyM _ hcb hx hxM hmfd i
    have e2 := FramedSub.union_v_right (F := pontryagin hM hMc hne hkP hyP F.dim _ hcb)
      (G := pontryagin hM hMc hne hkM hyM F.dim _ hcb) (h := hd) i x hxM hx'
    exact e1.trans e2.symm

end cancelTube

/-! ### Cancelling a framed submanifold against its negative -/

section cancelPair

variable {hMc : IsCompact M} {hne : M.Nonempty}

/-- **`F ⊔ F⁻ ∼ ∅`**: two disjoint parallel copies of `F` and of `F` with the first framing
vector negated together bound the cancelling cobordism. -/
theorem exists_cancel_pair (hp : 1 ≤ p) {F : FramedSub hM n p} [Nonempty F.N]
    (T : TubeData hMc hne F) :
    ∃ (P Q : FramedSub hM n p) (hd : Disjoint P.N Q.N), FramedCobordant hM F P ∧
      FramedCobordant hM (F.negFirst hp) Q ∧
      FramedCobordant hM (P.union Q hd) (emptyFramedSub F.dim) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hb := linearIndependent_single (m := p)
  have hε := T.hε
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = min (T.ε / 8) (1 / 4) := ⟨_, rfl⟩
  have ha : 0 < a := by rw [ha_def]; exact lt_min (by linarith) (by norm_num)
  have ha4 : a ≤ 1 / 4 := by rw [ha_def]; exact min_le_right _ _
  have haε : a ≤ T.ε / 8 := by rw [ha_def]; exact min_le_left _ _
  obtain ⟨r₀, hr₀_def⟩ : ∃ r₀ : ℝ, r₀ = T.ε / 2 := ⟨_, rfl⟩
  have hr₀ : r₀ < T.ε := by rw [hr₀_def]; linarith
  have hr₀pos : 0 < r₀ := by rw [hr₀_def]; linarith
  have har : 2 * a ≤ r₀ := by rw [hr₀_def]; linarith
  obtain ⟨ε₀, hε₀_def⟩ : ∃ ε₀ : ℝ, ε₀ = min (min r₀ (r₀ ^ 2 / 2)) (a * r₀) := ⟨_, rfl⟩
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀_def]; exact lt_min (lt_min hr₀pos (by positivity)) (by positivity)
  have hε₀1 : ε₀ / 2 ≤ a * r₀ := by
    have : ε₀ ≤ a * r₀ := by rw [hε₀_def]; exact min_le_right _ _
    linarith
  have hε₀2 : ε₀ / 2 ≤ min (r₀ / 2) (r₀ ^ 2 / 4) := by
    have h1 : ε₀ ≤ r₀ := by rw [hε₀_def]; exact (min_le_left _ _).trans (min_le_left _ _)
    have h2 : ε₀ ≤ r₀ ^ 2 / 2 := by
      rw [hε₀_def]; exact (min_le_left _ _).trans (min_le_right _ _)
    exact le_min (by linarith) (by linarith)
  obtain ⟨c, hc, hcs⟩ := exists_scale hb hε₀pos
  have hcb : LinearIndependent ℝ (fun i : Fin p => c • EuclideanSpace.single i (1 : ℝ)) := by
    convert hb.units_smul (fun _ => Units.mk0 c hc.ne') using 1
    funext i
    simp [Pi.smul_apply', Units.smul_def]
  have hσP : (1 : ℝ) * 1 = 1 := by norm_num
  have hσM : (-1 : ℝ) * -1 = 1 := by norm_num
  have hkP := contMDiff_tubeMap T (contMDiff_foldΦ hp hb (c := c) (a := a) (σ := 1)) hr₀
    (foldΦ_south hp hb hcs ha ha4 har hε₀1 hσP)
  have hyP := isRegularValue_tubeMap_fold T hp hb hc ha (by linarith) hσP hkP
  have hkM := contMDiff_tubeMap T (contMDiff_foldΦ hp hb (c := c) (a := a) (σ := -1)) hr₀
    (foldΦ_south hp hb hcs ha ha4 har hε₀1 hσM)
  have hyM := isRegularValue_tubeMap_fold T hp hb hc ha (by linarith) hσM hkM
  have hk0 := contMDiff_tubeMap T (contMDiff_can0 hp hb (c := c) (a := a)) hr₀
    (can0_south hp hb hcs ha har hε₀2)
  have hy0 := isRegularValue_tubeMap_can0 T hp hb hc ha hk0
  have hFP := framedCobordant_fold T hp hc hcs ha ha4 har hr₀ hε₀1 hσP F rfl
    (fun i x hx hx' => by split_ifs <;> simp) hkP hyP hcb
  have hFQ := framedCobordant_fold T hp hc hcs ha ha4 har hr₀ hε₀1 hσM (F.negFirst hp) rfl
    (fun i x hx hx' => rfl) hkM hyM hcb
  have hd : Disjoint (pontryagin hM hMc hne hkP hyP F.dim _ hcb).N
      (pontryagin hM hMc hne hkM hyM F.dim _ hcb).N := by
    refine Set.disjoint_left.2 fun z hzP hzM => ?_
    have hzP' : tubeMap T (foldΦ hp hb c a 1) z = north := hzP
    have hzM' : tubeMap T (foldΦ hp hb c a (-1)) z = north := hzM
    have h1 := (tubeMap_eq_north_iff T).1 hzP'
    have h2 := (tubeMap_eq_north_iff T).1 hzM'
    rw [foldΦ_eq_north_iff hp hb hc.ne' ha (by linarith) hσP] at h1
    rw [foldΦ_eq_north_iff hp hb hc.ne' ha (by linarith) hσM] at h2
    have h3 := h1.2.symm.trans h2.2
    rw [← sub_eq_zero, ← sub_smul, smul_eq_zero] at h3
    rcases h3 with h | h
    · linarith
    · have := norm_eZero hp
      rw [h, norm_zero] at this
      norm_num at this
  have hsplit := pontryagin_can0_eq_union T hp hc ha (by linarith) hk0 hy0 hkP hyP hkM hyM hcb hd
  refine ⟨_, _, hd, hFP, hFQ, ?_⟩
  rw [← hsplit]
  exact framedCobordant_can0 T hp hc hcs ha har hr₀ hε₀2 hk0 hy0 hcb

end cancelPair

end CGroup

open CGroup

/-! ### The group structure -/

section group

variable {hMc : IsCompact M} {hne : M.Nonempty}

/-- **Disjoint representatives** of two classes (`p ≥ m/2 + 1`). -/
theorem exists_disjoint_rep (hbig : m + 2 ≤ 2 * p) (c c' : FramedClass hM hMc hne n p) :
    ∃ F G : FramedSub hM n p, (⟦F⟧ : FramedClass hM hMc hne n p) = c ∧
      (⟦G⟧ : FramedClass hM hMc hne n p) = c' ∧ Disjoint F.N G.N := by
  obtain ⟨F, rfl⟩ := Quotient.exists_rep c
  obtain ⟨G, rfl⟩ := Quotient.exists_rep c'
  obtain ⟨F', hFF', hF'G, -⟩ := exists_cobordant_disjoint hMc hne hbig F G G
  exact ⟨F', G, Quotient.sound hFF'.symm, rfl, hF'G⟩

variable (hMc hne) in
include hMc hne in
/-- **The disjoint union of framed cobordant pairs** (`p ≥ m/2 + 1`): if `F ∼ F₁`, `G ∼ G₁`,
`F ∩ G = ∅` and `F₁ ∩ G₁ = ∅`, then `F ⊔ G ∼ F₁ ⊔ G₁`. -/
theorem framedCobordant_union_of_framedCobordant (hbig : m + 2 ≤ 2 * p)
    {F F₁ G G₁ : FramedSub hM n p} (hF : FramedCobordant hM F F₁) (hG : FramedCobordant hM G G₁)
    (h : Disjoint F.N G.N) (h₁ : Disjoint F₁.N G₁.N) :
    FramedCobordant hM (F.union G h) (F₁.union G₁ h₁) :=
  framedCobordant_union_of_framedCobordant' hMc hne hbig hF hG h h₁

/-- **The addition of classes by disjoint union** (`p ≥ m/2 + 1`): the class of `F ⊔ G` for
disjoint representatives `F`, `G`. -/
def cohomotopyAdd (hbig : m + 2 ≤ 2 * p) (c c' : FramedClass hM hMc hne n p) :
    FramedClass hM hMc hne n p :=
  ⟦(Classical.choose (exists_disjoint_rep hbig c c')).union
    (Classical.choose (Classical.choose_spec (exists_disjoint_rep hbig c c')))
    (Classical.choose_spec (Classical.choose_spec (exists_disjoint_rep hbig c c'))).2.2⟧

theorem cohomotopyAdd_mk (hbig : m + 2 ≤ 2 * p) {F G : FramedSub hM n p} (h : Disjoint F.N G.N) :
    cohomotopyAdd hbig ⟦F⟧ ⟦G⟧ = (⟦F.union G h⟧ : FramedClass hM hMc hne n p) := by
  have hs := Classical.choose_spec (Classical.choose_spec
    (exists_disjoint_rep (hMc := hMc) (hne := hne) hbig ⟦F⟧ ⟦G⟧))
  exact Quotient.sound (framedCobordant_union_of_framedCobordant hMc hne hbig
    (Quotient.exact hs.1) (Quotient.exact hs.2.1) _ h)

theorem cohomotopyAdd_comm (hbig : m + 2 ≤ 2 * p) (c c' : FramedClass hM hMc hne n p) :
    cohomotopyAdd hbig c c' = cohomotopyAdd hbig c' c := by
  obtain ⟨F, G, rfl, rfl, h⟩ := exists_disjoint_rep hbig c c'
  rw [cohomotopyAdd_mk hbig h, cohomotopyAdd_mk hbig h.symm, union_comm' F G h]

theorem cohomotopyAdd_assoc (hbig : m + 2 ≤ 2 * p) (a b c : FramedClass hM hMc hne n p) :
    cohomotopyAdd hbig (cohomotopyAdd hbig a b) c =
      cohomotopyAdd hbig a (cohomotopyAdd hbig b c) := by
  obtain ⟨F, G, rfl, rfl, h⟩ := exists_disjoint_rep hbig a b
  obtain ⟨H, rfl⟩ := Quotient.exists_rep c
  obtain ⟨H', hHH', hH'F, hH'G⟩ := exists_cobordant_disjoint hMc hne hbig H F G
  have hc : (⟦H⟧ : FramedClass hM hMc hne n p) = ⟦H'⟧ := Quotient.sound hHH'
  have h₁ : Disjoint (F.union G h).N H'.N := Disjoint.union_left hH'F.symm hH'G.symm
  have h₂ : Disjoint G.N H'.N := hH'G.symm
  have h₃ : Disjoint F.N (G.union H' h₂).N := Disjoint.union_right h hH'F.symm
  rw [hc, cohomotopyAdd_mk hbig h, cohomotopyAdd_mk hbig h₁, cohomotopyAdd_mk hbig h₂,
    cohomotopyAdd_mk hbig h₃, union_assoc' F G H' h h₂ h₁ h₃]

theorem cohomotopyAdd_zero (hbig : m + 2 ≤ 2 * p) (hnp : n + p = m)
    (c : FramedClass hM hMc hne n p) :
    cohomotopyAdd hbig c ⟦emptyFramedSub hnp⟧ = c := by
  obtain ⟨F, rfl⟩ := Quotient.exists_rep c
  have h : Disjoint F.N (emptyFramedSub (hM := hM) hnp).N := by
    rw [emptyFramedSub_N]; exact disjoint_empty _
  rw [cohomotopyAdd_mk hbig h, union_empty' F h]

theorem zero_cohomotopyAdd (hbig : m + 2 ≤ 2 * p) (hnp : n + p = m)
    (c : FramedClass hM hMc hne n p) :
    cohomotopyAdd hbig ⟦emptyFramedSub hnp⟧ c = c :=
  (cohomotopyAdd_comm hbig _ c).trans (cohomotopyAdd_zero hbig hnp c)

end group

/-! ### Inverses and the group -/

section inverse

variable {hMc : IsCompact M} {hne : M.Nonempty}

/-- **`[F] + [F⁻] = 0`**, where `F⁻` is `F` with its first framing vector negated. -/
theorem cohomotopyAdd_negFirst (hbig : m + 2 ≤ 2 * p) (hp : 1 ≤ p) (F : FramedSub hM n p) :
    cohomotopyAdd hbig ⟦F⟧ ⟦F.negFirst hp⟧ =
      (⟦emptyFramedSub F.dim⟧ : FramedClass hM hMc hne n p) := by
  by_cases hNe : Nonempty F.N
  · haveI := hNe
    obtain ⟨T⟩ := exists_tubeData hMc hne F
    obtain ⟨P, Q, hd, hFP, hFQ, hPQ⟩ := exists_cancel_pair hp T
    have e1 : (⟦F⟧ : FramedClass hM hMc hne n p) = ⟦P⟧ := Quotient.sound hFP
    have e2 : (⟦F.negFirst hp⟧ : FramedClass hM hMc hne n p) = ⟦Q⟧ := Quotient.sound hFQ
    rw [e1, e2, cohomotopyAdd_mk hbig hd]
    exact Quotient.sound hPQ
  · have hN : F.N = ∅ := by
      rw [not_nonempty_iff] at hNe
      exact Set.eq_empty_of_isEmpty _
    have hd : Disjoint F.N (F.negFirst hp).N := by
      rw [FramedSub.negFirst_N, hN]; exact disjoint_empty _
    rw [cohomotopyAdd_mk hbig hd]
    congr 1
    exact eq_empty_of_N _ (by rw [FramedSub.union_N, FramedSub.negFirst_N, hN, Set.union_empty])

/-- The negation of classes: negate the first framing vector of a representative. -/
def cohomotopyNeg (hp : 1 ≤ p) (c : FramedClass hM hMc hne n p) : FramedClass hM hMc hne n p :=
  ⟦(Quotient.out c).negFirst hp⟧

/-- The negation of the class of `F` is the class of `F` with its first framing vector negated
(inverses are unique). -/
theorem cohomotopyNeg_mk (hnp : n + p = m) (hbig : m + 2 ≤ 2 * p) (hp : 1 ≤ p)
    (F : FramedSub hM n p) :
    cohomotopyNeg hp (⟦F⟧ : FramedClass hM hMc hne n p) = ⟦F.negFirst hp⟧ := by
  obtain ⟨F₀, hF₀⟩ : ∃ F₀, Quotient.out (⟦F⟧ : FramedClass hM hMc hne n p) = F₀ := ⟨_, rfl⟩
  have hF₀F : (⟦F₀⟧ : FramedClass hM hMc hne n p) = ⟦F⟧ := by
    rw [← hF₀]; exact Quotient.out_eq _
  have hneg : cohomotopyNeg hp (⟦F⟧ : FramedClass hM hMc hne n p) = ⟦F₀.negFirst hp⟧ := by
    unfold cohomotopyNeg; rw [hF₀]
  have h1 : cohomotopyAdd hbig ⟦F₀⟧ ⟦F₀.negFirst hp⟧ =
      (⟦emptyFramedSub hnp⟧ : FramedClass hM hMc hne n p) := cohomotopyAdd_negFirst hbig hp F₀
  have h2 : cohomotopyAdd hbig ⟦F⟧ ⟦F.negFirst hp⟧ =
      (⟦emptyFramedSub hnp⟧ : FramedClass hM hMc hne n p) := cohomotopyAdd_negFirst hbig hp F
  rw [hneg]
  have s1 : (⟦F₀.negFirst hp⟧ : FramedClass hM hMc hne n p) =
      cohomotopyAdd hbig ⟦F₀.negFirst hp⟧ ⟦emptyFramedSub hnp⟧ :=
    (cohomotopyAdd_zero hbig hnp _).symm
  have s2 : cohomotopyAdd hbig (⟦F₀.negFirst hp⟧ : FramedClass hM hMc hne n p)
      ⟦emptyFramedSub hnp⟧ =
      cohomotopyAdd hbig ⟦F₀.negFirst hp⟧ (cohomotopyAdd hbig ⟦F⟧ ⟦F.negFirst hp⟧) :=
    congrArg (cohomotopyAdd hbig ⟦F₀.negFirst hp⟧) h2.symm
  have s3 : cohomotopyAdd hbig (⟦F₀.negFirst hp⟧ : FramedClass hM hMc hne n p)
      (cohomotopyAdd hbig ⟦F⟧ ⟦F.negFirst hp⟧) =
      cohomotopyAdd hbig (cohomotopyAdd hbig ⟦F₀.negFirst hp⟧ ⟦F⟧) ⟦F.negFirst hp⟧ :=
    (cohomotopyAdd_assoc hbig _ _ _).symm
  have s4 : cohomotopyAdd hbig (cohomotopyAdd hbig
      (⟦F₀.negFirst hp⟧ : FramedClass hM hMc hne n p) ⟦F⟧) ⟦F.negFirst hp⟧ =
      cohomotopyAdd hbig (cohomotopyAdd hbig ⟦F₀.negFirst hp⟧ ⟦F₀⟧) ⟦F.negFirst hp⟧ :=
    congrArg (fun X => cohomotopyAdd hbig (cohomotopyAdd hbig ⟦F₀.negFirst hp⟧ X)
      ⟦F.negFirst hp⟧) hF₀F.symm
  have s5 : cohomotopyAdd hbig (cohomotopyAdd hbig
      (⟦F₀.negFirst hp⟧ : FramedClass hM hMc hne n p) ⟦F₀⟧) ⟦F.negFirst hp⟧ =
      cohomotopyAdd hbig (cohomotopyAdd hbig ⟦F₀⟧ ⟦F₀.negFirst hp⟧) ⟦F.negFirst hp⟧ :=
    congrArg (fun X => cohomotopyAdd hbig X ⟦F.negFirst hp⟧) (cohomotopyAdd_comm hbig _ _)
  have s6 : cohomotopyAdd hbig (cohomotopyAdd hbig
      (⟦F₀⟧ : FramedClass hM hMc hne n p) ⟦F₀.negFirst hp⟧) ⟦F.negFirst hp⟧ =
      cohomotopyAdd hbig ⟦emptyFramedSub hnp⟧ ⟦F.negFirst hp⟧ :=
    congrArg (fun X => cohomotopyAdd hbig X ⟦F.negFirst hp⟧) h1
  have s7 : cohomotopyAdd hbig (⟦emptyFramedSub hnp⟧ : FramedClass hM hMc hne n p)
      ⟦F.negFirst hp⟧ = ⟦F.negFirst hp⟧ :=
    zero_cohomotopyAdd hbig hnp _
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans s7)))))

end inverse

variable (hM) (hMc : IsCompact M) (hne : M.Nonempty)

/-- **Milnor §8, Problem 17 (the group).**  For `p ≥ m/2 + 1` the set `Πᵖ(M)` of framed cobordism
classes of framed submanifolds of codimension `p` is an abelian group under disjoint union: the
zero is the class of the empty submanifold and the inverse of `[F]` is the class of `F` with its
first framing vector negated. -/
@[instance_reducible]
def cohomotopyGroup (hnp : n + p = m) (hbig : m + 2 ≤ 2 * p) (hp : 1 ≤ p) :
    AddCommGroup (FramedClass hM hMc hne n p) :=
  letI iAdd : Add (FramedClass hM hMc hne n p) := ⟨cohomotopyAdd hbig⟩
  letI iZero : Zero (FramedClass hM hMc hne n p) := ⟨⟦emptyFramedSub hnp⟧⟩
  letI iNeg : Neg (FramedClass hM hMc hne n p) := ⟨cohomotopyNeg hp⟩
  { add := (· + ·)
    add_assoc := cohomotopyAdd_assoc hbig
    zero := 0
    zero_add := zero_cohomotopyAdd hbig hnp
    add_zero := cohomotopyAdd_zero hbig hnp
    nsmul := nsmulRec
    neg := Neg.neg
    zsmul := zsmulRec
    neg_add_cancel := fun c => by
      have key : cohomotopyAdd hbig ⟦(Quotient.out c).negFirst hp⟧ ⟦Quotient.out c⟧ =
          (⟦emptyFramedSub hnp⟧ : FramedClass hM hMc hne n p) :=
        (cohomotopyAdd_comm hbig _ _).trans (cohomotopyAdd_negFirst hbig hp _)
      have e : (⟦Quotient.out c⟧ : FramedClass hM hMc hne n p) = c := Quotient.out_eq c
      rw [e] at key
      exact key
    add_comm := cohomotopyAdd_comm hbig }

theorem cohomotopyGroup_add (hnp : n + p = m) (hbig : m + 2 ≤ 2 * p) (hp : 1 ≤ p) :
    (cohomotopyGroup hM hMc hne hnp hbig hp).add = cohomotopyAdd hbig := rfl

theorem cohomotopyGroup_zero (hnp : n + p = m) (hbig : m + 2 ≤ 2 * p) (hp : 1 ≤ p) :
    (cohomotopyGroup hM hMc hne hnp hbig hp).zero = ⟦emptyFramedSub hnp⟧ := rfl

theorem cohomotopyGroup_neg (hnp : n + p = m) (hbig : m + 2 ≤ 2 * p) (hp : 1 ≤ p)
    (F : FramedSub hM n p) :
    (cohomotopyGroup hM hMc hne hnp hbig hp).neg ⟦F⟧ = ⟦F.negFirst hp⟧ :=
  cohomotopyNeg_mk hnp hbig hp F

end Problems

end Milnor
