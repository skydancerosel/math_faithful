import Morse
import RoundTrip.Check
import RoundTrip.Blind.V13_11
import RoundTrip.Bridge

open Set Filter Topology Function Metric
open scoped ContDiff Manifold

namespace RoundTrip.V13_11

/-- The project's statement (universes instantiated at `0`): for a slice submanifold `N ⊆ V` (any
normed `V`, any finite-dimensional model `Z`), `F : V → ℝ` smooth and `K ⊆ N` compact such that the
critical points of `F|N` in `K` have index `≥ λ₀`: in one slice chart, near a point `z₀` of its
target, there are `r, δ > 0` such that for every continuous linear `a : V → ℝ` with `‖a‖ < δ` the
critical points of `(F + a)|N` in `K` with chart value in `B(z₀, r)` have index `≥ λ₀`
(`exists_perturb_slice`); globally, there is `δ > 0` such that for every such `a` the critical
points of `(F + a)|N` in `K` have index `≥ λ₀` (`lemma_22_4_submanifold`). -/
def A : Prop :=
  type_of% @Morse.exists_perturb_slice.{0,0,0} ∧
  type_of% @Morse.lemma_22_4_submanifold.{0,0,0}

theorem A_holds : A := ⟨@Morse.exists_perturb_slice, @Morse.lemma_22_4_submanifold⟩

/-! Neither `A → B` nor `B → A` is proved; see `V13_11.json`.

* `A ⇒ B` fails genuinely. `A` controls only the perturbations `g = (F + a)|N` of a function
  restricted from the ambient space by a small *linear* form `a` on `V` (the perturbation the
  project uses to produce Morse functions, `Morse.ae_isMorseFunction_add_inner_comp`); `B` (Milnor's
  "`g` with first and second derivatives so close that Lemma 22.4 applies in a coordinate
  neighbourhood") controls *every* smooth `g` whose first and second chart derivatives are
  `ε`-close to those of `f` on a given finite cover of `K` by compact sets in charts. No statement
  about linear perturbations yields that. Moreover `B` is for abstract manifolds (`A` only for
  slice submanifolds; no embedding theorem).
* `B ⇒ A` fails: setting (`A` holds for slice submanifolds with any model `Z` and any normed `V`,
  `B` only speaks of manifolds modelled on `ℝᵐ`). On the Bridge's embedded manifolds
  (`M = ↥N`, model `ℝⁿ`) it is believed to be glue only: cover `K` by finitely many compact sets in
  charts `chartAt`, apply `B` to `f = F|N`, and bound the chart derivatives of `a ∘ incl ∘ e.symm`
  by `‖a‖` times bounds of the first two derivatives of the slice parametrization on the compact
  chart images (as in the project's proof of `exists_perturb_slice`); the blind `IsCritM`, `idxM`
  are the project's `IsCriticalPointM`, `indexM` (definitionally, resp. through
  `bIndex univ = index`). This is carried out below: `B_emb ⇒ A_emb`, where `A_emb` is A's
  global conjunct `lemma_22_4_submanifold` on the Bridge's manifolds (finite-dimensional inner
  product `V`, model `Z = ℝⁿ`). -/

/-! ### Dictionary (blind finite-dimensional vocabulary ↔ project) -/

section Dict

variable {m : ℕ}

/-- The blind index of a continuous bilinear form on the whole space is the project's `index`. -/
theorem bIndex_univ_eq_index (H : Rn m →L[ℝ] Rn m →L[ℝ] ℝ) :
    bIndex (Set.univ : Set (Rn m)) (fun v w => H v w) = (Morse.index H : ℕ∞) := by
  refine le_antisymm (iSup₂_le fun S hS => ?_) ?_
  · exact_mod_cast Morse.finrank_le_index_of_negDef H hS.2.2
  · obtain ⟨W, hW, hneg⟩ := Morse.exists_negDef_finrank_eq_index H
    rw [← hW]
    exact le_iSup₂_of_le (f := fun (S : Submodule ℝ (Rn m))
      (_ : (S : Set (Rn m)) ⊆ Set.univ ∧ FiniteDimensional ℝ S ∧ IsNegDefSub (fun v w => H v w) S) =>
      (Module.finrank ℝ S : ℕ∞)) W ⟨subset_univ _, inferInstance, hneg⟩ le_rfl

/-- The blind index on a manifold is the project's `indexM` (the blind `hessM` is `hessianM`). -/
theorem idxM_eq_indexM {M : Type} [TopologicalSpace M] [ChartedSpace (Rn m) M]
    (f : M → ℝ) (x : M) : idxM (m := m) f x = (Morse.indexM (Rn m) f x : ℕ∞) :=
  bIndex_univ_eq_index _

/-- `pd2` is the Hessian on coordinate vectors, wherever `g` is `C²`. -/
theorem pd2_eq {g : Rn m → ℝ} {x : Rn m} (hg : ContDiffAt ℝ 2 g x) (i j : Fin m) :
    pd2 g i j x = Morse.hessian g x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold pd2 pd
  rw [fderiv_clm_apply h1 (differentiableAt_const _)]
  simp [Morse.hessian]

/-- **Chart derivatives of a linear perturbation**: for `φ : ℝᵐ → V` smooth at `y`, the first and
second partial derivatives of `(F + a) ∘ φ` and `F ∘ φ` at `y` differ by at most `‖a‖` times the
norms of the first and second derivatives of `φ`. -/
theorem pd_pd2_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : V → ℝ}
    (hF : ContDiff ℝ ∞ F) (a : V →L[ℝ] ℝ) {φ : Rn m → V} {y : Rn m} (hφ : ContDiffAt ℝ ∞ φ y) :
    (∀ j, |pd ((fun x => F x + a x) ∘ φ) j y - pd (F ∘ φ) j y| ≤
        ‖a‖ * ‖iteratedFDeriv ℝ 1 φ y‖) ∧
    (∀ i j, |pd2 ((fun x => F x + a x) ∘ φ) i j y - pd2 (F ∘ φ) i j y| ≤
        ‖a‖ * ‖iteratedFDeriv ℝ 2 φ y‖) := by
  have hFφ : ContDiffAt ℝ 2 (F ∘ φ) y := (hF.contDiffAt.comp y hφ).of_le (by norm_cast)
  have haφ : ContDiffAt ℝ 2 (a ∘ φ) y := (a.contDiff.contDiffAt.comp y hφ).of_le (by norm_cast)
  have hsum : (fun x => F x + a x) ∘ φ = F ∘ φ + a ∘ φ := rfl
  obtain ⟨h1, h2⟩ := Morse.fderiv_hessian_add hFφ haφ
  have he : ∀ i : Fin m, ‖(EuclideanSpace.single i (1 : ℝ) : Rn m)‖ = 1 := fun i => by simp
  have hn1 : ‖fderiv ℝ (a ∘ φ) y‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ 1 φ y‖ := by
    rw [← norm_iteratedFDeriv_one, a.iteratedFDeriv_comp_left hφ (by exact_mod_cast le_top)]
    exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
  have hn2 : ‖Morse.hessian (a ∘ φ) y‖ ≤ ‖a‖ * ‖iteratedFDeriv ℝ 2 φ y‖ := by
    rw [Morse.hessian, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv,
      a.iteratedFDeriv_comp_left hφ (by norm_cast)]
    exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
  constructor
  · intro j
    have e : pd ((fun x => F x + a x) ∘ φ) j y - pd (F ∘ φ) j y =
        (fderiv ℝ ((fun x => F x + a x) ∘ φ) y - fderiv ℝ (F ∘ φ) y)
          (EuclideanSpace.single j (1 : ℝ)) := by simp [pd]
    rw [e, hsum, h1]
    have := (fderiv ℝ (a ∘ φ) y).le_opNorm (EuclideanSpace.single j (1 : ℝ))
    rw [he, mul_one, Real.norm_eq_abs] at this
    exact this.trans hn1
  · intro i j
    rw [pd2_eq (hsum ▸ hFφ.add haφ), pd2_eq hFφ]
    have e : Morse.hessian ((fun x => F x + a x) ∘ φ) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) -
        Morse.hessian (F ∘ φ) y (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
        (Morse.hessian ((fun x => F x + a x) ∘ φ) y - Morse.hessian (F ∘ φ) y)
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by simp
    rw [e, hsum, h2]
    have h3 := ((Morse.hessian (a ∘ φ) y) (EuclideanSpace.single i (1 : ℝ))).le_opNorm
      (EuclideanSpace.single j (1 : ℝ))
    have h4 := (Morse.hessian (a ∘ φ) y).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    rw [he, mul_one] at h3 h4
    rw [Real.norm_eq_abs] at h3
    exact (h3.trans h4).trans hn2

/-- A compact set of a manifold modelled on `ℝᵐ` is covered by finitely many chart preimages of
balls whose closures lie in the chart targets. -/
theorem exists_cover {M : Type} [TopologicalSpace M] [ChartedSpace (Rn m) M] {K : Set M}
    (hK : IsCompact K) :
    ∃ (k : ℕ) (c : Fin k → M) (r : Fin k → ℝ), (∀ i, 0 < r i) ∧
      (∀ i, closedBall (chartAt (Rn m) (c i) (c i)) (r i) ⊆ (chartAt (Rn m) (c i)).target) ∧
      K ⊆ ⋃ i, (chartAt (Rn m) (c i)).source ∩
        chartAt (Rn m) (c i) ⁻¹' ball (chartAt (Rn m) (c i) (c i)) (r i) := by
  classical
  have hr : ∀ x : M, ∃ r > 0, closedBall (chartAt (Rn m) x x) r ⊆ (chartAt (Rn m) x).target := by
    intro x
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (chartAt (Rn m) x).open_target _
      (mem_chart_target (Rn m) x)
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose r hr0 hrT using hr
  set O : M → Set M := fun x =>
    (chartAt (Rn m) x).source ∩ chartAt (Rn m) x ⁻¹' ball (chartAt (Rn m) x x) (r x) with hO
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover O
    (fun x => (chartAt (Rn m) x).isOpen_inter_preimage isOpen_ball)
    (fun y _ => mem_iUnion.2 ⟨y, mem_chart_source (Rn m) y, mem_ball_self (hr0 y)⟩)
  refine ⟨t.card, fun i => (t.equivFin.symm i : M), fun i => r (t.equivFin.symm i),
    fun i => hr0 _, fun i => hrT _, fun y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (ht hy)
  have hx' : (t.equivFin.symm (t.equivFin ⟨x, hx⟩) : M) = x := by simp
  refine mem_iUnion.2 ⟨t.equivFin ⟨x, hx⟩, ?_⟩
  show y ∈ O (t.equivFin.symm (t.equivFin ⟨x, hx⟩) : M)
  rw [hx']
  exact hyx

end Dict

/-! ### `B` on the Bridge's embedded manifolds, and `A`'s global conjunct there -/

/-- `B` for `M = ↥N` (the Bridge's smooth manifold, model `ℝⁿ`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ) (N : Set V)
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (f : Bridge.Sub hN → ℝ) (K : Set (Bridge.Sub hN)) (l0 : ℕ),
    ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) ∞ f → IsCompact K →
    (∀ x ∈ K, IsCritM (m := n) f x → (l0 : ℕ∞) ≤ idxM (m := n) f x) →
    ∀ (k : ℕ) (e : Fin k → OpenPartialHomeomorph (Bridge.Sub hN) (Rn n))
      (Kc : Fin k → Set (Bridge.Sub hN)),
      (∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, Rn n) ∞ (Bridge.Sub hN)) →
      (∀ i, IsCompact (Kc i)) → (∀ i, Kc i ⊆ (e i).source) → K ⊆ ⋃ i, Kc i →
      ∃ ε : ℝ, 0 < ε ∧ ∀ g : Bridge.Sub hN → ℝ, ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) ∞ g →
        (∀ i, ∀ y ∈ (e i) '' (Kc i), ∀ a,
          |pd (g ∘ (e i).symm) a y - pd (f ∘ (e i).symm) a y| < ε) →
        (∀ i, ∀ y ∈ (e i) '' (Kc i), ∀ a b,
          |pd2 (g ∘ (e i).symm) a b y - pd2 (f ∘ (e i).symm) a b y| < ε) →
        ∀ x ∈ K, IsCritM (m := n) g x → (l0 : ℕ∞) ≤ idxM (m := n) g x

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ n _ hN => hB n (Bridge.Sub hN)

/-- `A`'s global conjunct `lemma_22_4_submanifold` on the Bridge's manifolds: `V` a
finite-dimensional inner product space, model `Z = ℝⁿ`. -/
def A_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ) (N : Set V)
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) (F : V → ℝ), ContDiff ℝ ∞ F →
    ∀ (K : Set N), IsCompact K → ∀ (l₀ : ℕ),
    (letI := hN.chartedSpace; ∀ q ∈ K, Morse.IsCriticalPointM (Rn n) (F ∘ Subtype.val) q →
      l₀ ≤ Morse.indexM (Rn n) (F ∘ Subtype.val) q) →
    letI := hN.chartedSpace
    ∃ δ > 0, ∀ a : V →L[ℝ] ℝ, ‖a‖ < δ → ∀ q ∈ K,
      Morse.IsCriticalPointM (Rn n) ((fun x => F x + a x) ∘ Subtype.val) q →
      l₀ ≤ Morse.indexM (Rn n) ((fun x => F x + a x) ∘ Subtype.val) q

theorem A_to_A_emb : A → A_emb := fun hA _ _ _ _ _ _ _ _ _ hN _ hF _ hK _ hidx =>
  hA.2 hN hF hK hidx

/-- **On embedded manifolds `B` gives `A`'s Lemma 22.4 for linear perturbations**: cover `K` by
finitely many compact sets in charts, apply `B` to `f = F|N`, and bound the chart derivatives of
the perturbation `a ∘ incl ∘ e.symm` by `‖a‖` times bounds of the first two derivatives of the
chart parametrization `incl ∘ e.symm` on the compact chart images. -/
theorem B_emb_to_A_emb : B_emb → A_emb := by
  intro hB V _ _ _ W _ _ n N hN F hF K hK l0 hidx
  let _ := hN.chartedSpace
  have := hN.isManifold
  set K' : Set (Bridge.Sub hN) := K
  have hK' : IsCompact K' := hK
  have hf : ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) ∞ (F ∘ Bridge.incl hN) := Morse.contMDiff_comp_val hN hF
  obtain ⟨k, c, r, hr0, hrT, hcov⟩ := exists_cover (m := n) hK'
  set e : Fin k → OpenPartialHomeomorph (Bridge.Sub hN) (Rn n) := fun i => chartAt (Rn n) (c i)
    with he_def
  set Kc : Fin k → Set (Bridge.Sub hN) := fun i =>
    K' ∩ (e i).symm '' closedBall (e i (c i)) (r i) with hKc_def
  have hKc : ∀ i, IsCompact (Kc i) := fun i =>
    ((isCompact_closedBall _ _).image_of_continuousOn
      ((e i).continuousOn_symm.mono (hrT i))).inter_left hK'.isClosed
  have hKcs : ∀ i, Kc i ⊆ (e i).source := by
    rintro i y ⟨-, z, hz, rfl⟩
    exact (e i).map_target (hrT i hz)
  have hKcov : K' ⊆ ⋃ i, Kc i := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hy)
    exact mem_iUnion.2 ⟨i, hy, e i y, ball_subset_closedBall hi.2, (e i).left_inv hi.1⟩
  have himg : ∀ i, (e i) '' (Kc i) ⊆ closedBall (e i (c i)) (r i) := by
    rintro i _ ⟨y, ⟨-, z, hz, rfl⟩, rfl⟩
    rwa [(e i).right_inv (hrT i hz)]
  obtain ⟨ε, hε, H⟩ := hB V W n N hN (F ∘ Bridge.incl hN) K' l0 hf hK'
    (fun x hx hc => by
      have h := hidx x hx hc
      exact (show ((l0 : ℕ) : ℕ∞) ≤ (Morse.indexM (Rn n) (F ∘ Subtype.val) x : ℕ∞) by
        exact_mod_cast h).trans_eq (idxM_eq_indexM (m := n) (M := Bridge.Sub hN) _ _).symm)
    k e Kc (fun i => IsManifold.chart_mem_maximalAtlas _) hKc hKcs hKcov
  -- the chart parametrizations and bounds for their first two derivatives
  have hφ : ∀ i, ContDiffOn ℝ ∞ (Bridge.incl hN ∘ (e i).symm) (e i).target := fun i =>
    contMDiffOn_iff_contDiffOn.1 (Bridge.contMDiff_incl.comp_contMDiffOn contMDiffOn_chart_symm)
  have hbd : ∀ i (j : ℕ), ∃ C, ∀ y ∈ closedBall (e i (c i)) (r i),
      ‖iteratedFDeriv ℝ j (Bridge.incl hN ∘ (e i).symm) y‖ ≤ C := by
    intro i j
    have hTo : IsOpen (e i).target := (e i).open_target
    have hcont : ContinuousOn (iteratedFDeriv ℝ j (Bridge.incl hN ∘ (e i).symm)) (e i).target :=
      ((hφ i).continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast le_top)
        hTo.uniqueDiffOn).congr fun u hu => (iteratedFDerivWithin_of_isOpen j hTo hu).symm
    exact (isCompact_closedBall _ _).exists_bound_of_continuousOn (hcont.mono (hrT i))
  choose C₁ hC₁ using fun i => hbd i 1
  choose C₂ hC₂ using fun i => hbd i 2
  set C : ℝ := ∑ i, (|C₁ i| + |C₂ i|) + 1 with hC_def
  have hCi : ∀ i, |C₁ i| ≤ C ∧ |C₂ i| ≤ C := fun i => by
    have h := Finset.single_le_sum (f := fun i => |C₁ i| + |C₂ i|)
      (fun i _ => by positivity) (Finset.mem_univ i)
    constructor <;> linarith [abs_nonneg (C₁ i), abs_nonneg (C₂ i)]
  have hC : 0 < C := by
    have : 0 ≤ ∑ i, (|C₁ i| + |C₂ i|) := Finset.sum_nonneg fun i _ => by positivity
    linarith
  refine ⟨ε / C, div_pos hε hC, fun a ha q hq hcrit => ?_⟩
  have hsmall : ∀ X : ℝ, X ≤ C → ‖a‖ * X < ε := fun X hX => by
    calc ‖a‖ * X ≤ ‖a‖ * C := mul_le_mul_of_nonneg_left hX (norm_nonneg a)
      _ < ε / C * C := mul_lt_mul_of_pos_right ha hC
      _ = ε := div_mul_cancel₀ ε hC.ne'
  have hφy : ∀ i, ∀ y ∈ (e i) '' (Kc i), ContDiffAt ℝ ∞ (Bridge.incl hN ∘ (e i).symm) y :=
    fun i y hy => (hφ i).contDiffAt ((e i).open_target.mem_nhds (hrT i (himg i hy)))
  have hg : ContMDiff 𝓘(ℝ, Rn n) 𝓘(ℝ, ℝ) ∞ ((fun x => F x + a x) ∘ Bridge.incl hN) :=
    Morse.contMDiff_comp_val hN (hF.add a.contDiff)
  have h := H ((fun x => F x + a x) ∘ Bridge.incl hN) hg
    (fun i y hy j => lt_of_le_of_lt ((pd_pd2_bound hF a (hφy i y hy)).1 j)
      (hsmall _ (((hC₁ i y (himg i hy)).trans (le_abs_self _)).trans (hCi i).1)))
    (fun i y hy j j' => lt_of_le_of_lt ((pd_pd2_bound hF a (hφy i y hy)).2 j j')
      (hsmall _ (((hC₂ i y (himg i hy)).trans (le_abs_self _)).trans (hCi i).2)))
    q hq hcrit
  have h2 : ((l0 : ℕ) : ℕ∞) ≤
      (Morse.indexM (Rn n) ((fun x => F x + a x) ∘ Subtype.val) q : ℕ∞) :=
    h.trans_eq (idxM_eq_indexM (m := n) (M := Bridge.Sub hN) _ _)
  exact_mod_cast h2

#rt_check RoundTrip.V13_11.B_emb_to_A_emb [Morse.exists_perturb_slice,
  Morse.lemma_22_4_submanifold]
#rt_overlap RoundTrip.V13_11.B_emb_to_A_emb [Morse.exists_perturb_slice,
  Morse.lemma_22_4_submanifold]

end RoundTrip.V13_11
