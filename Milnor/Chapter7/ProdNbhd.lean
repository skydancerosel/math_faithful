import Milnor.Chapter7.ThmA

/-!
# The product neighbourhood theorem, abstract part (Milnor §7, pp. 46–47)

Let `G : N × ℝᵖ → X` be a smooth map of manifolds (`dim N = n`, `dim X = n + p`) whose
derivative at every point `(x, 0)` is bijective, and which is injective on `N × {0}`.  Then, by
the inverse function theorem and a compactness argument, `G` is injective on `N × B_ε` for some
`ε > 0`, its image is open, and its inverse is smooth.  (This is applied to
`G(x, t) = r(x + ∑ tᵢ vᵢ(x))`, `r` the nearest-point retraction, in `ProdNbhdM.lean`.)

The compactness argument allows a compact set `K ⊆ N` outside of which injectivity is already
known (for the cobordism case, where `N` is not compact but has product ends).
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace PN

variable {n p : ℕ} {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX} [IX.Boundaryless]
  [CompleteSpace EX]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N] [FirstCountableTopology N]
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  [IsManifold IX ∞ X] [T2Space X]
  {G : N × EuclideanSpace ℝ (Fin p) → X}
  (hG : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
    IX ∞ G)

/-- The chart representative of `G` at `q₀`. -/
def wr (n : ℕ) (IX : ModelWithCorners ℝ EX HX) [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [ChartedSpace HX X]
    (G : N × EuclideanSpace ℝ (Fin p) → X) (q₀ : N × EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p) → EX :=
  extChartAt IX (G q₀) ∘ G ∘
    (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q₀).symm

/-- The chart point. -/
def cpt (n : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] (q₀ : N × EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p) :=
  extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q₀ q₀

include hG in
theorem contDiffAt_wr (q₀ : N × EuclideanSpace ℝ (Fin p)) : ContDiffAt ℝ ∞ (wr n IX G q₀) (cpt n q₀) := by
  have h := (contMDiffAt_iff.1 (hG q₀)).2
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
  exact h

include hG in
theorem hasFDerivAt_wr (q₀ : N × EuclideanSpace ℝ (Fin p)) :
    HasFDerivAt (wr n IX G q₀) (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q₀) (cpt n q₀) := by
  have h := ((hG q₀).mdifferentiableAt (by simp)).hasMFDerivAt.2
  rw [ModelWithCorners.range_eq_univ] at h
  exact hasFDerivWithinAt_univ.1 h

/-- The derivative as a continuous linear equivalence. -/
def De (G : N × EuclideanSpace ℝ (Fin p) → X) (q₀ : N × EuclideanSpace ℝ (Fin p))
    (hbij : Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q₀)) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p)) ≃L[ℝ] EX :=
  ContinuousLinearEquiv.ofBijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
    𝓘(ℝ, EuclideanSpace ℝ (Fin p))) IX G q₀)
    (LinearMap.ker_eq_bot.2 hbij.1) (LinearMap.range_eq_top.2 hbij.2)

theorem De_coe (G : N × EuclideanSpace ℝ (Fin p) → X) (q₀ : N × EuclideanSpace ℝ (Fin p))
    (hbij : Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q₀)) :
    ((De G q₀ hbij).toContinuousLinearMap) =
      mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
        IX G q₀ :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

include hG in
theorem hasFDerivAt_wr' (q₀ : N × EuclideanSpace ℝ (Fin p)) 
    (hbij : Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q₀)) :
    HasFDerivAt (wr n IX G q₀) (De G q₀ hbij).toContinuousLinearMap (cpt n q₀) := by
  rw [De_coe]; exact hasFDerivAt_wr hG q₀

include hG in
/-- The local inverse of the chart representative. -/
def wrInv (q₀ : N × EuclideanSpace ℝ (Fin p))
    (hbij : Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q₀)) :
    EX → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin p) :=
  (contDiffAt_wr hG q₀).localInverse (hasFDerivAt_wr' hG q₀ hbij) (by simp)

include hG in
theorem eventually_wrInv_wr (q₀ : N × EuclideanSpace ℝ (Fin p)) 
    (hbij : Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q₀)) :
    ∀ᶠ c in 𝓝 (cpt n q₀), wrInv hG q₀ hbij (wr n IX G q₀ c) = c :=
  ((contDiffAt_wr hG q₀).hasStrictFDerivAt' (hasFDerivAt_wr' hG q₀ hbij)
    (by simp)).eventually_left_inverse

include hG in
theorem eventually_wr_wrInv (q₀ : N × EuclideanSpace ℝ (Fin p)) 
    (hbij : Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q₀)) :
    ∀ᶠ y in 𝓝 (wr n IX G q₀ (cpt n q₀)), wr n IX G q₀ (wrInv hG q₀ hbij y) = y :=
  ((contDiffAt_wr hG q₀).hasStrictFDerivAt' (hasFDerivAt_wr' hG q₀ hbij)
    (by simp)).eventually_right_inverse

include hG in
theorem contDiffAt_wrInv (q₀ : N × EuclideanSpace ℝ (Fin p)) 
    (hbij : Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q₀)) :
    ContDiffAt ℝ ∞ (wrInv hG q₀ hbij) (wr n IX G q₀ (cpt n q₀)) :=
  (contDiffAt_wr hG q₀).to_localInverse (hasFDerivAt_wr' hG q₀ hbij) (by simp)

theorem wr_cpt (q₀ : N × EuclideanSpace ℝ (Fin p)) :
    wr n IX G q₀ (cpt n q₀) = extChartAt IX (G q₀) (G q₀) := by
  simp only [wr, cpt, Function.comp]
  rw [(extChartAt _ q₀).left_inv (mem_extChartAt_source q₀)]

theorem wr_apply {q₀ q : N × EuclideanSpace ℝ (Fin p)}
    (hq : q ∈ (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q₀).source) :
    wr n IX G q₀ (extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q₀ q) =
      extChartAt IX (G q₀) (G q) := by
  simp only [wr, Function.comp]
  rw [(extChartAt _ q₀).left_inv hq]

include hG in
/-- **Local injectivity** at a point where the derivative is bijective. -/
theorem exists_injOn_nhds (q₀ : N × EuclideanSpace ℝ (Fin p)) 
    (hbij : Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p)))
      IX G q₀)) :
    ∃ U ∈ 𝓝 q₀, InjOn G U := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_wrInv_wr hG q₀ hbij)
  set e := extChartAt (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin p))) q₀
    with he
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (cpt n q₀) δ, ?_, ?_⟩
  · exact Filter.inter_mem (extChartAt_source_mem_nhds q₀)
      ((continuousAt_extChartAt q₀).preimage_mem_nhds (Metric.ball_mem_nhds _ hδ))
  · intro q hq q' hq' hqq'
    have h1 := hball (mem_ball.1 hq.2)
    have h2 := hball (mem_ball.1 hq'.2)
    rw [wr_apply hq.1] at h1
    rw [wr_apply hq'.1] at h2
    rw [hqq'] at h1
    have h3 : e q = e q' := by rw [← h1, ← h2]
    exact e.injOn hq.1 hq'.1 h3

include hG in
/-- **A uniform injectivity radius.**  `K ⊆ N` compact; outside `K` injectivity is assumed. -/
theorem exists_injOn (K : Set N) (hK : IsCompact K) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hbij : ∀ x ∈ K, Bijective (mfd (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin p))) IX G (x, 0)))
    (hinj0 : ∀ x x', G (x, 0) = G (x', 0) → x = x')
    (hout : ∀ q q' : N × EuclideanSpace ℝ (Fin p), ‖q.2‖ < ε₀ → ‖q'.2‖ < ε₀ → q.1 ∉ K →
      G q = G q' → q = q') :
    ∃ ε, 0 < ε ∧ ε ≤ ε₀ ∧ ∀ q q' : N × EuclideanSpace ℝ (Fin p), ‖q.2‖ < ε → ‖q'.2‖ < ε →
      G q = G q' → q = q' := by
  by_contra hcon
  push_neg at hcon
  -- sequences of bad pairs
  have hseq : ∀ k : ℕ, ∃ q q' : N × EuclideanSpace ℝ (Fin p),
      ‖q.2‖ < min ε₀ (1 / ((k : ℝ) + 1)) ∧
      ‖q'.2‖ < min ε₀ (1 / ((k : ℝ) + 1)) ∧ G q = G q' ∧ q ≠ q' := fun k =>
    hcon (min ε₀ (1 / ((k : ℝ) + 1))) (lt_min hε₀ (Nat.one_div_pos_of_nat (α := ℝ) (n := k)))
      (min_le_left _ _)
  choose q q' hq hq' hGq hne using hseq
  have hmin_le : ∀ k : ℕ, min ε₀ (1 / ((k : ℝ) + 1)) ≤ ε₀ := fun k => min_le_left _ _
  have hK1 : ∀ k, (q k).1 ∈ K := fun k => by
    by_contra h
    exact hne k (hout _ _ ((hq k).trans_le (hmin_le k)) ((hq' k).trans_le (hmin_le k)) h (hGq k))
  have hK2 : ∀ k, (q' k).1 ∈ K := fun k => by
    by_contra h
    exact hne k (hout _ _ ((hq' k).trans_le (hmin_le k)) ((hq k).trans_le (hmin_le k)) h
      (hGq k).symm).symm
  -- compactness
  set C : Set ((N × EuclideanSpace ℝ (Fin p)) × (N × EuclideanSpace ℝ (Fin p))) :=
    (K ×ˢ closedBall 0 ε₀) ×ˢ (K ×ˢ closedBall 0 ε₀) with hC
  have hCc : IsCompact C := (hK.prod (isCompact_closedBall _ _)).prod (hK.prod (isCompact_closedBall _ _))
  have hmem : ∀ k, (q k, q' k) ∈ C := fun k =>
    ⟨⟨hK1 k, mem_closedBall_zero_iff.2 ((hq k).trans_le (hmin_le k)).le⟩,
     ⟨hK2 k, mem_closedBall_zero_iff.2 ((hq' k).trans_le (hmin_le k)).le⟩⟩
  obtain ⟨⟨l, l'⟩, hlC, φ, hφ, hlim⟩ := hCc.tendsto_subseq hmem
  have hlim1 : Tendsto (fun k => q (φ k)) atTop (𝓝 l) := (continuous_fst.tendsto _).comp hlim
  have hlim2 : Tendsto (fun k => q' (φ k)) atTop (𝓝 l') := (continuous_snd.tendsto _).comp hlim
  -- the second coordinates tend to zero
  have hzero : ∀ (s : ℕ → N × EuclideanSpace ℝ (Fin p)) (m : N × EuclideanSpace ℝ (Fin p)),
      Tendsto (fun k => s (φ k)) atTop (𝓝 m) →
      (∀ k, ‖(s k).2‖ < min ε₀ (1 / ((k : ℝ) + 1))) → m.2 = 0 := by
    intro s m hs hb
    have h1 : Tendsto (fun k => ‖(s (φ k)).2‖) atTop (𝓝 ‖m.2‖) :=
      (continuous_norm.tendsto _).comp ((continuous_snd.tendsto _).comp hs)
    have h2 : Tendsto (fun k => ‖(s (φ k)).2‖) atTop (𝓝 0) := by
      have h3 : Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) := by
        have h4 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        exact h4.comp hφ.tendsto_atTop
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h3
      exact ((hb (φ k)).trans_le (min_le_right _ _)).le
    have := tendsto_nhds_unique h1 h2
    exact norm_eq_zero.1 this
  have hl2 : l.2 = 0 := hzero q l hlim1 hq
  have hl'2 : l'.2 = 0 := hzero q' l' hlim2 hq'
  -- the limits coincide
  have hGl : G l = G l' := by
    have h1 : Tendsto (fun k => G (q (φ k))) atTop (𝓝 (G l)) := (hG.continuous.tendsto _).comp hlim1
    have h2 : Tendsto (fun k => G (q (φ k))) atTop (𝓝 (G l')) := by
      have := (hG.continuous.tendsto _).comp hlim2
      refine this.congr fun k => ?_
      exact (hGq (φ k)).symm
    exact tendsto_nhds_unique h1 h2
  have h1 : (l.1, (0 : EuclideanSpace ℝ (Fin p))) = l := Prod.ext rfl hl2.symm
  have h2 : (l'.1, (0 : EuclideanSpace ℝ (Fin p))) = l' := Prod.ext rfl hl'2.symm
  have hll' : l = l' := by
    have hGl' : G (l.1, 0) = G (l'.1, 0) := by rw [h1, h2]; exact hGl
    exact Prod.ext (hinj0 _ _ hGl') (hl2.trans hl'2.symm)
  -- local injectivity at `l`
  have hlK : l.1 ∈ K := hlC.1.1
  obtain ⟨U, hU, hUinj⟩ := exists_injOn_nhds hG l (by rw [← h1]; exact hbij l.1 hlK)
  have hev1 := hlim1.eventually hU
  have hU' : U ∈ 𝓝 l' := hll' ▸ hU
  have hev2 : ∀ᶠ k in atTop, q' (φ k) ∈ U := hlim2.eventually hU'
  obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
  exact hne (φ k) (hUinj hk1 hk2 (hGq (φ k)))

end PN

end Milnor
