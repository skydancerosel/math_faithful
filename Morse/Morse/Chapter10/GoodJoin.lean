import Morse.Chapter10.GoodBalls
import Morse.Chapter10.FullPathDeform

/-!
Milnor, *Morse Theory*, §17, p. 93, and Lemma 17.B of Exposition/Chapter10.md: the good balls
of `Morse/Chapter10/GoodBalls.lean` as a system of minimal joins (`Morse.JoinSystem`) for the
proof of Theorem 17.1.

# Good balls as a join system

## In the embedded setting

* `Morse.exists_isCompact_inter_closedBall`: a slice submanifold is locally compact (small closed
  balls meet `N` in compact sets).
* `Morse.exists_smooth_glue`: smooth gluing of local smooth extensions over a compact set, with a
  parameter (a smooth partition of unity).
* `Morse.exists_goodSet`, `Morse.goodJoin`: **the join system of good balls**: the joins are the
  minimal geodesics `Morse.minGeo`; the good sets are the balls `B(x, r)`, `x ∈ N`, such that the
  balls `B(x, r')`, `r' ≤ 2r`, are good and `N ∩ B̄(x, r)` is compact; on each of them the minimal
  geodesic is the restriction of one smooth function of `(y, z, u)`.

## What Milnor leaves implicit

* Milnor's `ε₁(r)` (p. 93) asks for minimal geodesics "depending differentiably" on their end
  points; for the deformation along minimal geodesics to be continuous for Milnor's metric one
  needs one smooth extension on a whole good set, obtained here by gluing local ones.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace ENNReal

noncomputable section

namespace Morse

/-! ### Gluing local smooth extensions -/

/-- **Smooth gluing with a parameter**: if near every point of a compact set `K ⊆ S` the function
`g` (restricted to `S`) is given by a function smooth in `(y, u)` for `u` near `[0, 1]`, then one
smooth function on `E × (−ε, 1 + ε)` agrees with `g` on `K × (−ε, 1 + ε)` (a smooth partition of
unity in `y`). -/
theorem exists_smooth_glue {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K S : Set E}
    (hK : IsCompact K) (hKS : K ⊆ S) {g : E → ℝ → F}
    (hloc : ∀ x ∈ K, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∃ ε > 0, ∃ Φ : E × ℝ → F,
      ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-ε) (1 + ε)) ∧ ∀ y ∈ S ∩ U, ∀ u, Φ (y, u) = g y u) :
    ∃ ε > 0, ∃ Φ : E × ℝ → F, ContDiffOn ℝ ∞ Φ (univ ×ˢ Ioo (-ε) (1 + ε)) ∧
      ∀ y ∈ K, ∀ u, Φ (y, u) = g y u := by
  classical
  choose! U hU hxU ε hε Φ hΦ hΦg using hloc
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => U x) (fun x => hU x x.2)
    fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxU x hx⟩
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) hK.isClosed
    (fun i : t => U (i : K)) (fun i => hU _ (i : K).2) fun x hx => by
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  have hψs : ∀ i : t, ContDiff ℝ ∞ (ψ i) := fun i => contMDiff_iff_contDiff.1 (ψ i).contMDiff
  -- a common margin
  set ε₀ : ℝ := if h : t.Nonempty then t.inf' h fun i => ε (i : K) else 1 with hε₀
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀]
    split_ifs with h
    · exact (Finset.lt_inf'_iff h).2 fun i _ => hε _ (i : K).2
    · exact one_pos
  have hε₀le : ∀ i ∈ t, ε₀ ≤ ε (i : K) := fun i hi => by
    rw [hε₀, dif_pos ⟨i, hi⟩]
    exact Finset.inf'_le _ hi
  refine ⟨ε₀, hε₀pos, fun w => ∑ i : t, ψ i w.1 • Φ (i : K) w, ?_, fun y hy u => ?_⟩
  · -- each term is smooth on `E × (−ε₀, 1 + ε₀)`
    refine ContDiffOn.sum fun i _ => ?_
    intro w hw
    by_cases hwi : w.1 ∈ U (i : K)
    · have hIoo : w.2 ∈ Ioo (-ε (i : K)) (1 + ε (i : K)) := by
        have := hε₀le i i.2
        exact ⟨by linarith [hw.2.1], by linarith [hw.2.2]⟩
      have hopen : U (i : K) ×ˢ Ioo (-ε (i : K)) (1 + ε (i : K)) ∈ 𝓝 w :=
        ((hU _ (i : K).2).prod isOpen_Ioo).mem_nhds ⟨hwi, hIoo⟩
      exact (((hψs i).comp contDiff_fst).contDiffAt.smul
        ((hΦ _ (i : K).2).contDiffAt hopen)).contDiffWithinAt
    · have hnot : w.1 ∉ tsupport (ψ i) := fun h => hwi (hψ i h)
      have hzero : (fun w : E × ℝ => ψ i w.1 • Φ (i : K) w) =ᶠ[𝓝 w] fun _ => 0 := by
        have : ∀ᶠ w' : E × ℝ in 𝓝 w, w'.1 ∉ tsupport (ψ i) :=
          (continuous_fst.tendsto w).eventually ((isClosed_tsupport _).isOpen_compl.mem_nhds hnot)
        filter_upwards [this] with w' hw'
        rw [image_eq_zero_of_notMem_tsupport hw', zero_smul]
      exact (contDiffAt_const.congr_of_eventuallyEq hzero).contDiffWithinAt
  · -- on `K` the terms add up to `g`
    have hsum := ψ.sum_eq_one hy
    rw [finsum_eq_sum_of_fintype] at hsum
    have hterm : ∀ i : t, ψ i y • Φ (i : K) (y, u) = ψ i y • g y u := by
      intro i
      by_cases h0 : ψ i y = 0
      · simp [h0]
      · have hyU : y ∈ U (i : K) := hψ i (subset_tsupport _ h0)
        rw [hΦg _ (i : K).2 y ⟨hKS hy, hyU⟩]
    simp only [hterm, ← Finset.sum_smul, hsum, one_smul]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ W] in
include hN in
/-- **A submanifold is locally compact**: small closed balls meet `N` in compact sets (`N` is
closed in the domain of a slice chart). -/
theorem exists_isCompact_inter_closedBall {x : V} (hx : x ∈ N) :
    ∃ r > 0, IsCompact (N ∩ closedBall x r) := by
  obtain ⟨σ, hσ⟩ := hN x hx
  obtain ⟨r, hr, hrs⟩ := Metric.isOpen_iff.1 σ.φ.open_source x hσ
  refine ⟨r / 2, by positivity, ?_⟩
  have hsub : closedBall x (r / 2) ⊆ σ.φ.source :=
    (closedBall_subset_ball (by linarith)).trans hrs
  have heq : N ∩ closedBall x (r / 2) = closedBall x (r / 2) ∩ (fun y => (σ.φ y).2) ⁻¹' {0} := by
    ext y
    constructor
    · rintro ⟨hyN, hy⟩
      exact ⟨hy, (σ.slice y (hsub hy)).1 hyN⟩
    · rintro ⟨hy, hy0⟩
      exact ⟨(σ.slice y (hsub hy)).2 hy0, hy⟩
  rw [heq]
  refine (isCompact_closedBall x (r / 2)).of_isClosed_subset ?_ inter_subset_left
  have hc : ContinuousOn (fun y => (σ.φ y).2) (closedBall x (r / 2)) :=
    continuous_snd.comp_continuousOn
      ((Milnor.Problems.sliceChart_contDiffOn σ).continuousOn.mono hsub)
  exact hc.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton

include hN in
/-- **The good sets** used for Theorem 17.1: open balls `B(x, r)`, `x ∈ N`, such that all balls
`B(x, r')`, `r' ≤ 2r`, are good balls and `N ∩ B̄(x, r)` is compact. -/
theorem exists_goodSet {x : V} (hx : x ∈ N) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, r < ε ∧ (∀ r' ≤ 2 * r, IsGoodBall hN (ball x r')) ∧
      IsCompact (N ∩ closedBall x r) := by
  obtain ⟨r₀, hr₀, hgood⟩ := exists_isGoodBall_ball hN hx
  obtain ⟨r₁, hr₁, hcpt⟩ := exists_isCompact_inter_closedBall hN hx
  set r := min (r₀ / 2) (min r₁ (ε / 2)) with hr_def
  have hr : 0 < r := lt_min (by positivity) (lt_min hr₁ (by positivity))
  have hr₁' : r ≤ r₁ := (min_le_right _ _).trans (min_le_left _ _)
  have heq : N ∩ closedBall x r = (N ∩ closedBall x r₁) ∩ closedBall x r := by
    ext y
    simp only [mem_inter_iff]
    exact ⟨fun h => ⟨⟨h.1, closedBall_subset_closedBall hr₁' h.2⟩, h.2⟩,
      fun h => ⟨h.1.1, h.2⟩⟩
  refine ⟨r, hr, lt_of_le_of_lt (min_le_right _ _ |>.trans (min_le_right _ _)) (by linarith),
    fun r' hr' => hgood r' (hr'.trans (by have := min_le_left (r₀ / 2) (min r₁ (ε / 2)); linarith)),
    ?_⟩
  rw [heq]
  exact hcpt.inter_right isClosed_closedBall

/-- **The system of minimal joins in good balls** (Lemma 17.B of the exposition): the joins are
the minimal geodesics `Morse.minGeo`, the good sets the balls of `Morse.exists_goodSet`. -/
def goodJoin : JoinSystem N where
  geo := minGeo hN
  good := {O | ∃ x ∈ N, ∃ r > 0, O = ball x r ∧ (∀ r' ≤ 2 * r, IsGoodBall hN (ball x r')) ∧
    IsCompact (N ∩ closedBall x r)}
  isOpen := by
    rintro O ⟨x, -, r, -, rfl, -⟩
    exact isOpen_ball
  convex := by
    rintro O ⟨x, -, r, hr, rfl, hg, -⟩ y hy z hz u hu
    exact (hg r (by linarith)).convex y hy z hz u hu
  geo_zero := fun _ hy z => minGeo_zero hN hy z
  geo_one := by
    rintro O ⟨x, -, r, hr, rfl, hg, -⟩ y hy z hz
    exact (hg r (by linarith)).minGeo_one hy hz
  geo_self := fun _ hy u => minGeo_self hN hy u
  smooth := by
    rintro O ⟨x, -, r, hr, rfl, hg, hcpt⟩
    have hsub : (N ∩ closedBall x r) ×ˢ (N ∩ closedBall x r) ⊆
        (N ∩ ball x (2 * r)) ×ˢ (N ∩ ball x (2 * r)) := by
      have h1 : N ∩ closedBall x r ⊆ N ∩ ball x (2 * r) :=
        inter_subset_inter_right _ (closedBall_subset_ball (by linarith))
      exact prod_mono h1 h1
    obtain ⟨ε, hε, Φ, hΦ, hΦeq⟩ := exists_smooth_glue (hcpt.prod hcpt) hsub
      (g := fun w u => minGeo hN w.1 w.2 u) fun w hw => by
        obtain ⟨U, hU, hwU, ε, hε, Φ, hΦ, hΦeq⟩ :=
          (hg (2 * r) le_rfl).exists_smooth_minGeo (hsub hw).1 (hsub hw).2
        exact ⟨U, hU, hwU, ε, hε, Φ, hΦ, fun y hy u => hΦeq _ hy.1.1 _ hy.1.2 hy.2 u⟩
    refine ⟨univ, isOpen_univ, subset_univ _, ε, hε, Φ, hΦ.mono subset_rfl,
      fun y hy z hz u _ => hΦeq (y, z) ⟨⟨hy.1, ball_subset_closedBall hy.2⟩,
        ⟨hz.1, ball_subset_closedBall hz.2⟩⟩ u⟩
  lebesgue := by
    intro K hK hKN
    choose r hr _ hgr hcr using fun y : K => exists_goodSet hN (hKN y.2) one_pos
    obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK
      (c := fun y : K => ball (y : V) (r y)) (fun y : K => isOpen_ball)
      fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, mem_ball_self (hr ⟨y, hy⟩)⟩
    refine ⟨δ, hδ, fun x hx => ?_⟩
    obtain ⟨i, hi⟩ := hleb x hx
    exact ⟨ball (i : V) (r i), ⟨i, hKN i.2, r i, hr i, rfl, hgr i, hcr i⟩, hi⟩

theorem goodJoin_geo : (goodJoin hN).geo = minGeo hN := rfl

end Morse
