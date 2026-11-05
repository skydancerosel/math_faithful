import Milnor.Chapter7.Glue
import Milnor.Chapter7.Neighbour

/-!
# The segment property of chart balls, and the neighbour lemma for `M`

For a finite set `N ⊆ M` and `x ∈ N`, a small chart ball `J` around `x` meets `N` only in `x`,
and `J \ {x}` lies in the connected component of `x` in `M \ (N \ {x})`: every point of the ball
is joined to `x` by a segment in the chart.  Hence the neighbour lemma applies to `M`.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M}

include hM in
theorem locallyConnectedSpace_M : letI := hM.chartedSpace; LocallyConnectedSpace M :=
  letI := hM.chartedSpace
  ChartedSpace.locallyConnectedSpace (H := EuclideanSpace ℝ (Fin m)) (M := M)

/-- Small chart balls lie inside any neighbourhood of the centre, with the closed ball of the
same radius inside the chart target. -/
theorem exists_ballU_subset (x : M) {S : Set M} (hS : letI := hM.chartedSpace; S ∈ 𝓝 x) :
    letI := hM.chartedSpace
    ∃ r : ℝ, 0 < r ∧
      closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x x) r ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x).target ∧
      ballU hM x r ⊆ S := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  set φ := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x with hφ
  have h1 : φ.target ∈ 𝓝 (φ x) := (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have h2 : φ.symm ⁻¹' S ∈ 𝓝 (φ x) := by
    have hc : ContinuousAt φ.symm (φ x) := continuousAt_extChartAt_symm x
    have hx : φ.symm (φ x) = x := extChartAt_to_inv x
    apply hc.preimage_mem_nhds
    rw [hx]; exact hS
  have h3 := (eventually_closedBall_subset h1).and (eventually_closedBall_subset h2)
  obtain ⟨r, hr, hr1, hr2⟩ := h3.exists_gt
  refine ⟨r, hr, hr1, fun z hz => ?_⟩
  rw [mem_ballU] at hz
  have hzb : φ z ∈ closedBall (φ x) r := by
    rw [mem_closedBall, dist_eq_norm]; exact hz.2.le
  have := hr2 hzb
  rw [mem_preimage, φ.left_inv hz.1] at this
  exact this

/-- **The segment property.** If the chart ball around `x ∈ N` meets `N` only in `x`, every
other point of the ball lies in the component of `x` in `M \ (N \ {x})`. -/
theorem ballU_diff_subset_compl' (x : M) {N : Set M} {r : ℝ}
    (hrt : letI := hM.chartedSpace;
      closedBall (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x x) r ⊆
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x).target)
    (hJN : ballU hM x r ∩ N ⊆ {x}) :
    ballU hM x r \ {x} ⊆ compl' N x := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  rintro y ⟨hyU, hyx⟩
  have hyx' : y ≠ x := hyx
  set φ := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) x with hφ
  set c := φ x with hc
  set u := φ y with hu
  have hyU' := mem_ballU.1 hyU
  have huc : u ≠ c := by
    intro h
    exact hyx' (φ.injOn hyU'.1 (mem_extChartAt_source x) h)
  -- the segment from `c` to `u`
  set g : ℝ → M := fun s => φ.symm (c + s • (u - c)) with hg
  have hgmem : ∀ s ∈ Icc (0 : ℝ) 1, c + s • (u - c) ∈ closedBall c r := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs.1]
    calc s * ‖u - c‖ ≤ 1 * ‖u - c‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
      _ = ‖u - c‖ := one_mul _
      _ ≤ r := by
        have := hyU'.2; rw [← hu, ← hc] at this; exact this.le
  have hgball : ∀ s ∈ Ioc (0 : ℝ) 1, g s ∈ ballU hM x r \ {x} := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    have hmem := hgmem s hs'
    have htgt : c + s • (u - c) ∈ φ.target := hrt hmem
    refine ⟨?_, ?_⟩
    · rw [mem_ballU]
      refine ⟨φ.map_target htgt, ?_⟩
      show ‖φ (φ.symm (c + s • (u - c))) - c‖ < r
      rw [φ.right_inv htgt, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
      calc s * ‖u - c‖ ≤ 1 * ‖u - c‖ := mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
        _ = ‖u - c‖ := one_mul _
        _ < r := by
          have := hyU'.2; rw [← hu, ← hc] at this; exact this
    · intro h
      have h' : g s = x := h
      have := congrArg φ h'
      simp only [hg] at this
      rw [φ.right_inv htgt] at this
      have h2 : s • (u - c) = 0 := by
        have := this; rw [← hc] at this
        exact add_eq_left.1 this
      rcases smul_eq_zero.1 h2 with h3 | h3
      · exact hs.1.ne' h3
      · exact huc (sub_eq_zero.1 h3)
  set P : Set M := g '' Ioc 0 1 with hP
  have hPsub : P ⊆ (N \ {x})ᶜ := by
    rintro _ ⟨s, hs, rfl⟩ ⟨hN, hne⟩
    have := hgball s hs
    exact this.2 (hJN ⟨this.1, hN⟩)
  have hgcont : ContinuousOn g (Ioc 0 1) := by
    refine ContinuousOn.comp (f := fun s : ℝ => c + s • (u - c)) (g := φ.symm)
      (continuousOn_extChartAt_symm x) ?_ ?_
    · exact (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    · intro s hs
      exact hrt (hgmem s ⟨hs.1.le, hs.2⟩)
  have hPc : IsPreconnected P := isPreconnected_Ioc.image g hgcont
  -- `x` is in the closure of the segment
  have hxcl : x ∈ closure P := by
    have hg0 : g 0 = x := by
      simp only [hg, zero_smul, add_zero]; exact extChartAt_to_inv x
    have hgc : ContinuousAt g 0 := by
      have h0 : c + (0 : ℝ) • (u - c) ∈ φ.target := by
        rw [zero_smul, add_zero]; exact mem_extChartAt_target x
      refine ContinuousAt.comp (f := fun s : ℝ => c + s • (u - c)) (g := φ.symm) ?_ ?_
      · rw [zero_smul, add_zero]; exact continuousAt_extChartAt_symm x
      · exact (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    have ht : Tendsto g (𝓝[>] 0) (𝓝 x) := by
      rw [← hg0]; exact hgc.tendsto.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
    exact ⟨s, hs, rfl⟩
  have hQc : IsPreconnected (P ∪ {x}) :=
    hPc.subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.2 hxcl))
  have hQsub : P ∪ {x} ⊆ (N \ {x})ᶜ := by
    refine union_subset hPsub ?_
    rintro _ rfl ⟨-, h⟩
    exact h rfl
  have hQ : P ∪ {x} ⊆ compl' N x :=
    hQc.subset_connectedComponentIn (Or.inr rfl) hQsub
  have hy1 : y = g 1 := by
    simp only [hg, one_smul, add_sub_cancel]
    exact (φ.left_inv hyU'.1).symm
  rw [hy1]
  exact hQ (Or.inl ⟨1, ⟨zero_lt_one, le_rfl⟩, rfl⟩)

include hM in
/-- Every point of a finite set has a chart ball with the segment property. -/
theorem exists_segment_ball {N : Set M} (hN : N.Finite) (x : M) :
    ∃ J : Set M, IsOpen J ∧ x ∈ J ∧ J ∩ N ⊆ {x} ∧ J \ {x} ⊆ compl' N x := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hS : (N \ {x})ᶜ ∈ 𝓝 x :=
    (hN.diff.isClosed).isOpen_compl.mem_nhds (by simp)
  obtain ⟨r, hr, hrt, hsub⟩ := exists_ballU_subset x hS
  have hJN : ballU hM x r ∩ N ⊆ {x} := by
    rintro z ⟨hz, hzN⟩
    have := hsub hz
    by_contra h
    exact this ⟨hzN, h⟩
  exact ⟨ballU hM x r, isOpen_ballU x r, x_c_mem_ballU x hr, hJN,
    ballU_diff_subset_compl' x hrt hJN⟩

include hM in
/-- **The neighbour lemma for `M`.** -/
theorem exists_neighbour_M (hconn : letI := hM.chartedSpace; ConnectedSpace M) {N : Set M}
    (hNf : N.Finite) {B : Set M} (hBN : B ⊆ N) (hB : B.Nonempty) (hB' : (N \ B).Nonempty) :
    ∃ x ∈ B, ∃ z ∈ N \ B, z ∈ closure (compl' N x) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI := locallyConnectedSpace_M (hM := hM)
  haveI := hconn
  exact exists_neighbour hNf (fun x _ => exists_segment_ball (hM := hM) hNf x) hBN hB hB'

end Framed

end Milnor
