import Milnor.Chapter7.Gather
import Milnor.Chapter7.Cancel

/-!
# The cancel step: two neighbouring points of opposite sign disappear

If `x₀, z ∈ F.N` have opposite signs and `z` is a neighbour of `x₀` (in the closure of the
component of `x₀` in `M \ (F.N \ {x₀})`), then `F` is framed cobordant to `F` with `x₀` and
`z` removed.  Proof: move `x₀` into a small chart ball around `z` (`exists_reach`), change the
two frames to the standard ones of the cancelling map (`exists_reach` again), and cancel
(`exists_cancel`).  The signed count is unchanged.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} (hMc : IsCompact M) (hne : M.Nonempty)
  {oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m}

/-! ### Counting -/

/-- Removing two points. -/
theorem count_of_remove_two {F F' : FramedSub hM 0 m} {x₀ z : M} (hx₀ : x₀ ∈ F.N) (hz : z ∈ F.N)
    (hxz : x₀ ≠ z) (hN : F'.N = F.N \ {x₀, z})
    (hoff : ∀ i x (hx : x ∈ F.N), x ≠ x₀ → x ≠ z → ∀ hx' : x ∈ F'.N, F'.v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩) :
    count hM oM F' = count hM oM F - sgnAt oM F x₀ - sgnAt oM F z := by
  rw [count_eq_sum, count_eq_sum]
  have hsplit : F.finite_N.toFinset = insert x₀ (insert z F'.finite_N.toFinset) := by
    ext y
    simp only [Set.Finite.mem_toFinset, Finset.mem_insert, hN, Set.mem_sdiff, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · intro hy
      by_cases h1 : y = x₀
      · exact Or.inl h1
      · by_cases h2 : y = z
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨hy, fun h => h.elim h1 h2⟩)
    · rintro (rfl | rfl | ⟨hy, -⟩)
      · exact hx₀
      · exact hz
      · exact hy
  have hx₀n : x₀ ∉ insert z F'.finite_N.toFinset := by
    rw [Finset.mem_insert, Set.Finite.mem_toFinset, hN]
    rintro (h | ⟨-, h⟩)
    · exact hxz h
    · exact h (Or.inl rfl)
  have hzn : z ∉ F'.finite_N.toFinset := by
    rw [Set.Finite.mem_toFinset, hN]
    rintro ⟨-, h⟩
    exact h (Or.inr rfl)
  rw [hsplit, Finset.sum_insert hx₀n, Finset.sum_insert hzn]
  have hsum : ∑ x ∈ F'.finite_N.toFinset, sgnAt oM F' x = ∑ x ∈ F'.finite_N.toFinset, sgnAt oM F x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    have hx' : x ∈ F.N ∧ x ≠ x₀ ∧ x ≠ z := by
      rw [hN] at hx
      exact ⟨hx.1, fun h => hx.2 (Or.inl h), fun h => hx.2 (Or.inr h)⟩
    rw [sgnAt_of_mem oM F' hx, sgnAt_of_mem oM F hx'.1]
    congr 1
    funext i
    exact hoff i x hx'.1 hx'.2.1 hx'.2.2 hx
  rw [hsum]; ring

/-- Moving a point keeps the count. -/
theorem count_of_move {F F' : FramedSub hM 0 m} {x₀ y : M} (hx₀ : x₀ ∈ F.N)
    (hy : y ∉ F.N \ {x₀}) (hN : F'.N = (F.N \ {x₀}) ∪ {y}) (hoff : AgreesOff F F' x₀)
    (hs : ∀ hy' : y ∈ F'.N,
      frameSign hM oM (fun i => F'.v i ⟨y, hy'⟩) y = frameSign hM oM (fun i => F.v i ⟨x₀, hx₀⟩) x₀) :
    count hM oM F' = count hM oM F := by
  rw [count_eq_sum, count_eq_sum]
  have hy' : y ∈ F'.N := by rw [hN]; exact Or.inr rfl
  have hsplitF : F.finite_N.toFinset = insert x₀ (F.finite_N.toFinset.erase x₀) :=
    (Finset.insert_erase (F.finite_N.mem_toFinset.2 hx₀)).symm
  have hsplitF' : F'.finite_N.toFinset = insert y (F.finite_N.toFinset.erase x₀) := by
    ext q
    simp only [Set.Finite.mem_toFinset, hN, mem_union, Set.mem_sdiff, mem_singleton_iff,
      Finset.mem_insert, Finset.mem_erase]
    tauto
  have hyn : y ∉ F.finite_N.toFinset.erase x₀ := by
    simp only [Finset.mem_erase, Set.Finite.mem_toFinset, not_and]
    intro h1 h2
    exact hy ⟨h2, h1⟩
  rw [hsplitF, hsplitF', Finset.sum_insert hyn, Finset.sum_insert (Finset.notMem_erase x₀ _)]
  congr 1
  · rw [sgnAt_of_mem oM F' hy', sgnAt_of_mem oM F hx₀]
    exact hs hy'
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hx
    have hx' : x ∈ F'.N := by rw [hN]; exact Or.inl ⟨hx.2, hx.1⟩
    rw [sgnAt_of_mem oM F' hx', sgnAt_of_mem oM F hx.2]
    congr 1
    funext i
    exact hoff i x hx.2 hx.1 hx'

/-! ### Changing two frames -/

include hMc hne in
/-- If `F₀` differs from `F₁` only in the frames at two points, with the same signs there, then
`F₁` is framed cobordant to `F₀`. -/
theorem framedCobordant_of_frames (hm : 0 < m) {F₁ F₀ : FramedSub hM 0 m} {u z : M}
    (hu : u ∈ F₁.N) (hz : z ∈ F₁.N) (huz : u ≠ z) (hN : F₀.N = F₁.N)
    (hoff : ∀ i x (hx : x ∈ F₁.N), x ≠ u → x ≠ z → ∀ hx' : x ∈ F₀.N, F₀.v i ⟨x, hx'⟩ = F₁.v i ⟨x, hx⟩)
    (hsu : ∀ hu' : u ∈ F₀.N,
      frameSign hM oM (fun i => F₀.v i ⟨u, hu'⟩) u = frameSign hM oM (fun i => F₁.v i ⟨u, hu⟩) u)
    (hsz : ∀ hz' : z ∈ F₀.N,
      frameSign hM oM (fun i => F₀.v i ⟨z, hz'⟩) z = frameSign hM oM (fun i => F₁.v i ⟨z, hz⟩) z) :
    FramedCobordant hM F₁ F₀ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hu₀ : u ∈ F₀.N := hN ▸ hu
  have hz₀ : z ∈ F₀.N := hN ▸ hz
  -- change the frame at `u`
  obtain ⟨F₂, hN₂, hoff₂, hv₂, hcob₂⟩ := exists_reach hMc hne hm oM F₁ hu
    (mem_compl'_self (N := F₁.N) (x := u)) (fun i => F₀.tangent i ⟨u, hu₀⟩) (F₀.indep ⟨u, hu₀⟩)
    (hsu hu₀)
  have hN₂' : F₂.N = F₁.N := by
    rw [hN₂]; ext q
    simp only [mem_union, Set.mem_sdiff, mem_singleton_iff]
    constructor
    · rintro (⟨h, -⟩ | rfl); exact h; exact hu
    · intro h; by_cases hq : q = u
      · exact Or.inr hq
      · exact Or.inl ⟨h, hq⟩
  have hz₂ : z ∈ F₂.N := hN₂' ▸ hz
  -- change the frame at `z`
  obtain ⟨F₃, hN₃, hoff₃, hv₃, hcob₃⟩ := exists_reach hMc hne hm oM F₂ hz₂
    (mem_compl'_self (N := F₂.N) (x := z)) (fun i => F₀.tangent i ⟨z, hz₀⟩) (F₀.indep ⟨z, hz₀⟩)
    (by
      rw [hsz hz₀]
      congr 1
      funext i
      exact (hoff₂ i z hz huz.symm hz₂).symm)
  have hN₃' : F₃.N = F₂.N := by
    rw [hN₃]; ext q
    simp only [mem_union, Set.mem_sdiff, mem_singleton_iff]
    constructor
    · rintro (⟨h, -⟩ | rfl); exact h; exact hz₂
    · intro h; by_cases hq : q = z
      · exact Or.inr hq
      · exact Or.inl ⟨h, hq⟩
  -- `F₃ = F₀`
  have heq : F₃ = F₀ := by
    refine FramedSub.ext' hM (by rw [hN₃', hN₂', hN]) ?_
    intro i x hx₃ hx₀
    by_cases hxz : x = z
    · subst hxz; exact hv₃ i hx₃
    · have hx₂ : x ∈ F₂.N := hN₃' ▸ hx₃
      rw [hoff₃ i x hx₂ hxz hx₃]
      by_cases hxu : x = u
      · subst hxu; exact hv₂ i hx₂
      · have hx₁ : x ∈ F₁.N := hN₂' ▸ hx₂
        rw [hoff₂ i x hx₁ hxu hx₂, hoff i x hx₁ hxu hxz hx₀]
  rw [← heq]
  exact hcob₂.trans hcob₃

/-! ### The cancel step -/

include hMc hne in
/-- **Cancelling a neighbouring pair of opposite sign.** -/
theorem cancel_step (hm : 0 < m) (F : FramedSub hM 0 m) {x₀ z : M} (hx₀ : x₀ ∈ F.N)
    (hz : z ∈ F.N) (hxz : x₀ ≠ z)
    (hsign : frameSign hM oM (fun i => F.v i ⟨z, hz⟩) z =
      -frameSign hM oM (fun i => F.v i ⟨x₀, hx₀⟩) x₀)
    (hnb : z ∈ closure (compl' F.N x₀)) :
    ∃ F'' : FramedSub hM 0 m, F''.N = F.N \ {x₀, z} ∧
      (∀ i x (hx : x ∈ F.N), x ≠ x₀ → x ≠ z → ∀ hx' : x ∈ F''.N, F''.v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩) ∧
      FramedCobordant hM F F'' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI := locallyConnectedSpace_M (hM := hM)
  set s := frameSign hM oM (fun i => F.v i ⟨x₀, hx₀⟩) x₀ with hsdef
  have hs' : s = 1 ∨ s = -1 := frameSign_mem oM F hx₀
  set φ := extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) z with hφdef
  -- a good ball around `z`
  obtain ⟨R, hR, hRt, hpos, hcl, -⟩ :=
    exists_goodBall oM z (P := F.N \ {z}) (F.finite_N.diff) (fun h => h.2 rfl) isOpen_univ
      (mem_univ z)
  -- a point `u` of the component of `x₀`, close to `z`
  obtain ⟨u, huU, huC⟩ := mem_closure_iff.1 hnb (ballU hM z (R / 4)) (isOpen_ballU _ _)
    (x_c_mem_ballU z (by positivity))
  have hsub4 : ballU hM z (R / 4) ⊆ ballU hM z R := fun q hq => by
    rw [mem_ballU] at hq ⊢; exact ⟨hq.1, by linarith [hq.2]⟩
  have huR : u ∈ ballU hM z R := hsub4 huU
  have huNz : u ∉ F.N \ {z} := hcl u (subset_closure huR)
  have hux₀ : u ≠ x₀ := by
    rintro rfl
    exact huNz ⟨hx₀, hxz⟩
  have huz : u ≠ z := by
    rintro rfl
    exact compl'_subset F.N x₀ huC ⟨hz, fun h => hxz h.symm⟩
  have huN : u ∉ F.N := fun h => huNz ⟨h, huz⟩
  -- move `x₀` to `u`
  obtain ⟨v, hvT, hv, hvs⟩ := exists_frame_of_sign hm oM u hs'
  obtain ⟨F₁, hN₁, hoff₁, hv₁, hcob₁⟩ := exists_reach hMc hne hm oM F hx₀ huC hvT hv hvs
  have hu₁ : u ∈ F₁.N := by rw [hN₁]; exact Or.inr rfl
  have hz₁ : z ∈ F₁.N := by rw [hN₁]; exact Or.inl ⟨hz, fun h => hxz h.symm⟩
  have hsu₁ : frameSign hM oM (fun i => F₁.v i ⟨u, hu₁⟩) u = s := by
    have : (fun i => F₁.v i ⟨u, hu₁⟩) = v := funext fun i => hv₁ i hu₁
    rw [this]; exact hvs
  have hsz₁ : frameSign hM oM (fun i => F₁.v i ⟨z, hz₁⟩) z = -s := by
    have : (fun i => F₁.v i ⟨z, hz₁⟩) = fun i => F.v i ⟨z, hz⟩ :=
      funext fun i => hoff₁ i z hz (fun h => hxz h.symm) hz₁
    rw [this]; exact hsign
  have hFU₁ : ∀ x ∈ F₁.N, x ≠ u → x ≠ z → x ∉ closure (ballU hM z R) := by
    intro x hx hxu hxz' hxc
    rw [hN₁] at hx
    rcases hx with ⟨hxF, -⟩ | hxu'
    · exact hcl x hxc ⟨hxF, hxz'⟩
    · exact hxu hxu'
  -- the chart data
  have huU' := mem_ballU.1 huU
  set c := φ z with hcdef
  set p := φ u with hpdef
  have hpc : p ≠ c := fun h => huz (φ.injOn huU'.1 (mem_extChartAt_source z) h)
  have hpc' : 0 < ‖p - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hpc)
  set a : ℝ := ‖p - c‖ / 2 with hadef
  have ha : 0 < a := by positivity
  set w₀ : EuclideanSpace ℝ (Fin m) := ‖p - c‖⁻¹ • (p - c) with hw₀def
  have hw₀ : ‖w₀‖ = 1 := by
    rw [hw₀def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpc'.ne']
  set c₀ : EuclideanSpace ℝ (Fin m) := c + a • w₀ with hc₀def
  have haw : (2 * a) • w₀ = p - c := by
    rw [hadef, hw₀def, smul_smul]
    rw [show 2 * (‖p - c‖ / 2) * ‖p - c‖⁻¹ = 1 by field_simp, one_smul]
  have hφu : φ u = c₀ + a • w₀ := by
    rw [hc₀def, add_assoc, ← add_smul, show a + a = 2 * a by ring, haw]
    simp [hpdef, hcdef]
  have hφz : φ z = c₀ - a • w₀ := by
    rw [hc₀def]; simp [hcdef]
  have hc₀ : ‖c₀ - c‖ < R / 8 := by
    rw [hc₀def, add_sub_cancel_left, norm_smul, hw₀, mul_one, Real.norm_eq_abs, abs_of_pos ha,
      hadef]
    linarith [huU'.2]
  have haR : 8 * a ≤ R := by
    rw [hadef]; linarith [huU'.2]
  have hz_src : z ∈ φ.source := mem_extChartAt_source z
  -- the two orientations of the pair
  have finish : ∀ F₀ F' : FramedSub hM 0 m, F₀.N = F₁.N →
      (∀ i x (hx : x ∈ F₁.N), x ≠ u → x ≠ z → ∀ hx' : x ∈ F₀.N, F₀.v i ⟨x, hx'⟩ = F₁.v i ⟨x, hx⟩) →
      (∀ hu' : u ∈ F₀.N, frameSign hM oM (fun i => F₀.v i ⟨u, hu'⟩) u = s) →
      (∀ hz' : z ∈ F₀.N, frameSign hM oM (fun i => F₀.v i ⟨z, hz'⟩) z = -s) →
      F'.N = F₁.N \ {u, z} →
      (∀ i x (hx : x ∈ F₁.N), x ≠ u → x ≠ z → ∀ hx' : x ∈ F'.N, F'.v i ⟨x, hx'⟩ = F₁.v i ⟨x, hx⟩) →
      FramedCobordant hM F₀ F' →
      ∃ F'' : FramedSub hM 0 m, F''.N = F.N \ {x₀, z} ∧
        (∀ i x (hx : x ∈ F.N), x ≠ x₀ → x ≠ z → ∀ hx' : x ∈ F''.N, F''.v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩) ∧
        FramedCobordant hM F F'' := by
    intro F₀ F' hN₀ hoff₀ hsu₀ hsz₀ hN' hoff' hcob'
    have hcob₀ : FramedCobordant hM F₁ F₀ :=
      framedCobordant_of_frames hMc hne hm hu₁ hz₁ huz hN₀ hoff₀
        (fun hu' => by rw [hsu₀ hu', hsu₁]) (fun hz' => by rw [hsz₀ hz', hsz₁])
    refine ⟨F', ?_, ?_, hcob₁.trans (hcob₀.trans hcob')⟩
    · rw [hN', hN₁]
      ext q
      simp only [Set.mem_sdiff, mem_union, mem_singleton_iff, mem_insert_iff]
      constructor
      · rintro ⟨⟨hq, hqx⟩ | rfl, hq'⟩
        · exact ⟨hq, fun h => h.elim hqx (fun h' => hq' (Or.inr h'))⟩
        · exact absurd (Or.inl rfl) hq'
      · rintro ⟨hq, hq'⟩
        refine ⟨Or.inl ⟨hq, fun h => hq' (Or.inl h)⟩, ?_⟩
        rintro (h | h)
        · exact huN (h ▸ hq)
        · exact hq' (Or.inr h)
    · intro i x hx hxx₀ hxz' hx''
      have hx₁ : x ∈ F₁.N := by rw [hN₁]; exact Or.inl ⟨hx, hxx₀⟩
      have hxu : x ≠ u := fun h => huN (h ▸ hx)
      rw [hoff' i x hx₁ hxu hxz' hx'', hoff₁ i x hx hxx₀ hx₁]
  set ε := orSign (oM.or z) (stdOr m) (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))) with hε
  have hε' : ε = 1 ∨ ε = -1 :=
    orSign_eq_one_or_neg_one finrank_E finrank_E _ _ Function.bijective_id
  by_cases hsε : s = ε
  · obtain ⟨F₀, F', hN₀, hoff₀, hsu₀, hsz₀, hN', hoff', hcob'⟩ :=
      exists_cancel hMc hne hm oM F₁ z hR hRt hpos hc₀ hw₀ ha haR hu₁ hz₁ huU'.1 hz_src hφu hφz hFU₁
    exact finish F₀ F' hN₀ hoff₀ (fun hu' => by rw [hsu₀ hu', hsε]) (fun hz' => by rw [hsz₀ hz', hsε])
      hN' hoff' hcob'
  · have hsε' : s = -ε := by omega
    have hw₀' : ‖-w₀‖ = 1 := by rw [norm_neg, hw₀]
    have hφz' : φ z = c₀ + a • (-w₀) := by rw [hφz, smul_neg, sub_eq_add_neg]
    have hφu' : φ u = c₀ - a • (-w₀) := by rw [hφu, smul_neg, sub_neg_eq_add]
    have hFU₁' : ∀ x ∈ F₁.N, x ≠ z → x ≠ u → x ∉ closure (ballU hM z R) :=
      fun x hx h1 h2 => hFU₁ x hx h2 h1
    obtain ⟨F₀, F', hN₀, hoff₀, hsz₀, hsu₀, hN', hoff', hcob'⟩ :=
      exists_cancel hMc hne hm oM F₁ z hR hRt hpos hc₀ hw₀' ha haR hz₁ hu₁ hz_src huU'.1 hφz' hφu'
        hFU₁'
    refine finish F₀ F' hN₀ (fun i x hx h1 h2 hx' => hoff₀ i x hx h2 h1 hx')
      (fun hu' => by rw [hsu₀ hu', hsε']) (fun hz' => by rw [hsz₀ hz', hsε']; ring) ?_
      (fun i x hx h1 h2 hx' => hoff' i x hx h2 h1 hx') hcob'
    rw [hN', Set.pair_comm]

end Framed

end Milnor
