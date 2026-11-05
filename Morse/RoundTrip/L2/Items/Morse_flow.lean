import Morse
import RoundTrip.L2.Blind.Morse_flow

/-! Layer-2 check of `Morse.flow` against the blind textbook definition.

Project: `φ_t(x) = γ(t)` for a chosen integral curve `γ` of `X` through `x` defined on ALL of `ℝ`
(junk `x` if there is none). Blind: `φ_t(x) = c(t)` for a chosen integral curve `c` from `x` on
the closed interval between `0` and `t` (one-sided derivatives at the ends; junk `x` if none).

* `agree_of`: equal when `X` is bounded and globally Lipschitz (`Morse.IsBddLipschitz`, which
  holds for Milnor's `C¹` fields with compact support, `Morse.IsBddLipschitz.of_contDiff`) and `E`
  is complete: the global curve restricts to `[0, t]`, and integral curves on `[0, t]` (or
  `[t, 0]`) are unique (Grönwall, `ODE_solution_unique_of_mem_Icc_right/left`).
* `differ`: for the discontinuous field `X(y) = 1` (`y ≥ 0`), `0` (`y < 0`) on `ℝ` there is no
  global integral curve through `0` (it would have to enter `y < 0` backwards with speed `0`),
  so the project's `φ_1(0)` is the junk `0`, while the blind one is `1` (the curve `s ↦ s` on
  `[0, 1]`, the only one). A junk-value difference outside the textbook's hypotheses. -/

namespace RoundTrip.L2.Morse_flow

open Set Filter Topology

/-- **Agreement** for bounded Lipschitz fields on a Banach space. -/
theorem agree_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (X : E → E) (hX : Morse.IsBddLipschitz X) (t : ℝ) (x : E) : Morse.flow X t x = T X t x := by
  obtain ⟨hγ0, hγ⟩ := hX.flow_spec x
  set γ : ℝ → E := fun s => Morse.flow X s x with hγ_def
  have hex : ∃ c : ℝ → E, c 0 = x ∧ ∀ s ∈ uIcc 0 t, HasDerivWithinAt c (X (c s)) (uIcc 0 t) s :=
    ⟨γ, hγ0, fun s _ => (hγ s).hasDerivWithinAt⟩
  simp only [T, dif_pos hex]
  obtain ⟨hc0, hc⟩ := hex.choose_spec
  set c := hex.choose
  obtain ⟨K, hK⟩ := hX.lipschitz
  have hcont : ContinuousOn c (uIcc 0 t) := fun s hs => (hc s hs).continuousWithinAt
  have hγcont : ContinuousOn γ (uIcc 0 t) := fun s _ => (hγ s).continuousAt.continuousWithinAt
  have heq : EqOn c γ (uIcc 0 t) := by
    rcases le_total 0 t with ht | ht
    · rw [uIcc_of_le ht] at hcont hγcont hc ⊢
      exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => X) (s := fun _ => univ) (K := K)
        (fun _ _ => hK.lipschitzOnWith) hcont
        (fun s hs => (hc s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGE_of_mem hs)) (fun _ _ => mem_univ _) hγcont
        (fun s _ => (hγ s).hasDerivWithinAt) (fun _ _ => mem_univ _) (hc0.trans hγ0.symm)
    · rw [uIcc_of_ge ht] at hcont hγcont hc ⊢
      exact ODE_solution_unique_of_mem_Icc_left (v := fun _ => X) (s := fun _ => univ) (K := K)
        (fun _ _ => hK.lipschitzOnWith) hcont
        (fun s hs => (hc s (Ioc_subset_Icc_self hs)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem hs)) (fun _ _ => mem_univ _) hγcont
        (fun s _ => (hγ s).hasDerivWithinAt) (fun _ _ => mem_univ _) (hc0.trans hγ0.symm)
  exact (heq right_mem_uIcc).symm

/-- The field of the counterexample: `1` on `[0, ∞)`, `0` on `(-∞, 0)`. -/
noncomputable def Xc : ℝ → ℝ := fun y => if 0 ≤ y then 1 else 0

theorem no_global_curve :
    ¬ ∃ γ : ℝ → ℝ, γ 0 = 0 ∧ IsIntegralCurve γ (fun _ => Xc) := by
  rintro ⟨γ, hγ0, hγ⟩
  have h0 : HasDerivAt γ 1 0 := by simpa [Xc, hγ0] using hγ 0
  -- just before `0`, `γ < 0`
  have hslope := (hasDerivAt_iff_tendsto_slope.1 h0).mono_left
    (nhdsWithin_mono _ fun s (hs : s < 0) => ne_of_lt hs)
  have hev : ∀ᶠ s in 𝓝[<] (0 : ℝ), 0 < slope γ 0 s :=
    hslope.eventually_const_lt one_pos
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1
    (hev.and self_mem_nhdsWithin)
  have hneg : ∀ s ∈ Ioo l 0, γ s < 0 := fun s hs => by
    obtain ⟨h1, h2⟩ := hsub hs
    rw [slope_def_field, hγ0, sub_zero, sub_zero] at h1
    have h2' : s < 0 := h2
    exact (div_pos_iff.1 h1).resolve_left (fun h => absurd h.2 (not_lt.2 h2'.le)) |>.1
  -- on `[l/2, 0]` the speed is `0`, so `γ (l/2) = γ 0 = 0`
  have hl' : l / 2 < 0 := by linarith [show l < 0 from hl]
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope γ (fun s => Xc (γ s)) hl'
    (fun s _ => (hγ s).continuousAt.continuousWithinAt) (fun s _ => hγ s)
  have hξneg : γ ξ < 0 := hneg ξ ⟨by linarith [hξ.1, show l < 0 from hl], hξ.2⟩
  have hX0 : Xc (γ ξ) = 0 := by simp [Xc, not_le.2 hξneg]
  rw [hX0, hγ0, eq_comm, div_eq_zero_iff] at hξeq
  rcases hξeq with h | h
  · have := hneg (l / 2) ⟨by linarith [show l < 0 from hl], hl'⟩
    linarith
  · linarith

theorem T_Xc : T Xc 1 0 = 1 := by
  have hex : ∃ c : ℝ → ℝ, c 0 = 0 ∧ ∀ s ∈ uIcc 0 1, HasDerivWithinAt c (Xc (c s)) (uIcc 0 1) s :=
    ⟨fun s => s, rfl, fun s hs => by
      rw [uIcc_of_le zero_le_one] at hs
      simpa [Xc, hs.1] using (hasDerivAt_id' s).hasDerivWithinAt⟩
  simp only [T, dif_pos hex]
  obtain ⟨hc0, hc⟩ := hex.choose_spec
  set c := hex.choose
  rw [uIcc_of_le zero_le_one] at hc
  have hcont : ContinuousOn c (Icc 0 1) := fun s hs => (hc s hs).continuousWithinAt
  have hint : interior (Icc (0 : ℝ) 1) = Ioo 0 1 := interior_Icc
  have hmono : MonotoneOn c (Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont
      (f' := fun s => Xc (c s)) (fun s hs => ?_) (fun s _ => ?_)
    · rw [hint] at hs ⊢
      exact (hc s (Ioo_subset_Icc_self hs)).mono Ioo_subset_Icc_self
    · simp only [Xc]; split_ifs <;> norm_num
  have hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ c s := fun s hs =>
    hc0 ▸ hmono ⟨le_rfl, zero_le_one⟩ hs hs.1
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun s => c s - s) (fun _ => 0) zero_lt_one
    (hcont.sub continuousOn_id) (fun s hs => by
      have h1 : HasDerivAt (fun s => c s - s) (Xc (c s) - 1) s :=
        ((hc s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)).sub
          (hasDerivAt_id' s)
      convert h1 using 1
      simp [Xc, hpos s (Ioo_subset_Icc_self hs)])
  rw [hc0] at hξeq
  simp only [sub_zero, div_one] at hξeq
  linarith

/-- **They differ** for a discontinuous field (outside the textbook's hypotheses). -/
theorem differ : ∃ (X : ℝ → ℝ) (t x : ℝ), Morse.flow X t x ≠ T X t x := by
  refine ⟨Xc, 1, 0, ?_⟩
  rw [T_Xc, Morse.flow, dif_neg no_global_curve]
  norm_num

end RoundTrip.L2.Morse_flow
