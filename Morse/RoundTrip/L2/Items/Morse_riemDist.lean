import Morse
import RoundTrip.L2.Blind.Morse_riemDist

/-! Layer-2 check of `Morse.riemDist` against the blind textbook definition: equal for every
`N ⊆ V` and all `p q : V`.

Project: `sInf` of `ofReal (∫ₐᵇ ‖c'‖)` (a Bochner interval integral) over piecewise smooth paths
`c` on any `[a, b]`, `a ≤ b`, in `N` (break points: a finite set `B`). Blind: `⨅` of
`∫⁻_{[0,1]} ofReal ‖c'‖` over piecewise smooth paths on `[0, 1]` (break points: a strictly
increasing subdivision). Glue: a finite break set and a subdivision give each other
(`exists_subdiv`, `isPiecewiseSmooth_of_isPSPath`); the two integrals agree on piecewise smooth
paths (`len_eq`: the speed is integrable, `Ioc =ᵐ Icc`); a path on `[a, b]`, `a < b`, is
reparametrized affinely to `[0, 1]` without changing its length (`pathLength_reparam`), and the
degenerate `a = b` paths (constant, length `0`) are matched by constant paths on `[0, 1]`. -/

namespace RoundTrip.L2.Morse_riemDist

open Set Filter Topology
open scoped ContDiff Manifold


/-! ### Piecewise smooth paths, lengths, and the distance -/

section DistGlue

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {N : Set V}

/-- A blind subdivision gives the project's finite set of break points. -/
theorem isPiecewiseSmooth_of_isPSPath {c : ℝ → V} (h : IsPSPath N c 0 1) :
    Morse.IsPiecewiseSmooth c 0 1 := by
  classical
  obtain ⟨hcont, -, k, τ, h0, h1, hmono, hsm⟩ := h
  refine ⟨zero_le_one, hcont, Finset.univ.image τ, fun s t hs hst ht hB => ?_⟩
  set F := Finset.univ.filter (fun j : Fin (k + 1) => τ j ≤ s) with hF_def
  have hF : F.Nonempty := ⟨0, by simp [F, h0, hs]⟩
  set j := F.max' hF with hj_def
  have hj : τ j ≤ s := (Finset.mem_filter.1 (F.max'_mem hF)).2
  have hjl : j ≠ Fin.last k := fun e => by rw [e, h1] at hj; linarith
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hjl
  have hsi : s < τ i.succ := by
    by_contra hcon
    replace hcon := not_lt.1 hcon
    have h2 : i.succ ≤ j := F.le_max' _ (by simp [F, hcon])
    rw [← hi] at h2
    exact absurd h2 (not_le.2 (Fin.castSucc_lt_succ))
  have hti : t ≤ τ i.succ := by
    by_contra hcon
    replace hcon := not_le.1 hcon
    exact hB (τ i.succ) (by simp) ⟨hsi, hcon⟩
  exact (hsm i).mono (Icc_subset_Icc (hi ▸ hj) hti)

/-- The project's finite set of break points gives a blind subdivision. -/
theorem exists_subdiv {c : ℝ → V} {a b : ℝ} (hab : a < b) (h : Morse.IsPiecewiseSmooth c a b) :
    ∃ (k : ℕ) (τ : Fin (k + 1) → ℝ), τ 0 = a ∧ τ (Fin.last k) = b ∧ StrictMono τ ∧
      ∀ i : Fin k, ContDiffOn ℝ ∞ c (Icc (τ i.castSucc) (τ i.succ)) := by
  classical
  obtain ⟨-, -, B, hB⟩ := h
  set S : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b))) with hS_def
  have hSab : ∀ x ∈ S, a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : a ∈ S := by simp [S]
  have hbS : b ∈ S := by simp [S]
  have hcard : 2 ≤ S.card := by
    have hsub : ({a, b} : Finset ℝ) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact haS
      · exact hbS
    calc 2 = ({a, b} : Finset ℝ).card := (Finset.card_pair hab.ne).symm
      _ ≤ S.card := Finset.card_le_card hsub
  obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 := ⟨S.card - 1, by omega⟩
  set τ := S.orderEmbOfFin hk with hτ_def
  have hmem : ∀ i, τ i ∈ S := fun i => S.orderEmbOfFin_mem hk i
  have hrange : ∀ x ∈ S, ∃ i, τ i = x := fun x hx => by
    have : x ∈ Set.range τ := by rw [hτ_def, Finset.range_orderEmbOfFin]; exact hx
    exact this
  have hmono : StrictMono τ := τ.strictMono
  refine ⟨k, τ, ?_, ?_, hmono, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := hrange a haS
    apply le_antisymm
    · rw [← hj]; exact hmono.monotone (Fin.zero_le j)
    · exact (hSab _ (hmem 0)).1
  · obtain ⟨j, hj⟩ := hrange b hbS
    apply le_antisymm
    · exact (hSab _ (hmem _)).2
    · rw [← hj]; exact hmono.monotone (Fin.le_last j)
  · apply hB _ _ (hSab _ (hmem _)).1 (hmono Fin.castSucc_lt_succ) (hSab _ (hmem _)).2
    intro x hxB hx
    have hxS : x ∈ S := by
      simp only [S, Finset.mem_insert, Finset.mem_filter]
      right; right
      exact ⟨hxB, (hSab _ (hmem _)).1.trans_lt hx.1, hx.2.trans_le (hSab _ (hmem _)).2⟩
    obtain ⟨j, rfl⟩ := hrange x hxS
    have h1 : i.castSucc < j := hmono.lt_iff_lt.1 hx.1
    have h2 : j < i.succ := hmono.lt_iff_lt.1 hx.2
    rw [Fin.lt_def] at h1 h2
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    omega

theorem isPSPath_of_isPiecewiseSmooth {c : ℝ → V} (h : Morse.IsPiecewiseSmooth c 0 1)
    (hN : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ N) : IsPSPath N c 0 1 :=
  ⟨h.2.1, fun t ht => hN t ht, exists_subdiv zero_lt_one h⟩

/-- The blind (lower Lebesgue) length of a piecewise smooth path is the project's length. -/
theorem len_eq {c : ℝ → V} {a b : ℝ} (h : Morse.IsPiecewiseSmooth c a b) :
    len c a b = ENNReal.ofReal (Morse.pathLength c a b) := by
  have hab := h.1
  have hi := h.isAdmissible.integrable
  rw [len, Morse.pathLength, intervalIntegral.integral_of_le hab,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hi)
      (Filter.Eventually.of_forall fun t => norm_nonneg _)]
  exact MeasureTheory.setLIntegral_congr MeasureTheory.Ioc_ae_eq_Icc.symm

/-- Affine reparametrization of a piecewise smooth path on `[a, b]` to `[0, 1]`. -/
theorem isPiecewiseSmooth_reparam {c : ℝ → V} {a b : ℝ} (hab : a < b)
    (h : Morse.IsPiecewiseSmooth c a b) :
    Morse.IsPiecewiseSmooth (fun t => c (a + (b - a) * t)) 0 1 := by
  obtain ⟨-, hcont, B, hB⟩ := h
  have hba : 0 < b - a := sub_pos.2 hab
  have haff : ContDiff ℝ ∞ fun t : ℝ => a + (b - a) * t := by fun_prop
  have hmaps : ∀ {s t : ℝ}, MapsTo (fun t => a + (b - a) * t) (Icc s t)
      (Icc (a + (b - a) * s) (a + (b - a) * t)) := fun hu =>
    ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
  refine ⟨zero_le_one, hcont.comp haff.continuous.continuousOn fun t ht => ⟨?_, ?_⟩,
    B.image (fun x => (x - a) / (b - a)), fun s t hs hst ht hB' => ?_⟩
  · nlinarith [ht.1]
  · nlinarith [ht.2]
  · have hc := hB (a + (b - a) * s) (a + (b - a) * t) (by nlinarith) (by nlinarith) (by nlinarith)
      (fun x hx hxI => hB' ((x - a) / (b - a)) (Finset.mem_image_of_mem _ hx) ⟨by
        rw [lt_div_iff₀ hba]; linarith [hxI.1], by rw [div_lt_iff₀ hba]; linarith [hxI.2]⟩)
    exact hc.comp haff.contDiffOn hmaps

theorem pathLength_reparam (c : ℝ → V) {a b : ℝ} (hab : a ≤ b) :
    Morse.pathLength (fun t => c (a + (b - a) * t)) 0 1 = Morse.pathLength c a b := by
  have hd : ∀ t, deriv (fun t => c (a + (b - a) * t)) t = (b - a) • deriv c (a + (b - a) * t) :=
    fun t => by
      rw [deriv_comp_mul_left (b - a) (fun y => c (a + y)) t, deriv_comp_const_add]
  simp only [Morse.pathLength, hd, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (sub_nonneg.2 hab), intervalIntegral.integral_const_mul]
  have := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
    (fun x => ‖deriv c x‖) (b - a) a
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one, add_sub_cancel] at this
  exact this

/-- **The project's distance is the blind one.** -/
theorem riemDist_eq (p q : V) :
    Morse.riemDist (N := N) p q =
      ⨅ (c : ℝ → V) (_ : IsPSPath N c 0 1 ∧ c 0 = p ∧ c 1 = q), len c 0 1 := by
  apply le_antisymm
  · refine le_iInf₂ fun c ⟨hc, h0, h1⟩ => ?_
    have hps := isPiecewiseSmooth_of_isPSPath hc
    rw [len_eq hps]
    exact sInf_le ⟨c, 0, 1, hps, fun t ht => hc.2.1 ht, h0, h1, rfl⟩
  · refine le_sInf ?_
    rintro L ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
    rcases hc.1.eq_or_lt with hab | hab
    · -- a constant path
      subst hab
      have hp : p ∈ N := ha ▸ hcN a ⟨le_rfl, le_rfl⟩
      have hpq : p = q := ha.symm.trans hb
      have hconst : Morse.IsPiecewiseSmooth (fun _ : ℝ => p) 0 1 :=
        Morse.IsPiecewiseSmooth.of_contDiffOn (s := univ) contDiffOn_const zero_le_one
          (subset_univ _)
      refine (iInf₂_le (fun _ : ℝ => p) ⟨isPSPath_of_isPiecewiseSmooth hconst fun _ _ => hp,
        rfl, hpq⟩).trans ?_
      rw [len_eq hconst]
      simp [Morse.pathLength]
    · have hr := isPiecewiseSmooth_reparam hab hc
      refine (iInf₂_le (fun t => c (a + (b - a) * t)) ⟨isPSPath_of_isPiecewiseSmooth hr
        fun t ht => hcN _ ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩, by simpa using ha,
        by simpa using hb⟩).trans ?_
      rw [len_eq hr, pathLength_reparam c hab.le]

end DistGlue

/-- **Agreement**. -/
theorem agree {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {N : Set V} (p q : V) :
    Morse.riemDist (N := N) p q = T (N := N) p q :=
  riemDist_eq p q

end RoundTrip.L2.Morse_riemDist
