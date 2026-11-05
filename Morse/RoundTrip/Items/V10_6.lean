import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_6
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval

namespace RoundTrip.V10_6

/-- The project's statement (universes instantiated at `0`): smoothness on a slice submanifold
from local smooth ambient representatives (`contMDiffAt_of_locally_eq`), and for
`B : Morse.BrokenSetup hN p q c m`: near every `y₀ ∈ B.nodes`, `E' = B.energy'` is the
restriction of a smooth function on an open set of `V^m` (`exists_smooth_energy'`); `E'` is
smooth on the slice submanifold `N^m ∩ O` for open `O` with `N^m ∩ O ⊆ B.nodes`
(`contMDiff_energy'`); `{y ∈ B.nodes | E'(y) ≤ a}` is compact for `a < c`
(`isCompact_sublevel`). -/
def A : Prop :=
  type_of% @Morse.contMDiffAt_of_locally_eq.{0,0,0} ∧
    type_of% @Morse.BrokenSetup.exists_smooth_energy'.{0,0,0} ∧
    type_of% @Morse.BrokenSetup.contMDiff_energy'.{0,0,0} ∧
    type_of% @Morse.BrokenSetup.isCompact_sublevel.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.contMDiffAt_of_locally_eq, @Morse.BrokenSetup.exists_smooth_energy',
    @Morse.BrokenSetup.contMDiff_energy', @Morse.BrokenSetup.isCompact_sublevel⟩


/-! Neither `A → B` nor `B → A` is proved (see `V10_6.json`).

* `A → B` fails genuinely: B quantifies over abstract connected complete Riemannian
  `ℝⁿ`-manifolds; A only concerns slice submanifolds `N ⊆ V` with the induced metric, and only
  subdivisions carrying a `Morse.BrokenSetup`.
* `B → A` fails genuinely: A's `contMDiffAt_of_locally_eq` (a general lemma on slice
  submanifolds) is not in B; A's smoothness of `E'` is via smooth *ambient* representatives on open
  sets of `V^m` (`exists_smooth_energy'`) and on the slice submanifold `N^m ∩ O`
  (`contMDiff_energy'`), B's via a function smooth for the abstract product structure on the image
  of `B` only (extending it to `V^m` needs an extension argument); A holds for every
  `BrokenSetup`, whose subdivisions need not satisfy B's hypotheses.

## The embedded special case

`B_emb` is B for `M = ↥N` with the induced connection (`B_to_B_emb`). Dictionary (namespace
`Emb`) as in `Items/V10_5.lean` (Milnor's metric, normalized `Ω` vs `Morse.PathSp`, blind broken
geodesics vs `brokenPaths`, subdivisions, break points), plus: `PiM.contMDiff_eval` (evaluation is
smooth on the product manifold `M^m` with model `ModelWithCorners.pi` — not in Mathlib),
`contMDiff_iota`, `efun_eq_energy'` / `efun_eq_sum` (blind `E` = formula (∗) with `ρ = riemDist`),
`pathOf` (the blind broken geodesic of given break points, continuous). `thm162` proves B's
conclusion for every subdivision carrying a `Morse.BrokenSetup` (`A_to_B_emb_BS`): `F = E' ∘ incl`
is smooth on the image of `B` (A's local ambient representatives), `B^a` is compact (image of A's
compact sublevel set under `pathOf`), the evaluation map is a closed embedding on the compact
`B^a`, its image lies in `S^{k-1}` (`mem_closedRiemBall_of_energy_le`) and is closed in the
compact `K =` image. Hence `A_to_B_emb_of_gap : A → Gap16 → B_emb`; `Gap16` (B's `Setup16` gives a
`Morse.BrokenSetup` for the same subdivision) is the known gap of §16. -/

namespace PiM

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M]
  [IsManifold 𝓘(ℝ, Rn n) ∞ M] {m : ℕ}

theorem ipi_apply (x : Fin m → Rn n) : (Ipi n m) x = x := rfl
theorem ipi_symm_apply (x : Fin m → Rn n) : (Ipi n m).symm x = x := rfl
theorem range_ipi : range (Ipi n m) = univ := by
  rw [eq_univ_iff_forall]; intro x; exact ⟨x, rfl⟩

omit [IsManifold 𝓘(ℝ, Rn n) ∞ M] in
/-- Evaluation `(y_i) ↦ y_j` is smooth on the product manifold `M^m` (model `ModelWithCorners.pi`). -/
theorem contMDiff_eval (j : Fin m) :
    ContMDiff (Ipi n m) 𝓘(ℝ, Rn n) ∞ (fun y : Fin m → M => y j) := by
  intro y
  rw [contMDiffAt_iff]
  refine ⟨(continuous_apply j).continuousAt, ?_⟩
  rw [range_ipi]
  have hT : (chartAt (Rn n) (y j)).target ∈ 𝓝 (chartAt (Rn n) (y j) (y j)) :=
    (chartAt (Rn n) (y j)).open_target.mem_nhds (mem_chart_target _ _)
  have hev : (extChartAt 𝓘(ℝ, Rn n) (y j) ∘ (fun y : Fin m → M => y j) ∘
      (extChartAt (Ipi n m) y).symm) =ᶠ[𝓝 (extChartAt (Ipi n m) y y)] fun x => x j := by
    have : (fun x : Fin m → Rn n => x j) ⁻¹' (chartAt (Rn n) (y j)).target ∈
        𝓝 (extChartAt (Ipi n m) y y) :=
      (continuous_apply j).continuousAt.preimage_mem_nhds hT
    filter_upwards [this] with x hx
    simp only [comp_apply, extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
      PartialEquiv.coe_trans_symm, ModelWithCorners.toPartialEquiv_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, OpenPartialHomeomorph.toFun_eq_coe,
      OpenPartialHomeomorph.coe_toPartialEquiv_symm, modelWithCornersSelf_coe, id]
    rw [ipi_symm_apply, piChartedSpace_chartAt]
    exact (chartAt (Rn n) (y j)).right_inv hx
  exact ((contDiff_apply ℝ (Rn n) j).contDiffAt.congr_of_eventuallyEq hev).contDiffWithinAt


/-- **The product `M^m` of a smooth manifold is a smooth manifold** for the model
`ModelWithCorners.pi` (not in Mathlib): the transition maps of product charts are products of
transition maps. -/
theorem isManifold_pi : IsManifold (Ipi n m) ∞ (Fin m → M) := by
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨es, hes, rfl⟩ ⟨es', hes', rfl⟩
  have hc : ∀ i, ContDiffOn ℝ ∞ (fun z => es' i ((es i).symm z)) ((es i).symm ≫ₕ es' i).source := by
    intro i
    have h := (contDiffGroupoid ∞ 𝓘(ℝ, Rn n)).compatible (hes i trivial) (hes' i trivial)
    have h1 := (mem_groupoid_of_pregroupoid.1 h).1
    simpa [contDiffPregroupoid, Function.comp_def] using h1
  rw [range_ipi, inter_univ]
  have hS : ContDiffOn ℝ ∞ (fun x : Fin m → Rn n => fun i => es' i ((es i).symm (x i)))
      {x | ∀ i, x i ∈ ((es i).symm ≫ₕ es' i).source} := by
    refine contDiffOn_pi.2 fun i => ?_
    exact (hc i).comp (contDiff_apply ℝ (Rn n) i).contDiffOn fun x hx => hx i
  refine hS.mono ?_
  intro x hx
  simp only [mem_preimage, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    mem_inter_iff] at hx
  intro i
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, mem_inter_iff,
    mem_preimage]
  exact ⟨hx.1 i trivial, hx.2 i trivial⟩


end PiM

namespace Emb


set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! ### Milnor's metric (copied from `Items/V10_19.lean`) -/

theorem hasDerivAt_pathLength {c : ℝ → V} (hc : Morse.IsPiecewiseSmooth c 0 1) :
    ∃ B : Finset ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ B →
      HasDerivAt (fun x => Morse.pathLength c 0 x) ‖deriv c t‖ t := by
  obtain ⟨B, hB⟩ := hc.exists_deriv_piece
  refine ⟨B, fun t ht htB => ?_⟩
  have hopen : IsOpen (Ioo (0 : ℝ) 1 \ (B : Set ℝ)) := isOpen_Ioo.sdiff B.finite_toSet.isClosed
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen t ⟨ht, htB⟩
  have hsm : t - ε / 2 ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_neg (by linarith)]; linarith
  have hup : t + ε / 2 ∈ Metric.ball t ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    rw [abs_of_pos (by linarith)]; linarith
  have hs0 : 0 ≤ t - ε / 2 := (hball hsm).1.1.le
  have hu1 : t + ε / 2 ≤ 1 := (hball hup).1.2.le
  have hsu : t - ε / 2 < t + ε / 2 := by linarith
  have hfree : ∀ x ∈ B, x ∉ Ioo (t - ε / 2) (t + ε / 2) := by
    intro x hx hx'
    have : x ∈ Metric.ball t ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx'.1, hx'.2]
    exact (hball this).2 hx
  obtain ⟨K, hK, hKeq⟩ := hB _ _ hs0 hsu hu1 hfree
  have htI : t ∈ Ioo (t - ε / 2) (t + ε / 2) := ⟨by linarith, by linarith⟩
  have hev : deriv c =ᶠ[𝓝 t] K := by
    filter_upwards [Ioo_mem_nhds htI.1 htI.2] with x hx
    exact hKeq hx
  have hKt : ContinuousAt K t := hK.continuousAt (Icc_mem_nhds htI.1 htI.2)
  have hcont : ContinuousAt (fun x => ‖deriv c x‖) t :=
    (hKt.norm).congr (hev.fun_comp (‖·‖)).symm
  have hcontOn : ContinuousOn (fun x => ‖deriv c x‖) (Ioo (t - ε / 2) (t + ε / 2)) := by
    intro x hx
    have hev' : deriv c =ᶠ[𝓝 x] K := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hKeq hy
    exact ((hK.continuousAt (Icc_mem_nhds hx.1 hx.2)).norm.congr
      (hev'.fun_comp (‖·‖)).symm).continuousWithinAt
  have hmeas : StronglyMeasurableAtFilter (fun x => ‖deriv c x‖) (𝓝 t) volume :=
    hcontOn.stronglyMeasurableAtFilter isOpen_Ioo t htI
  have hint : IntervalIntegrable (fun x => ‖deriv c x‖) volume 0 t :=
    hc.isAdmissible.integrable.mono_set (by
      rw [uIcc_of_le zero_le_one, uIcc_of_le ht.1.le]
      exact Icc_subset_Icc le_rfl ht.2.le)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

theorem dsdt_eq {w : ℝ → Bridge.Sub hN} (hw : IsPW (n := n) w 0 1) :
    ∃ B : Finset ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ B →
      dsdt (n := n) w t = Morse.PathSp.speed (incl hN ∘ w) t := by
  obtain ⟨B, hB⟩ := hasDerivAt_pathLength (isPiecewiseSmooth_of_isPW hw)
  refine ⟨B, fun t ht htB => ?_⟩
  have e : (fun x => arcLen (n := n) w 0 x) = fun x => Morse.pathLength (incl hN ∘ w) 0 x :=
    funext fun x => arcLen_eq w 0 x
  show deriv (fun x => arcLen (n := n) w 0 x) t = _
  rw [e]
  exact (hB t ht htB).deriv

theorem integral_dsdt_eq {w w' : ℝ → Bridge.Sub hN} (hw : IsPW (n := n) w 0 1)
    (hw' : IsPW (n := n) w' 0 1) :
    ∫ t in (0 : ℝ)..1, (dsdt (n := n) w t - dsdt (n := n) w' t) ^ 2 =
      ∫ t in (0 : ℝ)..1, (Morse.PathSp.speed (incl hN ∘ w) t -
        Morse.PathSp.speed (incl hN ∘ w') t) ^ 2 := by
  classical
  obtain ⟨B, hB⟩ := dsdt_eq hw
  obtain ⟨B', hB'⟩ := dsdt_eq hw'
  refine intervalIntegral.integral_congr_ae ?_
  have hfin : ((B ∪ B' ∪ {1} : Finset ℝ) : Set ℝ).Finite := Finset.finite_toSet _
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hfin.measure_zero volume)] with t htB ht
  rw [uIoc_of_le zero_le_one] at ht
  simp only [Finset.coe_union, Finset.coe_singleton, mem_union, mem_singleton_iff,
    Finset.mem_coe, not_or] at htB
  have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 htB.2⟩
  rw [hB t ht' htB.1.1, hB' t ht' htB.1.2]

theorem supDist_ne_top {c c' : ℝ → V} {p q : V} (hc : c ∈ Morse.pathSpace N p q)
    (hc' : c' ∈ Morse.pathSpace N p q) : Morse.PathSp.supDist N c c' ≠ ⊤ := by
  have key : ∀ {c : ℝ → V}, c ∈ Morse.pathSpace N p q → ∀ t ∈ Icc (0 : ℝ) 1,
      Morse.riemDist (N := N) p (c t) ≤ ENNReal.ofReal (Morse.pathLength c 0 1) := by
    intro c hc t ht
    have h1 := Morse.riemDist_le_pathLength (N := N) (hc.1.mono le_rfl ht.1 ht.2)
      (fun s hs => hc.2.1 s ⟨hs.1, hs.2.trans ht.2⟩)
    rw [hc.2.2.1] at h1
    exact h1.trans (ENNReal.ofReal_le_ofReal (hc.1.isAdmissible.pathLength_le le_rfl ht.1 ht.2))
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (Morse.pathLength c 0 1) +
    ENNReal.ofReal (Morse.pathLength c' 0 1)) (by simp) ?_
  refine iSup₂_le fun t ht => ?_
  calc Morse.riemDist (N := N) (c t) (c' t)
      ≤ Morse.riemDist (N := N) (c t) p + Morse.riemDist (N := N) p (c' t) :=
        Morse.riemDist_triangle _ _ _
    _ ≤ _ := add_le_add ((Morse.riemDist_comm _ _).trans_le (key hc t ht)) (key hc' t ht)

theorem mem_pathSpace {p q : Bridge.Sub hN} {w : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) :
    incl hN ∘ w ∈ Morse.pathSpace N (incl hN p) (incl hN q) :=
  ⟨isPiecewiseSmooth_of_isPW hw.1, fun t _ => (w t).2, congrArg (incl hN) hw.2.1,
    congrArg (incl hN) hw.2.2⟩

def pt {p q : Bridge.Sub hN} {w : ℝ → Bridge.Sub hN} (hw : InOmega (n := n) p q w) :
    Morse.PathSp N (incl hN p) (incl hN q) :=
  ⟨incl hN ∘ w, mem_pathSpace hw⟩

theorem iSup_rho_eq {p q : Bridge.Sub hN} {w w' : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) (hw' : InOmega (n := n) p q w') :
    (⨆ t : Icc (0 : ℝ) 1, rho (n := n) (w t) (w' t)) =
      (Morse.PathSp.supDist N (incl hN ∘ w) (incl hN ∘ w')).toReal := by
  have hne := supDist_ne_top (mem_pathSpace hw) (mem_pathSpace hw')
  rw [Morse.PathSp.supDist, iSup_subtype', ENNReal.toReal_iSup ?_]
  · exact iSup_congr fun t => rho_eq _ _
  · intro t
    exact ne_top_of_le_ne_top hne (Morse.PathSp.riemDist_le_supDist t.2)

theorem edist_eq {p q : Bridge.Sub hN} {w w' : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) (hw' : InOmega (n := n) p q w') :
    edist (pt hw) (pt hw') = ENNReal.ofReal (dOm (n := n) w w') := by
  rw [Morse.PathSp.edist_def]
  show _ = ENNReal.ofReal ((⨆ t : Icc (0 : ℝ) 1, rho (n := n) (w t) (w' t)) +
    Real.sqrt (∫ t in (0 : ℝ)..1, (dsdt (n := n) w t - dsdt (n := n) w' t) ^ 2))
  rw [iSup_rho_eq hw hw', integral_dsdt_eq hw.1 hw'.1,
    ENNReal.ofReal_add ENNReal.toReal_nonneg (Real.sqrt_nonneg _),
    ENNReal.ofReal_toReal (supDist_ne_top (mem_pathSpace hw) (mem_pathSpace hw'))]
  rfl

theorem dOm_nonneg {p q : Bridge.Sub hN} {w w' : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) (hw' : InOmega (n := n) p q w') : 0 ≤ dOm (n := n) w w' := by
  show 0 ≤ (⨆ t : Icc (0 : ℝ) 1, rho (n := n) (w t) (w' t)) +
    Real.sqrt (∫ t in (0 : ℝ)..1, (dsdt (n := n) w t - dsdt (n := n) w' t) ^ 2)
  rw [iSup_rho_eq hw hw']
  exact add_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg _)

theorem efun_eq (w : ℝ → Bridge.Sub hN) : Efun (n := n) w = Morse.energy (incl hN ∘ w) 0 1 :=
  energy_eq w 0 1

/-! ### The normalized blind path space `Ω` and `Morse.PathSp` -/

section Omega

variable {p q : Bridge.Sub hN}

/-- `w ↦ incl ∘ w`, blind `Ω(↥N; p, q)` → `Morse.PathSp N p q`. -/
def tau (w : Om n p q) : Morse.PathSp N (incl hN p) (incl hN q) := pt w.2.1

theorem dOm_self (w : Om n p q) : dOm (n := n) w.1 w.1 = 0 := by
  have h := edist_eq w.2.1 w.2.1
  rw [edist_self] at h
  have h0 := dOm_nonneg w.2.1 w.2.1
  have := ENNReal.ofReal_eq_zero.1 h.symm
  linarith

/-- The blind topology of `Ω` (generated by the `d`-balls) is induced by `τ` (as in
`Items/V10_19.lean`). -/
theorem omTopology_eq :
    omTopology n p q = TopologicalSpace.induced (tau (n := n)) inferInstance := by
  apply le_antisymm
  · intro s hs
    obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.1 hs
    rw [isOpen_iff_forall_mem_open]
    intro w hw
    obtain ⟨ε, hε, hball⟩ := EMetric.isOpen_iff.1 hU _ hw
    obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hr : 0 < r := ENNReal.ofReal_pos.1 hr0
    refine ⟨{w' | dOm (n := n) w.1 w'.1 < r}, fun w' hw' => hball ?_,
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨w, r, rfl⟩, ?_⟩
    · rw [Metric.mem_eball, edist_comm]
      show edist (pt w.2.1) (pt w'.2.1) < ε
      rw [edist_eq w.2.1 w'.2.1]
      exact ((ENNReal.ofReal_lt_ofReal_iff hr).2 hw').trans hrε
    · show dOm (n := n) w.1 w.1 < r
      rw [dOm_self]; exact hr
  · refine le_generateFrom fun s ⟨w, ε, hs⟩ => ?_
    subst hs
    rcases le_or_gt ε 0 with hε | hε
    · convert @isOpen_empty _ (TopologicalSpace.induced (tau (n := n)) inferInstance)
      ext w'
      show dOm (n := n) w.1 w'.1 < ε ↔ False
      simp only [iff_false, not_lt]
      exact hε.trans (dOm_nonneg w.2.1 w'.2.1)
    · refine isOpen_induced_iff.2
        ⟨Metric.eball (tau w) (ENNReal.ofReal ε), Metric.isOpen_eball, ?_⟩
      ext w'
      show edist (tau w') (tau w) < ENNReal.ofReal ε ↔ dOm (n := n) w.1 w'.1 < ε
      rw [edist_comm]
      show edist (pt w.2.1) (pt w'.2.1) < _ ↔ _
      rw [edist_eq w.2.1 w'.2.1, ENNReal.ofReal_lt_ofReal_iff hε]

theorem isInducing_tau : IsInducing (tau (n := n) (p := p) (q := q)) := ⟨omTopology_eq⟩

/-- Clamping to `[0, 1]`. -/
def clamp (t : ℝ) : ℝ := max 0 (min t 1)

theorem clamp_mem (t : ℝ) : clamp t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

theorem clamp_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp t = t := by
  unfold clamp; rw [min_eq_left ht.2, max_eq_right ht.1]

theorem clamp_clamp (t : ℝ) : clamp (clamp t) = clamp t := clamp_of_mem (clamp_mem t)

/-- Elements of the normalized blind `Ω` agreeing on `[0, 1]` are equal. -/
theorem om_ext {w w' : Om n p q} (h : ∀ t ∈ Icc (0 : ℝ) 1, w.1 t = w'.1 t) : w = w' := by
  apply Subtype.ext
  funext t
  rw [w.2.2 t, w'.2.2 t]
  exact h _ (clamp_mem t)

theorem lift_congr {f : ℝ → V} {q₀ : Bridge.Sub hN} {t t' : ℝ} (h1 : f t ∈ N) (h : f t = f t') :
    lift f q₀ t = lift f q₀ t' := by
  have h2 : f t' ∈ N := h ▸ h1
  rw [lift_of_mem q₀ h1, lift_of_mem q₀ h2]
  exact Subtype.ext h

/-- The normalized lift of a project path to the blind `Ω`: `t ↦ γ(clamp t)` in `↥N`. -/
noncomputable def nlift (γ : Morse.PathSp N (incl hN p) (incl hN q)) : Om n p q :=
  ⟨lift ((γ : ℝ → V) ∘ clamp) p, by
    have hγ' : (γ : ℝ → V) ∘ clamp ∈ Morse.pathSpace N (incl hN p) (incl hN q) :=
      Morse.PathSp.pathSpace_congr γ.2 fun t ht => by simp [clamp_of_mem ht]
    have heq : EqOn (incl hN ∘ lift ((γ : ℝ → V) ∘ clamp) p) ((γ : ℝ → V) ∘ clamp) (Icc 0 1) :=
      fun t ht => incl_lift p (hγ'.2.1 t ht)
    refine ⟨⟨isPW_lift hγ'.1 hγ'.2.1 p, ?_, ?_⟩, fun t => ?_⟩
    · apply Subtype.ext
      exact (heq ⟨le_rfl, zero_le_one⟩).trans hγ'.2.2.1
    · apply Subtype.ext
      exact (heq ⟨zero_le_one, le_rfl⟩).trans hγ'.2.2.2
    · show lift ((γ : ℝ → V) ∘ clamp) p t = lift ((γ : ℝ → V) ∘ clamp) p (clamp t)
      exact lift_congr (γ.2.2.1 _ (clamp_mem t)) (by simp only [comp_apply, clamp_clamp])⟩

theorem incl_nlift (γ : Morse.PathSp N (incl hN p) (incl hN q)) (t : ℝ) :
    incl hN ((nlift (n := n) γ).1 t) = (γ : ℝ → V) (clamp t) :=
  incl_lift p (γ.2.2.1 _ (clamp_mem t))

theorem incl_nlift_of_mem (γ : Morse.PathSp N (incl hN p) (incl hN q)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : incl hN ((nlift (n := n) γ).1 t) = (γ : ℝ → V) t := by
  rw [incl_nlift, clamp_of_mem ht]

theorem edist_tau_nlift (γ : Morse.PathSp N (incl hN p) (incl hN q)) :
    edist (tau (nlift (n := n) γ)) γ = 0 :=
  Morse.PathSp.edist_eq_zero_of_eqOn fun _ ht => incl_nlift_of_mem γ ht

end Omega

/-! ### Geodesic segments: blind (closed interval) vs project (open interval) -/

/-- A curve in `N`, smooth on `[a, b]` and a project geodesic on `(a, b)`, is a blind geodesic of
the induced connection on the closed interval `[a, b]` (the normal acceleration vanishes at the end
points by continuity; as `Items/V8_10.lean` does on `[0, 1]`). -/
theorem isGeodesic_Icc_of {w : ℝ → Bridge.Sub hN} {a b : ℝ} (hab : a < b)
    (hc : ContDiffOn ℝ ∞ (incl hN ∘ w) (Icc a b))
    (hg : Morse.IsGeodesicOn hN (incl hN ∘ w) (Ioo a b)) :
    IsGeodesic (Bridge.conn (hN := hN)) w (Icc a b) := by
  show RoundTrip.BridgePrelude.IsGeodesic _ _ _
  refine Bridge.isGeodesic_iff.2 ⟨⟨ordConnected_Icc, uniqueDiffOn_Icc hab⟩, hc, ?_⟩
  set f := incl hN ∘ w
  set J := Icc a b
  have uI : UniqueDiffOn ℝ J := uniqueDiffOn_Icc hab
  have hg2 : ContinuousOn (derivWithin (derivWithin f J) J) J :=
    ((hc.derivWithin uI (m := ∞) (by simp)).derivWithin uI (m := 0) (by simp)).continuousOn
  have hpw : ContinuousOn w J := fun t ht =>
    (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := w)).2 (hc.continuousOn t ht)
  have hP : ContinuousOn (fun t => Bridge.P hN (w t)) J :=
    Bridge.contMDiff_P.continuous.comp_continuousOn hpw
  have hcont : ContinuousOn
      (fun t => Bridge.P hN (w t) (derivWithin (derivWithin f J) J t)) J := hP.clm_apply hg2
  have hzero : EqOn (fun t => Bridge.P hN (w t) (derivWithin (derivWithin f J) J t)) 0
      (Ioo a b) := by
    intro t ht
    have h1 : deriv f =ᶠ[𝓝 t] derivWithin f J := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with τ hτ
      exact (derivWithin_of_mem_nhds (Icc_mem_nhds hτ.1 hτ.2)).symm
    have e : derivWithin (derivWithin f J) J t = deriv (deriv f) t := by
      rw [h1.deriv_eq, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    show Bridge.P hN (w t) _ = 0
    rw [e]
    exact (Morse.tanProj_eq_zero_iff hN).2 (hg.normal t ht)
  intro t ht
  exact hzero.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne]) ht

/-! ### Blind subdivisions (`ℕ`-indexed) and `Morse.Subdivision` -/

/-- The project subdivision with the division points of a blind one (`k = m + 1` segments). -/
def subdiv {m : ℕ} (t : ℕ → ℝ) (h0 : t 0 = 0) (hk : t (m + 1) = 1)
    (ht : ∀ i < m + 1, t i < t (i + 1)) : Morse.Subdivision m where
  t i := t i
  strictMono := fun i j hij => lt_of_strictSeq ht (Fin.lt_def.1 hij) (by omega)
  t_zero := h0
  t_last := hk

/-! ### Blind broken geodesics and `Morse.BrokenSetup.brokenPaths` -/

section Core

variable {p q : Bridge.Sub hN} {c : ℝ} {m : ℕ} {t : ℕ → ℝ}
  (BS : Morse.BrokenSetup hN (incl hN p) (incl hN q) c m) (hBt : ∀ i : Fin (m + 2), BS.t i = t i)
include hBt

theorem t_mem (i : ℕ) (hi : i ≤ m + 1) : t i ∈ Icc (0 : ℝ) 1 := by
  have h := hBt ⟨i, by omega⟩
  exact ⟨h ▸ BS.t_nonneg _, h ▸ BS.t_le_one _⟩

theorem t_lt (i : ℕ) (hi : i < m + 1) : t i < t (i + 1) := by
  have h1 := hBt ⟨i, by omega⟩
  have h2 := hBt ⟨i + 1, by omega⟩
  rw [← h1, ← h2]
  exact BS.strictMono (Fin.lt_def.2 (by simp))

/-- A blind broken geodesic (blind `B`) is, in `V`, a project broken geodesic of energy `< c`. -/
theorem mem_brokenPaths_of_mem_Bset {w : Om n p q}
    (hw : w ∈ Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t) :
    (tau w : ℝ → V) ∈ BS.brokenPaths := by
  refine ⟨(tau w).2, fun i => ?_, ?_⟩
  · have hi : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) w.1
        (Icc (t i) (t (i + 1))) := hw.1.2 i.val i.isLt
    have h := Bridge.isGeodesicOn_Ioo hi
    rw [hBt, hBt]
    exact h
  · show Morse.energy (incl hN ∘ w.1) 0 1 < c
    rw [← efun_eq]; exact hw.2

/-- Conversely, an element of the blind `Ω` agreeing on `[0, 1]` with a project broken geodesic of
energy `< c` is a blind broken geodesic. -/
theorem mem_Bset_of {w : Om n p q} {γ : ℝ → V} (hγ : γ ∈ BS.brokenPaths)
    (heq : ∀ s ∈ Icc (0 : ℝ) 1, incl hN (w.1 s) = γ s) :
    w ∈ Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t := by
  refine ⟨⟨w.2.1, fun i hi => ?_⟩, ?_⟩
  · have hg : Morse.IsGeodesicOn hN γ (Ioo (BS.t (⟨i, hi⟩ : Fin (m + 1)).castSucc)
        (BS.t (⟨i, hi⟩ : Fin (m + 1)).succ)) := hγ.2.1 ⟨i, hi⟩
    rw [hBt, hBt] at hg
    have ha := (t_mem BS hBt i (by omega)).1
    have hb := (t_mem BS hBt (i + 1) (by omega)).2
    have hab := t_lt BS hBt i hi
    have hg' : Morse.IsGeodesicOn hN (incl hN ∘ w.1) (Ioo (t i) (t (i + 1))) :=
      hg.congr fun s hs => (heq s ⟨ha.trans hs.1.le, hs.2.le.trans hb⟩).symm
    exact isGeodesic_Icc_of hab (Morse.contDiffOn_Icc_of_isGeodesicOn hN
      (isPiecewiseSmooth_of_isPW w.2.1.1) ha hab hb hg') hg'
  · rw [efun_eq]; exact (Morse.energy_congr heq).trans_lt hγ.2.2

omit hBt in
/-- `y ↦ incl ∘ y`, `(↥N)^m → V^m`. -/
def iota (y : Fin m → Bridge.Sub hN) : Fin m → V := fun j => incl hN (y j)

omit hBt in
theorem isInducing_iota : IsInducing (iota (hN := hN) (m := m)) :=
  IsInducing.piMap fun _ => IsInducing.subtypeVal

omit hBt in
theorem iota_injective : Injective (iota (hN := hN) (m := m)) := fun y y' h =>
  funext fun j => Subtype.ext (congrFun h j)

/-- The blind break points of `w`, read in `V`, are the project's `nodeVal`. -/
theorem iota_evalPts (w : Om n p q) :
    iota (evalPts (m + 1) t w.1) = BS.nodeVal (tau w : ℝ → V) := by
  funext j
  show incl hN (w.1 (t ((j : ℕ) + 1))) = incl hN (w.1 (BS.t j.castSucc.succ))
  rw [hBt]
  rfl

/-- `nodeVal` only sees the values on `[0, 1]`. -/
theorem nodeVal_congr {γ γ' : ℝ → V} (h : EqOn γ γ' (Icc 0 1)) : BS.nodeVal γ = BS.nodeVal γ' :=
  funext fun j => h ⟨BS.t_nonneg _, BS.t_le_one _⟩

/-- **The core of Lemma 16.1 on embedded manifolds**: for a subdivision carrying the data of a
`Morse.BrokenSetup`, the blind evaluation map `w ↦ (w(t₁), …, w(t_m))` is an open embedding of the
blind `B = Int Ω(t₀, …, t_k)^c` (topology of Milnor's `d`) into `(↥N)^m`, given the project's
Lemma 16.1 (bijection with `B.nodes`), openness of `B.nodes` and the continuity of `B.pathP` and
`nodeVal` for Milnor's metric. -/
theorem isOpenEmbedding_evalPts
    (hpath : Continuous BS.pathP)
    (hnode : Continuous fun γ : Morse.PathSp N (incl hN p) (incl hN q) => BS.nodeVal γ)
    (h161a : ∀ y ∈ BS.nodes, BS.path y ∈ BS.brokenPaths ∧ BS.nodeVal (BS.path y) = y)
    (h161b : ∀ γ ∈ BS.brokenPaths, BS.nodeVal γ ∈ BS.nodes ∧
      EqOn (BS.path (BS.nodeVal γ)) γ (Icc 0 1))
    (hopen : ∃ O, IsOpen O ∧ BS.nodes = (Set.univ.pi fun _ => N) ∩ O) :
    IsOpenEmbedding
      (fun w : Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t => evalPts (m + 1) t w.1.1) := by
  set E := Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t
  set U : Set (Fin m → Bridge.Sub hN) := {y | iota y ∈ BS.nodes}
  obtain ⟨O, hO, hnodes⟩ := hopen
  have hU : IsOpen U := by
    have : U = iota ⁻¹' O := by
      ext y
      simp only [U, mem_ofPred_eq, mem_preimage, hnodes, mem_inter_iff, Set.mem_pi, mem_univ,
        true_implies, and_iff_right_iff_imp]
      exact fun _ j => (y j).2
    rw [this]; exact hO.preimage isInducing_iota.continuous
  have hbp : ∀ w : E, (tau w.1 : ℝ → V) ∈ BS.brokenPaths := fun w =>
    mem_brokenPaths_of_mem_Bset BS hBt w.2
  let f : E → U := fun w => ⟨evalPts (m + 1) t w.1.1, show iota _ ∈ BS.nodes by
    rw [iota_evalPts BS hBt]; exact (h161b _ (hbp w)).1⟩
  let g : U → E := fun y => ⟨nlift (BS.pathP ⟨iota y.1, y.2⟩),
    mem_Bset_of BS hBt (h161a _ y.2).1 fun s hs => incl_nlift_of_mem _ hs⟩
  have hfg : ∀ y, f (g y) = y := by
    intro y
    apply Subtype.ext
    apply iota_injective
    show iota (evalPts (m + 1) t (g y).1.1) = iota y.1
    rw [iota_evalPts BS hBt]
    rw [nodeVal_congr BS hBt (γ' := BS.path (iota y.1)) fun s hs => incl_nlift_of_mem _ hs]
    exact (h161a _ y.2).2
  have hgf : ∀ w, g (f w) = w := by
    intro w
    apply Subtype.ext
    apply om_ext
    intro s hs
    apply Subtype.ext
    show incl hN ((g (f w)).1.1 s) = incl hN (w.1.1 s)
    rw [incl_nlift_of_mem _ hs]
    show BS.path (iota (evalPts (m + 1) t w.1.1)) s = _
    rw [iota_evalPts BS hBt]
    exact (h161b _ (hbp w)).2 hs
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    refine isInducing_iota.continuous_iff.2 ?_
    have : (iota ∘ fun w : E => evalPts (m + 1) t w.1.1) =
        fun w : E => BS.nodeVal (tau w.1 : ℝ → V) := funext fun w => iota_evalPts BS hBt w.1
    rw [this]
    exact hnode.comp (isInducing_tau.continuous.comp continuous_subtype_val)
  have hgc : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    refine isInducing_tau.continuous_iff.2 ?_
    refine Morse.PathSp.continuous_of_edist_eq_zero
      (hpath.comp (Continuous.subtype_mk (isInducing_iota.continuous.comp continuous_subtype_val)
        fun y => y.2)) fun y => ?_
    exact edist_tau_nlift _
  let hom : E ≃ₜ U :=
    { toFun := f, invFun := g, left_inv := hgf, right_inv := hfg,
      continuous_toFun := hfc, continuous_invFun := hgc }
  exact hU.isOpenEmbedding_subtypeVal.comp hom.isOpenEmbedding

end Core


/-! ### Theorem 16.2 (1)–(2) on embedded manifolds, for `BrokenSetup` subdivisions -/

section Thm162

variable {p q : Bridge.Sub hN} {c : ℝ} {m : ℕ} {t : ℕ → ℝ}
  (BS : Morse.BrokenSetup hN (incl hN p) (incl hN q) c m) (hBt : ∀ i : Fin (m + 2), BS.t i = t i)
  (hnode : Continuous fun γ : Morse.PathSp N (incl hN p) (incl hN q) => BS.nodeVal γ)
include hBt

omit hBt in
/-- The map `y ↦ incl ∘ y` is smooth on the product manifold `(↥N)^m`. -/
theorem contMDiff_iota : ContMDiff (Ipi n m) 𝓘(ℝ, Fin m → V) ∞ (iota (hN := hN) (m := m)) :=
  contMDiff_pi_space.2 fun j => Bridge.contMDiff_incl.comp (PiM.contMDiff_eval j)

/-- The blind energy of a blind broken geodesic is `E'` of its break points. -/
theorem efun_eq_energy' {w : Om n p q}
    (hw : w ∈ Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t) :
    Efun (n := n) w.1 = BS.energy' (iota (evalPts (m + 1) t w.1)) := by
  have hbp := mem_brokenPaths_of_mem_Bset BS hBt hw
  obtain ⟨hy, heq⟩ := (BS.lemma_16_1).2 _ hbp
  rw [efun_eq, iota_evalPts BS hBt, ← BS.energy_path hy]
  exact (Morse.energy_congr fun s hs => (heq hs).symm)

/-- The explicit formula of p. 90 for blind broken geodesics. -/
theorem efun_eq_sum {w : Om n p q}
    (hw : w ∈ Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t) :
    Efun (n := n) w.1 = ∑ i ∈ Finset.range (m + 1),
      rho (n := n) (w.1 (t i)) (w.1 (t (i + 1))) ^ 2 / (t (i + 1) - t i) := by
  rw [efun_eq_energy' BS hBt hw, iota_evalPts BS hBt, Morse.BrokenSetup.energy',
    ← Fin.sum_univ_eq_sum_range (fun i => rho (n := n) (w.1 (t i)) (w.1 (t (i + 1))) ^ 2 /
      (t (i + 1) - t i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hγ := (tau w).2
  rw [BS.vert_nodeVal hγ, BS.vert_nodeVal hγ]
  have e1 := hBt i.castSucc
  have e2 := hBt i.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at e1 e2
  have hlen : BS.len i = t (i + 1) - t i := by
    show BS.t i.succ - BS.t i.castSucc = _
    rw [e1, e2]
  rw [hlen, e1, e2]
  have hr : rho (n := n) (w.1 (t i)) (w.1 (t (i + 1))) =
      (Morse.riemDist (N := N) (incl hN (w.1 (t i))) (incl hN (w.1 (t (i + 1))))).toReal :=
    rho_eq _ _
  rw [hr]
  rfl

theorem iota_mem_nodes_of_mem_Bset (h161b : ∀ γ ∈ BS.brokenPaths, BS.nodeVal γ ∈ BS.nodes ∧
      EqOn (BS.path (BS.nodeVal γ)) γ (Icc 0 1)) {w : Om n p q}
    (hw : w ∈ Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t) :
    iota (evalPts (m + 1) t w.1) ∈ BS.nodes := by
  rw [iota_evalPts BS hBt]
  exact (h161b _ (mem_brokenPaths_of_mem_Bset BS hBt hw)).1

omit hBt in
/-- The blind broken geodesic with break points `y`. -/
noncomputable def pathOf (y : BS.nodes) : Om n p q := nlift (BS.pathP y)

theorem mem_Bset_pathOf (h161a : ∀ y ∈ BS.nodes, BS.path y ∈ BS.brokenPaths) (y : BS.nodes) :
    pathOf (n := n) BS y ∈ Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t :=
  mem_Bset_of BS hBt (h161a _ y.2) fun s hs => incl_nlift_of_mem _ hs

theorem pathOf_evalPts (h161b : ∀ γ ∈ BS.brokenPaths, BS.nodeVal γ ∈ BS.nodes ∧
      EqOn (BS.path (BS.nodeVal γ)) γ (Icc 0 1)) {w : Om n p q}
    (hw : w ∈ Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t) :
    pathOf (n := n) BS ⟨_, iota_mem_nodes_of_mem_Bset BS hBt h161b hw⟩ = w := by
  apply om_ext
  intro s hs
  apply Subtype.ext
  show incl hN ((pathOf (n := n) BS _).1 s) = incl hN (w.1 s)
  rw [pathOf, incl_nlift_of_mem _ hs]
  show BS.path (iota (evalPts (m + 1) t w.1)) s = _
  rw [iota_evalPts BS hBt]
  exact (h161b _ (mem_brokenPaths_of_mem_Bset BS hBt hw)).2 hs

omit hBt in
theorem continuous_pathOf (hpath : Continuous BS.pathP) :
    Continuous (pathOf (n := n) BS) := by
  refine isInducing_tau.continuous_iff.2 ?_
  exact Morse.PathSp.continuous_of_edist_eq_zero hpath fun y => edist_tau_nlift _

include hnode in
theorem continuous_evalPts :
    Continuous (fun w : Om n p q => evalPts (m + 1) t w.1) := by
  refine isInducing_iota.continuous_iff.2 ?_
  have : (iota ∘ fun w : Om n p q => evalPts (m + 1) t w.1) =
      fun w => BS.nodeVal (tau w : ℝ → V) := funext fun w => iota_evalPts BS hBt w
  rw [this]
  exact hnode.comp isInducing_tau.continuous

theorem evalPts_injOn (h161b : ∀ γ ∈ BS.brokenPaths, BS.nodeVal γ ∈ BS.nodes ∧
      EqOn (BS.path (BS.nodeVal γ)) γ (Icc 0 1)) :
    InjOn (fun w : Om n p q => evalPts (m + 1) t w.1) (Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t) := by
  intro w hw w' hw' h
  rw [← pathOf_evalPts BS hBt h161b hw, ← pathOf_evalPts BS hBt h161b hw']
  congr 2
  exact congrArg iota h

include hnode in
/-- **Theorem 16.2 (1)–(2) of B on embedded manifolds, for a `BrokenSetup` subdivision**, from the
project's smooth local representatives of `E'` and compact sublevel sets (A), Lemma 16.1 and
formula (∗), and the continuity of `B.pathP` and `nodeVal`. -/
theorem thm162 (hpath : Continuous BS.pathP)
    (hsmooth : ∀ y₀ ∈ BS.nodes, ∃ O, IsOpen O ∧ y₀ ∈ O ∧ ∃ F : (Fin m → V) → ℝ,
      ContDiffOn ℝ ∞ F O ∧ ∀ y ∈ BS.nodes ∩ O, BS.energy' y = F y)
    (hcpt : ∀ a < c, IsCompact {y | y ∈ BS.nodes ∧ BS.energy' y ≤ a}) :
    (∃ F : (Fin (m + 1 - 1) → Bridge.Sub hN) → ℝ, IsEprime n (Bridge.conn (hN := hN)) p q c (m + 1) t F
        ((fun w : Om n p q => evalPts (m + 1) t w.1) '' Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t)) ∧
    (∀ w ∈ Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t, Efun (n := n) w.1 =
      ∑ i ∈ Finset.range (m + 1), rho (n := n) (w.1 (t i)) (w.1 (t (i + 1))) ^ 2 / (t (i + 1) - t i)) ∧
    ∀ a : ℝ, a < c →
      IsCompact (BsetA n (Bridge.conn (hN := hN)) p q c (m + 1) t a) ∧
      IsEmbedding (fun w : BsetA n (Bridge.conn (hN := hN)) p q c (m + 1) t a => evalPts (m + 1) t w.1.1) ∧
      (fun w : Om n p q => evalPts (m + 1) t w.1) '' BsetA n (Bridge.conn (hN := hN)) p q c (m + 1) t a ⊆
        Set.univ.pi (fun _ => Sball n p c) ∧
      ∃ K : Set (Fin (m + 1 - 1) → Bridge.Sub hN), IsCompact K ∧
        (fun w : Om n p q => evalPts (m + 1) t w.1) '' BsetA n (Bridge.conn (hN := hN)) p q c (m + 1) t a ⊆ K ∧
        ∃ C : Set (Fin (m + 1 - 1) → Bridge.Sub hN), IsClosed C ∧
          (fun w : Om n p q => evalPts (m + 1) t w.1) '' BsetA n (Bridge.conn (hN := hN)) p q c (m + 1) t a = C ∩ K := by
  have h161a : ∀ y ∈ BS.nodes, BS.path y ∈ BS.brokenPaths := fun y hy => (BS.lemma_16_1.1 y hy).1
  have h161b := BS.lemma_16_1.2
  set ev := fun w : Om n p q => evalPts (m + 1) t w.1
  have hev : Continuous ev := continuous_evalPts BS hBt hnode
  refine ⟨⟨fun y => BS.energy' (iota y), rfl, ?_, fun w hw => (efun_eq_energy' BS hBt hw).symm⟩,
    fun w hw => efun_eq_sum BS hBt hw, fun a ha => ?_⟩
  · -- smoothness of `E'` in the break points
    show ContMDiffOn (Ipi n m) 𝓘(ℝ, ℝ) ∞ (fun y : Fin m → Bridge.Sub hN => BS.energy' (iota y)) _
    intro y hy
    obtain ⟨w, hw, hwy⟩ := hy
    have hyN : iota y ∈ BS.nodes := by
      rw [← hwy]; exact iota_mem_nodes_of_mem_Bset BS hBt h161b hw
    obtain ⟨O, hO, hyO, F, hF, hEF⟩ := hsmooth _ hyN
    have h1 : ContMDiffAt (Ipi n m) 𝓘(ℝ, ℝ) ∞ (F ∘ iota) y :=
      (hF.contDiffAt (hO.mem_nhds hyO)).contMDiffAt.comp y (contMDiff_iota y)
    refine h1.contMDiffWithinAt.congr_of_eventuallyEq ?_ (hEF _ ⟨hyN, hyO⟩)
    have : iota ⁻¹' O ∈ 𝓝[ev '' Bset n (Bridge.conn (hN := hN)) p q c (m + 1) t] y :=
      mem_nhdsWithin_of_mem_nhds ((hO.preimage isInducing_iota.continuous).mem_nhds hyO)
    filter_upwards [this, self_mem_nhdsWithin] with y' hy'O hy'
    obtain ⟨w', hw', rfl⟩ := hy'
    exact hEF _ ⟨iota_mem_nodes_of_mem_Bset BS hBt h161b hw', hy'O⟩
  · -- `B^a` is the image of the compact sublevel set of `E'` under the continuous `pathOf`
    have hBa : BsetA n (Bridge.conn (hN := hN)) p q c (m + 1) t a =
        pathOf (n := n) BS '' {y : BS.nodes | BS.energy' y ≤ a} := by
      ext w
      constructor
      · rintro ⟨hw, hwa⟩
        refine ⟨⟨_, iota_mem_nodes_of_mem_Bset BS hBt h161b hw⟩, ?_, pathOf_evalPts BS hBt h161b hw⟩
        show BS.energy' _ ≤ a
        rw [← efun_eq_energy' BS hBt hw]; exact hwa
      · rintro ⟨y, hya, rfl⟩
        have hm := mem_Bset_pathOf BS hBt h161a y
        refine ⟨hm, ?_⟩
        rw [efun_eq_energy' BS hBt hm]
        have : iota (evalPts (m + 1) t (pathOf (n := n) BS y).1) = (y : Fin m → V) := by
          rw [iota_evalPts BS hBt, nodeVal_congr BS hBt (γ' := BS.path y)
            fun s hs => incl_nlift_of_mem _ hs]
          exact (BS.lemma_16_1.1 y y.2).2.1
        rw [this]; exact hya
    have hK : IsCompact (BsetA n (Bridge.conn (hN := hN)) p q c (m + 1) t a) := by
      rw [hBa]
      refine IsCompact.image ?_ (continuous_pathOf BS hpath)
      rw [Subtype.isCompact_iff]
      convert hcpt a ha using 1
      ext y
      simp only [mem_image, mem_ofPred_eq, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
    have hKim : IsCompact (ev '' BsetA n (Bridge.conn (hN := hN)) p q c (m + 1) t a) := hK.image hev
    refine ⟨hK, ?_, ?_, _, hKim, subset_rfl, _, hKim.isClosed, (inter_self _).symm⟩
    · haveI := isCompact_iff_compactSpace.1 hK
      refine (Continuous.isClosedEmbedding (hev.comp continuous_subtype_val) ?_).isEmbedding
      intro w w' h
      exact Subtype.ext (evalPts_injOn BS hBt h161b w.2.1 w'.2.1 h)
    · rintro _ ⟨w, hw, rfl⟩ j -
      show rho (n := n) p (w.1 (t ((j : ℕ) + 1))) ≤ Real.sqrt c
      have hE : Morse.energy (tau w : ℝ → V) 0 1 ≤ c := by
        show Morse.energy (incl hN ∘ w.1) 0 1 ≤ c
        rw [← efun_eq]; exact hw.2.trans ha.le
      have h := (Morse.mem_closedRiemBall_of_energy_le (tau w).2 hE
        (t_mem BS hBt ((j : ℕ) + 1) (by omega))).2
      have hr : rho (n := n) p (w.1 (t ((j : ℕ) + 1))) =
          (Morse.riemDist (N := N) (incl hN p) (incl hN (w.1 (t ((j : ℕ) + 1))))).toReal :=
        rho_eq _ _
      rw [hr]
      exact ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg c) h

end Thm162

end Emb

/-- B's conclusion for `M = ↥N`, the induced connection and the data `p, q, c, k, t`. -/
def Concl {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ}
    {N : Set V} (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (p q : Bridge.Sub hN) (c : ℝ) (k : ℕ) (t : ℕ → ℝ) : Prop :=
  (∃ F : (Fin (k - 1) → Bridge.Sub hN) → ℝ,
      IsEprime n (Bridge.conn (hN := hN)) p q c k t F
        ((fun w : Om n p q => evalPts k t w.1) '' Bset n (Bridge.conn (hN := hN)) p q c k t)) ∧
    (∀ w ∈ Bset n (Bridge.conn (hN := hN)) p q c k t, Efun (n := n) w.1 =
      ∑ i ∈ Finset.range k, rho (n := n) (w.1 (t i)) (w.1 (t (i + 1))) ^ 2 / (t (i + 1) - t i)) ∧
    ∀ a : ℝ, a < c →
      IsCompact (BsetA n (Bridge.conn (hN := hN)) p q c k t a) ∧
      IsEmbedding (fun w : BsetA n (Bridge.conn (hN := hN)) p q c k t a => evalPts k t w.1.1) ∧
      (fun w : Om n p q => evalPts k t w.1) '' BsetA n (Bridge.conn (hN := hN)) p q c k t a ⊆
        Set.univ.pi (fun _ => Sball n p c) ∧
      ∃ K : Set (Fin (k - 1) → Bridge.Sub hN), IsCompact K ∧
        (fun w : Om n p q => evalPts k t w.1) '' BsetA n (Bridge.conn (hN := hN)) p q c k t a ⊆ K ∧
        ∃ C : Set (Fin (k - 1) → Bridge.Sub hN), IsClosed C ∧
          (fun w : Om n p q => evalPts k t w.1) '' BsetA n (Bridge.conn (hN := hN)) p q c k t a =
            C ∩ K

/-- B on embedded manifolds: `M = ↥N` (`Bridge.Sub hN`, model `ℝⁿ`, induced metric, connected)
with the induced Levi-Civita connection `Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
    ∀ (p q : Bridge.Sub hN) (c ε : ℝ) (k : ℕ) (t : ℕ → ℝ),
      Setup16 n (Bridge.conn (hN := hN)) p q c ε k t → (∃ w : Om n p q, w ∈ OmLe n p q c) →
      Concl hN p q c k t

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- B's conclusion on embedded manifolds for every subdivision carrying the data of a
`Morse.BrokenSetup` (no completeness, connectedness or `Setup16` needed). -/
def B_emb_BS : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (p q : Bridge.Sub hN) (c : ℝ) (m : ℕ) (t : ℕ → ℝ)
    (BS : Morse.BrokenSetup hN (Bridge.incl hN p) (Bridge.incl hN q) c m),
    (∀ i : Fin (m + 2), BS.t i = t i) → Concl hN p q c (m + 1) t

/-- **A gives B's conclusion on embedded manifolds for `BrokenSetup` subdivisions**: A's local
smooth representatives of `E'` (`exists_smooth_energy'`) give a function on `(↥N)^m` smooth for the
product model; A's `isCompact_sublevel` gives the compactness of `B^a` (as the image of a compact
set of break points under the continuous broken-geodesic map); the formula of p. 90 is formula (∗)
(`energy_path`) with `ρ = riemDist`; Lemma 16.1 and the continuity of `pathP`, `nodeVal` are used
from outside the item. -/
theorem A_to_B_emb_BS : A → B_emb_BS := by
  intro hA V _ _ _ W _ _ _ n N hN p q c m t BS hBt
  exact Emb.thm162 BS hBt BS.continuous_nodeVal BS.continuous_pathP
    (fun y hy => hA.2.1 BS hy) (fun a ha => hA.2.2.2 BS ha)

/-- **The gap**, as a statement: on a complete connected `↥N`, B's data (`Setup16`: Milnor's `ε`
with the conclusion `ShortGood` of Lemma 10.8 on `S`, `t_{i+1} − t_i < ε²/c`) carry a
`Morse.BrokenSetup` with the same subdivision. Not proved (and not expected to follow from
`ShortGood`: `BrokenSetup` also asks for a normal radius `≥ δ` at every point of `S`, `IsShortJoin`
on an open set of `V × V`, and `c (t_{i+1} − t_i) < δ²`). -/
def Gap16 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
    ∀ (p q : Bridge.Sub hN) (c ε : ℝ) (k : ℕ) (t : ℕ → ℝ),
      Setup16 n (Bridge.conn (hN := hN)) p q c ε k t → (∃ w : Om n p q, w ∈ OmLe n p q c) →
      ∃ (m : ℕ) (BS : Morse.BrokenSetup hN (Bridge.incl hN p) (Bridge.incl hN q) c m),
        k = m + 1 ∧ ∀ i : Fin (m + 2), BS.t i = t i

/-- **A and the gap give B on embedded manifolds.** -/
theorem A_to_B_emb_of_gap : A → Gap16 → B_emb := by
  intro hA hgap V _ _ _ W _ _ _ n N hN _ hmc p q c ε k t hS hne
  obtain ⟨m, BS, rfl, hBt⟩ := hgap V W n N hN hmc p q c ε k t hS hne
  exact A_to_B_emb_BS hA V W n N hN p q c m t BS hBt

#rt_check RoundTrip.V10_6.A_to_B_emb_BS [Morse.contMDiffAt_of_locally_eq, Morse.BrokenSetup.exists_smooth_energy', Morse.BrokenSetup.contMDiff_energy', Morse.BrokenSetup.isCompact_sublevel]
#rt_check RoundTrip.V10_6.A_to_B_emb_of_gap [Morse.contMDiffAt_of_locally_eq, Morse.BrokenSetup.exists_smooth_energy', Morse.BrokenSetup.contMDiff_energy', Morse.BrokenSetup.isCompact_sublevel]
#rt_overlap RoundTrip.V10_6.A_to_B_emb_BS [Morse.contMDiffAt_of_locally_eq, Morse.BrokenSetup.exists_smooth_energy', Morse.BrokenSetup.contMDiff_energy', Morse.BrokenSetup.isCompact_sublevel]

end RoundTrip.V10_6
