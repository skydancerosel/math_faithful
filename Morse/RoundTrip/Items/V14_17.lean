import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V14_17

open Matrix
open scoped Morse.MatrixInner

namespace RoundTrip.V14_17

/-- The project's statement (universes of `ι` instantiated at `0`; `minVel`, `minPaths`, `expPath`,
`PathSp` are vocabulary; the defs `minPathsHomotopyEquiv`, `minVelHomeomorph` read as `Nonempty` of their
types). On the project's embedded `SU(2m) ⊆ M_{2m}(ℂ)` (`card ι = 2m`, induced metric; `Ω` = `PathSp` with
Milnor's metric `d`, `Ω^d = minPaths` = the paths of least energy): `exp(A/2) = A/π` for `A ∈ minVel`;
`E ≥ (π√(2m))²` on `Ω(I, −I)`; `t ↦ exp tA` (`A ∈ minVel`) has least energy, and every least-energy path
agrees on `[0,1]` with one of them; `A ↦ (t ↦ exp tA)` is continuous; `minVel ι ≃ Ω^d` up to homotopy, and
`minVel ι ≃ₜ` the separation quotient of `Ω^d`. -/
def A : Prop :=
  type_of% @Morse.exp_half_smul_of_mem_minVel.{0} ∧ type_of% @Morse.pi_sq_le_energy.{0} ∧
    type_of% @Morse.expPath_mem_minPaths.{0} ∧ type_of% @Morse.exists_minVel_of_mem_minPaths.{0} ∧
    type_of% @Morse.continuous_expPath.{0} ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}, Fintype.card ι = 2 * m →
      Nonempty (ContinuousMap.HomotopyEquiv (Morse.minVel ι)
        (Morse.minPaths (Matrix.specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)))) ∧
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}, Fintype.card ι = 2 * m →
      Nonempty (Morse.minVel ι ≃ₜ SeparationQuotient
        (Morse.minPaths (Matrix.specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1))))

theorem A_holds : A :=
  ⟨@Morse.exp_half_smul_of_mem_minVel, @Morse.pi_sq_le_energy, @Morse.expPath_mem_minPaths,
    @Morse.exists_minVel_of_mem_minPaths, @Morse.continuous_expPath,
    fun hcard => ⟨Morse.minPathsHomotopyEquiv hcard⟩, fun hcard => ⟨Morse.minVelHomeomorph hcard⟩⟩

/-! Neither direction is proved (see `V14_17.json`).

* `A → B` fails genuinely: `B` quantifies over every abstract `M` with an isometric embedding `ψ` onto
  `SU(2m)` (transport along `ψ` of `ρ`, `Ω`, the energy and Milnor's `d`-topology is not formalized). On the
  embedded `SU(2m)` (`Bridge.Sub`, `ψ` = inclusion) it holds: `A_to_B_emb` below, by the `τ`/`λ` dictionary
  of `Items/V10_19.lean`/`Items/V13_6.lean` between the blind `Ω^d` (`d`-topology) and `PathSp`, with
  `ρ(I,−I) = π√(2m)` (`riemDist_one_neg_one`), `energy_expPath` and `lemma_23_1` from outside the item.
* `B → A` fails genuinely: `B` only asserts the existence of mutually inverse continuous maps between
  `Ω^d` and `G_m(ℂ^{2m})`; it says nothing about `exp(A/2) = A/π`, the energy bound, which paths are minimal
  (`exists_minVel_of_mem_minPaths`, `expPath_mem_minPaths`) or the specific map `A ↦ exp tA`. -/


/-! ## The embedded special case

Dictionary for the blind `Ω`, its `d`-topology and the energy, copied from `Items/V13_6.lean` (itself from
`Items/V10_19.lean`); the `SU(n)` model (`Bridge.Sub` of `isSliceRn isSliceSubmanifold_specialUnitaryGroup`,
`ψ` the inclusion) copied from `Items/V14_14.lean`; `Grass = grassmannian` from `Items/V14_16.lean`. -/

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- The arc length `s(t) = ∫₀ᵗ ‖γ'‖` of a piecewise smooth path has derivative `‖γ'(t)‖` off a
finite set of `(0, 1)`. -/
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

/-- **Dictionary: `ds/dt`.** The blind `ds/dt` (derivative of the blind arc length) of a path in
`N` is the project's speed `‖(incl ∘ w)'‖`, off a finite subset of `(0, 1)`. -/
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

/-- **Dictionary: the `L²` part.** -/
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

/-- Two paths of `Ω(N; p, q)` are at finite uniform distance (both stay within their lengths of
`p`). -/
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

/-- A blind path of `Ω(↥N; p, q)` is, in `V`, a project path of `Ω(N; p, q)`. -/
theorem mem_pathSpace {p q : Bridge.Sub hN} {w : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) :
    incl hN ∘ w ∈ Morse.pathSpace N (incl hN p) (incl hN q) :=
  ⟨isPiecewiseSmooth_of_isPW hw.1, fun t _ => (w t).2, congrArg (incl hN) hw.2.1,
    congrArg (incl hN) hw.2.2⟩

/-- The project path `incl ∘ w` of a blind path, as an element of `Morse.PathSp N p q`. -/
def pt {p q : Bridge.Sub hN} {w : ℝ → Bridge.Sub hN} (hw : InOmega (n := n) p q w) :
    Morse.PathSp N (incl hN p) (incl hN q) :=
  ⟨incl hN ∘ w, mem_pathSpace hw⟩

/-- **Dictionary: the uniform part.** -/
theorem iSup_rho_eq {p q : Bridge.Sub hN} {w w' : ℝ → Bridge.Sub hN}
    (hw : InOmega (n := n) p q w) (hw' : InOmega (n := n) p q w') :
    (⨆ t : Icc (0 : ℝ) 1, rho (n := n) (w t) (w' t)) =
      (Morse.PathSp.supDist N (incl hN ∘ w) (incl hN ∘ w')).toReal := by
  have hne := supDist_ne_top (mem_pathSpace hw) (mem_pathSpace hw')
  rw [Morse.PathSp.supDist, iSup_subtype', ENNReal.toReal_iSup ?_]
  · exact iSup_congr fun t => rho_eq _ _
  · intro t
    exact ne_top_of_le_ne_top hne (Morse.PathSp.riemDist_le_supDist t.2)

/-- **Dictionary: Milnor's metric.** For blind paths `w, w'` of `Ω(↥N; p, q)`, the blind `d(w, w')`
is the project's `edist` of `incl ∘ w, incl ∘ w'` in `Morse.PathSp N p q`. -/
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


/-- The blind energy of a path in `N` is the project's energy of `incl ∘ w`. -/
theorem efun_eq (w : ℝ → Bridge.Sub hN) : Efun (n := n) w = Morse.energy (incl hN ∘ w) 0 1 :=
  energy_eq w 0 1

/-- A project path of `Ω(N; p, q)` lifts to a blind path of `Ω(↥N; p', q')` agreeing with it on
`[0, 1]`. -/
theorem inOmega_lift {p' q' : Bridge.Sub hN} {c : ℝ → V}
    (hc : c ∈ Morse.pathSpace N (incl hN p') (incl hN q')) :
    InOmega (n := n) p' q' (lift c p') ∧ EqOn (incl hN ∘ lift c p') c (Icc 0 1) := by
  have heq : EqOn (incl hN ∘ lift c p') c (Icc 0 1) := fun t ht => incl_lift p' (hc.2.1 t ht)
  refine ⟨⟨isPW_lift hc.1 hc.2.1 p', ?_, ?_⟩, heq⟩
  · apply Subtype.ext
    exact (heq ⟨le_rfl, zero_le_one⟩).trans hc.2.2.1
  · apply Subtype.ext
    exact (heq ⟨zero_le_one, le_rfl⟩).trans hc.2.2.2


section Omega

variable {p q : Bridge.Sub hN}

/-- The blind `Ω(↥N; p, q)` maps to the project's `Ω(N; p, q)` by `w ↦ incl ∘ w`. -/
def tau (w : Om n p q) : Morse.PathSp N (incl hN p) (incl hN q) := pt w.2

theorem dOm_self (w : Om n p q) : dOm (n := n) w.1 w.1 = 0 := by
  have h := edist_eq w.2 w.2
  rw [edist_self] at h
  have h0 := dOm_nonneg w.2 w.2
  have := ENNReal.ofReal_eq_zero.1 h.symm
  linarith

/-- **The blind topology of `Ω` (generated by Milnor's `d`-balls) is induced by `τ`** from the
project's pseudo-emetric topology on `Ω(N; p, q)`. -/
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
      show edist (pt w.2) (pt w'.2) < ε
      rw [edist_eq w.2 w'.2]
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
      exact hε.trans (dOm_nonneg w.2 w'.2)
    · refine isOpen_induced_iff.2
        ⟨Metric.eball (tau w) (ENNReal.ofReal ε), Metric.isOpen_eball, ?_⟩
      ext w'
      show edist (tau w') (tau w) < ENNReal.ofReal ε ↔ dOm (n := n) w.1 w'.1 < ε
      rw [edist_comm]
      show edist (pt w.2) (pt w'.2) < _ ↔ _
      rw [edist_eq w.2 w'.2, ENNReal.ofReal_lt_ofReal_iff hε]

theorem isInducing_tau : IsInducing (tau (n := n) (p := p) (q := q)) := ⟨omTopology_eq⟩

end Omega

section HE

variable {p q : Bridge.Sub hN}

/-- `τ` as a continuous map. -/
def tauC : C(Om n p q, Morse.PathSp N (incl hN p) (incl hN q)) :=
  ⟨tau, isInducing_tau.continuous⟩

/-- Lifting a project path to a blind one (`Bridge.lift`). -/
noncomputable def lam (γ : Morse.PathSp N (incl hN p) (incl hN q)) : Om n p q :=
  ⟨lift (γ : ℝ → V) p, (inOmega_lift γ.2).1⟩

theorem tau_lam_insep (γ : Morse.PathSp N (incl hN p) (incl hN q)) :
    Inseparable (tau (lam (n := n) γ)) γ :=
  EMetric.inseparable_iff.2 (Morse.PathSp.edist_eq_zero_of_eqOn (inOmega_lift γ.2).2)

theorem lam_tau_insep (w : Om n p q) : Inseparable (lam (n := n) (tau w)) w :=
  isInducing_tau.inseparable_iff.1 (EMetric.inseparable_iff.2
    (Morse.PathSp.edist_eq_zero_of_eqOn (inOmega_lift (tau w).2).2))

theorem continuous_lam : Continuous (lam (n := n) (p := p) (q := q)) := by
  refine isInducing_tau.continuous_iff.2 ?_
  exact (continuous_congr_of_inseparable tau_lam_insep).2 continuous_id

end HE

end Emb

namespace SUEmb

open RoundTrip.Bridge
open scoped Morse.MatrixInner

section Model

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A linear equivalence `Z ≃ ℝᵐ`, `m = dim Z` (copied from `Items/V7_28.lean`). -/
def eZ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] :
    Z ≃L[ℝ] Bridge.Rn (finrank ℝ Z) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- A slice chart modelled on `Z`, read in `ℝᵐ` (copied from `Items/V7_28.lean`). -/
def chartRn (sc : Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
    Milnor.SliceChart 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W N where
  φ := sc.φ.trans ((eZ Z).prodCongr (ContinuousLinearEquiv.refl ℝ W)).toDiffeomorph.toPartialDiffeomorph
  x₀ := sc.x₀
  x₀_mem := sc.x₀_mem
  x₀_source := ⟨sc.x₀_source, trivial⟩
  slice := fun p hp => sc.slice p hp.1

/-- A slice submanifold modelled on `Z` is one modelled on `ℝᵐ` (copied from `Items/V7_28.lean`). -/
theorem isSliceRn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W N :=
  fun p hp => ⟨chartRn (hN p hp).choose, ⟨(hN p hp).choose_spec, trivial⟩⟩

/-- ... with the same tangent spaces (copied from `Items/V7_28.lean`). -/
theorem tangentSubspace_rn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) :
    Morse.tangentSubspace (isSliceRn hN) q = Morse.tangentSubspace hN q := by
  obtain ⟨sc, hsc⟩ := hN q q.2
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam (isSliceRn hN) (chartRn sc) ⟨hsc, trivial⟩,
    Morse.tangentSubspace_eq_range_fderiv_sliceParam hN sc hsc]
  have e1 : Morse.sliceParam (chartRn sc) = Morse.sliceParam sc ∘ (eZ Z).symm := rfl
  have e2 : ((chartRn sc).φ q).1 = eZ Z (sc.φ q).1 := rfl
  rw [e1, e2, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearEquiv.symm_apply_apply]
  exact LinearMap.range_comp_of_range_eq_top
    ((fderiv ℝ (Morse.sliceParam sc) (sc.φ q).1 : Z →L[ℝ] V) : Z →ₗ[ℝ] V)
    (LinearMap.range_eq_top.2 (eZ Z).symm.surjective)

/-- Geodesics only depend on the tangent spaces. -/
theorem isGeodesicOn_rn_iff (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V}
    {s : Set ℝ} : Morse.IsGeodesicOn (isSliceRn hN) γ s ↔ Morse.IsGeodesicOn hN γ s :=
  ⟨fun h => ⟨h.isOpen, h.mem, h.contDiffOn, fun t ht => by
      have := h.normal t ht
      rwa [tangentSubspace_rn] at this⟩,
    fun h => ⟨h.isOpen, h.mem, h.contDiffOn, fun t ht => by
      have := h.normal t ht
      rwa [← tangentSubspace_rn hN] at this⟩⟩

end Model

variable (n : ℕ) [NeZero n]

/-- `SU(n)` as a slice submanifold modelled on `ℝᵈ`, `d = dim 𝔰𝔲(n)`. -/
abbrev hR := isSliceRn (Morse.isSliceSubmanifold_specialUnitaryGroup (ι := Fin n))

/-- The dimension `d`. -/
abbrev dd : ℕ := finrank ℝ (Morse.specialSkewHermitian (Fin n)).toSubmodule

/-- `SU(n)` as an abstract Riemannian manifold (induced metric). -/
abbrev SUM := Bridge.Sub (hR n)

/-- The inclusion `ψ : SU(n) → Mₙ(ℂ)`, read in the blind file's `Fin n → Fin n → ℂ`. -/
def ψ : SUM n → Mat n := incl (hR n)

variable {n}

theorem ψ_eq (x : SUM n) : ψ n x = incl (hR n) x := rfl

/-- `id : (Mₙ(ℂ), Frobenius) → (Fin n → Fin n → ℂ, sup norm)` as a continuous linear map. -/
def idFP : Mat n →L[ℝ] (Fin n → Fin n → ℂ) :=
  ContinuousLinearMap.id ℝ (Mat n)

theorem dMat_ψ (x : SUM n) (v : TangentSpace 𝓘(ℝ, Rn (dd n)) x) :
    dMat (n := dd n) n (ψ n) x v = D (hR n) x v := by
  have h : ψ n = (idFP (n := n)) ∘ incl (hR n) := rfl
  unfold dMat
  rw [h, mfderiv_comp x (idFP (n := n)).mdifferentiableAt
    (contMDiff_incl.mdifferentiableAt (by simp)), ContinuousLinearMap.mfderiv_eq]
  rfl

theorem re_trace_swap (X Y : Mat n) :
    RCLike.re (trace (Xᴴ * Y)) = (trace (X * Yᴴ)).re := by
  have h1 : trace (Xᴴ * Y) = star (trace (Yᴴ * X)) := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [h1, Matrix.trace_mul_comm Yᴴ X]
  simp

/-- **`ψ` is an `IsSUModel`.** -/
theorem isSUModel_ψ : IsSUModel (n := dd n) n (ψ n) := by
  refine ⟨(idFP (n := n)).contMDiff.comp contMDiff_incl, Topology.IsEmbedding.subtypeVal, Subtype.range_val, fun x v w => ?_⟩
  rw [inner_eq, Morse.inner_def, dMat_ψ, dMat_ψ]
  exact re_trace_swap _ _

end SUEmb

/-- For an idempotent matrix, the trace is the rank. -/
theorem trace_eq_rank {k : ℕ} {P : Mat k} (hP : P * P = P) : P.trace = (P.rank : ℂ) := by
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  rw [← Matrix.trace_toLin'_eq, (LinearMap.IsIdempotentElem.isProj_range _ he).trace, Matrix.rank]
  rfl

theorem grass_eq (m : ℕ) : Grass (2 * m) m = Morse.grassmannian (Fin (2 * m)) m := by
  ext P
  simp only [Grass, Morse.grassmannian, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [trace_eq_rank h2, h3]⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [trace_eq_rank h2] at h3
    exact_mod_cast h3



open SUEmb in
/-- `B` for `M = SU(2m)` (`m ≥ 1`) with the induced metric (`Bridge.Sub`, model `ℝᵈ`), `ψ` the inclusion;
connectedness of `SU(2m)` (an instance argument of `B`, formalized neither in Mathlib nor in the project) is
kept as a hypothesis. -/
def B_emb : Prop :=
  ∀ (m : ℕ) [NeZero (2 * m)], ConnectedSpace (SUM (2 * m)) →
    ∀ p q : SUM (2 * m), ψ (2 * m) p = 1 → ψ (2 * m) q = -1 →
      ∃ (Φ : C(↥(OmD (dd (2 * m)) p q), ↥(Grass (2 * m) m)))
        (Ψ : C(↥(Grass (2 * m) m), ↥(OmD (dd (2 * m)) p q))),
        (∀ P, Φ (Ψ P) = P) ∧ ∀ w, Set.EqOn (Ψ (Φ w)).1.1 w.1.1 (Set.Icc 0 1)

theorem B_to_B_emb : B → B_emb := by
  intro hB m _ _ p q hp hq
  exact hB m (SUEmb.dd (2 * m)) (SUEmb.SUM (2 * m)) (SUEmb.ψ (2 * m)) SUEmb.isSUModel_ψ p q hp hq

namespace EmbSU

open SUEmb RoundTrip.Bridge

variable {m : ℕ} [NeZero (2 * m)] {p q : SUM (2 * m)}

/-- `Ω(SU(2m); I, −I)` of the project, as `N`. -/
abbrev N2 (m : ℕ) : Set (Mat (2 * m)) := (specialUnitaryGroup (Fin (2 * m)) ℂ : Set (Mat (2 * m)))

/-- Re-reading a path of `Ω(N; a, b)` as one of `Ω(N; a', b')` (`a = a'`, `b = b'`): an isometry. -/
def castP {a b a' b' : Mat (2 * m)} (ha : a = a') (hb : b = b') (γ : Morse.PathSp (N2 m) a b) :
    Morse.PathSp (N2 m) a' b' :=
  ⟨γ.1, ha ▸ hb ▸ γ.2⟩

theorem continuous_castP {a b a' b' : Mat (2 * m)} (ha : a = a') (hb : b = b') :
    Continuous (castP ha hb) := by
  subst ha hb
  exact continuous_id

theorem continuous_apply_half' {a b : Mat (2 * m)} :
    Continuous fun γ : Morse.PathSp (N2 m) a b => (γ : ℝ → Mat (2 * m)) (1 / 2) :=
  (continuous_eval_const (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).comp
    (continuous_subtype_val.comp Morse.PathSp.continuous_toPathC)

/-- The velocity `π·w(1/2)` of a blind path. -/
def velW (w : Om (dd (2 * m)) p q) : Mat (2 * m) :=
  (Real.pi : ℝ) • incl (hR (2 * m)) (w.1 (1 / 2))

theorem continuous_velW : Continuous (velW (m := m) (p := p) (q := q)) :=
  ((continuous_apply_half'.comp Emb.isInducing_tau.continuous)).const_smul (Real.pi : ℝ)

end EmbSU

open SUEmb EmbSU RoundTrip.Bridge in
/-- `A` (its first five conjuncts) gives `B_emb`: `Φ w = lemma_23_1 (π·w(1/2))`, `Ψ P = (t ↦ exp(t·A_P))`
lifted to `SU(2m)`, `A_P = lemma_23_1⁻¹ P`. Outside the item: `riemDist_one_neg_one` (`ρ(I,−I) = π√(2m)`),
`energy_expPath`, `lemma_23_1`. -/
theorem A_to_B_emb : A → B_emb := by
  rintro ⟨hhalf, hpi, -, hex, hcont, -, -⟩ m _ _ p q hp hq
  classical
  have hcard : Fintype.card (Fin (2 * m)) = 2 * m := Fintype.card_fin _
  have hp' : incl (hR (2 * m)) p = 1 := hp
  have hq' : incl (hR (2 * m)) q = -1 := hq
  -- `ρ(p, q)² = (π√(2m))²`
  have hρ : dPQ (dd (2 * m)) p q = (Real.pi * Real.sqrt (2 * m)) ^ 2 := by
    show rho (n := dd (2 * m)) p q ^ 2 = _
    rw [show rho (n := dd (2 * m)) p q = BridgePrelude.rho (n := dd (2 * m)) p q from rfl,
      rho_eq, hp', hq', Morse.riemDist_one_neg_one hcard,
      ENNReal.toReal_ofReal (by positivity)]
  have hpath : ∀ w : Om (dd (2 * m)) p q,
      incl (hR (2 * m)) ∘ w.1 ∈ Morse.pathSpace (N2 m) 1 (-1) := fun w => by
    have := Emb.mem_pathSpace w.2
    rwa [hp', hq'] at this
  -- a path of `Ω^d` has least energy, hence is `exp(t A)`, `A = π w(1/2) ∈ minVel`
  have hminP : ∀ w : ↥(OmD (dd (2 * m)) p q),
      (⟨_, hpath w.1⟩ : Morse.PathSp (N2 m) 1 (-1)) ∈ Morse.minPaths (N2 m) 1 (-1) := by
    intro w γ'
    have h1 : Efun (n := dd (2 * m)) w.1.1 ≤ dPQ (dd (2 * m)) p q := w.2
    rw [Emb.efun_eq, hρ] at h1
    exact h1.trans (hpi hcard γ'.mem)
  have hvel : ∀ w : ↥(OmD (dd (2 * m)) p q), velW w.1 ∈ Morse.minVel (Fin (2 * m)) ∧
      EqOn (incl (hR (2 * m)) ∘ w.1.1) (fun s : ℝ => NormedSpace.exp (s • velW w.1)) (Icc 0 1) := by
    intro w
    obtain ⟨A, hA, heq⟩ := hex hcard (hminP w)
    have hv : velW w.1 = A := by
      have h1 : incl (hR (2 * m)) (w.1.1 (1 / 2)) = NormedSpace.exp ((1 / 2 : ℝ) • A) :=
        heq ⟨by norm_num, by norm_num⟩
      rw [velW, h1, hhalf hA, smul_smul, mul_inv_cancel₀ Real.pi_ne_zero, one_smul]
    rw [hv]
    exact ⟨hA, heq⟩
  -- `Φ`
  obtain ⟨Φ0, hΦ0⟩ : ∃ Φ0 : C(↥(OmD (dd (2 * m)) p q), Morse.minVel (Fin (2 * m))),
      ∀ w, (Φ0 w : Mat (2 * m)) = velW w.1 :=
    ⟨⟨fun w => ⟨velW w.1, (hvel w).1⟩,
      ((continuous_velW (m := m) (p := p) (q := q)).comp continuous_subtype_val).subtype_mk
        fun w => (hvel w).1⟩,
      fun _ => rfl⟩
  have hΦm : ∀ w, ((Morse.lemma_23_1 hcard) (Φ0 w) : Mat (2 * m)) ∈ Grass (2 * m) m := fun w => by
    rw [grass_eq]; exact ((Morse.lemma_23_1 hcard) (Φ0 w)).2
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : C(↥(OmD (dd (2 * m)) p q), ↥(Grass (2 * m) m)),
      ∀ w, (Φ w : Mat (2 * m)) = ((Morse.lemma_23_1 hcard) (Φ0 w) : Mat (2 * m)) :=
    ⟨⟨fun w => ⟨((Morse.lemma_23_1 hcard) (Φ0 w) : Mat (2 * m)), hΦm w⟩,
      ((continuous_subtype_val.comp ((Morse.lemma_23_1 hcard).continuous.comp
        Φ0.continuous))).subtype_mk hΦm⟩, fun _ => rfl⟩
  -- `Ψ`
  have hGm : ∀ P : ↥(Grass (2 * m) m), P.1 ∈ Morse.grassmannian (Fin (2 * m)) m := fun P => by
    rw [← grass_eq]; exact P.2
  obtain ⟨G, hG⟩ : ∃ G : C(↥(Grass (2 * m) m), Morse.minVel (Fin (2 * m))),
      ∀ P, ((Morse.lemma_23_1 hcard) (G P) : Mat (2 * m)) = P.1 :=
    ⟨⟨fun P => (Morse.lemma_23_1 hcard).symm ⟨P.1, hGm P⟩,
      (Morse.lemma_23_1 hcard).symm.continuous.comp (continuous_subtype_val.subtype_mk hGm)⟩,
      fun P => by
        show ((Morse.lemma_23_1 hcard) ((Morse.lemma_23_1 hcard).symm _) : Mat (2 * m)) = _
        rw [Homeomorph.apply_symm_apply]⟩
  let γP : ↥(Grass (2 * m) m) → Morse.PathSp (N2 m) (incl (hR (2 * m)) p) (incl (hR (2 * m)) q) :=
    fun P => castP hp'.symm hq'.symm (Morse.expPath (G P))
  have hγP : Continuous γP :=
    (continuous_castP _ _).comp ((hcont hcard).comp G.continuous)
  have hΨmem : ∀ P, Emb.lam (n := dd (2 * m)) (γP P) ∈ OmD (dd (2 * m)) p q := by
    intro P
    show Efun (n := dd (2 * m)) (Emb.lam (n := dd (2 * m)) (γP P)).1 ≤ dPQ (dd (2 * m)) p q
    rw [Emb.efun_eq, hρ, ← Morse.energy_expPath hcard (G P)]
    exact (Morse.energy_congr fun t ht => (Emb.inOmega_lift (γP P).2).2 ht).le
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : C(↥(Grass (2 * m) m), ↥(OmD (dd (2 * m)) p q)),
      ∀ P, ∀ t ∈ Icc (0 : ℝ) 1, incl (hR (2 * m)) ((Ψ P).1.1 t) =
        NormedSpace.exp (t • (G P : Mat (2 * m))) :=
    ⟨⟨fun P => ⟨Emb.lam (γP P), hΨmem P⟩, (Emb.continuous_lam.comp hγP).subtype_mk hΨmem⟩,
      fun P t ht => (Emb.inOmega_lift (γP P).2).2 ht⟩
  refine ⟨Φ, Ψ, fun P => ?_, fun w t ht => ?_⟩
  · -- `Φ (Ψ P) = P`
    have hv : Φ0 (Ψ P) = G P := by
      apply Subtype.ext
      rw [hΦ0, velW, hΨ P _ ⟨by norm_num, by norm_num⟩, hhalf (G P).2, smul_smul,
        mul_inv_cancel₀ Real.pi_ne_zero, one_smul]
    apply Subtype.ext
    rw [hΦ, hv, hG]
  · -- `Ψ (Φ w) = w` on `[0, 1]`
    have h1 : G (Φ w) = Φ0 w := by
      apply (Morse.lemma_23_1 hcard).injective
      apply Subtype.ext
      rw [hG, hΦ]
    apply Subtype.ext
    show incl (hR (2 * m)) ((Ψ (Φ w)).1.1 t) = incl (hR (2 * m)) (w.1.1 t)
    rw [hΨ _ t ht, h1, hΦ0]
    exact ((hvel w).2 ht).symm

#rt_check RoundTrip.V14_17.A_to_B_emb [Morse.exp_half_smul_of_mem_minVel, Morse.pi_sq_le_energy, Morse.expPath_mem_minPaths, Morse.exists_minVel_of_mem_minPaths, Morse.continuous_expPath, Morse.minPathsHomotopyEquiv, Morse.minVelHomeomorph]
#rt_check RoundTrip.V14_17.B_to_B_emb [Morse.exp_half_smul_of_mem_minVel, Morse.pi_sq_le_energy, Morse.expPath_mem_minPaths, Morse.exists_minVel_of_mem_minPaths, Morse.continuous_expPath, Morse.minPathsHomotopyEquiv, Morse.minVelHomeomorph]
#rt_overlap RoundTrip.V14_17.A_to_B_emb [Morse.exp_half_smul_of_mem_minVel, Morse.pi_sq_le_energy, Morse.expPath_mem_minPaths, Morse.exists_minVel_of_mem_minPaths, Morse.continuous_expPath, Morse.minPathsHomotopyEquiv, Morse.minVelHomeomorph]

end

end RoundTrip.V14_17
