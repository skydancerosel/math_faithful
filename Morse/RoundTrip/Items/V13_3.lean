import Morse
import RoundTrip.Check
import RoundTrip.Blind.V13_3
import RoundTrip.Bridge
import RoundTrip.EnergyC2

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval Topology.Homotopy

namespace RoundTrip.V13_3

/-- The project's statement (universes instantiated at `0`, including the index type `K`): for a
slice submanifold `N ⊆ V` (any model `Z`) and `p, q ∈ N`, if the closed `ρ`-balls about `p` are
compact, every unbroken geodesic from `p` to `q` which is not of least energy has index
(`formIndex` of `energyHessian`) `≥ λ₀`, and `Ω^d` (`Morse.minPaths`, the paths of least energy)
is a retract of an open neighbourhood in `Ω(N; p, q)`, then the inclusion `Ω^d → Ω` induces
bijections `π_K(Ω^d, γ) → π_K(Ω, γ)` for `|K| + 2 ≤ λ₀` and surjections for `|K| < λ₀`, at every
`γ ∈ Ω^d` (Mathlib's `HomotopyGroup K`, any finite `K`). -/
def A : Prop :=
  type_of% @Morse.theorem_22_1_bijective.{0,0,0,0} ∧ type_of% @Morse.theorem_22_1_surjective.{0,0,0,0}

theorem A_holds : A := ⟨@Morse.theorem_22_1_bijective, @Morse.theorem_22_1_surjective⟩

/-! Neither `A → B` nor `B → A` is proved; see `V13_3.json`.

## The embedded special case: dictionary

Copied from `Items/V10_19.lean` (blind `Ω` ↔ `Morse.PathSp`), `Items/V9_7″.lean`
(`isGeodesic_lift_of`) and `Items/V7_29.lean` (`metricComplete_iff`). -/

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


/-! ### Topological dictionary for `Ω` and `Ω*` (new; as in Items/V10_15.lean) -/

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

/-- **The blind `Ω*` (continuous maps `I → ↥N`) is homeomorphic to the project's `PathC`**
(continuous maps `I → V` with values in `N`), both with the compact-open topology. -/
def sigma : OmStar p q ≃ₜ Morse.PathC N (incl hN p) (incl hN q) where
  toFun w := ⟨(⟨incl hN, continuous_subtype_val⟩ : C(Bridge.Sub hN, V)).comp w.1,
    fun t => (w.1 t).2, congrArg (incl hN) w.2.1, congrArg (incl hN) w.2.2⟩
  invFun γ := ⟨⟨fun t => (⟨(γ.1 : C(I, V)) t, γ.2.1 t⟩ : N), by fun_prop⟩,
    Subtype.ext γ.2.2.1, Subtype.ext γ.2.2.2⟩
  left_inv w := rfl
  right_inv γ := rfl
  continuous_toFun :=
    ((ContinuousMap.continuous_postcomp _).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine (ContinuousMap.isInducing_postcomp
      (⟨incl hN, continuous_subtype_val⟩ : C(Bridge.Sub hN, V))
      IsInducing.subtypeVal).continuous_iff.2 ?_
    exact continuous_subtype_val

theorem isInducing_sigma_val :
    IsInducing (fun w : OmStar p q => ((sigma w : Morse.PathC N _ _) : C(I, V))) :=
  IsInducing.subtypeVal.comp sigma.isInducing

end Omega

/-! ### Homotopy equivalence `Ω ≃ PathSp` (new) -/

/-- Two maps whose values are pointwise inseparable are homotopic. -/
theorem homotopic_of_inseparable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f g : C(X, Y)) (h : ∀ x, Inseparable (f x) (g x)) : f.Homotopic g := by
  classical
  refine ⟨{ toFun := fun z => if (z.1 : ℝ) = 0 then f z.2 else g z.2
            continuous_toFun := ?_
            map_zero_left := fun x => by simp
            map_one_left := fun x => by simp }⟩
  refine (continuous_congr_of_inseparable (g := fun z : I × X => g z.2) fun z => ?_).2
    (g.continuous.comp continuous_snd)
  split_ifs
  · exact h z.2
  · exact Inseparable.refl _

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

noncomputable def lamC : C(Morse.PathSp N (incl hN p) (incl hN q), Om n p q) := ⟨lam, continuous_lam⟩

theorem lam_tau_homotopic : ((lamC (n := n) (p := p) (q := q)).comp tauC).Homotopic
    (ContinuousMap.id _) :=
  homotopic_of_inseparable _ _ lam_tau_insep

theorem tau_lam_homotopic : ((tauC (n := n) (p := p) (q := q)).comp lamC).Homotopic
    (ContinuousMap.id _) :=
  homotopic_of_inseparable _ _ tau_lam_insep

/-- **The blind `Ω` and the project's `Ω(N; p, q)` are homotopy equivalent** via `τ`. -/
theorem isHomotopyEquiv_tau : Morse.IsHomotopyEquiv (tauC (n := n) (p := p) (q := q)) :=
  ⟨lamC, lam_tau_homotopic, tau_lam_homotopic⟩

theorem isHomotopyEquiv_lam : Morse.IsHomotopyEquiv (lamC (n := n) (p := p) (q := q)) :=
  Morse.IsHomotopyEquiv.of_inverse lam_tau_homotopic tau_lam_homotopic

end HE

theorem intv_Icc : RoundTrip.BridgePrelude.IsIntv (Icc (0 : ℝ) 1) :=
  ⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩

/-- A project geodesic on `(0, 1)`, smooth on `[0, 1]`, lifts to a blind geodesic on `[0, 1]`. -/
theorem isGeodesic_lift_of {c : ℝ → V} (q : Bridge.Sub hN) (hc : ContDiffOn ℝ ∞ c (Icc 0 1))
    (hcN : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ N) (hgeo : Morse.IsGeodesicOn hN c (Ioo 0 1)) :
    IsGeodesic (Bridge.conn (hN := hN)) (lift c q) (Icc 0 1) := by
  have uI : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have heq : EqOn (incl hN ∘ lift c q) c (Icc 0 1) := fun t ht => incl_lift q (hcN t ht)
  have hd : EqOn (derivWithin (incl hN ∘ lift c q) (Icc 0 1)) (derivWithin c (Icc 0 1))
      (Icc 0 1) := fun t ht => derivWithin_congr heq (heq ht)
  have hdd : EqOn (derivWithin (derivWithin (incl hN ∘ lift c q) (Icc 0 1)) (Icc 0 1))
      (derivWithin (derivWithin c (Icc 0 1)) (Icc 0 1)) (Icc 0 1) :=
    fun t ht => derivWithin_congr hd (hd ht)
  have hG : EqOn (fun t => Morse.prj hN (c t) (derivWithin (derivWithin c (Icc 0 1)) (Icc 0 1) t))
      0 (Icc 0 1) := by
    refine EqOn.of_subset_closure (s := Ioo 0 1) ?_ ?_ continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
    · intro t ht
      have hn : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
      have e1 : derivWithin c (Icc 0 1) =ᶠ[𝓝 t] deriv c := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
        exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
      simp only [Pi.zero_apply]
      rw [derivWithin_of_mem_nhds hn, e1.deriv_eq, Morse.prj_of_mem hN (hgeo.mem t ht)]
      exact hgeo.tanProj_deriv_deriv ht
    · exact (Morse.ContDiffOn.prj_comp hN hc hcN).continuousOn.clm_apply
        ((hc.derivWithin uI (m := ∞) (by simp)).derivWithin uI (m := ∞) (by simp)).continuousOn
  refine (isGeodesic_iff (c := lift c q) (s := Icc 0 1)).2 ⟨intv_Icc, hc.congr heq, fun t ht => ?_⟩
  rw [hdd ht]
  have := hG ht
  simp only [Pi.zero_apply, Morse.prj_of_mem hN (hcN t ht)] at this
  rw [lift_of_mem q (hcN t ht)]
  exact this


theorem riemDist_eq_ofReal_rho (hpre : IsPreconnected N) (p q : Bridge.Sub hN) :
    Morse.riemDist (N := N) (incl hN p) (incl hN q) = ENNReal.ofReal (rho (n := n) p q) := by
  have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
  rw [e, rho_eq]
  exact (ENNReal.ofReal_toReal (Morse.riemDist_ne_top hN hpre p.2 q.2)).symm

theorem rho_nonneg (p q : Bridge.Sub hN) : 0 ≤ rho (n := n) p q := by
  have e : rho (n := n) p q = RoundTrip.BridgePrelude.rho (n := n) p q := rfl
  rw [e, rho_eq]
  exact ENNReal.toReal_nonneg

theorem rho_lt_iff (hpre : IsPreconnected N) (p q : Bridge.Sub hN) {ε : ℝ} (hε : 0 < ε) :
    rho (n := n) p q < ε ↔ Morse.riemDist (N := N) (incl hN p) (incl hN q) < ENNReal.ofReal ε := by
  rw [riemDist_eq_ofReal_rho hpre, ENNReal.ofReal_lt_ofReal_iff hε]

theorem metricComplete_iff (hpre : IsPreconnected N) :
    MetricComplete n (Bridge.Sub hN) ↔ Morse.IsRiemComplete N := by
  constructor
  · intro h x hx hcau
    let x' : ℕ → Bridge.Sub hN := fun k => ⟨x k, hx k⟩
    obtain ⟨p, hp⟩ := h x' fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := hcau ε hε
      exact ⟨n₀, fun m hm k hk => (rho_lt_iff hpre _ _ hε).2 (hn₀ m hm k hk)⟩
    refine ⟨incl hN p, p.2, ?_⟩
    have ht : Tendsto (fun k => rho (n := n) (x' k) p) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨n₀, hn₀⟩ := hp ε hε
      refine ⟨n₀, fun m hm => ?_⟩
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (rho_nonneg _ _)]
      exact hn₀ m hm
    have := ENNReal.tendsto_ofReal ht
    rw [ENNReal.ofReal_zero] at this
    refine this.congr fun k => ?_
    exact (riemDist_eq_ofReal_rho hpre (x' k) p).symm
  · intro h x hcau
    obtain ⟨y, hy, hlim⟩ := h (fun k => incl hN (x k)) (fun k => (x k).2) fun ε hε => by
      obtain ⟨n₀, hn₀⟩ := hcau ε hε
      exact ⟨n₀, fun m hm k hk => (rho_lt_iff hpre _ _ hε).1 (hn₀ m hm k hk)⟩
    refine ⟨⟨y, hy⟩, fun ε hε => ?_⟩
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
      (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)))
    exact ⟨n₀, fun m hm => (rho_lt_iff hpre _ _ hε).2 (hn₀ m hm)⟩

/-! ### New glue -/

/-- B's `piMap` is the project's `homotopyGroupMap`. -/
theorem piMap_eq {K X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    piMap (N := K) f x = Morse.Homotopy.homotopyGroupMap f x := by
  funext c
  induction c using Quotient.inductionOn
  rfl

/-- An unbroken geodesic has constant speed, so `E = L²` on `[0, 1]`. -/
theorem energy_eq_sq {p q : V} {γ : ℝ → V} (hγ : γ ∈ Morse.pathSpace N p q)
    (hub : Morse.IsUnbrokenGeodesic hN γ) :
    Morse.energy γ 0 1 = Morse.pathLength γ 0 1 ^ 2 := by
  have h := (Morse.pathLength_sq_eq_energy_iff hγ.1).2 ⟨‖deriv γ (1 / 2)‖, fun t ht _ =>
    hub.2.norm_deriv_eq isPreconnected_Ioo ht ⟨by norm_num, by norm_num⟩⟩
  rw [h]; ring

/-- `ρ(x, y) ≤` the length of any piecewise smooth path from `x` to `y`. -/
theorem rho_le_arcLen {x y : Bridge.Sub hN} {pw : ℝ → Bridge.Sub hN} {a b : ℝ} (hab : a ≤ b)
    (hpw : IsPW (n := n) pw a b) (ha : pw a = x) (hb : pw b = y) :
    rho (n := n) x y ≤ arcLen (n := n) pw a b := by
  refine csInf_le ⟨0, ?_⟩ ⟨pw, a, b, hab, hpw, ha, hb, rfl⟩
  rintro L ⟨pth, a', b', hab', -, -, -, rfl⟩
  exact arcLen_nonneg hab'

/-- A project path of `Ω(N; p, q)` that is an unbroken geodesic, with a competitor of smaller
energy, lifts to a blind geodesic from `p` to `q` that is not minimal (`ℓ² ≤ E`, `E = L²`). -/
theorem not_isMinimal_lift {p q : Bridge.Sub hN} {γ : ℝ → V}
    (hγ : γ ∈ Morse.pathSpace N (incl hN p) (incl hN q)) (hub : Morse.IsUnbrokenGeodesic hN γ)
    (hnm : ∃ γ' ∈ Morse.pathSpace N (incl hN p) (incl hN q),
      Morse.energy γ' 0 1 < Morse.energy γ 0 1) :
    IsGeodPQ n (Bridge.conn (hN := hN)) p q (lift γ p) ∧
      ¬ IsMinimal (Bridge.conn (hN := hN)) (lift γ p) 0 1 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hgeo : IsGeodesic (Bridge.conn (hN := hN)) (lift γ p) (Icc 0 1) :=
    isGeodesic_lift_of p hub.1 hγ.2.1 hub.2
  have hgc : EqOn (incl hN ∘ lift γ p) γ (Icc 0 1) := fun t ht => incl_lift p (hγ.2.1 t ht)
  have hg0 : lift γ p 0 = p := Subtype.ext ((hgc h0).trans hγ.2.2.1)
  have hg1 : lift γ p 1 = q := Subtype.ext ((hgc h1).trans hγ.2.2.2)
  refine ⟨⟨hgeo, hg0, hg1⟩, ?_⟩
  rintro ⟨-, hmin⟩
  obtain ⟨γ', hγ', hlt⟩ := hnm
  have hpw := isPW_lift (n := n) hγ'.1 hγ'.2.1 p
  have h0' : lift γ' p 0 = lift γ p 0 := by
    rw [hg0]; exact Subtype.ext ((incl_lift p (hγ'.2.1 0 h0)).trans hγ'.2.2.1)
  have h1' : lift γ' p 1 = lift γ p 1 := by
    rw [hg1]; exact Subtype.ext ((incl_lift p (hγ'.2.1 1 h1)).trans hγ'.2.2.2)
  have hle := hmin _ 0 1 zero_le_one hpw h0' h1'
  have e1 : arcLen (n := n) (lift γ p) 0 1 = Morse.pathLength γ 0 1 :=
    (arcLen_eq _ 0 1).trans (pathLength_congr zero_le_one hgc)
  have e2 : arcLen (n := n) (lift γ' p) 0 1 = Morse.pathLength γ' 0 1 :=
    (arcLen_eq _ 0 1).trans (pathLength_congr zero_le_one
      (show EqOn (incl hN ∘ lift γ' p) γ' (Icc 0 1) from fun t ht => incl_lift p (hγ'.2.1 t ht)))
  rw [e1, e2] at hle
  have hsq := Morse.pathLength_sq_le_energy hγ'.1
  rw [energy_eq_sq hγ hub] at hlt
  have hL0 : 0 ≤ Morse.pathLength γ 0 1 := hγ.1.isAdmissible.pathLength_nonneg
  have := mul_self_le_mul_self hL0 hle
  nlinarith

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric, connected) with the induced
Levi-Civita connection `Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    MetricComplete n (Bridge.Sub hN) →
    ∀ (p q : Bridge.Sub hN) (l0 : ℕ), Hyp221 n (Bridge.conn (hN := hN)) p q l0 →
      ∀ x₀ : ↥(OmD n p q),
        (∀ i : ℕ, i + 2 ≤ l0 → Function.Bijective (piMap (N := Fin i) (inclD n p q) x₀)) ∧
        (∀ i : ℕ, i + 1 = l0 → Function.Surjective (piMap (N := Fin i) (inclD n p q) x₀)) ∧
        (∀ k : ℕ, k + 2 ≤ l0 → ∀ a b : π_ (k + 1) ↥(OmD n p q) x₀,
          piMap (inclD n p q) x₀ (a * b) = piMap (inclD n p q) x₀ a * piMap (inclD n p q) x₀ b)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **Hanner's theorem for `Ω^d`** (NOT proved, missing topology): on embedded complete manifolds,
if (the separation quotient of) B's `Ω^d` is a topological manifold, then the project's `Ω^d`
(`Morse.minPaths`) is a retract of an open neighbourhood in `Ω(N; p, q)` (A's hypothesis). -/
def Hanner : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (p q : Bridge.Sub hN),
    MetricComplete n (Bridge.Sub hN) → IsTopMfd (SeparationQuotient ↥(OmD n p q)) →
    ∃ O : Set (Morse.PathSp N (Bridge.incl hN p) (Bridge.incl hN q)), IsOpen O ∧
      Morse.minPaths N (Bridge.incl hN p) (Bridge.incl hN q) ⊆ O ∧
      ∃ ρ : Morse.PathSp N (Bridge.incl hN p) (Bridge.incl hN q) →
          Morse.PathSp N (Bridge.incl hN p) (Bridge.incl hN q),
        ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ Morse.minPaths N (Bridge.incl hN p) (Bridge.incl hN q)) ∧
        ∀ γ ∈ Morse.minPaths N (Bridge.incl hN p) (Bridge.incl hN q), ρ γ = γ

/-- **The index dictionary** (NOT proved; the V9_20/V9_22/V9_24 blocker): on embedded manifolds,
B's variational index `lam 1 γ` of a blind geodesic is the project's `formIndex` of
`energyHessian` of `incl ∘ γ`. -/
def LamEq : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    (p q : Bridge.Sub hN) (γ : ℝ → Bridge.Sub hN)
    (hc : Bridge.incl hN ∘ γ ∈ Morse.pathSpace N (Bridge.incl hN p) (Bridge.incl hN q)),
    IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1) →
    lam (n := n) 1 γ = Morse.formIndex (Morse.energyHessian hN hc)

open Emb RoundTrip.Bridge in
/-- **A, with Hanner's theorem and the index dictionary, implies B on embedded manifolds.**
Everything else is dictionary: completeness ⇒ compact balls (Hopf–Rinow), B's `Ω^d = E⁻¹[0, ρ²]`
is the project's `minPaths` (a minimal geodesic has `E = ρ²`, and `ρ² ≤ E` always), B's index
hypothesis on non-minimal blind geodesics gives A's on geodesics not of least energy, and the
blind `Ω^d ⊆ Ω` is homotopy equivalent, compatibly with the inclusions, to `minPaths ⊆ PathSp`. -/
theorem A_to_B_emb_of_hanner_lamEq : A → Hanner → LamEq → B_emb := by
  intro hA hH hL V _ _ _ W _ _ _ n N hN _ hcomp p q l0 ⟨hmfd, hidx⟩ x₀
  have hpre : IsPreconnected N :=
    isPreconnected_iff_preconnectedSpace.2 (inferInstanceAs (PreconnectedSpace (Bridge.Sub hN)))
  have hRC : Morse.IsRiemComplete N := (metricComplete_iff hpre).1 hcomp
  have hball : ∀ r : ℝ, IsCompact (Morse.closedRiemBall N (incl hN p) r) := fun r =>
    Morse.isCompact_closedRiemBall_of_isRiemComplete hN hpre hRC _ r
  -- `ρ(p,q)²` is the least energy
  obtain ⟨-, -, hmg, -⟩ := Morse.hopf_rinow_of_isRiemComplete hN hpre hRC
  obtain ⟨γ₀, ⟨-, ⟨s, hs, hgeo₀⟩, -⟩, hγ₀0, hγ₀1, hd⟩ := hmg p q
  have hcd₀ : ContDiffOn ℝ ∞ γ₀ (Icc 0 1) := hgeo₀.contDiffOn.mono hs
  have hmem₀ : γ₀ ∈ Morse.pathSpace N (incl hN p) (incl hN q) :=
    ⟨Morse.IsPiecewiseSmooth.of_contDiffOn hcd₀ zero_le_one le_rfl,
      fun t ht => hgeo₀.mem t (hs ht), hγ₀0, hγ₀1⟩
  have hub₀ : Morse.IsUnbrokenGeodesic hN γ₀ :=
    ⟨hcd₀, hgeo₀.mono isOpen_Ioo (Ioo_subset_Icc_self.trans hs)⟩
  have hrho : rho (n := n) p q = Morse.pathLength γ₀ 0 1 := by
    have h := rho_eq (hN := hN) p q
    rw [show Morse.riemDist (N := N) (incl hN p) (incl hN q) = _ from hd,
      ENNReal.toReal_ofReal hmem₀.1.isAdmissible.pathLength_nonneg] at h
    exact h
  have hE₀ : Morse.energy γ₀ 0 1 = rho (n := n) p q ^ 2 := by rw [hrho, energy_eq_sq hmem₀ hub₀]
  have hlow : ∀ c ∈ Morse.pathSpace N (incl hN p) (incl hN q),
      rho (n := n) p q ^ 2 ≤ Morse.energy c 0 1 := by
    intro c hc
    have h := Morse.riemDist_sq_le_energy (N := N) hc.1 hc.2.1
    rw [hc.2.2.1, hc.2.2.2, sub_zero, one_mul] at h
    exact (show rho (n := n) p q = _ from rho_eq p q) ▸ h
  have hOmD : ∀ w : Om n p q, w ∈ OmD n p q ↔
      tau w ∈ Morse.minPaths N (incl hN p) (incl hN q) := by
    intro w
    constructor
    · intro hw γ'
      show Morse.energy (incl hN ∘ w.1) 0 1 ≤ _
      rw [← efun_eq]
      exact hw.trans (hlow _ γ'.2)
    · intro hw
      show Efun (n := n) w.1 ≤ rho (n := n) p q ^ 2
      rw [efun_eq, ← hE₀]
      exact hw ⟨γ₀, hmem₀⟩
  -- A's index hypothesis, from B's and the dictionary
  have hidx' : ∀ γ (hγ : γ ∈ Morse.pathSpace N (incl hN p) (incl hN q)),
      Morse.IsUnbrokenGeodesic hN γ →
      (∃ γ' ∈ Morse.pathSpace N (incl hN p) (incl hN q), Morse.energy γ' 0 1 < Morse.energy γ 0 1) →
      (l0 : ℕ∞) ≤ Morse.formIndex (Morse.energyHessian hN hγ) := by
    intro γ hγ hub hnm
    obtain ⟨hPQ, hnmin⟩ := not_isMinimal_lift hγ hub hnm
    have h := hidx _ hPQ hnmin
    have hgc : EqOn (incl hN ∘ lift γ p) γ (Icc 0 1) := fun t ht => incl_lift p (hγ.2.1 t ht)
    have hc' : incl hN ∘ lift γ p ∈ Morse.pathSpace N (incl hN p) (incl hN q) :=
      ⟨isPiecewiseSmooth_of_isPW (isPW_lift hγ.1 hγ.2.1 p), fun t _ => (lift γ p t).2,
        (hgc ⟨le_rfl, zero_le_one⟩).trans hγ.2.2.1, (hgc ⟨zero_le_one, le_rfl⟩).trans hγ.2.2.2⟩
    have hub' : Morse.IsUnbrokenGeodesic hN (incl hN ∘ lift γ p) :=
      ⟨isSmoothCurve_iff.1 hPQ.1.2.1, isGeodesicOn_Ioo hPQ.1⟩
    rw [hL V W n N hN p q (lift γ p) hc' hPQ.1,
      Morse.formIndex_energyHessian_congr hc' hγ hub' hub hgc] at h
    exact h
  have hretr := hH V W n N hN p q hcomp hmfd
  -- the square `Ω^d ⊆ Ω` (blind) → `minPaths ⊆ PathSp` (project)
  let tauD : C(↥(OmD n p q), ↥(Morse.minPaths N (incl hN p) (incl hN q))) :=
    ⟨fun w => ⟨tau w.1, (hOmD w.1).1 w.2⟩,
      (isInducing_tau.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hlamD : ∀ γ : ↥(Morse.minPaths N (incl hN p) (incl hN q)),
      Emb.lam (p := p) (q := q) γ.1 ∈ OmD n p q := fun γ => (hOmD _).2 fun γ' => by
    show Morse.energy (incl hN ∘ lift (γ.1 : ℝ → V) p) 0 1 ≤ _
    rw [Morse.energy_congr (inOmega_lift (p' := p) (q' := q) γ.1.2).2]
    exact γ.2 γ'
  let lamD : C(↥(Morse.minPaths N (incl hN p) (incl hN q)), ↥(OmD n p q)) :=
    ⟨fun γ => ⟨Emb.lam (p := p) (q := q) γ.1, hlamD γ⟩,
      Continuous.subtype_mk (show Continuous fun γ : ↥(Morse.minPaths N (incl hN p) (incl hN q)) =>
        Emb.lam (p := p) (q := q) γ.1 from continuous_lam.comp continuous_subtype_val) hlamD⟩
  have hHE : Morse.IsHomotopyEquiv tauD :=
    ⟨lamD, homotopic_of_inseparable _ _ fun w =>
        Topology.IsInducing.subtypeVal.inseparable_iff.1 (lam_tau_insep w.1),
      homotopic_of_inseparable _ _ fun γ =>
        Topology.IsInducing.subtypeVal.inseparable_iff.1 (tau_lam_insep (p := p) (q := q) γ.1)⟩
  have key : ∀ (K : Type) [Fintype K] [DecidableEq K],
      Morse.Homotopy.homotopyGroupMap (N := K) tauC (inclD n p q x₀) ∘
          piMap (N := K) (inclD n p q) x₀ =
        Morse.Homotopy.homotopyGroupMap (N := K) (Morse.minPathsIncl N (incl hN p) (incl hN q))
          (tauD x₀) ∘ Morse.Homotopy.homotopyGroupMap (N := K) tauD x₀ := by
    intro K _ _
    rw [piMap_eq, ← Morse.Homotopy.homotopyGroupMap_comp, ← Morse.Homotopy.homotopyGroupMap_comp]
    rfl
  have hF : ∀ (K : Type) [Fintype K] [DecidableEq K],
      Bijective (Morse.Homotopy.homotopyGroupMap (N := K) tauC (inclD n p q x₀)) := fun K _ _ =>
    Morse.Homotopy.bijective_homotopyGroupMap_of_isHomotopyEquiv isHomotopyEquiv_tau _
  have hG : ∀ (K : Type) [Fintype K] [DecidableEq K],
      Bijective (Morse.Homotopy.homotopyGroupMap (N := K) tauD x₀) := fun K _ _ =>
    Morse.Homotopy.bijective_homotopyGroupMap_of_isHomotopyEquiv hHE _
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun k _ a b => ?_⟩
  · have hH' := hA.1 hN p.2 q.2 hball hidx' hretr (K := Fin i) (by simpa using hi) (tauD x₀)
    have hcomp' := key (Fin i)
    exact (Bijective.of_comp_iff' (hF (Fin i)) _).1 (hcomp' ▸ hH'.comp (hG (Fin i)))
  · have hH' := hA.2 hN p.2 q.2 hball hidx' hretr (K := Fin i) (by simp; omega) (tauD x₀)
    have hcomp' := key (Fin i)
    intro z
    obtain ⟨y, hy⟩ := (hH'.comp (hG (Fin i)).2) (Morse.Homotopy.homotopyGroupMap (N := Fin i) tauC
      (inclD n p q x₀) z)
    refine ⟨y, (hF (Fin i)).1 ?_⟩
    rw [← hy]
    exact congrFun hcomp' y
  · rw [piMap_eq]
    exact Morse.Homotopy.homotopyGroupMap_mul _ _ a b

#rt_check RoundTrip.V13_3.A_to_B_emb_of_hanner_lamEq [Morse.theorem_22_1_bijective, Morse.theorem_22_1_surjective]
#rt_overlap RoundTrip.V13_3.A_to_B_emb_of_hanner_lamEq [Morse.theorem_22_1_bijective, Morse.theorem_22_1_surjective]

namespace LamPf

/-! ### `λ = indexUpTo` on `↥N` (copied from `Items/V9_23.lean`, namespace `Emb` there; the blind
vocabulary of this item's blind file is textually the same as V9_23's) -/

open Set Filter Topology Function
open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- `e₀, e₁ ∈ ℝ²`. -/
noncomputable abbrev e0 : Rn 2 := EuclideanSpace.single 0 (1 : ℝ)
noncomputable abbrev e1 : Rn 2 := EuclideanSpace.single 1 (1 : ℝ)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! ### Maps into `↥N` (copied from `Items/V8_10.lean`, `Items/V8_12.lean`) -/

theorem contMDiffWithinAt_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s x ↔
      ContDiffWithinAt ℝ ∞ (Bridge.incl hN ∘ f) s x := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((Bridge.contMDiff_incl (f x)).comp_contMDiffWithinAt x h)
  · intro h
    have hcont : ContinuousWithinAt f s x :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := f)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set sl := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (sl.φ y).1) (Bridge.incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn sl).contDiffAt
        (sl.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) =
        (fun y => (sl.φ y).1) ∘ (Bridge.incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt x h)

theorem contMDiffOn_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s ↔ ContDiffOn ℝ ∞ (Bridge.incl hN ∘ f) s :=
  forall₂_congr fun _ _ => contMDiffWithinAt_map_iff

/-- The derivative of a map from a normed space into `N`, read in `V`. -/
theorem D_mfderiv_map {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → Bridge.Sub hN}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x) (v : E) :
    Bridge.D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (Bridge.incl hN ∘ f) x v := by
  have h := HasMFDerivAt.comp x
    ((Bridge.contMDiff_incl (f x)).mdifferentiableAt (by simp)).hasMFDerivAt hf.hasMFDerivAt
  have h' : HasFDerivAt (Bridge.incl hN ∘ f)
      ((Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n)) x :=
    hasMFDerivAt_iff_hasFDerivAt.1 h
  have h'' : fderiv ℝ (Bridge.incl hN ∘ f) x =
      (Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n) :=
    HasFDerivAt.fderiv h'
  exact (DFunLike.congr_fun h'' v).symm

/-- A map into `N` that is `C^∞` at `x` when read in `V` has its derivative read in `V`. -/
theorem D_mfderiv_of_contDiffAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {x : E} (hf : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ f) x) (v : E) :
    Bridge.D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (Bridge.incl hN ∘ f) x v := by
  have : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f x := by
    rw [← contMDiffWithinAt_univ]
    exact contMDiffWithinAt_map_iff.2 (contDiffWithinAt_univ.2 hf)
  exact D_mfderiv_map (this.mdifferentiableAt (by simp)) v

/-! ### Paths, geodesics and `TΩ` -/

/-- A blind geodesic on `[0, 1]` (induced connection) is a project unbroken geodesic. -/
theorem isUnbrokenGeodesic_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) := h
  exact ⟨(Bridge.isGeodesic_iff.1 h').2.1, Bridge.isGeodesicOn_Ioo h'⟩

theorem mem_pathSpace_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Bridge.incl hN ∘ pw ∈ Morse.pathSpace N (Bridge.incl hN (pw 0)) (Bridge.incl hN (pw 1)) := by
  have hcd := (isUnbrokenGeodesic_of_isGeodesic h).1
  exact ⟨⟨zero_le_one, hcd.continuousOn, ∅, fun s u hs _ hu _ => hcd.mono (Icc_subset_Icc hs hu)⟩,
    fun t _ => (pw t).2, rfl, rfl⟩
/-! ### 2-parameter variations -/

/-- The ambient family `(u, s) ↦ α(u, s) ∈ N ⊆ V`. -/
def amb {m : ℕ} (α : Rn m → ℝ → Bridge.Sub hN) : Rn m → ℝ → V := fun u s => Bridge.incl hN (α u s)

/-- Theorem 13.1 for `N` (the statement of `Morse.second_variation`, or of
`Morse.hasDerivAt_energyHessian` unfolded), taken as a hypothesis. -/
def SV (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Prop :=
  ∀ {γ : ℝ → V} {p q : V}, γ ∈ Morse.pathSpace N p q → Morse.IsUnbrokenGeodesic hN γ →
    ∀ {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ}, Morse.IsVariation N U α B →
    (∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) →
    HasDerivAt (fun u₁ => deriv (fun u₂ => Morse.energy (α (u₁, u₂)) 0 1) 0)
      (2 * Morse.secondVariation hN γ (fun t => deriv (fun u₁ => α (u₁, 0) t) 0)
        (fun t => deriv (fun u₂ => α (0, u₂) t) 0)) 0

/-! ### Existence of `IsHess` values (Lemma 11.A on `↥N`, fields matched on all of `ℝ`) -/

/-- Near the zero section `exp` is smooth with `d(exp_q)₀ = id` (from `Morse.exists_isOpen_exp`
and `Morse.hasFDerivAt_exp_zero`), along any linear map into `T_qN`. -/
theorem exp_local {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {q : V} (hq : q ∈ N)
    (Λ : P →L[ℝ] V) (hΛ : ∀ u, Morse.prj hN q (Λ u) = Λ u) :
    (∀ᶠ u in 𝓝 (0 : P), Morse.exp hN q (Λ u) ∈ N) ∧
    ContDiffAt ℝ ∞ (fun u => Morse.exp hN q (Λ u)) 0 ∧
    HasFDerivAt (fun u => Morse.exp hN q (Λ u)) Λ 0 := by
  obtain ⟨O, hO, hO0, hexp⟩ := Morse.exists_isOpen_exp (hN := hN)
  have hTN : ∀ u, (q, Λ u) ∈ Milnor.Problems.tangentBundleSet hN :=
    fun u => ⟨hq, (Morse.prj_eq_self_iff hN hq).1 (hΛ u)⟩
  have hc : Continuous (fun u : P => (q, Λ u)) := continuous_const.prodMk Λ.continuous
  have hq0 : (q, Λ 0) ∈ O := by rw [map_zero]; exact hO0 q hq
  have hev : ∀ᶠ u in 𝓝 (0 : P), (q, Λ u) ∈ O :=
    hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hq0)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hev] with u hu
    exact Morse.exp_mem_of_mem_expDom (hexp _ hu (hTN u)).1
  · obtain ⟨-, F, O', hO', hzO', hF, hFeq⟩ := hexp _ hq0 (hTN 0)
    have h1 : ContDiffAt ℝ ∞ (fun u => F (q, Λ u)) 0 :=
      (hF.contDiffAt (hO'.mem_nhds hzO')).comp (0 : P)
        (contDiff_const.prodMk Λ.contDiff).contDiffAt
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hO'.mem_nhds hzO')] with u hu
    exact hFeq _ hu (hTN u)
  · set qt : N := ⟨q, hq⟩
    let L : P →L[ℝ] Morse.tangentSubspace hN qt :=
      Λ.codRestrict (Morse.tangentSubspace hN qt) fun u =>
        (Morse.prj_eq_self_iff hN hq).1 (hΛ u)
    have h1 := Morse.hasFDerivAt_exp_zero (hN := hN) qt
    rw [← map_zero L] at h1
    have h2 := h1.comp (0 : P) L.hasFDerivAt
    have hL : ((Morse.tangentSubspace hN qt).subtypeL.comp L) = Λ :=
      ContinuousLinearMap.ext fun u => rfl
    rw [hL] at h2
    exact h2

open Classical in
/-- Milnor's `α(u, t) = exp_{γ(t)}(Λ(t) u)`, as a map into `↥N` (junk `γ t` where `exp` leaves
`N`, which does not happen near `u = 0`). -/
noncomputable def liftE (γ : ℝ → Bridge.Sub hN) (Λ : ℝ → Rn 2 →L[ℝ] V) (u : Rn 2) (t : ℝ) :
    Bridge.Sub hN :=
  if h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N then (⟨_, h⟩ : N) else γ t

theorem liftE_of_mem {γ : ℝ → Bridge.Sub hN} {Λ : ℝ → Rn 2 →L[ℝ] V} {u : Rn 2} {t : ℝ}
    (h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N) :
    liftE γ Λ u t = (⟨_, h⟩ : N) := by
  unfold liftE; exact dif_pos h

theorem incl_liftE {γ : ℝ → Bridge.Sub hN} {Λ : ℝ → Rn 2 →L[ℝ] V} {u : Rn 2} {t : ℝ}
    (h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N) :
    Bridge.incl hN (liftE γ Λ u t) = Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) := by
  rw [liftE_of_mem h]; rfl

open RoundTrip.Bridge

theorem isSmoothCurveIn {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    Morse.IsSmoothCurveIn hN (incl hN ∘ γ) :=
  ⟨isSmoothCurve_iff.1 hγ, fun t _ => (γ t).2⟩

open Classical in
/-- A blind field along `γ` from an ambient field `X`: `t ↦ L_{γ t}(X t)` on `[0,1]`, `0` outside. -/
noncomputable def toFA (γ : ℝ → Bridge.Sub hN) (X : ℝ → V) : FA n γ :=
  fun t => if t ∈ Icc (0 : ℝ) 1 then L hN (γ t) (X t) else 0

theorem toFA_of_mem {γ : ℝ → Bridge.Sub hN} (X : ℝ → V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    toFA γ X t = L hN (γ t) (X t) := by
  unfold toFA
  exact if_pos ht

theorem toFA_of_not_mem {γ : ℝ → Bridge.Sub hN} (X : ℝ → V) {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    toFA γ X t = 0 := by
  unfold toFA
  exact if_neg ht

theorem ambA_toFA {γ : ℝ → Bridge.Sub hN} {X : ℝ → V}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (X t) = X t) :
    EqOn (ambA γ (toFA γ X)) X (Icc 0 1) := fun t ht => by
  show D hN (γ t) (toFA γ X t) = X t
  rw [toFA_of_mem X ht]
  exact D_L ((Morse.prj_eq_self_iff hN (γ t).2).1 (hX t ht))

/-- `toFA` as a linear map. -/
noncomputable def toFAₗ (γ : ℝ → Bridge.Sub hN) : (ℝ → V) →ₗ[ℝ] FA n γ where
  toFun := toFA γ
  map_add' X Y := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · show toFA γ (X + Y) t = toFA γ X t + toFA γ Y t
      rw [toFA_of_mem _ ht, toFA_of_mem _ ht, toFA_of_mem _ ht]
      exact map_add (L hN (γ t)) (X t) (Y t)
    · show toFA γ (X + Y) t = toFA γ X t + toFA γ Y t
      rw [toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, add_zero]
  map_smul' c X := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · show toFA γ (c • X) t = c • toFA γ X t
      rw [toFA_of_mem _ ht, toFA_of_mem _ ht]
      exact map_smul (L hN (γ t)) c (X t)
    · show toFA γ (c • X) t = c • toFA γ X t
      rw [toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, smul_zero]


/-- On fields tangent along `γ` on `[0,1]` and constant off `[0,1]`, `toFA` is injective. -/
theorem toFA_injOn {γ : ℝ → Bridge.Sub hN} {X Y : ℝ → V}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (X t) = X t)
    (hY : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (Y t) = Y t)
    (h : toFA γ X = toFA γ Y) : EqOn X Y (Icc 0 1) := fun t ht => by
  rw [← ambA_toFA hX ht, ← ambA_toFA hY ht, h]

/-- Theorem 13.1 (`Morse.second_variation`, not a theorem of this item) in the form `SV`. -/
theorem sv_holds : SV hN := by
  intro _ _ _ _ hub _ _ _ hβ hβγ
  exact Morse.second_variation hN hub hβ hβγ


/-- Continuity on `[0, t_k]` from continuity on the closed pieces of a subdivision. -/
theorem continuousOn_of_pieces {β : Type*} [TopologicalSpace β] {f : ℝ → β} {t : ℕ → ℝ}
    (ht0 : t 0 = 0) : ∀ {k : ℕ}, (∀ i < k, t i < t (i + 1)) →
    (∀ i < k, ContinuousOn f (Icc (t i) (t (i + 1)))) → ContinuousOn f (Icc 0 (t k))
  | 0, _, _ => by rw [ht0, Icc_self]; exact continuousOn_singleton f 0
  | k + 1, hlt, h => by
    have hlt' : ∀ i < k, t i < t (i + 1) := fun i hi => hlt i (by omega)
    have h0k : 0 ≤ t k := ht0 ▸ Bridge.le_of_strictSeq hlt' (Nat.zero_le k) le_rfl
    rw [← Icc_union_Icc_eq_Icc h0k (hlt k (by omega)).le]
    exact (continuousOn_of_pieces ht0 hlt' fun i hi => h i (by omega)).union_of_isClosed
      (h k (by omega)) isClosed_Icc isClosed_Icc

/-! #### Subdivisions of `[0, τ]` -/

theorem exists_piece_of_memT {τ : ℝ} (hτ : 0 < τ) {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0)
    (hk : t k = τ) (hlt : ∀ i < k, t i < t (i + 1)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) :
    ∃ i < k, s ∈ Icc (t i) (t (i + 1)) := by
  classical
  have hk0 : k ≠ 0 := by rintro rfl; rw [h0] at hk; exact hτ.ne hk
  have hP : ∃ j, s ≤ t j ∧ j ≤ k := ⟨k, hk ▸ hs.2, le_rfl⟩
  have hm := Nat.find_spec hP
  by_cases hm0 : Nat.find hP = 0
  · refine ⟨0, Nat.pos_of_ne_zero hk0, ?_, ?_⟩
    · rw [h0]; exact hs.1
    · have : s ≤ t 0 := by rw [← hm0]; exact hm.1
      exact this.trans (hlt 0 (Nat.pos_of_ne_zero hk0)).le
  · refine ⟨Nat.find hP - 1, by omega, ?_, ?_⟩
    · by_contra hcon
      exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
        ⟨(lt_of_not_ge hcon).le, by omega⟩
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]; exact hm.1

theorem exists_piece_of_subdivT {τ : ℝ} {t : ℕ → ℝ} {k : ℕ} (h0 : t 0 = 0) (hk : t k = τ)
    (hlt : ∀ i < k, t i < t (i + 1)) {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hub : u ≤ τ)
    (hB : ∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s u) :
    ∃ i < k, t i ≤ s ∧ u ≤ t (i + 1) := by
  have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
  classical
  set m := Nat.find hP
  have hm : s < t m ∧ m ≤ k := Nat.find_spec hP
  have hm0 : m ≠ 0 := by
    intro h; have := hm.1; rw [h, h0] at this; linarith
  have hi : t (m - 1) ≤ s := by
    by_contra hcon
    exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
      ⟨lt_of_not_ge hcon, by omega⟩
  have hu : u ≤ t m := by
    by_contra hcon
    exact hB (t m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩)
      ⟨hm.1, lt_of_not_ge hcon⟩
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
  exact ⟨m - 1, by omega, hi, hm1.symm ▸ hu⟩

/-- A subdivision `0 = t₀ < ⋯ < t_k = τ` whose open pieces avoid a finite set `B`. -/
theorem exists_subdivT {τ : ℝ} (hτ : 0 < τ) (B : Finset ℝ) : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧
    t k = τ ∧ (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ τ ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) := by
  classical
  have hlt : (0 : ℝ) < τ := hτ
  set a : ℝ := 0
  set b : ℝ := τ
  set S : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b)))
  have hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hbS : b ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨a, haS, b, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else b
  have ht : ∀ j (h : j < m), t j = e ⟨j, h⟩ := fun j h => dif_pos h
  refine ⟨m - 1, t, ?_, ?_, ?_, ?_⟩
  · rw [ht 0 (by omega), Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (Finset.min'_le _ _ haS) ((hS _ (Finset.min'_mem _ _)).1)
  · rw [ht (m - 1) (by omega), Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm ((hS _ (Finset.max'_mem _ _)).2) (Finset.le_max' _ _ hbS)
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    refine ⟨(hS _ (Finset.orderEmbOfFin_mem _ _ _)).1, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2,
      fun x hx hxi => ?_⟩
    have hxS : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hx, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).1.trans_lt hxi.1,
        hxi.2.trans_le (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2⟩))
    obtain ⟨j, rfl⟩ : x ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    have h1 := e.lt_iff_lt.1 hxi.1
    have h2 := e.lt_iff_lt.1 hxi.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega

/-! #### `TΩ(γ|[0, τ])`: blind `TOm τ` vs the project's `fieldsUpTo τ` -/

/-- **Blind ⇒ project**: the ambient field of a blind `W ∈ TΩ(γ|[0,τ])` lies in the project's
`TΩ_γ` and vanishes outside `[0, τ]`. -/
theorem mem_pathTangent_of_inTOmegaT {τ : ℝ} (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    {X : FA n γ} (h : InTOmegaT (n := n) τ γ X) :
    Bridge.ambA γ X ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ) ∧
      ∀ t, t ∉ Icc (0 : ℝ) τ → Bridge.ambA γ X t = 0 := by
  obtain ⟨⟨k, t, ht0, htk, hlt, -, hsm⟩, hX0, hXτ, hout⟩ := h
  have hzero : ∀ s, τ ≤ s → Bridge.ambA γ X s = 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs with rfl | hs'
    · show Bridge.D hN (γ τ) (X τ) = 0
      rw [hXτ]; exact map_zero _
    · show Bridge.D hN (γ s) (X s) = 0
      rw [hout s fun h => absurd h.2 (not_le.2 hs')]; exact map_zero _
  have hsm' : ∀ i < k, ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc (t i) (t (i + 1))) := fun i hi => by
    have h' : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc (t i) (t (i + 1))) X := hsm i hi
    exact (Bridge.isSmoothAlong_iff.1 h').2
  have hpiece : ∀ s u, 0 ≤ s → s < u → u ≤ 1 →
      (∀ x ∈ insert τ ((Finset.range (k + 1)).image t), x ∉ Ioo s u) →
      ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc s u) := by
    intro s u hs hsu hu hB
    by_cases huτ : u ≤ τ
    · obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdivT ht0 htk hlt hs hsu huτ
        fun x hx => hB x (Finset.mem_insert_of_mem hx)
      exact (hsm' i hi).mono (Icc_subset_Icc hti hui)
    · have hτs : τ ≤ s := by
        by_contra h
        exact hB τ (Finset.mem_insert_self _ _) ⟨lt_of_not_ge h, lt_of_not_ge huτ⟩
      exact contDiffOn_const.congr fun x hx => hzero x (hτs.trans hx.1)
  refine ⟨(Morse.mem_pathTangent hN).2 ⟨⟨zero_le_one, Morse.continuousOn_of_piecewise
    fun s u hs hsu hu hB => (hpiece s u hs hsu hu hB).continuousOn, _, hpiece⟩,
    fun τ' _ => (Morse.prj_eq_self_iff hN (γ τ').2).2 (Bridge.D_mem (γ τ') (X τ')), ?_, ?_⟩, ?_⟩
  · show Bridge.D hN (γ 0) (X 0) = 0
    rw [hX0]; exact map_zero _
  · exact hzero 1 hτ1
  · intro s hs
    show Bridge.D hN (γ s) (X s) = 0
    rw [hout s hs]; exact map_zero _

/-- **Project ⇒ blind**: a project field in `TΩ_γ` vanishing outside `[0, τ]` gives a blind field
`toFA γ X ∈ TΩ(γ|[0,τ])`. -/
theorem inTOmegaT_toFA_T {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {X : ℝ → V}
    (hX : X ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ))
    (hXτ : ∀ t, t ∉ Icc (0 : ℝ) τ → X t = 0) :
    InTOmegaT (n := n) τ γ (toFA γ X) := by
  obtain ⟨⟨-, -, B, hB⟩, hT, hX0, -⟩ := (Morse.mem_pathTangent hN).1 hX
  have hmem : (⟨X, hX⟩ : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) ∈
      Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ := hXτ
  have hXτ0 : X τ = 0 := Morse.fieldsUpTo_apply_self hτ.le hτ1 hmem
  obtain ⟨k, t, ht0, htk, hlt, hgood⟩ := exists_subdivT hτ B
  have hsm : ∀ i < k, IsSmoothAlong γ (Icc (t i) (t (i + 1))) (toFA γ X) := by
    intro i hi
    obtain ⟨h0i, hi1, hBi⟩ := hgood i hi
    have hsub : Icc (t i) (t (i + 1)) ⊆ Icc 0 1 := Icc_subset_Icc h0i (hi1.trans hτ1)
    exact Bridge.isSmoothAlong_iff.2 ⟨ContMDiffOn.mono hγ hsub,
      (hB _ _ h0i (hlt i hi) (hi1.trans hτ1) hBi).congr fun s hs => ambA_toFA hT (hsub hs)⟩
  refine ⟨⟨k, t, ht0, htk, hlt, ?_, hsm⟩, ?_, ?_, fun s hs => ?_⟩
  · rw [← htk]
    exact continuousOn_of_pieces ht0 hlt fun i hi => ContMDiffOn.continuousOn (hsm i hi)
  · rw [toFA_of_mem X ⟨le_rfl, zero_le_one⟩, hX0, map_zero]; rfl
  · rw [toFA_of_mem X ⟨hτ.le, hτ1⟩, hXτ0, map_zero]; rfl
  · by_cases hs1 : s ∈ Icc (0 : ℝ) 1
    · rw [toFA_of_mem X hs1, hXτ s hs, map_zero]; rfl
    · exact toFA_of_not_mem X hs1

/-! #### Variations of `γ|[0, τ]` -/

/-- The extension of a blind variation of `γ|[0, τ]` by `α 0` on `(τ, 1]`, read in `V`. -/
noncomputable def extA {m : ℕ} (τ : ℝ) (α : Rn m → ℝ → Bridge.Sub hN) : Rn m → ℝ → V :=
  fun u s => if s ≤ τ then Bridge.incl hN (α u s) else Bridge.incl hN (α 0 s)

theorem extA_zero {m : ℕ} (τ : ℝ) (α : Rn m → ℝ → Bridge.Sub hN) (s : ℝ) :
    extA τ α 0 s = Bridge.incl hN (α 0 s) := by
  unfold extA; split_ifs <;> rfl

/-- **The extension is a project variation** of `incl ∘ α 0` on `[0, 1]`. -/
theorem isVariation_extA {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (hγ : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ α 0) (Icc 0 1)) :
    Morse.IsVariation N U (extA τ α) (insert τ ((Finset.range (k + 1)).image t)) := by
  obtain ⟨hU, h0U, ht0, htk, hlt, hend, hsm⟩ := hα
  refine ⟨hU, h0U, fun u _ s _ => ?_, fun u hu => ?_, fun u hu => ?_,
    fun s u hs hsu hu hB => ?_⟩
  · unfold extA
    split_ifs
    · exact (α u s).2
    · exact (α 0 s).2
  · rw [extA_zero]
    unfold extA
    rw [if_pos hτ.le, (hend u hu).2.1]
  · rw [extA_zero]
    unfold extA
    split_ifs with h1
    · have : τ = 1 := le_antisymm hτ1 h1
      subst this
      rw [(hend u hu).2.2]
    · rfl
  · by_cases huτ : u ≤ τ
    · obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdivT ht0 htk hlt hs hsu huτ
        fun x hx => hB x (Finset.mem_insert_of_mem hx)
      refine ((contMDiffOn_map_iff.1 (hsm i hi)).mono
        (prod_mono subset_rfl (Icc_subset_Icc hti hui))).congr fun p hp => ?_
      show extA τ α p.1 p.2 = Bridge.incl hN (α p.1 p.2)
      unfold extA
      rw [if_pos (hp.2.2.trans huτ)]
    · have hτs : τ ≤ s := by
        by_contra h
        exact hB τ (Finset.mem_insert_self _ _) ⟨lt_of_not_ge h, lt_of_not_ge huτ⟩
      have hg : ContDiffOn ℝ ∞ ((Bridge.incl hN ∘ α 0) ∘ Prod.snd) (U ×ˢ Icc s u) :=
        hγ.comp contDiff_snd.contDiffOn fun p hp => ⟨hs.trans hp.2.1, hp.2.2.trans hu⟩
      refine hg.congr fun p hp => ?_
      show extA τ α p.1 p.2 = Bridge.incl hN (α 0 p.2)
      unfold extA
      split_ifs with h
      · have hpτ : p.2 = τ := le_antisymm h (hτs.trans hp.2.1)
        rw [hpτ, (hend p.1 hp.1).2.2]
      · rfl

/-- `E_0^1` of the extension is `E_0^τ` of the blind path plus the constant `E_τ^1(γ)`. -/
theorem energy_extA {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {B : Finset ℝ}
    (hvar : Morse.IsVariation N U (extA τ α) B) {v : Rn m} (hv : v ∈ U) :
    Morse.energy (extA τ α v) 0 1 =
      Morse.energy (Bridge.incl hN ∘ α v) 0 τ + Morse.energy (Bridge.incl hN ∘ α 0) τ 1 := by
  have hint := (hvar.isPiecewiseSmooth hv).intervalIntegrable_norm_deriv_sq
  have h1 : IntervalIntegrable (fun s => ‖deriv (extA τ α v) s‖ ^ 2) MeasureTheory.volume 0 τ :=
    hint.mono_set (by
      rw [uIcc_of_le hτ.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hτ1)
  have h2 : IntervalIntegrable (fun s => ‖deriv (extA τ α v) s‖ ^ 2) MeasureTheory.volume τ 1 :=
    hint.mono_set (by
      rw [uIcc_of_le hτ1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hτ.le le_rfl)
  unfold Morse.energy
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  congr 1
  · refine intervalIntegral.integral_congr_Ioo_of_le hτ.le fun s hs => ?_
    have : extA τ α v =ᶠ[𝓝 s] Bridge.incl hN ∘ α v := by
      filter_upwards [Iio_mem_nhds hs.2] with x hx
      unfold extA
      rw [if_pos (le_of_lt hx)]
      rfl
    simp only [this.deriv_eq]
  · refine intervalIntegral.integral_congr_Ioo_of_le hτ1 fun s hs => ?_
    have : extA τ α v =ᶠ[𝓝 s] Bridge.incl hN ∘ α 0 := by
      filter_upwards [Ioi_mem_nhds hs.1] with x hx
      unfold extA
      rw [if_neg (not_le.2 hx)]
      rfl
    simp only [this.deriv_eq]

/-- Variation fields of a blind variation of `γ|[0, τ]`, read in `V`, on `[0, τ]`. -/
theorem D_varFieldT {τ : ℝ} (hτ : 0 < τ) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (i : Fin m) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) :
    Bridge.D hN (α 0 s) (varField (n := n) α i s) =
      deriv (fun r : ℝ => amb α (r • EuclideanSpace.single i (1 : ℝ)) s) 0 := by
  obtain ⟨hU, h0U, ht0, htk, hlt, -, hsm⟩ := hα
  obtain ⟨j, hj, hsj⟩ := exists_piece_of_memT hτ ht0 htk hlt hs
  have hG : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn m × ℝ => α x.1 x.2)
      (U ×ˢ Icc (t j) (t (j + 1))) := contMDiffOn_map_iff.1 (hsm j hj)
  have hcd : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ fun u => α u s) 0 :=
    (hG.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun u hu => ⟨hu, hsj⟩).contDiffAt
      (hU.mem_nhds h0U)
  have h1 := D_mfderiv_of_contDiffAt hcd (EuclideanSpace.single i (1 : ℝ))
  have h2 := RoundTrip.EnergyC2.hasDerivAt_line (hcd.differentiableAt (by simp))
    (EuclideanSpace.single i (1 : ℝ))
  simp only [zero_add] at h2
  exact h1.trans h2.deriv.symm

/-- The variation fields of the extension: the blind ones on `[0, τ]`, `0` beyond. -/
theorem deriv_extA {τ : ℝ} (hτ : 0 < τ) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (i : Fin m) {s : ℝ} (hs : 0 ≤ s) :
    deriv (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) 0 =
      if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α i) s else 0 := by
  split_ifs with h
  · have e : (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) =
        fun r : ℝ => amb α (r • EuclideanSpace.single i (1 : ℝ)) s := funext fun r => by
      unfold extA
      rw [if_pos h]
      rfl
    rw [e, ← D_varFieldT hτ hα i ⟨hs, h⟩]
    rfl
  · have e : (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) =
        fun _ : ℝ => Bridge.incl hN (α 0 s) := funext fun r => by
      unfold extA
      rw [if_neg h]
    rw [e, deriv_const]

/-- **`E_0^τ ∘ α` is `C²` and its blind `mixedD` is `2 secondVariation`** of the fields
(extended by `0` beyond `τ`), for every blind variation of `γ|[0, τ]`, `γ` a geodesic of `↥N`. -/
theorem hessT_data {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {U : Set (Rn 2)}
    {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) (α 0) (Icc 0 1)) :
    DifferentiableAt ℝ
        (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => energy (n := n) (α v) 0 τ) u e0) 0 ∧
      mixedD (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =
        2 * Morse.secondVariation hN (Bridge.incl hN ∘ α 0)
          (fun s => if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α 0) s else 0)
          (fun s => if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α 1) s else 0) := by
  have hub := isUnbrokenGeodesic_of_isGeodesic hgeo
  have hvar := isVariation_extA hτ hτ1 hα hub.1
  have hU := hvar.isOpen
  have h0U := hvar.zero_mem
  have hFG : ∀ v ∈ U, energy (n := n) (α v) 0 τ =
      Morse.energy (extA τ α v) 0 1 - Morse.energy (Bridge.incl hN ∘ α 0) τ 1 := by
    intro v hv
    have h1 : energy (n := n) (α v) 0 τ = Morse.energy (Bridge.incl hN ∘ α v) 0 τ :=
      Bridge.energy_eq (α v) 0 τ
    rw [h1, energy_extA hτ hτ1 hvar hv]
    ring
  have hG : ContDiffOn ℝ 2 (fun v => Morse.energy (extA τ α v) 0 1) U :=
    hvar.contDiffOn_energy.of_le ENat.LEInfty.out
  have hF : ContDiffOn ℝ 2 (fun v : Rn 2 => energy (n := n) (α v) 0 τ) U :=
    (hG.sub contDiffOn_const).congr hFG
  have hev : (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =ᶠ[𝓝 0]
      fun v => Morse.energy (extA τ α v) 0 1 - Morse.energy (Bridge.incl hN ∘ α 0) τ 1 :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds h0U) hFG
  have hD : (fun u => fderiv ℝ (fun v : Rn 2 => energy (n := n) (α v) 0 τ) u e0) =ᶠ[𝓝 0]
      fun u => fderiv ℝ (fun v => Morse.energy (extA τ α v) 0 1) u e0 := by
    filter_upwards [hev.fderiv (𝕜 := ℝ)] with u hu
    rw [hu, fderiv_sub_const]
  refine ⟨RoundTrip.EnergyC2.differentiableAt_fderiv_apply hU hF h0U e0, ?_⟩
  have hmix : mixedD (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =
      fderiv ℝ (fun u => fderiv ℝ (fun v => Morse.energy (extA τ α v) 0 1) u e0) 0 e1 := by
    unfold mixedD
    rw [hD.fderiv_eq]
  have h := RoundTrip.EnergyC2.fderiv_fderiv_apply_eq_deriv_deriv hU hG h0U e0 e1
  simp only [zero_add] at h
  rw [hmix, h]
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  have hφ0 : (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) 0 ∈ U := by
    simpa using h0U
  have hvar2 := hvar.comp hφ hφ0
  have hαγ : ∀ s ∈ Icc (0 : ℝ) 1,
      (fun p : ℝ × ℝ => extA τ α (p.1 • e0 + p.2 • e1)) 0 s = (Bridge.incl hN ∘ α 0) s := by
    intro s _
    simp only [Prod.fst_zero, Prod.snd_zero, zero_smul, add_zero]
    exact extA_zero τ α s
  have hd := sv_holds (mem_pathSpace_of_isGeodesic hgeo) hub hvar2 hαγ
  simp only [zero_smul, add_zero, zero_add] at hd
  rw [hd.deriv]
  congr 1
  refine Morse.secondVariation_congr hN (fun s hs => ?_) (fun s hs => ?_)
  · exact deriv_extA hτ hα 0 hs.1
  · exact deriv_extA hτ hα 1 hs.1

/-- **Every `IsHessT τ` value is `2 secondVariation`** of the ambient fields, for blind fields in
`TΩ(γ|[0,τ])` (`0` beyond `τ`). -/
theorem hessT_eqT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) {r : ℝ}
    (h : IsHessT (n := n) τ γ W₁ W₂ r) :
    r = 2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  obtain ⟨U, α, k, t, hα, rfl, hW₁, hW₂, -, hr⟩ := h
  rw [← hr, (hessT_data hτ hτ1 hα hgeo).2]
  congr 1
  refine Morse.secondVariation_congr hN (fun s _ => ?_) (fun s _ => ?_)
  · split_ifs with hs
    · show Bridge.D hN (α 0 s) (varField (n := n) α 0 s) = Bridge.D hN (α 0 s) (W₁ s)
      rw [eq_of_heq (hW₁ s)]
    · show (0 : V) = Bridge.D hN (α 0 s) (W₁ s)
      rw [h₁.2.2.2 s fun h' => hs h'.2]
      exact (map_zero _).symm
  · split_ifs with hs
    · show Bridge.D hN (α 0 s) (varField (n := n) α 1 s) = Bridge.D hN (α 0 s) (W₂ s)
      rw [eq_of_heq (hW₂ s)]
    · show (0 : V) = Bridge.D hN (α 0 s) (W₂ s)
      rw [h₂.2.2.2 s fun h' => hs h'.2]
      exact (map_zero _).symm

/-- **Existence of `E_**(W₁, W₂)` for `E_0^τ` on `↥N`** (Lemma 11.A on `[0, 1]`, restricted to a
subdivision of `[0, τ]`; fields matched on all of `ℝ`). -/
theorem exists_isHessT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) :
    ∃ r, IsHessT (n := n) τ γ W₁ W₂ r := by
  have hc := mem_pathSpace_of_isGeodesic hgeo
  obtain ⟨hXs₁, -, hX0₁, hX1₁⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmegaT hτ1 h₁).1
  obtain ⟨hXs₂, -, hX0₂, hX1₂⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmegaT hτ1 h₂).1
  set X₁ := Bridge.ambA γ W₁
  set X₂ := Bridge.ambA γ W₂
  have hXτ₁ : X₁ τ = 0 := by
    show Bridge.D hN (γ τ) (W₁ τ) = 0
    rw [h₁.2.2.1]; exact map_zero _
  have hXτ₂ : X₂ τ = 0 := by
    show Bridge.D hN (γ τ) (W₂ τ) = 0
    rw [h₂.2.2.1]; exact map_zero _
  set Λ : ℝ → Rn 2 →L[ℝ] V := fun t =>
    (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₁ t) +
      (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₂ t) with hΛdef
  have hΛapp : ∀ t u, Λ t u = u 0 • X₁ t + u 1 • X₂ t := fun t u => by
    simp [hΛdef]
  have hΛT : ∀ t u, Morse.prj hN (Bridge.incl hN (γ t)) (Λ t u) = Λ t u := fun t u =>
    (Morse.prj_eq_self_iff hN (γ t).2).2 (by
      rw [hΛapp]
      exact add_mem (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₁ t)))
        (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₂ t))))
  have hΛs : Morse.IsPiecewiseSmooth Λ 0 1 :=
    (hXs₁.smulRight (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ)).add
      (hXs₂.smulRight (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ))
  have hΛ0 : Λ 0 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX0₁, hX0₂]
  have hΛ1 : Λ 1 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX1₁, hX1₂]
  have hΛτ : Λ τ = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hXτ₁, hXτ₂]
  obtain ⟨ε, hε, B, hα, -, -⟩ := Morse.exists_variation hN hc (P := Rn 2) hΛs
    (fun t _ u => hΛT t u) hΛ0 hΛ1
  set α := liftE γ Λ
  have hinc : ∀ u ∈ Metric.ball (0 : Rn 2) ε, ∀ t ∈ Icc (0 : ℝ) 1,
      Bridge.incl hN (α u t) = Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) :=
    fun u hu t ht => incl_liftE (hα.mem u hu t ht)
  have hinj : Function.Injective (Bridge.incl hN) := Subtype.val_injective
  have hα0 : α 0 = γ := funext fun t => by
    have e : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t 0) = Bridge.incl hN (γ t) := by
      rw [map_zero]; exact Morse.exp_zero (γ t).2
    exact hinj ((incl_liftE (γ := γ) (Λ := Λ) (u := 0) (t := t) (by rw [e]; exact (γ t).2)).trans e)
  obtain ⟨k, tt, ht0, htk, hlt, hgood⟩ := exists_subdivT hτ B
  have hstrip : ∀ i < k, ContMDiffOn 𝓘(ℝ, Rn 2 × ℝ) 𝓘(ℝ, Rn n) ∞
      (fun x : Rn 2 × ℝ => α x.1 x.2) (Metric.ball (0 : Rn 2) ε ×ˢ Icc (tt i) (tt (i + 1))) := by
    intro i hi
    obtain ⟨hi0, hi1, hiB⟩ := hgood i hi
    refine contMDiffOn_map_iff.2
      ((hα.smooth _ _ hi0 (hlt i hi) (hi1.trans hτ1) hiB).congr fun p hp => ?_)
    exact hinc p.1 hp.1 p.2 ⟨hi0.trans hp.2.1, hp.2.2.trans (hi1.trans hτ1)⟩
  have hvs : IsVarSubT (n := n) τ (Metric.ball (0 : Rn 2) ε) α k tt := by
    refine ⟨Metric.isOpen_ball, Metric.mem_ball_self hε, ht0, htk, hlt, fun u hu => ⟨?_, ?_, ?_⟩,
      hstrip⟩
    · refine ⟨k, tt, ht0, htk, hlt, fun i hi => ?_⟩
      have hι : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn 2 × ℝ) ∞ (fun s : ℝ => (u, s)) :=
        contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id)
      exact (hstrip i hi).comp hι.contMDiffOn fun s hs => ⟨hu, hs⟩
    · refine hinj ?_
      rw [hinc u hu 0 ⟨le_rfl, zero_le_one⟩, hinc 0 (Metric.mem_ball_self hε) 0 ⟨le_rfl, zero_le_one⟩,
        hΛ0]
      rfl
    · refine hinj ?_
      rw [hinc u hu τ ⟨hτ.le, hτ1⟩, hinc 0 (Metric.mem_ball_self hε) τ ⟨hτ.le, hτ1⟩, hΛτ]
      rfl
  have hfield : ∀ (i : Fin 2) (t : ℝ),
      Bridge.D hN (γ t) (varField (n := n) α i t) = Λ t (EuclideanSpace.single i (1 : ℝ)) := by
    intro i t
    obtain ⟨hmem, hcd, hfd⟩ := exp_local (hN := hN) (γ t).2 (Λ t) (hΛT t)
    have hev : (Bridge.incl hN ∘ fun u => α u t) =ᶠ[𝓝 0]
        fun u => Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) := by
      filter_upwards [hmem] with u hu
      exact incl_liftE hu
    have h1 := D_mfderiv_of_contDiffAt (hcd.congr_of_eventuallyEq hev)
      (EuclideanSpace.single i (1 : ℝ))
    have h2 := (hfd.congr_of_eventuallyEq hev).fderiv
    rw [h2] at h1
    calc Bridge.D hN (γ t) (varField (n := n) α i t)
        = Bridge.D hN (α 0 t) (varField (n := n) α i t) := by rw [congrFun hα0 t]
      _ = _ := h1
  have hW : ∀ (i : Fin 2) (Wi : FA n γ), (∀ t, Λ t (EuclideanSpace.single i (1 : ℝ)) =
      Bridge.D hN (γ t) (Wi t)) → ∀ t, HEq (Wi t) (varField (n := n) α i t) := by
    intro i Wi hWi t
    have := Bridge.D_injective (γ t) ((hfield i t).trans (hWi t))
    exact heq_of_eq this.symm
  have hgeo' : IsGeodesic (Bridge.conn (hN := hN)) (α 0) (Icc 0 1) := by rw [hα0]; exact hgeo
  refine ⟨_, Metric.ball (0 : Rn 2) ε, α, k, tt, hvs, hα0,
    hW 0 W₁ fun t => by rw [hΛapp]; simp [X₁, Bridge.ambA],
    hW 1 W₂ fun t => by rw [hΛapp]; simp [X₂, Bridge.ambA], (hessT_data hτ hτ1 hvs hgeo').1, rfl⟩

theorem isHessT_iffT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) {r : ℝ} :
    IsHessT (n := n) τ γ W₁ W₂ r ↔
      r = 2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  refine ⟨hessT_eqT hτ hτ1 hgeo h₁ h₂, fun h => ?_⟩
  obtain ⟨r', hr'⟩ := exists_isHessT hτ hτ1 hgeo h₁ h₂
  rw [h, ← hessT_eqT hτ hτ1 hgeo h₁ h₂ hr']
  exact hr'

/-- **The choice function `HessT τ γ` is `2 secondVariation`** on `TΩ(γ|[0,τ])`. -/
theorem hessT_eq_T {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) :
    HessT (n := n) τ γ W₁ W₂ =
      2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  have hex := exists_isHessT hτ hτ1 hgeo h₁ h₂
  unfold HessT
  rw [dif_pos hex]
  exact hessT_eqT hτ hτ1 hgeo h₁ h₂ hex.choose_spec


section LinAlgT

variable {E M : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup M] [Module ℝ M]

theorem bIndex_eq_formIndex_of {T : Set E} {H : E → E → ℝ} (B : LinearMap.BilinForm ℝ M)
    (φ : M →ₗ[ℝ] E) (hφ : Injective φ) (hT : Set.range φ = T)
    (hH : ∀ x y, H (φ x) (φ y) = B x y) : bIndex T H = Morse.formIndex B := by
  apply le_antisymm
  · unfold bIndex
    refine iSup₂_le fun S ⟨hST, hfd, hneg⟩ => ?_
    have hSR : S ≤ LinearMap.range φ := fun v hv => by
      have := hST hv
      rw [← hT] at this
      exact this
    have hmap : (S.comap φ).map φ = S := Submodule.map_comap_eq_of_le hSR
    let e : S.comap φ ≃ₗ[ℝ] S :=
      (Submodule.equivMapOfInjective φ hφ (S.comap φ)).trans (LinearEquiv.ofEq _ _ hmap)
    haveI : FiniteDimensional ℝ (S.comap φ) := LinearEquiv.finiteDimensional e.symm
    have hneg' : Morse.IsNegDefOn B (S.comap φ) := fun x hx hx0 => by
      rw [← hH]
      exact hneg (φ x) hx fun h => hx0 (hφ (h.trans (map_zero φ).symm))
    calc (Module.finrank ℝ S : ℕ∞) = Module.finrank ℝ (S.comap φ) := by rw [e.finrank_eq]
      _ ≤ Morse.formIndex B := Morse.le_formIndex hneg'
  · refine Morse.formIndex_le fun S' hfd hneg => ?_
    let e : S' ≃ₗ[ℝ] S'.map φ := Submodule.equivMapOfInjective φ hφ S'
    haveI : FiniteDimensional ℝ (S'.map φ) := LinearEquiv.finiteDimensional e
    have hST : ((S'.map φ : Submodule ℝ E) : Set E) ⊆ T := by
      rintro _ ⟨x, -, rfl⟩
      rw [← hT]
      exact ⟨x, rfl⟩
    have hneg' : IsNegDefSub H (S'.map φ) := by
      rintro _ ⟨x, hx, rfl⟩ hx0
      rw [hH]
      exact hneg x hx fun h => hx0 (by rw [h, map_zero])
    calc (Module.finrank ℝ S' : ℕ∞) = Module.finrank ℝ (S'.map φ) := by rw [e.finrank_eq]
      _ ≤ bIndex T H := by
        unfold bIndex
        exact le_iSup₂_of_le (f := fun (S : Submodule ℝ E)
          (_ : (S : Set E) ⊆ T ∧ FiniteDimensional ℝ S ∧ IsNegDefSub H S) =>
            (Module.finrank ℝ S : ℕ∞)) (S'.map φ) ⟨hST, inferInstance, hneg'⟩ le_rfl


end LinAlgT

/-- The dictionary map `fieldsUpTo τ → FA n γ`, `X ↦ toFA γ X`. -/
noncomputable def φT (γ : ℝ → Bridge.Sub hN) (τ : ℝ) :
    Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ →ₗ[ℝ] FA n γ :=
  (toFAₗ γ).comp ((Morse.pathTangent hN (Bridge.incl hN ∘ γ)).subtype.comp
    (Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ).subtype)

theorem φT_apply (γ : ℝ → Bridge.Sub hN) (τ : ℝ) (x : Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ) :
    φT (n := n) γ τ x = toFA γ ((x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) := rfl

theorem φT_injective {τ : ℝ} (hτ1 : τ ≤ 1) (γ : ℝ → Bridge.Sub hN) :
    Injective (φT (n := n) γ τ) := by
  intro x y h
  have hx := ((Morse.mem_pathTangent hN).1 (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have hy := ((Morse.mem_pathTangent hN).1 (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have h' := toFA_injOn hx hy h
  have hx0 : ∀ t, t ∉ Icc (0 : ℝ) τ →
      ((x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) t = 0 := x.2
  have hy0 : ∀ t, t ∉ Icc (0 : ℝ) τ →
      ((y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) t = 0 := y.2
  refine Subtype.ext (Subtype.ext (funext fun t => ?_))
  by_cases ht : t ∈ Icc (0 : ℝ) τ
  · exact h' ⟨ht.1, ht.2.trans hτ1⟩
  · rw [hx0 t ht, hy0 t ht]

theorem range_φT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    Set.range (φT (n := n) γ τ) = TOm (n := n) τ γ := by
  ext Wf
  constructor
  · rintro ⟨x, rfl⟩
    exact inTOmegaT_toFA_T hτ hτ1 hγ (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 x.2
  · intro hW
    have hW' : InTOmegaT (n := n) τ γ Wf := hW
    obtain ⟨hm, hout⟩ := mem_pathTangent_of_inTOmegaT hτ1 hW'
    refine ⟨⟨⟨_, hm⟩, hout⟩, funext fun t => ?_⟩
    rw [φT_apply]
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [toFA_of_mem _ ht]
      exact Bridge.L_D (γ t) (Wf t)
    · rw [toFA_of_not_mem _ ht, hW'.2.2.2 t fun h => ht ⟨h.1, h.2.trans hτ1⟩]

/-- **`HessT τ` pulled back by `toFA` is `energyHessian` on `fieldsUpTo τ`.** -/
theorem hessT_φT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1))
    (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ))
    (x y : Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ) :
    HessT (n := n) τ γ (φT γ τ x) (φT γ τ y) =
      ((Morse.energyHessian hN hc.mem_pathSpace).restrict
        (Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ)) x y := by
  have hγs : IsSmoothCurve (n := n) γ (Icc 0 1) := hgeo.2.1
  have hx := inTOmegaT_toFA_T hτ hτ1 hγs (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 x.2
  have hy := inTOmegaT_toFA_T hτ hτ1 hγs (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 y.2
  have hxT := ((Morse.mem_pathTangent hN).1 (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have hyT := ((Morse.mem_pathTangent hN).1 (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  rw [φT_apply, φT_apply, hessT_eq_T hτ hτ1 hgeo hx hy]
  show _ = Morse.energyHessian hN hc.mem_pathSpace (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ))
    (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ))
  rw [Morse.energyHessian_apply]
  congr 1
  exact Morse.secondVariation_congr hN (fun t ht => ambA_toFA hxT ht) (fun t ht => ambA_toFA hyT ht)

/-- **`λ(τ)` of B is the project's `indexUpTo τ`** on `↥N` (for a geodesic, `0 < τ ≤ 1`). -/
theorem lam_eq_indexUpTo {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1))
    (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ)) :
    lam (n := n) τ γ = Morse.indexUpTo hN (Bridge.incl hN ∘ γ) hc τ := by
  unfold lam Morse.indexUpTo
  exact bIndex_eq_formIndex_of _ (φT γ τ) (φT_injective hτ1 γ) (range_φT hτ hτ1 hgeo.2.1)
    (hessT_φT hτ hτ1 hgeo hc)

end LamPf

/-! ## Third attempt: the index dictionary `LamEq` is a theorem

`LamPf` above is a copy of the proof of `Emb.lamEqOne` of `Items/V9_23.lean` (Lemma 11.A and
Theorem 13.1 = `Morse.second_variation` for `E_0^τ` on `↥N`, `EnergyC2`'s `C²` regularity of
`u ↦ E(α(u))`, the `TΩ(γ|[0,τ])` dictionary `toFA`/`φT`, index transport `bIndex_eq_formIndex_of`,
then `Morse.indexUpTo_one`). So the conditional `A_to_B_emb_of_hanner_lamEq` loses its `LamEq`
hypothesis; Hanner's theorem (not formalized) remains an explicit hypothesis. -/

/-- **`LamEq` holds** (`Items/V9_23.lean`, `Emb.lamEqOne`). -/
theorem lamEq_holds : LamEq := by
  intro V _ _ _ W _ _ _ n N hN p q γ hc hgeo
  have hcs := LamPf.isSmoothCurveIn (hgeo.2.1 : IsSmoothCurve (n := n) γ (Icc 0 1))
  rw [LamPf.lam_eq_indexUpTo one_pos le_rfl hgeo hcs, Morse.indexUpTo_one]
  congr 1

/-- **A, with Hanner's theorem, implies B on embedded manifolds** (`LamEq` discharged). -/
theorem A_to_B_emb_of_hanner : A → Hanner → B_emb := fun hA hH =>
  A_to_B_emb_of_hanner_lamEq hA hH lamEq_holds

#rt_check RoundTrip.V13_3.lamEq_holds [Morse.theorem_22_1_bijective, Morse.theorem_22_1_surjective]
#rt_check RoundTrip.V13_3.A_to_B_emb_of_hanner [Morse.theorem_22_1_bijective, Morse.theorem_22_1_surjective]
#rt_overlap RoundTrip.V13_3.A_to_B_emb_of_hanner [Morse.theorem_22_1_bijective, Morse.theorem_22_1_surjective]

end RoundTrip.V13_3
