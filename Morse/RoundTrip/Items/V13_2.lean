import Morse
import RoundTrip.Check
import RoundTrip.Blind.V13_2
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval

namespace RoundTrip.V13_2

/-- The project's statement (universes instantiated at `0`; `Morse.minPathsIncl` is vocabulary):
for a slice submanifold `N ⊆ V` (any model `Z`), `p, q ∈ N`, closed Riemannian balls about `p`
compact (completeness), every unbroken geodesic from `p` to `q` NOT of least energy of index
`formIndex (energyHessian) ≥ λ₀`, and `Ω^d = Morse.minPaths` (least-energy paths) a RETRACT OF AN
OPEN NEIGHBOURHOOD in `Ω(N; p, q)` (in place of Milnor's "topological manifold": Hanner's theorem
is not formalized): every map `h` from a compact `P` embedded in a real vector space of dimension
`< λ₀` into `Ω` is homotopic rel `h⁻¹(Ω^d)` to a map into `Ω^d` (`theorem_22_1`); the same as a
compression property of the inclusion `Ω^d → Ω` (`compresses_minPaths`). -/
def A : Prop :=
  type_of% @Morse.theorem_22_1.{0,0,0,0,0} ∧ type_of% @Morse.compresses_minPaths.{0,0,0,0,0}

theorem A_holds : A := ⟨@Morse.theorem_22_1, @Morse.compresses_minPaths⟩

/-! Neither `A → B` nor `B → A` is proved; see `V13_2.json`.

## The embedded special case

`B_emb` (B on `M = ↥N`, `cov = Bridge.conn`) is not reached from A: its hypothesis (i) "`Ω^d` is a
topological manifold" gives A's neighbourhood-retract hypothesis only through Hanner's theorem
(manifold + metrizable ⇒ ANR), and its index hypothesis (ii) uses the blind index `lam 1 γ` of
Milnor's variational `E_**`, while A uses `formIndex (energyHessian)` — identifying them needs the
2-parameter-variation/`TΩ` dictionary (cf. Items/V10_10, V10_11). What IS glue is the conclusion:
`B_emb'` is `B_emb` with (i), (ii) replaced by A's hypotheses (on `PathSp N p q`), and A ⇒ `B_emb'`
is proved below: A's compression for `P = Iⁱ ⊆ ℝⁱ` gives `π_i(Ω, Ω^d) = 0` for the blind `Ω`
(paths `ℝ → ↥N`, `d`-topology) and the blind `Ω^d = E⁻¹[0, ρ²]`, by transporting maps and
homotopies along the dictionary `Ω ≃ₕ PathSp` of Items/V10_19.lean (correcting the lifted homotopy
on points at distance `0` so that it stays fixed on `∂Iⁱ`) and `minPaths ⊆ E⁻¹[0, ρ²]` (Hopf–Rinow). -/

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

/-! ### Distance and energy (copied from Items/V13_1.lean and V7_29.lean) -/

theorem rho_eq' (p q : Bridge.Sub hN) :
    rho (n := n) p q = (Morse.riemDist (N := N) (incl hN p) (incl hN q)).toReal :=
  rho_eq p q

theorem rho_sq_le_energy {p q : Bridge.Sub hN} {γ' : ℝ → V}
    (hγ' : γ' ∈ Morse.pathSpace N (incl hN p) (incl hN q)) :
    rho (n := n) p q ^ 2 ≤ Morse.energy γ' 0 1 := by
  have h := Morse.riemDist_sq_le_energy (N := N) hγ'.1 hγ'.2.1
  rw [hγ'.2.2.1, hγ'.2.2.2, sub_zero, one_mul] at h
  rw [rho_eq']
  exact h

/-- A path of the blind `Ω^d` has least energy: `tau w ∈ Morse.minPaths`. -/
theorem tau_mem_minPaths {p q : Bridge.Sub hN} {w : Om n p q} (hw : w ∈ OmD n p q) :
    tau w ∈ Morse.minPaths N (incl hN p) (incl hN q) := by
  intro γ'
  have h1 : Efun (n := n) w.1 ≤ rho (n := n) p q ^ 2 := hw
  rw [efun_eq] at h1
  exact h1.trans (rho_sq_le_energy γ'.2)

theorem riemDist_eq_ofReal_rho (hpre : IsPreconnected N) (p q : Bridge.Sub hN) :
    Morse.riemDist (N := N) (incl hN p) (incl hN q) = ENNReal.ofReal (rho (n := n) p q) := by
  rw [rho_eq']
  exact (ENNReal.ofReal_toReal (Morse.riemDist_ne_top hN hpre p.2 q.2)).symm

theorem rho_lt_iff (hpre : IsPreconnected N) (p q : Bridge.Sub hN) {ε : ℝ} (hε : 0 < ε) :
    rho (n := n) p q < ε ↔ Morse.riemDist (N := N) (incl hN p) (incl hN q) < ENNReal.ofReal ε := by
  rw [riemDist_eq_ofReal_rho hpre, ENNReal.ofReal_lt_ofReal_iff hε]

theorem rho_nonneg (p q : Bridge.Sub hN) : 0 ≤ rho (n := n) p q := by
  rw [rho_eq']; exact ENNReal.toReal_nonneg

/-- Blind metric completeness gives the project's (from Items/V7_29.lean). -/
theorem isRiemComplete_of (hpre : IsPreconnected N) (h : MetricComplete n (Bridge.Sub hN)) :
    Morse.IsRiemComplete N := by
  intro x hx hcau
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

/-- On a connected complete `N`, least-energy paths have energy `≤ ρ²` (a minimal geodesic of
length `ρ` exists, Hopf–Rinow). -/
theorem energy_le_of_mem_minPaths (hpre : IsPreconnected N) (hR : Morse.IsRiemComplete N)
    (p q : Bridge.Sub hN) {γ : Morse.PathSp N (incl hN p) (incl hN q)}
    (hγ : γ ∈ Morse.minPaths N (incl hN p) (incl hN q)) :
    Morse.energy γ 0 1 ≤ rho (n := n) p q ^ 2 := by
  obtain ⟨-, -, hHR, -⟩ := Morse.hopf_rinow_of_isRiemComplete hN hpre hR
  obtain ⟨γ₀, hγ₀min, hγ₀0, hγ₀1, hρ⟩ := hHR p q
  obtain ⟨hγ₀, hγ₀geo, -⟩ := hγ₀min.isMinimalPath
  rw [hγ₀0, hγ₀1] at hγ₀
  have hE₀ := Morse.energy_eq_pathLength_sq_of_geodesic hγ₀ hγ₀geo
  have hL₀ : Morse.pathLength γ₀ 0 1 = rho (n := n) p q := by
    have hρ' : Morse.riemDist (N := N) (incl hN p) (incl hN q) =
        ENNReal.ofReal (Morse.pathLength γ₀ 0 1) := hρ
    rw [rho_eq', hρ', ENNReal.toReal_ofReal hγ₀.1.isAdmissible.pathLength_nonneg]
  rw [← hL₀, ← hE₀]
  exact hγ ⟨γ₀, hγ₀⟩

/-! ### Transport of the compression property (new) -/

/-- Inseparable paths of `Morse.PathSp` have the same energy. -/
theorem energy_eq_of_inseparable {p q : V} {γ γ' : Morse.PathSp N p q} (h : Inseparable γ γ') :
    Morse.energy γ 0 1 = Morse.energy γ' 0 1 :=
  (h.map (Morse.PathSp.continuous_energy le_rfl zero_le_one le_rfl)).eq

/-- **A's conclusion gives B's**: if `Ω^d = minPaths` lies in `E⁻¹[0, ρ²]` and maps `Iⁱ → PathSp`
can be pushed into `minPaths` rel the preimage of `minPaths` (A's `PushesInto`), then
`π_i(Ω, Ω^d) = 0` for the blind `Ω` and `Ω^d` (`RelPiTrivial`). -/
theorem relPiTrivial_of_pushes {p q : Bridge.Sub hN}
    (hd : ∀ γ ∈ Morse.minPaths N (incl hN p) (incl hN q), Morse.energy γ 0 1 ≤ rho (n := n) p q ^ 2)
    (i : ℕ) (hP : Morse.PushesInto (Fin i → I) (Morse.minPaths N (incl hN p) (incl hN q)) univ) :
    RelPiTrivial (Om n p q) (OmD n p q) i := by
  classical
  intro f hf
  let h : C(Fin i → I, Morse.PathSp N (incl hN p) (incl hN q)) := tauC.comp f
  obtain ⟨h', hh'min, ⟨H⟩⟩ := hP h fun _ => trivial
  let G : I × (Fin i → I) → Om n p q := fun z =>
    if Inseparable (H z) (tau (f z.2)) then f z.2 else lam (H z)
  have hG : ∀ z, Inseparable (tau (G z)) (H z) := by
    intro z
    by_cases hc : Inseparable (H z) (tau (f z.2))
    · simp only [G, if_pos hc]; exact hc.symm
    · simp only [G, if_neg hc]; exact tau_lam_insep _
  have hGc : Continuous G :=
    isInducing_tau.continuous_iff.2 ((continuous_congr_of_inseparable hG).2 H.continuous)
  have hG0 : ∀ x, G (0, x) = f x := by
    intro x
    have : Inseparable (H (0, x)) (tau (f x)) := by
      rw [H.apply_zero]; exact Inseparable.refl _
    simp only [G, if_pos this]
  have hGS : ∀ t x, x ∈ Cube.boundary (Fin i) → G (t, x) = f x := by
    intro t x hx
    have hxS : x ∈ h ⁻¹' Morse.minPaths N (incl hN p) (incl hN q) := tau_mem_minPaths (hf x hx)
    have : Inseparable (H (t, x)) (tau (f x)) := by
      rw [H.eq_fst t hxS]; exact Inseparable.refl _
    simp only [G, if_pos this]
  let g : C(Fin i → I, Om n p q) := ⟨fun x => G (1, x), hGc.comp (by fun_prop)⟩
  have hF : f.HomotopicRel g (Cube.boundary (Fin i)) := by
    let F0 : ContinuousMap.Homotopy f g :=
      { toFun := G
        continuous_toFun := hGc
        map_zero_left := hG0
        map_one_left := fun _ => rfl }
    refine ⟨{ toHomotopy := F0, prop' := ?_ }⟩
    intro t x hx
    exact hGS t x hx
  refine ⟨g, fun y => ?_, hF⟩
  show Efun (n := n) (G (1, y)).1 ≤ rho (n := n) p q ^ 2
  have e1 : Efun (n := n) (G (1, y)).1 = Morse.energy (tau (G (1, y))) 0 1 := efun_eq _
  rw [e1, energy_eq_of_inseparable (hG (1, y)), H.apply_one]
  exact hd _ (hh'min y)

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric, connected), `cov = Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
    ∀ (p q : Bridge.Sub hN) (l0 : ℕ), Hyp221 n (Bridge.conn (hN := hN)) p q l0 →
      ∀ i : ℕ, i < l0 → RelPiTrivial (Om n p q) (OmD n p q) i

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- `B_emb` with Milnor's hypotheses replaced by A's: (i') `Ω^d = Morse.minPaths` is a retract of
an open neighbourhood in `Morse.PathSp N p q` (what Hanner's theorem would give from "topological
manifold"), (ii') every unbroken geodesic not of least energy has `formIndex (energyHessian) ≥ λ₀`
(the project's index). Conclusion as in B, for the blind `Ω`, `Ω^d`. -/
def B_emb' : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
    ∀ (p q : Bridge.Sub hN) (l0 : ℕ),
      (∃ O : Set (Morse.PathSp N (Bridge.incl hN p) (Bridge.incl hN q)), IsOpen O ∧
        Morse.minPaths N (Bridge.incl hN p) (Bridge.incl hN q) ⊆ O ∧
        ∃ r : Morse.PathSp N (Bridge.incl hN p) (Bridge.incl hN q) →
            Morse.PathSp N (Bridge.incl hN p) (Bridge.incl hN q),
          ContinuousOn r O ∧ (∀ γ ∈ O, r γ ∈ Morse.minPaths N (Bridge.incl hN p) (Bridge.incl hN q)) ∧
          ∀ γ ∈ Morse.minPaths N (Bridge.incl hN p) (Bridge.incl hN q), r γ = γ) →
      (∀ γ (hγ : γ ∈ Morse.pathSpace N (Bridge.incl hN p) (Bridge.incl hN q)),
        Morse.IsUnbrokenGeodesic hN γ →
        (∃ γ' ∈ Morse.pathSpace N (Bridge.incl hN p) (Bridge.incl hN q),
          Morse.energy γ' 0 1 < Morse.energy γ 0 1) →
        (l0 : ℕ∞) ≤ Morse.formIndex (Morse.energyHessian hN hγ)) →
      ∀ i : ℕ, i < l0 → RelPiTrivial (Om n p q) (OmD n p q) i

/-- **A gives B's conclusion on `↥N` under A's hypotheses** (uses A's `theorem_22_1` with
`P = Iⁱ ⊆ ℝⁱ`; completeness gives compact balls and `minPaths ⊆ E⁻¹[0, ρ²]` via Hopf–Rinow). -/
theorem A_to_B_emb' : A → B_emb' := by
  intro hA V _ _ _ W _ _ _ n N hN _ hcpl p q l0 hretr hidx i hi
  have hpre : IsPreconnected N :=
    isPreconnected_iff_preconnectedSpace.2 (inferInstance : PreconnectedSpace (Bridge.Sub hN))
  have hR := Emb.isRiemComplete_of hpre hcpl
  have hball : ∀ r : ℝ, IsCompact (Morse.closedRiemBall N (Bridge.incl hN p) r) :=
    Morse.isCompact_closedRiemBall_of_isRiemComplete hN hpre hR _
  have hP := hA.1 hN p.2 q.2 hball hidx hretr (P := Fin i → I) (E := Fin i → ℝ)
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hi)
    (ι := fun y j => (y j : ℝ)) (by fun_prop)
    (fun a b hab => funext fun j => Subtype.ext (congrFun hab j))
  exact Emb.relPiTrivial_of_pushes (fun γ hγ => Emb.energy_le_of_mem_minPaths hpre hR p q hγ) i hP

#rt_check RoundTrip.V13_2.A_to_B_emb' [Morse.theorem_22_1, Morse.compresses_minPaths]
#rt_overlap RoundTrip.V13_2.A_to_B_emb' [Morse.theorem_22_1, Morse.compresses_minPaths]

end RoundTrip.V13_2
