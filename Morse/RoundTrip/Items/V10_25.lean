import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_25
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval

namespace RoundTrip.V10_25

/-- The project's statement (universes instantiated at `0`; `windowLevels` is vocabulary): the
general homology tools of p. 96 — `Homology.bettiNumber_eq_of_steps` (Betti numbers of an
exhausted space from the steps of a filtration whose relative homology vanishes beyond `k₀`),
`Homology.sublevel_step_of_isCompact` (Milnor p. 29 slab homology for a function on a slice
submanifold with compact sublevels), `BrokenSetup.finrank_subsetHomology_Omega` (slab homology of
`Ω` over a field: one generator per geodesic of index `j` in the window) and
`bettiNumber_omega_of_unique` (closed `N`, one non-degenerate geodesic `g k` per energy window of
index `k r`, `r ≥ 2`: `dim_𝕜 H_i(Ω(N; p, q); 𝕜) = 1` if `r ∣ i`, else `0`, over every field). -/
def A : Prop :=
  type_of% @Morse.Homology.bettiNumber_eq_of_steps.{0} ∧
    type_of% @Morse.Homology.sublevel_step_of_isCompact.{0,0,0,0} ∧
    type_of% @Morse.BrokenSetup.finrank_subsetHomology_Omega.{0,0,0} ∧
    type_of% @Morse.bettiNumber_omega_of_unique.{0,0,0}

theorem A_holds : A := ⟨@Morse.Homology.bettiNumber_eq_of_steps,
  @Morse.Homology.sublevel_step_of_isCompact, @Morse.BrokenSetup.finrank_subsetHomology_Omega,
  @Morse.bettiNumber_omega_of_unique⟩

/-! Neither `A → B` nor `B → A` is proved; see `V10_25.json`.  B is the INTEGRAL homology of
`Ω(Sⁿ)`, `n > 2` (`H_i ≅ ℤ` for `i = k(n − 1)`, else `0`, for `Ω` and `Ω*`, `M` abstract and
isometric to `Sⁿ` via `ψ`).  A consists of general tools (filtrations, slab homology, the lacunary
computation for one geodesic per window) over FIELDS, for embedded closed `N`, and contains
nothing about the sphere: the sphere's geodesics, energies, indices and non-conjugacy come from
other project results (`Morse/Chapter10/SphereGeodesics.lean`).  Coefficient gap as in V10_26
(universal coefficients; field Betti numbers do not determine `ℤ`-homology without finite
generation).

## The embedded special case

`B_emb` is B at `M = Sⁿ ⊆ ℝⁿ⁺¹` with `ψ` the inclusion.  A's `bettiNumber_omega_of_unique`, fed
with the sphere's geodesics `sphGeod p q k` (project lemmas outside A) and transported to the blind
`Ω` and `Ω*`, gives the field-coefficient version of `B_emb` (`A_to_A_emb`). -/

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
noncomputable def lft (γ : Morse.PathSp N (incl hN p) (incl hN q)) : Om n p q :=
  ⟨lift (γ : ℝ → V) p, (inOmega_lift γ.2).1⟩

theorem tau_lft_insep (γ : Morse.PathSp N (incl hN p) (incl hN q)) :
    Inseparable (tau (lft (n := n) γ)) γ :=
  EMetric.inseparable_iff.2 (Morse.PathSp.edist_eq_zero_of_eqOn (inOmega_lift γ.2).2)

theorem lft_tau_insep (w : Om n p q) : Inseparable (lft (n := n) (tau w)) w :=
  isInducing_tau.inseparable_iff.1 (EMetric.inseparable_iff.2
    (Morse.PathSp.edist_eq_zero_of_eqOn (inOmega_lift (tau w).2).2))

theorem continuous_lft : Continuous (lft (n := n) (p := p) (q := q)) := by
  refine isInducing_tau.continuous_iff.2 ?_
  exact (continuous_congr_of_inseparable tau_lft_insep).2 continuous_id

noncomputable def lftC : C(Morse.PathSp N (incl hN p) (incl hN q), Om n p q) := ⟨lft, continuous_lft⟩

theorem lft_tau_homotopic : ((lftC (n := n) (p := p) (q := q)).comp tauC).Homotopic
    (ContinuousMap.id _) :=
  homotopic_of_inseparable _ _ lft_tau_insep

theorem tau_lft_homotopic : ((tauC (n := n) (p := p) (q := q)).comp lftC).Homotopic
    (ContinuousMap.id _) :=
  homotopic_of_inseparable _ _ tau_lft_insep

/-- **The blind `Ω` and the project's `Ω(N; p, q)` are homotopy equivalent** via `τ`. -/
theorem isHomotopyEquiv_tau : Morse.IsHomotopyEquiv (tauC (n := n) (p := p) (q := q)) :=
  ⟨lftC, lft_tau_homotopic, tau_lft_homotopic⟩

theorem isHomotopyEquiv_lft : Morse.IsHomotopyEquiv (lftC (n := n) (p := p) (q := q)) :=
  Morse.IsHomotopyEquiv.of_inverse lft_tau_homotopic tau_lft_homotopic


/-- **The blind `Ω` is homotopy equivalent to the project's `Ω(N; p, q)`** (via `τ = incl ∘ ·`). -/
theorem nonempty_he_om :
    Nonempty (ContinuousMap.HomotopyEquiv (Om n p q) (Morse.PathSp N (incl hN p) (incl hN q))) :=
  ⟨(isHomotopyEquiv_tau (n := n) (p := p) (q := q)).exists_homotopyEquiv.choose⟩

/-- **The blind `Ω*` is homotopy equivalent to the project's `Ω(N; p, q)`**: `Ω* ≅ PathC` (`σ`)
and the project's Theorem 17.1 (`pathIncl : PathSp → PathC` is a homotopy equivalence). -/
theorem nonempty_he_omStar :
    Nonempty (ContinuousMap.HomotopyEquiv (OmStar p q) (Morse.PathSp N (incl hN p) (incl hN q))) :=
  ⟨(sigma (hN := hN) (p := p) (q := q)).toHomotopyEquiv.trans
    (Morse.theorem_17_1 hN (incl hN p) (incl hN q)).exists_homotopyEquiv.choose.symm⟩

end HE
end Emb

/-! ### The round sphere through the Bridge -/

namespace Sph

open RoundTrip.Bridge Milnor.Sphere

/-- `Sⁿ = Milnor.Sphere.Sph n ⊆ ℝⁿ⁺¹` as a blind manifold (model `ℝⁿ`, induced metric). -/
abbrev S (n : ℕ) : Type := Bridge.Sub (sphSub n)

/-- `ψ = incl : Sⁿ → ℝⁿ⁺¹`. -/
noncomputable abbrev ψ (n : ℕ) : S n → EuclideanSpace ℝ (Fin (n + 1)) := Bridge.incl (sphSub n)

/-- The inclusion of the project's sphere is a blind `IsRoundSphere`. -/
theorem isRoundSphere (n : ℕ) : IsRoundSphere n (ψ n) := by
  refine ⟨Bridge.contMDiff_incl (hN := sphSub n), Subtype.val_injective, ?_, fun x v w => ?_⟩
  · show range (Subtype.val : Sph n → _) = _
    rw [Subtype.range_coe]
    exact preimage_eq_sphere
  · exact Bridge.inner_eq x v w

theorem connectedSpace (n : ℕ) (hn : 1 ≤ n) : ConnectedSpace (S n) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  have h : IsConnected (Sph n) := by
    rw [show Sph n = Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 from preimage_eq_sphere]
    exact isConnected_sphere hrank 0 zero_le_one
  exact Subtype.connectedSpace h

end Sph

open Sph in
/-- B on the embedded round sphere: `M = Sⁿ ⊆ ℝⁿ⁺¹` with the induced metric, `ψ` the inclusion,
the induced Levi-Civita connection. -/
def B_emb : Prop :=
  ∀ (n : ℕ), 2 < n → ∀ (p q : S n), ψ n q ≠ ψ n p → ψ n q ≠ -ψ n p →
    (∀ i : ℕ, ((∃ k : ℕ, i = k * (n - 1)) → Nonempty (singH i (Om n p q) ≅ ModuleCat.of ℤ ℤ)) ∧
      ((¬ ∃ k : ℕ, i = k * (n - 1)) → CategoryTheory.Limits.IsZero (singH i (Om n p q)))) ∧
    (∀ i : ℕ, ((∃ k : ℕ, i = k * (n - 1)) → Nonempty (singH i (OmStar p q) ≅ ModuleCat.of ℤ ℤ)) ∧
      ((¬ ∃ k : ℕ, i = k * (n - 1)) → CategoryTheory.Limits.IsZero (singH i (OmStar p q))))

theorem B_to_B_emb : B → B_emb := fun hB n hn p q h1 h2 =>
  haveI := Sph.connectedSpace n (by omega)
  hB n (Sph.S n) (Bridge.conn (hN := Milnor.Sphere.sphSub n)) Bridge.conn_isLC hn (Sph.ψ n)
    (Sph.isRoundSphere n) p q h1 h2

open Sph in
/-- **The field-coefficient version of `B_emb`**: for every field `𝕜`, `n ≥ 3`, `q ≠ ±p`, the
blind `Ω(Sⁿ; p, q)` and `Ω*(Sⁿ; p, q)` have `dim_𝕜 H_i = 1` if `n − 1 ∣ i` (B's
`∃ k, i = k(n − 1)`), else `0`. -/
def A_emb : Prop :=
  ∀ (𝕜 : Type) [Field 𝕜] (n : ℕ), 2 < n → ∀ (p q : S n), ψ n q ≠ ψ n p → ψ n q ≠ -ψ n p →
    (∀ i : ℕ, Morse.Homology.bettiNumber 𝕜 (Om n p q) i = if (n - 1) ∣ i then 1 else 0) ∧
    (∀ i : ℕ, Morse.Homology.bettiNumber 𝕜 (OmStar p q) i = if (n - 1) ∣ i then 1 else 0)

open Morse Milnor.Sphere in
/-- A's `bettiNumber_omega_of_unique`, with the sphere's geodesics supplied by the project's
`SphereGeodesics` (outside A), transported to the blind `Ω` and `Ω*`. -/
theorem A_to_A_emb : A → A_emb := by
  intro hA 𝕜 _ n hn p q hqp hqn
  have hp : Sph.ψ n p ∈ Sph n := p.2
  have hq : Sph.ψ n q ∈ Sph n := q.2
  have hS : ∀ i, Homology.bettiNumber 𝕜 (PathSp (Sph n) (Sph.ψ n p) (Sph.ψ n q)) i =
      if (n - 1) ∣ i then 1 else 0 := fun i =>
    hA.2.2.2 (hN := sphSub n) (𝕜 := 𝕜) isCompact_sph.isClosed hp hq
      (fun _ hγ hgeo => hessNullity_eq_zero_of_notMem_conjLocus
        (notMem_conjLocus_sph hp hq hqp hqn (by omega)) hγ hgeo)
      (sphGeod_mem_pathSpace hp hq hqp hqn) (isUnbrokenGeodesic_sphGeod hp hq hqp hqn)
      (fun γ hγ hgeo => exists_eqOn_sphGeod hp hq hqp hqn (by omega) hγ hgeo)
      (strictMono_energy_sphGeod hp hq hqp hqn) (tendsto_energy_sphGeod hp hq hqp hqn)
      (by omega)
      (fun k γ hγ hgeo heq => formIndex_eq_of_eqOn_sphGeod hp hq hqp hqn (by omega) hγ hgeo heq) i
  obtain ⟨e⟩ := Emb.nonempty_he_om (n := n) (hN := sphSub n) (p := p) (q := q)
  obtain ⟨e'⟩ := Emb.nonempty_he_omStar (n := n) (hN := sphSub n) (p := p) (q := q)
  exact ⟨fun i => by rw [Homology.bettiNumber_eq_of_homotopyEquiv 𝕜 e i]; exact hS i,
    fun i => by rw [Homology.bettiNumber_eq_of_homotopyEquiv 𝕜 e' i]; exact hS i⟩

#rt_check RoundTrip.V10_25.A_to_A_emb [Morse.Homology.bettiNumber_eq_of_steps, Morse.Homology.sublevel_step_of_isCompact, Morse.BrokenSetup.finrank_subsetHomology_Omega, Morse.bettiNumber_omega_of_unique]
#rt_overlap RoundTrip.V10_25.A_to_A_emb [Morse.Homology.bettiNumber_eq_of_steps, Morse.Homology.sublevel_step_of_isCompact, Morse.BrokenSetup.finrank_subsetHomology_Omega, Morse.bettiNumber_omega_of_unique]

end RoundTrip.V10_25
