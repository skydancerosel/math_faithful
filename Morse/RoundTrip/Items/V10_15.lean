import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_15
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval

namespace RoundTrip.V10_15

/-- The project's statement (universe instantiated at `0`): the item's only theorem,
`Morse.PathSp.edist_toPathC_le` (`d* ≤ d` for the inclusion `i = toPathC : Ω → Ω*`), for ANY set
`N` in an inner product space `V`, where `d*` on `PathC N p q ⊆ C([0,1], V)` is the uniform
distance for the NORM of `V` (not for `ρ`). `pathCSet`, `PathC`, `toPathC`, `pathIncl` are
vocabulary (definitions). -/
def A : Prop := type_of% @Morse.PathSp.edist_toPathC_le.{0}

theorem A_holds : A := @Morse.PathSp.edist_toPathC_le

/-- `A` is provable outright from other project lemmas (`supDist_le_edist`,
`ofReal_norm_sub_le_riemDist`, `riemDist_le_supDist`): it is the elementary bound
`‖γ(t) − γ'(t)‖ ≤ ρ(γ(t), γ'(t)) ≤ supDist ≤ d`. -/
theorem A_outright : A := by
  intro V _ _ _ N p q γ γ'
  refine le_trans ?_ (Morse.PathSp.supDist_le_edist γ γ')
  rcases eq_or_ne (Morse.PathSp.supDist N γ γ') ⊤ with h | h
  · rw [h]
    exact le_top
  · rw [edist_dist, ← ENNReal.ofReal_toReal h]
    refine ENNReal.ofReal_le_ofReal ?_
    change dist (Morse.PathSp.toC γ) (Morse.PathSp.toC γ') ≤ _
    refine (ContinuousMap.dist_le ENNReal.toReal_nonneg).2 fun t => ?_
    rw [dist_eq_norm]
    have h1 := Morse.ofReal_norm_sub_le_riemDist (N := N) (γ' (t : ℝ)) (γ (t : ℝ))
    have h2 := Morse.PathSp.riemDist_le_supDist (N := N) (γ := (γ : ℝ → V))
      (γ' := (γ' : ℝ → V)) t.2
    rw [Morse.riemDist_comm] at h1
    exact (ENNReal.ofReal_le_iff_le_toReal h).1 (h1.trans h2)

/-- **B ⇒ A, vacuously**: A holds outright (`A_outright`); the hypothesis is not used. -/
theorem B_to_A : B → A := fun _ => A_outright

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


/-! ### Topological dictionary for `Ω` and `Ω*` (new) -/

/-- `↥N` connected gives `N` preconnected. -/
theorem isPreconnected_of [ConnectedSpace (Bridge.Sub hN)] : IsPreconnected N :=
  isPreconnected_iff_preconnectedSpace.2 (inferInstanceAs (PreconnectedSpace (Bridge.Sub hN)))

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

section Star

variable [ConnectedSpace (Bridge.Sub hN)]

theorem rho_cont : Continuous (fun z : Bridge.Sub hN × Bridge.Sub hN => rho (n := n) z.1 z.2) := by
  have e : (fun z : Bridge.Sub hN × Bridge.Sub hN => rho (n := n) z.1 z.2) =
      fun z => (Morse.riemDist (N := N) (incl hN z.1) (incl hN z.2)).toReal :=
    funext fun z => rho_eq z.1 z.2
  rw [e]
  exact ENNReal.continuousOn_toReal.comp_continuous (Morse.continuous_riemDist hN)
    fun z => Morse.riemDist_ne_top hN (isPreconnected_of (hN := hN)) z.1.2 z.2.2

theorem rho_nonneg (x y : Bridge.Sub hN) : 0 ≤ rho (n := n) x y := by
  rw [show rho (n := n) x y = _ from rho_eq x y]; exact ENNReal.toReal_nonneg

theorem rho_self (x : Bridge.Sub hN) : rho (n := n) x x = 0 := by
  rw [show rho (n := n) x x = _ from rho_eq x x,
    Morse.riemDist_self (N := N) (show incl hN x ∈ N from x.2)]; rfl

theorem norm_le_rho (x y : Bridge.Sub hN) : ‖incl hN x - incl hN y‖ ≤ rho (n := n) x y := by
  rw [show rho (n := n) x y = _ from rho_eq x y, norm_sub_rev]
  exact (ENNReal.ofReal_le_iff_le_toReal
    (Morse.riemDist_ne_top hN (isPreconnected_of (hN := hN)) (p := incl hN x) (q := incl hN y)
      x.2 y.2)).1 (Morse.ofReal_norm_sub_le_riemDist (N := N) (incl hN x) (incl hN y))

theorem bddAbove_rho (w w' : C(I, Bridge.Sub hN)) :
    BddAbove (range fun t => rho (n := n) (w t) (w' t)) :=
  (isCompact_range (rho_cont.comp (w.continuous.prodMk w'.continuous))).bddAbove

theorem dstar_self (w : C(I, Bridge.Sub hN)) : dstar n w w = 0 := by
  show (⨆ t : I, rho (n := n) (w t) (w t)) = 0
  simp only [rho_self, ciSup_const]

theorem dstar_cont (w : C(I, Bridge.Sub hN)) :
    Continuous (fun w' : C(I, Bridge.Sub hN) => dstar n w w') := by
  have hf : Continuous (fun z : C(I, Bridge.Sub hN) × I => rho (n := n) (w z.2) (z.1 z.2)) :=
    rho_cont.comp ((w.continuous.comp continuous_snd).prodMk continuous_eval)
  have h := isCompact_univ.continuous_sSup (f := fun (w' : C(I, Bridge.Sub hN)) (t : I) => rho (n := n) (w t) (w' t)) hf
  simp only [image_univ] at h
  exact h

variable {p q : Bridge.Sub hN}

theorem dist_le_dstar (w w' : OmStar p q) :
    dist ((sigma w : Morse.PathC N _ _) : C(I, V)) (sigma w' : C(I, V)) ≤ dstar n w.1 w'.1 := by
  have hbdd := bddAbove_rho (n := n) w.1 w'.1
  refine (ContinuousMap.dist_le ((rho_nonneg _ _).trans (le_ciSup hbdd 0))).2 fun t => ?_
  rw [dist_eq_norm]
  exact (norm_le_rho (w.1 t) (w'.1 t)).trans (le_ciSup hbdd t)

/-- **The compact-open topology of the blind `Ω*` on `↥N` is the topology of `d*`**
(`d* = max_t ρ`): `d*`-balls are open since `d*(w, ·)` is continuous (`ρ` is continuous on
`N × N`), and conversely `‖x − y‖ ≤ ρ(x, y)` makes uniform balls in `V` contain `d*`-balls. -/
theorem topology_eq :
    (inferInstance : TopologicalSpace (OmStar p q)) = TopologicalSpace.generateFrom
      {S | ∃ (w : OmStar p q) (ε : ℝ), S = {w' | dstar n w.1 w'.1 < ε}} := by
  apply le_antisymm
  · refine le_generateFrom fun s ⟨w, ε, hs⟩ => ?_
    subst hs
    exact isOpen_lt ((dstar_cont w.1).comp continuous_subtype_val) continuous_const
  · intro U hU
    obtain ⟨U', hU', rfl⟩ := isInducing_sigma_val.isOpen_iff.1 hU
    refine (@isOpen_iff_forall_mem_open (OmStar p q) (TopologicalSpace.generateFrom _) _).2
      fun w hw => ?_
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU' _ hw
    refine ⟨{w' | dstar n w.1 w'.1 < r}, fun w' hw' => hball ?_,
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨w, r, rfl⟩, ?_⟩
    · rw [Metric.mem_ball, dist_comm]
      exact (dist_le_dstar w w').trans_lt hw'
    · show dstar n w.1 w.1 < r
      rw [dstar_self]; exact hr

end Star

section Incl

variable {p q : Bridge.Sub hN}

/-- The natural map `i : Ω → Ω*` of the blind file, read through the dictionary: `σ⁻¹ ∘ toPathC ∘ τ`,
continuous as soon as the project's `toPathC` is. -/
def iMap (hcont : Continuous (Morse.PathSp.toPathC :
    Morse.PathSp N (incl hN p) (incl hN q) → Morse.PathC N (incl hN p) (incl hN q))) :
    C(Om n p q, OmStar p q) :=
  ⟨fun w => sigma.symm (Morse.PathSp.toPathC (tau w)),
    sigma.symm.continuous.comp (hcont.comp isInducing_tau.continuous)⟩

theorem iMap_apply (hcont : Continuous (Morse.PathSp.toPathC :
    Morse.PathSp N (incl hN p) (incl hN q) → Morse.PathC N (incl hN p) (incl hN q)))
    (w : Om n p q) (t : I) : (iMap hcont w).1 t = w.1 t := rfl

end Incl
end Emb

/-! `A → B` is not proved: B quantifies over abstract connected Hausdorff `ℝⁿ`-manifolds with a
smooth Riemannian metric, where `d*` is built from Milnor's `ρ`; A only concerns sets `N ⊆ V` and
bounds the uniform distance for the NORM of `V`. Neither does A contain B's first clause (the
compact-open topology of `Ω*` is the topology of `d* = max_t ρ`).

## The embedded special case -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), connected. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], ∀ (p q : Bridge.Sub hN),
    (inferInstance : TopologicalSpace (OmStar p q)) =
      TopologicalSpace.generateFrom {S | ∃ (w : OmStar p q) (ε : ℝ), S = {w' | dstar n w.1 w'.1 < ε}} ∧
    ∃ i : C(Om n p q, OmStar p q), NatMap n i ∧
      ∀ w w' : Om n p q, dstar n (i w).1 (i w').1 ≤ dOm (n := n) w.1 w'.1

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ p q => hB n (Bridge.Sub hN) p q

/-- **A implies B on embedded manifolds.** The continuity of `i` comes from A (`d*_V ≤ d` makes
the project's `toPathC` 1-Lipschitz), transported by the dictionary: the blind topology of `Ω` is
induced by `τ = incl ∘ ·` (`Emb.omTopology_eq`, from `Emb.edist_eq`), and the blind `Ω*` is
homeomorphic to `PathC` (`Emb.sigma`). The first clause (compact-open = `d*`-topology, with `ρ`)
is NOT in A: it is proved from the continuity of `ρ` on `N × N` (`Morse.continuous_riemDist`)
and `‖x − y‖ ≤ ρ(x, y)` (`Emb.topology_eq`). `d* ≤ d` itself is immediate from the blind
definitions (`d = max_t ρ + L²-term`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ p q
  have hcont : Continuous (Morse.PathSp.toPathC :
      Morse.PathSp N (Bridge.incl hN p) (Bridge.incl hN q) → Morse.PathC N _ _) :=
    (LipschitzWith.of_edist_le fun x y => hA x y).continuous
  refine ⟨Emb.topology_eq, Emb.iMap hcont, fun w t => rfl, fun w w' => ?_⟩
  show (⨆ t : I, rho (n := n) ((Emb.iMap hcont w).1 t) ((Emb.iMap hcont w').1 t)) ≤
    (⨆ t : Icc (0 : ℝ) 1, rho (n := n) (w.1 t) (w'.1 t)) +
      Real.sqrt (∫ t in (0 : ℝ)..1, (dsdt (n := n) w.1 t - dsdt (n := n) w'.1 t) ^ 2)
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)

#rt_check RoundTrip.V10_15.B_to_A [Morse.PathSp.edist_toPathC_le]
#rt_overlap RoundTrip.V10_15.B_to_A [Morse.PathSp.edist_toPathC_le]
#rt_check RoundTrip.V10_15.A_to_B_emb [Morse.PathSp.edist_toPathC_le]
#rt_overlap RoundTrip.V10_15.A_to_B_emb [Morse.PathSp.edist_toPathC_le]

end RoundTrip.V10_15
