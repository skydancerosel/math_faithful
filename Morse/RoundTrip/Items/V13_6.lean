import Morse
import RoundTrip.Check
import RoundTrip.Blind.V13_6
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval RealInnerProductSpace

namespace RoundTrip.V13_6

/-- The project's statement (no universe parameters: everything lives in `ℝⁿ⁺²`): on the round
`Sⁿ⁺¹ = Milnor.Sphere.Sph (n+1)` (slice structure `sphSub`, induced metric), for `p ∈ Sⁿ⁺¹`:
(1) every unbroken geodesic from `p` to `-p` is, on `[0,1]`, a great circle `cos(Lt)p + sin(Lt)u`
with `L = (2m+1)π`; (2) these great circles are paths from `p` to `-p`; (3) every path from `p`
to `-p` has energy `≥ π²`; (4) every path of least energy is a great semicircle (`L = π`)
through a point `u` of the equator; (5) `u ↦` the semicircle is continuous for Milnor's metric;
and the two definitions `sphMinPathsHomotopyEquiv`, `sphMinPathsHomeomorph`, read as the
`Nonempty` of their types: `equator ≃ Ω^d` up to homotopy, and `equator ≃ₜ` the separation
quotient of `Ω^d` (vocabulary: `Morse.equator`, `Morse.semicircle`, `Morse.minPaths`). -/
def A : Prop :=
  type_of% @Morse.exists_eqOn_greatCircle_antipode ∧
    type_of% @Morse.greatCircle_mem_pathSpace_antipode ∧
    type_of% @Morse.pi_sq_le_energy_sph ∧
    type_of% @Morse.exists_eqOn_semicircle ∧
    type_of% @Morse.continuous_semicircle ∧
    (∀ {n : ℕ} {p : EuclideanSpace ℝ (Fin (n + 1 + 1))}, p ∈ Milnor.Sphere.Sph (n + 1) →
      Nonempty (ContinuousMap.HomotopyEquiv (Morse.equator p)
        (Morse.minPaths (Milnor.Sphere.Sph (n + 1)) p (-p)))) ∧
    (∀ {n : ℕ} {p : EuclideanSpace ℝ (Fin (n + 1 + 1))}, p ∈ Milnor.Sphere.Sph (n + 1) →
      Nonempty (Morse.equator p ≃ₜ
        SeparationQuotient (Morse.minPaths (Milnor.Sphere.Sph (n + 1)) p (-p))))

theorem A_holds : A :=
  ⟨@Morse.exists_eqOn_greatCircle_antipode, @Morse.greatCircle_mem_pathSpace_antipode,
    @Morse.pi_sq_le_energy_sph, @Morse.exists_eqOn_semicircle, @Morse.continuous_semicircle,
    fun hp => ⟨Morse.sphMinPathsHomotopyEquiv hp⟩, fun hp => ⟨Morse.sphMinPathsHomeomorph hp⟩⟩

/-- The part of A used for the embedded special case: conjuncts (1)–(4). (Conjunct (5) and every
statement mentioning `Morse.semicircle` cannot pass `#rt_check`: the body of the definition
`Morse.semicircle` uses `Morse.semicircle_mem`, which is proved with the item's theorem
`Morse.greatCircle_mem_pathSpace_antipode`; see the JSON.) -/
def A_core : Prop :=
  type_of% @Morse.exists_eqOn_greatCircle_antipode ∧
    type_of% @Morse.greatCircle_mem_pathSpace_antipode ∧
    type_of% @Morse.pi_sq_le_energy_sph ∧
    type_of% @Morse.exists_eqOn_semicircle

theorem A_to_A_core : A → A_core := fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-! Neither `A → B` nor `B → A` is proved; see `V13_6.json`.

## The embedded special case: dictionary

Copied from `Items/V10_19.lean` (blind `Ω` ↔ `Morse.PathSp`: `edist_eq`, `tau`, `isInducing_tau`,
`lam`, …) and `Items/V9_7″.lean` (`isGeodesic_lift_of`). -/

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


/-! ### New glue -/

theorem isInducing_incl : IsInducing (incl hN) := Topology.IsInducing.subtypeVal

/-- Blind geodesics on `[0, 1]` only depend on the curve on `[0, 1]`. -/
theorem isGeodesic_congr {c₁ c₂ : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) c₂ (Icc 0 1))
    (heq : EqOn (incl hN ∘ c₁) (incl hN ∘ c₂) (Icc 0 1)) :
    IsGeodesic (Bridge.conn (hN := hN)) c₁ (Icc 0 1) := by
  obtain ⟨hs, hc, hP⟩ := isGeodesic_iff.1 h
  refine isGeodesic_iff.2 ⟨hs, hc.congr heq, fun t ht => ?_⟩
  have hd : EqOn (derivWithin (incl hN ∘ c₁) (Icc 0 1)) (derivWithin (incl hN ∘ c₂) (Icc 0 1))
      (Icc 0 1) := fun t ht => derivWithin_congr heq (heq ht)
  have hct : c₁ t = c₂ t := Subtype.ext (heq ht)
  rw [derivWithin_congr hd (hd ht), hct]
  exact hP t ht

/-- `ρ(x, y) ≤` the length of any piecewise smooth path from `x` to `y`. -/
theorem rho_le_arcLen {x y : Bridge.Sub hN} {pw : ℝ → Bridge.Sub hN} {a b : ℝ} (hab : a ≤ b)
    (hpw : IsPW (n := n) pw a b) (ha : pw a = x) (hb : pw b = y) :
    rho (n := n) x y ≤ arcLen (n := n) pw a b := by
  refine csInf_le ⟨0, ?_⟩ ⟨pw, a, b, hab, hpw, ha, hb, rfl⟩
  rintro L ⟨pth, a', b', hab', -, -, -, rfl⟩
  exact arcLen_nonneg hab'

end Emb

/-! ### The sphere -/

namespace Sph

open Emb RoundTrip.Bridge Milnor.Sphere Real

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin (n + 1 + 1))

theorem neg_mem {p : 𝔼} (hp : p ∈ Sph (n + 1)) : -p ∈ Sph (n + 1) :=
  mem_iff_norm.2 (by rw [norm_neg]; exact mem_iff_norm.1 hp)

theorem pathLength_greatCircle {p u : 𝔼} (hp : p ∈ Sph (n + 1)) (hu : ‖u‖ = 1)
    (hpu : ⟪p, u⟫ = 0) (L : ℝ) : Morse.pathLength (Morse.greatCircle p u L) 0 1 = |L| := by
  unfold Morse.pathLength
  have h : ∀ t, ‖deriv (Morse.greatCircle p u L) t‖ = |L| := fun t =>
    Morse.speed_greatCircle hp hu hpu L t
  simp only [h, intervalIntegral.integral_const, sub_zero, one_smul]

/-- **`ρ(p, -p) = π`** on `Sⁿ⁺¹` (uses A's list of the geodesics from `p` to `-p`, and the
project's Hopf–Rinow theorem for the sphere: a minimal geodesic realizes `ρ`). -/
theorem riemDist_antipode
    (hA1 : type_of% @Morse.exists_eqOn_greatCircle_antipode)
    (hA2 : type_of% @Morse.greatCircle_mem_pathSpace_antipode)
    {p : 𝔼} (hp : p ∈ Sph (n + 1)) :
    Morse.riemDist (N := Sph (n + 1)) p (-p) = ENNReal.ofReal π := by
  obtain ⟨-, hmin⟩ := Morse.sphere_hopf_rinow (n := n + 1) (by omega)
  obtain ⟨γ, hγm, hγ0, hγ1, hd⟩ := hmin ⟨p, hp⟩ ⟨-p, Sph.neg_mem hp⟩
  obtain ⟨-, ⟨s, hs, hgeo⟩, -⟩ := hγm
  have hcd : ContDiffOn ℝ ∞ γ (Icc 0 1) := hgeo.contDiffOn.mono hs
  have hmem : γ ∈ Morse.pathSpace (Sph (n + 1)) p (-p) :=
    ⟨Morse.IsPiecewiseSmooth.of_contDiffOn hcd zero_le_one le_rfl,
      fun t ht => hgeo.mem t (hs ht), hγ0, hγ1⟩
  have hub : Morse.IsUnbrokenGeodesic (sphSub (n + 1)) γ :=
    ⟨hcd, hgeo.mono isOpen_Ioo (Ioo_subset_Icc_self.trans hs)⟩
  obtain ⟨u, m, hu, hpu, heq⟩ := hA1 hmem hub
  have hlen : Morse.pathLength γ 0 1 = (2 * m + 1) * π := by
    rw [pathLength_congr zero_le_one heq, pathLength_greatCircle hp hu hpu,
      abs_of_pos (by positivity)]
  have hsemi : Morse.greatCircle p u π ∈ Morse.pathSpace (Sph (n + 1)) p (-p) := by
    simpa using hA2 hp hu hpu 0
  have hle := Morse.riemDist_le_pathLength (N := Sph (n + 1)) hsemi.1 hsemi.2.1
  rw [hsemi.2.2.1, hsemi.2.2.2, pathLength_greatCircle hp hu hpu, abs_of_pos pi_pos] at hle
  have hd' : Morse.riemDist (N := Sph (n + 1)) p (-p) = ENNReal.ofReal ((2 * m + 1) * π) := by
    rw [← hlen]; exact hd
  rw [hd'] at hle ⊢
  have h2 : (2 * (m : ℝ) + 1) * π ≤ π := (ENNReal.ofReal_le_ofReal_iff pi_pos.le).1 hle
  have hm : (m : ℝ) = 0 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [pi_pos]
  rw [hm]; ring_nf

/-- A copy of the project's proof of `Morse.continuous_semicircle` (an item theorem, whose
statement mentions `Morse.semicircle`, see `A_core`), for any continuous family of points of the
equator. -/
theorem continuous_semi {X : Type} [TopologicalSpace X] {x y : 𝔼} (hx : x ∈ Sph (n + 1))
    (f : X → 𝔼) (hf : Continuous f) (hfu : ∀ v, ‖f v‖ = 1) (hxf : ∀ v, ⟪x, f v⟫ = 0)
    (hmem : ∀ v, Morse.greatCircle x (f v) π ∈ Morse.pathSpace (Sph (n + 1)) x y) :
    Continuous (Y := Morse.PathSp (Sph (n + 1)) x y)
      (fun v => ⟨Morse.greatCircle x (f v) π, hmem v⟩) := by
  let F : X → Morse.PathSp (Sph (n + 1)) x y := fun v => ⟨Morse.greatCircle x (f v) π, hmem v⟩
  show Continuous F
  refine continuous_iff_continuousAt.2 fun u => ?_
  show Tendsto F (𝓝 u) (𝓝 (F u))
  rw [tendsto_iff_edist_tendsto_0, ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr' : 0 < r := ENNReal.ofReal_pos.1 hr
  have hE : ∀ v, Morse.energy (Morse.greatCircle x (f v) π) 0 1 = π ^ 2 := fun v =>
    Morse.energy_greatCircle (Morse.norm_of_mem_sph hx) (hfu v) (hxf v) π
  have hcs : ∀ s, Continuous fun v => Morse.greatCircle x (f v) π s := fun s => by
    unfold Morse.greatCircle; fun_prop
  have h1 := Morse.PathSp.eventually_supDist_le_of_tendsto_apply (sphSub (n + 1))
    (C := π ^ 2) (l := 𝓝 u) (αs := fun v => Morse.greatCircle x (f v) π)
    (Eventually.of_forall fun v => ⟨hmem v, (hE v).le⟩)
    (hmem u) (hE u).le (fun s _ => (hcs s).tendsto u) hr'
  filter_upwards [h1] with v hv
  have hl2 : Morse.PathSp.l2Dist (Morse.greatCircle x (f v) π) (Morse.greatCircle x (f u) π) = 0 := by
    simp only [Morse.PathSp.l2Dist, Morse.speed_greatCircle hx (hfu v) (hxf v),
      Morse.speed_greatCircle hx (hfu u) (hxf u), sub_self]
    simp
  rw [Morse.PathSp.edist_def]
  rw [show Morse.PathSp.l2Dist (F v : ℝ → 𝔼) (F u) = 0 from hl2, ENNReal.ofReal_zero, add_zero]
  exact hv.trans hrε.le

theorem semicircle_mem' {p u : 𝔼} (hp : p ∈ Sph (n + 1)) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) :
    Morse.greatCircle p u π ∈ Morse.pathSpace (Sph (n + 1)) p (-p) :=
  ⟨Morse.IsPiecewiseSmooth.of_contDiff (Morse.contDiff_greatCircle p u π) zero_le_one,
    fun t _ => Morse.greatCircle_mem_sph hp hu hpu π t, Morse.greatCircle_zero p u π,
    by simp [Morse.greatCircle]⟩

/-- On a great circle from `p` to `-p`, `cos L = -1` (copied from `Items/V9_7″.lean`). -/
theorem cos_of_antipodal {p u : 𝔼} (hp : p ∈ Sph (n + 1)) (_hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0)
    {L : ℝ} (h : Morse.greatCircle p u L 1 = -p) : Real.cos L = -1 := by
  have hp1 := Morse.norm_of_mem_sph hp
  have hpp : ⟪p, p⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hp1, one_pow]
  simp only [Morse.greatCircle, mul_one] at h
  have h1 := congrArg (fun x => ⟪p, x⟫) h
  simp only [inner_add_right, real_inner_smul_right, inner_neg_right, hpp, hpu] at h1
  linarith

/-- `cos L = -1` and `0 ≤ L ≤ π` force `L = π`. -/
theorem eq_pi_of_cos {L : ℝ} (hcos : Real.cos L = -1) (h0 : 0 ≤ L) (h1 : L ≤ π) : L = π := by
  obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.1 hcos
  have hk0 : k = 0 := by
    have a : (k : ℝ) * (2 * π) ≤ 0 := by linarith
    have b : -π ≤ (k : ℝ) * (2 * π) := by linarith
    have a' : (k : ℝ) ≤ 0 := by nlinarith [pi_pos]
    have b' : (-1 : ℝ) < k := by nlinarith [pi_pos]
    have : k ≤ 0 := by exact_mod_cast a'
    have : -1 < k := by exact_mod_cast b'
    omega
  rw [← hk, hk0]; simp

end Sph

open Milnor.Sphere in
/-- B on the embedded round sphere: `M = ↥Sⁿ⁺¹` (`Bridge.Sub (sphSub (n+1))`, model `ℝⁿ⁺¹`,
induced metric and connection `Bridge.conn`), `ψ = incl` (the inclusion into `ℝⁿ⁺²`). -/
def B_emb : Prop :=
  ∀ (n : ℕ) (p q : Bridge.Sub (sphSub (n + 1))),
    Bridge.incl (sphSub (n + 1)) q = -Bridge.incl (sphSub (n + 1)) p →
      dPQ (n + 1) p q = Real.pi ^ 2 ∧
      (∀ w : Om (n + 1) p q, w ∈ OmLe (n + 1) p q (Real.pi ^ 2) ↔
        IsMinimal (Bridge.conn (hN := sphSub (n + 1))) w.1 0 1) ∧
      ∃ (Φ : C(↥(OmLe (n + 1) p q (Real.pi ^ 2)), ↥(equator (Bridge.incl (sphSub (n + 1))) p)))
        (Ψ : C(↥(equator (Bridge.incl (sphSub (n + 1))) p), ↥(OmLe (n + 1) p q (Real.pi ^ 2)))),
        (∀ u, Φ (Ψ u) = u) ∧ ∀ w, Set.EqOn (Ψ (Φ w)).1.1 w.1.1 (Set.Icc 0 1)

open Milnor.Sphere in
/-- The inclusion `↥Sⁿ⁺¹ → ℝⁿ⁺²` is a round sphere in the blind sense. -/
theorem isRoundSphere_incl (n : ℕ) : IsRoundSphere (n + 1) (Bridge.incl (sphSub (n + 1))) := by
  refine ⟨Bridge.contMDiff_incl, Subtype.val_injective, ?_, fun x v w => rfl⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact mem_sphere_zero_iff_norm.2 (mem_iff_norm.1 x.2)
  · intro hy
    exact ⟨⟨y, mem_iff_norm.2 (mem_sphere_zero_iff_norm.1 hy)⟩, rfl⟩

open Milnor.Sphere in
instance connectedSpace_sph (n : ℕ) : ConnectedSpace (Bridge.Sub (sphSub (n + 1))) := by
  have : PreconnectedSpace (Sph (n + 1)) := preconnectedSpace (by omega)
  obtain ⟨x, hx⟩ := nonempty_sph_set (n := n + 1)
  exact { toPreconnectedSpace := this, toNonempty := ⟨⟨x, hx⟩⟩ }

/-- `B_emb` is a special case of B. -/
theorem B_to_B_emb : B → B_emb := fun hB n p q hpq =>
  hB n (Bridge.Sub (Milnor.Sphere.sphSub (n + 1))) Bridge.conn Bridge.conn_isLC _
    (isRoundSphere_incl n) p q hpq

open Emb Sph RoundTrip.Bridge Milnor.Sphere Real in
/-- **A (conjuncts (1)–(4)) implies B on the embedded round sphere.** -/
theorem A_core_to_B_emb : A_core → B_emb := by
  intro hA n p q hpq
  obtain ⟨hA1, hA2, hA3, hA4⟩ := hA
  set x : EuclideanSpace ℝ (Fin (n + 1 + 1)) := incl (sphSub (n + 1)) p with hxdef
  have hx : x ∈ Sph (n + 1) := p.2
  have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hrho : rho (n := n + 1) p q = π := by
    have h := rho_eq (hN := sphSub (n + 1)) p q
    rw [hpq, riemDist_antipode hA1 hA2 hx, ENNReal.toReal_ofReal pi_pos.le] at h
    exact h
  have hmemw : ∀ w : Om (n + 1) p q,
      incl (sphSub (n + 1)) ∘ w.1 ∈ Morse.pathSpace (Sph (n + 1)) x (-x) := by
    intro w
    rw [← hpq]; exact mem_pathSpace w.2
  have hsemi : ∀ w : Om (n + 1) p q, Efun (n := n + 1) w.1 ≤ π ^ 2 →
      ∃ u : Morse.equator x,
        EqOn (incl (sphSub (n + 1)) ∘ w.1) (Morse.greatCircle x u π) (Icc 0 1) := by
    intro w hw
    refine hA4 hx (γ := ⟨_, hmemw w⟩) fun γ' => ?_
    show Morse.energy (incl (sphSub (n + 1)) ∘ w.1) 0 1 ≤ _
    rw [← efun_eq]
    exact hw.trans (hA3 hx γ'.2)
  have hgcN : ∀ (u : EuclideanSpace ℝ (Fin (n + 1 + 1))), ‖u‖ = 1 → ⟪x, u⟫ = 0 → ∀ L t,
      Morse.greatCircle x u L t ∈ Sph (n + 1) :=
    fun u hu hxu L t => Morse.greatCircle_mem_sph hx hu hxu L t
  have hgeoLift : ∀ (u : EuclideanSpace ℝ (Fin (n + 1 + 1))) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
      (L : ℝ), IsGeodesic (Bridge.conn (hN := sphSub (n + 1)))
        (lift (Morse.greatCircle x u L) p) (Icc 0 1) :=
    fun u hu hxu L => isGeodesic_lift_of p (Morse.contDiff_greatCircle x u L).contDiffOn
      (fun t _ => hgcN u hu hxu L t)
      ((Morse.isGeodesicOn_greatCircle hx hu hxu L).mono isOpen_Ioo (subset_univ _))
  refine ⟨?_, fun w => ⟨fun hw => ?_, fun hmin => ?_⟩, ?_⟩
  · show rho (n := n + 1) p q ^ 2 = π ^ 2
    rw [hrho]
  · -- `E ≤ π²` ⇒ a semicircle ⇒ a minimal geodesic
    obtain ⟨u, heq⟩ := hsemi w hw
    have heq' : EqOn (incl (sphSub (n + 1)) ∘ w.1)
        (incl (sphSub (n + 1)) ∘ lift (Morse.greatCircle x u π) p) (Icc 0 1) :=
      fun t ht => (heq ht).trans (incl_lift p (hgcN u u.2.1 u.2.2 π t)).symm
    refine ⟨isGeodesic_congr (hgeoLift u u.2.1 u.2.2 π) heq', fun pw a' b' hab hpw ha hb => ?_⟩
    have hlen : arcLen (n := n + 1) w.1 0 1 = π := (arcLen_eq w.1 0 1).trans (by
      rw [pathLength_congr zero_le_one heq, pathLength_greatCircle hx u.2.1 u.2.2,
        abs_of_pos pi_pos])
    rw [hlen, ← hrho]
    exact rho_le_arcLen hab hpw (ha.trans w.2.2.1) (hb.trans w.2.2.2)
  · -- a minimal geodesic is a great circle of length `(2m+1)π ≤ π`, so `E = π²`
    obtain ⟨hgeo, hmin⟩ := hmin
    have hub : Morse.IsUnbrokenGeodesic (sphSub (n + 1)) (incl (sphSub (n + 1)) ∘ w.1) :=
      ⟨(isGeodesic_iff.1 hgeo).2.1, isGeodesicOn_Ioo hgeo⟩
    obtain ⟨u, m, hu, hxu, heq⟩ := hA1 (hmemw w) hub
    have hpi : Morse.IsPiecewiseSmooth (Morse.greatCircle x u π) 0 1 :=
      Morse.IsPiecewiseSmooth.of_contDiff (Morse.contDiff_greatCircle x u π) zero_le_one
    have hpw := isPW_lift (n := n + 1) hpi (fun t _ => hgcN u hu hxu π t) p
    have hl0 : lift (Morse.greatCircle x u π) p 0 = w.1 0 := by
      apply Subtype.ext
      show incl (sphSub (n + 1)) (lift _ p 0) = incl (sphSub (n + 1)) (w.1 0)
      rw [incl_lift p (hgcN u hu hxu π 0), Morse.greatCircle_zero, w.2.2.1]
    have hl1 : lift (Morse.greatCircle x u π) p 1 = w.1 1 := by
      apply Subtype.ext
      show incl (sphSub (n + 1)) (lift _ p 1) = incl (sphSub (n + 1)) (w.1 1)
      rw [incl_lift p (hgcN u hu hxu π 1), w.2.2.2, hpq]
      simp [Morse.greatCircle]
    have hle := hmin _ 0 1 zero_le_one hpw hl0 hl1
    have e1 : arcLen (n := n + 1) w.1 0 1 = (2 * m + 1) * π := (arcLen_eq w.1 0 1).trans (by
      rw [pathLength_congr zero_le_one heq, pathLength_greatCircle hx hu hxu,
        abs_of_pos (by positivity)])
    have e2 : arcLen (n := n + 1) (lift (Morse.greatCircle x u π) p) 0 1 = π :=
      (arcLen_eq _ 0 1).trans (by
        rw [pathLength_congr zero_le_one (show EqOn (incl (sphSub (n + 1)) ∘
            lift (Morse.greatCircle x u π) p) (Morse.greatCircle x u π) (Icc 0 1) from
            fun t _ => incl_lift p (hgcN u hu hxu π t)),
          pathLength_greatCircle hx hu hxu, abs_of_pos pi_pos])
    rw [e1, e2] at hle
    have hm : (m : ℝ) = 0 := by nlinarith [pi_pos, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    show Efun (n := n + 1) w.1 ≤ π ^ 2
    rw [efun_eq, Morse.energy_congr heq,
      Morse.energy_greatCircle (Morse.norm_of_mem_sph hx) hu hxu, hm]
    norm_num
  · -- the identification with the equator: `w ↦ w(1/2)` and `u ↦` the semicircle through `u`
    have hΦmem : ∀ w : ↥(OmLe (n + 1) p q (π ^ 2)),
        w.1.1 (1 / 2) ∈ equator (incl (sphSub (n + 1))) p := by
      intro w
      obtain ⟨u, heq⟩ := hsemi w.1 w.2
      show inner ℝ (incl (sphSub (n + 1)) (w.1.1 (1 / 2))) x = 0
      have : incl (sphSub (n + 1)) (w.1.1 (1 / 2)) = u :=
        (heq hhalf).trans (Morse.greatCircle_pi_half x u)
      rw [this, real_inner_comm]
      exact u.2.2
    have hcont_half : Continuous fun w : ↥(OmLe (n + 1) p q (π ^ 2)) => w.1.1 (1 / 2) := by
      refine (isInducing_incl (hN := sphSub (n + 1))).continuous_iff.2 ?_
      have : Continuous fun γ : Morse.PathSp (Sph (n + 1)) x (incl (sphSub (n + 1)) q) =>
          (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) (1 / 2) :=
        (continuous_eval_const (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).comp
          (continuous_subtype_val.comp Morse.PathSp.continuous_toPathC)
      exact this.comp (isInducing_tau.continuous.comp continuous_subtype_val)
    have hvu : ∀ v : ↥(equator (incl (sphSub (n + 1))) p),
        ‖incl (sphSub (n + 1)) v.1‖ = 1 := fun v => mem_iff_norm.1 v.1.2
    have hxv : ∀ v : ↥(equator (incl (sphSub (n + 1))) p),
        ⟪x, incl (sphSub (n + 1)) v.1⟫ = 0 := fun v => by
      rw [real_inner_comm]; exact v.2
    have hsm : ∀ v : ↥(equator (incl (sphSub (n + 1))) p),
        Morse.greatCircle x (incl (sphSub (n + 1)) v.1) π ∈
          Morse.pathSpace (Sph (n + 1)) x (incl (sphSub (n + 1)) q) := fun v => by
      rw [hpq]; simpa using hA2 hx (hvu v) (hxv v) 0
    let semi : ↥(equator (incl (sphSub (n + 1))) p) →
        Morse.PathSp (Sph (n + 1)) x (incl (sphSub (n + 1)) q) :=
      fun v => ⟨Morse.greatCircle x (incl (sphSub (n + 1)) v.1) π, hsm v⟩
    have hfc : Continuous fun v : ↥(equator (incl (sphSub (n + 1))) p) =>
        incl (sphSub (n + 1)) v.1 :=
      (isInducing_incl (hN := sphSub (n + 1))).continuous.comp continuous_subtype_val
    have hsemi_c : Continuous semi :=
      continuous_semi (X := ↥(equator (incl (sphSub (n + 1))) p)) (x := x)
        (y := incl (sphSub (n + 1)) q) hx (fun v => incl (sphSub (n + 1)) v.1) hfc hvu hxv hsm
    have hΨmem : ∀ v, Emb.lam (semi v) ∈ OmLe (n + 1) p q (π ^ 2) := fun v => by
      show Efun (n := n + 1) (Emb.lam (semi v)).1 ≤ π ^ 2
      rw [efun_eq]
      show Morse.energy (incl (sphSub (n + 1)) ∘
        lift (semi v : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) p) 0 1 ≤ π ^ 2
      rw [Morse.energy_congr (inOmega_lift (semi v).2).2]
      exact (Morse.energy_greatCircle (Morse.norm_of_mem_sph hx) (hvu v) (hxv v) π).le
    let Φ : C(↥(OmLe (n + 1) p q (π ^ 2)), ↥(equator (incl (sphSub (n + 1))) p)) :=
      ⟨fun w => ⟨w.1.1 (1 / 2), hΦmem w⟩, hcont_half.subtype_mk _⟩
    let Ψ : C(↥(equator (incl (sphSub (n + 1))) p), ↥(OmLe (n + 1) p q (π ^ 2))) :=
      ⟨fun v => ⟨Emb.lam (semi v), hΨmem v⟩, (Emb.continuous_lam.comp hsemi_c).subtype_mk _⟩
    refine ⟨Φ, Ψ, fun v => ?_, fun w t ht => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      show incl (sphSub (n + 1)) (lift (Morse.greatCircle x (incl (sphSub (n + 1)) v.1) π) p
        (1 / 2)) = incl (sphSub (n + 1)) v.1
      rw [incl_lift p (hgcN _ (hvu v) (hxv v) π _), Morse.greatCircle_pi_half]
    · obtain ⟨u, heq⟩ := hsemi w.1 w.2
      have hw2 : incl (sphSub (n + 1)) (w.1.1 (1 / 2)) = u :=
        (heq hhalf).trans (Morse.greatCircle_pi_half x u)
      apply Subtype.ext
      show incl (sphSub (n + 1)) (lift (Morse.greatCircle x
        (incl (sphSub (n + 1)) (w.1.1 (1 / 2))) π) p t) = incl (sphSub (n + 1)) (w.1.1 t)
      rw [incl_lift p (hgcN _ (hvu ⟨_, hΦmem w⟩) (hxv ⟨_, hΦmem w⟩) π t), hw2]
      exact (heq ht).symm

/-! `A → B_emb` is `A_core_to_B_emb ∘ A_to_A_core`, but a theorem with hypothesis `A` cannot pass
`#rt_check` (nor `#rt_check_soft`): the statement of A mentions `Morse.semicircle` (in the type of
`Morse.continuous_semicircle`), whose body uses `Morse.semicircle_mem`, proved with the item's
theorem `Morse.greatCircle_mem_pathSpace_antipode` (checked separately: `#rt_check_soft` reports
exactly that constant). The check is therefore run on `A_core_to_B_emb`, whose hypothesis `A_core`
(conjuncts (1)–(4) of A, verbatim) does not mention `Morse.semicircle`; conjunct (5) is not used
(its content is re-proved in `Sph.continuous_semi`, a copy of the project's proof). -/

#rt_check RoundTrip.V13_6.A_core_to_B_emb [Morse.exists_eqOn_greatCircle_antipode, Morse.greatCircle_mem_pathSpace_antipode, Morse.pi_sq_le_energy_sph, Morse.exists_eqOn_semicircle, Morse.continuous_semicircle]

/-! ### `B_emb` gives conjuncts (3), (4), and the identification of A -/

open Emb Sph RoundTrip.Bridge Milnor.Sphere Real in
/-- **B on the embedded sphere gives A's conjunct (3)**, `E ≥ π²` on `Ω(Sⁿ⁺¹; p, -p)`: by B,
`ρ(p, -p)² = π²`, and `ρ² ≤ E` (Cauchy–Schwarz, `Morse.riemDist_sq_le_energy`). -/
theorem B_emb_to_A3 : B_emb → type_of% @Morse.pi_sq_le_energy_sph := by
  intro hB n p hp γ hγ
  let p' : Bridge.Sub (sphSub (n + 1)) := ⟨p, hp⟩
  let q' : Bridge.Sub (sphSub (n + 1)) := ⟨-p, Sph.neg_mem hp⟩
  have h1 := (hB n p' q' rfl).1
  have e : (Morse.riemDist (N := Sph (n + 1)) p (-p)).toReal = rho (n := n + 1) p' q' :=
    (rho_eq p' q').symm
  have h3 := Morse.riemDist_sq_le_energy (N := Sph (n + 1)) hγ.1 hγ.2.1
  rw [hγ.2.2.1, hγ.2.2.2, e, sub_zero, one_mul] at h3
  exact (show rho (n := n + 1) p' q' ^ 2 = π ^ 2 from h1) ▸ h3

open Emb Sph RoundTrip.Bridge Milnor.Sphere Real in
/-- **B on the embedded sphere gives A's conjunct (4)**: a path of least energy has `E ≤ π²`
(compare with a semicircle), so by B it is a minimal geodesic; by the project's classification
of the geodesics of the sphere (`Morse.exists_eqOn_greatCircle`, not an item theorem) it is a
great circle of speed `L ≥ 0` with `cos L = -1`, and minimality forces `L ≤ π`, so `L = π`. -/
theorem B_emb_to_A4 : B_emb → type_of% @Morse.exists_eqOn_semicircle := by
  intro hB n p hp γ hγ
  let p' : Bridge.Sub (sphSub (n + 1)) := ⟨p, hp⟩
  let q' : Bridge.Sub (sphSub (n + 1)) := ⟨-p, Sph.neg_mem hp⟩
  obtain ⟨-, h2, -⟩ := hB n p' q' rfl
  obtain ⟨u₀, hu₀, hpu₀⟩ := Morse.exists_unit_orthogonal (n := n + 1) (by omega) p
  have hEγ : Morse.energy (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) 0 1 ≤ π ^ 2 := by
    have := hγ ⟨_, semicircle_mem' hp hu₀ hpu₀⟩
    rwa [Morse.energy_greatCircle (Morse.norm_of_mem_sph hp) hu₀ hpu₀] at this
  let w : Om (n + 1) p' q' := Emb.lam (p := p') (q := q') γ
  have hw : w ∈ OmLe (n + 1) p' q' (π ^ 2) := by
    show Efun (n := n + 1) w.1 ≤ π ^ 2
    rw [efun_eq]
    show Morse.energy (incl (sphSub (n + 1)) ∘
      lift (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) p') 0 1 ≤ π ^ 2
    rw [Morse.energy_congr (inOmega_lift (p' := p') (q' := q') γ.2).2]
    exact hEγ
  obtain ⟨hgeo, hmin⟩ := (h2 w).1 hw
  have hub : Morse.IsUnbrokenGeodesic (sphSub (n + 1)) (incl (sphSub (n + 1)) ∘ w.1) :=
    ⟨(isGeodesic_iff.1 hgeo).2.1, isGeodesicOn_Ioo hgeo⟩
  have hmemw : incl (sphSub (n + 1)) ∘ w.1 ∈ Morse.pathSpace (Sph (n + 1)) p (-p) :=
    mem_pathSpace w.2
  obtain ⟨u, L, hu, hpu, hL, heq⟩ := Morse.exists_eqOn_greatCircle (n := n + 1) (by omega)
    hmemw hub
  have hcos := cos_of_antipodal hp hu hpu
    ((heq ⟨zero_le_one, le_rfl⟩).symm.trans hmemw.2.2.2)
  have hpi : Morse.IsPiecewiseSmooth (Morse.greatCircle p u π) 0 1 :=
    Morse.IsPiecewiseSmooth.of_contDiff (Morse.contDiff_greatCircle p u π) zero_le_one
  have hgN : ∀ t, Morse.greatCircle p u π t ∈ Sph (n + 1) := fun t =>
    Morse.greatCircle_mem_sph hp hu hpu π t
  have hpw := isPW_lift (n := n + 1) hpi (fun t _ => hgN t) p'
  have hl0 : lift (Morse.greatCircle p u π) p' 0 = w.1 0 := by
    apply Subtype.ext
    show incl (sphSub (n + 1)) (lift _ p' 0) = incl (sphSub (n + 1)) (w.1 0)
    rw [incl_lift p' (hgN 0), Morse.greatCircle_zero, w.2.2.1]
    rfl
  have hl1 : lift (Morse.greatCircle p u π) p' 1 = w.1 1 := by
    apply Subtype.ext
    show incl (sphSub (n + 1)) (lift _ p' 1) = incl (sphSub (n + 1)) (w.1 1)
    rw [incl_lift p' (hgN 1), w.2.2.2]
    show _ = -p
    simp [Morse.greatCircle]
  have hle := hmin _ 0 1 zero_le_one hpw hl0 hl1
  have e1 : arcLen (n := n + 1) w.1 0 1 = L := (arcLen_eq w.1 0 1).trans (by
    rw [pathLength_congr zero_le_one heq, pathLength_greatCircle hp hu hpu, abs_of_nonneg hL])
  have e2 : arcLen (n := n + 1) (lift (Morse.greatCircle p u π) p') 0 1 = π :=
    (arcLen_eq _ 0 1).trans (by
      rw [pathLength_congr zero_le_one (show EqOn (incl (sphSub (n + 1)) ∘
          lift (Morse.greatCircle p u π) p') (Morse.greatCircle p u π) (Icc 0 1) from
          fun t _ => incl_lift p' (hgN t)),
        pathLength_greatCircle hp hu hpu, abs_of_pos pi_pos])
  rw [e1, e2] at hle
  have hLπ := eq_pi_of_cos hcos hL hle
  refine ⟨⟨u, hu, hpu⟩, fun t ht => ?_⟩
  have hγt : (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) t = (incl (sphSub (n + 1)) ∘ w.1) t :=
    ((inOmega_lift (p' := p') (q' := q') γ.2).2 ht).symm
  rw [hγt, heq ht, hLπ]

#rt_check RoundTrip.V13_6.B_emb_to_A3 [Morse.exists_eqOn_greatCircle_antipode, Morse.greatCircle_mem_pathSpace_antipode, Morse.pi_sq_le_energy_sph, Morse.exists_eqOn_semicircle, Morse.continuous_semicircle]
#rt_check RoundTrip.V13_6.B_emb_to_A4 [Morse.exists_eqOn_greatCircle_antipode, Morse.greatCircle_mem_pathSpace_antipode, Morse.pi_sq_le_energy_sph, Morse.exists_eqOn_semicircle, Morse.continuous_semicircle]

open Emb Sph RoundTrip.Bridge Milnor.Sphere Real in
/-- **B on the embedded sphere gives A's identification of `Ω^d` with the equator** (the two
`Nonempty` conjuncts of A): B's maps `Φ`, `Ψ` between `Ω^{π²}` (blind) and the blind equator,
transported along `τ`/`λ` (blind `Ω` ↔ `Morse.PathSp`, pointwise at distance `0`) and the obvious
homeomorphism of the two equators; `Ω^{π²} ↔ minPaths` uses conjunct (3) from `B_emb_to_A3`. -/
theorem B_emb_to_A67 : B_emb →
    (∀ {n : ℕ} {p : EuclideanSpace ℝ (Fin (n + 1 + 1))}, p ∈ Sph (n + 1) →
      Nonempty (ContinuousMap.HomotopyEquiv (Morse.equator p)
        (Morse.minPaths (Sph (n + 1)) p (-p)))) ∧
    (∀ {n : ℕ} {p : EuclideanSpace ℝ (Fin (n + 1 + 1))}, p ∈ Sph (n + 1) →
      Nonempty (Morse.equator p ≃ₜ
        SeparationQuotient (Morse.minPaths (Sph (n + 1)) p (-p)))) := by
  intro hB
  have hA3 : type_of% @Morse.pi_sq_le_energy_sph := B_emb_to_A3 hB
  have key : ∀ {n : ℕ} {p : EuclideanSpace ℝ (Fin (n + 1 + 1))}, p ∈ Sph (n + 1) →
      ∃ (f : C(Morse.equator p, Morse.minPaths (Sph (n + 1)) p (-p)))
        (g : C(Morse.minPaths (Sph (n + 1)) p (-p), Morse.equator p)),
        (∀ u, g (f u) = u) ∧ ∀ γ, Inseparable (f (g γ)) γ := by
    intro n p hp
    let p' : Bridge.Sub (sphSub (n + 1)) := ⟨p, hp⟩
    let q' : Bridge.Sub (sphSub (n + 1)) := ⟨-p, Sph.neg_mem hp⟩
    obtain ⟨-, -, Φ, Ψ, hΦΨ, hΨΦ⟩ := hB n p' q' rfl
    obtain ⟨u₀, hu₀, hpu₀⟩ := Morse.exists_unit_orthogonal (n := n + 1) (by omega) p
    have hmin_iff : ∀ γ : Morse.PathSp (Sph (n + 1)) p (-p),
        γ ∈ Morse.minPaths (Sph (n + 1)) p (-p) ↔
          Morse.energy (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) 0 1 ≤ π ^ 2 := by
      intro γ
      constructor
      · intro h
        have := h ⟨_, semicircle_mem' hp hu₀ hpu₀⟩
        rwa [Morse.energy_greatCircle (Morse.norm_of_mem_sph hp) hu₀ hpu₀] at this
      · intro h γ'
        exact h.trans (hA3 hp γ'.2)
    have htmem : ∀ w : ↥(OmLe (n + 1) p' q' (π ^ 2)),
        (Emb.tau w.1 : Morse.PathSp (Sph (n + 1)) p (-p)) ∈
          Morse.minPaths (Sph (n + 1)) p (-p) := fun w => (hmin_iff _).2 (by
      have := w.2
      show Morse.energy (incl (sphSub (n + 1)) ∘ w.1.1) 0 1 ≤ π ^ 2
      rw [← efun_eq]; exact this)
    let tm : C(↥(OmLe (n + 1) p' q' (π ^ 2)), Morse.minPaths (Sph (n + 1)) p (-p)) :=
      ⟨fun w => ⟨Emb.tau w.1, htmem w⟩,
        (isInducing_tau.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hlmem : ∀ γ : Morse.minPaths (Sph (n + 1)) p (-p),
        Emb.lam (p := p') (q := q') γ.1 ∈ OmLe (n + 1) p' q' (π ^ 2) := fun γ => by
      show Efun (n := n + 1) (Emb.lam (p := p') (q := q') γ.1).1 ≤ π ^ 2
      rw [efun_eq]
      show Morse.energy (incl (sphSub (n + 1)) ∘
        lift (γ.1 : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) p') 0 1 ≤ π ^ 2
      rw [Morse.energy_congr (inOmega_lift (p' := p') (q' := q') γ.1.2).2]
      exact (hmin_iff γ.1).1 γ.2
    let lm : C(Morse.minPaths (Sph (n + 1)) p (-p), ↥(OmLe (n + 1) p' q' (π ^ 2))) :=
      ⟨fun γ => ⟨Emb.lam (p := p') (q := q') γ.1, hlmem γ⟩,
        Continuous.subtype_mk (show Continuous fun γ : Morse.minPaths (Sph (n + 1)) p (-p) =>
          Emb.lam (p := p') (q := q') γ.1 from
          (continuous_lam (p := p') (q := q')).comp continuous_subtype_val) _⟩
    have he1c : Continuous fun u : Morse.equator p =>
        (⟨u.1, mem_iff_norm.2 u.2.1⟩ : Bridge.Sub (sphSub (n + 1))) :=
      (isInducing_incl (hN := sphSub (n + 1))).continuous_iff.2 continuous_subtype_val
    have he1m : ∀ u : Morse.equator p, (⟨u.1, mem_iff_norm.2 u.2.1⟩ :
        Bridge.Sub (sphSub (n + 1))) ∈ equator (incl (sphSub (n + 1))) p' := fun u => by
      show inner ℝ u.1 p = 0
      rw [real_inner_comm]; exact u.2.2
    let e1 : C(Morse.equator p, ↥(equator (incl (sphSub (n + 1))) p')) :=
      ⟨fun u => ⟨_, he1m u⟩, he1c.subtype_mk he1m⟩
    let e2 : C(↥(equator (incl (sphSub (n + 1))) p'), Morse.equator p) :=
      ⟨fun v => ⟨incl (sphSub (n + 1)) v.1, mem_iff_norm.1 v.1.2, by
        rw [real_inner_comm]; exact v.2⟩,
        ((isInducing_incl (hN := sphSub (n + 1))).continuous.comp
          continuous_subtype_val).subtype_mk _⟩
    refine ⟨tm.comp (Ψ.comp e1), e2.comp (Φ.comp lm), fun u => ?_, fun γ => ?_⟩
    · have hins : Inseparable (lm (tm (Ψ (e1 u)))) (Ψ (e1 u)) :=
        Topology.IsInducing.subtypeVal.inseparable_iff.1 (lam_tau_insep _)
      have h1 : Φ (lm (tm (Ψ (e1 u)))) = Φ (Ψ (e1 u)) := (hins.map Φ.continuous).eq
      show e2 (Φ (lm (tm (Ψ (e1 u))))) = u
      rw [h1, hΦΨ]
      rfl
    · have he : e1 (e2 (Φ (lm γ))) = Φ (lm γ) := Subtype.ext (Subtype.ext rfl)
      show Inseparable (tm (Ψ (e1 (e2 (Φ (lm γ)))))) γ
      rw [he]
      have h1 : Inseparable (tm (Ψ (Φ (lm γ)))) (tm (lm γ)) :=
        Topology.IsInducing.subtypeVal.inseparable_iff.1 (EMetric.inseparable_iff.2
          (Morse.PathSp.edist_eq_zero_of_eqOn fun t ht =>
            congrArg (incl (sphSub (n + 1))) (hΨΦ (lm γ) ht)))
      have h2 : Inseparable (tm (lm γ)) γ :=
        Topology.IsInducing.subtypeVal.inseparable_iff.1 (tau_lam_insep (p := p') (q := q') γ.1)
      exact h1.trans h2
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨f, g, hgf, hfg⟩ := key hp
    refine ⟨{ toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }⟩
    · rw [show g.comp f = ContinuousMap.id _ from ContinuousMap.ext hgf]
    · exact homotopic_of_inseparable _ _ hfg
  · obtain ⟨f, g, hgf, hfg⟩ := key hp
    exact ⟨{ toFun := fun u => SeparationQuotient.mk (f u)
             invFun := SeparationQuotient.lift g fun _ _ h => (h.map g.continuous).eq
             left_inv := fun u => by simp only [SeparationQuotient.lift_mk]; exact hgf u
             right_inv := SeparationQuotient.surjective_mk.forall.2 fun γ => by
               simp only [SeparationQuotient.lift_mk]
               exact SeparationQuotient.mk_eq_mk.2 (hfg γ)
             continuous_toFun := SeparationQuotient.continuous_mk.comp f.continuous
             continuous_invFun := SeparationQuotient.continuous_lift g.continuous }⟩

#rt_check RoundTrip.V13_6.B_emb_to_A67 [Morse.exists_eqOn_greatCircle_antipode, Morse.greatCircle_mem_pathSpace_antipode, Morse.pi_sq_le_energy_sph, Morse.exists_eqOn_semicircle, Morse.continuous_semicircle]

/-- The part of A that `B_emb` gives back: conjuncts (3), (4) and the two `Nonempty`
identifications of `Ω^d` with the equator. -/
def A_B : Prop :=
  type_of% @Morse.pi_sq_le_energy_sph ∧ type_of% @Morse.exists_eqOn_semicircle ∧
    (∀ {n : ℕ} {p : EuclideanSpace ℝ (Fin (n + 1 + 1))}, p ∈ Milnor.Sphere.Sph (n + 1) →
      Nonempty (ContinuousMap.HomotopyEquiv (Morse.equator p)
        (Morse.minPaths (Milnor.Sphere.Sph (n + 1)) p (-p)))) ∧
    (∀ {n : ℕ} {p : EuclideanSpace ℝ (Fin (n + 1 + 1))}, p ∈ Milnor.Sphere.Sph (n + 1) →
      Nonempty (Morse.equator p ≃ₜ
        SeparationQuotient (Morse.minPaths (Milnor.Sphere.Sph (n + 1)) p (-p))))

theorem A_to_A_B : A → A_B := fun h => ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- **B on the embedded sphere gives back conjuncts (3), (4) and the identification of A.** -/
theorem B_emb_to_A_B : B_emb → A_B := fun hB =>
  ⟨B_emb_to_A3 hB, B_emb_to_A4 hB, (B_emb_to_A67 hB).1, (B_emb_to_A67 hB).2⟩

/-- **B gives back conjuncts (3), (4) and the identification of A** (through `B_emb`). -/
theorem B_to_A_B : B → A_B := fun hB => B_emb_to_A_B (B_to_B_emb hB)

#rt_check RoundTrip.V13_6.B_to_A_B [Morse.exists_eqOn_greatCircle_antipode, Morse.greatCircle_mem_pathSpace_antipode, Morse.pi_sq_le_energy_sph, Morse.exists_eqOn_semicircle, Morse.continuous_semicircle]
#rt_overlap RoundTrip.V13_6.B_to_A_B [Morse.exists_eqOn_greatCircle_antipode, Morse.greatCircle_mem_pathSpace_antipode, Morse.pi_sq_le_energy_sph, Morse.exists_eqOn_semicircle, Morse.continuous_semicircle]
#rt_overlap RoundTrip.V13_6.A_core_to_B_emb [Morse.exists_eqOn_greatCircle_antipode, Morse.greatCircle_mem_pathSpace_antipode, Morse.pi_sq_le_energy_sph, Morse.exists_eqOn_semicircle, Morse.continuous_semicircle]

end RoundTrip.V13_6
