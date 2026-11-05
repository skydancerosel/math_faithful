import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_22
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal unitInterval

namespace RoundTrip.V11_22

/-! # Round trip for V11_22 (Milnor §19, Theorem 19.6)

`A` (universes `0`): `energy_le_of_geodesicIndex_le` (with `K ≥ (n-1)/r²`, `dim ≥ 2`, a geodesic of
index `≤ d` has energy `≤ ((d+1)πr)²`), `theorem_19_6_of_ricciLowerBound` (closed `N`, the same
Ricci bound, `q` not conjugate to `p` along any geodesic: `Ω(N;p,q)` has the project's countable
cell-complex type with finitely many cells in each dimension) and `theorem_19_6` (the same for
compact `N` with positive definite Ricci tensor); slice submanifolds `N ⊆ V`, induced metric.

`B`: for every compact abstract connected Riemannian `ℝⁿ`-manifold with a Levi-Civita connection
and positive definite Ricci tensor, and ALL `p, q`: the blind `Ω(M;p,q)` is homotopy equivalent to
a Mathlib `CWComplex` with finitely many cells in each dimension.

Neither direction: setting; the CW-model gap (the project's cell tower with non-cellular attaching
maps vs a Mathlib `CWComplex`, exactly as for V11_24 / V10_29); and A assumes `q` not conjugate to
`p` (Milnor's reduction step), while B is for all `p, q` (the project proves that case separately,
`Morse.theorem_19_6_all`, item V11_24). Embedded special case below, up to the cell model:
`A_to_B_cell_emb_nc`. The `Emb` dictionary is copied from Items/V11_24.lean
(`Ω ≃ₕ PathSp`, `ricci_eq`, `ricci_pos_of`). -/

def A : Prop :=
  type_of% @Morse.energy_le_of_geodesicIndex_le.{0,0,0} ∧
    type_of% @Morse.theorem_19_6_of_ricciLowerBound.{0,0,0} ∧
    type_of% @Morse.theorem_19_6.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.energy_le_of_geodesicIndex_le, @Morse.theorem_19_6_of_ricciLowerBound,
    @Morse.theorem_19_6⟩

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


/-- The blind `Ω(↥N; p, q)` and the project's `Ω(N; p, q)` are homotopy equivalent. -/
noncomputable def heOm :
    ContinuousMap.HomotopyEquiv (Om n p q) (Morse.PathSp N (incl hN p) (incl hN q)) where
  toFun := tauC
  invFun := lamC
  left_inv := lam_tau_homotopic
  right_inv := tau_lam_homotopic

end HE

/-- The project's cell-complex type is invariant under homotopy equivalence (re-proved inline:
`Morse.IsCountableCellComplexType.of_homotopyEquiv` is one of A's theorems). -/
theorem cellType_of_he {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {cells : ℕ → List ℕ}
    (h : Morse.IsCountableCellComplexType Y cells) (e : ContinuousMap.HomotopyEquiv X Y) :
    Morse.IsCountableCellComplexType X cells := by
  obtain ⟨T, ⟨e'⟩⟩ := h
  exact ⟨T, ⟨e.trans e'⟩⟩

/-! ### The Ricci tensor (new) -/

/-- The coordinate isomorphism `ℝⁿ ≃ T_xN`, `z ↦ D_x z`. -/
noncomputable def eT (x : Bridge.Sub hN) : Rn n ≃ₗ[ℝ] Morse.tangentSubspace hN x :=
  LinearEquiv.ofBijective
    ((D hN x : Rn n →ₗ[ℝ] V).codRestrict (Morse.tangentSubspace hN x) (D_mem x))
    ⟨fun _ _ h => D_injective x (congrArg Subtype.val h),
      fun v => ⟨L hN x v, Subtype.ext (D_L v.2)⟩⟩

theorem coe_eT (x : Bridge.Sub hN) (z : Rn n) : (eT x z : V) = D hN x z := rfl

/-- **Dictionary: curvature values.** The blind `R(a, b)c` (choice function over `IsCurvVal`) for
the induced connection is `L_x (curvOp (D a) (D b) (D c))`. -/
theorem curvR_eq (x : Bridge.Sub hN) (a b c : TangentSpace 𝓘(ℝ, Rn n) x) :
    curvR (Bridge.conn (hN := hN)) x a b c =
      L hN x (Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c)) := by
  have hr : ∀ r, IsCurvVal (Bridge.conn (hN := hN)) x a b c r ↔
      D hN x r = Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) := fun r => by
    have h := Bridge.isCurvVal_iff x a b c r
    have e : Morse.curvR hN (incl hN x) (D hN x a) (D hN x b) (D hN x c) =
        Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) := Morse.curvR_of_mem hN x.2 _ _ _
    rw [e] at h
    exact h
  have hmem : Morse.curvOp hN x (D hN x a) (D hN x b) (D hN x c) ∈ Morse.tangentSubspace hN x :=
    Morse.curvOp_mem hN (D_mem x a) (D_mem x b) (D_mem x c)
  have hex : ∃ r, IsCurvVal (Bridge.conn (hN := hN)) x a b c r :=
    ⟨L hN x _, (hr _).2 (D_L hmem)⟩
  unfold curvR
  rw [dif_pos hex]
  apply D_injective x
  rw [(hr _).1 hex.choose_spec, D_L hmem]

/-- **Dictionary: the Ricci tensor.** For the induced connection, the blind `K(U, U)` (trace of
`W ↦ R(U, W)U` on `ℝⁿ`) is the project's `Morse.ricci` at `D_x U`. -/
theorem ricci_eq (x : Bridge.Sub hN) (U : TangentSpace 𝓘(ℝ, Rn n) x) :
    ricci (Bridge.conn (hN := hN)) x U U =
      Morse.ricci hN x ⟨D hN x U, D_mem x U⟩ ⟨D hN x U, D_mem x U⟩ := by
  set U' : Morse.tangentSubspace hN x := ⟨D hN x U, D_mem x U⟩
  set T := (Morse.curvTensor hN x U').flip U'
  have hT : ∀ W : Rn n, ((eT x).symm.conj T) W = curvR (Bridge.conn (hN := hN)) x U W U := by
    intro W
    have hmem : Morse.curvOp hN x (D hN x U) (D hN x W) (D hN x U) ∈
        Morse.tangentSubspace hN x :=
      Morse.curvOp_mem hN (D_mem x U) (D_mem x W) (D_mem x U)
    have h1 : ((eT x).symm.conj T) W = (eT x).symm (T (eT x W)) := rfl
    have h2 : (eT x).symm (T (eT x W)) =
        L hN x (Morse.curvOp hN x (D hN x U) (D hN x W) (D hN x U)) := by
      apply (eT x).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      show Morse.curvOp hN x (D hN x U) (D hN x W) (D hN x U) = D hN x (L hN x _)
      exact (D_L hmem).symm
    exact h1.trans (h2.trans (curvR_eq x U W U).symm)
  have hex : ∃ L' : Rn n →ₗ[ℝ] Rn n, ∀ W : Rn n,
      L' W = curvR (Bridge.conn (hN := hN)) x U W U := ⟨_, hT⟩
  have hch : hex.choose = (eT x).symm.conj T :=
    LinearMap.ext fun W => (hex.choose_spec W).trans (hT W).symm
  unfold ricci
  rw [dif_pos hex, hch, LinearMap.trace_conj']
  rfl

/-- Positive definiteness of the blind Ricci tensor (induced connection) gives the project's. -/
theorem ricci_pos_of
    (hpos : ∀ (x : Bridge.Sub hN) (U : TangentSpace 𝓘(ℝ, Rn n) x), U ≠ 0 →
      0 < ricci (Bridge.conn (hN := hN)) x U U) :
    ∀ q : N, ∀ U' : Morse.tangentSubspace hN q, U' ≠ 0 → 0 < Morse.ricci hN q U' U' := by
  intro q U' hU'
  let q' : Bridge.Sub hN := q
  have hU : (L hN q' U' : TangentSpace 𝓘(ℝ, Rn n) q') ≠ 0 := fun h => hU' (Subtype.ext (by
    have := D_L (x := q') U'.2
    rw [h, map_zero] at this
    exact this.symm))
  have e : (⟨D hN q' (L hN q' U'), D_mem q' _⟩ : Morse.tangentSubspace hN q) = U' :=
    Subtype.ext (D_L U'.2)
  have h := lt_of_lt_of_eq (hpos q' _ hU) (ricci_eq q' (L hN q' U'))
  rw [e] at h
  exact h

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric, connected), `cov = Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], CompactSpace (Bridge.Sub hN) →
    (∀ (x : Bridge.Sub hN) (U : TangentSpace 𝓘(ℝ, Rn n) x), U ≠ 0 →
      0 < ricci (Bridge.conn (hN := hN)) x U U) →
    ∀ p q : Bridge.Sub hN, ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y)
      (_ : CWComplex (Set.univ : Set Y)),
      Nonempty (ContinuousMap.HomotopyEquiv (Om n p q) Y) ∧
      ∀ l : ℕ, Finite (Topology.CWComplex.cell (Set.univ : Set Y) l)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ hc hpos p q =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC hc hpos p q

/-- `B_emb` for `n ≥ 2` and `q` not conjugate to `p` (A's hypothesis, stated with the project's
`conjLocus`), with the Mathlib CW complex replaced by the project's countable cell-complex type. -/
def B_cell_emb_nc : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N), 2 ≤ n →
    CompactSpace (Bridge.Sub hN) →
    (∀ (x : Bridge.Sub hN) (U : TangentSpace 𝓘(ℝ, Rn n) x), U ≠ 0 →
      0 < ricci (Bridge.conn (hN := hN)) x U U) →
    ∀ p q : Bridge.Sub hN, Bridge.incl hN q ∉ Morse.conjLocus hN (Bridge.incl hN p) →
      ∃ cells : ℕ → List ℕ,
        Morse.IsCountableCellComplexType (Om n p q) cells ∧ ∀ d : ℕ, {k | d ∈ cells k}.Finite

/-- **A gives B on embedded manifolds for non-conjugate end points, up to the cell-complex model**
(A's `theorem_19_6`, through `Emb.ricci_pos_of` and `Ω ≃ₕ PathSp`). -/
theorem A_to_B_cell_emb_nc : A → B_cell_emb_nc := by
  intro hA V _ _ _ W _ _ _ n N hN hn hc hpos p q hnc
  have hNc : IsCompact N := isCompact_iff_compactSpace.2 hc
  have hn' : 2 ≤ finrank ℝ (Rn n) := by rw [finrank_euclideanSpace_fin]; exact hn
  obtain ⟨cells, h, hfin⟩ := hA.2.2 (hN := hN) hNc hn' (Emb.ricci_pos_of hpos) p.2 q.2 hnc
  exact ⟨cells, Emb.cellType_of_he h (Emb.heOm (n := n)), hfin⟩

#rt_check RoundTrip.V11_22.A_to_B_cell_emb_nc [Morse.energy_le_of_geodesicIndex_le,
  Morse.theorem_19_6_of_ricciLowerBound, Morse.theorem_19_6]
#rt_overlap RoundTrip.V11_22.A_to_B_cell_emb_nc [Morse.energy_le_of_geodesicIndex_le,
  Morse.theorem_19_6_of_ricciLowerBound, Morse.theorem_19_6]

end RoundTrip.V11_22
