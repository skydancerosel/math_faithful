import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_2
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal

namespace RoundTrip.V10_2

/-- The project's statement (universe instantiated at `0`), for ANY set `N` in an inner product
space `V` and `Ω(N; p, q) = Morse.PathSp N p q` with Milnor's pseudo-emetric:
* `abs_sqrt_energy_sub_le` (Lemma 16.A): `|√E_a^b(γ) − √E_a^b(γ')| ≤ (∫₀¹ (‖γ'‖ − ‖γ''‖)²)^{1/2}`
  for `0 ≤ a ≤ b ≤ 1`;
* `lipschitzWith_sqrt_energy`: `√E_a^b` is `1`-Lipschitz on `Ω`;
* `continuous_energy`: `E_a^b` is continuous on `Ω`;
* `isClosed_sublevel`, `isOpen_sublevel_lt`: `{E ≤ c}` closed, `{E < c}` open;
* `exists_energy_lt_of_tendsto` (Lemma 16.B): along a convergent sequence the energy on short
  intervals is uniformly small. -/
def A : Prop :=
  type_of% @Morse.PathSp.abs_sqrt_energy_sub_le.{0} ∧
    type_of% @Morse.PathSp.lipschitzWith_sqrt_energy.{0} ∧
    type_of% @Morse.PathSp.continuous_energy.{0} ∧
    type_of% @Morse.PathSp.isClosed_sublevel.{0} ∧
    type_of% @Morse.PathSp.isOpen_sublevel_lt.{0} ∧
    type_of% @Morse.PathSp.exists_energy_lt_of_tendsto.{0}

theorem A_holds : A :=
  ⟨@Morse.PathSp.abs_sqrt_energy_sub_le, @Morse.PathSp.lipschitzWith_sqrt_energy,
    @Morse.PathSp.continuous_energy, @Morse.PathSp.isClosed_sublevel,
    @Morse.PathSp.isOpen_sublevel_lt, @Morse.PathSp.exists_energy_lt_of_tendsto⟩

/-! Neither `A → B` nor `B → A` is proved: B quantifies over abstract connected Hausdorff
`ℝⁿ`-manifolds with an arbitrary smooth metric, A over sets `N ⊆ V` with the induced lengths.
See `V10_2.json`.

## The embedded special case

The metric dictionary of `Items/V10_1.lean` (copied in namespace `Emb`: the blind `dOm` on `↥N` is
the project's `edist`, `Emb.edist_eq`) and `Bridge.energy_eq` turn A's continuity of `E` into B's
`ε`-`δ` continuity on `↥N` (`A_to_B_emb`), and B's continuity back into the continuity of `E_0^1`
on `Ω(N; p, q)` for connected `N` with model `ℝⁿ` (`B_emb_to_A_cont`). -/

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

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric) with the induced Levi-Civita
connection `Bridge.conn` (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ (p q : Bridge.Sub hN) (c : ℝ),
    (∀ w : ℝ → Bridge.Sub hN, InOmega (n := n) p q w → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ w' : ℝ → Bridge.Sub hN, InOmega (n := n) p q w' →
        dOm (n := n) w w' < δ → |Efun (n := n) w' - Efun (n := n) w| < ε) ∧
    (∀ w : ℝ → Bridge.Sub hN, InOmega (n := n) p q w → (∀ δ : ℝ, 0 < δ → ∃ w' : ℝ → Bridge.Sub hN,
        InOmega (n := n) p q w' ∧ dOm (n := n) w w' < δ ∧ Efun (n := n) w' ≤ c) →
        Efun (n := n) w ≤ c) ∧
    (∀ w ∈ IntOmegaC (n := n) p q c, ∃ δ : ℝ, 0 < δ ∧ ∀ w' : ℝ → Bridge.Sub hN,
        InOmega (n := n) p q w' → dOm (n := n) w w' < δ → w' ∈ IntOmegaC (n := n) p q c)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds**: A's continuity of `E_0^1` on `Ω(N; p, q)` (conjunct
`continuous_energy`), read through `d = edist` (`Emb.edist_eq`) and `E = Morse.energy`
(`Bridge.energy_eq`); closedness and openness follow. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ p q c
  have hcont : Continuous fun γ : Morse.PathSp N (Bridge.incl hN p) (Bridge.incl hN q) =>
      Morse.energy γ 0 1 := hA.2.2.1 le_rfl zero_le_one le_rfl
  -- the `ε`-`δ` continuity
  have h1 : ∀ w : ℝ → Bridge.Sub hN, InOmega (n := n) p q w → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ w' : ℝ → Bridge.Sub hN, InOmega (n := n) p q w' →
      dOm (n := n) w w' < δ → |Efun (n := n) w' - Efun (n := n) w| < ε := by
    intro w hw ε hε
    obtain ⟨δ, hδ, hδε⟩ := EMetric.continuous_iff.1 hcont (Emb.pt hw) (ENNReal.ofReal ε)
      (ENNReal.ofReal_pos.2 hε)
    obtain ⟨r, -, hr0, hrδ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
    refine ⟨r, ENNReal.ofReal_pos.1 hr0, fun w' hw' hd => ?_⟩
    have hlt : edist (Emb.pt hw') (Emb.pt hw) < δ := by
      rw [edist_comm, Emb.edist_eq hw hw']
      exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.ofReal_pos.1 hr0)).2 hd |>.trans hrδ
    have h := hδε _ hlt
    rw [edist_lt_ofReal, Real.dist_eq] at h
    rw [Emb.efun_eq, Emb.efun_eq]
    exact h
  refine ⟨h1, fun w hw happ => ?_, fun w hw => ?_⟩
  · by_contra hgt
    push Not at hgt
    obtain ⟨δ, hδ, hδε⟩ := h1 w hw _ (sub_pos.2 hgt)
    obtain ⟨w', hw', hd, hle⟩ := happ δ hδ
    have := hδε w' hw' hd
    rw [abs_lt] at this
    linarith [this.1]
  · obtain ⟨δ, hδ, hδε⟩ := h1 w hw.1 _ (sub_pos.2 hw.2)
    refine ⟨δ, hδ, fun w' hw' hd => ⟨hw', ?_⟩⟩
    have := hδε w' hw' hd
    rw [abs_lt] at this
    linarith [this.2]

/-- The part of A that B covers on embedded manifolds: continuity of `E = E_0^1` on `Ω(N; p, q)`
(hence `Ω^c` closed and `Int Ω^c` open), for model `ℝⁿ` and connected `↥N`. -/
def A_cont : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)] (p q : V),
    Continuous fun γ : Morse.PathSp N p q => Morse.energy γ 0 1

theorem A_to_A_cont : A → A_cont := fun hA _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
  hA.2.2.1 le_rfl zero_le_one le_rfl

/-- **B on embedded manifolds implies the continuity of `E_0^1`** on `Ω(N; p, q)` (model `ℝⁿ`,
`↥N` connected): lift paths to `↥N` (`Emb.inOmega_lift`), compare distances by `Emb.edist_eq`
(and `PathSp.edist_eq_zero_of_eqOn`, a theorem of item V10_1, for the lift), energies by
`Bridge.energy_eq`. -/
theorem B_emb_to_A_cont : B_emb → A_cont := by
  intro hB V _ _ _ W _ _ _ n N hN _ p q
  refine EMetric.continuous_iff.2 fun γ ε hε => ?_
  have hpN : p ∈ N := γ.2.2.2.1 ▸ γ.2.2.1 0 ⟨le_rfl, zero_le_one⟩
  have hqN : q ∈ N := γ.2.2.2.2 ▸ γ.2.2.1 1 ⟨zero_le_one, le_rfl⟩
  let p' : Bridge.Sub hN := (⟨p, hpN⟩ : N)
  let q' : Bridge.Sub hN := (⟨q, hqN⟩ : N)
  have hmem : ∀ γ' : Morse.PathSp N p q,
      (γ' : ℝ → V) ∈ Morse.pathSpace N (Bridge.incl hN p') (Bridge.incl hN q') := fun γ' => γ'.2
  obtain ⟨hw, heqw⟩ := Emb.inOmega_lift (hmem γ)
  obtain ⟨r, -, hr0, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr : 0 < r := ENNReal.ofReal_pos.1 hr0
  obtain ⟨δ, hδ, hδr⟩ := (hB V W n N hN p' q' 0).1 _ hw r hr
  refine ⟨ENNReal.ofReal δ, ENNReal.ofReal_pos.2 hδ, fun γ' hγ' => ?_⟩
  obtain ⟨hw', heqw'⟩ := Emb.inOmega_lift (hmem γ')
  have e0 : edist (Emb.pt hw : Morse.PathSp N p q) γ = 0 :=
    Morse.PathSp.edist_eq_zero_of_eqOn heqw
  have e0' : edist γ' (Emb.pt hw' : Morse.PathSp N p q) = 0 :=
    Morse.PathSp.edist_eq_zero_of_eqOn fun t ht => (heqw' ht).symm
  have hd : edist (Emb.pt hw : Morse.PathSp N p q) (Emb.pt hw') < ENNReal.ofReal δ := by
    calc edist (Emb.pt hw : Morse.PathSp N p q) (Emb.pt hw')
        ≤ edist (Emb.pt hw : Morse.PathSp N p q) γ + edist γ γ' +
            edist γ' (Emb.pt hw' : Morse.PathSp N p q) := edist_triangle4 _ _ _ _
      _ = edist γ' γ := by rw [e0, e0', zero_add, add_zero, edist_comm]
      _ < _ := hγ'
  rw [Emb.edist_eq hw hw'] at hd
  have hdl := hδr _ hw' ((ENNReal.ofReal_lt_ofReal_iff hδ).1 hd)
  rw [Emb.efun_eq, Emb.efun_eq, Morse.energy_congr fun t ht => heqw ht,
    Morse.energy_congr fun t ht => heqw' ht] at hdl
  rw [edist_dist, Real.dist_eq]
  exact (ENNReal.ofReal_lt_ofReal_iff hr |>.2 hdl).trans hrε

#rt_check RoundTrip.V10_2.A_to_B_emb [Morse.PathSp.abs_sqrt_energy_sub_le, Morse.PathSp.lipschitzWith_sqrt_energy, Morse.PathSp.continuous_energy, Morse.PathSp.isClosed_sublevel, Morse.PathSp.isOpen_sublevel_lt, Morse.PathSp.exists_energy_lt_of_tendsto]
#rt_check RoundTrip.V10_2.B_emb_to_A_cont [Morse.PathSp.abs_sqrt_energy_sub_le, Morse.PathSp.lipschitzWith_sqrt_energy, Morse.PathSp.continuous_energy, Morse.PathSp.isClosed_sublevel, Morse.PathSp.isOpen_sublevel_lt, Morse.PathSp.exists_energy_lt_of_tendsto]
#rt_overlap RoundTrip.V10_2.B_emb_to_A_cont [Morse.PathSp.abs_sqrt_energy_sub_le, Morse.PathSp.lipschitzWith_sqrt_energy, Morse.PathSp.continuous_energy, Morse.PathSp.isClosed_sublevel, Morse.PathSp.isOpen_sublevel_lt, Morse.PathSp.exists_energy_lt_of_tendsto]
#rt_overlap RoundTrip.V10_2.A_to_B_emb [Morse.PathSp.abs_sqrt_energy_sub_le, Morse.PathSp.lipschitzWith_sqrt_energy, Morse.PathSp.continuous_energy, Morse.PathSp.isClosed_sublevel, Morse.PathSp.isOpen_sublevel_lt, Morse.PathSp.exists_energy_lt_of_tendsto]

end RoundTrip.V10_2
