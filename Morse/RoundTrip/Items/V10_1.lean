import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_1
import RoundTrip.Bridge

open Set Filter Topology Function Module MeasureTheory
open scoped ContDiff Manifold ENNReal

namespace RoundTrip.V10_1

/-- The project's statement (universe instantiated at `0`): the only theorem of the item is that
Milnor's distance on `Morse.PathSp N p q` (an extended pseudometric, `Morse.PathSp.instPseudoEMetricSpace`,
`edist γ γ' = supDist N γ γ' + ofReal (l2Dist γ γ')`, for ANY set `N` in an inner product space) gives
distance `0` to paths agreeing on `[0, 1]`. `PathSp`, `speed`, `supDist`, `l2Dist` and the instance
are vocabulary. -/
def A : Prop := type_of% @Morse.PathSp.edist_eq_zero_of_eqOn.{0}

theorem A_holds : A := @Morse.PathSp.edist_eq_zero_of_eqOn

/-- `A` is provable outright from the definitions (both parts of `edist` only see `[0, 1]`). -/
theorem A_outright : A := by
  intro V _ _ N p q α β h
  rw [Morse.PathSp.edist_def, Morse.PathSp.supDist_congr h (fun _ _ => rfl),
    Morse.PathSp.l2Dist_congr h (fun _ _ => rfl), Morse.PathSp.supDist_self β.mem,
    Morse.PathSp.l2Dist_self, ENNReal.ofReal_zero, add_zero]

/-- **B ⇒ A, vacuously**: A holds outright (`A_outright`); the hypothesis is not used. -/
theorem B_to_A : B → A := fun _ => A_outright

/-! `A → B` is not proved: B quantifies over abstract connected Hausdorff `ℝⁿ`-manifolds with an
arbitrary smooth metric (and Levi-Civita connection), A only over sets `N ⊆ V`; and A lacks B's
content (that `d` is a metric: symmetry, the triangle inequality, `d = 0 ⇒ w = w'` on `[0, 1]`).

## The embedded special case

The substantive comparison is of the definitions. On `↥N` (model `ℝⁿ`, induced metric) the blind
`dOm` is the project's `edist` (`Emb.edist_eq`): the sup parts agree through `Bridge.rho_eq`
(`ρ = riemDist.toReal`, the sup being finite, `Emb.supDist_ne_top`), and the `L²` parts agree because
`ds/dt` (the derivative of the arc length) is `‖γ'‖` off the finitely many break points
(`Emb.dsdt_eq`, by the fundamental theorem of calculus). Hence B on `↥N` follows from A and the
project's pseudometric axioms (`A_to_B_emb`). -/

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

end Emb

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric) with the induced Levi-Civita
connection `Bridge.conn` (a special case of B, see `B_to_B_emb`; the claim does not involve the
connection). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ p q : Bridge.Sub hN, ∀ w w' w'' : ℝ → Bridge.Sub hN, InOmega (n := n) p q w →
      InOmega (n := n) p q w' → InOmega (n := n) p q w'' →
      0 ≤ dOm (n := n) w w' ∧ (dOm (n := n) w w' = 0 ↔ Set.EqOn w w' (Set.Icc 0 1)) ∧
      dOm (n := n) w w' = dOm (n := n) w' w ∧
      dOm (n := n) w w'' ≤ dOm (n := n) w w' + dOm (n := n) w' w''

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds**: through the dictionary `Emb.edist_eq`, `d = edist` on
`Ω(↥N; p, q)`; A gives `w = w'` on `[0, 1] ⇒ d = 0`; symmetry and the triangle inequality are those
of the project's pseudometric, and `d = 0 ⇒ w = w'` is positivity of `ρ`
(`Morse.eq_of_riemDist_eq_zero`). -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ p q w w' w'' hw hw' hw''
  have e₁ := Emb.edist_eq hw hw'
  have e₂ := Emb.edist_eq hw' hw
  have e₃ := Emb.edist_eq hw hw''
  have e₄ := Emb.edist_eq hw' hw''
  have h₁ := Emb.dOm_nonneg hw hw'
  have h₂ := Emb.dOm_nonneg hw' hw
  have h₃ := Emb.dOm_nonneg hw hw''
  have h₄ := Emb.dOm_nonneg hw' hw''
  refine ⟨h₁, ⟨fun h0 => ?_, fun heq => ?_⟩, ?_, ?_⟩
  · -- `d = 0 ⇒ w = w'` on `[0, 1]`
    rw [h0, ENNReal.ofReal_zero, Morse.PathSp.edist_def] at e₁
    have hs := (add_eq_zero.1 e₁).1
    intro t ht
    have h := (Morse.PathSp.riemDist_le_supDist (N := N) (γ := Bridge.incl hN ∘ w)
      (γ' := Bridge.incl hN ∘ w') ht).trans_eq hs
    exact Morse.eq_of_riemDist_eq_zero hN (p := (w t : N)) (q := (w' t : N)) (le_zero_iff.1 h)
  · -- `w = w'` on `[0, 1] ⇒ d = 0`: this is A
    have h := @hA V _ _ N _ _ (Emb.pt hw) (Emb.pt hw')
      (fun t ht => congrArg (Bridge.incl hN) (heq ht))
    rw [e₁] at h
    exact le_antisymm (ENNReal.ofReal_eq_zero.1 h) h₁
  · -- symmetry
    have h := edist_comm (Emb.pt hw) (Emb.pt hw')
    rw [e₁, e₂] at h
    exact (ENNReal.ofReal_eq_ofReal_iff h₁ h₂).1 h
  · -- the triangle inequality
    have h := edist_triangle (Emb.pt hw) (Emb.pt hw') (Emb.pt hw'')
    rw [e₃, e₁, e₄, ← ENNReal.ofReal_add h₁ h₄] at h
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg h₁ h₄)).1 h

#rt_check RoundTrip.V10_1.B_to_A [Morse.PathSp.edist_eq_zero_of_eqOn]
#rt_overlap RoundTrip.V10_1.B_to_A [Morse.PathSp.edist_eq_zero_of_eqOn]
#rt_check RoundTrip.V10_1.A_to_B_emb [Morse.PathSp.edist_eq_zero_of_eqOn]
#rt_overlap RoundTrip.V10_1.A_to_B_emb [Morse.PathSp.edist_eq_zero_of_eqOn]

end RoundTrip.V10_1
