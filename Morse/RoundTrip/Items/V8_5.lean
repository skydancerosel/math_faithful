import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_5
import RoundTrip.Bridge

open Set Filter Topology MeasureTheory
open scoped ContDiff Manifold Interval

namespace RoundTrip.V8_5

/-- The project's statement (universes instantiated at 0): for any path `c : ℝ → E` into a real
normed space, piecewise smooth on `[a, b]`: Schwarz's inequality `L_a^b(c)² ≤ (b - a) E_a^b(c)`,
with equality iff the speed `‖c'‖` is constant at the points of `(a, b)` where `c` is
differentiable; and for an admissible path of constant speed `k`, `E_a^b = k² (b - a)`. -/
def A : Prop :=
  type_of% @Morse.pathLength_sq_le_energy.{0} ∧
    type_of% @Morse.pathLength_sq_eq_energy_iff.{0} ∧
    type_of% @Morse.energy_eq_of_norm_deriv.{0}

theorem A_holds : A :=
  ⟨@Morse.pathLength_sq_le_energy, @Morse.pathLength_sq_eq_energy_iff,
    @Morse.energy_eq_of_norm_deriv⟩

/-! Neither `A → B` nor `B → A` is proved; see `V8_5.json`. B quantifies over abstract connected
Riemannian `ℝⁿ`-manifolds (Riemannian norm of `mfderiv`), A over paths in a real normed space
(any norm, not only Euclidean, and `a < b` arbitrary). Below: the embedded special case. -/

namespace Emb

set_option linter.unusedSectionVars false

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- B's three claims for a path `c` in `V` on `[a, b]`. -/
def Bv (c : ℝ → V) (a b : ℝ) : Prop :=
  Morse.pathLength c a b ^ 2 ≤ (b - a) * Morse.energy c a b ∧
    (Morse.pathLength c a b ^ 2 = (b - a) * Morse.energy c a b ↔
      ∃ k : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a b → ‖deriv c t‖ = k) ∧
    (Morse.pathLength c a b ^ 2 = (b - a) * Morse.energy c a b ↔
      ∀ t ∈ Icc a b, Morse.pathLength c a t = (t - a) / (b - a) * Morse.pathLength c a b)

/-- The project's form of the equality case, restricted to `0 ≤ a < b ≤ 1`. -/
def Av (c : ℝ → V) (a b : ℝ) : Prop :=
  Morse.pathLength c a b ^ 2 ≤ (b - a) * Morse.energy c a b ∧
    (Morse.pathLength c a b ^ 2 = (b - a) * Morse.energy c a b ↔
      ∃ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ c t → ‖deriv c t‖ = k)

theorem ae_ne (b : ℝ) : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b :=
  measure_eq_zero_iff_ae_notMem.1 (measure_singleton (μ := volume) b)

/-- "Constant speed a.e." is "constant speed at the points of differentiability", for piecewise
smooth paths (the second direction by continuity on the closed pieces, as in the project). -/
theorem ae_const_iff {c : ℝ → V} {a b : ℝ} (hc : Morse.IsPiecewiseSmooth c a b) :
    (∃ k : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a b → ‖deriv c t‖ = k) ↔
      ∃ k, ∀ t ∈ Ioo a b, DifferentiableAt ℝ c t → ‖deriv c t‖ = k := by
  constructor
  · rintro ⟨k, hae⟩
    refine ⟨k, fun t ht hdt => ?_⟩
    obtain ⟨-, -, B, hB⟩ := hc
    obtain ⟨s, has, hst, hBs⟩ := Morse.exists_piece_left B ht.1
    have hpiece := hB s t has hst ht.2.le hBs
    obtain ⟨hd1, hd2⟩ := Morse.IsPiecewiseSmooth.derivWithin_piece hst hpiece
    set G : ℝ → ℝ := fun x => ‖derivWithin c (Icc s t) x‖
    have hG : ContinuousOn G (Icc s t) := hd1.continuousOn.norm
    have hGae : G =ᵐ[volume.restrict (Icc s t)] fun _ => k := by
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hae] with x hx hxs
      simp only [G, ← hd2 hxs]
      exact hx ⟨has.trans_lt hxs.1, hxs.2.trans ht.2⟩
    have hclos : Icc s t ⊆ closure (interior (Icc s t)) := by
      rw [interior_Icc, closure_Ioo hst.ne]
    have hGt := Measure.eqOn_of_ae_eq hGae hG continuousOn_const hclos
      (right_mem_Icc.2 hst.le)
    simp only [G] at hGt
    rwa [Morse.derivWithin_eq_deriv_of_piece hst (right_mem_Icc.2 hst.le) hdt] at hGt
  · rintro ⟨k, hk⟩
    obtain ⟨C, hC, hd⟩ := hc.isAdmissible.countable
    refine ⟨k, ?_⟩
    filter_upwards [hC.ae_notMem volume] with t htC ht
    exact hk t ht (hd t ⟨ht, htC⟩)

/-- Constant speed a.e. computes `L` and `E`. -/
theorem eq_of_ae_const {c : ℝ → V} {a b k : ℝ} (hab : a ≤ b)
    (hae : ∀ᵐ t ∂volume, t ∈ Ioo a b → ‖deriv c t‖ = k) :
    Morse.pathLength c a b = k * (b - a) ∧ Morse.energy c a b = k ^ 2 * (b - a) := by
  have hae' : ∀ᵐ t ∂volume, t ∈ Ι a b → ‖deriv c t‖ = k := by
    filter_upwards [hae, ae_ne b] with t h1 h2 ht
    rw [uIoc_of_le hab] at ht
    exact h1 ⟨ht.1, lt_of_le_of_ne ht.2 h2⟩
  constructor
  · rw [Morse.pathLength, intervalIntegral.integral_congr_ae hae']
    simp [mul_comm]
  · have hae2 : ∀ᵐ t ∂volume, t ∈ Ι a b → ‖deriv c t‖ ^ 2 = k ^ 2 := by
      filter_upwards [hae'] with t h ht
      rw [h ht]
    rw [Morse.energy, intervalIntegral.integral_congr_ae hae2]
    simp [mul_comm]

/-- On a piece around `t`, the speed is continuous at `t`. -/
theorem continuousOn_speed {c : ℝ → V} {s s' : ℝ} (hss' : s < s')
    (hc : ContDiffOn ℝ ∞ c (Icc s s')) : ContinuousOn (fun x => ‖deriv c x‖) (Ioo s s') := by
  obtain ⟨hd1, hd2⟩ := Morse.IsPiecewiseSmooth.derivWithin_piece hss' hc
  refine (hd1.continuousOn.norm.mono Ioo_subset_Icc_self).congr fun x hx => ?_
  simp only [hd2 hx]

/-- **B's three claims from A**, for a piecewise smooth path in `V` (any `a < b`). -/
theorem Bv_of_A (hA : A) {c : ℝ → V} {a b : ℝ} (hc : Morse.IsPiecewiseSmooth c a b) (hab : a < b) :
    Bv c a b := by
  obtain ⟨hA1, hA2, -⟩ := hA
  have hpos : 0 < b - a := sub_pos.2 hab
  have h2 : Morse.pathLength c a b ^ 2 = (b - a) * Morse.energy c a b ↔
      ∃ k : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a b → ‖deriv c t‖ = k := by
    rw [ae_const_iff hc]
    exact hA2 hc
  refine ⟨hA1 hc, h2, ?_⟩
  constructor
  · intro heq
    obtain ⟨k, hk⟩ := (hA2 hc).1 heq
    have hL : Morse.pathLength c a b = k * (b - a) :=
      Morse.pathLength_eq_of_norm_deriv hc.isAdmissible hk
    intro t ht
    have hLt : Morse.pathLength c a t = k * (t - a) :=
      Morse.pathLength_eq_of_norm_deriv (hc.isAdmissible.mono le_rfl ht.1 ht.2)
        fun x hx hdx => hk x ⟨hx.1, hx.2.trans_le ht.2⟩ hdx
    rw [hLt, hL]
    field_simp
  · intro hlin
    refine h2.2 ⟨Morse.pathLength c a b / (b - a), ?_⟩
    have hadm := hc.isAdmissible
    obtain ⟨-, -, B, hB⟩ := hc
    filter_upwards [B.countable_toSet.ae_notMem volume] with t htB ht
    obtain ⟨s, s', has, hst, hts', hs'b, hBs⟩ := Morse.exists_piece_around B ht.1 ht.2 htB
    have hpiece := hB s s' has (hst.trans hts') hs'b hBs
    have hcont := continuousOn_speed (hst.trans hts') hpiece
    have hcat : ContinuousAt (fun x => ‖deriv c x‖) t :=
      hcont.continuousAt (Ioo_mem_nhds hst hts')
    have hint : IntervalIntegrable (fun x => ‖deriv c x‖) volume a t :=
      hadm.integrable.mono_set (by
        rw [uIcc_of_le ht.1.le, uIcc_of_le hab.le]
        exact Icc_subset_Icc le_rfl ht.2.le)
    have hmeas : StronglyMeasurableAtFilter (fun x => ‖deriv c x‖) (𝓝 t) volume :=
      hcont.stronglyMeasurableAtFilter isOpen_Ioo t ⟨hst, hts'⟩
    have hd1 : HasDerivAt (fun u => ∫ x in a..u, ‖deriv c x‖) ‖deriv c t‖ t :=
      intervalIntegral.integral_hasDerivAt_right hint hmeas hcat
    have hd2 : HasDerivAt (fun u => (u - a) / (b - a) * Morse.pathLength c a b)
        (Morse.pathLength c a b / (b - a)) t := by
      have h0 : HasDerivAt (fun u : ℝ => (u - a) / (b - a) * Morse.pathLength c a b)
          (1 / (b - a) * Morse.pathLength c a b) t :=
        (((hasDerivAt_id' t).sub_const a).div_const (b - a)).mul_const (Morse.pathLength c a b)
      exact h0.congr_deriv (by ring)
    have hev : (fun u => ∫ x in a..u, ‖deriv c x‖) =ᶠ[𝓝 t]
        fun u => (u - a) / (b - a) * Morse.pathLength c a b := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact hlin u (Ioo_subset_Icc_self hu)
    exact (hd1.congr_of_eventuallyEq hev.symm).unique hd2 |>.symm ▸ rfl

theorem eventuallyEq_of_eqOn {c c' : ℝ → V} {a b t : ℝ} (h : EqOn c c' (Icc a b))
    (ht : t ∈ Ioo a b) : c =ᶠ[𝓝 t] c' := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
  exact h (Ioo_subset_Icc_self hy)

theorem energy_congr {c c' : ℝ → V} {a b : ℝ} (hab : a ≤ b) (h : EqOn c c' (Icc a b)) :
    Morse.energy c a b = Morse.energy c' a b := by
  unfold Morse.energy
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne b] with x hx hxab
  rw [uIoc_of_le hab] at hxab
  rw [(eventuallyEq_of_eqOn h ⟨hxab.1, lt_of_le_of_ne hxab.2 hx⟩).deriv_eq]

theorem Bv_congr {c c' : ℝ → V} {a b : ℝ} (hab : a < b) (h : EqOn c c' (Icc a b)) :
    Bv c a b ↔ Bv c' a b := by
  have hL : ∀ t ∈ Icc a b, Morse.pathLength c a t = Morse.pathLength c' a t := fun t ht =>
    RoundTrip.Bridge.pathLength_congr ht.1 (h.mono (Icc_subset_Icc le_rfl ht.2))
  have hE := energy_congr hab.le h
  have hD : ∀ t ∈ Ioo a b, deriv c t = deriv c' t := fun t ht =>
    (eventuallyEq_of_eqOn h ht).deriv_eq
  have hae : (∃ k : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a b → ‖deriv c t‖ = k) ↔
      ∃ k : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a b → ‖deriv c' t‖ = k :=
    exists_congr fun k => Filter.eventually_congr (.of_forall fun t =>
      forall_congr' fun ht => by rw [hD t ht])
  unfold Bv
  rw [hL b (right_mem_Icc.2 hab.le), hE, hae]
  refine and_congr Iff.rfl (and_congr Iff.rfl (iff_congr Iff.rfl (forall₂_congr fun t ht => ?_)))
  rw [hL t ht]

theorem Av_congr {c c' : ℝ → V} {a b : ℝ} (hab : a < b) (h : EqOn c c' (Icc a b)) :
    Av c a b ↔ Av c' a b := by
  have hD : ∀ t ∈ Ioo a b, deriv c t = deriv c' t := fun t ht =>
    (eventuallyEq_of_eqOn h ht).deriv_eq
  have hDiff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ c t ↔ DifferentiableAt ℝ c' t := fun t ht =>
    (eventuallyEq_of_eqOn h ht).differentiableAt_iff
  unfold Av
  rw [RoundTrip.Bridge.pathLength_congr hab.le h, energy_congr hab.le h]
  refine and_congr Iff.rfl (iff_congr Iff.rfl (exists_congr fun k => forall₂_congr fun t ht => ?_))
  rw [hD t ht, hDiff t ht]

/-- On a piecewise smooth path, B's three claims give the project's two (equality case read
pointwise instead of a.e.). -/
theorem Av_of_Bv {c : ℝ → V} {a b : ℝ} (hc : Morse.IsPiecewiseSmooth c a b) (h : Bv c a b) :
    Av c a b :=
  ⟨h.1, h.2.1.trans (ae_const_iff hc)⟩

end Emb

open Bundle in
/-- B on embedded manifolds: `M = ↥N` with the induced metric (a special case of B, see
`B_to_B_emb`; no connection is involved). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ pw : ℝ → Bridge.Sub hN, IsPW (n := n) pw 0 1 → ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    arcLen (n := n) pw a b ^ 2 ≤ (b - a) * energy (n := n) pw a b ∧
    (arcLen (n := n) pw a b ^ 2 = (b - a) * energy (n := n) pw a b ↔
      ∃ c : ℝ, ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo a b →
        ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pw t (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pw t))‖ = c) ∧
    (arcLen (n := n) pw a b ^ 2 = (b - a) * energy (n := n) pw a b ↔
      ∀ t ∈ Set.Icc a b, arcLen (n := n) pw a t = (t - a) / (b - a) * arcLen (n := n) pw a b)

/-- `B_emb` is a special case of B. -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ => hB n (Bridge.Sub hN)

/-- The project's A1 ∧ A2 for paths in a (connected) slice submanifold `N ⊆ V` modelled on `ℝⁿ`,
piecewise smooth on `[0, 1]`, on subintervals `[a, b] ⊆ [0, 1]` with `a < b`. -/
def A_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ c : ℝ → V, Morse.IsPiecewiseSmooth c 0 1 → (∀ t ∈ Icc (0 : ℝ) 1, c t ∈ N) →
    ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 → Emb.Av c a b

open Bundle in
/-- B's claims for `pw : ℝ → ↥N`, read in `V` through the Bridge's dictionary. -/
theorem body_iff {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
    {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N} (pw : ℝ → Bridge.Sub hN) (a b : ℝ) :
    (arcLen (n := n) pw a b ^ 2 ≤ (b - a) * energy (n := n) pw a b ∧
    (arcLen (n := n) pw a b ^ 2 = (b - a) * energy (n := n) pw a b ↔
      ∃ c : ℝ, ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo a b →
        ‖(mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) pw t (1 : ℝ) : TangentSpace 𝓘(ℝ, Rn n) (pw t))‖ = c) ∧
    (arcLen (n := n) pw a b ^ 2 = (b - a) * energy (n := n) pw a b ↔
      ∀ t ∈ Set.Icc a b, arcLen (n := n) pw a t = (t - a) / (b - a) * arcLen (n := n) pw a b)) ↔
    Emb.Bv (Bridge.incl hN ∘ pw) a b := by
  have e1 : ∀ x y, arcLen (n := n) pw x y = Morse.pathLength (Bridge.incl hN ∘ pw) x y :=
    fun x y => Bridge.arcLen_eq pw x y
  have e2 : ∀ x y, energy (n := n) pw x y = Morse.energy (Bridge.incl hN ∘ pw) x y :=
    fun x y => Bridge.energy_eq pw x y
  simp only [e1, e2, Bridge.norm_mfderiv_curve, Emb.Bv]

/-- **A implies B on embedded manifolds.** -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ pw hpw a b ha hab hb
  rw [body_iff]
  exact Emb.Bv_of_A hA ((Bridge.isPiecewiseSmooth_of_isPW hpw).mono ha hab.le hb) hab

/-- **B on embedded manifolds implies A1 ∧ A2 for paths in `N`.** -/
theorem B_emb_to_A_emb : B_emb → A_emb := by
  intro h V _ _ _ W _ _ _ n N hN _ c hc hcN a b ha hab hb
  let p₀ : Bridge.Sub hN := ⟨c 0, hcN 0 ⟨le_rfl, zero_le_one⟩⟩
  have hpw := Bridge.isPW_lift (n := n) hc hcN p₀
  have hB := (body_iff _ a b).1 (h V W n N hN _ hpw a b ha hab hb)
  have heq : EqOn (Bridge.incl hN ∘ Bridge.lift c p₀) c (Icc a b) := fun t ht =>
    Bridge.incl_lift p₀ (hcN t ⟨ha.trans ht.1, ht.2.trans hb⟩)
  rw [Emb.Bv_congr hab heq] at hB
  exact Emb.Av_of_Bv (hc.mono ha hab.le hb) hB

theorem B_to_A_emb : B → A_emb := fun hB => B_emb_to_A_emb (B_to_B_emb hB)

#rt_check RoundTrip.V8_5.A_to_B_emb [Morse.pathLength_sq_le_energy,
  Morse.pathLength_sq_eq_energy_iff, Morse.energy_eq_of_norm_deriv]
#rt_check RoundTrip.V8_5.B_to_A_emb [Morse.pathLength_sq_le_energy,
  Morse.pathLength_sq_eq_energy_iff, Morse.energy_eq_of_norm_deriv]
#rt_overlap RoundTrip.V8_5.B_to_A_emb [Morse.pathLength_sq_le_energy,
  Morse.pathLength_sq_eq_energy_iff, Morse.energy_eq_of_norm_deriv]

end RoundTrip.V8_5
