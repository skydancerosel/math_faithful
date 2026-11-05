import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V7_28

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

set_option linter.unusedSectionVars false

namespace RoundTrip.V7_28.Aux

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

/-- A blind geodesic of the induced connection on `[a, b]` restricts to `[a, b']`, with the same
initial velocity. -/
theorem isGeodesic_Icc_mono {c : ℝ → Sub hN} {a b b' : ℝ} (hab' : a < b') (hb' : b' ≤ b)
    (h : BridgePrelude.IsGeodesic (conn (hN := hN)) c (Icc a b)) :
    BridgePrelude.IsGeodesic (conn (hN := hN)) c (Icc a b') ∧
      derivWithin (incl hN ∘ c) (Icc a b') a = derivWithin (incl hN ∘ c) (Icc a b) a := by
  obtain ⟨-, hc, hP⟩ := isGeodesic_iff.1 h
  have hsub : Icc a b' ⊆ Icc a b := Icc_subset_Icc le_rfl hb'
  have u' : UniqueDiffOn ℝ (Icc a b') := uniqueDiffOn_Icc hab'
  have u : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc (lt_of_lt_of_le hab' hb')
  have hd1 : ∀ t ∈ Icc a b', derivWithin (incl hN ∘ c) (Icc a b') t =
      derivWithin (incl hN ∘ c) (Icc a b) t :=
    fun t ht => derivWithin_subset hsub (u' t ht) ((hc.differentiableOn (by simp)) t (hsub ht))
  have hdc : ContDiffOn ℝ ∞ (derivWithin (incl hN ∘ c) (Icc a b)) (Icc a b) :=
    hc.derivWithin u (by simp)
  have hd2 : ∀ t ∈ Icc a b', derivWithin (derivWithin (incl hN ∘ c) (Icc a b')) (Icc a b') t =
      derivWithin (derivWithin (incl hN ∘ c) (Icc a b)) (Icc a b) t := by
    intro t ht
    rw [derivWithin_congr hd1 (hd1 t ht)]
    exact derivWithin_subset hsub (u' t ht) ((hdc.differentiableOn (by simp)) t (hsub ht))
  refine ⟨isGeodesic_iff.2 ⟨⟨ordConnected_Icc, u'⟩, hc.mono hsub, fun t ht => ?_⟩,
    hd1 a ⟨le_rfl, hab'.le⟩⟩
  rw [hd2 t ht]
  exact hP t (hsub ht)

/-- A project geodesic on an open set `s ⊇ [a, b]` lifts to a blind geodesic on `[a, b]`. -/
theorem isGeodesic_lift_Icc {γ : ℝ → V} {s : Set ℝ} (hγ : Morse.IsGeodesicOn hN γ s) {a b : ℝ}
    (hab : a < b) (hsub : Icc a b ⊆ s) (x : Sub hN) :
    BridgePrelude.IsGeodesic (conn (hN := hN)) (lift γ x) (Icc a b) ∧
      EqOn (incl hN ∘ lift γ x) γ (Icc a b) ∧
      derivWithin (incl hN ∘ lift γ x) (Icc a b) a = deriv γ a := by
  set I := Icc a b
  have uI : UniqueDiffOn ℝ I := uniqueDiffOn_Icc hab
  have heq : EqOn (incl hN ∘ lift γ x) γ I := fun t ht => incl_lift x (hγ.mem t (hsub ht))
  have hd : EqOn (derivWithin (incl hN ∘ lift γ x) I) (deriv γ) I := fun t ht => by
    rw [derivWithin_congr heq (heq ht)]
    exact (hγ.hasDerivAt (hsub ht)).hasDerivWithinAt.derivWithin (uI t ht)
  have hdd : ∀ t ∈ I, derivWithin (derivWithin (incl hN ∘ lift γ x) I) I t =
      deriv (deriv γ) t := fun t ht => by
    rw [derivWithin_congr hd (hd ht)]
    exact (hγ.hasDerivAt_deriv (hsub ht)).hasDerivWithinAt.derivWithin (uI t ht)
  refine ⟨isGeodesic_iff.2 ⟨⟨ordConnected_Icc, uI⟩, (hγ.contDiffOn.mono hsub).congr heq,
    fun t ht => ?_⟩, heq, hd ⟨le_rfl, hab.le⟩⟩
  rw [hdd t ht, lift_of_mem x (hγ.mem t (hsub ht))]
  exact hγ.tanProj_deriv_deriv (hsub ht)

/-- **Blind geodesic completeness gives the project's `exp`**: if every blind `exp` of the induced
connection is defined (geodesics on `[0, 1]`), then every `(q, v)`, `v ∈ T_qN`, lies in the
project's `expDom` (a geodesic on an OPEN interval `(-δ, 1 + δ)`). A geodesic on a closed interval
is extended by starting it a little before `q`: from `x₁ = exp_q(-τ/2 · v)` with a large speed,
compared with `t ↦ exp_q(tv)` by uniqueness from the initial point. -/
theorem mem_expDom_of_expDefined
    (hc : ∀ (x : Sub hN) (w : TangentSpace 𝓘(ℝ, Bridge.Rn n) x),
      BridgePrelude.ExpDefined (conn (hN := hN)) x w)
    (q : N) {v : V} (hv : v ∈ Morse.tangentSubspace hN q) : ((q : V), v) ∈ Morse.expDom hN := by
  obtain ⟨τ, hτ, hg, hgd⟩ := Morse.exists_isGeodesicOn_exp_smul q hv
  set g : ℝ → V := fun t => Morse.exp hN q (t • v) with hg_def
  set K : ℝ := τ + 2 with hK
  have hK0 : 0 < K := by positivity
  have hm : -τ / 2 ∈ Ioo (-τ) τ := ⟨by linarith, by linarith⟩
  set x₁ : Sub hN := (⟨g (-τ / 2), hg.mem _ hm⟩ : N) with hx₁
  set u₁ : V := deriv g (-τ / 2) with hu₁_def
  have hu₁ : K • u₁ ∈ Morse.tangentSubspace hN x₁ := Submodule.smul_mem _ _ (hg.deriv_mem hm)
  obtain ⟨c, hcg, hci⟩ := hc x₁ (L hN x₁ (K • u₁))
  have hc0 : c 0 = x₁ := hci.1
  have u01 : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hc0' : derivWithin (incl hN ∘ c) (Icc 0 1) 0 = K • u₁ := by
    have h1 := (initData_iff hc0).1 hci
    rw [D_vel (isSmoothCurve_iff.2 (isGeodesic_iff.1 hcg).2.1) u01 ⟨le_rfl, zero_le_one⟩] at h1
    rw [h1]
    exact D_L hu₁
  -- `h(s) = g(K s - τ/2)`, a project geodesic on an open interval around `0`
  have hh := hg.comp_mul_add K (-τ / 2)
  set S := (fun t => K * t + -τ / 2) ⁻¹' Ioo (-τ) τ with hS
  set h : ℝ → V := fun t => g (K * t + -τ / 2) with hh_def
  have hhd : ∀ t ∈ S, HasDerivAt h (K • deriv g (K * t + -τ / 2)) t := fun t ht => by
    have hlin : HasDerivAt (fun t : ℝ => K * t + -τ / 2) K t := by
      simpa using ((hasDerivAt_id t).const_mul K).add_const (-τ / 2)
    exact (hg.hasDerivAt ht).scomp t hlin
  set ε : ℝ := τ / K with hε
  have hε0 : 0 < ε := by positivity
  have hεK : K * ε = τ := by rw [hε]; field_simp
  have hε1 : ε < 1 := by rw [hε, div_lt_one hK0]; linarith
  have hsubS : Icc 0 ε ⊆ S := by
    intro t ht
    simp only [hS, mem_preimage, mem_Ioo]
    have h1 : K * t ≤ τ := by rw [← hεK]; exact mul_le_mul_of_nonneg_left ht.2 hK0.le
    have h2 : 0 ≤ K * t := mul_nonneg hK0.le ht.1
    constructor <;> linarith
  obtain ⟨hl, hleq, hld⟩ := isGeodesic_lift_Icc hh hε0 hsubS x₁
  obtain ⟨hcε, hcε'⟩ := isGeodesic_Icc_mono hε0 hε1.le hcg
  have h0S : (0 : ℝ) ∈ S := hsubS ⟨le_rfl, hε0.le⟩
  have hagree := eqOn_Icc_of_isGeodesic hε0 hl hcε ?_ ?_
  rotate_left
  · rw [hc0]
    apply Subtype.ext
    change incl hN (lift h x₁ 0) = g (-τ / 2)
    rw [incl_lift x₁ (hh.mem 0 h0S)]
    simp [hh_def]
  · rw [hld, hcε', hc0', (hhd 0 h0S).deriv]
    simp only [mul_zero, zero_add]
    rfl
  -- so `incl ∘ c = h` on `[0, ε]`, hence near `s₀ = ε / 2`
  have hEq : EqOn (incl hN ∘ c) h (Icc 0 ε) := fun t ht => by
    rw [← hleq ht]
    exact (congrArg (incl hN) (hagree ht)).symm
  set s₀ : ℝ := ε / 2 with hs₀
  have hs₀ε : s₀ ∈ Ioo 0 ε := ⟨by positivity, by linarith⟩
  have hev : incl hN ∘ c =ᶠ[𝓝 s₀] h :=
    eventually_of_mem (Ioo_mem_nhds hs₀ε.1 hs₀ε.2) fun t ht => hEq (Ioo_subset_Icc_self ht)
  have hKs₀ : K * s₀ + -τ / 2 = 0 := by rw [hs₀]; linarith [hεK]
  have hpos : (incl hN ∘ c) s₀ = q := by
    rw [hev.self_of_nhds]
    simp only [hh_def, hg_def, hKs₀, zero_smul]
    exact Morse.exp_zero q.2
  have hder : deriv (incl hN ∘ c) s₀ = K • v := by
    rw [hev.deriv_eq, (hhd s₀ (hsubS (Ioo_subset_Icc_self hs₀ε))).deriv, hKs₀, hgd.deriv]
  -- reparametrize: `γ(t) = c(t / K + s₀)`
  have hG := (isGeodesicOn_Ioo hcg).comp_mul_add (1 / K) s₀
  set δ : ℝ := min (τ / 2) 1 with hδ
  have hδ0 : 0 < δ := by positivity
  have hsubP : Ioo (-δ) (1 + δ) ⊆ (fun t => 1 / K * t + s₀) ⁻¹' Ioo 0 1 := by
    intro t ht
    have hδ1 : δ ≤ τ / 2 := min_le_left _ _
    have hδ2 : δ ≤ 1 := min_le_right _ _
    have hs₀' : s₀ = τ / (2 * K) := by rw [hs₀, hε]; field_simp
    simp only [mem_preimage, mem_Ioo]
    constructor
    · rw [hs₀']
      have : -τ / 2 < t := by linarith [ht.1]
      have h3 : 1 / K * t > 1 / K * (-τ / 2) := mul_lt_mul_of_pos_left this (by positivity)
      have h4 : 1 / K * (-τ / 2) + τ / (2 * K) = 0 := by field_simp; ring
      linarith
    · rw [hs₀']
      have : t < 2 := by linarith [ht.2]
      have h3 : 1 / K * t < 1 / K * 2 := mul_lt_mul_of_pos_left this (by positivity)
      have h4 : 1 / K * 2 + τ / (2 * K) < 1 := by
        have e : 1 / K * 2 + τ / (2 * K) = (4 + τ) / (2 * K) := by field_simp; ring
        rw [e, div_lt_one (by positivity)]
        linarith
      linarith
  refine ⟨fun t => (incl hN ∘ c) (1 / K * t + s₀), δ, hδ0, hG.mono isOpen_Ioo hsubP, ?_, ?_⟩
  · simpa using hpos
  · have hs₀1 : s₀ ∈ Ioo (0 : ℝ) 1 := ⟨hs₀ε.1, hs₀ε.2.trans hε1⟩
    have hlin : HasDerivAt (fun t : ℝ => 1 / K * t + s₀) (1 / K) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 / K)).add_const s₀
    have h1 := ((isGeodesicOn_Ioo hcg).hasDerivAt (s := Ioo 0 1) (t := 1 / K * 0 + s₀)
      (by simpa using hs₀1)).scomp (0 : ℝ) hlin
    change deriv ((incl hN ∘ c) ∘ fun t => 1 / K * t + s₀) 0 = v
    rw [h1.deriv]
    simp only [mul_zero, zero_add]
    rw [hder, smul_smul, one_div, inv_mul_cancel₀ hK0.ne', one_smul]


/-! ### Changing the model space, open parts, and the tangent spaces -/

section Model

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A linear equivalence `Z ≃ ℝᵐ`, `m = dim Z`. -/
def eZ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] :
    Z ≃L[ℝ] Bridge.Rn (finrank ℝ Z) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- A slice chart modelled on `Z`, read in `ℝᵐ`. -/
def chartRn (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
    Milnor.SliceChart 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W N where
  φ := σ.φ.trans ((eZ Z).prodCongr (ContinuousLinearEquiv.refl ℝ W)).toDiffeomorph.toPartialDiffeomorph
  x₀ := σ.x₀
  x₀_mem := σ.x₀_mem
  x₀_source := ⟨σ.x₀_source, trivial⟩
  slice := fun p hp => σ.slice p hp.1

/-- A slice submanifold modelled on `Z` is one modelled on `ℝᵐ`. -/
theorem isSliceRn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W N :=
  fun p hp => ⟨chartRn (hN p hp).choose, ⟨(hN p hp).choose_spec, trivial⟩⟩

/-- ... with the same tangent spaces. -/
theorem tangentSubspace_rn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) (q : N) :
    Morse.tangentSubspace (isSliceRn hN) q = Morse.tangentSubspace hN q := by
  obtain ⟨σ, hσ⟩ := hN q q.2
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam (isSliceRn hN) (chartRn σ) ⟨hσ, trivial⟩,
    Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  have e1 : Morse.sliceParam (chartRn σ) = Morse.sliceParam σ ∘ (eZ Z).symm := rfl
  have e2 : ((chartRn σ).φ q).1 = eZ Z (σ.φ q).1 := rfl
  rw [e1, e2, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearEquiv.symm_apply_apply]
  exact LinearMap.range_comp_of_range_eq_top
    ((fderiv ℝ (Morse.sliceParam σ) (σ.φ q).1 : Z →L[ℝ] V) : Z →ₗ[ℝ] V)
    (LinearMap.range_eq_top.2 (eZ Z).symm.surjective)

/-- An open part has the same tangent spaces. -/
theorem tangentSubspace_inter (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {O : Set V}
    (hO : IsOpen O) (x : V) (hx : x ∈ N ∩ O) :
    Morse.tangentSubspace (Morse.IsSliceSubmanifold.inter_isOpen hN hO) ⟨x, hx⟩ =
      Morse.tangentSubspace hN ⟨x, hx.1⟩ := by
  obtain ⟨σ, hσ⟩ := hN x hx.1
  rw [Morse.tangentSubspace_eq_range_fderiv_sliceParam _ (Morse.SliceChart.inter σ hO hx hσ)
    ⟨hσ, hx.2⟩, Morse.tangentSubspace_eq_range_fderiv_sliceParam hN σ hσ]
  rfl

end Model

section Mono

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z₁ : Type} [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁] {W₁ : Type} [NormedAddCommGroup W₁]
  [NormedSpace ℝ W₁] {Z₂ : Type} [NormedAddCommGroup Z₂] [NormedSpace ℝ Z₂] {W₂ : Type}
  [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] {N₁ N₂ : Set V}
  {hN₁ : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z₁ W₁ N₁}
  {hN₂ : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z₂ W₂ N₂}

/-- Geodesics of `N₁ ⊆ N₂` with the same tangent spaces are geodesics of `N₂`. -/
theorem isGeodesicOn_mono (hsub : N₁ ⊆ N₂)
    (hT : ∀ x (h₁ : x ∈ N₁), Morse.tangentSubspace hN₁ ⟨x, h₁⟩ =
      Morse.tangentSubspace hN₂ ⟨x, hsub h₁⟩)
    {γ : ℝ → V} {s : Set ℝ} (h : Morse.IsGeodesicOn hN₁ γ s) : Morse.IsGeodesicOn hN₂ γ s :=
  ⟨h.isOpen, fun t ht => hsub (h.mem t ht), h.contDiffOn, fun t ht => by
    have := h.normal t ht
    rwa [hT] at this⟩

theorem mem_expDom_mono (hsub : N₁ ⊆ N₂)
    (hT : ∀ x (h₁ : x ∈ N₁), Morse.tangentSubspace hN₁ ⟨x, h₁⟩ =
      Morse.tangentSubspace hN₂ ⟨x, hsub h₁⟩)
    {q v : V} (h : (q, v) ∈ Morse.expDom hN₁) : (q, v) ∈ Morse.expDom hN₂ := by
  obtain ⟨γ, δ, hδ, hγ, h0, h0'⟩ := h
  exact ⟨γ, δ, hδ, isGeodesicOn_mono hsub hT hγ, h0, h0'⟩

end Mono

section Component

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {m : ℕ} {N : Set V}

/-- The connected component of `q` in a slice submanifold is an open part `N ∩ O`, connected, and
piecewise smooth paths in `N` starting in it stay in it. -/
theorem exists_component (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn m) W N) (q : N) :
    ∃ O : Set V, IsOpen O ∧ (q : V) ∈ O ∧ IsConnected (N ∩ O) ∧
      ∀ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) →
        c a ∈ N ∩ O → ∀ t ∈ Icc a b, c t ∈ N ∩ O := by
  let _ := hN.chartedSpace
  have := ChartedSpace.locallyConnectedSpace (Bridge.Rn m) N
  have hK : IsOpen (connectedComponent q) := isOpen_connectedComponent
  obtain ⟨O, hO, hOK⟩ := isOpen_induced_iff.1 hK
  have hNO : N ∩ O = connectedComponentIn N (q : V) := by
    rw [connectedComponentIn_eq_image q.2]
    ext x
    constructor
    · rintro ⟨hxN, hxO⟩
      refine ⟨⟨x, hxN⟩, ?_, rfl⟩
      rw [← hOK]
      exact hxO
    · rintro ⟨y, hyK, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [← hOK] at hyK
      exact hyK
  refine ⟨O, hO, ?_, ?_, ?_⟩
  · have : q ∈ connectedComponent q := mem_connectedComponent
    rw [← hOK] at this
    exact this
  · rw [hNO]
    exact isConnected_connectedComponentIn_iff.2 q.2
  · intro c a b hc hcN ha t ht
    rw [hNO] at ha ⊢
    rw [connectedComponentIn_eq ha]
    have hpre : IsPreconnected (c '' Icc a b) := isPreconnected_Icc.image c hc.2.1
    exact hpre.subset_connectedComponentIn ⟨a, ⟨le_rfl, hc.1⟩, rfl⟩
      (by rintro _ ⟨s, hs, rfl⟩; exact hcN s hs) ⟨t, ht, rfl⟩

variable {C : Set V}

theorem riemDist_eq_of_closed (hCN : C ⊆ N)
    (hpath : ∀ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) →
      c a ∈ C → ∀ t ∈ Icc a b, c t ∈ C) {x : V} (hx : x ∈ C) (y : V) :
    Morse.riemDist (N := C) x y = Morse.riemDist (N := N) x y := by
  unfold Morse.riemDist Morse.pathLengths
  congr 1
  ext L
  constructor
  · rintro ⟨c, a, b, hc, hcC, ha, hb, rfl⟩
    exact ⟨c, a, b, hc, fun t ht => hCN (hcC t ht), ha, hb, rfl⟩
  · rintro ⟨c, a, b, hc, hcN, ha, hb, rfl⟩
    exact ⟨c, a, b, hc, hpath c a b hc hcN (by rw [ha]; exact hx), ha, hb, rfl⟩

theorem mem_of_riemDist_ne_top
    (hpath : ∀ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) →
      c a ∈ C → ∀ t ∈ Icc a b, c t ∈ C) {x y : V} (hx : x ∈ C)
    (h : Morse.riemDist (N := N) x y ≠ ⊤) : y ∈ C := by
  unfold Morse.riemDist at h
  have hne : (Morse.pathLengths (N := N) x y).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, sInf_empty] at h
    exact h rfl
  obtain ⟨L, c, a, b, hc, hcN, ha, hb, -⟩ := hne
  rw [← hb]
  exact hpath c a b hc hcN (by rw [ha]; exact hx) b ⟨hc.1, le_rfl⟩

end Component

end RoundTrip.V7_28.Aux

namespace RoundTrip.V7_28

open RoundTrip.Bridge RoundTrip.V7_28.Aux

/-- The project's statement (universes instantiated at 0): for ANY slice submanifold `N ⊆ V`
(model `Z` arbitrary, `N` not assumed connected or nonempty) with the induced metric, if `(N, ρ)`
is complete (`ρ`-Cauchy sequences of points of `N` `ρ`-converge in `N`), then `N` is geodesically
complete (`exp_q v` is defined, by a geodesic on an open interval containing `[0, 1]`, for every
`q ∈ N`, `v ∈ T_qN`). -/
def A : Prop := type_of% @Morse.isGeodesicallyComplete_of_isRiemComplete.{0,0,0}

theorem A_holds : A := @Morse.isGeodesicallyComplete_of_isRiemComplete

/-- **`B → A`**: Milnor's abstract statement, applied to the connected component of `q` in `N`
(an open part `N ∩ O`, re-modelled on `ℝᵐ`) with the induced metric and Levi-Civita connection
of `RoundTrip.Bridge`, gives the project's theorem. Glue: `ρ` of the component is the project's
`riemDist` of `N` (paths in `N` from the component stay in it), so `(N, ρ)` complete makes the
component `MetricComplete`; `B` makes it `GeodComplete` (blind geodesics on `[0, 1]`); and
`mem_expDom_of_expDefined` turns these into the project's geodesics on open intervals. -/
theorem B_to_A : B → A := by
  intro hB V _ _ _ Z _ _ _ W _ _ _ N hN hcomp q v hv
  set m := finrank ℝ Z
  have hN' : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn m) W N := isSliceRn hN
  obtain ⟨O, hO, hqO, hconn, hpath⟩ := exists_component hN' q
  set C := N ∩ O with hC_def
  set hC : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn m) W C :=
    Morse.IsSliceSubmanifold.inter_isOpen hN' hO
  have hqC : (q : V) ∈ C := ⟨q.2, hqO⟩
  have : ConnectedSpace (Sub hC) := isConnected_iff_connectedSpace.1 hconn
  have hTC : ∀ x (hx : x ∈ C), Morse.tangentSubspace hC ⟨x, hx⟩ =
      Morse.tangentSubspace hN ⟨x, inter_subset_left hx⟩ := fun x hx =>
    (tangentSubspace_inter hN' hO x hx).trans (tangentSubspace_rn hN ⟨x, hx.1⟩)
  -- the component is complete for its `ρ`
  have hrho : ∀ a b : Sub hC, rho (n := m) a b =
      (Morse.riemDist (N := C) (incl hC a) (incl hC b)).toReal := fun a b => rho_eq a b
  have hfin : ∀ a b : Sub hC, Morse.riemDist (N := C) (incl hC a) (incl hC b) ≠ ⊤ := fun a b =>
    Morse.riemDist_ne_top hC hconn.isPreconnected a.2 b.2
  have hCN : ∀ a : Sub hC, ∀ y : V,
      Morse.riemDist (N := C) (incl hC a) y = Morse.riemDist (N := N) (incl hC a) y := fun a y =>
    riemDist_eq_of_closed inter_subset_left hpath a.2 y
  have hMC : MetricComplete m (Sub hC) := by
    intro x hx
    have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ n₀, ∀ k ≥ n₀, ∀ l ≥ n₀,
        Morse.riemDist (N := N) (incl hC (x k)) (incl hC (x l)) < ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨n₀, hn₀⟩ := hx ε hε
      refine ⟨n₀, fun k hk l hl => ?_⟩
      rw [← hCN, ← ENNReal.ofReal_toReal (hfin _ _)]
      refine (ENNReal.ofReal_lt_ofReal_iff hε).2 ?_
      rw [← hrho]
      exact hn₀ k hk l hl
    obtain ⟨y, -, hy⟩ := hcomp (fun k => incl hC (x k)) (fun k => (x k).2.1) hcauchy
    obtain ⟨k, hk⟩ := (hy.eventually (gt_mem_nhds (show (0 : ENNReal) < 1 from one_pos))).exists
    have hyC : y ∈ C := mem_of_riemDist_ne_top hpath (x k).2 (ne_top_of_lt hk)
    refine ⟨(⟨y, hyC⟩ : C), fun ε hε => ?_⟩
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hy.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε)))
    refine ⟨n₀, fun k hk => (hrho (x k) (⟨y, hyC⟩ : C)).trans_lt ?_⟩
    change (Morse.riemDist (N := C) (incl hC (x k)) y).toReal < ε
    rw [hCN]
    exact ENNReal.toReal_lt_of_lt_ofReal (hn₀ k hk)
  have hGC := hB m (Sub hC) (conn (hN := hC)) conn_isLC hMC
  have hexp := mem_expDom_of_expDefined (hN := hC) (fun x w => hGC x w) ⟨q, hqC⟩ (v := v)
    (by rw [hTC]; exact hv)
  exact mem_expDom_mono inter_subset_left hTC hexp

#rt_check RoundTrip.V7_28.B_to_A [Morse.isGeodesicallyComplete_of_isRiemComplete]
#rt_overlap RoundTrip.V7_28.B_to_A [Morse.isGeodesicallyComplete_of_isRiemComplete]

end RoundTrip.V7_28
