import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V7_27

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

set_option linter.unusedSectionVars false

/-! Glue for the embedded case of `B` (copied from `RoundTrip/Items/V7_28.lean`). -/

namespace RoundTrip.V7_27.Aux

open RoundTrip.Bridge

section Lift

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn n) W N}

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

end Lift

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

end RoundTrip.V7_27.Aux

namespace RoundTrip.V7_27

open RoundTrip.Bridge RoundTrip.V7_27.Aux

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with
the induced metric: (1) if `N` is preconnected and `exp_p` is defined on all of `T_pN` for ONE `p`,
every `ρ`-bounded `X` has compact closure contained in `N`; (2) if every `ρ`-bounded set has
compact closure in `N`, then `(N, ρ)` is complete (no completeness hypothesis); (3) Corollary
10.10: `N` preconnected and geodesically complete ⇒ (bounded sets have compact closure in `N`) and
`(N, ρ)` is complete. -/
def A : Prop :=
  type_of% @Morse.isCompact_closure_of_isRiemBounded.{0,0,0} ∧
    type_of% @Morse.isRiemComplete_of_forall_isCompact_closure.{0,0,0} ∧
    type_of% @Morse.corollary_10_10.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.isCompact_closure_of_isRiemBounded, @Morse.isRiemComplete_of_forall_isCompact_closure,
    @Morse.corollary_10_10⟩

/-- **Partial `B → A`: `B` gives the third conjunct of `A`** (`Morse.corollary_10_10`, Milnor's
Corollary 10.10 on a preconnected, geodesically complete slice submanifold), by applying `B` to `N`
(re-modelled on `ℝᵐ`) with the induced metric and Levi-Civita connection of `RoundTrip.Bridge`;
`ρ` is the project's `riemDist` (`Bridge.rho_eq`, finite on a connected `N`), and compactness in
`N` is compactness in `V` of the image. The first two conjuncts (completeness at one point only;
"bounded sets have compact closure ⇒ complete" with no geodesic hypothesis) are not consequences
of `B`. -/
theorem B_to_A_milnor : B → type_of% @Morse.corollary_10_10.{0,0,0} := by
  intro hB V _ _ _ Z _ _ _ W _ _ _ N hN hconn hc
  rcases N.eq_empty_or_nonempty with hN0 | ⟨p₀, hp₀⟩
  · refine ⟨fun X hX => ?_, fun x hxN _ => ?_⟩
    · have hX0 : X = ∅ := by
        rcases X.eq_empty_or_nonempty with h | ⟨x, hx⟩
        · exact h
        · obtain ⟨d, hd⟩ := hX
          have := hd x hx x hx
          rw [Morse.riemDist_eq_top_of_notMem (by rw [hN0]; exact notMem_empty x)] at this
          exact absurd (top_le_iff.1 this) ENNReal.ofReal_ne_top
      subst hX0
      simp
    · exact absurd (hxN 0) (by rw [hN0]; exact notMem_empty _)
  set m := finrank ℝ Z
  set hN' : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn m) W N := isSliceRn hN
  have hT' : ∀ x (hx : x ∈ N), Morse.tangentSubspace hN ⟨x, hx⟩ =
      Morse.tangentSubspace hN' ⟨x, Subset.rfl hx⟩ := fun x hx =>
    (tangentSubspace_rn hN ⟨x, hx⟩).symm
  have : ConnectedSpace (Sub hN') := isConnected_iff_connectedSpace.1 ⟨⟨p₀, hp₀⟩, hconn⟩
  have hGC : GeodComplete (conn (hN := hN')) := by
    intro x w
    refine expDefined_of_mem_expDom ?_
    refine mem_expDom_mono Subset.rfl hT' (hc x (D hN' x w) ?_)
    have := D_mem x w
    rw [← tangentSubspace_rn hN x]
    exact this
  obtain ⟨hbdd, hMC⟩ := hB m (Sub hN') (conn (hN := hN')) conn_isLC hGC
  have hrho : ∀ a b : Sub hN', rho (n := m) a b =
      (Morse.riemDist (N := N) (incl hN' a) (incl hN' b)).toReal := fun a b => rho_eq a b
  have hfin : ∀ a b : Sub hN', Morse.riemDist (N := N) (incl hN' a) (incl hN' b) ≠ ⊤ :=
    fun a b => Morse.riemDist_ne_top hN hconn a.2 b.2
  refine ⟨fun X hX => ?_, fun x hxN hx => ?_⟩
  · obtain ⟨d, hd⟩ := hX
    have hXN : X ⊆ N := fun x hx => by
      by_contra h
      have := hd x hx x hx
      rw [Morse.riemDist_eq_top_of_notMem h] at this
      exact ENNReal.ofReal_ne_top (top_le_iff.1 this)
    set X' : Set (Sub hN') := incl hN' ⁻¹' X with hX'
    have hRB : RBounded (n := m) X' := by
      refine ⟨max d 0, fun x hx y hy => ?_⟩
      rw [hrho]
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hd _ hx _ hy)
      rwa [ENNReal.toReal_ofReal'] at h1
    have hK := (hbdd X' hRB).image (continuous_subtype_val (p := fun x => x ∈ N))
    have hXK : X ⊆ Subtype.val '' closure X' := fun x hx =>
      ⟨⟨x, hXN hx⟩, subset_closure (show incl hN' ⟨x, hXN hx⟩ ∈ X from hx), rfl⟩
    have hcl : closure X ⊆ Subtype.val '' closure X' := closure_minimal hXK hK.isClosed
    refine ⟨hK.of_isClosed_subset isClosed_closure hcl, hcl.trans ?_⟩
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  · set x' : ℕ → Sub hN' := fun k => (⟨x k, hxN k⟩ : N) with hx'
    have hcauchy : ∀ ε > 0, ∃ n₀ : ℕ, ∀ k ≥ n₀, ∀ l ≥ n₀, rho (n := m) (x' k) (x' l) < ε := by
      intro ε hε
      obtain ⟨n₀, hn₀⟩ := hx ε hε
      exact ⟨n₀, fun k hk l hl => (hrho _ _).trans_lt (ENNReal.toReal_lt_of_lt_ofReal (hn₀ k hk l hl))⟩
    obtain ⟨y, hy⟩ := hMC x' hcauchy
    refine ⟨incl hN' y, y.2, ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_⟩
    obtain ⟨η, -, hη1, hη2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
    have hη : 0 < η := ENNReal.ofReal_pos.1 hη1
    obtain ⟨n₀, hn₀⟩ := hy η hη
    filter_upwards [eventually_ge_atTop n₀] with k hk
    have h1 := (hrho (x' k) y).symm.trans_lt (hn₀ k hk)
    have h2 : Morse.riemDist (N := N) (incl hN' (x' k)) (incl hN' y) < ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_toReal (hfin (x' k) y)]
      exact (ENNReal.ofReal_lt_ofReal_iff hη).2 h1
    exact h2.le.trans hη2.le

#rt_check RoundTrip.V7_27.B_to_A_milnor [Morse.isCompact_closure_of_isRiemBounded, Morse.isRiemComplete_of_forall_isCompact_closure, Morse.corollary_10_10]
#rt_overlap RoundTrip.V7_27.B_to_A_milnor [Morse.isCompact_closure_of_isRiemBounded, Morse.isRiemComplete_of_forall_isCompact_closure, Morse.corollary_10_10]

/-! No full direction is proved; see `V7_27.json`. -/

end RoundTrip.V7_27
