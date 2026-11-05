import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V7_26

open Set Filter Topology Function Module
open scoped ContDiff Manifold

noncomputable section

set_option linter.unusedSectionVars false

/-! Glue for the embedded case of `B` (copied from `RoundTrip/Items/V7_28.lean`). -/

namespace RoundTrip.V7_26.Aux

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

end RoundTrip.V7_26.Aux

namespace RoundTrip.V7_26

open RoundTrip.Bridge RoundTrip.V7_26.Aux

/-- The project's statement (universes instantiated at 0), for a slice submanifold `N ⊆ V` with
the induced metric: Theorem 10.9 at one point (if `exp_p` is defined on all of `T_pN`, every `q`
with `ρ(p, q) < ∞` is `exp_p v` with `‖v‖ = ρ(p, q)` and `t ↦ exp_p(tv)` is a minimal geodesic on
`[0, 1]`), and Milnor's statement (`N` preconnected and geodesically complete: any two points are
joined by a minimal geodesic on `[0, 1]` of length `ρ`). -/
def A : Prop :=
  type_of% @Morse.theorem_10_9.{0,0,0} ∧ type_of% @Morse.theorem_10_9'.{0,0,0}

theorem A_holds : A := ⟨@Morse.theorem_10_9, @Morse.theorem_10_9'⟩

/-- **Partial `B → A`: `B` gives the second conjunct of `A`** (`Morse.theorem_10_9'`, Milnor's
statement on a preconnected, geodesically complete slice submanifold), by applying `B` to `N`
(re-modelled on `ℝᵐ`) with the induced metric and Levi-Civita connection of `RoundTrip.Bridge`.
The blind minimal geodesic `γ` on `[0, 1]` is identified with `t ↦ exp_p(tv)` (a project geodesic
on `ℝ`) by uniqueness from the initial point, and lengths/paths are translated by the Bridge
dictionary. The first conjunct (`Morse.theorem_10_9`, completeness only at `p`, `q` only at finite
distance, `N` not connected) is not a consequence of `B`. -/
theorem B_to_A_milnor : B → type_of% @Morse.theorem_10_9'.{0,0,0} := by
  intro hB V _ _ _ Z _ _ _ W _ _ _ N hN hconn hc p q
  set m := finrank ℝ Z
  set hN' : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn m) W N := isSliceRn hN
  have hT' : ∀ x (hx : x ∈ N), Morse.tangentSubspace hN ⟨x, hx⟩ =
      Morse.tangentSubspace hN' ⟨x, Subset.rfl hx⟩ := fun x hx =>
    (tangentSubspace_rn hN ⟨x, hx⟩).symm
  have : ConnectedSpace (Sub hN') := isConnected_iff_connectedSpace.1 ⟨⟨p, p.2⟩, hconn⟩
  have hGC : GeodComplete (conn (hN := hN')) := by
    intro x w
    refine expDefined_of_mem_expDom ?_
    refine mem_expDom_mono Subset.rfl hT' (hc x (D hN' x w) ?_)
    have := D_mem x w
    rw [← tangentSubspace_rn hN x]
    exact this
  obtain ⟨γ, ⟨hγg, hγmin⟩, hγ0, hγ1⟩ := hB m (Sub hN') (conn (hN := hN')) conn_isLC hGC p q
  have hγg' : BridgePrelude.IsGeodesic (conn (hN := hN')) γ (Icc 0 1) := hγg
  have u01 : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  set v₀ : V := derivWithin (incl hN' ∘ γ) (Icc 0 1) 0 with hv₀_def
  have hv₀' : v₀ ∈ Morse.tangentSubspace hN' p := by
    rw [hv₀_def, ← D_vel (isSmoothCurve_iff.2 (isGeodesic_iff.1 hγg').2.1) u01
      ⟨le_rfl, zero_le_one⟩, hγ0]
    exact D_mem _ _
  have hv₀ : v₀ ∈ Morse.tangentSubspace hN p := by rw [← tangentSubspace_rn hN p]; exact hv₀'
  set g : ℝ → V := fun t => Morse.exp hN p (t • v₀) with hg_def
  have hg : Morse.IsGeodesicOn hN g univ := Morse.isGeodesicOn_univ_exp_smul (hc p) hv₀
  have hg' : Morse.IsGeodesicOn hN' g univ := isGeodesicOn_mono Subset.rfl hT' hg
  have hg0 : g 0 = p := by simp only [hg_def, zero_smul]; exact Morse.exp_zero p.2
  obtain ⟨hl, hleq, hld⟩ := isGeodesic_lift_Icc hg' zero_lt_one (subset_univ _) p
  have hagree := eqOn_Icc_of_isGeodesic zero_lt_one hl hγg' ?_ ?_
  rotate_left
  · apply Subtype.ext
    change incl hN' (lift g p 0) = incl hN' (γ 0)
    rw [incl_lift p (hg.mem 0 trivial), hγ0, hg0]
    rfl
  · rw [hld, (Morse.hasDerivAt_exp_smul_zero p hv₀).deriv]
  have hEq : EqOn (incl hN' ∘ γ) g (Icc 0 1) := fun t ht => by
    rw [← hleq ht]
    exact (congrArg (incl hN') (hagree ht)).symm
  have hg1 : g 1 = q := by
    rw [← hEq ⟨zero_le_one, le_rfl⟩]
    change incl hN' (γ 1) = incl hN' q
    rw [hγ1]
  have hgps : Morse.IsPiecewiseSmooth g 0 1 :=
    Morse.IsPiecewiseSmooth.of_contDiffOn hg.contDiffOn zero_le_one (subset_univ _)
  -- minimality, through the blind minimality of `γ`
  have hmin : ∀ (c : ℝ → V) (a b : ℝ), Morse.IsPiecewiseSmooth c a b → (∀ t ∈ Icc a b, c t ∈ N) →
      c a = g 0 → c b = g 1 → Morse.pathLength g 0 1 ≤ Morse.pathLength c a b := by
    intro c a b hcps hcN ha hb
    have hlc : EqOn (incl hN' ∘ lift (hN := hN') c p) c (Icc a b) := fun t ht => incl_lift p (hcN t ht)
    have h1 : Morse.pathLength g 0 1 = arcLen (n := m) γ 0 1 := by
      rw [show arcLen (n := m) γ 0 1 = BridgePrelude.arcLen (n := m) γ 0 1 from rfl, arcLen_eq]
      exact (pathLength_congr zero_le_one hEq).symm
    have h2 : arcLen (n := m) (lift (hN := hN') c p) a b = Morse.pathLength c a b := by
      rw [show arcLen (n := m) (lift (hN := hN') c p) a b = BridgePrelude.arcLen (n := m) (lift (hN := hN') c p) a b
        from rfl, arcLen_eq]
      exact pathLength_congr hcps.1 hlc
    rw [h1, ← h2]
    refine hγmin (lift (hN := hN') c p) a b hcps.1 (isPW_lift hcps hcN p) ?_ ?_
    · apply Subtype.ext
      change incl hN' (lift (hN := hN') c p a) = incl hN' (γ 0)
      rw [incl_lift p (hcN a ⟨le_rfl, hcps.1⟩), ha, hg0, hγ0]
      rfl
    · apply Subtype.ext
      change incl hN' (lift (hN := hN') c p b) = incl hN' (γ 1)
      rw [incl_lift p (hcN b ⟨hcps.1, le_rfl⟩), hb]
      exact (hEq ⟨zero_le_one, le_rfl⟩).symm
  refine ⟨g, ⟨zero_le_one, ⟨univ, subset_univ _, hg⟩, hmin⟩, hg0, hg1, le_antisymm ?_ ?_⟩
  · have := Morse.riemDist_le_pathLength (N := N) hgps fun t _ => hg.mem t trivial
    rwa [hg0, hg1] at this
  · refine le_sInf ?_
    rintro _ ⟨c, a, b, hcps, hcN, ha, hb, rfl⟩
    exact ENNReal.ofReal_le_ofReal (hmin c a b hcps hcN (ha.trans hg0.symm) (hb.trans hg1.symm))

#rt_check RoundTrip.V7_26.B_to_A_milnor [Morse.theorem_10_9, Morse.theorem_10_9']
#rt_overlap RoundTrip.V7_26.B_to_A_milnor [Morse.theorem_10_9, Morse.theorem_10_9']

/-! No full direction is proved; see `V7_26.json`. -/

end RoundTrip.V7_26
