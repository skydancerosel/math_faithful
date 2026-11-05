import Morse
import RoundTrip.Check
import RoundTrip.Blind.V11_15
import RoundTrip.Bridge
import RoundTrip.EnergyC2

/-! # Round trip for V11_15 (Milnor §19, proof of Theorem 19.6: test fields on disjoint pieces)

`A` (universes `0`; `Morse.sinBump` is vocabulary): `sinBump_mem_pathTangent` (the field
`sin(π(t-a)/(b-a)) P(t)` on `[a,b]`, `0` elsewhere, lies in `TΩ_γ`), `energyHessian_sinBump`
(its `E_**` as an integral), `energyHessian_sinBump_disjoint` (fields on pieces with disjoint
interiors are `E_**`-orthogonal) and `exists_sinBump_neg` (for `dim ≥ 2`, a Ricci-type lower bound
summed over a parallel orthonormal frame perpendicular to `γ`, and `L(b-a) > πr`, some frame
field gives `E_**(X,X) < 0`); all for slice submanifolds `N ⊆ V` with the induced metric.

`B`: on every abstract connected Hausdorff Riemannian `ℝⁿ`-manifold with a Levi-Civita
connection, if `K(U,U) ≥ (n-1)/r²` for unit `U`, every geodesic `γ : [0,1] → M` of length
`> kπr` (`k ≥ 1`) carries fields `X_i ∈ TΩ_γ`, `X_i = 0` off `(i/k,(i+1)/k)`, with
`E_**(X_i,X_i) < 0` and `E_**(X_i,X_j) = 0` (`i ≠ j`), in the blind variational sense `IsHessT`.

**`B` is false** (`not_B`), as the blind formalizer flagged: for `n = 1` the hypothesis
`K ≥ (n-1)/r² = 0` holds on the flat line `ℝ¹` (the open slice submanifold `univ ⊆ ℝ¹`, with the
induced metric and connection `Bridge.conn`), which has geodesics of any length, but on a flat
manifold `E_**` is positive semi-definite (`Morse.energyHessian_pos_of_nonpos`), so no field has
`E_**(X,X) < 0`. Transport from the blind `IsHessT` to the project's `energyHessian`:
`Emb.isHessT_eq` (copied from Items/V11_8.lean). Hence `¬ (A → B)`, and `B → A` holds
vacuously. (`A` itself assumes `2 ≤ dim`, as Milnor's argument needs.)

Embedded special case: `B_emb` is false too (the counter-model is embedded); the repaired
`B_emb2` (`n ≥ 2`) follows from A (`A_to_B_emb2`, via `A'` with generalized membership proofs,
`A'_to_B_emb2` under `#rt_check`). -/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V11_15

open Bundle

def A : Prop :=
  type_of% @Morse.sinBump_mem_pathTangent.{0,0,0} ∧
    type_of% @Morse.energyHessian_sinBump.{0,0,0} ∧
    type_of% @Morse.energyHessian_sinBump_disjoint.{0,0,0} ∧
    type_of% @Morse.exists_sinBump_neg.{0,0,0,0}

theorem A_holds : A :=
  ⟨@Morse.sinBump_mem_pathTangent, @Morse.energyHessian_sinBump,
    @Morse.energyHessian_sinBump_disjoint, @Morse.exists_sinBump_neg⟩

/-! ### Glue (copied from Items/V11_17.lean and Items/V11_8.lean) -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

theorem prj_incl (x : Bridge.Sub hN) : Morse.prj hN (incl hN x) = P hN x :=
  Morse.prj_of_mem hN x.2

theorem isIntv_Icc : RoundTrip.BridgePrelude.IsIntv (Icc (0 : ℝ) 1) :=
  ⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩

/-- On the interior, `derivWithin [0,1]` of a function smooth on `[0, 1]` is `deriv`, near `t`. -/
theorem derivWithin_eventuallyEq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} (hF : ContDiffOn ℝ ∞ F (Icc 0 1)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    derivWithin F (Icc 0 1) =ᶠ[𝓝 t] deriv F := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with x hx
  exact ((hF.contDiffAt (Icc_mem_nhds hx.1 hx.2)).differentiableAt (by simp)).hasDerivAt
    |>.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one x (Ioo_subset_Icc_self hx))

/-- A smooth curve in `N` on `[0, 1]` which is a geodesic on `(0, 1)` lifts to a blind geodesic of
the induced connection on the closed interval `[0, 1]` (endpoint condition by continuity). -/
theorem isGeodesic_lift {γ : ℝ → V} (hc : Morse.IsSmoothCurveIn hN γ)
    (hg : Morse.IsGeodesicOn hN γ (Ioo 0 1)) (q : Bridge.Sub hN) :
    IsGeodesic (conn (hN := hN)) (lift γ q) (Icc 0 1) ∧
      EqOn (incl hN ∘ lift γ q) γ (Icc 0 1) := by
  have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
  have heq : EqOn (incl hN ∘ lift γ q) γ (Icc 0 1) := fun t ht => incl_lift q (hc.mem t ht)
  refine ⟨?_, heq⟩
  have h : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) (lift γ q) (Icc 0 1) := by
    refine isGeodesic_iff.2 ⟨isIntv_Icc, hc.contDiffOn.congr heq, fun t ht => ?_⟩
    have hd1 : EqOn (derivWithin (incl hN ∘ lift γ q) (Icc 0 1)) (derivWithin γ (Icc 0 1))
        (Icc 0 1) := fun s hs => derivWithin_congr heq (heq hs)
    rw [derivWithin_congr hd1 (hd1 ht)]
    have hP : P hN (lift γ q t) = Morse.prj hN (γ t) := by
      rw [← prj_incl]
      exact congrArg (Morse.prj hN) (heq ht)
    rw [hP]
    -- the normal condition, extended from `(0, 1)` to `[0, 1]` by continuity
    have hf : ContinuousOn (fun s => Morse.prj hN (γ s)
        (derivWithin (derivWithin γ (Icc 0 1)) (Icc 0 1) s)) (Icc 0 1) :=
      hc.contDiffOn_prj.continuousOn.clm_apply
        ((hc.contDiffOn_velAlong.derivWithin hu (m := 0) (by simp)).continuousOn)
    refine EqOn.of_subset_closure (g := fun _ => (0 : V)) (fun s hs => ?_) hf continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo zero_ne_one]) ht
    show Morse.prj hN (γ s) (derivWithin (derivWithin γ (Icc 0 1)) (Icc 0 1) s) = 0
    have hv : ContDiffOn ℝ ∞ (derivWithin γ (Icc 0 1)) (Icc 0 1) := hc.contDiffOn_velAlong
    rw [(derivWithin_eventuallyEq hv hs).eq_of_nhds,
      (derivWithin_eventuallyEq hc.contDiffOn hs).deriv_eq,
      Morse.prj_of_mem hN (hc.mem s (Ioo_subset_Icc_self hs))]
    exact (Morse.tanProj_eq_zero_iff hN).2 (hg.normal s hs)
  exact h

end Emb

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- **Dictionary: geodesics from `p` to `q`, blind ⇒ project.** -/
theorem unbroken_of_geodPQ {p q : Bridge.Sub hN} {γ : ℝ → Bridge.Sub hN}
    (h : IsGeodPQ n (conn (hN := hN)) p q γ) :
    incl hN ∘ γ ∈ Morse.pathSpace N (incl hN p) (incl hN q) ∧
      Morse.IsUnbrokenGeodesic hN (incl hN ∘ γ) := by
  obtain ⟨hγ, hγ0, hγ1⟩ := h
  have hγ' : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hN)) γ (Icc 0 1) := hγ
  have hcd := (isGeodesic_iff.1 hγ').2.1
  refine ⟨⟨Morse.IsPiecewiseSmooth.of_contDiffOn hcd zero_le_one subset_rfl,
    fun t _ => (γ t).2, ?_, ?_⟩, hcd, isGeodesicOn_Ioo hγ'⟩
  · show incl hN (γ 0) = incl hN p
    rw [hγ0]
  · show incl hN (γ 1) = incl hN q
    rw [hγ1]

/-- **Dictionary: geodesics from `p` to `q`, project ⇒ blind** (the lift `Bridge.lift`). -/
theorem geodPQ_of_unbroken {p q : Bridge.Sub hN} {γ : ℝ → V}
    (hγ : γ ∈ Morse.pathSpace N (incl hN p) (incl hN q)) (hg : Morse.IsUnbrokenGeodesic hN γ) :
    IsGeodPQ n (conn (hN := hN)) p q (lift γ p) ∧ EqOn (incl hN ∘ lift γ p) γ (Icc 0 1) := by
  obtain ⟨hgeo, heqc⟩ := isGeodesic_lift (hg.isSmoothCurveIn hN hγ) hg.2 p
  refine ⟨⟨hgeo, Subtype.ext ?_, Subtype.ext ?_⟩, heqc⟩
  · exact (heqc ⟨le_rfl, zero_le_one⟩).trans hγ.2.2.1
  · exact (heqc ⟨zero_le_one, le_rfl⟩).trans hγ.2.2.2

end Emb

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- The differential of a map into `N`, read in `V`. -/
theorem D_mfderiv_map {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x)
    (v : E) :
    D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (incl hN ∘ f) x v := by
  have hi : MDifferentiableAt 𝓘(ℝ, Rn n) 𝓘(ℝ, V) (incl hN) (f x) :=
    (contMDiff_incl (f x)).mdifferentiableAt (by simp)
  have h := (hi.hasMFDerivAt.comp x hf.hasMFDerivAt).mfderiv
  rw [mfderiv_eq_fderiv] at h
  rw [h]
  rfl

end Emb

/-! ### The Hessian dictionary: blind `IsHessT 1` ⇒ the project's `energyHessian` -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- `Bridge.contMDiffWithinAt_curve_iff` for maps from any normed space. -/
theorem contMDiffWithinAt_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s x ↔ ContDiffWithinAt ℝ ∞ (incl hN ∘ f) s x := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((contMDiff_incl (f x)).comp_contMDiffWithinAt x h)
  · intro h
    have hcont : ContinuousWithinAt f s x :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := f)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set σ := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (σ.φ y).1) (incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn σ).contDiffAt
        (σ.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt x h)

theorem contMDiffOn_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s ↔ ContDiffOn ℝ ∞ (incl hN ∘ f) s :=
  forall₂_congr fun _ _ => contMDiffWithinAt_map_iff

/-- A map into `N` that is differentiable in `V` is differentiable into the manifold `N`. -/
theorem mdifferentiableAt_of_differentiableAt {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : E → Bridge.Sub hN} {x : E}
    (h : DifferentiableAt ℝ (incl hN ∘ f) x) : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x := by
  have hcont : ContinuousAt f x :=
    (Topology.IsInducing.subtypeVal.continuousAt_iff (f := f)).2 h.continuousAt
  rw [mdifferentiableAt_iff_target]
  refine ⟨hcont, ?_⟩
  set σ := Morse.sliceAt hN (f x)
  have hφ : DifferentiableAt ℝ (fun y => (σ.φ y).1) (incl hN (f x)) :=
    (Milnor.Problems.sliceChart_differentiableAt σ (Morse.mem_sliceAt_source hN (f x))).fst
  have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) = (fun y => (σ.φ y).1) ∘ (incl hN ∘ f) := rfl
  rw [e]
  exact mdifferentiableAt_iff_differentiableAt.2 (hφ.comp x h)

/-- An interval `[s, s']` of `[0, 1]` whose interior avoids the subdivision points lies in one
strip `[t i, t (i+1)]`. -/
theorem exists_strip {t : ℕ → ℝ} {k : ℕ} (h0 : t 0 = 0) (hk : t k = 1)
    (hlt : ∀ i < k, t i < t (i + 1)) {s s' : ℝ} (hs : 0 ≤ s) (hss' : s < s') (hs' : s' ≤ 1)
    (hB : ∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s s') :
    ∃ i < k, t i ≤ s ∧ s' ≤ t (i + 1) := by
  classical
  have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
  set m := Nat.find hP
  have hm : s < t m ∧ m ≤ k := Nat.find_spec hP
  have hm0 : m ≠ 0 := by
    intro h; have := hm.1; rw [h, h0] at this; linarith
  have hi : t (m - 1) ≤ s := by
    by_contra hcon
    exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
      ⟨lt_of_not_ge hcon, by omega⟩
  have hu : s' ≤ t m := by
    by_contra hcon
    exact hB (t m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩)
      ⟨hm.1, lt_of_not_ge hcon⟩
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
  exact ⟨m - 1, by omega, hi, by rw [hm1]; exact hu⟩

/-- **Dictionary: 2-parameter variations.** A blind variation `α : ℝ² → ℝ → ↥N` (strips
`U × [t i, t (i+1)]`) is, read in `V`, a project variation (`Morse.IsVariation`, parameters in
`ℝ²`, break points the `t i`). -/
theorem isVariation_of_isVarSubT {U : Set (Rn 2)} {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ}
    {t : ℕ → ℝ} (h : IsVarSubT (n := n) 1 U α k t) :
    Morse.IsVariation N U (fun u s => incl hN (α u s)) ((Finset.range (k + 1)).image t) := by
  obtain ⟨hU, h0U, ht0, htk, hlt, hpaths, hsm⟩ := h
  refine ⟨hU, h0U, fun u _ s _ => (α u s).2, fun u hu => ?_, fun u hu => ?_, ?_⟩
  · show incl hN (α u 0) = incl hN (α 0 0)
    rw [(hpaths u hu).2.1]
  · show incl hN (α u 1) = incl hN (α 0 1)
    rw [(hpaths u hu).2.2]
  · intro s s' hs hss' hs' hB
    obtain ⟨i, hi, his, his'⟩ := exists_strip ht0 htk hlt hs hss' hs' hB
    exact contMDiffOn_map_iff.1 ((hsm i hi).mono (prod_mono subset_rfl (Icc_subset_Icc his his')))

/-- **Dictionary: variation fields.** For `s ∈ [0, 1]`, the derivative of `r ↦ α(r w, s)` read
in `V` is `D` of the blind (manifold) derivative of `u ↦ α(u, s)` in the direction `w`. -/
theorem deriv_line_eq {U : Set (Rn 2)} {α : Rn 2 → ℝ → Bridge.Sub hN} {B : Finset ℝ}
    (hα : Morse.IsVariation N U (fun u s => incl hN (α u s)) B) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (w : Rn 2) :
    deriv (fun r : ℝ => incl hN (α (r • w) s)) 0 =
      D hN (α 0 s) (mfderiv 𝓘(ℝ, Rn 2) 𝓘(ℝ, Rn n) (fun u => α u s) 0 w) := by
  obtain ⟨a, b, ha, hab, hb, hsab, hB⟩ := Morse.exists_piece_mem B zero_lt_one hs
  have hF := hα.smooth a b ha hab hb hB
  have hd := RoundTrip.EnergyC2.hasFDerivAt_pderiv hα.isOpen
    (f := fun u s => incl hN (α u s)) (hF.differentiableOn (by simp)) hα.zero_mem hsab
  have hmd : MDifferentiableAt 𝓘(ℝ, Rn 2) 𝓘(ℝ, Rn n) (fun u => α u s) 0 :=
    mdifferentiableAt_of_differentiableAt hd.differentiableAt
  rw [D_mfderiv_map hmd w]
  have hl := RoundTrip.EnergyC2.hasDerivAt_line hd.differentiableAt w
  simp only [zero_add] at hl
  exact hl.deriv

/-- **Dictionary: Milnor's `E_**` on `↥N`.** If `r = E_**(W₁, W₂)` in the blind sense (`IsHessT`:
`r` is the mixed partial of the energy of some 2-parameter blind variation of the blind geodesic
`γ` with variation fields `W₁, W₂`), then `r` is the project's `energyHessian` of two elements of
`TΩ` which agree on `[0, 1]` with `W₁, W₂` read in `V`. (Theorem 13.1 `hasDerivAt_energyHessian`
and the C² regularity of `RoundTrip/EnergyC2.lean`.) -/
theorem isHessT_eq {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1))
    {W₁ W₂ : FA n γ} {r : ℝ} (h : IsHessT (n := n) 1 γ W₁ W₂ r) :
    ∃ X₁ X₂ : Morse.pathTangent hN (incl hN ∘ γ),
      (∀ s ∈ Icc (0 : ℝ) 1, (X₁ : ℝ → V) s = ambA γ W₁ s) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, (X₂ : ℝ → V) s = ambA γ W₂ s) ∧
      r = Morse.energyHessian hN
        (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1
        X₁ X₂ := by
  obtain ⟨hpath, hgeo⟩ :=
    unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)
  obtain ⟨U, α, k, t, hvar, hα0, hW₁, hW₂, -, hr⟩ := h
  have hα' := isVariation_of_isVarSubT hvar
  set α' : Rn 2 → ℝ → V := fun u s => incl hN (α u s) with hα'def
  set e₀ : Rn 2 := EuclideanSpace.single 0 (1 : ℝ)
  set e₁ : Rn 2 := EuclideanSpace.single 1 (1 : ℝ)
  set φ : ℝ × ℝ → Rn 2 := fun u => u.1 • e₀ + u.2 • e₁ with hφdef
  have hφ : ContDiff ℝ ∞ φ :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  have hφ0 : φ 0 ∈ U := by
    have : φ 0 = 0 := by simp [hφdef]
    rw [this]; exact hvar.2.1
  have hα'' := hα'.comp hφ hφ0
  have hα''γ : ∀ s ∈ Icc (0 : ℝ) 1, α' (φ 0) s = (incl hN ∘ γ) s := by
    intro s _
    have : φ 0 = 0 := by simp [hφdef]
    rw [this, ← hα0]
    rfl
  have hHD := Morse.hasDerivAt_energyHessian hN hpath hgeo hα'' hα''γ
  refine ⟨⟨_, hα''.partial₁_mem hN hα''γ⟩, ⟨_, hα''.partial₂_mem hN hα''γ⟩, ?_, ?_, ?_⟩
  · intro s hs
    show deriv (fun u₁ => α' (φ (u₁, 0)) s) 0 = D hN (γ s) (W₁ s)
    have e : (fun u₁ : ℝ => α' (φ (u₁, 0)) s) = fun u₁ => incl hN (α (u₁ • e₀) s) := by
      funext u₁; simp [hφdef, hα'def]
    rw [e, deriv_line_eq hα' hs e₀]
    have hv : (W₁ s : Rn n) = (varField (n := n) α 0 s : Rn n) := eq_of_heq (hW₁ s)
    subst hα0
    rw [hv]
    rfl
  · intro s hs
    show deriv (fun u₂ => α' (φ (0, u₂)) s) 0 = D hN (γ s) (W₂ s)
    have e : (fun u₂ : ℝ => α' (φ (0, u₂)) s) = fun u₂ => incl hN (α (u₂ • e₁) s) := by
      funext u₂; simp [hφdef, hα'def]
    rw [e, deriv_line_eq hα' hs e₁]
    have hv : (W₂ s : Rn n) = (varField (n := n) α 1 s : Rn n) := eq_of_heq (hW₂ s)
    subst hα0
    rw [hv]
    rfl
  · rw [← hr, ← hHD.deriv]
    have hF : ContDiffOn ℝ 2 (fun v => Morse.energy (α' v) 0 1) U :=
      hα'.contDiffOn_energy.of_le ENat.LEInfty.out
    have hmix := RoundTrip.EnergyC2.fderiv_fderiv_apply_eq_deriv_deriv hvar.1 hF hvar.2.1 e₀ e₁
    have hEF : (fun v : Rn 2 => energy (n := n) (α v) 0 1) =
        fun v => Morse.energy (α' v) 0 1 := funext fun v => Bridge.energy_eq (α v) 0 1
    show fderiv ℝ (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => energy (n := n) (α v) 0 1) u e₀) 0 e₁
      = _
    rw [hEF, hmix]
    simp only [zero_add, hφdef]

end Emb


/-! ### The converse Hessian dictionary: every field of `TΩ` is realized by a blind variation -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- A subdivision `0 = t 0 < … < t k = 1` whose open pieces avoid a finite set (as in
`Bridge.isPW_lift`). -/
theorem exists_subdiv (B : Finset ℝ) : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧ t k = 1 ∧
    (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ 1 ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) := by
  classical
  have hlt : (0 : ℝ) < 1 := zero_lt_one
  set S : Finset ℝ := insert 0 (insert 1 (B.filter (· ∈ Ioo (0 : ℝ) 1)))
  have hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
  have hbS : (1 : ℝ) ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨0, haS, 1, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else 1
  have ht : ∀ j (h : j < m), t j = e ⟨j, h⟩ := fun j h => dif_pos h
  refine ⟨m - 1, t, ?_, ?_, ?_, ?_⟩
  · rw [ht 0 (by omega), Finset.orderEmbOfFin_zero rfl (by omega)]
    exact le_antisymm (Finset.min'_le _ _ haS) ((hS _ (Finset.min'_mem _ _)).1)
  · rw [ht (m - 1) (by omega), Finset.orderEmbOfFin_last rfl (by omega)]
    exact le_antisymm ((hS _ (Finset.max'_mem _ _)).2) (Finset.le_max' _ _ hbS)
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  · intro i hi
    rw [ht i (by omega), ht (i + 1) (by omega)]
    refine ⟨(hS _ (Finset.orderEmbOfFin_mem _ _ _)).1, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2,
      fun x hx hxi => ?_⟩
    have hxS : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨hx, (hS _ (Finset.orderEmbOfFin_mem _ _ _)).1.trans_lt hxi.1,
        hxi.2.trans_le (hS _ (Finset.orderEmbOfFin_mem _ _ _)).2⟩))
    obtain ⟨j, rfl⟩ : x ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hxS
    have h1 := e.lt_iff_lt.1 hxi.1
    have h2 := e.lt_iff_lt.1 hxi.2
    rw [Fin.lt_def] at h1 h2
    simp only at h1 h2
    omega

/-- Gluing continuity over the pieces of a subdivision of `[0, 1]`. -/
theorem continuousOn_of_pieces {X : Type*} [TopologicalSpace X] {f : ℝ → X} {k : ℕ}
    {t : ℕ → ℝ} (h0 : t 0 = 0) (hk : t k = 1) (hlt : ∀ i < k, t i < t (i + 1))
    (hf : ∀ i < k, ContinuousOn f (Icc (t i) (t (i + 1)))) : ContinuousOn f (Icc 0 1) := by
  have key : ∀ j ≤ k, ContinuousOn f (Icc (t 0) (t j)) := by
    intro j
    induction j with
    | zero => intro _; rw [Icc_self]; exact continuousOn_singleton _ _
    | succ j ih =>
      intro hj
      rw [← Icc_union_Icc_eq_Icc (Bridge.le_of_strictSeq hlt (Nat.zero_le j) (by omega))
        (hlt j (by omega)).le]
      exact (ih (by omega)).union_of_isClosed (hf j (by omega)) isClosed_Icc isClosed_Icc
  rw [← h0, ← hk]
  exact key k le_rfl

/-- The blind field along `γ` of an ambient field `X` (zero off `[0, 1]`). -/
noncomputable def toW (γ : ℝ → Bridge.Sub hN) (X : ℝ → V) : FA n γ :=
  fun t => if t ∈ Icc (0 : ℝ) 1 then L hN (γ t) (X t) else 0

theorem ambA_toW {γ : ℝ → Bridge.Sub hN} {X : ℝ → V}
    (hX : X ∈ Morse.pathTangent hN (incl hN ∘ γ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ambA γ (toW γ X) t = X t := by
  show D hN (γ t) (if t ∈ Icc (0 : ℝ) 1 then L hN (γ t) (X t) else 0) = X t
  rw [if_pos ht]
  exact D_L ((Morse.prj_eq_self_iff hN (γ t).2).1 (hX.2.1 t ht))

theorem toW_of_notMem {γ : ℝ → Bridge.Sub hN} {X : ℝ → V} {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    toW γ X t = 0 := if_neg ht

/-- `X ↦ toW γ X` on `TΩ`, as a linear map. -/
noncomputable def toWₗ (γ : ℝ → Bridge.Sub hN) :
    Morse.pathTangent hN (incl hN ∘ γ) →ₗ[ℝ] FA n γ where
  toFun X := toW γ X
  map_add' X Y := funext fun t => by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simp [toW, ht, map_add]
      rfl
    · simp [toW, ht]
  map_smul' c X := funext fun t => by
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simp [toW, ht, map_smul]
      rfl
    · simp [toW, ht]

/-- **Dictionary: `TΩ`, project ⇒ blind.** -/
theorem toW_mem {γ : ℝ → Bridge.Sub hN} (hγs : IsSmoothCurve (n := n) γ (Icc 0 1)) {X : ℝ → V}
    (hX : X ∈ Morse.pathTangent hN (incl hN ∘ γ)) : toW γ X ∈ TOm (n := n) 1 γ := by
  have hX' := hX
  obtain ⟨⟨-, -, B, hB⟩, -, hX0, hX1⟩ := hX'
  obtain ⟨k, t, h0, hk, hlt, hgood⟩ := exists_subdiv B
  have hpiece : ∀ i < k, IsSmoothAlong γ (Icc (t i) (t (i + 1))) (toW γ X) := by
    intro i hi
    obtain ⟨hti, hti1, hBi⟩ := hgood i hi
    have hsub : Icc (t i) (t (i + 1)) ⊆ Icc 0 1 := Icc_subset_Icc hti hti1
    have hγs' : RoundTrip.BridgePrelude.IsSmoothCurve (n := n) γ (Icc (t i) (t (i + 1))) :=
      hγs.mono hsub
    exact isSmoothAlong_iff.2 ⟨hγs', (hB _ _ hti (hlt i hi) hti1 hBi).congr fun s hs =>
      ambA_toW hX (hsub hs)⟩
  refine ⟨⟨k, t, h0, hk, hlt, continuousOn_of_pieces h0 hk hlt fun i hi =>
    (hpiece i hi).continuousOn, hpiece⟩, ?_, ?_, fun s hs => toW_of_notMem hs⟩
  · show (if (0 : ℝ) ∈ Icc (0 : ℝ) 1 then L hN (γ 0) (X 0) else 0) = 0
    rw [if_pos ⟨le_rfl, zero_le_one⟩, hX0, map_zero]
  · show (if (1 : ℝ) ∈ Icc (0 : ℝ) 1 then L hN (γ 1) (X 1) else 0) = 0
    rw [if_pos ⟨zero_le_one, le_rfl⟩, hX1, map_zero]

/-- **Every pair of `TΩ` is realized by a blind 2-parameter variation** (Lemma 11.A of the project,
`Morse.exists_variation_two`, lifted to `↥N` and frozen off `[0, 1]`). -/
theorem exists_isHessT {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1))
    {X₁ X₂ : ℝ → V} (hX₁ : X₁ ∈ Morse.pathTangent hN (incl hN ∘ γ))
    (hX₂ : X₂ ∈ Morse.pathTangent hN (incl hN ∘ γ)) :
    ∃ r, IsHessT (n := n) 1 γ (toW γ X₁) (toW γ X₂) r := by
  classical
  obtain ⟨hpath, -⟩ :=
    unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)
  obtain ⟨ε, hε, B, hα, h0, hd1, hd2⟩ := Morse.exists_variation_two hN hpath hX₁ hX₂
  set α' : ℝ × ℝ → ℝ → V := fun u t =>
    Morse.exp hN ((incl hN ∘ γ) t) (u.1 • X₁ t + u.2 • X₂ t) with hα'def
  set ψ : Rn 2 →L[ℝ] ℝ × ℝ := (EuclideanSpace.proj (0 : Fin 2)).prod (EuclideanSpace.proj 1)
    with hψdef
  have hψ0 : ψ 0 ∈ Metric.ball (0 : ℝ × ℝ) ε := by simp [hε]
  have hβ := hα.comp ψ.contDiff hψ0
  set U := ψ ⁻¹' Metric.ball (0 : ℝ × ℝ) ε with hUdef
  have h0U : (0 : Rn 2) ∈ U := hβ.zero_mem
  let αb : Rn 2 → ℝ → Bridge.Sub hN := fun u t =>
    if h : u ∈ U ∧ t ∈ Icc (0 : ℝ) 1 then ((⟨α' (ψ u) t, hβ.mem u h.1 t h.2⟩ : N) : Bridge.Sub hN)
    else γ t
  have hincl : ∀ u ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, incl hN (αb u t) = α' (ψ u) t := by
    intro u hu t ht
    have e : αb u t = ((⟨α' (ψ u) t, hβ.mem u hu t ht⟩ : N) : Bridge.Sub hN) := dif_pos ⟨hu, ht⟩
    rw [e]
    rfl
  have hout : ∀ u, ∀ t ∉ Icc (0 : ℝ) 1, αb u t = γ t := fun u t ht =>
    dif_neg (fun h : u ∈ U ∧ t ∈ Icc (0 : ℝ) 1 => ht h.2)
  have hα0 : αb 0 = γ := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · apply Subtype.ext
      show incl hN (αb 0 t) = incl hN (γ t)
      rw [hincl 0 h0U t ht]
      have := h0 t ht
      simpa [hα'def] using this
    · exact hout 0 t ht
  have hvarV : Morse.IsVariation N U (fun u s => incl hN (αb u s)) B := by
    refine ⟨hβ.isOpen, h0U, fun u _ t _ => (αb u t).2, fun u hu => ?_, fun u hu => ?_, ?_⟩
    · rw [hincl u hu 0 ⟨le_rfl, zero_le_one⟩, hincl 0 h0U 0 ⟨le_rfl, zero_le_one⟩]
      exact hβ.start u hu
    · rw [hincl u hu 1 ⟨zero_le_one, le_rfl⟩, hincl 0 h0U 1 ⟨zero_le_one, le_rfl⟩]
      exact hβ.finish u hu
    · intro s s' hs hss' hs' hB
      exact (hβ.smooth s s' hs hss' hs' hB).congr fun x hx =>
        hincl x.1 hx.1 x.2 ⟨hs.trans hx.2.1, hx.2.2.trans hs'⟩
  obtain ⟨k, t, ht0, htk, hlt, hgood⟩ := exists_subdiv B
  have hstrip : ∀ i < k, ContMDiffOn 𝓘(ℝ, Rn 2 × ℝ) 𝓘(ℝ, Rn n) ∞
      (fun x : Rn 2 × ℝ => αb x.1 x.2) (U ×ˢ Icc (t i) (t (i + 1))) := fun i hi => by
    obtain ⟨h1, h2, h3⟩ := hgood i hi
    exact contMDiffOn_map_iff.2 (hvarV.smooth _ _ h1 (hlt i hi) h2 h3)
  have hvarB : IsVarSubT (n := n) 1 U αb k t := by
    refine ⟨hβ.isOpen, h0U, ht0, htk, hlt, fun u hu => ⟨⟨k, t, ht0, htk, hlt, fun i hi => ?_⟩,
      ?_, ?_⟩, hstrip⟩
    · have hg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn 2 × ℝ) ∞ (fun s : ℝ => (u, s)) :=
        (contDiff_const.prodMk contDiff_id).contMDiff
      exact (hstrip i hi).comp hg.contMDiffOn fun s hs => mk_mem_prod hu hs
    · apply Subtype.ext
      show incl hN (αb u 0) = incl hN (αb 0 0)
      rw [hincl u hu 0 ⟨le_rfl, zero_le_one⟩, hincl 0 h0U 0 ⟨le_rfl, zero_le_one⟩]
      exact hβ.start u hu
    · apply Subtype.ext
      show incl hN (αb u 1) = incl hN (αb 0 1)
      rw [hincl u hu 1 ⟨zero_le_one, le_rfl⟩, hincl 0 h0U 1 ⟨zero_le_one, le_rfl⟩]
      exact hβ.finish u hu
  -- the variation fields
  have hfield : ∀ (i : Fin 2) (X : ℝ → V), X ∈ Morse.pathTangent hN (incl hN ∘ γ) →
      (∀ s ∈ Icc (0 : ℝ) 1,
        deriv (fun r : ℝ => α' (ψ (r • EuclideanSpace.single i (1 : ℝ))) s) 0 = X s) →
      ∀ s, HEq (toW γ X s) (varField (n := n) αb i s) := by
    intro i X hX hd s
    apply heq_of_eq
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · have h1 := deriv_line_eq hvarV hs (EuclideanSpace.single i (1 : ℝ))
      have hev : (fun r : ℝ => incl hN (αb (r • EuclideanSpace.single i (1 : ℝ)) s)) =ᶠ[𝓝 0]
          fun r : ℝ => α' (ψ (r • EuclideanSpace.single i (1 : ℝ))) s := by
        have hc : Continuous fun r : ℝ => r • EuclideanSpace.single i (1 : ℝ) :=
          continuous_id.smul continuous_const
        have hmem : ∀ᶠ r in 𝓝 (0 : ℝ), r • EuclideanSpace.single i (1 : ℝ) ∈ U :=
          hc.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hβ.isOpen.mem_nhds h0U)
        filter_upwards [hmem] with r hr
        exact hincl _ hr s hs
      rw [hev.deriv_eq, hd s hs] at h1
      have e : αb 0 s = γ s := congrFun hα0 s
      rw [e] at h1
      apply D_injective (γ s)
      refine (ambA_toW hX hs).trans ?_
      exact h1
    · rw [toW_of_notMem hs]
      have hc : (fun u => αb u s) = fun _ => γ s := funext fun u => hout u s hs
      show (0 : Rn n) = mfderiv 𝓘(ℝ, Rn 2) 𝓘(ℝ, Rn n) (fun u => αb u s) 0 _
      rw [hc, mfderiv_const]
      rfl
  have hF2 : ContDiffOn ℝ 2 (fun v => Morse.energy ((fun u s => incl hN (αb u s)) v) 0 1) U :=
    hvarV.contDiffOn_energy.of_le ENat.LEInfty.out
  have hEF : (fun v : Rn 2 => energy (n := n) (αb v) 0 1) =
      fun v => Morse.energy ((fun u s => incl hN (αb u s)) v) 0 1 :=
    funext fun v => Bridge.energy_eq (αb v) 0 1
  refine ⟨_, U, αb, k, t, hvarB, hα0, hfield 0 X₁ hX₁ fun s hs => ?_, hfield 1 X₂ hX₂ fun s hs => ?_,
    ?_, rfl⟩
  · have e : (fun r : ℝ => α' (ψ (r • EuclideanSpace.single (0 : Fin 2) (1 : ℝ))) s) =
        fun u₁ : ℝ => Morse.exp hN ((incl hN ∘ γ) s) (u₁ • X₁ s + (0 : ℝ) • X₂ s) := by
      funext r; simp [hα'def, hψdef]
    rw [e]; exact hd1 s hs
  · have e : (fun r : ℝ => α' (ψ (r • EuclideanSpace.single (1 : Fin 2) (1 : ℝ))) s) =
        fun u₂ : ℝ => Morse.exp hN ((incl hN ∘ γ) s) ((0 : ℝ) • X₁ s + u₂ • X₂ s) := by
      funext r; simp [hα'def, hψdef]
    rw [e]; exact hd2 s hs
  · rw [hEF]
    exact RoundTrip.EnergyC2.differentiableAt_fderiv_apply hβ.isOpen hF2 h0U _

/-- **The blind `E_**` on `toW`-fields is the project's `energyHessian`.** -/
theorem hessT_toW {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1))
    {X : ℝ → V} (hX : X ∈ Morse.pathTangent hN (incl hN ∘ γ)) :
    HessT (n := n) 1 γ (toW γ X) (toW γ X) = Morse.energyHessian hN
      (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1
      ⟨X, hX⟩ ⟨X, hX⟩ := by
  have h := exists_isHessT hγ hX hX
  unfold HessT
  rw [dif_pos h]
  obtain ⟨X₁, X₂, h1, h2, hr⟩ := isHessT_eq hγ h.choose_spec
  rw [hr, Morse.energyHessian_apply, Morse.energyHessian_apply,
    Morse.secondVariation_congr hN (fun s hs => (h1 s hs).trans (ambA_toW hX hs))
      (fun s hs => (h2 s hs).trans (ambA_toW hX hs))]

/-- **The project's index is at most the blind index** `λ(1)` (on embedded manifolds). -/
theorem formIndex_le_lam {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1)) :
    Morse.formIndex (Morse.energyHessian hN
      (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1) ≤
      lam (n := n) 1 γ := by
  set hpath :=
    (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1
  have hγs : IsSmoothCurve (n := n) γ (Icc 0 1) := hγ.2.1
  refine Morse.formIndex_le fun S hS hneg => ?_
  set Φ := toWₗ (hN := hN) (n := n) γ
  have hinj : ∀ x ∈ S, Φ x = 0 → x = 0 := by
    intro x hx h0
    by_contra hne
    have hlt := hneg x hx hne
    have hx0 : ∀ s ∈ Icc (0 : ℝ) 1, (x : ℝ → V) s = ((0 : Morse.pathTangent hN (incl hN ∘ γ)) :
        ℝ → V) s := fun s hs => by
      rw [← ambA_toW x.2 hs]
      show D hN (γ s) (toW γ x s) = 0
      rw [show toW γ x s = 0 from congrFun h0 s]
      exact map_zero _
    have : Morse.energyHessian hN hpath x x = Morse.energyHessian hN hpath 0 0 := by
      rw [Morse.energyHessian_apply, Morse.energyHessian_apply,
        Morse.secondVariation_congr hN hx0 hx0]
    rw [this] at hlt
    simp at hlt
  have hfin := Morse.finrank_map_of_injOn Φ S hinj
  have hmem : ((S.map Φ : Submodule ℝ (FA n γ)) : Set (FA n γ)) ⊆ TOm (n := n) 1 γ := by
    rintro _ ⟨x, -, rfl⟩
    exact toW_mem hγs x.2
  have hneg' : IsNegDefSub (HessT (n := n) 1 γ) (S.map Φ) := by
    rintro _ ⟨x, hx, rfl⟩ hne
    have hx0 : x ≠ 0 := fun h => hne (by rw [h, map_zero])
    show HessT (n := n) 1 γ (toW γ x) (toW γ x) < 0
    rw [hessT_toW hγ x.2]
    exact hneg x hx hx0
  unfold lam bIndex
  rw [← hfin]
  exact le_iSup₂_of_le (f := fun (S' : Submodule ℝ (FA n γ)) (_ : (S' : Set (FA n γ)) ⊆
    TOm (n := n) 1 γ ∧ FiniteDimensional ℝ S' ∧ IsNegDefSub (HessT (n := n) 1 γ) S') =>
      (finrank ℝ S' : ℕ∞)) (S.map Φ) ⟨hmem, inferInstance, hneg'⟩ le_rfl

end Emb


namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

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


/-! ### The counter-model: the flat line `ℝ¹` (adapted from Items/V10_5.lean) -/

namespace Model

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

/-- `ℝ¹` as an (open) slice submanifold of itself. -/
theorem hU : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn 1) (Rn 1) (Rn 0) (univ : Set (Rn 1)) :=
  Morse.isSliceSubmanifold_of_isOpen (Rn 0) isOpen_univ

abbrev M := Bridge.Sub hU

instance : ConnectedSpace M := Subtype.connectedSpace isConnected_univ

def pt (x : Rn 1) : M := (⟨x, mem_univ x⟩ : (univ : Set (Rn 1)))

theorem htop : ∀ q : (univ : Set (Rn 1)), Morse.tangentSubspace hU q = ⊤ :=
  Morse.tangentSubspace_of_isOpen isOpen_univ hU

theorem P_eq (x : M) (v : Rn 1) : P hU x v = v := by
  have hv : v ∈ Morse.tangentSubspace hU x := by rw [htop x]; trivial
  rw [← D_L hv, P_D]

/-- The segment from `x` to `y`. -/
noncomputable def seg (x y : M) (t : ℝ) : M := pt (incl hU x + t • (incl hU y - incl hU x))

theorem incl_seg (x y : M) : incl hU ∘ seg x y = fun t => incl hU x + t • (incl hU y - incl hU x) :=
  rfl

theorem hasDerivAt_seg (x y : M) (t : ℝ) :
    HasDerivAt (incl hU ∘ seg x y) (incl hU y - incl hU x) t := by
  rw [incl_seg]
  simpa using ((hasDerivAt_id t).smul_const (incl hU y - incl hU x)).const_add (incl hU x)

theorem contDiff_seg (x y : M) : ContDiff ℝ ∞ (incl hU ∘ seg x y) := by
  rw [incl_seg]
  exact contDiff_const.add (contDiff_id.smul contDiff_const)

theorem isGeodesic_seg (x y : M) : IsGeodesic (conn (hN := hU)) (seg x y) (Icc 0 1) := by
  have h : RoundTrip.BridgePrelude.IsGeodesic (conn (hN := hU)) (seg x y) (Icc 0 1) := by
    rw [isGeodesic_iff]
    simp only [P_eq]
    refine ⟨⟨ordConnected_Icc, uniqueDiffOn_Icc zero_lt_one⟩,
      (contDiff_seg x y).contDiffOn, fun t ht => ?_⟩
    have h1 : EqOn (derivWithin (incl hU ∘ seg x y) (Icc 0 1)) (fun _ => incl hU y - incl hU x)
        (Icc 0 1) := fun τ hτ =>
      (hasDerivAt_seg x y τ).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one τ hτ)
    rw [derivWithin_congr h1 (h1 ht)]
    simp
  exact h

theorem arcLen_seg (x y : M) :
    arcLen (n := 1) (seg x y) 0 1 = ‖incl hU y - incl hU x‖ := by
  show RoundTrip.BridgePrelude.arcLen (n := 1) (seg x y) 0 1 = _
  rw [arcLen_eq]
  have hd : ∀ t, deriv (incl hU ∘ seg x y) t = incl hU y - incl hU x := fun t =>
    (hasDerivAt_seg x y t).deriv
  simp [Morse.pathLength, hd]

/-- The flat line has curvature `0` (blind choice-function `R`). -/
theorem curvR_zero (p : M) (x y z : TangentSpace 𝓘(ℝ, Rn 1) p) :
    curvR (conn (hN := hU)) p x y z = 0 := by
  unfold curvR
  split_ifs with h
  · have hr : RoundTrip.V8_13.IsCurvVal (conn (hN := hU)) p x y z h.choose := h.choose_spec
    have h1 := (isCurvVal_iff p x y z _).1 hr
    rw [Morse.curvR_eq_zero_of_top htop] at h1
    exact D_injective p (h1.trans (map_zero _).symm)
  · rfl

/-- The blind Ricci tensor of the flat line vanishes. -/
theorem ricci_zero (p : M) (U : TangentSpace 𝓘(ℝ, Rn 1) p) : ricci (conn (hN := hU)) p U U = 0 := by
  unfold ricci
  split_ifs with h
  · have h0 : h.choose = 0 := LinearMap.ext fun W => (h.choose_spec W).trans (curvR_zero p U W U)
    rw [h0, map_zero]
  · rfl

theorem nonpos : Morse.NonposCurvature hU := by
  intro q A _ B _
  rw [← Morse.curvR_of_mem hU q.2, Morse.curvR_eq_zero_of_top htop]
  simp

/-- On the flat line, `E_**(X, X) ≥ 0`. -/
theorem energyHessian_nonneg {p q : Rn 1} {γ : ℝ → Rn 1}
    (hγ : γ ∈ Morse.pathSpace (univ : Set (Rn 1)) p q) (hgeo : Morse.IsUnbrokenGeodesic hU γ)
    (X : Morse.pathTangent hU γ) : 0 ≤ Morse.energyHessian hU hγ X X := by
  by_cases hX : ∃ t ∈ Icc (0 : ℝ) 1, (X : ℝ → Rn 1) t ≠ 0
  · exact (Morse.energyHessian_pos_of_nonpos nonpos hγ hgeo X hX).le
  · push Not at hX
    have : Morse.energyHessian hU hγ X X = Morse.energyHessian hU hγ 0 0 := by
      rw [Morse.energyHessian_apply, Morse.energyHessian_apply]
      congr 1
      exact Morse.secondVariation_congr hU (fun t ht => hX t ht) (fun t ht => hX t ht)
    rw [this, map_zero]

end Model

/-- **B is false** (`n = 1`, the flat line, `r = 1`, `k = 1`, a segment of length `10 > π`). -/
theorem not_B : ¬ B := by
  intro hB
  open Model in
  set e : Rn 1 := EuclideanSpace.single 0 1
  set γ := seg (pt 0) (pt ((10 : ℝ) • e)) with hγdef
  have hγ : IsGeodesic (Bridge.conn (hN := hU)) γ (Icc 0 1) := isGeodesic_seg _ _
  have hlen : ((1 : ℕ) : ℝ) * Real.pi * 1 < arcLen (n := 1) γ 0 1 := by
    rw [arcLen_seg]
    have : Bridge.incl hU (pt ((10 : ℝ) • e)) - Bridge.incl hU (pt 0) = (10 : ℝ) • e := by
      show (10 : ℝ) • e - 0 = _
      simp
    rw [this, norm_smul]
    simp only [e, PiLp.norm_single, norm_one, Real.norm_eq_abs]
    norm_num
    linarith [Real.pi_le_four]
  have hRic : RicciGE (Bridge.conn (hN := hU)) ((((1 : ℕ) : ℝ) - 1) / 1 ^ 2) := by
    intro p U _
    rw [ricci_zero]
    simp
  obtain ⟨X, hX, -⟩ := hB 1 M (Bridge.conn (hN := hU)) Bridge.conn_isLC 1 one_pos hRic 1 le_rfl
    γ hγ hlen
  obtain ⟨-, -, h, hneg, hH⟩ := hX 0
  obtain ⟨X₁, X₂, h1, h2, hr⟩ := Emb.isHessT_eq hγ hH
  obtain ⟨hpath, hgeo⟩ := Emb.unbroken_of_geodPQ
    (⟨hγ, rfl, rfl⟩ : IsGeodPQ 1 (Bridge.conn (hN := hU)) (γ 0) (γ 1) γ)
  have heq : Morse.energyHessian hU hpath X₁ X₂ = Morse.energyHessian hU hpath X₁ X₁ := by
    rw [Morse.energyHessian_apply, Morse.energyHessian_apply,
      Morse.secondVariation_congr hU (fun _ _ => rfl)
        (fun s hs => (h2 s hs).trans (h1 s hs).symm)]
  have hnn := energyHessian_nonneg hpath hgeo X₁
  rw [hr, heq] at hneg
  linarith



/-! ### `A'`: A with the membership proofs generalized

`A`'s statement contains the banned `Morse.sinBump_mem_pathTangent` as a proof term (inside the
types of `energyHessian_sinBump`, `energyHessian_sinBump_disjoint`, `exists_sinBump_neg`), so no
proof from `A` can pass `#rt_check`. As for V8_14, `A'` restates the three conjuncts used below with
the membership proofs as hypotheses; `A → A'` is proof irrelevance (`A_to_A'`), and the
transport `A'_to_B_emb2` is put under `#rt_check`. -/

def A' : Prop :=
  type_of% @Morse.sinBump_mem_pathTangent.{0,0,0} ∧
  (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {p q : V} {γ : ℝ → V}
    {c : ℝ → N} {P : ℝ → V} {a b : ℝ} (hγ : γ ∈ Morse.pathSpace N p q),
    ContDiff ℝ ∞ (fun t => (c t : V)) → (∀ t ∈ Icc (0 : ℝ) 1, γ t = c t) →
    ∀ {P' : ℝ → V}, Morse.IsParallel hN c P → Morse.IsParallel hN c P' → ∀ {a' b' : ℝ},
    0 ≤ a → a < b → b ≤ 1 → 0 ≤ a' → a' < b' → b' ≤ 1 → b ≤ a' →
    ∀ (h1 : Morse.sinBump a b P ∈ Morse.pathTangent hN γ)
      (h2 : Morse.sinBump a' b' P' ∈ Morse.pathTangent hN γ),
    Morse.energyHessian hN hγ ⟨_, h1⟩ ⟨_, h2⟩ = 0) ∧
  (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {N : Set V} {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N} {r : ℝ}, 0 < r →
    2 ≤ Module.finrank ℝ Z → ∀ {p q : V} {γ : ℝ → V} (hγ : γ ∈ Morse.pathSpace N p q)
    {c : ℝ → N}, ContDiff ℝ ∞ (fun t => (c t : V)) → (∀ t ∈ Icc (0 : ℝ) 1, γ t = c t) →
    ∀ {Vf : ℝ → V}, ContDiff ℝ ∞ Vf → (∀ t, Vf t ∈ Morse.tangentSubspace hN (c t)) →
    (∀ t ∈ Ioo (0 : ℝ) 1, deriv γ t = Vf t) → ∀ {ι : Type} {s : Finset ι} {P : ι → ℝ → V},
    (∀ i, Morse.IsParallel hN c (P i)) → (∀ i t, ‖P i t‖ = 1) → s.card + 1 = Module.finrank ℝ Z →
    (∀ t, Morse.pathLength γ 0 1 ^ 2 * (s.card / r ^ 2) ≤
      ∑ i ∈ s, ⟪Morse.curvR hN (c t) (Vf t) (P i t) (Vf t), P i t⟫) →
    ∀ {a b : ℝ}, 0 ≤ a → a < b → b ≤ 1 → Real.pi * r < Morse.pathLength γ 0 1 * (b - a) →
    ∀ (hmem : ∀ i, Morse.sinBump a b (P i) ∈ Morse.pathTangent hN γ),
    ∃ i ∈ s, Morse.energyHessian hN hγ ⟨_, hmem i⟩ ⟨_, hmem i⟩ < 0)

theorem A_to_A' : A → A' := by
  intro hA
  refine ⟨hA.1, ?_, ?_⟩
  · intro V _ _ _ Z _ _ _ W _ _ _ N hN p q γ c P a b hγ hcs hγc P' hP hP' a' b' ha hab hb ha'
      hab' hb' hba' _ _
    exact hA.2.2.1 hγ hcs hγc hP hP' ha hab hb ha' hab' hb' hba'
  · intro V _ _ _ Z _ _ _ W _ _ _ N hN r hr hn p q γ hγ c hcs hγc Vf hVfs hVfT hVγ ι s P hP hPn
      hcard hksum a b ha hab hb hL _
    exact hA.2.2.2 hr hn hγ hcs hγc hVfs hVfT hVγ hP hPn hcard hksum ha hab hb hL

/-! ### The embedded special case -/

/-- B on embedded manifolds: `M = ↥N` (model `ℝⁿ`, induced metric), `cov = Bridge.conn`. False as
well: the counter-model is embedded. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ r : ℝ, 0 < r → RicciGE (Bridge.conn (hN := hN)) (((n : ℝ) - 1) / r ^ 2) →
    ∀ k : ℕ, 1 ≤ k → ∀ γ : ℝ → Bridge.Sub hN, IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
      (k : ℝ) * Real.pi * r < arcLen (n := n) γ 0 1 →
      ∃ X : Fin k → FA n γ,
        (∀ i : Fin k, X i ∈ TOm (n := n) 1 γ ∧
          (∀ t : ℝ, t ∉ Set.Ioo ((i : ℝ) / k) (((i : ℝ) + 1) / k) → X i t = 0) ∧
          ∃ h : ℝ, h < 0 ∧ IsHessT (n := n) 1 γ (X i) (X i) h) ∧
        ∀ i j : Fin k, i ≠ j → IsHessT (n := n) 1 γ (X i) (X j) 0

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- The repaired `B_emb`: `n ≥ 2`. -/
def B_emb2 : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], 2 ≤ n →
    ∀ r : ℝ, 0 < r → RicciGE (Bridge.conn (hN := hN)) (((n : ℝ) - 1) / r ^ 2) →
    ∀ k : ℕ, 1 ≤ k → ∀ γ : ℝ → Bridge.Sub hN, IsGeodesic (Bridge.conn (hN := hN)) γ (Set.Icc 0 1) →
      (k : ℝ) * Real.pi * r < arcLen (n := n) γ 0 1 →
      ∃ X : Fin k → FA n γ,
        (∀ i : Fin k, X i ∈ TOm (n := n) 1 γ ∧
          (∀ t : ℝ, t ∉ Set.Ioo ((i : ℝ) / k) (((i : ℝ) + 1) / k) → X i t = 0) ∧
          ∃ h : ℝ, h < 0 ∧ IsHessT (n := n) 1 γ (X i) (X i) h) ∧
        ∀ i j : Fin k, i ≠ j → IsHessT (n := n) 1 γ (X i) (X j) 0

theorem B_emb_to_B_emb2 : B_emb → B_emb2 := fun hB V _ _ _ W _ _ _ n N hN _ _ => hB V W n N hN

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- Blind `IsHessT` values of transported project fields are the project's `E_**`. -/
theorem isHessT_toW {γ : ℝ → Bridge.Sub hN} (hγ : IsGeodesic (conn (hN := hN)) γ (Icc 0 1))
    {X₁ X₂ : ℝ → V} (hX₁ : X₁ ∈ Morse.pathTangent hN (incl hN ∘ γ))
    (hX₂ : X₂ ∈ Morse.pathTangent hN (incl hN ∘ γ)) :
    IsHessT (n := n) 1 γ (toW γ X₁) (toW γ X₂) (Morse.energyHessian hN
      (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1
      ⟨X₁, hX₁⟩ ⟨X₂, hX₂⟩) := by
  obtain ⟨r, hr⟩ := exists_isHessT hγ hX₁ hX₂
  obtain ⟨Y₁, Y₂, h1, h2, hY⟩ := isHessT_eq hγ hr
  have e : r = Morse.energyHessian hN
      (unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (conn (hN := hN)) (γ 0) (γ 1) γ)).1
      ⟨X₁, hX₁⟩ ⟨X₂, hX₂⟩ := by
    rw [hY, Morse.energyHessian_apply, Morse.energyHessian_apply,
      Morse.secondVariation_congr hN (fun s hs => (h1 s hs).trans (ambA_toW hX₁ hs))
        (fun s hs => (h2 s hs).trans (ambA_toW hX₂ hs))]
  exact e ▸ hr

end Emb

/-- **A' implies the repaired B on embedded manifolds.** The frame along `γ` is
`Morse.exists_parallel_frame` (a project lemma, not one of A's theorems); on each piece
`[i/k, (i+1)/k]` A's `exists_sinBump_neg` picks a frame field `P_{j(i)}` with
`E_**(X_i, X_i) < 0` for `X_i = sinBump (i/k) ((i+1)/k) P_{j(i)}`; A's
`energyHessian_sinBump_disjoint` (with the symmetry of `E_**`) gives `E_**(X_i, X_j) = 0`; the
fields are carried to blind fields by `Emb.toW` (in `TΩ` by `Emb.toW_mem`) and the values to blind
`IsHessT` by the converse Hessian dictionary (`Emb.exists_isHessT`, `Emb.isHessT_eq`, Items/V11_8.lean).
The blind Ricci bound gives the project's through `Emb.ricci_eq` and `Bridge.norm_eq`. -/
theorem A'_to_B_emb2 : A' → B_emb2 := by
  intro hA V _ _ _ W _ _ _ n N hN _ hn r hr hRic k hk γ hγ hL
  obtain ⟨hpath, hgeo⟩ :=
    Emb.unbroken_of_geodPQ (⟨hγ, rfl, rfl⟩ : IsGeodPQ n (Bridge.conn (hN := hN)) (γ 0) (γ 1) γ)
  have hγs : IsSmoothCurve (n := n) γ (Icc 0 1) := hγ.2.1
  have hfr : Module.finrank ℝ (Rn n) = n := finrank_euclideanSpace_fin
  -- the project's Ricci bound
  have hRicP : Morse.RicciLowerBound hN r := by
    intro q U hU
    let x : Bridge.Sub hN := q
    let U' : TangentSpace 𝓘(ℝ, Rn n) x := Bridge.L hN x U
    have hU' : ‖U'‖ = 1 := by
      refine (Bridge.norm_eq x U').trans ?_
      show ‖Bridge.D hN x (Bridge.L hN x U)‖ = 1
      rw [Bridge.D_L U.2]
      simpa using hU
    have h := hRic x U' hU'
    rw [Emb.ricci_eq] at h
    have e : (⟨Bridge.D hN x (Bridge.L hN x U), Bridge.D_mem x _⟩ : Morse.tangentSubspace hN q) = U :=
      Subtype.ext (Bridge.D_L U.2)
    rw [e] at h
    rw [hfr]
    exact h
  -- the length
  have hlen : (k : ℝ) * Real.pi * r < Morse.pathLength (Bridge.incl hN ∘ γ) 0 1 := by
    rw [← Bridge.arcLen_eq]; exact hL
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hLpos : 0 < Morse.pathLength (Bridge.incl hN ∘ γ) 0 1 :=
    lt_trans (by positivity) hlen
  obtain ⟨c, hcs, hγc, Vf, hVfs, hVfT, hVγ, u, s, P, hP, hPn, hcard, hksum⟩ :=
    Morse.exists_parallel_frame hpath hgeo hLpos
  have hn' : 2 ≤ Module.finrank ℝ (Rn n) := by rw [hfr]; exact hn
  -- the pieces
  set a : Fin k → ℝ := fun i => (i : ℝ) / k with ha_def
  set b : Fin k → ℝ := fun i => ((i : ℝ) + 1) / k with hb_def
  have ha0 : ∀ i, 0 ≤ a i := fun i => by positivity
  have hab : ∀ i, a i < b i := fun i => by
    simp only [ha_def, hb_def]
    exact div_lt_div_of_pos_right (by linarith) hkpos
  have hb1 : ∀ i : Fin k, b i ≤ 1 := fun i => by
    simp only [hb_def]
    rw [div_le_one hkpos]
    have : ((i : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast i.2
    simpa using this
  have hba : ∀ i, b i - a i = 1 / k := fun i => by simp only [ha_def, hb_def]; ring
  have hLi : ∀ i, Real.pi * r < Morse.pathLength (Bridge.incl hN ∘ γ) 0 1 * (b i - a i) := by
    intro i
    rw [hba, mul_one_div, lt_div_iff₀ hkpos]
    linarith
  have hneg : ∀ i : Fin k, ∃ j ∈ s, Morse.energyHessian hN hpath
      ⟨_, hA.1 hcs hγc (hP j) (ha0 i) (hab i) (hb1 i)⟩
      ⟨_, hA.1 hcs hγc (hP j) (ha0 i) (hab i) (hb1 i)⟩ < 0 := fun i =>
    hA.2.2 hr hn' hpath hcs hγc hVfs hVfT hVγ hP hPn hcard (hksum r hRicP) (ha0 i) (hab i)
      (hb1 i) (hLi i) fun j => hA.1 hcs hγc (hP j) (ha0 i) (hab i) (hb1 i)
  choose j hjs hj using hneg
  have hmem : ∀ i : Fin k, Morse.sinBump (a i) (b i) (P (j i)) ∈
      Morse.pathTangent hN (Bridge.incl hN ∘ γ) := fun i =>
    hA.1 hcs hγc (hP (j i)) (ha0 i) (hab i) (hb1 i)
  refine ⟨fun i => Emb.toW γ (Morse.sinBump (a i) (b i) (P (j i))), fun i => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Emb.toW_mem hγs (hmem i)
  · intro t ht
    show (if t ∈ Icc (0 : ℝ) 1 then Bridge.L hN (γ t) (Morse.sinBump (a i) (b i) (P (j i)) t)
      else 0) = 0
    split_ifs
    · rcases le_or_gt t (a i) with h | h
      · rw [Morse.sinBump_of_le (hab i).le h, map_zero]
      · have : b i ≤ t := by
          by_contra hcon
          exact ht ⟨h, lt_of_not_ge hcon⟩
        rw [Morse.sinBump_of_ge (hab i) this, map_zero]
    · rfl
  · exact ⟨_, hj i, Emb.isHessT_toW hγ (hmem i) (hmem i)⟩
  · intro i i' hii'
    have h := Emb.isHessT_toW hγ (hmem i) (hmem i')
    have hzero : Morse.energyHessian hN hpath ⟨_, hmem i⟩ ⟨_, hmem i'⟩ = 0 := by
      rcases lt_or_gt_of_ne hii' with hlt | hlt
      · have hle : b i ≤ a i' := by
          simp only [ha_def, hb_def]
          refine div_le_div_of_nonneg_right ?_ hkpos.le
          have : (i : ℕ) + 1 ≤ i' := hlt
          exact_mod_cast this
        exact hA.2.1 hpath hcs hγc (hP (j i)) (hP (j i')) (ha0 i) (hab i) (hb1 i) (ha0 i')
          (hab i') (hb1 i') hle _ _
      · have hle : b i' ≤ a i := by
          simp only [ha_def, hb_def]
          refine div_le_div_of_nonneg_right ?_ hkpos.le
          have : (i' : ℕ) + 1 ≤ i := hlt
          exact_mod_cast this
        rw [← (Morse.energyHessian_isSymm hN hpath).eq]
        exact hA.2.1 hpath hcs hγc (hP (j i')) (hP (j i)) (ha0 i') (hab i') (hb1 i') (ha0 i)
          (hab i) (hb1 i) hle _ _
    exact hzero ▸ h

/-- `A → B` is false (A holds, B does not). -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A`: vacuous (B is false). Not under `#rt_check`: `A`'s statement itself contains the
banned `Morse.sinBump_mem_pathTangent` as a proof term (inside the type of
`Morse.energyHessian_sinBump`), so every term of type `A` mentions it; the proof content is
`not_B`, which passes `#rt_check`. -/
theorem B_to_A : B → A := fun hB => (not_B hB).elim

#rt_check RoundTrip.V11_15.not_B [Morse.sinBump_mem_pathTangent, Morse.energyHessian_sinBump,
  Morse.energyHessian_sinBump_disjoint, Morse.exists_sinBump_neg]
/-- **A implies the repaired B on embedded manifolds.** -/
theorem A_to_B_emb2 : A → B_emb2 := fun hA => A'_to_B_emb2 (A_to_A' hA)

#rt_check RoundTrip.V11_15.A'_to_B_emb2 [Morse.sinBump_mem_pathTangent,
  Morse.energyHessian_sinBump, Morse.energyHessian_sinBump_disjoint, Morse.exists_sinBump_neg]
#rt_overlap RoundTrip.V11_15.A'_to_B_emb2 [Morse.sinBump_mem_pathTangent,
  Morse.energyHessian_sinBump, Morse.energyHessian_sinBump_disjoint, Morse.exists_sinBump_neg]
#rt_overlap RoundTrip.V11_15.not_B [Morse.sinBump_mem_pathTangent, Morse.energyHessian_sinBump,
  Morse.energyHessian_sinBump_disjoint, Morse.exists_sinBump_neg]

end RoundTrip.V11_15
