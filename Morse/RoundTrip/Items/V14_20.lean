import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.EnergyC2
import RoundTrip.Blind.V14_20

open Matrix Set Filter Topology Module
open scoped ContDiff Manifold

noncomputable section

set_option linter.unusedSectionVars false

namespace RoundTrip.V14_20

/-- The project's statement (universes of `ι` instantiated at `0`): Lemma 23.2 with the index computed
by the Index Theorem (for `A ∈ 𝔰𝔲(2m)`, `exp A = −I`: there are odd `k_j`, `Σ k_j = 0`, `A = T suDiag(k) Tᴴ`;
the index of `t ↦ exp tA` is `0` if all `k_j = ±1` and `≥ 2m + 2` otherwise); the energy of `t ↦ exp tA` is
`‖A‖²`; and every unbroken geodesic from `I` to `−I` in `SU(2m)` which does not have least energy has
index (`formIndex` of the project's `energyHessian`) `≥ 2m + 2`. -/
def A : Prop :=
  type_of% @Morse.lemma_23_2_index.{0} ∧ type_of% @Morse.energy_exp_smul.{0} ∧
    type_of% @Morse.le_formIndex_of_not_minimal_su.{0}

theorem A_holds : A :=
  ⟨@Morse.lemma_23_2_index, @Morse.energy_exp_smul, @Morse.le_formIndex_of_not_minimal_su⟩

/-! ## The embedded special case: `SU(n)` as `Bridge.Sub` (model `ℝᵈ`), `ψ` the inclusion
(infrastructure copied from `Items/V14_14.lean`) -/

namespace Emb

open RoundTrip.Bridge
open scoped Morse.MatrixInner

section Model

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A linear equivalence `Z ≃ ℝᵐ`, `m = dim Z` (copied from `Items/V7_28.lean`). -/
def eZ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] :
    Z ≃L[ℝ] Bridge.Rn (finrank ℝ Z) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {N : Set V}

/-- A slice chart modelled on `Z`, read in `ℝᵐ` (copied from `Items/V7_28.lean`). -/
def chartRn (σ : Milnor.SliceChart 𝓘(ℝ, V) Z W N) :
    Milnor.SliceChart 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W N where
  φ := σ.φ.trans ((eZ Z).prodCongr (ContinuousLinearEquiv.refl ℝ W)).toDiffeomorph.toPartialDiffeomorph
  x₀ := σ.x₀
  x₀_mem := σ.x₀_mem
  x₀_source := ⟨σ.x₀_source, trivial⟩
  slice := fun p hp => σ.slice p hp.1

/-- A slice submanifold modelled on `Z` is one modelled on `ℝᵐ` (copied from `Items/V7_28.lean`). -/
theorem isSliceRn (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Bridge.Rn (finrank ℝ Z)) W N :=
  fun p hp => ⟨chartRn (hN p hp).choose, ⟨(hN p hp).choose_spec, trivial⟩⟩

/-- ... with the same tangent spaces (copied from `Items/V7_28.lean`). -/
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

/-- Geodesics only depend on the tangent spaces. -/
theorem isGeodesicOn_rn_iff (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {γ : ℝ → V}
    {s : Set ℝ} : Morse.IsGeodesicOn (isSliceRn hN) γ s ↔ Morse.IsGeodesicOn hN γ s :=
  ⟨fun h => ⟨h.isOpen, h.mem, h.contDiffOn, fun t ht => by
      have := h.normal t ht
      rwa [tangentSubspace_rn] at this⟩,
    fun h => ⟨h.isOpen, h.mem, h.contDiffOn, fun t ht => by
      have := h.normal t ht
      rwa [← tangentSubspace_rn hN] at this⟩⟩

end Model

variable (n : ℕ) [NeZero n]

/-- `SU(n)` as a slice submanifold modelled on `ℝᵈ`, `d = dim 𝔰𝔲(n)`. -/
abbrev hR := isSliceRn (Morse.isSliceSubmanifold_specialUnitaryGroup (ι := Fin n))

/-- The dimension `d`. -/
abbrev dd : ℕ := finrank ℝ (Morse.specialSkewHermitian (Fin n)).toSubmodule

/-- `SU(n)` as an abstract Riemannian manifold (induced metric). -/
abbrev SUM := Bridge.Sub (hR n)

/-- The inclusion `ψ : SU(n) → Mₙ(ℂ)`, read in the blind file's `Fin n → Fin n → ℂ`. -/
def ψ : SUM n → Mat n := incl (hR n)

variable {n}

theorem ψ_eq (x : SUM n) : ψ n x = incl (hR n) x := rfl

/-- `id : (Mₙ(ℂ), Frobenius) → (Fin n → Fin n → ℂ, sup norm)` as a continuous linear map. -/
def idFP : Mat n →L[ℝ] (Fin n → Fin n → ℂ) :=
  ContinuousLinearMap.id ℝ (Mat n)

theorem dMat_ψ (x : SUM n) (v : TangentSpace 𝓘(ℝ, Rn (dd n)) x) :
    dMat (n := dd n) n (ψ n) x v = D (hR n) x v := by
  have h : ψ n = (idFP (n := n)) ∘ incl (hR n) := rfl
  unfold dMat
  rw [h, mfderiv_comp x (idFP (n := n)).mdifferentiableAt
    (contMDiff_incl.mdifferentiableAt (by simp)), ContinuousLinearMap.mfderiv_eq]
  rfl

theorem re_trace_swap (X Y : Mat n) :
    RCLike.re (trace (Xᴴ * Y)) = (trace (X * Yᴴ)).re := by
  have h1 : trace (Xᴴ * Y) = star (trace (Yᴴ * X)) := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  rw [h1, Matrix.trace_mul_comm Yᴴ X]
  simp

/-- **`ψ` is an `IsSUModel`.** -/
theorem isSUModel_ψ : IsSUModel (n := dd n) n (ψ n) := by
  refine ⟨(idFP (n := n)).contMDiff.comp contMDiff_incl, Topology.IsEmbedding.subtypeVal, Subtype.range_val, fun x v w => ?_⟩
  rw [inner_eq, Morse.inner_def, dMat_ψ, dMat_ψ]
  exact re_trace_swap _ _

/-- Blind geodesic of the induced connection on `[0, 1]` ⇒ project unbroken geodesic of `SU(n)`. -/
theorem isUnbrokenGeodesic_of_isGeodesic {γ : ℝ → SUM n}
    (h : IsGeodesic (conn (hN := hR n)) γ (Icc 0 1)) :
    Morse.IsUnbrokenGeodesic Morse.isSliceSubmanifold_specialUnitaryGroup (incl (hR n) ∘ γ) :=
  ⟨isSmoothCurve_iff.1 h.2.1, (isGeodesicOn_rn_iff _).1 (isGeodesicOn_Ioo h)⟩

theorem mem_pathSpace_of_isGeodesic {γ : ℝ → SUM n}
    (h : IsGeodesic (conn (hN := hR n)) γ (Icc 0 1)) :
    incl (hR n) ∘ γ ∈ Morse.pathSpace (specialUnitaryGroup (Fin n) ℂ : Set (Mat n))
      (incl (hR n) (γ 0)) (incl (hR n) (γ 1)) :=
  ⟨Morse.IsPiecewiseSmooth.of_contDiffOn (isSmoothCurve_iff.1 h.2.1) zero_le_one subset_rfl,
    fun t _ => (γ t).2, rfl, rfl⟩

/-- A project minimal geodesic agreeing with `incl ∘ γ` on `[0, 1]` makes `γ` a blind minimal geodesic. -/
theorem isMinimal_of_isMinimalGeodesic {γ : ℝ → SUM n} {c : ℝ → Mat n}
    (h : IsGeodesic (conn (hN := hR n)) γ (Icc 0 1)) (heq : EqOn (incl (hR n) ∘ γ) c (Icc 0 1))
    (hmin : Morse.IsMinimalGeodesic Morse.isSliceSubmanifold_specialUnitaryGroup c 0 1) :
    IsMinimal (conn (hN := hR n)) γ 0 1 := by
  refine ⟨h, fun pw a' b' _ hpw ha hb => ?_⟩
  have h1 := hmin.2.2 (incl (hR n) ∘ pw) a' b' (isPiecewiseSmooth_of_isPW hpw)
    (fun t _ => (pw t).2)
    (by rw [Function.comp_apply, ha, ← heq ⟨le_rfl, zero_le_one⟩]; rfl)
    (by rw [Function.comp_apply, hb, ← heq ⟨zero_le_one, le_rfl⟩]; rfl)
  have e1 : arcLen (n := dd n) γ 0 1 = Morse.pathLength c 0 1 := by
    rw [show arcLen (n := dd n) γ 0 1 = BridgePrelude.arcLen (n := dd n) γ 0 1 from rfl, arcLen_eq,
      pathLength_congr zero_le_one heq]
  have e2 : arcLen (n := dd n) pw a' b' = Morse.pathLength (incl (hR n) ∘ pw) a' b' := by
    rw [show arcLen (n := dd n) pw a' b' = BridgePrelude.arcLen (n := dd n) pw a' b' from rfl,
      arcLen_eq]
  rw [e1, e2]
  exact h1

end Emb

open scoped Morse.MatrixInner

open Emb in
/-- The missing index dictionary (as in `Items/V13_7.lean`): for a blind geodesic `γ` on `[0,1]` of the
induced connection of `SU(n)` from `I` to `−I`, Milnor's variational index `lam 1 γ` (blind: the index of the
blind `HessT` on the blind `TΩ_γ`) is the project's `formIndex (energyHessian _)`. Not proved here. -/
def LamEq : Prop :=
  ∀ (n : ℕ) [NeZero n] (γ : ℝ → SUM n)
    (hγ : Bridge.incl (hR n) ∘ γ ∈ Morse.pathSpace (specialUnitaryGroup (Fin n) ℂ : Set (Mat n)) 1 (-1)),
    IsGeodesic (Bridge.conn (hN := hR n)) γ (Icc 0 1) →
      lam (n := dd n) 1 γ = Morse.formIndex
        (Morse.energyHessian Morse.isSliceSubmanifold_specialUnitaryGroup hγ)

open Emb in
/-- `B` for `M = SU(2m)` (`m ≥ 1`) with the induced metric (`Bridge.Sub`, model `ℝᵈ`), `ψ` the inclusion,
`cov` the induced connection; connectedness of `SU(2m)` (an instance argument of `B`, formalized neither in
Mathlib nor in the project) is kept as a hypothesis. -/
def B_emb : Prop :=
  ∀ (m : ℕ) [NeZero (2 * m)], ConnectedSpace (SUM (2 * m)) →
    ∀ p q : SUM (2 * m), ψ (2 * m) p = 1 → ψ (2 * m) q = -1 → ∀ γ : ℝ → SUM (2 * m),
      IsGeodPQ (dd (2 * m)) (Bridge.conn (hN := hR (2 * m))) p q γ →
      ¬ IsMinimal (Bridge.conn (hN := hR (2 * m))) γ 0 1 →
      ((2 * m + 2 : ℕ) : ℕ∞) ≤ lam (n := dd (2 * m)) 1 γ

theorem B_to_B_emb : B → B_emb := by
  intro hB m _ _ p q hp hq γ hγ hnm
  exact hB m (Emb.dd (2 * m)) (Emb.SUM (2 * m)) (Emb.ψ (2 * m)) Emb.isSUModel_ψ Bridge.conn
    Bridge.conn_isLC p q hp hq γ hγ hnm

/-- `A` (its Lemma 23.2 conjunct) gives `B_emb`, granted the index dictionary `LamEq`. -/
theorem A_to_B_emb_of_lamEq : A → LamEq → B_emb := by
  rintro ⟨h232, -, -⟩ hlam m _ _ p q hp hq γ ⟨hgeo, h0, h1⟩ hnm
  have hcard : Fintype.card (Fin (2 * m)) = 2 * m := Fintype.card_fin _
  have hu := Emb.isUnbrokenGeodesic_of_isGeodesic hgeo
  have hpath := Emb.mem_pathSpace_of_isGeodesic hgeo
  have hp' : Bridge.incl (Emb.hR (2 * m)) p = 1 := hp
  have hq' : Bridge.incl (Emb.hR (2 * m)) q = -1 := hq
  rw [h0, h1, hp', hq'] at hpath
  obtain ⟨A, hA, hEq⟩ := Morse.eqOn_exp_smul_of_isUnbrokenGeodesic_su hpath hu
  have hexp : NormedSpace.exp A = -1 := by
    have := hEq ⟨zero_le_one, le_rfl⟩
    simp only [Function.comp_apply, h1, hq', one_smul] at this
    exact this.symm
  have hγA := Morse.mem_pathSpace_exp hA hexp
  obtain ⟨k, -, -, ⟨T, hT, hAeq⟩, -, hnon⟩ := h232 hcard hA hexp hγA
  have hpm : ¬ ∀ i, k i = 1 ∨ k i = -1 := by
    intro hpm
    have hsq : A * A = -((Real.pi : ℂ) ^ 2) • (1 : Mat (2 * m)) := by
      rw [hAeq]; exact (Morse.sq_conj_suDiag_iff hT k).2 hpm
    exact hnm (Emb.isMinimal_of_isMinimalGeodesic hgeo hEq
      ((Morse.isMinimalGeodesic_exp_iff hcard hA hexp).2 hsq))
  rw [hlam (2 * m) γ hpath hgeo, Morse.formIndex_energyHessian_congr hpath hγA hu
    (Morse.isUnbrokenGeodesic_exp hA) hEq]
  exact hnon hpm

#rt_check RoundTrip.V14_20.A_to_B_emb_of_lamEq [Morse.lemma_23_2_index, Morse.energy_exp_smul, Morse.le_formIndex_of_not_minimal_su]
#rt_check RoundTrip.V14_20.B_to_B_emb [Morse.lemma_23_2_index, Morse.energy_exp_smul, Morse.le_formIndex_of_not_minimal_su]
#rt_overlap RoundTrip.V14_20.A_to_B_emb_of_lamEq [Morse.lemma_23_2_index, Morse.energy_exp_smul, Morse.le_formIndex_of_not_minimal_su]

namespace LamPf

/-! ### `λ = indexUpTo` on `↥N` (copied from `Items/V9_23.lean`, namespace `Emb` there; the blind
vocabulary of this item's blind file is textually the same as V9_23's) -/

open Set Filter Topology Function
open scoped ContDiff Manifold
open Bundle

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- `e₀, e₁ ∈ ℝ²`. -/
noncomputable abbrev e0 : Rn 2 := EuclideanSpace.single 0 (1 : ℝ)
noncomputable abbrev e1 : Rn 2 := EuclideanSpace.single 1 (1 : ℝ)

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-! ### Maps into `↥N` (copied from `Items/V8_10.lean`, `Items/V8_12.lean`) -/

theorem contMDiffWithinAt_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s x ↔
      ContDiffWithinAt ℝ ∞ (Bridge.incl hN ∘ f) s x := by
  constructor
  · intro h
    exact contMDiffWithinAt_iff_contDiffWithinAt.1
      ((Bridge.contMDiff_incl (f x)).comp_contMDiffWithinAt x h)
  · intro h
    have hcont : ContinuousWithinAt f s x :=
      (Topology.IsInducing.subtypeVal.continuousWithinAt_iff (f := f)).2 h.continuousWithinAt
    rw [contMDiffWithinAt_iff_target]
    refine ⟨hcont, ?_⟩
    set sl := Morse.sliceAt hN (f x)
    have hφ : ContDiffAt ℝ ∞ (fun y => (sl.φ y).1) (Bridge.incl hN (f x)) :=
      contDiff_fst.contDiffAt.comp _ ((Milnor.Problems.sliceChart_contDiffOn sl).contDiffAt
        (sl.φ.open_source.mem_nhds (Morse.mem_sliceAt_source hN (f x))))
    have e : (extChartAt 𝓘(ℝ, Rn n) (f x) ∘ f) =
        (fun y => (sl.φ y).1) ∘ (Bridge.incl hN ∘ f) := rfl
    rw [e]
    exact contMDiffWithinAt_iff_contDiffWithinAt.2 (hφ.comp_contDiffWithinAt x h)

theorem contMDiffOn_map_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {s : Set E} :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f s ↔ ContDiffOn ℝ ∞ (Bridge.incl hN ∘ f) s :=
  forall₂_congr fun _ _ => contMDiffWithinAt_map_iff

/-- The derivative of a map from a normed space into `N`, read in `V`. -/
theorem D_mfderiv_map {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → Bridge.Sub hN}
    {x : E} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x) (v : E) :
    Bridge.D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (Bridge.incl hN ∘ f) x v := by
  have h := HasMFDerivAt.comp x
    ((Bridge.contMDiff_incl (f x)).mdifferentiableAt (by simp)).hasMFDerivAt hf.hasMFDerivAt
  have h' : HasFDerivAt (Bridge.incl hN ∘ f)
      ((Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n)) x :=
    hasMFDerivAt_iff_hasFDerivAt.1 h
  have h'' : fderiv ℝ (Bridge.incl hN ∘ f) x =
      (Bridge.D hN (f x)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x : E →L[ℝ] Rn n) :=
    HasFDerivAt.fderiv h'
  exact (DFunLike.congr_fun h'' v).symm

/-- A map into `N` that is `C^∞` at `x` when read in `V` has its derivative read in `V`. -/
theorem D_mfderiv_of_contDiffAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Bridge.Sub hN} {x : E} (hf : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ f) x) (v : E) :
    Bridge.D hN (f x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Rn n) f x v) = fderiv ℝ (Bridge.incl hN ∘ f) x v := by
  have : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Rn n) ∞ f x := by
    rw [← contMDiffWithinAt_univ]
    exact contMDiffWithinAt_map_iff.2 (contDiffWithinAt_univ.2 hf)
  exact D_mfderiv_map (this.mdifferentiableAt (by simp)) v

/-! ### Paths, geodesics and `TΩ` -/

/-- A blind geodesic on `[0, 1]` (induced connection) is a project unbroken geodesic. -/
theorem isUnbrokenGeodesic_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Morse.IsUnbrokenGeodesic hN (Bridge.incl hN ∘ pw) := by
  have h' : RoundTrip.BridgePrelude.IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1) := h
  exact ⟨(Bridge.isGeodesic_iff.1 h').2.1, Bridge.isGeodesicOn_Ioo h'⟩

theorem mem_pathSpace_of_isGeodesic {pw : ℝ → Bridge.Sub hN}
    (h : IsGeodesic (Bridge.conn (hN := hN)) pw (Icc 0 1)) :
    Bridge.incl hN ∘ pw ∈ Morse.pathSpace N (Bridge.incl hN (pw 0)) (Bridge.incl hN (pw 1)) := by
  have hcd := (isUnbrokenGeodesic_of_isGeodesic h).1
  exact ⟨⟨zero_le_one, hcd.continuousOn, ∅, fun s u hs _ hu _ => hcd.mono (Icc_subset_Icc hs hu)⟩,
    fun t _ => (pw t).2, rfl, rfl⟩
/-! ### 2-parameter variations -/

/-- The ambient family `(u, s) ↦ α(u, s) ∈ N ⊆ V`. -/
def amb {m : ℕ} (α : Rn m → ℝ → Bridge.Sub hN) : Rn m → ℝ → V := fun u s => Bridge.incl hN (α u s)

/-- Theorem 13.1 for `N` (the statement of `Morse.second_variation`, or of
`Morse.hasDerivAt_energyHessian` unfolded), taken as a hypothesis. -/
def SV (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N) : Prop :=
  ∀ {γ : ℝ → V} {p q : V}, γ ∈ Morse.pathSpace N p q → Morse.IsUnbrokenGeodesic hN γ →
    ∀ {U : Set (ℝ × ℝ)} {α : ℝ × ℝ → ℝ → V} {B : Finset ℝ}, Morse.IsVariation N U α B →
    (∀ t ∈ Icc (0 : ℝ) 1, α 0 t = γ t) →
    HasDerivAt (fun u₁ => deriv (fun u₂ => Morse.energy (α (u₁, u₂)) 0 1) 0)
      (2 * Morse.secondVariation hN γ (fun t => deriv (fun u₁ => α (u₁, 0) t) 0)
        (fun t => deriv (fun u₂ => α (0, u₂) t) 0)) 0

/-! ### Existence of `IsHess` values (Lemma 11.A on `↥N`, fields matched on all of `ℝ`) -/

/-- Near the zero section `exp` is smooth with `d(exp_q)₀ = id` (from `Morse.exists_isOpen_exp`
and `Morse.hasFDerivAt_exp_zero`), along any linear map into `T_qN`. -/
theorem exp_local {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {q : V} (hq : q ∈ N)
    (Λ : P →L[ℝ] V) (hΛ : ∀ u, Morse.prj hN q (Λ u) = Λ u) :
    (∀ᶠ u in 𝓝 (0 : P), Morse.exp hN q (Λ u) ∈ N) ∧
    ContDiffAt ℝ ∞ (fun u => Morse.exp hN q (Λ u)) 0 ∧
    HasFDerivAt (fun u => Morse.exp hN q (Λ u)) Λ 0 := by
  obtain ⟨O, hO, hO0, hexp⟩ := Morse.exists_isOpen_exp (hN := hN)
  have hTN : ∀ u, (q, Λ u) ∈ Milnor.Problems.tangentBundleSet hN :=
    fun u => ⟨hq, (Morse.prj_eq_self_iff hN hq).1 (hΛ u)⟩
  have hc : Continuous (fun u : P => (q, Λ u)) := continuous_const.prodMk Λ.continuous
  have hq0 : (q, Λ 0) ∈ O := by rw [map_zero]; exact hO0 q hq
  have hev : ∀ᶠ u in 𝓝 (0 : P), (q, Λ u) ∈ O :=
    hc.continuousAt.preimage_mem_nhds (hO.mem_nhds hq0)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hev] with u hu
    exact Morse.exp_mem_of_mem_expDom (hexp _ hu (hTN u)).1
  · obtain ⟨-, F, O', hO', hzO', hF, hFeq⟩ := hexp _ hq0 (hTN 0)
    have h1 : ContDiffAt ℝ ∞ (fun u => F (q, Λ u)) 0 :=
      (hF.contDiffAt (hO'.mem_nhds hzO')).comp (0 : P)
        (contDiff_const.prodMk Λ.contDiff).contDiffAt
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hc.continuousAt.preimage_mem_nhds (hO'.mem_nhds hzO')] with u hu
    exact hFeq _ hu (hTN u)
  · set qt : N := ⟨q, hq⟩
    let L : P →L[ℝ] Morse.tangentSubspace hN qt :=
      Λ.codRestrict (Morse.tangentSubspace hN qt) fun u =>
        (Morse.prj_eq_self_iff hN hq).1 (hΛ u)
    have h1 := Morse.hasFDerivAt_exp_zero (hN := hN) qt
    rw [← map_zero L] at h1
    have h2 := h1.comp (0 : P) L.hasFDerivAt
    have hL : ((Morse.tangentSubspace hN qt).subtypeL.comp L) = Λ :=
      ContinuousLinearMap.ext fun u => rfl
    rw [hL] at h2
    exact h2

open Classical in
/-- Milnor's `α(u, t) = exp_{γ(t)}(Λ(t) u)`, as a map into `↥N` (junk `γ t` where `exp` leaves
`N`, which does not happen near `u = 0`). -/
noncomputable def liftE (γ : ℝ → Bridge.Sub hN) (Λ : ℝ → Rn 2 →L[ℝ] V) (u : Rn 2) (t : ℝ) :
    Bridge.Sub hN :=
  if h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N then (⟨_, h⟩ : N) else γ t

theorem liftE_of_mem {γ : ℝ → Bridge.Sub hN} {Λ : ℝ → Rn 2 →L[ℝ] V} {u : Rn 2} {t : ℝ}
    (h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N) :
    liftE γ Λ u t = (⟨_, h⟩ : N) := by
  unfold liftE; exact dif_pos h

theorem incl_liftE {γ : ℝ → Bridge.Sub hN} {Λ : ℝ → Rn 2 →L[ℝ] V} {u : Rn 2} {t : ℝ}
    (h : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) ∈ N) :
    Bridge.incl hN (liftE γ Λ u t) = Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) := by
  rw [liftE_of_mem h]; rfl

open RoundTrip.Bridge

theorem isSmoothCurveIn {γ : ℝ → Bridge.Sub hN} (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    Morse.IsSmoothCurveIn hN (incl hN ∘ γ) :=
  ⟨isSmoothCurve_iff.1 hγ, fun t _ => (γ t).2⟩

open Classical in
/-- A blind field along `γ` from an ambient field `X`: `t ↦ L_{γ t}(X t)` on `[0,1]`, `0` outside. -/
noncomputable def toFA (γ : ℝ → Bridge.Sub hN) (X : ℝ → V) : FA n γ :=
  fun t => if t ∈ Icc (0 : ℝ) 1 then L hN (γ t) (X t) else 0

theorem toFA_of_mem {γ : ℝ → Bridge.Sub hN} (X : ℝ → V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    toFA γ X t = L hN (γ t) (X t) := by
  unfold toFA
  exact if_pos ht

theorem toFA_of_not_mem {γ : ℝ → Bridge.Sub hN} (X : ℝ → V) {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) :
    toFA γ X t = 0 := by
  unfold toFA
  exact if_neg ht

theorem ambA_toFA {γ : ℝ → Bridge.Sub hN} {X : ℝ → V}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (X t) = X t) :
    EqOn (ambA γ (toFA γ X)) X (Icc 0 1) := fun t ht => by
  show D hN (γ t) (toFA γ X t) = X t
  rw [toFA_of_mem X ht]
  exact D_L ((Morse.prj_eq_self_iff hN (γ t).2).1 (hX t ht))

/-- `toFA` as a linear map. -/
noncomputable def toFAₗ (γ : ℝ → Bridge.Sub hN) : (ℝ → V) →ₗ[ℝ] FA n γ where
  toFun := toFA γ
  map_add' X Y := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · show toFA γ (X + Y) t = toFA γ X t + toFA γ Y t
      rw [toFA_of_mem _ ht, toFA_of_mem _ ht, toFA_of_mem _ ht]
      exact map_add (L hN (γ t)) (X t) (Y t)
    · show toFA γ (X + Y) t = toFA γ X t + toFA γ Y t
      rw [toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, add_zero]
  map_smul' c X := by
    funext t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · show toFA γ (c • X) t = c • toFA γ X t
      rw [toFA_of_mem _ ht, toFA_of_mem _ ht]
      exact map_smul (L hN (γ t)) c (X t)
    · show toFA γ (c • X) t = c • toFA γ X t
      rw [toFA_of_not_mem _ ht, toFA_of_not_mem _ ht, smul_zero]


/-- On fields tangent along `γ` on `[0,1]` and constant off `[0,1]`, `toFA` is injective. -/
theorem toFA_injOn {γ : ℝ → Bridge.Sub hN} {X Y : ℝ → V}
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (X t) = X t)
    (hY : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN ((incl hN ∘ γ) t) (Y t) = Y t)
    (h : toFA γ X = toFA γ Y) : EqOn X Y (Icc 0 1) := fun t ht => by
  rw [← ambA_toFA hX ht, ← ambA_toFA hY ht, h]

/-- Theorem 13.1 (`Morse.second_variation`, not a theorem of this item) in the form `SV`. -/
theorem sv_holds : SV hN := by
  intro _ _ _ _ hub _ _ _ hβ hβγ
  exact Morse.second_variation hN hub hβ hβγ


/-- Continuity on `[0, t_k]` from continuity on the closed pieces of a subdivision. -/
theorem continuousOn_of_pieces {β : Type*} [TopologicalSpace β] {f : ℝ → β} {t : ℕ → ℝ}
    (ht0 : t 0 = 0) : ∀ {k : ℕ}, (∀ i < k, t i < t (i + 1)) →
    (∀ i < k, ContinuousOn f (Icc (t i) (t (i + 1)))) → ContinuousOn f (Icc 0 (t k))
  | 0, _, _ => by rw [ht0, Icc_self]; exact continuousOn_singleton f 0
  | k + 1, hlt, h => by
    have hlt' : ∀ i < k, t i < t (i + 1) := fun i hi => hlt i (by omega)
    have h0k : 0 ≤ t k := ht0 ▸ Bridge.le_of_strictSeq hlt' (Nat.zero_le k) le_rfl
    rw [← Icc_union_Icc_eq_Icc h0k (hlt k (by omega)).le]
    exact (continuousOn_of_pieces ht0 hlt' fun i hi => h i (by omega)).union_of_isClosed
      (h k (by omega)) isClosed_Icc isClosed_Icc

/-! #### Subdivisions of `[0, τ]` -/

theorem exists_piece_of_memT {τ : ℝ} (hτ : 0 < τ) {k : ℕ} {t : ℕ → ℝ} (h0 : t 0 = 0)
    (hk : t k = τ) (hlt : ∀ i < k, t i < t (i + 1)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) :
    ∃ i < k, s ∈ Icc (t i) (t (i + 1)) := by
  classical
  have hk0 : k ≠ 0 := by rintro rfl; rw [h0] at hk; exact hτ.ne hk
  have hP : ∃ j, s ≤ t j ∧ j ≤ k := ⟨k, hk ▸ hs.2, le_rfl⟩
  have hm := Nat.find_spec hP
  by_cases hm0 : Nat.find hP = 0
  · refine ⟨0, Nat.pos_of_ne_zero hk0, ?_, ?_⟩
    · rw [h0]; exact hs.1
    · have : s ≤ t 0 := by rw [← hm0]; exact hm.1
      exact this.trans (hlt 0 (Nat.pos_of_ne_zero hk0)).le
  · refine ⟨Nat.find hP - 1, by omega, ?_, ?_⟩
    · by_contra hcon
      exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
        ⟨(lt_of_not_ge hcon).le, by omega⟩
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]; exact hm.1

theorem exists_piece_of_subdivT {τ : ℝ} {t : ℕ → ℝ} {k : ℕ} (h0 : t 0 = 0) (hk : t k = τ)
    (hlt : ∀ i < k, t i < t (i + 1)) {s u : ℝ} (hs : 0 ≤ s) (hsu : s < u) (hub : u ≤ τ)
    (hB : ∀ x ∈ (Finset.range (k + 1)).image t, x ∉ Ioo s u) :
    ∃ i < k, t i ≤ s ∧ u ≤ t (i + 1) := by
  have hP : ∃ j, s < t j ∧ j ≤ k := ⟨k, by rw [hk]; linarith, le_rfl⟩
  classical
  set m := Nat.find hP
  have hm : s < t m ∧ m ≤ k := Nat.find_spec hP
  have hm0 : m ≠ 0 := by
    intro h; have := hm.1; rw [h, h0] at this; linarith
  have hi : t (m - 1) ≤ s := by
    by_contra hcon
    exact Nat.find_min hP (Nat.sub_lt (Nat.pos_of_ne_zero hm0) one_pos)
      ⟨lt_of_not_ge hcon, by omega⟩
  have hu : u ≤ t m := by
    by_contra hcon
    exact hB (t m) (Finset.mem_image.2 ⟨m, Finset.mem_range.2 (by omega), rfl⟩)
      ⟨hm.1, lt_of_not_ge hcon⟩
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
  exact ⟨m - 1, by omega, hi, hm1.symm ▸ hu⟩

/-- A subdivision `0 = t₀ < ⋯ < t_k = τ` whose open pieces avoid a finite set `B`. -/
theorem exists_subdivT {τ : ℝ} (hτ : 0 < τ) (B : Finset ℝ) : ∃ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 ∧
    t k = τ ∧ (∀ i < k, t i < t (i + 1)) ∧
    ∀ i < k, 0 ≤ t i ∧ t (i + 1) ≤ τ ∧ ∀ x ∈ B, x ∉ Ioo (t i) (t (i + 1)) := by
  classical
  have hlt : (0 : ℝ) < τ := hτ
  set a : ℝ := 0
  set b : ℝ := τ
  set S : Finset ℝ := insert a (insert b (B.filter (· ∈ Ioo a b)))
  have hS : ∀ x ∈ S, a ≤ x ∧ x ≤ b := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_filter] at hx
    rcases hx with rfl | rfl | ⟨-, hx⟩
    · exact ⟨le_rfl, hlt.le⟩
    · exact ⟨hlt.le, le_rfl⟩
    · exact ⟨hx.1.le, hx.2.le⟩
  have haS : a ∈ S := Finset.mem_insert_self _ _
  have hbS : b ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := S.card
  have hm : 1 < m := Finset.one_lt_card.2 ⟨a, haS, b, hbS, hlt.ne⟩
  set e := S.orderEmbOfFin rfl
  set t : ℕ → ℝ := fun j => if h : j < m then e ⟨j, h⟩ else b
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

/-! #### `TΩ(γ|[0, τ])`: blind `TOm τ` vs the project's `fieldsUpTo τ` -/

/-- **Blind ⇒ project**: the ambient field of a blind `W ∈ TΩ(γ|[0,τ])` lies in the project's
`TΩ_γ` and vanishes outside `[0, τ]`. -/
theorem mem_pathTangent_of_inTOmegaT {τ : ℝ} (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    {X : FA n γ} (h : InTOmegaT (n := n) τ γ X) :
    Bridge.ambA γ X ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ) ∧
      ∀ t, t ∉ Icc (0 : ℝ) τ → Bridge.ambA γ X t = 0 := by
  obtain ⟨⟨k, t, ht0, htk, hlt, -, hsm⟩, hX0, hXτ, hout⟩ := h
  have hzero : ∀ s, τ ≤ s → Bridge.ambA γ X s = 0 := by
    intro s hs
    rcases eq_or_lt_of_le hs with rfl | hs'
    · show Bridge.D hN (γ τ) (X τ) = 0
      rw [hXτ]; exact map_zero _
    · show Bridge.D hN (γ s) (X s) = 0
      rw [hout s fun h => absurd h.2 (not_le.2 hs')]; exact map_zero _
  have hsm' : ∀ i < k, ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc (t i) (t (i + 1))) := fun i hi => by
    have h' : RoundTrip.BridgePrelude.IsSmoothAlong γ (Icc (t i) (t (i + 1))) X := hsm i hi
    exact (Bridge.isSmoothAlong_iff.1 h').2
  have hpiece : ∀ s u, 0 ≤ s → s < u → u ≤ 1 →
      (∀ x ∈ insert τ ((Finset.range (k + 1)).image t), x ∉ Ioo s u) →
      ContDiffOn ℝ ∞ (Bridge.ambA γ X) (Icc s u) := by
    intro s u hs hsu hu hB
    by_cases huτ : u ≤ τ
    · obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdivT ht0 htk hlt hs hsu huτ
        fun x hx => hB x (Finset.mem_insert_of_mem hx)
      exact (hsm' i hi).mono (Icc_subset_Icc hti hui)
    · have hτs : τ ≤ s := by
        by_contra h
        exact hB τ (Finset.mem_insert_self _ _) ⟨lt_of_not_ge h, lt_of_not_ge huτ⟩
      exact contDiffOn_const.congr fun x hx => hzero x (hτs.trans hx.1)
  refine ⟨(Morse.mem_pathTangent hN).2 ⟨⟨zero_le_one, Morse.continuousOn_of_piecewise
    fun s u hs hsu hu hB => (hpiece s u hs hsu hu hB).continuousOn, _, hpiece⟩,
    fun τ' _ => (Morse.prj_eq_self_iff hN (γ τ').2).2 (Bridge.D_mem (γ τ') (X τ')), ?_, ?_⟩, ?_⟩
  · show Bridge.D hN (γ 0) (X 0) = 0
    rw [hX0]; exact map_zero _
  · exact hzero 1 hτ1
  · intro s hs
    show Bridge.D hN (γ s) (X s) = 0
    rw [hout s hs]; exact map_zero _

/-- **Project ⇒ blind**: a project field in `TΩ_γ` vanishing outside `[0, τ]` gives a blind field
`toFA γ X ∈ TΩ(γ|[0,τ])`. -/
theorem inTOmegaT_toFA_T {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) {X : ℝ → V}
    (hX : X ∈ Morse.pathTangent hN (Bridge.incl hN ∘ γ))
    (hXτ : ∀ t, t ∉ Icc (0 : ℝ) τ → X t = 0) :
    InTOmegaT (n := n) τ γ (toFA γ X) := by
  obtain ⟨⟨-, -, B, hB⟩, hT, hX0, -⟩ := (Morse.mem_pathTangent hN).1 hX
  have hmem : (⟨X, hX⟩ : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) ∈
      Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ := hXτ
  have hXτ0 : X τ = 0 := Morse.fieldsUpTo_apply_self hτ.le hτ1 hmem
  obtain ⟨k, t, ht0, htk, hlt, hgood⟩ := exists_subdivT hτ B
  have hsm : ∀ i < k, IsSmoothAlong γ (Icc (t i) (t (i + 1))) (toFA γ X) := by
    intro i hi
    obtain ⟨h0i, hi1, hBi⟩ := hgood i hi
    have hsub : Icc (t i) (t (i + 1)) ⊆ Icc 0 1 := Icc_subset_Icc h0i (hi1.trans hτ1)
    exact Bridge.isSmoothAlong_iff.2 ⟨ContMDiffOn.mono hγ hsub,
      (hB _ _ h0i (hlt i hi) (hi1.trans hτ1) hBi).congr fun s hs => ambA_toFA hT (hsub hs)⟩
  refine ⟨⟨k, t, ht0, htk, hlt, ?_, hsm⟩, ?_, ?_, fun s hs => ?_⟩
  · rw [← htk]
    exact continuousOn_of_pieces ht0 hlt fun i hi => ContMDiffOn.continuousOn (hsm i hi)
  · rw [toFA_of_mem X ⟨le_rfl, zero_le_one⟩, hX0, map_zero]; rfl
  · rw [toFA_of_mem X ⟨hτ.le, hτ1⟩, hXτ0, map_zero]; rfl
  · by_cases hs1 : s ∈ Icc (0 : ℝ) 1
    · rw [toFA_of_mem X hs1, hXτ s hs, map_zero]; rfl
    · exact toFA_of_not_mem X hs1

/-! #### Variations of `γ|[0, τ]` -/

/-- The extension of a blind variation of `γ|[0, τ]` by `α 0` on `(τ, 1]`, read in `V`. -/
noncomputable def extA {m : ℕ} (τ : ℝ) (α : Rn m → ℝ → Bridge.Sub hN) : Rn m → ℝ → V :=
  fun u s => if s ≤ τ then Bridge.incl hN (α u s) else Bridge.incl hN (α 0 s)

theorem extA_zero {m : ℕ} (τ : ℝ) (α : Rn m → ℝ → Bridge.Sub hN) (s : ℝ) :
    extA τ α 0 s = Bridge.incl hN (α 0 s) := by
  unfold extA; split_ifs <;> rfl

/-- **The extension is a project variation** of `incl ∘ α 0` on `[0, 1]`. -/
theorem isVariation_extA {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (hγ : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ α 0) (Icc 0 1)) :
    Morse.IsVariation N U (extA τ α) (insert τ ((Finset.range (k + 1)).image t)) := by
  obtain ⟨hU, h0U, ht0, htk, hlt, hend, hsm⟩ := hα
  refine ⟨hU, h0U, fun u _ s _ => ?_, fun u hu => ?_, fun u hu => ?_,
    fun s u hs hsu hu hB => ?_⟩
  · unfold extA
    split_ifs
    · exact (α u s).2
    · exact (α 0 s).2
  · rw [extA_zero]
    unfold extA
    rw [if_pos hτ.le, (hend u hu).2.1]
  · rw [extA_zero]
    unfold extA
    split_ifs with h1
    · have : τ = 1 := le_antisymm hτ1 h1
      subst this
      rw [(hend u hu).2.2]
    · rfl
  · by_cases huτ : u ≤ τ
    · obtain ⟨i, hi, hti, hui⟩ := exists_piece_of_subdivT ht0 htk hlt hs hsu huτ
        fun x hx => hB x (Finset.mem_insert_of_mem hx)
      refine ((contMDiffOn_map_iff.1 (hsm i hi)).mono
        (prod_mono subset_rfl (Icc_subset_Icc hti hui))).congr fun p hp => ?_
      show extA τ α p.1 p.2 = Bridge.incl hN (α p.1 p.2)
      unfold extA
      rw [if_pos (hp.2.2.trans huτ)]
    · have hτs : τ ≤ s := by
        by_contra h
        exact hB τ (Finset.mem_insert_self _ _) ⟨lt_of_not_ge h, lt_of_not_ge huτ⟩
      have hg : ContDiffOn ℝ ∞ ((Bridge.incl hN ∘ α 0) ∘ Prod.snd) (U ×ˢ Icc s u) :=
        hγ.comp contDiff_snd.contDiffOn fun p hp => ⟨hs.trans hp.2.1, hp.2.2.trans hu⟩
      refine hg.congr fun p hp => ?_
      show extA τ α p.1 p.2 = Bridge.incl hN (α 0 p.2)
      unfold extA
      split_ifs with h
      · have hpτ : p.2 = τ := le_antisymm h (hτs.trans hp.2.1)
        rw [hpτ, (hend p.1 hp.1).2.2]
      · rfl

/-- `E_0^1` of the extension is `E_0^τ` of the blind path plus the constant `E_τ^1(γ)`. -/
theorem energy_extA {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {B : Finset ℝ}
    (hvar : Morse.IsVariation N U (extA τ α) B) {v : Rn m} (hv : v ∈ U) :
    Morse.energy (extA τ α v) 0 1 =
      Morse.energy (Bridge.incl hN ∘ α v) 0 τ + Morse.energy (Bridge.incl hN ∘ α 0) τ 1 := by
  have hint := (hvar.isPiecewiseSmooth hv).intervalIntegrable_norm_deriv_sq
  have h1 : IntervalIntegrable (fun s => ‖deriv (extA τ α v) s‖ ^ 2) MeasureTheory.volume 0 τ :=
    hint.mono_set (by
      rw [uIcc_of_le hτ.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hτ1)
  have h2 : IntervalIntegrable (fun s => ‖deriv (extA τ α v) s‖ ^ 2) MeasureTheory.volume τ 1 :=
    hint.mono_set (by
      rw [uIcc_of_le hτ1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hτ.le le_rfl)
  unfold Morse.energy
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  congr 1
  · refine intervalIntegral.integral_congr_Ioo_of_le hτ.le fun s hs => ?_
    have : extA τ α v =ᶠ[𝓝 s] Bridge.incl hN ∘ α v := by
      filter_upwards [Iio_mem_nhds hs.2] with x hx
      unfold extA
      rw [if_pos (le_of_lt hx)]
      rfl
    simp only [this.deriv_eq]
  · refine intervalIntegral.integral_congr_Ioo_of_le hτ1 fun s hs => ?_
    have : extA τ α v =ᶠ[𝓝 s] Bridge.incl hN ∘ α 0 := by
      filter_upwards [Ioi_mem_nhds hs.1] with x hx
      unfold extA
      rw [if_neg (not_le.2 hx)]
      rfl
    simp only [this.deriv_eq]

/-- Variation fields of a blind variation of `γ|[0, τ]`, read in `V`, on `[0, τ]`. -/
theorem D_varFieldT {τ : ℝ} (hτ : 0 < τ) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (i : Fin m) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) τ) :
    Bridge.D hN (α 0 s) (varField (n := n) α i s) =
      deriv (fun r : ℝ => amb α (r • EuclideanSpace.single i (1 : ℝ)) s) 0 := by
  obtain ⟨hU, h0U, ht0, htk, hlt, -, hsm⟩ := hα
  obtain ⟨j, hj, hsj⟩ := exists_piece_of_memT hτ ht0 htk hlt hs
  have hG : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ fun x : Rn m × ℝ => α x.1 x.2)
      (U ×ˢ Icc (t j) (t (j + 1))) := contMDiffOn_map_iff.1 (hsm j hj)
  have hcd : ContDiffAt ℝ ∞ (Bridge.incl hN ∘ fun u => α u s) 0 :=
    (hG.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun u hu => ⟨hu, hsj⟩).contDiffAt
      (hU.mem_nhds h0U)
  have h1 := D_mfderiv_of_contDiffAt hcd (EuclideanSpace.single i (1 : ℝ))
  have h2 := RoundTrip.EnergyC2.hasDerivAt_line (hcd.differentiableAt (by simp))
    (EuclideanSpace.single i (1 : ℝ))
  simp only [zero_add] at h2
  exact h1.trans h2.deriv.symm

/-- The variation fields of the extension: the blind ones on `[0, τ]`, `0` beyond. -/
theorem deriv_extA {τ : ℝ} (hτ : 0 < τ) {m : ℕ} {U : Set (Rn m)}
    {α : Rn m → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (i : Fin m) {s : ℝ} (hs : 0 ≤ s) :
    deriv (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) 0 =
      if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α i) s else 0 := by
  split_ifs with h
  · have e : (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) =
        fun r : ℝ => amb α (r • EuclideanSpace.single i (1 : ℝ)) s := funext fun r => by
      unfold extA
      rw [if_pos h]
      rfl
    rw [e, ← D_varFieldT hτ hα i ⟨hs, h⟩]
    rfl
  · have e : (fun r : ℝ => extA τ α (r • EuclideanSpace.single i (1 : ℝ)) s) =
        fun _ : ℝ => Bridge.incl hN (α 0 s) := funext fun r => by
      unfold extA
      rw [if_neg h]
    rw [e, deriv_const]

/-- **`E_0^τ ∘ α` is `C²` and its blind `mixedD` is `2 secondVariation`** of the fields
(extended by `0` beyond `τ`), for every blind variation of `γ|[0, τ]`, `γ` a geodesic of `↥N`. -/
theorem hessT_data {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {U : Set (Rn 2)}
    {α : Rn 2 → ℝ → Bridge.Sub hN} {k : ℕ} {t : ℕ → ℝ} (hα : IsVarSubT (n := n) τ U α k t)
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) (α 0) (Icc 0 1)) :
    DifferentiableAt ℝ
        (fun u : Rn 2 => fderiv ℝ (fun v : Rn 2 => energy (n := n) (α v) 0 τ) u e0) 0 ∧
      mixedD (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =
        2 * Morse.secondVariation hN (Bridge.incl hN ∘ α 0)
          (fun s => if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α 0) s else 0)
          (fun s => if s ≤ τ then Bridge.ambA (α 0) (varField (n := n) α 1) s else 0) := by
  have hub := isUnbrokenGeodesic_of_isGeodesic hgeo
  have hvar := isVariation_extA hτ hτ1 hα hub.1
  have hU := hvar.isOpen
  have h0U := hvar.zero_mem
  have hFG : ∀ v ∈ U, energy (n := n) (α v) 0 τ =
      Morse.energy (extA τ α v) 0 1 - Morse.energy (Bridge.incl hN ∘ α 0) τ 1 := by
    intro v hv
    have h1 : energy (n := n) (α v) 0 τ = Morse.energy (Bridge.incl hN ∘ α v) 0 τ :=
      Bridge.energy_eq (α v) 0 τ
    rw [h1, energy_extA hτ hτ1 hvar hv]
    ring
  have hG : ContDiffOn ℝ 2 (fun v => Morse.energy (extA τ α v) 0 1) U :=
    hvar.contDiffOn_energy.of_le ENat.LEInfty.out
  have hF : ContDiffOn ℝ 2 (fun v : Rn 2 => energy (n := n) (α v) 0 τ) U :=
    (hG.sub contDiffOn_const).congr hFG
  have hev : (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =ᶠ[𝓝 0]
      fun v => Morse.energy (extA τ α v) 0 1 - Morse.energy (Bridge.incl hN ∘ α 0) τ 1 :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds h0U) hFG
  have hD : (fun u => fderiv ℝ (fun v : Rn 2 => energy (n := n) (α v) 0 τ) u e0) =ᶠ[𝓝 0]
      fun u => fderiv ℝ (fun v => Morse.energy (extA τ α v) 0 1) u e0 := by
    filter_upwards [hev.fderiv (𝕜 := ℝ)] with u hu
    rw [hu, fderiv_sub_const]
  refine ⟨RoundTrip.EnergyC2.differentiableAt_fderiv_apply hU hF h0U e0, ?_⟩
  have hmix : mixedD (fun v : Rn 2 => energy (n := n) (α v) 0 τ) =
      fderiv ℝ (fun u => fderiv ℝ (fun v => Morse.energy (extA τ α v) 0 1) u e0) 0 e1 := by
    unfold mixedD
    rw [hD.fderiv_eq]
  have h := RoundTrip.EnergyC2.fderiv_fderiv_apply_eq_deriv_deriv hU hG h0U e0 e1
  simp only [zero_add] at h
  rw [hmix, h]
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  have hφ0 : (fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1) 0 ∈ U := by
    simpa using h0U
  have hvar2 := hvar.comp hφ hφ0
  have hαγ : ∀ s ∈ Icc (0 : ℝ) 1,
      (fun p : ℝ × ℝ => extA τ α (p.1 • e0 + p.2 • e1)) 0 s = (Bridge.incl hN ∘ α 0) s := by
    intro s _
    simp only [Prod.fst_zero, Prod.snd_zero, zero_smul, add_zero]
    exact extA_zero τ α s
  have hd := sv_holds (mem_pathSpace_of_isGeodesic hgeo) hub hvar2 hαγ
  simp only [zero_smul, add_zero, zero_add] at hd
  rw [hd.deriv]
  congr 1
  refine Morse.secondVariation_congr hN (fun s hs => ?_) (fun s hs => ?_)
  · exact deriv_extA hτ hα 0 hs.1
  · exact deriv_extA hτ hα 1 hs.1

/-- **Every `IsHessT τ` value is `2 secondVariation`** of the ambient fields, for blind fields in
`TΩ(γ|[0,τ])` (`0` beyond `τ`). -/
theorem hessT_eqT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) {r : ℝ}
    (h : IsHessT (n := n) τ γ W₁ W₂ r) :
    r = 2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  obtain ⟨U, α, k, t, hα, rfl, hW₁, hW₂, -, hr⟩ := h
  rw [← hr, (hessT_data hτ hτ1 hα hgeo).2]
  congr 1
  refine Morse.secondVariation_congr hN (fun s _ => ?_) (fun s _ => ?_)
  · split_ifs with hs
    · show Bridge.D hN (α 0 s) (varField (n := n) α 0 s) = Bridge.D hN (α 0 s) (W₁ s)
      rw [eq_of_heq (hW₁ s)]
    · show (0 : V) = Bridge.D hN (α 0 s) (W₁ s)
      rw [h₁.2.2.2 s fun h' => hs h'.2]
      exact (map_zero _).symm
  · split_ifs with hs
    · show Bridge.D hN (α 0 s) (varField (n := n) α 1 s) = Bridge.D hN (α 0 s) (W₂ s)
      rw [eq_of_heq (hW₂ s)]
    · show (0 : V) = Bridge.D hN (α 0 s) (W₂ s)
      rw [h₂.2.2.2 s fun h' => hs h'.2]
      exact (map_zero _).symm

/-- **Existence of `E_**(W₁, W₂)` for `E_0^τ` on `↥N`** (Lemma 11.A on `[0, 1]`, restricted to a
subdivision of `[0, τ]`; fields matched on all of `ℝ`). -/
theorem exists_isHessT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) :
    ∃ r, IsHessT (n := n) τ γ W₁ W₂ r := by
  have hc := mem_pathSpace_of_isGeodesic hgeo
  obtain ⟨hXs₁, -, hX0₁, hX1₁⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmegaT hτ1 h₁).1
  obtain ⟨hXs₂, -, hX0₂, hX1₂⟩ := (Morse.mem_pathTangent hN).1 (mem_pathTangent_of_inTOmegaT hτ1 h₂).1
  set X₁ := Bridge.ambA γ W₁
  set X₂ := Bridge.ambA γ W₂
  have hXτ₁ : X₁ τ = 0 := by
    show Bridge.D hN (γ τ) (W₁ τ) = 0
    rw [h₁.2.2.1]; exact map_zero _
  have hXτ₂ : X₂ τ = 0 := by
    show Bridge.D hN (γ τ) (W₂ τ) = 0
    rw [h₂.2.2.1]; exact map_zero _
  set Λ : ℝ → Rn 2 →L[ℝ] V := fun t =>
    (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₁ t) +
      (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ).smulRight (X₂ t) with hΛdef
  have hΛapp : ∀ t u, Λ t u = u 0 • X₁ t + u 1 • X₂ t := fun t u => by
    simp [hΛdef]
  have hΛT : ∀ t u, Morse.prj hN (Bridge.incl hN (γ t)) (Λ t u) = Λ t u := fun t u =>
    (Morse.prj_eq_self_iff hN (γ t).2).2 (by
      rw [hΛapp]
      exact add_mem (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₁ t)))
        (Submodule.smul_mem _ _ (Bridge.D_mem (γ t) (W₂ t))))
  have hΛs : Morse.IsPiecewiseSmooth Λ 0 1 :=
    (hXs₁.smulRight (EuclideanSpace.proj (0 : Fin 2) : Rn 2 →L[ℝ] ℝ)).add
      (hXs₂.smulRight (EuclideanSpace.proj (1 : Fin 2) : Rn 2 →L[ℝ] ℝ))
  have hΛ0 : Λ 0 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX0₁, hX0₂]
  have hΛ1 : Λ 1 = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hX1₁, hX1₂]
  have hΛτ : Λ τ = 0 := ContinuousLinearMap.ext fun u => by
    rw [hΛapp]; simp [hXτ₁, hXτ₂]
  obtain ⟨ε, hε, B, hα, -, -⟩ := Morse.exists_variation hN hc (P := Rn 2) hΛs
    (fun t _ u => hΛT t u) hΛ0 hΛ1
  set α := liftE γ Λ
  have hinc : ∀ u ∈ Metric.ball (0 : Rn 2) ε, ∀ t ∈ Icc (0 : ℝ) 1,
      Bridge.incl hN (α u t) = Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) :=
    fun u hu t ht => incl_liftE (hα.mem u hu t ht)
  have hinj : Function.Injective (Bridge.incl hN) := Subtype.val_injective
  have hα0 : α 0 = γ := funext fun t => by
    have e : Morse.exp hN (Bridge.incl hN (γ t)) (Λ t 0) = Bridge.incl hN (γ t) := by
      rw [map_zero]; exact Morse.exp_zero (γ t).2
    exact hinj ((incl_liftE (γ := γ) (Λ := Λ) (u := 0) (t := t) (by rw [e]; exact (γ t).2)).trans e)
  obtain ⟨k, tt, ht0, htk, hlt, hgood⟩ := exists_subdivT hτ B
  have hstrip : ∀ i < k, ContMDiffOn 𝓘(ℝ, Rn 2 × ℝ) 𝓘(ℝ, Rn n) ∞
      (fun x : Rn 2 × ℝ => α x.1 x.2) (Metric.ball (0 : Rn 2) ε ×ˢ Icc (tt i) (tt (i + 1))) := by
    intro i hi
    obtain ⟨hi0, hi1, hiB⟩ := hgood i hi
    refine contMDiffOn_map_iff.2
      ((hα.smooth _ _ hi0 (hlt i hi) (hi1.trans hτ1) hiB).congr fun p hp => ?_)
    exact hinc p.1 hp.1 p.2 ⟨hi0.trans hp.2.1, hp.2.2.trans (hi1.trans hτ1)⟩
  have hvs : IsVarSubT (n := n) τ (Metric.ball (0 : Rn 2) ε) α k tt := by
    refine ⟨Metric.isOpen_ball, Metric.mem_ball_self hε, ht0, htk, hlt, fun u hu => ⟨?_, ?_, ?_⟩,
      hstrip⟩
    · refine ⟨k, tt, ht0, htk, hlt, fun i hi => ?_⟩
      have hι : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn 2 × ℝ) ∞ (fun s : ℝ => (u, s)) :=
        contMDiff_iff_contDiff.2 (contDiff_const.prodMk contDiff_id)
      exact (hstrip i hi).comp hι.contMDiffOn fun s hs => ⟨hu, hs⟩
    · refine hinj ?_
      rw [hinc u hu 0 ⟨le_rfl, zero_le_one⟩, hinc 0 (Metric.mem_ball_self hε) 0 ⟨le_rfl, zero_le_one⟩,
        hΛ0]
      rfl
    · refine hinj ?_
      rw [hinc u hu τ ⟨hτ.le, hτ1⟩, hinc 0 (Metric.mem_ball_self hε) τ ⟨hτ.le, hτ1⟩, hΛτ]
      rfl
  have hfield : ∀ (i : Fin 2) (t : ℝ),
      Bridge.D hN (γ t) (varField (n := n) α i t) = Λ t (EuclideanSpace.single i (1 : ℝ)) := by
    intro i t
    obtain ⟨hmem, hcd, hfd⟩ := exp_local (hN := hN) (γ t).2 (Λ t) (hΛT t)
    have hev : (Bridge.incl hN ∘ fun u => α u t) =ᶠ[𝓝 0]
        fun u => Morse.exp hN (Bridge.incl hN (γ t)) (Λ t u) := by
      filter_upwards [hmem] with u hu
      exact incl_liftE hu
    have h1 := D_mfderiv_of_contDiffAt (hcd.congr_of_eventuallyEq hev)
      (EuclideanSpace.single i (1 : ℝ))
    have h2 := (hfd.congr_of_eventuallyEq hev).fderiv
    rw [h2] at h1
    calc Bridge.D hN (γ t) (varField (n := n) α i t)
        = Bridge.D hN (α 0 t) (varField (n := n) α i t) := by rw [congrFun hα0 t]
      _ = _ := h1
  have hW : ∀ (i : Fin 2) (Wi : FA n γ), (∀ t, Λ t (EuclideanSpace.single i (1 : ℝ)) =
      Bridge.D hN (γ t) (Wi t)) → ∀ t, HEq (Wi t) (varField (n := n) α i t) := by
    intro i Wi hWi t
    have := Bridge.D_injective (γ t) ((hfield i t).trans (hWi t))
    exact heq_of_eq this.symm
  have hgeo' : IsGeodesic (Bridge.conn (hN := hN)) (α 0) (Icc 0 1) := by rw [hα0]; exact hgeo
  refine ⟨_, Metric.ball (0 : Rn 2) ε, α, k, tt, hvs, hα0,
    hW 0 W₁ fun t => by rw [hΛapp]; simp [X₁, Bridge.ambA],
    hW 1 W₂ fun t => by rw [hΛapp]; simp [X₂, Bridge.ambA], (hessT_data hτ hτ1 hvs hgeo').1, rfl⟩

theorem isHessT_iffT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) {r : ℝ} :
    IsHessT (n := n) τ γ W₁ W₂ r ↔
      r = 2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  refine ⟨hessT_eqT hτ hτ1 hgeo h₁ h₂, fun h => ?_⟩
  obtain ⟨r', hr'⟩ := exists_isHessT hτ hτ1 hgeo h₁ h₂
  rw [h, ← hessT_eqT hτ hτ1 hgeo h₁ h₂ hr']
  exact hr'

/-- **The choice function `HessT τ γ` is `2 secondVariation`** on `TΩ(γ|[0,τ])`. -/
theorem hessT_eq_T {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1)) {W₁ W₂ : FA n γ}
    (h₁ : InTOmegaT (n := n) τ γ W₁) (h₂ : InTOmegaT (n := n) τ γ W₂) :
    HessT (n := n) τ γ W₁ W₂ =
      2 * Morse.secondVariation hN (Bridge.incl hN ∘ γ) (Bridge.ambA γ W₁) (Bridge.ambA γ W₂) := by
  have hex := exists_isHessT hτ hτ1 hgeo h₁ h₂
  unfold HessT
  rw [dif_pos hex]
  exact hessT_eqT hτ hτ1 hgeo h₁ h₂ hex.choose_spec


section LinAlgT

variable {E M : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup M] [Module ℝ M]

theorem bIndex_eq_formIndex_of {T : Set E} {H : E → E → ℝ} (B : LinearMap.BilinForm ℝ M)
    (φ : M →ₗ[ℝ] E) (hφ : Injective φ) (hT : Set.range φ = T)
    (hH : ∀ x y, H (φ x) (φ y) = B x y) : bIndex T H = Morse.formIndex B := by
  apply le_antisymm
  · unfold bIndex
    refine iSup₂_le fun S ⟨hST, hfd, hneg⟩ => ?_
    have hSR : S ≤ LinearMap.range φ := fun v hv => by
      have := hST hv
      rw [← hT] at this
      exact this
    have hmap : (S.comap φ).map φ = S := Submodule.map_comap_eq_of_le hSR
    let e : S.comap φ ≃ₗ[ℝ] S :=
      (Submodule.equivMapOfInjective φ hφ (S.comap φ)).trans (LinearEquiv.ofEq _ _ hmap)
    haveI : FiniteDimensional ℝ (S.comap φ) := LinearEquiv.finiteDimensional e.symm
    have hneg' : Morse.IsNegDefOn B (S.comap φ) := fun x hx hx0 => by
      rw [← hH]
      exact hneg (φ x) hx fun h => hx0 (hφ (h.trans (map_zero φ).symm))
    calc (Module.finrank ℝ S : ℕ∞) = Module.finrank ℝ (S.comap φ) := by rw [e.finrank_eq]
      _ ≤ Morse.formIndex B := Morse.le_formIndex hneg'
  · refine Morse.formIndex_le fun S' hfd hneg => ?_
    let e : S' ≃ₗ[ℝ] S'.map φ := Submodule.equivMapOfInjective φ hφ S'
    haveI : FiniteDimensional ℝ (S'.map φ) := LinearEquiv.finiteDimensional e
    have hST : ((S'.map φ : Submodule ℝ E) : Set E) ⊆ T := by
      rintro _ ⟨x, -, rfl⟩
      rw [← hT]
      exact ⟨x, rfl⟩
    have hneg' : IsNegDefSub H (S'.map φ) := by
      rintro _ ⟨x, hx, rfl⟩ hx0
      rw [hH]
      exact hneg x hx fun h => hx0 (by rw [h, map_zero])
    calc (Module.finrank ℝ S' : ℕ∞) = Module.finrank ℝ (S'.map φ) := by rw [e.finrank_eq]
      _ ≤ bIndex T H := by
        unfold bIndex
        exact le_iSup₂_of_le (f := fun (S : Submodule ℝ E)
          (_ : (S : Set E) ⊆ T ∧ FiniteDimensional ℝ S ∧ IsNegDefSub H S) =>
            (Module.finrank ℝ S : ℕ∞)) (S'.map φ) ⟨hST, inferInstance, hneg'⟩ le_rfl


end LinAlgT

/-- The dictionary map `fieldsUpTo τ → FA n γ`, `X ↦ toFA γ X`. -/
noncomputable def φT (γ : ℝ → Bridge.Sub hN) (τ : ℝ) :
    Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ →ₗ[ℝ] FA n γ :=
  (toFAₗ γ).comp ((Morse.pathTangent hN (Bridge.incl hN ∘ γ)).subtype.comp
    (Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ).subtype)

theorem φT_apply (γ : ℝ → Bridge.Sub hN) (τ : ℝ) (x : Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ) :
    φT (n := n) γ τ x = toFA γ ((x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) := rfl

theorem φT_injective {τ : ℝ} (hτ1 : τ ≤ 1) (γ : ℝ → Bridge.Sub hN) :
    Injective (φT (n := n) γ τ) := by
  intro x y h
  have hx := ((Morse.mem_pathTangent hN).1 (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have hy := ((Morse.mem_pathTangent hN).1 (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have h' := toFA_injOn hx hy h
  have hx0 : ∀ t, t ∉ Icc (0 : ℝ) τ →
      ((x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) t = 0 := x.2
  have hy0 : ∀ t, t ∉ Icc (0 : ℝ) τ →
      ((y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)) : ℝ → V) t = 0 := y.2
  refine Subtype.ext (Subtype.ext (funext fun t => ?_))
  by_cases ht : t ∈ Icc (0 : ℝ) τ
  · exact h' ⟨ht.1, ht.2.trans hτ1⟩
  · rw [hx0 t ht, hy0 t ht]

theorem range_φT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hγ : IsSmoothCurve (n := n) γ (Icc 0 1)) :
    Set.range (φT (n := n) γ τ) = TOm (n := n) τ γ := by
  ext Wf
  constructor
  · rintro ⟨x, rfl⟩
    exact inTOmegaT_toFA_T hτ hτ1 hγ (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 x.2
  · intro hW
    have hW' : InTOmegaT (n := n) τ γ Wf := hW
    obtain ⟨hm, hout⟩ := mem_pathTangent_of_inTOmegaT hτ1 hW'
    refine ⟨⟨⟨_, hm⟩, hout⟩, funext fun t => ?_⟩
    rw [φT_apply]
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · rw [toFA_of_mem _ ht]
      exact Bridge.L_D (γ t) (Wf t)
    · rw [toFA_of_not_mem _ ht, hW'.2.2.2 t fun h => ht ⟨h.1, h.2.trans hτ1⟩]

/-- **`HessT τ` pulled back by `toFA` is `energyHessian` on `fieldsUpTo τ`.** -/
theorem hessT_φT {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1))
    (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ))
    (x y : Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ) :
    HessT (n := n) τ γ (φT γ τ x) (φT γ τ y) =
      ((Morse.energyHessian hN hc.mem_pathSpace).restrict
        (Morse.fieldsUpTo hN (Bridge.incl hN ∘ γ) τ)) x y := by
  have hγs : IsSmoothCurve (n := n) γ (Icc 0 1) := hgeo.2.1
  have hx := inTOmegaT_toFA_T hτ hτ1 hγs (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 x.2
  have hy := inTOmegaT_toFA_T hτ hτ1 hγs (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2 y.2
  have hxT := ((Morse.mem_pathTangent hN).1 (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  have hyT := ((Morse.mem_pathTangent hN).1 (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ)).2).2.1
  rw [φT_apply, φT_apply, hessT_eq_T hτ hτ1 hgeo hx hy]
  show _ = Morse.energyHessian hN hc.mem_pathSpace (x : Morse.pathTangent hN (Bridge.incl hN ∘ γ))
    (y : Morse.pathTangent hN (Bridge.incl hN ∘ γ))
  rw [Morse.energyHessian_apply]
  congr 1
  exact Morse.secondVariation_congr hN (fun t ht => ambA_toFA hxT ht) (fun t ht => ambA_toFA hyT ht)

/-- **`λ(τ)` of B is the project's `indexUpTo τ`** on `↥N` (for a geodesic, `0 < τ ≤ 1`). -/
theorem lam_eq_indexUpTo {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {γ : ℝ → Bridge.Sub hN}
    (hgeo : IsGeodesic (Bridge.conn (hN := hN)) γ (Icc 0 1))
    (hc : Morse.IsSmoothCurveIn hN (Bridge.incl hN ∘ γ)) :
    lam (n := n) τ γ = Morse.indexUpTo hN (Bridge.incl hN ∘ γ) hc τ := by
  unfold lam Morse.indexUpTo
  exact bIndex_eq_formIndex_of _ (φT γ τ) (φT_injective hτ1 γ) (range_φT hτ hτ1 hgeo.2.1)
    (hessT_φT hτ hτ1 hgeo hc)

end LamPf

/-! ## Third attempt: the index dictionary `LamEq` is a theorem

`LamPf` above is a copy of the proof of `Emb.lamEq` of `Items/V9_23.lean` (Lemma 11.A and Theorem 13.1 =
`Morse.second_variation` for `E_0^τ` on `↥N`, `EnergyC2`'s `C²` regularity of `u ↦ E(α(u))`, the
`TΩ(γ|[0,τ])` dictionary `toFA`/`φT`, index transport `bIndex_eq_formIndex_of`, then `Morse.indexUpTo_one`),
applied to `SU(n)` re-modelled on `ℝᵈ`; `ModelRn` below moves the index back to the project's model. -/

/-! ### Changing the model of a slice submanifold does not change `E_**` or its index

`LamPf` gives B's `lam 1 γ` as the index of `energyHessian (hR n)`, for the re-modelled slice structure
`hR n = Emb.isSliceRn isSliceSubmanifold_specialUnitaryGroup` (model `ℝᵈ`, needed by the Bridge), while A
speaks of `energyHessian isSliceSubmanifold_specialUnitaryGroup` (model `𝔰𝔲(n)`). Both have the same tangent
spaces (`Emb.tangentSubspace_rn`), hence the same projections, covariant derivatives, `TΩ` and (through
`Morse.dN_eq_fderiv`, `dN` of `P` on tangent vectors being chart-free) the same curvature on tangent vectors;
so the two second variations agree along a smooth curve and the two forms have the same index. -/

namespace ModelRn

open Emb

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {N : Set V}
  (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N)

theorem tanProj_rn (q : N) : Morse.tanProj (isSliceRn hN) q = Morse.tanProj hN q := by
  unfold Morse.tanProj
  congr 1
  exact tangentSubspace_rn hN q

theorem prj_rn : Morse.prj (isSliceRn hN) = Morse.prj hN := by
  funext x
  unfold Morse.prj
  split_ifs with h
  · exact tanProj_rn hN ⟨x, h⟩
  · rfl

theorem pathTangent_rn (c : ℝ → V) :
    Morse.pathTangent (isSliceRn hN) c = Morse.pathTangent hN c := by
  ext X
  rw [Morse.mem_pathTangent, Morse.mem_pathTangent, prj_rn hN]

theorem covD_rn : Morse.covD (isSliceRn hN) = Morse.covD hN := by
  funext c X t
  unfold Morse.covD
  rw [prj_rn hN]

theorem dN_tanProj_rn (q : N) {v : V} (hv : v ∈ Morse.tangentSubspace hN q) :
    Morse.dN (isSliceRn hN) (Morse.tanProj (isSliceRn hN)) q v =
      Morse.dN hN (Morse.tanProj hN) q v := by
  have hq := Morse.mem_sliceAt_source hN q
  rw [Morse.dN_tanProj_eq_fderiv hN (Morse.sliceAt hN q) hq hv]
  refine Morse.dN_eq_fderiv (isSliceRn hN)
    ((Morse.contDiffAt_projRep (Morse.sliceAt hN q) hq).differentiableAt (by simp)) ?_
    ((tangentSubspace_rn hN q).symm ▸ hv)
  filter_upwards [(Morse.sliceAt hN q).toChart.open_source.mem_nhds hq] with x hx
  rw [tanProj_rn hN]
  exact (Morse.projRep_eq hN _ hx).symm

theorem curvOp_rn (q : N) {a b : V} (ha : a ∈ Morse.tangentSubspace hN q)
    (hb : b ∈ Morse.tangentSubspace hN q) :
    Morse.curvOp (isSliceRn hN) q a b = Morse.curvOp hN q a b := by
  unfold Morse.curvOp
  rw [dN_tanProj_rn hN q ha, dN_tanProj_rn hN q hb]

theorem curvR_rn {x a b : V} (hx : x ∈ N) (ha : a ∈ Morse.tangentSubspace hN ⟨x, hx⟩)
    (hb : b ∈ Morse.tangentSubspace hN ⟨x, hx⟩) (c : V) :
    Morse.curvR (isSliceRn hN) x a b c = Morse.curvR hN x a b c := by
  rw [Morse.curvR_of_mem _ hx, Morse.curvR_of_mem _ hx, curvOp_rn hN _ ha hb]

theorem secondVariation_rn {γ X₁ X₂ : ℝ → V} (hc : Morse.IsSmoothCurveIn hN γ)
    (hX : ∀ t ∈ Icc (0 : ℝ) 1, Morse.prj hN (γ t) (X₁ t) = X₁ t) :
    Morse.secondVariation (isSliceRn hN) γ X₁ X₂ = Morse.secondVariation hN γ X₁ X₂ := by
  unfold Morse.secondVariation
  rw [prj_rn hN, covD_rn hN]
  congr 1
  refine intervalIntegral.integral_congr_Ioo_of_le zero_le_one fun t ht => ?_
  have ht' := Ioo_subset_Icc_self ht
  have hmem := hc.mem t ht'
  have hv : deriv γ t ∈ Morse.tangentSubspace hN ⟨γ t, hmem⟩ := by
    have h := hc.velAlong_mem ht'
    rw [hc.velAlong_eq ht] at h
    exact (Morse.prj_eq_self_iff hN hmem).1 h
  rw [curvR_rn hN hmem hv ((Morse.prj_eq_self_iff hN hmem).1 (hX t ht'))]

/-- **The index of `E_**` does not depend on the model of the slice structure.** -/
theorem formIndex_energyHessian_rn {γ : ℝ → V} {p q : V} (h : γ ∈ Morse.pathSpace N p q)
    (hc : Morse.IsSmoothCurveIn hN γ) :
    Morse.formIndex (Morse.energyHessian (isSliceRn hN) h) =
      Morse.formIndex (Morse.energyHessian hN h) := by
  refine Morse.formIndex_eq_of_equiv (LinearEquiv.ofEq _ _ (pathTangent_rn hN γ)) fun X Y => ?_
  rw [Morse.energyHessian_apply, Morse.energyHessian_apply]
  have hX := ((Morse.mem_pathTangent hN).1
    (LinearEquiv.ofEq _ _ (pathTangent_rn hN γ) X).2).2.1
  exact congrArg (2 * ·) (secondVariation_rn hN hc hX).symm

end ModelRn

open Emb in
/-- **`LamEq` holds** (`LamPf` + `ModelRn.formIndex_energyHessian_rn`). -/
theorem lamEq_holds : LamEq := by
  intro n _ γ hγ hgeo
  have hcs := LamPf.isSmoothCurveIn (hgeo.2.1 : IsSmoothCurve (n := dd n) γ (Icc 0 1))
  rw [LamPf.lam_eq_indexUpTo one_pos le_rfl hgeo hcs, Morse.indexUpTo_one,
    show Morse.formIndex (Morse.energyHessian (hR n) hcs.mem_pathSpace) =
      Morse.formIndex (Morse.energyHessian (hR n) hγ) by congr 1]
  exact ModelRn.formIndex_energyHessian_rn _ hγ ⟨hcs.contDiffOn, hcs.mem⟩

/-- **`A ⇒ B_emb`** (unconditional; `ConnectedSpace (SU n)` stays a hypothesis of `B_emb`). -/
theorem A_to_B_emb : A → B_emb := fun hA => A_to_B_emb_of_lamEq hA lamEq_holds

#rt_check RoundTrip.V14_20.lamEq_holds [Morse.lemma_23_2_index, Morse.energy_exp_smul, Morse.le_formIndex_of_not_minimal_su]
#rt_check RoundTrip.V14_20.A_to_B_emb [Morse.lemma_23_2_index, Morse.energy_exp_smul, Morse.le_formIndex_of_not_minimal_su]
#rt_overlap RoundTrip.V14_20.A_to_B_emb [Morse.lemma_23_2_index, Morse.energy_exp_smul, Morse.le_formIndex_of_not_minimal_su]

end RoundTrip.V14_20
