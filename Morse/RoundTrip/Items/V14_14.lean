import Morse
import RoundTrip.Check
import RoundTrip.Bridge
import RoundTrip.Blind.V14_14

open Matrix Set Filter Topology Module
open scoped ContDiff Manifold

noncomputable section

set_option linter.unusedSectionVars false

namespace RoundTrip.V14_14

/-- The project's statement (universes of `ι` instantiated at `0`): every unbroken geodesic of
`SU(n)` (slice submanifold of `Mₙ(ℂ)`, induced metric) from `I` is `t ↦ exp tA` on `[0,1]` with
`A ∈ 𝔰𝔲(n)`; every `A ∈ 𝔰𝔲(n)` with `exp A = −I` is `T suDiag(k) Tᴴ` with `T` unitary, `k_j` odd,
`Σ k_j = 0`; conversely such `T suDiag(k) Tᴴ` has `exp = −I` (odd `k_j`) and lies in `𝔰𝔲(n)`
(`Σ k_j = 0`), and for `A ∈ 𝔰𝔲(n)` with `exp A = −I`, `t ↦ exp tA` is a path in
`Ω(SU(n); I, −I)` and an unbroken geodesic. -/
def A : Prop :=
  type_of% @Morse.eqOn_exp_smul_of_isUnbrokenGeodesic_su.{0} ∧
    type_of% @Morse.exists_unitary_suDiag.{0} ∧ type_of% @Morse.exp_conj_suDiag.{0} ∧
    type_of% @Morse.conj_suDiag_mem.{0} ∧ type_of% @Morse.mem_pathSpace_exp.{0} ∧
    type_of% @Morse.isUnbrokenGeodesic_exp.{0}

theorem A_holds : A :=
  ⟨@Morse.eqOn_exp_smul_of_isUnbrokenGeodesic_su, @Morse.exists_unitary_suDiag,
    @Morse.exp_conj_suDiag, @Morse.conj_suDiag_mem, @Morse.mem_pathSpace_exp,
    @Morse.isUnbrokenGeodesic_exp⟩

/-! `A → B` and `B → A` are not proved (see `V14_14.json`): `B` quantifies over every abstract `M` with an
isometric embedding `ψ` onto `SU(n)` and every Levi-Civita connection (transport along `ψ` and uniqueness of
the Levi-Civita connection are not formalized); `B` only describes geodesics from `I` to `−I` and only in one
direction, while `A` also covers geodesics from `I` to any `q` and the converse (every `exp tA` with
`exp A = −I` is a geodesic, and the facts about `T suDiag(k) Tᴴ`).

## The embedded special case: `SU(n)` as `Bridge.Sub` (model `ℝᵈ`), `ψ` the inclusion -/

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

end Emb

open scoped Morse.MatrixInner

open Emb in
/-- `B` for `M = SU(n)` (`n ≥ 1`) with the induced metric (`Bridge.Sub`, model `ℝᵈ`), `ψ` the inclusion,
`cov` the induced connection. Connectedness of `SU(n)` (an instance argument of `B`) is not
formalized (neither in Mathlib nor in the project), so it is kept as a hypothesis. -/
def B_emb : Prop :=
  ∀ (n : ℕ) [NeZero n], ConnectedSpace (SUM n) →
    ∀ p q : SUM n, ψ n p = 1 → ψ n q = -1 → ∀ γ : ℝ → SUM n,
      IsGeodPQ (dd n) (Bridge.conn (hN := hR n)) p q γ →
      ∃ A ∈ suAlg n, mexp A = -1 ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, ψ n (γ t) = mexp (t • A)) ∧
        ∃ T ∈ Un n, ∃ k : Fin n → ℤ, (∀ j, Odd (k j)) ∧ ∑ j, k j = 0 ∧ A = T * milnorA k * Tᴴ

theorem B_to_B_emb : B → B_emb := by
  intro hB n _ _ p q hp hq γ hγ
  exact hB n (Emb.dd n) (Emb.SUM n) (Emb.ψ n) Emb.isSUModel_ψ Bridge.conn Bridge.conn_isLC p q hp hq
    γ hγ

theorem milnorA_eq_suDiag {n : ℕ} (k : Fin n → ℤ) : milnorA k = Morse.suDiag k := by
  unfold milnorA diagI Morse.suDiag
  congr 1
  funext j
  push_cast
  ring

theorem A_to_B_emb : A → B_emb := by
  rintro ⟨heq, hdiag, -, -, -, -⟩ n _ _ p q hp hq γ ⟨hgeo, h0, h1⟩
  have hu := Emb.isUnbrokenGeodesic_of_isGeodesic hgeo
  have hpath := Emb.mem_pathSpace_of_isGeodesic hgeo
  rw [h0, h1] at hpath
  have hp' : Bridge.incl (Emb.hR n) p = 1 := hp
  have hq' : Bridge.incl (Emb.hR n) q = -1 := hq
  rw [hp', hq'] at hpath
  obtain ⟨A, hA, hEq⟩ := heq hpath hu
  have hexp : NormedSpace.exp A = -1 := by
    have := hEq ⟨zero_le_one, le_rfl⟩
    simp only [Function.comp_apply, h1, hq', one_smul] at this
    exact this.symm
  obtain ⟨T, k, hT, hk, hsum, hAeq⟩ := hdiag hA hexp
  refine ⟨A, hA, hexp, fun t ht => hEq ht, T, ?_, k, hk, hsum, by rw [hAeq, milnorA_eq_suDiag]⟩
  show T ∈ Matrix.unitaryGroup (Fin n) ℂ
  rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
  exact hT


#rt_check RoundTrip.V14_14.A_to_B_emb [Morse.eqOn_exp_smul_of_isUnbrokenGeodesic_su, Morse.exists_unitary_suDiag, Morse.exp_conj_suDiag, Morse.conj_suDiag_mem, Morse.mem_pathSpace_exp, Morse.isUnbrokenGeodesic_exp]
#rt_check RoundTrip.V14_14.B_to_B_emb [Morse.eqOn_exp_smul_of_isUnbrokenGeodesic_su, Morse.exists_unitary_suDiag, Morse.exp_conj_suDiag, Morse.conj_suDiag_mem, Morse.mem_pathSpace_exp, Morse.isUnbrokenGeodesic_exp]
#rt_overlap RoundTrip.V14_14.A_to_B_emb [Morse.eqOn_exp_smul_of_isUnbrokenGeodesic_su, Morse.exists_unitary_suDiag, Morse.exp_conj_suDiag, Morse.conj_suDiag_mem, Morse.mem_pathSpace_exp, Morse.isUnbrokenGeodesic_exp]

end RoundTrip.V14_14
