import Morse.Chapter13.Corollaries
import Morse.Chapter12.SUMinimal
import Morse.Chapter10.SphereGeodesics

/-!
Milnor, *Morse Theory*, §23, pp. 128–129 (Exposition/Chapter14.md, §3): Theorem 22.1 for the
minimal geodesics from `I` to `−I` in `SU(2m)`.

# `π_i(Ω^d(SU(2m); I, −I)) ≅ π_{i+1}(SU(2m))` for `i ≤ 2m`

## Milnor's text, paraphrased

(p. 128) By Lemma 23.1 the space `Ω^d` of minimal geodesics from `I` to `−I` in `SU(2m)` is
homeomorphic to `G_m(ℂ^{2m})`, and by Lemma 23.2 every non-minimal geodesic has index
`≥ 2m + 2`.  "Together with Theorem 22.1, this proves" (p. 129) that
`π_i G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m)` for `i ≤ 2m`.

## What is formalized

* `Morse.eqOn_exp_smul_of_isUnbrokenGeodesic_su`: every geodesic `γ : [0, 1] → SU(n)` from `I` is
  `t ↦ exp(tA)` on `[0, 1]`, `A ∈ 𝔰𝔲(n)` (Lemma 21.2 and its converse, glued to the end points).
* `Morse.le_formIndex_of_not_minimal_su`: **the index hypothesis of Theorem 22.1 for `SU(2m)`**:
  every geodesic from `I` to `−I` which does not have least energy has index `≥ 2m + 2`
  (Lemma 23.2, `Morse.lemma_23_2_index`, plus: a geodesic with all `k_j = ±1` is minimal by
  Lemma 23.1's computation, hence has least energy, `E = L² ≤ L(ω)² ≤ E(ω)`).
* `Morse.corollary_22_2_su`: **conditional on the neighbourhood-retract hypothesis for `Ω^d`**,
  `π_i(Ω^d, γ) ≃ π_{i+1}(SU(2m), I)` for `i ≤ 2m`, by Corollary 22.2.

## What is missing (now supplied in `Morse/Chapter14/`)

* **The neighbourhood retract** `hretr` (Theorem 22.1 needs `Ω^d` to be a retract of a
  neighbourhood in `Ω`) is proved in `Morse/Chapter14/MinimalRetract.lean`
  (`Morse.exists_retraction_minPaths_su`, by the spectral projection of the Hermitian part of
  `½(I − iω(1/2))`), giving the unconditional `Morse.corollary_22_2_su'`.
* **`Ω^d ≅ G_m(ℂ^{2m})` on homotopy groups**: `Morse/Chapter14/MinimalPaths.lean`
  (`Morse.minPathsHomotopyEquiv`) and `Morse.theorem_23_3` in
  `Morse/Chapter14/Periodicity.lean`.
-/

open Matrix Set Filter Topology Module Finset
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Every geodesic of `SU(n)` from `I` is a one-parameter subgroup on `[0, 1]`.** -/
theorem eqOn_exp_smul_of_isUnbrokenGeodesic_su {γ : ℝ → Matrix ι ι ℂ} {q : Matrix ι ι ℂ}
    (hγ : γ ∈ pathSpace (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 q)
    (hgeo : IsUnbrokenGeodesic isSliceSubmanifold_specialUnitaryGroup γ) :
    ∃ A ∈ specialSkewHermitian ι,
      EqOn γ (fun s : ℝ => NormedSpace.exp (s • A)) (Icc 0 1) := by
  have hG := isMatrixGroup_specialUnitaryGroup (ι := ι)
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨hX, heq⟩ := hG.eqOn_mul_exp_smul hgeo.2 isPreconnected_Ioo hhalf
  set X := (γ (1 / 2))ᴴ * deriv γ (1 / 2) with hX_def
  set φ : ℝ → Matrix ι ι ℂ := fun t => γ (1 / 2) * NormedSpace.exp ((t - 1 / 2) • X)
  have hφc : Continuous φ := by
    have : Continuous fun t : ℝ => NormedSpace.exp ((t - 1 / 2) • X) :=
      (contDiff_exp_smul X).continuous.comp (continuous_id.sub continuous_const)
    exact continuous_const.mul this
  have heqI : EqOn γ φ (Icc 0 1) :=
    heq.of_subset_closure hgeo.1.continuousOn hφc.continuousOn Ioo_subset_Icc_self
      (by rw [closure_Ioo zero_ne_one])
  have hexp_add : ∀ t : ℝ, NormedSpace.exp ((t - 1 / 2) • X) =
      NormedSpace.exp ((-(1 / 2 : ℝ)) • X) * NormedSpace.exp (t • X) := fun t => by
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left _ |>.smul_right _),
      ← add_smul]
    congr 2; ring
  have h0 : γ (1 / 2) * NormedSpace.exp ((-(1 / 2 : ℝ)) • X) = 1 := by
    have := heqI ⟨le_rfl, zero_le_one⟩
    rw [hγ.2.2.1] at this
    simp only [φ, hexp_add, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at this
    exact this.symm
  refine ⟨X, hX, fun t ht => ?_⟩
  rw [heqI ht]
  simp only [φ, hexp_add, ← Matrix.mul_assoc, h0, Matrix.one_mul]

omit [Nonempty ι] in
/-- The energy of `t ↦ exp(tA)` on `[0, 1]` is `‖A‖²`. -/
theorem energy_exp_smul {A : Matrix ι ι ℂ} (hA : Aᴴ = -A) :
    energy (fun t : ℝ => NormedSpace.exp (t • A)) 0 1 = ‖A‖ ^ 2 := by
  have h := energy_eq_of_norm_deriv (k := ‖A‖)
    (IsPiecewiseSmooth.of_contDiff (contDiff_exp_smul A) zero_le_one).isAdmissible
    (fun t _ _ => by
      rw [(hasDerivAt_exp_smul_const A t).deriv]
      have hu : (NormedSpace.exp (t • A))ᴴ * NormedSpace.exp (t • A) = 1 :=
        exp_conjTranspose_mul_exp_of_skew (by rw [conjTranspose_smul, star_trivial, hA, smul_neg])
      rw [← mulLeftIso_apply _ hu, LinearIsometryEquiv.norm_map])
  rw [h, sub_zero, mul_one]

/-- **The index hypothesis of Theorem 22.1 for `SU(2m)`** (Lemma 23.2): a geodesic from `I` to
`−I` which does not have least energy has index `≥ 2m + 2`. -/
theorem le_formIndex_of_not_minimal_su {m : ℕ} (hcard : Fintype.card ι = 2 * m)
    {γ : ℝ → Matrix ι ι ℂ}
    (hγ : γ ∈ pathSpace (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1))
    (hgeo : IsUnbrokenGeodesic isSliceSubmanifold_specialUnitaryGroup γ)
    (hnm : ∃ γ' ∈ pathSpace (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1),
      energy γ' 0 1 < energy γ 0 1) :
    ((2 * m + 2 : ℕ) : ℕ∞) ≤
      formIndex (energyHessian isSliceSubmanifold_specialUnitaryGroup hγ) := by
  obtain ⟨A, hA, heq⟩ := eqOn_exp_smul_of_isUnbrokenGeodesic_su hγ hgeo
  have hexp : NormedSpace.exp A = -1 := by
    have := heq ⟨zero_le_one, le_rfl⟩
    rw [hγ.2.2.2] at this
    simpa using this.symm
  have hγA := mem_pathSpace_exp hA hexp
  rw [formIndex_energyHessian_congr hγ hγA hgeo (isUnbrokenGeodesic_exp hA) heq]
  obtain ⟨k, hk, -, ⟨T, hT, hAeq⟩, -, hnon⟩ := lemma_23_2_index hcard hA hexp hγA
  refine hnon fun hpm => ?_
  -- all `k_j = ±1`: the geodesic is minimal, so it has least energy
  have hsq : A * A = -((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) := by
    rw [hAeq]; exact (sq_conj_suDiag_iff hT k).2 hpm
  have hmin := (isMinimalGeodesic_exp_iff hcard hA hexp).2 hsq
  obtain ⟨w, hw, hwE⟩ := hnm
  have hlen := pathLength_exp_smul hA.1
  have h1 := hmin.2.2 w 0 1 hw.1 hw.2.1 (by rw [hw.2.2.1]; simp) (by rw [hw.2.2.2]; simp [hexp])
  rw [hlen] at h1
  have h2 := pathLength_sq_le_energy hw.1
  rw [sub_zero, one_mul] at h2
  have h3 : energy γ 0 1 = ‖A‖ ^ 2 := by
    rw [energy_congr heq, energy_exp_smul hA.1]
  have h4 : ‖A‖ ^ 2 ≤ pathLength w 0 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg A) h1 2
  linarith

omit [Nonempty ι] in
/-- `−I ∈ SU(2m)`. -/
theorem neg_one_mem_su {m : ℕ} (hcard : Fintype.card ι = 2 * m) :
    (-1 : Matrix ι ι ℂ) ∈ (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) := by
  refine mem_specialUnitaryGroup_iff.2 ⟨by rw [mem_unitaryGroup_iff]; simp, ?_⟩
  rw [det_neg, det_one, mul_one, Fintype.card, ← Fintype.card, hcard, pow_mul]
  simp

/-- **Corollary 22.2 for `SU(2m)`** (Milnor pp. 128–129), conditional on the neighbourhood-retract
hypothesis `hretr` (see the module docstring): for `i ≤ 2m` and every minimal geodesic `γ` from
`I` to `−I`, `π_i(Ω^d, γ) ≃ π_{i+1}(SU(2m), I)`. -/
theorem corollary_22_2_su {m : ℕ} (hcard : Fintype.card ι = 2 * m)
    (hretr : ∃ O : Set (PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)),
      IsOpen O ∧ minPaths _ 1 (-1) ⊆ O ∧
      ∃ ρ : PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1) →
          PathSp (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1),
        ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths _ 1 (-1)) ∧
        ∀ γ ∈ minPaths _ 1 (-1), ρ γ = γ)
    {i : ℕ} (hi : i ≤ 2 * m)
    (γ : minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    Nonempty (HomotopyGroup.Pi i (minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1))
        γ ≃ HomotopyGroup.Pi (i + 1) (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))
          ⟨1, (specialUnitaryGroup ι ℂ).one_mem⟩) :=
  corollary_22_2 isSliceSubmanifold_specialUnitaryGroup (specialUnitaryGroup ι ℂ).one_mem
    (neg_one_mem_su hcard)
    (fun r => isCompact_closedRiemBall_of_isClosed isSliceSubmanifold_specialUnitaryGroup
      isCompact_specialUnitaryGroup.isClosed 1 r) (l₀ := 2 * m + 2)
    (fun γ hγ hgeo hnm => le_formIndex_of_not_minimal_su hcard hγ hgeo hnm) hretr
    (by omega) γ

end Morse
