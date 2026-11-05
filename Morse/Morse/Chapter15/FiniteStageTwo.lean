import Morse.Chapter15.IndexBoundTwo
import Morse.Chapter13.Componentwise

/-!
Milnor, *Morse Theory*, §24, pp. 147–148 (proof of Theorem 24.5, case `k ≡ 2 (mod 4)`), finite
stage; Exposition/Chapter15.md, §6, Lemma 6.2 and the case `k ≡ 2 (mod 4)`.

# Theorem 22.1 for `Ω_k(n)`, `k ≡ 2 (mod 4)`, one component `Ω^{(c)}` at a time

## Milnor's text, paraphrased

(p. 148) For `k = 2, 6`, Theorem 22.1 is applied to each `Ω^{(c)}` separately: `φ_r` maps
`Ω_{k+1}(n)^{(c)}` into `Ω^{(c)}`, inducing isomorphisms of `π_i` for `i ≤ (ν − |c|)/4 − 2`,
`ν = n/m_k`.

## What is formalized

Here `J : ℕ → Mₙ(ℝ)` with `IsAnticommFamily J (k + 1)`, `k ≠ 0`, `k + 1 ≤ 8`, `k ≢ 3 (mod 4)`,
and Milnor's `i = J_1⋯J_{k−1}` satisfying `Morse.IsCentralI` (for `k = 2, 6`:
`Morse.isCentralI_two`, `Morse.isCentralI_six` with `Morse.iWordM_two`, `Morse.iWordM_six`).
`Ω^{(c)}` is `Morse.omegaComp` with angle `π m_{k+1} c/2`.

* `Morse.omegaPhi_mem_omegaComp`: **`φ_r(J')` lies in the component of angle
  `−π tr(J_kᵀJ'·i)/2`** (so `Ω_{k+1}(n)^{(c)}` is `{J' : −tr(J_kᵀJ'i) = m_{k+1}c}`).
* `Morse.omega_hidx_two`: the index hypothesis of Lemma 6.2 on `Ω^{(c)}`, with
  `λ₀ = (n/m_{k+1} − |c|)/4`.
* **`Morse.omegaPhi_bijective_two`** (Theorem 24.5, finite stage, `k ≡ 2 (mod 4)`): `φ_r` is
  bijective on `π_{j+1}` at every `J'` with `φ_r(J') ∈ Ω^{(c)}`, for `j + 3 ≤ (ν − |c|)/4`.
* **`Morse.omega_minPaths_bijective_two`** (Lemma 6.2 on `Ω^{(c)}`, including `π_0`): the
  inclusion of the minimal geodesics in `Ω^{(c)}` into `Ω^{(c)}` is bijective on `π_j` for
  `j + 2 ≤ (ν − |c|)/4`.

## What Milnor leaves implicit

* For `π_0` the statement is about the minimal geodesics in `Ω^{(c)}`, which `φ_r` identifies
  with `Ω_{k+1}(n)^{(c)}` up to homotopy (`Morse.isHomotopyEquiv_omegaPhi_minPaths`).
* The higher homotopy groups of `Ω^{(c)}` at its points are those of the whole path space,
  `Ω^{(c)}` being open and closed (`Morse.bijective_val_of_pushesInto`).
-/

open Matrix Set Filter Topology Module Function
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

/-- **Milnor's `i = J_1⋯J_{k−1}` for `k = 2, 6`.** -/
theorem isCentralI_iWordM (hJ : IsAnticommFamily J (k + 1)) (hk : k = 2 ∨ k = 6) :
    IsCentralI J k (iWordM J k) := by
  rcases hk with rfl | rfl
  · rw [iWordM_two]; exact isCentralI_two (hJ.mono (by norm_num))
  · rw [iWordM_six]; exact isCentralI_six (hJ.mono (by norm_num))

section Stage

variable (hJ : IsAnticommFamily J (k + 1))
include hJ

/-- **The component of `φ_r(J')`**: the angle of `f` along the semicircle through `J'` is
`−π tr(J_kᵀJ'·i)/2`. -/
theorem omegaPhi_mem_omegaComp (hii : IsCentralI J k (iWordM J k)) (J' : Omega J (k + 1)) :
    (omegaPhi hJ J' : PathSp _ _ _) ∈ omegaComp J k (iWordM J k)
      (-(Real.pi * trace ((basePt J k)ᴴ * (J' : Matrix ι ι ℝ) * iWordM J k)) / 2) := by
  have hJk := hJ.mono k.le_succ
  have hA : (basePt J k)ᴴ * (J' : Matrix ι ι ℝ) ∈ minVelO J k (basePt J k) :=
    (minVelOHomeomorph hJk).symm J' |>.2
  have hV : Real.pi • ((basePt J k)ᴴ * (J' : Matrix ι ι ℝ)) ∈ tanAlg J k (basePt J k) :=
    (tanAlg J k _).smul_mem _ hA.1
  have heq : EqOn (omegaPhi hJ J' : ℝ → Matrix ι ι ℝ)
      (fun t => basePt J k * NormedSpace.exp (t • (Real.pi • ((basePt J k)ᴴ * J'))))
      (Icc 0 1) := fun t _ => by
    rw [omegaPhi_apply, ← omegaGeo_eq_semicircle hJk J'.2 t]
    rfl
  refine (mem_omegaComp_geo_iff hJk hii (omegaPhi hJ J').2 hV heq _).2 ?_
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul]

/-- **The index hypothesis of Lemma 6.2 on `Ω^{(c)}`**, `λ₀ = (n/m_{k+1} − |c|)/4`. -/
theorem omega_hidx_two (hk : k ≠ 0) (hk8 : k + 1 ≤ 8) (hk3 : k % 4 ≠ 3)
    (hii : IsCentralI J k (iWordM J k)) (c : ℤ) :
    ∀ γ (hγ : γ ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k)),
      (⟨γ, hγ⟩ : PathSp _ _ _) ∈
        omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2) →
      IsUnbrokenGeodesic (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k)) γ →
      (∃ γ' ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k),
        energy γ' 0 1 < energy γ 0 1) →
      (((Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4 : ℕ) : ℕ∞) ≤
        formIndex (energyHessian
          (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k)) hγ) := by
  intro γ hγ hc hgeo hnm
  obtain ⟨ν, hν, hle⟩ := le_formIndex_of_not_minimal_omega_two (hJ.mono k.le_succ) hk hk8 hk3
    hii (minVel_base hJ) hγ hgeo hnm hc
  have hdiv : Fintype.card ι / milnorM (k + 1) = ν := by
    rw [← hν, Nat.mul_div_cancel _ (milnorM_pos _)]
  rw [hdiv]
  exact hle

/-- **Lemma 6.2 on `Ω^{(c)}`, with `π_0`** (Milnor p. 148): the minimal geodesics in `Ω^{(c)}`
include into `Ω^{(c)}` bijectively on `π_j` for `j + 2 ≤ (ν − |c|)/4`. -/
theorem omega_minPaths_bijective_two (hk : k ≠ 0) (hk8 : k + 1 ≤ 8) (hk3 : k % 4 ≠ 3)
    (hii : IsCentralI J k (iWordM J k)) (c : ℤ) {j : ℕ}
    (hj : j + 2 ≤ (Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4)
    (γ : {γ : minPaths (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k) |
      (γ : PathSp _ _ _) ∈ omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2)}) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := Fin j)
      (clopenIncl (minPaths _ _ _)
        (omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2))) γ) :=
  theorem_22_1_clopen_bijective
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ)
    (fun r => isCompact_closedRiemBall_of_isClosed
      (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
      (isClosed_omegaStratum (hJ.mono k.le_succ) _) _ r)
    (isClopen_omegaComp (hJ.mono k.le_succ) hk hii _) (omega_hidx_two hJ hk hk8 hk3 hii c)
    (exists_retraction_minPaths_omega (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ))
    (by simpa using hj) γ

/-- **Theorem 24.5, finite stage, `k ≡ 2 (mod 4)`** (Milnor pp. 147–148): `φ_r` induces
bijections `π_{j+1}(Ω_{k+1}(n), J') → π_{j+1}(Ω(Ω_k(n); J_k, −J_k), φ_r(J'))` whenever
`φ_r(J') ∈ Ω^{(c)}` and `j + 3 ≤ (ν − |c|)/4`, `ν = n/m_{k+1}`. -/
theorem omegaPhi_bijective_two (hk : k ≠ 0) (hk8 : k + 1 ≤ 8) (hk3 : k % 4 ≠ 3)
    (hii : IsCentralI J k (iWordM J k)) (c : ℤ) {j : ℕ}
    (hj : j + 3 ≤ (Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4) (J' : Omega J (k + 1))
    (hJ' : (omegaPhi hJ J' : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2)) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := Fin (j + 1)) (omegaPhi hJ) J') := by
  obtain ⟨e, he⟩ := isHomotopyEquiv_omegaPhi_minPaths hJ
  have hmem : ((e.toFun J' : minPaths _ _ _) : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2) := by
    have := congrFun (congrArg DFunLike.coe he) J'
    simp only [ContinuousMap.comp_apply] at this
    change minPathsIncl _ _ _ (e.toFun J') ∈ _
    rw [this]
    exact hJ'
  rw [← he, Morse.Homotopy.homotopyGroupMap_comp]
  exact (theorem_22_1_clopen_bijective_minPathsIncl
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ)
    (fun r => isCompact_closedRiemBall_of_isClosed
      (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
      (isClosed_omegaStratum (hJ.mono k.le_succ) _) _ r)
    (isClopen_omegaComp (hJ.mono k.le_succ) hk hii _) (omega_hidx_two hJ hk hk8 hk3 hii c)
    (exists_retraction_minPaths_omega (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ))
    (K := Fin (j + 1)) (by simpa using hj) _ hmem).comp
    (Morse.Homotopy.bijective_homotopyGroupMap_of_homotopyEquiv e J')

/-- **Theorem 24.5, finite stage, for `k = 2, 6`** (Milnor pp. 147–148): `φ_r` is bijective on
`π_{j+1}` at every `J' ∈ Ω_{k+1}(n)^{(c)}` for `j + 3 ≤ (n/m_k − |c|)/4`. -/
theorem theorem_24_5_two_six (hk : k = 2 ∨ k = 6) (c : ℤ) {j : ℕ}
    (hj : j + 3 ≤ (Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4) (J' : Omega J (k + 1))
    (hJ' : (omegaPhi hJ J' : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2)) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := Fin (j + 1)) (omegaPhi hJ) J') :=
  omegaPhi_bijective_two hJ (by omega) (by omega) (by omega) (isCentralI_iWordM hJ hk) c hj J' hJ'

/-- **Theorem 24.5, finite stage, `k ≡ 2 (mod 4)`, as Milnor's isomorphism** (pp. 147–148 with
Corollary 22.2): `π_{j+1}(Ω_{k+1}(n), J') ≅ π_{j+2}(Ω_k(n), J_k)` (as sets) for
`φ_r(J') ∈ Ω^{(c)}` and `j + 3 ≤ (n/m_{k+1} − |c|)/4`. -/
theorem omega_pi_equiv_two (hk : k ≠ 0) (hk8 : k + 1 ≤ 8) (hk3 : k % 4 ≠ 3)
    (hii : IsCentralI J k (iWordM J k)) (c : ℤ) {j : ℕ}
    (hj : j + 3 ≤ (Fintype.card ι / milnorM (k + 1) - c.natAbs) / 4) (J' : Omega J (k + 1))
    (hJ' : (omegaPhi hJ J' : PathSp _ _ _) ∈
      omegaComp J k (iWordM J k) (Real.pi * milnorM (k + 1) * c / 2)) :
    Nonempty (π_ (j + 1) (Omega J (k + 1)) J' ≃
      π_ (j + 2) (Omega J k) ⟨basePt J k, basePt_mem hJ⟩) := by
  have e₁ := Equiv.ofBijective _ (omegaPhi_bijective_two hJ hk hk8 hk3 hii c hj J' hJ')
  obtain ⟨e₂⟩ := nonempty_mulEquiv_pathSp
    (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ) j (omegaPhi hJ J')
  obtain ⟨e₃⟩ := nonempty_pi_stratum_equiv (hJ.mono k.le_succ)
    (self_mem_omegaStratum (basePt_mem hJ)) (j + 1)
  exact ⟨e₁.trans (e₂.toEquiv.trans e₃)⟩

end Stage

end Morse
