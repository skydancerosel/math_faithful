import Morse.Chapter15.IndexBound
import Morse.Chapter15.OmegaRetract
import Morse.Chapter13.Corollaries
import Morse.Chapter13.CorollaryGroups
import Morse.Homotopy.BundlesUnitary

/-!
Milnor, *Morse Theory*, §24, Theorem 24.3 (p. 136) and the proof of Theorem 24.5 (pp. 144–146),
finite stage; Exposition/Chapter15.md, §1 and §6.

# Theorem 22.1 for `Ω_k(n)`: `π_i Ω_{k+1}(n) ≅ π_{i+1} Ω_k(n)` in a range

## Milnor's text, paraphrased

(Theorem 24.3) The inclusion `Ω_1(n) → Ω(O(n); I, −I)` induces isomorphisms of homotopy groups
in dimensions `≤ n − 4`; hence `π_iΩ_1(n) ≅ π_{i+1}O(n)` for `i ≤ n − 4`.  (p. 146) For
`k ≢ 2 (mod 4)`, by Theorem 22.1 the inclusion `φ_r : Ω_{k+1}(n) → Ω(Ω_k(n); J_k, −J_k)` induces
isomorphisms of `π_i` for `i ≤ n/m_{k+1} − 3`.

## What is formalized

Here `J : ℕ → Mₙ(ℝ)` with `IsAnticommFamily J (k + 1)` (Milnor's `J_1, …, J_{k+1}`), `J_k` is
`Morse.basePt J k` (`J_0 = I`), and the path space is that of the stratum of `J_k`
(`Morse.omegaStratum`, open and closed in `Ω_k(n)`).

* `Morse.omegaPhi`: **Milnor's `φ_r`**, `J' ↦ (t ↦ cos(πt)J_k + sin(πt)J')`
  (`Morse.omegaPhi_apply`), a homotopy equivalence onto `Ω^d`
  (`Morse.isHomotopyEquiv_omegaPhi_minPaths`).
* `Morse.omega_hidx`: the index hypothesis of Theorem 22.1 with `λ₀ = r₀(n/m_{k+1} − 1)`;
  `Morse.omega_theorem_22_1_bijective`: Theorem 22.1 for `Ω_k(n)`.
* **`Morse.omegaPhi_bijective`** (Theorem 24.5, finite stage, `k ≤ 7`, `k ≢ 2 (mod 4)`):
  `φ_r` is bijective on `π_i` at every `J'` for `i + 2 ≤ r₀(n/m_{k+1} − 1)`, i.e.
  `i ≤ n/m_{k+1} − 3` for `r₀ = 1`.
* **`Morse.omega_pi_equiv`**: `π_i(Ω_{k+1}(n), J') ≃ π_{i+1}(Ω_k(n), J_k)` in the same range
  (Corollary 22.2, and `Morse.nonempty_pi_stratum_equiv` from the stratum to `Ω_k(n)`).
* **`Morse.theorem_24_3`**: for `k = 0` (`r₀ = 2`): `φ_r : Ω_1(n) → Ω(O(n); I, −I)` is bijective
  on `π_i` and `π_iΩ_1(n) ≃ π_{i+1}O(n)`, for `i ≤ n − 4`.

All isomorphisms are bijections of pointed sets.

## What Milnor leaves implicit

* Theorem 22.1 is applied to the stratum of `J_k` (one model space); the paths from `J_k` stay in
  it, and it has the homotopy groups of `Ω_k(n)` at `J_k`.
* The manifold hypothesis of Theorem 22.1 is replaced by the explicit neighbourhood retraction of
  `Morse/Chapter15/OmegaRetract.lean`; completeness by the compactness of the stratum.

## Continued elsewhere

The case `k ≡ 2 (mod 4)` (Lemma 6.2 and the winding number of `det_ℂ`) is
`Morse/Chapter15/FiniteStageTwo.lean`; the chain `π_{j+1}Ω_8(16r) ≅ π_{j+9}O(16r)` is
`Morse/Chapter15/BottChain.lean`, the stabilization maps and the compatibility
`φ_{r+1}(J' ⊕ J'_{k+1}) = φ_r(J') ⊕ δ_k` are `Morse/Chapter15/Stabilization.lean`, and
`Ω_8(16r) ≅ O(r)` with `π_{j+1}O(r) ≅ π_{j+9}O(16r)` is `Morse/Chapter15/OmegaEight.lean`.
Not formalized: the colimits `Ω_k = ⋃_r Ω_k(16r)` and their homotopy groups.
-/

open Matrix Set Filter Topology Module Function
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

section Stage

variable (hJ : IsAnticommFamily J (k + 1))
include hJ

/-- `J_k ∈ Ω_k(n)` (`J_0 = I`). -/
theorem basePt_mem : basePt J k ∈ Omega J k :=
  basePt_mem_omega (hJ.mono k.le_succ)

/-- The direction of the semicircle through `J_{k+1}`: `J_kᴴJ_{k+1}`, a minimal direction. -/
theorem minVel_base : (basePt J k)ᴴ * J (k + 1) ∈ minVelO J k (basePt J k) := by
  refine (mem_minVelO_iff (hJ.mono k.le_succ)).2 ?_
  rw [← Matrix.mul_assoc, mul_conjTranspose_eq_one (omega_orth (basePt_mem hJ)),
    Matrix.one_mul]
  exact hJ.mem_omega (by omega)

theorem neg_basePt_mem : -basePt J k ∈ omegaStratum J k (basePt J k) :=
  neg_mem_omegaStratum (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ)

/-- **Milnor's `φ_r : Ω_{k+1}(n) → Ω(Ω_k(n); J_k, −J_k)`** (p. 138): `J' ↦` the semicircle
`t ↦ cos(πt) J_k + sin(πt) J'` (`Morse.omegaPhi_apply`). -/
def omegaPhi : C(Omega J (k + 1), PathSp (omegaStratum J k (basePt J k)) (basePt J k)
    (-basePt J k)) :=
  (minPathsIncl _ _ _).comp ((omegaMinPathsHomotopyEquiv (hJ.mono k.le_succ) (basePt_mem hJ)
    (minVel_base hJ)).toFun.comp
      ⟨_, (minVelOHomeomorph (hJ.mono k.le_succ)).symm.continuous⟩)

theorem omegaPhi_apply (J' : Omega J (k + 1)) (t : ℝ) :
    (omegaPhi hJ J' : ℝ → Matrix ι ι ℝ) t =
      Real.cos (Real.pi * t) • basePt J k + Real.sin (Real.pi * t) • (J' : Matrix ι ι ℝ) :=
  omegaGeo_eq_semicircle (hJ.mono k.le_succ) J'.2 t

/-- `φ_r` is a homotopy equivalence onto the space `Ω^d` of minimal geodesics (Lemma 24.4 (iii)
in the path space). -/
theorem isHomotopyEquiv_omegaPhi_minPaths :
    ∃ e : ContinuousMap.HomotopyEquiv (Omega J (k + 1))
      (minPaths (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k)),
      (minPathsIncl _ _ _).comp e.toFun = omegaPhi hJ :=
  ⟨(minVelOHomeomorph (hJ.mono k.le_succ)).symm.toHomotopyEquiv.trans
    (omegaMinPathsHomotopyEquiv (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ)), rfl⟩

/-- **The index hypothesis of Theorem 22.1 for `Ω_k(n)`**, `k ≢ 2 (mod 4)`, `k ≤ 7`: every
non-minimal geodesic from `J_k` to `−J_k` has index `≥ r₀(n/m_{k+1} − 1)`. -/
theorem omega_hidx (hk8 : k + 1 ≤ 8) (hk3 : (k + 1) % 4 ≠ 3) {r₀ : ℕ}
    (hr₀ : r₀ = 1 ∨ (r₀ = 2 ∧ k = 0)) :
    ∀ γ (hγ : γ ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k)),
      IsUnbrokenGeodesic (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k)) γ →
      (∃ γ' ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k),
        energy γ' 0 1 < energy γ 0 1) →
      ((r₀ * (Fintype.card ι / milnorM (k + 1) - 1) : ℕ) : ℕ∞) ≤
        formIndex (energyHessian
          (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k)) hγ) := by
  intro γ hγ hgeo hnm
  obtain ⟨s, hs, hle⟩ := le_formIndex_of_not_minimal_omega (hJ.mono k.le_succ) hk8 hk3
    (minVel_base hJ) hr₀ hγ hgeo hnm
  have hdiv : Fintype.card ι / milnorM (k + 1) = s + 1 := by
    rw [← hs, Nat.mul_div_cancel _ (milnorM_pos _)]
  rw [hdiv, Nat.add_sub_cancel]
  exact hle

/-- **Theorem 22.1 for `Ω_k(n)`** (Milnor pp. 145–146 with p. 118): the inclusion of the minimal
geodesics `Ω^d → Ω(Ω_k(n); J_k, −J_k)` is bijective on `π_i` for `i + 2 ≤ r₀(n/m_{k+1} − 1)`. -/
theorem omega_theorem_22_1_bijective (hk8 : k + 1 ≤ 8) (hk3 : (k + 1) % 4 ≠ 3) {r₀ : ℕ}
    (hr₀ : r₀ = 1 ∨ (r₀ = 2 ∧ k = 0)) {i : ℕ}
    (hi : i + 2 ≤ r₀ * (Fintype.card ι / milnorM (k + 1) - 1))
    (γ : minPaths (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k)) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := Fin i) (minPathsIncl _ _ _) γ) :=
  theorem_22_1_bijective (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ)
    (fun r => isCompact_closedRiemBall_of_isClosed
      (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
      (isClosed_omegaStratum (hJ.mono k.le_succ) _) _ r)
    (omega_hidx hJ hk8 hk3 hr₀)
    (exists_retraction_minPaths_omega (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ))
    (by simpa using hi) γ

/-- **Theorem 24.5, finite stage, `k ≢ 2 (mod 4)`** (Milnor pp. 144–146): for `k ≤ 7`,
`k ≢ 2 (mod 4)`, Milnor's `φ_r : Ω_{k+1}(n) → Ω(Ω_k(n); J_k, −J_k)`,
`J' ↦ (t ↦ cos(πt)J_k + sin(πt)J')`, induces bijections `π_i(Ω_{k+1}(n), J') →
π_i(Ω(Ω_k(n); J_k, −J_k), φ_r(J'))` for `i ≤ r₀(n/m_{k+1} − 1) − 2`; with `r₀ = 1` this is
Milnor's `i ≤ n/m_{k+1} − 3`, and for `k = 0` (Theorem 24.3) `r₀ = 2` gives `i ≤ n − 4`. -/
theorem omegaPhi_bijective (hk8 : k + 1 ≤ 8) (hk3 : (k + 1) % 4 ≠ 3) {r₀ : ℕ}
    (hr₀ : r₀ = 1 ∨ (r₀ = 2 ∧ k = 0)) {i : ℕ}
    (hi : i + 2 ≤ r₀ * (Fintype.card ι / milnorM (k + 1) - 1)) (J' : Omega J (k + 1)) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := Fin i) (omegaPhi hJ) J') := by
  obtain ⟨e, he⟩ := isHomotopyEquiv_omegaPhi_minPaths hJ
  rw [← he, Morse.Homotopy.homotopyGroupMap_comp]
  exact (omega_theorem_22_1_bijective hJ hk8 hk3 hr₀ hi _).comp
    (Morse.Homotopy.bijective_homotopyGroupMap_of_homotopyEquiv e J')

end Stage

/-! ### From the stratum to `Ω_k(n)` -/

section Clopen

variable {p : Matrix ι ι ℝ}

/-- The stratum, inside `Ω_k(n)`. -/
def stratumIn (J : ℕ → Matrix ι ι ℝ) (k : ℕ) (p : Matrix ι ι ℝ) : Set (Omega J k) :=
  {y | (y : Matrix ι ι ℝ) ∈ omegaStratum J k p}

theorem isClopen_stratumIn (hJ : IsAnticommFamily J k) :
    IsClopen (stratumIn J k p) := by
  refine ⟨(isClosed_omegaStratum hJ p).preimage continuous_subtype_val, ?_⟩
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have h := eventually_mem_omegaStratum hJ hy
  have h2 := continuous_subtype_val.continuousAt.eventually h
  filter_upwards [h2] with z hz
  exact hz z.2

/-- `stratumIn ≅ omegaStratum`. -/
def stratumInHomeomorph (J : ℕ → Matrix ι ι ℝ) (k : ℕ) (p : Matrix ι ι ℝ) :
    stratumIn J k p ≃ₜ omegaStratum J k p where
  toFun y := ⟨y.1.1, y.2⟩
  invFun z := ⟨⟨z.1, omegaStratum_subset p z.2⟩, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- **The stratum carries the homotopy groups of `Ω_k(n)` at its points** (it is open and
closed). -/
theorem nonempty_pi_stratum_equiv (hJ : IsAnticommFamily J k) {x : Matrix ι ι ℝ}
    (hx : x ∈ omegaStratum J k p) (j : ℕ) :
    Nonempty (π_ (j + 1) (omegaStratum J k p) ⟨x, hx⟩ ≃
      π_ (j + 1) (Omega J k) ⟨x, omegaStratum_subset p hx⟩) := by
  have e₁ := Morse.Homotopy.piEquivOfHomeomorph (stratumInHomeomorph J k p).symm
    (x := ⟨x, hx⟩) (y := ⟨⟨x, omegaStratum_subset p hx⟩, hx⟩) rfl (j + 1)
  have e₂ := Equiv.ofBijective _ (Morse.Homotopy.bijective_homotopyGroupMap_clopen
    (N := Fin (j + 1)) (isClopen_stratumIn (p := p) hJ) (x := ⟨x, omegaStratum_subset p hx⟩) hx)
  exact ⟨e₁.trans e₂⟩

end Clopen

section Loop

variable (hJ : IsAnticommFamily J (k + 1))
include hJ

/-- **Theorem 24.5, finite stage, as Milnor's isomorphism of homotopy groups** (pp. 145–146 with
Corollary 22.2): for `k ≤ 7`, `k ≢ 2 (mod 4)` and `i + 2 ≤ r₀(n/m_{k+1} − 1)`,
`π_i(Ω_{k+1}(n), J') ≅ π_{i+1}(Ω_k(n), J_k)` (as sets; `r₀ = 1`, or `2` for `k = 0`). -/
theorem omega_pi_equiv (hk8 : k + 1 ≤ 8) (hk3 : (k + 1) % 4 ≠ 3) {r₀ : ℕ}
    (hr₀ : r₀ = 1 ∨ (r₀ = 2 ∧ k = 0)) {i : ℕ}
    (hi : i + 2 ≤ r₀ * (Fintype.card ι / milnorM (k + 1) - 1)) (J' : Omega J (k + 1)) :
    Nonempty (π_ i (Omega J (k + 1)) J' ≃ π_ (i + 1) (Omega J k) ⟨basePt J k, basePt_mem hJ⟩) := by
  obtain ⟨e, -⟩ := isHomotopyEquiv_omegaPhi_minPaths hJ
  have e₁ := Morse.Homotopy.homotopyGroupEquivOfHomotopyEquiv (N := Fin i) e J'
  obtain ⟨e₂⟩ := corollary_22_2 (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
    (self_mem_omegaStratum (basePt_mem hJ)) (neg_basePt_mem hJ)
    (fun r => isCompact_closedRiemBall_of_isClosed
      (isSliceSubmanifold_omegaStratum (hJ.mono k.le_succ) (basePt J k))
      (isClosed_omegaStratum (hJ.mono k.le_succ) _) _ r)
    (omega_hidx hJ hk8 hk3 hr₀)
    (exists_retraction_minPaths_omega (hJ.mono k.le_succ) (basePt_mem hJ) (minVel_base hJ))
    hi (e.toFun J')
  obtain ⟨e₃⟩ := nonempty_pi_stratum_equiv (hJ.mono k.le_succ)
    (self_mem_omegaStratum (basePt_mem hJ)) i
  exact ⟨e₁.trans (e₂.trans e₃)⟩

end Loop

/-! ### Theorem 24.3 -/

theorem omegaStratum_zero (J : ℕ → Matrix ι ι ℝ) (p : Matrix ι ι ℝ) :
    omegaStratum J 0 p = Omega J 0 := by
  ext x
  exact ⟨fun h => h.1, fun h => ⟨h, by rw [tanAlg_zero J x p]⟩⟩

/-- **Theorem 24.3 (Bott)** (Milnor p. 136): the inclusion of the complex structures
`Ω_1(n) → Ω(O(n); I, −I)`, `J ↦ (t ↦ cos(πt) I + sin(πt) J)`, induces bijections on `π_i` for
`i ≤ n − 4`, and `π_i Ω_1(n) ≅ π_{i+1} O(n)` for `i ≤ n − 4` (`Ω_1(n)` = `Morse.Omega J 1`, the
complex structures; `J_1` any complex structure, so `n` is even). -/
theorem theorem_24_3 (hJ : IsAnticommFamily J 1) {i : ℕ} (hi : i + 4 ≤ Fintype.card ι)
    (J' : Omega J 1) :
    Bijective (Morse.Homotopy.homotopyGroupMap (N := Fin i) (omegaPhi (k := 0) hJ) J') ∧
      Nonempty (π_ i (Omega J 1) J' ≃
        π_ (i + 1) (orthogonalGroup ι ℝ : Set (Matrix ι ι ℝ)) ⟨1, (orthogonalGroup ι ℝ).one_mem⟩) := by
  have heven := (hJ.cs 1 le_rfl le_rfl).even_card
  obtain ⟨m, hm⟩ := heven
  have hi' : i + 2 ≤ 2 * (Fintype.card ι / milnorM (0 + 1) - 1) := by
    have : milnorM (0 + 1) = 2 := rfl
    rw [this, hm, ← two_mul, Nat.mul_div_cancel_left _ two_pos]
    omega
  refine ⟨omegaPhi_bijective hJ (by norm_num) (by norm_num) (Or.inr ⟨rfl, rfl⟩) hi' J', ?_⟩
  obtain ⟨e⟩ := omega_pi_equiv hJ (by norm_num) (by norm_num) (Or.inr ⟨rfl, rfl⟩) hi' J'
  exact ⟨e⟩

end Morse
