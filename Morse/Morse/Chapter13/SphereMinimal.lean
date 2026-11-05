import Morse.Chapter13.Corollaries
import Morse.Chapter10.SphereGeodesics

/-!
Milnor, *Morse Theory*, §22, p. 119 (the proof of Corollary 22.3), with Lemmas A and B of
Exposition/Chapter13.md, §1.

# The minimal geodesics from `p` to `−p` on `Sⁿ⁺¹` and the index of the others

## Milnor's text, paraphrased

(p. 119) Let `p`, `q = −p` be antipodal on `Sⁿ⁺¹`.  "Then the space `Ω^{π²}` of minimal geodesics
from `p` to `q` can be identified with the equator `Sⁿ`.  Every non-minimal geodesic must wind
one and a half times around `Sⁿ⁺¹`, and therefore has index `≥ 2n` (it passes through two
conjugate points of multiplicity `n` in its interior).  Evidently the hypotheses of Theorem 22.1
are satisfied with `λ₀ = 2n`."

## What is formalized

`Sⁿ⁺¹` is `Milnor.Sphere.Sph (n + 1) ⊆ ℝⁿ⁺²` with the slice structure `Milnor.Sphere.sphSub`, and
the great circles `Morse.greatCircle p u L` of `Morse/Chapter10/SphereGeodesics.lean`.

* `Morse.exists_eqOn_greatCircle_antipode`: **every geodesic from `p` to `−p` is
  `t ↦ cos(Lt) p + sin(Lt) u` on `[0, 1]` with `L = (2m + 1)π`** (`cos L = −1`).
* `Morse.pi_sq_le_energy_sph`: every path from `p` to `−p` has energy `≥ π²`, so `d = π²`.
* `Morse.formIndex_greatCircle_antipode`: **Lemma B, the index of the geodesic with
  `L = (2m + 1)π` is `2mn`**, and `Morse.le_formIndex_of_not_minimal_sph`: **every geodesic from
  `p` to `−p` which does not have least energy has index `≥ 2n`** (the index hypothesis of
  Theorem 22.1 with `λ₀ = 2n`).
* `Morse.equator p`, `Morse.semicircle`, `Morse.exists_eqOn_semicircle`: **Lemma A, the paths of
  least energy are the great semicircles** `t ↦ cos(πt) p + sin(πt) u`, `u` on the equator;
  `Morse.continuous_semicircle`: `u ↦` the semicircle is continuous for Milnor's metric;
  `Morse.sphMinPathsHomotopyEquiv`: **`equator ≃ Ω^d` up to homotopy** (inverse `γ ↦ γ(1/2)`), and
  `Morse.sphMinPathsHomeomorph`: **`equator ≅ Ω^d`** as a homeomorphism onto the separation
  quotient.

## What Milnor leaves implicit

* **The list of geodesics from `p` to `−p`.**  A geodesic from `p` is a great circle
  (`Morse.exists_eqOn_greatCircle`); it reaches `−p` at `t = 1` iff `cos L = −1`.  The value
  `d = π²` needs a minimal geodesic to exist (Theorem 16.2's remark,
  `Morse.BrokenSetup.exists_energy_minimizing`): it is one of these circles, so its energy is
  `((2m + 1)π)² ≥ π²`.
* **"Winds one and a half times … therefore has index `≥ 2n`"**: by the index theorem the index
  is the number of interior conjugate points with multiplicity; along the circle of length
  `(2m + 1)π` these are the `t = j/(2m + 1)`, `1 ≤ j ≤ 2m`, each of multiplicity `n`
  (`Morse.conjMultiplicity_greatCircle`), so the index is `2mn` (the end point `t = 1` is also
  conjugate, but does not count).
* **"Identified with the equator"**: the identification is `u ↦` the semicircle through `u`,
  with inverse `γ ↦ γ(1/2)`; its continuity for Milnor's metric uses that all semicircles have
  speed `π`, so the `L²` part of the metric vanishes on `Ω^d`.  As paths are functions on `ℝ`,
  `Ω^d` is homeomorphic to the equator only after identifying paths that agree on `[0, 1]`.
-/

open Set Filter Topology Function Module
open scoped ContDiff Manifold RealInnerProductSpace ENNReal

noncomputable section

namespace Morse

open Milnor.Sphere Real

variable {n : ℕ}


open Classical in
/-- `Σ_{0 < t < 1} [Lt ∈ πℕ] m = km` for `kπ < L ≤ (k + 1)π`. -/
theorem finsum_mem_Ioo_ite_eq' {L : ℝ} {k : ℕ} (hk1 : k * π < L) (hk2 : L ≤ (k + 1) * π)
    (m : ℕ) : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, (if ∃ j : ℕ, L * t = j * π then m else 0) = k * m := by
  have hL : 0 < L := lt_of_le_of_lt (by positivity) hk1
  set f : ℝ → ℕ := fun t => if ∃ j : ℕ, L * t = j * π then m else 0 with hf
  set T : Finset ℝ := (Finset.Icc 1 k).image (fun j : ℕ => (j : ℝ) * π / L) with hT
  have hTmem : ∀ t, t ∈ T ↔ ∃ j : ℕ, (1 ≤ j ∧ j ≤ k) ∧ (j : ℝ) * π / L = t := by
    intro t
    simp only [hT, Finset.mem_image, Finset.mem_Icc]
  have hinj : Injective (fun j : ℕ => (j : ℝ) * π / L) := by
    intro i j hij
    have : (i : ℝ) = j := by
      have := hij
      simp only at this
      field_simp at this
      nlinarith [Real.pi_pos]
    exact_mod_cast this
  rw [finsum_mem_eq_sum_of_inter_support_eq f (t := T) ?_]
  · rw [Finset.sum_congr rfl (g := fun _ => m) ?_, Finset.sum_const,
      Finset.card_image_of_injective _ hinj, Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel]
    intro t ht
    obtain ⟨j, -, rfl⟩ := (hTmem t).1 ht
    simp only [hf]
    rw [if_pos ⟨j, by field_simp⟩]
  · ext t
    simp only [mem_inter_iff, Function.mem_support, Finset.mem_coe]
    constructor
    · rintro ⟨ht, hft⟩
      refine ⟨?_, hft⟩
      have hex : ∃ j : ℕ, L * t = j * π := by
        by_contra h
        exact hft (if_neg h)
      obtain ⟨j, hj⟩ := hex
      have hj0 : (0 : ℝ) < j := by
        have : 0 < (j : ℝ) * π := by rw [← hj]; exact mul_pos hL ht.1
        exact pos_of_mul_pos_left this Real.pi_pos.le
      have hjk : (j : ℝ) < k + 1 := by
        have : (j : ℝ) * π < (k + 1) * π := by rw [← hj]; nlinarith [ht.2]
        exact lt_of_mul_lt_mul_right this Real.pi_pos.le
      refine (hTmem t).2 ⟨j, ⟨?_, ?_⟩, ?_⟩
      · exact_mod_cast hj0
      · have : j < k + 1 := by exact_mod_cast hjk
        omega
      · rw [← hj]
        field_simp
    · rintro ⟨ht, hft⟩
      refine ⟨?_, hft⟩
      obtain ⟨j, ⟨hj1, hjk⟩, rfl⟩ := (hTmem t).1 ht
      have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
      refine ⟨div_pos (mul_pos (by linarith) Real.pi_pos) hL, ?_⟩
      rw [div_lt_one hL]
      nlinarith [Real.pi_pos]

theorem isClosed_sph : IsClosed (Sph n) := by
  change IsClosed ((sphG (n := n)) ⁻¹' {0})
  rw [preimage_eq_sphere]
  exact Metric.isClosed_sphere

variable {p : EuclideanSpace ℝ (Fin (n + 1 + 1))}

theorem neg_mem_sph (hp : p ∈ Sph (n + 1)) : -p ∈ Sph (n + 1) :=
  mem_iff_norm.2 (by rw [norm_neg]; exact mem_iff_norm.1 hp)

/-- The great circle `cos(Lt) p + sin(Lt) u` is a path from `p` to `−p` when `L = (2m + 1)π`. -/
theorem greatCircle_mem_pathSpace_antipode (hp : p ∈ Sph (n + 1)) {u : EuclideanSpace ℝ (Fin (n + 1 + 1))} (hu : ‖u‖ = 1)
    (hpu : ⟪p, u⟫ = 0) (m : ℕ) :
    greatCircle p u ((2 * m + 1) * π) ∈ pathSpace (Sph (n + 1)) p (-p) := by
  have h1 : greatCircle p u ((2 * m + 1) * π) 1 = -p := by
    rw [greatCircle, mul_one, show (2 * (m : ℝ) + 1) * π = π + (m : ℝ) * (2 * π) by ring,
      Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi, Real.cos_pi, Real.sin_pi]
    simp
  exact ⟨IsPiecewiseSmooth.of_contDiff (contDiff_greatCircle _ _ _) zero_le_one,
    fun t _ => greatCircle_mem_sph hp hu hpu _ t, greatCircle_zero _ _ _, h1⟩

theorem isUnbrokenGeodesic_greatCircle (hp : p ∈ Sph (n + 1)) {u : EuclideanSpace ℝ (Fin (n + 1 + 1))} (hu : ‖u‖ = 1)
    (hpu : ⟪p, u⟫ = 0) (L : ℝ) : IsUnbrokenGeodesic (sphSub (n + 1)) (greatCircle p u L) :=
  ⟨(contDiff_greatCircle _ _ _).contDiffOn,
    (isGeodesicOn_greatCircle hp hu hpu _).mono isOpen_Ioo (subset_univ _)⟩

/-- **The geodesics from `p` to `−p`** (Lemma A of Exposition/Chapter13.md, first half): every
geodesic from `p` to `−p` is `t ↦ cos(Lt) p + sin(Lt) u` on `[0, 1]`, with `u ⊥ p` a unit vector
and `L = (2m + 1)π`. -/
theorem exists_eqOn_greatCircle_antipode {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))} (hγ : γ ∈ pathSpace (Sph (n + 1)) p (-p))
    (hgeo : IsUnbrokenGeodesic (sphSub (n + 1)) γ) :
    ∃ u : EuclideanSpace ℝ (Fin (n + 1 + 1)), ∃ m : ℕ, ‖u‖ = 1 ∧ ⟪p, u⟫ = 0 ∧
      EqOn γ (greatCircle p u ((2 * m + 1) * π)) (Icc 0 1) := by
  obtain ⟨u, L, hu, hpu, hL, heq⟩ := exists_eqOn_greatCircle (by omega) hγ hgeo
  have hp : p ∈ Sph (n + 1) := hγ.2.2.1 ▸ hγ.2.1 0 ⟨le_rfl, zero_le_one⟩
  have hp1 := norm_of_mem_sph hp
  have h1 : greatCircle p u L 1 = -p := (heq ⟨zero_le_one, le_rfl⟩).symm.trans hγ.2.2.2
  have hcos : Real.cos L = -1 := by
    have := congrArg (fun x => ⟪p, x⟫) h1
    simp only [greatCircle, mul_one, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hp1, hpu, inner_neg_right] at this
    linarith
  obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.1 hcos
  have hk0 : 0 ≤ k := by
    by_contra h
    have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    nlinarith [Real.pi_pos]
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
  refine ⟨u, m, hu, hpu, fun t ht => ?_⟩
  rw [heq ht, ← hk]
  push_cast
  ring_nf

/-- Every path from `p` to `−p` on `Sⁿ⁺¹` has energy `≥ π²` (a path of least energy exists by
Theorem 16.2 and is one of the great circles of `Morse.exists_eqOn_greatCircle_antipode`). -/
theorem pi_sq_le_energy_sph (hp : p ∈ Sph (n + 1)) {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (hγ : γ ∈ pathSpace (Sph (n + 1)) p (-p)) : π ^ 2 ≤ energy γ 0 1 := by
  have hc : 0 < energy γ 0 1 + 1 :=
    lt_of_le_of_lt (PathSp.energy_nonneg_of_le zero_le_one) (lt_add_one _)
  obtain ⟨k, ⟨B⟩⟩ := exists_brokenSetup_uniform (sphSub (n + 1)) hp (neg_mem_sph hp) hc
    (isCompact_closedRiemBall_of_isClosed (sphSub (n + 1)) isClosed_sph p _)
  obtain ⟨y, hy, hgeo, hmin⟩ := B.exists_energy_minimizing hγ (lt_add_one _)
  obtain ⟨u, m, hu, hpu, heq⟩ :=
    exists_eqOn_greatCircle_antipode (B.path_mem_pathSpace hy) hgeo
  refine le_trans ?_ (hmin γ hγ)
  rw [energy_congr heq, energy_greatCircle (norm_of_mem_sph hp) hu hpu]
  have : (1 : ℝ) ≤ 2 * m + 1 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  exact pow_le_pow_left₀ Real.pi_pos.le (by nlinarith [Real.pi_pos]) 2

/-- **Lemma B** (Exposition/Chapter13.md): the geodesic `t ↦ cos((2m + 1)πt) p + sin((2m + 1)πt) u`
from `p` to `−p` on `Sⁿ⁺¹` has index `2mn`: its interior conjugate points are the `2m` passages
through `±p`, each of multiplicity `n`. -/
theorem formIndex_greatCircle_antipode (hp : p ∈ Sph (n + 1)) {u : EuclideanSpace ℝ (Fin (n + 1 + 1))} (hu : ‖u‖ = 1)
    (hpu : ⟪p, u⟫ = 0) (m : ℕ) :
    formIndex (energyHessian (sphSub (n + 1)) (greatCircle_mem_pathSpace_antipode hp hu hpu m)) =
      ((2 * m * n : ℕ) : ℕ∞) := by
  rw [(theorem_15_1 (sphSub (n + 1)) (greatCircle_mem_pathSpace_antipode hp hu hpu m)
    (isUnbrokenGeodesic_greatCircle hp hu hpu _)).2]
  have hL : 0 < (2 * (m : ℝ) + 1) * π := by positivity
  have h1 : ((2 * m : ℕ) : ℝ) * π < (2 * m + 1) * π := by push_cast; nlinarith [Real.pi_pos]
  have h2 : (2 * m + 1) * π ≤ (((2 * m : ℕ) : ℝ) + 1) * π := by push_cast; rfl
  have := finsum_mem_Ioo_ite_eq' h1 h2 (n + 1 - 1)
  rw [show 2 * m * n = 2 * m * (n + 1 - 1) by simp]
  congr 1
  refine (finsum_mem_congr rfl fun t ht => ?_).trans this
  exact conjMultiplicity_greatCircle (by omega) hp hu hpu hL _ ⟨ht.1, ht.2.le⟩

/-- **The index hypothesis of Theorem 22.1 for `Sⁿ⁺¹`** (Lemma B): a geodesic from `p` to `−p`
which does not have least energy has index `≥ 2n`. -/
theorem le_formIndex_of_not_minimal_sph (hp : p ∈ Sph (n + 1)) {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (hγ : γ ∈ pathSpace (Sph (n + 1)) p (-p)) (hgeo : IsUnbrokenGeodesic (sphSub (n + 1)) γ)
    (hnm : ∃ γ' ∈ pathSpace (Sph (n + 1)) p (-p), energy γ' 0 1 < energy γ 0 1) :
    ((2 * n : ℕ) : ℕ∞) ≤ formIndex (energyHessian (sphSub (n + 1)) hγ) := by
  obtain ⟨u, m, hu, hpu, heq⟩ := exists_eqOn_greatCircle_antipode hγ hgeo
  have hmem := greatCircle_mem_pathSpace_antipode hp hu hpu m
  rw [formIndex_energyHessian_congr hγ hmem hgeo (isUnbrokenGeodesic_greatCircle hp hu hpu _) heq,
    formIndex_greatCircle_antipode hp hu hpu m]
  obtain ⟨γ', hγ', hlt⟩ := hnm
  have hm : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    have h1 := pi_sq_le_energy_sph hp hγ'
    rw [energy_congr heq, energy_greatCircle (norm_of_mem_sph hp) hu hpu, hm0] at hlt
    simp only [Nat.cast_zero, mul_zero, zero_add, one_mul] at hlt
    linarith
  exact_mod_cast (show 2 * n ≤ 2 * m * n by nlinarith)

/-! ### Lemma A: the minimal geodesics from `p` to `−p` -/

variable (p) in
/-- **The equator** `{u : ‖u‖ = 1, u ⊥ p}` of `Sⁿ⁺¹` with respect to the pole `p`. -/
def equator : Set (EuclideanSpace ℝ (Fin (n + 1 + 1))) := {u | ‖u‖ = 1 ∧ ⟪p, u⟫ = 0}

theorem semicircle_mem (hp : p ∈ Sph (n + 1)) (u : equator p) :
    greatCircle p (u : EuclideanSpace ℝ (Fin (n + 1 + 1))) π ∈ pathSpace (Sph (n + 1)) p (-p) := by
  have := greatCircle_mem_pathSpace_antipode hp u.2.1 u.2.2 0
  rwa [Nat.cast_zero, mul_zero, zero_add, one_mul] at this

/-- **The great semicircle** `t ↦ cos(πt) p + sin(πt) u` from `p` to `−p` through `u`. -/
def semicircle (hp : p ∈ Sph (n + 1)) (u : equator p) : PathSp (Sph (n + 1)) p (-p) :=
  ⟨greatCircle p (u : EuclideanSpace ℝ (Fin (n + 1 + 1))) π, semicircle_mem hp u⟩

theorem energy_semicircle (hp : p ∈ Sph (n + 1)) (u : equator p) :
    energy (semicircle hp u) 0 1 = π ^ 2 :=
  energy_greatCircle (norm_of_mem_sph hp) u.2.1 u.2.2 π

/-- The semicircles have least energy `π²`: they lie in `Ω^d`, `d = π²`. -/
theorem semicircle_mem_minPaths (hp : p ∈ Sph (n + 1)) (u : equator p) :
    semicircle hp u ∈ minPaths (Sph (n + 1)) p (-p) := fun γ' =>
  (energy_semicircle hp u).trans_le (pi_sq_le_energy_sph hp γ'.mem)

theorem speed_greatCircle (hp : p ∈ Sph (n + 1)) {u : EuclideanSpace ℝ (Fin (n + 1 + 1))}
    (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0) (L t : ℝ) :
    PathSp.speed (greatCircle p u L) t = |L| := by
  have hpu' : ⟪u, -p⟫ = 0 := by rw [inner_neg_right, real_inner_comm, hpu, neg_zero]
  rw [PathSp.speed, deriv_greatCircle, norm_smul,
    norm_greatCircle hu (by rw [norm_neg, norm_of_mem_sph hp]) hpu' L t, mul_one, Real.norm_eq_abs]

/-- **`u ↦ (t ↦ cos(πt) p + sin(πt) u)` is continuous for Milnor's metric**: all speeds are `π`, so
the `L²` part vanishes, and the uniform part is controlled by pointwise convergence. -/
theorem continuous_semicircle (hp : p ∈ Sph (n + 1)) : Continuous (semicircle hp) := by
  refine continuous_iff_continuousAt.2 fun u => ?_
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0, ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr' : 0 < r := ENNReal.ofReal_pos.1 hr
  have hcs : ∀ s, Continuous fun v : equator p =>
      greatCircle p (v : EuclideanSpace ℝ (Fin (n + 1 + 1))) π s := fun s => by
    unfold greatCircle; fun_prop
  have h1 := PathSp.eventually_supDist_le_of_tendsto_apply (sphSub (n + 1))
    (C := π ^ 2) (l := 𝓝 u)
    (αs := fun v : equator p => (semicircle hp v : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))))
    (Eventually.of_forall fun v => ⟨(semicircle hp v).mem, (energy_semicircle hp v).le⟩)
    (semicircle hp u).mem (energy_semicircle hp u).le (fun s _ => (hcs s).tendsto u) hr'
  filter_upwards [h1] with v hv
  have hl2 : PathSp.l2Dist (semicircle hp v : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1)))
      (semicircle hp u) = 0 := by
    simp only [PathSp.l2Dist, semicircle, speed_greatCircle hp v.2.1 v.2.2,
      speed_greatCircle hp u.2.1 u.2.2, sub_self]
    simp
  rw [PathSp.edist_def, hl2, ENNReal.ofReal_zero, add_zero]
  exact hv.trans hrε.le

/-- **Lemma A** (Exposition/Chapter13.md): every path of least energy from `p` to `−p` agrees on
`[0, 1]` with a great semicircle `t ↦ cos(πt) p + sin(πt) u`, `u` on the equator. -/
theorem exists_eqOn_semicircle (hp : p ∈ Sph (n + 1)) {γ : PathSp (Sph (n + 1)) p (-p)}
    (hγ : γ ∈ minPaths (Sph (n + 1)) p (-p)) :
    ∃ u : equator p, EqOn γ (greatCircle p (u : EuclideanSpace ℝ (Fin (n + 1 + 1))) π)
      (Icc 0 1) := by
  have hgeo := isUnbrokenGeodesic_of_minimal (hN := sphSub (n + 1)) γ.mem
    (fun γ' hγ' => hγ ⟨γ', hγ'⟩)
  obtain ⟨u, m, hu, hpu, heq⟩ := exists_eqOn_greatCircle_antipode γ.mem hgeo
  have hE := hγ (semicircle hp ⟨u, hu, hpu⟩)
  rw [energy_semicircle, energy_congr heq, energy_greatCircle (norm_of_mem_sph hp) hu hpu] at hE
  have hm : m = 0 := by
    by_contra h
    have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h
    have h3 : π < (2 * m + 1) * π := by nlinarith [Real.pi_pos]
    have := pow_lt_pow_left₀ h3 Real.pi_pos.le two_ne_zero
    linarith
  subst hm
  refine ⟨⟨u, hu, hpu⟩, fun t ht => ?_⟩
  rw [heq ht]
  simp

theorem greatCircle_pi_half (p u : EuclideanSpace ℝ (Fin (n + 1 + 1))) :
    greatCircle p u π (1 / 2) = u := by
  rw [greatCircle, show π * (1 / 2) = π / 2 by ring, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem continuous_apply_half_sph :
    Continuous fun γ : PathSp (Sph (n + 1)) p (-p) =>
      (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) (1 / 2) :=
  (continuous_eval_const (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).comp
    (continuous_subtype_val.comp PathSp.continuous_toPathC)

/-- `u ↦` the semicircle through `u`, `equator → Ω^d`. -/
def equatorToMinPaths (hp : p ∈ Sph (n + 1)) : C(equator p, minPaths (Sph (n + 1)) p (-p)) :=
  ⟨fun u => ⟨semicircle hp u, semicircle_mem_minPaths hp u⟩,
    (continuous_semicircle hp).subtype_mk _⟩

theorem apply_half_mem_equator (hp : p ∈ Sph (n + 1)) (γ : minPaths (Sph (n + 1)) p (-p)) :
    (γ.1 : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) (1 / 2) ∈ equator p := by
  obtain ⟨u, heq⟩ := exists_eqOn_semicircle hp γ.2
  rw [heq ⟨by norm_num, by norm_num⟩, greatCircle_pi_half]
  exact u.2

/-- `γ ↦ γ(1/2)`, `Ω^d → equator`. -/
def minPathsToEquator (hp : p ∈ Sph (n + 1)) : C(minPaths (Sph (n + 1)) p (-p), equator p) where
  toFun γ := ⟨(γ.1 : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) (1 / 2), apply_half_mem_equator hp γ⟩
  continuous_toFun := (continuous_apply_half_sph.comp continuous_subtype_val).subtype_mk _

theorem minPathsToEquator_equatorToMinPaths (hp : p ∈ Sph (n + 1)) (u : equator p) :
    minPathsToEquator hp (equatorToMinPaths hp u) = u :=
  Subtype.ext (greatCircle_pi_half p u)

theorem edist_equatorToMinPaths_minPathsToEquator (hp : p ∈ Sph (n + 1))
    (γ : minPaths (Sph (n + 1)) p (-p)) :
    edist (equatorToMinPaths hp (minPathsToEquator hp γ)) γ = 0 := by
  obtain ⟨u, heq⟩ := exists_eqOn_semicircle hp γ.2
  rw [Subtype.edist_eq]
  refine PathSp.edist_eq_zero_of_eqOn fun t ht => ?_
  change greatCircle p ((γ.1 : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) (1 / 2)) π t =
    (γ.1 : ℝ → EuclideanSpace ℝ (Fin (n + 1 + 1))) t
  rw [heq ⟨by norm_num, by norm_num⟩, greatCircle_pi_half, heq ht]

/-- **Lemma A, up to homotopy**: the semicircles give a homotopy equivalence
`equator ≃ Ω^d(Sⁿ⁺¹; p, −p)`, with homotopy inverse `γ ↦ γ(1/2)`. -/
def sphMinPathsHomotopyEquiv (hp : p ∈ Sph (n + 1)) :
    ContinuousMap.HomotopyEquiv (equator p) (minPaths (Sph (n + 1)) p (-p)) where
  toFun := equatorToMinPaths hp
  invFun := minPathsToEquator hp
  left_inv := by
    have : (minPathsToEquator hp).comp (equatorToMinPaths hp) = ContinuousMap.id _ := by
      ext u : 1
      exact minPathsToEquator_equatorToMinPaths hp u
    rw [this]
  right_inv := by
    classical
    refine ⟨{
      toFun := fun x => if (x.1 : ℝ) < 1 then equatorToMinPaths hp (minPathsToEquator hp x.2)
        else x.2
      continuous_toFun := PathSp.continuous_of_edist_eq_zero continuous_snd fun x => ?_
      map_zero_left := fun γ => by simp
      map_one_left := fun γ => by simp }⟩
    split_ifs
    · exact edist_equatorToMinPaths_minPathsToEquator hp x.2
    · exact edist_self _

/-- **Lemma A** (Milnor p. 119, "`Ω^{π²}` … can be identified with the equator"): the semicircles
give a homeomorphism of the equator onto `Ω^d`, up to the identification of paths agreeing on
`[0, 1]` (the separation quotient of Milnor's pseudometric). -/
def sphMinPathsHomeomorph (hp : p ∈ Sph (n + 1)) :
    equator p ≃ₜ SeparationQuotient (minPaths (Sph (n + 1)) p (-p)) where
  toFun u := SeparationQuotient.mk (equatorToMinPaths hp u)
  invFun := SeparationQuotient.lift (minPathsToEquator hp) fun _ _ h =>
    (h.map (minPathsToEquator hp).continuous).eq
  left_inv u := by
    simp only [SeparationQuotient.lift_mk]
    exact minPathsToEquator_equatorToMinPaths hp u
  right_inv := SeparationQuotient.surjective_mk.forall.2 fun γ => by
    simp only [SeparationQuotient.lift_mk]
    exact SeparationQuotient.mk_eq_mk.2
      (EMetric.inseparable_iff.2 (edist_equatorToMinPaths_minPathsToEquator hp γ))
  continuous_toFun := SeparationQuotient.continuous_mk.comp (equatorToMinPaths hp).continuous
  continuous_invFun := SeparationQuotient.continuous_lift (minPathsToEquator hp).continuous

end Morse
