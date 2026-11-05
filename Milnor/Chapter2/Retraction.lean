import Mathlib

/-!
# Milnor's Lemma 6 (§2, p. 14): the retraction built from a fixed-point-free map

Given a map `P` of the closed unit disk to itself with no fixed point, Milnor defines
`u(x) = (x - P x)/‖x - P x‖`, `t(x) = -⟪x, u⟫ + √(1 - ‖x‖² + ⟪x, u⟫²)` and `f(x) = x + t(x) u(x)`,
the point where the ray from `P x` through `x` leaves the disk, and says it is "easy to verify"
that `f` is a smooth retraction of the disk onto its boundary sphere.  This file is the
verification: on the open set `good P` where the formulas make sense, `f` is smooth, has norm one,
and fixes the sphere; and the disk is contained in `good P` whenever `P` has no fixed point there.
Everything here is calculus in a real inner product space; no manifolds.
-/

open Set Metric
open scoped RealInnerProductSpace ContDiff

noncomputable section

namespace Milnor
namespace Retraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unit vector from `P x` toward `x`. -/
def uVec (P : E → E) (x : E) : E := ‖x - P x‖⁻¹ • (x - P x)

/-- The radicand `1 - ‖x‖² + ⟪x, u⟫²`. -/
def rad (P : E → E) (x : E) : ℝ := 1 - ‖x‖ ^ 2 + ⟪x, uVec P x⟫ ^ 2

/-- The parameter `t(x)`. -/
def tVal (P : E → E) (x : E) : ℝ := -⟪x, uVec P x⟫ + Real.sqrt (rad P x)

/-- The retraction `f(x) = x + t(x) u(x)`. -/
def retr (P : E → E) (x : E) : E := x + tVal P x • uVec P x

/-- The open set on which the formulas are smooth. -/
def good (P : E → E) : Set E := {x | x ≠ P x ∧ 0 < rad P x}

variable {P : E → E}

theorem norm_uVec {x : E} (hx : x ≠ P x) : ‖uVec P x‖ = 1 := by
  have h : x - P x ≠ 0 := sub_ne_zero.2 hx
  rw [uVec, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]

theorem inner_uVec (x : E) : ⟪x, uVec P x⟫ = ‖x - P x‖⁻¹ * (‖x‖ ^ 2 - ⟪x, P x⟫) := by
  rw [uVec, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq]

/-- On `good P`, the retraction has norm one. -/
theorem norm_retr {x : E} (hx : x ∈ good P) : ‖retr P x‖ = 1 := by
  obtain ⟨hne, hrad⟩ := hx
  set a := ⟪x, uVec P x⟫ with ha
  set s := Real.sqrt (rad P x) with hs
  have hs2 : s ^ 2 = rad P x := Real.sq_sqrt hrad.le
  have hu : ‖uVec P x‖ = 1 := norm_uVec hne
  have hsq : ‖retr P x‖ ^ 2 = 1 := by
    have ht : tVal P x = -a + s := rfl
    have hr : rad P x = 1 - ‖x‖ ^ 2 + a ^ 2 := rfl
    rw [hr] at hs2
    rw [retr, norm_add_sq_real, inner_smul_right, norm_smul, hu, mul_one, Real.norm_eq_abs, sq_abs,
      ← ha, ht]
    linear_combination hs2
  have h0 : 0 ≤ ‖retr P x‖ := norm_nonneg _
  rw [← Real.sqrt_sq h0, hsq, Real.sqrt_one]

/-- On the unit sphere, if `‖P x‖ ≤ 1`, the retraction fixes `x`. -/
theorem retr_eq_self {x : E} (hx : x ∈ good P) (hx1 : ‖x‖ = 1) (hP : ‖P x‖ ≤ 1) :
    retr P x = x := by
  obtain ⟨hne, hrad⟩ := hx
  have ha : 0 ≤ ⟪x, uVec P x⟫ := by
    rw [inner_uVec, hx1, one_pow]
    apply mul_nonneg (inv_nonneg.2 (norm_nonneg _))
    have := real_inner_le_norm x (P x)
    rw [hx1, one_mul] at this
    linarith
  have hrad' : rad P x = ⟪x, uVec P x⟫ ^ 2 := by
    show 1 - ‖x‖ ^ 2 + ⟪x, uVec P x⟫ ^ 2 = _
    rw [hx1]; ring
  have ht : tVal P x = 0 := by
    show -⟪x, uVec P x⟫ + Real.sqrt (rad P x) = 0
    rw [hrad', Real.sqrt_sq ha]; ring
  rw [retr, ht, zero_smul, add_zero]

/-- `P` maps the disk to itself and has no fixed point on it: then the disk lies in `good P`. -/
theorem closedBall_subset_good (hP : ∀ x ∈ closedBall (0 : E) 1, P x ∈ closedBall (0 : E) 1)
    (hfix : ∀ x ∈ closedBall (0 : E) 1, P x ≠ x) : closedBall (0 : E) 1 ⊆ good P := by
  intro x hx
  have hx1 : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hx
  have hPx : ‖P x‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hP x hx
  refine ⟨fun h => hfix x hx h.symm, ?_⟩
  show 0 < 1 - ‖x‖ ^ 2 + ⟪x, uVec P x⟫ ^ 2
  have h1 : 0 ≤ 1 - ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
  have h2 : 0 ≤ ⟪x, uVec P x⟫ ^ 2 := sq_nonneg _
  by_contra hcon
  have hcon' : 1 - ‖x‖ ^ 2 + ⟪x, uVec P x⟫ ^ 2 ≤ 0 := not_lt.1 hcon
  have hx1' : ‖x‖ ^ 2 = 1 := by linarith
  have ha : ⟪x, uVec P x⟫ = 0 := by nlinarith
  -- then `⟪x, P x⟫ = 1`, so `‖x - P x‖² ≤ 0`, so `P x = x`.
  rw [inner_uVec, hx1', mul_eq_zero, inv_eq_zero, norm_eq_zero, sub_eq_zero] at ha
  rcases ha with h | h
  · exact hfix x hx h.symm
  · have hin : ⟪x, P x⟫ = 1 := by linarith
    have hsq : ‖x - P x‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, P x⟫ + ‖P x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm]
      ring
    have hle : ‖x - P x‖ ^ 2 ≤ 0 := by
      rw [hsq, hx1', hin]; nlinarith [norm_nonneg (P x), hPx]
    have h0 : ‖x - P x‖ = 0 := by nlinarith [norm_nonneg (x - P x)]
    exact hfix x hx (sub_eq_zero.1 (norm_eq_zero.1 h0)).symm

/-- `good P` is open when `P` is continuous. -/
theorem isOpen_good (hP : Continuous P) : IsOpen (good P) := by
  have hne : IsOpen {x : E | x ≠ P x} :=
    isOpen_ne_fun continuous_id hP
  have hcont : ContinuousOn (rad P) {x : E | x ≠ P x} := by
    intro x hx
    have h0 : x - P x ≠ 0 := sub_ne_zero.2 hx
    have hsub : ContinuousAt (fun y => y - P y) x := (continuous_id.sub hP).continuousAt
    have hnorm : ContinuousAt (fun y => ‖y - P y‖⁻¹) x :=
      (hsub.norm).inv₀ (norm_ne_zero_iff.2 h0)
    have hu : ContinuousAt (uVec P) x := hnorm.smul hsub
    have hinner : ContinuousAt (fun y => ⟪y, uVec P y⟫) x := continuousAt_id.inner hu
    exact ((continuousAt_const.sub (continuousAt_id.norm.pow 2)).add (hinner.pow 2)).continuousWithinAt
  have heq : good P = {x : E | x ≠ P x} ∩ rad P ⁻¹' Ioi 0 := by
    ext x; simp [good]
  rw [heq]
  exact hcont.isOpen_inter_preimage (t := Ioi (0 : ℝ)) hne isOpen_Ioi

/-- The retraction is smooth on `good P` when `P` is smooth. -/
theorem contDiffOn_retr (hP : ContDiff ℝ ∞ P) : ContDiffOn ℝ ∞ (retr P) (good P) := by
  intro x hx
  obtain ⟨hne, hrad⟩ := hx
  have h0 : x - P x ≠ 0 := sub_ne_zero.2 hne
  have hsub : ContDiffAt ℝ ∞ (fun y => y - P y) x := (contDiff_id.sub hP).contDiffAt
  have hnorm : ContDiffAt ℝ ∞ (fun y => ‖y - P y‖⁻¹) x := (hsub.norm ℝ h0).inv (norm_ne_zero_iff.2 h0)
  have hu : ContDiffAt ℝ ∞ (uVec P) x := hnorm.smul hsub
  have hinner : ContDiffAt ℝ ∞ (fun y => ⟪y, uVec P y⟫) x := contDiffAt_id.inner ℝ hu
  have hradc : ContDiffAt ℝ ∞ (rad P) x :=
    (contDiffAt_const.sub (contDiffAt_id.norm_sq ℝ)).add (hinner.pow 2)
  have hsqrt : ContDiffAt ℝ ∞ (fun y => Real.sqrt (rad P y)) x := hradc.sqrt hrad.ne'
  have ht : ContDiffAt ℝ ∞ (tVal P) x := hinner.neg.add hsqrt
  exact ((contDiffAt_id.add (ht.smul hu)) : ContDiffAt ℝ ∞ (retr P) x).contDiffWithinAt

end Retraction
end Milnor
