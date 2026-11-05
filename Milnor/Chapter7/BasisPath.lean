import Milnor.Chapter7.GLplus
import Milnor.Chapter7.Transition

/-!
# Smooth paths of bases

Two bases `b`, `b'` of `ℝᵖ` with the same orientation are joined by a smooth path of bases,
constant near the ends of `[0,1]` (`exists_basisPath`).
-/

open Matrix Finset Function Module
open scoped ContDiff

noncomputable section

namespace Milnor

namespace GLp

variable {p : ℕ}

/-- The tuple `j ↦ ∑ᵢ M i j • b i`. -/
def mulTuple (M : Matrix (Fin p) (Fin p) ℝ) (b : Fin p → EuclideanSpace ℝ (Fin p)) :
    Fin p → EuclideanSpace ℝ (Fin p) := fun j => ∑ i, M i j • b i

theorem mulTuple_one (b : Fin p → EuclideanSpace ℝ (Fin p)) : mulTuple 1 b = b := by
  funext j
  simp [mulTuple, Matrix.one_apply]

/-- `mulTuple M b` is linearly independent when `b` is and `M` is invertible. -/
theorem linearIndependent_mulTuple {b : Fin p → EuclideanSpace ℝ (Fin p)}
    (hb : LinearIndependent ℝ b) {M : Matrix (Fin p) (Fin p) ℝ} (hM : det M ≠ 0) :
    LinearIndependent ℝ (mulTuple M b) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∑ j, g j • mulTuple M b j = ∑ i, (M.mulVec g) i • b i := by
    simp only [mulTuple, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  rw [key] at hg
  have h0 : M.mulVec g = 0 := funext ((Fintype.linearIndependent_iff.1 hb) _ hg)
  have := Matrix.eq_zero_of_mulVec_eq_zero hM h0
  exact fun i => congrFun this i

/-- **Paths of bases.**  If `det A > 0`, the tuple `mulTuple A b` is joined to `b` by a smooth
path of linearly independent tuples, constant near the ends of `[0,1]`. -/
theorem exists_basisPath {b : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    {A : Matrix (Fin p) (Fin p) ℝ} (hA : 0 < det A) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ B : ℝ → Fin p → EuclideanSpace ℝ (Fin p), ContDiff ℝ ∞ B ∧
      (∀ t, t ≤ ε → B t = mulTuple A b) ∧ (∀ t, 1 - ε ≤ t → B t = b) ∧
      ∀ t, LinearIndependent ℝ (B t) := by
  obtain ⟨G, hGs, hG0, hG1, hGdet⟩ := exists_glPath A hA
  obtain ⟨ρ, hρs, hρ0, hρ1, hρ01, -⟩ := exists_timeTransition hε hε'
  refine ⟨fun t => mulTuple (G (ρ t)) b, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_pi]
    intro j
    exact ContDiff.sum fun i _ => ((hGs i j).comp hρs).smul contDiff_const
  · intro t ht; simp [hρ0 t ht, hG0]
  · intro t ht; simp [hρ1 t ht, hG1, mulTuple_one]
  · intro t
    exact linearIndependent_mulTuple hb (hGdet (ρ t) (hρ01 t).1 (hρ01 t).2).ne'

/-- Two bases with the same orientation are related by a matrix of positive determinant. -/
theorem exists_det_pos_of_orientation_eq (e e' : Basis (Fin p) ℝ (EuclideanSpace ℝ (Fin p)))
    (h : e.orientation = e'.orientation) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ, 0 < det A ∧ mulTuple A e = e' := by
  refine ⟨e.toMatrix e', ?_, ?_⟩
  · rw [← Basis.det_apply]; exact (Basis.orientation_eq_iff_det_pos e e').1 h
  · funext j
    simp only [mulTuple, Basis.toMatrix_apply]
    exact e.sum_repr (e' j)

end GLp

end Milnor
