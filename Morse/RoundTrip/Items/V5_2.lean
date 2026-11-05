import Morse
import RoundTrip.Check
import RoundTrip.Blind.V5_2

open Module Complex
open scoped ContDiff Manifold

namespace RoundTrip.V5_2

/-- The project's statement: the three listed theorems (`reBilin`, `reInner`, `realMulI`,
`complexStructureEquiv` are definitions), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.reBilin_apply.{0} ∧
  type_of% @Morse.reBilin_I_smul.{0} ∧
  type_of% @Morse.reInner_I_smul.{0}

theorem A_holds : A := ⟨@Morse.reBilin_apply.{0}, @Morse.reBilin_I_smul.{0}, @Morse.reInner_I_smul.{0}⟩

section Coord

variable {k : ℕ}

/-- Multiplication by `i` in real coordinates: `(x, y) ↦ (-y, x)`. -/
noncomputable def Tfun (w : R2 k) : R2 k :=
  WithLp.toLp 2 (Sum.elim (fun h => -w (Sum.inr h)) (fun h => w (Sum.inl h)))

noncomputable def Tinv (w : R2 k) : R2 k :=
  WithLp.toLp 2 (Sum.elim (fun h => w (Sum.inr h)) (fun h => -w (Sum.inl h)))

noncomputable def Tlin : R2 k ≃ₗ[ℝ] R2 k where
  toFun := Tfun
  invFun := Tinv
  map_add' x y := by ext (a | a) <;> simp [Tfun] <;> ring
  map_smul' c x := by ext (a | a) <;> simp [Tfun]
  left_inv w := by ext (a | a) <;> simp [Tfun, Tinv]
  right_inv w := by ext (a | a) <;> simp [Tfun, Tinv]

/-- It is orthogonal. -/
noncomputable def T : R2 k ≃ₗᵢ[ℝ] R2 k :=
  Tlin.isometryOfInner fun x y ↦ by
    simp only [PiLp.inner_apply, Fintype.sum_sum_type]
    simp [Tlin, Tfun, add_comm]

theorem toC_T (w : R2 k) : toC (T w) = fun h => I * toC w h := by
  funext h
  apply Complex.ext <;> simp [toC, T, Tlin, Tfun]

/-- The complex bilinear form `B(z, z') = Σ b_{hj} z^h z'^j` on `ℂᵏ`. -/
noncomputable def Bform (b : Matrix (Fin k) (Fin k) ℂ) :
    (Fin k → ℂ) →L[ℂ] (Fin k → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((Fin k → ℂ) →ₗ[ℂ] ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ
      Matrix.toLinearMap₂' ℂ b)

theorem Bform_apply (b : Matrix (Fin k) (Fin k) ℂ) (z : Fin k → ℂ) : Bform b z z = Qc b z := by
  simp only [Bform, Qc, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
    Function.comp_apply, LinearEquiv.coe_coe, Matrix.toLinearMap₂'_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun h _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end Coord

/-- **A ⇒ B.** (2) is A's `reBilin_I_smul` (and `reBilin_apply`) for the bilinear form of `b` on
`ℂᵏ`, with `T = ` multiplication by `i` in real coordinates. (1) is the complex identity
`Q(iz) = -Q(z)`, of which A states only the real part; it is proved directly (`i² = -1`). -/
theorem A_to_B : A → B := by
  intro hA k b
  refine ⟨fun z ↦ ?_, T, fun w ↦ ?_⟩
  · simp only [Qc, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun h _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    linear_combination (b h j * z h * z j) * I_mul_I
  · have h2 := hA.2.1 (V := Fin k → ℂ) (Bform b) (toC w) (toC w)
    rw [hA.1, hA.1] at h2
    have hI : (I • toC w : Fin k → ℂ) = toC (T w) := by
      rw [toC_T]; rfl
    rw [hI, Bform_apply, Bform_apply] at h2
    exact h2

/-- **B ⇒ A**, by proving A outright (B, about `ℂᵏ` in coordinates, says nothing about an
arbitrary complex normed space `V`, possibly infinite-dimensional): the three identities are
one-line computations (`i · i = -1`, `conj i · i = 1`). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨fun B v w ↦ ?_, fun B v w ↦ ?_, fun v w ↦ ?_⟩
  · simp [Morse.reBilin]
  · simp [Morse.reBilin, ← mul_assoc]
  · change (inner ℂ (I • v) (I • w)).re = (inner ℂ v w).re
    rw [inner_smul_left, inner_smul_right, ← mul_assoc, conj_I, neg_mul, I_mul_I, neg_neg, one_mul]

#rt_check RoundTrip.V5_2.A_to_B [Morse.reBilin_apply, Morse.reBilin_I_smul, Morse.reInner_I_smul]
#rt_check RoundTrip.V5_2.B_to_A [Morse.reBilin_apply, Morse.reBilin_I_smul, Morse.reInner_I_smul]
#rt_overlap RoundTrip.V5_2.B_to_A [Morse.reBilin_apply, Morse.reBilin_I_smul, Morse.reInner_I_smul]

end RoundTrip.V5_2
