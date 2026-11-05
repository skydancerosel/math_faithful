import Morse
import RoundTrip.Check
import RoundTrip.Blind.V1_12

open scoped ContDiff Manifold

namespace RoundTrip.V1_12

/-- The project's statement: the types of the listed theorems (the examples live on `ℝ` and
`ℝ × ℝ`, with the vector-space notions `Morse.IsCriticalPoint`/`Morse.hessian`), universes
instantiated at `0`. -/
def A : Prop :=
  (type_of% @Morse.Examples.cube_degenerate) ∧
  (type_of% @Morse.Examples.isCriticalPoint_cube_iff) ∧
  (type_of% @Morse.Examples.hessian_cube) ∧
  (type_of% @Morse.Examples.monkey_degenerate) ∧
  (type_of% @Morse.Examples.isCriticalPoint_monkey_iff) ∧
  (type_of% @Morse.Examples.isCriticalPoint_sqFst_iff) ∧
  (type_of% @Morse.Examples.not_isNondegenerate_sqFst) ∧
  (type_of% @Morse.Examples.isCriticalPoint_sqMul_iff) ∧
  (type_of% @Morse.Examples.not_isNondegenerate_sqMul) ∧
  (type_of% @Morse.not_isNondegenerate_of_frequently.{0})

theorem A_holds : A :=
  ⟨Morse.Examples.cube_degenerate, Morse.Examples.isCriticalPoint_cube_iff,
    Morse.Examples.hessian_cube, Morse.Examples.monkey_degenerate,
    Morse.Examples.isCriticalPoint_monkey_iff, Morse.Examples.isCriticalPoint_sqFst_iff,
    @Morse.Examples.not_isNondegenerate_sqFst, Morse.Examples.isCriticalPoint_sqMul_iff,
    @Morse.Examples.not_isNondegenerate_sqMul, @Morse.not_isNondegenerate_of_frequently.{0}⟩

/-- `B` is false: its clause (d) asserts that the critical set of `(x, y) ↦ x²` is the
x-axis `{y = 0}` (Milnor's words read literally), but `(1, 0)` lies on the x-axis and is not a
critical point (the derivative in the `x` direction is `2`). -/
theorem not_B : ¬ B := by
  intro hB
  have hset := hB.2.2.2.1.1
  let p : P := EuclideanSpace.single 0 1
  have hp : p ∈ {p : P | p 1 = 0} := by simp [p]
  rw [← hset] at hp
  have hcrit : mfderiv 𝓘(ℝ, P) 𝓘(ℝ, ℝ) (fun q : P => q 0 ^ 2) p = 0 := hp
  rw [mfderiv_eq_fderiv] at hcrit
  have hl : HasFDerivAt (fun q : P => q 0) (EuclideanSpace.proj (0 : Fin 2) : P →L[ℝ] ℝ) p :=
    (EuclideanSpace.proj (0 : Fin 2) : P →L[ℝ] ℝ).hasFDerivAt
  have h2 := (hl.pow 2).fderiv
  rw [h2] at hcrit
  have := congrArg (fun L : P →L[ℝ] ℝ => L p) hcrit
  simp [p] at this
  exact two_ne_zero (α := ℝ) this

theorem B_to_A : B → A := fun h => (not_B h).elim

#rt_check RoundTrip.V1_12.B_to_A [Morse.Examples.cube_degenerate,
  Morse.Examples.isCriticalPoint_cube_iff, Morse.Examples.hessian_cube,
  Morse.Examples.monkey_degenerate, Morse.Examples.isCriticalPoint_monkey_iff,
  Morse.Examples.isCriticalPoint_sqFst_iff, Morse.Examples.not_isNondegenerate_sqFst,
  Morse.Examples.isCriticalPoint_sqMul_iff, Morse.Examples.not_isNondegenerate_sqMul,
  Morse.not_isNondegenerate_of_frequently]
#rt_overlap RoundTrip.V1_12.B_to_A [Morse.Examples.cube_degenerate,
  Morse.Examples.isCriticalPoint_cube_iff, Morse.Examples.hessian_cube,
  Morse.Examples.monkey_degenerate, Morse.Examples.isCriticalPoint_monkey_iff,
  Morse.Examples.isCriticalPoint_sqFst_iff, Morse.Examples.not_isNondegenerate_sqFst,
  Morse.Examples.isCriticalPoint_sqMul_iff, Morse.Examples.not_isNondegenerate_sqMul,
  Morse.not_isNondegenerate_of_frequently]

end RoundTrip.V1_12
