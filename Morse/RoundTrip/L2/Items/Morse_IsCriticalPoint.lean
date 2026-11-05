import Morse
import RoundTrip.L2.Blind.Morse_IsCriticalPoint

/-! Layer-2 check of `Morse.IsCriticalPoint` (`HasFDerivAt f 0 p`: differentiable with derivative
`0`) against the blind textbook definition (`fderiv ℝ f p = 0`). The project's notion always implies
the blind one and is equivalent to it where `f` is differentiable (in particular for the textbook's
smooth `f`); at a non-differentiable point Mathlib's junk `fderiv = 0` makes the blind notion true
and the project's false (`|x|` at `0`). -/

namespace RoundTrip.L2.Morse_IsCriticalPoint

theorem P_imp_T {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (p : E) :
    Morse.IsCriticalPoint f p → T f p :=
  fun h => h.fderiv_eq

/-- Agreement exactly when the blind notion forces differentiability, in particular wherever `f`
is differentiable. -/
theorem agree_of {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (p : E)
    (hf : DifferentiableAt ℝ f p) : Morse.IsCriticalPoint f p ↔ T f p :=
  Morse.isCriticalPoint_iff hf

/-- The two notions agree at `p` iff the blind one implies differentiability at `p`. -/
theorem agree_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (p : E) :
    (Morse.IsCriticalPoint f p ↔ T f p) ↔ (T f p → DifferentiableAt ℝ f p) := by
  constructor
  · intro h hT
    exact (h.2 hT).differentiableAt
  · intro h
    exact ⟨P_imp_T f p, fun hT => (Morse.isCriticalPoint_iff (h hT)).2 hT⟩

/-- `|x|` at `0`: not differentiable, so `fderiv` is the junk value `0`. -/
theorem differ : ¬ (Morse.IsCriticalPoint (fun x : ℝ => |x|) 0 ↔ T (fun x : ℝ => |x|) 0) := by
  have hT : T (fun x : ℝ => |x|) 0 :=
    fderiv_zero_of_not_differentiableAt not_differentiableAt_abs_zero
  intro h
  exact not_differentiableAt_abs_zero (h.2 hT).differentiableAt

end RoundTrip.L2.Morse_IsCriticalPoint
