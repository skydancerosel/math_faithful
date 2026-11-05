import Morse
import RoundTrip.L2.Blind.Morse_IsAngleLift

/-! Layer-2 check of `Morse.IsAngleLift` (`θ 0 = 0` and `F(ω t) = e^{iθ(t)}`) against the blind
textbook definition (the continuous angle of a path in `ℂ ∖ 0`: `θ 0 = 0` and
`F(ω t) = |F(ω t)| e^{i(arg F(ω 0) + θ(t))}`). The project's notion is the special case of a loop
in the unit circle starting at `1`: exactly, `P ↔ T ∧ |F ∘ ω| = 1 on [0, 1] ∧ F(ω 0) = 1`. This is
the only case Milnor needs (p. 147: `f(J') = det_ℂ(J⁻¹J') ∈ S¹` and `f(J) = 1`). Outside it the
project's predicate is false while the textbook's angle exists (e.g. `F ≡ 2`, `θ = 0`). -/

namespace RoundTrip.L2.Morse_IsAngleLift

open scoped unitInterval

/-- **Exact characterisation**: the project's angle is the textbook's angle of a path in the unit
circle starting at `1`. -/
theorem agree_iff {V : Type*} (F : V → ℂ) (ω : ℝ → V) (θ : C(I, ℝ)) :
    Morse.IsAngleLift F ω θ ↔ T F ω θ ∧ (∀ t : I, ‖F (ω t)‖ = 1) ∧ F (ω 0) = 1 := by
  constructor
  · rintro ⟨h0, hF⟩
    have hn : ∀ t : I, ‖F (ω t)‖ = 1 := fun t => by
      rw [hF t]; exact Complex.norm_exp_ofReal_mul_I (θ t)
    have h1 : F (ω 0) = 1 := by
      have := hF 0
      rw [h0, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at this
      simpa using this
    refine ⟨⟨h0, fun t => ?_⟩, hn, h1⟩
    rw [hn t, h1, Complex.arg_one, zero_add, Complex.ofReal_one, one_mul]
    exact hF t
  · rintro ⟨⟨h0, hF⟩, hn, h1⟩
    refine ⟨h0, fun t => ?_⟩
    have := hF t
    rwa [hn t, h1, Complex.arg_one, zero_add, Complex.ofReal_one, one_mul] at this

/-- Agreement for Milnor's case: `|F ∘ ω| = 1` on `[0, 1]` and `F(ω 0) = 1`. -/
theorem agree_of {V : Type*} (F : V → ℂ) (ω : ℝ → V) (θ : C(I, ℝ))
    (hn : ∀ t : I, ‖F (ω t)‖ = 1) (h1 : F (ω 0) = 1) : Morse.IsAngleLift F ω θ ↔ T F ω θ :=
  (agree_iff F ω θ).trans ⟨fun h => h.1, fun h => ⟨h, hn, h1⟩⟩

/-- The project's predicate always implies the textbook's. -/
theorem P_imp_T {V : Type*} (F : V → ℂ) (ω : ℝ → V) (θ : C(I, ℝ)) :
    Morse.IsAngleLift F ω θ → T F ω θ :=
  fun h => ((agree_iff F ω θ).1 h).1

/-- `F ≡ 2` (a constant path off the unit circle) has the textbook angle `θ = 0`, but no
project angle. -/
theorem differ :
    T (fun _ : Unit => (2 : ℂ)) (fun _ => ()) 0 ∧
      ¬ Morse.IsAngleLift (fun _ : Unit => (2 : ℂ)) (fun _ => ()) 0 := by
  refine ⟨⟨rfl, fun t => ?_⟩, fun h => ?_⟩
  · simp
  · have := ((agree_iff _ _ _).1 h).2.2
    norm_num at this

end RoundTrip.L2.Morse_IsAngleLift
