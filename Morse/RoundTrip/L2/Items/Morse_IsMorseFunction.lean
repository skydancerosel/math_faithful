import Morse
import RoundTrip.L2.Blind.Morse_IsMorseFunction

/-! Layer-2 check of `Morse.IsMorseFunction` (a structure: `C^∞`, and every critical point has a
non-degenerate Hessian) against the blind textbook definition (the same two conjuncts): same
smoothness, same criticality, same Hessian (the extended chart of the model `𝓘(ℝ, E)` is the
preferred chart) and the same non-degeneracy. -/

namespace RoundTrip.L2.Morse_IsMorseFunction

theorem hessianM_eq (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) :
    Morse.hessianM E f p = hess E f p := by
  simp only [Morse.hessianM, Morse.hessian, Morse.localRep, hess, Morse.extChartAt_self_coe,
    Morse.extChartAt_self_coe_symm]

theorem agree (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) :
    Morse.IsMorseFunction E f ↔ T E f := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun p hp => ?_⟩
    have := h2 p hp
    rwa [hessianM_eq, Morse.isNondegenerate_iff] at this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun p hp => ?_⟩
    rw [hessianM_eq, Morse.isNondegenerate_iff]
    exact h2 p hp

end RoundTrip.L2.Morse_IsMorseFunction
