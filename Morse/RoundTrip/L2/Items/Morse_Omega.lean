import Morse
import RoundTrip.L2.Blind.Morse_Omega

/-! Layer-2 check of `Morse.Omega` (Milnor p. 136: `Ω₀(n) = O(n)`, `Ω_{k+1}(n)` the complex
structures anticommuting with `J 1, …, J k`) against the blind textbook definition. Both index the
fixed structures from `1` exactly as Milnor (`Ω_{k+1}` uses `J 1, …, J k`) and impose no standing
hypothesis on the sequence `J`; they differ only in how anticommutation is written
(`J α J' = −J' J α` versus `J' J α = −J α J'`), which is the same equation. -/

namespace RoundTrip.L2.Morse_Omega

theorem agree {n : Type*} [Fintype n] [DecidableEq n] (J : ℕ → Matrix n n ℝ) (k : ℕ) :
    Morse.Omega J k = T J k := by
  cases k with
  | zero => rfl
  | succ k =>
    ext K
    simp only [Morse.Omega, T, Morse.IsComplexStructure, IsCplxStr, Set.mem_ofPred_eq]
    refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun _ =>
      ⟨fun h => by rw [h, neg_neg], fun h => by rw [h, neg_neg]⟩)

end RoundTrip.L2.Morse_Omega
