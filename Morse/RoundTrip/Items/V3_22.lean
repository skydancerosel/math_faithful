import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_22

open Module
open scoped ContDiff Manifold

namespace RoundTrip.V3_22

/-- The project's statement: the six listed theorems (`Morse.torus`, `Morse.Torus.poly` are
definitions). -/
def A : Prop :=
  type_of% @Morse.Torus.mem_torus_iff ∧
  type_of% @Morse.Torus.dpoly_ne_zero ∧
  type_of% @Morse.Torus.isRegularValue_poly1 ∧
  type_of% @Morse.isSliceSubmanifold_torus ∧
  type_of% @Morse.isCompact_torus ∧
  type_of% @Morse.Torus.finrank_tangentSubspace_torus

theorem A_holds : A :=
  ⟨@Morse.Torus.mem_torus_iff, @Morse.Torus.dpoly_ne_zero, @Morse.Torus.isRegularValue_poly1,
    @Morse.isSliceSubmanifold_torus, @Morse.isCompact_torus,
    @Morse.Torus.finrank_tangentSubspace_torus⟩

/-- Vocabulary: B's torus is the project's `Morse.torus`. -/
theorem torus_eq (R r : ℝ) : torus R r = Morse.torus R r := rfl

/-- The lowest point of the torus (not in `A`; elementary). -/
theorem lowest {R r : ℝ} (hr : 0 < r) {x : Rn 3} (hx : x ∈ torus R r) :
    -(R + r) ≤ x 0 ∧ (x 0 = -(R + r) → x = pP R r) := by
  have h : (Real.sqrt (x 0 ^ 2 + x 1 ^ 2) - R) ^ 2 + x 2 ^ 2 = r ^ 2 := hx
  set s := Real.sqrt (x 0 ^ 2 + x 1 ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = x 0 ^ 2 + x 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hsle : s ≤ R + r := by nlinarith [sq_nonneg (x 2), sq_nonneg (s - R - r)]
  have hx0 : |x 0| ≤ s := Real.abs_le_sqrt (by nlinarith [sq_nonneg (x 1)])
  have hlow : -(R + r) ≤ x 0 := by linarith [neg_abs_le (x 0)]
  refine ⟨hlow, fun he ↦ ?_⟩
  have hsR : s = R + r := by
    rw [he, abs_neg] at hx0
    linarith [le_abs_self (R + r)]
  have h2 : x 2 = 0 := by
    rw [hsR] at h
    nlinarith [sq_nonneg (x 2)]
  have h1 : x 1 = 0 := by
    rw [hsR, he] at hss
    nlinarith [sq_nonneg (x 1)]
  ext i
  fin_cases i
  · simp [pP, he]
  · simp [pP, h1]
  · simp [pP, h2]

/-- `A` with the proof `isSliceSubmanifold_torus hr hrR` inside the statement of
`finrank_tangentSubspace_torus` generalized to any proof `hT` (the same statement by proof
irrelevance, `A_iff_A'`); needed because `#rt_check` follows the constants of `A`'s statement. -/
def A' : Prop :=
  type_of% @Morse.Torus.mem_torus_iff ∧
  type_of% @Morse.Torus.dpoly_ne_zero ∧
  type_of% @Morse.Torus.isRegularValue_poly1 ∧
  type_of% @Morse.isSliceSubmanifold_torus ∧
  type_of% @Morse.isCompact_torus ∧
  ∀ {R r : ℝ}, 0 < r → r < R →
    ∀ (hT : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn 3) (Rn 2) (Rn 1) (Morse.torus R r))
      (q : Morse.torus R r), finrank ℝ (Morse.tangentSubspace hT q) = 2

theorem A_iff_A' : A ↔ A' := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, fun hr hrR _ q ↦ h6 hr hrR q⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, fun hr hrR q ↦ h6 hr hrR _ q⟩

theorem A'_to_B : A' → B := by
  intro hA R r hr hrR
  exact ⟨hA.2.2.2.2.1 hr hrR, hA.2.2.2.1 hr hrR, fun x hx ↦ (lowest hr hx).1,
    fun x hx ↦ ⟨(lowest hr hx).2, fun h ↦ by subst h; simp [pP]⟩⟩

theorem A_to_B : A → B := fun h ↦ A'_to_B (A_iff_A'.1 h)

/- `#rt_check` on `A_to_B` itself reports the four theorems behind the proof term
`isSliceSubmanifold_torus hr hrR` occurring in the statement `A`; the proof is checked on
`A'_to_B`. -/
#rt_check RoundTrip.V3_22.A'_to_B [Morse.Torus.mem_torus_iff, Morse.Torus.dpoly_ne_zero,
  Morse.Torus.isRegularValue_poly1, Morse.isSliceSubmanifold_torus, Morse.isCompact_torus,
  Morse.Torus.finrank_tangentSubspace_torus]

end RoundTrip.V3_22
