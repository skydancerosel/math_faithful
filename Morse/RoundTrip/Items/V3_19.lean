import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V3_19

open Module
open scoped ContDiff Manifold

namespace RoundTrip.V3_19

/-- The project's statement: the seven listed theorems (`Morse.tangentialGradient` is a
definition), universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.inner_tangentialGradient.{0, 0, 0} ∧
  type_of% @Morse.tangentialGradient_eq_zero_iff.{0, 0, 0} ∧
  type_of% @Morse.contMDiff_tangentialGradient ∧
  type_of% @Morse.index_hessT ∧
  type_of% @Morse.bijective_dvT_tangentialGradient ∧
  type_of% @Morse.indexN_tangentialGradient ∧
  type_of% @Morse.sgn_det_eq_neg_one_pow_index.{0}

theorem A_holds : A :=
  ⟨@Morse.inner_tangentialGradient.{0, 0, 0}, @Morse.tangentialGradient_eq_zero_iff.{0, 0, 0},
    @Morse.contMDiff_tangentialGradient, @Morse.index_hessT,
    @Morse.bijective_dvT_tangentialGradient, @Morse.indexN_tangentialGradient,
    @Morse.sgn_det_eq_neg_one_pow_index.{0}⟩

/-- `A` with the proof argument `contMDiff_tangentialGradient hN hNc hne hF` (which occurs *inside
the statements* of `bijective_dvT_tangentialGradient` and `indexN_tangentialGradient`) replaced by
an arbitrary proof `hv` of the same proposition. By proof irrelevance this is the same statement
(`A_iff_A'`); it is needed only because `#rt_check` follows the constants of `A`'s own statement,
which contains the banned `Morse.contMDiff_tangentialGradient` as a proof term. -/
def A' : Prop :=
  type_of% @Morse.inner_tangentialGradient.{0, 0, 0} ∧
  type_of% @Morse.tangentialGradient_eq_zero_iff.{0, 0, 0} ∧
  type_of% @Morse.contMDiff_tangentialGradient ∧
  type_of% @Morse.index_hessT ∧
  (∀ {K d m : ℕ} {N : Set (Rn (K + 1))}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) N)
    (hNc : IsCompact N) (hne : N.Nonempty) {F : Rn (K + 1) → ℝ} (_hF : ContDiff ℝ ∞ F) {q : N}
    (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) ∞
      (Morse.tangentialGradient hN F))
    (hvq : Morse.tangentialGradient hN F q = 0),
    (letI := hN.chartedSpace; Morse.IsNondegenerate (Morse.hessianM (Rn (d + 1)) (F ∘ Subtype.val) q)) →
    (letI := hN.chartedSpace
     Function.Bijective (Milnor.Tub.dvT hN hNc hne (Morse.tangentialGradient hN F) hv
        (Morse.isTangent_tangentialGradient hN F) q hvq) ∧
      Milnor.sgn (LinearMap.det (Milnor.Tub.dvT hN hNc hne (Morse.tangentialGradient hN F) hv
        (Morse.isTangent_tangentialGradient hN F) q hvq)) =
        (-1) ^ Morse.indexM (Rn (d + 1)) (F ∘ Subtype.val) q)) ∧
  (∀ {K d m : ℕ} {N : Set (Rn (K + 1))}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) N)
    (hNc : IsCompact N) (hne : N.Nonempty), 0 < K →
    ∀ {F : Rn (K + 1) → ℝ} (_hF : ContDiff ℝ ∞ F) {q : N}
    (hv : letI := hN.chartedSpace; ContMDiff 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) ∞
      (Morse.tangentialGradient hN F)),
    (letI := hN.chartedSpace; Morse.IsNondegenerateCriticalPointM (Rn (d + 1)) (F ∘ Subtype.val) q) →
    (letI := hN.chartedSpace
     Milnor.Tub.indexN hN hNc hne (Morse.tangentialGradient hN F) hv q =
      (-1) ^ Morse.indexM (Rn (d + 1)) (F ∘ Subtype.val) q)) ∧
  type_of% @Morse.sgn_det_eq_neg_one_pow_index.{0}

/-- `A` and `A'` are the same statement up to proof irrelevance. -/
theorem A_iff_A' : A ↔ A' := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨h1, h2, h3, h4, ?_, ?_, h7⟩
    · intro K d m N hN hNc hne F hF q hv hvq hnd
      exact h5 hN hNc hne hF hvq hnd
    · intro K d m N hN hNc hne hK F hF q hv hq
      exact h6 hN hNc hne hK hF hq
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨h1, h2, h3, h4, ?_, ?_, h7⟩
    · intro K d m N hN hNc hne F hF q hvq hnd
      exact h5 hN hNc hne hF _ hvq hnd
    · intro K d m N hN hNc hne hK F hF q hq
      exact h6 hN hNc hne hK hF _ hq

theorem A'_to_B : A' → B := by
  intro hA K d m N hN hc hne
  let _ := hN.chartedSpace
  intro Φ hΦ hv q hq
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact (RoundTrip.Glue.no_sliceSubmanifold_R1 hN hc hne).elim
  have hΦ' : ContDiff ℝ ∞ Φ := contMDiff_iff_contDiff.1 hΦ
  exact hA.2.2.2.2.2.1 hN hc hne hK hΦ' hv hq

theorem A_to_B : A → B := fun h ↦ A'_to_B (A_iff_A'.1 h)

/- `#rt_check` on `A_to_B` itself necessarily reports `Morse.contMDiff_tangentialGradient`: that
theorem occurs as a proof term inside the *statement* `A` (in the types of
`bijective_dvT_tangentialGradient` and `indexN_tangentialGradient`), and the check follows the
constants of the binder type `A`. The proof content is checked on `A'_to_B`. -/
#rt_check RoundTrip.V3_19.A'_to_B [Morse.inner_tangentialGradient,
  Morse.tangentialGradient_eq_zero_iff, Morse.contMDiff_tangentialGradient, Morse.index_hessT,
  Morse.bijective_dvT_tangentialGradient, Morse.indexN_tangentialGradient,
  Morse.sgn_det_eq_neg_one_pow_index]

end RoundTrip.V3_19
