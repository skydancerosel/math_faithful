import Morse
import RoundTrip.Check
import RoundTrip.Blind.V5_10

open Complex Module
open scoped ContDiff Manifold

namespace RoundTrip.V5_10

/-- The project's statement: the three listed index bounds (pure linear algebra on a complex
vector space; universes instantiated at 0). -/
def A : Prop :=
  type_of% @Morse.index_le_finrank_of_eq_sub_re.{0} ∧
    type_of% @Morse.index_le_finrank_of_hermitian.{0} ∧
    type_of% @Morse.index_hessian_le_finrank_complex.{0}

theorem A_holds : A :=
  ⟨@Morse.index_le_finrank_of_eq_sub_re, @Morse.index_le_finrank_of_hermitian,
    @Morse.index_hessian_le_finrank_complex⟩

/-- B with the model dimension generalized, from the project's geometric index bound
`Morse.indexM_normSq_sub_le` (outside the item). -/
theorem key2 {K D m k : ℕ} (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn D) (Rn m) M)
    {J : Rn (K + 1) →L[ℝ] Rn (K + 1)} (hJ : Morse.IsOrthComplexStructure J)
    (hc : Morse.IsComplexSubmanifold hM J) (hD : D = 2 * k) (p : Rn (K + 1)) :
    letI := hM.chartedSpace
    ∀ q : M, Morse.IsCriticalPointM (Rn D) (fun y : M => Lp p y.1) q →
      Morse.indexM (Rn D) (fun y : M => Lp p y.1) q ≤ k := by
  subst hD
  intro q hq
  exact Morse.indexM_normSq_sub_le hM hJ hc p q hq

theorem key {K d m k : ℕ} (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)
    (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) (hJ : IsCplxStr J) (hc : IsCplxSub hM J)
    (hD : d + 1 = 2 * k) (p : Rn (K + 1)) :
    letI := hM.chartedSpace
    ∀ q : M, Morse.IsCriticalPointM (Rn (d + 1)) (fun y : M => Lp p y.1) q →
      Morse.indexM (Rn (d + 1)) (fun y : M => Lp p y.1) q ≤ k :=
  key2 M hM (J := (J.toContinuousLinearEquiv : Rn (K + 1) →L[ℝ] Rn (K + 1)))
    ⟨fun v => hJ v, fun v w => J.inner_map_map v w⟩ (fun q v hv => hc q v hv) hD p

/-- A ⇒ B holds only because B is a theorem of the project outside A
(`Morse.indexM_normSq_sub_le`, via `Morse.two_mul_indexM_normSq_sub_le`): A, an index bound for
abstract bilinear forms `G − Re B` on a complex vector space, is not used. -/
theorem A_to_B : A → B := by
  intro _ K d m k M hM J hJ hc hdk p q hq _
  exact key M hM J hJ hc hdk p q hq

/-- B ⇒ A holds only because A is provable outright (the project's short algebraic proof,
re-done from `Morse.index_le_finrank_complex` and `Morse.apply_J_apply_J_eq`); B, about the
specific functions `L_p` on complex submanifolds, does not give bounds for arbitrary forms. -/
theorem B_to_A : B → A := by
  intro _
  have h1 : type_of% @Morse.index_le_finrank_of_eq_sub_re.{0} := by
    intro V _ _ _ H G B hG hGI hH
    refine Morse.index_le_finrank_complex H fun v => ?_
    have h := Morse.apply_J_apply_J_eq H G (Morse.reBilin B) (I • ·) (by simpa using hH) hGI
      (fun v => Morse.reBilin_I_smul B v v) v
    linarith [hG v]
  refine ⟨h1, ?_, ?_⟩
  · intro V _ _ _ H B hH
    exact h1 H Morse.reInner B (fun v => by rw [Morse.reInner_self]; positivity)
      (fun v => Morse.reInner_I_smul v v) (fun v => by rw [hH, Morse.reInner_self])
  · intro V _ _ _ f q G B hG hGI hf
    exact h1 _ G B hG hGI hf

#rt_check RoundTrip.V5_10.A_to_B [Morse.index_le_finrank_of_eq_sub_re, Morse.index_le_finrank_of_hermitian, Morse.index_hessian_le_finrank_complex]
#rt_check RoundTrip.V5_10.B_to_A [Morse.index_le_finrank_of_eq_sub_re, Morse.index_le_finrank_of_hermitian, Morse.index_hessian_le_finrank_complex]
#rt_overlap RoundTrip.V5_10.B_to_A [Morse.index_le_finrank_of_eq_sub_re, Morse.index_le_finrank_of_hermitian, Morse.index_hessian_le_finrank_complex]

end RoundTrip.V5_10
