import Morse
import RoundTrip.Check
import RoundTrip.Blind.V5_11

open Complex Module
open scoped ContDiff Manifold

namespace RoundTrip.V5_11

/-- The project's statement (universes instantiated at 0): in a holomorphic chart `w : V → F`
(`C²` over `ℂ` at `q`), the Hessian of `z ↦ ‖w z − p‖²` at `q` has index `≤ dim_ℂ V`. -/
def A : Prop := type_of% @Morse.index_hessian_normSq_sub_holomorphic_le.{0,0}

theorem A_holds : A := @Morse.index_hessian_normSq_sub_holomorphic_le

/-- Clauses (1)–(3) of B hold, from project theorems outside the item (Lemma 6.6 existence of a
Morse `L_p`, compact sublevels of a closed `M`, and the geometric index bound
`Morse.indexM_normSq_sub_le`); clause (4), a *Mathlib* `CWComplex`, is what is missing. -/
theorem B_clauses_123 {K D m k : ℕ} (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn D) (Rn m) M)
    {J : Rn (K + 1) →L[ℝ] Rn (K + 1)} (hJ : Morse.IsOrthComplexStructure J)
    (hc : Morse.IsComplexSubmanifold hM J) (hcl : IsClosed M) (hD : D = 2 * k) :
    letI := hM.chartedSpace
    ∃ p : Rn (K + 1),
      (∀ q : M, Morse.IsCriticalPointM (Rn D) (fun y : M => Lp p y.1) q →
        Morse.IsNondegenerateCriticalPointM (Rn D) (fun y : M => Lp p y.1) q) ∧
      (∀ a : ℝ, IsCompact {q : M | Lp p q.1 ≤ a}) ∧
      (∀ q : M, Morse.IsCriticalPointM (Rn D) (fun y : M => Lp p y.1) q →
        Morse.indexM (Rn D) (fun y : M => Lp p y.1) q ≤ k) := by
  subst hD
  let _ := hM.chartedSpace
  obtain ⟨p, hp⟩ := Morse.exists_isMorseFunction_normSq_sub (hM := hM)
  exact ⟨p, fun q hq => hp.isNondegenerateCriticalPointM hq,
    fun a => Morse.isCompact_sublevel_normSq_sub hcl p a,
    fun q hq => Morse.indexM_normSq_sub_le hM hJ hc p q hq⟩

/-- B ⇒ A holds only because A is provable outright (the project's short computation, re-done from
`Morse.hessian_normSq_sub_holomorphic` and `Morse.index_le_finrank_complex`); B, about a global
cell structure, says nothing about Hessians in a chart. -/
theorem B_to_A : B → A := by
  intro _ V _ _ _ F _ _ w q hw p
  refine Morse.index_le_finrank_complex _ fun v => ?_
  rw [Morse.hessian_normSq_sub_holomorphic hw, Morse.hessian_normSq_sub_holomorphic hw]
  have h1 : Morse.reInner (fderiv ℂ w q (I • v)) (fderiv ℂ w q (I • v)) =
      Morse.reInner (fderiv ℂ w q v) (fderiv ℂ w q v) := by
    rw [map_smul, Morse.reInner_I_smul]
  have h2 : Morse.reInner (w q - p) (fderiv ℂ (fderiv ℂ w) q (I • v) (I • v)) =
      -Morse.reInner (w q - p) (fderiv ℂ (fderiv ℂ w) q v v) := by
    simp only [map_smul, smul_apply, smul_smul, I_mul_I, neg_one_smul, map_neg]
  rw [h1, h2, Morse.reInner_self]
  nlinarith [sq_nonneg ‖fderiv ℂ w q v‖]

#rt_check RoundTrip.V5_11.B_to_A [Morse.index_hessian_normSq_sub_holomorphic_le]
#rt_check RoundTrip.V5_11.B_clauses_123 [Morse.index_hessian_normSq_sub_holomorphic_le]
#rt_overlap RoundTrip.V5_11.B_to_A [Morse.index_hessian_normSq_sub_holomorphic_le]

end RoundTrip.V5_11
