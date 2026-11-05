import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V4_23

open Module
open scoped ContDiff Manifold

namespace RoundTrip.V4_23

/-- The project's statement: the three listed theorems; no universe parameters. -/
def A : Prop :=
  type_of% @Morse.index_firstFF_sub_secondFF ∧
  type_of% @Morse.indexM_normSq_sub_eq_card ∧
  type_of% @Morse.indexM_normSq_sub_eq_finsum_focalMult

theorem A_holds : A :=
  ⟨@Morse.index_firstFF_sub_secondFF, @Morse.indexM_normSq_sub_eq_card,
    @Morse.indexM_normSq_sub_eq_finsum_focalMult⟩

section Bridge

variable {K d m : ℕ} {M : Set (Rn (K + 1))}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)

include hM in
theorem hkw_of (q : M) : d + 1 + m = K + 1 :=
  Morse.slice_dim_add_eq_of_nonempty hM ⟨q.1, q.2⟩

noncomputable def cplx (h : d + 1 + m = K + 1) : Rn (K + 1) ≃L[ℝ] (Rn m × Rn (d + 1)) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [finrank_prod]; omega)

/-- **B's nullity of `dE` (any structure `hNN` on `N`) is the project's focal multiplicity**
(`Glue.endpointNullity_eq_of_slice`). -/
theorem nullE_eq_focalMult
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1))
      (NSet hM)) (q : M) (e : Rn (K + 1)) :
    nullE hNN (q.1, e - q.1) = Morse.focalMult hM (hkw_of hM q) q e := by
  unfold nullE Morse.focalMult
  by_cases h : ((q : Rn (K + 1)), e - q) ∈ NSet hM
  · rw [dif_pos h, dif_pos (show ((q : Rn (K + 1)), e - q) ∈ Milnor.Problems.normalBundleSet hM
      from h)]
    exact (Glue.endpointNullity_eq_of_slice hM (hkw_of hM q) hNN (cplx (hkw_of hM q)) _).symm
  · rw [dif_neg h, dif_neg (show ((q : Rn (K + 1)), e - q) ∉ Milnor.Problems.normalBundleSet hM
      from h)]

end Bridge

/-- **A ⇒ B**: B's multiplicities are the project's `focalMult` (structure independence of the
nullity of `dE`, `Glue.endpointNullity_eq_of_slice`); the index formula is A's third clause.
B's finiteness clause is not in A: it uses the project's `isFocalPoint_add_smul_iff` (V4_7, focal
points on the normal line are `q + K⁻¹ v`, `K` an eigenvalue of the shape operator) and
`isCriticalPointM_normSq_sub_iff_mem_normalBundleSet` (V4_10). -/
theorem A_to_B : A → B := by
  intro hA K d m M hM hNN q p hcrit hnd
  let _ := hM.chartedSpace
  have hkw := hkw_of hM q
  have he : ∀ s : ℝ, nullE hNN (q.1, s • (p - q.1)) =
      Morse.focalMult hM hkw q (q.1 + s • (p - q.1)) := by
    intro s
    have := nullE_eq_focalMult hM hNN q (q.1 + s • (p - q.1))
    rwa [add_sub_cancel_left] at this
  simp only [he]
  refine ⟨?_, hA.2.2 hM hkw p q hnd⟩
  -- finiteness
  have hmem := (Morse.isCriticalPointM_normSq_sub_iff_mem_normalBundleSet (hM := hM) p q).1 hcrit
  obtain ⟨hq, hv⟩ := (Morse.mem_normalBundleSet_iff hM).1 hmem
  refine ((Module.End.finite_hasEigenvalue
    (Morse.shapeOp hM q (p - q.1) : Module.End ℝ (Morse.tanSpace hM q))).image (·⁻¹)).subset ?_
  rintro s ⟨-, hs⟩
  have hf : Morse.IsFocalPoint hM hkw q (q.1 + s • (p - q.1)) :=
    (Morse.isFocalPoint_iff_focalMult_pos hM hkw q _).2 hs
  obtain ⟨Kc, -, hK, rfl⟩ := (Morse.isFocalPoint_add_smul_iff hM hkw q hv s).1 hf
  exact ⟨Kc, hK, rfl⟩

/-! `B_to_A` is not proved, and is genuinely weaker: B is only the third clause of A
(`indexM = Σ focal multiplicities` at a NON-DEGENERATE critical point, `dim M ≥ 1`). A also
states, in the project's parametrization, that `index (g − ℓ_v) = #{principal curvatures > 1}` for
EVERY `v ∈ ℝⁿ` (`index_firstFF_sub_secondFF`, pure linear algebra of the shape operator, no
critical point) and `indexM L_p = #{principal curvatures of p − q that are > 1}` at EVERY critical
point, degenerate ones included (`indexM_normSq_sub_eq_card`). B has no principal curvatures and
nothing at degenerate critical points, so it cannot give these. -/

#rt_check RoundTrip.V4_23.A_to_B [Morse.index_firstFF_sub_secondFF,
  Morse.indexM_normSq_sub_eq_card, Morse.indexM_normSq_sub_eq_finsum_focalMult]

end RoundTrip.V4_23
