import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V4_11

open Module
open scoped ContDiff Manifold

namespace RoundTrip.V4_11

/-- The project's statement: the three listed theorems; no universe parameters. -/
def A : Prop :=
  type_of% @Morse.nullityM_normSq_sub_eq_endpointNullity ∧
  type_of% @Morse.isFocalPointMult_iff ∧
  type_of% @Morse.isDegenerate_normSq_sub_iff_isFocalPoint

theorem A_holds : A :=
  ⟨@Morse.nullityM_normSq_sub_eq_endpointNullity, @Morse.isFocalPointMult_iff,
    @Morse.isDegenerate_normSq_sub_iff_isFocalPoint⟩

section Bridge

variable {K d m : ℕ} {M : Set (Rn (K + 1))}
  (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M)

include hM in
/-- The dimension count, read off a point of `M`. -/
theorem hkw_of (q : M) : d + 1 + m = K + 1 :=
  Morse.slice_dim_add_eq_of_nonempty hM ⟨q.1, q.2⟩

/-- The linear isomorphism between the complements of `hNN` and of the canonical structure. -/
noncomputable def cplx (h : d + 1 + m = K + 1) : Rn (K + 1) ≃L[ℝ] (Rn m × Rn (d + 1)) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [finrank_prod]; omega)

/-- **B's nullity of `dE` (any structure `hNN` on `N`) is the project's focal multiplicity.** -/
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

theorem isFocalOfMult_iff
    (hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1))
      (NSet hM)) (q : M) (e : Rn (K + 1)) (μ : ℕ) :
    IsFocalOfMult hNN q.1 e μ ↔ Morse.IsFocalPointMult hM (hkw_of hM q) q e μ := by
  rw [Morse.isFocalPointMult_iff_focalMult, IsFocalOfMult, nullE_eq_focalMult]
  exact and_comm

/-- The canonical structure on `N`, with complement `ℝ^{K+1}`. -/
theorem canonical (h : d + 1 + m = K + 1) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1)) (NSet hM) :=
  Glue.isSliceSubmanifold_congr_complement
    (Milnor.Problems.isSliceSubmanifold_normalBundle hM h) (cplx h).symm

end Bridge

/-- **A ⇒ B**: B's focal multiplicity (any slice structure `hNN` on `N`) is the project's
(`Glue.endpointNullity_eq_of_slice`), and then B is A's second and third clause. -/
theorem A_to_B : A → B := by
  intro hA K d m M hM hNN q p
  let _ := hM.chartedSpace
  have hkw := hkw_of hM q
  refine ⟨?_, fun μ hμ ↦ ?_⟩
  · have h3 := hA.2.2 (hM := hM) hkw p q
    simp only [Morse.IsFocalPoint, ← isFocalOfMult_iff hM hNN q] at h3
    rw [← h3]
    unfold Morse.IsNondegenerateCriticalPointM
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, fun h ↦ h2 ⟨h1, h⟩⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, fun h ↦ h2 h.2⟩⟩
  · exact ((hA.2.1 (hM := hM) hkw p q μ).1 ((isFocalOfMult_iff hM hNN q p μ).1 hμ)).2.1

/-- In dimension `0` the nullity of `dE` vanishes (the project's `endpointNullity_eq_nullity`,
a form on `ℝ⁰`). -/
theorem endpointNullity_dim0 {n w : ℕ} {M : Set (Rn n)}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn n) (Rn 0) (Rn w) M) (hkw : 0 + w = n)
    (x : Milnor.Problems.normalBundleSet hM) : Morse.endpointNullity hM hkw x = 0 := by
  rw [Morse.endpointNullity_eq_nullity, Morse.nullity]
  exact Submodule.finrank_eq_zero.2 (Subsingleton.elim _ _)

/-- **B ⇒ A**. For `k ≥ 1` apply B with the canonical structure on `N` (complement changed to
`ℝⁿ`); `k = 0` (points) separately: everything is critical and non-degenerate, nullities `0`.
Uses outside the item: `isCriticalPointM_normSq_sub_iff_mem_normalBundleSet` (V4_10, critical ↔
normal) and, for `k = 0`, `endpointNullity_eq_nullity` (V4_8). -/
theorem B_to_A : B → A := by
  intro hB
  -- the three clauses, for each `M`
  suffices H : ∀ {n k w : ℕ} {M : Set (Rn n)}
      (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn n) (Rn k) (Rn w) M) (hkw : k + w = n)
      (p : Rn n) (q : M),
      (letI := hM.chartedSpace
      ∀ h : ((q : Rn n), p - q) ∈ Milnor.Problems.normalBundleSet hM,
        Morse.nullityM (Rn k) (fun x : M => ‖(x : Rn n) - p‖ ^ 2) q =
          Morse.endpointNullity hM hkw ⟨_, h⟩) ∧
      (letI := hM.chartedSpace
      ∀ μ, Morse.IsFocalPointMult hM hkw q p μ ↔
        Morse.IsCriticalPointM (Rn k) (fun x : M => ‖(x : Rn n) - p‖ ^ 2) q ∧
          Morse.nullityM (Rn k) (fun x : M => ‖(x : Rn n) - p‖ ^ 2) q = μ ∧ 0 < μ) ∧
      (letI := hM.chartedSpace
      (Morse.IsCriticalPointM (Rn k) (fun x : M => ‖(x : Rn n) - p‖ ^ 2) q ∧
        ¬ Morse.IsNondegenerate (Morse.hessianM (Rn k) (fun x : M => ‖(x : Rn n) - p‖ ^ 2) q))
          ↔ Morse.IsFocalPoint hM hkw q p) by
    exact ⟨fun hkw p q h ↦ (H _ hkw p q).1 h, fun hkw p q μ ↦ (H _ hkw p q).2.1 μ,
      fun hkw p q ↦ (H _ hkw p q).2.2⟩
  intro n k w M hM hkw p q
  let _ := hM.chartedSpace
  have hcrit := Morse.isCriticalPointM_normSq_sub_iff_mem_normalBundleSet (hM := hM) p q
  rcases k with _ | d
  · -- dimension `0`
    have hnd : Morse.IsNondegenerate
        (Morse.hessianM (Rn 0) (fun x : M => ‖(x : Rn n) - p‖ ^ 2) q) :=
      Subsingleton.elim _ _
    have hnull : Morse.nullityM (Rn 0) (fun x : M => ‖(x : Rn n) - p‖ ^ 2) q = 0 :=
      Submodule.finrank_eq_zero.2 (Subsingleton.elim _ _)
    have hnf : ∀ μ, ¬ Morse.IsFocalPointMult hM hkw q p μ := by
      rintro μ ⟨h, hμ, hpos⟩
      rw [endpointNullity_dim0] at hμ
      omega
    refine ⟨fun h ↦ by rw [hnull, endpointNullity_dim0], fun μ ↦ ⟨fun h ↦ (hnf μ h).elim, ?_⟩,
      ⟨fun h ↦ (h.2 hnd).elim, fun ⟨μ, h⟩ ↦ (hnf μ h).elim⟩⟩
    rintro ⟨-, h1, h2⟩
    omega
  · obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨d + w, by omega⟩
    have hNN := canonical hM hkw
    have hB1 := (hB K d w M hM hNN q p).1
    have hB2 := (hB K d w M hM hNN q p).2
    simp only [isFocalOfMult_iff hM hNN q] at hB1 hB2
    -- `hkw_of hM q` and `hkw` are equal proofs
    have hfm : ∀ μ, Morse.IsFocalPointMult hM (hkw_of hM q) q p μ ↔
        Morse.IsFocalPointMult hM hkw q p μ := fun _ ↦ Iff.rfl
    simp only [hfm] at hB1 hB2
    have hdeg : (Morse.IsCriticalPointM (Rn (d + 1)) (fun x : M => ‖(x : Rn (K + 1)) - p‖ ^ 2) q ∧
        ¬ Morse.IsNondegenerate
          (Morse.hessianM (Rn (d + 1)) (fun x : M => ‖(x : Rn (K + 1)) - p‖ ^ 2) q)) ↔
        Morse.IsFocalPoint hM hkw q p := by
      rw [Morse.IsFocalPoint, ← hB1]
      unfold Morse.IsNondegenerateCriticalPointM
      exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, fun h ↦ h2 h.2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, fun h ↦ h2 ⟨h1, h⟩⟩⟩
    have hpos : ∀ μ, Morse.IsFocalPointMult hM hkw q p μ →
        Morse.nullityM (Rn (d + 1)) (fun x : M => ‖(x : Rn (K + 1)) - p‖ ^ 2) q = μ := hB2
    refine ⟨fun h ↦ ?_, fun μ ↦ ⟨fun hμ ↦ ?_, fun ⟨hc, hn, hμ⟩ ↦ ?_⟩, hdeg⟩
    · by_cases h0 : 0 < Morse.endpointNullity hM hkw ⟨_, h⟩
      · exact hpos _ ⟨h, rfl, h0⟩
      · have hnf : ¬ Morse.IsFocalPoint hM hkw q p := by
          rintro ⟨μ, h', hμ, hp⟩
          exact h0 (hμ ▸ hp)
        have hc := hcrit.2 h
        have hnd : Morse.IsNondegenerate
            (Morse.hessianM (Rn (d + 1)) (fun x : M => ‖(x : Rn (K + 1)) - p‖ ^ 2) q) := by
          by_contra hn
          exact hnf (hdeg.1 ⟨hc, hn⟩)
        rw [Morse.nullityM, (Morse.isNondegenerate_iff_nullity_eq_zero).1 hnd]
        omega
    · obtain ⟨h, -, hp⟩ := id hμ
      exact ⟨hcrit.2 h, hpos μ hμ, hp⟩
    · have hn' : ¬ Morse.IsNondegenerate
          (Morse.hessianM (Rn (d + 1)) (fun x : M => ‖(x : Rn (K + 1)) - p‖ ^ 2) q) := by
        intro hnd
        rw [Morse.nullityM, (Morse.isNondegenerate_iff_nullity_eq_zero).1 hnd] at hn
        omega
      obtain ⟨μ', hμ'⟩ := hdeg.1 ⟨hc, hn'⟩
      have := hpos μ' hμ'
      rw [hn] at this
      exact this ▸ hμ'

#rt_check RoundTrip.V4_11.A_to_B [Morse.nullityM_normSq_sub_eq_endpointNullity,
  Morse.isFocalPointMult_iff, Morse.isDegenerate_normSq_sub_iff_isFocalPoint]
#rt_check RoundTrip.V4_11.B_to_A [Morse.nullityM_normSq_sub_eq_endpointNullity,
  Morse.isFocalPointMult_iff, Morse.isDegenerate_normSq_sub_iff_isFocalPoint]
#rt_overlap RoundTrip.V4_11.B_to_A [Morse.nullityM_normSq_sub_eq_endpointNullity,
  Morse.isFocalPointMult_iff, Morse.isDegenerate_normSq_sub_iff_isFocalPoint]

end RoundTrip.V4_11
