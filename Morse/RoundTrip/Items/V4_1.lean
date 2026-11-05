import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V4_1

open Module
open scoped ContDiff Manifold

namespace RoundTrip.V4_1

/-- The project's statement: the four listed theorems (`normalBundleSet`, `normalEnd` are
definitions); no universe parameters. -/
def A : Prop :=
  type_of% @Milnor.Problems.isSliceSubmanifold_normalBundle ∧
  type_of% @Morse.mem_normalBundleSet_iff ∧
  type_of% @Morse.slice_dim_add_eq_of_nonempty ∧
  type_of% @Morse.normalEnd_id

theorem A_holds : A :=
  ⟨@Milnor.Problems.isSliceSubmanifold_normalBundle, @Morse.mem_normalBundleSet_iff,
    @Morse.slice_dim_add_eq_of_nonempty, @Morse.normalEnd_id⟩

/-- B's normal bundle is the project's (`Milnor.Tub.tanN` is the range of `mfd val`). -/
theorem NSet_eq {K d m : ℕ} {M : Set (Rn (K + 1))}
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) M) :
    NSet hM = Milnor.Problems.normalBundleSet hM := rfl

/-- A ⇒ B. For nonempty `M`, `d + 1 + m = K + 1` (A's `slice_dim_add_eq_of_nonempty`) and A's
`isSliceSubmanifold_normalBundle` gives a slice structure on `N` with complement `ℝᵐ × ℝ^{d+1}`,
moved to complement `ℝ^{K+1}` by `Glue.isSliceSubmanifold_congr_complement`; for empty `M`, `N` is
empty. Smoothness of `E|N` holds for every slice structure (`E` is linear, `val` smooth). -/
theorem A_to_B : A → B := by
  intro hA K d m M hM _
  have hNN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) (Rn (K + 1)) (Rn (K + 1))
      (NSet hM) := by
    rcases M.eq_empty_or_nonempty with hempty | hne
    · intro p hp
      obtain ⟨hq, -⟩ := hp
      rw [hempty] at hq
      exact absurd hq (Set.notMem_empty _)
    · have hdim : d + 1 + m = K + 1 := hA.2.2.1 hM hne
      have h0 := hA.1 hM hdim
      have hfr : finrank ℝ (Rn m × Rn (d + 1)) = finrank ℝ (Rn (K + 1)) := by
        simp only [finrank_prod, finrank_euclideanSpace_fin]
        omega
      exact Glue.isSliceSubmanifold_congr_complement h0 (ContinuousLinearEquiv.ofFinrankEq hfr)
  refine ⟨hNN, ?_⟩
  let _ := hNN.chartedSpace
  have h2 : ContMDiff 𝓘(ℝ, Rn (K + 1) × Rn (K + 1)) 𝓘(ℝ, Rn (K + 1)) ∞
      (fun q : Rn (K + 1) × Rn (K + 1) => q.1 + q.2) :=
    (contDiff_fst.add contDiff_snd).contMDiff
  exact h2.comp hNN.contMDiff_val

/-! `B_to_A` is not proved: B gives a slice structure on `N` only for `M` of dimension `d + 1 ≥ 1`
and codimension `K - d ≥ 1` (hypothesis `d < K`), while A's `isSliceSubmanifold_normalBundle` covers
every slice submanifold of `ℝᵏ` (dimension `0`, codimension `0` included). B also has nothing
corresponding to the dimension count `k + w = n` (`slice_dim_add_eq_of_nonempty`); the other two
clauses are restatements (`mem_normalBundleSet_iff`, `normalEnd_id` is `rfl`). -/

#rt_check RoundTrip.V4_1.A_to_B [Milnor.Problems.isSliceSubmanifold_normalBundle,
  Morse.mem_normalBundleSet_iff, Morse.slice_dim_add_eq_of_nonempty, Morse.normalEnd_id]

end RoundTrip.V4_1
