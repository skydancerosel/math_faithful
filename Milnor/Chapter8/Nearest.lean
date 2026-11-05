import Milnor.Chapter8.NormalBundle
import Milnor.Chapter8.Retraction

/-!
# Problem 12, first part: the retraction `r(x + v) = x` picks the nearest point

Milnor §8, Problem 12: "Define `r : N_ε → M` by `r(x + v) = x`. Show that `r(x + v)` is closer to
`x + v` than any other point of `M`."

With the radius `normalε` of Problem 11 (`NormalBundle.lean`), for `(x, v)` in the normal bundle
with `‖v‖ < ε` the nearest-point retraction of Chapter 6 satisfies `r(x + v) = x`
(`normalRetraction_eq`), and the nearest point is strictly nearer than any other point of `M`
(`tubr_dist_lt`, `Retraction.lean`). The second part of Problem 12 (the analogue of Problem 4 for
maps into `M`) is `exists_smooth_approx_mfld` and `smoothHomotopic_of_homotopic_mfld` in
`Retraction.lean`.
-/

open Set Metric
open scoped ContDiff Manifold

noncomputable section

namespace Milnor

namespace Problems

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty) (hmk : m + w = K + 1)

/-- **Problem 12, the retraction.** For `(x, v)` in the normal bundle with `‖v‖ < ε`, the
retraction satisfies `r(x + v) = x`, and `x` is strictly closer to `x + v` than any other point
of `M`. -/
theorem normalRetraction_nearest (q : normalBundleSet hM)
    (hq : q ∈ normalTube hM (normalε hM hMc hne hmk)) :
    (Tub.tubr hM hMc hne (q.1.1 + q.1.2)).1 = q.1.1 ∧
      ∀ z ∈ M, z ≠ q.1.1 → ‖(q.1.1 + q.1.2) - q.1.1‖ < ‖(q.1.1 + q.1.2) - z‖ := by
  have hr := normalRetraction_eq hM hMc hne hmk q hq
  refine ⟨hr, fun z hz hzx => ?_⟩
  obtain ⟨hx, -⟩ := q.2
  have hv : ‖q.1.2‖ < normalε hM hMc hne hmk := hq
  have hy : infDist (q.1.1 + q.1.2) M < Tub.tubε hM hMc hne := by
    calc infDist (q.1.1 + q.1.2) M ≤ dist (q.1.1 + q.1.2) q.1.1 := infDist_le_dist_of_mem hx
      _ = ‖q.1.2‖ := by rw [dist_eq_norm, add_sub_cancel_left]
      _ < normalε hM hMc hne hmk := hv
      _ ≤ Tub.tubε hM hMc hne := normalε_le_tubε hM hMc hne hmk
  have hne' : (⟨z, hz⟩ : M) ≠ Tub.tubr hM hMc hne (q.1.1 + q.1.2) := fun h => hzx (by
    have h1 := congrArg Subtype.val h
    rw [hr] at h1
    exact h1)
  have h := tubr_dist_lt hM hMc hne hy ⟨z, hz⟩ hne'
  rw [hr] at h
  exact h

end Problems

end Milnor
