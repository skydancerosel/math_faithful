import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_2

open Module Function
open scoped ContDiff Manifold

namespace RoundTrip.V4_2

/-- The project's statement: the three listed theorems (`endpointNullity`, `IsFocalPointMult`,
`IsFocalPoint`, `focalSet` are definitions); no universe parameters. -/
def A : Prop :=
  type_of% @Morse.endpointNullity_pos_iff ∧
  type_of% @Morse.isFocalPoint_iff ∧
  type_of% @Morse.focalSet_eq_image_critPoints

theorem A_holds : A :=
  ⟨@Morse.endpointNullity_pos_iff, @Morse.isFocalPoint_iff, @Morse.focalSet_eq_image_critPoints⟩

/-- For an endomorphism of `ℝⁿ`: nontrivial kernel ↔ not surjective. -/
lemma finrank_ker_pos_iff {n : ℕ} (L : Rn n →L[ℝ] Rn n) :
    0 < finrank ℝ (LinearMap.ker (L : Rn n →ₗ[ℝ] Rn n)) ↔ ¬ Surjective L := by
  have : Surjective L ↔ Surjective (L : Rn n →ₗ[ℝ] Rn n) := Iff.rfl
  rw [this, ← LinearMap.injective_iff_surjective, Nat.pos_iff_ne_zero, Ne,
    Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]

/-- **B holds outright**, for every slice structure `hNN` on `N`: it is the same rank–nullity
unpacking as A's `endpointNullity_pos_iff` / `focalSet_eq_image_critPoints`, done for `hNN`
instead of the project's canonical structure `isSliceSubmanifold_normalBundle hM hkw`. -/
theorem B_holds : B := by
  intro K d m M hM hNN
  let _ := hNN.chartedSpace
  ext e
  constructor
  · rintro ⟨q, μ, hμ, hnull⟩
    have hmem : (q, e - q) ∈ NSet hM := by
      by_contra h
      simp [nullE, h] at hnull
      omega
    refine ⟨(q, e - q), ⟨hmem, ?_⟩, by simp [endpt]⟩
    rw [nullE, dif_pos hmem] at hnull
    exact (finrank_ker_pos_iff _).1 (hnull ▸ hμ)
  · rintro ⟨p, ⟨hp, hns⟩, rfl⟩
    have hpe : (p.1, endpt p - p.1) = p := by simp [endpt]
    refine ⟨p.1, nullE hNN p, ?_, by rw [hpe]⟩
    rw [nullE, dif_pos hp]
    exact (finrank_ker_pos_iff _).2 hns

/-- A ⇒ B: B is true outright (`B_holds`); A is not needed. -/
theorem A_to_B : A → B := fun _ ↦ B_holds

#rt_check RoundTrip.V4_2.A_to_B [Morse.endpointNullity_pos_iff, Morse.isFocalPoint_iff,
  Morse.focalSet_eq_image_critPoints]

/-- B ⇒ A, by re-proving A outright (B is about an arbitrary structure `hNN` on `N ⊆ ℝ^{K+1}`,
`dim M ≥ 1`; A about the canonical structure on the normal bundle of any `M ⊆ ℝⁿ`; transferring
would need the uniqueness of the smooth structure of an embedded submanifold, which costs more
than the three statements themselves). The proofs are the same rank–nullity unpacking. -/
theorem B_to_A : B → A := by
  intro _
  have h1 : type_of% @Morse.endpointNullity_pos_iff := by
    intro n k w M hM hkw x
    let := (Milnor.Problems.isSliceSubmanifold_normalBundle hM hkw).chartedSpace
    exact finrank_ker_pos_iff _
  have h2 : type_of% @Morse.isFocalPoint_iff := by
    intro n k w M hM hkw q e
    constructor
    · rintro ⟨μ, h, hμ, hpos⟩
      exact ⟨h, (h1 hM hkw _).1 (hμ ▸ hpos)⟩
    · rintro ⟨h, hc⟩
      exact ⟨_, h, rfl, (h1 hM hkw _).2 hc⟩
  refine ⟨h1, h2, ?_⟩
  intro n k w M hM hkw
  let := (Milnor.Problems.isSliceSubmanifold_normalBundle hM hkw).chartedSpace
  ext e
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨h, hc⟩ := (h2 hM hkw q e).1 hq
    refine ⟨_, hc, ?_⟩
    change (q : Rn n) + (e - q) = e
    abel
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Morse.footPoint hM x, (h2 hM hkw _ _).2 ?_⟩
    have hx' : (((Morse.footPoint hM x : M) : Rn n),
        Milnor.Problems.normalSum hM x - (Morse.footPoint hM x : Rn n)) = x.1 := by
      change (x.1.1, x.1.1 + x.1.2 - x.1.1) = x.1
      rw [add_sub_cancel_left]
    have hmem : (((Morse.footPoint hM x : M) : Rn n),
        Milnor.Problems.normalSum hM x - (Morse.footPoint hM x : Rn n)) ∈
        Milnor.Problems.normalBundleSet hM := hx' ▸ x.2
    refine ⟨hmem, ?_⟩
    have hxx : (⟨_, hmem⟩ : Milnor.Problems.normalBundleSet hM) = x := Subtype.ext hx'
    rw [hxx]
    exact hx

#rt_check RoundTrip.V4_2.B_to_A [Morse.endpointNullity_pos_iff, Morse.isFocalPoint_iff,
  Morse.focalSet_eq_image_critPoints]
#rt_overlap RoundTrip.V4_2.B_to_A [Morse.endpointNullity_pos_iff, Morse.isFocalPoint_iff,
  Morse.focalSet_eq_image_critPoints]

end RoundTrip.V4_2
