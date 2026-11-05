import Morse
import RoundTrip.Check
import RoundTrip.Glue
import RoundTrip.Blind.V4_21

open Module Set
open scoped ContDiff Manifold

namespace RoundTrip.V4_21

/-- The project's statement: the five listed theorems (`ballDiffeo` is a definition), universes
instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.exists_isMorseFunction_approx.{0} ∧
  type_of% @Morse.isSliceSubmanifold_ballImage ∧
  type_of% @Morse.isMorseFunction_of_ballImage ∧
  type_of% @Morse.ae_isMorseFunction_add_inner_ballDiffeo ∧
  type_of% @Morse.exists_isMorseFunction_approx_uniform.{0}

theorem A_holds : A :=
  ⟨@Morse.exists_isMorseFunction_approx.{0}, @Morse.isSliceSubmanifold_ballImage,
    @Morse.isMorseFunction_of_ballImage, @Morse.ae_isMorseFunction_add_inner_ballDiffeo,
    @Morse.exists_isMorseFunction_approx_uniform.{0}⟩

/-- `A` with the proof `isSliceSubmanifold_ballImage hM`, which occurs in the statement of
`isMorseFunction_of_ballImage` (the chart structure on `β(M)`), replaced by a bound variable `hB`
(same statement by proof irrelevance, `A_iff_A'`); `#rt_check` runs on `A'_to_B`. -/
def A' : Prop :=
  type_of% @Morse.exists_isMorseFunction_approx.{0} ∧
  type_of% @Morse.isSliceSubmanifold_ballImage ∧
  (∀ {n k w : ℕ} {M : Set (Rn n)} (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn n) (Rn k) (Rn w) M)
    (hB : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn n) (Rn k) (Rn w)
      ((Morse.ballDiffeo n).toPartialEquiv '' M))
    {g : M → ℝ} {g' : (Morse.ballDiffeo n).toPartialEquiv '' M → ℝ},
    (letI := hM.chartedSpace; ContMDiff 𝓘(ℝ, Rn k) 𝓘(ℝ, ℝ) ∞ g) →
    (∀ x, g' (Morse.toBall x) = g x) →
    (letI := hB.chartedSpace; Morse.IsMorseFunction (Rn k) g') →
    (letI := hM.chartedSpace; Morse.IsMorseFunction (Rn k) g)) ∧
  type_of% @Morse.ae_isMorseFunction_add_inner_ballDiffeo ∧
  type_of% @Morse.exists_isMorseFunction_approx_uniform.{0}

theorem A_iff_A' : A ↔ A' :=
  ⟨fun h ↦ ⟨h.1, h.2.1, fun hM _ _ _ hg hgg hm ↦ h.2.2.1 hM hg hgg hm, h.2.2.2⟩,
    fun h ↦ ⟨h.1, h.2.1, fun hM _ _ hg hgg hm ↦ h.2.2.1 hM (h.2.1 hM) hg hgg hm, h.2.2.2⟩⟩

/-- **A ⇒ B**: A's `exists_isMorseFunction_approx_uniform` (any slice submanifold, `f` need not be
bounded) with `ι = Fin r`, `y_j = φ_j`, `K_j = φ_j(C_j)`; B bounds the difference of the
derivatives, A the derivatives of the difference (`Glue.iteratedFDeriv_sub_comp_symm`). -/
theorem A'_to_B : A' → B := by
  intro hA K d m M hM f hf _ ε hε k r φ hφ C hC
  let _ := hM.chartedSpace
  have := hM.isManifold
  have hy : ∀ j, Morse.IsSmoothCoord (Rn (d + 1)) (φ j) := fun j ↦
    Morse.isSmoothCoord_of_mem_maximalAtlas (hφ j)
  obtain ⟨g, hg, hgf, hder⟩ := hA.2.2.2.2 hM hf (ι := Fin r) φ hy (fun j ↦ φ j '' C j)
    (fun j ↦ (hC j).1.image_of_continuousOn ((φ j).continuousOn.mono (hC j).2))
    (fun j ↦ (image_mono (hC j).2).trans (φ j).image_source_subset) k hε
  refine ⟨g, hg.contMDiff, fun q hq ↦ hg.isNondegenerateCriticalPointM hq, hgf, ?_⟩
  intro j i hi u hu
  have hut : u ∈ (φ j).target := (image_mono (hC j).2).trans (φ j).image_source_subset hu
  rw [← Glue.iteratedFDeriv_sub_comp_symm (hy j) hf hg.contMDiff hut]
  exact hder j i hi u hu

theorem A_to_B : A → B := fun h ↦ A'_to_B (A_iff_A'.1 h)

/-! `B_to_A` is not proved, and is genuinely weaker. B is the existence of approximations of a
BOUNDED smooth `f` on `M ⊆ ℝ^{K+1}` (dim ≥ 1). A drops boundedness (`approx_uniform`) and also
contains the steps of Milnor's proof as theorems: `ballDiffeo` (`ℝⁿ ≅` open unit ball) maps slice
submanifolds to slice submanifolds and Morse functions back to Morse functions, and for almost
every `a`, `f + ⟪a, ballDiffeo(·)⟫` is a Morse function (`ae_isMorseFunction_add_inner_ballDiffeo`).
None of these follows from B: the first two are about an arbitrary image under a specific
diffeomorphism of `ℝⁿ`, the third is a measure statement, and B does not cover unbounded `f`
(whether the unbounded case follows from the bounded one is not obvious: approximating `arctan ∘ f`
loses uniform control of `f`). -/

#rt_check RoundTrip.V4_21.A'_to_B [Morse.exists_isMorseFunction_approx,
  Morse.isSliceSubmanifold_ballImage, Morse.isMorseFunction_of_ballImage,
  Morse.ae_isMorseFunction_add_inner_ballDiffeo, Morse.exists_isMorseFunction_approx_uniform]

end RoundTrip.V4_21
