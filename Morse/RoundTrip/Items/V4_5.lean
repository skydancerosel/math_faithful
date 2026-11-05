import Morse
import RoundTrip.Check
import RoundTrip.Blind.V4_5

open Module Function
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V4_5

/-- The listed declarations (`xParam`, `uParam`, `dParam`, `d2Param`, `firstFF`, `secondFF`,
`normalForm`) are all definitions: A is the empty conjunction. -/
def A : Prop := True

theorem A_holds : A := trivial

section Calc

variable {k n : ℕ}

/-- `∂²x/∂uⁱ∂uʲ` is the second derivative applied to `(eᵢ, eⱼ)`. -/
lemma d2x_eq {x : Rn k → Rn n} {u : Rn k} (hx : DifferentiableAt ℝ (fderiv ℝ x) u) (i j : Fin k) :
    d2x x u i j = fderiv ℝ (fderiv ℝ x) u (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  unfold d2x dx
  rw [fderiv_clm_apply hx (differentiableAt_const _)]
  simp

lemma dx_mem_tangSp (x : Rn k → Rn n) (u : Rn k) (l : Fin k) : dx x u l ∈ tangSp x u :=
  Submodule.subset_span ⟨l, rfl⟩

end Calc

/-- **B holds outright** (Mathlib only): the Gram matrix of independent vectors is positive
definite (`Matrix.posDef_gram_of_linearIndependent`), the second derivative of a `C²` map is
symmetric (`ContDiffAt.isSymmSndFDerivAt`), and the orthogonal projection lands in the normal
space. -/
theorem B_holds : B := by
  intro k n x U hU hx u hu hli
  have hxu : ContDiffAt ℝ 2 x u := hx.contDiffAt (hU.mem_nhds hu)
  have hd : DifferentiableAt ℝ (fderiv ℝ x) u :=
    (hxu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym := hxu.isSymmSndFDerivAt (by simp)
  have hd2 : ∀ i j, d2x x u i j = d2x x u j i := by
    intro i j
    rw [d2x_eq hd, d2x_eq hd, hsym]
  have hell : ∀ i j, ell x u i j = ell x u j i := fun i j ↦ by unfold ell; rw [hd2]
  refine ⟨?_, ?_, hell, ?_, ?_⟩
  · ext i j
    simp [gmat, real_inner_comm]
  · have := Matrix.posDef_gram_of_linearIndependent (𝕜 := ℝ) hli
    exact this
  · intro i j l
    have h1 : ell x u i j ∈ (tangSp x u)ᗮ := Submodule.starProjection_apply_mem _ _
    exact (Submodule.mem_orthogonal' _ _).1 h1 _ (dx_mem_tangSp x u l)
  · intro v
    ext i j
    simp [sff, hell]

theorem A_to_B : A → B := fun _ ↦ B_holds
theorem B_to_A : B → A := fun _ ↦ trivial

/-! ### Vocabulary check (not part of `A`): in the project's parametrization `xParam hM q`, B's
`g_ij` is the project's `firstFF` and, for `v` normal to `M` at `q`, B's `v · ℓ_ij` is the
project's `secondFF` (which uses `⟪v, ∂²x⟫` without projecting, legitimately since `v` is normal). -/

section Vocab

variable {N k w : ℕ} {M : Set (Rn N)} (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn N) (Rn k) (Rn w) M)

theorem gmat_eq_firstFF (q : M) (i j : Fin k) :
    gmat (Morse.xParam hM q) (Morse.uParam hM q) i j =
      Morse.firstFF hM q (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := rfl

theorem tangSp_eq_range (q : M) :
    tangSp (Morse.xParam hM q) (Morse.uParam hM q) =
      LinearMap.range (Morse.dParam hM q : Rn k →ₗ[ℝ] Rn N) := by
  unfold tangSp
  rw [LinearMap.range_eq_map, ← (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.span_eq,
    Submodule.map_span, ← Set.range_comp]
  congr 1
  ext i
  simp [dx, Morse.dParam]

theorem sff_eq_secondFF (q : M) {v : Rn N}
    (hv : v ∈ (LinearMap.range (Morse.dParam hM q : Rn k →ₗ[ℝ] Rn N))ᗮ) (i j : Fin k) :
    sff (Morse.xParam hM q) (Morse.uParam hM q) v i j =
      Morse.secondFF hM q v (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (Morse.xParam hM q)) (Morse.uParam hM q) :=
    (Morse.hasFDerivAt_fderiv_xParam hM q).differentiableAt
  rw [← tangSp_eq_range] at hv
  simp only [sff, ell, Matrix.of_apply, Morse.secondFF_apply]
  rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hv,
    d2x_eq hd]
  rfl

end Vocab

#rt_check RoundTrip.V4_5.A_to_B [Morse.xParam, Morse.uParam, Morse.dParam, Morse.d2Param, Morse.firstFF,
  Morse.secondFF, Morse.normalForm]
#rt_check RoundTrip.V4_5.B_to_A [Morse.xParam, Morse.uParam, Morse.dParam, Morse.d2Param, Morse.firstFF,
  Morse.secondFF, Morse.normalForm]
#rt_overlap RoundTrip.V4_5.B_to_A [Morse.xParam, Morse.uParam, Morse.dParam, Morse.d2Param, Morse.firstFF,
  Morse.secondFF, Morse.normalForm]

end RoundTrip.V4_5
