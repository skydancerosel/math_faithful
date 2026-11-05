import Morse.Chapter1.Nondegenerate
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Milnor.Chapter5.OrSign

/-!
Milnor, *Morse Theory*, §6, Application 2 (p. 36), and §5, p. 29 (the Euler characteristic as an
alternating count of critical points): the linear algebra used for them.

# The sign of the determinant of a self-adjoint operator is `(-1)^index`

Milnor reads off the Euler characteristic `χ(M) = C₀ - C₁ + ⋯ ± Cₙ` (p. 29; formula (3) of
Theorem 5.2) from the homology of the slabs `(M^{a_i}, M^{a_{i-1}})`.  The files
`Morse/Chapter3/EulerChar*.lean` prove that the alternating count is a topological invariant
without homology, through the Poincaré–Hopf theorem of the companion project, as in Milnor's §6,
Application 2: at a non-degenerate critical point `q` of index `λ`, the gradient field of `f` has
index `(-1)^λ`.  The index of a non-degenerate zero of a vector field is the sign of the
determinant of its derivative (the companion project's `Milnor.Tub.indexN_eq_sgn_det`, Milnor's
*Topology from the Differentiable Viewpoint*, §6, Lemma 4), and the derivative of a gradient field
at a critical point is the self-adjoint operator `A` of the Hessian: `f_**(v, w) = ⟪A v, w⟫`.
What remains is the linear algebra of this file:

> *If `H` is a non-degenerate symmetric bilinear form on a finite-dimensional real inner product
> space and `A` is the operator with `H(v, w) = ⟪A v, w⟫`, then `sgn det A = (-1)^{index H}`.*

Milnor uses this fact without comment: in Application 2 of §6 (p. 36), and again in *Topology from
the Differentiable Viewpoint* (§6, p. 40, "Step 1" of the proof of the Poincaré–Hopf theorem), he
says only that `(-1)^λ` is the index of `grad f` at a critical point of index `λ`.

## Proof

By the spectral theorem (Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis`) `A` has an
orthonormal basis of eigenvectors `b₁, …, bₙ` with eigenvalues `μ₁, …, μₙ`.  In the coordinates
`cᵢ = ⟪bᵢ, v⟫` the quadratic form is `H(v, v) = Σ μᵢ cᵢ²`
(`Morse.inner_apply_self_eq_sum_eigenvalues`), so by the uniqueness half of Sylvester's law of
inertia (Mathlib's `QuadraticForm.sigNeg_of_equiv_weightedSumSquares`) the index of `H` — the
largest dimension of a subspace on which `H` is negative definite, Mathlib's `sigNeg` — is the
number of negative eigenvalues (`Morse.index_eq_ncard_eigenvalues_neg`).  On the other hand
`det A = Π μᵢ` (`LinearMap.IsSymmetric.det_eq_prod_eigenvalues`), and when `H` is non-degenerate
no `μᵢ` vanishes, so `sgn det A = Π sgn μᵢ = (-1)^{#{i | μᵢ < 0}}`.

## Independence of the inner product

The right-hand side `(-1)^{index H}` is defined from `H` alone (`Morse.index` is `sigNeg` of the
quadratic form `v ↦ H(v, v)`); the inner product enters only through the operator `A`.  So
`Morse.sgn_det_eq_neg_one_pow_index` says in particular that `sgn det A` is the same for the
operators representing `H` with respect to *any* two inner products.  This is what makes the
argument usable on a submanifold `N ⊆ ℝᴷ`, where the operator lives on the tangent space `T_qN`
with the inner product induced from `ℝᴷ`, while the Hessian `f_**` of Milnor's §2 is read in a
chart, where that inner product is the first fundamental form, not the standard one.

## Main results

* `Morse.index_eq_ncard_eigenvalues_neg`: the index of `(v, w) ↦ ⟪A v, w⟫` is the number of
  negative eigenvalues of `A`.
* `Morse.isNondegenerate_iff_bijective`: the form is non-degenerate iff `A` is bijective.
* `Morse.sgn_det_eq_neg_one_pow_index`: `sgn det A = (-1)^{index H}` for `H` non-degenerate.
* `Morse.sgn_det_eq_neg_one_pow_index_of_symm`: the same with the symmetry of `A` deduced from the
  symmetry of `H`.
* `Morse.index_eq_finrank_of_negDef`, `Morse.index_eq_zero_of_posDef`: the index of a negative
  (positive) definite form is the dimension (zero).
-/

open Module Finset
open scoped RealInnerProductSpace

noncomputable section

namespace Morse

/-- The sign of a product is the product of the signs (`Milnor.sgn` is the sign of a real number,
as an integer). -/
theorem sgn_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    Milnor.sgn (∏ i ∈ s, f i) = ∏ i ∈ s, Milnor.sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Milnor.sgn_one]
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, Milnor.sgn_mul, ih]

/-- The product of the signs of finitely many nonzero reals is `(-1)` to the number of negative
ones. -/
theorem prod_sgn_eq_neg_one_pow {ι : Type*} [Fintype ι] (μ : ι → ℝ) (hμ : ∀ i, μ i ≠ 0) :
    ∏ i, Milnor.sgn (μ i) = (-1) ^ {i | μ i < 0}.ncard := by
  classical
  have h1 : ∀ i, Milnor.sgn (μ i) = if μ i < 0 then -1 else 1 := by
    intro i
    by_cases hi : μ i < 0
    · rw [if_pos hi, Milnor.sgn_neg hi]
    · rw [if_neg hi, Milnor.sgn_pos (lt_of_le_of_ne (not_lt.1 hi) (hμ i).symm)]
  have h2 : {i | μ i < 0} = ↑(univ.filter fun i => μ i < 0) := by ext; simp
  simp_rw [h1]
  rw [prod_ite, prod_const, prod_const_one, mul_one, h2, Set.ncard_coe_finset]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

section Spectral

variable {A : V →ₗ[ℝ] V} (hA : A.IsSymmetric) {n : ℕ} (hn : finrank ℝ V = n)

/-- **The quadratic form of a self-adjoint operator in an orthonormal eigenbasis**:
`⟪A v, v⟫ = Σ μᵢ ⟪bᵢ, v⟫²`. -/
theorem inner_apply_self_eq_sum_eigenvalues (v : V) :
    ⟪A v, v⟫ = ∑ i, hA.eigenvalues hn i * (hA.eigenvectorBasis hn).repr v i ^ 2 := by
  set b := hA.eigenvectorBasis hn
  rw [← b.sum_inner_mul_inner (A v) v]
  refine sum_congr rfl fun i _ => ?_
  have h1 : ⟪A v, b i⟫ = hA.eigenvalues hn i * ⟪b i, v⟫ := by
    rw [hA v (b i), hA.apply_eigenvectorBasis hn i, real_inner_smul_right, real_inner_comm]
    rfl
  rw [h1, b.repr_apply_apply]
  ring

/-- **The quadratic form `v ↦ ⟪A v, v⟫` is equivalent to the weighted sum of squares with the
eigenvalues as weights.** -/
theorem quadForm_equivalent_weightedSumSquares {H : V →L[ℝ] V →L[ℝ] ℝ}
    (hH : ∀ v w, H v w = ⟪A v, w⟫) :
    (quadForm H).Equivalent (QuadraticMap.weightedSumSquares ℝ (hA.eigenvalues hn)) := by
  set b := hA.eigenvectorBasis hn
  refine ⟨{ toLinearEquiv := b.toBasis.equivFun
            map_app' := fun v => ?_ }⟩
  have he : ∀ i, b.toBasis.equivFun v i = b.repr v i := fun i => by
    rw [Basis.equivFun_apply, OrthonormalBasis.coe_toBasis_repr_apply]
  change QuadraticMap.weightedSumSquares ℝ (hA.eigenvalues hn) (b.toBasis.equivFun v) = _
  rw [QuadraticMap.weightedSumSquares_apply, quadForm_apply, hH,
    inner_apply_self_eq_sum_eigenvalues hA hn v]
  refine sum_congr rfl fun i _ => ?_
  rw [he, smul_eq_mul]
  ring

/-- **The index of `(v, w) ↦ ⟪A v, w⟫` is the number of negative eigenvalues of `A`** (Sylvester's
law of inertia applied to an orthonormal eigenbasis). -/
theorem index_eq_ncard_eigenvalues_neg {H : V →L[ℝ] V →L[ℝ] ℝ} (hH : ∀ v w, H v w = ⟪A v, w⟫) :
    index H = {i | hA.eigenvalues hn i < 0}.ncard :=
  QuadraticForm.sigNeg_of_equiv_weightedSumSquares (quadForm_equivalent_weightedSumSquares hA hn hH)

/-- At a non-degenerate form no eigenvalue vanishes. -/
theorem eigenvalues_ne_zero {H : V →L[ℝ] V →L[ℝ] ℝ} (hH : ∀ v w, H v w = ⟪A v, w⟫)
    (hnd : IsNondegenerate H) (i : Fin n) : hA.eigenvalues hn i ≠ 0 := by
  intro h0
  set b := hA.eigenvectorBasis hn
  have hAb : A (b i) = 0 := by
    rw [hA.apply_eigenvectorBasis hn i, h0]
    simp
  have hb : b i = 0 := isNondegenerate_iff.1 hnd (b i) fun w => by rw [hH, hAb, inner_zero_left]
  have := b.norm_eq_one i
  rw [hb, norm_zero] at this
  exact zero_ne_one this

end Spectral

/-- **Non-degeneracy of `(v, w) ↦ ⟪A v, w⟫` is the bijectivity of `A`.** -/
theorem isNondegenerate_iff_bijective {A : V →ₗ[ℝ] V} {H : V →L[ℝ] V →L[ℝ] ℝ}
    (hH : ∀ v w, H v w = ⟪A v, w⟫) : IsNondegenerate H ↔ Function.Bijective A := by
  rw [isNondegenerate_iff]
  constructor
  · intro h
    have hinj : Function.Injective A := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro v hv
      refine h v fun w => ?_
      rw [hH, LinearMap.mem_ker.1 hv, inner_zero_left]
    exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  · intro h v hv
    have h0 : A v = 0 := by
      have := hv (A v)
      rw [hH, real_inner_self_eq_norm_sq] at this
      exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this)
    exact h.1 (by rw [h0, map_zero])

/-- **The sign of the determinant of the operator of a non-degenerate form is `(-1)^index`.**
If `H(v, w) = ⟪A v, w⟫` with `A` self-adjoint and `H` non-degenerate, then
`sgn det A = (-1)^{index H}`.  The index on the right is defined from `H` alone, so the sign is
independent of the inner product used to represent `H` by an operator. -/
theorem sgn_det_eq_neg_one_pow_index {A : V →ₗ[ℝ] V} (hA : A.IsSymmetric)
    {H : V →L[ℝ] V →L[ℝ] ℝ} (hH : ∀ v w, H v w = ⟪A v, w⟫) (hnd : IsNondegenerate H) :
    Milnor.sgn (LinearMap.det A) = (-1) ^ index H := by
  rw [hA.det_eq_prod_eigenvalues rfl, index_eq_ncard_eigenvalues_neg hA rfl hH]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  rw [sgn_prod, prod_sgn_eq_neg_one_pow _ (eigenvalues_ne_zero hA rfl hH hnd)]

omit [FiniteDimensional ℝ V] in
/-- The operator of a symmetric form is self-adjoint. -/
theorem isSymmetric_of_symm {A : V →ₗ[ℝ] V} {H : V →L[ℝ] V →L[ℝ] ℝ}
    (hH : ∀ v w, H v w = ⟪A v, w⟫) (hsymm : ∀ v w, H v w = H w v) : A.IsSymmetric := by
  intro v w
  rw [← hH, hsymm, hH, real_inner_comm]

/-- **`sgn det A = (-1)^{index H}`, for a symmetric non-degenerate form `H`** and any operator
`A` with `H(v, w) = ⟪A v, w⟫` (such an `A` is automatically self-adjoint). -/
theorem sgn_det_eq_neg_one_pow_index_of_symm {A : V →ₗ[ℝ] V} {H : V →L[ℝ] V →L[ℝ] ℝ}
    (hH : ∀ v w, H v w = ⟪A v, w⟫) (hsymm : ∀ v w, H v w = H w v) (hnd : IsNondegenerate H) :
    Milnor.sgn (LinearMap.det A) = (-1) ^ index H :=
  sgn_det_eq_neg_one_pow_index (isSymmetric_of_symm hH hsymm) hH hnd

/-! ### Definite forms -/

/-- **A negative definite form has index the dimension.** -/
theorem index_eq_finrank_of_negDef {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : E →L[ℝ] E →L[ℝ] ℝ} (hH : ∀ v, v ≠ 0 → H v v < 0) :
    index H = finrank ℝ E := by
  refine le_antisymm (sigPos_le_finrank _) ?_
  have h := finrank_le_index_of_negDef H (W := ⊤) fun v _ hv => hH v hv
  rwa [finrank_top] at h

/-- **A positive semi-definite form has index `0`.** -/
theorem index_eq_zero_of_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : E →L[ℝ] E →L[ℝ] ℝ} (hH : ∀ v, 0 ≤ H v v) : index H = 0 := by
  obtain ⟨W, hW, hneg⟩ := exists_negDef_finrank_eq_index H
  rw [← hW, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
  intro v hv
  by_contra hv0
  exact absurd (hneg v hv hv0) (not_lt.2 (hH v))

end Morse
