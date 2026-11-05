import Morse
import RoundTrip.Check
import RoundTrip.Blind.V5_3

open Module Complex Polynomial
open scoped ContDiff Manifold

namespace RoundTrip.V5_3

/-- The project's statement: the three listed theorems, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Morse.nullity_reBilin_sub_smul_reInner_eq.{0} ∧
  type_of% @Morse.eigenspace_eq_nullSpace_sub_smul_reInner.{0} ∧
  type_of% @Morse.finrank_eigenspace_neg_eq.{0}

theorem A_holds : A :=
  ⟨@Morse.nullity_reBilin_sub_smul_reInner_eq.{0}, @Morse.eigenspace_eq_nullSpace_sub_smul_reInner.{0},
    @Morse.finrank_eigenspace_neg_eq.{0}⟩

section Glue

variable {k : ℕ}

local notation "ι" => Fin k ⊕ Fin k

/-- Eigenspaces of an operator conjugate to `Q` are the kernels of `Q - e`. -/
lemma finrank_eigenspace_eq {X : Type} [AddCommGroup X] [Module ℝ X] (Ψ : X ≃ₗ[ℝ] (ι → ℝ))
    (S : X →ₗ[ℝ] X) (Q : Matrix ι ι ℝ) (hS : ∀ x, Ψ (S x) = Q.mulVec (Ψ x)) (e : ℝ) :
    finrank ℝ (Module.End.eigenspace S e) =
      finrank ℝ (LinearMap.ker (Q - e • (1 : Matrix ι ι ℝ)).mulVecLin) := by
  have h : Module.End.eigenspace S e =
      (LinearMap.ker (Q - e • (1 : Matrix ι ι ℝ)).mulVecLin).comap Ψ.toLinearMap := by
    ext x
    rw [Module.End.mem_eigenspace_iff, Submodule.mem_comap, LinearMap.mem_ker,
      Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      LinearEquiv.coe_coe, ← hS, sub_eq_zero]
    constructor
    · intro h; rw [h, map_smul]
    · intro h; apply Ψ.injective; rw [h, map_smul]
  rw [h, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

/-- Real coordinates `(x, y)` ↦ `x + i y ∈ ℂᵏ`. -/
noncomputable def Φ : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℂ (Fin k) where
  toFun w := WithLp.toLp 2 (fun h => (⟨w (Sum.inl h), w (Sum.inr h)⟩ : ℂ))
  invFun z := Sum.elim (fun h => (z h).re) (fun h => (z h).im)
  map_add' x y := by ext h; apply Complex.ext <;> simp
  map_smul' c x := by ext h; apply Complex.ext <;> simp
  left_inv w := by funext a; rcases a with a | a <;> simp
  right_inv z := by ext h <;> simp

lemma Φ_apply (w : ι → ℝ) (h : Fin k) : Φ w h = ⟨w (Sum.inl h), w (Sum.inr h)⟩ := rfl

lemma re_inner_Φ (x y : ι → ℝ) : (inner ℂ (Φ x) (Φ y)).re = ∑ a, x a * y a := by
  simp only [PiLp.inner_apply, Φ_apply, Fintype.sum_sum_type, RCLike.inner_apply, re_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  simp [Complex.mul_re, mul_comm]

/-- The symmetric complex bilinear form of `b`, `B(u, w) = Σ (b_{hj} + b_{jh})/2 u^h w^j`. -/
noncomputable def Bs (b : Matrix (Fin k) (Fin k) ℂ) :
    EuclideanSpace ℂ (Fin k) →L[ℂ] EuclideanSpace ℂ (Fin k) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        (EuclideanSpace ℂ (Fin k) →ₗ[ℂ] ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ
      (Matrix.toLinearMap₂' ℂ (Matrix.of fun h j => (b h j + b j h) / 2)).compl₁₂
        (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)).toLinearMap
        (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)).toLinearMap)

lemma Bs_apply (b : Matrix (Fin k) (Fin k) ℂ) (u w : EuclideanSpace ℂ (Fin k)) :
    Bs b u w = ∑ h, ∑ j, u h * w j * ((b h j + b j h) / 2) := by
  simp only [Bs, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearMap.compl₁₂_apply, Matrix.toLinearMap₂'_apply, smul_eq_mul,
    Matrix.of_apply, WithLp.linearEquiv_apply]
  refine Finset.sum_congr rfl fun h _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  change u.ofLp h * (w.ofLp j * ((b h j + b j h) / 2)) = _
  ring

lemma Bs_symm (b : Matrix (Fin k) (Fin k) ℂ) (u w : EuclideanSpace ℂ (Fin k)) :
    Bs b u w = Bs b w u := by
  rw [Bs_apply, Bs_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  ring

lemma Qp_eq (b : Matrix (Fin k) (Fin k) ℂ) (w : R2 k) :
    Qp b w = (Bs b (Φ (WithLp.ofLp w)) (Φ (WithLp.ofLp w))).re := by
  have h1 : Qc b (toC w) = Bs b (Φ (WithLp.ofLp w)) (Φ (WithLp.ofLp w)) := by
    rw [Bs_apply]
    simp only [add_div, mul_add, Finset.sum_add_distrib]
    have hs : ∑ h, ∑ j, Φ (WithLp.ofLp w) h * Φ (WithLp.ofLp w) j * (b j h / 2) =
        ∑ h, ∑ j, Φ (WithLp.ofLp w) h * Φ (WithLp.ofLp w) j * (b h j / 2) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    rw [hs, ← Finset.sum_add_distrib]
    unfold Qc
    refine Finset.sum_congr rfl fun h _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Φ_apply, toC]
    ring
  rw [Qp, h1]

lemma qmat_eq (b : Matrix (Fin k) (Fin k) ℂ) (a c : ι) :
    qmat b a c = (Bs b (Φ (Pi.single a 1)) (Φ (Pi.single c 1))).re := by
  simp only [qmat, Matrix.of_apply, Qp_eq, WithLp.ofLp_add, PiLp.ofLp_single, map_add,
    add_apply, add_re, Bs_symm b (Φ (Pi.single c 1)) (Φ (Pi.single a 1))]
  ring

lemma qmat_symm (b : Matrix (Fin k) (Fin k) ℂ) (a c : ι) : qmat b a c = qmat b c a := by
  simp only [qmat, Matrix.of_apply, add_comm (EuclideanSpace.single a (1 : ℝ))]
  ring

/-- Re `B(Φx, Φy)` in coordinates: the bilinear form of the matrix `qmat`. -/
lemma re_Bs_Φ (b : Matrix (Fin k) (Fin k) ℂ) (x y : ι → ℝ) :
    (Bs b (Φ x) (Φ y)).re = ∑ a, ∑ c, x a * y c * qmat b a c := by
  have hsingle : ∀ z : ι → ℝ, z = ∑ a, z a • (Pi.single a 1 : ι → ℝ) := by
    intro z
    conv_lhs => rw [← Finset.univ_sum_single z]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    ext j
    by_cases h : j = a
    · subst h; simp
    · simp [h]
  have hterm : ∀ (r s : ℝ) (u w : ι → ℝ),
      (Bs b (Φ (r • u)) (Φ (s • w))).re = r * s * (Bs b (Φ u) (Φ w)).re := by
    intro r s u w
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, ← Complex.coe_smul, ← Complex.coe_smul,
      ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, smul_apply,
      smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    ring
  conv_lhs => rw [hsingle x, hsingle y]
  simp only [map_sum, sum_apply, re_sum, hterm, qmat_eq]
  exact Finset.sum_comm

/-- The real-linear operator of `qmat` on `ℂᵏ` (through `Φ`). -/
noncomputable def Aop (b : Matrix (Fin k) (Fin k) ℂ) :
    EuclideanSpace ℂ (Fin k) →ₗ[ℝ] EuclideanSpace ℂ (Fin k) :=
  Φ.toLinearMap ∘ₗ (qmat b).mulVecLin ∘ₗ Φ.symm.toLinearMap

lemma hAop (b : Matrix (Fin k) (Fin k) ℂ) (u w : EuclideanSpace ℂ (Fin k)) :
    (inner ℂ (Aop b u) w).re = (Bs b u w).re := by
  obtain ⟨x, rfl⟩ := Φ.surjective u
  obtain ⟨y, rfl⟩ := Φ.surjective w
  simp only [Aop, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply, Matrix.mulVecLin_apply]
  rw [re_inner_Φ, re_Bs_Φ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [qmat_symm]
  ring

lemma roots_prod {n : ℕ} (f : Fin n → ℝ) :
    (∏ i, (X - C (f i))).roots = Multiset.map f Finset.univ.val := by
  have : (fun i => X - C (f i)) = (fun a => X - C a) ∘ f := rfl
  rw [Finset.prod_eq_multiset_prod, this, ← Multiset.map_map, roots_multiset_prod_X_sub_C]

/-- For the symmetric matrix `qmat`, the root multiplicity of `e` in the characteristic polynomial
is the dimension of `ker (qmat - e)` (spectral theorem; Mathlib). -/
lemma count_roots_eq (b : Matrix (Fin k) (Fin k) ℂ) (e : ℝ) :
    (qmat b).charpoly.roots.count e =
      finrank ℝ (LinearMap.ker (qmat b - e • (1 : Matrix ι ι ℝ)).mulVecLin) := by
  classical
  have hH : (qmat b).IsHermitian := by
    ext a c
    simp [qmat_symm]
  have hT := Matrix.isSymmetric_toEuclideanLin_iff.2 hH
  have hn : finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card ι := finrank_euclideanSpace
  have hc : (Matrix.toEuclideanLin (qmat b)).charpoly = (qmat b).charpoly := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, ← LinearMap.charpoly_toMatrix _
      (EuclideanSpace.basisFun ι ℝ).toBasis, LinearMap.toMatrix_toLin]
  rw [← hc, hT.charpoly_eq hn, roots_prod, Multiset.count_map]
  have := hT.card_filter_eigenvalues_eq hn e
  rw [← finrank_eigenspace_eq (WithLp.linearEquiv 2 ℝ (ι → ℝ)) (Matrix.toEuclideanLin (qmat b))
    (qmat b) (fun x ↦ by simp) e, ← this]
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun i _ ↦ eq_comm

end Glue

/-- **A ⇒ B.** On `V = ℂᵏ` take `B` the symmetrized bilinear form of `b` and `A` the real operator
of B's polar matrix `qmat` (through `x + iy`); `Re⟨A u, w⟩ = Re B(u, w)` (`hAop`), so A's
`finrank_eigenspace_neg_eq` gives `dim ker (qmat − e) = dim ker (qmat + e)`. The
characteristic-polynomial form of the multiplicity is not in A: for the symmetric matrix `qmat`
it equals `dim ker (qmat − e)` by Mathlib's spectral theorem (`count_roots_eq`). -/
theorem A_to_B : A → B := by
  intro hA k b e
  have h3 := hA.2.2 (V := EuclideanSpace ℂ (Fin k)) (Bs b) (Aop b) (hAop b) e
  have hk : ∀ e : ℝ, finrank ℝ (Module.End.eigenspace (Aop b) e) =
      finrank ℝ (LinearMap.ker (qmat b - e • (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ)).mulVecLin) :=
    fun e ↦ finrank_eigenspace_eq Φ.symm (Aop b) (qmat b) (fun x ↦ by simp [Aop]) e
  have hneg : qmat b - (-e) • (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ) =
      qmat b + e • (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ) := by
    rw [neg_smul, sub_neg_eq_add]
  refine ⟨?_, ?_⟩
  · rw [← hk, h3, hk, hneg]
  · rw [count_roots_eq, count_roots_eq, ← hk, h3, hk]

/-- **B ⇒ A**, by proving A outright (B, about `ℂᵏ` in coordinates, says nothing about a general,
possibly infinite-dimensional, complex inner product space `V`): the project's short proofs, from
`nullity_sub_smul_eq_nullity_add_smul'` (Assertion 2, algebraic form) and `reInner_I_smul`, which
are not in this item. -/
theorem B_to_A : B → A := by
  intro _
  have h1 : type_of% @Morse.nullity_reBilin_sub_smul_reInner_eq.{0} := fun B e ↦
    Morse.nullity_sub_smul_eq_nullity_add_smul' _ _ Morse.realMulI Morse.realMulI_realMulI
      (fun v w => by simpa using Morse.reInner_I_smul v w) (fun v w => by simp) e
  have h2 : type_of% @Morse.eigenspace_eq_nullSpace_sub_smul_reInner.{0} := by
    intro V _ _ A L hA e
    ext u
    rw [Module.End.mem_eigenspace_iff, Morse.mem_nullSpace]
    simp only [sub_apply, smul_apply, smul_eq_mul, Morse.reInner_apply, ← hA]
    constructor
    · intro h w
      rw [h, Morse.re_inner_real_smul_left, sub_self]
    · intro h
      have hw := h (A u - e • u)
      rw [← Morse.re_inner_real_smul_left, ← Complex.sub_re, ← inner_sub_left, ← Morse.reInner_apply,
        Morse.reInner_self, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero] at hw
      exact hw
  refine ⟨h1, h2, ?_⟩
  intro V _ _ B A hA e
  have hA' : ∀ u w, (inner ℂ (A u) w).re = Morse.reBilin B u w := by simpa using hA
  rw [h2 A (Morse.reBilin B) hA', h2 A (Morse.reBilin B) hA']
  have := h1 B e
  rw [Morse.nullity, Morse.nullity] at this
  have h : Morse.reBilin B - (-e) • Morse.reInner =
      Morse.reBilin B + e • (Morse.reInner : V →L[ℝ] V →L[ℝ] ℝ) := by
    ext v w
    simp
  rw [this, h]

#rt_check RoundTrip.V5_3.A_to_B [Morse.nullity_reBilin_sub_smul_reInner_eq,
  Morse.eigenspace_eq_nullSpace_sub_smul_reInner, Morse.finrank_eigenspace_neg_eq]
#rt_check RoundTrip.V5_3.B_to_A [Morse.nullity_reBilin_sub_smul_reInner_eq,
  Morse.eigenspace_eq_nullSpace_sub_smul_reInner, Morse.finrank_eigenspace_neg_eq]
#rt_overlap RoundTrip.V5_3.B_to_A [Morse.nullity_reBilin_sub_smul_reInner_eq,
  Morse.eigenspace_eq_nullSpace_sub_smul_reInner, Morse.finrank_eigenspace_neg_eq]

end RoundTrip.V5_3
