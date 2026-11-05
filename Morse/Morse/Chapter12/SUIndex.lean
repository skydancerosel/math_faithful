import Morse.Chapter12.SUJacobi
import Morse.Chapter9.IndexTheorem
import Morse.Chapter14.IndexCount

/-!
Milnor, *Morse Theory*, Theorem 20.5 (p. 110), Theorem 15.1 (p. 83) and §23 (pp. 130–132): the
conjugate points and the index of a geodesic `t ↦ exp(tA)` from `I` to `−I` in `SU(n)`.

# The index of a geodesic from `I` to `−I` in `SU(n)`

## Milnor's text, paraphrased

* p. 130: by Theorem 20.5 the conjugate points along `t ↦ exp(tA)` are governed by the
  eigenvalues of `K_A`; for `A = diag(iπk_1, …, iπk_n)` they are `π²(k_j − k_l)²/4` (each
  positive one twice, for `k_j > k_l`).  An eigenvalue `e > 0` gives conjugate points at the
  multiples of `π/√e`.
* p. 131: by the Index Theorem 15.1, **the index of `t ↦ exp(tA)`, `0 ≤ t ≤ 1`, is
  `Σ_{k_j > k_l} (k_j − k_l − 2)`**; **Lemma 23.2**: if `n = 2m` and the geodesic is not minimal,
  the index is `≥ 2m + 2`.

## What is formalized

Here the Riemannian input enters as **theorems about the submanifold `SU(n) ⊆ Mₙ(ℂ)`**, not as
definitions (closing the gap "Theorems 20.5/15.1 enter only as definitions" of
`Morse/Chapter14/IndexCount.lean`):

* `Morse.hadKer a t = {W ∈ 𝔰𝔲(n) : S(t) ⊙ W = 0}` and
  **`Morse.conjMultiplicity_su`** (Theorem 20.5 for `SU(n)`): for `A = T diag(ia) Tᴴ ∈ 𝔰𝔲(n)`,
  `T` unitary, the multiplicity of `t₀ ∈ [0, 1]` as a parameter conjugate to `0` along
  `exp(tA)` (Milnor's definition, `Morse.conjMultiplicity`: the dimension of the space of Jacobi
  fields vanishing at `0` and `t₀`) is `dim hadKer a t₀`.  The isomorphism is
  `J ↦ DJ/dt(0)` onto `{C ∈ 𝔰𝔲 : S(t₀) ⊙ TᴴCT = 0}` (every Jacobi field vanishing at `0` is a
  `J_C` of `Morse/Chapter12/SUJacobi.lean`, by uniqueness).
* **`Morse.finrank_hadKer`** (the count): for `a = πk`, `0 < t₀ < 1`,
  `dim hadKer (πk) t₀ = conjMult (suSpectrum k) t₀`, Milnor's multiplicity computed from his
  spectrum in `Morse/Chapter14/IndexCount.lean`.  (Coordinates: the real and imaginary parts of the
  entries `w_{jl}`, `k_j > k_l`, with `(k_j − k_l)t₀/2 ∈ ℤ`.)
* **`Morse.formIndex_su_geodesic`** (Theorems 15.1 + 20.5 for `SU(n)`): for `k` odd with
  `Σ k_j = 0` and `T` unitary, `γ(t) = exp(t T suDiag(k) Tᴴ)` is a geodesic in
  `Ω(SU(n); I, −I)` whose index (Milnor's `λ`, the index of the Hessian `E_**` of the energy, via
  the project's `Morse.theorem_15_1`) is `spectralIndex (suSpectrum k) = Σ_{k_j > k_l}
  (k_j − k_l − 2)` (`Morse.spectralIndex_suSpectrum`).
* **`Morse.exists_unitary_suDiag`**: every `A ∈ 𝔰𝔲(n)` with `exp A = −I` is `T suDiag(k) Tᴴ` with
  `T` unitary, `k` odd, `Σ k_j = 0` (spectral theorem).  Hence **`Morse.index_su_eq_bottIndex`**:
  the index of every geodesic `t ↦ exp(tA)` from `I` to `−I` in `SU(n)` is `bottIndex k`, and
  **`Morse.lemma_23_2_index`**: in `SU(2m)`, it is `≥ 2m + 2` unless the geodesic is minimal, in
  which case it is `0` (the same theorem).

## Gaps in Milnor's text

* p. 131, "adding over all `j, l`": the multiplicity of a conjugate point is the *dimension* of a
  space of Jacobi fields; that it is the number of eigenvalues `e` of `K_A` (with multiplicity)
  with `t ∈ (π/√e)ℤ` needs the description of *all* Jacobi fields vanishing at `0`, which is
  Milnor's proof of 20.5 in an eigenbasis.  Here it is the explicit kernel `hadKer` and its real
  dimension.
* p. 130: the reduction to diagonal `A` (by an isometry `X ↦ TXT⁻¹` fixing `±I`) is replaced by
  carrying `T` through the computation: `K_{TDTᴴ}(TMTᴴ) = T K_D(M) Tᴴ`.
-/

open Matrix Set Filter Topology Module Finset
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The kernel of `W ↦ S(t) ⊙ W` on `𝔰𝔲(n)` -/

omit [Fintype ι] [DecidableEq ι] in
theorem hadSin_add (a : ι → ℝ) (W W' : Matrix ι ι ℂ) (t : ℝ) :
    hadSin a (W + W') t = hadSin a W t + hadSin a W' t := by
  ext j l; simp [mul_add]

omit [Fintype ι] [DecidableEq ι] in
theorem hadSin_smul (a : ι → ℝ) (r : ℝ) (W : Matrix ι ι ℂ) (t : ℝ) :
    hadSin a (r • W) t = r • hadSin a W t := by
  ext j l
  simp only [hadSin_apply, Matrix.smul_apply, Complex.real_smul]
  ring

/-- `{W ∈ 𝔰𝔲(n) : S(t) ⊙ W = 0}`. -/
def hadKer (a : ι → ℝ) (t : ℝ) : Submodule ℝ (Matrix ι ι ℂ) where
  carrier := {W | W ∈ specialSkewHermitian ι ∧ hadSin a W t = 0}
  add_mem' {W W'} hW hW' := ⟨(specialSkewHermitian ι).add_mem hW.1 hW'.1, by
    rw [hadSin_add, hW.2, hW'.2, add_zero]⟩
  zero_mem' := ⟨(specialSkewHermitian ι).zero_mem, by ext; simp⟩
  smul_mem' r W hW := ⟨(specialSkewHermitian ι).smul_mem r hW.1, by
    rw [hadSin_smul, hW.2, smul_zero]⟩

theorem mem_hadKer {a : ι → ℝ} {t : ℝ} {W : Matrix ι ι ℂ} :
    W ∈ hadKer a t ↔ W ∈ specialSkewHermitian ι ∧ hadSin a W t = 0 := Iff.rfl

/-- `C ↦ TᴴCT`, a linear isomorphism of `Mₙ(ℂ)` for unitary `T`. -/
def conjEquiv (T : Matrix ι ι ℂ) (hT : Tᴴ * T = 1) : Matrix ι ι ℂ ≃ₗ[ℝ] Matrix ι ι ℂ where
  toFun C := Tᴴ * C * T
  invFun C := T * C * Tᴴ
  map_add' C C' := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r C := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv C := by
    have hT' := mul_conjTranspose_eq_one hT
    simp only [← Matrix.mul_assoc, hT', Matrix.one_mul]
    rw [Matrix.mul_assoc, hT', Matrix.mul_one]
  right_inv C := by
    simp only [← Matrix.mul_assoc, hT, Matrix.one_mul]
    rw [Matrix.mul_assoc, hT, Matrix.mul_one]

/-- The parameters `C = DJ/dt(0)` of the Jacobi fields vanishing at `0` and `t`. -/
def conjRange (a : ι → ℝ) (T : Matrix ι ι ℂ) (hT : Tᴴ * T = 1) (t : ℝ) :
    Submodule ℝ (Matrix ι ι ℂ) :=
  (hadKer a t).comap (conjEquiv T hT).toLinearMap

theorem mem_conjRange {a : ι → ℝ} {T : Matrix ι ι ℂ} {hT : Tᴴ * T = 1} {t : ℝ}
    {C : Matrix ι ι ℂ} : C ∈ conjRange a T hT t ↔ Tᴴ * C * T ∈ hadKer a t := Iff.rfl

theorem finrank_conjRange (a : ι → ℝ) (T : Matrix ι ι ℂ) (hT : Tᴴ * T = 1) (t : ℝ) :
    finrank ℝ (conjRange a T hT t) = finrank ℝ (hadKer a t) := by
  rw [conjRange, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

/-! ### The count: `dim hadKer (πk) t = conjMult (suSpectrum k) t` -/

section Count

variable (k : ι → ℤ)

omit [Fintype ι] [DecidableEq ι] in
/-- For `k_l < k_j` and `0 < t < 1`: `sin(ω_{jl}t) = 0`, `ω_{jl} = π(k_j − k_l)/2`, iff `t` is a
conjugate parameter (in the sense of `Morse.conjParams`) of the eigenvalue `π²(k_j − k_l)²/4`. -/
theorem jacSin_eq_zero_iff_mem_conjParams {j l : ι} (h : k l < k j) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    jacSin ((Real.pi * k j - Real.pi * k l) / 2) t = 0 ↔
      t ∈ conjParams (Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2) := by
  have hd : (0 : ℝ) < (k j : ℝ) - k l := by
    have : ((k l : ℤ) : ℝ) < (k j : ℝ) := by exact_mod_cast h
    linarith
  set b := (Real.pi * k j - Real.pi * k l) / 2 with hb
  have hbpos : 0 < b := by rw [hb]; nlinarith [Real.pi_pos]
  have he : Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2 = b ^ 2 := by rw [hb]; ring
  have hsq : Real.sqrt (Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2) = b := by
    rw [he, Real.sqrt_sq hbpos.le]
  rw [jacSin_eq_zero_iff hbpos.ne']
  simp only [conjParams, Set.mem_ofPred_eq, hsq]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨by rw [he]; positivity, ht.1, ht.2, s, ?_⟩
    field_simp
    linarith
  · rintro ⟨-, -, -, s, hs⟩
    refine ⟨s, ?_⟩
    rw [hs]
    field_simp

/-- The real coordinates of `hadKer (πk) t`: the real and imaginary parts of the entries `w_{jl}`
for the pairs `k_j > k_l` whose eigenvalue `π²(k_j − k_l)²/4` has `t` as a conjugate
parameter — Milnor's `E_{jl}`, `E'_{jl}` components. -/
def hadCoord (t : ℝ) : hadKer (fun j => Real.pi * k j) t →ₗ[ℝ]
    ({q : {p : ι × ι // k p.2 < k p.1} × Fin 2 // t ∈ conjParams (suSpectrum k q)} → ℝ) where
  toFun W q := if q.1.2 = 0 then ((W : Matrix ι ι ℂ) q.1.1.1.1 q.1.1.1.2).re
    else ((W : Matrix ι ι ℂ) q.1.1.1.1 q.1.1.1.2).im
  map_add' W W' := by
    funext q
    simp only [Submodule.coe_add, Matrix.add_apply, Complex.add_re, Complex.add_im, Pi.add_apply]
    split_ifs <;> rfl
  map_smul' r W := by
    funext q
    simp only [Submodule.coe_smul, Matrix.smul_apply, Complex.real_smul, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
      RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> rfl

theorem hadKer_entry {t : ℝ} (W : hadKer (fun j => Real.pi * k j) t) (j l : ι) :
    (jacSin ((Real.pi * k j - Real.pi * k l) / 2) t : ℂ) * (W : Matrix ι ι ℂ) j l = 0 := by
  have := congrFun (congrFun W.2.2 j) l
  simpa using this

theorem hadKer_skew {t : ℝ} (W : hadKer (fun j => Real.pi * k j) t) (j l : ι) :
    (W : Matrix ι ι ℂ) j l = -star ((W : Matrix ι ι ℂ) l j) := by
  have := congrFun (congrFun W.2.1.1 j) l
  simp only [conjTranspose_apply, Matrix.neg_apply] at this
  rw [this, neg_neg]

theorem hadCoord_injective {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Function.Injective (hadCoord k t) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro W hW
  have hpos : ∀ j l, k l < k j → (W : Matrix ι ι ℂ) j l = 0 := by
    intro j l hjl
    by_cases hc : t ∈ conjParams (Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2)
    · have h0 := congrFun hW ⟨(⟨(j, l), hjl⟩, 0), hc⟩
      have h1 := congrFun hW ⟨(⟨(j, l), hjl⟩, 1), hc⟩
      simp only [hadCoord, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, if_true] at h0
      simp only [hadCoord, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
        show ¬ ((1 : Fin 2) = 0) by decide, if_false] at h1
      exact Complex.ext h0 h1
    · have hs : jacSin ((Real.pi * k j - Real.pi * k l) / 2) t ≠ 0 := fun h =>
        hc ((jacSin_eq_zero_iff_mem_conjParams k hjl ht).1 h)
      exact (mul_eq_zero.1 (hadKer_entry k W j l)).resolve_left (by exact_mod_cast hs)
  apply Subtype.ext
  ext j l
  rcases lt_trichotomy (k l) (k j) with h | h | h
  · exact hpos j l h
  · have hs : jacSin ((Real.pi * k j - Real.pi * k l) / 2) t = t := by
      rw [h, sub_self, zero_div, jacSin_of_eq_zero]
    refine (mul_eq_zero.1 (hadKer_entry k W j l)).resolve_left ?_
    rw [hs]
    exact_mod_cast ht.1.ne'
  · rw [hadKer_skew k W j l, hpos l j h, star_zero, neg_zero]
    rfl

theorem hadCoord_surjective {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Function.Surjective (hadCoord k t) := by
  classical
  intro c
  set f : ι → ι → ℂ := fun j l => if h : k l < k j then
    (if hc : t ∈ conjParams (Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2) then
      (c ⟨(⟨(j, l), h⟩, 0), hc⟩ : ℂ) + (c ⟨(⟨(j, l), h⟩, 1), hc⟩ : ℂ) * Complex.I else 0)
    else 0 with hfdef
  have hf0 : ∀ j l, ¬ k l < k j → f j l = 0 := fun j l h => by simp only [hfdef, dif_neg h]
  have hfc : ∀ j l (h : k l < k j),
      t ∉ conjParams (Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2) → f j l = 0 := fun j l h hc => by
    simp only [hfdef, dif_pos h, dif_neg hc]
  set W : Matrix ι ι ℂ := of fun j l => f j l - star (f l j) with hWdef
  have hWmem : W ∈ hadKer (fun j => Real.pi * k j) t := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · ext j l
      simp only [hWdef, conjTranspose_apply, of_apply, star_sub, star_star, Matrix.neg_apply]
      ring
    · simp only [trace, diag_apply, hWdef, of_apply, hf0 _ _ (lt_irrefl _), star_zero, sub_zero,
        Finset.sum_const_zero]
    · ext j l
      simp only [hadSin_apply, hWdef, of_apply, Matrix.zero_apply]
      rcases lt_trichotomy (k l) (k j) with h | h | h
      · rw [hf0 l j (not_lt.2 h.le), star_zero, sub_zero]
        by_cases hc : t ∈ conjParams (Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2)
        · rw [(jacSin_eq_zero_iff_mem_conjParams k h ht).2 hc, Complex.ofReal_zero, zero_mul]
        · rw [hfc j l h hc, mul_zero]
      · rw [hf0 j l (by rw [h]; exact lt_irrefl _), hf0 l j (by rw [h]; exact lt_irrefl _),
          star_zero, sub_zero, mul_zero]
      · rw [hf0 j l (not_lt.2 h.le), zero_sub]
        by_cases hc : t ∈ conjParams (Real.pi ^ 2 / 4 * ((k l : ℝ) - k j) ^ 2)
        · have h0 := (jacSin_eq_zero_iff_mem_conjParams k h ht).2 hc
          rw [show (Real.pi * k j - Real.pi * k l) / 2 = -((Real.pi * k l - Real.pi * k j) / 2) by
            ring, jacSin_neg, h0, Complex.ofReal_zero, zero_mul]
        · rw [hfc l j h hc, star_zero, neg_zero, mul_zero]
  refine ⟨⟨W, hWmem⟩, ?_⟩
  funext q
  obtain ⟨⟨⟨⟨j, l⟩, hjl⟩, i⟩, hq⟩ := q
  have hWjl : W j l = (c ⟨(⟨(j, l), hjl⟩, 0), hq⟩ : ℂ) +
      (c ⟨(⟨(j, l), hjl⟩, 1), hq⟩ : ℂ) * Complex.I := by
    have hq' : t ∈ conjParams (Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2) := hq
    rw [hWdef, of_apply, hf0 l j (not_lt.2 hjl.le), star_zero, sub_zero]
    simp only [hfdef, dif_pos hjl, dif_pos hq']
  fin_cases i
  · simp [hadCoord, hWjl]
  · simp [hadCoord, hWjl]

/-- **The count** (Milnor p. 131, "adding over all `j, l`"): for `0 < t < 1`,
`dim {W ∈ 𝔰𝔲(n) : S(t) ⊙ W = 0} = conjMult (suSpectrum k) t`: each pair `k_j > k_l` whose
eigenvalue `π²(k_j − k_l)²/4` has `t` as a conjugate parameter contributes `2` (Milnor's `E_{jl}`
and `E'_{jl}`). -/
theorem finrank_hadKer {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    finrank ℝ (hadKer (fun j => Real.pi * k j) t) = conjMult (suSpectrum k) t := by
  classical
  rw [(LinearEquiv.ofBijective (hadCoord k t) ⟨hadCoord_injective k ht,
    hadCoord_surjective k ht⟩).finrank_eq, Module.finrank_fintype_fun_eq_card, conjMult,
    Fintype.card_subtype]

end Count

/-! ### Theorem 20.5 for `SU(n)`: the multiplicity of a conjugate point -/

variable [Nonempty ι]

/-- **Theorem 20.5 for `SU(n)`**: along `γ(t) = exp(tA)`, `A = T diag(ia) Tᴴ ∈ 𝔰𝔲(n)`, the
multiplicity of `t₀ ∈ [0, 1]` as a parameter conjugate to `0` is `dim {W ∈ 𝔰𝔲 : S(t₀) ⊙ W = 0}`. -/
theorem conjMultiplicity_su {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) {a : ι → ℝ}
    (hA : T * diagI a * Tᴴ ∈ specialSkewHermitian ι)
    (hc : IsSmoothCurveIn isSliceSubmanifold_specialUnitaryGroup
      (fun s => NormedSpace.exp (s • (T * diagI a * Tᴴ))))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
    conjMultiplicity isSliceSubmanifold_specialUnitaryGroup _ hc 0 t₀ =
      finrank ℝ (hadKer a t₀) := by
  set hSU := isSliceSubmanifold_specialUnitaryGroup (ι := ι)
  set γ := fun s : ℝ => NormedSpace.exp (s • (T * diagI a * Tᴴ)) with hγdef
  have hG := isMatrixGroup_specialUnitaryGroup (ι := ι)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hγ0 : γ 0 = 1 := by simp [γ]
  -- the Jacobi fields `J_C`, normalized, as elements of `𝒥(γ)`
  have hJC : ∀ C ∈ specialSkewHermitian ι,
      (fun t => suJac a T C (projIcc (0 : ℝ) 1 zero_le_one t)) ∈ jacobiSpace hSU γ hc :=
    fun C hC => (isJacobiField_suJac hT hA hC).comp_projIcc_mem hc
  have hJCcov : ∀ C ∈ specialSkewHermitian ι,
      covAlong hSU γ (fun t => suJac a T C (projIcc (0 : ℝ) 1 zero_le_one t)) 0 = C := by
    intro C hC
    have heq : EqOn (fun t => suJac a T C (projIcc (0 : ℝ) 1 zero_le_one t)) (suJac a T C)
        (Icc 0 1) := fun t ht => by simp [projIcc_of_mem _ ht]
    rw [covAlong, derivWithin_congr heq (heq h0)]
    exact covAlong_suJac_zero hT hA hC
  -- `D : J ↦ DJ/dt(0)` on the conjugate space
  set CS := conjSpace hSU γ hc 0 t₀ with hCS
  let D : CS →ₗ[ℝ] Matrix ι ι ℂ := (tanAt hSU (γ 0)).subtype ∘ₗ LinearMap.snd ℝ _ _ ∘ₗ
    jacEval hc h0 ∘ₗ Submodule.inclusion (conjSpace_le_jacobiSpace hc 0 t₀)
  have hD : ∀ J : CS, D J = covAlong hSU γ (J : ℝ → Matrix ι ι ℂ) 0 := fun J => rfl
  have hDinj : Function.Injective D := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro J hJ
    obtain ⟨hJs, hJ0, -⟩ := (mem_conjSpace hc).1 J.2
    exact Subtype.ext (jacobiSpace_eq_zero hc hJs
      (hJs.1.eqOn_zero hc h0 hJ0 ((hD J).symm.trans hJ)))
  -- the range of `D`
  have hR : LinearMap.range D = conjRange a T hT t₀ := by
    ext C
    constructor
    · rintro ⟨J, rfl⟩
      obtain ⟨hJs, hJ0, hJt⟩ := (mem_conjSpace hc).1 J.2
      -- `C = DJ/dt(0)` lies in `T_IG = 𝔰𝔲(n)`
      have hCmem : D J ∈ specialSkewHermitian ι := by
        have h1 : covAlong hSU γ J 0 ∈ tangentSubspace hSU ⟨γ 0, hc.mem 0 h0⟩ :=
          (prj_eq_self_iff hSU (hc.mem 0 h0)).1 (prj_prj hSU _ _)
        rw [hG.mem_tangentSubspace_iff] at h1
        rw [hD]
        simpa [hγ0] using h1
      -- `J = J_C` on `[0, 1]`, by uniqueness
      have heqJ : (J : ℝ → Matrix ι ι ℂ) =
          fun t => suJac a T (D J) (projIcc (0 : ℝ) 1 zero_le_one t) := by
        have := (jacEval_bijective hc h0).1 (a₁ := ⟨J, hJs⟩) (a₂ := ⟨_, hJC (D J) hCmem⟩)
          (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
        · exact congrArg Subtype.val this
        · change (J : ℝ → Matrix ι ι ℂ) 0 = suJac a T (D J) (projIcc (0 : ℝ) 1 zero_le_one 0)
          rw [hJ0, projIcc_of_mem _ h0]
          exact (suJac_zero a T (D J)).symm
        · change covAlong hSU γ J 0 = covAlong hSU γ _ 0
          rw [hJCcov (D J) hCmem]
          rfl
      have hzero : suJac a T (D J) t₀ = 0 := by
        have := congrFun heqJ t₀
        rw [projIcc_of_mem _ ht₀] at this
        rw [← this]
        exact hJt
      rw [suJac_eq_zero_iff hT hA] at hzero
      exact ⟨conj_mem_specialSkewHermitian' hT hCmem, hzero⟩
    · intro hC
      have hCmem : C ∈ specialSkewHermitian ι := by
        have := conj_mem_specialSkewHermitian hT hC.1
        convert this using 1
        exact ((conjEquiv T hT).symm_apply_apply C).symm
      have hJCS : (fun t => suJac a T C (projIcc (0 : ℝ) 1 zero_le_one t)) ∈ CS := by
        rw [hCS, mem_conjSpace hc]
        refine ⟨hJC C hCmem, ?_, ?_⟩
        · simp [suJac_zero]
        · simp only [projIcc_of_mem _ ht₀]
          exact (suJac_eq_zero_iff hT hA C t₀).2 hC.2
      exact ⟨⟨_, hJCS⟩, by rw [hD]; exact hJCcov C hCmem⟩
  rw [conjMultiplicity, ← LinearMap.finrank_range_of_inj hDinj, hR, finrank_conjRange]

/-! ### Geodesics from `I` to `−I` -/

omit [Nonempty ι] in
/-- `suDiag k ∈ 𝔰𝔲(n)` iff `Σ k_j = 0`; then so is `T suDiag(k) Tᴴ`. -/
theorem conj_suDiag_mem {k : ι → ℤ} (hsum : ∑ i, k i = 0) {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) :
    T * suDiag k * Tᴴ ∈ specialSkewHermitian ι := by
  refine conj_mem_specialSkewHermitian hT ⟨?_, ?_⟩
  · rw [suDiag, diagonal_conjTranspose, diagonal_neg]
    congr 1
    funext j
    simp only [Pi.star_apply, star_mul', Complex.star_def, Complex.conj_I,
      Complex.conj_ofReal, map_intCast, mul_neg]
  · rw [trace_suDiag]
    have : (∑ j, (k j : ℂ)) = ((∑ j, k j : ℤ) : ℂ) := by push_cast; rfl
    rw [this, hsum, Int.cast_zero, mul_zero]

omit [Nonempty ι] in
/-- **`exp A = −I`** for `A = T suDiag(k) Tᴴ` with every `k_j` odd (Milnor p. 127). -/
theorem exp_conj_suDiag {k : ι → ℤ} (hk : ∀ i, Odd (k i)) {T : Matrix ι ι ℂ}
    (hT : Tᴴ * T = 1) : NormedSpace.exp (T * suDiag k * Tᴴ) = -1 := by
  have hT' := mul_conjTranspose_eq_one hT
  have hinv : T⁻¹ = Tᴴ := Matrix.inv_eq_left_inv hT
  have hD : NormedSpace.exp (suDiag k) = -1 := by
    rw [suDiag_eq_diagI, diagI]
    exact (exp_diagonal_eq_neg_one_iff _).2 fun j => ⟨k j, hk j, rfl⟩
  rw [← hinv, Matrix.exp_conj T _ ⟨⟨T, Tᴴ, hT', hT⟩, rfl⟩, hD, hinv, Matrix.mul_neg,
    Matrix.mul_one, Matrix.neg_mul, hT']

omit [Nonempty ι] in
/-- **Every geodesic `t ↦ exp(tA)` from `I` to `−I` in `SU(n)` is of Milnor's form** (p. 127):
`A ∈ 𝔰𝔲(n)` with `exp A = −I` is `T suDiag(k) Tᴴ` with `T` unitary, every `k_j` odd and
`Σ k_j = 0`.  (Spectral theorem for the Hermitian matrix `iA`.) -/
theorem exists_unitary_suDiag {A : Matrix ι ι ℂ} (hA : A ∈ specialSkewHermitian ι)
    (hexp : NormedSpace.exp A = -1) :
    ∃ (T : Matrix ι ι ℂ) (k : ι → ℤ), Tᴴ * T = 1 ∧ (∀ i, Odd (k i)) ∧ ∑ i, k i = 0 ∧
      A = T * suDiag k * Tᴴ := by
  have hH : (Complex.I • A).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, hA.1, Complex.star_def, Complex.conj_I, neg_smul,
      smul_neg, neg_neg]
  set U : Matrix ι ι ℂ := (hH.eigenvectorUnitary : Matrix ι ι ℂ)
  set ev := hH.eigenvalues
  have hU : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  have hU' := mul_conjTranspose_eq_one hU
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at hspec
  set D : Matrix ι ι ℂ := Matrix.diagonal fun j => ((-ev j : ℝ) : ℂ) * Complex.I with hDdef
  have hAD : A = U * D * Uᴴ := by
    have e1 : A = (-Complex.I) • (Complex.I • A) := by
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    have e2 : D = (-Complex.I) • Matrix.diagonal (RCLike.ofReal ∘ ev) := by
      rw [hDdef, ← diagonal_smul]
      congr 1
      funext j
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_neg, neg_mul]
      exact congrArg Neg.neg (mul_comm _ _)
    rw [e2, Matrix.mul_smul, Matrix.smul_mul, ← hspec, ← e1]
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hU
  have hexpD : NormedSpace.exp D = -1 := by
    have h1 := hexp
    rw [hAD, ← hinv, Matrix.exp_conj U _ ⟨⟨U, Uᴴ, hU', hU⟩, rfl⟩, hinv] at h1
    have r : ∀ X : Matrix ι ι ℂ, Uᴴ * (U * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    have h2 : Uᴴ * (U * NormedSpace.exp D * Uᴴ) * U = Uᴴ * (-1) * U := by rw [h1]
    simpa only [Matrix.mul_assoc, r, hU, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.one_mul] using h2
  have hk := (exp_diagonal_eq_neg_one_iff _).1 hexpD
  choose k hk using hk
  have hDk : D = suDiag k := by
    rw [suDiag_eq_diagI, diagI, hDdef]
    congr 1
    funext j
    rw [(hk j).2]
  refine ⟨U, k, hU, fun i => (hk i).1, ?_, by rw [hAD, hDk]⟩
  have htr := hA.2
  rw [hAD, trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, hDk, trace_suDiag] at htr
  have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero
  have h1 := (mul_eq_zero.1 htr).resolve_left hpi
  exact_mod_cast h1

/-- **The geodesic `t ↦ exp(tA)` lies in `Ω(SU(n); I, −I)`** when `exp A = −I`. -/
theorem mem_pathSpace_exp {A : Matrix ι ι ℂ} (hA : A ∈ specialSkewHermitian ι)
    (hexp : NormedSpace.exp A = -1) :
    (fun s : ℝ => NormedSpace.exp (s • A)) ∈
      pathSpace (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1) :=
  ⟨IsPiecewiseSmooth.of_contDiff (contDiff_exp_smul A) zero_le_one,
    fun t _ => isMatrixGroup_specialUnitaryGroup.exp_smul_mem hA t, by simp, by simp [hexp]⟩

/-- It is an (unbroken) geodesic of `SU(n)`. -/
theorem isUnbrokenGeodesic_exp {A : Matrix ι ι ℂ} (hA : A ∈ specialSkewHermitian ι) :
    IsUnbrokenGeodesic isSliceSubmanifold_specialUnitaryGroup
      (fun s : ℝ => NormedSpace.exp (s • A)) :=
  ⟨(contDiff_exp_smul A).contDiffOn,
    (isMatrixGroup_specialUnitaryGroup.isGeodesicOn_exp_smul hA).mono isOpen_Ioo
      (subset_univ _)⟩

/-! ### The index -/

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem support_conjMult_subset {κ : Type*} [Fintype κ] (e : κ → ℝ) :
    Function.support (conjMult e) ⊆ Ioo (0 : ℝ) 1 := by
  classical
  intro t ht
  rw [Function.mem_support, conjMult, ne_eq, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff] at ht
  push Not at ht
  obtain ⟨i, -, hi⟩ := ht
  exact ⟨hi.2.1, hi.2.2.1⟩

/-- **The index of a geodesic from `I` to `−I` in `SU(n)`, from Theorems 15.1 and 20.5**: for
`A = T suDiag(k) Tᴴ` (`T` unitary, `k_j` odd, `Σ k_j = 0`), the index of the Hessian of the
energy at `γ(t) = exp(tA)` is `spectralIndex (suSpectrum k)`, the count of
`Morse/Chapter14/IndexCount.lean`. -/
theorem formIndex_su_geodesic {A : Matrix ι ι ℂ} (k : ι → ℤ) (hsum : ∑ i, k i = 0)
    {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) (hAeq : A = T * suDiag k * Tᴴ)
    (hγ : (fun s : ℝ => NormedSpace.exp (s • A)) ∈
      pathSpace (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    formIndex (energyHessian isSliceSubmanifold_specialUnitaryGroup hγ) =
      (spectralIndex (suSpectrum k) : ℕ∞) := by
  have hA : A ∈ specialSkewHermitian ι := hAeq ▸ conj_suDiag_mem hsum hT
  have hgeo := isUnbrokenGeodesic_exp hA
  rw [(theorem_15_1 isSliceSubmanifold_specialUnitaryGroup hγ hgeo).2]
  congr 1
  rw [spectralIndex, ← Set.indicator_eq_self.2 (support_conjMult_subset (suSpectrum k)),
    ← finsum_mem_def]
  refine finsum_mem_congr rfl fun t ht => ?_
  rw [suDiag_eq_diagI] at hAeq
  subst hAeq
  rw [conjMultiplicity_su hT hA _ (Ioo_subset_Icc_self ht), finrank_hadKer k ht]

/-- **The index formula in `SU(n)`** (Milnor p. 131), proved through the project's Index Theorem
`Morse.theorem_15_1` and Theorem 20.5 for `SU(n)`: every geodesic `t ↦ exp(tA)` from `I` to `−I`
in `SU(n)` (`A ∈ 𝔰𝔲(n)`, `exp A = −I`) has, for the odd integers `k_j` with `A` unitarily
conjugate to `diag(iπk_1, …, iπk_n)`, index `λ = Σ_{k_i > k_j} (k_i − k_j − 2)`. -/
theorem index_su_eq_bottIndex {A : Matrix ι ι ℂ} (hA : A ∈ specialSkewHermitian ι)
    (hexp : NormedSpace.exp A = -1)
    (hγ : (fun s : ℝ => NormedSpace.exp (s • A)) ∈
      pathSpace (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    ∃ k : ι → ℤ, (∀ i, Odd (k i)) ∧ ∑ i, k i = 0 ∧
      (∃ T : Matrix ι ι ℂ, Tᴴ * T = 1 ∧ A = T * suDiag k * Tᴴ) ∧
      ∃ n : ℕ, formIndex (energyHessian isSliceSubmanifold_specialUnitaryGroup hγ) = n ∧
        (n : ℤ) = bottIndex k := by
  obtain ⟨T, k, hT, hk, hsum, hAeq⟩ := exists_unitary_suDiag hA hexp
  exact ⟨k, hk, hsum, ⟨T, hT, hAeq⟩, spectralIndex (suSpectrum k),
    formIndex_su_geodesic k hsum hT hAeq hγ, spectralIndex_suSpectrum hk⟩

/-- **Lemma 23.2 for the geodesics of `SU(2m)`** (Milnor pp. 131–132), with the index computed
by the Index Theorem: a geodesic `t ↦ exp(tA)` from `I` to `−I` in `SU(2m)` has index `0` if all
`k_j = ±1` (a minimal geodesic), and index `≥ 2m + 2` otherwise. -/
theorem lemma_23_2_index {m : ℕ} (hcard : Fintype.card ι = 2 * m) {A : Matrix ι ι ℂ}
    (hA : A ∈ specialSkewHermitian ι) (hexp : NormedSpace.exp A = -1)
    (hγ : (fun s : ℝ => NormedSpace.exp (s • A)) ∈
      pathSpace (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    ∃ k : ι → ℤ, (∀ i, Odd (k i)) ∧ ∑ i, k i = 0 ∧
      (∃ T : Matrix ι ι ℂ, Tᴴ * T = 1 ∧ A = T * suDiag k * Tᴴ) ∧
      ((∀ i, k i = 1 ∨ k i = -1) →
        formIndex (energyHessian isSliceSubmanifold_specialUnitaryGroup hγ) = 0) ∧
      (¬ (∀ i, k i = 1 ∨ k i = -1) →
        ((2 * m + 2 : ℕ) : ℕ∞) ≤
          formIndex (energyHessian isSliceSubmanifold_specialUnitaryGroup hγ)) := by
  obtain ⟨k, hk, hsum, hT, n, hn, hnk⟩ := index_su_eq_bottIndex hA hexp hγ
  refine ⟨k, hk, hsum, hT, fun hmin => ?_, fun hnm => ?_⟩
  · rw [hn]
    have := bottIndex_eq_zero_of_minimal hmin
    rw [this] at hnk
    exact_mod_cast hnk
  · rw [hn]
    have h := bottIndex_ge hk hcard hsum hnm
    rw [← hnk] at h
    exact_mod_cast (show 2 * m + 2 ≤ n by exact_mod_cast h)

end Morse
