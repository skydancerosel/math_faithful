import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_2

open Matrix Finset
open scoped Matrix.Norms.Elementwise

namespace RoundTrip.V14_2

/-- The project's statement (universe of `ι` instantiated at `0`): for `A = suDiag k =
diag(iπk_j)` (any finite index type, any integers `k_j`), `tr AA* = π² Σ k_j²` and
`tr A = iπ Σ k_j`. (`suDiag` is vocabulary.) -/
def A : Prop :=
  type_of% @Morse.trace_suDiag_mul_conjTranspose.{0} ∧ type_of% @Morse.trace_suDiag.{0}

theorem A_holds : A := ⟨@Morse.trace_suDiag_mul_conjTranspose.{0}, @Morse.trace_suDiag.{0}⟩

section Aux

variable {n : ℕ}

theorem unitary_facts {T : Mat n} (hT : T ∈ Un n) :
    Tᴴ * T = 1 ∧ T * Tᴴ = 1 ∧ T⁻¹ = Tᴴ ∧ IsUnit T := by
  have h1 : Tᴴ * T = 1 := by
    rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hT
  have h2 : T * Tᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hT
  exact ⟨h1, h2, Matrix.inv_eq_left_inv h1, ⟨⟨T, Tᴴ, h2, h1⟩, rfl⟩⟩

/-- The diagonal entries `iπk_j` of `milnorA k`. -/
noncomputable def dvec (k : Fin n → ℤ) : Fin n → ℂ :=
  fun j => ((Real.pi * (k j : ℝ) : ℝ) : ℂ) * Complex.I

theorem milnorA_eq (k : Fin n → ℤ) : milnorA k = diagonal (dvec k) := rfl

theorem milnorA_eq_suDiag (k : Fin n → ℤ) : milnorA k = Morse.suDiag k := by
  rw [milnorA_eq, Morse.suDiag]
  congr 1
  funext j
  unfold dvec
  push_cast
  rfl

theorem mexp_conj {T : Mat n} (hT : T ∈ Un n) (D : Mat n) :
    mexp (T * D * Tᴴ) = T * mexp D * Tᴴ := by
  obtain ⟨-, -, hinv, hu⟩ := unitary_facts hT
  unfold mexp
  rw [← hinv, Matrix.exp_conj T _ hu]

theorem expCurve_eq {T : Mat n} (hT : T ∈ Un n) (k : Fin n → ℤ) (t : ℝ) :
    expCurve (T * milnorA k * Tᴴ) t =
      T * diagonal (fun j => Complex.exp ((t : ℂ) * dvec k j)) * Tᴴ := by
  unfold expCurve
  rw [show t • (T * milnorA k * Tᴴ) = T * (t • milnorA k) * Tᴴ by
    rw [Matrix.mul_smul, Matrix.smul_mul]]
  rw [mexp_conj hT, milnorA_eq, ← diagonal_smul]
  unfold mexp
  rw [Matrix.exp_diagonal, Pi.exp_def]
  congr 3
  funext j
  rw [← Complex.exp_eq_exp_ℂ, Pi.smul_apply, Complex.real_smul]

/-- `v ↦ T diag(v) Tᴴ` as a linear map. -/
noncomputable def conjDiag (T : Mat n) : (Fin n → ℂ) →ₗ[ℝ] Mat n where
  toFun v := T * diagonal v * Tᴴ
  map_add' v w := by
    rw [show diagonal (v + w) = diagonal v + diagonal w from (diagonal_add v w).symm,
      Matrix.mul_add, Matrix.add_mul]
  map_smul' c v := by
    simp only [RingHom.id_apply]
    rw [diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem hasDerivAt_expCurve {T : Mat n} (hT : T ∈ Un n) (k : Fin n → ℤ) (t : ℝ) :
    HasDerivAt (expCurve (T * milnorA k * Tᴴ))
      (T * diagonal (fun j => dvec k j * Complex.exp ((t : ℂ) * dvec k j)) * Tᴴ) t := by
  have hg : HasDerivAt (fun s : ℝ => fun j => Complex.exp ((s : ℂ) * dvec k j))
      (fun j => dvec k j * Complex.exp ((t : ℂ) * dvec k j)) t := by
    rw [hasDerivAt_pi]
    intro j
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * dvec k j) (dvec k j) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).mul_const (dvec k j)
    simpa [mul_comm] using h1.cexp
  have h := (LinearMap.toContinuousLinearMap (conjDiag T)).hasFDerivAt.comp_hasDerivAt t hg
  have he : expCurve (T * milnorA k * Tᴴ) =
      (LinearMap.toContinuousLinearMap (conjDiag T)) ∘
        (fun s : ℝ => fun j => Complex.exp ((s : ℂ) * dvec k j)) := by
    funext s
    rw [expCurve_eq hT]
    rfl
  rw [he]
  exact h

theorem conjDiag_mul_conjTranspose {T : Mat n} (hT : T ∈ Un n) (v : Fin n → ℂ) :
    (T * diagonal v * Tᴴ) * (T * diagonal v * Tᴴ)ᴴ =
      T * diagonal (fun j => v j * star (v j)) * Tᴴ := by
  obtain ⟨h1, -, -, -⟩ := unitary_facts hT
  have r : ∀ X : Mat n, Tᴴ * (T * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose,
    Matrix.mul_assoc, r]
  rw [← Matrix.mul_assoc (diagonal v), diagonal_mul_diagonal]
  rfl

theorem exp_mul_star (k : Fin n → ℤ) (t : ℝ) (j : Fin n) :
    Complex.exp ((t : ℂ) * dvec k j) * star (Complex.exp ((t : ℂ) * dvec k j)) = 1 := by
  have hz : (t : ℂ) * dvec k j = ((t * (Real.pi * (k j : ℝ)) : ℝ) : ℂ) * Complex.I := by
    rw [dvec]; push_cast; ring
  rw [hz, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  simp

theorem normM_deriv_expCurve {T : Mat n} (hT : T ∈ Un n) (k : Fin n → ℤ) (t : ℝ) :
    normM (deriv (expCurve (T * milnorA k * Tᴴ)) t) = normM (T * milnorA k * Tᴴ) := by
  have hd : deriv (expCurve (T * milnorA k * Tᴴ)) t =
      T * diagonal (fun j => dvec k j * Complex.exp ((t : ℂ) * dvec k j)) * Tᴴ :=
    (hasDerivAt_expCurve hT k t).deriv
  rw [hd]
  unfold normM ipM
  rw [conjDiag_mul_conjTranspose hT, milnorA_eq, conjDiag_mul_conjTranspose hT]
  have hf : (fun j => dvec k j * Complex.exp ((t : ℂ) * dvec k j) *
      star (dvec k j * Complex.exp ((t : ℂ) * dvec k j))) = fun j => dvec k j * star (dvec k j) := by
    funext j
    rw [star_mul', show dvec k j * Complex.exp ((t : ℂ) * dvec k j) *
        (star (dvec k j) * star (Complex.exp ((t : ℂ) * dvec k j))) =
        dvec k j * star (dvec k j) *
          (Complex.exp ((t : ℂ) * dvec k j) * star (Complex.exp ((t : ℂ) * dvec k j))) by ring,
      exp_mul_star, mul_one]
  rw [hf]

theorem trace_conj {T : Mat n} (hT : T ∈ Un n) (X : Mat n) : trace (T * X * Tᴴ) = trace X := by
  obtain ⟨h1, -, -, -⟩ := unitary_facts hT
  rw [trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem conj_mul_conjTranspose {T : Mat n} (hT : T ∈ Un n) (X : Mat n) :
    (T * X * Tᴴ) * (T * X * Tᴴ)ᴴ = T * (X * Xᴴ) * Tᴴ := by
  obtain ⟨h1, -, -, -⟩ := unitary_facts hT
  have r : ∀ X : Mat n, Tᴴ * (T * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, r]

theorem conj_conjTranspose (T X : Mat n) : (T * X * Tᴴ)ᴴ = T * Xᴴ * Tᴴ := by
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]

end Aux

theorem A_to_B : A → B := by
  rintro ⟨hA1, hA2⟩ n T hT k _hk A rfl
  have htr : Matrix.trace ((T * milnorA k * Tᴴ) * (T * milnorA k * Tᴴ)ᴴ) =
      ((Real.pi ^ 2 * ∑ j, ((k j : ℝ)) ^ 2 : ℝ) : ℂ) := by
    rw [conj_mul_conjTranspose hT, trace_conj hT, milnorA_eq_suDiag]
    exact hA1 k
  have hnorm : normM (T * milnorA k * Tᴴ) = Real.pi * Real.sqrt (∑ j, ((k j : ℝ)) ^ 2) := by
    unfold normM ipM
    rw [htr, Complex.ofReal_re, Real.sqrt_mul (by positivity), Real.sqrt_sq Real.pi_pos.le]
  refine ⟨?_, htr, hnorm, ?_⟩
  · -- the length of `t ↦ exp tA` on `[0, 1]` is `|A|`
    unfold arcLenM
    rw [intervalIntegral.integral_congr (g := fun _ => normM (T * milnorA k * Tᴴ))
      (fun t _ => normM_deriv_expCurve hT k t)]
    simp
  · -- `A ∈ 𝔰𝔲(n)` iff `Σ k_j = 0`
    have hskew : (T * milnorA k * Tᴴ)ᴴ = -(T * milnorA k * Tᴴ) := by
      have hD : (milnorA k)ᴴ = -milnorA k := by
        rw [milnorA_eq, diagonal_conjTranspose, diagonal_neg]
        congr 1
        funext j
        simp [dvec, Complex.conj_ofReal]
      rw [conj_conjTranspose, hD, Matrix.mul_neg, Matrix.neg_mul]
    have htrace : Matrix.trace (T * milnorA k * Tᴴ) = (Real.pi : ℂ) * Complex.I * ∑ j, (k j : ℂ) := by
      rw [trace_conj hT, milnorA_eq_suDiag]
      exact hA2 k
    change (T * milnorA k * Tᴴ)ᴴ = -(T * milnorA k * Tᴴ) ∧ Matrix.trace (T * milnorA k * Tᴴ) = 0 ↔ _
    rw [htrace]
    have hpi : (Real.pi : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero
    simp only [hskew, true_and, mul_eq_zero, hpi, false_or]
    rw [show (∑ j, (k j : ℂ)) = ((∑ j, k j : ℤ) : ℂ) by push_cast; rfl]
    exact_mod_cast Iff.rfl

/-- `A` is an elementary computation; it is proved outright (the hypothesis `B` is not used:
`B` only covers odd `k_j`, and gives `tr A = 0 ↔ Σ k_j = 0` rather than the value of `tr A`). -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_⟩
  · intro ι _ _ k
    simp only [Morse.suDiag, diagonal_conjTranspose, diagonal_mul_diagonal, trace_diagonal]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [Pi.star_apply, star_mul', RCLike.star_def, Complex.conj_ofReal, Complex.conj_I,
      map_intCast]
    linear_combination (-(Real.pi : ℂ) ^ 2 * (k j : ℂ) ^ 2) * Complex.I_sq
  · intro ι _ _ k
    simp only [Morse.suDiag, trace_diagonal, mul_sum]
    exact sum_congr rfl fun j _ => by ring

#rt_check RoundTrip.V14_2.A_to_B [Morse.trace_suDiag_mul_conjTranspose, Morse.trace_suDiag]
#rt_check RoundTrip.V14_2.B_to_A [Morse.trace_suDiag_mul_conjTranspose, Morse.trace_suDiag]
#rt_overlap RoundTrip.V14_2.B_to_A [Morse.trace_suDiag_mul_conjTranspose, Morse.trace_suDiag]
#rt_overlap RoundTrip.V14_2.A_to_B [Morse.trace_suDiag_mul_conjTranspose, Morse.trace_suDiag]

end RoundTrip.V14_2
