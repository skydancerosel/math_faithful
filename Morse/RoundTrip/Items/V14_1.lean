import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_1

open Matrix

namespace RoundTrip.V14_1

/-- The project's statement (universe of `ι` instantiated at `0`): the scalar criterion
`e^{ia} = −1 ⇔ a = kπ, k odd`, and `exp diag(ia_j) = −I ⇔ every a_j = k_jπ, k_j odd`. -/
def A : Prop :=
  type_of% @Morse.exp_ofReal_mul_I_eq_neg_one_iff ∧ type_of% @Morse.exp_diagonal_eq_neg_one_iff.{0}

theorem A_holds : A := ⟨@Morse.exp_ofReal_mul_I_eq_neg_one_iff, @Morse.exp_diagonal_eq_neg_one_iff.{0}⟩

section Aux

/-- `exp(diag(ia_j)) = diag(e^{ia_j})` (Mathlib's `Matrix.exp_diagonal`). -/
theorem mexp_diagI {n : ℕ} (a : Fin n → ℝ) :
    mexp (diagI a) = Matrix.diagonal fun j => Complex.exp ((a j : ℂ) * Complex.I) := by
  unfold mexp diagI
  rw [Matrix.exp_diagonal]
  congr 1
  ext j
  rw [Pi.coe_exp, Complex.exp_eq_exp_ℂ]

/-- Spectral theorem for a skew-Hermitian matrix (via the Hermitian `iA`). -/
theorem exists_unitary_diagI {n : ℕ} {A : Mat n} (hA : Aᴴ = -A) :
    ∃ T ∈ Un n, ∃ a : Fin n → ℝ, A = T * diagI a * Tᴴ := by
  have hH : (Complex.I • A).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, hA, Complex.star_def, Complex.conj_I, neg_smul,
      smul_neg, neg_neg]
  set U : Mat n := (hH.eigenvectorUnitary : Mat n)
  set ev := hH.eigenvalues
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at hspec
  refine ⟨U, hH.eigenvectorUnitary.2, fun j => -ev j, ?_⟩
  have e1 : A = (-Complex.I) • (Complex.I • A) := by
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  have e2 : diagI (fun j => -ev j) = (-Complex.I) • Matrix.diagonal (RCLike.ofReal ∘ ev) := by
    rw [diagI, ← diagonal_smul]
    congr 1
    funext j
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_neg, neg_mul]
    exact congrArg Neg.neg (mul_comm _ _)
  rw [e2, Matrix.mul_smul, Matrix.smul_mul, ← hspec, ← e1]

theorem unitary_facts {n : ℕ} {T : Mat n} (hT : T ∈ Un n) :
    Tᴴ * T = 1 ∧ T * Tᴴ = 1 ∧ T⁻¹ = Tᴴ ∧ IsUnit T := by
  have h1 : Tᴴ * T = 1 := by
    rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.1 hT
  have h2 : T * Tᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hT
  exact ⟨h1, h2, Matrix.inv_eq_left_inv h1, ⟨⟨T, Tᴴ, h2, h1⟩, rfl⟩⟩

/-- `exp(T D Tᴴ) = T exp(D) Tᴴ` for unitary `T`. -/
theorem mexp_conj {n : ℕ} {T : Mat n} (hT : T ∈ Un n) (D : Mat n) :
    mexp (T * D * Tᴴ) = T * mexp D * Tᴴ := by
  obtain ⟨-, -, hinv, hu⟩ := unitary_facts hT
  unfold mexp
  rw [← hinv, Matrix.exp_conj T _ hu]

theorem conj_eq_neg_one_iff {n : ℕ} {T : Mat n} (hT : T ∈ Un n) (X : Mat n) :
    T * X * Tᴴ = -1 ↔ X = -1 := by
  obtain ⟨h1, h2, -, -⟩ := unitary_facts hT
  constructor
  · intro h
    have h3 : Tᴴ * (T * X * Tᴴ) * T = Tᴴ * (-1) * T := by rw [h]
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ T, h1, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_neg, Matrix.neg_mul] using h3
  · rintro rfl
    rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, h2]

theorem diagI_eq_milnorA_iff {n : ℕ} (a : Fin n → ℝ) (k : Fin n → ℤ) :
    diagI a = milnorA k ↔ ∀ j, a j = Real.pi * k j := by
  unfold milnorA diagI
  rw [diagonal_eq_diagonal_iff]
  refine forall_congr' fun j => ?_
  constructor
  · intro h
    have := mul_right_cancel₀ Complex.I_ne_zero h
    exact_mod_cast this
  · intro h; rw [h]

end Aux

theorem A_to_B : A → B := by
  rintro ⟨-, hA2⟩
  have hii : ∀ (n : ℕ) (a : Fin n → ℝ),
      mexp (diagI a) = -1 ↔ ∃ k : Fin n → ℤ, (∀ j, Odd (k j)) ∧ diagI a = milnorA k := by
    intro n a
    unfold mexp
    rw [diagI, hA2 a]
    constructor
    · intro h
      choose k hk using h
      exact ⟨k, fun j => (hk j).1, (diagI_eq_milnorA_iff a k).2 fun j => (hk j).2⟩
    · rintro ⟨k, hk, he⟩ j
      exact ⟨k j, hk j, (diagI_eq_milnorA_iff a k).1 he j⟩
  refine ⟨fun n a => mexp_diagI a, hii, fun n A hA => exists_unitary_diagI hA, ?_⟩
  intro n A hA
  constructor
  · intro hexp
    obtain ⟨T, hT, a, rfl⟩ := exists_unitary_diagI hA
    rw [mexp_conj hT, conj_eq_neg_one_iff hT] at hexp
    obtain ⟨k, hk, he⟩ := (hii n a).1 hexp
    exact ⟨T, hT, k, hk, by rw [he]⟩
  · rintro ⟨T, hT, k, hk, rfl⟩
    rw [mexp_conj hT, conj_eq_neg_one_iff hT, milnorA]
    exact (hii n _).2 ⟨k, hk, rfl⟩

theorem B_to_A : B → A := by
  rintro ⟨hBi, hBii, -, -⟩
  -- the scalar criterion, from `B` for `n = 1`
  have hscalar : ∀ a : ℝ, Complex.exp (a * Complex.I) = -1 ↔ ∃ k : ℤ, Odd k ∧ a = Real.pi * k := by
    intro a
    have h := hBii 1 (fun _ => a)
    rw [hBi 1 (fun _ => a), ← diagonal_one, diagonal_neg, diagonal_eq_diagonal_iff] at h
    simp only [Fin.forall_fin_one] at h
    rw [h]
    constructor
    · rintro ⟨k, hk, he⟩
      exact ⟨k 0, hk, (diagI_eq_milnorA_iff _ k).1 he 0⟩
    · rintro ⟨k, hk, he⟩
      exact ⟨fun _ => k, hk, (diagI_eq_milnorA_iff _ _).2 fun j => he⟩
  refine ⟨hscalar, ?_⟩
  intro ι _ _ a
  rw [Matrix.exp_diagonal, ← diagonal_one, diagonal_neg, diagonal_eq_diagonal_iff]
  refine forall_congr' fun j => ?_
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  exact hscalar (a j)

#rt_check RoundTrip.V14_1.A_to_B [Morse.exp_ofReal_mul_I_eq_neg_one_iff, Morse.exp_diagonal_eq_neg_one_iff]
#rt_check RoundTrip.V14_1.B_to_A [Morse.exp_ofReal_mul_I_eq_neg_one_iff, Morse.exp_diagonal_eq_neg_one_iff]
#rt_overlap RoundTrip.V14_1.B_to_A [Morse.exp_ofReal_mul_I_eq_neg_one_iff, Morse.exp_diagonal_eq_neg_one_iff]
#rt_overlap RoundTrip.V14_1.A_to_B [Morse.exp_ofReal_mul_I_eq_neg_one_iff, Morse.exp_diagonal_eq_neg_one_iff]

end RoundTrip.V14_1
