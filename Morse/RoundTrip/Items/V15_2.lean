import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_2

open Matrix

namespace RoundTrip.V15_2

/-- The project's statement (universes instantiated at `0`): for every `J` with `J² = -1`
(orthogonal or not, any finite index type), `exp(θJ) = cos θ · I + sin θ · J` and `exp(πJ) = -I`. -/
def A : Prop :=
  type_of% @Morse.exp_smul_of_mul_self_eq_neg_one.{0} ∧ type_of% @Morse.exp_pi_smul.{0}

theorem A_holds : A := ⟨@Morse.exp_smul_of_mul_self_eq_neg_one.{0}, @Morse.exp_pi_smul.{0}⟩

/-! ### A ⇒ B, conditionally on the normal form of skew matrices -/

/-- The (real) normal form of a skew matrix on `ℝ^{2m}`, B's Claim 1 without the exponential: this
is the part of B that neither A nor the project contains. -/
def NormalForm : Prop :=
  ∀ (m : ℕ) (A : Mat (Fin 2 × Fin m)), IsSkew A →
    ∃ P ∈ Orth (Fin 2 × Fin m), ∃ a : Fin m → ℝ, Pᵀ * A * P = blk (fun j => a j • sig2)

theorem sig2_sq : sig2 * sig2 = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sig2]

theorem rot2_eq (θ : ℝ) : Real.cos θ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Real.sin θ • sig2 = rot2 θ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sig2, rot2]

/-- A + normal form ⇒ B: in the basis `P`, `exp(πA)` is `exp` of the block-diagonal `π a_j σ`, and A
(for `σ² = -1` on `ℝ²`) turns each block `exp(π a_j σ)` into the rotation `rot2(π a_j)`; A's
`exp(θJ)` / `exp(πJ)` give Claim 2 directly. -/
theorem B_of_A_normalForm (hA : A) (hNF : NormalForm) : B := by
  obtain ⟨hexp, hpi⟩ := hA
  refine ⟨fun m X hX => ?_, fun n J hJ => ⟨fun θ => hexp hJ.2 θ, hpi hJ.2⟩⟩
  obtain ⟨P, hP, a, hPX⟩ := hNF m X hX
  refine ⟨P, hP, a, hPX, ?_⟩
  have hPP : Pᵀ * P = 1 := by
    simpa [Orth, mem_orthogonalGroup_iff'] using hP
  have hPinv : (Pᵀ)⁻¹ = P := Matrix.inv_eq_right_inv hPP
  have hPu : IsUnit Pᵀ := ⟨⟨Pᵀ, P, hPP, mul_eq_one_comm.1 hPP⟩, rfl⟩
  have h1 : Pᵀ * mexp (Real.pi • X) * P = mexp (Real.pi • (Pᵀ * X * P)) := by
    have := Matrix.exp_conj Pᵀ (Real.pi • X) hPu
    rw [hPinv] at this
    rw [mexp, mexp, ← this, Matrix.mul_smul, Matrix.smul_mul]
  rw [h1, hPX, blk, ← blockDiagonal_smul, mexp, Matrix.exp_blockDiagonal]
  congr 1
  funext j
  have hpi : NormedSpace.exp (Real.pi • fun j => a j • sig2) j =
      NormedSpace.exp ((Real.pi • fun j => a j • sig2) j) := by
    open scoped Matrix.Norms.Operator in
      exact Pi.coe_exp (𝔸 := fun _ : Fin m => Matrix (Fin 2) (Fin 2) ℝ) _ j
  rw [hpi, Pi.smul_apply, smul_smul, hexp sig2_sq, rot2_eq]

/-! ### B ⇒ A: every `J` with `J² = -1` is conjugate to a complex structure -/

section Factor
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A positive definite real matrix is a Gram matrix `SᵀS` (spectral theorem). -/
theorem exists_factor {G : Mat ι} (hG : G.PosDef) : ∃ S : Mat ι, Sᵀ * S = G := by
  have hH := hG.isHermitian
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at hspec
  set U : Mat ι := (hH.eigenvectorUnitary : Mat ι)
  set ev := hH.eigenvalues
  refine ⟨diagonal (fun i => √(ev i)) * Uᵀ, ?_⟩
  have hev : ∀ i, 0 ≤ ev i := fun i => (hG.eigenvalues_pos i).le
  rw [conjTranspose_eq_transpose_of_trivial] at hspec
  have hd : (fun i => √(ev i) * √(ev i)) = (RCLike.ofReal ∘ ev : ι → ℝ) :=
    funext fun i => by simp [Real.mul_self_sqrt (hev i)]
  calc (diagonal (fun i => √(ev i)) * Uᵀ)ᵀ * (diagonal (fun i => √(ev i)) * Uᵀ)
        = U * (diagonal (fun i => √(ev i)) * diagonal (fun i => √(ev i))) * Uᵀ := by
          rw [transpose_mul, diagonal_transpose, transpose_transpose]
          simp only [Matrix.mul_assoc]
      _ = U * diagonal (RCLike.ofReal ∘ ev) * Uᵀ := by rw [diagonal_mul_diagonal, hd]
      _ = G := hspec.symm

theorem reindex_mul' {κ : Type} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (X Y : Mat ι) :
    reindex e e (X * Y) = reindex e e X * reindex e e Y := by
  simpa only [coe_reindexAlgEquiv] using map_mul (reindexAlgEquiv ℝ ℝ e) X Y

theorem reindex_exp {κ : Type} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (X : Mat ι) :
    reindex e e (NormedSpace.exp X) = NormedSpace.exp (reindex e e X) := by
  open scoped Matrix.Norms.Operator in
  have hc : Continuous (reindexAlgEquiv ℝ ℝ e) := by
    rw [coe_reindexAlgEquiv]
    show Continuous fun X : Mat ι => reindex e e X
    simp only [reindex_apply]
    exact continuous_id.matrix_submatrix _ _
  open scoped Matrix.Norms.Operator in
  have := NormedSpace.map_exp (reindexAlgEquiv ℝ ℝ e) hc X
  rw [coe_reindexAlgEquiv] at this
  exact this

end Factor

theorem B_to_A : B → A := by
  rintro ⟨-, hB⟩
  have key : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {J : Mat ι}, J * J = -1 → ∀ θ : ℝ,
      NormedSpace.exp (θ • J) = Real.cos θ • (1 : Mat ι) + Real.sin θ • J := by
    intro ι _ _ J hJ θ
    -- the Gram matrix `G = 1 + JᵀJ` of a `J`-invariant inner product
    have hG : (1 + Jᵀ * J).PosDef := by
      have := Matrix.PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self J)
      simpa [conjTranspose_eq_transpose_of_trivial] using this
    obtain ⟨S, hS⟩ := exists_factor hG
    have hdet : IsUnit S.det := by
      have h := hG.det_pos
      rw [← hS, det_mul, det_transpose] at h
      exact isUnit_iff_ne_zero.2 fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl _ h
    have hSu : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).2 hdet
    have hSi : S⁻¹ * S = 1 := nonsing_inv_mul S hdet
    have hSi' : S * S⁻¹ = 1 := mul_nonsing_inv S hdet
    have hJT : Jᵀ * Jᵀ = -1 := by rw [← transpose_mul, hJ, transpose_neg, transpose_one]
    have hinv : Jᵀ * (Sᵀ * S) * J = Sᵀ * S := by
      rw [hS, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        show Jᵀ * (Jᵀ * J) * J = (Jᵀ * Jᵀ) * (J * J) by simp only [Matrix.mul_assoc], hJT, hJ,
        neg_mul_neg, Matrix.one_mul, add_comm]
    -- `J₀ = S J S⁻¹` is a complex structure (orthogonal for the standard inner product)
    set J₀ := S * J * S⁻¹ with hJ₀def
    have hJ₀ : Morse.IsComplexStructure J₀ := by
      refine ⟨?_, ?_⟩
      · rw [mem_orthogonalGroup_iff']
        calc J₀ᵀ * J₀ = (S⁻¹)ᵀ * (Jᵀ * (Sᵀ * S) * J) * S⁻¹ := by
              simp only [hJ₀def, transpose_mul, Matrix.mul_assoc]
          _ = (S * S⁻¹)ᵀ * (S * S⁻¹) := by
              rw [hinv, transpose_mul]; simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hSi', transpose_one, Matrix.one_mul]
      · calc J₀ * J₀ = S * J * (S⁻¹ * S) * J * S⁻¹ := by simp only [hJ₀def, Matrix.mul_assoc]
          _ = -1 := by
              rw [hSi, Matrix.mul_one, Matrix.mul_assoc S J J, hJ, Matrix.mul_neg, Matrix.mul_one,
                Matrix.neg_mul, hSi']
    -- B on `Fin (card ι)`, transported back
    set e := Fintype.equivFin ι
    have hcs : IsCplxStr (reindex e e J₀) := by
      obtain ⟨hO, h2⟩ := hJ₀
      rw [mem_orthogonalGroup_iff'] at hO
      refine ⟨?_, ?_⟩
      · rw [mem_orthogonalGroup_iff', transpose_reindex, ← reindex_mul', hO]
        ext i j; simp [one_apply]
      · rw [← reindex_mul', h2]
        ext i j; simp [one_apply]
    have h := (hB (Fintype.card ι) (reindex e e J₀) hcs).1 θ
    have h0 : NormedSpace.exp (θ • J₀) = Real.cos θ • (1 : Mat ι) + Real.sin θ • J₀ := by
      apply (reindex e e).injective
      rw [reindex_exp]
      have e1 : reindex e e (θ • J₀) = θ • reindex e e J₀ := by ext; simp
      rw [e1, mexp] at *
      rw [h]
      ext i j; simp [one_apply]
    have hconj : θ • J = S⁻¹ * (θ • J₀) * S := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
      congr 1
      simp only [hJ₀def, Matrix.mul_assoc]
      rw [hSi, Matrix.mul_one, ← Matrix.mul_assoc, hSi, Matrix.one_mul]
    rw [hconj, Matrix.exp_conj' S _ hSu, h0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hSi, Matrix.mul_smul, Matrix.smul_mul]
    congr 2
    simp only [hJ₀def, Matrix.mul_assoc]
    rw [hSi, Matrix.mul_one, ← Matrix.mul_assoc, hSi, Matrix.one_mul]
  refine ⟨@fun ι _ _ J hJ θ => key hJ θ, @fun ι _ _ J hJ => ?_⟩
  have := key hJ Real.pi
  rw [Real.cos_pi, Real.sin_pi, zero_smul, add_zero, neg_one_smul] at this
  exact this

#rt_check RoundTrip.V15_2.B_of_A_normalForm [Morse.exp_smul_of_mul_self_eq_neg_one,
  Morse.exp_pi_smul]
#rt_check RoundTrip.V15_2.B_to_A [Morse.exp_smul_of_mul_self_eq_neg_one, Morse.exp_pi_smul]
#rt_overlap RoundTrip.V15_2.B_to_A [Morse.exp_smul_of_mul_self_eq_neg_one, Morse.exp_pi_smul]

end RoundTrip.V15_2
