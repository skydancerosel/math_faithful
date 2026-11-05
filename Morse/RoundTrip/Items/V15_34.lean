import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_34

open Matrix

namespace RoundTrip.V15_34

/-- The project's statement (universes instantiated at `0`, arbitrary finite index types, an
ARBITRARY real matrix `ii` with `ii² = −1`, not necessarily orthogonal or a product of the `J_α`):
`det_ℂ = Morse.cdet ii` is multiplicative on matrices commuting with `ii`, `det_ℂ 1 = 1`,
`|det_ℂ M| = 1` for orthogonal `M` commuting with `ii` (when also `iiᵀ = −ii`), and
`det_ℂ exp(tV) = e^{−√−1·t·tr(V·ii)/2}` for `V` commuting with `ii` with `tr V = 0`. -/
def A : Prop :=
  type_of% @Morse.cdet_mul.{0} ∧ type_of% @Morse.cdet_one.{0} ∧ type_of% @Morse.norm_cdet.{0} ∧
    type_of% @Morse.cdet_exp.{0}

theorem A_holds : A :=
  ⟨@Morse.cdet_mul.{0}, @Morse.cdet_one.{0}, @Morse.norm_cdet.{0}, @Morse.cdet_exp.{0}⟩

/-! ### Vocabulary: B's `cplx`, `projQ`, `cdet`, `ctr` are the project's `cplx`, `projP`, `cdet` -/

section Vocab
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem cplx_eq (X : Mat ι) : cplx X = Morse.cplx X := rfl

theorem projQ_eq (i : Mat ι) : projQ i = Morse.projP i := rfl

theorem one_sub_projQ (i : Mat ι) : 1 - projQ i = Morse.projM i := by
  rw [projQ_eq, ← Morse.projP_add_projM (ii := i), add_sub_cancel_left]

/-- B's `det_ℂ` (`det(UQ + I − Q)`) is the project's `det(U_ℂP₊ + P₋)`. -/
theorem cdet_eq (i U : Mat ι) : cdet i U = Morse.cdet i U := by
  rw [cdet, Morse.cdet, one_sub_projQ, cplx_eq, projQ_eq]

/-- B's `tr_ℂ A = tr(A_ℂ Q)` is `−√−1·tr(A·i)/2` for `tr A = 0`. -/
theorem ctr_eq (i A : Mat ι) (htr : trace A = 0) :
    ctr i A = (((-(trace (A * i)) / 2 : ℝ)) : ℂ) * Complex.I := by
  rw [ctr, projQ_eq, cplx_eq, Morse.projP, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_smul, trace_smul, trace_sub, trace_smul, ← map_mul, Morse.trace_cplx,
    Morse.trace_cplx, htr]
  push_cast
  simp only [smul_eq_mul]
  ring

/-! ### `i = J_1 ⋯ J_m` -/

theorem iProd_succ (Js : ℕ → Mat ι) (m : ℕ) : iProd Js (m + 1) = iProd Js m * Js (m + 1) := rfl

theorem iProd_mem_orth (Js : ℕ → Mat ι) :
    ∀ m, (∀ α, 1 ≤ α → α ≤ m → Js α ∈ orthogonalGroup ι ℝ) → iProd Js m ∈ orthogonalGroup ι ℝ
  | 0, _ => (orthogonalGroup ι ℝ).one_mem
  | m + 1, h => by
    rw [iProd_succ]
    exact (orthogonalGroup ι ℝ).mul_mem (iProd_mem_orth Js m fun α h1 h2 => h α h1 (by omega))
      (h (m + 1) (by omega) le_rfl)

theorem comm_iProd (Js : ℕ → Mat ι) (X : Mat ι) :
    ∀ m, (∀ α, 1 ≤ α → α ≤ m → Commute X (Js α)) → Commute X (iProd Js m)
  | 0, _ => Commute.one_right X
  | m + 1, h => by
    rw [iProd_succ]
    exact (comm_iProd Js X m fun α h1 h2 => h α h1 (by omega)).mul_right
      (h (m + 1) (by omega) le_rfl)

/-- `J_β (J_1 ⋯ J_m) = (−1)^m (J_1 ⋯ J_m) J_β` when `J_β` anticommutes with `J_1, …, J_m`. -/
theorem anti_iProd (Js : ℕ → Mat ι) (Y : Mat ι) :
    ∀ m, (∀ α, 1 ≤ α → α ≤ m → Y * Js α = -(Js α * Y)) →
      Y * iProd Js m = ((-1 : ℝ) ^ m) • (iProd Js m * Y)
  | 0, _ => by simp [iProd]
  | m + 1, h => by
    have ih := anti_iProd Js Y m fun α h1 h2 => h α h1 (by omega)
    rw [iProd_succ, ← Matrix.mul_assoc, ih, Matrix.smul_mul, Matrix.mul_assoc,
      h (m + 1) (by omega) le_rfl, Matrix.mul_neg, pow_succ, mul_neg_one, neg_smul, smul_neg,
      ← Matrix.mul_assoc]

/-- `(J_1 ⋯ J_m)² = (−1)^{m(m+1)/2}` for anticommuting complex structures. -/
theorem sq_iProd (Js : ℕ → Mat ι) :
    ∀ m, IsACFam Js m → iProd Js m * iProd Js m = ((-1 : ℝ) ^ (m * (m + 1) / 2)) • 1
  | 0, _ => by simp [iProd]
  | m + 1, h => by
    have hm : IsACFam Js m :=
      ⟨fun α h1 h2 => h.1 α h1 (by omega), fun α β h1 h2 h3 h4 hne => h.2 α β h1 (by omega) h3
        (by omega) hne⟩
    have ih := sq_iProd Js m hm
    have hanti := anti_iProd Js (Js (m + 1)) m fun α h1 h2 =>
      h.2 (m + 1) α (by omega) le_rfl h1 (by omega) (by omega)
    have hJJ : Js (m + 1) * Js (m + 1) = -1 := (h.1 (m + 1) (by omega) le_rfl).2
    have hdiv : (m + 1) * (m + 1 + 1) / 2 = m * (m + 1) / 2 + (m + 1) := by
      rw [show (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) by ring,
        Nat.add_mul_div_left _ _ two_pos]
    rw [iProd_succ]
    calc iProd Js m * Js (m + 1) * (iProd Js m * Js (m + 1))
        = iProd Js m * (Js (m + 1) * iProd Js m) * Js (m + 1) := by simp only [Matrix.mul_assoc]
      _ = ((-1 : ℝ) ^ m) • ((iProd Js m * iProd Js m) * (Js (m + 1) * Js (m + 1))) := by
          rw [hanti, Matrix.mul_smul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [ih, hJJ, hdiv, Matrix.smul_mul, Matrix.one_mul, smul_smul, smul_neg, ← neg_smul]
          congr 1
          ring

/-- For `m ≡ 1 (mod 4)`, `J_1 ⋯ J_m` is a complex structure. -/
theorem isCplxStr_iProd (Js : ℕ → Mat ι) (m : ℕ) (hm : m % 4 = 1) (h : IsACFam Js m) :
    IsCplxStr (iProd Js m) := by
  refine ⟨iProd_mem_orth Js m fun α h1 h2 => (h.1 α h1 h2).1, ?_⟩
  rw [sq_iProd Js m h]
  obtain ⟨q, rfl⟩ : ∃ q, m = 4 * q + 1 := ⟨m / 4, by omega⟩
  have : (4 * q + 1) * (4 * q + 1 + 1) / 2 = 2 * (4 * q * q + 3 * q) + 1 := by
    rw [show (4 * q + 1) * (4 * q + 1 + 1) = 2 * (2 * (4 * q * q + 3 * q) + 1) by ring]
    exact Nat.mul_div_cancel_left _ two_pos
  rw [this, pow_succ, pow_mul]
  simp

theorem transpose_eq_neg {J : Mat ι} (hJ : IsCplxStr J) : Jᵀ = -J := by
  have h1 : Jᵀ * J = 1 := by
    have := hJ.1
    rw [Matrix.mem_orthogonalGroup_iff'] at this
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  calc Jᵀ = Jᵀ * (J * -J) := by rw [Matrix.mul_neg, hJ.2, neg_neg, Matrix.mul_one]
    _ = -J := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

omit [DecidableEq ι] in
theorem trace_eq_zero_of_skew {A : Mat ι} (hA : IsSkew A) : trace A = 0 := by
  have h := congrArg trace hA
  rw [trace_transpose, trace_neg] at h
  linarith

end Vocab

/-- **A ⇒ B.** B's "`i` is a complex structure" (`J_1 ⋯ J_{k-1}` with `k − 1 ≡ 1 (mod 4)`) and
`f(J exp(πtA)) = det_ℂ(exp(πtA))` (`J⁻¹J = 1`) are elementary and not in A (proved here); the
claims about `det_ℂ` itself, `|det_ℂ U| = 1` and `det_ℂ exp(πtA) = e^{πt tr_ℂ A}`, are A's
`norm_cdet` and `cdet_exp`, after identifying B's `det_ℂ`, `tr_ℂ` with the project's. -/
theorem A_to_B : A → B := by
  rintro ⟨-, -, hnorm, hexp⟩
  intro n k Js hk hJs
  have hm : (k - 1) % 4 = 1 := by omega
  have hi := isCplxStr_iProd Js (k - 1) hm hJs
  set i := iProd Js (k - 1) with hidef
  have hskew := transpose_eq_neg hi
  refine ⟨hi, fun U hU hUi => ?_, fun J hJ A hA hAJ hAα t => ⟨?_, ?_⟩⟩
  · rw [cdet_eq]
    refine hnorm hi.2 hskew hUi.eq ?_
    have := hU
    rw [SetLike.mem_coe, Matrix.mem_orthogonalGroup_iff] at this
    simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using this
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hJ2 : J * J = -1 := hJ.1.2
    have hinv : J⁻¹ = -J := Matrix.inv_eq_right_inv (by rw [Matrix.mul_neg, hJ2, neg_neg])
    rw [fJ, hinv, ← Matrix.mul_assoc, Matrix.neg_mul, hJ2, neg_neg, Matrix.one_mul]
  · have hAi : A * i = i * A := (comm_iProd Js A (k - 1) hAα).eq
    have htr := trace_eq_zero_of_skew hA
    rw [cdet_eq, hexp hi.2 hAi htr, ctr_eq i A htr]
    congr 1
    push_cast
    ring

/-! ### B ⇒ A, only vacuously

A is a statement about an arbitrary `ii` with `ii² = −1` and arbitrary matrices commuting with it
(multiplicativity, `det_ℂ 1 = 1` and the exponential formula for every traceless `V`, not only for
skew `V` in Milnor's `T`); B has none of this (no multiplicativity at all, `|det_ℂ| = 1` only for
`i = J_1 ⋯ J_{k-1}`, the exponential formula only for `A ∈ T` and `i = J_1 ⋯ J_{k-1}`). A is
re-proved outright, by the project's argument (its auxiliary lemmas on `P₊`, `P₋`, Jacobi's
formula `det exp = e^{tr}` are reused; the item's four theorems are not). -/

section Outright
open scoped Morse.MatrixInner
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ii : Matrix ι ι ℝ}

theorem cdet_mul' (hii : ii * ii = -1) (M : Matrix ι ι ℝ) {N : Matrix ι ι ℝ}
    (hN : N * ii = ii * N) : Morse.cdet ii (M * N) = Morse.cdet ii M * Morse.cdet ii N := by
  rw [Morse.cdet, Morse.cdet, Morse.cdet, ← det_mul]
  congr 1
  have hPN := Morse.cplx_comm_projP hN
  have hQN := Morse.cplx_comm_projM hN
  have e1 : Morse.cplx M * Morse.projP ii * (Morse.cplx N * Morse.projP ii) =
      Morse.cplx M * Morse.cplx N * Morse.projP ii :=
    calc Morse.cplx M * Morse.projP ii * (Morse.cplx N * Morse.projP ii)
        = Morse.cplx M * (Morse.projP ii * Morse.cplx N) * Morse.projP ii := by
          simp only [Matrix.mul_assoc]
      _ = Morse.cplx M * (Morse.cplx N * Morse.projP ii) * Morse.projP ii := by rw [← hPN]
      _ = Morse.cplx M * Morse.cplx N * (Morse.projP ii * Morse.projP ii) := by
          simp only [Matrix.mul_assoc]
      _ = Morse.cplx M * Morse.cplx N * Morse.projP ii := by rw [Morse.projP_mul_projP hii]
  have e2 : Morse.cplx M * Morse.projP ii * Morse.projM ii = 0 := by
    rw [Matrix.mul_assoc, Morse.projP_mul_projM hii, Matrix.mul_zero]
  have e3 : Morse.projM ii * (Morse.cplx N * Morse.projP ii) = 0 := by
    rw [← Matrix.mul_assoc, ← hQN, Matrix.mul_assoc, Morse.projM_mul_projP hii, Matrix.mul_zero]
  rw [map_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3,
    Morse.projM_mul_projM hii, add_zero, zero_add]

theorem cdet_one' : Morse.cdet ii 1 = 1 := by
  rw [Morse.cdet, map_one, Matrix.one_mul, Morse.projP_add_projM, det_one]

theorem norm_cdet' (hii : ii * ii = -1) (hskew : iiᵀ = -ii) {M : Matrix ι ι ℝ}
    (hM : M * ii = ii * M) (horth : M * Mᵀ = 1) : ‖Morse.cdet ii M‖ = 1 := by
  have hMt : Mᵀ * ii = ii * Mᵀ := by
    have := congrArg transpose hM
    rw [transpose_mul, transpose_mul, hskew, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at this
    exact this.symm
  have h := Complex.mul_conj (Morse.cdet ii M)
  rw [Morse.conj_cdet hskew hM, ← cdet_mul' hii M hMt, horth, cdet_one'] at h
  have h2 : Complex.normSq (Morse.cdet ii M) = 1 := by exact_mod_cast h.symm
  rw [Complex.normSq_eq_norm_sq] at h2
  have := norm_nonneg (Morse.cdet ii M)
  nlinarith

theorem cdet_exp' (hii : ii * ii = -1) {V : Matrix ι ι ℝ} (hV : V * ii = ii * V)
    (htr : trace V = 0) (t : ℝ) :
    Morse.cdet ii (NormedSpace.exp (t • V)) =
      Complex.exp (((-(t * trace (V * ii)) / 2 : ℝ) : ℂ) * Complex.I) := by
  set W := Morse.cplx V with hW
  have hWP : W * Morse.projP ii = Morse.projP ii * W := Morse.cplx_comm_projP hV
  have hWM : W * Morse.projM ii = Morse.projM ii * W := Morse.cplx_comm_projM hV
  have hmap : ∀ s : ℝ, Morse.cplx (NormedSpace.exp (s • V)) = NormedSpace.exp (s • W) :=
    fun s => by
      rw [NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (Morse.cplx (ι := ι)) Morse.continuous_cplx _
        (by rw [NormedSpace.expSeries_radius_eq_top]; exact edist_lt_top _ _), Morse.cplx_smul]
  set c : ℝ → Matrix ι ι ℂ := fun s => NormedSpace.exp (s • W) * Morse.projP ii + Morse.projM ii
    with hcdef
  have hc : ∀ s, HasDerivAt c (c s * (W * Morse.projP ii)) s := fun s => by
    refine ((hasDerivAt_exp_smul_const W s).mul_const (Morse.projP ii)).add_const (Morse.projM ii)
      |>.congr_deriv ?_
    have e1 : Morse.projM ii * (W * Morse.projP ii) = 0 := by
      rw [← Matrix.mul_assoc, ← hWM, Matrix.mul_assoc, Morse.projM_mul_projP hii,
        Matrix.mul_zero]
    have e2 : NormedSpace.exp (s • W) * Morse.projP ii * (W * Morse.projP ii) =
        NormedSpace.exp (s • W) * W * Morse.projP ii :=
      calc NormedSpace.exp (s • W) * Morse.projP ii * (W * Morse.projP ii)
          = NormedSpace.exp (s • W) * (Morse.projP ii * W) * Morse.projP ii := by
            simp only [Matrix.mul_assoc]
        _ = NormedSpace.exp (s • W) * (W * Morse.projP ii) * Morse.projP ii := by rw [← hWP]
        _ = NormedSpace.exp (s • W) * W * (Morse.projP ii * Morse.projP ii) := by
            simp only [Matrix.mul_assoc]
        _ = NormedSpace.exp (s • W) * W * Morse.projP ii := by rw [Morse.projP_mul_projP hii]
    simp only [hcdef]
    rw [Matrix.add_mul, e1, e2, add_zero]
  have hc0 : c 0 = 1 := by simp [hcdef, Morse.projP_add_projM]
  have hct := Morse.eq_mul_exp_smul_of_hasDerivAt_cplx hc t
  rw [hc0, Matrix.one_mul] at hct
  rw [Morse.cdet, hmap,
    show NormedSpace.exp (t • W) * Morse.projP ii + Morse.projM ii = c t from rfl, hct,
    Morse.det_exp_smul_cplx]
  congr 1
  rw [Morse.projP, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, trace_smul,
    trace_sub, trace_smul, hW, ← map_mul, Morse.trace_cplx, Morse.trace_cplx, htr]
  push_cast
  simp only [smul_eq_mul]
  ring

end Outright

theorem B_to_A : B → A := fun _ =>
  ⟨@cdet_mul', @cdet_one', @norm_cdet', @cdet_exp'⟩

#rt_check RoundTrip.V15_34.A_to_B [Morse.cdet_mul, Morse.cdet_one, Morse.norm_cdet, Morse.cdet_exp]
#rt_check RoundTrip.V15_34.B_to_A [Morse.cdet_mul, Morse.cdet_one, Morse.norm_cdet, Morse.cdet_exp]
#rt_overlap RoundTrip.V15_34.B_to_A [Morse.cdet_mul, Morse.cdet_one, Morse.norm_cdet,
  Morse.cdet_exp]

end RoundTrip.V15_34
