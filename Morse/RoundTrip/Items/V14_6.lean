import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_6

open Matrix Finset

namespace RoundTrip.V14_6

/-- The project's statement (universes of `ι` instantiated at `0`; `eReal`, `eImag`, `suDiag`,
`jacobiMat` are vocabulary): `E_jl`, `E'_jl` are eigenvectors of `K_A` with eigenvalue
`π²(k_j − k_l)²/4` and diagonal matrices are killed by `K_A` (any finite index type, any integers
`k_j`, any `j, l`, any complex diagonal), and every skew-Hermitian `W` is
`diag(w_jj) + Σ_{j<l} (Re w_jl E_jl + Im w_jl E'_jl)` (spanning only). -/
def A : Prop :=
  type_of% @Morse.jacobiMat_eReal.{0} ∧ type_of% @Morse.jacobiMat_eImag.{0} ∧
    type_of% @Morse.jacobiMat_diagonal.{0} ∧ type_of% @Morse.eq_diagonal_add_sum_eReal_eImag.{0}

theorem A_holds : A :=
  ⟨@Morse.jacobiMat_eReal.{0}, @Morse.jacobiMat_eImag.{0}, @Morse.jacobiMat_diagonal.{0},
    @Morse.eq_diagonal_add_sum_eReal_eImag.{0}⟩

section Vocab

variable {n : ℕ}

theorem milnorA_eq_suDiag (k : Fin n → ℤ) : milnorA k = Morse.suDiag k := by
  unfold milnorA diagI Morse.suDiag
  congr 1
  funext j
  push_cast
  rfl

theorem Kop_eq_jacobiMat (A W : Mat n) : Kop A W = Morse.jacobiMat A W := by
  unfold Kop Morse.jacobiMat
  rw [← Complex.coe_smul]
  push_cast
  rfl

theorem eReal_eq (j l : Fin n) : eReal j l = Morse.eReal j l := rfl

theorem eImag_eq (j l : Fin n) : eImag j l = Morse.eImag j l := rfl

/-- `Σ_{j<l} (x_jl E_jl + y_jl E'_jl)`. -/
noncomputable def S (x y : Pairs n → ℝ) : Mat n :=
  ∑ p : Pairs n, (x p • eReal p.1.1 p.1.2 + y p • eImag p.1.1 p.1.2)

/-- The `(j, l)` entry (`j < l`) of `S x y` is `x_jl + i y_jl`. -/
theorem S_apply_lt (x y : Pairs n → ℝ) {j l : Fin n} (h : j < l) :
    S x y j l = (x ⟨(j, l), h⟩ : ℂ) + (y ⟨(j, l), h⟩ : ℂ) * Complex.I := by
  unfold S
  rw [Matrix.sum_apply, Finset.sum_eq_single ⟨(j, l), h⟩]
  · simp [eReal, eImag, h.ne, h.ne', Complex.real_smul]
  · intro p _ hp
    have h1 : ¬ (p.1.1 = j ∧ p.1.2 = l) := by
      rintro ⟨h1, h2⟩
      apply hp
      apply Subtype.ext
      exact Prod.ext h1 h2
    have h2 : ¬ (p.1.2 = j ∧ p.1.1 = l) := by
      rintro ⟨h2, h3⟩
      have := p.2
      rw [h2, h3] at this
      exact absurd h (lt_asymm this)
    simp only [Matrix.add_apply, Matrix.smul_apply, eReal, eImag, Matrix.sub_apply,
      Matrix.single_apply, h1, h2, if_false, sub_zero, add_zero, smul_zero]
  · simp

/-- The double sum with `if j < l` is the sum over `Pairs n`. -/
theorem sum_ite_lt (f : Fin n → Fin n → Mat n) :
    (∑ j, ∑ l, if j < l then f j l else 0) = ∑ p : Pairs n, f p.1.1 p.1.2 := by
  rw [← Finset.sum_subtype (univ.filter fun q : Fin n × Fin n => q.1 < q.2)
    (by simp) (fun q => f q.1 q.2), Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]

end Vocab

theorem A_to_B : A → B := by
  rintro ⟨hA1, hA2, hA3, hA4⟩ n k _ _
  refine ⟨fun j l hjl => ⟨?_, ?_, ?_, ?_⟩, fun D hD => ?_, fun W hW => ?_⟩
  · exact ⟨Morse.eReal_conjTranspose j l, Morse.trace_eReal hjl.ne⟩
  · rw [Kop_eq_jacobiMat, milnorA_eq_suDiag, eReal_eq, hA1]; exact Complex.coe_smul _ _
  · exact ⟨Morse.eImag_conjTranspose j l, Morse.trace_eImag hjl.ne⟩
  · rw [Kop_eq_jacobiMat, milnorA_eq_suDiag, eImag_eq, hA2]; exact Complex.coe_smul _ _
  · have hDd : D = diagonal fun i => D i i := by
      ext i j
      by_cases h : i = j
      · subst h; simp
      · rw [diagonal_apply_ne _ h, hD.2 i j h]
    rw [Kop_eq_jacobiMat, milnorA_eq_suDiag, hDd]
    exact hA3 k _
  · -- existence from the project's spanning statement; uniqueness by reading off entries
    obtain ⟨hskew, htr⟩ := hW
    have hent : ∀ a b, W a b = -(starRingEnd ℂ) (W b a) := by
      intro a b
      have := congrFun (congrFun hskew a) b
      simp only [conjTranspose_apply, Matrix.neg_apply, RCLike.star_def] at this
      rw [this, neg_neg]
    set x : Pairs n → ℝ := fun p => (W p.1.1 p.1.2).re
    set y : Pairs n → ℝ := fun p => (W p.1.1 p.1.2).im
    have hdec : W = S x y + diagonal fun j => W j j := by
      have h := hA4 W hskew
      rw [sum_ite_lt (fun j l => ((W j l).re : ℂ) • Morse.eReal j l +
        ((W j l).im : ℂ) • Morse.eImag j l)] at h
      rw [add_comm, S]
      convert h using 3 with p
      rw [Complex.coe_smul, Complex.coe_smul]
      rfl
    have hDmem : (diagonal fun j => W j j) ∈ diagSU n := by
      refine ⟨⟨?_, ?_⟩, fun i j h => diagonal_apply_ne _ h⟩
      · rw [diagonal_conjTranspose, diagonal_neg]
        congr 1
        funext j
        simp only [Pi.star_apply, RCLike.star_def]
        have := hent j j
        linear_combination this
      · rw [trace_diagonal]
        exact htr
    refine ⟨⟨x, y, diagonal fun j => W j j⟩, ⟨hDmem, hdec⟩, ?_⟩
    rintro ⟨x', y', D'⟩ ⟨hD', hW'⟩
    change D' ∈ diagSU n at hD'
    change W = S x' y' + D' at hW'
    have hxy : x' = x ∧ y' = y := by
      constructor <;> funext p <;>
      · have h1 := congrFun (congrFun hW' p.1.1) p.1.2
        rw [Matrix.add_apply, S_apply_lt x' y' p.2, hD'.2 _ _ p.2.ne, add_zero] at h1
        simp only [x, y, h1, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        simp
    obtain ⟨rfl, rfl⟩ := hxy
    have hD : D' = diagonal fun j => W j j := by
      have h1 : S x y + D' = S x y + diagonal fun j => W j j := by rw [← hW', ← hdec]
      exact add_left_cancel h1
    rw [hD]

/-- `A` is proved outright (it is the project's computation, re-done here): `B` only covers odd
`k_j` (so `k_j − k_l` even), `j < l`, diagonal matrices of `𝔰𝔲(n)` and `W ∈ 𝔰𝔲(n)`. -/
theorem B_to_A : B → A := by
  intro _
  have hJ : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℤ) (W : Matrix ι ι ℂ) (j l : ι),
      Morse.jacobiMat (Morse.suDiag k) W j l =
        ((Real.pi ^ 2 / 4 * ((k j : ℝ) - k l) ^ 2 : ℝ) : ℂ) * W j l := by
    intro ι _ _ k W j l
    simp only [Morse.jacobiMat, Morse.suDiag, Matrix.smul_apply, Matrix.sub_apply, mul_diagonal,
      diagonal_mul, smul_eq_mul]
    push_cast
    linear_combination (-(1 / 4 : ℂ) * Real.pi ^ 2 * ((k j : ℂ) - k l) ^ 2 * W j l) * Complex.I_sq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ι _ _ k j l
    ext a b
    rw [hJ, Matrix.smul_apply, smul_eq_mul]
    simp only [Morse.eReal, Matrix.sub_apply, single_apply]
    by_cases h1 : j = a ∧ l = b
    · obtain ⟨rfl, rfl⟩ := h1; simp
    · by_cases h2 : l = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h2
        simp only [and_self, if_true]
        split_ifs
        push_cast
        ring
      · rw [if_neg h1, if_neg h2]; simp
  · intro ι _ _ k j l
    ext a b
    rw [hJ, Matrix.smul_apply, smul_eq_mul]
    simp only [Morse.eImag, Matrix.add_apply, single_apply]
    by_cases h1 : j = a ∧ l = b
    · obtain ⟨rfl, rfl⟩ := h1; simp
    · by_cases h2 : l = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h2
        simp only [and_self, if_true]
        split_ifs
        push_cast
        ring
      · rw [if_neg h1, if_neg h2]; simp
  · intro ι _ _ k d
    ext a b
    rw [hJ]
    by_cases h : a = b
    · subst h; simp
    · simp [diagonal_apply_ne _ h]
  · intro ι _ _ _ W hW
    have hskew : ∀ a b, W a b = -(starRingEnd ℂ) (W b a) := by
      intro a b
      have := congrFun (congrFun hW a) b
      simp only [conjTranspose_apply, Matrix.neg_apply, RCLike.star_def] at this
      rw [this, neg_neg]
    ext a b
    simp only [Matrix.add_apply, Matrix.sum_apply]
    have hterm : ∀ j l, (if j < l then (((W j l).re : ℂ) • Morse.eReal j l +
        ((W j l).im : ℂ) • Morse.eImag j l) else 0) a b =
        if j < l ∧ ((j = a ∧ l = b) ∨ (l = a ∧ j = b)) then W a b else 0 := by
      intro j l
      by_cases h1 : j < l
      · rw [if_pos h1]
        simp only [Matrix.add_apply, Matrix.smul_apply, Morse.eReal, Morse.eImag,
          Matrix.sub_apply, single_apply, smul_eq_mul]
        by_cases h2 : j = a ∧ l = b
        · obtain ⟨rfl, rfl⟩ := h2
          simp only [h1, h1.ne, h1.ne', and_self, true_or, if_true, if_false, sub_zero,
            add_zero, mul_one]
          conv_rhs => rw [← Complex.re_add_im (W j l)]
        · by_cases h3 : l = a ∧ j = b
          · obtain ⟨rfl, rfl⟩ := h3
            simp only [h1, h1.ne, h1.ne', and_self, or_true, if_true, if_false,
              zero_sub, zero_add, mul_neg, mul_one]
            rw [hskew l j]
            conv_rhs => rw [← Complex.re_add_im (W j l)]
            simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
            ring
          · simp [h2, h3]
      · rw [if_neg h1, if_neg (fun h => h1 h.1)]; rfl
    simp_rw [hterm]
    rcases lt_trichotomy a b with hab | rfl | hab
    · rw [diagonal_apply_ne _ hab.ne, zero_add, Finset.sum_eq_single a, Finset.sum_eq_single b]
      · simp [hab]
      · intro l _ hl
        rw [if_neg]
        rintro ⟨h0, ⟨-, h⟩ | ⟨h1, h2⟩⟩
        · exact hl h
        · subst h1; subst h2; exact absurd hab (not_lt.2 h0.le)
      · simp
      · intro j _ hj
        refine sum_eq_zero fun l _ => ?_
        rw [if_neg]
        rintro ⟨h0, ⟨h, -⟩ | ⟨h1, h2⟩⟩
        · exact hj h
        · subst h1; subst h2; exact absurd hab (not_lt.2 h0.le)
      · simp
    · simp only [diagonal_apply_eq]
      rw [Finset.sum_eq_zero, add_zero]
      intro j _
      refine sum_eq_zero fun l _ => ?_
      rw [if_neg]
      rintro ⟨h0, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> subst h1 <;> subst h2 <;> exact lt_irrefl _ h0
    · rw [diagonal_apply_ne _ hab.ne', zero_add, Finset.sum_eq_single b, Finset.sum_eq_single a]
      · simp [hab]
      · intro l _ hl
        rw [if_neg]
        rintro ⟨h0, ⟨h1, h2⟩ | ⟨h, -⟩⟩
        · subst h1; subst h2; exact absurd hab (not_lt.2 h0.le)
        · exact hl h
      · simp
      · intro j _ hj
        refine sum_eq_zero fun l _ => ?_
        rw [if_neg]
        rintro ⟨h0, ⟨h1, h2⟩ | ⟨-, h⟩⟩
        · subst h1; subst h2; exact absurd hab (not_lt.2 h0.le)
        · exact hj h
      · simp

#rt_check RoundTrip.V14_6.A_to_B [Morse.jacobiMat_eReal, Morse.jacobiMat_eImag, Morse.jacobiMat_diagonal, Morse.eq_diagonal_add_sum_eReal_eImag]
#rt_check RoundTrip.V14_6.B_to_A [Morse.jacobiMat_eReal, Morse.jacobiMat_eImag, Morse.jacobiMat_diagonal, Morse.eq_diagonal_add_sum_eReal_eImag]
#rt_overlap RoundTrip.V14_6.B_to_A [Morse.jacobiMat_eReal, Morse.jacobiMat_eImag, Morse.jacobiMat_diagonal, Morse.eq_diagonal_add_sum_eReal_eImag]
#rt_overlap RoundTrip.V14_6.A_to_B [Morse.jacobiMat_eReal, Morse.jacobiMat_eImag, Morse.jacobiMat_diagonal, Morse.eq_diagonal_add_sum_eReal_eImag]

end RoundTrip.V14_6
