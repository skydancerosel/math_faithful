import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Set.Card

/-!
Milnor, *Morse Theory*, §23 (The Bott periodicity theorem for the unitary group), pp. 126–132,
and the index counts of §24, pp. 134–135 and 144–148.

# The index of a geodesic from `I` to `-I`: the combinatorial core

## Milnor's text, paraphrased

* **Geodesics from `I` to `-I`** (pp. 126–127).  After conjugating by a unitary matrix, a
  skew-Hermitian `A` is `diag(i a_1, …, i a_n)` with `a_j` real, and `exp A = -I` exactly when
  `A = diag(iπk_1, …, iπk_n)` with every `k_j` an odd integer.  The geodesic `t ↦ exp tA`,
  `0 ≤ t ≤ 1`, has length `|A| = (tr AA*)^{1/2} = π(k_1² + ⋯ + k_n²)^{1/2}`, so it is minimal
  iff every `k_j = ±1`, of length `π√n`.  In `SU(2m)` the extra condition `tr A = 0`, i.e.
  `Σ k_j = 0`, forces `m` of each sign (p. 127): this is Lemma 23.1, the minimal geodesics form
  `G_m(ℂ^{2m})`.
* **The operator `K_A`** (pp. 130–131).  By 20.5 the conjugate points are governed by
  `K_A(W) = R(A,W)A = ¼[[A,W],A]` on `𝔰𝔲(n)`.  For `A = diag(iπk_1, …, iπk_n)`,
  `k_1 ≥ ⋯ ≥ k_n`, "a short computation" gives `[A,W] = (iπ(k_j − k_l) w_{jl})` and
  `K_A(W) = (π²/4 (k_j − k_l)² w_{jl})`.  Eigenvectors: for `j < l` the matrix `E_{jl}`
  (`+1` at `(j,l)`, `-1` at `(l,j)`) and `E'_{jl}` (`+i` at both places), with eigenvalue
  `π²(k_j − k_l)²/4`, and the diagonal matrices, with eigenvalue `0`.  So the non-zero
  eigenvalues are the `π²(k_j − k_l)²/4` with `k_j > k_l`, each counted twice.
* **The count** (p. 131).  An eigenvalue `e > 0` gives conjugate points at `t = π/√e, 2π/√e, …`,
  here `t = 2/(k_j − k_l), 4/(k_j − k_l), …`, and "the number of such values of `t` in the open
  interval `(0,1)` is evidently `(k_j − k_l)/2 − 1`".  By the Index Theorem each pair
  `k_j > k_l` contributes `2((k_j − k_l)/2 − 1)`, whence **the index formula**
  `λ = Σ_{k_j > k_l} (k_j − k_l − 2)`.
* **Lemma 23.2** (pp. 131–132).  For a minimal geodesic all `k_j = ±1` and `λ = 0`.  Let
  `n = 2m` and the geodesic be non-minimal.  *Case 1*: at least `m + 1` of the `k_j` are (say)
  negative; then some positive `k_j` is `≥ 3` and `λ ≥ Σ_1^{m+1} (3 − (−1) − 2) = 2(m+1)`.
  *Case 2*: `m` are positive and `m` negative, not all `±1`; then one is `≥ 3` and one is
  `≤ −3`, and `λ ≥ (m−1)·2 + (m−1)·2 + 4 = 4m ≥ 2(m+1)`.  So **every non-minimal geodesic from
  `I` to `-I` in `SU(2m)` has index `≥ 2m + 2`**.
* **`O(2m)`, Lemma 24.2** (pp. 134–135).  Up to conjugacy the geodesic is `t ↦ exp(πtA)` with
  `A` block diagonal with blocks `a_j (0 1; −1 0)`, `a_1 ≥ ⋯ ≥ a_m > 0` odd, `⟨A,A⟩ = 2Σa_j²`,
  minimal iff all `a_j = 1`.  The non-zero eigenvalues of `K_A` are `(a_i + a_j)²/4` (`i < j`)
  and `(a_i − a_j)²/4` (`a_i > a_j`), each twice, so
  `λ = Σ_{i<j} (a_i + a_j − 2) + Σ_{a_i > a_j} (a_i − a_j − 2)`; non-minimal means `a_1 ≥ 3`,
  and `λ ≥ Σ_{j=2}^m (3 + 1 − 2) = 2m − 2`.
* **§24, `k ≢ 2 (mod 4)`** (pp. 145–146).  `K_A` has at least `s − 1` eigenvalues
  `(a_{h₀} + a_j)²/4 ≥ 4`, and each eigenvalue `e² ≥ 4` gives a conjugate point `t = 1/e` in
  `(0,1)`; hence the index is `≥ s − 1`.
* **§24, `k ≡ 2 (mod 4)`** (pp. 147–148).  With odd integers `a_1, …, a_r` (now of both signs),
  `Σ a_h = c` and some `|a_h| ≥ 3`: `2λ ≥ Σ_{a_h > a_j} (a_h − a_j − 2)`, and with `p`, `−q`
  the sums of the positive and negative `a_h`, `p − q = c`, `p + q ≥ r`, Milnor concludes
  `4λ ≥ 2p ≥ r + c`.

## What is formalized

The geometry (Theorems 15.1, 20.5, 21.3, the spectral theorem and the reduction to diagonal `A`)
is the input, and enters only through the definitions below; everything downstream of it is
proved.  For `SU(n)` the input is proved in `Morse/Chapter12/SUIndex.lean`:
`Morse.conjMultiplicity_su` and `Morse.finrank_hadKer` (Theorem 20.5 for the submanifold
`SU(n) ⊆ Mₙ(ℂ)`: the multiplicity of a conjugate parameter is `conjMult (suSpectrum k)`) and
`Morse.index_su_eq_bottIndex` (through the project's Index Theorem `Morse.theorem_15_1`: the index
of every geodesic from `I` to `−I` in `SU(n)` is `bottIndex k`).

* `Morse.conjParams e`: the parameters `t ∈ (0,1)` of the conjugate points produced by an
  eigenvalue `e` of `K_V` (Theorem 20.5): `t = πs/√e`, `s ∈ ℤ`, and none if `e ≤ 0`.
  `Morse.ncard_conjParams_sq`: for `e = (πd)²`, `d ≥ 1` an integer, there are exactly `d − 1`
  (Milnor's "evidently").
* `Morse.spectralIndex e`: for a spectrum `e : κ → ℝ` (eigenvalues with multiplicity), the sum
  over `t ∈ (0,1)` of the multiplicity `#{i | t ∈ conjParams (e i)}` of `γ(t)` as a conjugate
  point (Theorem 20.5), i.e. the index by the Index Theorem 15.1.  `Morse.spectralIndex_eq`:
  it is `Σ_i #conjParams (e i)`, the interchange of summations behind Milnor's "adding over all
  `j, l`".  `Morse.spectralIndex_double`: a spectrum in which every eigenvalue occurs twice has
  index `2 ×` (Bott's "conjugate points occur in pairs", 21.7); `Morse.even_spectralIndex`: if
  every positive eigenvalue has even multiplicity the index is even (with
  `Morse.even_finrank_eigenspace` of `Morse/Chapter12/BiInvariant.lean` this is 21.7's "the
  index of any geodesic is even").
* `Morse.bottIndex k = Σ_{k_i > k_j} (k_i − k_j − 2)`, the index formula as a definition, and
  `Morse.spectralIndex_suSpectrum`: it is the index computed from Milnor's spectrum
  `π²(k_i − k_j)²/4` (`k_i > k_j`, each twice).
* The matrix computations behind the spectrum (`exp A = −I`, `K_A` for diagonal `A`, Milnor's
  eigenvectors, minimal geodesics as Hermitian projections) are in
  `Morse/Chapter14/SUMatrices.lean`.
* Minimal geodesics: `Morse.card_le_sum_sq` and `Morse.sum_sq_eq_card_iff` (`Σ k_j² ≥ n`, with
  equality iff all `k_j = ±1`), `Morse.card_eq_of_minimal` (then `m` of each sign in `SU(2m)`),
  `Morse.bottIndex_eq_zero_of_minimal`.
* **Lemma 23.2**: `Morse.bottIndex_ge`.
* The `U(n)` remark (Chapter 14 of the exposition, §2): `k = (3, 1, …, 1)` has index `0`
  (`Morse.bottIndex_remarkK`), is not minimal, and `Σ k_j = n + 2` while every minimal `k` has
  `|Σ k_j| ≤ n` (`Morse.abs_sum_le_card_of_minimal`); `Σ k_j` is the degree of `det` along the
  geodesic, a homotopy invariant of the path (this last fact is topology, not formalized).
* **Lemma 24.2**: `Morse.bottIndexO`, `Morse.spectralIndex_oSpectrum`,
  `Morse.bottIndexO_eq_zero`, `Morse.bottIndexO_ge`.
* §24: `Morse.card_lt_le_spectralIndex` and `Morse.card_sub_one_le_spectralIndex`
  (`k ≢ 2 mod 4`); `Morse.card_sub_abs_sum_le_two_mul_bottIndex` and
  `Morse.card_sub_abs_sum_le_four_mul_spectralIndex` (`k ≡ 2 mod 4`: `4λ ≥ r − |c|`).

Not formalized in this file: the Riemannian input listed above (that every geodesic from `I` to
`-I` is conjugate, by an isometry fixing `±I`, to one with diagonal `A`; Theorems 15.1, 20.5, 21.3
on `SU(n)` — for `SU(n)` see `Morse/Chapter12/`); the linear independence of Milnor's eigenvectors and hence the bookkeeping "spectrum
with multiplicity = values on an eigenbasis"; and all topology (Lemma 23.1 as a homeomorphism,
Theorem 23.3 and the homotopy groups).

## Gaps in Milnor's text

* p. 131, "evidently `(k_j − k_l)/2 − 1`": uses that `k_j − k_l` is even (both are odd), so
  that the conjugate parameters `t = 2s/(k_j − k_l)` of the pair (the `t` with
  `((k_j − k_l)/2)·t ∈ ℤ`) lying in `(0,1)` are those with `s = 1, …, (k_j − k_l)/2 − 1`.
* p. 131, "adding over all `j, l`": the Index Theorem sums multiplicities over conjugate
  *points* `t`; Theorem 20.5 gives the multiplicity of `t` as the number of eigenvalues whose
  conjugate parameters contain `t`, and the formula needs the interchange of the two finite
  sums (`Morse.spectralIndex_eq`).
* p. 131, the eigenbasis: Milnor lists the eigenvectors but does not say why they span
  (`Morse.eq_diagonal_add_sum_eReal_eImag`).
* p. 132, Case 1, "(say) negative": the case of `m + 1` positive `k_j` follows because the
  formula is invariant under `k ↦ −k` (`Morse.bottIndex_neg`); and "one of the positive `k_i`
  must be `≥ 3`" uses `Σ k_j = 0`.  Here both cases are handled through the sum over all
  (positive, negative) pairs, which equals `N·S + P·S − 2PN` (`P`, `N` the numbers of positive
  and negative `k_j`, `S` the sum of the positive ones); this reproduces Milnor's bounds `2N`
  and `4m` exactly.
* p. 132, Case 2, "then one is `≥ 3` and one is `≤ −3`": uses `Σ k_j = 0` and `P = N = m`.
* p. 127, `U(n)` is "rather inconvenient": worse, `k = (3,1,…,1)` is a non-minimal geodesic of
  index `0` in a component of the path space without minimal geodesics, so Theorem 22.1 cannot
  be applied to `U(n)` at all.
* p. 135, Lemma 24.2: Milnor speaks of eigenvalues of `K_A` but the velocity is `πA`; the
  conjugate points come from `K_{πA} = π² K_A`, whose eigenvalues `π²(a_i ± a_j)²/4` are the
  ones used in `Morse.oSpectrum`.
* p. 148: Milnor treats only "some `a_h` equal to `−3`"; the case of some `a_h ≥ 3` gives
  `4λ ≥ r − c` instead, so in general `4λ ≥ r − |c|`.  His displayed chain
  `Σ (a_h − a_j − 2) > Σ_{a_h > 0} (a_h − (−3) − 3) = p` uses `−3` for `−2` and a strict
  inequality, which fails when no `a_h` is positive (both sides are then `0`); the correct
  bound is `Σ_{a_h > 0} (a_h + 1) ≥ p`.
-/

open Finset Real

noncomputable section

namespace Morse

/-! ### Conjugate points from a spectrum (Theorems 20.5 and 15.1) -/

/-- The parameters `t ∈ (0,1)` at which an eigenvalue `e` of `K_V` produces a conjugate point
along `t ↦ γ(t)` (Milnor's Theorem 20.5): `t = π s / √e` with `s ∈ ℤ`, and none if `e ≤ 0`. -/
def conjParams (e : ℝ) : Set ℝ :=
  {t | 0 < e ∧ 0 < t ∧ t < 1 ∧ ∃ s : ℤ, t = π * s / √e}

theorem conjParams_subset (e : ℝ) :
    conjParams e ⊆ (fun s : ℤ => π * s / √e) '' Set.Ioo 0 ⌈√e / π⌉ := by
  rintro t ⟨he, ht0, ht1, s, rfl⟩
  have hse : 0 < √e := Real.sqrt_pos.2 he
  refine ⟨s, ⟨?_, ?_⟩, rfl⟩
  · have : 0 < π * s := by
      rcases div_pos_iff.1 ht0 with h | h
      · exact h.1
      · exact absurd h.2 (not_lt.2 hse.le)
    have : (0 : ℝ) < s := pos_of_mul_pos_right this pi_pos.le
    exact_mod_cast this
  · rw [Int.lt_ceil, lt_div_iff₀ pi_pos]
    rw [div_lt_one hse] at ht1
    linarith

theorem conjParams_finite (e : ℝ) : (conjParams e).Finite :=
  ((Set.finite_Ioo _ _).image _).subset (conjParams_subset e)

/-- For `e = (π d)²` the conjugate parameters in `(0,1)` are `1/d, 2/d, …, (d−1)/d`. -/
theorem conjParams_sq (d : ℕ) (hd : 0 < d) :
    conjParams ((π * d) ^ 2) = ((Finset.Ioo 0 d).image fun s : ℕ => (s : ℝ) / d : Set ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpd : 0 < π * d := mul_pos pi_pos hdR
  ext t
  simp only [conjParams, Real.sqrt_sq hpd.le, Set.mem_ofPred_eq, coe_image, coe_Ioo,
    Set.mem_image, Set.mem_Ioo]
  constructor
  · rintro ⟨-, ht0, ht1, s, rfl⟩
    have e1 : π * (s : ℝ) / (π * d) = s / d := by field_simp
    rw [e1] at ht0 ht1 ⊢
    have hs0 : (0 : ℝ) < s := by
      rcases div_pos_iff.1 ht0 with h | h
      · exact h.1
      · exact absurd h.2 (not_lt.2 hdR.le)
    have hs1 : (s : ℝ) < d := by rwa [div_lt_one hdR] at ht1
    have hs0' : 0 < s := by exact_mod_cast hs0
    refine ⟨s.toNat, ⟨by omega, ?_⟩, ?_⟩
    · have : s < (d : ℤ) := by exact_mod_cast hs1
      omega
    · have : ((s.toNat : ℕ) : ℝ) = (s : ℝ) := by
        have : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hs0'.le
        exact_mod_cast this
      rw [this]
  · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
    refine ⟨by positivity, by positivity, ?_, s, ?_⟩
    · rw [div_lt_one hdR]; exact_mod_cast hs1
    · push_cast; field_simp

/-- **Milnor p. 131, "evidently"**: an eigenvalue `(π d)²`, `d ≥ 1` an integer, produces exactly
`d − 1` conjugate points in the open interval `(0,1)`. -/
theorem ncard_conjParams_sq (d : ℕ) (hd : 0 < d) : (conjParams ((π * d) ^ 2)).ncard = d - 1 := by
  rw [conjParams_sq d hd, Set.ncard_coe_finset, card_image_of_injective, Nat.card_Ioo]
  · simp
  · intro a b h
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [div_left_inj' hdR, Nat.cast_inj] at h
    exact h

section Spectrum

variable {κ : Type*} [Fintype κ]

open Classical in
/-- The multiplicity of `γ(t)` as a conjugate point, for a spectrum `e : κ → ℝ` of `K_V`
(eigenvalues with multiplicity): the number of eigenvalues whose conjugate parameters contain
`t` (Theorem 20.5). -/
def conjMult (e : κ → ℝ) (t : ℝ) : ℕ := #{i | t ∈ conjParams (e i)}

/-- The index of the geodesic `γ : [0,1] → M`, computed from the spectrum `e` of `K_V` by the
Index Theorem 15.1: the number of conjugate points `γ(t)`, `0 < t < 1`, counted with
multiplicity. -/
def spectralIndex (e : κ → ℝ) : ℕ := ∑ᶠ t, conjMult e t

/-- **Adding over the eigenvalues** (Milnor p. 131): the index is the sum, over the eigenvalues
with multiplicity, of the number of conjugate parameters each produces in `(0,1)`. -/
theorem spectralIndex_eq (e : κ → ℝ) : spectralIndex e = ∑ i, (conjParams (e i)).ncard := by
  classical
  set T : Finset ℝ := univ.biUnion fun i => (conjParams_finite (e i)).toFinset with hT
  have hsupp : Function.support (conjMult e) ⊆ T := by
    intro t ht
    simp only [Function.mem_support, conjMult, ne_eq, card_eq_zero, filter_eq_empty_iff,
      mem_univ, true_imp_iff, not_forall, not_not] at ht
    obtain ⟨i, hi⟩ := ht
    simp only [hT, coe_biUnion, coe_univ, Set.mem_univ, Set.iUnion_true, Set.Finite.coe_toFinset,
      Set.mem_iUnion]
    exact ⟨i, hi⟩
  rw [spectralIndex, finsum_eq_sum_of_support_subset _ hsupp]
  simp only [conjMult, card_filter]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← card_filter, Set.ncard_eq_toFinset_card _ (conjParams_finite (e i))]
  congr 1
  ext t
  simp only [mem_filter, Set.Finite.mem_toFinset, and_iff_right_iff_imp]
  intro ht
  simp only [hT, mem_biUnion, mem_univ, true_and, Set.Finite.mem_toFinset]
  exact ⟨i, ht⟩

/-- Every eigenvalue `e > π²` produces a conjugate point `t = π/√e` in `(0,1)`; so the index is
at least the number of such eigenvalues (Milnor p. 146: "if `e² ≥ 4` then one obtains at least
one interior conjugate point", for the eigenvalue `π²e²` of `K_{πA}`). -/
theorem card_lt_le_spectralIndex (e : κ → ℝ) :
    #{i | π ^ 2 < e i} ≤ spectralIndex e := by
  rw [spectralIndex_eq, card_filter]
  refine sum_le_sum fun i _ => ?_
  split_ifs with h
  · have he : 0 < e i := lt_trans (by positivity) h
    have hs : π < √(e i) := by
      rw [← Real.sqrt_sq pi_pos.le]
      exact Real.sqrt_lt_sqrt (by positivity) h
    have hmem : π * ((1 : ℤ) : ℝ) / √(e i) ∈ conjParams (e i) := by
      refine ⟨he, by simp [pi_pos, Real.sqrt_pos.2 he], ?_, 1, rfl⟩
      rw [Int.cast_one, mul_one, div_lt_one (Real.sqrt_pos.2 he)]
      exact hs
    exact (Set.ncard_pos (conjParams_finite (e i))).2 ⟨_, hmem⟩
  · exact Nat.zero_le _

/-- A spectrum in which every eigenvalue occurs twice has twice the index: Bott's "the
conjugate points occur in pairs" (proof of 21.7). -/
theorem spectralIndex_double (e : κ → ℝ) :
    spectralIndex (fun q : κ × Fin 2 => e q.1) = 2 * spectralIndex e := by
  rw [spectralIndex_eq, spectralIndex_eq, Fintype.sum_prod_type, mul_sum]
  simp [two_mul]

/-- **Bott's evenness** (proof of 21.7): if every positive eigenvalue of `K_V` occurs with even
multiplicity, the index is even. -/
theorem even_spectralIndex (e : κ → ℝ) (h : ∀ μ, 0 < μ → Even #{i | e i = μ}) :
    Even (spectralIndex e) := by
  classical
  rw [spectralIndex_eq, sum_comp (fun μ => (conjParams μ).ncard) e]
  refine even_sum _ fun μ _ => ?_
  rcases le_or_gt μ 0 with hμ | hμ
  · have : conjParams μ = ∅ := Set.eq_empty_of_forall_notMem fun t ht => not_lt.2 hμ ht.1
    simp [this]
  · rw [smul_eq_mul]
    exact (h μ hμ).mul_right _

end Spectrum

/-! ### The index formula -/

section IndexFormula

variable {ι : Type*} [Fintype ι]

/-- **Milnor's index formula** (p. 131): `λ = Σ_{k_i > k_j} (k_i − k_j − 2)`, the sum over the
ordered pairs `(i, j)` with `k_i > k_j`, i.e. over the unordered pairs with `k_i ≠ k_j`, the
larger first. -/
def bottIndex (k : ι → ℤ) : ℤ :=
  ∑ i, ∑ j, if k j < k i then k i - k j - 2 else 0

omit [Fintype ι] in
theorem two_le_sub_of_odd {a b : ℤ} (ha : Odd a) (hb : Odd b) (h : b < a) : 2 ≤ a - b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  omega

omit [Fintype ι] in
theorem bottIndex_term_nonneg {k : ι → ℤ} (hk : ∀ i, Odd (k i)) (i j : ι) :
    0 ≤ if k j < k i then k i - k j - 2 else 0 := by
  split_ifs with h
  · linarith [two_le_sub_of_odd (hk i) (hk j) h]
  · exact le_rfl

/-- Every term of the index formula is `≥ 0` (the `k_j` being odd). -/
theorem bottIndex_nonneg {k : ι → ℤ} (hk : ∀ i, Odd (k i)) : 0 ≤ bottIndex k :=
  sum_nonneg fun i _ => sum_nonneg fun j _ => bottIndex_term_nonneg hk i j

/-- The formula is invariant under `k ↦ −k` (Milnor's "(say) negative", p. 132). -/
theorem bottIndex_neg (k : ι → ℤ) : bottIndex (-k) = bottIndex k := by
  unfold bottIndex
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  simp only [Pi.neg_apply, neg_lt_neg_iff]
  split_ifs <;> ring

/-- The formula does not depend on the order of the `k_j` (Milnor's `k_1 ≥ k_2 ≥ ⋯ ≥ k_n`). -/
theorem bottIndex_comp_equiv {ι' : Type*} [Fintype ι'] (k : ι → ℤ) (e : ι' ≃ ι) :
    bottIndex (k ∘ e) = bottIndex k := by
  unfold bottIndex
  rw [← Equiv.sum_comp e]
  refine sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp e (fun j => if k j < k (e i) then k (e i) - k j - 2 else 0)

theorem bottIndex_eq_sum_subtype (k : ι → ℤ) :
    bottIndex k = ∑ p : {p : ι × ι // k p.2 < k p.1}, (k p.1.1 - k p.1.2 - 2) := by
  classical
  unfold bottIndex
  rw [← Fintype.sum_prod_type' (fun i j => if k j < k i then k i - k j - 2 else 0),
    ← sum_filter]
  exact sum_subtype _ (fun p => by simp) (fun p : ι × ι => k p.1 - k p.2 - 2)

/-- For odd `b < a`, the eigenvalue `π²(a − b)²/4` produces `(a − b)/2 − 1` conjugate points in
`(0,1)`; twice that is `a − b − 2`. -/
theorem two_mul_ncard_conjParams {a b : ℤ} (ha : Odd a) (hb : Odd b) (h : b < a) :
    2 * ((conjParams (π ^ 2 / 4 * ((a : ℝ) - b) ^ 2)).ncard : ℤ) = a - b - 2 := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  set d : ℕ := (x - y).toNat with hd
  have hd' : (d : ℤ) = x - y := Int.toNat_of_nonneg (by omega)
  have hd0 : 0 < d := by omega
  have he : π ^ 2 / 4 * (((2 * x + 1 : ℤ) : ℝ) - ((2 * y + 1 : ℤ) : ℝ)) ^ 2 = (π * d) ^ 2 := by
    have : ((d : ℤ) : ℝ) = (x : ℝ) - y := by rw [hd']; push_cast; ring
    rw [show ((d : ℕ) : ℝ) = ((d : ℤ) : ℝ) by norm_cast, this]
    push_cast; ring
  rw [he, ncard_conjParams_sq d hd0]
  push_cast [Nat.one_le_iff_ne_zero.2 hd0.ne']
  omega

/-- One eigenvalue `π²(k_i − k_j)²/4` for each pair `k_i > k_j`. -/
def pairSpectrum (k : ι → ℤ) : {p : ι × ι // k p.2 < k p.1} → ℝ :=
  fun p => π ^ 2 / 4 * ((k p.1.1 : ℝ) - k p.1.2) ^ 2

theorem two_mul_spectralIndex_pairSpectrum {k : ι → ℤ} (hk : ∀ i, Odd (k i)) :
    2 * (spectralIndex (pairSpectrum k) : ℤ) = bottIndex k := by
  rw [spectralIndex_eq, bottIndex_eq_sum_subtype, Nat.cast_sum, mul_sum]
  exact sum_congr rfl fun p _ => two_mul_ncard_conjParams (hk p.1.1) (hk p.1.2) p.2

/-- Milnor's spectrum of `K_A` for `A = diag(iπk_1, …, iπk_n)` (p. 131): the positive
eigenvalues are the `π²(k_i − k_j)²/4` with `k_i > k_j`, each counted twice. -/
def suSpectrum (k : ι → ℤ) : {p : ι × ι // k p.2 < k p.1} × Fin 2 → ℝ :=
  fun q => pairSpectrum k q.1

/-- **The index formula from the spectrum** (p. 131): Theorems 20.5 and 15.1 applied to Milnor's
spectrum of `K_A` give `λ = Σ_{k_i > k_j} (k_i − k_j − 2)`. -/
theorem spectralIndex_suSpectrum {k : ι → ℤ} (hk : ∀ i, Odd (k i)) :
    (spectralIndex (suSpectrum k) : ℤ) = bottIndex k := by
  rw [show suSpectrum k = fun q => pairSpectrum k q.1 from rfl, spectralIndex_double,
    Nat.cast_mul, Nat.cast_ofNat, two_mul_spectralIndex_pairSpectrum hk]

/-! ### Minimal geodesics (pp. 127–128, 131–132) -/

omit [Fintype ι] in
theorem one_le_sq_of_odd {a : ℤ} (ha : Odd a) : 1 ≤ a ^ 2 := by
  have h0 : a ≠ 0 := by rintro rfl; simp at ha
  have h1 := Int.one_le_abs h0
  nlinarith [sq_abs a]

omit [Fintype ι] in
theorem sq_eq_one_iff' {a : ℤ} : a ^ 2 = 1 ↔ a = 1 ∨ a = -1 := by
  rw [sq, mul_self_eq_one_iff]

/-- The energy `|A|² = π² Σ k_j²` of a geodesic from `I` to `-I` is at least `π² n` (p. 127). -/
theorem card_le_sum_sq {k : ι → ℤ} (hk : ∀ i, Odd (k i)) :
    (Fintype.card ι : ℤ) ≤ ∑ i, k i ^ 2 := by
  rw [← Finset.card_univ, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact sum_le_sum fun i _ => one_le_sq_of_odd (hk i)

/-- **Minimal geodesics** (p. 127): the energy bound is attained exactly when every `k_j = ±1`. -/
theorem sum_sq_eq_card_iff {k : ι → ℤ} (hk : ∀ i, Odd (k i)) :
    ∑ i, k i ^ 2 = Fintype.card ι ↔ ∀ i, k i = 1 ∨ k i = -1 := by
  rw [← Finset.card_univ, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, eq_comm,
    sum_eq_sum_iff_of_le fun i _ => one_le_sq_of_odd (hk i)]
  simp only [mem_univ, true_imp_iff]
  exact forall_congr' fun i => by rw [eq_comm, sq_eq_one_iff']

/-- In `SU(2m)` (`Σ k_j = 0`) a minimal geodesic has exactly `m` of the `k_j` equal to `+1` and
`m` equal to `−1` (p. 127: `Eigen(iπ)` is `m`-dimensional; Lemma 23.1). -/
theorem card_eq_of_minimal {m : ℕ} {k : ι → ℤ} (h : ∀ i, k i = 1 ∨ k i = -1)
    (hcard : Fintype.card ι = 2 * m) (hsum : ∑ i, k i = 0) :
    #{i | k i = 1} = m ∧ #{i | k i = -1} = m := by
  have hcompl : univ.filter (fun i => ¬ k i = 1) = univ.filter (fun i => k i = -1) := by
    ext i; simp only [mem_filter, mem_univ, true_and]
    rcases h i with hi | hi <;> simp [hi]
  have h1 := card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun i => k i = 1)
  rw [hcompl, card_univ, hcard] at h1
  have h2 := sum_filter_add_sum_filter_not (univ : Finset ι) (fun i => k i = 1) k
  rw [hcompl, hsum] at h2
  have e1 : ∑ i ∈ univ.filter (fun i => k i = 1), k i = #{i | k i = 1} := by
    rw [sum_congr rfl fun i hi => (mem_filter.1 hi).2]; simp
  have e2 : ∑ i ∈ univ.filter (fun i => k i = -1), k i = -(#{i | k i = -1} : ℤ) := by
    rw [sum_congr rfl fun i hi => (mem_filter.1 hi).2]; simp
  rw [e1, e2] at h2
  omega

/-- A minimal geodesic has index `0` (p. 132). -/
theorem bottIndex_eq_zero_of_minimal {k : ι → ℤ} (h : ∀ i, k i = 1 ∨ k i = -1) :
    bottIndex k = 0 := by
  refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => ?_
  split_ifs with hij
  · rcases h i with hi | hi <;> rcases h j with hj | hj <;> simp [hi, hj] at hij ⊢
  · rfl

/-! ### Lemma 23.2 -/

/-- The sum over the pairs (positive `k_i`, negative `k_j`) is a lower bound for the index. -/
theorem sum_pos_neg_le_bottIndex {k : ι → ℤ} (hk : ∀ i, Odd (k i)) :
    ∑ i ∈ univ.filter (fun i => 0 < k i), ∑ j ∈ univ.filter (fun j => k j < 0), (k i - k j - 2)
      ≤ bottIndex k := by
  unfold bottIndex
  calc ∑ i ∈ univ.filter (fun i => 0 < k i), ∑ j ∈ univ.filter (fun j => k j < 0), (k i - k j - 2)
      = ∑ i ∈ univ.filter (fun i => 0 < k i), ∑ j ∈ univ.filter (fun j => k j < 0),
          (if k j < k i then k i - k j - 2 else 0) := by
        refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
        simp only [mem_filter, mem_univ, true_and] at hi hj
        rw [if_pos (by omega)]
    _ ≤ ∑ i ∈ univ.filter (fun i => 0 < k i), ∑ j, (if k j < k i then k i - k j - 2 else 0) :=
        sum_le_sum fun i _ => sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun j _ _ => bottIndex_term_nonneg hk i j
    _ ≤ ∑ i, ∑ j, (if k j < k i then k i - k j - 2 else 0) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun i _ _ => sum_nonneg fun j _ => bottIndex_term_nonneg hk i j

theorem sum_pos_neg_eq (k : ι → ℤ) :
    ∑ i ∈ univ.filter (fun i => 0 < k i), ∑ j ∈ univ.filter (fun j => k j < 0), (k i - k j - 2)
      = (#{j | k j < 0} : ℤ) * ∑ i ∈ univ.filter (fun i => 0 < k i), k i
        + (#{i | 0 < k i} : ℤ) * (-∑ j ∈ univ.filter (fun j => k j < 0), k j)
        - 2 * #{i | 0 < k i} * #{j | k j < 0} := by
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_sum, mul_neg]
  ring

/-- The bookkeeping behind Milnor's two cases: `P`, `N` are the numbers of positive and
negative `k_j`, `S_p` and `S_n` the sums of the positive `k_j` and of the `|k_j|`, `k_j < 0`. -/
theorem exists_pos_neg_data {k : ι → ℤ} (hk : ∀ i, Odd (k i)) :
    ∃ P N Sp Sn : ℤ, 0 ≤ P ∧ 0 ≤ N ∧ P + N = Fintype.card ι ∧ Sp - Sn = ∑ i, k i ∧
      P ≤ Sp ∧ N ≤ Sn ∧ N * Sp + P * Sn - 2 * P * N ≤ bottIndex k ∧
      (∀ i, 3 ≤ k i → P + 2 ≤ Sp ∧ 1 ≤ P) ∧ (∀ i, k i ≤ -3 → N + 2 ≤ Sn ∧ 1 ≤ N) := by
  classical
  set Pos := univ.filter (fun i => 0 < k i) with hPos
  set Neg := univ.filter (fun j => k j < 0) with hNeg
  have hk0 : ∀ i, k i ≠ 0 := fun i h => by simpa [h] using hk i
  have hcompl : univ.filter (fun i => ¬ 0 < k i) = Neg := by
    ext i; simp only [mem_filter, mem_univ, true_and, not_lt, hNeg]
    exact ⟨fun h => lt_of_le_of_ne h (hk0 i), fun h => h.le⟩
  refine ⟨#Pos, #Neg, ∑ i ∈ Pos, k i, -∑ j ∈ Neg, k j, by positivity, by positivity, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · have := card_filter_add_card_filter_not (s := (univ : Finset ι)) (fun i => 0 < k i)
    rw [hcompl, card_univ] at this
    exact_mod_cast this
  · have := sum_filter_add_sum_filter_not (univ : Finset ι) (fun i => 0 < k i) k
    rw [hcompl] at this
    linarith
  · rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact sum_le_sum fun i hi => by simp only [hPos, mem_filter] at hi; omega
  · rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, ← sum_neg_distrib]
    exact sum_le_sum fun i hi => by simp only [hNeg, mem_filter] at hi; omega
  · have h1 := sum_pos_neg_le_bottIndex hk
    rw [sum_pos_neg_eq] at h1
    exact h1
  · intro i₀ h
    have hmem : i₀ ∈ Pos := by simp only [hPos, mem_filter, mem_univ, true_and]; omega
    have h1 : (#(Pos.erase i₀) : ℤ) ≤ ∑ i ∈ Pos.erase i₀, k i := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact sum_le_sum fun i hi => by simp only [hPos, mem_erase, mem_filter] at hi; omega
    have h2 : #(Pos.erase i₀) + 1 = #Pos := card_erase_add_one hmem
    have h3 : k i₀ + ∑ i ∈ Pos.erase i₀, k i = ∑ i ∈ Pos, k i := add_sum_erase _ _ hmem
    have h2' : (#(Pos.erase i₀) : ℤ) + 1 = #Pos := by rw [← h2]; push_cast; ring
    constructor <;> linarith
  · intro i₀ h
    have hmem : i₀ ∈ Neg := by simp only [hNeg, mem_filter, mem_univ, true_and]; omega
    have h1 : ∑ i ∈ Neg.erase i₀, k i ≤ -(#(Neg.erase i₀) : ℤ) := by
      rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, ← sum_neg_distrib]
      exact sum_le_sum fun i hi => by simp only [hNeg, mem_erase, mem_filter] at hi; omega
    have h2 : #(Neg.erase i₀) + 1 = #Neg := card_erase_add_one hmem
    have h3 : k i₀ + ∑ i ∈ Neg.erase i₀, k i = ∑ i ∈ Neg, k i := add_sum_erase _ _ hmem
    have h2' : (#(Neg.erase i₀) : ℤ) + 1 = #Neg := by rw [← h2]; push_cast; ring
    constructor <;> linarith

/-- **Lemma 23.2** (pp. 131–132).  Let `k_1, …, k_{2m}` be odd integers with `Σ k_j = 0`, not
all `±1` (a non-minimal geodesic from `I` to `-I` in `SU(2m)`).  Then
`Σ_{k_i > k_j} (k_i − k_j − 2) ≥ 2m + 2`. -/
theorem bottIndex_ge {m : ℕ} {k : ι → ℤ} (hk : ∀ i, Odd (k i)) (hcard : Fintype.card ι = 2 * m)
    (hsum : ∑ i, k i = 0) (hnm : ¬ ∀ i, k i = 1 ∨ k i = -1) :
    2 * (m : ℤ) + 2 ≤ bottIndex k := by
  obtain ⟨P, N, Sp, Sn, hP0, hN0, hPN, hc, hSpP, hSnN, hbound, hpos3, hneg3⟩ :=
    exists_pos_neg_data hk
  rw [hsum] at hc
  rw [hcard] at hPN
  push_cast at hPN
  obtain ⟨i₀, hi₀⟩ : ∃ i, 3 ≤ k i ∨ k i ≤ -3 := by
    push Not at hnm
    obtain ⟨i, h1, h2⟩ := hnm
    obtain ⟨x, hx⟩ := hk i
    exact ⟨i, by omega⟩
  have hm : 1 ≤ (m : ℤ) := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i₀⟩
    omega
  have hbig : P + 2 ≤ Sp ∨ N + 2 ≤ Sn := by
    rcases hi₀ with h | h
    · exact Or.inl (hpos3 i₀ h).1
    · exact Or.inr (hneg3 i₀ h).1
  rcases lt_trichotomy P N with hlt | heq | hgt
  · -- Case 1: at least `m + 1` of the `k_j` are negative; the bound is `2N ≥ 2(m+1)`.
    have hN1 : (m : ℤ) + 1 ≤ N := by omega
    nlinarith
  · -- Case 2: `m` of each sign; the bound is `4m`.
    have hS : (m : ℤ) + 2 ≤ Sp := by rcases hbig with h | h <;> omega
    nlinarith
  · -- Case 1 with the signs reversed.
    have hP1 : (m : ℤ) + 1 ≤ P := by omega
    nlinarith

/-! ### The unitary group (Milnor p. 127: `U(n)` is "rather inconvenient") -/

/-- `k = (3, 1, …, 1)`: a geodesic from `I` to `-I` in `U(n + 1)`. -/
def remarkK (n : ℕ) : Fin (n + 1) → ℤ := fun i => if i = 0 then 3 else 1

theorem odd_remarkK (n : ℕ) (i : Fin (n + 1)) : Odd (remarkK n i) := by
  unfold remarkK; split_ifs <;> decide

/-- `k = (3, 1, …, 1)` has index `0`. -/
theorem bottIndex_remarkK (n : ℕ) : bottIndex (remarkK n) = 0 := by
  refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => ?_
  unfold remarkK
  split_ifs <;> omega

theorem not_minimal_remarkK (n : ℕ) : ¬ ∀ i, remarkK n i = 1 ∨ remarkK n i = -1 := fun h => by
  have := h 0
  simp [remarkK] at this

/-- `Σ k_j = (n + 1) + 2` for `k = (3, 1, …, 1)`. -/
theorem sum_remarkK (n : ℕ) : ∑ i, remarkK n i = (n + 1 : ℕ) + 2 := by
  rw [Fin.sum_univ_succ]
  simp [remarkK, Fin.succ_ne_zero]
  ring

/-- Every minimal geodesic has `|Σ k_j| ≤ n`; so `(3, 1, …, 1)`, with `Σ k_j = n + 2`, lies in
a component of the path space containing no minimal geodesic. -/
theorem abs_sum_le_card_of_minimal {k : ι → ℤ} (h : ∀ i, k i = 1 ∨ k i = -1) :
    |∑ i, k i| ≤ Fintype.card ι := by
  rw [← Finset.card_univ, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
  rcases h i with hi | hi <;> simp [hi]

/-! ### §24, the case `k ≡ 2 (mod 4)` (pp. 147–148) -/

/-- For odd `a_1, …, a_r` with `Σ a_h = c` and some `|a_h| ≥ 3`:
`Σ_{a_h > a_j} (a_h − a_j − 2) ≥ (r − |c|)/2`. -/
theorem card_sub_abs_sum_le_two_mul_bottIndex {a : ι → ℤ} (ha : ∀ i, Odd (a i))
    (hnm : ∃ i, 3 ≤ a i ∨ a i ≤ -3) :
    (Fintype.card ι : ℤ) - |∑ i, a i| ≤ 2 * bottIndex a := by
  obtain ⟨P, N, Sp, Sn, hP0, hN0, hPN, hc, hSpP, hSnN, hbound, hpos3, hneg3⟩ :=
    exists_pos_neg_data ha
  obtain ⟨i₀, hi₀⟩ := hnm
  rw [← hPN, ← hc]
  rcases hi₀ with h | h
  · obtain ⟨h1, h2⟩ := hpos3 i₀ h
    have : Sn + N ≤ bottIndex a := by
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hSnN), mul_nonneg hN0 (sub_nonneg.2 h1)]
    have := le_abs_self (Sp - Sn)
    linarith
  · obtain ⟨h1, h2⟩ := hneg3 i₀ h
    have : Sp + P ≤ bottIndex a := by
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hSpP), mul_nonneg hP0 (sub_nonneg.2 h1)]
    have := neg_abs_le (Sp - Sn)
    linarith

/-- **§24, `k ≡ 2 (mod 4)`** (p. 148): the pairs `a_h > a_j` give independent eigenvectors of
`K_A` with eigenvalues `π²(a_h − a_j)²/4` (one each), whose conjugate points alone give
`4λ ≥ r − |c|`, where `r` is the number of minimal summands and `c = Σ a_h`. -/
theorem card_sub_abs_sum_le_four_mul_spectralIndex {a : ι → ℤ} (ha : ∀ i, Odd (a i))
    (hnm : ∃ i, 3 ≤ a i ∨ a i ≤ -3) :
    (Fintype.card ι : ℤ) - |∑ i, a i| ≤ 4 * spectralIndex (pairSpectrum a) := by
  have h1 := card_sub_abs_sum_le_two_mul_bottIndex ha hnm
  have h2 := two_mul_spectralIndex_pairSpectrum ha
  linarith

end IndexFormula

/-! ### The orthogonal group: Lemma 24.2 (pp. 134–135) and §24, `k ≢ 2 (mod 4)` -/

section Orthogonal

variable {m : ℕ}

/-- **Milnor's index formula for `O(2m)`** (p. 135):
`λ = Σ_{i<j} (a_i + a_j − 2) + Σ_{a_i > a_j} (a_i − a_j − 2)`. -/
def bottIndexO (a : Fin m → ℤ) : ℤ :=
  (∑ i, ∑ j, if i < j then a i + a j - 2 else 0) + bottIndex a

/-- The spectrum of `K_V`, `V = πA`, for `A` with blocks `a_j (0 1; −1 0)` (p. 135): the numbers
`π²(a_i + a_j)²/4`, `i < j`, and `π²(a_i − a_j)²/4`, `a_i > a_j`, each counted twice. -/
def oSpectrum (a : Fin m → ℤ) :
    ({p : Fin m × Fin m // p.1 < p.2} ⊕ {p : Fin m × Fin m // a p.2 < a p.1}) × Fin 2 → ℝ
  | (Sum.inl p, _) => π ^ 2 / 4 * ((a p.1.1 : ℝ) + a p.1.2) ^ 2
  | (Sum.inr p, _) => π ^ 2 / 4 * ((a p.1.1 : ℝ) - a p.1.2) ^ 2

/-- The `O(2m)` index formula from the spectrum (p. 135). -/
theorem spectralIndex_oSpectrum {a : Fin m → ℤ} (hodd : ∀ i, Odd (a i))
    (hpos : ∀ i, 0 < a i) : (spectralIndex (oSpectrum a) : ℤ) = bottIndexO a := by
  rw [spectralIndex_eq, Fintype.sum_prod_type, Fintype.sum_sum_type, Nat.cast_add, Nat.cast_sum,
    Nat.cast_sum, bottIndexO, bottIndex_eq_sum_subtype]
  congr 1
  · rw [← Fintype.sum_prod_type' (fun i j => if i < j then a i + a j - 2 else 0), ← sum_filter,
      sum_subtype (p := fun p : Fin m × Fin m => p.1 < p.2) _ (fun p => by simp)
        (fun p : Fin m × Fin m => a p.1 + a p.2 - 2)]
    refine sum_congr rfl fun p _ => ?_
    have hneg : Odd (-a p.1.2) := (hodd _).neg
    have hlt : -a p.1.2 < a p.1.1 := by linarith [hpos p.1.1, hpos p.1.2]
    rw [Nat.cast_sum, Fin.sum_univ_two]
    have := two_mul_ncard_conjParams (hodd p.1.1) hneg hlt
    simp only [oSpectrum, Int.cast_neg, sub_neg_eq_add] at this ⊢
    linarith
  · refine sum_congr rfl fun p _ => ?_
    rw [Nat.cast_sum, Fin.sum_univ_two, ← two_mul_ncard_conjParams (hodd p.1.1) (hodd p.1.2) p.2]
    simp only [oSpectrum]
    ring

/-- A minimal geodesic in `O(2m)` (all `a_j = 1`) has index `0` (p. 135). -/
theorem bottIndexO_eq_zero {a : Fin m → ℤ} (h : ∀ i, a i = 1) : bottIndexO a = 0 := by
  simp [bottIndexO, bottIndex, h]

/-- **Lemma 24.2** (p. 135): every non-minimal geodesic from `I` to `-I` in `O(2m)` has index
`≥ 2m − 2`. -/
theorem bottIndexO_ge {a : Fin m → ℤ} (hodd : ∀ i, Odd (a i)) (hpos : ∀ i, 0 < a i)
    (hnm : ¬ ∀ i, a i = 1) : 2 * (m : ℤ) - 2 ≤ bottIndexO a := by
  push Not at hnm
  obtain ⟨i₀, hi₀⟩ := hnm
  have h3 : 3 ≤ a i₀ := by obtain ⟨x, hx⟩ := hodd i₀; have := hpos i₀; omega
  set g : Fin m → Fin m → ℤ := fun i j => if i < j then a i + a j - 2 else 0 with hg
  have hg0 : ∀ i j, 0 ≤ g i j := fun i j => by
    simp only [hg]; split_ifs <;> linarith [hpos i, hpos j]
  set r : Fin m → ℤ := fun i => ∑ j, g i j with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => sum_nonneg fun j _ => hg0 i j
  have hrow : ∀ i, (if i < i₀ then a i + a i₀ - 2 else 0) ≤ r i := fun i => by
    split_ifs with h
    · have := single_le_sum (fun j _ => hg0 i j) (mem_univ i₀)
      simpa [hg, h] using this
    · exact hr0 i
  have hF : (∑ i, ∑ j, if i < j then a i + a j - 2 else 0) = r i₀ + ∑ i ∈ univ.erase i₀, r i :=
    (add_sum_erase _ _ (mem_univ i₀)).symm
  have hcol : ∑ i, (if i < i₀ then a i + a i₀ - 2 else 0) ≤ ∑ i ∈ univ.erase i₀, r i := by
    rw [← add_sum_erase _ _ (mem_univ i₀), if_neg (lt_irrefl _), zero_add]
    exact sum_le_sum fun i _ => hrow i
  have hrow0 : r i₀ + ∑ i, (if i < i₀ then a i + a i₀ - 2 else 0)
      = ∑ j, ((if i₀ < j then a i₀ + a j - 2 else 0) + (if j < i₀ then a j + a i₀ - 2 else 0)) := by
    rw [sum_add_distrib]
  have hlow : ∑ j, (if j ≠ i₀ then (2 : ℤ) else 0) ≤
      ∑ j, ((if i₀ < j then a i₀ + a j - 2 else 0) + (if j < i₀ then a j + a i₀ - 2 else 0)) := by
    refine sum_le_sum fun j _ => ?_
    have := hpos j
    rcases lt_trichotomy j i₀ with h | h | h
    · rw [if_pos h.ne, if_neg (not_lt.2 h.le), if_pos h]; omega
    · subst h; simp
    · rw [if_pos h.ne', if_pos h, if_neg (not_lt.2 h.le)]; omega
  have hcount : ∑ j, (if j ≠ i₀ then (2 : ℤ) else 0) = 2 * ((m : ℤ) - 1) := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, filter_ne' univ i₀,
      card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have : 1 ≤ m := by have := i₀.pos; omega
    push_cast [this]; ring
  have hB := bottIndex_nonneg hodd
  unfold bottIndexO
  linarith

/-- **§24, `k ≢ 2 (mod 4)`** (pp. 145–146): if `a_{h₀} ≥ 3` and all `a_j ≥ 1`, the `s − 1`
eigenvalues `π²(a_{h₀} + a_j)²/4`, `j ≠ h₀`, of `K_{πA}` exceed `π²`, so they alone force index
`≥ s − 1`. -/
theorem card_sub_one_le_spectralIndex {s : ℕ} (a : Fin s → ℤ) (hpos : ∀ j, 1 ≤ a j) (h₀ : Fin s)
    (h3 : 3 ≤ a h₀) :
    s - 1 ≤ spectralIndex (fun j : {j // j ≠ h₀} => π ^ 2 / 4 * ((a h₀ : ℝ) + a j) ^ 2) := by
  refine le_trans (le_of_eq ?_) (card_lt_le_spectralIndex _)
  rw [filter_true_of_mem, card_univ, Fintype.card_subtype_compl, Fintype.card_fin,
    Fintype.card_unique]
  intro j _
  have h1 : (4 : ℝ) ≤ ((a h₀ : ℝ) + a j) := by
    have := hpos j
    have : (4 : ℤ) ≤ a h₀ + a j := by omega
    exact_mod_cast this
  have h2 : (16 : ℝ) ≤ ((a h₀ : ℝ) + a j) ^ 2 := by nlinarith
  have h3 : 0 < π ^ 2 := by positivity
  nlinarith

end Orthogonal

end Morse
