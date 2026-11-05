import Morse.Chapter12.SUIndex
import Morse.Chapter7.HopfRinow

/-!
Milnor, *Morse Theory*, §23, Lemma 23.1 (pp. 126–128): the minimal geodesics from `I` to `−I`
in `SU(2m)`.

# The minimal geodesics from `I` to `−I` in `SU(2m)` form the Grassmannian `G_m(ℂ^{2m})`

## Milnor's text, paraphrased

* p. 127: a geodesic `t ↦ exp(tA)` from `I` to `−I` has length `|A| = π(Σ k_j²)^{1/2}`; it is
  minimal iff all `k_j = ±1`.  Such an `A` is completely determined by `Eigen(iπ)`, an arbitrary
  subspace of `ℂⁿ`; in `SU(2m)` (`tr A = 0`) an arbitrary `m`-dimensional one.
* **Lemma 23.1** (p. 128): the space of minimal geodesics from `I` to `−I` in `SU(2m)` is
  homeomorphic to the complex Grassmann manifold `G_m(ℂ^{2m})`.

## What is formalized

* `Morse.pathLength_exp_smul`: the length of `t ↦ exp(tA)`, `0 ≤ t ≤ 1`, is `‖A‖`;
  `Morse.norm_conj_suDiag_sq`: `‖T suDiag(k) Tᴴ‖² = π² Σ k_j²`.
* **`Morse.riemDist_one_neg_one`**: in `SU(2m)` (`m ≥ 1`), the Riemannian distance (Milnor's `ρ`)
  from `I` to `−I` is `π√(2m)`: `≤` by the geodesic with `k = (1, …, 1, −1, …, −1)`, `≥` because a
  minimal geodesic exists (the project's Hopf–Rinow theorem `Morse.theorem_10_9`, at the point
  `I`, where `exp` is defined everywhere) and is some `t ↦ exp(tA)` with `exp A = −I`.
* **`Morse.isMinimalGeodesic_exp_iff`**: a geodesic `t ↦ exp(tA)` from `I` to `−I` in `SU(2m)` is
  a minimal geodesic (`Morse.IsMinimalGeodesic`: no piecewise smooth path in `SU(2m)` from `I` to
  `−I` is shorter) iff all `k_j = ±1` iff `A² = −π²I`.
* **Lemma 23.1** (`Morse.lemma_23_1`): the set `Morse.minVel ι` of the `A ∈ 𝔰𝔲(2m)` with
  `A² = −π²I` — by `Morse.mem_minVel_iff`, exactly the initial velocities of the minimal geodesics
  from `I` to `−I` — is homeomorphic to `Morse.grassmannian ι m`, the Hermitian projections of
  trace `m` (each the orthogonal projection onto an `m`-dimensional subspace of `ℂ^{2m}`), by
  `A ↦ ½(I − (i/π)A)`, with inverse `P ↦ iπ(2P − I)` (Milnor's `Eigen(iπ)` ↔ its projection).

Not formalized: the identification of the projections of trace `m` with the `m`-dimensional
subspaces as a topological space (Mathlib has no Grassmannian), and of the set of initial
velocities with the space of minimal geodesics as a subspace of the path space `Ω` (the map
`A ↦ (t ↦ exp(tA))`; this is `Morse.minPathsHomotopyEquiv` and `Morse.minVelHomeomorph` in
`Morse/Chapter14/MinimalPaths.lean`).

## Gaps in Milnor's text

* p. 127, "it is minimal iff all `k_j = ±1`": the length of every geodesic from `I` to `−I` is
  `≥ π√n`, but that the geodesics of length `π√n` are *minimal* needs that the distance is
  attained by some geodesic (Hopf–Rinow) *and* that every geodesic from `I` is `t ↦ exp(tA)`
  (Lemma 21.2 and its converse, `Morse.IsMatrixGroup.eqOn_mul_exp_smul`).  In `SU(2m)` there is a
  geodesic with all `k_j = ±1` (`m` of each sign), so the minimum is `π√(2m)`.
* p. 127, "`A` is completely determined by `Eigen(iπ)`": this is `A = iπ(2P − I)` with `P` the
  orthogonal projection onto `Eigen(iπ)`, which uses the normality of `A`
  (`Morse.sq_eq_neg_pi_sq_iff` of `Morse/Chapter14/SUMatrices.lean`).
-/

open Matrix Set Filter Topology Module Finset
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Lengths -/

/-- `‖suDiag k‖² = π² Σ k_j²` (Milnor p. 127). -/
theorem norm_suDiag_sq (k : ι → ℤ) :
    ‖suDiag k‖ ^ 2 = Real.pi ^ 2 * ∑ j, (k j : ℝ) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_def, trace_mul_comm, trace_suDiag_mul_conjTranspose]
  rfl

/-- Conjugation by a unitary matrix preserves the norm. -/
theorem norm_conj_unitary {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) (M : Matrix ι ι ℂ) :
    ‖T * M * Tᴴ‖ = ‖M‖ := by
  have hT' : Tᴴᴴ * Tᴴ = 1 := by
    rw [conjTranspose_conjTranspose]; exact mul_conjTranspose_eq_one hT
  have h1 : ‖T * M * Tᴴ‖ = ‖T * M‖ := (mulRightIso Tᴴ hT').norm_map (T * M)
  have h2 : ‖T * M‖ = ‖M‖ := (mulLeftIso T hT).norm_map M
  rw [h1, h2]

/-- **The length of `t ↦ T exp(t suDiag(k)) Tᴴ`** is `π(Σ k_j²)^{1/2}` (Milnor p. 127). -/
theorem norm_conj_suDiag_sq {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) (k : ι → ℤ) :
    ‖T * suDiag k * Tᴴ‖ ^ 2 = Real.pi ^ 2 * ∑ j, (k j : ℝ) ^ 2 := by
  rw [norm_conj_unitary hT, norm_suDiag_sq]

/-- The length of the geodesic `t ↦ exp(tA)`, `0 ≤ t ≤ 1`, is `‖A‖`, for skew-Hermitian `A`. -/
theorem pathLength_exp_smul {A : Matrix ι ι ℂ} (hA : Aᴴ = -A) :
    pathLength (fun t : ℝ => NormedSpace.exp (t • A)) 0 1 = ‖A‖ := by
  have h := pathLength_eq_of_norm_deriv (k := ‖A‖)
    (IsPiecewiseSmooth.of_contDiff (contDiff_exp_smul A) zero_le_one).isAdmissible
    (fun t _ _ => by
      rw [(hasDerivAt_exp_smul_const A t).deriv]
      have hu : (NormedSpace.exp (t • A))ᴴ * NormedSpace.exp (t • A) = 1 :=
        exp_conjTranspose_mul_exp_of_skew (by rw [conjTranspose_smul, star_trivial, hA, smul_neg])
      rw [← mulLeftIso_apply _ hu, LinearIsometryEquiv.norm_map])
  rw [h, sub_zero, mul_one]

/-! ### A geodesic of length `π√(2m)` -/

/-- `k₀ = (1, …, 1, −1, …, −1)` (`m` of each sign), for `card ι = 2m`. -/
def kHalf {m : ℕ} (hcard : Fintype.card ι = 2 * m) : ι → ℤ := fun i =>
  if ((Fintype.equivFinOfCardEq (hcard.trans (two_mul m))) i : ℕ) < m then 1 else -1

omit [DecidableEq ι] in
theorem kHalf_pm {m : ℕ} (hcard : Fintype.card ι = 2 * m) (i : ι) :
    kHalf hcard i = 1 ∨ kHalf hcard i = -1 := by
  unfold kHalf; split_ifs <;> simp

omit [DecidableEq ι] in
theorem sum_kHalf {m : ℕ} (hcard : Fintype.card ι = 2 * m) : ∑ i, kHalf hcard i = 0 := by
  set e := Fintype.equivFinOfCardEq (hcard.trans (two_mul m))
  have h1 : ∑ i, kHalf hcard i = ∑ j : Fin (m + m), (if (j : ℕ) < m then (1 : ℤ) else -1) :=
    (Equiv.sum_comp e (fun j : Fin (m + m) => if (j : ℕ) < m then (1 : ℤ) else -1))
  rw [h1, Fin.sum_univ_add]
  have h2 : ∀ a : Fin m, ((Fin.castAdd m a : Fin (m + m)) : ℕ) < m := fun a => a.2
  have h3 : ∀ b : Fin m, ¬ ((Fin.natAdd m b : Fin (m + m)) : ℕ) < m := fun b => by
    simp [Fin.natAdd]
  simp only [h2, h3, if_true, if_false, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, mul_neg]
  ring

omit [DecidableEq ι] in
theorem odd_kHalf {m : ℕ} (hcard : Fintype.card ι = 2 * m) (i : ι) : Odd (kHalf hcard i) := by
  rcases kHalf_pm hcard i with h | h <;> rw [h] <;> decide

/-! ### The distance from `I` to `−I` -/

variable [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- `π √(Σ k_j²) ≥ π √n` for odd `k_j`. -/
theorem pi_sqrt_card_le {k : ι → ℤ} (hk : ∀ i, Odd (k i)) :
    Real.pi * Real.sqrt (Fintype.card ι) ≤ Real.pi * Real.sqrt (∑ j, (k j : ℝ) ^ 2) := by
  have h := card_le_sum_sq hk
  have h' : (Fintype.card ι : ℝ) ≤ ∑ j, (k j : ℝ) ^ 2 := by exact_mod_cast h
  gcongr

omit [Nonempty ι] in
theorem norm_eq_pi_sqrt {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) (k : ι → ℤ) :
    ‖T * suDiag k * Tᴴ‖ = Real.pi * Real.sqrt (∑ j, (k j : ℝ) ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_conj_suDiag_sq hT, Real.sqrt_mul (by positivity),
    Real.sqrt_sq Real.pi_pos.le]

omit [Nonempty ι] in
/-- Every geodesic `t ↦ exp(tA)` from `I` to `−I` in `SU(n)` has length `≥ π√n`. -/
theorem pi_sqrt_card_le_norm {A : Matrix ι ι ℂ} (hA : A ∈ specialSkewHermitian ι)
    (hexp : NormedSpace.exp A = -1) : Real.pi * Real.sqrt (Fintype.card ι) ≤ ‖A‖ := by
  obtain ⟨T, k, hT, hk, -, rfl⟩ := exists_unitary_suDiag hA hexp
  rw [norm_eq_pi_sqrt hT]
  exact pi_sqrt_card_le hk

/-- **The distance from `I` to `−I` in `SU(2m)` is `π√(2m)`** (Milnor p. 127). -/
theorem riemDist_one_neg_one {m : ℕ} (hcard : Fintype.card ι = 2 * m) :
    riemDist (N := (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) 1 (-1) =
      ENNReal.ofReal (Real.pi * Real.sqrt (2 * m)) := by
  set hSU := isSliceSubmanifold_specialUnitaryGroup (ι := ι)
  have hG := isMatrixGroup_specialUnitaryGroup (ι := ι)
  have hcard' : (Fintype.card ι : ℝ) = 2 * m := by exact_mod_cast hcard
  -- `≤`: the geodesic with `k = (1, …, 1, −1, …, −1)`
  have hA₀ : suDiag (kHalf hcard) ∈ specialSkewHermitian ι := by
    simpa using conj_suDiag_mem (sum_kHalf hcard) (T := 1) (by simp)
  have hexp₀ : NormedSpace.exp (suDiag (kHalf hcard)) = -1 := by
    simpa using exp_conj_suDiag (odd_kHalf hcard) (T := 1) (by simp)
  have hle : riemDist (N := (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) 1 (-1) ≤
      ENNReal.ofReal (Real.pi * Real.sqrt (2 * m)) := by
    have h1 := riemDist_le_pathLength (N := (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)))
      (mem_pathSpace_exp hA₀ hexp₀).1 (mem_pathSpace_exp hA₀ hexp₀).2.1
    simp only [zero_smul, NormedSpace.exp_zero, one_smul, hexp₀] at h1
    rw [pathLength_exp_smul hA₀.1] at h1
    have h2 : ‖suDiag (kHalf hcard)‖ = Real.pi * Real.sqrt (2 * m) := by
      have := norm_eq_pi_sqrt (T := 1) (by simp) (kHalf hcard)
      simp only [Matrix.one_mul, conjTranspose_one, Matrix.mul_one] at this
      rw [this]
      congr 2
      rw [← hcard']
      have := sum_sq_eq_card_iff (odd_kHalf hcard)
      have h3 := this.2 (kHalf_pm hcard)
      exact_mod_cast h3
    rwa [h2] at h1
  refine le_antisymm hle ?_
  -- `≥`: a minimal geodesic from `I` (Hopf–Rinow at `I`) is some `exp(tA)` with `exp A = −I`
  have hne : riemDist (N := (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) 1 (-1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  obtain ⟨v, hv, hexpv, hρ, -⟩ := theorem_10_9 (hN := hSU) (p := ⟨1, hG.one_mem⟩)
    (hG.isGeodesicallyComplete ⟨1, hG.one_mem⟩) (q := ⟨-1, (mem_pathSpace_exp hA₀ hexp₀).2.2.2 ▸
      (mem_pathSpace_exp hA₀ hexp₀).2.1 1 ⟨zero_le_one, le_rfl⟩⟩) hne
  rw [hG.mem_tangentSubspace_iff] at hv
  simp only [conjTranspose_one, Matrix.one_mul] at hv
  have hv' : Morse.exp hSU 1 v = NormedSpace.exp v := by
    simpa using hG.exp_eq hG.one_mem hv
  rw [hv'] at hexpv
  have hρ' : riemDist (N := (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) 1 (-1) =
      ENNReal.ofReal ‖v‖ := hρ
  rw [hρ']
  apply ENNReal.ofReal_le_ofReal
  have := pi_sqrt_card_le_norm hv hexpv
  rwa [hcard'] at this

/-! ### The minimal geodesics -/

omit [Nonempty ι] in
/-- `A = T suDiag(k) Tᴴ` satisfies `A² = −π²I` iff all `k_j = ±1`. -/
theorem sq_conj_suDiag_iff {T : Matrix ι ι ℂ} (hT : Tᴴ * T = 1) (k : ι → ℤ) :
    (T * suDiag k * Tᴴ) * (T * suDiag k * Tᴴ) = -((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) ↔
      ∀ i, k i = 1 ∨ k i = -1 := by
  have hT' := mul_conjTranspose_eq_one hT
  have r : ∀ X : Matrix ι ι ℂ, Tᴴ * (T * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hT, Matrix.one_mul]
  have hsq : (T * suDiag k * Tᴴ) * (T * suDiag k * Tᴴ) = T * (suDiag k * suDiag k) * Tᴴ := by
    simp only [Matrix.mul_assoc, r]
  have hD : suDiag k * suDiag k = diagonal fun j => -((Real.pi : ℂ) ^ 2 * (k j : ℂ) ^ 2) := by
    rw [suDiag, diagonal_mul_diagonal]
    congr 1
    funext j
    linear_combination ((Real.pi : ℂ) ^ 2 * (k j : ℂ) ^ 2) * Complex.I_sq
  rw [hsq, hD]
  constructor
  · intro h i
    have h1 : Tᴴ * (T * (diagonal fun j => -((Real.pi : ℂ) ^ 2 * (k j : ℂ) ^ 2)) * Tᴴ) * T =
        Tᴴ * (-((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ)) * T := by rw [h]
    simp only [Matrix.mul_assoc, r, hT, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul] at h1
    have h2 := congrFun (congrFun h1 i) i
    simp only [diagonal_apply_eq, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h2
    have hpi : (Real.pi : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
    have h3 : (k i : ℂ) ^ 2 = 1 := by
      have := neg_inj.1 h2
      field_simp at this
      exact this
    have h4 : (k i) ^ 2 = 1 := by exact_mod_cast h3
    exact (sq_eq_one_iff' (a := k i)).1 h4
  · intro h
    have hD1 : (diagonal fun j => -((Real.pi : ℂ) ^ 2 * (k j : ℂ) ^ 2)) =
        -((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) := by
      rw [← diagonal_one, ← diagonal_smul]
      congr 1
      funext j
      rcases h j with hj | hj <;> simp [hj]
    rw [hD1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hT']

/-- **Milnor p. 127, "minimal iff all `k_j = ±1`"**: a geodesic `t ↦ exp(tA)` from `I` to `−I` in
`SU(2m)` is a minimal geodesic iff `A² = −π²I`. -/
theorem isMinimalGeodesic_exp_iff {m : ℕ} (hcard : Fintype.card ι = 2 * m)
    {A : Matrix ι ι ℂ} (hA : A ∈ specialSkewHermitian ι) (hexp : NormedSpace.exp A = -1) :
    IsMinimalGeodesic isSliceSubmanifold_specialUnitaryGroup
        (fun t : ℝ => NormedSpace.exp (t • A)) 0 1 ↔
      A * A = -((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) := by
  have hG := isMatrixGroup_specialUnitaryGroup (ι := ι)
  have hcard' : (Fintype.card ι : ℝ) = 2 * m := by exact_mod_cast hcard
  have hρ := riemDist_one_neg_one hcard
  have hpath := mem_pathSpace_exp hA hexp
  have hlen := pathLength_exp_smul hA.1
  obtain ⟨T, k, hT, hk, hsum, hAeq⟩ := exists_unitary_suDiag hA hexp
  have hnorm : ‖A‖ = Real.pi * Real.sqrt (∑ j, (k j : ℝ) ^ 2) := by
    rw [hAeq]; exact norm_eq_pi_sqrt hT k
  rw [hAeq, sq_conj_suDiag_iff hT, ← sum_sq_eq_card_iff hk, ← hAeq]
  constructor
  · rintro ⟨-, -, hmin⟩
    -- compare with any path realizing the distance up to `ε`: use `ρ = π√(2m)` as a lower bound
    have hle : ‖A‖ ≤ Real.pi * Real.sqrt (2 * m) := by
      -- the geodesic with `k = (1, …, 1, −1, …, −1)` has length `π√(2m)`
      have hA₀ : suDiag (kHalf hcard) ∈ specialSkewHermitian ι := by
        simpa using conj_suDiag_mem (sum_kHalf hcard) (T := 1) (by simp)
      have hexp₀ : NormedSpace.exp (suDiag (kHalf hcard)) = -1 := by
        simpa using exp_conj_suDiag (odd_kHalf hcard) (T := 1) (by simp)
      have hp₀ := mem_pathSpace_exp hA₀ hexp₀
      have h1 := hmin _ 0 1 hp₀.1 hp₀.2.1 (by simp) (by simp [hexp, hexp₀])
      rw [hlen, pathLength_exp_smul hA₀.1] at h1
      have h2 : ‖suDiag (kHalf hcard)‖ = Real.pi * Real.sqrt (2 * m) := by
        have := norm_eq_pi_sqrt (T := 1) (by simp) (kHalf hcard)
        simp only [Matrix.one_mul, conjTranspose_one, Matrix.mul_one] at this
        rw [this, ← hcard']
        congr 2
        exact_mod_cast (sum_sq_eq_card_iff (odd_kHalf hcard)).2 (kHalf_pm hcard)
      rwa [h2] at h1
    have hge := pi_sqrt_card_le hk
    rw [← hnorm, hcard'] at hge
    have heq : Real.sqrt (∑ j, (k j : ℝ) ^ 2) = Real.sqrt (Fintype.card ι) := by
      have h3 : Real.pi * Real.sqrt (∑ j, (k j : ℝ) ^ 2) = Real.pi * Real.sqrt (2 * m) := by
        rw [← hnorm]; linarith
      rw [hcard']
      exact mul_left_cancel₀ Real.pi_ne_zero h3
    have h4 := congrArg (· ^ 2) heq
    simp only [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (k j : ℝ)),
      Real.sq_sqrt (Nat.cast_nonneg _)] at h4
    exact_mod_cast h4
  · intro hmin
    refine ⟨zero_le_one, ⟨univ, subset_univ _, hG.isGeodesicOn_exp_smul hA⟩,
      fun c a b hc hcN ha hb => ?_⟩
    have h1 := riemDist_le_pathLength (N := (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))) hc
      hcN
    simp only [ha, hb, zero_smul, NormedSpace.exp_zero, one_smul, hexp] at h1
    rw [hρ] at h1
    have h2 := (ENNReal.ofReal_le_ofReal_iff hc.isAdmissible.pathLength_nonneg).1 h1
    rw [hlen, hnorm]
    have h5 : (∑ j, (k j : ℝ) ^ 2) = 2 * m := by
      rw [← hcard']; exact_mod_cast hmin
    rw [h5]
    exact h2

/-! ### Lemma 23.1 -/

/-- **The initial velocities of the minimal geodesics from `I` to `−I`**: the `A ∈ 𝔰𝔲(n)` with
`A² = −π²I` (Milnor p. 127). -/
def minVel (ι : Type*) [Fintype ι] [DecidableEq ι] : Set (Matrix ι ι ℂ) :=
  {A | A ∈ specialSkewHermitian ι ∧ A * A = -((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ)}

/-- **The Grassmannian `G_m(ℂⁿ)`**, as the Hermitian projections of trace `m` (the orthogonal
projections onto the `m`-dimensional subspaces). -/
def grassmannian (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) : Set (Matrix ι ι ℂ) :=
  {P | Pᴴ = P ∧ P * P = P ∧ trace P = m}

omit [Nonempty ι] in
/-- `A² = −π²I` gives `exp A = −I` (all eigenvalues are `±iπ`). -/
theorem exp_eq_neg_one_of_sq {A : Matrix ι ι ℂ} (hA : Aᴴ = -A)
    (hsq : A * A = -((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ)) : NormedSpace.exp A = -1 := by
  have hH : (Complex.I • A).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, hA, Complex.star_def, Complex.conj_I, neg_smul,
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
  have r : ∀ X : Matrix ι ι ℂ, Uᴴ * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  -- `D² = −π²I`, so `ev j = ±π`
  have hD2 : D * D = -((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) := by
    have h1 : Uᴴ * (A * A) * U = Uᴴ * (-((Real.pi : ℂ) ^ 2) • (1 : Matrix ι ι ℂ)) * U := by
      rw [hsq]
    rw [hAD] at h1
    simpa only [Matrix.mul_assoc, r, hU, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.one_mul] using h1
  have hev : ∀ j, ∃ k : ℤ, Odd k ∧ -ev j = Real.pi * k := by
    intro j
    have h1 := congrFun (congrFun hD2 j) j
    simp only [hDdef, diagonal_mul_diagonal, diagonal_apply_eq, Matrix.smul_apply, one_apply_eq,
      smul_eq_mul, mul_one] at h1
    push_cast at h1
    have h2 : ((ev j : ℂ)) ^ 2 = (Real.pi : ℂ) ^ 2 := by
      linear_combination (-1 : ℂ) * h1 + (ev j : ℂ) ^ 2 * Complex.I_sq
    have h3 : ev j ^ 2 = Real.pi ^ 2 := by exact_mod_cast h2
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h | h
    · exact ⟨-1, by decide, by rw [h]; push_cast; ring⟩
    · exact ⟨1, by decide, by rw [h]; push_cast; ring⟩
  have hexpD : NormedSpace.exp D = -1 := by
    rw [hDdef]
    exact (exp_diagonal_eq_neg_one_iff _).2 hev
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hU
  rw [hAD, ← hinv, Matrix.exp_conj U _ ⟨⟨U, Uᴴ, hU', hU⟩, rfl⟩, hexpD, hinv, Matrix.mul_neg,
    Matrix.mul_one, Matrix.neg_mul, hU']

/-- **`minVel` is the set of initial velocities of the minimal geodesics from `I` to `−I`** in
`SU(2m)`: `A ∈ minVel` iff `t ↦ exp(tA)` is a geodesic from `I` to `−I` (`A ∈ 𝔰𝔲`,
`exp A = −I`) which is minimal. -/
theorem mem_minVel_iff {m : ℕ} (hcard : Fintype.card ι = 2 * m) {A : Matrix ι ι ℂ} :
    A ∈ minVel ι ↔ A ∈ specialSkewHermitian ι ∧ NormedSpace.exp A = -1 ∧
      IsMinimalGeodesic isSliceSubmanifold_specialUnitaryGroup
        (fun t : ℝ => NormedSpace.exp (t • A)) 0 1 := by
  constructor
  · rintro ⟨hA, hsq⟩
    have hexp := exp_eq_neg_one_of_sq hA.1 hsq
    exact ⟨hA, hexp, (isMinimalGeodesic_exp_iff hcard hA hexp).2 hsq⟩
  · rintro ⟨hA, hexp, hmin⟩
    exact ⟨hA, (isMinimalGeodesic_exp_iff hcard hA hexp).1 hmin⟩

omit [Nonempty ι] in
theorem projOf_mem {m : ℕ} (hcard : Fintype.card ι = 2 * m) {A : Matrix ι ι ℂ}
    (hA : A ∈ minVel ι) : (1 / 2 : ℂ) • (1 - (Complex.I / Real.pi) • A) ∈ grassmannian ι m := by
  obtain ⟨⟨hskew, htr⟩, hsq⟩ := hA
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hskew]
    simp only [star_div₀, star_one, RCLike.star_def, Complex.conj_I, Complex.conj_ofReal,
      smul_neg, neg_div, neg_smul, neg_neg, map_ofNat]
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
      mul_smul_comm, smul_smul, hsq]
    match_scalars <;> field_simp
    all_goals ((try simp only [Complex.I_sq]); ring1)
  · rw [trace_smul, trace_sub, trace_one, trace_smul, htr, smul_zero, sub_zero, smul_eq_mul,
      hcard]
    push_cast
    ring

omit [Nonempty ι] in
theorem velOf_mem {m : ℕ} (hcard : Fintype.card ι = 2 * m) {P : Matrix ι ι ℂ}
    (hP : P ∈ grassmannian ι m) :
    ((Real.pi : ℂ) * Complex.I) • ((2 : ℂ) • P - 1) ∈ minVel ι := by
  obtain ⟨hH, hPP, htr⟩ := hP
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hH]
    simp only [star_mul', RCLike.star_def, Complex.conj_I, Complex.conj_ofReal, map_ofNat,
      mul_neg, neg_smul]
  · rw [trace_smul, trace_sub, trace_smul, trace_one, htr, hcard]
    push_cast
    ring
  · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
      mul_smul_comm, smul_smul, hPP]
    match_scalars
    · ring
    · linear_combination (Real.pi : ℂ) ^ 2 * Complex.I_sq

omit [Nonempty ι] in
/-- **Lemma 23.1** (Milnor p. 128): in `SU(2m)`, the set of initial velocities of the minimal
geodesics from `I` to `−I` is homeomorphic to the Grassmannian of `m`-planes in `ℂ^{2m}` (as
Hermitian projections of trace `m`), by `A ↦ ½(I − (i/π)A)` (the projection onto
`Eigen(iπ)`), with inverse `P ↦ iπ(2P − I)`. -/
def lemma_23_1 {m : ℕ} (hcard : Fintype.card ι = 2 * m) : minVel ι ≃ₜ grassmannian ι m where
  toFun A := ⟨_, projOf_mem hcard A.2⟩
  invFun P := ⟨_, velOf_mem hcard P.2⟩
  left_inv A := by
    apply Subtype.ext
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    change ((Real.pi : ℂ) * Complex.I) • ((2 : ℂ) • ((1 / 2 : ℂ) •
      (1 - (Complex.I / Real.pi) • (A : Matrix ι ι ℂ))) - 1) = A
    rw [smul_smul]
    match_scalars <;> field_simp
    all_goals ((try simp only [Complex.I_sq]); ring1)
  right_inv P := by
    apply Subtype.ext
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    change (1 / 2 : ℂ) • (1 - (Complex.I / Real.pi) •
      (((Real.pi : ℂ) * Complex.I) • ((2 : ℂ) • (P : Matrix ι ι ℂ) - 1))) = P
    match_scalars <;> field_simp
    all_goals ((try simp only [Complex.I_sq]); ring1)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop

end Morse
