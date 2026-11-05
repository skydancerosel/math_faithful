import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Morse.Chapter15.Relations

/-!
Milnor, *Morse Theory*, §24 (The periodicity theorem for the orthogonal group), pp. 133–142.

# Complex structures and the spaces `Ω_k(n)`

## Milnor's text, paraphrased

* **Definition** (p. 133).  For `n` even, a *complex structure* on `ℝⁿ` is a linear map
  `J ∈ O(n)` with `J² = −I`; `Ω_1(n)` is the space of them.
* **Lemma 24.1** (pp. 133–135).  The minimal geodesics from `I` to `−I` in `O(n)` are the
  `t ↦ exp(πtJ)`, `J ∈ Ω_1(n)`.  In the proof, a complex structure is skew (`J* = −J`), and a
  skew `A` with `A² = −I` is a complex structure.
* **Definition** (p. 136).  Fix complex structures `J_1, …, J_{k−1}` which anticommute.  `Ω_k(n)`
  is the set of complex structures anticommuting with `J_1, …, J_{k−1}`, and `Ω_0(n) = O(n)`;
  so `Ω_k(n) ⊂ Ω_{k−1}(n) ⊂ ⋯ ⊂ Ω_1(n) ⊂ O(n)`, and "clearly each `Ω_k(n)` is a compact set".
* **Lemma 24.4** (pp. 136–138).  Each `Ω_k(n)` is a smooth totally geodesic submanifold of
  `O(n)`, and the minimal geodesics from `J_ℓ` to `−J_ℓ` in `Ω_ℓ(n)` form a space homeomorphic
  to `Ω_{ℓ+1}(n)`.  Each component of `Ω_k(n)` is a symmetric space: the reflection of `O(n)` in
  a point of `Ω_k(n)` carries `Ω_k(n)` to itself.  *Proof*: points of `O(n)` near `J` are
  `J exp A`, `A` small and skew.  *Assertion 1*: `J exp A` is a complex structure iff `A`
  anticommutes with `J`.  *Assertion 2*: `J exp A` anticommutes with `J_1, …, J_{k−1}` iff `A`
  commutes with them.  For `J = J_kA ∈ Ω_{k+1}(n)`, `A` is a complex structure anticommuting with
  `J_k` and commuting with `J_1, …, J_{k−1}`, so `t ↦ J_k exp(πtA)` is a geodesic from `J_k` to
  `−J_k` in `Ω_k(n)`; conversely.
* **Remark** (p. 138).  The point `J_kA ∈ Ω_{k+1}(n)` is the midpoint `γ(1/2)` of the geodesic.
* **Lemma 24.6** (pp. 139–142).  `Ω_3(16r)` is the set of quaternionic subspaces of `ℍ^{4r}`
  (via `J_1J_2J_3`); `Ω_4(16r) ≅ Sp(2r)` (via `J_3J_4`); `Ω_5`, `Ω_6`, `Ω_7` are sets of
  subspaces (via `J_1J_4J_5`, `J_2J_4J_6`, `J_1J_6J_7`); `Ω_8(16r) ≅ O(r)` (via `J_7J_8`).

## What is formalized

Matrices are real `n × n` matrices indexed by a finite type `n`; `J : ℕ → Matrix n n ℝ` is the
sequence of fixed structures (`J 0` unused).

* `Morse.IsComplexStructure`, `Morse.isComplexStructure_iff` (orthogonal with `J² = −1` iff skew
  with `J² = −1`), `Morse.IsComplexStructure.even_card` (`n` must be even, as Milnor assumes),
  `Morse.IsComplexStructure.trace_transpose_mul_self` (`|J|² = n`).
* `Morse.Omega J k` is Milnor's `Ω_k(n)`; `Morse.omega_succ_subset` (the chain),
  `Morse.isCompact_omega` (compactness), `Morse.IsAnticommFamily` (Milnor's standing
  assumption on `J_1, …, J_k`) and `Morse.IsAnticommFamily.mem_omega` (`J_k ∈ Ω_k(n)`).
* `Morse.exp_smul_of_mul_self_eq_neg_one`: `exp(θJ) = cos θ · I + sin θ · J` (pp. 134–135), so
  `t ↦ exp(πtJ)` runs from `I` to `−I` (`Morse.exp_pi_smul`).
* **Lemma 24.4 (iii)**, algebraic part: `Morse.omega_succ_decomp` and `Morse.mul_mem_omega_succ`
  (`J' ∈ Ω_{k+1}` iff `J' = J_kA` with `A` a complex structure anticommuting with `J_k` and
  commuting with `J_1, …, J_{k−1}`); `Morse.semicircle_mem_omega` and
  `Morse.mul_exp_eq_semicircle`: the geodesic `J_k exp(tA) = cos t · J_k + sin t · J'` stays in
  `Ω_k(n)` for all `t`, passes through `J'` at `t = π/2` (the Remark) and ends at `−J_k`.
* **Assertions 1 and 2**, the "if" halves: `Morse.isComplexStructure_mul_exp`,
  `Morse.anticomm_mul_exp`.
* **Lemma 24.4 (ii)**: `Morse.reflection_mem_omega` (`J' ↦ J J'⁻¹ J = −JJ'J` preserves `Ω_k`).
* Remark p. 138: `Morse.trace_transpose_mul_eq_zero` (anticommuting complex structures are
  orthogonal, so the geodesics of (iii) are great semicircles on the sphere `|J|² = n`).
* **Lemma 24.6, odd steps** (3), (5), (6), (7): `Morse.theta_of_mem_omega` and
  `Morse.mem_omega_of_theta`: `J ↦ θ = J_aJ_bJ` is a bijection from `Ω_{k+1}(n)` onto the
  symmetric orthogonal involutions commuting with `J_a`, `J_b` and anticommuting with the other
  `J_c`, `c ≤ k`, with inverse `θ ↦ J_bJ_aθ` (`Morse.mul_theta_mul`); an involution is the same as
  its `+1`-eigenspace, which is how Milnor phrases (3), (5), (6), (7) in terms of subspaces.
  The even steps (4), (8) (`J ↦ J_kJ`) are Lemma 24.4 (iii) with `A = −J_kJ`.

Not in this file, but proved later: the "only if" halves of Assertions 1 and 2, which need `exp`
injective near `0` (`Morse.mem_tanAlg_of_mul_exp_mem`), the manifold structure and total geodesy
(`Morse.isSliceSubmanifold_omegaStratum`, `Morse.isTotGeo_omegaStratum`, all three in
`Morse/Chapter15/OmegaManifold.lean`), and `Ω_8(16r) ≅ O(r)` (`Morse.omegaEightHomeomorph`,
`Morse/Chapter15/OmegaEight.lean`).  Not formalized: the identification of the components of
`Ω_k(16r)`, `k ≤ 7`, with Grassmannians and classical groups (beyond the bijections above).

## Gaps in Milnor's text

* p. 133: `n` even is needed for `Ω_1(n) ≠ ∅` (`Morse.IsComplexStructure.even_card`).
* p. 136: the definition of `Ω_k(n)` makes sense for any fixed `J_1, …, J_{k−1}`, but Lemma 24.4
  needs them anticommuting complex structures *and* `Ω_{ℓ+1}(n) ≠ ∅`.
* p. 137: Assertions 1 and 2 are "iff" only for small `A`; the "if" halves (used for total
  geodesy) hold for all skew `A`.
* p. 137: "Now choose a specific point `J_k ∈ Ω_k(n)`": Milnor's later use takes `J_k` to be the
  next member of the fixed anticommuting family, which is what `Morse.IsAnticommFamily` records.
* pp. 139–141: "it is not hard to see that `J_5` is uniquely determined", "it can be shown that
  `J_7` is uniquely determined": these are the inverse maps `θ ↦ J_bJ_aθ`.
-/

open Matrix

noncomputable section

namespace Morse

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Milnor p. 133**: a complex structure on `ℝⁿ` is an orthogonal `J` with `J² = −I`. -/
def IsComplexStructure (J : Matrix n n ℝ) : Prop := J ∈ orthogonalGroup n ℝ ∧ J * J = -1

/-- Proof of Lemma 24.1 (p. 135): orthogonal with `J² = −I` iff skew with `J² = −I`. -/
theorem isComplexStructure_iff {J : Matrix n n ℝ} :
    IsComplexStructure J ↔ Jᵀ = -J ∧ J * J = -1 := by
  constructor
  · rintro ⟨hO, hJ⟩
    refine ⟨?_, hJ⟩
    rw [mem_orthogonalGroup_iff'] at hO
    have : Jᵀ = -(Jᵀ * J * J) := by rw [Matrix.mul_assoc, hJ]; simp
    rw [this, hO, Matrix.one_mul]
  · rintro ⟨hT, hJ⟩
    refine ⟨?_, hJ⟩
    rw [mem_orthogonalGroup_iff', hT, Matrix.neg_mul, hJ, neg_neg]

theorem IsComplexStructure.transpose_mul_self {J : Matrix n n ℝ} (h : IsComplexStructure J) :
    Jᵀ * J = 1 := by simpa [mem_orthogonalGroup_iff'] using h.1

theorem IsComplexStructure.transpose {J : Matrix n n ℝ} (h : IsComplexStructure J) :
    Jᵀ = -J := (isComplexStructure_iff.1 h).1

theorem IsComplexStructure.mul_self {J : Matrix n n ℝ} (h : IsComplexStructure J) :
    J * J = -1 := h.2

theorem IsComplexStructure.neg {J : Matrix n n ℝ} (h : IsComplexStructure J) :
    IsComplexStructure (-J) := by
  rw [isComplexStructure_iff] at h ⊢
  exact ⟨by rw [transpose_neg, h.1], by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, h.2]⟩

/-- A complex structure exists on `ℝⁿ` only for `n` even (Milnor's "Now suppose that `n` is
even", p. 133): `det(J)² = det(−I) = (−1)ⁿ`. -/
theorem IsComplexStructure.even_card {J : Matrix n n ℝ} (h : IsComplexStructure J) :
    Even (Fintype.card n) := by
  have := congrArg det h.2
  rw [det_mul, det_neg, det_one, mul_one] at this
  rcases Nat.even_or_odd (Fintype.card n) with he | ho
  · exact he
  · rw [ho.neg_one_pow] at this
    nlinarith [mul_self_nonneg (det J)]

/-- `|J|² = tr(JᵀJ) = n`: every complex structure lies on the same sphere (p. 138). -/
theorem IsComplexStructure.trace_transpose_mul_self {J : Matrix n n ℝ}
    (h : IsComplexStructure J) : trace (Jᵀ * J) = Fintype.card n := by
  rw [h.transpose_mul_self, trace_one]

/-- **Milnor's `Ω_k(n)`** (p. 136): `Ω_0(n) = O(n)`, and for `k ≥ 1` the complex structures
anticommuting with the fixed `J 1, …, J (k−1)`. -/
def Omega (J : ℕ → Matrix n n ℝ) : ℕ → Set (Matrix n n ℝ)
  | 0 => orthogonalGroup n ℝ
  | k + 1 => {J' | IsComplexStructure J' ∧ ∀ α, 1 ≤ α → α ≤ k → J α * J' = -(J' * J α)}

/-- `Ω_{k+1}(n) ⊆ Ω_k(n)` (p. 136). -/
theorem omega_succ_subset (J : ℕ → Matrix n n ℝ) (k : ℕ) : Omega J (k + 1) ⊆ Omega J k := by
  cases k with
  | zero => exact fun J' h => h.1.1
  | succ k => exact fun J' h => ⟨h.1, fun α h1 h2 => h.2 α h1 (h2.trans (Nat.le_succ k))⟩

theorem isClosed_orthogonalGroup : IsClosed (orthogonalGroup n ℝ : Set (Matrix n n ℝ)) := by
  have : (orthogonalGroup n ℝ : Set (Matrix n n ℝ)) = (fun A : Matrix n n ℝ => Aᵀ * A) ⁻¹' {1} := by
    ext A; simp [mem_orthogonalGroup_iff']
  rw [this]
  exact isClosed_singleton.preimage (by fun_prop)

theorem abs_apply_le_one_of_mem_orthogonalGroup {A : Matrix n n ℝ} (h : A ∈ orthogonalGroup n ℝ)
    (i j : n) : |A i j| ≤ 1 := by
  rw [mem_orthogonalGroup_iff'] at h
  have hjj := congrFun (congrFun h j) j
  simp only [mul_apply, transpose_apply, one_apply_eq] at hjj
  have : A i j * A i j ≤ 1 := by
    rw [← hjj]
    exact Finset.single_le_sum (f := fun k => A k j * A k j) (fun k _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  rw [← sq] at this
  exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [sq_abs (A i j)])

theorem isCompact_orthogonalGroup : IsCompact (orthogonalGroup n ℝ : Set (Matrix n n ℝ)) := by
  refine (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
    (a := (-1 : ℝ)) (b := 1)).of_isClosed_subset isClosed_orthogonalGroup ?_
  intro A hA
  simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, Set.mem_Icc]
  intro i j
  exact abs_le.1 (abs_apply_le_one_of_mem_orthogonalGroup hA i j)

theorem isClosed_omega (J : ℕ → Matrix n n ℝ) (k : ℕ) : IsClosed (Omega J k) := by
  cases k with
  | zero => exact isClosed_orthogonalGroup
  | succ k =>
    have : Omega J (k + 1) = (orthogonalGroup n ℝ : Set (Matrix n n ℝ)) ∩
        {J' | J' * J' = -1} ∩ ⋂ α ∈ Finset.Icc 1 k, {J' | J α * J' = -(J' * J α)} := by
      ext J'
      simp only [Omega, IsComplexStructure, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
        Finset.mem_Icc, SetLike.mem_coe, and_imp]
    rw [this]
    refine (isClosed_orthogonalGroup.inter (isClosed_eq (by fun_prop) (by fun_prop))).inter
      (isClosed_biInter fun α _ => isClosed_eq (by fun_prop) (by fun_prop))

/-- p. 136: "Clearly each Ω_k(n) is a compact set." -/
theorem isCompact_omega (J : ℕ → Matrix n n ℝ) (k : ℕ) : IsCompact (Omega J k) := by
  refine isCompact_orthogonalGroup.of_isClosed_subset (isClosed_omega J k) ?_
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (omega_succ_subset J k).trans ih

/-- Milnor's standing assumption (p. 136): `J 1, …, J k` are anticommuting complex
structures. -/
structure IsAnticommFamily (J : ℕ → Matrix n n ℝ) (k : ℕ) : Prop where
  cs : ∀ α, 1 ≤ α → α ≤ k → IsComplexStructure (J α)
  anti : ∀ α β, 1 ≤ α → α ≤ k → 1 ≤ β → β ≤ k → α ≠ β → J α * J β = -(J β * J α)

/-- The base point `J_k` lies in `Ω_k(n)`. -/
theorem IsAnticommFamily.mem_omega {J : ℕ → Matrix n n ℝ} {k : ℕ} (h : IsAnticommFamily J k)
    (hk : 1 ≤ k) : J k ∈ Omega J k := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact ⟨h.cs _ hk le_rfl, fun α h1 h2 => h.anti α (k + 1) h1 (by omega) hk le_rfl (by omega)⟩

theorem IsComplexStructure.mul_mem_orthogonalGroup {J J' : Matrix n n ℝ}
    (h : IsComplexStructure J) (h' : IsComplexStructure J') : J * J' ∈ orthogonalGroup n ℝ :=
  Submonoid.mul_mem _ h.1 h'.1

theorem complexLift_continuous {J : Matrix n n ℝ} (hJ : J * J = -1) :
    Continuous (Complex.lift ⟨J, hJ⟩ : ℂ →ₐ[ℝ] Matrix n n ℝ) :=
  (Complex.lift ⟨J, hJ⟩ : ℂ →ₐ[ℝ] Matrix n n ℝ).toLinearMap.continuous_of_finiteDimensional

set_option backward.isDefEq.respectTransparency false in
/-- **pp. 134–135**: for `J² = −I`, `exp(θJ) = cos θ · I + sin θ · J`. -/
theorem exp_smul_of_mul_self_eq_neg_one {J : Matrix n n ℝ} (hJ : J * J = -1) (θ : ℝ) :
    NormedSpace.exp (θ • J) = Real.cos θ • (1 : Matrix n n ℝ) + Real.sin θ • J := by
  have h1 : (Complex.lift ⟨J, hJ⟩ : ℂ →ₐ[ℝ] Matrix n n ℝ) (θ * Complex.I) = θ • J := by
    rw [show (θ : ℂ) * Complex.I = θ • Complex.I by simp [Complex.real_smul], map_smul]
    simp
  have h2 : (Complex.lift ⟨J, hJ⟩ : ℂ →ₐ[ℝ] Matrix n n ℝ) (NormedSpace.exp (θ * Complex.I)) =
      NormedSpace.exp (θ • J) := by
    rw [← h1]
    open scoped Norms.Operator in
    exact NormedSpace.map_exp _ (complexLift_continuous hJ) _
  rw [← h2, ← Complex.exp_eq_exp_ℂ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.lift_apply, Algebra.smul_def, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

/-- The geodesic `t ↦ exp(πtJ)` ends at `−I` (Lemma 24.1). -/
theorem exp_pi_smul {J : Matrix n n ℝ} (hJ : J * J = -1) :
    NormedSpace.exp (Real.pi • J) = -1 := by
  rw [exp_smul_of_mul_self_eq_neg_one hJ, Real.cos_pi, Real.sin_pi]
  simp

/-- **Lemma 24.4 (iii)**, algebraic part: for `J' ∈ Ω_{k+1}(n)`, `A = J_k⁻¹J' = −J_kJ'` is a
complex structure which anticommutes with `J_k` and commutes with `J_1, …, J_{k−1}`, and
`J' = J_kA`. -/
theorem omega_succ_decomp {J : ℕ → Matrix n n ℝ} {k : ℕ} (hJ : IsAnticommFamily J k)
    (hk : 1 ≤ k) {J' : Matrix n n ℝ} (hJ' : J' ∈ Omega J (k + 1)) :
    IsComplexStructure (-(J k * J')) ∧ -(J k * J') * J k = -(J k * -(J k * J')) ∧
      (∀ α, 1 ≤ α → α < k → -(J k * J') * J α = J α * -(J k * J')) ∧ J k * -(J k * J') = J' := by
  obtain ⟨hcs', hanti'⟩ := hJ'
  have hJk := hJ.cs k hk le_rfl
  have h1 : J k * J k = -1 := hJk.2
  have h2 : J' * J' = -1 := hcs'.2
  have h3 : J' * J k = -(J k * J') := by rw [hanti' k hk le_rfl, neg_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [isComplexStructure_iff]
    refine ⟨?_, ?_⟩
    · rw [transpose_neg, transpose_mul, hJk.transpose, hcs'.transpose, neg_mul_neg, h3]
    · word_simp [h1, h2, h3]
  · word_simp [h1, h3]
  · intro α hα hαk
    have h4 : J' * J α = -(J α * J') := by rw [hanti' α hα hαk.le, neg_neg]
    have h5 : J k * J α = -(J α * J k) := hJ.anti k α hk le_rfl hα hαk.le hαk.ne'
    word_simp [h4, h5]
  · word_simp [h1]

/-- **Lemma 24.4 (iii)**, converse: if `A` is a complex structure anticommuting with `J_k` and
commuting with `J_1, …, J_{k−1}`, then `J_kA ∈ Ω_{k+1}(n)`. -/
theorem mul_mem_omega_succ {J : ℕ → Matrix n n ℝ} {k : ℕ} (hJ : IsAnticommFamily J k)
    (hk : 1 ≤ k) {A : Matrix n n ℝ} (hA : IsComplexStructure A) (hAk : A * J k = -(J k * A))
    (hAα : ∀ α, 1 ≤ α → α < k → A * J α = J α * A) : J k * A ∈ Omega J (k + 1) := by
  have hJk := hJ.cs k hk le_rfl
  have h1 : J k * J k = -1 := hJk.2
  have h2 : A * A = -1 := hA.2
  refine ⟨?_, ?_⟩
  · rw [isComplexStructure_iff]
    refine ⟨?_, ?_⟩
    · rw [transpose_mul, hJk.transpose, hA.transpose, neg_mul_neg, hAk]
    · word_simp [h1, h2, hAk]
  · intro α hα hαk
    rcases lt_or_eq_of_le hαk with hlt | rfl
    · have h5 : J α * J k = -(J k * J α) := hJ.anti α k hα hαk hk le_rfl hlt.ne
      have h6 := hAα α hα hlt
      word_simp [h5, h6]
    · word_simp [h1, hAk]


/-- **Lemma 24.4 (iii)**: the semicircle `cos t · J_k + sin t · J'`, `J' ∈ Ω_{k+1}(n)`, lies in
`Ω_k(n)` for every `t` (and is the geodesic `J_k exp(tA)`, `Morse.mul_exp_eq_semicircle`). -/
theorem semicircle_mem_omega {J : ℕ → Matrix n n ℝ} {k : ℕ} (hJ : IsAnticommFamily J k)
    (hk : 1 ≤ k) {J' : Matrix n n ℝ} (hJ' : J' ∈ Omega J (k + 1)) (t : ℝ) :
    Real.cos t • J k + Real.sin t • J' ∈ Omega J k := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hcs', hanti'⟩ := hJ'
  have hJk := hJ.cs (k + 1) hk le_rfl
  have h1 : J (k + 1) * J (k + 1) = -1 := hJk.2
  have h2 : J' * J' = -1 := hcs'.2
  have h3 : J' * J (k + 1) = -(J (k + 1) * J') := by rw [hanti' (k + 1) hk le_rfl, neg_neg]
  refine ⟨?_, ?_⟩
  · rw [isComplexStructure_iff]
    refine ⟨?_, ?_⟩
    · rw [transpose_add, transpose_smul, transpose_smul, hJk.transpose, hcs'.transpose, smul_neg,
        smul_neg, neg_add]
    · simp only [add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, smul_neg]
      rw [show (-1 : Matrix n n ℝ) = -((Real.cos t ^ 2 + Real.sin t ^ 2) • (1 : Matrix n n ℝ)) by
        rw [Real.cos_sq_add_sin_sq, one_smul]]
      module
  · intro α hα hαk
    have h4 : J α * J' = -(J' * J α) := hanti' α hα (by omega)
    have h5 : J α * J (k + 1) = -(J (k + 1) * J α) := hJ.anti α (k + 1) hα (by omega) hk le_rfl
      (by omega)
    rw [mul_add, add_mul, mul_smul_comm, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, h4, h5,
      smul_neg, smul_neg, neg_add]


/-- The semicircle is the `O(n)`-geodesic `t ↦ J_k exp(tA)`, `A = −J_kJ'`: it starts at `J_k`,
passes through `J'` at `t = π/2` (the Remark, p. 138) and ends at `−J_k` at `t = π`. -/
theorem mul_exp_eq_semicircle {Jk J' : Matrix n n ℝ} (hJk : Jk * Jk = -1)
    (hA : -(Jk * J') * -(Jk * J') = -1) (t : ℝ) :
    Jk * NormedSpace.exp (t • -(Jk * J')) = Real.cos t • Jk + Real.sin t • J' := by
  rw [exp_smul_of_mul_self_eq_neg_one hA, mul_add, mul_smul_comm, mul_smul_comm, mul_one,
    mul_neg, ← Matrix.mul_assoc, hJk, Matrix.neg_mul, Matrix.one_mul, neg_neg]

set_option backward.isDefEq.respectTransparency false in
theorem mul_exp_eq_exp_neg_mul {J A : Matrix n n ℝ} (hAJ : A * J = -(J * A)) :
    J * NormedSpace.exp A = NormedSpace.exp (-A) * J := by
  have h : SemiconjBy J A (-A) := by
    change J * A = -A * J
    rw [neg_mul, hAJ, neg_neg]
  open scoped Norms.Operator in exact h.exp_right

theorem exp_neg_mul_exp (A : Matrix n n ℝ) :
    NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl A)), neg_add_cancel,
    NormedSpace.exp_zero]

/-- **Assertion 1** of the proof of 24.4 (p. 137), "if" half: if `A` is skew and anticommutes with
`J`, then `J exp A` is a complex structure. -/
theorem isComplexStructure_mul_exp {J A : Matrix n n ℝ} (hJ : IsComplexStructure J)
    (hA : Aᵀ = -A) (hAJ : A * J = -(J * A)) : IsComplexStructure (J * NormedSpace.exp A) := by
  have e1 := mul_exp_eq_exp_neg_mul hAJ
  have hAJ' : -A * J = -(J * -A) := by rw [neg_mul, hAJ, mul_neg]
  have e2 := mul_exp_eq_exp_neg_mul hAJ'
  rw [neg_neg] at e2
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff', transpose_mul, ← Matrix.exp_transpose, hA, Matrix.mul_assoc,
      ← Matrix.mul_assoc Jᵀ, hJ.transpose_mul_self, Matrix.one_mul, exp_neg_mul_exp]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (NormedSpace.exp A), ← e2, Matrix.mul_assoc,
      ← Matrix.mul_assoc J J, hJ.2, Matrix.neg_mul, Matrix.one_mul, exp_neg_mul_exp]


set_option backward.isDefEq.respectTransparency false in
/-- **Assertion 2** of the proof of 24.4 (p. 137), "if" half: if `A` commutes with `J_α` and
`J_α` anticommutes with `J`, then `J_α` anticommutes with `J exp A`. -/
theorem anticomm_mul_exp {J A Jα : Matrix n n ℝ} (hJα : Jα * J = -(J * Jα))
    (hA : Commute A Jα) : Jα * (J * NormedSpace.exp A) = -((J * NormedSpace.exp A) * Jα) := by
  have h : Commute (NormedSpace.exp A) Jα := by
    open scoped Norms.Operator in exact hA.exp_left
  rw [← Matrix.mul_assoc, hJα, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, h.eq]

/-- **Lemma 24.4 (ii)** (p. 136): the reflection `I_P(J') = P J'⁻¹ P = −PJ'P` of `O(n)` in a
point `P ∈ Ω_k(n)` carries `Ω_k(n)` to itself (here `k ≥ 1`). -/
theorem reflection_mem_omega {J : ℕ → Matrix n n ℝ} {k : ℕ} {P J' : Matrix n n ℝ}
    (hP : P ∈ Omega J (k + 1)) (hJ' : J' ∈ Omega J (k + 1)) : -(P * J' * P) ∈ Omega J (k + 1) := by
  obtain ⟨hPc, hPa⟩ := hP
  obtain ⟨hc, ha⟩ := hJ'
  have h1 : P * P = -1 := hPc.2
  have h2 : J' * J' = -1 := hc.2
  refine ⟨?_, ?_⟩
  · rw [isComplexStructure_iff]
    refine ⟨?_, ?_⟩
    · rw [transpose_neg, transpose_mul, transpose_mul, hPc.transpose, hc.transpose]
      word_simp []
    · word_simp [h1, h2]
  · intro α hα hαk
    have h3 := hPa α hα hαk
    have h4 := ha α hα hαk
    word_simp [h3, h4]

/-- Remark p. 138: anticommuting complex structures are orthogonal, `⟨J', J⟩ = tr(J'ᵀJ) = 0`; so the
minimal geodesics of 24.4 (iii) are great semicircles from the pole `J_k` through the equator. -/
theorem trace_transpose_mul_eq_zero {J J' : Matrix n n ℝ} (h' : IsComplexStructure J')
    (hanti : J' * J = -(J * J')) : trace (J'ᵀ * J) = 0 := by
  have h : trace (J' * J) = -trace (J' * J) := by
    conv_lhs => rw [hanti]
    rw [trace_neg, trace_mul_comm]
  rw [h'.transpose, Matrix.neg_mul, trace_neg]
  linarith


/-- **Lemma 24.6, odd steps** (pp. 139–141), forward: for `J' ∈ Ω_{k+1}(n)` and `a < b ≤ k`,
`θ = J_aJ_bJ'` is a symmetric orthogonal involution commuting with `J_a`, `J_b` and anticommuting
with every other `J_c`, `c ≤ k`. -/
theorem theta_of_mem_omega {J : ℕ → Matrix n n ℝ} {k a b : ℕ} (hJ : IsAnticommFamily J k)
    (ha : 1 ≤ a) (hab : a < b) (hbk : b ≤ k) {J' : Matrix n n ℝ} (hJ' : J' ∈ Omega J (k + 1)) :
    (J a * J b * J')ᵀ = J a * J b * J' ∧ (J a * J b * J') * (J a * J b * J') = 1 ∧
      (J a * J b * J') * J a = J a * (J a * J b * J') ∧
      (J a * J b * J') * J b = J b * (J a * J b * J') ∧
      ∀ c, 1 ≤ c → c ≤ k → c ≠ a → c ≠ b → (J a * J b * J') * J c = -(J c * (J a * J b * J')) := by
  obtain ⟨hc', ha'⟩ := hJ'
  have hJa := hJ.cs a ha (hab.le.trans hbk)
  have hJb := hJ.cs b (ha.trans hab.le) hbk
  have h1 : J a * J a = -1 := hJa.2
  have h2 : J b * J b = -1 := hJb.2
  have h3 : J' * J' = -1 := hc'.2
  have h4 : J b * J a = -(J a * J b) :=
    hJ.anti b a (ha.trans hab.le) hbk ha (hab.le.trans hbk) hab.ne'
  have h5 : J' * J a = -(J a * J') := by rw [ha' a ha (hab.le.trans hbk), neg_neg]
  have h6 : J' * J b = -(J b * J') := by rw [ha' b (ha.trans hab.le) hbk, neg_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [transpose_mul, transpose_mul, hJa.transpose, hJb.transpose, hc'.transpose]
    word_simp [h4, h5, h6]
  · word_simp [h1, h2, h3, h4, h5, h6]
  · word_simp [h1, h4, h5]
  · word_simp [h2, h4, h5, h6]
  · intro c hc hck hca hcb
    have h7 : J a * J c = -(J c * J a) := hJ.anti a c ha (hab.le.trans hbk) hc hck (Ne.symm hca)
    have h8 : J b * J c = -(J c * J b) := hJ.anti b c (ha.trans hab.le) hbk hc hck (Ne.symm hcb)
    have h9 : J' * J c = -(J c * J') := by rw [ha' c hc hck, neg_neg]
    word_simp [h7, h8, h9]

/-- **Lemma 24.6, odd steps**, backward: conversely such a `θ` comes from
`J' = J_bJ_aθ ∈ Ω_{k+1}(n)`. -/
theorem mem_omega_of_theta {J : ℕ → Matrix n n ℝ} {k a b : ℕ} (hJ : IsAnticommFamily J k)
    (ha : 1 ≤ a) (hab : a < b) (hbk : b ≤ k) {θ : Matrix n n ℝ} (hθT : θᵀ = θ) (hθ : θ * θ = 1)
    (hθa : θ * J a = J a * θ) (hθb : θ * J b = J b * θ)
    (hθc : ∀ c, 1 ≤ c → c ≤ k → c ≠ a → c ≠ b → θ * J c = -(J c * θ)) :
    J b * J a * θ ∈ Omega J (k + 1) ∧ J a * J b * (J b * J a * θ) = θ := by
  have hJa := hJ.cs a ha (hab.le.trans hbk)
  have hJb := hJ.cs b (ha.trans hab.le) hbk
  have h1 : J a * J a = -1 := hJa.2
  have h2 : J b * J b = -1 := hJb.2
  have h4 : J b * J a = -(J a * J b) :=
    hJ.anti b a (ha.trans hab.le) hbk ha (hab.le.trans hbk) hab.ne'
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isComplexStructure_iff]
    refine ⟨?_, ?_⟩
    · rw [transpose_mul, transpose_mul, hJa.transpose, hJb.transpose, hθT]
      word_simp [h1, h2, h4, hθa, hθb]
    · word_simp [h1, h2, h4, hθ, hθa, hθb]
  · intro c hc hck
    by_cases hca : c = a
    · subst hca; word_simp [h1, h4, hθa]
    by_cases hcb : c = b
    · subst hcb; word_simp [h2, h4, hθa, hθb]
    have h7 : J a * J c = -(J c * J a) := hJ.anti a c ha (hab.le.trans hbk) hc hck (Ne.symm hca)
    have h8 : J b * J c = -(J c * J b) := hJ.anti b c (ha.trans hab.le) hbk hc hck (Ne.symm hcb)
    have h9 := hθc c hc hck hca hcb
    word_simp [h7, h8, h9]
  · word_simp [h1, h2, h4]

/-- The two maps of the odd steps are inverse to each other. -/
theorem mul_theta_mul {J : ℕ → Matrix n n ℝ} {k a b : ℕ} (hJ : IsAnticommFamily J k)
    (ha : 1 ≤ a) (hab : a < b) (hbk : b ≤ k) (J' : Matrix n n ℝ) :
    J b * J a * (J a * J b * J') = J' := by
  have h1 : J a * J a = -1 := (hJ.cs a ha (hab.le.trans hbk)).2
  have h2 : J b * J b = -1 := (hJ.cs b (ha.trans hab.le) hbk).2
  word_simp [h1, h2]

end Morse
