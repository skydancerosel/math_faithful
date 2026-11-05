import Morse.Chapter15.OmegaManifold
import Morse.Chapter13.Theorem22
import Morse.Chapter10.FullPathSpace

/-!
Milnor, *Morse Theory*, §24, Lemma 24.1 (pp. 134–135) and Lemma 24.4 (iii) (pp. 137–138);
Exposition/Chapter15.md, §§1–2.

# The minimal geodesics from `J_k` to `−J_k` in `Ω_k(n)` form `Ω_{k+1}(n)`

## Milnor's text, paraphrased

(Lemma 24.1) The geodesics from `I` to `−I` in `O(n)` are the `t ↦ exp(πtA)`, `exp(πA) = −I`;
in the normal form `A = diag(a_jJ_0)` the `a_j` are odd and the length is `π(2Σa_j²)^{1/2} ≥ π√n`,
with equality iff `A² = −I`.  (Lemma 24.4 (iii)) The minimal geodesics from `J_k` to `−J_k` in
`Ω_k(n)` are the semicircles `t ↦ cos(πt) J_k + sin(πt) J'`, `J' ∈ Ω_{k+1}(n)`, and
`J' ↦ γ_{J'}` is a homeomorphism; `J'` is the midpoint (Remark p. 138).

## What is formalized

* `Morse.pi_sq_mul_card_le_norm_sq`, `Morse.mul_self_eq_of_norm_sq_le`: **for `V` skew with
  `exp V = −I`, `‖V‖² ≥ π²n`, with equality only if `V² = −π²I`**.  No normal form: each
  eigenvalue `λ` of `−V² = VᵀV` is `≥ π²` (`Morse.pi_sq_le_of_sq_mul`: on the span of an
  eigenvector `exp(tV) = cos(√λ t) + sin(√λ t)V/√λ`, by the uniqueness of solutions of `c' = Vc`,
  and `cos √λ = −1`), and `‖V‖² = tr VᵀV = Σλ`.
* For `p ∈ Ω_k(n)` and `Morse.minVelO J k p = {A ∈ 𝒯_p : A² = −I}` (assumed non-empty):
  `Morse.riemDist_omegaStratum` (**the distance from `p` to `−p` is `π√n`**: Hopf–Rinow in the
  stratum, every geodesic being `t ↦ p exp(tV)`), `Morse.omegaPath_mem_minPaths` (the semicircles
  `t ↦ p exp(πtA)` have least energy `π²n`), `Morse.exists_minVelO_of_mem_minPaths` (**every path
  of least energy is one of them on `[0, 1]`**), `Morse.omegaGeo_half` (the midpoint is `pA`).
* `Morse.continuous_omegaPath` (continuity for Milnor's metric), `Morse.omegaMinPathsHomotopyEquiv`
  (**`minVelO ≃ Ω^d` up to homotopy**, inverse `γ ↦ pᴴγ(1/2)`), `Morse.omegaMinPathsHomeomorph`
  (onto the separation quotient).
* **Lemma 24.4 (iii)**: `Morse.mem_minVelO_iff` and `Morse.minVelOHomeomorph`:
  `minVelO J k J_k ≅ Ω_{k+1}(n)`, `A ↦ J_kA` (`J_0 = I`, `Morse.basePt`), and
  `Morse.omegaGeo_eq_semicircle` (the geodesic is `cos(πt)J_k + sin(πt)J'`).

## What Milnor leaves implicit

* "Minimal in `O(n)`, hence certainly minimal in `Ω_k(n)`" (p. 138): what is used is that the
  distance in `Ω_k(n)` is attained (Hopf–Rinow in the stratum) and that every geodesic of
  `Ω_k(n)` from `J_k` is an `O(n)`-geodesic `J_k exp(tV)`, whose length is `≥ π√n` by the spectral
  argument above; no comparison of distances in `Ω_k(n)` and `O(n)` is needed.
* "Homeomorphic": paths here are functions on `ℝ`, so the homeomorphism is with the separation
  quotient of Milnor's pseudometric; for homotopy groups the homotopy equivalence is used.
* Lemma 24.4 (iii) needs `Ω_{k+1}(n) ≠ ∅` (here: `IsAnticommFamily J (k + 1)`).
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Skew matrices with `exp V = −I` -/

section ExpNegOne

/-- A solution of `c' = Vc` is `c(t) = exp(tV) c(0)`. -/
theorem eq_exp_smul_mul_of_hasDerivAt {V : Matrix ι ι ℝ} {c : ℝ → Matrix ι ι ℝ}
    (hc : ∀ t, HasDerivAt c (V * c t) t) (t : ℝ) :
    c t = NormedSpace.exp (t • V) * c 0 := by
  set g : ℝ → Matrix ι ι ℝ := fun s => NormedSpace.exp (s • -V) * c s with hgdef
  have hg : ∀ s, HasDerivAt g 0 s := fun s => by
    have h1 := (hasDerivAt_exp_smul_const (-V) s).mul (hc s)
    refine h1.congr_deriv ?_
    have hcomm : NormedSpace.exp (s • -V) * -V = -V * NormedSpace.exp (s • -V) :=
      exp_smul_mul_self (-V) s
    have hcomm' : NormedSpace.exp (s • -V) * V = V * NormedSpace.exp (s • -V) := by
      have := congrArg Neg.neg hcomm
      simpa only [Matrix.mul_neg, Matrix.neg_mul, neg_neg] using this
    rw [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, neg_add_eq_zero]
  have hgc : ∀ s, g s = g 0 := fun s =>
    is_const_of_deriv_eq_zero (fun u => (hg u).differentiableAt) (fun u => (hg u).deriv) s 0
  have h0 : g 0 = c 0 := by simp [hgdef]
  have ht := hgc t
  rw [h0] at ht
  calc c t = NormedSpace.exp (t • V) * (NormedSpace.exp (t • -V) * c t) := by
        rw [← Matrix.mul_assoc, smul_neg, exp_mul_exp_neg (t • V), Matrix.one_mul]
    _ = NormedSpace.exp (t • V) * c 0 := by rw [← ht]

omit [DecidableEq ι] in
theorem inner_mul_left_adj (V A B : Matrix ι ι ℝ) : ⟪V * A, B⟫ = ⟪A, Vᴴ * B⟫ := by
  rw [inner_def, inner_def, conjTranspose_mul, Matrix.mul_assoc]

omit [DecidableEq ι] in
theorem inner_self_mul_skew {V : Matrix ι ι ℝ} (hV : Vᴴ = -V) (E : Matrix ι ι ℝ) :
    ⟪E, V * E⟫ = 0 := by
  have h1 : ⟪V * E, E⟫ = -⟪V * E, E⟫ := by
    conv_lhs => rw [inner_mul_left_adj, hV, Matrix.neg_mul, inner_neg_right, real_inner_comm]
  have h2 : ⟪V * E, E⟫ = 0 := by linarith
  rwa [real_inner_comm] at h2

/-- **The eigenvalues of `−V²` for `exp V = −I`** (Lemma 24.1 and Lemma 6.1 of the exposition):
if `V` is skew, `exp V = −I`, `E ≠ 0` and `V²E = −λE`, then `λ ≥ π²`.  (On the span of the
columns of `E`, `exp(tV) = cos(√λ t) + sin(√λ t) V/√λ`, and `cos √λ = −1`.) -/
theorem pi_sq_le_of_sq_mul {V E : Matrix ι ι ℝ} (hV : Vᴴ = -V)
    (hexp : NormedSpace.exp V = -1) (hE : E ≠ 0) {l : ℝ} (hl : V * (V * E) = -l • E) :
    Real.pi ^ 2 ≤ l := by
  have hEpos : 0 < ‖E‖ := norm_pos_iff.2 hE
  have hnorm : ‖V * E‖ ^ 2 = l * ‖E‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_mul_left_adj, hV, Matrix.neg_mul, hl,
      inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hl0 : 0 ≤ l := by
    by_contra h
    push Not at h
    have : l * ‖E‖ ^ 2 < 0 := mul_neg_of_neg_of_pos h (by positivity)
    linarith [sq_nonneg ‖V * E‖]
  rcases eq_or_lt_of_le hl0 with hl0 | hlpos
  · exfalso
    have hVE : V * E = 0 := by
      rw [← hl0, zero_mul] at hnorm
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hnorm)
    have := eq_exp_smul_mul_of_hasDerivAt (V := V) (c := fun _ => E)
      (fun t => by rw [hVE]; exact hasDerivAt_const t E) 1
    rw [one_smul, hexp, Matrix.neg_mul, Matrix.one_mul] at this
    exact hE (by
      have h2 : (2 : ℝ) • E = 0 := by rw [two_smul]; nth_rewrite 1 [this]; exact neg_add_cancel E
      exact (smul_eq_zero.1 h2).resolve_left two_ne_zero)
  · set μ := Real.sqrt l with hμ
    have hμpos : 0 < μ := Real.sqrt_pos.2 hlpos
    have hμsq : μ * μ = l := Real.mul_self_sqrt hl0
    set c : ℝ → Matrix ι ι ℝ := fun t =>
      Real.cos (μ * t) • E + (Real.sin (μ * t) / μ) • (V * E) with hcdef
    have hc : ∀ t, HasDerivAt c (V * c t) t := fun t => by
      have h1 : HasDerivAt (fun t => Real.cos (μ * t)) (-Real.sin (μ * t) * μ) t := by
        have := ((hasDerivAt_id t).const_mul μ).cos
        refine this.congr_deriv ?_
        simp only [id, mul_one]
      have h2 : HasDerivAt (fun t => Real.sin (μ * t) / μ) (Real.cos (μ * t)) t := by
        have := (((hasDerivAt_id t).const_mul μ).sin).div_const μ
        refine this.congr_deriv ?_
        simp only [id, mul_one]
        field_simp
      refine ((h1.smul_const E).add (h2.smul_const (V * E))).congr_deriv ?_
      simp only [hcdef, Matrix.mul_add, Matrix.mul_smul, hl]
      rw [smul_smul, ← hμsq]
      field_simp
      module
    have h1 := eq_exp_smul_mul_of_hasDerivAt hc 1
    simp only [hcdef, one_smul, mul_one, mul_zero, Real.cos_zero, Real.sin_zero, zero_div,
      zero_smul, add_zero, hexp, Matrix.neg_mul, Matrix.one_mul] at h1
    have h2 := congrArg (fun M => ⟪E, M⟫) h1
    simp only [inner_add_right, real_inner_smul_right, inner_self_mul_skew hV,
      inner_neg_right, real_inner_self_eq_norm_sq, mul_zero, add_zero] at h2
    have hcos : Real.cos μ = -1 := by
      have hE2 : ‖E‖ ^ 2 ≠ 0 := by positivity
      field_simp at h2
      linarith
    have hμπ : Real.pi ≤ μ := by
      by_contra h
      push Not at h
      have := Real.cos_lt_cos_of_nonneg_of_le_pi hμpos.le le_rfl h
      rw [Real.cos_pi] at this
      linarith
    calc Real.pi ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ Real.pi_pos.le hμπ 2
      _ = l := by rw [sq, hμsq]

/-- The data of the spectral theorem for `S = VᴴV`: eigenvalues `≥ π²`. -/
theorem exists_eigen_ge {V : Matrix ι ι ℝ} (hV : Vᴴ = -V) (hexp : NormedSpace.exp V = -1) :
    ∃ (U : Matrix ι ι ℝ) (l : ι → ℝ), Uᴴ * U = 1 ∧ Vᴴ * V = U * Matrix.diagonal l * Uᴴ ∧
      ∀ i, Real.pi ^ 2 ≤ l i := by
  set S := Vᴴ * V with hSdef
  have hS : S.IsHermitian := by
    rw [IsHermitian, hSdef, conjTranspose_mul, conjTranspose_conjTranspose]
  have hspec := hS.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at hspec
  set U : Matrix ι ι ℝ := (hS.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hU : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self _
  set l := hS.eigenvalues
  have hD : Matrix.diagonal (RCLike.ofReal ∘ l) = Matrix.diagonal l := by
    congr 1
  rw [hD] at hspec
  refine ⟨U, l, hU, hspec, fun i => ?_⟩
  set E := U * single i i (1 : ℝ)
  have hE : E ≠ 0 := by
    intro h0
    have : Uᴴ * E = single i i (1 : ℝ) := by
      simp only [E, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [h0, Matrix.mul_zero] at this
    have h1 := congrFun (congrFun this i) i
    simp at h1
  have hDs : Matrix.diagonal l * single i i (1 : ℝ) = l i • single i i (1 : ℝ) := by
    ext a b
    simp only [diagonal_mul, Matrix.smul_apply, single_apply, smul_eq_mul]
    split_ifs with h1
    · rw [← h1.1]
    · rw [mul_zero, mul_zero]
  have hSE : S * E = l i • E := by
    calc S * E = U * Matrix.diagonal l * (Uᴴ * U) * single i i (1 : ℝ) := by
          rw [hspec, show E = U * single i i (1 : ℝ) from rfl]
          simp only [Matrix.mul_assoc]
      _ = l i • E := by
          rw [hU, Matrix.mul_one, Matrix.mul_assoc, hDs, Matrix.mul_smul]
  have hVV : V * (V * E) = -l i • E := by
    rw [← Matrix.mul_assoc, neg_smul, ← hSE, hSdef, hV, Matrix.neg_mul, Matrix.neg_mul, neg_neg]
  exact pi_sq_le_of_sq_mul hV hexp hE hVV

theorem norm_sq_eq_trace (V : Matrix ι ι ℝ) : ‖V‖ ^ 2 = trace (Vᴴ * V) := by
  rw [← real_inner_self_eq_norm_sq, inner_def]
  rfl

/-- **Lemma 24.1, the length** (Milnor p. 134): a geodesic `t ↦ x exp(tV)` from `x` to `−x` in
`O(n)` (`V` skew, `exp V = −I`) has length `‖V‖ ≥ π√n`. -/
theorem pi_sq_mul_card_le_norm_sq {V : Matrix ι ι ℝ} (hV : Vᴴ = -V)
    (hexp : NormedSpace.exp V = -1) : Real.pi ^ 2 * Fintype.card ι ≤ ‖V‖ ^ 2 := by
  obtain ⟨U, l, hU, hspec, hl⟩ := exists_eigen_ge hV hexp
  rw [norm_sq_eq_trace, hspec, trace_mul_cycle, hU, Matrix.one_mul, trace_diagonal]
  calc Real.pi ^ 2 * Fintype.card ι = ∑ _i : ι, Real.pi ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i, l i := Finset.sum_le_sum fun i _ => hl i

/-- **Lemma 24.1, equality** (Milnor p. 134): the length is `π√n` only if `V² = −π²I`. -/
theorem mul_self_eq_of_norm_sq_le {V : Matrix ι ι ℝ} (hV : Vᴴ = -V)
    (hexp : NormedSpace.exp V = -1) (hle : ‖V‖ ^ 2 ≤ Real.pi ^ 2 * Fintype.card ι) :
    V * V = -(Real.pi ^ 2) • (1 : Matrix ι ι ℝ) := by
  obtain ⟨U, l, hU, hspec, hl⟩ := exists_eigen_ge hV hexp
  rw [norm_sq_eq_trace, hspec, trace_mul_cycle, hU, Matrix.one_mul, trace_diagonal] at hle
  have hsum : ∑ i, (l i - Real.pi ^ 2) ≤ 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hl i))).1
    (le_antisymm hsum (Finset.sum_nonneg fun i _ => sub_nonneg.2 (hl i)))
  have hlc : l = fun _ => Real.pi ^ 2 := funext fun i => by
    have := hzero i (Finset.mem_univ i); linarith
  have hS : Vᴴ * V = Real.pi ^ 2 • (1 : Matrix ι ι ℝ) := by
    rw [hspec, hlc, ← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      mul_conjTranspose_eq_one hU]
  rw [hV, Matrix.neg_mul] at hS
  rw [← neg_neg (V * V), hS, neg_smul]

end ExpNegOne

/-! ### The minimal geodesics from `p` to `−p` -/

section MinGeo

variable {J : ℕ → Matrix ι ι ℝ} {k : ℕ} {p : Matrix ι ι ℝ}

variable (J k p) in
/-- **The initial directions of the minimal geodesics** from `p` to `−p` in `Ω_k(n)`: the
`A ∈ 𝒯_p` with `A² = −I` (Milnor p. 137; the geodesic is `t ↦ p exp(πtA)`). -/
def minVelO : Set (Matrix ι ι ℝ) := {A | A ∈ tanAlg J k p ∧ A * A = -1}

/-- The geodesic `t ↦ p exp(πtA)`. -/
def omegaGeo (p A : Matrix ι ι ℝ) : ℝ → Matrix ι ι ℝ :=
  fun t => p * NormedSpace.exp (t • (Real.pi • A))

theorem exp_pi_smul_of_minVelO {A : Matrix ι ι ℝ} (hA : A ∈ minVelO J k p) :
    NormedSpace.exp (Real.pi • A) = -1 :=
  exp_pi_smul hA.2

theorem norm_sq_of_minVelO {A : Matrix ι ι ℝ} (hA : A ∈ minVelO J k p) :
    ‖A‖ ^ 2 = Fintype.card ι := by
  rw [norm_sq_eq_trace, hA.1.1, Matrix.neg_mul, hA.2, neg_neg, trace_one]

theorem norm_pi_smul_of_minVelO {A : Matrix ι ι ℝ} (hA : A ∈ minVelO J k p) :
    ‖Real.pi • A‖ = Real.pi * Real.sqrt (Fintype.card ι) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos Real.pi_pos, ← norm_sq_of_minVelO hA,
    Real.sqrt_sq (norm_nonneg _)]

variable (hJ : IsAnticommFamily J k) (hp : p ∈ Omega J k)
include hJ hp

theorem neg_mem_omegaStratum {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p) :
    -p ∈ omegaStratum J k p := by
  have := (isTotGeo_omegaStratum hJ p).mul_exp_mem p (self_mem_omegaStratum hp) _
    ((tanAlg J k p).smul_mem Real.pi hA₀.1)
  rwa [exp_pi_smul_of_minVelO hA₀, Matrix.mul_neg, Matrix.mul_one] at this

theorem omegaGeo_mem_pathSpace {A : Matrix ι ι ℝ} (hA : A ∈ minVelO J k p) :
    omegaGeo p A ∈ pathSpace (omegaStratum J k p) p (-p) := by
  have := (isTotGeo_omegaStratum hJ p).mem_pathSpace_mul_exp (self_mem_omegaStratum hp)
    ((tanAlg J k p).smul_mem Real.pi hA.1)
  rwa [exp_pi_smul_of_minVelO hA, Matrix.mul_neg, Matrix.mul_one] at this

omit hJ in
theorem energy_omegaGeo {A : Matrix ι ι ℝ} (hA : A ∈ minVelO J k p) :
    energy (omegaGeo p A) 0 1 = Real.pi ^ 2 * Fintype.card ι := by
  unfold omegaGeo
  rw [IsTotGeo.energy_mul_exp_smul (omega_orth hp)
    ((tanAlg J k p).smul_mem Real.pi hA.1).1, norm_pi_smul_of_minVelO hA, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]

/-- **The distance from `p` to `−p` in `Ω_k(n)` is `π√n`** (Milnor p. 138): `≤` by a semicircle,
`≥` because a minimal geodesic exists (Hopf–Rinow at `p`) and is `t ↦ p exp(tV)` with
`exp V = −I`, of length `‖V‖ ≥ π√n` (`Morse.pi_sq_mul_card_le_norm_sq`). -/
theorem riemDist_omegaStratum {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p) :
    riemDist (N := omegaStratum J k p) p (-p) =
      ENNReal.ofReal (Real.pi * Real.sqrt (Fintype.card ι)) := by
  set hN := isSliceSubmanifold_omegaStratum hJ p
  have hT := isTotGeo_omegaStratum hJ p
  have hpN := self_mem_omegaStratum hp
  have hpo := omega_orth hp
  have hγ := omegaGeo_mem_pathSpace hJ hp hA₀
  have hle : riemDist (N := omegaStratum J k p) p (-p) ≤
      ENNReal.ofReal (Real.pi * Real.sqrt (Fintype.card ι)) := by
    have h1 := riemDist_le_pathLength (N := omegaStratum J k p) hγ.1 hγ.2.1
    rw [hγ.2.2.1, hγ.2.2.2] at h1
    unfold omegaGeo at h1
    rw [IsTotGeo.pathLength_mul_exp_smul hpo
      ((tanAlg J k p).smul_mem Real.pi hA₀.1).1, norm_pi_smul_of_minVelO hA₀] at h1
    exact h1
  refine le_antisymm hle ?_
  have hne : riemDist (N := omegaStratum J k p) p (-p) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  obtain ⟨v, hv, hexpv, hρ, -⟩ := theorem_10_9 (hN := hN) (p := ⟨p, hpN⟩)
    (hT.isGeodesicallyComplete ⟨p, hpN⟩) (q := ⟨-p, neg_mem_omegaStratum hJ hp hA₀⟩) hne
  rw [hT.mem_tangentSubspace_iff] at hv
  have hv' : v = p * (pᴴ * v) := by
    rw [← Matrix.mul_assoc, mul_conjTranspose_eq_one hpo, Matrix.one_mul]
  have hexp : Morse.exp hN p v = p * NormedSpace.exp (pᴴ * v) := by
    conv_lhs => rw [hv']
    exact hT.exp_eq hpN hv
  change Morse.exp hN p v = -p at hexpv
  rw [hexp] at hexpv
  have hexpV : NormedSpace.exp (pᴴ * v) = -1 := by
    have := congrArg (pᴴ * ·) hexpv
    simpa only [← Matrix.mul_assoc, hpo, Matrix.one_mul, Matrix.mul_neg] using this
  have hnorm : ‖v‖ = ‖pᴴ * v‖ := by
    conv_lhs => rw [hv']
    exact (mulLeftIso p hpo).norm_map _
  change riemDist (N := omegaStratum J k p) p (-p) = ENNReal.ofReal ‖v‖ at hρ
  rw [hρ, hnorm]
  apply ENNReal.ofReal_le_ofReal
  have h2 := pi_sq_mul_card_le_norm_sq hv.1 hexpV
  have h3 : (Real.pi * Real.sqrt (Fintype.card ι)) ^ 2 ≤ ‖pᴴ * v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; exact h2
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h3

/-- Every path from `p` to `−p` in `Ω_k(n)` has energy `≥ π²n`. -/
theorem pi_sq_card_le_energy {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p) {γ : ℝ → Matrix ι ι ℝ}
    (hγ : γ ∈ pathSpace (omegaStratum J k p) p (-p)) :
    Real.pi ^ 2 * Fintype.card ι ≤ energy γ 0 1 := by
  have h1 := riemDist_le_pathLength (N := omegaStratum J k p) hγ.1 hγ.2.1
  rw [hγ.2.2.1, hγ.2.2.2, riemDist_omegaStratum hJ hp hA₀] at h1
  have h2 := (ENNReal.ofReal_le_ofReal_iff hγ.1.isAdmissible.pathLength_nonneg).1 h1
  have h3 := pathLength_sq_le_energy hγ.1
  rw [sub_zero, one_mul] at h3
  calc Real.pi ^ 2 * Fintype.card ι = (Real.pi * Real.sqrt (Fintype.card ι)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    _ ≤ pathLength γ 0 1 ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    _ ≤ _ := h3

/-- The geodesic `t ↦ p exp(πtA)`, `A ∈ minVelO`, as a point of `Ω(Ω_k(n); p, −p)`. -/
def omegaPath (A : minVelO J k p) : PathSp (omegaStratum J k p) p (-p) :=
  ⟨omegaGeo p A, omegaGeo_mem_pathSpace hJ hp A.2⟩

theorem omegaPath_apply (A : minVelO J k p) (t : ℝ) :
    (omegaPath hJ hp A : ℝ → Matrix ι ι ℝ) t = p * NormedSpace.exp (t • (Real.pi • A.1)) := rfl

/-- **The semicircles are minimal** (Milnor p. 138): `t ↦ p exp(πtA)` has least energy. -/
theorem omegaPath_mem_minPaths (A : minVelO J k p) :
    omegaPath hJ hp A ∈ minPaths (omegaStratum J k p) p (-p) := fun γ' => by
  change energy (omegaGeo p A) 0 1 ≤ _
  rw [energy_omegaGeo hp A.2]
  exact pi_sq_card_le_energy hJ hp A.2 γ'.mem

/-- **Conversely, every path of least energy from `p` to `−p` is a semicircle** on `[0, 1]`
(Milnor p. 138): it is a geodesic `t ↦ p exp(tV)` (`Morse.isUnbrokenGeodesic_of_minimal`,
`Morse.IsTotGeo.eqOn_of_isUnbrokenGeodesic`) with `exp V = −I` and `‖V‖² ≤ π²n`, hence
`V² = −π²I` (`Morse.mul_self_eq_of_norm_sq_le`). -/
theorem exists_minVelO_of_mem_minPaths {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p)
    {γ : PathSp (omegaStratum J k p) p (-p)}
    (hγ : γ ∈ minPaths (omegaStratum J k p) p (-p)) :
    ∃ A ∈ minVelO J k p, EqOn γ (omegaGeo p A) (Icc 0 1) := by
  set hN := isSliceSubmanifold_omegaStratum hJ p
  have hT := isTotGeo_omegaStratum hJ p
  have hpo := omega_orth hp
  have hgeo := isUnbrokenGeodesic_of_minimal (hN := hN) γ.mem (fun γ' hγ' => hγ ⟨γ', hγ'⟩)
  obtain ⟨V, hV, heq⟩ := hT.eqOn_of_isUnbrokenGeodesic γ.mem hgeo
  have hexp : NormedSpace.exp V = -1 := by
    have h1 := heq ⟨zero_le_one, le_rfl⟩
    rw [γ.mem.2.2.2] at h1
    simp only [one_smul] at h1
    have := congrArg (pᴴ * ·) h1
    simpa only [← Matrix.mul_assoc, hpo, Matrix.one_mul, Matrix.mul_neg] using this.symm
  have hE := hγ (omegaPath hJ hp ⟨A₀, hA₀⟩)
  change energy γ 0 1 ≤ energy (omegaGeo p A₀) 0 1 at hE
  rw [energy_omegaGeo hp hA₀, energy_congr heq, IsTotGeo.energy_mul_exp_smul hpo hV.1] at hE
  have hsq := mul_self_eq_of_norm_sq_le hV.1 hexp hE
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  refine ⟨Real.pi⁻¹ • V, ⟨(tanAlg J k p).smul_mem _ hV, ?_⟩, fun t ht => ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul, smul_smul]
    rw [show Real.pi⁻¹ * Real.pi⁻¹ * -(Real.pi ^ 2) = -1 by field_simp]
    simp
  · rw [heq ht]
    simp only [omegaGeo, smul_smul, mul_inv_cancel₀ hπ, one_smul]

omit hJ hp in
/-- **Milnor's Remark (p. 138)**: the midpoint of the semicircle `t ↦ p exp(πtA)` is `pA`. -/
theorem omegaGeo_half {A : Matrix ι ι ℝ} (hA : A * A = -1) : omegaGeo p A (1 / 2) = p * A := by
  simp only [omegaGeo, smul_smul]
  rw [exp_smul_of_mul_self_eq_neg_one hA, show 1 / 2 * Real.pi = Real.pi / 2 by ring,
    Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, zero_add, one_smul]

omit hJ in
theorem speed_omegaGeo {A : Matrix ι ι ℝ} (hA : A ∈ minVelO J k p) (t : ℝ) :
    PathSp.speed (omegaGeo p A) t = Real.pi * Real.sqrt (Fintype.card ι) := by
  unfold omegaGeo
  rw [PathSp.speed, IsTotGeo.norm_deriv_mul_exp_smul (omega_orth hp)
    ((tanAlg J k p).smul_mem Real.pi hA.1).1, norm_pi_smul_of_minVelO hA]

/-- **`A ↦ (t ↦ p exp(πtA))` is continuous for Milnor's metric**: all speeds are `π√n`, so the
`L²` term of the metric vanishes, and the uniform term is controlled by pointwise convergence at
bounded energy (`Morse.PathSp.eventually_supDist_le_of_tendsto_apply`). -/
theorem continuous_omegaPath : Continuous (omegaPath hJ hp) := by
  refine continuous_iff_continuousAt.2 fun A => ?_
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0, ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr' : 0 < r := ENNReal.ofReal_pos.1 hr
  have h1 := PathSp.eventually_supDist_le_of_tendsto_apply
    (isSliceSubmanifold_omegaStratum hJ p)
    (C := Real.pi ^ 2 * Fintype.card ι) (l := 𝓝 A)
    (αs := fun B : minVelO J k p => (omegaPath hJ hp B : ℝ → Matrix ι ι ℝ))
    (Eventually.of_forall fun B => ⟨(omegaPath hJ hp B).mem, (energy_omegaGeo hp B.2).le⟩)
    (omegaPath hJ hp A).mem (energy_omegaGeo hp A.2).le (fun s _ =>
      (((continuous_const.mul (contDiff_exp_matrix.continuous.comp
        ((continuous_const_smul s).comp (continuous_const_smul Real.pi))))).comp
        continuous_subtype_val).tendsto A) hr'
  filter_upwards [h1] with B hB
  have hl2 : PathSp.l2Dist (omegaPath hJ hp B : ℝ → Matrix ι ι ℝ) (omegaPath hJ hp A) = 0 := by
    simp only [PathSp.l2Dist]
    change √(∫ t in (0 : ℝ)..1, (PathSp.speed (omegaGeo p B.1) t -
      PathSp.speed (omegaGeo p A.1) t) ^ 2) = 0
    simp only [speed_omegaGeo hp B.2, speed_omegaGeo hp A.2, sub_self]
    simp
  rw [PathSp.edist_def, hl2, ENNReal.ofReal_zero, add_zero]
  exact hB.trans hrε.le

omit hJ hp in
theorem continuous_apply_half_omega :
    Continuous fun γ : PathSp (omegaStratum J k p) p (-p) => (γ : ℝ → Matrix ι ι ℝ) (1 / 2) :=
  (continuous_eval_const (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval)).comp
    (continuous_subtype_val.comp PathSp.continuous_toPathC)

/-- `A ↦ (t ↦ p exp(πtA))`, `minVelO → Ω^d`. -/
def minVelToOmegaPaths : C(minVelO J k p, minPaths (omegaStratum J k p) p (-p)) :=
  ⟨fun A => ⟨omegaPath hJ hp A, omegaPath_mem_minPaths hJ hp A⟩,
    (continuous_omegaPath hJ hp).subtype_mk _⟩

omit hJ hp in
theorem conjTranspose_mul_half {A : Matrix ι ι ℝ} (hpo : pᴴ * p = 1) (hA : A * A = -1) :
    pᴴ * omegaGeo p A (1 / 2) = A := by
  rw [omegaGeo_half hA, ← Matrix.mul_assoc, hpo, Matrix.one_mul]

theorem half_mem_minVelO {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p)
    {γ : PathSp (omegaStratum J k p) p (-p)} (hγ : γ ∈ minPaths (omegaStratum J k p) p (-p)) :
    pᴴ * (γ : ℝ → Matrix ι ι ℝ) (1 / 2) ∈ minVelO J k p := by
  obtain ⟨A, hA, heq⟩ := exists_minVelO_of_mem_minPaths hJ hp hA₀ hγ
  rw [heq ⟨by norm_num, by norm_num⟩, conjTranspose_mul_half (omega_orth hp) hA.2]
  exact hA

/-- The midpoint map `Ω^d → minVelO`, `γ ↦ pᴴ γ(1/2)` (Milnor's Remark p. 138: the minimal
geodesic is determined by its midpoint). -/
def omegaPathsToMinVel {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p) :
    C(minPaths (omegaStratum J k p) p (-p), minVelO J k p) where
  toFun γ := ⟨pᴴ * (γ.1 : ℝ → Matrix ι ι ℝ) (1 / 2), half_mem_minVelO hJ hp hA₀ γ.2⟩
  continuous_toFun :=
    ((continuous_const.mul (continuous_apply_half_omega.comp continuous_subtype_val))).subtype_mk
      _

theorem omegaPathsToMinVel_minVelToOmegaPaths {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p)
    (A : minVelO J k p) :
    omegaPathsToMinVel hJ hp hA₀ (minVelToOmegaPaths hJ hp A) = A :=
  Subtype.ext (conjTranspose_mul_half (omega_orth hp) A.2.2)

theorem edist_minVelToOmegaPaths {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p)
    (γ : minPaths (omegaStratum J k p) p (-p)) :
    edist (minVelToOmegaPaths hJ hp (omegaPathsToMinVel hJ hp hA₀ γ)) γ = 0 := by
  obtain ⟨A, hA, heq⟩ := exists_minVelO_of_mem_minPaths hJ hp hA₀ γ.2
  rw [Subtype.edist_eq]
  refine PathSp.edist_eq_zero_of_eqOn fun t ht => ?_
  change omegaGeo p (pᴴ * (γ.1 : ℝ → Matrix ι ι ℝ) (1 / 2)) t = (γ.1 : ℝ → Matrix ι ι ℝ) t
  rw [heq ⟨by norm_num, by norm_num⟩, conjTranspose_mul_half (omega_orth hp) hA.2, heq ht]

/-- **Lemma 24.4 (iii) for the path space, up to homotopy** (Milnor p. 138):
`A ↦ (t ↦ p exp(πtA))` is a homotopy equivalence from `minVelO` to the space `Ω^d` of minimal
geodesics from `p` to `−p` in `Ω_k(n)`, with homotopy inverse `γ ↦ pᴴγ(1/2)`. -/
def omegaMinPathsHomotopyEquiv {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p) :
    ContinuousMap.HomotopyEquiv (minVelO J k p) (minPaths (omegaStratum J k p) p (-p)) where
  toFun := minVelToOmegaPaths hJ hp
  invFun := omegaPathsToMinVel hJ hp hA₀
  left_inv := by
    have : (omegaPathsToMinVel hJ hp hA₀).comp (minVelToOmegaPaths hJ hp) =
        ContinuousMap.id _ := by
      ext A : 1
      exact omegaPathsToMinVel_minVelToOmegaPaths hJ hp hA₀ A
    rw [this]
  right_inv := by
    classical
    refine ⟨{
      toFun := fun x => if (x.1 : ℝ) < 1 then
        minVelToOmegaPaths hJ hp (omegaPathsToMinVel hJ hp hA₀ x.2) else x.2
      continuous_toFun := PathSp.continuous_of_edist_eq_zero continuous_snd fun x => ?_
      map_zero_left := fun γ => by simp
      map_one_left := fun γ => by simp }⟩
    split_ifs
    · exact edist_minVelToOmegaPaths hJ hp hA₀ x.2
    · exact edist_self _

/-- **Lemma 24.4 (iii) for the path space** (Milnor p. 138): `minVelO` is homeomorphic to the
space of minimal geodesics from `p` to `−p` (up to the identification of paths agreeing on
`[0, 1]`, the separation quotient of Milnor's pseudometric). -/
def omegaMinPathsHomeomorph {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p) :
    minVelO J k p ≃ₜ SeparationQuotient (minPaths (omegaStratum J k p) p (-p)) where
  toFun A := SeparationQuotient.mk (minVelToOmegaPaths hJ hp A)
  invFun := SeparationQuotient.lift (omegaPathsToMinVel hJ hp hA₀) fun _ _ h =>
    (h.map (omegaPathsToMinVel hJ hp hA₀).continuous).eq
  left_inv A := by
    simp only [SeparationQuotient.lift_mk]
    exact omegaPathsToMinVel_minVelToOmegaPaths hJ hp hA₀ A
  right_inv := SeparationQuotient.surjective_mk.forall.2 fun γ => by
    simp only [SeparationQuotient.lift_mk]
    exact SeparationQuotient.mk_eq_mk.2
      (EMetric.inseparable_iff.2 (edist_minVelToOmegaPaths hJ hp hA₀ γ))
  continuous_toFun := SeparationQuotient.continuous_mk.comp (minVelToOmegaPaths hJ hp).continuous
  continuous_invFun := SeparationQuotient.continuous_lift (omegaPathsToMinVel hJ hp hA₀).continuous

end MinGeo

/-! ### Lemma 24.4 (iii): the minimal geodesics are `Ω_{k+1}(n)` -/

section Lemma244

variable {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

variable (J k) in
/-- Milnor's base point `J_k` of `Ω_k(n)` (`J_0 = I`, `Ω_0(n) = O(n)`). -/
def basePt : Matrix ι ι ℝ := if k = 0 then 1 else J k

theorem basePt_mem_omega (hJ : IsAnticommFamily J k) : basePt J k ∈ Omega J k := by
  unfold basePt
  split_ifs with hk
  · subst hk; exact mem_omega_zero (by simp)
  · exact hJ.mem_omega (by omega)

/-- **Lemma 24.4 (iii), algebraic part** (Milnor p. 137): `A` is the initial direction of a
minimal geodesic from `J_k` to `−J_k` iff `J' = J_kA ∈ Ω_{k+1}(n)` (for `k = 0`: `J_0 = I` and
`Ω_1(n)` is the set of complex structures, Lemma 24.1). -/
theorem mem_minVelO_iff (hJ : IsAnticommFamily J k) {A : Matrix ι ι ℝ} :
    A ∈ minVelO J k (basePt J k) ↔ basePt J k * A ∈ Omega J (k + 1) := by
  unfold basePt
  split_ifs with hk
  · subst hk
    rw [Matrix.one_mul]
    constructor
    · rintro ⟨⟨h1, -, -⟩, h2⟩
      exact ⟨isComplexStructure_iff.2 ⟨by rw [← conjTranspose_real, h1], h2⟩,
        fun α h1 h2 => absurd (h1.trans h2) (by norm_num)⟩
    · rintro ⟨hc, -⟩
      obtain ⟨h1, h2⟩ := isComplexStructure_iff.1 hc
      exact ⟨⟨by rw [conjTranspose_real, h1], fun h => absurd rfl h,
        fun α _ h => (by omega : False).elim⟩, h2⟩
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
    have hJk := (hJ.cs k hk1 le_rfl).2
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact mul_mem_omega_succ hJ hk1
        (isComplexStructure_iff.2 ⟨by rw [← conjTranspose_real, h1], h4⟩) (h2 hk) h3
    · intro hJ'
      obtain ⟨hc, hak, hα, -⟩ := omega_succ_decomp hJ hk1 hJ'
      have hA : -(J k * (J k * A)) = A := by
        rw [← Matrix.mul_assoc, hJk, Matrix.neg_mul, Matrix.one_mul, neg_neg]
      rw [hA] at hc hak hα
      obtain ⟨h1, h2⟩ := isComplexStructure_iff.1 hc
      exact ⟨⟨by rw [conjTranspose_real, h1], fun _ => hak, hα⟩, h2⟩

/-- **Lemma 24.4 (iii)** (Milnor p. 138): `A ↦ J_kA` is a homeomorphism from the initial
directions of the minimal geodesics from `J_k` to `−J_k` onto `Ω_{k+1}(n)` (inverse
`J' ↦ J_kᴴJ'`); `J_kA` is the midpoint of the geodesic (`Morse.omegaGeo_half`). -/
def minVelOHomeomorph (hJ : IsAnticommFamily J k) :
    minVelO J k (basePt J k) ≃ₜ Omega J (k + 1) where
  toFun A := ⟨basePt J k * A, (mem_minVelO_iff hJ).1 A.2⟩
  invFun J' := ⟨(basePt J k)ᴴ * J', (mem_minVelO_iff hJ).2 (by
    rw [← Matrix.mul_assoc, mul_conjTranspose_eq_one (omega_orth (basePt_mem_omega hJ)),
      Matrix.one_mul]
    exact J'.2)⟩
  left_inv A := Subtype.ext (by
    simp only
    rw [← Matrix.mul_assoc, omega_orth (basePt_mem_omega hJ), Matrix.one_mul])
  right_inv J' := Subtype.ext (by
    simp only
    rw [← Matrix.mul_assoc, mul_conjTranspose_eq_one (omega_orth (basePt_mem_omega hJ)),
      Matrix.one_mul])
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

/-- **The semicircle** of `J' ∈ Ω_{k+1}(n)`: `t ↦ cos(πt) J_k + sin(πt) J'` (Milnor p. 138). -/
theorem omegaGeo_eq_semicircle (hJ : IsAnticommFamily J k) {J' : Matrix ι ι ℝ}
    (hJ' : J' ∈ Omega J (k + 1)) (t : ℝ) :
    omegaGeo (basePt J k) ((basePt J k)ᴴ * J') t =
      Real.cos (Real.pi * t) • basePt J k + Real.sin (Real.pi * t) • J' := by
  have hpo := omega_orth (basePt_mem_omega hJ)
  have hA : (basePt J k)ᴴ * J' ∈ minVelO J k (basePt J k) :=
    (minVelOHomeomorph hJ).symm ⟨J', hJ'⟩ |>.2
  simp only [omegaGeo, smul_smul]
  rw [exp_smul_of_mul_self_eq_neg_one hA.2, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
    Matrix.mul_smul, ← Matrix.mul_assoc, mul_conjTranspose_eq_one hpo, Matrix.one_mul,
    mul_comm t Real.pi]

end Lemma244

end Morse
