import Morse.Chapter15.OmegaIntertwiners
import Morse.Chapter15.SplittingData
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
Milnor, *Morse Theory*, §24, Lemma 24.2 (p. 135) and pp. 145–146; Exposition/Chapter15.md, §1 and
§6, case `k ≢ 2 (mod 4)`.

# The index of non-minimal geodesics from `J_k` to `−J_k` in `Ω_k(n)`

## Milnor's text, paraphrased

(p. 146) "The index of a non-minimal geodesic from `J` to `−J` in `Ω_k(n)` is `≥ n/m_{k+1} − 1`"
for `k ≢ 2 (mod 4)`; (Lemma 24.2, p. 135) for `k = 0`, in `O(2m)`, it is `≥ 2m − 2`.

## What is formalized

* `Morse.matE`: Mathlib's star-algebra isomorphism `Mₙ(ℝ) ≅ End(ℝⁿ)`, transporting the matrices
  `A`, `J_k`, `J_α` to operators (`Morse.isOmegaOps_matE`) and the data back.
* `Morse.one_le_of_sq_mulVec`, `Morse.one_le_of_minInvar`: `A²v = −cv`, `v ≠ 0`, `exp(πA) = −I`
  imply `c ≥ 1`.
* `Morse.exists_killing_spaces_omega`: the Killing-field spaces for `A ∈ 𝒯_{J_k}`,
  `exp(πA) = −I`, `A² ≠ −I`.
* **`Morse.le_formIndex_of_not_minimal_omega`**: for `k + 1 ≤ 8`, `k + 1 ≢ 3 (mod 4)`, every
  geodesic from `J_k` to `−J_k` in (the stratum of) `Ω_k(n)` which does not have least energy has
  index `≥ r₀ s`, where `n = (s + 1)m_{k+1}`; `r₀ = 1`, and `r₀ = 2` is allowed for `k = 0`
  (Lemma 24.2: `2(n/2 − 1) = n − 2`).

## What Milnor leaves implicit

* "Non-minimal" for Theorem 22.1 means "not of least energy"; such a geodesic `t ↦ J_k exp(tV)`
  has `V² ≠ −π²I`, since otherwise its energy is `π²n`, the minimum.
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

/-- The star-algebra isomorphism `Mₙ(ℝ) ≅ End(ℝⁿ)` (Mathlib's `Matrix.toEuclideanCLM`). -/
abbrev matE (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℝ ≃⋆ₐ[ℝ] (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)

theorem matE_mul (M N : Matrix ι ι ℝ) : matE ι (M * N) = matE ι M * matE ι N := map_mul _ _ _
theorem matE_smul (c : ℝ) (M : Matrix ι ι ℝ) : matE ι (c • M) = c • matE ι M := map_smul _ _ _
theorem matE_neg (M : Matrix ι ι ℝ) : matE ι (-M) = -matE ι M := map_neg _ _
theorem matE_sub (M N : Matrix ι ι ℝ) : matE ι (M - N) = matE ι M - matE ι N := map_sub _ _ _
theorem matE_zero : matE ι (0 : Matrix ι ι ℝ) = 0 := map_zero _
theorem matE_inj {M N : Matrix ι ι ℝ} (h : matE ι M = matE ι N) : M = N := (matE ι).injective h

theorem matE_conjTranspose (M : Matrix ι ι ℝ) :
    matE ι Mᴴ = ContinuousLinearMap.adjoint (matE ι M) := by
  rw [← star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint]

theorem adjoint_matE_of_skew {M : Matrix ι ι ℝ} (hM : Mᴴ = -M) :
    ContinuousLinearMap.adjoint (matE ι M) = -matE ι M := by
  rw [← matE_conjTranspose, hM, map_neg]

/-- **The operators of §6**: `A`, `J = basePt`, `J_α` as operators on `ℝⁿ` satisfy Milnor's
relations. -/
theorem isOmegaOps_matE (hJ : IsAnticommFamily J k) {A : Matrix ι ι ℝ}
    (hA : A ∈ tanAlg J k (basePt J k)) :
    IsOmegaOps k (matE ι A) (matE ι (basePt J k)) (fun α => matE ι (J α)) where
  a_skew := adjoint_matE_of_skew hA.1
  q_zero hk := by simp [basePt, hk]
  q_sq hk := by
    have : basePt J k * basePt J k = -1 := by
      simp only [basePt, if_neg hk]; exact (hJ.cs k (Nat.one_le_iff_ne_zero.2 hk) le_rfl).2
    rw [← map_mul, this, map_neg, map_one]
  q_skew hk := by
    refine adjoint_matE_of_skew ?_
    simp only [basePt, if_neg hk]
    rw [conjTranspose_real]; exact (hJ.cs k (Nat.one_le_iff_ne_zero.2 hk) le_rfl).transpose
  aq hk := by rw [← map_mul, hA.2.1 hk, map_neg, map_mul]
  j_sq α h1 h2 := by rw [← map_mul, (hJ.cs α h1 h2.le).2, map_neg, map_one]
  j_skew α h1 h2 := adjoint_matE_of_skew (by
    rw [conjTranspose_real]; exact (hJ.cs α h1 h2.le).transpose)
  j_anti α β h1 h2 h3 h4 hne := by
    rw [← map_mul, hJ.anti α β h1 h2.le h3 h4.le hne, map_neg, map_mul]
  jq α h1 h2 := by
    have hk : k ≠ 0 := by omega
    simp only [basePt, if_neg hk]
    rw [← map_mul, hJ.anti α k h1 h2.le (by omega) le_rfl h2.ne, map_neg, map_mul]
  ja α h1 h2 := by rw [← map_mul, ← hA.2.2 α h1 h2, map_mul]

/-- The matrix with every column equal to `w`. -/
def colRep (w : ι → ℝ) : Matrix ι ι ℝ := Matrix.of fun i _ => w i

omit [DecidableEq ι] in
theorem mul_colRep (A : Matrix ι ι ℝ) (w : ι → ℝ) : A * colRep w = colRep (A *ᵥ w) := by
  ext i l
  simp [colRep, Matrix.mul_apply, mulVec, dotProduct]

/-- **`A² ≤ −1`** (Lemma 6.1): on every vector with `A²v = −cv`, `c ≥ 1`, for `A` skew with
`exp(πA) = −I` (from `Morse.pi_sq_le_of_sq_mul` with `V = πA`). -/
theorem one_le_of_sq_mulVec {A : Matrix ι ι ℝ} (hA : Aᴴ = -A)
    (hexp : NormedSpace.exp (Real.pi • A) = -1) {w : ι → ℝ} (hw : w ≠ 0) {c : ℝ}
    (hc : A *ᵥ (A *ᵥ w) = -(c • w)) : 1 ≤ c := by
  have hV : (Real.pi • A)ᴴ = -(Real.pi • A) := by
    rw [conjTranspose_smul, star_trivial, hA, smul_neg]
  have hE : colRep w ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
    have := congrFun (congrFun h0 i) i
    exact hi (by simpa [colRep] using this)
  have hl : (Real.pi • A) * ((Real.pi • A) * colRep w) = -(Real.pi ^ 2 * c) • colRep w := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, mul_colRep, hc, smul_smul]
    ext i l
    simp [colRep]
    ring
  have := pi_sq_le_of_sq_mul hV hexp hE hl
  have hπ : 0 < Real.pi ^ 2 := by positivity
  nlinarith

theorem one_le_of_minInvar {A : Matrix ι ι ℝ} (hA : Aᴴ = -A)
    (hexp : NormedSpace.exp (Real.pi • A) = -1) {M : Submodule ℝ (EuclideanSpace ℝ ι)}
    (hM : M ≠ ⊥) {c : ℝ} (hc : ∀ v ∈ M, matE ι A (matE ι A v) = -(c • v)) : 1 ≤ c := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM
  refine one_le_of_sq_mulVec hA hexp (w := WithLp.ofLp v) ?_ ?_
  · intro h0; exact hv0 (by simpa using congrArg (WithLp.toLp 2) h0)
  · have := congrArg WithLp.ofLp (hc v hv)
    simpa using this

omit [Fintype ι] [DecidableEq ι] in
theorem commute_adjoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {d g : E →L[ℝ] E} (hdg : d * g = g * d)
    (hg : ContinuousLinearMap.adjoint g = g ∨ ContinuousLinearMap.adjoint g = -g) :
    ContinuousLinearMap.adjoint d * g = g * ContinuousLinearMap.adjoint d := by
  have h1 := congrArg star hdg
  simp only [star_mul, ContinuousLinearMap.star_eq_adjoint] at h1
  rcases hg with hg | hg
  · rw [hg] at h1; exact h1.symm
  · rw [hg, neg_mul, mul_neg, neg_inj] at h1; exact h1.symm

/-- **The algebraic core of the index bound for `k ≢ 2 (mod 4)`** (Milnor pp. 144–146, with
Lemma 6.1 and Lemma 24.8): for `A ∈ 𝒯_{J_k}` with `exp(πA) = −I` and `A² ≠ −I`, there are
Killing-field spaces `𝒳_τ` (`τ ∈ T ⊆ (0, 1)`) of total dimension `r₀ s`, where `ℝⁿ` splits into
`s + 1` minimal pieces of dimension `m_{k+1}`; `r₀ = 1`, or `r₀ = 2` when `k = 0`. -/
theorem exists_killing_spaces_omega (hJ : IsAnticommFamily J k) (hk8 : k + 1 ≤ 8)
    (hk3 : (k + 1) % 4 ≠ 3) {A : Matrix ι ι ℝ} (hA : A ∈ tanAlg J k (basePt J k))
    (hexp : NormedSpace.exp (Real.pi • A) = -1) (hnm : A * A ≠ -1) {r₀ : ℕ}
    (hr₀ : r₀ = 1 ∨ (r₀ = 2 ∧ k = 0)) :
    ∃ (T : Finset ℝ) (𝒳 : ℝ → Submodule ℝ (Matrix ι ι ℝ)) (s : ℕ),
      (∀ τ ∈ T, τ ∈ Ioo (0 : ℝ) 1) ∧ (∀ τ ∈ T, 𝒳 τ ≤ isoAlg J k (basePt J k)) ∧
      (∀ τ ∈ T, ∀ X ∈ 𝒳 τ, X * NormedSpace.exp (τ • (Real.pi • A)) =
        NormedSpace.exp (τ • (Real.pi • A)) * X) ∧
      (∀ τ ∈ T, ∀ X ∈ 𝒳 τ, X * (Real.pi • A) = (Real.pi • A) * X → X = 0) ∧
      ∑ τ ∈ T, finrank ℝ (𝒳 τ) = r₀ * s ∧ (s + 1) * milnorM (k + 1) = Fintype.card ι := by
  have hops := isOmegaOps_matE hJ hA
  have hge : ∀ M : Submodule ℝ (EuclideanSpace ℝ ι), IsMinInvar (omegaGens k (matE ι A)
      (matE ι (basePt J k)) (fun α => matE ι (J α))) M → ∀ c : ℝ,
      (∀ v ∈ M, matE ι A (matE ι A v) = -(c • v)) → 1 ≤ c :=
    fun M hM c hc => one_le_of_minInvar hA.1 hexp hM.1 hc
  have hnm' : matE ι A * matE ι A ≠ -1 := fun h0 => hnm ((matE ι).injective (by
    change matE ι (A * A) = matE ι (-1)
    rw [map_mul, h0, map_neg, map_one]))
  obtain ⟨κ, _, _, ⟨pd⟩, hcard⟩ := hops.exists_omegaPieceData hk8 hk3 hge hnm' hr₀
  rw [finrank_euclideanSpace] at hcard
  set D : κ × Fin r₀ → Matrix ι ι ℝ := fun i => (matE ι).symm (pd.d i) with hD
  have hDe : ∀ i, matE ι (D i) = pd.d i := fun i => by simp [hD]
  have hDH : ∀ i, matE ι (D i)ᴴ = ContinuousLinearMap.adjoint (pd.d i) := fun i => by
    rw [matE_conjTranspose, hDe]
  set R : Matrix ι ι ℝ := (matE ι).symm pd.R with hRdef
  have hRe : matE ι R = pd.R := by simp [hRdef]
  set Q : κ → Matrix ι ι ℝ := fun j' => (matE ι).symm (pd.Q j') with hQdef
  have hQe : ∀ j', matE ι (Q j') = pd.Q j' := fun j' => by simp [hQdef]
  have hstar : ∀ g ∈ omegaGens k (matE ι A) (matE ι (basePt J k)) (fun α => matE ι (J α)),
      ContinuousLinearMap.adjoint g = g ∨ ContinuousLinearMap.adjoint g = -g :=
    hops.isStarSigned
  have hiso : ∀ i, D i - (D i)ᴴ ∈ isoAlg J k (basePt J k) := fun i => by
    have hcq : D i * basePt J k = basePt J k * D i := matE_inj (by
      rw [matE_mul, matE_mul, hDe]; exact pd.hq i)
    have hcqH : (D i)ᴴ * basePt J k = basePt J k * (D i)ᴴ := matE_inj (by
      rw [matE_mul, matE_mul, hDH]
      exact commute_adjoint (pd.hq i) (hstar _ IsOmegaOps.q_mem))
    refine ⟨by rw [conjTranspose_sub, conjTranspose_conjTranspose, neg_sub], ?_,
      fun α h1 h2 => ?_⟩
    · rw [Matrix.sub_mul, Matrix.mul_sub, hcq, hcqH]
    · have hcj : D i * J α = J α * D i := matE_inj (by
        rw [matE_mul, matE_mul, hDe]; exact pd.hj i α h1 h2)
      have hcjH : (D i)ᴴ * J α = J α * (D i)ᴴ := matE_inj (by
        rw [matE_mul, matE_mul, hDH]
        exact commute_adjoint (pd.hj i α h1 h2) (hstar _ (IsOmegaOps.j_mem h1 h2)))
      rw [Matrix.sub_mul, Matrix.mul_sub, hcj, hcjH]
  have hrel : ∀ i, IsInterRel A (D i) pd.a₀ (pd.b i.1) := fun i =>
    { rel := matE_inj (by rw [matE_smul, matE_smul, matE_mul, matE_mul, hDe]; exact pd.rel i)
      left := matE_inj (by rw [matE_smul, matE_mul, matE_mul, hDe]; exact pd.left i)
      right := matE_inj (by rw [matE_smul, matE_mul, matE_mul, hDe]; exact pd.right i) }
  have hR : ∀ i, D i * R = D i := fun i => matE_inj (by rw [matE_mul, hDe, hRe]; exact pd.hR i)
  have hR' : ∀ i, (D i)ᴴ * R = 0 := fun i => matE_inj (by
    rw [matE_mul, hDH, hRe, matE_zero]; exact pd.hR' i)
  have hQ : ∀ j' i, Q j' * (A * D i) = if i.1 = j' then A * D i else 0 := fun j' i => by
    apply matE_inj
    rw [matE_mul, matE_mul, hQe, hDe, pd.hQ j' i]
    split_ifs
    · rw [matE_mul, hDe]
    · rw [matE_zero]
  have hind : ∀ j', LinearIndependent ℝ (fun l : Fin r₀ => A * D (j', l)) := fun j' => by
    have e : (fun l : Fin r₀ => A * D (j', l)) =
        ((matE ι).symm.toAlgEquiv.toLinearEquiv : _ →ₗ[ℝ] Matrix ι ι ℝ) ∘
          (fun l => matE ι A * pd.d (j', l)) := by
      funext l
      simp [hD]
    rw [e]
    exact (pd.hind j').map' _ (LinearEquiv.ker _)
  obtain ⟨T, 𝒳, h1, h2, h3, h4, h5⟩ := exists_killing_spaces (J := J) (k := k) (p := basePt J k)
    hA.1 pd.ha₀ pd.b pd.hb D hiso hrel R hR hR' Q hQ hind
  exact ⟨T, 𝒳, Fintype.card κ, h1, h2, h3, h4, h5, hcard⟩

/-- A geodesic `t ↦ p exp(tV)` from `p` to `−p` with `V² = −π²I` has least energy. -/
theorem norm_sq_of_sq_eq {V : Matrix ι ι ℝ} (hV : Vᴴ = -V)
    (hsq : V * V = -(Real.pi ^ 2) • (1 : Matrix ι ι ℝ)) :
    ‖V‖ ^ 2 = Real.pi ^ 2 * Fintype.card ι := by
  rw [norm_sq_eq_trace, hV, Matrix.neg_mul, hsq, neg_smul, neg_neg, trace_smul, trace_one,
    smul_eq_mul]

/-- **The index bound for `k ≢ 2 (mod 4)`** (Milnor pp. 145–146, and Lemma 24.2 for `k = 0`):
every geodesic from `J_k` to `−J_k` in `Ω_k(n)` which does not have least energy has index
`≥ r₀ s`, where `n = (s + 1) m_{k+1}` (so `s = n/m_{k+1} − 1`), `r₀ = 1` (or `r₀ = 2` for
`k = 0`, Lemma 24.2's `2m − 2`). -/
theorem le_formIndex_of_not_minimal_omega (hJ : IsAnticommFamily J k) (hk8 : k + 1 ≤ 8)
    (hk3 : (k + 1) % 4 ≠ 3) {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k (basePt J k))
    {r₀ : ℕ} (hr₀ : r₀ = 1 ∨ (r₀ = 2 ∧ k = 0)) {γ : ℝ → Matrix ι ι ℝ}
    (hγ : γ ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k))
    (hgeo : IsUnbrokenGeodesic (isSliceSubmanifold_omegaStratum hJ (basePt J k)) γ)
    (hnm : ∃ γ' ∈ pathSpace (omegaStratum J k (basePt J k)) (basePt J k) (-basePt J k),
      energy γ' 0 1 < energy γ 0 1) :
    ∃ s : ℕ, (s + 1) * milnorM (k + 1) = Fintype.card ι ∧
      ((r₀ * s : ℕ) : ℕ∞) ≤
        formIndex (energyHessian (isSliceSubmanifold_omegaStratum hJ (basePt J k)) hγ) := by
  set p := basePt J k with hpdef
  have hp : p ∈ Omega J k := basePt_mem_omega hJ
  have hpo := omega_orth hp
  have hT := isTotGeo_omegaStratum hJ p
  obtain ⟨V, hV, heq⟩ := hT.eqOn_of_isUnbrokenGeodesic hγ hgeo
  have hexpV : NormedSpace.exp V = -1 := by
    have h1 := heq ⟨zero_le_one, le_rfl⟩
    rw [hγ.2.2.2] at h1
    simp only [one_smul] at h1
    have := congrArg (pᴴ * ·) h1
    simpa only [← Matrix.mul_assoc, hpo, Matrix.one_mul, Matrix.mul_neg] using this.symm
  set A := Real.pi⁻¹ • V with hAdef
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hVA : Real.pi • A = V := by rw [hAdef, smul_smul, mul_inv_cancel₀ hπ, one_smul]
  have hA : A ∈ tanAlg J k p := (tanAlg J k p).smul_mem _ hV
  have hexpA : NormedSpace.exp (Real.pi • A) = -1 := by rw [hVA, hexpV]
  have hnmA : A * A ≠ -1 := by
    intro hsq
    obtain ⟨γ', hγ', hlt⟩ := hnm
    have hVV : V * V = -(Real.pi ^ 2) • (1 : Matrix ι ι ℝ) := by
      rw [← hVA, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_smul, smul_neg, ← neg_smul, sq]
    have hE : energy γ 0 1 = Real.pi ^ 2 * Fintype.card ι := by
      rw [energy_congr heq, IsTotGeo.energy_mul_exp_smul hpo hV.1, norm_sq_of_sq_eq hV.1 hVV]
    have := pi_sq_card_le_energy hJ hp hA₀ hγ'
    linarith
  obtain ⟨T, 𝒳, s, h1, h2, h3, h4, h5, h6⟩ :=
    exists_killing_spaces_omega hJ hk8 hk3 hA hexpA hnmA hr₀
  refine ⟨s, h6, ?_⟩
  rw [← h5]
  refine sum_finrank_le_formIndex hJ hp hγ hgeo hV heq T h1 𝒳 h2 (fun τ hτ X hX => ?_)
    (fun τ hτ X hX hc => ?_)
  · rw [← hVA]; exact h3 τ hτ X hX
  · rw [← hVA] at hc; exact h4 τ hτ X hX hc

end Morse
