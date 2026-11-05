import Morse.Chapter15.OmegaMinimal
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
Milnor, *Morse Theory*, §22, Theorem 22.1 (p. 118), for `Ω_k(n)` (§24, p. 145).

# The minimal geodesics of `Ω_k(n)` form a neighbourhood retract

## Milnor's text, paraphrased

(p. 118) Theorem 22.1 assumes that the space `Ω^d` of minimal geodesics is a topological
manifold.  (p. 145) "By Lemma 24.4, `Ω^d` is homeomorphic to `Ω_{k+1}(n)`", a manifold.

## What is formalized

The project's Theorem 22.1 (`Morse.theorem_22_1`) asks instead that `Ω^d` be a retract of an
open neighbourhood in `Ω` (Hanner's theorem for manifolds is not formalized).  Here this is
proved directly:

* `Morse.invSqrtM S = S^{−1/2}` (Mathlib's continuous functional calculus of symmetric matrices),
  `Morse.continuousOn_invSqrtM` (continuous where the spectrum stays in `(0, ∞)`),
  `Morse.invSqrtM_mul_self_mul`, `Morse.invSqrtM_one`, `Morse.spectrum_subset_Ioi`.
* `Morse.midDir`: the orthogonal projection of `pᴴω(1/2)` onto `𝒯_p`; `Morse.polarDir`: its
  **polar part** `Y(YᵀY)^{−1/2}`, which lies in `minVelO` (`Morse.polarDir_mem`: skew, `𝒯_p`-
  relations preserved because `YᵀY` commutes with `p` and the `J_α`, and square `−I`) and is
  the identity on midpoints of minimal geodesics (`Morse.polarDir_mul`).
* `Morse.exists_retraction_minPaths_omega`: **`Ω^d` is a retract of the open set
  `Morse.omegaNbhd = {ω : det(YᵀY) ≠ 0}`**, by `ω ↦ (t ↦ p exp(πt · polarDir ω(1/2)))`.

## What Milnor leaves implicit

* That `Ω^d` is a neighbourhood retract (the content of "manifold" in Theorem 22.1's proof) is a
  matter of finding the nearest complex structure in `𝒯_p` to a matrix close to one: the polar
  decomposition, which needs the linear constraints of `𝒯_p` to be imposed first (orthogonal
  projection) and the square root to commute with them.
-/

open Matrix Set Filter Topology

noncomputable section

namespace Morse

section CFC

open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `x ↦ 1/√x`. -/
def invSqrtR (x : ℝ) : ℝ := (Real.sqrt x)⁻¹

/-- `S^{−1/2}`, by the continuous functional calculus of symmetric matrices. -/
def invSqrtM (S : Matrix ι ι ℝ) : Matrix ι ι ℝ := cfc invSqrtR S

theorem continuousOn_invSqrtR : ContinuousOn invSqrtR (Ioi 0) := fun x hx =>
  (Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_pos.2 hx).ne').continuousWithinAt

theorem continuousOn_invSqrtM {X : Type*} [TopologicalSpace X] {a : X → Matrix ι ι ℝ}
    {t : Set X} (ha : ContinuousOn a t) (hsa : ∀ x ∈ t, IsSelfAdjoint (a x))
    (hspec : ∀ x ∈ t, spectrum ℝ (a x) ⊆ Ioi 0) :
    ContinuousOn (fun x => invSqrtM (a x)) t := by
  refine ContinuousOn.cfc_of_mem_nhdsSet (s := Ioi 0) invSqrtR ?_ ha hsa continuousOn_invSqrtR
  refine isOpen_Ioi.mem_nhdsSet.2 ?_
  intro y hy
  simp only [mem_iUnion] at hy
  obtain ⟨x, hx, hy⟩ := hy
  exact hspec x hx hy

theorem invSqrtM_isSelfAdjoint (S : Matrix ι ι ℝ) : IsSelfAdjoint (invSqrtM S) :=
  cfc_predicate _ _

theorem commute_invSqrtM {S B : Matrix ι ι ℝ} (h : Commute S B) : Commute (invSqrtM S) B :=
  h.cfc_real _

theorem invSqrtM_mul_self_mul {S : Matrix ι ι ℝ} (hsa : IsSelfAdjoint S)
    (hspec : spectrum ℝ S ⊆ Ioi 0) : invSqrtM S * invSqrtM S * S = 1 := by
  have hc : ContinuousOn invSqrtR (spectrum ℝ S) := continuousOn_invSqrtR.mono hspec
  calc invSqrtM S * invSqrtM S * S =
        cfc (fun x => invSqrtR x * invSqrtR x) S * cfc (fun x : ℝ => x) S := by
          rw [invSqrtM, ← cfc_mul invSqrtR invSqrtR S hc hc, cfc_id' ℝ S hsa]
    _ = cfc (fun x => invSqrtR x * invSqrtR x * x) S :=
          (cfc_mul _ _ S (hc.mul hc) (by fun_prop)).symm
    _ = cfc (fun _ : ℝ => (1 : ℝ)) S := cfc_congr fun x hx => by
          have := hspec hx
          simp only [invSqrtR, Set.mem_Ioi] at this ⊢
          rw [← mul_inv, Real.mul_self_sqrt this.le, inv_mul_cancel₀ this.ne']
    _ = 1 := cfc_const_one ℝ S

theorem invSqrtM_one : invSqrtM (1 : Matrix ι ι ℝ) = 1 := by
  have h := cfc_algebraMap (A := Matrix ι ι ℝ) (1 : ℝ) invSqrtR
  rw [map_one] at h
  rw [invSqrtM, h]
  simp [invSqrtR]

/-- `S = YᴴY` invertible has positive spectrum. -/
theorem spectrum_subset_Ioi {Y : Matrix ι ι ℝ} (hdet : (Yᴴ * Y).det ≠ 0) :
    spectrum ℝ (Yᴴ * Y) ⊆ Ioi 0 := by
  have hpsd := posSemidef_conjTranspose_mul_self Y
  intro x hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [spectrum.zero_mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hx
    exact hx hdet
  rw [hpsd.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact lt_of_le_of_ne (hpsd.eigenvalues_nonneg i) (Ne.symm hx0)

end CFC

section Retraction

open scoped Morse.MatrixInner

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}
  {p : Matrix ι ι ℝ}

variable (J k p) in
/-- The orthogonal projection of `pᴴY` onto `𝒯_p` (for `Y = γ(1/2) = pA` on a minimal geodesic,
this is `A`). -/
def midDir (Y : Matrix ι ι ℝ) : Matrix ι ι ℝ := (tanAlg J k p).starProjection (pᴴ * Y)

variable (J k p) in
/-- **The polar part** `Y₁(Y₁ᴴY₁)^{−1/2}` of `Y₁ = midDir Y`: the nearest complex structure in
`𝒯_p`. -/
def polarDir (Y : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  midDir J k p Y * invSqrtM ((midDir J k p Y)ᴴ * midDir J k p Y)

omit [DecidableEq ι] in
theorem isSelfAdjoint_conjTranspose_mul_self' (Y : Matrix ι ι ℝ) : IsSelfAdjoint (Yᴴ * Y) := by
  rw [IsSelfAdjoint, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- **The retraction lands in the minimal directions**: if `Y₁ᴴY₁` is invertible, the polar
part of `Y₁ ∈ 𝒯_p` is a complex structure in `𝒯_p`. -/
theorem polarDir_mem (Y : Matrix ι ι ℝ)
    (hdet : ((midDir J k p Y)ᴴ * midDir J k p Y).det ≠ 0) : polarDir J k p Y ∈ minVelO J k p := by
  set Y₁ := midDir J k p Y with hY₁
  have hmem : Y₁ ∈ tanAlg J k p := (tanAlg J k p).starProjection_apply_mem _
  obtain ⟨h1, h2, h3⟩ := hmem
  set S := Y₁ᴴ * Y₁ with hSdef
  have hS : S = -(Y₁ * Y₁) := by rw [hSdef, h1, Matrix.neg_mul]
  set f := invSqrtM S with hfdef
  have hfsa : fᴴ = f := by
    have := invSqrtM_isSelfAdjoint S
    rwa [IsSelfAdjoint, star_eq_conjTranspose] at this
  have hcY : Commute f Y₁ := commute_invSqrtM (by
    rw [Commute, SemiconjBy, hS, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc])
  have hfSS : f * f * S = 1 := invSqrtM_mul_self_mul (isSelfAdjoint_conjTranspose_mul_self' Y₁)
    (spectrum_subset_Ioi hdet)
  have hcS : Commute f S := commute_invSqrtM (Commute.refl S)
  refine ⟨⟨?_, fun hk => ?_, fun α ha hb => ?_⟩, ?_⟩
  · change (Y₁ * f)ᴴ = -(Y₁ * f)
    rw [conjTranspose_mul, hfsa, h1, Matrix.mul_neg, hcY.eq]
  · have hcp : Commute f p := commute_invSqrtM (by
      rw [Commute, SemiconjBy, hS, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, h2 hk,
        Matrix.mul_neg, ← Matrix.mul_assoc, h2 hk, Matrix.neg_mul, neg_neg, Matrix.mul_assoc])
    change Y₁ * f * p = -(p * (Y₁ * f))
    rw [Matrix.mul_assoc, hcp.eq, ← Matrix.mul_assoc, h2 hk, Matrix.neg_mul, Matrix.mul_assoc]
  · have hcJ : Commute f (J α) := commute_invSqrtM (by
      rw [Commute, SemiconjBy, hS, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc,
        h3 α ha hb, ← Matrix.mul_assoc, h3 α ha hb, Matrix.mul_assoc])
    change Y₁ * f * J α = J α * (Y₁ * f)
    rw [Matrix.mul_assoc, hcJ.eq, ← Matrix.mul_assoc, h3 α ha hb, Matrix.mul_assoc]
  · change Y₁ * f * (Y₁ * f) = -1
    have hYf : Commute Y₁ f := hcY.symm
    have h4 : Commute (Y₁ * Y₁) (f * f) := (hYf.mul_left hYf).mul_right (hYf.mul_left hYf)
    calc Y₁ * f * (Y₁ * f) = Y₁ * Y₁ * (f * f) := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc f, ← hYf.eq]; simp only [Matrix.mul_assoc]
      _ = f * f * (Y₁ * Y₁) := h4.eq
      _ = -(f * f * S) := by rw [hS, Matrix.mul_neg, neg_neg]
      _ = -1 := by rw [hfSS]

/-- On the midpoints `pA` of minimal geodesics the projection and the polar part do nothing. -/
theorem midDir_mul {A : Matrix ι ι ℝ} (hpo : pᴴ * p = 1) (hA : A ∈ minVelO J k p) :
    midDir J k p (p * A) = A := by
  rw [midDir, ← Matrix.mul_assoc, hpo, Matrix.one_mul]
  exact Submodule.starProjection_eq_self_iff.2 hA.1

theorem conjTranspose_mul_self_of_minVelO {A : Matrix ι ι ℝ} (hA : A ∈ minVelO J k p) :
    Aᴴ * A = 1 := by
  rw [hA.1.1, Matrix.neg_mul, hA.2, neg_neg]

theorem polarDir_mul {A : Matrix ι ι ℝ} (hpo : pᴴ * p = 1) (hA : A ∈ minVelO J k p) :
    polarDir J k p (p * A) = A := by
  rw [polarDir, midDir_mul hpo hA, conjTranspose_mul_self_of_minVelO hA, invSqrtM_one,
    Matrix.mul_one]

theorem continuous_midDir : Continuous (midDir J k p) :=
  (tanAlg J k p).starProjection.continuous.comp (continuous_const.mul continuous_id)

variable (hJ : IsAnticommFamily J k) (hp : p ∈ Omega J k)

variable (J k p) in
/-- **The neighbourhood `O` of `Ω^d`**: the paths `ω` for which `Y₁ = midDir ω(1/2)` has
`det(Y₁ᴴY₁) ≠ 0`. -/
def omegaNbhd : Set (PathSp (omegaStratum J k p) p (-p)) :=
  {γ | ((midDir J k p ((γ : ℝ → Matrix ι ι ℝ) (1 / 2)))ᴴ *
    midDir J k p ((γ : ℝ → Matrix ι ι ℝ) (1 / 2))).det ≠ 0}

theorem continuous_midDir_half :
    Continuous fun γ : PathSp (omegaStratum J k p) p (-p) =>
      midDir J k p ((γ : ℝ → Matrix ι ι ℝ) (1 / 2)) :=
  continuous_midDir.comp continuous_apply_half_omega

theorem isOpen_omegaNbhd : IsOpen (omegaNbhd J k p) :=
  isOpen_ne_fun ((continuous_midDir_half.matrix_conjTranspose.mul
    continuous_midDir_half).matrix_det) continuous_const

theorem continuousOn_polarDir_half :
    ContinuousOn (fun γ : PathSp (omegaStratum J k p) p (-p) =>
      polarDir J k p ((γ : ℝ → Matrix ι ι ℝ) (1 / 2))) (omegaNbhd J k p) := by
  refine continuous_midDir_half.continuousOn.mul ?_
  exact continuousOn_invSqrtM
    (continuous_midDir_half.matrix_conjTranspose.mul continuous_midDir_half).continuousOn
    (fun γ _ => isSelfAdjoint_conjTranspose_mul_self' _) fun γ hγ => spectrum_subset_Ioi hγ

include hJ hp in
open scoped Classical in
/-- **The retraction** `ω ↦ (t ↦ p exp(πt r(ω)))`, `r(ω)` the polar part of `midDir ω(1/2)`. -/
def omegaRetrPath (γ : PathSp (omegaStratum J k p) p (-p)) :
    PathSp (omegaStratum J k p) p (-p) :=
  if h : γ ∈ omegaNbhd J k p then
    omegaPath hJ hp ⟨polarDir J k p ((γ : ℝ → Matrix ι ι ℝ) (1 / 2)), polarDir_mem _ h⟩
  else γ

include hJ hp in
theorem continuousOn_omegaRetrPath : ContinuousOn (omegaRetrPath hJ hp) (omegaNbhd J k p) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have e : (omegaNbhd J k p).domRestrict (omegaRetrPath hJ hp) = fun γ : omegaNbhd J k p =>
      omegaPath hJ hp ⟨polarDir J k p ((γ.1 : ℝ → Matrix ι ι ℝ) (1 / 2)), polarDir_mem _ γ.2⟩ :=
    funext fun γ => by simp only [Set.domRestrict_apply, omegaRetrPath, dif_pos γ.2]
  rw [e]
  have hQ : Continuous fun γ : omegaNbhd J k p =>
      polarDir J k p ((γ.1 : ℝ → Matrix ι ι ℝ) (1 / 2)) :=
    continuousOn_iff_continuous_domRestrict.1 continuousOn_polarDir_half
  exact (continuous_omegaPath hJ hp).comp (hQ.subtype_mk _)

include hJ hp in
theorem omegaRetrPath_mem_minPaths {γ : PathSp (omegaStratum J k p) p (-p)}
    (hγ : γ ∈ omegaNbhd J k p) :
    omegaRetrPath hJ hp γ ∈ minPaths (omegaStratum J k p) p (-p) := by
  rw [omegaRetrPath, dif_pos hγ]
  exact omegaPath_mem_minPaths hJ hp _

include hJ hp in
/-- On `Ω^d`: `ω ∈ O`, and the retraction agrees with `ω` on `[0, 1]`. -/
theorem mem_omegaNbhd_and_eqOn {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p)
    {γ : PathSp (omegaStratum J k p) p (-p)}
    (hγ : γ ∈ minPaths (omegaStratum J k p) p (-p)) :
    γ ∈ omegaNbhd J k p ∧ EqOn (omegaRetrPath hJ hp γ) γ (Icc 0 1) := by
  obtain ⟨A, hA, heq⟩ := exists_minVelO_of_mem_minPaths hJ hp hA₀ hγ
  have hpo := omega_orth hp
  have hhalf : (γ : ℝ → Matrix ι ι ℝ) (1 / 2) = p * A := by
    rw [heq ⟨by norm_num, by norm_num⟩, omegaGeo_half hA.2]
  have hmem : γ ∈ omegaNbhd J k p := by
    change ((midDir J k p ((γ : ℝ → Matrix ι ι ℝ) (1 / 2)))ᴴ *
      midDir J k p ((γ : ℝ → Matrix ι ι ℝ) (1 / 2))).det ≠ 0
    rw [hhalf, midDir_mul hpo hA, conjTranspose_mul_self_of_minVelO hA, det_one]
    exact one_ne_zero
  refine ⟨hmem, fun t ht => ?_⟩
  rw [omegaRetrPath, dif_pos hmem, omegaPath_apply]
  simp only
  rw [hhalf, polarDir_mul hpo hA, heq ht]
  rfl

include hJ hp in
/-- **The neighbourhood retract of Theorem 22.1 for `Ω_k(n)`**: the space `Ω^d` of minimal
geodesics from `p` to `−p` is a retract of the open neighbourhood `Morse.omegaNbhd` in
`Ω(Ω_k(n); p, −p)` (Milnor's hypothesis "`Ω^d` is a topological manifold", here proved by an
explicit retraction: project `p⁻¹ω(1/2)` to `𝒯_p` and take its polar part). -/
theorem exists_retraction_minPaths_omega {A₀ : Matrix ι ι ℝ} (hA₀ : A₀ ∈ minVelO J k p) :
    ∃ O : Set (PathSp (omegaStratum J k p) p (-p)),
      IsOpen O ∧ minPaths _ p (-p) ⊆ O ∧
      ∃ ρ : PathSp (omegaStratum J k p) p (-p) → PathSp (omegaStratum J k p) p (-p),
        ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths _ p (-p)) ∧
        ∀ γ ∈ minPaths _ p (-p), ρ γ = γ := by
  classical
  set S := minPaths (omegaStratum J k p) p (-p)
  refine ⟨omegaNbhd J k p, isOpen_omegaNbhd, fun γ hγ => (mem_omegaNbhd_and_eqOn hJ hp hA₀ hγ).1,
    fun γ => if γ ∈ S then γ else omegaRetrPath hJ hp γ, ?_, fun γ hγ => ?_,
    fun γ hγ => if_pos hγ⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    refine PathSp.continuous_of_edist_eq_zero
      (continuousOn_iff_continuous_domRestrict.1 (continuousOn_omegaRetrPath hJ hp)) fun γ => ?_
    simp only [domRestrict_apply]
    split_ifs with h
    · rw [edist_comm]
      exact PathSp.edist_eq_zero_of_eqOn (mem_omegaNbhd_and_eqOn hJ hp hA₀ h).2
    · exact edist_self _
  · simp only
    split_ifs with h
    · exact h
    · exact omegaRetrPath_mem_minPaths hJ hp hγ

end Retraction

end Morse
