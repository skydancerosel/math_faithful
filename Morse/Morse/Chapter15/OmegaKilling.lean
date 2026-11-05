import Morse.Chapter15.OmegaMinimal
import Morse.Chapter9.IndexTheorem
import Morse.Chapter9.JacobiVariation

/-!
Milnor, *Morse Theory*, Theorems 15.1, 20.5 and Lemma 14.3, as used in §24 (pp. 135, 145–146);
Exposition/Chapter15.md, §6.

# Killing fields and lower bounds for the index in `Ω_k(n)`

## Milnor's text, paraphrased

(pp. 145–146) The conjugate points along `t ↦ J exp(πtA)` are governed by the eigenvalues of
`K_A(B) = −¼[A,[A,B]]` on `𝒯` (Theorem 20.5): an eigenvalue `e² ≥ 4` gives a conjugate point at
`t = 1/e ≤ 1/2`, so the index is at least the number of such eigenvalues.

## What is formalized

Instead of the curvature of `Ω_k(n)` and Theorem 20.5, the Jacobi fields are produced by
isometries (Milnor's argument for the sphere, p. 80):

* `Morse.isoAlg J k p`: the skew `X` commuting with `p` and the `J_α`; `exp(uX)` acts on `Ω_k(n)`
  by isometries fixing `p`.
* `Morse.isJacobiField_killing`: **the Killing field `t ↦ Xγ(t) − γ(t)X` is a Jacobi field along
  `γ(t) = p exp(tV)`** (Lemma 14.3 for the variation `u ↦ exp(uX)γexp(−uX)` through the geodesics
  `t ↦ p exp(t e^{uX}Ve^{−uX})`).  It vanishes at `t = 0`, and at `t = τ` when `X` commutes with
  `exp(τV)`.
* `Morse.finrank_le_conjMultiplicity`: for a space `𝒳 ⊆ isoAlg` of such `X` on which
  `X ↦ [X, V]` is injective, `γ(τ)` is conjugate with multiplicity `≥ dim 𝒳`.
* `Morse.sum_finrank_le_formIndex`: **the index of `γ` is `≥ Σ_{τ ∈ T} dim 𝒳_τ`** (Theorem 15.1).

## What Milnor leaves implicit

* Theorem 20.5 for `Ω_k(n)` needs its curvature (the Gauss equation, Lemma 2.2 (b) of the
  exposition) and the eigenvectors of `K_A`; for a lower bound only the eigenvectors are needed,
  and Milnor's eigenvector `B` is `[X, A]` for an `X ∈ isoAlg` (`X = CK_h` on `M_h`), so the
  corresponding Jacobi fields are Killing fields.
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

theorem sum_le_finsum_mem {m : ℝ → ℕ} {s : Set ℝ} (hfin : (s ∩ Function.support m).Finite)
    (T : Finset ℝ) (hT : ↑T ⊆ s) : ∑ τ ∈ T, m τ ≤ ∑ᶠ t ∈ s, m t := by
  classical
  rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum m hfin,
    ← Finset.sum_filter_ne_zero]
  refine Finset.sum_le_sum_of_subset fun τ hτ => ?_
  rw [Finset.mem_filter] at hτ
  rw [Set.Finite.mem_toFinset]
  exact ⟨hT hτ.1, hτ.2⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Killing fields along geodesics of `Ω_k(n)` -/

section Killing

variable {J : ℕ → Matrix ι ι ℝ} {k : ℕ} {p : Matrix ι ι ℝ}

variable (J k p) in
/-- **The isotropy algebra** of `p` in `Ω_k(n)`: skew `X` commuting with `p` and
`J_1, …, J_{k−1}`; `t ↦ exp(tX)` acts on `Ω_k(n)` by isometries fixing `±p`. -/
def isoAlg : Submodule ℝ (Matrix ι ι ℝ) where
  carrier := {X | Xᴴ = -X ∧ X * p = p * X ∧ ∀ α, 1 ≤ α → α < k → X * J α = J α * X}
  add_mem' := by
    rintro A B ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    exact ⟨by rw [conjTranspose_add, h1, h1', neg_add],
      by rw [add_mul, mul_add, h2, h2'],
      fun α ha hb => by rw [add_mul, mul_add, h3 α ha hb, h3' α ha hb]⟩
  zero_mem' := ⟨by simp, by simp, fun _ _ _ => by simp⟩
  smul_mem' := by
    rintro c A ⟨h1, h2, h3⟩
    exact ⟨by rw [conjTranspose_smul, star_trivial, h1, smul_neg],
      by rw [smul_mul_assoc, mul_smul_comm, h2],
      fun α ha hb => by rw [smul_mul_assoc, mul_smul_comm, h3 α ha hb]⟩

/-- The Killing field of `X` along `t ↦ p exp(tV)`: `t ↦ X γ(t) − γ(t) X`. -/
def killing (p V X : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  X * (p * NormedSpace.exp (t • V)) - p * NormedSpace.exp (t • V) * X

omit [DecidableEq ι] in
theorem hasDerivAt_conj_exp [DecidableEq ι] (M X : Matrix ι ι ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X) * M * NormedSpace.exp (u • -X))
      (X * M - M * X) 0 := by
  have h1 := ((hasDerivAt_exp_smul_const X (0 : ℝ)).mul_const M).mul
    (hasDerivAt_exp_smul_const (-X) (0 : ℝ))
  refine h1.congr_deriv ?_
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg]
  abel

theorem isoAlg_exp {X : Matrix ι ι ℝ} (hX : X ∈ isoAlg J k p) (u : ℝ) :
    (NormedSpace.exp (u • X))ᴴ * NormedSpace.exp (u • X) = 1 ∧
      NormedSpace.exp (u • X) * p = p * NormedSpace.exp (u • X) ∧
      ∀ α, 1 ≤ α → α < k → NormedSpace.exp (u • X) * J α = J α * NormedSpace.exp (u • X) := by
  obtain ⟨h1, h2, h3⟩ := hX
  refine ⟨exp_conjTranspose_mul_exp_of_skew (by rw [conjTranspose_smul, star_trivial, h1,
    smul_neg]), ((((show Commute X p from h2).smul_left u)).exp_left).eq, fun α ha hb =>
    ((((show Commute X (J α) from h3 α ha hb).smul_left u)).exp_left).eq⟩

theorem exp_smul_conjTranspose (X : Matrix ι ι ℝ) (hX : Xᴴ = -X) (u : ℝ) :
    (NormedSpace.exp (u • X))ᴴ = NormedSpace.exp (u • -X) := by
  rw [← Matrix.exp_conjTranspose, conjTranspose_smul, star_trivial, hX]

/-- **The Killing fields are Jacobi fields** (Milnor's argument of p. 80 for the sphere, here for
the isometries `x ↦ g x g⁻¹`, `g = exp(uX)`, `X ∈ isoAlg`, of `Ω_k(n)` fixing `p`): they move the
geodesic `t ↦ p exp(tV)` through the geodesics `t ↦ p exp(t gVg⁻¹)`, and Lemma 14.3 applies. -/
theorem isJacobiField_killing (hJ : IsAnticommFamily J k) (hp : p ∈ Omega J k)
    {V : Matrix ι ι ℝ} (hV : V ∈ tanAlg J k p) {X : Matrix ι ι ℝ} (hX : X ∈ isoAlg J k p) :
    IsJacobiField (isSliceSubmanifold_omegaStratum hJ p)
      (fun t => p * NormedSpace.exp (t • V)) (killing p V X) := by
  have hT := isTotGeo_omegaStratum hJ p
  have hpN := self_mem_omegaStratum hp
  set α : ℝ → ℝ → Matrix ι ι ℝ := fun u t =>
    NormedSpace.exp (u • X) * (p * NormedSpace.exp (t • V)) * NormedSpace.exp (u • -X) with hαdef
  -- each `α u` is the geodesic with initial direction `g V gᴴ`
  have hαu : ∀ u, α u = fun t => p * NormedSpace.exp (t • (NormedSpace.exp (u • X) * V *
      NormedSpace.exp (u • -X))) := fun u => by
    obtain ⟨hg, hgp, -⟩ := isoAlg_exp hX u
    have hgH := exp_smul_conjTranspose X hX.1 u
    funext t
    have hu : IsUnit (NormedSpace.exp (u • X)) :=
      ⟨⟨_, _, mul_conjTranspose_eq_one hg, hg⟩, rfl⟩
    have hinv : (NormedSpace.exp (u • X))⁻¹ = NormedSpace.exp (u • -X) := by
      rw [← hgH]; exact Matrix.inv_eq_left_inv hg
    have := Matrix.exp_conj (NormedSpace.exp (u • X)) (t • V) hu
    rw [hinv] at this
    simp only [hαdef]
    calc NormedSpace.exp (u • X) * (p * NormedSpace.exp (t • V)) * NormedSpace.exp (u • -X) =
          p * (NormedSpace.exp (u • X) * NormedSpace.exp (t • V) * NormedSpace.exp (u • -X)) := by
            rw [← Matrix.mul_assoc, hgp]; simp only [Matrix.mul_assoc]
      _ = p * NormedSpace.exp (NormedSpace.exp (u • X) * (t • V) * NormedSpace.exp (u • -X)) := by
            rw [this]
      _ = _ := by rw [Matrix.mul_smul, Matrix.smul_mul]
  have hVu : ∀ u, NormedSpace.exp (u • X) * V * NormedSpace.exp (u • -X) ∈ tanAlg J k p :=
    fun u => by
      have hX' : -X ∈ isoAlg J k p := (isoAlg J k p).neg_mem hX
      obtain ⟨hg, hgp, hgJ⟩ := isoAlg_exp hX' u
      have hgH := exp_smul_conjTranspose (-X) hX'.1 u
      rw [neg_neg] at hgH
      have := conj_mem_tanAlg hg hgJ hV
      rw [hgH] at this
      have hp' : NormedSpace.exp (u • X) * p * NormedSpace.exp (u • -X) = p := by
        obtain ⟨hg1, hgp1, -⟩ := isoAlg_exp hX u
        rw [hgp1, Matrix.mul_assoc, ← hgH, hg, Matrix.mul_one]
      rwa [hp'] at this
  have hgeo : ∀ u ∈ Ioo (-1 : ℝ) 1, IsGeodesicOn (isSliceSubmanifold_omegaStratum hJ p) (α u)
      (Ioo 0 1) := fun u _ => by
    rw [hαu u]
    exact (hT.isGeodesicOn_mul_exp_smul hpN (hVu u)).mono isOpen_Ioo (subset_univ _)
  have hmem : ∀ u ∈ Ioo (-1 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, α u t ∈ omegaStratum J k p :=
    fun u _ t _ => by
      rw [hαu u]
      exact hT.mul_exp_smul_mem hpN (hVu u) t
  have hcd : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => α q.1 q.2) (Ioo (-1) 1 ×ˢ Icc (0 : ℝ) 1) := by
    refine ContDiff.contDiffOn ?_
    simp only [hαdef]
    refine ((contDiff_exp_matrix.comp (contDiff_fst.smul contDiff_const)).mul
      (contDiff_const.mul (contDiff_exp_matrix.comp (contDiff_snd.smul contDiff_const)))).mul
      (contDiff_exp_matrix.comp (contDiff_fst.smul contDiff_const))
  have h := lemma_14_3 (hN := isSliceSubmanifold_omegaStratum hJ p) one_pos hcd hmem hgeo
  have e1 : α 0 = fun t => p * NormedSpace.exp (t • V) := by
    funext t; simp [hαdef]
  have e2 : (fun t => deriv (fun u => α u t) 0) = killing p V X := by
    funext t
    exact (hasDerivAt_conj_exp (p * NormedSpace.exp (t • V)) X).deriv
  rw [e1, e2] at h
  exact h

theorem hasDerivAt_killing (p V X : Matrix ι ι ℝ) (t : ℝ) :
    HasDerivAt (killing p V X) (X * (p * NormedSpace.exp (t • V) * V) -
      p * NormedSpace.exp (t • V) * V * X) t := by
  have h := hasDerivAt_mul_exp_smul p V t
  exact (h.const_mul X).sub (h.mul_const X)

theorem killing_zero {X : Matrix ι ι ℝ} (hX : X ∈ isoAlg J k p) (V : Matrix ι ι ℝ) :
    killing p V X 0 = 0 := by
  simp [killing, hX.2.1]

theorem killing_eq_zero {X V : Matrix ι ι ℝ} (hX : X ∈ isoAlg J k p) {τ : ℝ}
    (hc : X * NormedSpace.exp (τ • V) = NormedSpace.exp (τ • V) * X) : killing p V X τ = 0 := by
  simp only [killing]
  rw [← Matrix.mul_assoc, hX.2.1, Matrix.mul_assoc, hc, Matrix.mul_assoc, sub_self]

/-- A Killing field vanishing on `[0, 1]` comes from an `X` commuting with `V`. -/
theorem commute_of_killing_eqOn {X V : Matrix ι ι ℝ} (hX : X ∈ isoAlg J k p) (hpo : pᴴ * p = 1)
    (h0 : EqOn (killing p V X) 0 (Icc 0 1)) : X * V = V * X := by
  have hd := (hasDerivAt_killing p V X 0).hasDerivWithinAt (s := Icc 0 1)
  have hz : HasDerivWithinAt (killing p V X) 0 (Icc 0 1) 0 :=
    (hasDerivWithinAt_const (0 : ℝ) (Icc 0 1) (0 : Matrix ι ι ℝ)).congr h0
      (h0 ⟨le_rfl, zero_le_one⟩)
  have huniq := (uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩).eq_deriv _ hd hz
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at huniq
  rw [← Matrix.mul_assoc, hX.2.1, Matrix.mul_assoc, sub_eq_zero] at huniq
  have := congrArg (pᴴ * ·) huniq
  simpa only [← Matrix.mul_assoc, hpo, Matrix.one_mul] using this

/-- **The multiplicity of a conjugate point is at least the number of independent Killing
fields vanishing there** (Theorem 20.5 replaced by isometries): if `𝒳 ⊆ isoAlg` consists of `X`
commuting with `exp(τV)` and `X ↦ [X, V]` is injective on `𝒳`, then `γ(τ)` is conjugate to
`γ(0)` along `γ(t) = p exp(tV)` with multiplicity `≥ dim 𝒳`. -/
theorem finrank_le_conjMultiplicity (hJ : IsAnticommFamily J k) (hp : p ∈ Omega J k)
    {γ : ℝ → Matrix ι ι ℝ} {q : Matrix ι ι ℝ} (hγ : γ ∈ pathSpace (omegaStratum J k p) p q)
    (hgeo : IsUnbrokenGeodesic (isSliceSubmanifold_omegaStratum hJ p) γ) {V : Matrix ι ι ℝ}
    (hV : V ∈ tanAlg J k p) (heq : EqOn γ (fun t => p * NormedSpace.exp (t • V)) (Icc 0 1))
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) (𝒳 : Submodule ℝ (Matrix ι ι ℝ)) (h𝒳 : 𝒳 ≤ isoAlg J k p)
    (hcomm : ∀ X ∈ 𝒳, X * NormedSpace.exp (τ • V) = NormedSpace.exp (τ • V) * X)
    (hinj : ∀ X ∈ 𝒳, X * V = V * X → X = 0) :
    finrank ℝ 𝒳 ≤ conjMultiplicity (isSliceSubmanifold_omegaStratum hJ p) γ
      (hgeo.isSmoothCurveIn _ hγ) 0 τ := by
  set hN := isSliceSubmanifold_omegaStratum hJ p
  set hc := hgeo.isSmoothCurveIn hN hγ
  have hpo := omega_orth hp
  let Φ : 𝒳 →ₗ[ℝ] conjSpace hN γ hc 0 τ :=
    { toFun := fun X => ⟨fun t => killing p V X (projIcc (0 : ℝ) 1 zero_le_one t), by
        refine (mem_conjSpace hc).2 ⟨?_, ?_, ?_⟩
        · exact ((isJacobiField_killing hJ hp hV (h𝒳 X.2)).congr_curve heq.symm).comp_projIcc_mem hc
        · simp only [projIcc_of_mem _ (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc (0 : ℝ) 1)]
          exact killing_zero (h𝒳 X.2) V
        · simp only [projIcc_of_mem _ hτ]
          exact killing_eq_zero (h𝒳 X.2) (hcomm X X.2)⟩
      map_add' := fun X Y => by
        ext t : 2
        simp only [killing, Submodule.coe_add, Pi.add_apply]
        noncomm_ring
      map_smul' := fun c X => by
        ext t : 2
        simp only [killing, SetLike.val_smul, Pi.smul_apply, RingHom.id_apply,
          Matrix.smul_mul, Matrix.mul_smul, smul_sub] }
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro X hX
    have h0 : EqOn (killing p V X) 0 (Icc 0 1) := fun t ht => by
      have := congrFun (congrArg Subtype.val (LinearMap.mem_ker.1 hX)) t
      simpa [Φ, projIcc_of_mem _ ht] using this
    exact Subtype.ext (hinj X X.2 (commute_of_killing_eqOn (h𝒳 X.2) hpo h0))
  exact LinearMap.finrank_le_finrank_of_injective hΦ

/-- **The index is at least the number of independent Killing fields vanishing at interior
points** (Theorems 15.1 and 20.5 in the form needed for Milnor's lower bounds): for a finite set
`T ⊆ (0, 1)` and spaces `𝒳_τ` as in `Morse.finrank_le_conjMultiplicity`, the index of the
geodesic `γ = p exp(tV)` is at least `Σ_{τ ∈ T} dim 𝒳_τ`. -/
theorem sum_finrank_le_formIndex (hJ : IsAnticommFamily J k) (hp : p ∈ Omega J k)
    {γ : ℝ → Matrix ι ι ℝ} {q : Matrix ι ι ℝ} (hγ : γ ∈ pathSpace (omegaStratum J k p) p q)
    (hgeo : IsUnbrokenGeodesic (isSliceSubmanifold_omegaStratum hJ p) γ) {V : Matrix ι ι ℝ}
    (hV : V ∈ tanAlg J k p) (heq : EqOn γ (fun t => p * NormedSpace.exp (t • V)) (Icc 0 1))
    (T : Finset ℝ) (hT : ∀ τ ∈ T, τ ∈ Ioo (0 : ℝ) 1) (𝒳 : ℝ → Submodule ℝ (Matrix ι ι ℝ))
    (h𝒳 : ∀ τ ∈ T, 𝒳 τ ≤ isoAlg J k p)
    (hcomm : ∀ τ ∈ T, ∀ X ∈ 𝒳 τ, X * NormedSpace.exp (τ • V) = NormedSpace.exp (τ • V) * X)
    (hinj : ∀ τ ∈ T, ∀ X ∈ 𝒳 τ, X * V = V * X → X = 0) :
    ((∑ τ ∈ T, finrank ℝ (𝒳 τ) : ℕ) : ℕ∞) ≤
      formIndex (energyHessian (isSliceSubmanifold_omegaStratum hJ p) hγ) := by
  set hN := isSliceSubmanifold_omegaStratum hJ p
  set hc := hgeo.isSmoothCurveIn hN hγ
  obtain ⟨hfin, heq'⟩ := theorem_15_1 hN hγ hgeo
  rw [heq']
  have hsupp : (Ioo (0 : ℝ) 1 ∩ Function.support (conjMultiplicity hN γ hc 0)).Finite := by
    refine hfin.subset fun t ht => ⟨ht.1, (isConjugate_iff hc).2 ⟨⟨le_rfl, zero_le_one⟩,
      Ioo_subset_Icc_self ht.1, ht.1.1.ne, Nat.pos_of_ne_zero ht.2⟩⟩
  have h1 := sum_le_finsum_mem hsupp T (fun τ hτ => hT τ hτ)
  have h2 : ∑ τ ∈ T, finrank ℝ (𝒳 τ) ≤ ∑ τ ∈ T, conjMultiplicity hN γ hc 0 τ :=
    Finset.sum_le_sum fun τ hτ => finrank_le_conjMultiplicity hJ hp hγ hgeo hV heq
      (Ioo_subset_Icc_self (hT τ hτ)) (𝒳 τ) (h𝒳 τ hτ) (hcomm τ hτ) (hinj τ hτ)
  exact_mod_cast h2.trans h1

end Killing

end Morse
