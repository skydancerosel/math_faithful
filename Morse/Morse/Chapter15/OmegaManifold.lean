import Morse.Chapter15.TotallyGeodesic
import Morse.Chapter15.ComplexStructure

/-!
Milnor, *Morse Theory*, §24, Lemma 24.4 (i) (pp. 136–137); Exposition/Chapter15.md, §2.

# `Ω_k(n)` is a smooth totally geodesic submanifold

## Milnor's text, paraphrased

(p. 137) Let `B_ε` be a ball in which `exp` is a diffeomorphism.  *Assertion 1*: `J exp A` is a
complex structure iff `A` anticommutes with `J`.  *Assertion 2*: `J exp A` anticommutes with `J_α`
iff `A` commutes with `J_α`.  Hence near `J`, `Ω_k(n) = J exp(𝒯_J ∩ B_ε)`,
`𝒯_J = {A ∈ 𝔬(n) : AJ = −JA, AJ_α = J_αA (α < k)}`, a smooth submanifold, totally geodesic.

## What is formalized

* `Morse.exists_exp_injective`, `Morse.exists_log`: `exp` is injective on a ball, with a local
  inverse near `I` (Mathlib's inverse function theorem, for the Frobenius norm).
* `Morse.tanAlg J k x` is Milnor's `𝒯_x` (`= 𝔬(n)` for `k = 0`, `Ω_0(n) = O(n)`).
* **Assertions 1 and 2**: `Morse.mul_exp_mem_omega` (the "if" halves, all `A`) and
  `Morse.mem_tanAlg_of_mul_exp_mem` (the **"only if" halves for `‖A‖ < ε`**, by injectivity of
  `exp`: `exp(x⁻¹Ax) = exp(−A)`, `exp(J_αAJ_α⁻¹) = exp(A)`, `exp(Aᵀ) = exp(−A)`).
* `Morse.exists_local_log`: **near `x ∈ Ω_k(n)`, every point of `Ω_k(n)` is `x exp(C)` with
  `C ∈ 𝒯_x` small**; `Morse.finrank_tanAlg_mul_exp` (`x exp A = gᴴxg`, `g = exp(A/2)`, so
  `dim 𝒯` is constant along geodesics), `Morse.eventually_finrank_tanAlg` (locally constant).
* `Morse.omegaStratum J k p`: the points of `Ω_k(n)` where `dim 𝒯 = dim 𝒯_p`; open and closed in
  `Ω_k(n)` (`Morse.eventually_mem_omegaStratum`, `Morse.isClosed_omegaStratum`), compact.
* **Lemma 24.4 (i)**: `Morse.isSliceSubmanifold_omegaStratum` (a slice submanifold of `Mₙ(ℝ)`
  modelled on `𝒯_p`, parametrized near `x` by `(a, w) ↦ x(exp a + w)`, `a ∈ 𝒯_x`, `w ⊥ 𝒯_x`) and
  `Morse.isTotGeo_omegaStratum` (its geodesics are the `t ↦ x exp(tA)`, `A ∈ 𝒯_x`).

## What Milnor leaves implicit

* p. 137: the "only if" halves of Assertions 1 and 2 hold only for small `A`, and need `exp` to
  be injective near `0` together with the invariance of `B_ε` under `A ↦ −A`, `Aᵀ`, `gAg⁻¹`
  (Frobenius norm, `g` orthogonal).
* **The components of `Ω_k(n)` may have different dimensions** (e.g. `Ω_3(16r)` is a union of
  quaternionic Grassmannians of all dimensions), so `Ω_k(n)` is not a manifold modelled on a
  single space.  Theorem 22.1 only sees the paths from `J_k`, which stay in the stratum of
  `J_k`; the stratum is open and closed in `Ω_k(n)`, so it has the same homotopy groups at `J_k`
  (`Morse.nonempty_pi_stratum_equiv`).
-/

open Matrix Set Filter Topology Module
open scoped Morse.MatrixInner RealInnerProductSpace Manifold ContDiff

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The exponential near `0` -/

section ExpLocal

/-- `exp` has derivative `id` at `0` (in the Frobenius-normed algebra). -/
theorem exists_hasStrictFDerivAt_exp_zero :
    ∃ e : Matrix ι ι ℝ ≃L[ℝ] Matrix ι ι ℝ,
      HasStrictFDerivAt (NormedSpace.exp : Matrix ι ι ℝ → Matrix ι ι ℝ)
        (e : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ) 0 := by
  have := hasStrictFDerivAt_exp_zero_of_radius_pos (𝕂 := ℝ) (𝔸 := Matrix ι ι ℝ)
    (by rw [NormedSpace.expSeries_radius_eq_top]; exact ENNReal.zero_lt_top)
  exact ⟨ContinuousLinearEquiv.refl ℝ _, this.congr_fderiv (by ext; simp)⟩

/-- **`exp` is injective near `0`** (inverse function theorem). -/
theorem exists_exp_injective :
    ∃ ε > 0, ∀ C D : Matrix ι ι ℝ, ‖C‖ < ε → ‖D‖ < ε →
      NormedSpace.exp C = NormedSpace.exp D → C = D := by
  obtain ⟨e₀, hf⟩ := exists_hasStrictFDerivAt_exp_zero (ι := ι)
  set e := hf.toOpenPartialHomeomorph _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_source 0
    hf.mem_toOpenPartialHomeomorph_source
  refine ⟨ε, hε, fun C D hC hD hCD => e.injOn (hball ?_) (hball ?_) hCD⟩
  · simpa using hC
  · simpa using hD

/-- **A local logarithm near `I`**: `exp (L y) = y` for `y` near `I`, and `L y → 0`. -/
theorem exists_log :
    ∃ L : Matrix ι ι ℝ → Matrix ι ι ℝ, (∀ᶠ y in 𝓝 (1 : Matrix ι ι ℝ), NormedSpace.exp (L y) = y) ∧
      Tendsto L (𝓝 1) (𝓝 0) := by
  obtain ⟨e₀, hf⟩ := exists_hasStrictFDerivAt_exp_zero (ι := ι)
  have h1 := hf.eventually_right_inverse
  have h2 := hf.localInverse_tendsto
  rw [NormedSpace.exp_zero] at h1 h2
  exact ⟨_, h1, h2⟩

end ExpLocal

/-! ### Norms -/

theorem norm_conjTranspose_real (C : Matrix ι ι ℝ) : ‖Cᴴ‖ = ‖C‖ := by
  have h := inner_conjTranspose C C
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem norm_conj_orth {g : Matrix ι ι ℝ} (hg : gᴴ * g = 1) (C : Matrix ι ι ℝ) :
    ‖gᴴ * C * g‖ = ‖C‖ := by
  have hg' : gᴴᴴ * gᴴ = 1 := by
    rw [conjTranspose_conjTranspose]; exact mul_conjTranspose_eq_one hg
  have h1 : ‖gᴴ * C * g‖ = ‖gᴴ * C‖ := (mulRightIso g hg).norm_map (gᴴ * C)
  rw [h1]
  exact (mulLeftIso gᴴ hg').norm_map C

/-! ### `Ω_k(n)`: membership -/

section OmegaFacts

variable {J : ℕ → Matrix ι ι ℝ} {k : ℕ} {x : Matrix ι ι ℝ}

omit [Fintype ι] [DecidableEq ι] in
theorem conjTranspose_real (A : Matrix ι ι ℝ) : Aᴴ = Aᵀ := conjTranspose_eq_transpose_of_trivial A

theorem omega_subset_orthogonal (J : ℕ → Matrix ι ι ℝ) :
    ∀ k, Omega J k ⊆ (orthogonalGroup ι ℝ : Set (Matrix ι ι ℝ))
  | 0 => fun _ h => h
  | k + 1 => (omega_succ_subset J k).trans (omega_subset_orthogonal J k)

theorem omega_orth (hx : x ∈ Omega J k) : xᴴ * x = 1 := by
  have := omega_subset_orthogonal J k hx
  rwa [SetLike.mem_coe, mem_orthogonalGroup_iff', ← conjTranspose_real] at this

theorem omega_sq (hk : k ≠ 0) (hx : x ∈ Omega J k) : x * x = -1 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact hx.1.2

theorem omega_anti (hx : x ∈ Omega J k) {α : ℕ} (h1 : 1 ≤ α) (h2 : α < k) :
    J α * x = -(x * J α) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact hx.2 α h1 (by omega)

theorem mem_omega_of (hk : k ≠ 0) (horth : xᴴ * x = 1) (hsq : x * x = -1)
    (hanti : ∀ α, 1 ≤ α → α < k → J α * x = -(x * J α)) : x ∈ Omega J k := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine ⟨⟨?_, hsq⟩, fun α h1 h2 => hanti α h1 (by omega)⟩
  rw [mem_orthogonalGroup_iff', ← conjTranspose_real]
  exact horth

theorem mem_omega_zero (horth : xᴴ * x = 1) : x ∈ Omega J 0 := by
  change x ∈ (orthogonalGroup ι ℝ : Set (Matrix ι ι ℝ))
  rw [SetLike.mem_coe, mem_orthogonalGroup_iff', ← conjTranspose_real]
  exact horth

theorem IsAnticommFamily.orth {k : ℕ} (hJ : IsAnticommFamily J k) {α : ℕ} (h1 : 1 ≤ α)
    (h2 : α ≤ k) : (J α)ᴴ * J α = 1 := by
  have := (hJ.cs α h1 h2).1
  rwa [mem_orthogonalGroup_iff', ← conjTranspose_real] at this

end OmegaFacts

/-! ### Milnor's `𝒯_J` -/

/-- **Milnor's `𝒯_J`** (Lemma 24.4, p. 137): the skew `A` anticommuting with `J` and commuting with
`J_1, …, J_{k−1}`, so that `J exp A ∈ Ω_k(n)`.  For `k = 0` (`Ω_0(n) = O(n)`) it is `𝔬(n)`. -/
def tanAlg (J : ℕ → Matrix ι ι ℝ) (k : ℕ) (x : Matrix ι ι ℝ) : Submodule ℝ (Matrix ι ι ℝ) where
  carrier := {A | Aᴴ = -A ∧ (k ≠ 0 → A * x = -(x * A)) ∧ ∀ α, 1 ≤ α → α < k → A * J α = J α * A}
  add_mem' := by
    rintro A B ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩
    exact ⟨by rw [conjTranspose_add, h1, h1', neg_add],
      fun hk => by rw [add_mul, mul_add, h2 hk, h2' hk, neg_add],
      fun α ha hb => by rw [add_mul, mul_add, h3 α ha hb, h3' α ha hb]⟩
  zero_mem' := ⟨by simp, fun _ => by simp, fun _ _ _ => by simp⟩
  smul_mem' := by
    rintro c A ⟨h1, h2, h3⟩
    exact ⟨by rw [conjTranspose_smul, star_trivial, h1, smul_neg],
      fun hk => by rw [smul_mul_assoc, mul_smul_comm, h2 hk, smul_neg],
      fun α ha hb => by rw [smul_mul_assoc, mul_smul_comm, h3 α ha hb]⟩

theorem mem_tanAlg {J : ℕ → Matrix ι ι ℝ} {k : ℕ} {x A : Matrix ι ι ℝ} :
    A ∈ tanAlg J k x ↔
      Aᴴ = -A ∧ (k ≠ 0 → A * x = -(x * A)) ∧ ∀ α, 1 ≤ α → α < k → A * J α = J α * A :=
  Iff.rfl

section Assertions

variable {J : ℕ → Matrix ι ι ℝ} {k : ℕ} {x : Matrix ι ι ℝ}

/-- **Assertions 1 and 2**, "if" halves (Milnor p. 137): `x exp A ∈ Ω_k(n)` for `A ∈ 𝒯_x`. -/
theorem mul_exp_mem_omega (hx : x ∈ Omega J k) {A : Matrix ι ι ℝ} (hA : A ∈ tanAlg J k x) :
    x * NormedSpace.exp A ∈ Omega J k := by
  obtain ⟨h1, h2, h3⟩ := hA
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine mem_omega_zero ?_
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc xᴴ, omega_orth hx,
      Matrix.one_mul]
    exact exp_conjTranspose_mul_exp_of_skew h1
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨isComplexStructure_mul_exp hx.1 (by rw [← conjTranspose_real, h1])
      (h2 (by omega)), fun α hα hαk => ?_⟩
    exact anticomm_mul_exp (hx.2 α hα hαk) (h3 α hα (by omega))

/-- `A ∈ 𝒯_{x exp A}`: the velocity of `t ↦ x exp(tA)` stays in `𝒯`. -/
theorem mem_tanAlg_mul_exp {A : Matrix ι ι ℝ} (hA : A ∈ tanAlg J k x) :
    A ∈ tanAlg J k (x * NormedSpace.exp A) := by
  obtain ⟨h1, h2, h3⟩ := hA
  refine ⟨h1, fun hk => ?_, h3⟩
  have hc : A * NormedSpace.exp A = NormedSpace.exp A * A := by
    simpa using (exp_smul_mul_self A 1).symm
  rw [← Matrix.mul_assoc, h2 hk, Matrix.neg_mul, Matrix.mul_assoc, hc, Matrix.mul_assoc]

theorem exp_conj_orth {g : Matrix ι ι ℝ} (hg : gᴴ * g = 1) (C : Matrix ι ι ℝ) :
    NormedSpace.exp (gᴴ * C * g) = gᴴ * NormedSpace.exp C * g := by
  have hinv : g⁻¹ = gᴴ := Matrix.inv_eq_left_inv hg
  have hu : IsUnit g := ⟨⟨g, gᴴ, mul_conjTranspose_eq_one hg, hg⟩, rfl⟩
  rw [← hinv]
  exact Matrix.exp_conj' g C hu

/-- **Assertions 1 and 2**, "only if" halves (Milnor p. 137, for `A` small): if `x ∈ Ω_k(n)` and
`x exp C ∈ Ω_k(n)` with `‖C‖ < ε`, `ε` a radius of injectivity of `exp`, then `C ∈ 𝒯_x`. -/
theorem mem_tanAlg_of_mul_exp_mem (hJ : IsAnticommFamily J k) {ε : ℝ}
    (hε : ∀ C D : Matrix ι ι ℝ, ‖C‖ < ε → ‖D‖ < ε →
      NormedSpace.exp C = NormedSpace.exp D → C = D)
    (hx : x ∈ Omega J k) {C : Matrix ι ι ℝ} (hC : ‖C‖ < ε)
    (hy : x * NormedSpace.exp C ∈ Omega J k) : C ∈ tanAlg J k x := by
  have hxo := omega_orth hx
  have hyo := omega_orth hy
  have hxo' := mul_conjTranspose_eq_one hxo
  have hneg : ‖-C‖ < ε := by rwa [norm_neg]
  have hE : (NormedSpace.exp C)ᴴ * NormedSpace.exp C = 1 := by
    have e : (x * NormedSpace.exp C)ᴴ * (x * NormedSpace.exp C) =
        (NormedSpace.exp C)ᴴ * (xᴴ * x) * NormedSpace.exp C := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [hxo, Matrix.mul_one] at e
    rw [← e]; exact hyo
  have hEneg : (NormedSpace.exp C)ᴴ = NormedSpace.exp (-C) := by
    calc (NormedSpace.exp C)ᴴ = (NormedSpace.exp C)ᴴ * (NormedSpace.exp C * NormedSpace.exp (-C)) := by
          rw [exp_mul_exp_neg, Matrix.mul_one]
      _ = NormedSpace.exp (-C) := by rw [← Matrix.mul_assoc, hE, Matrix.one_mul]
  refine ⟨?_, fun hk => ?_, fun α h1 h2 => ?_⟩
  · refine hε _ _ (by rwa [norm_conjTranspose_real]) hneg ?_
    rw [Matrix.exp_conjTranspose, hEneg]
  · have hx2 := omega_sq hk hx
    have hy2 := omega_sq hk hy
    have hxH : xᴴ = -x := by
      calc xᴴ = xᴴ * (-(x * x)) := by rw [hx2, neg_neg, Matrix.mul_one]
        _ = -x := by rw [Matrix.mul_neg, ← Matrix.mul_assoc, hxo, Matrix.one_mul]
    have key : NormedSpace.exp (xᴴ * C * x) * NormedSpace.exp C = 1 := by
      rw [exp_conj_orth hxo]
      have : x * NormedSpace.exp C * (x * NormedSpace.exp C) =
          -(xᴴ * NormedSpace.exp C * x * NormedSpace.exp C) := by
        rw [hxH]; simp only [Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
      rw [← neg_inj, ← this, hy2]
    have h3 : NormedSpace.exp (xᴴ * C * x) = NormedSpace.exp (-C) := by
      calc NormedSpace.exp (xᴴ * C * x) =
            NormedSpace.exp (xᴴ * C * x) * (NormedSpace.exp C * NormedSpace.exp (-C)) := by
              rw [exp_mul_exp_neg, Matrix.mul_one]
        _ = NormedSpace.exp (-C) := by rw [← Matrix.mul_assoc, key, Matrix.one_mul]
    have h4 := hε _ _ (by rwa [norm_conj_orth hxo]) hneg h3
    calc C * x = x * (xᴴ * C * x) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hxo', Matrix.one_mul]
      _ = -(x * C) := by rw [h4, Matrix.mul_neg]
  · have ha := omega_anti hx h1 h2
    have hb := omega_anti hy h1 h2
    have hJo := hJ.orth h1 (by omega)
    have hJo' := mul_conjTranspose_eq_one hJo
    have hc : J α * NormedSpace.exp C = NormedSpace.exp C * J α := by
      have e : x * (J α * NormedSpace.exp C) = x * (NormedSpace.exp C * J α) := by
        have ha' : x * J α = -(J α * x) := by rw [ha, neg_neg]
        calc x * (J α * NormedSpace.exp C) = -(J α * (x * NormedSpace.exp C)) := by
              rw [← Matrix.mul_assoc, ha', Matrix.neg_mul, Matrix.mul_assoc]
          _ = x * (NormedSpace.exp C * J α) := by rw [hb, neg_neg, Matrix.mul_assoc]
      have := congrArg (xᴴ * ·) e
      simpa only [← Matrix.mul_assoc, hxo, Matrix.one_mul] using this
    have hJH : ((J α)ᴴ)ᴴ * (J α)ᴴ = 1 := by rw [conjTranspose_conjTranspose]; exact hJo'
    have h3 : NormedSpace.exp (J α * C * (J α)ᴴ) = NormedSpace.exp C := by
      have := exp_conj_orth hJH C
      rw [conjTranspose_conjTranspose] at this
      rw [this, hc, Matrix.mul_assoc, hJo', Matrix.mul_one]
    have h4 := hε _ _ (by
      have := norm_conj_orth hJH C
      rw [conjTranspose_conjTranspose] at this
      rwa [this]) hC h3
    calc C * J α = J α * C * (J α)ᴴ * J α := by rw [h4]
      _ = J α * C := by rw [Matrix.mul_assoc, hJo, Matrix.mul_one]

omit [Fintype ι] [DecidableEq ι] in
theorem orth_conjTranspose [Fintype ι] [DecidableEq ι] {g : Matrix ι ι ℝ} (hg : gᴴ * g = 1) :
    gᴴᴴ * gᴴ = 1 := by
  rw [conjTranspose_conjTranspose]; exact mul_conjTranspose_eq_one hg

/-- Conjugation `B ↦ gᴴBg` by an orthogonal `g`, as a linear isometry. -/
def conjIso (g : Matrix ι ι ℝ) (hg : gᴴ * g = 1) : Matrix ι ι ℝ ≃ₗᵢ[ℝ] Matrix ι ι ℝ :=
  (mulRightIso g hg).trans (mulLeftIso gᴴ (orth_conjTranspose hg))

@[simp] theorem conjIso_apply (g : Matrix ι ι ℝ) (hg : gᴴ * g = 1) (B : Matrix ι ι ℝ) :
    conjIso g hg B = gᴴ * B * g := by
  simp [conjIso, Matrix.mul_assoc]

/-- Conjugation by an orthogonal `g` commuting with `J_1, …, J_{k−1}` carries `𝒯_x` into
`𝒯_{gᴴxg}`. -/
theorem conj_mem_tanAlg {g : Matrix ι ι ℝ} (hg : gᴴ * g = 1)
    (hgJ : ∀ α, 1 ≤ α → α < k → g * J α = J α * g) {B : Matrix ι ι ℝ}
    (hB : B ∈ tanAlg J k x) : gᴴ * B * g ∈ tanAlg J k (gᴴ * x * g) := by
  obtain ⟨h1, h2, h3⟩ := hB
  have hg' := mul_conjTranspose_eq_one hg
  refine ⟨by rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, h1,
      Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc], fun hk => ?_, fun α ha hb => ?_⟩
  · calc gᴴ * B * g * (gᴴ * x * g) = gᴴ * (B * x) * g := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc g, hg', Matrix.one_mul]
      _ = -(gᴴ * x * g * (gᴴ * B * g)) := by
          rw [h2 hk]; simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc g gᴴ, hg', Matrix.one_mul]
  · have hc := hgJ α ha hb
    have hc' : gᴴ * J α = J α * gᴴ := by
      calc gᴴ * J α = gᴴ * J α * (g * gᴴ) := by rw [hg', Matrix.mul_one]
        _ = gᴴ * (g * J α) * gᴴ := by rw [hc]; simp only [Matrix.mul_assoc]
        _ = J α * gᴴ := by rw [← Matrix.mul_assoc, hg, Matrix.one_mul]
    calc gᴴ * B * g * J α = gᴴ * (B * J α) * g := by
          simp only [Matrix.mul_assoc]; rw [hc]
      _ = J α * (gᴴ * B * g) := by
          rw [h3 α ha hb, ← Matrix.mul_assoc, hc']; simp only [Matrix.mul_assoc]

theorem finrank_tanAlg_conj_le {g : Matrix ι ι ℝ} (hg : gᴴ * g = 1)
    (hgJ : ∀ α, 1 ≤ α → α < k → g * J α = J α * g) :
    finrank ℝ (tanAlg J k x) ≤ finrank ℝ (tanAlg J k (gᴴ * x * g)) := by
  rw [← LinearEquiv.finrank_map_eq (conjIso g hg).toLinearEquiv]
  refine Submodule.finrank_mono ?_
  rintro _ ⟨B, hB, rfl⟩
  change conjIso g hg B ∈ _
  rw [conjIso_apply]
  exact conj_mem_tanAlg hg hgJ hB

/-- `dim 𝒯_{gᴴxg} = dim 𝒯_x`. -/
theorem finrank_tanAlg_conj {g : Matrix ι ι ℝ} (hg : gᴴ * g = 1)
    (hgJ : ∀ α, 1 ≤ α → α < k → g * J α = J α * g) :
    finrank ℝ (tanAlg J k (gᴴ * x * g)) = finrank ℝ (tanAlg J k x) := by
  refine le_antisymm ?_ (finrank_tanAlg_conj_le hg hgJ)
  have hg' : gᴴᴴ * gᴴ = 1 := by
    rw [conjTranspose_conjTranspose]; exact mul_conjTranspose_eq_one hg
  have hgJ' : ∀ α, 1 ≤ α → α < k → gᴴ * J α = J α * gᴴ := fun α ha hb => by
    have hc := hgJ α ha hb
    calc gᴴ * J α = gᴴ * J α * (g * gᴴ) := by rw [mul_conjTranspose_eq_one hg, Matrix.mul_one]
      _ = gᴴ * (g * J α) * gᴴ := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = J α * gᴴ := by rw [← Matrix.mul_assoc, hg, Matrix.one_mul]
  have := finrank_tanAlg_conj_le (x := gᴴ * x * g) hg' hgJ'
  have e : g * (gᴴ * x * g) * gᴴ = x := by
    simp only [← Matrix.mul_assoc, mul_conjTranspose_eq_one hg, Matrix.one_mul]
    rw [Matrix.mul_assoc, mul_conjTranspose_eq_one hg, Matrix.mul_one]
  rwa [conjTranspose_conjTranspose, e] at this

theorem tanAlg_zero (J : ℕ → Matrix ι ι ℝ) (x y : Matrix ι ι ℝ) :
    tanAlg J 0 x = tanAlg J 0 y := by
  ext A
  simp only [mem_tanAlg, ne_eq, not_true_eq_false, false_imp_iff, true_and]

/-- **The dimension of `𝒯` is constant along the geodesics**: `dim 𝒯_{x exp A} = dim 𝒯_x` for
`A ∈ 𝒯_x` (`x exp A = gᴴxg` with `g = exp(A/2)`). -/
theorem finrank_tanAlg_mul_exp {A : Matrix ι ι ℝ} (hA : A ∈ tanAlg J k x) :
    finrank ℝ (tanAlg J k (x * NormedSpace.exp A)) = finrank ℝ (tanAlg J k x) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [tanAlg_zero J _ x]
  obtain ⟨h1, h2, h3⟩ := hA
  set g := NormedSpace.exp ((1 / 2 : ℝ) • A) with hgdef
  have hA2 : ((1 / 2 : ℝ) • A)ᴴ = -((1 / 2 : ℝ) • A) := by
    rw [conjTranspose_smul, star_trivial, h1, smul_neg]
  have hg : gᴴ * g = 1 := exp_conjTranspose_mul_exp_of_skew hA2
  have hgJ : ∀ α, 1 ≤ α → α < k → g * J α = J α * g := fun α ha hb =>
    (((show Commute A (J α) from h3 α ha hb).smul_left (1 / 2 : ℝ)).exp_left).eq
  have hgx : gᴴ * x * g = x * NormedSpace.exp A := by
    have hAx : (1 / 2 : ℝ) • A * x = -(x * ((1 / 2 : ℝ) • A)) := by
      rw [smul_mul_assoc, h2 hk.ne', mul_smul_comm, smul_neg]
    have e1 := mul_exp_eq_exp_neg_mul hAx
    have hgH : gᴴ = NormedSpace.exp (-((1 / 2 : ℝ) • A)) := by
      rw [hgdef, ← Matrix.exp_conjTranspose, hA2]
    rw [hgH, ← e1, Matrix.mul_assoc, hgdef, exp_smul_mul_exp_smul]
    norm_num
  rw [← hgx, finrank_tanAlg_conj hg hgJ]

end Assertions

/-! ### Lemma 24.4 (i): the local structure of `Ω_k(n)` -/

section Local

variable {J : ℕ → Matrix ι ι ℝ} {k : ℕ}

/-- **Near `x ∈ Ω_k(n)`, `Ω_k(n) = x exp(𝒯_x)`** (Milnor p. 137): there is `L`, continuous at
`x` with `L x → 0`, such that every `y ∈ Ω_k(n)` near `x` is `x exp(L y)` with `L y ∈ 𝒯_x`. -/
theorem exists_local_log (hJ : IsAnticommFamily J k) {x : Matrix ι ι ℝ} (hx : x ∈ Omega J k) :
    ∃ L : Matrix ι ι ℝ → Matrix ι ι ℝ, Tendsto L (𝓝 x) (𝓝 0) ∧
      ∀ᶠ y in 𝓝 x, y ∈ Omega J k → L y ∈ tanAlg J k x ∧ x * NormedSpace.exp (L y) = y := by
  obtain ⟨ε, hε, hinj⟩ := exists_exp_injective (ι := ι)
  obtain ⟨lg, hlg1, hlg2⟩ := exists_log (ι := ι)
  have hxo := omega_orth hx
  have ht : Tendsto (fun y => xᴴ * y) (𝓝 x) (𝓝 1) := by
    have : Continuous fun y : Matrix ι ι ℝ => xᴴ * y := continuous_const.mul continuous_id
    have h := this.tendsto x
    rwa [hxo] at h
  refine ⟨fun y => lg (xᴴ * y), hlg2.comp ht, ?_⟩
  have h1 := ht.eventually hlg1
  have h2 := (hlg2.comp ht).eventually (Metric.ball_mem_nhds (0 : Matrix ι ι ℝ) hε)
  filter_upwards [h1, h2] with y hy1 hy2 hy
  have hxy : x * NormedSpace.exp (lg (xᴴ * y)) = y := by
    rw [hy1, ← Matrix.mul_assoc, mul_conjTranspose_eq_one hxo, Matrix.one_mul]
  have hnorm : ‖lg (xᴴ * y)‖ < ε := by simpa using hy2
  refine ⟨mem_tanAlg_of_mul_exp_mem hJ hinj hx hnorm (by rw [hxy]; exact hy), hxy⟩

/-- **The dimension of `𝒯` is locally constant on `Ω_k(n)`.** -/
theorem eventually_finrank_tanAlg (hJ : IsAnticommFamily J k) {x : Matrix ι ι ℝ}
    (hx : x ∈ Omega J k) :
    ∀ᶠ y in 𝓝 x, y ∈ Omega J k → finrank ℝ (tanAlg J k y) = finrank ℝ (tanAlg J k x) := by
  obtain ⟨L, -, hL⟩ := exists_local_log hJ hx
  filter_upwards [hL] with y hy hyΩ
  obtain ⟨hmem, hxy⟩ := hy hyΩ
  rw [← hxy, finrank_tanAlg_mul_exp hmem]

variable (J k) in
/-- **The stratum of `Ω_k(n)` through `p`**: the points of `Ω_k(n)` where `𝒯` has the dimension
of `𝒯_p`.  It is open and closed in `Ω_k(n)` (`Morse.isClosed_omegaStratum`,
`Morse.eventually_mem_omegaStratum`), so it contains the component of `p`; Milnor's "the
components of `Ω_k(n)` may have different dimensions" (p. 139) is why it is needed. -/
def omegaStratum (p : Matrix ι ι ℝ) : Set (Matrix ι ι ℝ) :=
  {x | x ∈ Omega J k ∧ finrank ℝ (tanAlg J k x) = finrank ℝ (tanAlg J k p)}

theorem omegaStratum_subset (p : Matrix ι ι ℝ) : omegaStratum J k p ⊆ Omega J k :=
  fun _ h => h.1

theorem self_mem_omegaStratum {p : Matrix ι ι ℝ} (hp : p ∈ Omega J k) :
    p ∈ omegaStratum J k p := ⟨hp, rfl⟩

/-- The stratum is open in `Ω_k(n)`. -/
theorem eventually_mem_omegaStratum (hJ : IsAnticommFamily J k) {p x : Matrix ι ι ℝ}
    (hx : x ∈ omegaStratum J k p) : ∀ᶠ y in 𝓝 x, y ∈ Omega J k → y ∈ omegaStratum J k p := by
  filter_upwards [eventually_finrank_tanAlg hJ hx.1] with y hy hyΩ
  exact ⟨hyΩ, (hy hyΩ).trans hx.2⟩

/-- The stratum is closed. -/
theorem isClosed_omegaStratum (hJ : IsAnticommFamily J k) (p : Matrix ι ι ℝ) :
    IsClosed (omegaStratum J k p) := by
  refine isClosed_of_closure_subset fun y hy => ?_
  have hyΩ : y ∈ Omega J k :=
    closure_minimal (omegaStratum_subset p) (isClosed_omega J k) hy
  have h := eventually_finrank_tanAlg hJ hyΩ
  obtain ⟨z, hz, hzS⟩ := mem_closure_iff_nhds.1 hy _ h
  exact ⟨hyΩ, ((hz hzS.1).symm.trans hzS.2)⟩

theorem isCompact_omegaStratum (hJ : IsAnticommFamily J k) (p : Matrix ι ι ℝ) :
    IsCompact (omegaStratum J k p) :=
  (isCompact_omega J k).of_isClosed_subset (isClosed_omegaStratum hJ p) (omegaStratum_subset p)

/-- **Lemma 24.4 (i)** (Milnor p. 137): the stratum of `Ω_k(n)` through `p` is a smooth
submanifold of `Mₙ(ℝ)`, modelled on `𝒯_p`.  Near `x` it is parametrized by
`(a, w) ↦ x (exp(a) + w)`, `a ∈ 𝒯_x`, `w ⊥ 𝒯_x`: the points with `w = 0` are in `Ω_k(n)`
(Assertions 1, 2), and every point of `Ω_k(n)` near `x` is `x exp(C)` with `C ∈ 𝒯_x` small
(`Morse.exists_local_log`). -/
theorem isSliceSubmanifold_omegaStratum (hJ : IsAnticommFamily J k) (p : Matrix ι ι ℝ) :
    Milnor.IsSliceSubmanifold 𝓘(ℝ, Matrix ι ι ℝ) (tanAlg J k p) (tanAlg J k p)ᗮ
      (omegaStratum J k p) := by
  refine isSliceSubmanifold_of_param fun x hx => ?_
  set K := tanAlg J k x with hKdef
  have hxo := omega_orth hx.1
  have hK : finrank ℝ (tanAlg J k p) = finrank ℝ K := hx.2.symm
  have hKo : finrank ℝ (tanAlg J k p)ᗮ = finrank ℝ Kᗮ := by
    have h1 := Submodule.finrank_add_finrank_orthogonal (tanAlg J k p)
    have h2 := Submodule.finrank_add_finrank_orthogonal K
    omega
  set Lz : tanAlg J k p ≃L[ℝ] K := ContinuousLinearEquiv.ofFinrankEq hK
  set Lw : (tanAlg J k p)ᗮ ≃L[ℝ] Kᗮ := ContinuousLinearEquiv.ofFinrankEq hKo
  set Ψ : tanAlg J k p × (tanAlg J k p)ᗮ → Matrix ι ι ℝ := fun q =>
    x * (NormedSpace.exp ((Lz q.1 : K) : Matrix ι ι ℝ) + ((Lw q.2 : Kᗮ) : Matrix ι ι ℝ))
    with hΨdef
  set f₁ : tanAlg J k p × (tanAlg J k p)ᗮ → Matrix ι ι ℝ := fun q => ((Lz q.1 : K) : Matrix ι ι ℝ)
  set f₂ : tanAlg J k p × (tanAlg J k p)ᗮ → Matrix ι ι ℝ := fun q => ((Lw q.2 : Kᗮ) : Matrix ι ι ℝ)
  set F₁ : tanAlg J k p × (tanAlg J k p)ᗮ →L[ℝ] Matrix ι ι ℝ :=
    (K.subtypeL.comp (Lz : _ →L[ℝ] K)).comp (ContinuousLinearMap.fst ℝ _ _)
  set F₂ : tanAlg J k p × (tanAlg J k p)ᗮ →L[ℝ] Matrix ι ι ℝ :=
    (Kᗮ.subtypeL.comp (Lw : _ →L[ℝ] Kᗮ)).comp (ContinuousLinearMap.snd ℝ _ _)
  have hf₁ : f₁ = F₁ := rfl
  have hf₂ : f₂ = F₂ := rfl
  have hΨc : ContDiff ℝ ∞ Ψ := by
    refine contDiff_const.mul (ContDiff.add ?_ ?_)
    · exact contDiff_exp_matrix.comp F₁.contDiff
    · exact F₂.contDiff
  have hΨ0 : Ψ 0 = x := by simp [hΨdef]
  -- the derivative at `0`
  have hcompl : IsCompl K Kᗮ := Submodule.isCompl_orthogonal K
  set e : (tanAlg J k p × (tanAlg J k p)ᗮ) ≃L[ℝ] Matrix ι ι ℝ :=
    ((Lz.prodCongr Lw).trans
      (Submodule.prodEquivOfIsCompl K Kᗮ hcompl).toContinuousLinearEquiv).trans
      (mulLeftIso x hxo).toContinuousLinearEquiv with hedef
  have he : ∀ q, e q = x * (((Lz q.1 : K) : Matrix ι ι ℝ) + ((Lw q.2 : Kᗮ) : Matrix ι ι ℝ)) :=
    fun q => rfl
  have hexp : HasFDerivAt (NormedSpace.exp : Matrix ι ι ℝ → Matrix ι ι ℝ)
      (ContinuousLinearMap.id ℝ (Matrix ι ι ℝ)) (f₁ 0) := by
    have := (hasStrictFDerivAt_exp_zero_of_radius_pos (𝕂 := ℝ) (𝔸 := Matrix ι ι ℝ)
      (by rw [NormedSpace.expSeries_radius_eq_top]; exact ENNReal.zero_lt_top)).hasFDerivAt
    have h0 : f₁ 0 = 0 := by simp [f₁]
    rw [h0]
    exact this.congr_fderiv (by ext; simp)
  refine ⟨Ψ, hΨc, hΨ0, ⟨e, ?_⟩, ?_⟩
  · have h1 := hexp.comp (0 : tanAlg J k p × (tanAlg J k p)ᗮ) F₁.hasFDerivAt
    have h3 := ((mulLeftIso x hxo).toContinuousLinearEquiv : Matrix ι ι ℝ →L[ℝ]
      Matrix ι ι ℝ).hasFDerivAt.comp (0 : tanAlg J k p × (tanAlg J k p)ᗮ)
      (h1.add F₂.hasFDerivAt)
    have hEq : (((mulLeftIso x hxo).toContinuousLinearEquiv : Matrix ι ι ℝ →L[ℝ]
      Matrix ι ι ℝ).comp ((ContinuousLinearMap.id ℝ (Matrix ι ι ℝ)).comp F₁ + F₂)) =
        (e : _ →L[ℝ] Matrix ι ι ℝ) := by
      refine ContinuousLinearMap.ext fun q => ?_
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe, he, _root_.add_apply]
      rfl
    have h4 := h3.congr_fderiv hEq
    exact h4.congr_of_eventuallyEq (Eventually.of_forall fun q => rfl)
  refine ⟨?_, ?_⟩
  · refine Eventually.of_forall fun q hq => ?_
    have hq' : Ψ q = x * NormedSpace.exp ((Lz q.1 : K) : Matrix ι ι ℝ) := by
      simp [hΨdef, hq]
    rw [hq']
    exact ⟨mul_exp_mem_omega hx.1 (Lz q.1).2,
      (finrank_tanAlg_mul_exp (Lz q.1).2).trans hx.2⟩
  · obtain ⟨L, hLt, hLev⟩ := exists_local_log hJ hx.1
    set P := K.starProjection
    set g : tanAlg J k p × (tanAlg J k p)ᗮ → tanAlg J k p := fun q =>
      Lz.symm ⟨P (L (Ψ q)), K.starProjection_apply_mem _⟩
    have hΨt : Tendsto Ψ (𝓝 0) (𝓝 x) := by
      have := hΨc.continuous.tendsto 0
      rwa [hΨ0] at this
    refine ⟨g, ?_, ?_⟩
    · have h1 : Tendsto (fun q => (⟨P (L (Ψ q)), K.starProjection_apply_mem _⟩ : K)) (𝓝 0)
          (𝓝 0) := by
        rw [tendsto_subtype_rng]
        have := (P.continuous.tendsto 0).comp (hLt.comp hΨt)
        rw [map_zero] at this
        exact this
      have := (Lz.symm.continuous.tendsto 0).comp h1
      rw [map_zero] at this
      exact this
    · filter_upwards [hΨt.eventually hLev] with q hq hqS
      obtain ⟨hmem, hxq⟩ := hq hqS.1
      have hP : P (L (Ψ q)) = L (Ψ q) := Submodule.starProjection_eq_self_iff.2 hmem
      have : ((Lz (g q) : K) : Matrix ι ι ℝ) = L (Ψ q) := by
        simp only [g, ContinuousLinearEquiv.apply_symm_apply]
        exact hP
      simp only [hΨdef, map_zero, ZeroMemClass.coe_zero, add_zero]
      rw [this]
      exact hxq

/-- **Lemma 24.4 (i), total geodesy** (Milnor p. 137, "this clearly implies"): the stratum is a
totally geodesic set of orthogonal matrices with `T = 𝒯`; its geodesics are the
`t ↦ x exp(tA)`, `A ∈ 𝒯_x` (`Morse.IsTotGeo.isGeodesicOn_mul_exp_smul`,
`Morse.IsTotGeo.eqOn_mul_exp_smul`). -/
theorem isTotGeo_omegaStratum (hJ : IsAnticommFamily J k) (p : Matrix ι ι ℝ) :
    IsTotGeo (isSliceSubmanifold_omegaStratum hJ p) (tanAlg J k) where
  unitary _ hx := omega_orth hx.1
  skew _ _ _ hA := hA.1
  mul_exp_mem _ hx _ hA :=
    ⟨mul_exp_mem_omega hx.1 hA, (finrank_tanAlg_mul_exp hA).trans hx.2⟩
  mem_mul_exp _ _ _ hA := mem_tanAlg_mul_exp hA
  finrank_eq _ hx := hx.2

end Local

end Morse
