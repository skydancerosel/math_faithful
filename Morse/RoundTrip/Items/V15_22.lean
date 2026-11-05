import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_22

open Matrix Set Filter Topology Module
open scoped ContDiff

namespace RoundTrip.V15_22

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The project's statement (universes instantiated at `0`, any finite index type, any sequence
`J`; `Morse.tanAlg J k x` is Milnor's `𝒯_x = {A skew | (k ≠ 0 →) Ax = −xA, AJ_α = J_αA (α < k)}`):
its membership (`mem_tanAlg`), `𝒯` for `k = 0` does not depend on the point; **Assertions 1 and 2,
"if" halves**: `x exp A ∈ Ω_k(n)` for `x ∈ Ω_k(n)`, `A ∈ 𝒯_x` (every `A`, no smallness);
`A ∈ 𝒯_{x exp A}`; `exp` is injective on a ball `‖·‖ < ε` (Frobenius norm); **"only if" halves**:
for such an `ε`, an anticommuting family `J_1, …, J_k`, `x ∈ Ω_k(n)` and `‖C‖ < ε`,
`x exp C ∈ Ω_k(n)` implies `C ∈ 𝒯_x`; and the **local logarithm**: near `x ∈ Ω_k(n)`, every point of
`Ω_k(n)` is `x exp(L y)` with `L y ∈ 𝒯_x`, `L y → 0`. -/
def A : Prop :=
  type_of% @Morse.mem_tanAlg.{0} ∧ type_of% @Morse.tanAlg_zero.{0} ∧
    type_of% @Morse.mul_exp_mem_omega.{0} ∧ type_of% @Morse.mem_tanAlg_mul_exp.{0} ∧
    type_of% @Morse.exists_exp_injective.{0} ∧ type_of% @Morse.mem_tanAlg_of_mul_exp_mem.{0} ∧
    type_of% @Morse.exists_local_log.{0}

theorem A_holds : A :=
  ⟨@Morse.mem_tanAlg.{0}, @Morse.tanAlg_zero.{0}, @Morse.mul_exp_mem_omega.{0},
    @Morse.mem_tanAlg_mul_exp.{0}, @Morse.exists_exp_injective.{0},
    @Morse.mem_tanAlg_of_mul_exp_mem.{0}, @Morse.exists_local_log.{0}⟩

/-! ## Vocabulary -/

section Vocab
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isACFam_iff (Js : ℕ → Mat ι) (m : ℕ) : IsACFam Js m ↔ Morse.IsAnticommFamily Js m :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.cs, h.anti⟩⟩

theorem omegaK_eq_omega (Js : ℕ → Mat ι) (k : ℕ) : OmegaK Js k = Morse.Omega Js k := by
  cases k with
  | zero => rfl
  | succ k =>
    ext J
    simp only [OmegaK, Morse.Omega, IsCplxStr, Morse.IsComplexStructure, AntiComm,
      Set.mem_ofPred_eq]
    refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun _ =>
      ⟨fun h => by rw [h, neg_neg], fun h => by rw [h, neg_neg]⟩)

theorem omegaK_subset_orth (Js : ℕ → Mat ι) (k : ℕ) : OmegaK Js k ⊆ Orth ι := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact fun J hJ => hJ.1.1

theorem orth_iff {X : Mat ι} : X ∈ Orth ι ↔ Xᵀ * X = 1 := by
  rw [Orth, SetLike.mem_coe, mem_orthogonalGroup_iff']

theorem orth_iff' {X : Mat ι} : X ∈ Orth ι ↔ X * Xᵀ = 1 := by
  rw [Orth, SetLike.mem_coe, mem_orthogonalGroup_iff]

/-- The family where `J_k` is replaced by a point `x ∈ Ω_k(n)` (Milnor's `J_1, …, J_{k-1}, x`). -/
def famAt (Js : ℕ → Mat ι) (k : ℕ) (x : Mat ι) : ℕ → Mat ι := Function.update Js k x

theorem omega_famAt (Js : ℕ → Mat ι) (k : ℕ) (x : Mat ι) :
    Morse.Omega (famAt Js k x) k = Morse.Omega Js k := by
  cases k with
  | zero => rfl
  | succ k =>
    ext J
    simp only [Morse.Omega, Set.mem_ofPred_eq, famAt]
    refine and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun h => ?_)
    rw [Function.update_of_ne (by omega)]

theorem tanAlg_famAt (Js : ℕ → Mat ι) (k : ℕ) (x y : Mat ι) :
    Morse.tanAlg (famAt Js k x) k y = Morse.tanAlg Js k y := by
  ext A
  change (Aᴴ = -A ∧ (k ≠ 0 → A * y = -(y * A)) ∧
      ∀ α, 1 ≤ α → α < k → A * famAt Js k x α = famAt Js k x α * A) ↔
    (Aᴴ = -A ∧ (k ≠ 0 → A * y = -(y * A)) ∧ ∀ α, 1 ≤ α → α < k → A * Js α = Js α * A)
  simp only [famAt]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ =>
    forall_congr' fun h => ?_))
  rw [Function.update_of_ne (by omega)]

theorem omegaStratum_famAt (Js : ℕ → Mat ι) (k : ℕ) (x p : Mat ι) :
    Morse.omegaStratum (famAt Js k x) k p = Morse.omegaStratum Js k p := by
  ext y
  simp only [Morse.omegaStratum, Set.mem_ofPred_eq, omega_famAt]
  rw [tanAlg_famAt, tanAlg_famAt]

/-- For `x ∈ Ω_k(n)` (`J_1, …, J_{k-1}` anticommuting complex structures), `J_1, …, J_{k-1}, x` is
an anticommuting family (`k ≥ 1`; for `k = 0` the empty family). -/
theorem isAnticommFamily_famAt {Js : ℕ → Mat ι} {k : ℕ} (hJ : IsACFam Js (k - 1)) {x : Mat ι}
    (hx : x ∈ OmegaK Js k) : Morse.IsAnticommFamily (famAt Js k x) k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨fun α h1 h2 => absurd h2 (by omega), fun α _ h1 h2 _ _ _ => absurd h2 (by omega)⟩
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hx' := hx
  simp only [Nat.add_sub_cancel] at hJ
  refine ⟨fun α h1 h2 => ?_, fun α β h1 h2 h3 h4 hne => ?_⟩
  · by_cases hα : α = k + 1
    · subst hα; simp only [famAt, Function.update_self]; exact hx.1
    · simp only [famAt, Function.update_of_ne hα]; exact hJ.1 α h1 (by omega)
  · by_cases hα : α = k + 1
    · subst hα
      simp only [famAt, Function.update_self, Function.update_of_ne (Ne.symm hne)]
      have := hx.2 β h3 (by omega)
      exact this
    · by_cases hβ : β = k + 1
      · subst hβ
        simp only [famAt, Function.update_self, Function.update_of_ne hα]
        have := hx.2 α h1 (by omega)
        rw [this, neg_neg]
      · simp only [famAt, Function.update_of_ne hα, Function.update_of_ne hβ]
        exact hJ.2 α β h1 (by omega) h3 (by omega) hne

end Vocab

section Alg
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem omegaK_cs {Js : ℕ → Mat ι} {k : ℕ} (hk : 1 ≤ k) {x : Mat ι} (hx : x ∈ OmegaK Js k) :
    IsCplxStr x := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact hx.1

theorem omegaK_anti {Js : ℕ → Mat ι} {k : ℕ} {x : Mat ι} (hx : x ∈ OmegaK Js k) {α : ℕ}
    (h1 : 1 ≤ α) (h2 : α ≤ k - 1) (hk : 1 ≤ k) : AntiComm x (Js α) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact hx.2 α h1 (by omega)

/-- The constant family `J` (so that `Ω_1 = ` complex structures and `𝒯_x` for `k = 1` only asks
`Ax = −xA`). -/
def cst (J : Mat ι) : ℕ → Mat ι := fun _ => J

theorem mem_omega_cst_one {J x : Mat ι} : x ∈ Morse.Omega (cst J) 1 ↔ IsCplxStr x :=
  ⟨fun h => h.1, fun h => ⟨h, fun α h1 h2 => absurd (h1.trans h2) (by norm_num)⟩⟩

theorem isAnticommFamily_cst {J : Mat ι} (hJ : IsCplxStr J) : Morse.IsAnticommFamily (cst J) 1 :=
  ⟨fun _ _ _ => hJ, fun α β h1 h2 h3 h4 hne => absurd (by omega : α = β) hne⟩

theorem mem_tanAlg_cst_one {J x A : Mat ι} :
    A ∈ Morse.tanAlg (cst J) 1 x ↔ Aᵀ = -A ∧ A * x = -(x * A) := by
  change (Aᴴ = -A ∧ (1 ≠ 0 → A * x = -(x * A)) ∧
    ∀ α, 1 ≤ α → α < 1 → A * cst J α = cst J α * A) ↔ _
  rw [conjTranspose_eq_transpose_of_trivial]
  exact and_congr Iff.rfl ⟨fun h => h.1 one_ne_zero, fun h => ⟨fun _ => h,
    fun α h1 h2 => absurd h2 (by omega)⟩⟩

theorem tset_eq {Js : ℕ → Mat ι} {k : ℕ} (hk : 1 ≤ k) (J : Mat ι) :
    Tset Js k J = (Morse.tanAlg Js k J : Set (Mat ι)) := by
  ext A
  change _ ↔ (Aᴴ = -A ∧ (k ≠ 0 → A * J = -(J * A)) ∧ ∀ α, 1 ≤ α → α < k → A * Js α = Js α * A)
  simp only [Tset, Set.mem_ofPred_eq, IsSkew, AntiComm, conjTranspose_eq_transpose_of_trivial]
  refine and_congr Iff.rfl (and_congr ⟨fun h _ => h, fun h => h (by omega)⟩
    (forall_congr' fun α => forall_congr' fun _ => ⟨fun h h2 => (h (by omega)).eq,
      fun h h2 => h (by omega)⟩))

end Alg

section Main
open scoped Morse.MatrixInner

/-- A ⇒ B. Fix `J ∈ Ω_k(n)` and an injectivity radius `ε` of `exp` (A's `exists_exp_injective`);
for skew `A` with `‖A‖ < ε` (a neighbourhood of `0`):
* Assertion 1: "if" is A's `mul_exp_mem_omega`, "only if" A's `mem_tanAlg_of_mul_exp_mem`, both for
  the family `(J, J, …)` with `k = 1` (`Ω_1` = complex structures);
* Assertion 2: "if" is algebra (`Morse.anticomm_mul_exp`); "only if" is the injectivity of `exp`
  (A's `exists_exp_injective`): `exp(J_αAJ_α⁻¹) = J_α exp(A) J_α⁻¹ = exp A` (A's
  `mem_tanAlg_of_mul_exp_mem` needs `J exp A ∈ Ω_k(n)`, i.e. also Assertion 1's hypothesis, which
  Milnor's Assertion 2 does not assume; its proof is the one used here);
* `T = 𝒯_J` is A's submodule `tanAlg` (`mem_tanAlg`); `J exp(T ∩ U) ⊆ Ω_k(n)` by
  `mul_exp_mem_omega`, and it is a neighbourhood of `J` in `Ω_k(n)` for every neighbourhood `U` of
  `0` by A's local logarithm `exists_local_log` (for the family `J_1, …, J_{k-1}, J`). -/
theorem A_to_B : A → B := by
  rintro ⟨hmemT, -, hmulexp, -, hinj, honlyif, hlog⟩ n k Js hk hJ J hJΩ
  have hJcs : IsCplxStr J := omegaK_cs hk hJΩ
  have hJo : Jᵀ * J = 1 := orth_iff.1 hJcs.1
  have hJo' : J * Jᵀ = 1 := orth_iff'.1 hJcs.1
  have hJΩ' : J ∈ Morse.Omega Js k := by rw [← omegaK_eq_omega]; exact hJΩ
  obtain ⟨ε, hε, hε'⟩ := hinj (ι := Fin n)
  refine ⟨?_, ⟨Morse.tanAlg Js k J, (tset_eq hk J).symm⟩, univ, univ_mem, fun U hU _ => ⟨?_, ?_⟩⟩
  · filter_upwards [Metric.ball_mem_nhds (0 : Mat (Fin n)) hε] with A hA hskew
    have hA' : ‖A‖ < ε := by simpa using hA
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h α h1 h2 => ?_, fun h α h1 h2 => ?_⟩⟩
    · -- Assertion 1, only if
      have := honlyif (isAnticommFamily_cst hJcs) hε' (mem_omega_cst_one.2 hJcs) hA'
        (mem_omega_cst_one.2 h)
      exact (mem_tanAlg_cst_one.1 this).2
    · -- Assertion 1, if
      exact (mem_omega_cst_one (J := J)).1 (hmulexp ((mem_omega_cst_one (J := J)).2 hJcs)
        (mem_tanAlg_cst_one.2 ⟨hskew, h⟩))
    · -- Assertion 2, only if
      have hα := h α h1 h2
      have hJα : IsCplxStr (Js α) := hJ.1 α h1 h2
      have hJαo : (Js α)ᵀ * Js α = 1 := orth_iff.1 hJα.1
      have hJαo' : Js α * (Js α)ᵀ = 1 := orth_iff'.1 hJα.1
      have hJJα : J * Js α = -(Js α * J) := omegaK_anti hJΩ h1 h2 hk
      -- `exp A` commutes with `J_α`
      have hc : NormedSpace.exp A * Js α = Js α * NormedSpace.exp A := by
        have e : J * (NormedSpace.exp A * Js α) = J * (Js α * NormedSpace.exp A) := by
          rw [← Matrix.mul_assoc, hα, ← Matrix.mul_assoc,
            show Js α * J = -(J * Js α) by rw [hJJα, neg_neg], Matrix.neg_mul, neg_neg,
            Matrix.mul_assoc]
        have := congrArg (Jᵀ * ·) e
        simpa only [← Matrix.mul_assoc, hJo, Matrix.one_mul] using this
      have hg : ((Js α)ᵀ)ᴴ * (Js α)ᵀ = 1 := by
        rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]; exact hJαo'
      have h3 : NormedSpace.exp (((Js α)ᵀ)ᴴ * A * (Js α)ᵀ) = NormedSpace.exp A := by
        rw [Morse.exp_conj_orth hg, conjTranspose_eq_transpose_of_trivial, transpose_transpose,
          ← hc, Matrix.mul_assoc, hJαo', Matrix.mul_one]
      have h4 := hε' _ _ (by rwa [Morse.norm_conj_orth hg]) hA' h3
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at h4
      calc A * Js α = Js α * A * (Js α)ᵀ * Js α := by rw [h4]
        _ = Js α * A := by rw [Matrix.mul_assoc, hJαo, Matrix.mul_one]
    · -- Assertion 2, if
      have hJJα : Js α * J = -(J * Js α) := by
        rw [omegaK_anti hJΩ h1 h2 hk, neg_neg]
      have := Morse.anticomm_mul_exp hJJα (h α h1 h2)
      change J * NormedSpace.exp A * Js α = -(Js α * (J * NormedSpace.exp A))
      rw [this, neg_neg]
  · rintro _ ⟨A, ⟨hAT, -⟩, rfl⟩
    rw [tset_eq hk] at hAT
    rw [omegaK_eq_omega]
    exact hmulexp hJΩ' hAT
  · have hJ' := isAnticommFamily_famAt (by simpa using hJ) hJΩ
    have hJΩ'' : J ∈ Morse.Omega (famAt Js k J) k := by rw [omega_famAt]; exact hJΩ'
    obtain ⟨L, hLt, hL⟩ := hlog hJ' hJΩ''
    rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [hL, hLt.eventually hU] with y hy hyU hyΩ
    rw [omegaK_eq_omega, ← omega_famAt Js k J] at hyΩ
    obtain ⟨hmem, heq⟩ := hy hyΩ
    rw [tanAlg_famAt] at hmem
    exact ⟨L y, ⟨by rw [tset_eq hk]; exact hmem, hyU⟩, heq⟩

#rt_check RoundTrip.V15_22.A_to_B [Morse.mem_tanAlg, Morse.tanAlg_zero, Morse.mul_exp_mem_omega,
  Morse.mem_tanAlg_mul_exp, Morse.exists_exp_injective, Morse.mem_tanAlg_of_mul_exp_mem,
  Morse.exists_local_log]

end Main

/-! ## B ⇒ A, only vacuously: A re-proved outright (the project's proofs, copied) -/

section Outright
open scoped Morse.MatrixInner
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_exp_injective' :
    ∃ ε > 0, ∀ C D : Matrix ι ι ℝ, ‖C‖ < ε → ‖D‖ < ε →
      NormedSpace.exp C = NormedSpace.exp D → C = D := by
  obtain ⟨e₀, hf⟩ := Morse.exists_hasStrictFDerivAt_exp_zero (ι := ι)
  set e := hf.toOpenPartialHomeomorph _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_source 0
    hf.mem_toOpenPartialHomeomorph_source
  refine ⟨ε, hε, fun C D hC hD hCD => e.injOn (hball ?_) (hball ?_) hCD⟩
  · simpa using hC
  · simpa using hD

theorem mul_exp_mem_omega' {J : ℕ → Mat ι} {k : ℕ} {x : Mat ι} (hx : x ∈ Morse.Omega J k) {A : Matrix ι ι ℝ} (hA : A ∈ Morse.tanAlg J k x) :
    x * NormedSpace.exp A ∈ Morse.Omega J k := by
  obtain ⟨h1, h2, h3⟩ := hA
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine Morse.mem_omega_zero ?_
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc xᴴ, Morse.omega_orth hx,
      Matrix.one_mul]
    exact Morse.exp_conjTranspose_mul_exp_of_skew h1
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine ⟨Morse.isComplexStructure_mul_exp hx.1 (by rw [← Morse.conjTranspose_real, h1])
      (h2 (by omega)), fun α hα hαk => ?_⟩
    exact Morse.anticomm_mul_exp (hx.2 α hα hαk) (h3 α hα (by omega))

theorem mem_tanAlg_mul_exp' {J : ℕ → Mat ι} {k : ℕ} {x : Mat ι} {A : Matrix ι ι ℝ} (hA : A ∈ Morse.tanAlg J k x) :
    A ∈ Morse.tanAlg J k (x * NormedSpace.exp A) := by
  obtain ⟨h1, h2, h3⟩ := hA
  refine ⟨h1, fun hk => ?_, h3⟩
  have hc : A * NormedSpace.exp A = NormedSpace.exp A * A := by
    simpa using (Morse.exp_smul_mul_self A 1).symm
  rw [← Matrix.mul_assoc, h2 hk, Matrix.neg_mul, Matrix.mul_assoc, hc, Matrix.mul_assoc]

theorem mem_tanAlg_of_mul_exp_mem' {J : ℕ → Mat ι} {k : ℕ} {x : Mat ι} (hJ : Morse.IsAnticommFamily J k) {ε : ℝ}
    (hε : ∀ C D : Matrix ι ι ℝ, ‖C‖ < ε → ‖D‖ < ε →
      NormedSpace.exp C = NormedSpace.exp D → C = D)
    (hx : x ∈ Morse.Omega J k) {C : Matrix ι ι ℝ} (hC : ‖C‖ < ε)
    (hy : x * NormedSpace.exp C ∈ Morse.Omega J k) : C ∈ Morse.tanAlg J k x := by
  have hxo := Morse.omega_orth hx
  have hyo := Morse.omega_orth hy
  have hxo' := Morse.mul_conjTranspose_eq_one hxo
  have hneg : ‖-C‖ < ε := by rwa [norm_neg]
  have hE : (NormedSpace.exp C)ᴴ * NormedSpace.exp C = 1 := by
    have e : (x * NormedSpace.exp C)ᴴ * (x * NormedSpace.exp C) =
        (NormedSpace.exp C)ᴴ * (xᴴ * x) * NormedSpace.exp C := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [hxo, Matrix.mul_one] at e
    rw [← e]; exact hyo
  have hEneg : (NormedSpace.exp C)ᴴ = NormedSpace.exp (-C) := by
    calc (NormedSpace.exp C)ᴴ = (NormedSpace.exp C)ᴴ * (NormedSpace.exp C * NormedSpace.exp (-C)) := by
          rw [Morse.exp_mul_exp_neg, Matrix.mul_one]
      _ = NormedSpace.exp (-C) := by rw [← Matrix.mul_assoc, hE, Matrix.one_mul]
  refine ⟨?_, fun hk => ?_, fun α h1 h2 => ?_⟩
  · refine hε _ _ (by rwa [Morse.norm_conjTranspose_real]) hneg ?_
    rw [Matrix.exp_conjTranspose, hEneg]
  · have hx2 := Morse.omega_sq hk hx
    have hy2 := Morse.omega_sq hk hy
    have hxH : xᴴ = -x := by
      calc xᴴ = xᴴ * (-(x * x)) := by rw [hx2, neg_neg, Matrix.mul_one]
        _ = -x := by rw [Matrix.mul_neg, ← Matrix.mul_assoc, hxo, Matrix.one_mul]
    have key : NormedSpace.exp (xᴴ * C * x) * NormedSpace.exp C = 1 := by
      rw [Morse.exp_conj_orth hxo]
      have : x * NormedSpace.exp C * (x * NormedSpace.exp C) =
          -(xᴴ * NormedSpace.exp C * x * NormedSpace.exp C) := by
        rw [hxH]; simp only [Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
      rw [← neg_inj, ← this, hy2]
    have h3 : NormedSpace.exp (xᴴ * C * x) = NormedSpace.exp (-C) := by
      calc NormedSpace.exp (xᴴ * C * x) =
            NormedSpace.exp (xᴴ * C * x) * (NormedSpace.exp C * NormedSpace.exp (-C)) := by
              rw [Morse.exp_mul_exp_neg, Matrix.mul_one]
        _ = NormedSpace.exp (-C) := by rw [← Matrix.mul_assoc, key, Matrix.one_mul]
    have h4 := hε _ _ (by rwa [Morse.norm_conj_orth hxo]) hneg h3
    calc C * x = x * (xᴴ * C * x) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hxo', Matrix.one_mul]
      _ = -(x * C) := by rw [h4, Matrix.mul_neg]
  · have ha := Morse.omega_anti hx h1 h2
    have hb := Morse.omega_anti hy h1 h2
    have hJo := hJ.orth h1 (by omega)
    have hJo' := Morse.mul_conjTranspose_eq_one hJo
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
      have := Morse.exp_conj_orth hJH C
      rw [conjTranspose_conjTranspose] at this
      rw [this, hc, Matrix.mul_assoc, hJo', Matrix.mul_one]
    have h4 := hε _ _ (by
      have := Morse.norm_conj_orth hJH C
      rw [conjTranspose_conjTranspose] at this
      rwa [this]) hC h3
    calc C * J α = J α * C * (J α)ᴴ * J α := by rw [h4]
      _ = J α * C := by rw [Matrix.mul_assoc, hJo, Matrix.mul_one]

theorem tanAlg_zero' (J : ℕ → Matrix ι ι ℝ) (x y : Matrix ι ι ℝ) :
    Morse.tanAlg J 0 x = Morse.tanAlg J 0 y := by
  ext A
  change (_ ∧ (0 ≠ 0 → _) ∧ ∀ α, 1 ≤ α → α < 0 → _) ↔ (_ ∧ (0 ≠ 0 → _) ∧ ∀ α, 1 ≤ α → α < 0 → _)
  simp only [ne_eq, not_true_eq_false, false_imp_iff, true_and]

theorem exists_local_log' {J : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily J k) {x : Matrix ι ι ℝ} (hx : x ∈ Morse.Omega J k) :
    ∃ L : Matrix ι ι ℝ → Matrix ι ι ℝ, Tendsto L (𝓝 x) (𝓝 0) ∧
      ∀ᶠ y in 𝓝 x, y ∈ Morse.Omega J k → L y ∈ Morse.tanAlg J k x ∧ x * NormedSpace.exp (L y) = y := by
  obtain ⟨ε, hε, hinj⟩ := exists_exp_injective' (ι := ι)
  obtain ⟨lg, hlg1, hlg2⟩ := Morse.exists_log (ι := ι)
  have hxo := Morse.omega_orth hx
  have ht : Tendsto (fun y => xᴴ * y) (𝓝 x) (𝓝 1) := by
    have : Continuous fun y : Matrix ι ι ℝ => xᴴ * y := continuous_const.mul continuous_id
    have h := this.tendsto x
    rwa [hxo] at h
  refine ⟨fun y => lg (xᴴ * y), hlg2.comp ht, ?_⟩
  have h1 := ht.eventually hlg1
  have h2 := (hlg2.comp ht).eventually (Metric.ball_mem_nhds (0 : Matrix ι ι ℝ) hε)
  filter_upwards [h1, h2] with y hy1 hy2 hy
  have hxy : x * NormedSpace.exp (lg (xᴴ * y)) = y := by
    rw [hy1, ← Matrix.mul_assoc, Morse.mul_conjTranspose_eq_one hxo, Matrix.one_mul]
  have hnorm : ‖lg (xᴴ * y)‖ < ε := by simpa using hy2
  refine ⟨mem_tanAlg_of_mul_exp_mem' hJ hinj hx hnorm (by rw [hxy]; exact hy), hxy⟩

end Outright

/-- B ⇒ A, only vacuously: A is proved outright. B gives the Assertions only on some neighbourhood
of `0` depending on `J`, only for `J ∈ Ω_k(n)` with `J_1, …, J_{k-1}` anticommuting complex
structures, on `ℝⁿ = Fin n`; A's "if" halves hold for every `A ∈ 𝒯_x`, its "only if" halves on any
injectivity ball of `exp` (an explicit radius), and A states the injectivity of `exp` and the local
logarithm as such. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@fun ι _ _ J k x A => Iff.rfl, @fun ι _ _ J x y => tanAlg_zero' J x y,
    @fun ι _ _ J k x hx A hA => mul_exp_mem_omega' hx hA,
    @fun ι _ _ J k x A hA => mem_tanAlg_mul_exp' hA, @fun ι _ _ => exists_exp_injective',
    @fun ι _ _ J k x hJ ε hε hx C hC hy => mem_tanAlg_of_mul_exp_mem' hJ hε hx hC hy,
    @fun ι _ _ J k hJ x hx => exists_local_log' hJ hx⟩

#rt_check RoundTrip.V15_22.B_to_A [Morse.mem_tanAlg, Morse.tanAlg_zero, Morse.mul_exp_mem_omega,
  Morse.mem_tanAlg_mul_exp, Morse.exists_exp_injective, Morse.mem_tanAlg_of_mul_exp_mem,
  Morse.exists_local_log]
#rt_overlap RoundTrip.V15_22.B_to_A [Morse.mem_tanAlg, Morse.tanAlg_zero, Morse.mul_exp_mem_omega,
  Morse.mem_tanAlg_mul_exp, Morse.exists_exp_injective, Morse.mem_tanAlg_of_mul_exp_mem,
  Morse.exists_local_log]

end

end RoundTrip.V15_22
