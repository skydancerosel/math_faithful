import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_26

open Matrix Set Filter Topology Module
open scoped ContDiff

namespace RoundTrip.V15_26

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The project's statement (universes instantiated at `0`, any finite index type; `basePt J k` is
`J_k`, `J_0 = I`; `minVelO J k p = {A ∈ 𝒯_p | A² = −I}` the initial directions of the minimal
geodesics; `omegaPhi` is Milnor's `φ : Ω_{k+1}(n) → Ω(Ω_k(n); J_k, −J_k)` into the project's path
space of the stratum of `J_k` (paths `ℝ → Mₙ(ℝ)`, Milnor's metric with the stratum's distance)):
`A ∈ minVelO J k J_k ↔ J_kA ∈ Ω_{k+1}(n)` (`J_1, …, J_k` anticommuting); the geodesic
`t ↦ J_k exp(πt J_kᴴJ')` is the semicircle `cos(πt)J_k + sin(πt)J'`; `omegaPhi J'` is that
semicircle; and, for `J_1, …, J_{k+1}` anticommuting, `omegaPhi` factors through a **homotopy
equivalence** `Ω_{k+1}(n) ≃ₕ` (energy-minimal paths from `J_k` to `−J_k`). The definitions
`minVelOHomeomorph` (`minVelO ≅ Ω_{k+1}`, `A ↦ J_kA`) and `omegaMinPathsHomeomorph` (`minVelO ≅` the
separation quotient of the minimal paths) are vocabulary, not part of `A`. -/
def A : Prop :=
  type_of% @Morse.mem_minVelO_iff.{0} ∧ type_of% @Morse.omegaGeo_eq_semicircle.{0} ∧
    type_of% @Morse.omegaPhi_apply.{0} ∧ type_of% @Morse.isHomotopyEquiv_omegaPhi_minPaths.{0}

theorem A_holds : A :=
  ⟨@Morse.mem_minVelO_iff.{0}, @Morse.omegaGeo_eq_semicircle.{0}, @Morse.omegaPhi_apply.{0},
    @Morse.isHomotopyEquiv_omegaPhi_minPaths.{0}⟩

/-! ## B ⇒ A, only vacuously: A re-proved outright (the project's proofs, copied) -/

section Outright
open scoped Morse.MatrixInner
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_minVelO_iff' {J : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily J k) {A : Matrix ι ι ℝ} :
    A ∈ Morse.minVelO J k (Morse.basePt J k) ↔ Morse.basePt J k * A ∈ Morse.Omega J (k + 1) := by
  unfold Morse.basePt
  split_ifs with hk
  · subst hk
    rw [Matrix.one_mul]
    constructor
    · rintro ⟨⟨h1, -, -⟩, h2⟩
      exact ⟨Morse.isComplexStructure_iff.2 ⟨by rw [← Morse.conjTranspose_real, h1], h2⟩,
        fun α h1 h2 => absurd (h1.trans h2) (by norm_num)⟩
    · rintro ⟨hc, -⟩
      obtain ⟨h1, h2⟩ := Morse.isComplexStructure_iff.1 hc
      exact ⟨⟨by rw [Morse.conjTranspose_real, h1], fun h => absurd rfl h,
        fun α _ h => (by omega : False).elim⟩, h2⟩
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
    have hJk := (hJ.cs k hk1 le_rfl).2
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact Morse.mul_mem_omega_succ hJ hk1
        (Morse.isComplexStructure_iff.2 ⟨by rw [← Morse.conjTranspose_real, h1], h4⟩) (h2 hk) h3
    · intro hJ'
      obtain ⟨hc, hak, hα, -⟩ := Morse.omega_succ_decomp hJ hk1 hJ'
      have hA : -(J k * (J k * A)) = A := by
        rw [← Matrix.mul_assoc, hJk, Matrix.neg_mul, Matrix.one_mul, neg_neg]
      rw [hA] at hc hak hα
      obtain ⟨h1, h2⟩ := Morse.isComplexStructure_iff.1 hc
      exact ⟨⟨by rw [Morse.conjTranspose_real, h1], fun _ => hak, hα⟩, h2⟩

theorem omegaGeo_eq_semicircle' {J : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily J k) {J' : Matrix ι ι ℝ}
    (hJ' : J' ∈ Morse.Omega J (k + 1)) (t : ℝ) :
    Morse.omegaGeo (Morse.basePt J k) ((Morse.basePt J k)ᴴ * J') t =
      Real.cos (Real.pi * t) • Morse.basePt J k + Real.sin (Real.pi * t) • J' := by
  have hpo := Morse.omega_orth (Morse.basePt_mem_omega hJ)
  have hA : (Morse.basePt J k)ᴴ * J' ∈ Morse.minVelO J k (Morse.basePt J k) := by
    refine (mem_minVelO_iff' hJ).2 ?_
    rw [← Matrix.mul_assoc, Morse.mul_conjTranspose_eq_one hpo, Matrix.one_mul]
    exact hJ'
  simp only [Morse.omegaGeo, smul_smul]
  rw [Morse.exp_smul_of_mul_self_eq_neg_one hA.2, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
    Matrix.mul_smul, ← Matrix.mul_assoc, Morse.mul_conjTranspose_eq_one hpo, Matrix.one_mul,
    mul_comm t Real.pi]

theorem minVel_base' {J : ℕ → Mat ι} {k : ℕ} (hJ : Morse.IsAnticommFamily J (k + 1)) :
    (Morse.basePt J k)ᴴ * J (k + 1) ∈ Morse.minVelO J k (Morse.basePt J k) := by
  refine (mem_minVelO_iff' (hJ.mono k.le_succ)).2 ?_
  rw [← Matrix.mul_assoc, Morse.mul_conjTranspose_eq_one
    (Morse.omega_orth (Morse.basePt_mem_omega (hJ.mono k.le_succ))), Matrix.one_mul]
  exact hJ.mem_omega (by omega)

end Outright

/-- The two conjuncts of `A` whose statements do not mention `omegaPhi`. (`#rt_check` cannot be run
on any term mentioning `A`: the *definition* `Morse.omegaPhi`, in the statements of
`omegaPhi_apply` and `isHomotopyEquiv_omegaPhi_minPaths`, applies the theorem `Morse.minVel_base`,
which is proved with `Morse.mem_minVelO_iff`.) -/
def A2 : Prop :=
  type_of% @Morse.mem_minVelO_iff.{0} ∧ type_of% @Morse.omegaGeo_eq_semicircle.{0}

/-- B ⇒ A2, only vacuously: proved outright (the project's proofs, copied). -/
theorem B_to_A2 : B → A2 := fun _ =>
  ⟨@fun ι _ _ J k hJ A => mem_minVelO_iff' hJ, @fun ι _ _ J k hJ J' hJ' t =>
    omegaGeo_eq_semicircle' hJ hJ' t⟩

/-- B ⇒ A, only vacuously: A is proved outright (B's homeomorphisms between Milnor's spaces of
minimal geodesics and `Ω_{ℓ+1}(n)` are mere existence statements about the blind path spaces; they
cannot produce A's explicit identities, nor A's homotopy equivalence on the project's path space).
The last two conjuncts hold by the definition of `omegaPhi` (through `minVelOHomeomorph` and
`omegaMinPathsHomotopyEquiv`). -/
theorem B_to_A : B → A := fun hB =>
  ⟨(B_to_A2 hB).1, (B_to_A2 hB).2, @fun ι _ _ J k hJ J' t =>
    omegaGeo_eq_semicircle' (hJ.mono k.le_succ) J'.2 t, @fun ι _ _ J k hJ =>
    ⟨(Morse.minVelOHomeomorph (hJ.mono k.le_succ)).symm.toHomotopyEquiv.trans
      (Morse.omegaMinPathsHomotopyEquiv (hJ.mono k.le_succ)
        (Morse.basePt_mem_omega (hJ.mono k.le_succ)) (minVel_base' hJ)), rfl⟩⟩

#rt_check RoundTrip.V15_26.B_to_A2 [Morse.mem_minVelO_iff, Morse.omegaGeo_eq_semicircle,
  Morse.omegaPhi_apply, Morse.isHomotopyEquiv_omegaPhi_minPaths]
#rt_overlap RoundTrip.V15_26.B_to_A2 [Morse.mem_minVelO_iff, Morse.omegaGeo_eq_semicircle,
  Morse.omegaPhi_apply, Morse.isHomotopyEquiv_omegaPhi_minPaths]

end

end RoundTrip.V15_26
