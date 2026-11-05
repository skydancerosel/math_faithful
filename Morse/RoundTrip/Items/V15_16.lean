import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_16

open Matrix Module
open scoped MatrixOrder

namespace RoundTrip.V15_16

/-- The project's statement (universes instantiated at `0`), for an abstract real vector space
with anticommuting square roots of `-1` (`Morse.IsClifford`, no inner product) and
`Morse.IsMinimalCliffordModule` (non-zero, no proper non-trivial invariant subspace): for `k ≤ 8`
a minimal space has dimension `milnorM k`; a space of dimension `milnorM k` is minimal;
`milnorM k ≤ dim ≤ 2^k` for minimal spaces; for `k ≤ 2` the dimension is `milnorM k`; a central
involution acts by `±1` on a minimal space (any `k`); a minimal `(J_1, J_2, J_3)`-space is a
minimal `(J_1, J_2)`-space; a minimal `(J_1, …, J_7)`-space is a minimal `(J_1, …, J_6)`-space. -/
def A : Prop :=
  type_of% @Morse.finrank_eq_milnorM_of_isMinimal.{0} ∧
    type_of% @Morse.isMinimal_of_finrank_eq_milnorM.{0} ∧
    type_of% @Morse.milnorM_le_finrank_le.{0} ∧ type_of% @Morse.finrank_eq_milnorM_of_le_two.{0} ∧
    type_of% @Morse.central_involution.{0} ∧ type_of% @Morse.minimal_three.{0} ∧
    type_of% @Morse.minimal_seven.{0}

theorem A_holds : A :=
  ⟨@Morse.finrank_eq_milnorM_of_isMinimal.{0}, @Morse.isMinimal_of_finrank_eq_milnorM.{0},
    @Morse.milnorM_le_finrank_le.{0}, @Morse.finrank_eq_milnorM_of_le_two.{0},
    @Morse.central_involution.{0}, @Morse.minimal_three.{0}, @Morse.minimal_seven.{0}⟩

/-! ## Glue: orthogonalizing an abstract `(J_1, …, J_k)`-space (for B ⇒ A)

B speaks of anticommuting *orthogonal* complex structures on `ℝⁿ = Fin n → ℝ`; A of anticommuting
square roots of `-1` on an abstract space. Averaging the inner product over `J_1, …, J_k`
(`G_{j+1} = G_j + J_{j+1}ᵀ G_j J_{j+1}`) and conjugating by a square root of `G_k` turns the latter
into the former (`ortho_glue`); minimality transfers along the compatible isomorphism. -/

namespace Glue
section Ortho
variable {n : Type} [Fintype n] [DecidableEq n]

/-- Iterated averaging of the standard inner product: `G_0 = 1`,
`G_{j+1} = G_j + M_{j+1}ᵀ G_j M_{j+1}`. -/
noncomputable def avgG (M : ℕ → Matrix n n ℝ) : ℕ → Matrix n n ℝ
  | 0 => 1
  | j + 1 => avgG M j + (M (j + 1))ᵀ * avgG M j * M (j + 1)

/-- `G_j` is positive definite and invariant under `M_1, …, M_j`. -/
theorem avgG_spec {M : ℕ → Matrix n n ℝ} {k : ℕ} (h : Morse.IsClifford M k) :
    ∀ j ≤ k, (avgG M j).PosDef ∧ ∀ a, 1 ≤ a → a ≤ j → (M a)ᵀ * avgG M j * M a = avgG M j := by
  intro j
  induction j with
  | zero => intro _; exact ⟨PosDef.one, fun a h1 h2 => by omega⟩
  | succ j ih =>
    intro hj
    obtain ⟨hpd, hinv⟩ := ih (by omega)
    have hG' : avgG M (j + 1) = avgG M j + (M (j + 1))ᵀ * avgG M j * M (j + 1) := rfl
    have hb2 : M (j + 1) * M (j + 1) = -1 := h.sq (j + 1) (by omega) hj
    refine ⟨?_, fun a h1 h2 => ?_⟩
    · rw [hG']
      refine hpd.add_posSemidef ?_
      have := hpd.posSemidef.conjTranspose_mul_mul_same (M (j + 1))
      rwa [Morse.conjTranspose_real] at this
    · rw [hG']
      rcases Nat.lt_or_ge a (j + 1) with ha | ha
      · have hab : M (j + 1) * M a = -(M a * M (j + 1)) :=
          h.anti (j + 1) a (by omega) hj h1 (by omega) (by omega)
        have h1' := hinv a h1 (by omega)
        calc (M a)ᵀ * (avgG M j + (M (j + 1))ᵀ * avgG M j * M (j + 1)) * M a
            = (M a)ᵀ * avgG M j * M a +
                (M (j + 1) * M a)ᵀ * avgG M j * (M (j + 1) * M a) := by
              simp only [transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
          _ = (M a)ᵀ * avgG M j * M a +
                (M (j + 1))ᵀ * ((M a)ᵀ * avgG M j * M a) * M (j + 1) := by
              rw [hab]
              simp only [transpose_neg, transpose_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
                Matrix.mul_assoc]
          _ = avgG M j + (M (j + 1))ᵀ * avgG M j * M (j + 1) := by rw [h1']
      · obtain rfl : a = j + 1 := by omega
        calc (M (j + 1))ᵀ * (avgG M j + (M (j + 1))ᵀ * avgG M j * M (j + 1)) * M (j + 1)
            = (M (j + 1))ᵀ * avgG M j * M (j + 1) +
                (M (j + 1) * M (j + 1))ᵀ * avgG M j * (M (j + 1) * M (j + 1)) := by
              simp only [transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
          _ = avgG M j + (M (j + 1))ᵀ * avgG M j * M (j + 1) := by
              rw [hb2]; simp [add_comm]

/-- Anticommuting square roots of `-1` (not necessarily orthogonal) are conjugate to anticommuting
complex structures: conjugate by a square root of the averaged inner product. -/
theorem exists_conj_orth {M : ℕ → Matrix n n ℝ} {k : ℕ} (h : Morse.IsClifford M k) :
    ∃ P : Matrix n n ℝ, IsUnit P.det ∧ Morse.IsAnticommFamily (fun α => P * M α * P⁻¹) k := by
  obtain ⟨hpd, hinv⟩ := avgG_spec h k le_rfl
  obtain ⟨B, hB⟩ : ∃ B : Matrix n n ℝ, avgG M k = star B * B :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpd.posSemidef.nonneg
  have hBt : star B = Bᵀ := by rw [star_eq_conjTranspose, Morse.conjTranspose_real]
  rw [hBt] at hB
  have hdet : IsUnit B.det := by
    have := hpd.det_pos
    rw [hB, det_mul, det_transpose] at this
    exact isUnit_iff_ne_zero.2 (fun h0 => by rw [h0, mul_zero] at this; exact lt_irrefl _ this)
  have hBB : B⁻¹ * B = 1 := nonsing_inv_mul B hdet
  have hBB' : B * B⁻¹ = 1 := mul_nonsing_inv B hdet
  refine ⟨B, hdet, fun α h1 h2 => ⟨?_, ?_⟩, fun α β h1 h2 h3 h4 hab => ?_⟩
  · rw [mem_orthogonalGroup_iff']
    have hM := hinv α h1 h2
    rw [hB] at hM
    calc (B * M α * B⁻¹)ᵀ * (B * M α * B⁻¹)
        = B⁻¹ᵀ * ((M α)ᵀ * (Bᵀ * B) * M α) * B⁻¹ := by
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = B⁻¹ᵀ * (Bᵀ * B) * B⁻¹ := by rw [hM]
      _ = (B * B⁻¹)ᵀ * (B * B⁻¹) := by simp only [transpose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hBB']; simp
  · calc B * M α * B⁻¹ * (B * M α * B⁻¹) = B * (M α * (B⁻¹ * B) * M α) * B⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = -1 := by
          rw [hBB, Matrix.mul_one, h.sq α h1 h2, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
            hBB']
  · calc B * M α * B⁻¹ * (B * M β * B⁻¹) = B * (M α * (B⁻¹ * B) * M β) * B⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = B * (M α * M β) * B⁻¹ := by rw [hBB, Matrix.mul_one]
      _ = -(B * (M β * (B⁻¹ * B) * M α) * B⁻¹) := by
          rw [hBB, Matrix.mul_one, h.anti α β h1 h2 h3 h4 hab, Matrix.mul_neg, Matrix.neg_mul]
      _ = -(B * M β * B⁻¹ * (B * M α * B⁻¹)) := by simp only [Matrix.mul_assoc]

end Ortho

/-- **Orthogonalization**: a finite-dimensional real vector space with `k` anticommuting square
roots of `-1` is isomorphic, compatibly with them, to `ℝ^d` with `k` anticommuting complex
structures (orthogonal), `d = dim V`. -/
theorem ortho_glue {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {J : ℕ → Module.End ℝ V} {k : ℕ} (h : Morse.IsClifford J k) :
    ∃ (Js : ℕ → Matrix (Fin (finrank ℝ V)) (Fin (finrank ℝ V)) ℝ)
      (E : V ≃ₗ[ℝ] (Fin (finrank ℝ V) → ℝ)),
      Morse.IsAnticommFamily Js k ∧ ∀ α, 1 ≤ α → α ≤ k → ∀ v, E (J α v) = Js α *ᵥ E v := by
  set b := Module.finBasis ℝ V
  set M : ℕ → Matrix (Fin (finrank ℝ V)) (Fin (finrank ℝ V)) ℝ :=
    fun α => LinearMap.toMatrix b b (J α)
  have hM : Morse.IsClifford M k := by
    refine ⟨fun a h1 h2 => ?_, fun a c h1 h2 h3 h4 hac => ?_⟩
    · simp only [M]
      rw [← LinearMap.toMatrix_mul, h.sq a h1 h2, map_neg, LinearMap.toMatrix_one]
    · simp only [M]
      rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, h.anti a c h1 h2 h3 h4 hac, map_neg]
  obtain ⟨P, hP, hfam⟩ := exists_conj_orth hM
  let hPi := P.invertibleOfIsUnitDet hP
  have hE2 : ∀ x, (Matrix.toLinearEquiv' P hPi) x = P *ᵥ x := fun x => rfl
  refine ⟨_, b.equivFun.trans (Matrix.toLinearEquiv' P hPi), hfam, fun α h1 h2 v => ?_⟩
  simp only [LinearEquiv.trans_apply, Module.Basis.equivFun_apply, hE2]
  rw [← LinearMap.toMatrix_mulVec_repr b b (J α) v, mulVec_mulVec, mulVec_mulVec,
    Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul P hP, Matrix.mul_one]

/-- Minimality transfers along an isomorphism compatible with the structures. -/
theorem minimal_transfer {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {J : ℕ → Module.End ℝ V} {J' : ℕ → Module.End ℝ W} {k : ℕ} (E : V ≃ₗ[ℝ] W)
    (hE : ∀ α, 1 ≤ α → α ≤ k → ∀ v, E (J α v) = J' α (E v))
    (hW : ∀ S : Submodule ℝ W, (∀ α, 1 ≤ α → α ≤ k → ∀ w ∈ S, J' α w ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∀ S : Submodule ℝ V, (∀ α, 1 ≤ α → α ≤ k → ∀ v ∈ S, J α v ∈ S) → S = ⊥ ∨ S = ⊤ := by
  intro S hS
  have hinv : ∀ α, 1 ≤ α → α ≤ k → ∀ w ∈ S.map (E : V →ₗ[ℝ] W), J' α w ∈ S.map (E : V →ₗ[ℝ] W) := by
    rintro α h1 h2 _ ⟨v, hv, rfl⟩
    exact ⟨J α v, hS α h1 h2 v hv, hE α h1 h2 v⟩
  have hc : S = (S.map (E : V →ₗ[ℝ] W)).comap (E : V →ₗ[ℝ] W) :=
    (Submodule.comap_map_eq_of_injective E.injective S).symm
  rcases hW _ hinv with h | h
  · left; rw [hc, h, Submodule.comap_bot]; exact LinearMap.ker_eq_bot.2 E.injective
  · right; rw [hc, h, Submodule.comap_top]

theorem intertwine_symm {V W : Type} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {J : ℕ → Module.End ℝ V} {J' : ℕ → Module.End ℝ W} {k : ℕ} (E : V ≃ₗ[ℝ] W)
    (hE : ∀ α, 1 ≤ α → α ≤ k → ∀ v, E (J α v) = J' α (E v)) :
    ∀ α, 1 ≤ α → α ≤ k → ∀ w, E.symm (J' α w) = J α (E.symm w) := by
  intro α h1 h2 w
  rw [LinearEquiv.symm_apply_eq, hE α h1 h2, LinearEquiv.apply_symm_apply]

end Glue

open Glue

/-! ## Vocabulary -/

theorem isACFam_iff {ι : Type} [Fintype ι] [DecidableEq ι] (Js : ℕ → Mat ι) (k : ℕ) :
    IsACFam Js k ↔ Morse.IsAnticommFamily Js k :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.cs, h.anti⟩⟩

/-- The structures of a matrix family, as endomorphisms of `ℝⁿ`. -/
abbrev lin {n : ℕ} (Js : ℕ → Mat (Fin n)) : ℕ → Module.End ℝ (Fin n → ℝ) :=
  fun α => Matrix.toLinAlgEquiv' (Js α)

/-- B's minimal spaces are the project's minimal Clifford modules `ℝⁿ`. -/
theorem isMinimal_of_minACSp {n k : ℕ} {Js : ℕ → Mat (Fin n)} (h : IsMinACSp Js k) :
    Morse.IsClifford (lin Js) k ∧ Morse.IsMinimalCliffordModule (lin Js) k := by
  obtain ⟨hne, hfam, hmin⟩ := h
  refine ⟨((isACFam_iff Js k).1 hfam).isClifford_toLin', ?_, fun W hW => hmin W fun α h1 h2 v hv => ?_⟩
  · have := hne; infer_instance
  · exact hW α h1 h2 v hv

theorem minACSp_of_isMinimal {n k : ℕ} {Js : ℕ → Mat (Fin n)} (hfam : Morse.IsAnticommFamily Js k)
    (hmin : Morse.IsMinimalCliffordModule (lin Js) k) : IsMinACSp Js k := by
  obtain ⟨hnt, hmin⟩ := hmin
  refine ⟨?_, (isACFam_iff Js k).2 hfam, fun W hW => hmin W fun α h1 h2 v hv => hW α h1 h2 v hv⟩
  by_contra hc
  rw [not_nonempty_iff] at hc
  obtain ⟨x, y, hxy⟩ := hnt
  exact hxy (funext fun i => isEmptyElim i)

/-! ## Matrix lemmas -/

section MatLemmas
variable {n : ℕ}

theorem kerM_neg (X : Mat (Fin n)) : kerM (-X) = kerM X := by
  ext v; simp [kerM]

theorem kerM_mul_left {U X : Mat (Fin n)} (hU : U * U = -1) : kerM (U * X) = kerM X := by
  ext v
  simp only [kerM, LinearMap.mem_ker, Matrix.mulVecLin_apply, ← mulVec_mulVec]
  refine ⟨fun h => ?_, fun h => by rw [h, mulVec_zero]⟩
  have := congrArg (fun w => U *ᵥ w) h
  simp only [mulVec_mulVec, mulVec_zero] at this
  rwa [← Matrix.mul_assoc, hU, Matrix.neg_mul, Matrix.one_mul, neg_mulVec, neg_eq_zero] at this

theorem stab_of_comm {X A : Mat (Fin n)} (h : X * A = A * X) : Stab A (kerM X) := by
  intro v hv
  simp only [kerM, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
  rw [mulVec_mulVec, h, ← mulVec_mulVec, hv, mulVec_zero]

theorem sup_top_of_sq {θ : Mat (Fin n)} (hθ : θ * θ = 1) : kerM (θ + 1) ⊔ kerM (θ - 1) = ⊤ := by
  refine eq_top_iff.2 fun v _ => Submodule.mem_sup.2 ⟨(1 / 2 : ℝ) • (v - θ *ᵥ v), ?_,
    (1 / 2 : ℝ) • (v + θ *ᵥ v), ?_, ?_⟩
  · simp only [kerM, LinearMap.mem_ker, Matrix.mulVecLin_apply, mulVec_smul, mulVec_sub,
      mulVec_mulVec, Matrix.add_mul, hθ, Matrix.one_mul, add_mulVec, one_mulVec]
    ext i; simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul]; ring
  · simp only [kerM, LinearMap.mem_ker, Matrix.mulVecLin_apply, mulVec_smul, mulVec_add,
      mulVec_mulVec, Matrix.sub_mul, hθ, Matrix.one_mul, sub_mulVec, one_mulVec]
    ext i; simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul]; ring
  · ext i; simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]; ring

/-- The two eigenspaces of an involution `θ` anticommuting with an invertible `P` have half the
dimension (the project's halving lemma `finrank_eq_two_mul_of_anticomm`). -/
theorem finrank_halves {θ P : Mat (Fin n)} (hθ : θ * θ = 1) (hP : P * P = -1)
    (hPθ : P * θ = -(θ * P)) :
    n = 2 * finrank ℝ (kerM (θ - 1)) ∧ n = 2 * finrank ℝ (kerM (θ + 1)) := by
  have hinj : Function.Injective (Matrix.toLinAlgEquiv' P) :=
    Morse.injective_of_mul_self_eq_neg_one (by rw [← map_mul, hP, map_neg, map_one])
  have h1 := Morse.finrank_eq_two_mul_of_anticomm (Matrix.toLinAlgEquiv' θ)
    (Matrix.toLinAlgEquiv' P) (by rw [← map_mul, hθ, map_one]) hinj
    (by rw [← map_mul, ← map_mul, hPθ, map_neg])
  have h2 := Morse.finrank_eq_two_mul_of_anticomm (Matrix.toLinAlgEquiv' (-θ))
    (Matrix.toLinAlgEquiv' P) (by rw [← map_mul, neg_mul_neg, hθ, map_one]) hinj
    (by rw [← map_mul, ← map_mul, Matrix.mul_neg, Matrix.neg_mul, hPθ, map_neg])
  rw [finrank_fin_fun] at h1 h2
  have e1 : kerM (θ - 1) = LinearMap.ker (Matrix.toLinAlgEquiv' θ - 1) := by
    rw [← map_one Matrix.toLinAlgEquiv', ← map_sub]; rfl
  have e2 : kerM (θ + 1) = LinearMap.ker (Matrix.toLinAlgEquiv' (-θ) - 1) := by
    rw [← kerM_neg, ← map_one Matrix.toLinAlgEquiv', ← map_sub, neg_add']; rfl
  exact ⟨e1 ▸ h1, e2 ▸ h2⟩

/-- A central involution acting by `±1` (module form) is `±1` as a matrix. -/
theorem eq_one_of_forall {θ : Mat (Fin n)} (h : ∀ v, Matrix.toLinAlgEquiv' θ v = v) : θ = 1 := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_one]; exact LinearMap.ext fun v => h v

theorem eq_neg_one_of_forall {θ : Mat (Fin n)} (h : ∀ v, Matrix.toLinAlgEquiv' θ v = -v) :
    θ = -1 := by
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_neg, map_one]; exact LinearMap.ext fun v => by simpa using h v

end MatLemmas

theorem mTab_eq (k : Fin 9) : mTab k = Morse.milnorM k := by
  fin_cases k <;> rfl

theorem comm_add_one {n : ℕ} {θ A : Mat (Fin n)} (h : Commute θ A) : (θ + 1) * A = A * (θ + 1) :=
  (h.add_left (Commute.one_left A)).eq

theorem comm_sub_one {n : ℕ} {θ A : Mat (Fin n)} (h : Commute θ A) : (θ - 1) * A = A * (θ - 1) :=
  (h.sub_left (Commute.one_left A)).eq

/-! ## A ⇒ B -/

/-- B's claim 1, from A's `finrank_eq_milnorM_of_isMinimal`. -/
theorem dim_of_A (hA : A) {k : ℕ} (hk : k ≤ 8) {n : ℕ} {Js : ℕ → Mat (Fin n)}
    (h : IsMinACSp Js k) : n = Morse.milnorM k := by
  obtain ⟨hc, hm⟩ := isMinimal_of_minACSp h
  have := hA.1 hk hc hm
  rwa [finrank_fin_fun] at this

/-- A central involution `θ` (a word in the `J_α`, `θ² = 1`, commuting with `J_1, …, J_k`) is `±1`
on a minimal space: A's `central_involution`, read back as a matrix identity. -/
theorem central_of_A (hA : A) {n k : ℕ} {Js : ℕ → Mat (Fin n)} (h : IsMinACSp Js k)
    {θ : Mat (Fin n)} (hsq : θ * θ = 1) (hc : ∀ α, 1 ≤ α → α ≤ k → Commute θ (Js α)) :
    θ = 1 ∨ θ = -1 := by
  obtain ⟨-, hm⟩ := isMinimal_of_minACSp h
  rcases hA.2.2.2.2.1 hm (θ := Matrix.toLinAlgEquiv' θ) (by rw [← map_mul, hsq, map_one])
      (fun α h1 h2 => (hc α h1 h2).map (Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin n))) with h1 | h1
  · exact Or.inl (eq_one_of_forall h1)
  · exact Or.inr (eq_neg_one_of_forall h1)

/-- A ⇒ B. Claim 1 is A's `finrank_eq_milnorM_of_isMinimal`; `J_3 = ±J_1J_2` (`k = 3`) and
`J_7 = ±J_1⋯J_6` (`k = 7`) are A's `central_involution` applied to `θ₃ = J_1J_2J_3`,
`ω₇ = J_1⋯J_7`; the descriptions `H ⊕ H'` (`k = 4, 5, 6`) and `L ⊕ L'` (`k = 8`) are the `∓1`
eigenspaces of `θ₃` resp. `ω₇` (`ker(J_3 ∓ J_1J_2) = ker(θ₃ ± 1)`, `ker(J_7 ∓ J_1⋯J_6) = ker(ω₇ ± 1)`),
of equal dimension because `J_4` resp. `J_8` anticommutes with the involution (the project's
halving lemma), with the total dimension `8` resp. `16` from A. -/
theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun k n Js h => ?_, fun n Js h => ?_, fun k n Js hk4 hk6 h => ?_, fun n Js h => ?_,
    fun n Js h => ?_⟩
  · rw [mTab_eq]; exact dim_of_A hA (by omega) h
  · -- k = 3
    have hM : Morse.IsClifford Js 3 := ((isACFam_iff Js 3).1 h.2.1).isClifford
    obtain ⟨hsq, hc1, hc2, hc3⟩ := Morse.θ₃_spec hM
    have hJ3 : Js 3 = -(Js 1 * Js 2 * Morse.θ₃ Js) := by unfold Morse.θ₃; clifford_simp hM
    rcases central_of_A hA h hsq (fun α h1 h2 => by interval_cases α <;> assumption) with h1 | h1
    · right; rw [hJ3, h1, Matrix.mul_one]
    · left; rw [hJ3, h1, Matrix.mul_neg, Matrix.mul_one, neg_neg]
  · -- k = 4, 5, 6
    have hn : n = 8 := by
      have := dim_of_A hA (by omega) h
      interval_cases k <;> simpa [Morse.milnorM] using this
    have hM : Morse.IsClifford Js k := ((isACFam_iff Js k).1 h.2.1).isClifford
    have hM4 : Morse.IsClifford Js 4 := hM.mono hk4
    obtain ⟨hsq, hc1, hc2, -⟩ := Morse.θ₃_spec (hM4.mono (by norm_num))
    have hanti : Js 4 * Morse.θ₃ Js = -(Morse.θ₃ Js * Js 4) := by
      unfold Morse.θ₃; clifford_simp hM4
    obtain ⟨hd1, hd2⟩ := finrank_halves hsq (hM4.sq 4 (by norm_num) le_rfl) hanti
    have hU : Js 1 * Js 2 * (Js 1 * Js 2) = -1 := by clifford_simp hM4
    have i1 : Js 1 * Js 2 * Morse.θ₃ Js = -Js 3 := by unfold Morse.θ₃; clifford_simp hM4
    have e1 : kerM (Js 3 - Js 1 * Js 2) = kerM (Morse.θ₃ Js + 1) := by
      rw [← kerM_neg, ← kerM_mul_left hU (X := Morse.θ₃ Js + 1), Matrix.mul_add, i1,
        Matrix.mul_one, neg_sub, sub_eq_neg_add]
    have e2 : kerM (Js 3 + Js 1 * Js 2) = kerM (Morse.θ₃ Js - 1) := by
      rw [← kerM_neg, ← kerM_mul_left hU (X := Morse.θ₃ Js - 1), Matrix.mul_sub, i1,
        Matrix.mul_one, neg_add']
    rw [e1, e2]
    refine ⟨by omega, by omega, sup_top_of_sq hsq, fun α h1 h2 => ?_⟩
    have hc : Commute (Morse.θ₃ Js) (Js α) := by interval_cases α <;> assumption
    exact ⟨stab_of_comm (comm_add_one hc), stab_of_comm (comm_sub_one hc)⟩
  · -- k = 7
    have hM : Morse.IsClifford Js 7 := ((isACFam_iff Js 7).1 h.2.1).isClifford
    obtain ⟨-, hc⟩ := Morse.ω₇_spec hM
    have hsq : Morse.ω₇ Js * Morse.ω₇ Js = 1 := by unfold Morse.ω₇; clifford_simp hM
    have hJ7 : Js 7 = -(P6 Js * Morse.ω₇ Js) := by unfold P6 Morse.ω₇; clifford_simp hM
    rcases central_of_A hA h hsq hc with h1 | h1
    · right; rw [hJ7, h1, Matrix.mul_one]
    · left; rw [hJ7, h1, Matrix.mul_neg, Matrix.mul_one, neg_neg]
  · -- k = 8
    have hn : n = 16 := by simpa [Morse.milnorM] using dim_of_A hA le_rfl h
    have hM : Morse.IsClifford Js 8 := ((isACFam_iff Js 8).1 h.2.1).isClifford
    obtain ⟨-, hc⟩ := Morse.ω₇_spec (hM.mono (by norm_num))
    have hsq : Morse.ω₇ Js * Morse.ω₇ Js = 1 := by unfold Morse.ω₇; clifford_simp hM
    have hanti : Js 8 * Morse.ω₇ Js = -(Morse.ω₇ Js * Js 8) := by
      unfold Morse.ω₇; clifford_simp hM
    obtain ⟨hd1, hd2⟩ := finrank_halves hsq (hM.sq 8 (by norm_num) le_rfl) hanti
    have hU : P6 Js * P6 Js = -1 := by unfold P6; clifford_simp hM
    have i1 : P6 Js * Morse.ω₇ Js = -Js 7 := by unfold P6 Morse.ω₇; clifford_simp hM
    have e1 : kerM (Js 7 - P6 Js) = kerM (Morse.ω₇ Js + 1) := by
      rw [← kerM_neg, ← kerM_mul_left hU (X := Morse.ω₇ Js + 1), Matrix.mul_add, i1,
        Matrix.mul_one, neg_sub, sub_eq_neg_add]
    have e2 : kerM (Js 7 + P6 Js) = kerM (Morse.ω₇ Js - 1) := by
      rw [← kerM_neg, ← kerM_mul_left hU (X := Morse.ω₇ Js - 1), Matrix.mul_sub, i1,
        Matrix.mul_one, neg_add']
    rw [e1, e2]
    refine ⟨by omega, by omega, sup_top_of_sq hsq, fun α h1 h2 => ?_⟩
    exact ⟨stab_of_comm (comm_add_one (hc α h1 h2)), stab_of_comm (comm_sub_one (hc α h1 h2))⟩

/-! ## B ⇒ A -/

/-- An abstract finite-dimensional minimal `(J_1, …, J_k)`-space is, after orthogonalization, one
of B's minimal spaces `ℝ^d` (`d = dim V`), by a compatible isomorphism. -/
theorem transfer_min {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {J : ℕ → Module.End ℝ V} {k : ℕ} (h : Morse.IsClifford J k)
    (hmin : Morse.IsMinimalCliffordModule J k) :
    ∃ (Js : ℕ → Mat (Fin (finrank ℝ V))) (E : V ≃ₗ[ℝ] (Fin (finrank ℝ V) → ℝ)),
      IsMinACSp Js k ∧ ∀ α, 1 ≤ α → α ≤ k → ∀ v, E (J α v) = Js α *ᵥ E v := by
  obtain ⟨Js, E, hfam, hE⟩ := ortho_glue h
  refine ⟨Js, E, minACSp_of_isMinimal hfam ⟨?_, ?_⟩, hE⟩
  · have := hmin.1; exact E.symm.toEquiv.nontrivial
  · exact minimal_transfer (J := lin Js) (J' := J) E.symm
      (intertwine_symm (J' := lin Js) E hE) hmin.2

/-- A's first claim from B's claim 1 (via orthogonalization). -/
theorem finrank_of_B (hB : B) {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {J : ℕ → Module.End ℝ V} {k : ℕ} (hk : k ≤ 8) (h : Morse.IsClifford J k)
    (hmin : Morse.IsMinimalCliffordModule J k) : finrank ℝ V = Morse.milnorM k := by
  obtain ⟨Js, -, hJs, -⟩ := transfer_min h hmin
  have := hB.1 ⟨k, by omega⟩ _ Js hJs
  rwa [mTab_eq] at this

/-- From B: every non-zero `(J_1, …, J_k)`-space (`k ≤ 8`) has dimension `≥ milnorM k` (it contains
a minimal one; induction on the dimension). -/
theorem le_finrank_of_B (hB : B) {k : ℕ} (hk : k ≤ 8) : ∀ (d : ℕ) {V : Type} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] {J : ℕ → Module.End ℝ V}, finrank ℝ V = d →
    Morse.IsClifford J k → Nontrivial V → Morse.milnorM k ≤ finrank ℝ V := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro V _ _ _ J hd h hnt
    by_cases hmin : ∀ S : Submodule ℝ V, (∀ α, 1 ≤ α → α ≤ k → ∀ v ∈ S, J α v ∈ S) →
        S = ⊥ ∨ S = ⊤
    · exact (finrank_of_B hB hk h ⟨hnt, hmin⟩).ge
    · push Not at hmin
      obtain ⟨S, hS, hbot, htop⟩ := hmin
      obtain ⟨J', hJ'⟩ := h.exists_restrict S hS
      have hlt := Submodule.finrank_lt htop
      have := ih (finrank ℝ S) (hd ▸ hlt) rfl hJ' (Submodule.nontrivial_iff_ne_bot.2 hbot)
      omega

/-- A minimal space (any dimension a priori) is finite-dimensional: it is the image of `C_k`. -/
theorem finite_of_minimal {V : Type} [AddCommGroup V] [Module ℝ V] {J : ℕ → Module.End ℝ V}
    {k : ℕ} (h : Morse.IsClifford J k) (hmin : Morse.IsMinimalCliffordModule J k) :
    FiniteDimensional ℝ V := by
  have := hmin.1
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  exact Module.Finite.of_surjective (Morse.cyclicMap h u)
    (LinearMap.range_eq_top.1 (Morse.range_cyclicMap_eq_top h hmin hu))

/-- B ⇒ A. A's dimension statements are B's claim 1 after orthogonalizing the abstract space
(`ortho_glue`, averaging the inner product); "dimension `m_k` ⇒ minimal" follows since every
non-zero `(J_1, …, J_k)`-space contains a minimal one (dimension induction). `minimal_three` and
`minimal_seven` come from B's `J_3 = ±J_1J_2`, `J_7 = ±J_1⋯J_6`, pulled back along the
orthogonalizing isomorphism (a minimal space is finite-dimensional, being the image of `C_k`:
`Morse.range_cyclicMap_eq_top`, a lemma outside this item). `central_involution` (any `k`, any
involution commuting with the `J_α`) is not in B — B only has its two instances `k = 3, 7` — and is
re-proved outright (the project's five-line argument: `ker(θ − 1)` is invariant). -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨@fun k V _ _ _ J hk h hmin => finrank_of_B hB hk h hmin,
    @fun V _ _ _ J k hk h hdim => ?_, @fun V _ _ _ J k hk h hmin => ?_,
    @fun V _ _ _ J k hk h hmin => finrank_of_B hB (by omega) h hmin,
    @fun k V _ _ J θ hmin hθ hc => ?_, @fun V _ _ J h hmin => ?_, @fun V _ _ J h hmin => ?_⟩
  · -- dimension `m_k` ⇒ minimal
    have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (hdim ▸ Morse.milnorM_pos k)
    refine ⟨hnt, fun S hS => ?_⟩
    by_cases hbot : S = ⊥
    · exact Or.inl hbot
    · obtain ⟨J', hJ'⟩ := h.exists_restrict S hS
      have := le_finrank_of_B hB hk _ rfl hJ' (Submodule.nontrivial_iff_ne_bot.2 hbot)
      exact Or.inr (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le S)
        (by omega)))
  · have := finrank_of_B hB hk h hmin
    refine ⟨this.ge, ?_⟩
    rw [this]
    interval_cases k <;> simp [Morse.milnorM]
  · -- `central_involution`, outright
    have hθv : ∀ v, θ (θ v) = v := fun v => by
      rw [← Module.End.mul_apply, hθ, Module.End.one_apply]
    rcases hmin.2 (LinearMap.ker (θ - 1))
        (fun α h1 h2 w hw => Morse.mapsTo_ker_of_commute (hc α h1 h2).eq.symm hw) with hbot | htop
    · right
      intro v
      have hmem : v + θ v ∈ LinearMap.ker (θ - 1) := by
        rw [Morse.mem_ker_sub_one_iff, map_add, hθv, add_comm]
      rw [hbot, Submodule.mem_bot] at hmem
      exact eq_neg_of_add_eq_zero_right hmem
    · left
      intro v
      have : v ∈ LinearMap.ker (θ - 1) := htop ▸ Submodule.mem_top
      exact (Morse.mem_ker_sub_one_iff _ _).1 this
  · -- `minimal_three`, from B's `J_3 = ±J_1J_2`
    have := finite_of_minimal h hmin
    obtain ⟨Js, E, hJs, hE⟩ := transfer_min h hmin
    have h3 : (∀ v, J 3 v = J 1 (J 2 v)) ∨ ∀ v, J 3 v = -J 1 (J 2 v) := by
      rcases hB.2.1 _ Js hJs with h' | h'
      · left; intro v; apply E.injective
        rw [hE 3 (by norm_num) le_rfl, h', ← mulVec_mulVec, ← hE 2 (by norm_num) (by norm_num),
          ← hE 1 le_rfl (by norm_num)]
      · right; intro v; apply E.injective
        rw [hE 3 (by norm_num) le_rfl, h', neg_mulVec, ← mulVec_mulVec,
          ← hE 2 (by norm_num) (by norm_num), ← hE 1 le_rfl (by norm_num), map_neg]
    refine ⟨hmin.1, fun S hS => hmin.2 S fun α h1 h2 v hv => ?_⟩
    rcases (by omega : α ≤ 2 ∨ α = 3) with hα | rfl
    · exact hS α h1 hα v hv
    · have h12 : J 1 (J 2 v) ∈ S := hS 1 le_rfl (by norm_num) _ (hS 2 (by norm_num) le_rfl v hv)
      rcases h3 with h3 | h3
      · rw [h3]; exact h12
      · rw [h3]; exact S.neg_mem h12
  · -- `minimal_seven`, from B's `J_7 = ±J_1⋯J_6`
    have := finite_of_minimal h hmin
    obtain ⟨Js, E, hJs, hE⟩ := transfer_min h hmin
    set w : V → V := fun v => J 1 (J 2 (J 3 (J 4 (J 5 (J 6 v)))))
    have hw : ∀ v, P6 Js *ᵥ E v = E (w v) := fun v => by
      simp only [P6, ← mulVec_mulVec, w]
      rw [← hE 6 (by norm_num) (by norm_num), ← hE 5 (by norm_num) (by norm_num),
        ← hE 4 (by norm_num) (by norm_num), ← hE 3 (by norm_num) (by norm_num),
        ← hE 2 (by norm_num) (by norm_num), ← hE 1 le_rfl (by norm_num)]
    have h7 : (∀ v, J 7 v = w v) ∨ ∀ v, J 7 v = -w v := by
      rcases hB.2.2.2.1 _ Js hJs with h' | h'
      · left; intro v; apply E.injective
        rw [hE 7 (by norm_num) le_rfl, h', hw]
      · right; intro v; apply E.injective
        rw [hE 7 (by norm_num) le_rfl, h', neg_mulVec, hw, map_neg]
    refine ⟨hmin.1, fun S hS => hmin.2 S fun α h1 h2 v hv => ?_⟩
    rcases (by omega : α ≤ 6 ∨ α = 7) with hα | rfl
    · exact hS α h1 hα v hv
    · have hwS : w v ∈ S := by
        simp only [w]
        refine hS 1 le_rfl (by norm_num) _ (hS 2 (by norm_num) (by norm_num) _
          (hS 3 (by norm_num) (by norm_num) _ (hS 4 (by norm_num) (by norm_num) _
          (hS 5 (by norm_num) (by norm_num) _ (hS 6 (by norm_num) le_rfl v hv)))))
      rcases h7 with h7 | h7
      · rw [h7]; exact hwS
      · rw [h7]; exact S.neg_mem hwS

#rt_check RoundTrip.V15_16.A_to_B [Morse.finrank_eq_milnorM_of_isMinimal,
  Morse.isMinimal_of_finrank_eq_milnorM, Morse.milnorM_le_finrank_le,
  Morse.finrank_eq_milnorM_of_le_two, Morse.central_involution, Morse.minimal_three,
  Morse.minimal_seven]
#rt_check RoundTrip.V15_16.B_to_A [Morse.finrank_eq_milnorM_of_isMinimal,
  Morse.isMinimal_of_finrank_eq_milnorM, Morse.milnorM_le_finrank_le,
  Morse.finrank_eq_milnorM_of_le_two, Morse.central_involution, Morse.minimal_three,
  Morse.minimal_seven]
#rt_overlap RoundTrip.V15_16.B_to_A [Morse.finrank_eq_milnorM_of_isMinimal,
  Morse.isMinimal_of_finrank_eq_milnorM, Morse.milnorM_le_finrank_le,
  Morse.finrank_eq_milnorM_of_le_two, Morse.central_involution, Morse.minimal_three,
  Morse.minimal_seven]
end RoundTrip.V15_16
