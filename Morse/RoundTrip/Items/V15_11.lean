import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_11

open Matrix Module
open scoped Matrix.Norms.Elementwise

namespace RoundTrip.V15_11

set_option linter.unusedSimpArgs false

/-- The project's statement (universes instantiated at `0`, any finite index type, any `k` and
`1 ≤ a < b ≤ k`): `J ↦ θ = J_aJ_bJ` maps `Ω_{k+1}(n)` into the symmetric orthogonal involutions
commuting with `J_a, J_b` and anticommuting with the other `J_c`, `c ≤ k`; conversely such a `θ`
gives `J_bJ_aθ ∈ Ω_{k+1}(n)` with `J_aJ_b(J_bJ_aθ) = θ`; and `J_bJ_a(J_aJ_bJ') = J'`. -/
def A : Prop :=
  type_of% @Morse.theta_of_mem_omega.{0} ∧ type_of% @Morse.mem_omega_of_theta.{0} ∧
    type_of% @Morse.mul_theta_mul.{0}

theorem A_holds : A :=
  ⟨@Morse.theta_of_mem_omega.{0}, @Morse.mem_omega_of_theta.{0}, @Morse.mul_theta_mul.{0}⟩

/-! ### B ⇒ A: vacuous

A is a pure word computation valid for every `n`, `k` and `a < b ≤ k`; B only treats `ℝ^{16r}`,
the fixed pairs `(a, b) = (1, 2), (1, 4), (2, 4), (1, 6)` and `k = 2, 4, 5, 6`, and phrases the
result through subspaces (projections). A is re-proved outright (the project's `word_simp`
computations). -/

theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_⟩
  · intro n _ _ J k a b hJ ha hab hbk J' hJ'
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
      have h8 : J b * J c = -(J c * J b) :=
        hJ.anti b c (ha.trans hab.le) hbk hc hck (Ne.symm hcb)
      have h9 : J' * J c = -(J c * J') := by rw [ha' c hc hck, neg_neg]
      word_simp [h7, h8, h9]
  · intro n _ _ J k a b hJ ha hab hbk θ hθT hθ hθa hθb hθc
    have hJa := hJ.cs a ha (hab.le.trans hbk)
    have hJb := hJ.cs b (ha.trans hab.le) hbk
    have h1 : J a * J a = -1 := hJa.2
    have h2 : J b * J b = -1 := hJb.2
    have h4 : J b * J a = -(J a * J b) :=
      hJ.anti b a (ha.trans hab.le) hbk ha (hab.le.trans hbk) hab.ne'
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Morse.isComplexStructure_iff]
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
      have h8 : J b * J c = -(J c * J b) :=
        hJ.anti b c (ha.trans hab.le) hbk hc hck (Ne.symm hcb)
      have h9 := hθc c hc hck hca hcb
      word_simp [h7, h8, h9]
    · word_simp [h1, h2, h4]
  · intro n _ _ J k a b hJ ha hab hbk J'
    have h1 : J a * J a = -1 := (hJ.cs a ha (hab.le.trans hbk)).2
    have h2 : J b * J b = -1 := (hJ.cs b (ha.trans hab.le) hbk).2
    word_simp [h1, h2]

/-! ### A ⇒ B: not proved; what is proved

B asserts four homeomorphisms `Ω_k(16r) ≅ {subspaces}` (`k = 3, 5, 6, 7`) and `dim X = 2r`. A gives
the bijection `J ↔ θ` onto involutions with a prescribed commute/anticommute pattern; the missing
step is `involutions with that pattern ↔ subspaces of the stated kind`. For step (3) (no
anticommutation constraint) this is immediate — `θ ↦ (1 + θ)/2`, the orthogonal projection onto
`{θ = 1}` — and is proved below (`step3`, using A). For (5), (6), (7) the inverse map must
*reconstruct* `θ` on all of `ℝ^{16r}` from its `+1`-eigenspace inside `V₁`, `W`, `X` by
transporting it with `J_4` (resp. `J_2, J_4`; `J_1, J_2, J_4`) and then verify all the
commutation relations — this is Milnor's "it is not hard to see that `J_5` is uniquely determined",
"it can be shown that `J_7` is uniquely determined", which the project does not formalize (its
docstring: "Not formalized: the identification of the components of `Ω_k(16r)`, `k ≤ 7`, with
Grassmannians … (beyond the bijections above)"). `dim X = 2r` is proved below from the project's
halving lemmas (outside the item). -/

section Lin
variable {ι : Type} [Fintype ι] [DecidableEq ι]
set_option linter.unusedSectionVars false

theorem mem_eig1 (θ : Mat ι) (v : ι → ℝ) : v ∈ eig1 θ ↔ θ *ᵥ v = v := by
  simp [eig1, sub_eq_zero]

/-- For an involution, `(1 + θ)/2` projects onto `{θ = 1}`. -/
theorem rng_half (θ : Mat ι) (hθ : θ * θ = 1) :
    rng ((1 / 2 : ℝ) • (1 + θ)) = eig1 θ := by
  ext v
  simp only [rng, LinearMap.mem_range, Matrix.mulVecLin_apply, mem_eig1]
  constructor
  · rintro ⟨u, rfl⟩
    rw [mulVec_mulVec, Matrix.mul_smul, Matrix.mul_add, hθ, Matrix.mul_one, add_comm]
  · intro hv
    refine ⟨v, ?_⟩
    rw [smul_mulVec, add_mulVec, one_mulVec, hv]
    module

theorem img_le_iff_aux (M : Mat ι) (S : Submodule ℝ (ι → ℝ)) :
    img M S ≤ S ↔ ∀ v ∈ S, M *ᵥ v ∈ S := by
  refine ⟨fun h v hv => h ⟨v, hv, rfl⟩, fun h => ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

theorem ker_toLinAlgEquiv' (T : Mat ι) :
    LinearMap.ker (Matrix.toLinAlgEquiv' T - 1) = eig1 T := by
  ext v
  rw [LinearMap.mem_ker, mem_eig1, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    Matrix.toLinAlgEquiv'_apply]

end Lin

/-- Step (3) of B, from A: `Ω_3(16r)` is homeomorphic to the "quaternionic Grassmannian" of
(projections onto) subspaces closed under `J_1, J_2`, by `J ↦ (1 + J_1J_2J)/2`. -/
theorem step3 (hA : A) (r : ℕ) (Js : ℕ → Mat (Fin (16 * r))) (hJ : IsACFam Js 7) :
    ∃ h : ↥(OmegaK Js 3) ≃ₜ ↥(GrH Js), ∀ J : ↥(OmegaK Js 3),
      rng (h J : Mat (Fin (16 * r))) = eig1 (Js 1 * Js 2 * (J : Mat (Fin (16 * r)))) := by
  obtain ⟨hth, hom, hmul⟩ := hA
  have hJ2 : Morse.IsAnticommFamily Js 2 :=
    ⟨fun a h1 h2 => hJ.1 a h1 (by omega), fun a b h1 h2 h3 h4 => hJ.2 a b h1 (by omega) h3
      (by omega)⟩
  have hO : ∀ J, J ∈ OmegaK Js 3 ↔ J ∈ Morse.Omega Js 3 := fun J => by
    simp only [OmegaK, Morse.Omega, IsCplxStr, Morse.IsComplexStructure, AntiComm,
      Set.mem_ofPred_eq]
    exact and_congr Iff.rfl (forall_congr' fun α => forall_congr' fun _ => forall_congr' fun _ =>
      ⟨fun h => by rw [h, neg_neg], fun h => by rw [h, neg_neg]⟩)
  have hT1 : (Js 1)ᵀ = -Js 1 := Morse.IsComplexStructure.transpose (hJ.1 1 le_rfl (by norm_num))
  have hT2 : (Js 2)ᵀ = -Js 2 := Morse.IsComplexStructure.transpose (hJ.1 2 (by norm_num)
    (by norm_num))
  -- a projection whose range is `M`-invariant, `M` skew, commutes with `M`
  have comm_of_inv : ∀ (P M : Mat (Fin (16 * r))), IsProj P → Mᵀ = -M →
      img M (rng P) ≤ rng P → M * P = P * M := by
    intro P M ⟨hPT, hPP⟩ hMT hinv
    have h1 : P * M * P = M * P := by
      refine (Matrix.toLin' (R := ℝ)).injective (LinearMap.ext fun v => ?_)
      simp only [Matrix.toLin'_apply]
      obtain ⟨u, hu⟩ := hinv ⟨P *ᵥ v, ⟨v, rfl⟩, rfl⟩
      simp only [Matrix.mulVecLin_apply] at hu
      rw [← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← hu, mulVec_mulVec, hPP]
    have h2 : P * (M * P) = P * M := by
      have := congrArg Matrix.transpose h1
      simp only [transpose_mul, hPT, hMT, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at this
      simpa [Matrix.mul_assoc] using this
    calc M * P = P * M * P := h1.symm
      _ = P * (M * P) := Matrix.mul_assoc _ _ _
      _ = P * M := h2
  let f : ↥(OmegaK Js 3) → ↥(GrH Js) := fun J =>
    ⟨(1 / 2 : ℝ) • (1 + Js 1 * Js 2 * (J : Mat (Fin (16 * r)))), by
      obtain ⟨hT, hsq, hc1, hc2, -⟩ := hth hJ2 le_rfl one_lt_two le_rfl ((hO _).1 J.2)
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · rw [transpose_smul, transpose_add, transpose_one, hT]
      · simp only [smul_mul_smul_comm, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
          Matrix.mul_one, hsq]
        module
      · rw [rng_half _ hsq, img_le_iff_aux]
        exact fun v hv => by
          rw [mem_eig1] at hv ⊢
          rw [mulVec_mulVec, hc1, ← mulVec_mulVec, hv]
      · rw [rng_half _ hsq, img_le_iff_aux]
        exact fun v hv => by
          rw [mem_eig1] at hv ⊢
          rw [mulVec_mulVec, hc2, ← mulVec_mulVec, hv]⟩
  have hθP : ∀ P : ↥(GrH Js), ((2 : ℝ) • (P : Mat (Fin (16 * r))) - 1)ᵀ =
        (2 : ℝ) • (P : Mat (Fin (16 * r))) - 1 ∧
      ((2 : ℝ) • (P : Mat (Fin (16 * r))) - 1) * ((2 : ℝ) • (P : Mat (Fin (16 * r))) - 1) = 1 ∧
      ((2 : ℝ) • (P : Mat (Fin (16 * r))) - 1) * Js 1 = Js 1 * ((2 : ℝ) • (P : Mat (Fin (16 * r))) - 1) ∧
      ((2 : ℝ) • (P : Mat (Fin (16 * r))) - 1) * Js 2 =
        Js 2 * ((2 : ℝ) • (P : Mat (Fin (16 * r))) - 1) := by
    intro P
    obtain ⟨⟨hPT, hPP⟩, h1, h2⟩ := P.2
    have c1 := comm_of_inv _ _ ⟨hPT, hPP⟩ hT1 h1
    have c2 := comm_of_inv _ _ ⟨hPT, hPP⟩ hT2 h2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [transpose_sub, transpose_smul, transpose_one, hPT]
    · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, hPP,
        Matrix.one_mul, Matrix.mul_one, smul_smul]
      module
    · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, c1,
        Matrix.one_mul, Matrix.mul_one]
    · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, c2,
        Matrix.one_mul, Matrix.mul_one]
  let g : ↥(GrH Js) → ↥(OmegaK Js 3) := fun P =>
    ⟨Js 2 * Js 1 * ((2 : ℝ) • (P : Mat (Fin (16 * r))) - 1), by
      obtain ⟨hT, hsq, hc1, hc2⟩ := hθP P
      exact (hO _).2 (hom hJ2 le_rfl one_lt_two le_rfl hT hsq hc1 hc2
        (fun c h1 h2 h3 h4 => by omega)).1⟩
  have lin : Function.LeftInverse g f := by
    intro J
    apply Subtype.ext
    change Js 2 * Js 1 * ((2 : ℝ) • ((1 / 2 : ℝ) • (1 + Js 1 * Js 2 * (J : Mat (Fin (16 * r))))) - 1)
      = J
    rw [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul, add_sub_cancel_left]
    exact hmul hJ2 le_rfl one_lt_two le_rfl _
  have rin : Function.RightInverse g f := by
    intro P
    apply Subtype.ext
    obtain ⟨hT, hsq, hc1, hc2⟩ := hθP P
    have := (hom hJ2 le_rfl one_lt_two le_rfl hT hsq hc1 hc2 (fun c h1 h2 h3 h4 => by omega)).2
    change (1 / 2 : ℝ) • (1 + Js 1 * Js 2 * (Js 2 * Js 1 * ((2 : ℝ) • (P : Mat (Fin (16 * r))) - 1)))
      = P
    rw [this]
    module
  have cf : Continuous f := Continuous.subtype_mk (by fun_prop) _
  have cg : Continuous g := Continuous.subtype_mk (by fun_prop) _
  refine ⟨Homeomorph.mk ⟨f, g, lin, rin⟩ cf cg, fun J => ?_⟩
  obtain ⟨-, hsq, -⟩ := hth hJ2 le_rfl one_lt_two le_rfl ((hO _).1 J.2)
  exact rng_half _ hsq

/-- B's last claim, `dim X = 2r`, from the project's halving lemmas (outside the item). -/
theorem dimX (r : ℕ) (Js : ℕ → Mat (Fin (16 * r))) (hJ : IsACFam Js 7) :
    finrank ℝ (Xsp Js) = 2 * r := by
  have hJ' : Morse.IsAnticommFamily Js 7 := ⟨hJ.1, hJ.2⟩
  have hC := hJ'.isClifford_toLin'
  have s1 := Morse.finrank_eq_two_mul_eigV₁ (hC.mono (by norm_num))
  have s2 := Morse.finrank_eigV₁_eq (hC.mono (by norm_num))
  have s3 := Morse.finrank_eigW_eq (hC.mono (by norm_num))
  have k3 : Morse.eigV₁ (fun α => Matrix.toLinAlgEquiv' (Js α)) = V1 Js := by
    rw [Morse.eigV₁, Morse.θ₃, ← map_mul, ← map_mul, ker_toLinAlgEquiv']; rfl
  have k5 : Morse.eigW (fun α => Matrix.toLinAlgEquiv' (Js α)) = Wsp Js := by
    rw [Morse.eigW, k3, Morse.θ₅, ← map_mul, ← map_mul, ker_toLinAlgEquiv']; rfl
  have k6 : Morse.eigX (fun α => Matrix.toLinAlgEquiv' (Js α)) = Xsp Js := by
    rw [Morse.eigX, k5, Morse.θ₆, ← map_mul, ← map_mul, ker_toLinAlgEquiv']; rfl
  rw [k3] at s1 s2
  rw [k5] at s2 s3
  rw [k6] at s3
  rw [Module.finrank_fin_fun] at s1
  omega

/-- What of B is proved from A: step (3) and `dim X = 2r`. -/
theorem A_to_B_partial (hA : A) (r : ℕ) (Js : ℕ → Mat (Fin (16 * r))) (hJ : IsACFam Js 7) :
    (∃ h : ↥(OmegaK Js 3) ≃ₜ ↥(GrH Js), ∀ J : ↥(OmegaK Js 3),
      rng (h J : Mat (Fin (16 * r))) = eig1 (Js 1 * Js 2 * (J : Mat (Fin (16 * r))))) ∧
    Module.finrank ℝ (Xsp Js) = 2 * r :=
  ⟨step3 hA r Js hJ, dimX r Js hJ⟩

#rt_check RoundTrip.V15_11.A_to_B_partial [Morse.theta_of_mem_omega, Morse.mem_omega_of_theta,
  Morse.mul_theta_mul]
#rt_check RoundTrip.V15_11.B_to_A [Morse.theta_of_mem_omega, Morse.mem_omega_of_theta,
  Morse.mul_theta_mul]
#rt_overlap RoundTrip.V15_11.B_to_A [Morse.theta_of_mem_omega, Morse.mem_omega_of_theta,
  Morse.mul_theta_mul]

end RoundTrip.V15_11
