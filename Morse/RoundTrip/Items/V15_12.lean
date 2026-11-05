import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_12

open Matrix Module

namespace RoundTrip.V15_12

set_option linter.unusedSimpArgs false

/-- The project's statement (universes instantiated at `0`; `eigV₁`, `eigW`, `eigX`, `jointEigen`
are vocabulary: the nested joint `+1`-eigenspaces of `θ₃, θ₅, θ₆, θ₇` of an abstract `ℝ`-vector
space): the halving lemma (`θ² = 1`, `P` injective anticommuting with `θ` ⇒ `dim V = 2 dim{θ = 1}`);
for 8 abstract endomorphisms with the Clifford relations, `dim V = 2 dim V₁ = 4 dim W = 8 dim X =
16 dim X₁`; and for Milnor's explicit structures on `ℝ^{16r}`, `dim X₁ = r`, `dim X = 2r`,
`dim W = 4r`, `dim V₁ = 8r`. -/
def A : Prop :=
  type_of% @Morse.finrank_eq_two_mul_of_anticomm.{0} ∧ type_of% @Morse.finrank_chain.{0} ∧
    type_of% @Morse.finrank_eq_sixteen_mul.{0} ∧ type_of% @Morse.finrank_jointEigen_bott16r

theorem A_holds : A :=
  ⟨@Morse.finrank_eq_two_mul_of_anticomm.{0}, @Morse.finrank_chain.{0},
    @Morse.finrank_eq_sixteen_mul.{0}, @Morse.finrank_jointEigen_bott16r⟩

/-! ### Linear algebra of eigenspaces of matrices on `ℝ^ι` -/

section Lin
variable {ι : Type} [Fintype ι] [DecidableEq ι]
set_option linter.unusedSectionVars false

theorem mem_eig1 (θ : Mat ι) (v : ι → ℝ) : v ∈ eig1 θ ↔ θ *ᵥ v = v := by
  simp [eig1, sub_eq_zero]

theorem mem_eigm1 (θ : Mat ι) (v : ι → ℝ) : v ∈ eigm1 θ ↔ θ *ᵥ v = -v := by
  simp [eigm1, add_eq_zero_iff_eq_neg]

theorem img_le_iff (M : Mat ι) (S : Submodule ℝ (ι → ℝ)) :
    img M S ≤ S ↔ ∀ v ∈ S, M *ᵥ v ∈ S := by
  refine ⟨fun h v hv => h ⟨v, hv, rfl⟩, fun h => ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

theorem eig1_inv {M θ : Mat ι} (h : M * θ = θ * M) : ∀ v ∈ eig1 θ, M *ᵥ v ∈ eig1 θ := by
  intro v hv; rw [mem_eig1] at hv ⊢; rw [mulVec_mulVec, ← h, ← mulVec_mulVec, hv]

theorem eigm1_inv {M θ : Mat ι} (h : M * θ = θ * M) : ∀ v ∈ eigm1 θ, M *ᵥ v ∈ eigm1 θ := by
  intro v hv; rw [mem_eigm1] at hv ⊢; rw [mulVec_mulVec, ← h, ← mulVec_mulVec, hv, mulVec_neg]

theorem eig1_swap {M θ : Mat ι} (h : M * θ = -(θ * M)) : ∀ v ∈ eig1 θ, M *ᵥ v ∈ eigm1 θ := by
  intro v hv; rw [mem_eig1] at hv; rw [mem_eigm1]
  rw [mulVec_mulVec, show θ * M = -(M * θ) by rw [h, neg_neg], neg_mulVec, ← mulVec_mulVec, hv]

theorem eigm1_swap {M θ : Mat ι} (h : M * θ = -(θ * M)) : ∀ v ∈ eigm1 θ, M *ᵥ v ∈ eig1 θ := by
  intro v hv; rw [mem_eigm1] at hv; rw [mem_eig1]
  rw [mulVec_mulVec, show θ * M = -(M * θ) by rw [h, neg_neg], neg_mulVec, ← mulVec_mulVec, hv,
    mulVec_neg, neg_neg]

theorem inf_inv {S T : Submodule ℝ (ι → ℝ)} {M : Mat ι} (hS : ∀ v ∈ S, M *ᵥ v ∈ S)
    (hT : ∀ v ∈ T, M *ᵥ v ∈ T) : ∀ v ∈ S ⊓ T, M *ᵥ v ∈ S ⊓ T :=
  fun v hv => ⟨hS v hv.1, hT v hv.2⟩

/-- Eigenspaces of a symmetric matrix for `+1` and `-1` are orthogonal. -/
theorem perp_eig {θ : Mat ι} (hT : θᵀ = θ) {S T : Submodule ℝ (ι → ℝ)} (hS : S ≤ eig1 θ)
    (hT' : T ≤ eigm1 θ) : Perp S T := by
  intro v hv w hw
  have h1 := (mem_eig1 θ v).1 (hS hv)
  have h2 := (mem_eigm1 θ w).1 (hT' hw)
  have : v ⬝ᵥ (θ *ᵥ w) = (θ *ᵥ v) ⬝ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hT]
  rw [h1, h2, dotProduct_neg] at this
  linarith

theorem disj_eig {θ : Mat ι} {S T : Submodule ℝ (ι → ℝ)} (hS : S ≤ eig1 θ) (hT : T ≤ eigm1 θ) :
    S ⊓ T = ⊥ := by
  rw [eq_bot_iff]
  intro v ⟨h1, h2⟩
  have e1 := (mem_eig1 θ v).1 (hS h1)
  have e2 := (mem_eigm1 θ v).1 (hT h2)
  rw [e1] at e2
  rw [Submodule.mem_bot]
  have : (2 : ℝ) • v = 0 := by rw [two_smul]; nth_rewrite 2 [e2]; exact add_neg_cancel v
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

/-- A `θ`-invariant subspace splits into its `±1`-eigenspaces (`θ² = 1`). -/
theorem split_eig {θ : Mat ι} (hθ : θ * θ = 1) (U : Submodule ℝ (ι → ℝ))
    (hU : ∀ v ∈ U, θ *ᵥ v ∈ U) : (U ⊓ eig1 θ) ⊔ (U ⊓ eigm1 θ) = U := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun v hv => ?_
  have hθv : θ *ᵥ (θ *ᵥ v) = v := by rw [mulVec_mulVec, hθ, one_mulVec]
  have h1 : (1 / 2 : ℝ) • (v + θ *ᵥ v) ∈ U ⊓ eig1 θ :=
    Submodule.mem_inf.2 ⟨U.smul_mem _ (U.add_mem hv (hU v hv)), by
      rw [mem_eig1, mulVec_smul, mulVec_add, hθv, add_comm]⟩
  have h2 : (1 / 2 : ℝ) • (v - θ *ᵥ v) ∈ U ⊓ eigm1 θ :=
    Submodule.mem_inf.2 ⟨U.smul_mem _ (U.sub_mem hv (hU v hv)), by
      rw [mem_eigm1, mulVec_smul, mulVec_sub, hθv, ← smul_neg, neg_sub]⟩
  have : v = (1 / 2 : ℝ) • (v + θ *ᵥ v) + (1 / 2 : ℝ) • (v - θ *ᵥ v) := by module
  rw [this]
  exact Submodule.add_mem_sup h1 h2

/-- An anticommuting `M` with `M² = -1` maps `U ∩ {θ = 1}` onto `U ∩ {θ = -1}`. -/
theorem img_swap {M θ : Mat ι} (hM : M * M = -1) (h : M * θ = -(θ * M))
    (U : Submodule ℝ (ι → ℝ)) (hU : ∀ v ∈ U, M *ᵥ v ∈ U) :
    img M (U ⊓ eig1 θ) = U ⊓ eigm1 θ := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨hU v hv.1, eig1_swap h v hv.2⟩
  · intro w hw
    refine ⟨-(M *ᵥ w), ⟨U.neg_mem (hU w hw.1), ?_⟩, ?_⟩
    · exact (eig1 θ).neg_mem (eigm1_swap h w hw.2)
    · simp only [Matrix.mulVecLin_apply, mulVec_neg, mulVec_mulVec, hM, neg_mulVec, one_mulVec,
        neg_neg]

theorem finrank_split {U S T : Submodule ℝ (ι → ℝ)} (hsup : S ⊔ T = U) (hinf : S ⊓ T = ⊥) :
    finrank ℝ U = finrank ℝ S + finrank ℝ T := by
  have := Submodule.finrank_sup_add_finrank_inf_eq S T
  rw [hsup, hinf, finrank_bot, add_zero] at this
  exact this

/-- The halving lemma inside an invariant subspace, from the hypothesis `hh` (A's first
conjunct) applied to the restrictions. -/
theorem halve (hh : type_of% @Morse.finrank_eq_two_mul_of_anticomm.{0})
    (U : Submodule ℝ (ι → ℝ)) {θ P : Mat ι} (hθ : θ * θ = 1) (hP : P * P = -1)
    (hPθ : P * θ = -(θ * P)) (hθU : ∀ v ∈ U, θ *ᵥ v ∈ U) (hPU : ∀ v ∈ U, P *ᵥ v ∈ U) :
    finrank ℝ U = 2 * finrank ℝ ↥(U ⊓ eig1 θ) := by
  let Θ : Module.End ℝ U := (Matrix.mulVecLin θ).restrict hθU
  let Pr : Module.End ℝ U := (Matrix.mulVecLin P).restrict hPU
  have hΘ : ∀ x : U, ((Θ x : U) : ι → ℝ) = θ *ᵥ (x : ι → ℝ) := fun x => rfl
  have hPr : ∀ x : U, ((Pr x : U) : ι → ℝ) = P *ᵥ (x : ι → ℝ) := fun x => rfl
  have h := hh Θ Pr
    (LinearMap.ext fun v => Subtype.ext (by
      rw [Module.End.mul_apply, hΘ, hΘ, mulVec_mulVec, hθ, one_mulVec]; rfl))
    (fun a b hab => by
      have h' := congrArg (fun x : U => P *ᵥ (x : ι → ℝ)) hab
      change P *ᵥ (P *ᵥ (a : ι → ℝ)) = P *ᵥ (P *ᵥ (b : ι → ℝ)) at h'
      rw [mulVec_mulVec, mulVec_mulVec, hP, neg_mulVec, neg_mulVec, one_mulVec, one_mulVec,
        neg_inj] at h'
      exact Subtype.ext h')
    (LinearMap.ext fun v => Subtype.ext (by
      change P *ᵥ (θ *ᵥ (v : ι → ℝ)) = -(θ *ᵥ (P *ᵥ (v : ι → ℝ)))
      rw [mulVec_mulVec, mulVec_mulVec, hPθ, neg_mulVec]))
  rw [h]
  congr 1
  have hmap : Submodule.map U.subtype (LinearMap.ker (Θ - 1)) = U ⊓ eig1 θ := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero, Submodule.mem_inf, Submodule.subtype_apply, mem_eig1]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, by rw [← hΘ]; exact congrArg Subtype.val hw⟩
    · rintro ⟨hU, hv⟩
      exact ⟨⟨v, hU⟩, Subtype.ext (by rw [hΘ]; exact hv), rfl⟩
  rw [← hmap, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ U.injective_subtype _)]

end Lin

/-! ### The relations, from `IsACFam` -/

theorem cliff {n : ℕ} {Js : ℕ → Mat (Fin n)} {m : ℕ} (h : IsACFam Js m) : Morse.IsClifford Js m :=
  ⟨fun a h1 h2 => (h.1 a h1 h2).2, h.2⟩

theorem tr {n : ℕ} {Js : ℕ → Mat (Fin n)} {m : ℕ} (h : IsACFam Js m) {a : ℕ} (h1 : 1 ≤ a)
    (h2 : a ≤ m) : (Js a)ᵀ = -Js a :=
  Morse.IsComplexStructure.transpose (h.1 a h1 h2)

/-- A ⇒ B. All dimension claims come from A's halving lemma (its first conjunct), applied
successively to `θ₃` on `ℝ^{16r}` (with `J_4`), `θ₅` on `V₁` (with `J_2`), `θ₆` on `W` (with
`J_1`), `θ₇` on `X` (with `J_7J_8`), plus `dim` of a direct sum. The splittings themselves
(orthogonality, `V₁ ⊔ V₂ = ⊤`, `W ⊔ J_2W = V₁`, …, invariance under `J_1, J_2`) are not in A
(A only states dimensions) and are proved here: eigenspaces of the symmetric involutions `θ`, and
`J_2W = V₁ ∩ {θ₅ = -1}` etc. -/
theorem trip_T {n : ℕ} {Js : ℕ → Mat (Fin n)} {m : ℕ} (h : IsACFam Js m) {a b c : ℕ}
    (ha : 1 ≤ a) (ha' : a ≤ m) (hb : 1 ≤ b) (hb' : b ≤ m) (hc : 1 ≤ c) (hc' : c ≤ m) :
    (Js a * Js b * Js c)ᵀ = -(Js c * (Js b * Js a)) := by
  rw [transpose_mul, transpose_mul, tr h ha ha', tr h hb hb', tr h hc hc']
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem mono {n : ℕ} {Js : ℕ → Mat (Fin n)} {m m' : ℕ} (hm : m ≤ m') (h : IsACFam Js m') :
    IsACFam Js m :=
  ⟨fun a h1 h2 => h.1 a h1 (h2.trans hm), fun a b h1 h2 h3 h4 => h.2 a b h1 (h2.trans hm) h3
    (h4.trans hm)⟩

theorem A_to_B : A → B := by
  rintro ⟨hh, -, -, -⟩
  intro r Js
  set t3 := Js 1 * Js 2 * Js 3 with ht3
  set t5 := Js 1 * Js 4 * Js 5 with ht5
  set t6 := Js 2 * Js 4 * Js 6 with ht6
  set t7 := Js 1 * Js 6 * Js 7 with ht7
  have eV1 : V1 Js = eig1 t3 := rfl
  have eV2 : V2 Js = eigm1 t3 := rfl
  have eW : Wsp Js = V1 Js ⊓ eig1 t5 := rfl
  have eX : Xsp Js = Wsp Js ⊓ eig1 t6 := rfl
  have eX1 : X1 Js = Xsp Js ⊓ eig1 t7 := rfl
  have eX2 : X2 Js = Xsp Js ⊓ eigm1 t7 := rfl
  -- the relations
  have R3 : IsACFam Js 3 → t3ᵀ = t3 ∧ t3 * t3 = 1 ∧ Js 1 * t3 = t3 * Js 1 ∧
      Js 2 * t3 = t3 * Js 2 := by
    intro h
    have hC := cliff h
    simp only [ht3, ht5, ht6, ht7]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [trip_T h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)]
      clifford_simp hC
    all_goals clifford_simp hC
  have R4 : IsACFam Js 4 → Js 4 * Js 4 = -1 ∧ Js 4 * t3 = -(t3 * Js 4) := by
    intro h
    have hC := cliff h
    exact ⟨(h.1 4 (by norm_num) le_rfl).2, by simp only [ht3]; clifford_simp hC⟩
  have R5 : IsACFam Js 5 → t5ᵀ = t5 ∧ t5 * t5 = 1 ∧ t5 * t3 = t3 * t5 ∧ Js 1 * t5 = t5 * Js 1 ∧
      Js 2 * t5 = -(t5 * Js 2) ∧ Js 2 * Js 2 = -1 := by
    intro h
    have hC := cliff h
    simp only [ht3, ht5, ht6, ht7]
    refine ⟨?_, ?_, ?_, ?_, ?_, (h.1 2 (by norm_num) (by norm_num)).2⟩
    · rw [trip_T h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)]
      clifford_simp hC
    all_goals clifford_simp hC
  have R6 : IsACFam Js 6 → t6ᵀ = t6 ∧ t6 * t6 = 1 ∧ t6 * t3 = t3 * t6 ∧ t6 * t5 = t5 * t6 ∧
      Js 1 * t6 = -(t6 * Js 1) ∧ Js 1 * Js 1 = -1 := by
    intro h
    have hC := cliff h
    simp only [ht3, ht5, ht6, ht7]
    refine ⟨?_, ?_, ?_, ?_, ?_, (h.1 1 le_rfl (by norm_num)).2⟩
    · rw [trip_T h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)]
      clifford_simp hC
    all_goals clifford_simp hC
  have R7 : IsACFam Js 7 → t7ᵀ = t7 ∧ t7 * t7 = 1 ∧ t7 * t3 = t3 * t7 ∧ t7 * t5 = t5 * t7 ∧
      t7 * t6 = t6 * t7 := by
    intro h
    have hC := cliff h
    simp only [ht3, ht5, ht6, ht7]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [trip_T h (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num)]
      clifford_simp hC
    all_goals clifford_simp hC
  have R8 : IsACFam Js 8 → (Js 7 * Js 8) * (Js 7 * Js 8) = -1 ∧
      (Js 7 * Js 8) * t7 = -(t7 * (Js 7 * Js 8)) ∧ (Js 7 * Js 8) * t3 = t3 * (Js 7 * Js 8) ∧
      (Js 7 * Js 8) * t5 = t5 * (Js 7 * Js 8) ∧ (Js 7 * Js 8) * t6 = t6 * (Js 7 * Js 8) := by
    intro h
    have hC := cliff h
    simp only [ht3, ht5, ht6, ht7]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> clifford_simp hC
  -- invariance of the nested subspaces
  have V1inv : ∀ {M : Mat (Fin (16 * r))}, M * t3 = t3 * M → ∀ v ∈ V1 Js, M *ᵥ v ∈ V1 Js :=
    fun hM => eig1_inv hM
  have Winv : ∀ {M : Mat (Fin (16 * r))}, M * t3 = t3 * M → M * t5 = t5 * M →
      ∀ v ∈ Wsp Js, M *ᵥ v ∈ Wsp Js :=
    fun h3 h5 => inf_inv (eig1_inv h3) (eig1_inv h5)
  have Xinv : ∀ {M : Mat (Fin (16 * r))}, M * t3 = t3 * M → M * t5 = t5 * M → M * t6 = t6 * M →
      ∀ v ∈ Xsp Js, M *ᵥ v ∈ Xsp Js :=
    fun h3 h5 h6 => inf_inv (Winv h3 h5) (eig1_inv h6)
  -- the splittings
  have S3 : IsACFam Js 3 → V1 Js ⊔ V2 Js = ⊤ := by
    intro h
    have := split_eig (R3 h).2.1 ⊤ (fun v _ => Submodule.mem_top)
    simpa [eV1, eV2] using this
  have I3 : V1 Js ⊓ V2 Js = ⊥ := disj_eig le_rfl le_rfl
  -- the dimensions
  have D4 : IsACFam Js 4 → finrank ℝ (V1 Js) = 8 * r := by
    intro h
    obtain ⟨hP, hPθ⟩ := R4 h
    have := halve hh ⊤ (R3 (mono (by norm_num) h)).2.1 hP hPθ
      (fun _ _ => Submodule.mem_top) (fun _ _ => Submodule.mem_top)
    rw [finrank_top, Module.finrank_fin_fun, top_inf_eq] at this
    rw [eV1]
    omega
  have S5 : IsACFam Js 5 → img (Js 2) (Wsp Js) = V1 Js ⊓ eigm1 t5 := by
    intro h
    obtain ⟨-, -, -, -, a25, s2⟩ := R5 h
    exact img_swap s2 a25 (V1 Js) (V1inv (R3 (mono (by norm_num) h)).2.2.2)
  have D5 : IsACFam Js 5 → finrank ℝ (Wsp Js) = 4 * r := by
    intro h
    obtain ⟨-, s5, c53, -, a25, s2⟩ := R5 h
    have := halve hh (V1 Js) s5 s2 a25 (V1inv c53) (V1inv (R3 (mono (by norm_num) h)).2.2.2)
    rw [D4 (mono (by norm_num) h), ← eW] at this
    omega
  have S6 : IsACFam Js 6 → img (Js 1) (Xsp Js) = Wsp Js ⊓ eigm1 t6 := by
    intro h
    obtain ⟨-, -, -, -, a16, s1⟩ := R6 h
    exact img_swap s1 a16 (Wsp Js) (Winv (R3 (mono (by norm_num) h)).2.2.1
      (R5 (mono (by norm_num) h)).2.2.2.1)
  have D6 : IsACFam Js 6 → finrank ℝ (Xsp Js) = 2 * r := by
    intro h
    obtain ⟨-, s6, c63, c65, a16, s1⟩ := R6 h
    have := halve hh (Wsp Js) s6 s1 a16 (Winv c63 c65)
      (Winv (R3 (mono (by norm_num) h)).2.2.1 (R5 (mono (by norm_num) h)).2.2.2.1)
    rw [D5 (mono (by norm_num) h), ← eX] at this
    omega
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨T3, -, c13, c23⟩ := R3 h
    exact ⟨perp_eig T3 le_rfl le_rfl, S3 h, (img_le_iff _ _).2 (eig1_inv c13),
      (img_le_iff _ _).2 (eig1_inv c23), (img_le_iff _ _).2 (eigm1_inv c13),
      (img_le_iff _ _).2 (eigm1_inv c23)⟩
  · refine ⟨by rw [D4 h]; ring, ?_⟩
    have := finrank_split (S3 (mono (by norm_num) h)) I3
    rw [finrank_top, Module.finrank_fin_fun, D4 h] at this
    omega
  · obtain ⟨T5, s5, c53, c15, -, -⟩ := R5 h
    have c13 := (R3 (mono (by norm_num) h)).2.2.1
    have hsup : Wsp Js ⊔ img (Js 2) (Wsp Js) = V1 Js := by
      rw [S5 h, eW]; exact split_eig s5 _ (V1inv c53)
    have hinf : Wsp Js ⊓ img (Js 2) (Wsp Js) = ⊥ := by
      rw [S5 h, eW]; exact disj_eig inf_le_right inf_le_right
    refine ⟨(img_le_iff _ _).2 (Winv c13 c15), ?_, hsup, D5 h, ?_⟩
    · rw [S5 h, eW]; exact perp_eig T5 inf_le_right inf_le_right
    · have := finrank_split hsup hinf
      rw [D4 (mono (by norm_num) h), D5 h] at this
      omega
  · obtain ⟨T6, s6, c63, c65, -, -⟩ := R6 h
    have hsup : Xsp Js ⊔ img (Js 1) (Xsp Js) = Wsp Js := by
      rw [S6 h, eX]; exact split_eig s6 _ (Winv c63 c65)
    have hinf : Xsp Js ⊓ img (Js 1) (Xsp Js) = ⊥ := by
      rw [S6 h, eX]; exact disj_eig inf_le_right inf_le_right
    refine ⟨?_, hsup, D6 h, ?_⟩
    · rw [S6 h, eX]; exact perp_eig T6 inf_le_right inf_le_right
    · have := finrank_split hsup hinf
      rw [D5 (mono (by norm_num) h), D6 h] at this
      omega
  · obtain ⟨T7, s7, c73, c75, c76⟩ := R7 h
    exact ⟨perp_eig T7 inf_le_right inf_le_right, split_eig s7 _ (Xinv c73 c75 c76)⟩
  · obtain ⟨T7, s7, c73, c75, c76⟩ := R7 (mono (by norm_num) h)
    obtain ⟨sP, aP, cP3, cP5, cP6⟩ := R8 h
    have := halve hh (Xsp Js) s7 sP aP (Xinv c73 c75 c76) (Xinv cP3 cP5 cP6)
    rw [D6 (mono (by norm_num) h), ← eX1] at this
    have hsplit := finrank_split (split_eig s7 _ (Xinv c73 c75 c76))
      (disj_eig (S := Xsp Js ⊓ eig1 t7) (T := Xsp Js ⊓ eigm1 t7) inf_le_right inf_le_right)
    rw [← eX1, ← eX2, D6 (mono (by norm_num) h)] at hsplit
    exact ⟨by omega, by omega⟩

/-! ### B ⇒ A -/

section Outright
open Morse
variable {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- A's halving lemma, re-proved (the project's proof, copied: B is only about `ℝ^{16r}`). -/
theorem halving (θ P : Module.End ℝ V) (hθ : θ * θ = 1)
    (hP : Function.Injective P) (hPθ : P * θ = -(θ * P)) :
    finrank ℝ V = 2 * finrank ℝ (LinearMap.ker (θ - 1)) := by
  set Vp := LinearMap.ker (θ - 1) with hVp
  set Vm := LinearMap.ker (θ + 1) with hVm
  have hθv : ∀ v, θ (θ v) = v := fun v => by
    have := congrArg (fun f : Module.End ℝ V => f v) hθ; simpa using this
  have hPv : ∀ v, P (θ v) = -θ (P v) := fun v => by
    have := congrArg (fun f : Module.End ℝ V => f v) hPθ; simpa using this
  have hmemp : ∀ v, v ∈ Vp ↔ θ v = v := fun v => by simp [hVp, sub_eq_zero]
  have hmemm : ∀ v, v ∈ Vm ↔ θ v = -v := fun v => by simp [hVm, add_eq_zero_iff_eq_neg]
  have hcompl : IsCompl Vp Vm := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hp hm
      rw [hmemp] at hp; rw [hmemm] at hm
      have : v = -v := hp.symm.trans hm
      have h2 : (2 : ℝ) • v = 0 := by rw [two_smul]; nth_rewrite 2 [this]; exact add_neg_cancel v
      exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      have h1 : (1 / 2 : ℝ) • (v + θ v) ∈ Vp := by
        rw [hmemp, map_smul, map_add, hθv, add_comm]
      have h2 : (1 / 2 : ℝ) • (v - θ v) ∈ Vm := by
        rw [hmemm, map_smul, map_sub, hθv, ← smul_neg, neg_sub]
      have : v = (1 / 2 : ℝ) • (v + θ v) + (1 / 2 : ℝ) • (v - θ v) := by module
      rw [this]
      exact Submodule.add_mem_sup h1 h2
  have hle1 : finrank ℝ Vp ≤ finrank ℝ Vm := by
    have hmap : ∀ v ∈ Vp, P v ∈ Vm := fun v hv => by
      rw [hmemp] at hv; rw [hmemm]
      have := hPv v; rw [hv] at this
      exact neg_eq_iff_eq_neg.1 this.symm
    exact LinearMap.finrank_le_finrank_of_injective (f := P.restrict hmap)
      (fun a b hab => Subtype.ext (hP (congrArg Subtype.val hab)))
  have hle2 : finrank ℝ Vm ≤ finrank ℝ Vp := by
    have hmap : ∀ v ∈ Vm, P v ∈ Vp := fun v hv => by
      rw [hmemm] at hv; rw [hmemp]
      have := hPv v; rw [hv, map_neg] at this
      exact (neg_inj.1 this).symm
    exact LinearMap.finrank_le_finrank_of_injective (f := P.restrict hmap)
      (fun a b hab => Subtype.ext (hP (congrArg Subtype.val hab)))
  rw [← Submodule.finrank_add_eq_of_isCompl hcompl]
  omega

theorem halving_sub (U : Submodule ℝ V) (θ P : Module.End ℝ V)
    (hθ : θ * θ = 1) (hP : Function.Injective P) (hPθ : P * θ = -(θ * P))
    (hθU : ∀ v ∈ U, θ v ∈ U) (hPU : ∀ v ∈ U, P v ∈ U) :
    finrank ℝ U = 2 * finrank ℝ ↥(U ⊓ LinearMap.ker (θ - 1)) := by
  have h := halving (θ.restrict hθU) (P.restrict hPU)
    (by ext v; have := congrArg (fun f : Module.End ℝ V => f v) hθ; simpa using this)
    (fun a b hab => Subtype.ext (hP (congrArg Subtype.val hab)))
    (by ext v; have := congrArg (fun f : Module.End ℝ V => f v) hPθ; simpa using this)
  rw [h]
  congr 1
  have hmap : Submodule.map U.subtype (LinearMap.ker (θ.restrict hθU - 1)) =
      U ⊓ LinearMap.ker (θ - 1) := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, by simpa using congrArg Subtype.val hw⟩
    · rintro ⟨hU, hv⟩
      exact ⟨⟨v, hU⟩, Subtype.ext (by simpa using hv), rfl⟩
  rw [← hmap, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ U.injective_subtype _)]

/-- A's chain, re-proved (the project's four halvings, with the re-proved halving lemma). -/
theorem chain {J : ℕ → Module.End ℝ V} (h : IsClifford J 8) :
    finrank ℝ V = 2 * finrank ℝ (eigV₁ J) ∧ finrank ℝ (eigV₁ J) = 2 * finrank ℝ (eigW J) ∧
      finrank ℝ (eigW J) = 2 * finrank ℝ (eigX J) ∧
      finrank ℝ (eigX J) = 2 * finrank ℝ (jointEigen J) := by
  obtain ⟨h3sq, h3c1, h3c2, -⟩ := θ₃_spec (h.mono (by norm_num))
  obtain ⟨h5sq, h5c1, -, -, h5a2, -, h53⟩ := θ₅_spec (h.mono (by norm_num))
  obtain ⟨h6sq, -, -, -, h6a1, -, -, h63, h65⟩ := θ₆_spec (h.mono (by norm_num))
  obtain ⟨h7sq, -, -, -, -, -, -, -, h73, h75, h76⟩ := θ₇_spec (h.mono (by norm_num))
  obtain ⟨h78c3, h78c5, h78c6, h78a7⟩ := J₇J₈_spec h
  have hJ78 : J 7 * J 8 * (J 7 * J 8) = -1 := by clifford_simp h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact halving (θ₃ J) (J 4) h3sq
      (injective_of_mul_self_eq_neg_one (h.sq 4 (by norm_num) (by norm_num)))
      (anticomm_symm (θ₃_anticommute h (by norm_num) (by norm_num)))
  · exact halving_sub (eigV₁ J) (θ₅ J) (J 2) h5sq
      (injective_of_mul_self_eq_neg_one (h.sq 2 (by norm_num) (by norm_num))) (anticomm_symm h5a2)
      (fun v hv => mapsTo_ker_of_commute h53.eq hv)
      (fun v hv => mapsTo_ker_of_commute h3c2.eq.symm hv)
  · exact halving_sub (eigW J) (θ₆ J) (J 1) h6sq
      (injective_of_mul_self_eq_neg_one (h.sq 1 le_rfl (by norm_num))) (anticomm_symm h6a1)
      (mapsTo_inf (fun v hv => mapsTo_ker_of_commute h63.eq hv)
        (fun v hv => mapsTo_ker_of_commute h65.eq hv))
      (mapsTo_inf (fun v hv => mapsTo_ker_of_commute h3c1.eq.symm hv)
        (fun v hv => mapsTo_ker_of_commute h5c1.eq.symm hv))
  · exact halving_sub (eigX J) (θ₇ J) (J 7 * J 8) h7sq
      (injective_of_mul_self_eq_neg_one hJ78) h78a7
      (mapsTo_inf (mapsTo_inf (fun v hv => mapsTo_ker_of_commute h73.eq hv)
        (fun v hv => mapsTo_ker_of_commute h75.eq hv))
        (fun v hv => mapsTo_ker_of_commute h76.eq hv))
      (mapsTo_inf (mapsTo_inf (fun v hv => mapsTo_ker_of_commute h78c3.eq hv)
        (fun v hv => mapsTo_ker_of_commute h78c5.eq hv))
        (fun v hv => mapsTo_ker_of_commute h78c6.eq hv))

end Outright

section Transport
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
set_option linter.unusedSectionVars false

/-- `v ↦ v ∘ e⁻¹`, `ℝ^ι ≃ ℝ^κ`. -/
noncomputable def L (e : ι ≃ κ) : (ι → ℝ) ≃ₗ[ℝ] (κ → ℝ) := LinearEquiv.funCongrLeft ℝ ℝ e.symm

theorem L_apply (e : ι ≃ κ) (v : ι → ℝ) : L e v = v ∘ e.symm := rfl

theorem eig1_reindex (e : ι ≃ κ) (T : Mat ι) :
    eig1 (reindex e e T) = (eig1 T).map (L e : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) := by
  ext w
  obtain ⟨v, rfl⟩ : ∃ v, w = L e v := ⟨(L e).symm w, ((L e).apply_symm_apply w).symm⟩
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_eig1, mem_eig1, L_apply,
    reindex_apply, submatrix_mulVec_equiv, Equiv.symm_symm, Function.comp_assoc,
    Equiv.symm_comp_self, Function.comp_id]
  constructor
  · intro h
    have := congrArg (· ∘ e) h
    simpa [Function.comp_assoc] using this
  · intro h
    rw [h]

theorem r_mul (e : ι ≃ κ) (X Y : Mat ι) : reindex e e (X * Y) = reindex e e X * reindex e e Y := by
  simpa only [coe_reindexAlgEquiv] using map_mul (reindexAlgEquiv ℝ ℝ e) X Y

theorem map_inf' (e : ι ≃ κ) (S T : Submodule ℝ (ι → ℝ)) :
    (S ⊓ T).map (L e : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) =
      S.map (L e : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) ⊓ T.map (L e : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)) :=
  Submodule.map_inf _ (L e).injective

theorem ker_toLinAlgEquiv' (T : Mat ι) :
    LinearMap.ker (Matrix.toLinAlgEquiv' T - 1) = eig1 T := by
  ext v
  rw [LinearMap.mem_ker, mem_eig1, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    Matrix.toLinAlgEquiv'_apply]

end Transport

/-- B ⇒ A. The fourth conjunct (Milnor's structures on `ℝ^{16r}`: `dim X₁, X, W, V₁ = r, 2r, 4r,
8r`) is B's dimension claims for the family `bott16 ⊕ ⋯ ⊕ bott16`, transported along
`I16 × Fin r ≃ Fin (16r)`. The first three conjuncts (the halving lemma and the chain, for an
ABSTRACT finite-dimensional real vector space with 8 endomorphisms satisfying the Clifford
relations, no inner product, any dimension) are not consequences of B (which only treats
orthogonal structures on `ℝ^{16r}`) and are re-proved outright (the project's proofs, copied). -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨@fun V _ _ _ θ P hθ hP hPθ => halving θ P hθ hP hPθ, @fun V _ _ _ J h => chain h,
    @fun V _ _ _ J h => ?_, ?_⟩
  · obtain ⟨s1, s2, s3, s4⟩ := chain h
    rw [s1, s2, s3, s4]; ring
  · intro r
    simp only
    set M : ℕ → Mat (Morse.I16 × Fin r) := fun α => Matrix.blockDiagonal fun _ : Fin r =>
      Morse.bott16 α with hM
    have hcard : Fintype.card (Morse.I16 × Fin r) = 16 * r := by simp
    set e : Morse.I16 × Fin r ≃ Fin (16 * r) := Fintype.equivFinOfCardEq hcard
    set Js : ℕ → Mat (Fin (16 * r)) := fun α => reindex e e (M α) with hJs
    have hJ : IsACFam Js 8 := by
      have := (Morse.isAnticommFamily_bott16r r).reindex e
      exact ⟨this.cs, this.anti⟩
    obtain ⟨-, d4, d5, d6, -, d8⟩ := hB r Js
    have d4 := (d4 (mono (by norm_num) hJ)).1
    have d5 := (d5 (mono (by norm_num) hJ)).2.2.2.1
    have d6 := (d6 (mono (by norm_num) hJ)).2.2.1
    have d8 := (d8 hJ).1
    -- the eigenspaces of `Js` are the images of those of `M`
    have t3 : Js 1 * Js 2 * Js 3 = reindex e e (M 1 * M 2 * M 3) := by simp only [hJs, r_mul]
    have t5 : Js 1 * Js 4 * Js 5 = reindex e e (M 1 * M 4 * M 5) := by simp only [hJs, r_mul]
    have t6 : Js 2 * Js 4 * Js 6 = reindex e e (M 2 * M 4 * M 6) := by simp only [hJs, r_mul]
    have t7 : Js 1 * Js 6 * Js 7 = reindex e e (M 1 * M 6 * M 7) := by simp only [hJs, r_mul]
    have eV : V1 Js = (V1 M).map (L e : _ →ₗ[ℝ] _) := by
      rw [V1, V1, t3, eig1_reindex]
    have eW : Wsp Js = (Wsp M).map (L e : _ →ₗ[ℝ] _) := by
      rw [Wsp, Wsp, eV, t5, eig1_reindex, map_inf']
    have eX : Xsp Js = (Xsp M).map (L e : _ →ₗ[ℝ] _) := by
      rw [Xsp, Xsp, eW, t6, eig1_reindex, map_inf']
    have eX1 : X1 Js = (X1 M).map (L e : _ →ₗ[ℝ] _) := by
      rw [X1, X1, eX, t7, eig1_reindex, map_inf']
    rw [eV, LinearEquiv.finrank_map_eq] at d4
    rw [eW, LinearEquiv.finrank_map_eq] at d5
    rw [eX, LinearEquiv.finrank_map_eq] at d6
    rw [eX1, LinearEquiv.finrank_map_eq] at d8
    -- the project's eigenspaces are B's, on `I16 × Fin r`
    have k3 : Morse.eigV₁ (fun α => Matrix.toLinAlgEquiv' (M α)) = V1 M := by
      rw [Morse.eigV₁, Morse.θ₃, ← map_mul, ← map_mul, ker_toLinAlgEquiv']; rfl
    have k5 : Morse.eigW (fun α => Matrix.toLinAlgEquiv' (M α)) = Wsp M := by
      rw [Morse.eigW, k3, Morse.θ₅, ← map_mul, ← map_mul, ker_toLinAlgEquiv']; rfl
    have k6 : Morse.eigX (fun α => Matrix.toLinAlgEquiv' (M α)) = Xsp M := by
      rw [Morse.eigX, k5, Morse.θ₆, ← map_mul, ← map_mul, ker_toLinAlgEquiv']; rfl
    have k7 : Morse.jointEigen (fun α => Matrix.toLinAlgEquiv' (M α)) = X1 M := by
      rw [Morse.jointEigen, k6, Morse.θ₇, ← map_mul, ← map_mul, ker_toLinAlgEquiv']; rfl
    rw [k3, k5, k6, k7]
    exact ⟨d8, d6, d5, by rw [d4]; ring⟩

#rt_check RoundTrip.V15_12.A_to_B [Morse.finrank_eq_two_mul_of_anticomm, Morse.finrank_chain,
  Morse.finrank_eq_sixteen_mul, Morse.finrank_jointEigen_bott16r]
#rt_check RoundTrip.V15_12.B_to_A [Morse.finrank_eq_two_mul_of_anticomm, Morse.finrank_chain,
  Morse.finrank_eq_sixteen_mul, Morse.finrank_jointEigen_bott16r]
#rt_overlap RoundTrip.V15_12.B_to_A [Morse.finrank_eq_two_mul_of_anticomm, Morse.finrank_chain,
  Morse.finrank_eq_sixteen_mul, Morse.finrank_jointEigen_bott16r]

end RoundTrip.V15_12
