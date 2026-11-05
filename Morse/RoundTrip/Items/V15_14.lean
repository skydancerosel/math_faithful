import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_14

open Matrix Module
open scoped MatrixOrder

namespace RoundTrip.V15_14

/-- The project's statement (universes instantiated at `0`): for an abstract real vector space `V`
with anticommuting square roots of `-1` (no inner product, `Morse.IsClifford`): `2 ∣ dim V`
(`k ≥ 1`), `4 ∣ dim V` (`k ≥ 2`), `8 ∣ dim V` (`k ≥ 4`), and `m_k ∣ dim V` for `k ≤ 8`
(`Morse.milnorM`, Milnor's table extended by `m_{k+8} = 16 m_k`); for anticommuting complex structures on
`ℝⁿ` (any finite index type) `m_k ∣ n`, `k ≤ 8`; `ℝ^{m_k}` carries `k` of them (`k ≤ 8`); and `m_k`
is the least positive such dimension (`k ≤ 8`). -/
def A : Prop :=
  type_of% @Morse.two_dvd_finrank_of_sq.{0} ∧ type_of% @Morse.four_dvd_finrank_of_anticomm.{0} ∧
    type_of% @Morse.eight_dvd_finrank.{0} ∧ type_of% @Morse.milnorM_dvd_finrank.{0} ∧
    type_of% @Morse.milnorM_dvd_card.{0} ∧ type_of% @Morse.exists_isAnticommFamily_fin ∧
    type_of% @Morse.isLeast_milnorM

theorem A_holds : A :=
  ⟨@Morse.two_dvd_finrank_of_sq.{0}, @Morse.four_dvd_finrank_of_anticomm.{0},
    @Morse.eight_dvd_finrank.{0}, @Morse.milnorM_dvd_finrank.{0}, @Morse.milnorM_dvd_card.{0},
    @Morse.exists_isAnticommFamily_fin, @Morse.isLeast_milnorM⟩

/-! ## Glue: orthogonalizing an abstract `(J_1, …, J_k)`-space

B speaks of anticommuting *orthogonal* complex structures on `ℝⁿ = Fin n → ℝ`; A of anticommuting
square roots of `-1` on an abstract space. Averaging the inner product over `J_1, …, J_k`
(`G_{j+1} = G_j + J_{j+1}ᵀ G_j J_{j+1}`) and conjugating by a square root of `G_k` turns the latter
into the former (`ortho_glue`). -/

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

theorem set_eq (k : ℕ) : {n : ℕ | 0 < n ∧ ∃ Js : ℕ → Mat (Fin n), IsACFam Js k} =
    {d | 0 < d ∧ ∃ J : ℕ → Matrix (Fin d) (Fin d) ℝ, Morse.IsAnticommFamily J k} := by
  ext d; simp only [Set.mem_ofPred_eq, isACFam_iff]

/-- B's `m_k` agrees with the project's `milnorM k` for `k ≤ 8`, given B's table. -/
theorem mk_eq_milnorM_of_B (hB : B) {k : ℕ} (hk : k ≤ 8) : mk k = Morse.milnorM k := by
  obtain ⟨-, -, h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hB
  interval_cases k <;> simp [Morse.milnorM, *]

/-- B's divisibility, for an abstract finite-dimensional `(J_1, …, J_k)`-space (no inner product):
orthogonalize, then apply B on `Fin (dim V)`. -/
theorem dvd_finrank_of_B (hB : B) {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {J : ℕ → Module.End ℝ V} {k : ℕ} (h : Morse.IsClifford J k) : mk k ∣ finrank ℝ V := by
  obtain ⟨Js, -, hJs, -⟩ := ortho_glue h
  exact hB.1 k _ Js ((isACFam_iff Js k).2 hJs)

theorem dvd_finrank_of_B' (hB : B) {V : Type} [AddCommGroup V] [Module ℝ V]
    {J : ℕ → Module.End ℝ V} {k : ℕ} (h : Morse.IsClifford J k) : mk k ∣ finrank ℝ V := by
  by_cases hfin : FiniteDimensional ℝ V
  · exact dvd_finrank_of_B hB h
  · rw [Module.finrank_of_not_finite hfin]; exact dvd_zero _

/-- B ⇒ A. B's divisibility (stated for orthogonal structures on `Fin n → ℝ`) gives A's abstract
divisibility after orthogonalizing (`ortho_glue`, averaging the inner product: the only glue);
infinite-dimensional `V` has `finrank = 0`. B's table identifies B's `m_k` (an `sInf` of dimensions of
minimal spaces) with `milnorM k` for `k ≤ 8`; A's matrix statements are B's after reindexing to
`Fin (card n)`. -/
theorem B_to_A : B → A := by
  intro hB
  have hmk := fun {k : ℕ} (hk : k ≤ 8) => mk_eq_milnorM_of_B hB hk
  have hdvd := hB.1
  have hleast := hB.2.1
  refine ⟨@fun V _ _ J hJ => ?_, @fun V _ _ J₁ J₂ h1 h2 h12 => ?_, @fun V _ _ _ J h => ?_,
    @fun V _ _ _ J k hk h => ?_, @fun n _ _ J k hk h => ?_, @fun k hk => ?_, @fun k hk => ?_⟩
  · have h' : Morse.IsClifford (fun _ => J) 1 :=
      ⟨fun _ _ _ => hJ, fun a b h1 h2 h3 h4 hab => absurd (by omega : a = b) hab⟩
    have := dvd_finrank_of_B' hB h'
    rwa [hmk (by norm_num)] at this
  · have h' : Morse.IsClifford (fun a => if a = 1 then J₁ else J₂) 2 := by
      refine ⟨fun a ha1 ha2 => ?_, fun a b ha1 ha2 hb1 hb2 hab => ?_⟩
      · rcases (by omega : a = 1 ∨ a = 2) with rfl | rfl <;> simp [h1, h2]
      · rcases (by omega : a = 1 ∨ a = 2) with rfl | rfl <;>
          rcases (by omega : b = 1 ∨ b = 2) with rfl | rfl <;> simp_all
    have := dvd_finrank_of_B' hB h'
    rwa [hmk (by norm_num)] at this
  · have := dvd_finrank_of_B hB h
    rwa [hmk (by norm_num)] at this
  · have := dvd_finrank_of_B hB h
    rwa [hmk hk] at this
  · have := hdvd k _ _ ((isACFam_iff _ k).2 (h.reindex (Fintype.equivFin n)))
    rwa [hmk hk] at this
  · obtain ⟨-, Js, hJs⟩ := (hleast k).1
    rw [← hmk hk]
    exact ⟨Js, (isACFam_iff Js k).1 hJs⟩
  · have := hleast k
    rwa [hmk hk, set_eq] at this

/-! ## A ⇒ B for `k ≤ 8` -/

/-- B restricted to `k ≤ 8` (the range of A). -/
def B_le8 : Prop :=
  (∀ (k n : ℕ) (Js : ℕ → Mat (Fin n)), k ≤ 8 → IsACFam Js k → mk k ∣ n) ∧
  (∀ k : ℕ, k ≤ 8 → IsLeast {n : ℕ | 0 < n ∧ ∃ Js : ℕ → Mat (Fin n), IsACFam Js k} (mk k)) ∧
  mk 0 = 1 ∧ mk 1 = 2 ∧ mk 2 = 4 ∧ mk 3 = 4 ∧ mk 4 = 8 ∧ mk 5 = 8 ∧ mk 6 = 8 ∧ mk 7 = 8 ∧ mk 8 = 16

/-- From A: for `k ≤ 8`, B's `m_k` (the least dimension of a minimal space) is `milnorM k`:
`ℝ^{milnorM k}` carries a family (A) which is minimal (every invariant subspace is again a
`(J_1, …, J_k)`-space, so its dimension is divisible by `milnorM k`, by A), and every minimal space
has dimension divisible by `milnorM k` (A). -/
theorem mk_eq_milnorM_of_A (hA : A) {k : ℕ} (hk : k ≤ 8) : mk k = Morse.milnorM k := by
  obtain ⟨-, -, -, hdf, hdc, hex, -⟩ := hA
  have hpos := Morse.milnorM_pos k
  obtain ⟨J, hJ⟩ := hex hk
  have hmem : Morse.milnorM k ∈ {n : ℕ | ∃ Js : ℕ → Mat (Fin n), IsMinACSp Js k} := by
    refine ⟨J, ⟨⟨⟨0, hpos⟩⟩, (isACFam_iff J k).2 hJ, fun W hW => ?_⟩⟩
    have hW' : ∀ α, 1 ≤ α → α ≤ k → ∀ w ∈ W, Matrix.toLinAlgEquiv' (J α) w ∈ W := by
      intro α h1 h2 w hw
      rw [Matrix.toLinAlgEquiv'_apply]
      exact hW α h1 h2 w hw
    obtain ⟨J', hJ'⟩ := hJ.isClifford_toLin'.exists_restrict W hW'
    have hd := hdf hk hJ'
    have hle : finrank ℝ W ≤ Morse.milnorM k := by
      simpa using Submodule.finrank_le W
    rcases Nat.eq_zero_or_pos (finrank ℝ W) with h0 | hp
    · exact Or.inl (Submodule.finrank_eq_zero.1 h0)
    · refine Or.inr (Submodule.eq_top_of_finrank_eq ?_)
      have := Nat.le_of_dvd hp hd
      simp only [finrank_fin_fun]
      omega
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ fun n ⟨Js, hJs⟩ => ?_)
  obtain ⟨hne, hfam, -⟩ := hJs
  have hn : 0 < n := Fin.pos_iff_nonempty.2 hne
  have := hdc hk ((isACFam_iff Js k).1 hfam)
  rw [Fintype.card_fin] at this
  exact Nat.le_of_dvd hn this

/-- A ⇒ B for `k ≤ 8` (all of B's content except the cases `k > 8` of its first two clauses). -/
theorem A_to_B_le8 : A → B_le8 := by
  intro hA
  have hmk := fun {k : ℕ} (hk : k ≤ 8) => mk_eq_milnorM_of_A hA hk
  refine ⟨fun k n Js hk hJs => ?_, fun k hk => ?_, ?_⟩
  · have := hA.2.2.2.2.1 hk ((isACFam_iff Js k).1 hJs)
    rwa [Fintype.card_fin, ← hmk hk] at this
  · have := hA.2.2.2.2.2.2 hk
    rwa [← hmk hk, ← set_eq] at this
  · simp only [hmk (by norm_num : (0 : ℕ) ≤ 8), hmk (by norm_num : (1 : ℕ) ≤ 8),
      hmk (by norm_num : (2 : ℕ) ≤ 8), hmk (by norm_num : (3 : ℕ) ≤ 8),
      hmk (by norm_num : (4 : ℕ) ≤ 8), hmk (by norm_num : (5 : ℕ) ≤ 8),
      hmk (by norm_num : (6 : ℕ) ≤ 8), hmk (by norm_num : (7 : ℕ) ≤ 8), hmk le_rfl]
    decide

#rt_check RoundTrip.V15_14.B_to_A [Morse.two_dvd_finrank_of_sq, Morse.four_dvd_finrank_of_anticomm,
  Morse.eight_dvd_finrank, Morse.milnorM_dvd_finrank, Morse.milnorM_dvd_card,
  Morse.exists_isAnticommFamily_fin, Morse.isLeast_milnorM]
#rt_check RoundTrip.V15_14.A_to_B_le8 [Morse.two_dvd_finrank_of_sq,
  Morse.four_dvd_finrank_of_anticomm, Morse.eight_dvd_finrank, Morse.milnorM_dvd_finrank,
  Morse.milnorM_dvd_card, Morse.exists_isAnticommFamily_fin, Morse.isLeast_milnorM]
#rt_overlap RoundTrip.V15_14.B_to_A [Morse.two_dvd_finrank_of_sq,
  Morse.four_dvd_finrank_of_anticomm, Morse.eight_dvd_finrank, Morse.milnorM_dvd_finrank,
  Morse.milnorM_dvd_card, Morse.exists_isAnticommFamily_fin, Morse.isLeast_milnorM]

end RoundTrip.V15_14
