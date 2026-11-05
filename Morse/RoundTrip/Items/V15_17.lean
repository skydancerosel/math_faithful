import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_17

open Matrix Module
open scoped MatrixOrder

namespace RoundTrip.V15_17

/-- The project's statement (universes instantiated at `0`; `Morse.cyclicMap`, the orbit map
`c ↦ c·u` of `C_k`, is vocabulary): Lemma 24.8 for `k ≤ 8`, `k ≢ 3 (mod 4)` — two minimal abstract
`(J_1, …, J_k)`-spaces (anticommuting square roots of `-1`, no inner product) are isomorphic by a
LINEAR isomorphism commuting with the `J_α`; plus the three lemmas of its proof: the orbit map of a
non-zero vector of a minimal space is onto; if `u ≠ 0` is fixed by commuting involutions `θ` and the
right-`θ`-fixed subspace `F ⊆ C_k` has dimension `m_k`, then `dim V = m_k` and `F ≅ V`; two minimal
spaces isomorphic to the same left ideal `F` by orbit maps are isomorphic. -/
def A : Prop :=
  type_of% @Morse.exists_iso_of_isMinimal.{0, 0} ∧ type_of% @Morse.range_cyclicMap_eq_top.{0} ∧
    type_of% @Morse.minimal_of_fixed.{0} ∧ type_of% @Morse.exists_iso_of_equiv.{0, 0}

theorem A_holds : A :=
  ⟨@Morse.exists_iso_of_isMinimal.{0, 0}, @Morse.range_cyclicMap_eq_top.{0},
    @Morse.minimal_of_fixed.{0}, @Morse.exists_iso_of_equiv.{0, 0}⟩

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

/-! ## B ⇒ A -/

/-- Outright (the project's argument): the orbit map of `u ≠ 0` in a minimal space is onto. -/
theorem range_cyclicMap_eq_top' {V : Type} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    {J : ℕ → Module.End ℝ V} (h : Morse.IsClifford J k) (hmin : Morse.IsMinimalCliffordModule J k)
    {u : V} (hu : u ≠ 0) : LinearMap.range (Morse.cyclicMap h u) = ⊤ := by
  rcases hmin.2 (LinearMap.range (Morse.cyclicMap h u)) (fun α h1 h2 w hw => by
      obtain ⟨c, rfl⟩ := LinearMap.mem_range.1 hw
      exact ⟨Morse.cliffE k α * c, Morse.cyclicMap_mul h u h1 h2 c⟩) with hbot | htop
  · exfalso
    have : u ∈ LinearMap.range (Morse.cyclicMap h u) :=
      ⟨1, by rw [Morse.cyclicMap_apply, map_one, Module.End.one_apply]⟩
    rw [hbot, Submodule.mem_bot] at this
    exact hu this
  · exact htop

/-- B ⇒ A. Lemma 24.8 (`exists_iso_of_isMinimal`) is B after orthogonalizing both spaces
(`ortho_glue`): B's isometry `T` (a matrix with `TᵀT = TTᵀ = I`) commuting with the structures
gives the linear isomorphism `E'⁻¹ ∘ T ∘ E`. The three technical lemmas of the project's proof
(orbit map onto; `F ≅ V` when `dim F = m_k`; two spaces isomorphic to the same `F` are isomorphic)
are about the Clifford algebra `C_k` and have no counterpart in B; they are re-proved outright (the
project's arguments, re-run without the item's theorems; `minimal_of_fixed` uses the outside lemma
`milnorM_dvd_finrank`). -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨@fun k V _ _ _ V' _ _ _ J J' hk hk3 h h' hmin hmin' => ?_,
    @fun k V _ _ J h hmin u hu => range_cyclicMap_eq_top' h hmin hu,
    @fun k V _ _ _ J h hk hmin θs hsq hcomm F hF hFdim u hu0 hfix => ?_,
    @fun k V _ _ V' _ _ J J' h h' F hFmul u u' e he e' he' => ?_⟩
  · -- Lemma 24.8, from B
    obtain ⟨Js, E, hJs, hE⟩ := transfer_min h hmin
    obtain ⟨Js', E', hJs', hE'⟩ := transfer_min h' hmin'
    obtain ⟨T, hT1, hT2, hTJ⟩ := hB k hk3 _ _ Js Js' hJs hJs'
    let Teq : (Fin (finrank ℝ V) → ℝ) ≃ₗ[ℝ] (Fin (finrank ℝ V') → ℝ) :=
      LinearEquiv.ofLinearMap (Matrix.toLin' T) (Matrix.toLin' Tᵀ)
        (by rw [← Matrix.toLin'_mul, hT2, Matrix.toLin'_one])
        (by rw [← Matrix.toLin'_mul, hT1, Matrix.toLin'_one])
    have hTeq : ∀ x, Teq x = T *ᵥ x := fun x => rfl
    have hE's := intertwine_symm (J' := lin Js') E' hE'
    refine ⟨E.trans (Teq.trans E'.symm), fun α h1 h2 v => ?_⟩
    simp only [LinearEquiv.trans_apply, hTeq]
    rw [hE α h1 h2, mulVec_mulVec, hTJ α h1 h2, ← mulVec_mulVec]
    exact hE's α h1 h2 _
  · -- `minimal_of_fixed`, outright
    have := hmin.1
    have hmap : Submodule.map (Morse.cyclicMap h u) F = ⊤ := by
      rw [eq_top_iff, ← range_cyclicMap_eq_top' h hmin hu0]
      rintro _ ⟨c, rfl⟩
      obtain ⟨c', hc', hfix'⟩ := Morse.exists_fixed (Morse.cyclicMap h u) θs hsq hcomm
        (fun θ hθ c => by rw [Morse.cyclicMap_apply, Morse.cyclicMap_apply, map_mul,
          Module.End.mul_apply, hfix θ hθ]) c
      exact ⟨c', (hF c').2 hfix', hc'⟩
    have hle : finrank ℝ V ≤ finrank ℝ F := by
      rw [← finrank_top ℝ V, ← hmap]
      exact Submodule.finrank_map_le _ _
    have hge : Morse.milnorM k ≤ finrank ℝ V :=
      Nat.le_of_dvd Module.finrank_pos (Morse.milnorM_dvd_finrank hk h)
    have hdim : finrank ℝ V = Morse.milnorM k := by omega
    refine ⟨hdim, ?_⟩
    set Φ : F →ₗ[ℝ] V := Morse.cyclicMap h u ∘ₗ F.subtype
    have hsurj : Function.Surjective Φ := by
      rw [← LinearMap.range_eq_top, LinearMap.range_comp, Submodule.range_subtype]
      exact hmap
    have hinj : Function.Injective Φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by omega)).2 hsurj
    exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun c => rfl⟩
  · -- `exists_iso_of_equiv`, outright
    refine ⟨e.symm.trans e', fun α h1 h2 v => ?_⟩
    set c := e.symm v with hc
    have hv : v = Morse.cliffordLift h c u := by rw [← he, hc, LinearEquiv.apply_symm_apply]
    have hJv : J α v = e ⟨Morse.cliffE k α * c, hFmul _ _ c.2⟩ := by
      rw [he, hv, ← Morse.cyclicMap_apply, ← Morse.cyclicMap_apply, Morse.cyclicMap_mul h u h1 h2]
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hJv, LinearEquiv.symm_apply_apply, he',
      he', ← Morse.cyclicMap_apply, ← Morse.cyclicMap_apply, Morse.cyclicMap_mul h' u' h1 h2]

/-! ## A ⇒ B for `k ≤ 8` -/

/-- B restricted to `k ≤ 8` (the range of A). -/
def B_le8 : Prop :=
  ∀ k : ℕ, k ≤ 8 → k % 4 ≠ 3 → ∀ (n n' : ℕ) (Js : ℕ → Mat (Fin n)) (Js' : ℕ → Mat (Fin n')),
    IsMinACSp Js k → IsMinACSp Js' k →
    ∃ T : Matrix (Fin n') (Fin n) ℝ, Tᵀ * T = 1 ∧ T * Tᵀ = 1 ∧
      ∀ α, 1 ≤ α → α ≤ k → T * Js α = Js' α * T

/-- **Polar decomposition**: an invertible `T₀` intertwining two families of anticommuting
(orthogonal) complex structures can be replaced by an orthogonal one, `U = T₀ (T₀ᵀT₀)^{-1/2}`
(`T₀ᵀT₀` commutes with the structures, hence so does its square root). -/
theorem polar {n k : ℕ} {Js Js' : ℕ → Mat (Fin n)} (hJ : Morse.IsAnticommFamily Js k)
    (hJ' : Morse.IsAnticommFamily Js' k) {T₀ W : Mat (Fin n)} (hW : W * T₀ = 1)
    (hT : ∀ α, 1 ≤ α → α ≤ k → T₀ * Js α = Js' α * T₀) :
    ∃ U : Mat (Fin n), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ ∀ α, 1 ≤ α → α ≤ k → U * Js α = Js' α * U := by
  set Sm := T₀ᵀ * T₀
  have hSpsd : Sm.PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self T₀
    rwa [Morse.conjTranspose_real] at this
  have hSc : ∀ α, 1 ≤ α → α ≤ k → Commute Sm (Js α) := by
    intro α h1 h2
    have ht := congrArg Matrix.transpose (hT α h1 h2)
    simp only [transpose_mul, (Morse.isComplexStructure_iff.1 (hJ.cs α h1 h2)).1,
      (Morse.isComplexStructure_iff.1 (hJ'.cs α h1 h2)).1, Matrix.neg_mul, Matrix.mul_neg,
      neg_inj] at ht
    -- ht : Js α * T₀ᵀ = T₀ᵀ * Js' α
    show Sm * Js α = Js α * Sm
    simp only [Sm, Matrix.mul_assoc, hT α h1 h2]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ht]
  set R := CFC.sqrt Sm
  have hR2 : R * R = Sm := CFC.sqrt_mul_sqrt_self Sm hSpsd.nonneg
  have hRt : Rᵀ = R := by
    have h2 := (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg Sm)).isHermitian
    rw [← Morse.conjTranspose_real]; exact h2
  have hRc : ∀ α, 1 ≤ α → α ≤ k → R * Js α = Js α * R := fun α h1 h2 => by
    have : Commute (CFC.sqrt Sm) (Js α) := by
      rw [CFC.sqrt_eq_cfc]; exact (hSc α h1 h2).cfc_nnreal _
    exact this.eq
  have hdetT : IsUnit T₀.det := by
    have := congrArg Matrix.det hW
    rw [det_mul, det_one] at this
    rw [mul_comm] at this
    exact IsUnit.of_mul_eq_one _ this
  have hdetR : IsUnit R.det := by
    have hS : IsUnit Sm.det := by
      simp only [Sm, det_mul, det_transpose]; exact hdetT.mul hdetT
    rw [← hR2, det_mul] at hS
    exact isUnit_of_mul_isUnit_left hS
  have hRR : R * R⁻¹ = 1 := mul_nonsing_inv R hdetR
  have hRR' : R⁻¹ * R = 1 := nonsing_inv_mul R hdetR
  have hRit : R⁻¹ᵀ = R⁻¹ := by rw [transpose_nonsing_inv, hRt]
  refine ⟨T₀ * R⁻¹, ?_, ?_, fun α h1 h2 => ?_⟩
  · calc (T₀ * R⁻¹)ᵀ * (T₀ * R⁻¹) = R⁻¹ * Sm * R⁻¹ := by
          simp only [transpose_mul, hRit, Sm, Matrix.mul_assoc]
      _ = 1 := by rw [← hR2, ← Matrix.mul_assoc, hRR', Matrix.one_mul, hRR]
  · rw [mul_eq_one_comm]
    calc (T₀ * R⁻¹)ᵀ * (T₀ * R⁻¹) = R⁻¹ * Sm * R⁻¹ := by
          simp only [transpose_mul, hRit, Sm, Matrix.mul_assoc]
      _ = 1 := by rw [← hR2, ← Matrix.mul_assoc, hRR', Matrix.one_mul, hRR]
  · have hRi : R⁻¹ * Js α = Js α * R⁻¹ := by
      calc R⁻¹ * Js α = R⁻¹ * Js α * (R * R⁻¹) := by rw [hRR, Matrix.mul_one]
        _ = R⁻¹ * (Js α * R) * R⁻¹ := by simp only [Matrix.mul_assoc]
        _ = R⁻¹ * (R * Js α) * R⁻¹ := by rw [hRc α h1 h2]
        _ = R⁻¹ * R * Js α * R⁻¹ := by simp only [Matrix.mul_assoc]
        _ = Js α * R⁻¹ := by rw [hRR', Matrix.one_mul]
    rw [Matrix.mul_assoc, hRi, ← Matrix.mul_assoc, hT α h1 h2, Matrix.mul_assoc]

/-- A ⇒ B for `k ≤ 8`: A's linear isomorphism (between `ℝⁿ` and `ℝ^{n'}` with B's structures),
made orthogonal by polar decomposition. -/
theorem A_to_B_le8 : A → B_le8 := by
  intro hA k hk hk3 n n' Js Js' hJs hJs'
  obtain ⟨hc, hm⟩ := isMinimal_of_minACSp hJs
  obtain ⟨hc', hm'⟩ := isMinimal_of_minACSp hJs'
  obtain ⟨Tl, hTl⟩ := hA.1 hk hk3 hc hc' hm hm'
  have hn : n = n' := by simpa using Tl.finrank_eq
  subst hn
  set T₀ := LinearMap.toMatrix' (Tl : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  set W := LinearMap.toMatrix' (Tl.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  have hW : W * T₀ = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (Tl.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ (Tl : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) =
        LinearMap.id := by ext v; simp
    rw [this, LinearMap.toMatrix'_id]
  have hT : ∀ α, 1 ≤ α → α ≤ k → T₀ * Js α = Js' α * T₀ := by
    intro α h1 h2
    have hl : (Tl : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ∘ₗ Matrix.toLin' (Js α) =
        Matrix.toLin' (Js' α) ∘ₗ (Tl : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :=
      LinearMap.ext fun v => hTl α h1 h2 v
    have := congrArg LinearMap.toMatrix' hl
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_toLin'] at this
  exact polar ((isACFam_iff Js k).1 hJs.2.1) ((isACFam_iff Js' k).1 hJs'.2.1) hW hT

#rt_check RoundTrip.V15_17.A_to_B_le8 [Morse.exists_iso_of_isMinimal,
  Morse.range_cyclicMap_eq_top, Morse.minimal_of_fixed, Morse.exists_iso_of_equiv]
#rt_check RoundTrip.V15_17.B_to_A [Morse.exists_iso_of_isMinimal, Morse.range_cyclicMap_eq_top,
  Morse.minimal_of_fixed, Morse.exists_iso_of_equiv]
#rt_overlap RoundTrip.V15_17.B_to_A [Morse.exists_iso_of_isMinimal, Morse.range_cyclicMap_eq_top,
  Morse.minimal_of_fixed, Morse.exists_iso_of_equiv]

end RoundTrip.V15_17
