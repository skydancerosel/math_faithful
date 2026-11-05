import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_18

open Matrix

namespace RoundTrip.V15_18

/-- The project's statement (universes instantiated at `0`): for anticommuting complex structures
on `ℝ^n` (any finite index type) and any `u`, `⟨J_αu, J_βu⟩ = δ_{αβ}|u|²`; `Ju ⟂ u` for a complex
structure; and the same two facts for Milnor's eight explicit structures on `ℝ^{16r}`. -/
def A : Prop :=
  type_of% @Morse.IsAnticommFamily.dotProduct_mulVec.{0} ∧
    type_of% @Morse.IsComplexStructure.dotProduct_mulVec_self.{0} ∧
    type_of% @Morse.bott16r_vectorFields

theorem A_holds : A :=
  ⟨@Morse.IsAnticommFamily.dotProduct_mulVec.{0},
    @Morse.IsComplexStructure.dotProduct_mulVec_self.{0}, @Morse.bott16r_vectorFields⟩

/-! Vocabulary: B's `IsACFam` is the project's `IsAnticommFamily`. -/

theorem isACFam_iff {ι : Type} [Fintype ι] [DecidableEq ι] (Js : ℕ → Mat ι) (k : ℕ) :
    IsACFam Js k ↔ Morse.IsAnticommFamily Js k :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.cs, h.anti⟩⟩

/-- A family on any index type of cardinality `n` gives one on `Fin n`. -/
theorem fam_fin {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ → Matrix ι ι ℝ} {k : ℕ}
    (h : Morse.IsAnticommFamily J k) {n : ℕ} (hn : Fintype.card ι = n) :
    ∃ Js : ℕ → Mat (Fin n), Morse.IsAnticommFamily Js k :=
  ⟨_, h.reindex (Fintype.equivFinOfCardEq hn)⟩

/-- `r` copies of a family on `Fin m`: a family on `Fin (r * m)`. -/
theorem fam_mul {m k : ℕ} {Js : ℕ → Mat (Fin m)} (h : Morse.IsAnticommFamily Js k) (r : ℕ) :
    ∃ Js' : ℕ → Mat (Fin (r * m)), Morse.IsAnticommFamily Js' k :=
  fam_fin (h.blockDiagonal (o := Fin r)) (by simp [Fintype.card_prod, mul_comm])

theorem sph_zero_empty (u : Fin 0 → ℝ) : u ∉ sph 0 := by simp [sph, dotProduct]

/-- The fields `u ↦ J_αu` from A's dot-product identities. -/
theorem fields_of_A (hA : A) {n k : ℕ} {Js : ℕ → Mat (Fin n)} (h : Morse.IsAnticommFamily Js k)
    (u : Fin n → ℝ) (hu : u ∈ sph n) :
    (∀ α, 1 ≤ α → α ≤ k → (Js α *ᵥ u) ⬝ᵥ u = 0) ∧
    (∀ α β, 1 ≤ α → α ≤ k → 1 ≤ β → β ≤ k → α ≠ β → (Js α *ᵥ u) ⬝ᵥ (Js β *ᵥ u) = 0) ∧
    LinearIndependent ℝ (fun i : Fin k => Js (i.val + 1) *ᵥ u) := by
  obtain ⟨hA1, hA2, -⟩ := hA
  have hu1 : u ⬝ᵥ u = 1 := hu
  refine ⟨fun α h1 h2 => hA2 (h.cs α h1 h2) u, fun α β h1 h2 h3 h4 hab => ?_, ?_⟩
  · rw [hA1 h h1 h2 h3 h4 u, if_neg hab]
  · refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    have hd := congrArg (fun v => v ⬝ᵥ (Js (i.val + 1) *ᵥ u)) hg
    simp only [sum_dotProduct, smul_dotProduct, zero_dotProduct, smul_eq_mul] at hd
    rw [Finset.sum_eq_single i] at hd
    · rw [hA1 h (by omega) (by omega) (by omega) (by omega) u, if_pos rfl, hu1, mul_one] at hd
      exact hd
    · intro j _ hji
      rw [hA1 h (by omega) (by omega) (by omega) (by omega) u, if_neg (by
        intro h'; exact hji (Fin.ext (by omega))), mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi

theorem hasIndep_of_A (hA : A) {n k : ℕ} {Js : ℕ → Mat (Fin n)}
    (h : Morse.IsAnticommFamily Js k) : HasIndepFields n k :=
  ⟨fun i u => Js (i.val + 1) *ᵥ u,
    fun i => (Continuous.matrix_mulVec continuous_const continuous_id).continuousOn,
    fun u hu => ⟨fun i => (fields_of_A hA h u hu).1 _ (by omega) (by omega),
      (fields_of_A hA h u hu).2.2⟩⟩

/-- A ⇒ B. (1) is A's identities plus orthonormal ⇒ linearly independent. (2), (3): the fields
`u ↦ J_αu` of a family on `ℝ^{rm_k}` (resp. `ℝ^{4r}, ℝ^{8r}, ℝ^{16r}`), the family being `r` copies
of a minimal space of dimension `m_k` (which exists by definition of `m_k` as an `sInf`, or `m_k = 0`
and the sphere is empty) resp. of the project's explicit `bott4`, `bott8`, `bott16`; the existence
of these families is not in A (it is outright, from `Nat.sInf_mem` and the project's
`isAnticommFamily_bott*`), the fields' properties come from A. -/
theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun n k Js hJs u hu => fields_of_A hA ((isACFam_iff Js k).1 hJs) u hu, fun r k => ?_,
    fun r => ⟨?_, ?_, ?_⟩⟩
  · by_cases hne : {n : ℕ | ∃ Js : ℕ → Mat (Fin n), IsMinACSp Js k}.Nonempty
    · have hm : mk k ∈ {n : ℕ | ∃ Js : ℕ → Mat (Fin n), IsMinACSp Js k} := Nat.sInf_mem hne
      obtain ⟨Js, hJs⟩ := hm
      obtain ⟨Js', h'⟩ := fam_mul ((isACFam_iff Js k).1 hJs.2.1) r
      exact hasIndep_of_A hA h'
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      have h0 : mk k = 0 := by unfold mk; rw [hne, Nat.sInf_empty]
      rw [h0, mul_zero]
      exact ⟨fun _ _ => 0, fun _ => continuousOn_const, fun u hu => absurd hu (sph_zero_empty u)⟩
  · obtain ⟨Js, h⟩ := fam_fin (Morse.isAnticommFamily_bott4.blockDiagonal (o := Fin r))
      (n := 4 * r) (by simp [Fintype.card_prod])
    exact hasIndep_of_A hA h
  · obtain ⟨Js, h⟩ := fam_fin (Morse.isAnticommFamily_bott8.blockDiagonal (o := Fin r))
      (n := 8 * r) (by simp [Fintype.card_prod])
    exact hasIndep_of_A hA h
  · obtain ⟨Js, h⟩ := fam_fin (Morse.isAnticommFamily_bott16.blockDiagonal (o := Fin r))
      (n := 16 * r) (by simp [Fintype.card_prod])
    exact hasIndep_of_A hA h

/-- B's (1), which is stated for unit vectors of `ℝⁿ = Fin n → ℝ`, transported to an arbitrary
finite index type and an arbitrary vector (by homogeneity). -/
theorem perp_of_B (hB : B) {ι : Type} [Fintype ι] [DecidableEq ι] {J : ℕ → Mat ι} {k : ℕ}
    (h : Morse.IsAnticommFamily J k) (u : ι → ℝ) :
    (∀ α, 1 ≤ α → α ≤ k → (J α *ᵥ u) ⬝ᵥ u = 0) ∧
    (∀ α β, 1 ≤ α → α ≤ k → 1 ≤ β → β ≤ k → α ≠ β → (J α *ᵥ u) ⬝ᵥ (J β *ᵥ u) = 0) := by
  by_cases hu : u = 0
  · subst hu; simp
  set e := Fintype.equivFin ι
  set Js : ℕ → Mat (Fin (Fintype.card ι)) := fun α => reindex e e (J α)
  have hJs : IsACFam Js k := (isACFam_iff _ _).2 (h.reindex e)
  have hpos : 0 < u ⬝ᵥ u :=
    lt_of_le_of_ne (dotProduct_self_star_nonneg u) (fun h' => hu (dotProduct_self_eq_zero.1 h'.symm))
  set c := Real.sqrt (u ⬝ᵥ u)
  have hc : 0 < c := Real.sqrt_pos.2 hpos
  have hcc : c * c = u ⬝ᵥ u := Real.mul_self_sqrt hpos.le
  set w : Fin (Fintype.card ι) → ℝ := (c⁻¹ • u) ∘ e.symm
  have hdot : ∀ x y : ι → ℝ, (x ∘ e.symm) ⬝ᵥ (y ∘ e.symm) = x ⬝ᵥ y :=
    fun x y => comp_equiv_dotProduct_comp_equiv x y e.symm
  have hmv : ∀ α, Js α *ᵥ w = (c⁻¹ • (J α *ᵥ u)) ∘ e.symm := fun α => by
    simp only [Js, reindex_apply, submatrix_mulVec_equiv]
    congr 1
    have hw' : ((c⁻¹ • u) ∘ e.symm) ∘ e.symm.symm = c⁻¹ • u := by ext; simp
    simp only [w]
    rw [hw', mulVec_smul]
  have hw : w ∈ sph (Fintype.card ι) := by
    show w ⬝ᵥ w = 1
    rw [hdot, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hcc]
    field_simp
  obtain ⟨h1, h2, -⟩ := hB.1 _ k Js hJs w hw
  refine ⟨fun α ha1 ha2 => ?_, fun α β ha1 ha2 hb1 hb2 hab => ?_⟩
  · have := h1 α ha1 ha2
    rw [hmv, hdot, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
    have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc.ne'
    simpa [hc'] using this
  · have := h2 α β ha1 ha2 hb1 hb2 hab
    rw [hmv, hmv, hdot, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at this
    have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc.ne'
    simpa [hc'] using this

/-- B ⇒ A. The perpendicularity statements come from B's (1) (transported from unit vectors of
`Fin n → ℝ` to arbitrary vectors on arbitrary index types); the norm identity
`|J_αu|² = |u|²` is not in B and is proved outright (`J_αᵀJ_α = 1`); the `ℝ^{16r}` statement is the
general one applied to the project's family `isAnticommFamily_bott16r`. -/
theorem B_to_A : B → A := by
  intro hB
  have hA1 : type_of% @Morse.IsAnticommFamily.dotProduct_mulVec.{0} := by
    intro ι _ _ J k h α β h1 h2 h3 h4 u
    split_ifs with hab
    · subst hab
      -- outright: `J_α` is orthogonal
      have hO : (J α)ᵀ * J α = 1 := by
        simpa [mem_orthogonalGroup_iff'] using (h.cs α h1 h2).1
      rw [Morse.dotProduct_mulVec_eq, hO, one_mulVec]
    · exact (perp_of_B hB h u).2 α β h1 h2 h3 h4 hab
  have hA2 : type_of% @Morse.IsComplexStructure.dotProduct_mulVec_self.{0} := by
    intro ι _ _ J hJ u
    have h : Morse.IsAnticommFamily (fun _ => J) 1 :=
      ⟨fun _ _ _ => hJ, fun α β h1 h2 h3 h4 hab => absurd (by omega : α = β) hab⟩
    exact (perp_of_B hB h u).1 1 le_rfl le_rfl
  refine ⟨hA1, hA2, fun r u α β h1 h2 h3 h4 => ?_⟩
  have h := Morse.isAnticommFamily_bott16r r
  exact ⟨hA1 h h1 h2 h3 h4 u, hA2 (h.cs α h1 h2) u⟩

#rt_check RoundTrip.V15_18.A_to_B [Morse.IsAnticommFamily.dotProduct_mulVec,
  Morse.IsComplexStructure.dotProduct_mulVec_self, Morse.bott16r_vectorFields]
#rt_check RoundTrip.V15_18.B_to_A [Morse.IsAnticommFamily.dotProduct_mulVec,
  Morse.IsComplexStructure.dotProduct_mulVec_self, Morse.bott16r_vectorFields]
#rt_overlap RoundTrip.V15_18.B_to_A [Morse.IsAnticommFamily.dotProduct_mulVec,
  Morse.IsComplexStructure.dotProduct_mulVec_self, Morse.bott16r_vectorFields]

end RoundTrip.V15_18
