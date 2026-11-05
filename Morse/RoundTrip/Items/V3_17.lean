import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_17

open CategoryTheory Morse.Homology Module
open scoped ContDiff Manifold

namespace RoundTrip.V3_17

/-- The project's statement: the one listed theorem (`Morse.IsEulerNumber` is a definition). -/
def A : Prop := type_of% @Morse.exists_isEulerNumber

theorem A_holds : A := @Morse.exists_isEulerNumber

/-- B's tangency `v q ∈ tanN hN q` is the project's `v q ∈ range (mfd val q)` by definition. -/
example {K d m : ℕ} {N : Set (Rn (K + 1))}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn (d + 1)) (Rn m) N) (q : N) :
    Milnor.Tub.tanN hN q = (letI := hN.chartedSpace; LinearMap.range
      ((Milnor.mfd 𝓘(ℝ, Rn (d + 1)) 𝓘(ℝ, Rn (K + 1)) (Subtype.val : N → Rn (K + 1)) q :
        Rn (d + 1) →L[ℝ] Rn (K + 1)) : Rn (d + 1) →ₗ[ℝ] Rn (K + 1))) := rfl

/-- The case `K = 0` of `B` is vacuous: a slice chart identifies `ℝ¹` locally with
`ℝ^{d+1} × ℝ^m`, so `m = 0`, every slice chart domain lies in `N`, and `N` is a nonempty compact
open subset of `ℝ¹`, impossible. -/
theorem no_K_zero {d m : ℕ} {N : Set (Rn (0 + 1))}
    (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (0 + 1)) (Rn (d + 1)) (Rn m) N) (hc : IsCompact N)
    (hne : N.Nonempty) : False := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨σ, hσ⟩ := hN x hx
  have hloc := σ.φ.isLocalDiffeomorphAt 𝓘(ℝ, Rn (0 + 1)) 𝓘(ℝ, Rn (d + 1) × Rn m) ∞ hσ
  have hbij := (hloc.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv.finrank_eq
  have hm : m = 0 := by
    have : finrank ℝ (TangentSpace 𝓘(ℝ, Rn (0 + 1)) x) = 1 := finrank_euclideanSpace_fin
    have h2 : finrank ℝ (TangentSpace 𝓘(ℝ, Rn (d + 1) × Rn m) (σ.φ x)) = d + 1 + m := by
      change finrank ℝ (Rn (d + 1) × Rn m) = _
      simp [finrank_prod]
    omega
  subst hm
  have hopen : IsOpen N := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨τ, hτ⟩ := hN p hp
    refine ⟨τ.φ.source, fun q hq ↦ (τ.slice q hq).2 (Subsingleton.elim _ _), τ.φ.open_source,
      hτ⟩
  have hclopen : IsClopen N := ⟨hc.isClosed, hopen⟩
  rcases isClopen_iff.1 hclopen with h | h
  · exact (Set.nonempty_of_mem hx).ne_empty h
  · rw [h] at hc
    exact noncompact_univ (Rn (0 + 1)) hc

/-- An index sum over an injective enumeration of the zeros is the `finsum` over the zero set. -/
lemma sum_enum_eq_finsum {α : Type} (S : Set α) (g : α → ℤ) {j : ℕ} (z : Fin j → α)
    (hz : Function.Injective z) (hzS : ∀ q, q ∈ S ↔ ∃ i, q = z i) :
    ∑ i, g (z i) = ∑ᶠ q ∈ S, g q := by
  classical
  have hS : S = Set.range z := by ext q; rw [hzS]; exact ⟨fun ⟨i, h⟩ ↦ ⟨i, h.symm⟩,
    fun ⟨i, h⟩ ↦ ⟨i, h.symm⟩⟩
  rw [hS, finsum_mem_range hz]
  exact (finsum_eq_sum_of_fintype _).symm

theorem A_to_B : A → B := by
  classical
  intro hA F _ K d m N hN hc hne
  let _ := hN.chartedSpace
  intro v hv hvT hfin
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact (no_K_zero hN hc hne).elim
  obtain ⟨χN, hχ⟩ := hA hN hc hne hK
  -- enumerate the zeros
  let s := hfin.toFinset
  let e := s.equivFin
  let z : Fin s.card → N := fun i ↦ (e.symm i).1
  have hz : Function.Injective z := fun i i' h ↦ e.symm.injective (Subtype.ext h)
  have hzS : ∀ q, q ∈ {q : N | v q = 0} ↔ ∃ i, q = z i := by
    intro q
    constructor
    · intro hq
      have hqs : q ∈ s := hfin.mem_toFinset.2 hq
      exact ⟨e ⟨q, hqs⟩, by simp [z]⟩
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.1 (e.symm i).2
  have h1 := hχ v hv hvT z hz (fun q ↦ hzS q)
  rw [← sum_enum_eq_finsum _ _ z hz hzS, h1,
    Morse.IsEulerNumber.eq_sum_bettiNumber (𝕜 := F) hN hc hne (Homeomorph.refl N) hK hχ]
  unfold chiN
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 2
  exact (finrank_subsetHomology_eq_bettiNumber (𝕜 := F) (Set.empty_subset _) rfl rfl i).symm

theorem B_to_A : B → A := by
  intro hB K d m N hN hc hne _
  refine ⟨chiN ℚ d N, fun v hv hvT j z hz hzero ↦ ?_⟩
  let _ := hN.chartedSpace
  have hfin : {q : N | v q = 0}.Finite := by
    refine (Set.finite_range z).subset fun q hq ↦ ?_
    obtain ⟨i, rfl⟩ := (hzero q).1 hq
    exact ⟨i, rfl⟩
  rw [sum_enum_eq_finsum {q : N | v q = 0} _ z hz (fun q ↦ hzero q)]
  exact hB ℚ K d m N hN hc hne v hv hvT hfin

#rt_check RoundTrip.V3_17.A_to_B [Morse.exists_isEulerNumber]
#rt_check RoundTrip.V3_17.B_to_A [Morse.exists_isEulerNumber]
#rt_overlap RoundTrip.V3_17.B_to_A [Morse.exists_isEulerNumber]

end RoundTrip.V3_17
