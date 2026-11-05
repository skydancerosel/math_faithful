import Milnor.Chapter5.OrSign

/-!
# Algebraic properties of the sign of a linear map

Consequences of the API of `orSign`: its values are `±1` for bijective maps, it squares to `1`,
inverse maps have inverse signs, `orSign a b T = orSign b a T` for endomorphisms, the target
orientation is determined by the sign, and `orSign a a T = sgn (det T)`.
-/

open Module

noncomputable section

namespace Milnor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {n : ℕ}

theorem orSign_eq_one_or_neg_one (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (a : Orientation ℝ E (Fin n)) (b : Orientation ℝ F (Fin n)) {T : E →L[ℝ] F}
    (hT : Function.Bijective T) : orSign a b T = 1 ∨ orSign a b T = -1 := by
  have hne : orSign a b T ≠ 0 := (orSign_ne_zero_iff hE hF a b T).2 hT
  rcases sgn_mem (x := (b.someVector.compLinearMap T.toLinearMap) (orTuple a) *
      a.someVector (orTuple a)) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hne

theorem orSign_mul_self (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (a : Orientation ℝ E (Fin n)) (b : Orientation ℝ F (Fin n)) {T : E →L[ℝ] F}
    (hT : Function.Bijective T) : orSign a b T * orSign a b T = 1 := by
  rcases orSign_eq_one_or_neg_one hE hF a b hT with h | h <;> rw [h] <;> norm_num

theorem orSign_comp_eq_one (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (a : Orientation ℝ E (Fin n)) (b : Orientation ℝ F (Fin n)) {T : E →L[ℝ] F} {S : F →L[ℝ] E}
    (h : S.comp T = ContinuousLinearMap.id ℝ E) : orSign b a S * orSign a b T = 1 := by
  rw [← orSign_comp hE hF a b a T S, h, orSign_id]

theorem orSign_symm (hE : finrank ℝ E = n) (a b : Orientation ℝ E (Fin n)) {T : E →L[ℝ] E}
    (hT : Function.Bijective T) : orSign a b T = orSign b a T := by
  have h1 : orSign a b T = orSign b b T * orSign a b (ContinuousLinearMap.id ℝ E) := by
    rw [← orSign_comp hE hE a b b (ContinuousLinearMap.id ℝ E) T, ContinuousLinearMap.comp_id]
  have h2 : orSign b b T = orSign a b (ContinuousLinearMap.id ℝ E) * orSign b a T := by
    rw [← orSign_comp hE hE b a b T (ContinuousLinearMap.id ℝ E), ContinuousLinearMap.id_comp]
  have h3 : orSign a b (ContinuousLinearMap.id ℝ E) * orSign a b (ContinuousLinearMap.id ℝ E) = 1 :=
    orSign_mul_self hE hE a b Function.bijective_id
  calc orSign a b T
      = orSign a b (ContinuousLinearMap.id ℝ E) * orSign a b (ContinuousLinearMap.id ℝ E) *
          orSign b a T := by rw [h1, h2]; ring
    _ = orSign b a T := by rw [h3, one_mul]

theorem orientation_eq_of_orSign_eq (hn : 0 < n) (hE : finrank ℝ E = n) (hF : finrank ℝ F = n)
    (a : Orientation ℝ E (Fin n)) {b b' : Orientation ℝ F (Fin n)} {T : E →L[ℝ] F}
    (hT : Function.Bijective T) (h : orSign a b T = orSign a b' T) : b = b' := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rcases Orientation.eq_or_eq_neg b b' (by rw [Fintype.card_fin, hF]) with hbb | hbb
  · exact hbb
  · exfalso
    rw [hbb, orSign_neg_right hE] at h
    have hne : orSign a b' T ≠ 0 := (orSign_ne_zero_iff hE hF a b' T).2 hT
    omega

theorem orSign_self_eq_sgn_det' (hn : 0 < n) (hE : finrank ℝ E = n) (a : Orientation ℝ E (Fin n))
    (T : E →L[ℝ] E) : orSign a a T = sgn (LinearMap.det (T : E →ₗ[ℝ] E)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hcard : Fintype.card (Fin n) = finrank ℝ E := by rw [Fintype.card_fin, hE]
  set e := a.someBasis hcard with he
  have ha : rayOfNeZero ℝ e.det e.det_ne_zero = a := a.someBasis_orientation hcard
  have hc : e.det.compLinearMap (T : E →ₗ[ℝ] E) = (LinearMap.det (T : E →ₗ[ℝ] E)) • e.det := by
    ext v
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul]
    exact e.det_comp _ v
  exact orSign_eq_sgn e.det_ne_zero e.det_ne_zero ha ha hc

end Milnor
