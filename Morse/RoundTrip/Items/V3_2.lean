import Morse
import RoundTrip.Check
import RoundTrip.Blind.V3_2

open Set Metric
open scoped ContDiff Manifold

noncomputable section

namespace RoundTrip.V3_2

/-- The project's statement (the extrema lemmas of Reeb's theorem), universes instantiated at
`0`. -/
def A : Prop :=
  (type_of% @Morse.isCriticalPointM_of_isLocalMin.{0, 0}) ∧
  (type_of% @Morse.indexM_eq_zero_of_isLocalMin.{0, 0}) ∧
  (type_of% @Morse.indexM_eq_finrank_of_isLocalMax.{0, 0}) ∧
  (type_of% @Morse.exists_morse_chart_of_isLocalMin.{0, 0}) ∧
  (type_of% @Morse.exists_morse_chart_of_isLocalMax.{0, 0}) ∧
  (type_of% @Morse.exists_image_closedBall_eq_sublevel.{0, 0})

theorem A_holds : A :=
  ⟨@Morse.isCriticalPointM_of_isLocalMin.{0, 0}, @Morse.indexM_eq_zero_of_isLocalMin.{0, 0},
    @Morse.indexM_eq_finrank_of_isLocalMax.{0, 0}, @Morse.exists_morse_chart_of_isLocalMin.{0, 0},
    @Morse.exists_morse_chart_of_isLocalMax.{0, 0},
    @Morse.exists_image_closedBall_eq_sublevel.{0, 0}⟩

/-! ### Glue -/

section Glue

variable {X : Type} [TopologicalSpace X] {n : ℕ}

instance : CompactSpace (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)

/-- An injective map, continuous on the closed ball, into a Hausdorff space is a homeomorphism of
the ball onto its image. -/
def homeoImage [T2Space X] (h : EuclideanSpace ℝ (Fin n) → X)
    (hc : ContinuousOn h (closedBall 0 1)) (hi : InjOn h (closedBall 0 1)) :
    closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ (h '' closedBall 0 1) :=
  have hcont : Continuous (fun z : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      (⟨h z.1, mem_image_of_mem h z.2⟩ : h '' closedBall 0 1)) :=
    (continuousOn_iff_continuous_domRestrict.1 hc).subtype_mk _
  hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ ⟨fun a b hab =>
    Subtype.ext (hi a.2 b.2 (congrArg Subtype.val hab)), fun ⟨_, z, hz, rfl⟩ => ⟨⟨z, hz⟩, rfl⟩⟩)

/-- Balls of equal dimension. -/
def ballCongr {k m : ℕ} (h : k = m) :
    closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 ≃ₜ closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
  subst h; exact Homeomorph.refl _

end Glue

theorem A_to_B : A → B := by
  intro hA n M _ _ _ _ _ f p q hf hpq hp hq honly hp0 hq1 hbd
  obtain ⟨hcrit, -, -, hmin, hmax, hball⟩ := hA
  have hfc : Continuous f := hf.continuous
  have hfU : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f univ := hf.contMDiffOn
  -- `p` is the strict minimum, `q` the strict maximum
  have hpmin : ∀ x, x ≠ p → f p < f x := by
    intro x hx
    refine lt_of_le_of_ne (hbd x).1 fun hfx => ?_
    have hc := hcrit (E := EuclideanSpace ℝ (Fin n)) (Filter.Eventually.of_forall fun y =>
      hfx ▸ (hbd y).1 : IsLocalMin f x)
    rcases honly x hc with rfl | rfl
    · exact hx rfl
    · rw [hp0, hq1] at hfx; norm_num at hfx
  have hqmax : ∀ x, x ≠ q → f x < f q := by
    intro x hx
    refine lt_of_le_of_ne (hbd x).2 fun hfx => ?_
    have hc := hcrit (E := EuclideanSpace ℝ (Fin n)) (f := fun y => -f y)
      (Filter.Eventually.of_forall fun y => by simp only [neg_le_neg_iff]; exact hfx ▸ (hbd y).2)
    have hc' : Morse.IsCriticalPointM (EuclideanSpace ℝ (Fin n)) f x := by
      have h1 : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) (fun y => -f y) x = 0 := hc
      have h2 : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) (fun y => -f y) x =
          -mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) f x :=
        (((hf.mdifferentiable (by simp)) x).hasMFDerivAt.neg).mfderiv
      change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) f x = 0
      rw [h2] at h1
      exact neg_eq_zero.1 h1
    rcases honly x hc' with rfl | rfl
    · rw [hp0, hq1] at hfx; norm_num at hfx
    · exact hx rfl
  -- Morse charts at the extrema
  obtain ⟨y₁, -, hp₁, -, hy₁0, hy₁⟩ := hmin isOpen_univ (mem_univ p) hfU hp
    (Filter.Eventually.of_forall fun x => (hbd x).1)
  obtain ⟨y₂, -, hq₂, -, hy₂0, hy₂⟩ := hmax isOpen_univ (mem_univ q) hfU hq
    (Filter.Eventually.of_forall fun x => (hbd x).2)
  obtain ⟨δ₁, hδ₁, h₁⟩ := hball hfc hpmin y₁ hp₁ hy₁0 hy₁
  obtain ⟨δ₂, hδ₂, h₂⟩ := hball (f := fun x => -f x) hfc.neg
    (fun x hx => neg_lt_neg (hqmax x hx)) y₂ hq₂ hy₂0
    (fun x hx => by rw [hy₂ x hx]; ring)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ε hε hεδ => ⟨?_, ?_⟩⟩
  · obtain ⟨hc, hi, him, -⟩ := h₁ ε hε (hεδ.trans_le (min_le_left _ _))
    have heq : (fun v => y₁.symm (√ε • v)) '' closedBall 0 1 = f ⁻¹' Icc 0 ε := by
      rw [him]
      ext x
      simp only [mem_ofPred_eq, mem_preimage, mem_Icc, hp0, zero_add]
      exact ⟨fun h => ⟨hp0 ▸ (hbd x).1, h⟩, fun h => h.2⟩
    exact ⟨((homeoImage _ hc hi).trans (Homeomorph.setCongr heq)).symm.trans
      (ballCongr finrank_euclideanSpace_fin)⟩
  · obtain ⟨hc, hi, him, -⟩ := h₂ ε hε (hεδ.trans_le (min_le_right _ _))
    have heq : (fun v => y₂.symm (√ε • v)) '' closedBall 0 1 = f ⁻¹' Icc (1 - ε) 1 := by
      rw [him]
      ext x
      simp only [mem_ofPred_eq, mem_preimage, mem_Icc, hq1]
      constructor
      · intro h
        exact ⟨by linarith, hq1 ▸ (hbd x).2⟩
      · intro h
        linarith [h.1]
    exact ⟨((homeoImage _ hc hi).trans (Homeomorph.setCongr heq)).symm.trans
      (ballCongr finrank_euclideanSpace_fin)⟩

#rt_check RoundTrip.V3_2.A_to_B [Morse.isCriticalPointM_of_isLocalMin,
  Morse.indexM_eq_zero_of_isLocalMin, Morse.indexM_eq_finrank_of_isLocalMax,
  Morse.exists_morse_chart_of_isLocalMin, Morse.exists_morse_chart_of_isLocalMax,
  Morse.exists_image_closedBall_eq_sublevel]

end RoundTrip.V3_2

end
