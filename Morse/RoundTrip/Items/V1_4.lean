import Morse
import RoundTrip.Check
import RoundTrip.Blind.V1_4

open scoped ContDiff Manifold

namespace RoundTrip.V1_4

/-- The project's statement: the type of the one listed theorem (`IsCriticalPointM`,
`hessianM`, `indexM`, `nullityM`, `IsNondegenerateCriticalPointM`, `IsMorseFunction` are
vocabulary), universes instantiated at `0`. -/
def A : Prop := type_of% @Morse.isCriticalPointM_iff_milnor.{0, 0}

theorem A_holds : A := @Morse.isCriticalPointM_iff_milnor.{0, 0}

/-- `B ⇒ A`. `A` (Milnor's `f_* = 0` agrees with the companion project's "`df_p` not
surjective") is elementary linear algebra; it is re-proved directly, without `B` (which says
nothing about `Milnor.IsCriticalPoint`) and without the item's theorem. -/
theorem B_to_A : B → A := by
  intro _ E _ _ M _ _ f p
  rw [Milnor.IsCriticalPoint, Milnor.IsRegularPoint, Morse.IsCriticalPointM]
  have h := Morse.surjective_iff_ne_zero (V := E) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f p)
  constructor
  · intro h0 hs
    exact (h.1 hs) h0
  · intro hns
    by_contra h0
    exact hns (h.2 h0)

/-! ### Vocabulary check (not part of `A`): all of `B` except Milnor's vector-field formula
`f_**(v, w) = ṽ_p(w̃ f)` holds for the project's `hessianM`/`indexM`. -/

/-- Clause (a) of `B` (Milnor's definition of `f_**` through extending vector fields). -/
def MilnorFormula : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : M → ℝ) (p : M), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f → Morse.IsCriticalPointM E f p →
    (∀ v w : E, ∀ X Y : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun x : M => (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) →
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞ (fun x : M => (⟨x, Y x⟩ : TangentBundle 𝓘(ℝ, E) M)) →
      X p = v → Y p = w →
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (fun x => mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x (Y x)) p (X p) = Morse.hessianM E f p v w)

/-- Everything in `B` but clause (a) — symmetry, the coordinate formula in the preferred chart,
and `indexM` = Milnor's index — holds for the project's definitions. -/
theorem B_of_milnorFormula (ha : MilnorFormula) : B := by
  intro E _ _ _ M _ _ _ _ f p hf hcrit
  refine ⟨ha E M f p hf hcrit, fun v w => ?_, fun v w => ?_, ?_⟩
  · exact Morse.hessianM_symm (hf.contMDiffAt.of_le (by norm_cast)) v w
  · have hy := Morse.isSmoothCoord_chartAt (E := E) p
    have hp := mem_chart_source E p
    have hD : ∀ u, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p) p u = u := by
      intro u
      rw [hy.mfderiv_eq hp]
      have hev : (chartAt E p ∘ (chartAt E p).symm) =ᶠ[nhds (chartAt E p p)] id :=
        (chartAt E p).eventually_right_inverse ((chartAt E p).map_source hp)
      rw [hev.fderiv_eq, fderiv_id]
      rfl
    have key : ∀ g : M → E, g = ⇑(chartAt E p) →
        ∀ u : E, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g p u : E) = u := by
      rintro g rfl
      exact hD
    have hv := key _ (Morse.extChartAt_self_coe p)
    rw [hv v, hv w, Morse.extChartAt_self_coe_symm, Morse.extChartAt_self_coe]
    have h2 := Morse.contDiffAt_comp_chartAt_symm (hf.contMDiffAt.of_le (by norm_cast)) (p := p)
    have hd : DifferentiableAt ℝ (fderiv ℝ (f ∘ (chartAt E p).symm)) (chartAt E p p) :=
      (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    rw [fderiv_clm_apply hd (differentiableAt_const _), Morse.hessianM_eq_chartAt]
    simp
    exact Morse.hessian_symm h2 v w
  · have h := (Morse.index_isGreatest (Morse.hessianM E f p)).csSup_eq
    exact h.symm

#rt_check RoundTrip.V1_4.B_to_A [Morse.isCriticalPointM_iff_milnor]
#rt_overlap RoundTrip.V1_4.B_to_A [Morse.isCriticalPointM_iff_milnor]

end RoundTrip.V1_4
