import Morse
import RoundTrip.Check
import RoundTrip.Blind.«V8_2»

open Set Filter Topology
open scoped ContDiff

namespace RoundTrip.«V8_2»

/-- The project's statement (universes instantiated at 0; `IsVariation N U α B` and `varField`
are definitions: `U ∋ 0` open in a normed space `P`, `α u t ∈ N` for `u ∈ U`, `t ∈ [0, 1]`, fixed
end points, `(u, t) ↦ α u t` smooth on every strip `U × [s, t]` avoiding the finite break set `B`;
`varField α t = ∂α/∂u (0, t)` for `P = ℝ` only): each `α u` lies in `Ω(N; α 0 0, α 0 1)`;
reparametrizing a variation by a smooth `φ` with `φ 0 ∈ U` gives a variation; the variation field
of a 1-parameter variation lies in `TΩ_{α 0}`. -/
def A : Prop :=
  type_of% @Morse.IsVariation.mem_pathSpace.{0,0} ∧
    type_of% @Morse.IsVariation.comp.{0,0,0} ∧
    type_of% @Morse.IsVariation.varField_mem.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.IsVariation.mem_pathSpace, @Morse.IsVariation.comp, @Morse.IsVariation.varField_mem⟩

/-- B ⇒ A holds only because A is provable outright from project lemmas outside the item
(`IsVariation.isPiecewiseSmooth`, `IsVariation.prj_varDeriv`, the strip-derivative lemmas
`contDiffOn_pdU`/`deriv_eq_pdU`, `continuousOn_of_piecewise`); the proofs below re-run the
project's. B (about abstract manifolds) is not used and could not be: it does not specialize to
`N ⊆ V` without an abstract↔embedded dictionary for variations and variation fields. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_, ?_⟩
  · intro V _ _ N P _ _ U α B hα u hu
    exact ⟨hα.isPiecewiseSmooth hu, hα.mem u hu, hα.start u hu, hα.finish u hu⟩
  · intro V _ _ N P _ _ U α B P' _ _ hα φ hφ h0
    exact
      { isOpen := hα.isOpen.preimage hφ.continuous
        zero_mem := h0
        mem := fun _ hu t ht => hα.mem _ hu t ht
        start := fun _ hu => (hα.start _ hu).trans (hα.start _ h0).symm
        finish := fun _ hu => (hα.finish _ hu).trans (hα.finish _ h0).symm
        smooth := fun s t hs hst ht hB =>
          (hα.smooth s t hs hst ht hB).comp ((hφ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
            fun _ hp => mk_mem_prod hp.1 hp.2 }
  · intro V _ _ _ Z _ _ _ W _ _ _ N hN U α B hα
    have hpiece : ∀ s t, 0 ≤ s → s < t → t ≤ 1 → (∀ x ∈ B, x ∉ Ioo s t) →
        ContDiffOn ℝ ∞ (Morse.varField α) (Icc s t) := by
      intro s t hs hst ht hB
      have hF := hα.smooth s t hs hst ht hB
      have h1 : ContDiffOn ℝ ∞
          (fun τ => Morse.pdU (U ×ˢ Icc s t) (fun p : ℝ × ℝ => α p.1 p.2) (0, τ)) (Icc s t) :=
        (Morse.contDiffOn_pdU hα.isOpen hst hF).comp (contDiffOn_const.prodMk contDiffOn_id)
          fun τ hτ => mk_mem_prod hα.zero_mem hτ
      refine h1.congr fun τ hτ => ?_
      exact Morse.deriv_eq_pdU hα.isOpen (F := fun p : ℝ × ℝ => α p.1 p.2)
        (hF.differentiableOn (by simp)) hα.zero_mem hτ
    refine ⟨⟨zero_le_one, Morse.continuousOn_of_piecewise fun s t hs hst ht hB =>
      (hpiece s t hs hst ht hB).continuousOn, B, hpiece⟩,
      fun t ht => hα.prj_varDeriv hN hα.zero_mem ht, ?_, ?_⟩
    · have hev : (fun u => α u 0) =ᶠ[𝓝 0] fun _ => α 0 0 := by
        filter_upwards [hα.isOpen.mem_nhds hα.zero_mem] with u hu
        exact hα.start u hu
      rw [Morse.varField, hev.deriv_eq, deriv_const]
    · have hev : (fun u => α u 1) =ᶠ[𝓝 0] fun _ => α 0 1 := by
        filter_upwards [hα.isOpen.mem_nhds hα.zero_mem] with u hu
        exact hα.finish u hu
      rw [Morse.varField, hev.deriv_eq, deriv_const]

#rt_check RoundTrip.«V8_2».B_to_A [Morse.IsVariation.mem_pathSpace, Morse.IsVariation.comp,
  Morse.IsVariation.varField_mem]
#rt_overlap RoundTrip.«V8_2».B_to_A [Morse.IsVariation.mem_pathSpace, Morse.IsVariation.comp,
  Morse.IsVariation.varField_mem]

/-! A ⇒ B is not proved; see `V8_2.json`. -/

end RoundTrip.«V8_2»
