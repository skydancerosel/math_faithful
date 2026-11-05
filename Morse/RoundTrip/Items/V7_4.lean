import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_4

open Set Filter Topology
open scoped ContDiff

namespace RoundTrip.V7_4

/-- The project's statement (universes instantiated at 0): local flows of smooth first-order
systems with smooth dependence on the initial point (`exists_localFlow`), Theorem 10.1 for
`u'' = F(u, u')` on any finite-dimensional `E` (existence, smooth dependence), and uniqueness of
solutions of `x' = G(x)` / of the second-order system on open preconnected time sets for `C¹`
right-hand sides on an arbitrary normed space. -/
def A : Prop :=
  type_of% @Morse.exists_localFlow.{0} ∧ type_of% @Morse.theorem_10_1.{0} ∧
    type_of% @Morse.ode_eqOn.{0} ∧ type_of% @Morse.theorem_10_1_unique.{0}

theorem A_holds : A :=
  ⟨@Morse.exists_localFlow, @Morse.theorem_10_1, @Morse.ode_eqOn, @Morse.theorem_10_1_unique⟩

/-- **A ⇒ B.** Existence and smooth dependence from `theorem_10_1` (with `E = ℝⁿ`), uniqueness on
`(-ε, ε)` from `theorem_10_1_unique` (with `v = u'`, at `t₀ = 0`). Differentiability of the
solution in `t` comes from its joint smoothness on `W × (-ε, ε)`. -/
theorem A_to_B : A → B := by
  rintro ⟨-, h101, -, huniq⟩ n U F hU hF z₁ hz₁
  obtain ⟨W, hW, ε, hε, u, hsm, hsol⟩ := h101 hU hF hz₁
  refine ⟨W, hW, ε, hε, u, hsm, fun z hz => ?_⟩
  obtain ⟨h0, hd0, hts⟩ := hsol z hz
  have hdiff : ∀ t ∈ Ioo (-ε) ε, DifferentiableAt ℝ (u z) t := by
    intro t ht
    have hc : ContDiffOn ℝ ∞ (fun t => u z t) (Ioo (-ε) ε) :=
      hsm.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht => ⟨hz, ht⟩)
    exact (hc.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
  have hsolz : IsODESol U F ε z.1 z.2 (u z) :=
    ⟨h0, hd0, fun t ht => ⟨hdiff t ht, (hts t ht).1, (hts t ht).2⟩⟩
  refine ⟨hsolz, fun w hw => ?_⟩
  have h0mem : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  refine huniq hU (hF.of_le (by simp)) isOpen_Ioo isPreconnected_Ioo
    (v₁ := deriv w) (v₂ := deriv (u z))
    (fun t ht => ⟨(hw.2.2 t ht).1.hasDerivAt, (hw.2.2 t ht).2.2, (hw.2.2 t ht).2.1⟩)
    (fun t ht => ⟨(hdiff t ht).hasDerivAt, (hts t ht).2, (hts t ht).1⟩) h0mem
    (by rw [hw.1, h0]) (by rw [hw.2.1, hd0])

#rt_check RoundTrip.V7_4.A_to_B [Morse.exists_localFlow, Morse.theorem_10_1, Morse.ode_eqOn,
  Morse.theorem_10_1_unique]

end RoundTrip.V7_4
