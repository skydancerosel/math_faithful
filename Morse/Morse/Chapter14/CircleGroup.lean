import Morse.Chapter14.PeriodicityGroups

/-!
Milnor, *Morse Theory*, §23, Theorem 23.5 (p. 130); Exposition/Chapter14.md, §3.

# `π₁ S¹ ≅ ℤ` as groups, and Theorem 23.5 with group isomorphisms onto `ℤ`

## Milnor's text, paraphrased

(p. 130) **Theorem 23.5 (Bott)**: the stable homotopy groups of the unitary group are
`π_0 U ≅ π_2 U ≅ π_4 U ≅ ⋯ ≅ 0` and `π_1 U ≅ π_3 U ≅ π_5 U ≅ ⋯ ≅ ℤ`.  *Proof*: by the periodicity
theorem it suffices to look at `π_0 U(1)` and `π_1 U(1)`; `U(1)` is the circle.

## What is formalized

* `Morse.Homotopy.piOneCircleMulEquiv`: **`π_1(S¹, 1) ≃* Multiplicative ℤ`** as groups (the
  additive group `ℤ`, written multiplicatively to match the multiplicative group `π_1`).
* `Morse.Homotopy.nonempty_mulEquiv_pi_one_unitary_circle`: `π_1 U(m) ≃* π_1 S¹` for `m ≥ 1`.
* `Morse.theorem_23_5_mulEquiv`: **Theorem 23.5, odd degrees, as groups**: in the stable range
  `2k + 2 ≤ 2m`, `π_{2k+1} U(m) ≃* Multiplicative ℤ`.  (The even degrees are trivial groups,
  `Morse.theorem_23_5`; `π_0` is not a group.)

## What Milnor leaves implicit

* **`π_1 S¹ ≅ ℤ` as groups.**  Milnor quotes it.  Here it is Mathlib's covering-space theory:
  `t ↦ e^{it}`, `ℝ → S¹`, is the quotient covering by the deck group `2πℤ`
  (`Circle.isAddQuotientCoveringMap_exp`), and for a simply connected total space (`ℝ` is
  contractible) the monodromy action at `0 ∈ exp⁻¹(1)` is an anti-isomorphism
  `π_1(S¹, 1) ≃* (2πℤ)ᵐᵒᵖ` (`IsAddQuotientCoveringMap.fundamentalGroupEquiv`); the deck group is
  abelian, so the `ᵐᵒᵖ` is harmless, and `2πℤ ≅ ℤ`.  Mathlib's `π_1` as fundamental group is
  identified with the cube model of `π_1` used throughout the project by
  `HomotopyGroup.pi1MulEquivFundamentalGroup`.
* **Groups along the whole chain.**  Stability `π_1 U(1) → π_1 U(m)` and the reindexing
  homeomorphism `U(1 + k) ≅ U(Fin (1 + k))` are group isomorphisms because the maps are induced by
  continuous maps (`Morse.Homotopy.homotopyGroupHom`); the periodicity steps are the group
  isomorphisms of `Morse/Chapter14/PeriodicityGroups.lean`.
-/

open Matrix Function Topology Real
open scoped Topology.Homotopy

noncomputable section

namespace Morse

namespace Homotopy

/-- The deck group `2πℤ` of `t ↦ e^{it}` is `ℤ`. -/
def intAddEquivZMultiplesTwoPi : ℤ ≃+ AddSubgroup.zmultiples (2 * π) :=
  (AddMonoidHom.ofInjective (f := zmultiplesHom ℝ (2 * π)) (by
    intro a b h; simpa [Real.pi_ne_zero] using h)).trans
    (AddEquiv.addSubgroupCongr (AddSubgroup.range_zmultiplesHom _))

/-- **`π_1(S¹) ≅ ℤ` as groups** (quoted by Milnor, p. 130): the monodromy of the universal
covering `ℝ → S¹`, `t ↦ e^{it}`. -/
def piOneCircleMulEquiv : π_ 1 Circle 1 ≃* Multiplicative ℤ :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.trans
    ((Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
      (⟨0, by simp⟩ : Circle.exp ⁻¹' {(1 : Circle)})).trans
      (MulOpposite.opMulEquiv.symm.trans
        (AddEquiv.toMultiplicative intAddEquivZMultiplesTwoPi.symm)))

/-- A homeomorphism carrying `x` to `y` induces `π_{n+1}(X, x) ≃* π_{n+1}(Y, y)`. -/
def piMulEquivOfHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y)
    {x : X} {y : Y} (hxy : h x = y) (n : ℕ) : π_ (n + 1) X x ≃* π_ (n + 1) Y y := by
  subst hxy
  exact MulEquiv.ofBijective (homotopyGroupHom (N := Fin (n + 1)) (h : C(X, Y)) x)
    (bijective_homotopyGroupMap_homeomorph h x)

/-- **`π_1 U(m) ≅ π_1 S¹` as groups for `m ≥ 1`** (stability from `U(1) = S¹`). -/
theorem nonempty_mulEquiv_pi_one_unitary_circle {m : ℕ} (hm : 1 ≤ m) :
    Nonempty (π_ 1 (unitaryGroup (Fin m) ℂ) 1 ≃* π_ 1 Circle 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 1 + k := ⟨m - 1, by omega⟩
  have e₁ := MulEquiv.ofBijective (homotopyGroupHom (N := Fin 1) (unitaryInclC (𝕜 := ℂ) 1 k) 1)
    (bijective_homotopyGroupMap_unitaryIncl_complex (m := 1) (k := k) (i := 1) (by omega) 1)
  rw [show unitaryInclC (𝕜 := ℂ) 1 k 1 = 1 from map_one (unitaryIncl ℂ (Fin 1) (Fin k))] at e₁
  have e₂ := piMulEquivOfHomeomorph
    (unitaryCongr (𝕜 := ℂ) (finSumFinEquiv (m := 1) (n := k)))
    (x := 1) (y := 1) (Subtype.ext (by simp [unitaryCongr])) 0
  have e₃ := piMulEquivOfHomeomorph unitaryOneHomeomorph unitaryOneHomeomorph_one 0
  exact ⟨e₂.symm.trans (e₁.symm.trans e₃)⟩

end Homotopy

/-- **Theorem 23.5 (Bott), odd degrees, as groups** (Milnor p. 130): in the stable range
`2k + 2 ≤ 2m`, `π_{2k+1} U(m) ≅ ℤ` as groups. -/
theorem theorem_23_5_mulEquiv {m k : ℕ} (hk : 2 * k + 2 ≤ 2 * m) :
    Nonempty (π_ (2 * k + 1) (unitaryGroup (Fin m) ℂ) 1 ≃* Multiplicative ℤ) := by
  obtain ⟨e₁⟩ := nonempty_mulEquiv_pi_unitary_odd hk
  obtain ⟨e₂⟩ := Homotopy.nonempty_mulEquiv_pi_one_unitary_circle (m := m) (by omega)
  exact ⟨e₁.trans (e₂.trans Homotopy.piOneCircleMulEquiv)⟩

end Morse
