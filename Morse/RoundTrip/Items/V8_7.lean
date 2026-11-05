import Morse
import RoundTrip.Check
import RoundTrip.Blind.V8_7
import RoundTrip.Bridge

open Set Filter Topology
open scoped ContDiff Manifold RealInnerProductSpace

namespace RoundTrip.V8_7

/-- The project's statement (universe instantiated at 0); the other declarations of the item
(`Morse.jump`, `Morse.covD`, `Morse.accel`, `Morse.firstVariation`) are definitions. For
`c, X : ℝ → V` (`V` a real inner product space) and a finite set `B` such that `c` is
differentiable at every point of `(0, 1)` off `B`, the jump sum `Σᶠ_{t ∈ (0,1)} ⟨X t, Δ_t c'⟩` is
the finite sum over `B ∩ (0, 1)`. -/
def A : Prop := type_of% @Morse.finsum_jump_eq_sum.{0}

theorem A_holds : A := @Morse.finsum_jump_eq_sum

/-! Neither `A → B` nor `B → A` is proved; see `V8_7.json`. Below: the embedded special case. -/

namespace Emb

set_option linter.unusedSectionVars false

open RoundTrip.Bridge

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {n : ℕ} {N : Set V}
  {hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N}

/-- **Dictionary: one-sided velocities.** The blind velocity within `s` of a curve in `N`, read in
`V`, is the derivative within `s` of the curve in `V` (both are `0` where not differentiable). -/
theorem D_mfderivWithin_curve (c : ℝ → Sub hN) {s : Set ℝ} {t : ℝ}
    (hs : UniqueDiffWithinAt ℝ s t) :
    D hN (c t) (mfderivWithin 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t 1) = derivWithin (incl hN ∘ c) s t := by
  by_cases h : MDifferentiableWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) c s t
  · exact ((hasDerivWithinAt_incl_comp h).derivWithin hs).symm
  · rw [mfderivWithin_zero_of_not_mdifferentiableWithinAt h,
      derivWithin_zero_of_not_differentiableWithinAt
        (mt mdifferentiableWithinAt_curve_iff.2 h)]
    exact map_zero _

/-- **Dictionary: the velocity jump** `Δ_t V` of the blind file is the project's `Morse.jump`. -/
theorem D_Vjump (c : ℝ → Sub hN) (t : ℝ) :
    D hN (c t) (Vjump (n := n) c t) = Morse.jump (incl hN ∘ c) t := by
  have h1 := D_mfderivWithin_curve c (uniqueDiffWithinAt_Ici t)
  have h2 := D_mfderivWithin_curve c (uniqueDiffWithinAt_Iic t)
  exact (D_tsub_aux _ _ _).trans (congrArg₂ (· - ·) h1 h2)

/-- From A: the jump of `c` vanishes at every point of `(0, 1)` off `B` (test field supported at
the point). -/
theorem jump_eq_zero_of_A (hA : A) {c : ℝ → V} {B : Finset ℝ}
    (hc : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ B → DifferentiableAt ℝ c x) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) (hx₀B : x₀ ∉ B) : Morse.jump c x₀ = 0 := by
  classical
  set X : ℝ → V := fun t => if t = x₀ then Morse.jump c x₀ else 0
  have h := hA (c := c) (X := X) (B := B) hc
  have hR : ∑ x ∈ B with x ∈ Ioo (0 : ℝ) 1, ⟪X x, Morse.jump c x⟫ = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxB : x ∈ B := (Finset.mem_filter.1 hx).1
    have hne : x ≠ x₀ := fun e => hx₀B (e ▸ hxB)
    simp [X, hne]
  have hL : ∑ᶠ t ∈ Ioo (0 : ℝ) 1, ⟪X t, Morse.jump c t⟫ = ⟪Morse.jump c x₀, Morse.jump c x₀⟫ := by
    rw [finsum_mem_def, finsum_eq_single _ x₀ fun x hx => ?_]
    · simp [Set.indicator_of_mem hx₀, X]
    · by_cases hxs : x ∈ Ioo (0 : ℝ) 1
      · simp [Set.indicator_of_mem hxs, X, hx]
      · simp [Set.indicator_of_notMem hxs]
  rw [hL, hR] at h
  exact inner_self_eq_zero.1 h

end Emb

open Emb in
/-- B on embedded manifolds: `M = ↥N` with the induced metric and the induced Levi-Civita
connection (a special case of B, see `B_to_B_emb`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ pw : ℝ → Bridge.Sub hN, IsPW (n := n) pw 0 1 →
    (∀ (k : ℕ) (t : ℕ → ℝ), t 0 = 0 → t k = 1 → (∀ i < k, t i < t (i + 1)) →
      (∀ i < k, IsSmoothCurve (n := n) pw (Set.Icc (t i) (t (i + 1)))) →
      ∀ i < k, ∃ A : FA n pw, HasCovDeriv (Bridge.conn (hN := hN)) pw (Set.Icc (t i) (t (i + 1)))
        (vel (n := n) pw (Set.Icc (t i) (t (i + 1)))) A) ∧
    {t : ℝ | t ∈ Set.Ioo (0 : ℝ) 1 ∧ Vjump (n := n) pw t ≠ 0}.Finite

/-- `B_emb` is a special case of B (the induced connection is Levi-Civita, `Bridge.conn_isLC`). -/
theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

/-- **A implies B on embedded manifolds.** The acceleration clause comes from the Bridge
(`hasCovDeriv_iff`: `A = P(dV/dt)`), with no use of A; the finiteness clause uses A
(`Emb.jump_eq_zero_of_A`) through the dictionary `Emb.D_Vjump`. -/
theorem A_to_B_emb : A → B_emb := by
  intro hA V _ _ _ W _ _ _ n N hN _ pw hpw
  refine ⟨fun k t _ _ hlt hsm i hi => ?_, ?_⟩
  · set s := Icc (t i) (t (i + 1))
    have hs : IsIntv s := ⟨ordConnected_Icc, uniqueDiffOn_Icc (hlt i hi)⟩
    have hc := hsm i hi
    have hc' : ContDiffOn ℝ ∞ (Bridge.incl hN ∘ pw) s := Bridge.isSmoothCurve_iff.1 hc
    have hv : IsSmoothAlong pw s (vel (n := n) pw s) :=
      Bridge.isSmoothAlong_iff.2 ⟨hc, (hc'.derivWithin hs.2 (by simp)).congr
        (Bridge.ambA_vel_eqOn hs.2 hc)⟩
    exact ⟨_, (Bridge.hasCovDeriv_iff hs hc).2 ⟨hv, fun _ _ => rfl⟩⟩
  · obtain ⟨-, -, B, hB⟩ := Bridge.isPiecewiseSmooth_of_isPW hpw
    have hdiff : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ B → DifferentiableAt ℝ (Bridge.incl hN ∘ pw) x := by
      intro x hx hxB
      obtain ⟨s, s', h0s, hsx, hxs', hs'1, hBs⟩ := Morse.exists_piece_around B hx.1 hx.2 hxB
      exact ((hB s s' h0s (hsx.trans hxs') hs'1 hBs).contDiffAt
        (Icc_mem_nhds hsx hxs')).differentiableAt (by simp)
    refine B.finite_toSet.subset fun x ⟨hx, hJ⟩ => ?_
    by_contra hxB
    apply hJ
    apply Bridge.D_injective (pw x)
    rw [Emb.D_Vjump, Emb.jump_eq_zero_of_A hA hdiff hx hxB]
    exact (map_zero _).symm

#rt_check RoundTrip.V8_7.A_to_B_emb [Morse.finsum_jump_eq_sum]

end RoundTrip.V8_7
