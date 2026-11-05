import Morse.Chapter13.Theorem22
import Morse.Chapter10.FullPathTheorem
import Morse.Homotopy.LoopSpace
import Morse.Homotopy.RelCells

/-!
Milnor, *Morse Theory*, §22, Corollary 22.2 (p. 118).

# `π_i(Ω^d) ≅ π_{i+1}(M)` for `i ≤ λ₀ − 2`

## Milnor's text, paraphrased

(p. 118) **Corollary 22.2**: with the hypotheses of Theorem 22.1, `π_i(Ω^d)` is isomorphic to
`π_{i+1}(M)` for `0 ≤ i ≤ λ₀ − 2`.  *Proof*: `π_i(Ω^d) ≅ π_i(Ω)` by Theorem 22.1 and the exact
sequence of the pair, and `π_i(Ω) ≅ π_{i+1}(M)` (Theorem 17.1 and the path fibration, (H3) of
the exposition).

## What is formalized

* `Morse.pathCHomeomorph`: `Ω* = PathC N p q` (continuous paths in `V` with values in `N`) is
  homeomorphic to Mathlib's `Path p q` in the subspace `N`.
* `Morse.corollary_22_2`: **Corollary 22.2**, as a bijection
  `π_i(Ω^d, γ) ≃ π_{i+1}(N, p)` for `i + 2 ≤ λ₀` and every minimal path `γ`, composed of: the
  bijection of Theorem 22.1 (`Morse.theorem_22_1_bijective`), Theorem 17.1
  (`Morse.theorem_17_1`), the homeomorphism above, the homotopy equivalence
  `Ω(N; p, q) → Ω(N; p, p)`, `δ ↦ δ · γ⁻¹` (`Morse.Homotopy.pathTransHomotopyEquiv`), the change
  of base point from `γ · γ⁻¹` to the constant loop along the contraction
  `s ↦ γ|[0, s] · γ|[0, s]⁻¹`
  (`Morse.Homotopy.changeBaseEquiv`), and `π_i(ΩN) ≃ π_{i+1}(N)`
  (`Morse.Homotopy.homotopyGroupPiLoopEquiv`).

## What Milnor leaves implicit

* **Base points**: `π_i(Ω, γ)` is taken at a minimal geodesic `γ`, while `π_i(ΩN) ≅ π_{i+1}(N)`
  concerns the component of the constant loop; using `γ` itself to identify `Ω(N; p, q)` with
  `Ω(N; p, p)` sends `γ` to `γ · γ⁻¹`, which is joined to the constant loop.  No connectedness of
  `N` is needed.
* The bijection is constructed from maps which are homomorphisms for `i ≥ 1`; the group
  isomorphism is `Morse.corollary_22_2_mulEquiv` (`Morse/Chapter13/CorollaryGroups.lean`).
-/

open Set Function Topology Module
open scoped unitInterval Manifold

noncomputable section

namespace Morse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V}

/-- **`Ω*` is Mathlib's path space of the subspace `N`.** -/
def pathCHomeomorph {p q : V} (hp : p ∈ N) (hq : q ∈ N) :
    PathC N p q ≃ₜ Path (⟨p, hp⟩ : N) ⟨q, hq⟩ where
  toFun γ := ⟨⟨fun t => ⟨γ.1 t, γ.2.1 t⟩, by fun_prop⟩, Subtype.ext γ.2.2.1, Subtype.ext γ.2.2.2⟩
  invFun δ := ⟨⟨fun t => (δ t : V), by fun_prop⟩, fun t => (δ t).2,
    congrArg Subtype.val δ.source, congrArg Subtype.val δ.target⟩
  left_inv γ := rfl
  right_inv δ := rfl
  continuous_toFun := by
    refine Path.continuous_uncurry_iff.1 ?_
    refine Continuous.subtype_mk ?_ _
    exact (continuous_eval (F := C(I, V)) (X := I) (Y := V)).comp
      (continuous_subtype_val.prodMap continuous_id)
  continuous_invFun := by
    refine Continuous.subtype_mk (ContinuousMap.continuous_of_continuous_uncurry _ ?_) _
    exact continuous_subtype_val.comp continuous_eval

section Contraction

variable {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}

/-- The loops `γ|[0, s] · γ|[0, s]⁻¹`, `t ↦ γ(s · min(2t, 2 − 2t))`. -/
def contractLoop (γ : Path x₀ x₁) (s : I) : Path x₀ x₀ where
  toFun t := γ.extend ((s : ℝ) * min (2 * (t : ℝ)) (2 - 2 * t))
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by norm_num

theorem continuous_contractLoop (γ : Path x₀ x₁) : Continuous (contractLoop γ) := by
  refine Path.continuous_uncurry_iff.1 ?_
  change Continuous fun z : I × I => γ.extend ((z.1 : ℝ) * min (2 * (z.2 : ℝ)) (2 - 2 * z.2))
  fun_prop

theorem contractLoop_zero (γ : Path x₀ x₁) : contractLoop γ 0 = Path.refl x₀ := by
  ext t
  simp [contractLoop]

theorem contractLoop_one (γ : Path x₀ x₁) : contractLoop γ 1 = γ.trans γ.symm := by
  ext t
  simp only [contractLoop, Path.coe_mk_mk, Set.Icc.coe_one, one_mul, Path.trans_apply,
    Path.symm_apply]
  split_ifs with ht
  · rw [min_eq_left (by linarith), Path.extend_apply]
  · push Not at ht
    rw [min_eq_right (by linarith), Path.extend_apply _ ⟨by linarith [t.2.2], by linarith⟩]
    congr 1
    ext
    simp only [unitInterval.coe_symm_eq]
    ring

/-- **A path in the loop space from `γ · γ⁻¹` to the constant loop.** -/
def contractPath (γ : Path x₀ x₁) : Path (γ.trans γ.symm) (Path.refl x₀) where
  toFun s := contractLoop γ (unitInterval.symm s)
  continuous_toFun := (continuous_contractLoop γ).comp unitInterval.continuous_symm
  source' := by rw [unitInterval.symm_zero, contractLoop_one]
  target' := by rw [unitInterval.symm_one, contractLoop_zero]

end Contraction

/-- **Corollary 22.2** (Milnor, p. 118): under the hypotheses of Theorem 22.1
(`Morse.theorem_22_1`), for every minimal path `γ` and `i + 2 ≤ λ₀` there is a bijection
`π_i(Ω^d, γ) ≃ π_{i+1}(N, p)`. -/
theorem corollary_22_2 (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (hball : ∀ r : ℝ, IsCompact (closedRiemBall N p r)) {l₀ : ℕ}
    (hidx : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ →
      (∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy γ 0 1) →
      (l₀ : ℕ∞) ≤ formIndex (energyHessian hN hγ))
    (hretr : ∃ O : Set (PathSp N p q), IsOpen O ∧ minPaths N p q ⊆ O ∧
      ∃ ρ : PathSp N p q → PathSp N p q, ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths N p q) ∧
        ∀ γ ∈ minPaths N p q, ρ γ = γ)
    {i : ℕ} (hi : i + 2 ≤ l₀) (γ : minPaths N p q) :
    Nonempty (HomotopyGroup.Pi i (minPaths N p q) γ ≃ HomotopyGroup.Pi (i + 1) N ⟨p, hp⟩) := by
  have h1 := theorem_22_1_bijective hN hp hq hball hidx hretr (K := Fin i)
    (by simpa using hi) γ
  have h2 := Morse.Homotopy.bijective_homotopyGroupMap_of_isHomotopyEquiv (N := Fin i)
    (theorem_17_1 hN p q) (γ : PathSp N p q)
  set e := pathCHomeomorph (N := N) hp hq
  have h3 := Morse.Homotopy.bijective_homotopyGroupMap_homeomorph (N := Fin i) e
    (pathIncl (N := N) p q γ)
  set x := e (pathIncl (N := N) p q γ)
  have h4 := Morse.Homotopy.bijective_homotopyGroupMap_of_homotopyEquiv (N := Fin i)
    (Morse.Homotopy.pathTransHomotopyEquiv x.symm) x
  exact ⟨(Equiv.ofBijective _ h1).trans ((Equiv.ofBijective _ h2).trans
    ((Equiv.ofBijective _ h3).trans ((Equiv.ofBijective _ h4).trans
      ((Morse.Homotopy.changeBaseEquiv (contractPath x)).trans
        (Morse.Homotopy.homotopyGroupPiLoopEquiv i)))))⟩

end Morse
