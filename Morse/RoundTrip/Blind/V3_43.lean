import Morse
/-! Blind formalization of V3_43 (Milnor §4, p. 27: the cells and the integral homology of `ℂPⁿ`). Choices:
- `ℂPⁿ` as in the V3_41 blind file (copied): unit vectors of `ℂ^{n+1}` modulo `z ∼ λz`, `|λ| = 1`, quotient topology.
  Both claims are topological, so no smooth structure is needed.
- "Homotopy type of a CW-complex of the form `e⁰ ∪ e² ∪ … ∪ e^{2n}`" (as in the V5_11 blind file for CW complexes): there is
  a Hausdorff space `Y : Type` with a Mathlib classical CW structure `Topology.CWComplex (Set.univ : Set Y)` having exactly
  one cell in each dimension `0, 2, …, 2n` and no other cells (`Finite` + `Nat.card` of `CWComplex.cell univ l`), and a
  homotopy equivalence `ContinuousMap.HomotopyEquiv (CPn n) Y`.
- Integral homology `H_i(ℂPⁿ; ℤ)`: the project's relative singular homology `relHomology` with coefficients
  `ModuleCat.of ℤ ℤ` of the pair `(univ, ∅)` (as for `R_λ(M)` in the V3_3x blind files, here over `ℤ`).
  "`= ℤ`" := linearly isomorphic to `ℤ`; "`= 0`" := subsingleton.
- B = conjunction of the two sentences (the "By Theorem 3.5" / "It follows" derivations are not part of B). `n = 0` allowed. -/
open scoped ContDiff Manifold
namespace RoundTrip.V3_43
open CategoryTheory Morse.Homology

/-- Unit vectors of `ℂ^{n+1}`: `Σ |z_j|² = 1`. -/
abbrev Sph (n : ℕ) : Type := {z : Fin (n + 1) → ℂ // ∑ j, ‖z j‖ ^ 2 = 1}

/-- `z ∼ w` iff `w = λ z` with `|λ| = 1`. -/
def Rel (n : ℕ) (z w : Sph n) : Prop := ∃ c : ℂ, ‖c‖ = 1 ∧ w.1 = c • z.1

/-- `ℂPⁿ`: equivalence classes of unit vectors of `ℂ^{n+1}`, with the quotient topology. -/
def CPn (n : ℕ) : Type := Quot (Rel n)

instance (n : ℕ) : TopologicalSpace (CPn n) := inferInstanceAs (TopologicalSpace (Quot (Rel n)))

/-- `H_i(X; ℤ)` (project's singular homology of the pair `(X, ∅)`). -/
noncomputable def HZ (X : Type) [TopologicalSpace X] (i : ℕ) : ModuleCat ℤ :=
  (relHomology (ModuleCat.of ℤ ℤ) i).obj (subsetPair (Set.empty_subset (Set.univ : Set X)))

/-- `ℂPⁿ ≃ e⁰ ∪ e² ∪ … ∪ e^{2n}`, and `H_i(ℂPⁿ; ℤ) = ℤ` for `i = 0, 2, …, 2n`, `0` otherwise. -/
def B : Prop :=
  ∀ n : ℕ,
    (∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : Topology.CWComplex (Set.univ : Set Y)),
      Nonempty (ContinuousMap.HomotopyEquiv (CPn n) Y) ∧
      ∀ l : ℕ, Finite (Topology.CWComplex.cell (Set.univ : Set Y) l) ∧
        Nat.card (Topology.CWComplex.cell (Set.univ : Set Y) l) = if Even l ∧ l ≤ 2 * n then 1 else 0) ∧
    (∀ i : ℕ, (Even i ∧ i ≤ 2 * n → Nonempty (HZ (CPn n) i ≃ₗ[ℤ] ℤ)) ∧
      (¬ (Even i ∧ i ≤ 2 * n) → Subsingleton (HZ (CPn n) i)))

end RoundTrip.V3_43
