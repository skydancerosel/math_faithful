import Morse
/-! Blind formalization of V15_46 (Milnor §23, the Periodicity Theorem, p. 129, for the stable groups of `U`).
Choices:
- Matrix-group setting exactly as in the blind files V14_23–V14_30 (prelude `MatrixGroups`/`Bundles` copied verbatim
  from V14_25/V14_28): `U(k) = U k = ↥(Matrix.unitaryGroup (Fin k) ℂ)` (Mathlib), a topological group with the subspace
  topology of `M_k(ℂ) = Mat k` (product topology). Only `U` is used here; the rest of the prelude is kept for
  uniformity.
- Homotopy groups as in the blind files V13_1–V13_5 and V14_25–V14_30: Mathlib's `π_ i X x` (`HomotopyGroup (Fin i)`;
  `π_ 0` = the set of path components, groups for `i ≥ 1`). "`A ≅ B`" between homotopy groups is `Nonempty (A ≃ B)`
  when one side is only a set (`π_0`) and `Nonempty (A ≃* B)` when both are groups (abstract isomorphisms: Milnor
  names none). Milnor's base-point-free `π_j` is read at every base point.
- Stable groups, as in V14_28: "`π_{i−1}U = π_{i−1}U(m)` for `i ≤ 2m`" — Milnor's `π_jU` is `π_jU(m)` for any `m` with
  `j + 1 ≤ 2m`. So "`π_{i−1}U ≅ π_{i+1}U` for `i ≥ 1`" (`π_{−1}` is meaningless) is: for all `m, m'` with `i ≤ 2m` and
  `i + 2 ≤ 2m'` and all base points, `π_{i−1}U(m) ≅ π_{i+1}U(m')`. Written with `k = i − 1 ≥ 0`: `k + 1 ≤ 2m`,
  `k + 3 ≤ 2m'`; as sets for every `k ≥ 0` (`k = 0`: `π_0U(m)` is only a set), and as groups for `k ≥ 1` (written
  `k + 1`: `k + 2 ≤ 2m`, `k + 4 ≤ 2m'`). This is exactly the first two conjuncts of V14_28 (the proof's chain through
  `G_m(ℂ^{2m})` and `SU(2m)` is not part of this item).
- The parenthetical "where `π_{i−1}U = π_{i−1}U(m)` for `i ≤ 2m`" fixes the meaning of the stable groups; that these do
  not depend on `m` (Lemma 23.4, V14_25) is not asserted separately (it also follows from the stated isomorphisms for
  all pairs `m, m'`).
- All `m, m' ≥ 0`.
-/
open scoped Matrix Topology
open Topology

namespace RoundTrip.V15_46

section MatrixGroups

/-- `M_k(ℂ)`: complex `k × k` matrices (Mathlib's `Matrix`, product topology). -/
abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℂ

/-- `U(k)`: Mathlib's unitary group, a topological group with the subspace topology of `M_k(ℂ)`. -/
abbrev U (k : ℕ) := ↥(Matrix.unitaryGroup (Fin k) ℂ)

/-- `SU(k)`: Mathlib's special unitary group. -/
abbrev SU (k : ℕ) := ↥(Matrix.specialUnitaryGroup (Fin k) ℂ)

/-- `diag(1,…,1,0,…,0)` (`j` ones): the orthogonal projection of `ℂ^k` onto `ℂ^j ⊕ 0`. -/
def topProj (k j : ℕ) : Mat k := Matrix.diagonal fun i => if (i : ℕ) < j then 1 else 0

/-- `diag(0,…,0,1,…,1)` (`j` zeros): the orthogonal projection of `ℂ^k` onto `0 ⊕ ℂ^{k-j}`. -/
def botProj (k j : ℕ) : Mat k := Matrix.diagonal fun i => if (i : ℕ) < j then 0 else 1

/-- Milnor's `U(j) ⊆ U(k)` (`j ≤ k`): unitary matrices fixing the basis vectors `e_i`, `i ≥ j`, i.e. the matrices
`diag(B, I_{k-j})` with `B ∈ U(j)` (`g · botProj = botProj` says the last `k - j` columns of `g` are those of `I`). -/
def fixSub (k j : ℕ) : Subgroup (U k) where
  carrier := {g | (g : Mat k) * botProj k j = botProj k j}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Matrix.UnitaryGroup.mul_val] at *
    rw [Matrix.mul_assoc, hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Matrix.UnitaryGroup.inv_val] at *
    calc star (a : Mat k) * botProj k j = star (a : Mat k) * ((a : Mat k) * botProj k j) := by rw [ha]
      _ = botProj k j := by rw [← Matrix.mul_assoc, Matrix.UnitaryGroup.star_mul_self, Matrix.one_mul]

/-- Milnor's `U(j) × U(k-j) ⊆ U(k)`: the block-diagonal unitary matrices `diag(A, B)`, i.e. those commuting with
`topProj k j` (preserving `ℂ^j ⊕ 0` and its orthogonal complement). -/
def blockSub (k j : ℕ) : Subgroup (U k) where
  carrier := {g | (g : Mat k) * topProj k j = topProj k j * (g : Mat k)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Matrix.UnitaryGroup.mul_val] at *
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, Matrix.UnitaryGroup.inv_val] at *
    have hs : star (topProj k j) = topProj k j := by
      ext i i'
      by_cases h : i = i'
      · subst h; by_cases h' : (i : ℕ) < j <;> simp [topProj, Matrix.star_apply, h']
      · simp [topProj, Matrix.star_apply, Matrix.diagonal_apply, h, Ne.symm h]
    have := congrArg star ha
    rw [star_mul, star_mul, hs] at this
    exact this.symm

/-- `diag(B, I_{k-j})` for `B ∈ M_j(ℂ)`: the standard inclusion `M_j(ℂ) → M_k(ℂ)` (`j ≤ k`). -/
def blockIncl (k j : ℕ) (B : Mat j) : Mat k :=
  Matrix.of fun a b => if h : (a : ℕ) < j ∧ (b : ℕ) < j then B ⟨a, h.1⟩ ⟨b, h.2⟩ else (1 : Mat k) a b

/-- `S^{2m+1}`: the unit sphere of `ℂ^{m+1}` (product topology). -/
def Sph (m : ℕ) : Set (Fin (m + 1) → ℂ) := {v | ∑ i, Complex.normSq (v i) = 1}

/-- `G_m(ℂ^k)`: the `m`-dimensional subspaces of `ℂ^k`, modelled by their orthogonal projections (Hermitian
idempotent matrices of rank `m`), with the subspace topology of `M_k(ℂ)`. -/
def Grass (k m : ℕ) : Set (Mat k) := {P | P.conjTranspose = P ∧ P * P = P ∧ P.rank = m}
end MatrixGroups

section Bundles

/-- `proj : Z → Y` is a (locally trivial) fibre bundle with fibre `F` (Milnor's "fibration `F → Z → Y`"): every point
of `Y` lies in the base set of a local trivialization (Mathlib's `Trivialization`). -/
def IsBundle (F : Type) [TopologicalSpace F] {Z Y : Type} [TopologicalSpace Z] [TopologicalSpace Y] (proj : Z → Y) :
    Prop :=
  ∀ y : Y, ∃ e : Bundle.Trivialization F proj, y ∈ e.baseSet

/-- `proj` has local cross-sections: every point of `Y` has an open neighbourhood `V` with a continuous `s : V → Z`,
`proj ∘ s = id`. -/
def HasLocalSections {Z Y : Type} [TopologicalSpace Z] [TopologicalSpace Y] (proj : Z → Y) : Prop :=
  ∀ y : Y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ ∃ s : Y → Z, ContinuousOn s V ∧ ∀ z ∈ V, proj (s z) = z
end Bundles

section Htpy
/-- `f ∘ γ` for a generalized loop `γ : (I^N, ∂I^N) → (X, x)`. -/
def genLoopMap {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) {x : X}
    (γ : ↥(GenLoop N X x)) : ↥(GenLoop N Y (f x)) :=
  ⟨f.comp γ.1, fun y hy => by simp [GenLoop.boundary γ y hy]⟩

/-- The homomorphism `f_* : π_N(X, x) → π_N(Y, f x)` induced by a map `f` (Mathlib's `HomotopyGroup`). -/
def piMap {N X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x : X) :
    HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map' (genLoopMap f) (fun _ _ h => ContinuousMap.HomotopicRel.comp_continuousMap h f)
end Htpy

/-- Bott periodicity for the stable groups of `U`: `π_{i−1}U ≅ π_{i+1}U` (`i ≥ 1`), where `π_{i−1}U = π_{i−1}U(m)` for
`i ≤ 2m`. -/
def B : Prop :=
  (∀ k m m' : ℕ, k + 1 ≤ 2 * m → k + 3 ≤ 2 * m' → ∀ (g : U m) (g' : U m'),
    Nonempty (π_ k (U m) g ≃ π_ (k + 2) (U m') g')) ∧
  (∀ k m m' : ℕ, k + 2 ≤ 2 * m → k + 4 ≤ 2 * m' → ∀ (g : U m) (g' : U m'),
    Nonempty (π_ (k + 1) (U m) g ≃* π_ (k + 3) (U m') g'))

end RoundTrip.V15_46
