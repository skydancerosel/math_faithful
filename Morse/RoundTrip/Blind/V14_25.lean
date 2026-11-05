import Morse
/-! Blind formalization of V14_25 (Milnor §23, Lemma 23.4 and its proof, pp. 128–129: stability, connectivity of the Stiefel manifold). Choices:
- Matrix-group setting exactly as in the blind file V14_23 (prelude `MatrixGroups`/`Bundles` copied verbatim):
  `U(k) = U k = ↥(Matrix.unitaryGroup (Fin k) ℂ)`, `SU(k) = SU k = ↥(Matrix.specialUnitaryGroup (Fin k) ℂ)`
  (Mathlib), topological groups with the subspace topology of `M_k(ℂ) = Mat k` (product topology); Milnor's
  `U(j) ⊆ U(k)` is `fixSub k j` (the matrices `diag(B, I_{k-j})`), `U(j) × U(k-j) ⊆ U(k)` is `blockSub k j`
  (`diag(A, B)`); coset spaces are Mathlib's `G ⧸ H` with the quotient topology; `G_m(ℂ^k) = Grass k m` (the
  `m`-dimensional subspaces, as orthogonal projections: Hermitian idempotents of rank `m`; subspace topology);
  `IsBundle F proj` = locally trivial fibre bundle with fibre `F` (every point of the base lies in the base set of a
  Mathlib `Bundle.Trivialization F proj`), modelled by hand (Mathlib has no such predicate).
- Homotopy groups as in the blind files V13_1–V13_5: Mathlib's `π_ i X x` (`HomotopyGroup (Fin i)`; `π_ 0` = the set
  of path components, groups for `i ≥ 1`), `piMap f x` = the induced map `f_*` (copied verbatim). "`A ≅ B`" between
  homotopy groups is `Nonempty (A ≃ B)` when one side is only a set (`π_0`) and `Nonempty (A ≃* B)` when both are
  groups; Milnor's base-point-free `π_i` is read at every base point.
- The inclusions `U(n) ⊆ U(n+1)` are `B ↦ diag(B, 1)` (`blockIncl (n+1) n`; a continuous map given by its values,
  `∃ ι`; it is unique, so `∃` costs nothing). "`π_{i−1}U(m) ≅ π_{i−1}U(m+1) ≅ π_{i−1}U(m+2) ≅ ⋯` for `i ≤ 2m`, induced
  by the inclusions": for every `r ≥ 0` and `0 ≤ j = i − 1 ≤ 2m − 1` (so `1 ≤ i ≤ 2m`; `π_{−1}` is meaningless), the
  map `π_j(U(m+r), g) → π_j(U(m+r+1), ι g)` induced by the inclusion is bijective at every base point, and a group
  isomorphism when `j ≥ 1`.
- "`π_{2m}U(m) → π_{2m}U(m+1)` is onto": the inclusion-induced map, at every base point.
- "`π_i(U(2m)/U(m)) = 0` for `i ≤ 2m`": for `0 ≤ i ≤ 2m` and every base point `π_i` has at most one element
  (`Subsingleton`; for `i = 0`: the coset space is path connected). `U(2m)/U(m) = U(2m) ⧸ fixSub (2m) m` (the Stiefel
  manifold of V14_23).
- All `m ≥ 0` (`m = 0`: the first claim is vacuous, the others hold trivially).
-/
open scoped Matrix Topology
open Topology

namespace RoundTrip.V14_25

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

/-- Lemma 23.4: inclusion-induced `π_{i−1}U(m) ≅ π_{i−1}U(m+1) ≅ ⋯` for `i ≤ 2m`; `π_{2m}U(m) → π_{2m}U(m+1)` onto;
`π_i(U(2m)/U(m)) = 0` for `i ≤ 2m`. -/
def B : Prop :=
  ∀ m : ℕ,
    (∀ r : ℕ, ∃ ι : C(U (m + r), U (m + r + 1)),
      (∀ g : U (m + r), (ι g : Mat (m + r + 1)) = blockIncl (m + r + 1) (m + r) (g : Mat (m + r))) ∧
      (∀ j : ℕ, j + 1 ≤ 2 * m → ∀ g : U (m + r), Function.Bijective (piMap (N := Fin j) ι g)) ∧
      (∀ k : ℕ, k + 2 ≤ 2 * m → ∀ g : U (m + r),
        ∃ e : π_ (k + 1) (U (m + r)) g ≃* π_ (k + 1) (U (m + r + 1)) (ι g), ⇑e = piMap ι g) ∧
      (r = 0 → ∀ g : U (m + r), Function.Surjective (piMap (N := Fin (2 * m)) ι g))) ∧
    ∀ i : ℕ, i ≤ 2 * m → ∀ x : U (2 * m) ⧸ fixSub (2 * m) m,
      Subsingleton (π_ i (U (2 * m) ⧸ fixSub (2 * m) m) x)

end RoundTrip.V14_25
