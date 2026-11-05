import Morse
/-! Blind formalization of V14_24 (Milnor §23, proof of Lemma 23.4, p. 129: the Grassmannian bundle `U(m) → U(2m)/U(m) → G_m(ℂ^{2m})`). Choices:
- Matrix-group setting exactly as in the blind file V14_23 (prelude `MatrixGroups`/`Bundles` copied verbatim):
  `U(k) = U k = ↥(Matrix.unitaryGroup (Fin k) ℂ)`, `SU(k) = SU k = ↥(Matrix.specialUnitaryGroup (Fin k) ℂ)`
  (Mathlib), topological groups with the subspace topology of `M_k(ℂ) = Mat k` (product topology); Milnor's
  `U(j) ⊆ U(k)` is `fixSub k j` (the matrices `diag(B, I_{k-j})`), `U(j) × U(k-j) ⊆ U(k)` is `blockSub k j`
  (`diag(A, B)`); coset spaces are Mathlib's `G ⧸ H` with the quotient topology; `G_m(ℂ^k) = Grass k m` (the
  `m`-dimensional subspaces, as orthogonal projections: Hermitian idempotents of rank `m`; subspace topology);
  `IsBundle F proj` = locally trivial fibre bundle with fibre `F` (every point of the base lies in the base set of a
  Mathlib `Bundle.Trivialization F proj`), modelled by hand (Mathlib has no such predicate).
- "`G_m(ℂ^{2m})` can be identified with `U(2m)/U(m) × U(m)`": a homeomorphism `U(2m)/(U(m) × U(m)) ≅ G_m(ℂ^{2m})`,
  taken to be the natural one, `g·(U(m) × U(m)) ↦ g(ℂ^m ⊕ 0)`, i.e. `↦ g P₀ g*` with `P₀ = topProj (2m) m` (the
  identification given by the transitive action of `U(2m)` on `G_m(ℂ^{2m})` with isotropy group `U(m) × U(m)`;
  Milnor names no other).
- "There is a fibration `U(m) → U(2m)/U(m) → G_m(ℂ^{2m})`": the natural map `U(2m)/U(m) → G_m(ℂ^{2m})`,
  `g·U(m) ↦ g P₀ g*` (the coset map `U(2m)/U(m) → U(2m)/(U(m) × U(m))` followed by the identification), is a locally
  trivial fibre bundle with fibre `U(m)`. Here `U(m) = fixSub (2m) m ⊆ U(m) × U(m)` (`diag(B, I_m)`), so the map is well
  defined. Maps out of coset spaces are given by their values on cosets (`∃ f` with `f(gH) = …`), so no
  well-definedness proof is needed. All `m ≥ 0` (`m = 0`: points).
-/
open scoped Matrix Topology
open Topology

namespace RoundTrip.V14_24

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

/-- `G_m(ℂ^{2m}) ≅ U(2m)/(U(m) × U(m))` (naturally), and `U(2m)/U(m) → G_m(ℂ^{2m})` is a fibre bundle with fibre
`U(m)`. -/
def B : Prop :=
  ∀ m : ℕ,
    (∃ h : (U (2 * m) ⧸ blockSub (2 * m) m) ≃ₜ ↥(Grass (2 * m) m),
      ∀ g : U (2 * m), ((h (g : U (2 * m) ⧸ blockSub (2 * m) m) : Mat (2 * m))) =
        (g : Mat (2 * m)) * topProj (2 * m) m * star (g : Mat (2 * m))) ∧
    (∃ f : (U (2 * m) ⧸ fixSub (2 * m) m) → ↥(Grass (2 * m) m),
      (∀ g : U (2 * m), ((f (g : U (2 * m) ⧸ fixSub (2 * m) m) : Mat (2 * m))) =
        (g : Mat (2 * m)) * topProj (2 * m) m * star (g : Mat (2 * m))) ∧
      IsBundle (U m) f)

end RoundTrip.V14_24
