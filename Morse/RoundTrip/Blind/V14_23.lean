import Morse
/-! Blind formalization of V14_23 (Milnor §23, proof of Lemma 23.4, pp. 128–129: coset bundles, local
cross-sections, the Stiefel manifold, `U(m+1) → S^{2m+1}`). Choices:
- Matrix-group setting (shared by the blind files V14_22–V14_30): `U(k) = Matrix.unitaryGroup (Fin k) ℂ`,
  `SU(k) = Matrix.specialUnitaryGroup (Fin k) ℂ` (Mathlib), as topological groups with the subspace topology of
  `M_k(ℂ)` (product topology). No Riemannian structure is needed for these items. Milnor's subgroups are modelled
  as subgroups of `U(k)`: `U(j) ⊆ U(k)` is `fixSub k j`, the matrices `diag(B, I_{k-j})` (= those fixing the basis
  vectors `e_i`, `i ≥ j`); `U(j) × U(k-j) ⊆ U(k)` is `blockSub k j`, the block-diagonal matrices `diag(A, B)`
  (= those commuting with the projection `topProj k j` onto `ℂ^j ⊕ 0`). Coset spaces are Mathlib's `G ⧸ H` with the
  quotient topology. `S^{2m+1} = Sph m = {v ∈ ℂ^{m+1} | Σ |v_i|² = 1}` (product topology). The fibre of a bundle
  "with fibre `U(m)`" is the Mathlib type `U m`.
- Modelled by hand (Mathlib has no predicate "is a fibre bundle" for a map between given spaces, only the
  structure `Trivialization` and `IsHomeomorphicTrivialFiberBundle` for globally trivial bundles): `IsBundle F proj`
  = every point of the base lies in the base set of a Mathlib `Trivialization F proj` (a locally trivial fibre
  bundle with fibre `F`; Milnor's "fibration"); `HasLocalSections proj` = every point of the base has an open
  neighbourhood with a continuous section of `proj` over it ("local cross-sections").
- Claims (conjunction): (0) the cited theorem of Steenrod: for every topological group `G` and subgroup `H`, if the
  coset map `G → G/H` has local cross-sections, it is a fibre bundle with fibre `H` (Milnor's citation; stated for
  arbitrary subgroups, where it is true, since Milnor gives no hypotheses); and for every `m ≥ 0` (`m = 0` allowed,
  all claims hold there): (1) `U(m+1)/U(m) ≅ S^{2m+1}` by the natural map `g·U(m) ↦ g e_{m+1}` (last column of `g`;
  `U(m)` = stabilizer of `e_{m+1}`, matching the orbit map of the transitive action); (2) the coset maps
  `U(m+1) → U(m+1)/U(m)` and `U(2m) → U(2m)/U(m)` have local cross-sections; (3) they are fibre bundles with fibre
  `U(m)`; (4) "the fibration `U(m) → U(m+1) → S^{2m+1}`": `g ↦ g e_{m+1}` (through the homeomorphism of (1)) is a
  fibre bundle with fibre `U(m)`. "The complex Stiefel manifold `U(2m)/U(m)`" is a name for the coset space (no claim
  about frames is made).
-/
open scoped Matrix Topology
open Topology

namespace RoundTrip.V14_23

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

/-- Steenrod's theorem (cited); `U(m+1)/U(m) ≅ S^{2m+1}`; the coset maps `U(m+1) → U(m+1)/U(m)`, `U(2m) → U(2m)/U(m)`
have local cross-sections and are fibre bundles with fibre `U(m)`; `g ↦ g e_{m+1}` is a bundle `U(m+1) → S^{2m+1}`. -/
def B : Prop :=
  (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G),
      HasLocalSections (QuotientGroup.mk : G → G ⧸ H) → IsBundle ↥H (QuotientGroup.mk : G → G ⧸ H)) ∧
  ∀ m : ℕ,
    (∃ h : (U (m + 1) ⧸ fixSub (m + 1) m) ≃ₜ ↥(Sph m),
        (∀ g : U (m + 1), ((h (g : U (m + 1) ⧸ fixSub (m + 1) m) : Fin (m + 1) → ℂ)) =
          fun i => (g : Mat (m + 1)) i (Fin.last m)) ∧
        IsBundle (U m) (fun g : U (m + 1) => h (g : U (m + 1) ⧸ fixSub (m + 1) m))) ∧
    HasLocalSections (QuotientGroup.mk : U (m + 1) → U (m + 1) ⧸ fixSub (m + 1) m) ∧
    HasLocalSections (QuotientGroup.mk : U (2 * m) → U (2 * m) ⧸ fixSub (2 * m) m) ∧
    IsBundle (U m) (QuotientGroup.mk : U (m + 1) → U (m + 1) ⧸ fixSub (m + 1) m) ∧
    IsBundle (U m) (QuotientGroup.mk : U (2 * m) → U (2 * m) ⧸ fixSub (2 * m) m)

end RoundTrip.V14_23
