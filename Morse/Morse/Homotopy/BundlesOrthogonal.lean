import Mathlib
import Morse.Homotopy.BundlesUnitary

/-!
# The bundles of Bott periodicity for the orthogonal group

Milnor, *Morse Theory*, §24, pp. 133, 138, 142.

## Milnor's text, paraphrased

* (p. 138) "`π_h O(n)` does not depend on `n` for `n > h + 1`" — the stable groups `π_h O`
  (Milnor defines `O = Ω₀` as the union of the `O(n)` and reads `π_h O` as the common value),
  by the same argument as for `U(n)`: the fibration `O(n) → O(n+1) → Sⁿ` and `πᵢ Sⁿ = 0` for
  `i < n`.
* (p. 133) `Ω₁(n) ≅ O(n)/U(n/2)`, and (pp. 139–142) the spaces `Ω_k(16r)` are coset spaces or
  Grassmannians: `Ω₇(16r)` is a union of Grassmannians `G_j(ℝ^{2r})`, `Ω₈(16r) ≅ O(r)`.
* (p. 142, the table, "left to the reader") `π₀ Ω_k` and the groups `π_h O`.

## What is formalized

The real case of `Morse/Homotopy/BundleHomotopy.lean` (`𝕜 = ℝ`, `d = 1`; `unitaryGroup ι ℝ` is
Mathlib's `orthogonalGroup ι ℝ`):

* `Morse.Homotopy.sphereConnected_real`: **`SphereConnected ℝ 1`**, `πᵢ(S^{n-1}) = 0` for
  `i < n − 1`.
* `Morse.Homotopy.isLocallyTrivial_sphereOrbit_real`: **`O(m) → O(m + 1) → Sᵐ`** is locally
  trivial.
* `Morse.Homotopy.bijective_homotopyGroupMap_orthogonalIncl`: **stability**, `T ↦ diag(T, I_k)`
  induces bijections `πᵢ O(m) → πᵢ O(m + k)` for `i < m − 1`, and
  `Morse.Homotopy.surjective_homotopyGroupMap_orthogonalIncl` surjections for `i ≤ m − 1`. With
  `k = 16` this is the stabilization `Ω₀(16r) → Ω₀(16r + 16)`, `T ↦ T ⊕ I₁₆`, of Milnor p. 138
  (`Morse.Homotopy.bijective_homotopyGroupMap_omegaZeroStab`).
* `Morse.Homotopy.subsingleton_pi_stiefel_real`: **`V_k(ℝⁿ)` is `(n − k − 1)`-connected**.
* `Morse.Homotopy.grassmannianEquiv_real`, `Morse.Homotopy.nonempty_mulEquiv_grassmannian_real`:
  **`π_{j+1} G_m(ℝ^{m'+m}) ≅ π_j O(m)` for `j + 2 ≤ m'`** (group isomorphism for `j ≥ 1`,
  `j + 3 ≤ m'`), at every base point of the Grassmannian
  (`Morse.Homotopy.grassmannianPiEquiv_real`,
  `Morse.Homotopy.nonempty_mulEquiv_grassmannianPi_real`,
  for a Grassmannian `Grassmannian ℝ ι m` with any `ι ≃ Fin m' ⊕ Fin m`). For the middle
  Grassmannian `G_r(ℝ^{2r})` of `Ω₇(16r)` this gives `πᵢ G_r(ℝ^{2r}) ≅ πᵢ₋₁ O(r)` for
  `1 ≤ i ≤ r − 1`.
* `Morse.Homotopy.bijective_homotopyGroupMap_soInclC`: **`πᵢ SO(n) ≅ πᵢ O(n)` for `i ≥ 1`**,
  used by Milnor in Theorem 24.3 (`π_{i+1} SO(n) = π_{i+1} O(n)`), through the general
  `Morse.Homotopy.bijective_homotopyGroupMap_clopen`: the inclusion of a clopen set containing
  the base point is bijective on `π_N`, `N ≠ ∅`.

## What Milnor's §24 needs at the topology level, and what is not formalized here

Milnor's proof of `πᵢ O ≅ π_{i+8} O` (Theorem 24.7) uses: (1) the stability of `πᵢ O(n)` (to
define `πᵢ O`) — done here; (2) `π_j Ω(Ω_k(n); J_k, −J_k) ≅ π_{j+1} Ω_k(n)` — the path/loop
space identification of `Morse/Homotopy/LoopSpace.lean`; (3) Theorem 22.1 for each `Ω_k(16r)`
(Morse theory, not a fibration); (4) `Ω₈(16r) ≅ O(r)` compatibly with the stabilizations
`J ↦ J ⊕ J'_k` (an explicit linear-algebra identification, Lemma 24.6, not a bundle); and
(5) passage to the colimit `r → ∞` (compact sets in a colimit lie in a stage). Not formalized
here:

* the colimit spaces `O`, `Ω_k`, and `πᵢ(colim) = colim πᵢ` (item 5);
* the stabilizations `J ↦ J ⊕ J'_k` of `Ω_k(16r)` for `k ≥ 1` and their compatibility with
  `Ω₈(16r) ≅ O(r)` (item 4; the eight structures `J'_α` on `ℝ¹⁶` are not in Lean);
* the coset descriptions `Ω₁(n) ≅ O(n)/U(n/2)`, `Ω₂ ≅ U/Sp`, …, and the bundles
  `Sp(m−1) → Sp(m) → S^{4m−1}`, `Sp(4r) → U(8r) → U(8r)/Sp(4r)` used for the table on p. 142
  (quaternionic matrices are not an `RCLike` field, so `BundleHomotopy.lean` does not apply);
* `π₀`: that `O(n)` has exactly two components (the table's `π₀ O = ℤ/2`).
-/

open Matrix Set Function Topology Metric
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

/-- **`SphereConnected ℝ 1`**: `πᵢ(V₁(ℝⁿ)) = πᵢ(S^{n-1}) = 0` for `i < n − 1`. -/
theorem sphereConnected_real : SphereConnected ℝ 1 := fun n i hi x => by
  have hV : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = (n - 1) + 1 := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
    omega
  exact subsingleton_homotopyGroup_of_homeomorph (stiefelSphere ℝ (Fin n)) x
    (subsingleton_pi_sphere_of_finrank hV (by omega) _)

/-- **`O(m) → O(m + 1) → Sᵐ` is locally trivial**, `g ↦ g e_{m+1}`, with fibre `O(m)`. -/
theorem isLocallyTrivial_sphereOrbit_real (m : ℕ) :
    IsLocallyTrivial (sphereOrbit ℝ m) (orthogonalGroup (Fin m) ℝ) :=
  isLocallyTrivial_sphereOrbit m

section Orthogonal

variable {m k : ℕ}

/-- **Stability for `O(m)`** (Milnor p. 138): the inclusion `O(m) → O(m + k)`,
`T ↦ diag(T, I_k)`, induces bijections `πᵢ O(m) → πᵢ O(m + k)` for `i < m − 1`. -/
theorem bijective_homotopyGroupMap_orthogonalIncl {i : ℕ} (hi : i + 2 ≤ m)
    (T : orthogonalGroup (Fin m) ℝ) :
    Bijective (homotopyGroupMap (N := Fin i) (unitaryInclC (𝕜 := ℝ) m k) T) :=
  bijective_homotopyGroupMap_unitaryIncl sphereConnected_real (by omega) T

/-- **Stability for `O(m)`, the top degree**: `πᵢ O(m) → πᵢ O(m + k)` is onto for `i ≤ m − 1`. -/
theorem surjective_homotopyGroupMap_orthogonalIncl {i : ℕ} (hi : i + 1 ≤ m)
    (T : orthogonalGroup (Fin m) ℝ) :
    Surjective (homotopyGroupMap (N := Fin i) (unitaryInclC (𝕜 := ℝ) m k) T) :=
  surjective_homotopyGroupMap_unitaryIncl sphereConnected_real (by omega) T

/-- **The stabilization `Ω₀(16r) = O(16r) → O(16r + 16) = Ω₀(16r + 16)`, `T ↦ T ⊕ I₁₆`**
(Milnor p. 138) induces bijections on `πᵢ` for `i < 16r − 1`. -/
theorem bijective_homotopyGroupMap_omegaZeroStab {r i : ℕ} (hi : i + 2 ≤ 16 * r)
    (T : orthogonalGroup (Fin (16 * r)) ℝ) :
    Bijective (homotopyGroupMap (N := Fin i) (unitaryInclC (𝕜 := ℝ) (16 * r) 16) T) :=
  bijective_homotopyGroupMap_orthogonalIncl hi T

/-- **`V_k(ℝⁿ)` is `(n − k − 1)`-connected**: `πᵢ V_k(ℝⁿ) = 0` for `i < n − k`. -/
theorem subsingleton_pi_stiefel_real {n i : ℕ} (hkn : k ≤ n) (hi : i + 1 ≤ n - k)
    (x : Stiefel ℝ (Fin n) (Fin k)) : Subsingleton (π_ i (Stiefel ℝ (Fin n) (Fin k)) x) :=
  subsingleton_pi_stiefel sphereConnected_real k n hkn i (by omega) x

end Orthogonal

section Grassmannian

variable {m m' : ℕ}

/-- **`π_{j+1} G_m(ℝ^{m'+m}) ≅ π_j O(m)` for `j + 2 ≤ m'`**, through the boundary map of
`O(m) → V_m(ℝ^{m'+m}) → G_m(ℝ^{m'+m})`; at the base point `P₀`. -/
def grassmannianEquiv_real {j : ℕ} (hj : j + 2 ≤ m') :
    π_ (j + 1) (Grassmannian ℝ (Fin m' ⊕ Fin m) m) (grassBase ℝ (Fin m') m) ≃
      π_ j (orthogonalGroup (Fin m) ℝ) 1 :=
  grassmannianEquiv sphereConnected_real (by omega)

/-- **`π_{j+2} G_m(ℝ^{m'+m}) ≅ π_{j+1} O(m)` as groups** for `j + 3 ≤ m'`. -/
theorem nonempty_mulEquiv_grassmannian_real {j : ℕ} (hj : j + 3 ≤ m') :
    Nonempty (π_ (j + 2) (Grassmannian ℝ (Fin m' ⊕ Fin m) m) (grassBase ℝ (Fin m') m) ≃*
      π_ (j + 1) (orthogonalGroup (Fin m) ℝ) 1) :=
  nonempty_mulEquiv_grassmannian sphereConnected_real (by omega)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Grassmannian of `ℝ^ι`, `ι ≃ Fin m' ⊕ Fin m`, at any point `P`, moved to the base point
`P₀` of `G_m(ℝ^{Fin m' ⊕ Fin m})`. -/
def grassmannianToBase_real (e : ι ≃ Fin m' ⊕ Fin m) (P : Grassmannian ℝ ι m) :
    Grassmannian ℝ ι m ≃ₜ Grassmannian ℝ (Fin m' ⊕ Fin m) m :=
  (grassCongr e).trans (grassMove (grassCongr e P))

omit [DecidableEq ι] in
theorem grassmannianToBase_real_self (e : ι ≃ Fin m' ⊕ Fin m) (P : Grassmannian ℝ ι m) :
    grassmannianToBase_real e P P = grassBase ℝ (Fin m') m :=
  grassMove_self _

/-- **`π_{j+1}(G_m(ℝ^ι), P) ≅ π_j(O(m), 1)`** for `|ι| = m' + m`, `j + 2 ≤ m'`, at any `P`. -/
def grassmannianPiEquiv_real (e : ι ≃ Fin m' ⊕ Fin m) (P : Grassmannian ℝ ι m) {j : ℕ}
    (hj : j + 2 ≤ m') : π_ (j + 1) (Grassmannian ℝ ι m) P ≃ π_ j (orthogonalGroup (Fin m) ℝ) 1 :=
  (piEquivOfHomeomorph (grassmannianToBase_real e P) (grassmannianToBase_real_self e P) _).trans
    (grassmannianEquiv_real hj)

omit [DecidableEq ι] in
/-- The same as groups, for `j + 3 ≤ m'`. -/
theorem nonempty_mulEquiv_grassmannianPi_real (e : ι ≃ Fin m' ⊕ Fin m) (P : Grassmannian ℝ ι m)
    {j : ℕ} (hj : j + 3 ≤ m') :
    Nonempty (π_ (j + 2) (Grassmannian ℝ ι m) P ≃* π_ (j + 1) (orthogonalGroup (Fin m) ℝ) 1) := by
  obtain ⟨e₁⟩ := nonempty_mulEquiv_of_homeomorph (grassmannianToBase_real e P)
    (grassmannianToBase_real_self e P) (j + 1)
  obtain ⟨e₂⟩ := nonempty_mulEquiv_grassmannian_real (m := m) hj
  exact ⟨e₁.trans e₂⟩

end Grassmannian


/-! ### `SO(n)` and `O(n)` have the same higher homotopy groups -/

section SpecialOrthogonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_mul_self_of_mem_orthogonalGroup {A : Matrix ι ι ℝ}
    (hA : A ∈ orthogonalGroup ι ℝ) : A.det * A.det = 1 := by
  simpa using Unitary.star_mul_self_of_mem (det_of_mem_unitary hA)

/-- `SO(n)`, as a subset of `O(n)`: the matrices of determinant `1`. -/
def soSet (ι : Type*) [Fintype ι] [DecidableEq ι] : Set (orthogonalGroup ι ℝ) :=
  {g | (g : Matrix ι ι ℝ).det = 1}

/-- **`SO(n)` is open and closed in `O(n)`** (`det = ±1` on `O(n)`). -/
theorem isClopen_soSet : IsClopen (soSet ι) := by
  have hc : Continuous fun g : orthogonalGroup ι ℝ => (g : Matrix ι ι ℝ).det :=
    continuous_subtype_val.matrix_det
  refine ⟨isClosed_eq hc continuous_const, ?_⟩
  have : soSet ι = {g : orthogonalGroup ι ℝ | 0 < (g : Matrix ι ι ℝ).det} := by
    ext g
    have h := det_mul_self_of_mem_orthogonalGroup g.2
    change _ = (1 : ℝ) ↔ (0 : ℝ) < _
    constructor
    · intro h1
      rw [h1]
      exact one_pos
    · intro h0
      nlinarith
  rw [this]
  exact isOpen_lt continuous_const hc

/-- `SO(n)` is homeomorphic to its copy in `O(n)`. -/
def soHomeomorph (ι : Type*) [Fintype ι] [DecidableEq ι] :
    specialOrthogonalGroup ι ℝ ≃ₜ soSet ι where
  toFun A := ⟨⟨A, (mem_specialOrthogonalGroup_iff.1 A.2).1⟩,
    (mem_specialOrthogonalGroup_iff.1 A.2).2⟩
  invFun g := ⟨g.1.1, mem_specialOrthogonalGroup_iff.2 ⟨g.1.2, g.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

variable (ι) in
/-- The inclusion `SO(n) → O(n)`. -/
def soInclC : C(specialOrthogonalGroup ι ℝ, orthogonalGroup ι ℝ) :=
  ⟨fun A => ⟨A, (mem_specialOrthogonalGroup_iff.1 A.2).1⟩, continuous_subtype_val.subtype_mk _⟩

/-- **`πᵢ SO(n) ≅ πᵢ O(n)` for `i ≥ 1`** (Milnor p. 135, in Theorem 24.3:
"`π_{i+1} SO(n) = π_{i+1} O(n)`"): the inclusion induces bijections on `π_N` for `N` nonempty.
`SO(n)` is the clopen set `det = 1` of `O(n)`, and a generalized loop or homotopy at a point of
a clopen set never leaves it. -/
theorem bijective_homotopyGroupMap_soInclC {N : Type*} [Finite N] [Nonempty N]
    (A : specialOrthogonalGroup ι ℝ) :
    Bijective (homotopyGroupMap (N := N) (soInclC ι) A) := by
  have hc : soInclC ι = (⟨Subtype.val, continuous_subtype_val⟩ : C(soSet ι, _)).comp
      (soHomeomorph ι : C(_, soSet ι)) := rfl
  rw [hc, homotopyGroupMap_comp]
  exact (bijective_homotopyGroupMap_clopen isClopen_soSet (soHomeomorph ι A).2).comp
    (bijective_homotopyGroupMap_homeomorph (N := N) (soHomeomorph ι) A)

end SpecialOrthogonal

end Morse.Homotopy
