import Mathlib
import Morse.Homotopy.CellAttach
import Morse.Homology.Spheres

/-!
# The homotopy groups of spheres below the dimension

`πᵢ(Sⁿ) = 0` for `i < n` (Mathlib lists this among the TODOs of
`Mathlib/Topology/Homotopy/HomotopyGroup.lean`). It is what feeds the exact homotopy sequences of
the fibrations `U(m) → U(m + 1) → S^{2m+1}` in Milnor's §§23–24.

## Proof

The unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` is the union of its lower hemisphere `D₋` and its upper hemisphere
`D₊`, the graphs of `∓√(1 - ‖z‖²)` over the closed unit ball of `ℝⁿ`
(`Morse.Homology.hemisphere`, `Morse.Homology.sphere_eq_union_hemisphere`), and `D₊` is an
`n`-cell embedded in `ℝⁿ⁺¹` meeting `D₋` exactly along its boundary
(`Morse.Homology.hemisphere_one_mem_iff`). So `Sⁿ` is `D₋` with an `n`-cell attached, and the
cell-attachment theorem (`Morse.Homotopy.surjective_homotopyGroupMap_union_cell`, the push-off
of `Morse/Homotopy/CellAttach.lean`) makes `πᵢ(D₋) → πᵢ(Sⁿ)` onto for `i < n`. The hemisphere
`D₋` is homeomorphic to the closed ball, which is convex, hence contractible: `πᵢ(D₋) = 0`
(`Morse.Homotopy.subsingleton_homotopyGroup_of_contractible`). This gives the basepoints in
`D₋`; the others follow by change of basepoint (`Sⁿ` is path-connected for `n ≥ 1`).

## Main results

* `Morse.Homotopy.subsingleton_homotopyGroup_sphere`: `π_N(Sⁿ, x)` is trivial for `|N| < n`, for
  the unit sphere of `EuclideanSpace ℝ (Fin (n + 1))`; `Morse.Homotopy.subsingleton_pi_sphere`:
  the same for `π_ i`, `i < n`.
* `Morse.Homotopy.subsingleton_pi_sphere_of_finrank`: the same for the unit sphere of any real
  inner product space of dimension `n + 1` (through a linear isometry with `ℝⁿ⁺¹`).
* `Morse.Homotopy.subsingleton_pi_sphere_complex`: `πᵢ(S^{2m-1}) = 0` for `i < 2m - 1`, for the
  unit sphere of `ℂᵐ = EuclideanSpace ℂ (Fin m)`.
-/

open Set Metric Function Module Topology
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

open Morse.Homology (hemisphere continuous_hemisphere hemisphere_injective
  sphere_eq_union_hemisphere hemisphere_one_mem_iff hemisphere_mem_sphere)

/-- **Contractible spaces have trivial homotopy groups.** -/
theorem subsingleton_homotopyGroup_of_contractible {N X : Type*} [Finite N] [TopologicalSpace X]
    [ContractibleSpace X] (x : X) : Subsingleton (HomotopyGroup N X x) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  have : Subsingleton (HomotopyGroup N Unit (e.toFun x)) := ⟨fun a b => by
    induction a using Quotient.inductionOn with
    | h a =>
    induction b using Quotient.inductionOn with
    | h b => exact congrArg _ (GenLoop.ext _ _ fun _ => rfl)⟩
  exact (bijective_homotopyGroupMap_of_homotopyEquiv (N := N) e x).injective.subsingleton

/-- Homotopy groups are trivial at every basepoint of a path-connected space once they are at
one. -/
theorem subsingleton_homotopyGroup_of_joined {N X : Type*} [Finite N] [TopologicalSpace X]
    {x y : X} (hxy : Joined x y) (h : Subsingleton (HomotopyGroup N X y)) :
    Subsingleton (HomotopyGroup N X x) := by
  have := Fintype.ofFinite N
  exact (changeBaseEquiv (N := N) hxy.somePath).injective.subsingleton

section Sphere

variable {n : ℕ}

/-- The lower hemisphere `D₋ ⊆ Sⁿ ⊆ ℝⁿ⁺¹`. -/
abbrev lowerHemisphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  hemisphere (-1) '' closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

theorem isClosed_lowerHemisphere : IsClosed (lowerHemisphere n) :=
  ((isCompact_closedBall _ _).image (continuous_hemisphere _)).isClosed

/-- The lower hemisphere is contractible: it is homeomorphic to the closed ball. -/
instance contractibleSpace_lowerHemisphere : ContractibleSpace (lowerHemisphere n) := by
  let f : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun z => hemisphere (-1) z
  have : CompactSpace (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  have hf : IsClosedEmbedding f :=
    ((continuous_hemisphere _).comp continuous_subtype_val).isClosedEmbedding
      fun z w h => Subtype.ext (hemisphere_injective _ h)
  have hrange : range f = lowerHemisphere n := by
    ext x
    simp [f, lowerHemisphere]
  let e : closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ lowerHemisphere n :=
    hf.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have : ContractibleSpace (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (convex_closedBall _ _).contractibleSpace ⟨0, mem_closedBall_self zero_le_one⟩
  exact e.symm.contractibleSpace

theorem lowerHemisphere_union : lowerHemisphere n ∪ hemisphere 1 '' closedBall 0 1 =
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  sphere_eq_union_hemisphere.symm

/-- The south pole `-eₙ₊₁`, in the lower hemisphere. -/
def southPole (n : ℕ) : lowerHemisphere n :=
  ⟨hemisphere (-1) 0, 0, mem_closedBall_self zero_le_one, rfl⟩

/-- **`π_N(Sⁿ)` vanishes at the south pole for `|N| < n`**: the sphere is the lower hemisphere,
which is contractible, with an `n`-cell attached. -/
theorem subsingleton_homotopyGroup_sphere_southPole {N : Type*} [Fintype N]
    (hN : Fintype.card N < n) :
    Subsingleton (HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      ⟨hemisphere (-1) 0,
        hemisphere_mem_sphere (by norm_num) (mem_closedBall_self zero_le_one)⟩) := by
  have hsurj := surjective_homotopyGroupMap_union_cell (N := N) isClosed_lowerHemisphere
    (continuous_hemisphere 1).continuousOn (hemisphere_injective 1).injOn
    (fun z hz => hemisphere_one_mem_iff hz) hN (southPole n)
  have := subsingleton_homotopyGroup_of_contractible (N := N) (southPole n)
  have : Subsingleton (HomotopyGroup N ↥(lowerHemisphere n ∪ hemisphere 1 '' closedBall 0 1)
      ⟨hemisphere (-1) 0, Or.inl (southPole n).2⟩) :=
    hsurj.subsingleton
  exact (bijective_homotopyGroupMap_homeomorph (N := N) (Homeomorph.setCongr lowerHemisphere_union)
    ⟨hemisphere (-1) 0, Or.inl (southPole n).2⟩).surjective.subsingleton

/-- **`πᵢ(Sⁿ) = 0` for `i < n`**, at every basepoint: `π_N(Sⁿ, x)` is trivial for `|N| < n`,
`Sⁿ` the unit sphere of `ℝⁿ⁺¹`. -/
theorem subsingleton_homotopyGroup_sphere {N : Type*} [Finite N] (hN : Nat.card N < n)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Subsingleton (HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) := by
  have := Fintype.ofFinite N
  rw [Nat.card_eq_fintype_card] at hN
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  have : PathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_sphere hrank 0 zero_le_one)
  exact subsingleton_homotopyGroup_of_joined (PathConnectedSpace.joined _ _)
    (subsingleton_homotopyGroup_sphere_southPole hN)

/-- **`πᵢ(Sⁿ) = 0` for `i < n`** (`π_ i` form), `Sⁿ` the unit sphere of `ℝⁿ⁺¹`. -/
theorem subsingleton_pi_sphere {i : ℕ} (hi : i < n)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Subsingleton (π_ i (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) :=
  subsingleton_homotopyGroup_sphere (by rwa [Nat.card_eq_fintype_card, Fintype.card_fin]) x

end Sphere

/-- A linear isometry carries the unit sphere homeomorphically onto the unit sphere. -/
def sphereHomeomorph {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [NormedSpace ℝ V] [NormedSpace ℝ W] (e : V ≃ₗᵢ[ℝ] W) :
    sphere (0 : V) 1 ≃ₜ sphere (0 : W) 1 where
  toFun v := ⟨e v, by simp⟩
  invFun w := ⟨e.symm w, by simp⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v)
  right_inv w := Subtype.ext (e.apply_symm_apply w)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- **`πᵢ(Sⁿ) = 0` for `i < n`** for the unit sphere of any real inner product space of dimension
`n + 1`. -/
theorem subsingleton_pi_sphere_of_finrank {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {n : ℕ} (hV : finrank ℝ V = n + 1) {i : ℕ}
    (hi : i < n) (x : sphere (0 : V) 1) : Subsingleton (π_ i (sphere (0 : V) 1) x) := by
  let e : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (stdOrthonormalBasis ℝ V).repr.trans (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hV))
  have := subsingleton_pi_sphere hi (sphereHomeomorph e x)
  exact (bijective_homotopyGroupMap_homeomorph (N := Fin i) (sphereHomeomorph e)
    x).injective.subsingleton

/-- **`πᵢ(S^{2m-1}) = 0` for `i < 2m - 1`**, for the unit sphere of `ℂᵐ`. -/
theorem subsingleton_pi_sphere_complex {m i : ℕ} (hi : i + 1 < 2 * m)
    (x : sphere (0 : EuclideanSpace ℂ (Fin m)) 1) :
    Subsingleton (π_ i (sphere (0 : EuclideanSpace ℂ (Fin m)) 1) x) := by
  have hV : finrank ℝ (EuclideanSpace ℂ (Fin m)) = (2 * m - 1) + 1 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
      Fintype.card_fin]
    omega
  exact subsingleton_pi_sphere_of_finrank hV (by omega) x

end Morse.Homotopy
