import Morse.Chapter13.Freudenthal
import Morse.Homotopy.ChangeOfBaseGroup

/-!
Milnor, *Morse Theory*, §22, Corollaries 22.2 and 22.3 (pp. 118–119), as isomorphisms of groups.

# Corollaries 22.2 and 22.3 for groups

## Milnor's text, paraphrased

(p. 118) **Corollary 22.2**: `π_i(Ω^d) ≅ π_{i+1}(M)` for `0 ≤ i ≤ λ₀ − 2`.  (p. 119)
**Corollary 22.3**: `π_i(Sⁿ) ≅ π_{i+1}(Sⁿ⁺¹)` for `i ≤ 2n − 2`.  The isomorphisms are of groups
for `i ≥ 1`.

## What is formalized

* `Morse.nonempty_mulEquiv_pathSp`: `π_{j+1}(Ω(N; p, q), γ) ≅ π_{j+2}(N, p)` as groups, at any
  `γ` (Theorem 17.1, `δ ↦ δ · γ⁻¹`, change of basepoint, loop space).
* `Morse.corollary_22_2_mulEquiv`: **Corollary 22.2 as groups**, `π_i(Ω^d, γ) ≃* π_{i+1}(N, p)`
  for `1 ≤ i ≤ λ₀ − 2`; `Morse.corollary_22_2_surjective_hom`: a surjective homomorphism for
  `1 ≤ i ≤ λ₀ − 1`.
* `Morse.corollary_22_3_mulEquiv`: **Corollary 22.3 as groups**, `π_i(Sⁿ, x) ≃* π_{i+1}(Sⁿ⁺¹, y)`
  for `1 ≤ i ≤ 2n − 2`; `Morse.corollary_22_3_surjective_hom`: a surjective homomorphism for
  `1 ≤ i ≤ 2n − 1`.

## What Milnor leaves implicit

* **Every step is a homomorphism.**  The bijections of `Morse.corollary_22_2` are composed of
  maps induced by continuous maps (homomorphisms, `Morse.Homotopy.homotopyGroupHom`), the
  loop-space isomorphism (`Morse.Homotopy.homotopyGroupPiLoopMulEquiv`), and one change of
  basepoint, from `γ · γ⁻¹` to the constant loop; that the last is a homomorphism is
  `Morse.Homotopy.changeBaseMulEquiv` (`Morse/Homotopy/ChangeOfBaseGroup.lean`).
* `i = 0`: `π_0` carries no group structure; the bijections are `Morse.corollary_22_2` and
  `Morse.corollary_22_3`.
-/

open Set Function Topology Module
open scoped Manifold Topology.Homotopy

noncomputable section

namespace Morse

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {N : Set V}

/-- The isomorphisms `π_{i+1}(Ω, γ) ≅ π_{i+2}(N, p)` behind Corollary 22.2, as a group isomorphism
(`Ω = Ω(N; p, q)` with Milnor's metric, at any path `γ`): Theorem 17.1, `Ω* ≅ Path p q`,
`δ ↦ δ · γ⁻¹`, change of basepoint, and the loop-space isomorphism. -/
theorem nonempty_mulEquiv_pathSp (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (j : ℕ) (γ : PathSp N p q) :
    Nonempty (π_ (j + 1) (PathSp N p q) γ ≃* π_ (j + 2) N ⟨p, hp⟩) := by
  have h2 := Morse.Homotopy.bijective_homotopyGroupMap_of_isHomotopyEquiv (N := Fin (j + 1))
    (theorem_17_1 hN p q) γ
  set e := pathCHomeomorph (N := N) hp hq
  have h3 := Morse.Homotopy.bijective_homotopyGroupMap_homeomorph (N := Fin (j + 1)) e
    (pathIncl (N := N) p q γ)
  set x := e (pathIncl (N := N) p q γ)
  have h4 := Morse.Homotopy.bijective_homotopyGroupMap_of_homotopyEquiv (N := Fin (j + 1))
    (Morse.Homotopy.pathTransHomotopyEquiv x.symm) x
  exact ⟨(MulEquiv.ofBijective (Morse.Homotopy.homotopyGroupHom _ _) h2).trans
    ((MulEquiv.ofBijective (Morse.Homotopy.homotopyGroupHom _ _) h3).trans
      ((MulEquiv.ofBijective (Morse.Homotopy.homotopyGroupHom _ _) h4).trans
        ((Morse.Homotopy.changeBaseMulEquiv (contractPath x)).trans
          (Morse.Homotopy.homotopyGroupPiLoopMulEquiv j))))⟩

/-- **Corollary 22.2 as groups** (Milnor p. 118): under the hypotheses of Theorem 22.1, for
`1 ≤ i ≤ λ₀ − 2` (`i = j + 1`) and every minimal path `γ`, `π_i(Ω^d, γ) ≅ π_{i+1}(N, p)` as
groups. -/
theorem corollary_22_2_mulEquiv (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (hball : ∀ r : ℝ, IsCompact (closedRiemBall N p r)) {l₀ : ℕ}
    (hidx : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ →
      (∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy γ 0 1) →
      (l₀ : ℕ∞) ≤ formIndex (energyHessian hN hγ))
    (hretr : ∃ O : Set (PathSp N p q), IsOpen O ∧ minPaths N p q ⊆ O ∧
      ∃ ρ : PathSp N p q → PathSp N p q, ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths N p q) ∧
        ∀ γ ∈ minPaths N p q, ρ γ = γ)
    {j : ℕ} (hj : j + 3 ≤ l₀) (γ : minPaths N p q) :
    Nonempty (π_ (j + 1) (minPaths N p q) γ ≃* π_ (j + 2) N ⟨p, hp⟩) := by
  have h1 := theorem_22_1_bijective hN hp hq hball hidx hretr (K := Fin (j + 1))
    (by simpa using hj) γ
  obtain ⟨e⟩ := nonempty_mulEquiv_pathSp hN hp hq j (γ : PathSp N p q)
  exact ⟨(MulEquiv.ofBijective (Morse.Homotopy.homotopyGroupHom _ _) h1).trans e⟩

/-- **Corollary 22.2, the top degree, as groups**: for `1 ≤ i ≤ λ₀ − 1` there is a surjective
homomorphism `π_i(Ω^d, γ) → π_{i+1}(N, p)`. -/
theorem corollary_22_2_surjective_hom (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) Z W N) {p q : V}
    (hp : p ∈ N) (hq : q ∈ N) (hball : ∀ r : ℝ, IsCompact (closedRiemBall N p r)) {l₀ : ℕ}
    (hidx : ∀ γ (hγ : γ ∈ pathSpace N p q), IsUnbrokenGeodesic hN γ →
      (∃ γ' ∈ pathSpace N p q, energy γ' 0 1 < energy γ 0 1) →
      (l₀ : ℕ∞) ≤ formIndex (energyHessian hN hγ))
    (hretr : ∃ O : Set (PathSp N p q), IsOpen O ∧ minPaths N p q ⊆ O ∧
      ∃ ρ : PathSp N p q → PathSp N p q, ContinuousOn ρ O ∧ (∀ γ ∈ O, ρ γ ∈ minPaths N p q) ∧
        ∀ γ ∈ minPaths N p q, ρ γ = γ)
    {j : ℕ} (hj : j + 2 ≤ l₀) (γ : minPaths N p q) :
    ∃ f : π_ (j + 1) (minPaths N p q) γ →* π_ (j + 2) N ⟨p, hp⟩, Surjective f := by
  have h1 := theorem_22_1_surjective hN hp hq hball hidx hretr (K := Fin (j + 1))
    (by simp; omega) γ
  obtain ⟨e⟩ := nonempty_mulEquiv_pathSp hN hp hq j (γ : PathSp N p q)
  exact ⟨e.toMonoidHom.comp (Morse.Homotopy.homotopyGroupHom (N := Fin (j + 1))
    (minPathsIncl N p q) γ), e.surjective.comp h1⟩

end General

open Milnor.Sphere

/-- **Corollary 22.3 (Freudenthal) as groups** (Milnor p. 119): `π_i(Sⁿ) ≅ π_{i+1}(Sⁿ⁺¹)` as
groups for `1 ≤ i ≤ 2n − 2` (`i = j + 1`), at any base points. -/
theorem corollary_22_3_mulEquiv {n j : ℕ} (hj : j + 3 ≤ 2 * n) (x : Sph n) (y : Sph (n + 1)) :
    Nonempty (π_ (j + 1) (Sph n) x ≃* π_ (j + 2) (Sph (n + 1)) y) := by
  obtain ⟨p, hp⟩ := y
  let h := equatorHomeomorph hp
  let H := sphMinPathsHomotopyEquiv hp
  obtain ⟨e₃⟩ := corollary_22_2_mulEquiv (sphSub (n + 1)) hp (neg_mem_sph hp) (hball_sph p)
    (hidx_sph hp) (exists_retraction_minPaths_sph hp) hj (H.toFun (h.symm x))
  exact ⟨(MulEquiv.ofBijective (Morse.Homotopy.homotopyGroupHom (h.symm : C(Sph n, equator p)) x)
    (Morse.Homotopy.bijective_homotopyGroupMap_homeomorph h.symm x)).trans
    ((MulEquiv.ofBijective (Morse.Homotopy.homotopyGroupHom H.toFun (h.symm x))
      (Morse.Homotopy.bijective_homotopyGroupMap_of_homotopyEquiv H (h.symm x))).trans e₃)⟩

/-- **The second half of Freudenthal's theorem, as groups**: a surjective homomorphism
`π_i(Sⁿ) → π_{i+1}(Sⁿ⁺¹)` for `1 ≤ i ≤ 2n − 1` (`i = j + 1`). -/
theorem corollary_22_3_surjective_hom {n j : ℕ} (hj : j + 2 ≤ 2 * n) (x : Sph n)
    (y : Sph (n + 1)) :
    ∃ f : π_ (j + 1) (Sph n) x →* π_ (j + 2) (Sph (n + 1)) y, Surjective f := by
  obtain ⟨p, hp⟩ := y
  let h := equatorHomeomorph hp
  let H := sphMinPathsHomotopyEquiv hp
  obtain ⟨f, hf⟩ := corollary_22_2_surjective_hom (sphSub (n + 1)) hp (neg_mem_sph hp)
    (hball_sph p) (hidx_sph hp) (exists_retraction_minPaths_sph hp) hj (H.toFun (h.symm x))
  let E := (MulEquiv.ofBijective (Morse.Homotopy.homotopyGroupHom (N := Fin (j + 1))
    (h.symm : C(Sph n, equator p)) x)
    (Morse.Homotopy.bijective_homotopyGroupMap_homeomorph h.symm x)).trans
    (MulEquiv.ofBijective (Morse.Homotopy.homotopyGroupHom (N := Fin (j + 1)) H.toFun (h.symm x))
      (Morse.Homotopy.bijective_homotopyGroupMap_of_homotopyEquiv H (h.symm x)))
  exact ⟨f.comp E.toMonoidHom, hf.comp E.surjective⟩

end Morse
