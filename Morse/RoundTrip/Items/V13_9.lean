import Morse
import RoundTrip.Check
import RoundTrip.Blind.V13_9

open scoped Topology

namespace RoundTrip.V13_9

/-- The project's statement: Corollary 22.3 (Freudenthal) on the project's spheres
`Milnor.Sphere.Sph n = sphG⁻¹{0} ⊆ ℝⁿ⁺¹`: the index estimate `hidx_sph` (non-minimal geodesics
from `p` to `-p` on `Sⁿ⁺¹` have index `≥ 2n`), compactness of closed Riemannian balls
`hball_sph`, bijections `π_i Sⁿ ≃ π_{i+1} Sⁿ⁺¹` (`i ≤ 2n − 2`), surjections (`i ≤ 2n − 1`),
group isomorphisms (`1 ≤ i ≤ 2n − 2`), surjective homomorphisms (`1 ≤ i ≤ 2n − 1`).
`equatorHomeomorph` is a definition (vocabulary). No universe parameters. -/
def A : Prop :=
  type_of% @Morse.hidx_sph ∧
  type_of% @Morse.hball_sph ∧
  type_of% @Morse.corollary_22_3 ∧
  type_of% @Morse.corollary_22_3_surjective ∧
  type_of% @Morse.corollary_22_3_mulEquiv ∧
  type_of% @Morse.corollary_22_3_surjective_hom

theorem A_holds : A :=
  ⟨@Morse.hidx_sph, @Morse.hball_sph, @Morse.corollary_22_3, @Morse.corollary_22_3_surjective,
    @Morse.corollary_22_3_mulEquiv, @Morse.corollary_22_3_surjective_hom⟩

/-- The project's sphere is the blind one (equal sets, not definitionally). -/
theorem sph_eq (n : ℕ) :
    Milnor.Sphere.Sph n = Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  Milnor.Sphere.preimage_eq_sphere

/-- `A ⇒ B`: the bijection and group-isomorphism clauses of `A`, rewritten along `sph_eq`. -/
theorem A_to_B : A → B := by
  rintro ⟨-, -, h1, -, h2, -⟩ n
  have e1 := sph_eq n
  have e2 := sph_eq (n + 1)
  have h1' : ∀ i : ℕ, i + 2 ≤ 2 * n → ∀ (x : ↥(Milnor.Sphere.Sph n))
      (y : ↥(Milnor.Sphere.Sph (n + 1))),
      Nonempty (HomotopyGroup.Pi i ↥(Milnor.Sphere.Sph n) x ≃
        HomotopyGroup.Pi (i + 1) ↥(Milnor.Sphere.Sph (n + 1)) y) := fun i hi => h1 hi
  have h2' : ∀ k : ℕ, k + 3 ≤ 2 * n → ∀ (x : ↥(Milnor.Sphere.Sph n))
      (y : ↥(Milnor.Sphere.Sph (n + 1))),
      Nonempty (HomotopyGroup.Pi (k + 1) ↥(Milnor.Sphere.Sph n) x ≃*
        HomotopyGroup.Pi (k + 2) ↥(Milnor.Sphere.Sph (n + 1)) y) := fun k hk => h2 hk
  rw [e1, e2] at h1' h2'
  exact fun x y => ⟨fun i hi => h1' i hi x y, fun k hk => h2' k hk x y⟩

/-! `B ⇒ A` is not proved: `A` has content `B` lacks.
* `corollary_22_3_surjective` / `_surjective_hom`: surjections `π_i Sⁿ → π_{i+1} Sⁿ⁺¹` for
  `i = 2n − 1` (the second half of Freudenthal's theorem), not a consequence of `B`
  (bijections only for `i ≤ 2n − 2`).
* `hidx_sph`: a Riemannian index estimate for geodesics on `Sⁿ⁺¹` (Jacobi fields / conjugate
  points), which no statement about homotopy groups implies.
* `hball_sph` is true outright (closed sets of a compact sphere) but not from `B`. -/

/-- On the common content the two agree: `B` gives back the bijection and group-isomorphism clauses
of `A` (`corollary_22_3`, `corollary_22_3_mulEquiv`). -/
theorem B_to_A_common : B →
    type_of% @Morse.corollary_22_3 ∧ type_of% @Morse.corollary_22_3_mulEquiv := by
  intro hB
  refine ⟨fun {n i} hi => ?_, fun {n k} hk => ?_⟩
  · rw [sph_eq n, sph_eq (n + 1)]
    exact fun x y => (hB n x y).1 i hi
  · rw [sph_eq n, sph_eq (n + 1)]
    exact fun x y => (hB n x y).2 k hk

#rt_check RoundTrip.V13_9.B_to_A_common [Morse.hidx_sph, Morse.hball_sph, Morse.corollary_22_3,
  Morse.corollary_22_3_surjective, Morse.corollary_22_3_mulEquiv,
  Morse.corollary_22_3_surjective_hom]

#rt_check RoundTrip.V13_9.A_to_B [Morse.hidx_sph, Morse.hball_sph, Morse.corollary_22_3,
  Morse.corollary_22_3_surjective, Morse.corollary_22_3_mulEquiv,
  Morse.corollary_22_3_surjective_hom]

end RoundTrip.V13_9
