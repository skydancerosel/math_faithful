import Morse
import RoundTrip.Check
import RoundTrip.Blind.V5_16

/-! Round trip V5_16 (Milnor §7, Theorem 7.1).  A = `Morse.theorem_7_1` (field coefficients,
closed complex submanifolds); B = Milnor's statement (`ℤ` coefficients, non-singular affine
algebraic varieties).  No direction is proved.  `A_to_B_field`: B's hypotheses give A's, so A gives
B with `ℤ` replaced by any field; the step to `ℤ` is the universal coefficient theorem (absent from
Mathlib and the project).  B ⇒ A fails genuinely (B is only about algebraic zero sets). -/

open CategoryTheory Morse.Homology
open scoped ContDiff Manifold

namespace RoundTrip.V5_16

/-- The project's statement (no universe parameters; `𝕜 : Type`): Theorem 7.1 **over a field**
for a closed slice submanifold `M ⊆ 𝔼 n` of real dimension `2k` with `J`-invariant tangent
spaces. -/
def A : Prop := type_of% @Morse.theorem_7_1

theorem A_holds : A := @Morse.theorem_7_1

/-- The common zero set of a family of polynomials is closed. -/
theorem isClosed_zeroSet {n : ℕ} (S : Set (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet S) := by
  have : zeroSet S = ⋂ F ∈ S, {z : Cn n | MvPolynomial.eval (fun j => z j) F = 0} := by
    ext z; simp [zeroSet]
  rw [this]
  refine isClosed_biInter fun F _ => isClosed_eq ?_ continuous_const
  exact (MvPolynomial.continuous_eval F).comp (continuous_pi fun j => PiLp.continuous_apply 2 _ j)

/-- A, specialised to B's setting with model dimension `D = 2k` written as a variable. -/
theorem key (hA : A) {K D m k : ℕ} (M : Set (Rn (K + 1)))
    (hM : Milnor.IsSliceSubmanifold 𝓘(ℝ, Rn (K + 1)) (Rn D) (Rn m) M)
    (J : Rn (K + 1) ≃ₗᵢ[ℝ] Rn (K + 1)) (hJ : IsCplxStr J)
    (hc : Morse.IsComplexSubmanifold hM (J.toContinuousLinearEquiv : Rn (K + 1) →L[ℝ] Rn (K + 1)))
    (hD : D = 2 * k)
    (hcl : IsClosed M) (𝕜 : Type) [Field 𝕜] {i : ℕ} (hi : k < i) :
    Subsingleton (spaceHomology 𝕜 i M) := by
  subst hD
  exact hA hM hcl (J := (J.toContinuousLinearEquiv : Rn (K + 1) →L[ℝ] Rn (K + 1)))
    ⟨fun v => hJ v, fun v w => J.inner_map_map v w⟩ hc hi

/-- **What A gives in B's setting: B with `ℤ` replaced by an arbitrary field.**  B's hypotheses
(zero set of polynomials, a complex submanifold of complex dimension `k` after a real isometry
`θ : ℂⁿ ≅ ℝ^{K+1}`) give A's (the zero set is closed; `θ` is a homeomorphism onto its image), so
`H_i(M; 𝕜) = 0` for `i > k` and every field `𝕜`.  The step to `ℤ` (B) is the universal
coefficient theorem, which neither Mathlib nor the project has. -/
theorem A_to_B_field (hA : A) (n k : ℕ) (S : Set (MvPolynomial (Fin n) ℂ))
    (hS : IsCplxSubmfd (zeroSet S) k) (𝕜 : Type) [Field 𝕜] (i : ℕ) (hi : k < i) :
    Subsingleton ((relHomology (ModuleCat.of 𝕜 𝕜) i).obj
      (subsetPair (Set.empty_subset (zeroSet S)))) := by
  obtain ⟨K, d, m, θ, J, hM, hJ, -, hc, hd⟩ := hS
  set M : Set (Rn (K + 1)) := θ '' zeroSet S with hM_def
  have hcl : IsClosed M := θ.toHomeomorph.isClosedMap _ (isClosed_zeroSet S)
  have h1 : Subsingleton (spaceHomology 𝕜 i M) := key hA M hM J hJ (fun q v hv => hc q v hv) hd hcl 𝕜 hi
  have h2 : Subsingleton (subsetHomology 𝕜 i (Set.empty_subset (Set.univ : Set M))) :=
    (subsetHomologyUnivEquiv (𝕜 := 𝕜) M i).toEquiv.subsingleton
  let φ : zeroSet S ≃ₜ (Set.univ : Set M) :=
    (θ.toHomeomorph.image (zeroSet S)).trans (Homeomorph.Set.univ M).symm
  exact subsingleton_subsetHomology_of_homeomorph (Set.empty_subset _) (Set.empty_subset _) φ
    (fun x => by simp) i h2

#rt_check RoundTrip.V5_16.A_to_B_field [Morse.theorem_7_1]

end RoundTrip.V5_16
