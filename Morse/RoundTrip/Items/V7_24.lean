import Morse
import RoundTrip.Check
import RoundTrip.Blind.V7_24

open scoped ContDiff Manifold
open Bundle

namespace RoundTrip.V7_24

/-- The project's statement (universes instantiated at 0): `Morse.IsMinimalGeodesic hN γ a b`
(a definition: `a ≤ b`, `γ` the restriction of a geodesic on a set `s ⊇ [a, b]` of the slice
submanifold `N ⊆ V`, and `pathLength γ a b ≤ pathLength c a' b'` for every piecewise smooth path
`c` in `N` with the same endpoints) is vocabulary; the theorems are: `exp` takes values in `N` on
its domain, and a geodesic `t ↦ exp_p(tv)` on `ℝ` with `ρ(p, exp_p v) = ‖v‖` is a minimal
geodesic on `[0, 1]` of length `‖v‖`. -/
def A : Prop :=
  type_of% @Morse.exp_mem_of_mem_expDom.{0,0,0} ∧
    type_of% @Morse.isMinimalGeodesic_exp_smul.{0,0,0}

theorem A_holds : A := ⟨@Morse.exp_mem_of_mem_expDom, @Morse.isMinimalGeodesic_exp_smul⟩

section Outright

set_option linter.unusedSectionVars false

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Rn n) M]
  [IsManifold 𝓘(ℝ, Rn n) ∞ M] [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, Rn n) x)]

/-- Arc lengths over `[a', b']`, `a' ≤ b'`, are nonnegative. -/
theorem arcLen_nonneg' {pth : ℝ → M} {a b : ℝ} (hab : a ≤ b) : 0 ≤ arcLen (n := n) pth a b :=
  intervalIntegral.integral_nonneg hab fun _ _ => norm_nonneg _

/-- A smooth curve on `[a, b]`, `a < b`, is piecewise smooth (one piece). -/
theorem isPW_of_smooth {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, Rn n) ∞ c (Set.Icc a b)) : IsPW (n := n) c a b := by
  refine ⟨1, fun i => if i = 0 then a else b, by simp, by simp, ?_, ?_⟩
  · intro i hi
    have : i = 0 := by omega
    subst this; simpa using hab
  · intro i hi
    have : i = 0 := by omega
    subst this; simpa using hc

/-- **B holds outright**: "minimal" (length `≤` that of every piecewise smooth path with the same
end points) is the same as "length `= ρ`" for a geodesic on `[a, b]`, `a < b`, since the geodesic
is itself one of the competing paths and lengths are `≥ 0`. No geometry (connection, Levi-Civita,
completeness) is used. -/
theorem B_holds : B := by
  intro n M _ _ _ _ _ _ _ cov _ γ a b hab
  set S : Set ℝ := {L | ∃ (pth : ℝ → M) (a' b' : ℝ), a' ≤ b' ∧ IsPW (n := n) pth a' b' ∧
    pth a' = γ a ∧ pth b' = γ b ∧ arcLen (n := n) pth a' b' = L} with hS
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨pth, a', b', hab', -, -, -, rfl⟩
    exact arcLen_nonneg' hab'
  have hmem : IsGeodesic cov γ (Set.Icc a b) → arcLen (n := n) γ a b ∈ S := fun hg =>
    ⟨γ, a, b, hab.le, isPW_of_smooth hab hg.2.1, rfl, rfl, rfl⟩
  have hrho : rho (n := n) (γ a) (γ b) = sInf S := rfl
  constructor
  · rintro ⟨hg, hmin⟩
    refine ⟨hg, ?_⟩
    rw [hrho]
    refine (IsLeast.csInf_eq ⟨hmem hg, ?_⟩).symm
    rintro _ ⟨pth, a', b', hab', hpw, ha, hb, rfl⟩
    exact hmin pth a' b' hab' hpw ha hb
  · rintro ⟨hg, hlen⟩
    refine ⟨hg, fun pw a' b' hab' hpw ha hb => ?_⟩
    rw [hlen, hrho]
    exact csInf_le hbdd ⟨pw, a', b', hab', hpw, ha, hb, rfl⟩

end Outright

/-- `A → B`, vacuously: `B` is proved outright (`B_holds`), without `A`. -/
theorem A_to_B : A → B := fun _ => B_holds

/-- `B → A`, vacuously: `A` is re-proved outright from other project lemmas (the proofs of
`Morse.exp_mem_of_mem_expDom` and `Morse.isMinimalGeodesic_exp_smul` replayed), without `B`; `B`
(a tautology about `sInf`, in the abstract setting) carries nothing towards `A`. -/
theorem B_to_A : B → A := by
  intro _
  refine ⟨?_, ?_⟩
  · intro V _ _ _ Z _ _ _ W _ _ _ N hN p v h
    obtain ⟨γ, hγ, he⟩ := Morse.exp_eq_of_mem_expDom h
    obtain ⟨δ, hδ, hγo, -, -⟩ := hγ
    rw [he]
    exact hγo.mem 1 ⟨by linarith, by linarith⟩
  · intro V _ _ _ Z _ _ _ W _ _ _ N hN p v hv hgeo hρ
    have hlen : Morse.pathLength (fun t => Morse.exp hN p (t • v)) 0 1 = ‖v‖ := by
      rw [hgeo.pathLength_eq isPreconnected_univ zero_le_one (Set.subset_univ _) (Set.mem_univ 0),
        (Morse.hasDerivAt_exp_smul_zero p hv).deriv]
      ring
    refine ⟨⟨zero_le_one, ⟨Set.univ, Set.subset_univ _, hgeo⟩, fun c a b hc hcN ha hb => ?_⟩, hlen⟩
    have h1 := Morse.riemDist_le_pathLength (N := N) hc hcN
    simp only [ha, hb, zero_smul, one_smul, Morse.exp_zero p.2, hρ] at h1
    rw [hlen]
    exact (ENNReal.ofReal_le_ofReal_iff hc.isAdmissible.pathLength_nonneg).1 h1

#rt_check RoundTrip.V7_24.A_to_B [Morse.exp_mem_of_mem_expDom, Morse.isMinimalGeodesic_exp_smul]
#rt_check RoundTrip.V7_24.B_to_A [Morse.exp_mem_of_mem_expDom, Morse.isMinimalGeodesic_exp_smul]
#rt_overlap RoundTrip.V7_24.B_to_A [Morse.exp_mem_of_mem_expDom, Morse.isMinimalGeodesic_exp_smul]

end RoundTrip.V7_24
