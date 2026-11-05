import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_30

namespace RoundTrip.V15_30

/-- The project's statement (universes instantiated at `0`): (1) `IsInterRel.commute_exp`: an
intertwiner `D` (`bDA = −aAD`, `A²D = −b²D`, `DA² = −a²D`) commutes with `exp(sA)` for
`s(a + b) = 2π`; (2) `exists_killing_spaces`: from such intertwiners (with projections and
independence data) one gets Killing spaces `𝒳_τ ⊆ isoAlg`, `τ ∈ (0,1)`, of total dimension
`r₀·#κ`, satisfying the hypotheses of `sum_finrank_le_formIndex`; (3)
`exists_killing_spaces_omega` (`k + 1 ≤ 8`, `k + 1 ≢ 3 mod 4`, `A ∈ T` at `J_k`, `exp(πA) = −I`,
`A² ≠ −1`): such spaces with total dimension `r₀ s`, `(s + 1)·m_{k+1} = n`; (4)
`le_formIndex_of_not_minimal_omega` (same `k`; GIVEN a minimal direction `A₀ ∈ minVelO`, i.e.
`Ω_{k+1}(n) ≠ ∅`): every unbroken geodesic `J_k → −J_k` of the slice submanifold
`omegaStratum J k J_k` which does not have least ENERGY in the project's `pathSpace` has
`formIndex (energyHessian …) ≥ r₀ s` with `(s+1) m_{k+1} = n`; (5) `omega_hidx`: the same as
`≥ r₀ (n / m_{k+1} − 1)` for `IsAnticommFamily J (k + 1)`. Here `r₀ = 1`, or `r₀ = 2` for
`k = 0` (Lemma 24.2: `2m − 2`). -/
def A : Prop :=
  type_of% @Morse.IsInterRel.commute_exp.{0} ∧ type_of% @Morse.exists_killing_spaces.{0, 0} ∧
    type_of% @Morse.exists_killing_spaces_omega.{0} ∧
    type_of% @Morse.le_formIndex_of_not_minimal_omega.{0} ∧ type_of% @Morse.omega_hidx.{0}

theorem A_holds : A :=
  ⟨@Morse.IsInterRel.commute_exp.{0}, @Morse.exists_killing_spaces.{0, 0},
    @Morse.exists_killing_spaces_omega.{0}, @Morse.le_formIndex_of_not_minimal_omega.{0},
    @Morse.omega_hidx.{0}⟩

/-- Vocabulary: B's `mK` is the project's `milnorM`. -/
theorem mK_eq_milnorM : ∀ k, mK k = Morse.milnorM k
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | k + 8 => by rw [mK, mK_eq_milnorM k]; rfl

/-- B's `k ≢ 2 (mod 4)` is the project's `k + 1 ≢ 3 (mod 4)`. -/
theorem mod_iff (k : ℕ) : k % 4 ≠ 2 ↔ (k + 1) % 4 ≠ 3 := by omega

/-! Neither direction is proved (see `Items/V15_30.json`).

* A ⇒ B: A bounds the project's `formIndex (energyHessian …)` of an `IsUnbrokenGeodesic` of the
  slice submanifold `omegaStratum J k J_k`, non-minimal meaning "some path in the project's
  `pathSpace` has smaller energy"; B bounds the blind variational index `idxIn` (`HessNeg`: some
  variation in `Ω_k(n)` with negative `d²E/du²`) of a blind geodesic `IsGeodOn` of the SUBSET
  `Ω_k(n)`, non-minimal meaning "not length-minimizing among blind piecewise smooth paths in
  `Ω_k(n)`". The dictionary `formIndex ≤ idxIn` (and geodesic/path-space/minimality
  identifications) for subsets of `M_n(ℝ)` is not available (the analogue of `LamEq` of
  `Items/V9_23.lean` for this blind model). Even with it, A covers only `k + 1 ≤ 8` (B: all
  `k ≥ 1`, `k ≢ 2 mod 4`: genuinely missing for `k ≥ 8`), and A needs `Ω_{k+1}(n) ≠ ∅`
  (`A₀ ∈ minVelO`) as a hypothesis, which B does not assume (it follows from the splitting of
  the geodesic's own velocity, not in A). B's arbitrary base point `J ∈ Ω_k(n)` is harmless
  (extend the family by `J_k := J`).
* B ⇒ A: B's bounds are on the blind `idxIn`; A's on `formIndex`; and A's algebraic lemmas
  (`IsInterRel.commute_exp`, the Killing-space constructions) have no counterpart in B. -/

end RoundTrip.V15_30
