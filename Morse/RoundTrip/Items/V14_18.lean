import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_18

namespace RoundTrip.V14_18

/-- The project's statement (universes of `ι` instantiated at `0`; `jacSin`, `hadSin`, `suSol`, `suJac`,
`hadKer` are vocabulary). On the project's embedded `SU(n) ⊆ Mₙ(ℂ)` (induced metric), for
`A = T·diag(ia)·Tᴴ` (`T` unitary, `a` real):
* `suSol_ode`: `U_C(t) = T (S(t) ⊙ TᴴCT) Tᴴ` solves `U'' + K_A(U) = 0` (`K_A = jacK A = ¼[[A,·],A]`);
* `isJacobiField_suJac`, `covAlong_suJac_zero`: `J_C(t) = exp(tA/2) U_C(t) exp(tA/2)` is a Jacobi field
  along `t ↦ exp tA` (project's `IsJacobiField`) with `DJ_C/dt(0) = C`, for `A, C ∈ 𝔰𝔲(n)`;
* `conjMultiplicity_su` (Theorem 20.5 for `SU(n)`): for `A ∈ 𝔰𝔲(n)` and `t₀ ∈ [0,1]`, the multiplicity of
  `t₀` as conjugate to `0` along `exp tA|[0,1]` (project's `conjMultiplicity`) is `dim hadKer a t₀`,
  `hadKer a t = {W ∈ 𝔰𝔲(n) | S(t) ⊙ W = 0}`;
* `finrank_hadKer` (the count): for `a = πk` (`k` integer) and `0 < t < 1`, `dim hadKer (πk) t =
  conjMult (suSpectrum k) t`, the number of eigenvalues `π²(k_j − k_l)²/4` (`k_j > k_l`, each twice) having
  `t` as a conjugate parameter. -/
def A : Prop :=
  type_of% @Morse.suSol_ode.{0} ∧ type_of% @Morse.isJacobiField_suJac.{0} ∧
    type_of% @Morse.covAlong_suJac_zero.{0} ∧ type_of% @Morse.conjMultiplicity_su.{0} ∧
    type_of% @Morse.finrank_hadKer.{0}

theorem A_holds : A :=
  ⟨@Morse.suSol_ode, @Morse.isJacobiField_suJac, @Morse.covAlong_suJac_zero,
    @Morse.conjMultiplicity_su, @Morse.finrank_hadKer⟩

/-! Neither direction is proved (see `V14_18.json`).

* `A → B` fails genuinely. Besides the abstract setting (`B` quantifies over every `M` isometric to `SU(n)`
  via `ψ` and every Levi-Civita connection; transport along `ψ` and uniqueness of the Levi-Civita connection
  are not formalized), `B` has content `A` lacks even on the embedded `SU(n)`: (i) the curvature formula
  `dψ(K_V W) = ¼[[A, dψ W], A]` (`A` has `K_A` only as the operator in the ODE `U'' + K_A U = 0`, never as the
  curvature `R(V, W)V`); (ii) Theorem 20.5 for an ARBITRARY eigenbasis `b` of `K_A` on `𝔰𝔲(n)` (`A` only has
  the adapted description `dim hadKer a t`, and only for `t ∈ [0,1]`), with `t > 0` arbitrary (conjugate
  points beyond `t = 1`; `A`'s `conjMultiplicity` lives on `γ|[0,1]`); (iii) for Milnor's `A` and `t ≥ 1`.
  For `t ∈ (0,1)`, (iii) would follow from `conjMultiplicity_su` and `finrank_hadKer` given a Jacobi-field
  dictionary between the blind `conjMultAt` (Jacobi fields on `[0,t]`) and the project's `conjMultiplicity`
  (Jacobi fields on `[0,1]` vanishing at `0` and `t`) and the count identity
  `conjMult (suSpectrum k) t = specMult (milnorSpec k) t` (zero eigenvalues and pairs with `k_j = k_l` never
  contribute); neither is in the project.
* `B → A` fails genuinely: `B` contains no explicit Jacobi fields (`suJac`, `suSol_ode`,
  `covAlong_suJac_zero`), no statement for real (non-integer) `a` or for general index types, and its
  multiplicities are the blind `conjMultAt` of an abstract `M`. -/

end RoundTrip.V14_18
