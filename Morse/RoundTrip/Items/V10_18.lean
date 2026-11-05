import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_18
import RoundTrip.Bridge

open Set Filter Topology Function
open scoped ContDiff Manifold unitInterval

namespace RoundTrip.V10_18

/-- The project's statement (universes instantiated at `0`): for a system of minimal joins
`J : JoinSystem N` (`N ⊆ V` any set for `isOpen_YSet`, a slice submanifold for the other two):
* `isOpen_YSet`: the set `Y_k ⊆ Ω*` of continuous paths whose DYADIC pieces of level `k`
  (`[j/2^k, (j+1)/2^k]`) lie in good sets is open;
* `continuous_brokenΩ`: the dyadic broken geodesic `Y_k → X_k = i⁻¹(Y_k) ⊆ Ω` (vertices at the
  FIXED dyadic times `j/2^k`) is continuous for Milnor's metric `d`;
* `isHomotopyEquiv_toY`: the inclusion `X_k → Y_k` is a homotopy equivalence.
`YSet`, `broken`, `interp` are vocabulary. -/
def A : Prop :=
  type_of% @Morse.JoinSystem.isOpen_YSet.{0} ∧
    type_of% @Morse.JoinSystem.continuous_brokenΩ.{0,0,0} ∧
    type_of% @Morse.JoinSystem.isHomotopyEquiv_toY.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.JoinSystem.isOpen_YSet, @Morse.JoinSystem.continuous_brokenΩ,
    @Morse.JoinSystem.isHomotopyEquiv_toY⟩

/-! Neither `A → B` nor `B → A` is proved; see `V10_18.json`.

B (Milnor's Lemma 17.C as he states it) asks, on every abstract Riemannian manifold with its
Levi-Civita connection, for a continuous `A : Ω* → (0,1]` and a CONTINUOUS `h : Ω* → Ω` (`d`-topology)
with `h(ω)` the broken minimal geodesic through `ω(0), ω(A), …, ω(⌊1/A⌋A), ω(1)`, and
`h ∘ i ≃ id`, `i ∘ h ≃ id`. This is believed FALSE (not formalized): on the round circle
(`p = q`), on a path component `C` of `Ω*` the function `A` takes values arbitrarily close to `0`
(paths winding back and forth around the circle in short time), so composing with
`Φ(ω) = ω · c` (`c` a fixed null-homotopic loop at `q` approaching `q` like `(1 − s)^{1/4}`)
there is `ω*` with `A(ω*) = 1/k` that is a limit of `ω_j` with `A(ω_j) ↑ 1/k`; then `h(ω_j)`
has a last segment on `[kA(ω_j), 1]` of length `→ 0` joining `ω_j(kA(ω_j))` to `q`, of energy
`≥ ρ²/(1 − kA) → ∞`, while `E` is `d`-continuous: `h` is not continuous at `ω*`. The project
(Morse/Chapter10/FullPathTheorem.lean, "h is not continuous for d") uses instead FIXED dyadic
subdivisions on the open sets `Y_k` (A's content), glued by Theorem A of the Appendix. A ⇒ B
fails genuinely (B is stronger than true; setting); B ⇒ A fails (B has no `Y_k`, no join systems,
and is about abstract manifolds). -/

/-- B on embedded manifolds: `M = ↥N` with the induced connection `Bridge.conn`. Also believed
false: the counterexample above is embedded (the unit circle in `ℝ²`). -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)],
    ∀ (p q : Bridge.Sub hN) (i : C(Om n p q, OmStar p q)), NatMap n i →
      ∃ A : OmStar p q → ℝ, Continuous A ∧ ∃ g : C(OmStar p q, Om n p q),
        IsBrokenInterp n (Bridge.conn (hN := hN)) A g ∧
        (g.comp i).Homotopic (ContinuousMap.id _) ∧ (i.comp g).Homotopic (ContinuousMap.id _)

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V10_18
