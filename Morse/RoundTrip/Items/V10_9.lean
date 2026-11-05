import Morse
import RoundTrip.Check
import RoundTrip.Blind.V10_9
import RoundTrip.Bridge

open Set Filter Topology Function
open scoped ContDiff Manifold

namespace RoundTrip.V10_9

/-- The project's statement (universes instantiated at `0`): (1) every tangent vector of a slice
submanifold is the velocity of a smooth curve in it; (2) a smooth curve of break points gives a
variation through broken geodesics; (3) the first variation formula on `B`: for `F` smooth on
`V^m` agreeing with `E'` on `N^m ∩ O ⊆ U`, `dF(w) = −2 Σⱼ ⟨wⱼ, Δ_{tⱼ} γ'⟩`, `γ = B.path y₀`;
(4) Theorem 16.2: `y` is a critical point of `E' = F|(N^m ∩ O)` (`IsCriticalPointM`, slice
submanifold `N^m ∩ O ⊆ V^m`) iff `B.path y` is an unbroken geodesic; (5) every unbroken geodesic
of `Ω` with energy `< c` is the broken geodesic of its break points, which lie in `U`. -/
def A : Prop :=
  type_of% @Morse.exists_curve_of_mem_tangentSubspace.{0,0,0} ∧
    type_of% @Morse.BrokenSetup.exists_variation_path.{0,0,0} ∧
    type_of% @Morse.BrokenSetup.fderiv_eq_jumps.{0,0,0} ∧
    type_of% @Morse.BrokenSetup.isCriticalPointM_iff.{0,0,0} ∧
    type_of% @Morse.BrokenSetup.eqOn_path_nodeVal_of_isUnbrokenGeodesic.{0,0,0}

theorem A_holds : A :=
  ⟨@Morse.exists_curve_of_mem_tangentSubspace, @Morse.BrokenSetup.exists_variation_path,
    @Morse.BrokenSetup.fderiv_eq_jumps, @Morse.BrokenSetup.isCriticalPointM_iff,
    @Morse.BrokenSetup.eqOn_path_nodeVal_of_isUnbrokenGeodesic⟩

/-! Neither direction is proved (see `V10_9.json`).

* `A → B` fails genuinely: B quantifies over abstract connected Hausdorff `ℝⁿ`-manifolds with any
  smooth metric and Levi-Civita connection; A only over slice submanifolds `N ⊆ V`. Also B's
  clause (1) (critical paths of `E` in `Int Ω^c` = unbroken geodesics of length `< √c`) is
  Corollary 12.3, which is not among A's theorems (it is `Morse.corollary_12_3`).
* `B → A` fails genuinely: A's conjuncts (1)–(3) (curves through tangent vectors, the variation
  through broken geodesics, the first variation formula for `E'`) have no counterpart in B; only
  (4) ≈ B's clause (3) and (5) ≈ B's clause (2).

## The embedded special case

`B_emb` (B for `M = ↥N`, induced connection; `B_to_B_emb`). On `↥N`, B's clauses (1)–(2) follow
from project lemmas outside A (`Items/V8_10.lean`: blind `IsCriticalPath Efun` ⇔
`Morse.IsCriticalPath`, blind geodesic on `[0, 1]` ⇔ `IsUnbrokenGeodesic`; then
`Morse.corollary_12_3` and Schwarz `L² ≤ E`). Clause (3) vs A's (4) needs: B's data (`Setup16`)
to give a `Morse.BrokenSetup` — they do not (normal-radius condition, `IsShortJoin`, see
V10_7/V10_8); the blind `E'` (`IsEprime`: any `F` smooth for the product structure
`ModelWithCorners.pi` on `(↥N)^{k−1}` on the image `V` of `B`, agreeing with `E` there) vs A's `F`
(smooth on all of `V^m`, agreeing with `energy'` on a slice submanifold `N^m ∩ O ⊆ U`); and the
blind `mfderiv` on `(↥N)^{k−1}` vs the project's `IsCriticalPointM` on `N^m ∩ O` (two manifold
structures on the same set; no dictionary exists). Note also that B's `F` need not extend
smoothly to `V^m`, so B's clause (3) quantifies over more functions than A's (4). -/

/-- **B on embedded manifolds**: `M = ↥N` (`Bridge.Sub hN`, model `ℝⁿ`, induced metric) with the
induced Levi-Civita connection `Bridge.conn`. -/
def B_emb : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] (n : ℕ)
    (N : Set V) (hN : Milnor.IsSliceSubmanifold 𝓘(ℝ, V) (Rn n) W N)
    [ConnectedSpace (Bridge.Sub hN)], MetricComplete n (Bridge.Sub hN) →
    ∀ (p q : Bridge.Sub hN) (c ε : ℝ) (k : ℕ) (t : ℕ → ℝ),
      Setup16 n (Bridge.conn (hN := hN)) p q c ε k t →
      (∀ w ∈ IntOm n p q c, IsCriticalPath (n := n) (Efun (n := n)) w.1 ↔
          (IsGeodesic (Bridge.conn (hN := hN)) w.1 (Set.Icc 0 1) ∧
            arcLen (n := n) w.1 0 1 < Real.sqrt c)) ∧
      (∀ w ∈ IntOm n p q c, IsCriticalPath (n := n) (Efun (n := n)) w.1 →
          w ∈ Bset n (Bridge.conn (hN := hN)) p q c k t) ∧
      (∀ (F : (Fin (k - 1) → Bridge.Sub hN) → ℝ) (V' : Set (Fin (k - 1) → Bridge.Sub hN)),
        IsEprime n (Bridge.conn (hN := hN)) p q c k t F V' →
        ∀ w ∈ Bset n (Bridge.conn (hN := hN)) p q c k t,
          IsCritPi n (k - 1) F (evalPts k t w.1) ↔
            IsGeodesic (Bridge.conn (hN := hN)) w.1 (Set.Icc 0 1))

theorem B_to_B_emb : B → B_emb := fun hB _ _ _ _ _ _ _ _ n _ hN _ =>
  hB n (Bridge.Sub hN) (Bridge.conn (hN := hN)) Bridge.conn_isLC

end RoundTrip.V10_9
