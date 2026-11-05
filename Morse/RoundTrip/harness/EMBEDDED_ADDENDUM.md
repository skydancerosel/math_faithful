ADDENDUM for items whose B quantifies over abstract Riemannian manifolds (Milnor §§8–19) — the
"embedded special case".

The project formalizes Riemannian geometry only on slice submanifolds `N ⊆ V` of a Euclidean space
with the induced metric, so A and B are usually incomparable for a reason already known (the
setting). That verdict stays as it is. In addition, test whether *Milnor's statement on embedded
manifolds* matches A:

1. `RoundTrip/Bridge.lean` packages a slice submanifold as a Mathlib Riemannian manifold:
   `Bridge.Sub hN` (the type `↥N`, model `ℝⁿ`, write it `Bridge.Sub`: plain `Sub` clashes with
   Lean's class), the induced metric (`Bridge.metric`, `RiemannianBundle` instance) and the induced
   connection `Bridge.conn` with `Bridge.conn_isLC`. Its dictionary translates the blind vocabulary
   (`RoundTrip.BridgePrelude.*`, the prelude shared by the blind files of §§8–10 — your item's
   blind file has its own copy of the same definitions, which unfold to the same terms) into the
   project's: `hasCovDeriv_iff`, `IsParallel.tangential`, `isGeodesic_iff`,
   `isGeodesic_iff_isGeodesicOn`, `isCurvVal_iff` (vs `RoundTrip.V8_13.IsCurvVal`), `arcLen_eq`,
   `energy_eq`, `eqOn_Icc_of_isGeodesic`, `expDefined_of_mem_expDom`, `expMap_eq`,
   `pathLengths_eq`, `rho_eq`. Read the statements you need (grep `^theorem` in Bridge.lean).
2. Worked example: `RoundTrip/Items/V7_29.lean` and `.json`: `B_emb` := B instantiated at
   `M = Bridge.Sub hN`, `cov = Bridge.conn` (`B_to_B_emb` shows it is a genuine special case);
   then `A_to_B_emb`, and `B_to_A…` for the part of A that B_emb covers, both under `#rt_check`.
3. Missing dictionary lemmas: prove them in your own Items file (in a `namespace Emb` section, as
   V7_29 does), never in Bridge.lean (other agents use it), and list them in your report.
4. JSON: add `"embedded_special_case": "proved|A_to_Bemb_only|Bemb_to_A_only|failed|not_applicable"`
   and `"embedded_special_case_note": "<what B_emb is, which directions were proved, what is
   missing (e.g. the Bridge has only the induced connection, not every Levi-Civita connection on
   ↥N; uniqueness of the Levi-Civita connection is not formalized)>"`.
   Use `not_applicable` when B does not quantify over Riemannian manifolds.

Spend effort on the embedded case in proportion: when B_emb ↔ A needs only dictionary glue, do it;
when it would need new Riemannian geometry, diagnose and stop.

Tips from earlier provers:
- The Riemannian norm/inner product on `TangentSpace` is a `scoped` instance: `open Bundle`; if its
  search times out, pass it by name.
- Your blind file's vocabulary (`IsGeodesic`, `arcLen`, `rho`, `vel`, …) consists of constants
  distinct from `BridgePrelude`'s but definitionally equal: use `show … from rfl` / `exact`, not `rw`.
- Blind geodesics on the closed `[0,1]` ⇒ the project's `expDom` (open interval): proved as
  `RoundTrip.V7_28.Aux.mem_expDom_of_expDefined` in `Items/V7_28.lean` (also `Morse.exists_initial_ray`);
  the same file has glue for changing the model `Z → ℝᵐ` and for connected components. Copy what you
  need into your own file (Items files are not imported by each other).
- The Bridge has no dictionary yet for variations / fields along piecewise smooth paths (§§11–13):
  build what a single item needs in its own file, and say in the report what a shared dictionary
  would have to contain.
- If `#rt_check` fails only because A mentions a project *definition* whose proof fields were proved
  with one of the item's theorems (e.g. `Morse.riemMetricSpace`, `Morse.energyHessian`), use
  `#rt_check_soft` (same syntax): it fails on any other use, and otherwise lists the definitions
  involved. Then make sure your proof does not use those proof fields (e.g. the bilinearity of
  `energyHessian`), and record `"rt_check_soft": "<definitions>"` in the JSON.
- Jacobi fields and conjugate points (§§14–15): `Items/V9_10.lean`, namespace `Emb`, has
  `jacobi_Icc`, `isJacobiField_of_isJacobi` / `isJacobi_of_isJacobiField` (blind `IsJacobi conn γ
  [0,1] J` ⇔ `Morse.IsJacobiField hN (incl∘γ) (ambA γ J)`), `isConj_iff` (blind `IsConj` ⇔
  `Morse.IsConjugate`) and `isGeodesic_lift`. Copy what you need.
- The variational Hessian (§§13–15): `RoundTrip/EnergyC2.lean` (`import RoundTrip.EnergyC2`) proves
  that the energy of a `Morse.IsVariation` is C^∞ in the parameters
  (`Morse.IsVariation.contDiffOn_energy`, `contDiffAt_energy`), that the blind `mixedD` shape is the
  iterated derivative (`fderiv_fderiv_apply_eq_deriv_deriv`), and that
  `fderiv_fderiv_apply_energy_eq_energyHessian` gives exactly the two clauses of a blind `IsHess`
  for a 2-parameter project variation of a geodesic. Read its module docstring first. Lift blind
  variations to `Morse.IsVariation` with the `Emb` dictionary of `Items/V8_9.lean`.
