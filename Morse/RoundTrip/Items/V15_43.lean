import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_43

open Matrix

noncomputable section

namespace RoundTrip.V15_43

/-- The project's statement (no universe parameters), for Milnor's explicit structures
`J_α = bottJ r α` on `ℝ^{16r}` (`I16 × Fin r`), all as bijections of SETS at the base points
`J_8`, `I`:
(1) `bott_chain`: `π_{j+1}(Ω_8(16r), J_8) ≃ π_{j+9}(O(16r), I)` for `2j + 12 ≤ r`;
(2) `bott_chain_of_le`: `π_i(Ω_8(16r), J_8) ≃ π_{i+8}(O(16r), I)` for `2i + 7 ≤ r` (including `i = 0`);
(3) `bott_periodicity_finite`: `π_{j+1}(O(r), I) ≃ π_{j+9}(O(16r), I)` for `2j + 12 ≤ r`;
(4) `bott_periodicity_finite_of_le`: `π_i(O(r), I) ≃ π_{i+8}(O(16r), I)` for `2i + 7 ≤ r`. -/
def A : Prop :=
  type_of% @Morse.bott_chain ∧ type_of% @Morse.bott_chain_of_le ∧
    type_of% @Morse.bott_periodicity_finite ∧ type_of% @Morse.bott_periodicity_finite_of_le

theorem A_holds : A :=
  ⟨@Morse.bott_chain, @Morse.bott_chain_of_le, @Morse.bott_periodicity_finite,
    @Morse.bott_periodicity_finite_of_le⟩

/-! Neither direction is proved (see `V15_43.json`).

* `A → B` fails genuinely. `B` (1) asks for each LINK `π_{i+2}(Ω_j(16r), J_j) ≅ π_{i+1}(Ω_{j+1}(16r), J_{j+1})`
  as a GROUP isomorphism, for EVERY family of eight anticommuting complex structures on `ℝ^{16r}`;
  `A` states only the eight-fold COMPOSITES, as bijections of sets, for Milnor's explicit family. (The
  links exist in the project as set bijections for arbitrary families — `Morse.omega_pi_equiv`,
  `Morse.omega_pi_equiv_two`, `Morse.theorem_24_3`, outside the item — and are induced by continuous
  maps, so their group versions are proof effort — `linkM`, `linkM_two` in `Items/V15_45.lean` do it
  for any family; for `k = 2, 6` the base point `J_{k+1}` has label
  `c = 0` for every family, since `J_{k+2}` anticommutes with `J_k J_{k+1} J_1⋯J_{k−1}`.)
  `B` (2), `Ω_8(16r) ≃ₜ O(r)` for EVERY family, is in neither `A` nor the project, which proves
  `Ω_8(16r) ≅ O(r)` only for the explicit family (`Morse.omegaEightHomeomorph`, item V15_42) via its
  explicit commutant; an arbitrary family needs the isometric uniqueness of the `Cl_8`-module `ℝ^{16r}`
  (conjugacy to `bottJ r`), which the project does not have (Lemma 24.8 there is linear and for
  minimal modules only).
* `B → A` fails genuinely. `B` (1) gives the links only for `r ≥ R(i, j)` with an unspecified `R`, so
  it cannot give `A`'s explicit ranges `2j + 12 ≤ r`, `2i + 7 ≤ r`; and all of `B`'s groups have
  positive index, so `A`'s degree-0 statements (`π_0 Ω_8(16r) ≃ π_8 O(16r)`,
  `π_0 O(r) ≃ π_8 O(16r)`) are not covered at all. -/

end RoundTrip.V15_43
