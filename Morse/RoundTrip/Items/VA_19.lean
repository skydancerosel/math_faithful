import Morse
import RoundTrip.Check
import RoundTrip.Blind.VA_19

/-! # Round trip for VA_19 (Milnor, Appendix p. 150: the topological part of Theorem 17.3)

`A` is the conjunction of the types (universe `0`) of `Morse.isCountableCellComplexType_of_tower`,
`Morse.isCountableCellComplexType_of_sublevel` and `Morse.isCountableCellComplexType_of_sublevel'`:
for ANY space `X` that is the homotopy direct limit of `{X_n}` (resp. any continuous `E : X → ℝ`
with levels `a_n ↗ ∞`, sublevels `X^{a_n}`), homotopy equivalences `g_n : X_n → K_n` to the stages
of a cell tower, compatible up to homotopy (resp. strictly), give
`IsCountableCellComplexType X cells` (`X ≃ₕ` the mapping telescope of the tower).

`B` (abstract complete Riemannian manifold, `p, q` non-conjugate, admissible levels): THERE EXIST a
Hausdorff Mathlib CW complex `Y` with exhausting subcomplexes `K_i` and a strictly commutative
diagram of homotopy equivalences `Ω^{a_i} → K_i`, such that `Ω`, `Y` are the homotopy direct
limits of `{Ω^{a_i}}`, `{K_i}` and the limit map `Ω → Y` is a homotopy equivalence.

* `A ⇒ B` fails genuinely: `A` takes the homotopy equivalences `X^{a_n} → K_n` as hypotheses,
  `B` asserts their existence for `Ω` (Theorems 16.3/17.3 on an abstract manifold); `B` also needs
  Example 2 for Mathlib CW complexes (`Y` is the homotopy direct limit of its subcomplexes), which
  the project does not have (it replaces the union with the weak topology by a mapping telescope).
* `B ⇒ A` only vacuously: `A` is re-proved outright from the non-listed
  `Morse.nonempty_homotopyEquiv_mappingTelescope` and `Morse.isHomotopyDirectLimit_sublevel`
  (the project's own route). -/

namespace RoundTrip.VA_19

open Set Filter CategoryTheory

/-- `A`: the three listed theorems, universe `0`. -/
def A : Prop :=
  (type_of% @Morse.isCountableCellComplexType_of_tower.{0}) ∧
    (type_of% @Morse.isCountableCellComplexType_of_sublevel.{0}) ∧
      (type_of% @Morse.isCountableCellComplexType_of_sublevel'.{0})

section Outright

variable {X : Type} [TopologicalSpace X] {cells : ℕ → List ℕ}

theorem of_tower' {S : ℕ → Set X} (hS : Monotone S) (hX : Morse.IsHomotopyDirectLimit S)
    (T : Morse.CellTower.{0} cells) (g : ∀ n, C(S n, T.K.obj n))
    (hg : ∀ n, Morse.IsHomotopyEquiv (g n))
    (hsq : ∀ n, ((Morse.tmap T.K (Nat.le_add_right n 1)).comp (g n)).Homotopic
      ((g (n + 1)).comp (Morse.up hS n))) :
    Morse.IsCountableCellComplexType X cells :=
  ⟨T, Morse.nonempty_homotopyEquiv_mappingTelescope T.K hS hX g hg hsq⟩

theorem of_sublevel' (E : C(X, ℝ)) {a : ℕ → ℝ} (ha : Monotone a) (ha' : Tendsto a atTop atTop)
    (T : Morse.CellTower.{0} cells) (g : ∀ n, C(Morse.sublevel E (a n), T.K.obj n))
    (hg : ∀ n, Morse.IsHomotopyEquiv (g n))
    (hcompat : ∀ n (x : Morse.sublevel E (a n)), Morse.tmap T.K (Nat.le_add_right n 1) (g n x) =
      g (n + 1) ⟨x, Morse.sublevel_mono E (ha (Nat.le_add_right n 1)) x.2⟩) :
    Morse.IsCountableCellComplexType X cells := by
  have hS : Monotone fun n => Morse.sublevel E (a n) := fun m n h => Morse.sublevel_mono E (ha h)
  refine of_tower' hS (Morse.isHomotopyDirectLimit_sublevel E ha ha') T g hg fun n => ?_
  have : (Morse.tmap T.K (Nat.le_add_right n 1)).comp (g n) = (g (n + 1)).comp (Morse.up hS n) :=
    ContinuousMap.ext fun x => hcompat n x
  rw [this]

theorem A_holds' : A := by
  refine ⟨@fun X _ S cells hS hX T g hg hsq => of_tower' hS hX T g hg hsq,
    @fun X _ cells E a ha ha' T g hg hc => of_sublevel' E ha ha' T g hg hc, ?_⟩
  intro X _ cells E a ha ha' K c h₀ hstep g hg hcompat
  exact of_sublevel' E ha ha' (Morse.CellTower.ofSequence K c h₀ hstep) g hg fun n x => by
    rw [Morse.CellTower.tmap_ofSequence]
    exact hcompat n x

end Outright

/-- `B ⇒ A`: vacuous (`A` holds outright). -/
theorem B_to_A : B → A := fun _ => A_holds'

#rt_check RoundTrip.VA_19.B_to_A [Morse.isCountableCellComplexType_of_tower, Morse.isCountableCellComplexType_of_sublevel, Morse.isCountableCellComplexType_of_sublevel']
#rt_overlap RoundTrip.VA_19.B_to_A [Morse.isCountableCellComplexType_of_tower, Morse.isCountableCellComplexType_of_sublevel, Morse.isCountableCellComplexType_of_sublevel']

end RoundTrip.VA_19
