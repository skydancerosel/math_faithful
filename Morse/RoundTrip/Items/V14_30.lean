import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_30

open Matrix Topology

namespace RoundTrip.V14_30

/-- The project's statement (no universe parameters). `Morse.Homotopy.piOneCircleMulEquiv` is a
definition (a group isomorphism `π_1(S¹, 1) ≃* Multiplicative ℤ`); it is read as the `Nonempty` of
its type. The four theorems are taken as they are:
(1) `π_1(S¹, 1) ≃* Multiplicative ℤ`;
(2) `π_1(U(m), 1) ≃* π_1(S¹, 1)` for `m ≥ 1`;
(3) Theorem 23.5, odd degrees: `π_{2k+1}(U(m), 1) ≃* Multiplicative ℤ` for `2k + 2 ≤ 2m`;
(4) `π_{2k+1}(U(m), 1) ≃* π_1(U(m), 1)` for `2k + 2 ≤ 2m`;
(5) `π_{2k+2}(U(m), 1) ≃* π_2(U(m), 1)` for `2k + 3 ≤ 2m`. -/
def A : Prop :=
  Nonempty (π_ 1 Circle 1 ≃* Multiplicative ℤ) ∧
  type_of% @Morse.Homotopy.nonempty_mulEquiv_pi_one_unitary_circle ∧
  type_of% @Morse.theorem_23_5_mulEquiv ∧
  type_of% @Morse.nonempty_mulEquiv_pi_unitary_odd ∧
  type_of% @Morse.nonempty_mulEquiv_pi_unitary_even

theorem A_holds : A :=
  ⟨⟨Morse.Homotopy.piOneCircleMulEquiv⟩, @Morse.Homotopy.nonempty_mulEquiv_pi_one_unitary_circle,
    @Morse.theorem_23_5_mulEquiv, @Morse.nonempty_mulEquiv_pi_unitary_odd,
    @Morse.nonempty_mulEquiv_pi_unitary_even⟩

/-! ### Glue -/

section Glue

/-- Left translation by `g` moves the base point `1` of a topological group to `g`, as groups. -/
theorem baseChange {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (g : G)
    (n : ℕ) : Nonempty (π_ (n + 1) G 1 ≃* π_ (n + 1) G g) :=
  Morse.Homotopy.nonempty_mulEquiv_of_homeomorph (Homeomorph.mulLeft g) (mul_one g) n

end Glue

/-- `A ⇒ B`: (1) and (3), moved from the base point `1` to any base point by left translation
(in `S¹` and in `U(m)`). -/
theorem A_to_B : A → B := by
  rintro ⟨⟨e1⟩, -, h3, -, -⟩
  refine ⟨fun x => ?_, fun m k hk g => ?_⟩
  · obtain ⟨b⟩ := baseChange x 0
    exact ⟨b.symm.trans e1⟩
  · obtain ⟨e⟩ := h3 (m := m) (k := k) hk
    obtain ⟨b⟩ := baseChange g (2 * k)
    exact ⟨b.symm.trans e⟩

/-- `B ⇒ A`. (1)–(4) are `B` at the base point `1` (with `k = 0` for `π_1`). (5), the even
degrees, is not in `B` (`B` only speaks of odd degrees): it is re-proved outright, by induction
with the project's periodicity theorem as groups (`Morse.periodicity_theorem_mulEquiv`, item
V14_28), without using `B`. -/
theorem B_to_A : B → A := by
  rintro ⟨hc, hU⟩
  have h1 : ∀ m, 1 ≤ m → Nonempty (π_ 1 (U m) 1 ≃* Multiplicative ℤ) := fun m hm =>
    hU m 0 (by omega) 1
  refine ⟨hc 1, fun {m} hm => ?_, fun {m k} hk => hU m k hk 1, fun {m k} hk => ?_,
    fun {m k} hk => ?_⟩
  · obtain ⟨e⟩ := h1 m hm
    obtain ⟨e'⟩ := hc 1
    exact ⟨e.trans e'.symm⟩
  · obtain ⟨e⟩ := hU m k hk 1
    obtain ⟨e'⟩ := h1 m (by omega)
    exact ⟨e.trans e'.symm⟩
  · -- outright (not from `B`)
    induction k with
    | zero => exact ⟨MulEquiv.refl _⟩
    | succ k ih =>
      obtain ⟨e⟩ := ih (by omega)
      obtain ⟨e'⟩ := Morse.periodicity_theorem_mulEquiv (m := m) (j := 2 * k + 1) (by omega)
      exact ⟨e'.symm.trans e⟩

#rt_check RoundTrip.V14_30.A_to_B [Morse.Homotopy.piOneCircleMulEquiv, Morse.Homotopy.nonempty_mulEquiv_pi_one_unitary_circle, Morse.theorem_23_5_mulEquiv, Morse.nonempty_mulEquiv_pi_unitary_odd, Morse.nonempty_mulEquiv_pi_unitary_even]
#rt_check RoundTrip.V14_30.B_to_A [Morse.Homotopy.piOneCircleMulEquiv, Morse.Homotopy.nonempty_mulEquiv_pi_one_unitary_circle, Morse.theorem_23_5_mulEquiv, Morse.nonempty_mulEquiv_pi_unitary_odd, Morse.nonempty_mulEquiv_pi_unitary_even]
#rt_overlap RoundTrip.V14_30.B_to_A [Morse.Homotopy.piOneCircleMulEquiv, Morse.Homotopy.nonempty_mulEquiv_pi_one_unitary_circle, Morse.theorem_23_5_mulEquiv, Morse.nonempty_mulEquiv_pi_unitary_odd, Morse.nonempty_mulEquiv_pi_unitary_even]
#rt_overlap RoundTrip.V14_30.A_to_B [Morse.Homotopy.piOneCircleMulEquiv, Morse.Homotopy.nonempty_mulEquiv_pi_one_unitary_circle, Morse.theorem_23_5_mulEquiv, Morse.nonempty_mulEquiv_pi_unitary_odd, Morse.nonempty_mulEquiv_pi_unitary_even]

end RoundTrip.V14_30
