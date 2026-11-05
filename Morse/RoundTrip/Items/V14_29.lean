import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_29

open Matrix Topology

namespace RoundTrip.V14_29

/-- The project's statement (no universe parameters). `Morse.Homotopy.unitaryOneHomeomorph` is a
definition (a homeomorphism `U(1) ≃ₜ S¹` whose underlying map is `g ↦ det g`); it is read as the
existence of such a homeomorphism, with that formula. The three theorems are taken as they are:
(1) `π_1(S¹, 1) ≃ ℤ` (as sets);
(2) `U(1) ≃ₜ S¹`, `g ↦ det g`;
(3) `π_i(U(m), 1) ≃ π_i(S¹, 1)` for `i < 2`, `m ≥ 1`;
(4) Theorem 23.5: for `j + 1 ≤ 2m`, `π_j(U(m), 1)` is a subsingleton for even `j` and `≃ ℤ` for
odd `j`. -/
def A : Prop :=
  type_of% @Morse.Homotopy.nonempty_pi_one_circle_equiv_int ∧
  (∃ h : ↥(Matrix.unitaryGroup (Fin 1) ℂ) ≃ₜ Circle,
    ∀ g, (h g : ℂ) = (g : Matrix (Fin 1) (Fin 1) ℂ).det) ∧
  type_of% @Morse.Homotopy.nonempty_pi_unitary_equiv_circle ∧
  type_of% @Morse.theorem_23_5

theorem A_holds : A :=
  ⟨Morse.Homotopy.nonempty_pi_one_circle_equiv_int,
    ⟨Morse.Homotopy.unitaryOneHomeomorph, fun _ => rfl⟩,
    @Morse.Homotopy.nonempty_pi_unitary_equiv_circle, @Morse.theorem_23_5⟩

/-! ### Glue -/

section Glue

/-- Left translation by `g` moves the base point `1` of a topological group to `g`. -/
noncomputable def baseChange {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (g : G) (n : ℕ) :
    π_ n G 1 ≃ π_ n G g :=
  Morse.Homotopy.piEquivOfHomeomorph (Homeomorph.mulLeft g) (mul_one g) n

/-- A subsingleton homotopy group is a one-point set. -/
def equivUnitOfSubsingleton {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
    (h : Subsingleton (π_ n X x)) : π_ n X x ≃ Unit where
  toFun _ := ()
  invFun _ := default
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := rfl

theorem det_fin_one' (g : Mat 1) : g.det = g 0 0 := Matrix.det_fin_one g

end Glue

/-- `A ⇒ B`: the homeomorphism is `unitaryOneHomeomorph` (`det` of a `1 × 1` matrix is its
entry); Theorem 23.5 is moved from the base point `1` to `g` by left translation. -/
theorem A_to_B : A → B := by
  rintro ⟨-, ⟨h, hh⟩, -, h235⟩
  refine ⟨⟨h, fun g => by rw [hh, det_fin_one']⟩, fun m j hj g => ?_⟩
  obtain ⟨hev, hodd⟩ := h235 (m := m) (j := j) hj
  refine ⟨fun he => ?_, fun ho => ?_⟩
  · have := hev he
    have : Subsingleton (π_ j (U m) g) := (baseChange g j).symm.subsingleton
    exact ⟨equivUnitOfSubsingleton this⟩
  · obtain ⟨e⟩ := hodd ho
    exact ⟨(baseChange g j).symm.trans e⟩

/-- `B ⇒ A`: `π_1 S¹ ≃ ℤ` and `π_0 S¹ = *` are `B` at `m = 1` transported along `U(1) ≃ₜ S¹`;
the rest is `B` at the base point `1`. -/
theorem B_to_A : B → A := by
  rintro ⟨⟨h, hh⟩, hB⟩
  -- `π_1(S¹, 1) ≃ ℤ` and `π_0(S¹, 1) ≃ *` from `U(1)`
  have hc : ∀ i, π_ i (U 1) (h.symm 1) ≃ π_ i Circle 1 := fun i =>
    Morse.Homotopy.piEquivOfHomeomorph h (h.apply_symm_apply 1) i
  have hZ : Nonempty (π_ 1 Circle 1 ≃ ℤ) := by
    obtain ⟨e⟩ := (hB 1 1 (by norm_num) (h.symm 1)).2 (by decide)
    exact ⟨(hc 1).symm.trans e⟩
  have h0 : Nonempty (π_ 0 Circle 1 ≃ Unit) := by
    obtain ⟨e⟩ := (hB 1 0 (by norm_num) (h.symm 1)).1 (by decide)
    exact ⟨(hc 0).symm.trans e⟩
  refine ⟨hZ, ⟨h, fun g => by rw [hh, det_fin_one']⟩, fun {m i} hm hi => ?_, fun {m j} hj => ?_⟩
  · interval_cases i
    · obtain ⟨e⟩ := (hB m 0 (by omega) 1).1 (by decide)
      obtain ⟨e'⟩ := h0
      exact ⟨e.trans e'.symm⟩
    · obtain ⟨e⟩ := (hB m 1 (by omega) 1).2 (by decide)
      obtain ⟨e'⟩ := hZ
      exact ⟨e.trans e'.symm⟩
  · obtain ⟨hev, hodd⟩ := hB m j hj 1
    refine ⟨fun he => ?_, fun ho => hodd ho⟩
    obtain ⟨e⟩ := hev he
    exact e.subsingleton

#rt_check RoundTrip.V14_29.A_to_B [Morse.Homotopy.nonempty_pi_one_circle_equiv_int, Morse.Homotopy.unitaryOneHomeomorph, Morse.Homotopy.nonempty_pi_unitary_equiv_circle, Morse.theorem_23_5]
#rt_check RoundTrip.V14_29.B_to_A [Morse.Homotopy.nonempty_pi_one_circle_equiv_int, Morse.Homotopy.unitaryOneHomeomorph, Morse.Homotopy.nonempty_pi_unitary_equiv_circle, Morse.theorem_23_5]
#rt_overlap RoundTrip.V14_29.B_to_A [Morse.Homotopy.nonempty_pi_one_circle_equiv_int, Morse.Homotopy.unitaryOneHomeomorph, Morse.Homotopy.nonempty_pi_unitary_equiv_circle, Morse.theorem_23_5]
#rt_overlap RoundTrip.V14_29.A_to_B [Morse.Homotopy.nonempty_pi_one_circle_equiv_int, Morse.Homotopy.unitaryOneHomeomorph, Morse.Homotopy.nonempty_pi_unitary_equiv_circle, Morse.theorem_23_5]

end RoundTrip.V14_29
