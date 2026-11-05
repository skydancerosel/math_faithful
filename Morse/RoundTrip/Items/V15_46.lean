import Morse
import RoundTrip.Check
import RoundTrip.Blind.V15_46

open Matrix Topology

noncomputable section

namespace RoundTrip.V15_46

/-- The project's statement (no universe parameters): for `i < 2n` and `i + 2 < 2n'`,
`π_i(U(n), I) ≃ π_{i+2}(U(n'), I)` — as sets, at the base point `I`. -/
def A : Prop := type_of% @Morse.periodicity_theorem_stable

theorem A_holds : A := @Morse.periodicity_theorem_stable

/-! ### Glue (copied from `Items/V14_28.lean`) -/

section Glue

open Morse.Homotopy

/-- Left translation by `g` moves the base point `1` of a topological group to `g`. -/
def bc {G : Type} [TopologicalSpace G] [Group G] [ContinuousMul G] (g : G) (n : ℕ) :
    π_ n G 1 ≃ π_ n G g :=
  piEquivOfHomeomorph (Homeomorph.mulLeft g) (mul_one g) n

/-- The same as groups. -/
theorem bcM {G : Type} [TopologicalSpace G] [Group G] [ContinuousMul G] (g : G) (n : ℕ) :
    Nonempty (π_ (n + 1) G 1 ≃* π_ (n + 1) G g) :=
  nonempty_mulEquiv_of_homeomorph (Homeomorph.mulLeft g) (mul_one g) n

/-- `U(Fin a ⊕ Fin b) ≃ₜ U(c)` for `a + b = c` (reindexing). -/
def sumCongr (a b c : ℕ) (h : a + b = c) :
    ↥(Matrix.unitaryGroup (Fin a ⊕ Fin b) ℂ) ≃ₜ U c :=
  unitaryCongr (finSumFinEquiv.trans (finCongr h))

theorem sumCongr_one (a b c : ℕ) (h : a + b = c) : sumCongr a b c h 1 = 1 :=
  Subtype.ext (by
    simp only [sumCongr, coe_unitaryCongr, Matrix.reindex_apply]
    exact Matrix.submatrix_one_equiv _)

/-- Stability as groups (the project's Lemma 23.4, `bijective_homotopyGroupMap_unitaryIncl_complex`,
outside the item): `π_{n+1} U(a) ≃* π_{n+1} U(a + c)` for `n + 1 < 2a`. -/
theorem stab_leM {n a c : ℕ} (hi : n + 1 < 2 * a) :
    Nonempty (π_ (n + 1) (U a) 1 ≃* π_ (n + 1) (U (a + c)) 1) := by
  have e₁ := MulEquiv.ofBijective (homotopyGroupHom (N := Fin (n + 1)) (unitaryInclC (𝕜 := ℂ) a c) 1)
    (bijective_homotopyGroupMap_unitaryIncl_complex (m := a) (k := c) (i := n + 1) hi 1)
  rw [show unitaryInclC (𝕜 := ℂ) a c 1 = 1 from map_one (unitaryIncl ℂ (Fin a) (Fin c))] at e₁
  obtain ⟨e₂⟩ := nonempty_mulEquiv_of_homeomorph (sumCongr a c (a + c) rfl) (sumCongr_one _ _ _ _) n
  exact ⟨e₁.trans e₂⟩

theorem stableM {n a b : ℕ} (ha : n + 1 < 2 * a) (hb : n + 1 < 2 * b) :
    Nonempty (π_ (n + 1) (U a) 1 ≃* π_ (n + 1) (U b) 1) := by
  rcases le_total a b with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    exact stab_leM ha
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨e⟩ := stab_leM (c := c) hb
    exact ⟨e.symm⟩

end Glue

open Morse.Homotopy in
/-- `A ⇒ B`. The first conjunct of `B` (sets, all base points) is `A` after moving the base
points by left translation. The second conjunct (group isomorphisms) is NOT in `A`, which is a
bijection of sets only: it is supplied by the project's group-level chain
`Morse.nonempty_mulEquiv_pi_unitary_two_mul` (item V14_28, outside this item), reindexing
`Fin m ⊕ Fin m ≃ Fin 2m`, stability as groups (`stableM`) and left translation. -/
theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun k m m' hk hk' g g' => ?_, fun k m m' hk hk' g g' => ?_⟩
  · obtain ⟨e⟩ := hA (i := k) (n := m) (n' := m') (by omega) (by omega)
    exact ⟨(bc g k).symm.trans (e.trans (bc g' (k + 2)))⟩
  · obtain ⟨e⟩ := Morse.nonempty_mulEquiv_pi_unitary_two_mul (m := m) (j := k) hk
    obtain ⟨r⟩ := nonempty_mulEquiv_of_homeomorph (sumCongr m m (2 * m) (two_mul m).symm)
      (sumCongr_one _ _ _ _) (k + 2)
    obtain ⟨s⟩ := stableM (n := k + 2) (a := 2 * m) (b := m') (by omega) (by omega)
    obtain ⟨b₁⟩ := bcM g k
    obtain ⟨b₂⟩ := bcM g' (k + 2)
    exact ⟨b₁.symm.trans (e.trans (r.trans (s.trans b₂)))⟩

/-- `B ⇒ A`: `B`'s first conjunct at the base points `1`. -/
theorem B_to_A : B → A := by
  rintro ⟨hB1, -⟩ i n n' hn hn'
  exact hB1 i n n' (by omega) (by omega) 1 1

#rt_check RoundTrip.V15_46.A_to_B [Morse.periodicity_theorem_stable]
#rt_check RoundTrip.V15_46.B_to_A [Morse.periodicity_theorem_stable]
#rt_overlap RoundTrip.V15_46.B_to_A [Morse.periodicity_theorem_stable]
#rt_overlap RoundTrip.V15_46.A_to_B [Morse.periodicity_theorem_stable]

end RoundTrip.V15_46
