import Morse
import RoundTrip.Check
import RoundTrip.Blind.V14_28

open Matrix Topology

noncomputable section

namespace RoundTrip.V14_28

/-- The project's statement (no universe parameters), the four theorems as they are:
(1) `π_j(U(m), 1) ≃ π_{j+2}(U(Fin m ⊕ Fin m), 1)` for `j + 1 ≤ 2m` (Milnor's chain, as sets);
(2) periodicity in the stable range, `π_{i−1}(U(m), 1) ≃ π_{i+1}(U(m), 1)` for `1 ≤ i`,
`i + 2 ≤ 2m` (as sets);
(3) `π_{j+1}(U(m), 1) ≃* π_{j+3}(U(Fin m ⊕ Fin m), 1)` for `j + 2 ≤ 2m` (the chain as groups);
(4) `π_{j+1}(U(m), 1) ≃* π_{j+3}(U(m), 1)` for `j + 4 ≤ 2m` (periodicity as groups). -/
def A : Prop :=
  type_of% @Morse.nonempty_equiv_pi_unitary_two_mul ∧
  type_of% @Morse.periodicity_theorem ∧
  type_of% @Morse.nonempty_mulEquiv_pi_unitary_two_mul ∧
  type_of% @Morse.periodicity_theorem_mulEquiv

theorem A_holds : A :=
  ⟨@Morse.nonempty_equiv_pi_unitary_two_mul, @Morse.periodicity_theorem,
    @Morse.nonempty_mulEquiv_pi_unitary_two_mul, @Morse.periodicity_theorem_mulEquiv⟩

/-! ### Glue -/

section Glue

open Morse.Homotopy

/-- Left translation by `g` moves the base point `1` of a topological monoid-group to `g`. -/
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

/-- Stability (Lemma 23.4 of the project, `bijective_homotopyGroupMap_unitaryIncl_complex`,
outside the item): `π_i U(a) ≃ π_i U(a + c)` for `i < 2a`. -/
theorem stab_le {i a c : ℕ} (hi : i < 2 * a) : Nonempty (π_ i (U a) 1 ≃ π_ i (U (a + c)) 1) := by
  have e₁ := Equiv.ofBijective _
    (bijective_homotopyGroupMap_unitaryIncl_complex (m := a) (k := c) (i := i) hi 1)
  rw [show unitaryInclC (𝕜 := ℂ) a c 1 = 1 from map_one (unitaryIncl ℂ (Fin a) (Fin c))] at e₁
  exact ⟨e₁.trans (piEquivOfHomeomorph (sumCongr a c (a + c) rfl) (sumCongr_one _ _ _ _) i)⟩

theorem stab_leM {n a c : ℕ} (hi : n + 1 < 2 * a) :
    Nonempty (π_ (n + 1) (U a) 1 ≃* π_ (n + 1) (U (a + c)) 1) := by
  have e₁ := MulEquiv.ofBijective (homotopyGroupHom (N := Fin (n + 1)) (unitaryInclC (𝕜 := ℂ) a c) 1)
    (bijective_homotopyGroupMap_unitaryIncl_complex (m := a) (k := c) (i := n + 1) hi 1)
  rw [show unitaryInclC (𝕜 := ℂ) a c 1 = 1 from map_one (unitaryIncl ℂ (Fin a) (Fin c))] at e₁
  obtain ⟨e₂⟩ := nonempty_mulEquiv_of_homeomorph (sumCongr a c (a + c) rfl) (sumCongr_one _ _ _ _) n
  exact ⟨e₁.trans e₂⟩

/-- Any two `U(a)`, `U(b)` in the stable range of degree `i` have the same `π_i`. -/
theorem stable {i a b : ℕ} (ha : i < 2 * a) (hb : i < 2 * b) :
    Nonempty (π_ i (U a) 1 ≃ π_ i (U b) 1) := by
  rcases le_total a b with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    exact stab_le ha
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨e⟩ := stab_le (c := c) hb
    exact ⟨e.symm⟩

theorem stableM {n a b : ℕ} (ha : n + 1 < 2 * a) (hb : n + 1 < 2 * b) :
    Nonempty (π_ (n + 1) (U a) 1 ≃* π_ (n + 1) (U b) 1) := by
  rcases le_total a b with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    exact stab_leM ha
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
    obtain ⟨e⟩ := stab_leM (c := c) hb
    exact ⟨e.symm⟩

/-- For an idempotent matrix, `rank = trace` (copied from the glue of item V14_26). -/
theorem rank_eq_trace {k : ℕ} {P : Mat k} (hP : P * P = P) : ((P.rank : ℕ) : ℂ) = P.trace := by
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have h := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
  rw [Matrix.trace_toLin'_eq] at h
  rw [h, Matrix.rank, Matrix.toLin'_apply']

/-- The blind Grassmannian (rank `m`) is the project's (trace `m`). -/
theorem grass_eq (k m : ℕ) : Grass k m = Morse.grassmannian (Fin k) m := by
  ext P
  simp only [Grass, Morse.grassmannian, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by rw [← rank_eq_trace h2, h3]⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [← rank_eq_trace h2] at h3
    exact_mod_cast h3

/-- The blind `G_m(ℂ^k)` is homeomorphic (identically) to the project's. -/
def hG (k m : ℕ) : ↥(Grass k m) ≃ₜ ↥(Morse.grassmannian (Fin k) m) :=
  Homeomorph.setCongr (grass_eq k m)

end Glue

open Morse.Homotopy in
/-- `A ⇒ B`. The `U(m) → U(m')` statements (first, second, and last conjuncts of `B`, and the
composite in the third) come from `A` (1), (3) after reindexing `Fin m ⊕ Fin m ≃ Fin (2m)`,
moving base points by left translation, and stability `π_i U(a) ≃ π_i U(b)` in the stable
range (the project's Lemma 23.4, outside the item) to pass from `U(2m)` to `U(m')`. The individual
links `π_{i−1} U(m) ≅ π_i G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m) ≅ π_{i+1} U(2m)` of `B` are not in `A` (`A`
states only the composites): they are supplied by the project's Lemma 23.4 for the Grassmannian
(`grassmannianPiEquiv`, `nonempty_mulEquiv_grassmannianPi`, item V14_26), Theorem 23.3 as groups
(`Morse.theorem_23_3_mulEquiv`) and `π_j SU ≅ π_j U` (`bijective_homotopyGroupMap_suInclC`, item
V14_27), all outside this item. -/
theorem A_to_B : A → B := by
  rintro ⟨h1, -, h3, -⟩
  -- the composites `U(m) → U(2m)`
  have c1 : ∀ m k, k + 1 ≤ 2 * m → ∀ (g : U m) (g' : U (2 * m)),
      Nonempty (π_ k (U m) g ≃ π_ (k + 2) (U (2 * m)) g') := by
    intro m k hk g g'
    obtain ⟨e⟩ := h1 (m := m) (j := k) hk
    exact ⟨(bc g k).symm.trans (e.trans ((piEquivOfHomeomorph (sumCongr m m (2 * m) (two_mul m).symm)
      (sumCongr_one _ _ _ _) (k + 2)).trans (bc g' (k + 2))))⟩
  have c3 : ∀ m k, k + 2 ≤ 2 * m → ∀ (g : U m) (g' : U (2 * m)),
      Nonempty (π_ (k + 1) (U m) g ≃* π_ (k + 3) (U (2 * m)) g') := by
    intro m k hk g g'
    obtain ⟨e⟩ := h3 (m := m) (j := k) hk
    obtain ⟨b₁⟩ := bcM g k
    obtain ⟨b₂⟩ := bcM g' (k + 2)
    obtain ⟨r⟩ := nonempty_mulEquiv_of_homeomorph (sumCongr m m (2 * m) (two_mul m).symm)
      (sumCongr_one _ _ _ _) (k + 2)
    exact ⟨b₁.symm.trans (e.trans (r.trans b₂))⟩
  have hcard : ∀ m, Fintype.card (Fin (2 * m)) = 2 * m := fun m => Fintype.card_fin _
  refine ⟨fun k m m' hk hk' g g' => ?_, fun k m m' hk hk' g g' => ?_,
    fun m k hk g P h g' => ?_, fun m k hk g P g' => ?_⟩
  · -- periodicity, sets
    obtain ⟨e⟩ := c1 m k hk g 1
    obtain ⟨s⟩ := stable (i := k + 2) (a := 2 * m) (b := m') (by omega) (by omega)
    exact ⟨e.trans (s.trans (bc g' (k + 2)))⟩
  · -- periodicity, groups
    obtain ⟨e⟩ := c3 m k hk g 1
    obtain ⟨s⟩ := stableM (n := k + 2) (a := 2 * m) (b := m') (by omega) (by omega)
    obtain ⟨b⟩ := bcM g' (k + 2)
    exact ⟨e.trans (s.trans b)⟩
  · -- the chain
    have : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
    refine ⟨?_, ?_, ?_, c1 m k hk g g'⟩
    · have e := grassmannianPiEquiv (hcard m) (hG (2 * m) m P) (j := k) hk
      exact ⟨(bc g k).symm.trans (e.symm.trans
        (piEquivOfHomeomorph (hG (2 * m) m) rfl (k + 1)).symm)⟩
    · obtain ⟨e⟩ := Morse.theorem_23_3_mulEquiv (hcard m) (hG (2 * m) m P) (j := k) hk
      obtain ⟨r⟩ := nonempty_mulEquiv_of_homeomorph (hG (2 * m) m) (x := P) rfl k
      obtain ⟨b⟩ := bcM (G := SU (2 * m)) h (k + 1)
      exact ⟨r.trans (e.trans b)⟩
    · have e := MulEquiv.ofBijective (homotopyGroupHom (N := Fin (k + 2))
        (suInclC (Fin (2 * m))) h) (bijective_homotopyGroupMap_suInclC (j := k) h)
      obtain ⟨b₁⟩ := bcM (suInclC (Fin (2 * m)) h) (k + 1)
      obtain ⟨b₂⟩ := bcM g' (k + 1)
      exact ⟨e.trans (b₁.symm.trans b₂)⟩
  · have : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
    refine ⟨?_, c3 m k hk g g'⟩
    obtain ⟨e⟩ := nonempty_mulEquiv_grassmannianPi (hcard m) (hG (2 * m) m P) (j := k) hk
    obtain ⟨r⟩ := nonempty_mulEquiv_of_homeomorph (hG (2 * m) m) (x := P) rfl (k + 1)
    obtain ⟨b⟩ := bcM g k
    exact ⟨b.symm.trans (e.symm.trans r.symm)⟩

/-- `B ⇒ A`: only the first two conjuncts of `B` are needed: `(1)`, `(3)` are `B` at `m' = 2m`
(reindexed to `Fin m ⊕ Fin m`), `(2)`, `(4)` are `B` at `m' = m`, all at the base point `1`. -/
theorem B_to_A : B → A := by
  rintro ⟨hB1, hB2, -, -⟩
  refine ⟨fun {m j} hj => ?_, fun {m i} hi him => ?_, fun {m j} hj => ?_, fun {m j} hj => ?_⟩
  · obtain ⟨e⟩ := hB1 j m (2 * m) hj (by omega) 1 1
    exact ⟨e.trans (Morse.Homotopy.piEquivOfHomeomorph
      (sumCongr m m (2 * m) (two_mul m).symm) (sumCongr_one _ _ _ _) (j + 2)).symm⟩
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact hB1 k m m (by omega) (by omega) 1 1
  · obtain ⟨e⟩ := hB2 j m (2 * m) hj (by omega) 1 1
    obtain ⟨r⟩ := Morse.Homotopy.nonempty_mulEquiv_of_homeomorph
      (sumCongr m m (2 * m) (two_mul m).symm) (sumCongr_one _ _ _ _) (j + 2)
    exact ⟨e.trans r.symm⟩
  · exact hB2 j m m (by omega) (by omega) 1 1

#rt_check RoundTrip.V14_28.A_to_B [Morse.nonempty_equiv_pi_unitary_two_mul, Morse.periodicity_theorem, Morse.nonempty_mulEquiv_pi_unitary_two_mul, Morse.periodicity_theorem_mulEquiv]
#rt_check RoundTrip.V14_28.B_to_A [Morse.nonempty_equiv_pi_unitary_two_mul, Morse.periodicity_theorem, Morse.nonempty_mulEquiv_pi_unitary_two_mul, Morse.periodicity_theorem_mulEquiv]
#rt_overlap RoundTrip.V14_28.B_to_A [Morse.nonempty_equiv_pi_unitary_two_mul, Morse.periodicity_theorem, Morse.nonempty_mulEquiv_pi_unitary_two_mul, Morse.periodicity_theorem_mulEquiv]
#rt_overlap RoundTrip.V14_28.A_to_B [Morse.nonempty_equiv_pi_unitary_two_mul, Morse.periodicity_theorem, Morse.nonempty_mulEquiv_pi_unitary_two_mul, Morse.periodicity_theorem_mulEquiv]

end RoundTrip.V14_28
