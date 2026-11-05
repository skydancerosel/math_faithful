import Morse.Chapter14.MinimalRetract
import Morse.Homotopy.BundlesUnitary

/-!
Milnor, *Morse Theory*, §23, Theorem 23.3, the periodicity theorem and Theorem 23.5
(pp. 128–130); Exposition/Chapter14.md, §§2–3.

# Bott periodicity for the unitary groups

## Milnor's text, paraphrased

* **Theorem 23.3 (Bott)** (p. 128): the inclusion `G_m(ℂ^{2m}) → Ω(SU(2m); I, −I)` induces
  isomorphisms of homotopy groups in dimensions `≤ 2m`; hence `π_i G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m)`
  for `0 ≤ i ≤ 2m`.
* **Periodicity theorem** (p. 129): `π_{i−1} U ≅ π_{i+1} U` for the stable groups, via
  `π_{i−1} U(m) ≅ π_i G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m) ≅ π_{i+1} U(2m)` (Lemma 23.4, Theorem 23.3,
  Lemma 23.4) and stability.
* **Theorem 23.5 (Bott)** (p. 130): `π_0 U ≅ π_2 U ≅ ⋯ = 0` and `π_1 U ≅ π_3 U ≅ ⋯ ≅ ℤ`, from
  `U(1) = S¹`.

## What is formalized

* `Morse.theorem_23_3`: **Theorem 23.3**, `π_i(G_m(ℂ^{2m}), P) ≃ π_{i+1}(SU(2m), I)` for
  `i ≤ 2m` and every `P` (Milnor's `G_m(ℂ^{2m})` is `Morse.grassmannian ι m`, `|ι| = 2m`), from
  Lemma 23.1 (`Morse.lemma_23_1`), its path-space form (`Morse.minPathsHomotopyEquiv`) and the
  unconditional Corollary 22.2 for `SU(2m)` (`Morse.corollary_22_2_su'`).
* `Morse.nonempty_equiv_pi_unitary_two_mul`: `π_{i−1} U(m) ≃ π_{i+1} U(2m)` for `1 ≤ i ≤ 2m`;
  `Morse.periodicity_theorem`: **`π_{i−1} U(m) ≃ π_{i+1} U(m)` for `1 ≤ i ≤ 2m − 2`** (the
  stable range, `i + 1 < 2m`).
* `Morse.theorem_23_5`: **for `j ≤ 2m − 1`, `π_j U(m) = 0` if `j` is even and `π_j U(m) ≃ ℤ` if
  `j` is odd**, by induction from `π_0 U(m) = 0`, `π_1 U(m) ≃ π_1 S¹ ≃ ℤ`
  (`Morse.Homotopy.nonempty_pi_unitary_equiv_circle`: stability from `U(1) ≅ S¹`,
  `Morse.Homotopy.unitaryOneHomeomorph`; `Morse.Homotopy.nonempty_pi_one_circle_equiv_int`: the
  exact sequence of the covering `ℤ → ℝ → S¹`).

All isomorphisms are bijections of pointed sets; the group isomorphisms (in the degrees where
both sides are groups) are in `Morse/Chapter14/PeriodicityGroups.lean`.

## What Milnor leaves implicit

* **Groups versus sets.** Theorem 22.1 is proved here as a compression statement, which gives
  bijections `π_i(Ω^d) → π_i(Ω)` (`Morse.theorem_22_1_bijective`); the isomorphisms of Theorem
  23.3 and of the periodicity theorem are therefore stated as bijections (as is the loop-space
  step `π_i Ω ≅ π_{i+1} M` of Corollary 22.2).
* **`π_1 S¹ ≅ ℤ`** is quoted by Milnor; here it is the boundary map of the covering `t ↦ e^{it}`
  (`π_1 ℝ = π_0 ℝ = 0`, the fibre is discrete), and `π_0` of a discrete space is the space.
* **The stable range.** Milnor's "for `i ≤ 2m`" in the chain gives `π_{i−1} U(m) ≅ π_{i+1} U(2m)`;
  to land back in `U(m)` stability needs `i + 1 < 2m`.  Both are recorded.
-/

open Matrix Set Function Topology
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}

/-- **Theorem 23.3 (Bott)** (Milnor pp. 128–129): `π_i G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m)` for
`0 ≤ i ≤ 2m`, at any point `P` of the Grassmannian. -/
theorem theorem_23_3 (hcard : Fintype.card ι = 2 * m) (P : grassmannian ι m) {i : ℕ}
    (hi : i ≤ 2 * m) :
    Nonempty (π_ i (grassmannian ι m) P ≃
      π_ (i + 1) (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))
        ⟨1, (specialUnitaryGroup ι ℂ).one_mem⟩) := by
  obtain ⟨e⟩ := corollary_22_2_su' hcard hi
    (minVelToPaths hcard ((lemma_23_1 hcard).symm P))
  exact ⟨(Homotopy.piEquivOfHomeomorph (lemma_23_1 hcard).symm rfl i).trans
    ((Homotopy.homotopyGroupEquivOfHomotopyEquiv (minPathsHomotopyEquiv hcard) _).trans e)⟩

omit [Nonempty ι] in
theorem card_sum_fin (m : ℕ) : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
  rw [Fintype.card_sum, Fintype.card_fin]
  ring

/-- **Milnor's chain** (p. 129): `π_{i−1} U(m) ≅ π_i G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m) ≅ π_{i+1} U(2m)`
for `1 ≤ i ≤ 2m` (written `i = j + 1`), by Lemma 23.4, Theorem 23.3 and Lemma 23.4 again. -/
theorem nonempty_equiv_pi_unitary_two_mul {j : ℕ} (hj : j + 1 ≤ 2 * m) :
    Nonempty (π_ j (unitaryGroup (Fin m) ℂ) 1 ≃ π_ (j + 2) (unitaryGroup (Fin m ⊕ Fin m) ℂ) 1) := by
  have : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hcard := card_sum_fin m
  set P := lemma_23_1 hcard ⟨_, suDiag_kHalf_mem_minVel hcard⟩
  obtain ⟨e₂⟩ := theorem_23_3 hcard P (i := j + 1) (by omega)
  have e₃ := Equiv.ofBijective _ (Homotopy.bijective_homotopyGroupMap_suInclC (j := j)
    (⟨1, (specialUnitaryGroup (Fin m ⊕ Fin m) ℂ).one_mem⟩ :
      specialUnitaryGroup (Fin m ⊕ Fin m) ℂ))
  exact ⟨(Homotopy.grassmannianPiEquiv hcard P hj).symm.trans (e₂.trans e₃)⟩

/-- **The periodicity theorem** (Milnor p. 129): `π_{i−1} U(m) ≅ π_{i+1} U(m)` for
`1 ≤ i ≤ 2m − 2`, i.e. in the stable range (`i + 1 < 2m`). -/
theorem periodicity_theorem {i : ℕ} (hi : 1 ≤ i) (him : i + 2 ≤ 2 * m) :
    Nonempty (π_ (i - 1) (unitaryGroup (Fin m) ℂ) 1 ≃ π_ (i + 1) (unitaryGroup (Fin m) ℂ) 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  obtain ⟨e⟩ := nonempty_equiv_pi_unitary_two_mul (m := m) (j := j) (by omega)
  have hs := Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex (m := m) (k := m)
    (i := j + 2) (by omega) 1
  have h1 : Homotopy.unitaryInclC (𝕜 := ℂ) m m 1 = 1 :=
    map_one (Homotopy.unitaryIncl ℂ (Fin m) (Fin m))
  have e' := Equiv.ofBijective _ hs
  rw [h1] at e'
  exact ⟨e.trans e'.symm⟩

/-! ### The values: Theorem 23.5 -/

namespace Homotopy

/-- `π₀` of a discrete space is the space itself. -/
def zerothHomotopyEquivOfDiscrete (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    ZerothHomotopy X ≃ X where
  toFun := Quotient.lift id fun a b (h : Joined a b) => by
    obtain ⟨γ⟩ := h
    exact (isConnected_range γ.continuous).isPreconnected.subsingleton ⟨0, γ.source⟩
      ⟨1, γ.target⟩
  invFun := ZerothHomotopy.mk
  left_inv q := Quotient.inductionOn q fun _ => rfl
  right_inv _ := rfl

/-- `π₀` of a path-connected space is trivial. -/
theorem subsingleton_pi_zero {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Subsingleton (π_ 0 X x) :=
  have : Subsingleton (ZerothHomotopy X) := ⟨fun a b => Quotient.inductionOn₂ a b fun a b =>
    Quotient.sound (PathConnectedSpace.joined a b)⟩
  HomotopyGroup.pi0EquivZerothHomotopy.subsingleton

/-- **`π₁(S¹) ≅ ℤ`** (as sets), from the exact sequence of the covering `ℤ → ℝ → S¹`,
`t ↦ e^{it}`: `∂ : π₁(S¹) → π₀(ℤ) = ℤ` is bijective since `ℝ` is contractible. -/
theorem nonempty_pi_one_circle_equiv_int : Nonempty (π_ 1 Circle 1 ≃ ℤ) := by
  have hp := isLocallyTrivial_circleExp.isSerreFibration (p := Circle.exp)
  obtain ⟨h⟩ := isLocallyTrivial_circleExp.nonempty_homeomorph_fiber (Circle.exp 0)
  have : DiscreteTopology (fiber Circle.exp 0) := h.isEmbedding.discreteTopology
  have e₁ := boundaryEquivPi hp 0 (k := 1)
    (fun _ _ => subsingleton_homotopyGroup_of_contractible _) (j := 0) le_rfl
  rw [Circle.exp_zero] at e₁
  exact ⟨e₁.trans (HomotopyGroup.pi0EquivZerothHomotopy.trans
    ((zerothHomotopyEquivOfDiscrete _).trans h.toEquiv))⟩

/-- **`U(1) ≅ S¹`**, `g ↦ det g`. -/
def unitaryOneHomeomorph : unitaryGroup (Fin 1) ℂ ≃ₜ Circle where
  toFun := detCircle (Fin 1)
  invFun := diagCircle 0
  left_inv g := Subtype.ext (by
    ext i j
    fin_cases i; fin_cases j
    simp [diagCircle, Matrix.det_unique])
  right_inv z := Circle.ext (by rw [coe_detCircle, det_diagCircle])
  continuous_toFun := (detCircle _).continuous
  continuous_invFun := continuous_diagCircle 0

theorem unitaryOneHomeomorph_one : unitaryOneHomeomorph 1 = 1 :=
  Circle.ext (by simp [unitaryOneHomeomorph])

/-- **`π_i U(m) ≅ π_i S¹` for `i ≤ 1`, `m ≥ 1`** (stability from `U(1) = S¹`). -/
theorem nonempty_pi_unitary_equiv_circle {m i : ℕ} (hm : 1 ≤ m) (hi : i < 2) :
    Nonempty (π_ i (unitaryGroup (Fin m) ℂ) 1 ≃ π_ i Circle 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 1 + k := ⟨m - 1, by omega⟩
  have e₁ := Equiv.ofBijective _
    (bijective_homotopyGroupMap_unitaryIncl_complex (m := 1) (k := k) (i := i) (by omega) 1)
  rw [show unitaryInclC (𝕜 := ℂ) 1 k 1 = 1 from map_one (unitaryIncl ℂ (Fin 1) (Fin k))] at e₁
  have e₂ := piEquivOfHomeomorph (unitaryCongr (𝕜 := ℂ) (finSumFinEquiv (m := 1) (n := k)))
    (x := 1) (y := 1) (Subtype.ext (by simp [unitaryCongr])) i
  have e₃ := piEquivOfHomeomorph unitaryOneHomeomorph unitaryOneHomeomorph_one i
  exact ⟨e₂.symm.trans (e₁.symm.trans e₃)⟩

end Homotopy

/-- **Theorem 23.5 (Bott)** (Milnor p. 130): in the stable range `j ≤ 2m − 1`, `π_j U(m) = 0` for
even `j` and `π_j U(m) ≅ ℤ` for odd `j` (as sets; the base case is `U(1) = S¹`). -/
theorem theorem_23_5 {m j : ℕ} (hj : j + 1 ≤ 2 * m) :
    (Even j → Subsingleton (π_ j (unitaryGroup (Fin m) ℂ) 1)) ∧
      (Odd j → Nonempty (π_ j (unitaryGroup (Fin m) ℂ) 1 ≃ ℤ)) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  match j, ih, hj with
  | 0, _, hj =>
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    obtain ⟨e⟩ := Homotopy.nonempty_pi_unitary_equiv_circle (m := m) (i := 0) (by omega)
      (by omega)
    have := Homotopy.subsingleton_pi_zero (1 : Circle)
    exact e.subsingleton
  | 1, _, hj =>
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    obtain ⟨e⟩ := Homotopy.nonempty_pi_unitary_equiv_circle (m := m) (i := 1) (by omega)
      (by omega)
    obtain ⟨e'⟩ := Homotopy.nonempty_pi_one_circle_equiv_int
    exact ⟨e.trans e'⟩
  | j + 2, ih, hj =>
    obtain ⟨e⟩ := periodicity_theorem (m := m) (i := j + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at e
    obtain ⟨h1, h2⟩ := ih j (by omega) (by omega)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := h1 (by obtain ⟨r, hr⟩ := h; exact ⟨r - 1, by omega⟩)
      exact e.symm.subsingleton
    · obtain ⟨e'⟩ := h2 (by obtain ⟨r, hr⟩ := h; exact ⟨r - 1, by omega⟩)
      exact ⟨e.symm.trans e'⟩

end Morse
