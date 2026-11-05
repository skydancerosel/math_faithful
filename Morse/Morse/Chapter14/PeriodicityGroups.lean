import Morse.Chapter14.Periodicity
import Morse.Chapter13.CorollaryGroups

/-!
Milnor, *Morse Theory*, §23, Theorem 23.3, the periodicity theorem and Theorem 23.5
(pp. 128–130), as isomorphisms of groups; Exposition/Chapter14.md, §§2–3.

# Bott periodicity for the unitary groups, as groups

## Milnor's text, paraphrased

(p. 128) **Theorem 23.3**: `π_i G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m)` for `i ≤ 2m`.  (p. 129) **The
periodicity theorem**: `π_{i−1} U ≅ π_{i+1} U`.  (p. 130) **Theorem 23.5**: `π_i U` is `0` for even
`i` and `ℤ` for odd `i`.  Milnor's isomorphisms are of groups.

## What is formalized

`Morse/Chapter14/Periodicity.lean` gives these as bijections; here they are group isomorphisms in
every degree where both sides are groups:

* `Morse.corollary_22_2_su_mulEquiv`: `π_i(Ω^d(SU(2m); I, −I), γ) ≃* π_{i+1} SU(2m)` for
  `1 ≤ i ≤ 2m`.
* `Morse.theorem_23_3_mulEquiv`: **Theorem 23.3**, `π_i(G_m(ℂ^{2m}), P) ≃* π_{i+1}(SU(2m), I)` for
  `1 ≤ i ≤ 2m`.
* `Morse.nonempty_mulEquiv_pi_unitary_two_mul`: `π_{i−1} U(m) ≃* π_{i+1} U(2m)` for `2 ≤ i ≤ 2m`;
  `Morse.periodicity_theorem_mulEquiv`: **`π_{i−1} U(m) ≃* π_{i+1} U(m)` for `2 ≤ i ≤ 2m − 2`**.
* `Morse.nonempty_mulEquiv_pi_unitary_odd`, `Morse.nonempty_mulEquiv_pi_unitary_even`: in the
  stable range, `π_j U(m) ≃* π_1 U(m)` for odd `j` and `π_j U(m) ≃* π_2 U(m)` for even `j ≥ 2`.

## What Milnor leaves implicit

* **Groups.**  The steps are Lemma 23.4 as groups
  (`Morse.Homotopy.nonempty_mulEquiv_grassmannianPi`), induced maps of homeomorphisms, homotopy
  equivalences and inclusions (`Morse.Homotopy.homotopyGroupHom`), and Corollary 22.2 as groups
  (`Morse.corollary_22_2_mulEquiv`, which needs change of basepoint to be a homomorphism,
  `Morse.Homotopy.changeBaseMulEquiv`).
* **`π_1 U(m) ≅ ℤ` as groups.**  The project's `π_1 S¹ ≃ ℤ`
  (`Morse.Homotopy.nonempty_pi_one_circle_equiv_int`) is the boundary map of the covering into
  `π_0` of the fibre, a bijection of sets; the group isomorphism `π_1 S¹ ≃* Multiplicative ℤ`
  (from Mathlib's monodromy of the covering `ℝ → S¹`) and Theorem 23.5 as `≃* Multiplicative ℤ`
  (`Morse.theorem_23_5_mulEquiv`) are in `Morse/Chapter14/CircleGroup.lean`.
-/

open Matrix Set Function Topology
open scoped unitInterval Topology.Homotopy Morse.MatrixInner

noncomputable section

namespace Morse

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}

/-- **Corollary 22.2 for `SU(2m)` as groups**: `π_i(Ω^d, γ) ≅ π_{i+1}(SU(2m), I)` for
`1 ≤ i ≤ 2m` (`i = j + 1`). -/
theorem corollary_22_2_su_mulEquiv (hcard : Fintype.card ι = 2 * m) {j : ℕ} (hj : j + 1 ≤ 2 * m)
    (γ : minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) :
    Nonempty (π_ (j + 1) (minPaths (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ)) 1 (-1)) γ ≃*
      π_ (j + 2) (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))
        ⟨1, (specialUnitaryGroup ι ℂ).one_mem⟩) :=
  corollary_22_2_mulEquiv isSliceSubmanifold_specialUnitaryGroup
    (specialUnitaryGroup ι ℂ).one_mem (neg_one_mem_su hcard)
    (fun r => isCompact_closedRiemBall_of_isClosed isSliceSubmanifold_specialUnitaryGroup
      isCompact_specialUnitaryGroup.isClosed 1 r) (l₀ := 2 * m + 2)
    (fun γ hγ hgeo hnm => le_formIndex_of_not_minimal_su hcard hγ hgeo hnm)
    (exists_retraction_minPaths_su hcard) (by omega) γ

/-- **Theorem 23.3 (Bott) as groups** (Milnor pp. 128–129): `π_i G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m)` as
groups for `1 ≤ i ≤ 2m` (`i = j + 1`), at any point `P` of the Grassmannian. -/
theorem theorem_23_3_mulEquiv (hcard : Fintype.card ι = 2 * m) (P : grassmannian ι m) {j : ℕ}
    (hj : j + 1 ≤ 2 * m) :
    Nonempty (π_ (j + 1) (grassmannian ι m) P ≃*
      π_ (j + 2) (specialUnitaryGroup ι ℂ : Set (Matrix ι ι ℂ))
        ⟨1, (specialUnitaryGroup ι ℂ).one_mem⟩) := by
  set A := (lemma_23_1 hcard).symm P
  obtain ⟨e⟩ := corollary_22_2_su_mulEquiv hcard hj (minVelToPaths hcard A)
  exact ⟨(MulEquiv.ofBijective (Homotopy.homotopyGroupHom (N := Fin (j + 1))
      ((lemma_23_1 hcard).symm : C(grassmannian ι m, minVel ι)) P)
      (Homotopy.bijective_homotopyGroupMap_homeomorph (lemma_23_1 hcard).symm P)).trans
    ((MulEquiv.ofBijective (Homotopy.homotopyGroupHom (N := Fin (j + 1))
      (minPathsHomotopyEquiv hcard).toFun A)
      (Homotopy.bijective_homotopyGroupMap_of_homotopyEquiv (minPathsHomotopyEquiv hcard) A)).trans
      e)⟩

/-- **Milnor's chain as groups** (p. 129): `π_{i−1} U(m) ≅ π_i G_m(ℂ^{2m}) ≅ π_{i+1} SU(2m) ≅
π_{i+1} U(2m)` for `2 ≤ i ≤ 2m` (`i = j + 2`). -/
theorem nonempty_mulEquiv_pi_unitary_two_mul {j : ℕ} (hj : j + 2 ≤ 2 * m) :
    Nonempty (π_ (j + 1) (unitaryGroup (Fin m) ℂ) 1 ≃*
      π_ (j + 3) (unitaryGroup (Fin m ⊕ Fin m) ℂ) 1) := by
  have : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hcard := card_sum_fin m
  set P := lemma_23_1 hcard ⟨_, suDiag_kHalf_mem_minVel hcard⟩
  obtain ⟨e₁⟩ := Homotopy.nonempty_mulEquiv_grassmannianPi hcard P hj
  obtain ⟨e₂⟩ := theorem_23_3_mulEquiv hcard P (j := j + 1) (by omega)
  have e₃ := MulEquiv.ofBijective (Homotopy.homotopyGroupHom (N := Fin (j + 3))
    (Homotopy.suInclC (Fin m ⊕ Fin m)) (⟨1, (specialUnitaryGroup (Fin m ⊕ Fin m) ℂ).one_mem⟩ :
      specialUnitaryGroup (Fin m ⊕ Fin m) ℂ))
    (Homotopy.bijective_homotopyGroupMap_suInclC (j := j + 1)
      (⟨1, (specialUnitaryGroup (Fin m ⊕ Fin m) ℂ).one_mem⟩ :
        specialUnitaryGroup (Fin m ⊕ Fin m) ℂ))
  exact ⟨e₁.symm.trans (e₂.trans e₃)⟩

/-- **The periodicity theorem as groups** (Milnor p. 129): `π_{i−1} U(m) ≅ π_{i+1} U(m)` as groups
for `2 ≤ i ≤ 2m − 2` (`i = j + 2`; for `i = 1`, `π_0` is not a group, see
`Morse.periodicity_theorem`). -/
theorem periodicity_theorem_mulEquiv {j : ℕ} (hj : j + 4 ≤ 2 * m) :
    Nonempty (π_ (j + 1) (unitaryGroup (Fin m) ℂ) 1 ≃* π_ (j + 3) (unitaryGroup (Fin m) ℂ) 1) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_pi_unitary_two_mul (m := m) (j := j) (by omega)
  have hs := Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex (m := m) (k := m)
    (i := j + 3) (by omega) 1
  have h1 : Homotopy.unitaryInclC (𝕜 := ℂ) m m 1 = 1 :=
    map_one (Homotopy.unitaryIncl ℂ (Fin m) (Fin m))
  have e' := MulEquiv.ofBijective (Homotopy.homotopyGroupHom _ _) hs
  rw [h1] at e'
  exact ⟨e.trans e'.symm⟩

/-- **Theorem 23.5 as groups, odd degrees**: in the stable range, `π_j U(m) ≅ π_1 U(m)` as groups
for odd `j` (`j = 2k + 1`, `2k + 2 ≤ 2m`); and `π_1 U(m) ≅ π_1 U(1) = π_1 S¹`
(`Morse.Homotopy.nonempty_pi_unitary_equiv_circle` as a bijection). -/
theorem nonempty_mulEquiv_pi_unitary_odd {k : ℕ} (hk : 2 * k + 2 ≤ 2 * m) :
    Nonempty (π_ (2 * k + 1) (unitaryGroup (Fin m) ℂ) 1 ≃* π_ 1 (unitaryGroup (Fin m) ℂ) 1) := by
  induction k with
  | zero => exact ⟨MulEquiv.refl _⟩
  | succ k ih =>
    obtain ⟨e⟩ := ih (by omega)
    obtain ⟨e'⟩ := periodicity_theorem_mulEquiv (m := m) (j := 2 * k) (by omega)
    exact ⟨e'.symm.trans e⟩

/-- **Theorem 23.5 as groups, even degrees `≥ 2`**: `π_j U(m) ≅ π_2 U(m)` for even `j ≥ 2` in the
stable range (and `π_2 U(m)` is trivial, `Morse.theorem_23_5`). -/
theorem nonempty_mulEquiv_pi_unitary_even {k : ℕ} (hk : 2 * k + 3 ≤ 2 * m) :
    Nonempty (π_ (2 * k + 2) (unitaryGroup (Fin m) ℂ) 1 ≃* π_ 2 (unitaryGroup (Fin m) ℂ) 1) := by
  induction k with
  | zero => exact ⟨MulEquiv.refl _⟩
  | succ k ih =>
    obtain ⟨e⟩ := ih (by omega)
    obtain ⟨e'⟩ := periodicity_theorem_mulEquiv (m := m) (j := 2 * k + 1) (by omega)
    exact ⟨e'.symm.trans e⟩

end Morse
