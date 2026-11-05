import Morse.Homology.TripleFiltration
import Morse.Homology.RelativeRetract
import Morse.Chapter2.CWType
import Morse.Chapter3.EulerChar
import Morse.Chapter4.Whitney

/-!
Milnor, *Morse Theory*, §5, pp. 28–29: the tools behind the computation of the homology of a
slab `(M^{a_i}, M^{a_{i-1}})`.

# Tools for the Morse inequalities in singular homology

`Morse/Homology/MorseHomology.lean` proves Milnor's Theorem 5.2, the inequalities `(4_λ)` and
Corollary 5.4 in singular homology for a compact submanifold of Euclidean space.  This file
collects what that proof uses beyond Chapters 2–3 and the relative homology of
`Morse/Homology/`.

## Milnor's computation (p. 29), paraphrased

For consecutive regular values `a_{i-1} < a_i` with one critical point, of index `λ_i`, between
them, Milnor writes in one line
`H_*(M^{a_i}, M^{a_{i-1}}) = H_*(M^{a_{i-1}} ∪ e^{λ_i}, M^{a_{i-1}}) = H_*(e^{λ_i}, ė^{λ_i})`, the
first equality by the homotopy type of `M^{a_i}` (Theorems 3.1 and 3.2), the second "by
excision", and the result is the coefficient field in dimension `λ_i` and zero otherwise.  The
abstract form of the argument made precise is `Morse.Homology.finrank_subsetHomology_of_cells`:
for subsets `A ⊆ B ⊆ B ∪ e ⊆ X' ⊆ X` of a Hausdorff space, where `e` is a finite union of
disjoint cells attached to the closed set `B`, if `A` is a strong deformation retract of `B`,
`B ∪ e` one of `X'` and `X'` one of `X`, then `dim H_i(X, A; 𝕜)` is the number of cells of
dimension `i`.  (For the slab, `A = M^{a_{i-1}}`, `B = M^{c-ε}`, `X' = M^{c+ε}`, `X = M^{a_i}`,
`c` the critical value.)

## What Milnor's computation leaves implicit

* **The first equality is about pairs, not spaces.**  Theorem 3.2 only says that `M^{c+ε}` has
  the homotopy type of `M^{c-ε} ∪ e^λ`; to compare relative homology one needs homotopy
  equivalences of pairs, and the cell is attached to `M^{c-ε}`, not to `M^{a_{i-1}}`.  The top of
  the pair can be moved along the deformation retraction of `M^{a_i}` onto `M^{c+ε}` (Theorem
  3.1), which fixes `M^{c-ε}` pointwise, and `M^{c+ε}` deforms onto `M^{c-ε} ∪ e^λ` fixing
  `M^{c-ε}` (the proof of Theorem 3.2;
  `Morse.Homology.relHomologyIsoOfIsStrongDeformationRetract`).  The bottom cannot be moved
  this way: the deformation of `M^{c-ε}` onto `M^{a_{i-1}}` does not extend to `M^{c+ε}`.  What is
  true is that `H_*(M^{c-ε}, M^{a_{i-1}}) = 0`, so that in the exact sequence of the triple
  `(M^{a_i}, M^{c-ε}, M^{a_{i-1}})` the map
  `H_*(M^{a_i}, M^{a_{i-1}}) → H_*(M^{a_i}, M^{c-ε})` is an isomorphism
  (`Morse.LongExactSeq.bijective_g_of_subsingleton`,
  `Morse.Homology.subsetHomologyEquivOfIsSDRBottom`).
* **Strong deformation retracts.**  The point above needs deformations that fix the smaller set
  at all times, which Milnor's statements of Theorem 3.2 and Remark 3.3 (homotopy type only) do
  not provide; the formalized versions (`Morse.theorem_3_1_submanifold`,
  `Morse.remark_3_3_submanifold`) are strong deformation retractions.
* **"By excision"** is not literally excision (the closure of what is cut out is not inside the
  interior of `M^{c-ε}`); it is the computation of the homology of cells attached to a closed set,
  recorded here as the property `Morse.Homology.CellAttachHomology 𝕜` and proved in
  `Morse/Homology/MorseHomologyCells.lean` (`Morse.Homology.cellAttachHomology`), from the
  excision argument of `Morse/Homology/CellExcision.lean` (after a radial deformation of the
  punctured cell) and the homology of `(Dᵏ, Sᵏ⁻¹)` of `Morse/Homology/Spheres.lean`.
* **The choice of the `a_i`** (p. 29) presupposes regular values separating the critical values;
  `Morse.exists_separating_seq` provides them for any finite set of critical values, with at most
  one critical value in each interval (several critical points on one level are allowed).

## Main definitions and results

* `Morse.exists_separating_seq`, `Morse.exists_mem_Ioo_of_lt`, `Morse.eq_of_mem_Ioo_of_monotone`:
  regular values separating finitely many values.
* `Morse.isCriticalPointM_of_forall_ge`: a global maximum is a critical point.
* `Morse.LongExactSeq.bijective_g_of_subsingleton`: in a long exact sequence whose first terms
  vanish, the middle maps are isomorphisms.
* `Morse.IsStrongDeformationRetract.preimage_subtype`: strong deformation retracts of subspaces
  are carried by homeomorphisms.
* `Morse.Homology.spaceHomology 𝕜 i X = H_i(X; 𝕜)` and `Morse.Homology.bettiNumber 𝕜 X i`, its
  dimension (Milnor's `R_i(X)`); `Morse.Homology.bettiNumber_eq_of_homeomorph`: Betti numbers are
  invariant under homeomorphisms; `Morse.Homology.finrank_subsetHomology_eq_bettiNumber`:
  `H_i(X, ∅) = H_i(X)`.
* `Morse.Homology.CellAttachHomology 𝕜`: the homology of finitely many disjoint cells attached
  to a closed set.
* `Morse.Homology.finrank_subsetHomology_of_cells`: the homology of a step of the Morse
  filtration, abstractly.
-/

open CategoryTheory Limits AlgebraicTopology HomologicalComplex Module Set Finset

universe u

noncomputable section

namespace Morse

/-! ### Regular values separating finitely many critical values -/

/-- **Regular values separating finitely many values** (Milnor p. 29: the choice of
`a_1 < ⋯ < a_k`).  For a finite set `s` of reals above `L` there are `n > 0` and a monotone
sequence `a` with `L < a 0` such that no `a k` lies in `s`, every element of `s` lies in
`(a 0, a n)`, and each interval `(a k, a (k + 1))`, `k < n`, contains at most one element of
`s`. -/
theorem exists_separating_seq (s : Finset ℝ) :
    ∀ L : ℝ, (∀ c ∈ s, L < c) →
      ∃ (n : ℕ) (a : ℕ → ℝ), 0 < n ∧ Monotone a ∧ L < a 0 ∧ (∀ c ∈ s, a 0 < c ∧ c < a n) ∧
        (∀ c ∈ s, ∀ k, a k ≠ c) ∧
        ∀ k < n, ∀ c ∈ s, ∀ c' ∈ s, a k < c → c < a (k + 1) → a k < c' → c' < a (k + 1) →
          c = c' := by
  classical
  induction s using Finset.induction_on_min with
  | empty =>
    intro L _
    exact ⟨1, fun _ ↦ L + 1, one_pos, monotone_const, by linarith, by simp, by simp, by simp⟩
  | insert m s hm ih =>
    intro L hL
    have hLm : L < m := hL m (mem_insert_self m s)
    obtain ⟨n, a, hn, hmono, hma, hin, hne, hsep⟩ := ih m hm
    -- prepend `(L + m) / 2`, just below the new smallest value `m`
    let a' : ℕ → ℝ := fun k ↦ Nat.casesOn k ((L + m) / 2) a
    have ha'0 : a' 0 = (L + m) / 2 := rfl
    have ha's : ∀ k, a' (k + 1) = a k := fun _ ↦ rfl
    have hlt : ∀ c ∈ s, a 0 < c := fun c hc ↦ (hin c hc).1
    refine ⟨n + 1, a', Nat.succ_pos n, monotone_nat_of_le_succ fun k ↦ ?_, ?_, ?_, ?_, ?_⟩
    · cases k with
      | zero => rw [ha'0, ha's]; linarith
      | succ k => rw [ha's, ha's]; exact hmono (Nat.le_succ k)
    · rw [ha'0]; linarith
    · intro c hc
      rw [ha'0, ha's]
      rcases mem_insert.1 hc with rfl | hc
      · exact ⟨by linarith, hma.trans_le (hmono (Nat.zero_le n))⟩
      · exact ⟨by linarith [hm c hc], (hin c hc).2⟩
    · intro c hc k
      rcases mem_insert.1 hc with rfl | hc
      · cases k with
        | zero => rw [ha'0]; linarith
        | succ k => rw [ha's]; exact (hma.trans_le (hmono (Nat.zero_le k))).ne'
      · cases k with
        | zero => rw [ha'0]; linarith [hm c hc]
        | succ k => rw [ha's]; exact hne c hc k
    · intro k hk c hc c' hc' h1 h2 h3 h4
      cases k with
      | zero =>
        change c < a 0 at h2
        change c' < a 0 at h4
        have hcm : c = m := (mem_insert.1 hc).resolve_right fun hc ↦ by linarith [hlt c hc]
        have hc'm : c' = m := (mem_insert.1 hc').resolve_right fun hc' ↦ by linarith [hlt c' hc']
        rw [hcm, hc'm]
      | succ k =>
        change a k < c at h1
        change c < a (k + 1) at h2
        change a k < c' at h3
        change c' < a (k + 1) at h4
        have hmk : m < a k := hma.trans_le (hmono (Nat.zero_le k))
        have hcs : c ∈ s := (mem_insert.1 hc).resolve_left fun h ↦ by rw [h] at h1; linarith
        have hc's : c' ∈ s := (mem_insert.1 hc').resolve_left fun h ↦ by rw [h] at h3; linarith
        exact hsep k (by omega) c hcs c' hc's h1 h2 h3 h4

/-- If `a 0 < c < a n` and `c` is never a value of `a`, then `c` lies in one of the intervals
`(a k, a (k + 1))`, `k < n`. -/
theorem exists_mem_Ioo_of_lt {a : ℕ → ℝ} {n : ℕ} {c : ℝ} (h0 : a 0 < c) (hn : c < a n)
    (hne : ∀ k, a k ≠ c) : ∃ k < n, a k < c ∧ c < a (k + 1) := by
  classical
  have hex : ∃ j, c < a j := ⟨n, hn⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (fun h : Nat.find hex = 0 ↦ by
    have := Nat.find_spec hex
    rw [h] at this
    linarith)
  refine ⟨k, ?_, ?_, ?_⟩
  · have := Nat.find_min' hex hn
    omega
  · exact lt_of_le_of_ne (not_lt.1 (Nat.find_min hex (show k < Nat.find hex by omega))) (hne k)
  · have := Nat.find_spec hex
    rwa [hk] at this

/-- The intervals `(a k, a (k + 1))` of a monotone sequence are pairwise disjoint. -/
theorem eq_of_mem_Ioo_of_monotone {a : ℕ → ℝ} (ha : Monotone a) {c : ℝ} {k j : ℕ}
    (hk : a k < c ∧ c < a (k + 1)) (hj : a j < c ∧ c < a (j + 1)) : k = j := by
  by_contra hkj
  rcases lt_or_gt_of_ne hkj with h | h
  · linarith [ha (show k + 1 ≤ j by omega), hk.2, hj.1]
  · linarith [ha (show j + 1 ≤ k by omega), hj.2, hk.1]

/-! ### Maxima, exact sequences and strong deformation retracts -/

/-- **A global maximum is a critical point** (the companion of
`Morse.isCriticalPointM_of_forall_le`; used for "`M^{a_k} = M`", p. 29). -/
theorem isCriticalPointM_of_forall_ge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (hp : ∀ x, f x ≤ f p) : IsCriticalPointM E f p := by
  rw [isCriticalPointM_iff_fderiv]
  refine IsLocalMax.fderiv_eq_zero (Filter.Eventually.of_forall fun u ↦ ?_)
  rw [localRep_self]
  exact hp _

section LongExactSeq

variable {F : Type*} [Field F] {A B C : ℕ → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module F (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module F (B i)]
  [∀ i, AddCommGroup (C i)] [∀ i, Module F (C i)]

/-- In a long exact sequence `⋯ → A i → B i → C i → A (i - 1) → ⋯` all of whose terms `A i`
vanish, the maps `B i → C i` are bijective. -/
theorem LongExactSeq.bijective_g_of_subsingleton (E : LongExactSeq F A B C)
    (hA : ∀ i, Subsingleton (A i)) (i : ℕ) : Function.Bijective (E.g i) := by
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, (E.exact_f_g i).linearMap_ker_eq, LinearMap.range_eq_bot]
    exact LinearMap.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  · cases i with
    | zero => exact E.surjective_g_zero
    | succ i => exact fun z ↦ (E.exact_g_δ i z).1 (Subsingleton.elim _ _)

/-- The isomorphism `B i ≃ C i` of a long exact sequence all of whose terms `A i` vanish. -/
def LongExactSeq.equivOfSubsingleton (E : LongExactSeq F A B C)
    (hA : ∀ i, Subsingleton (A i)) (i : ℕ) : B i ≃ₗ[F] C i :=
  LinearEquiv.ofBijective (E.g i) (E.bijective_g_of_subsingleton hA i)

end LongExactSeq

/-- **Strong deformation retracts of subspaces are carried by homeomorphisms**: if `A ⊆ B ⊆ T'`
and `A` is a strong deformation retract of `B`, then `e⁻¹(A)` is one of `e⁻¹(B)` for every
homeomorphism `e : T ≃ T'`. -/
theorem IsStrongDeformationRetract.preimage_subtype {T T' : Type*} [TopologicalSpace T]
    [TopologicalSpace T'] (e : T ≃ₜ T') {A B : Set T'}
    (h : IsStrongDeformationRetract ((↑) ⁻¹' A : Set B)) :
    IsStrongDeformationRetract ((↑) ⁻¹' (e ⁻¹' A) : Set (e ⁻¹' B)) :=
  h.preimage_homeomorph (e.subtype (p := (· ∈ e ⁻¹' B)) (q := (· ∈ B)) fun _ ↦ Iff.rfl)

/-- Counting the elements of a finite type satisfying a predicate does not depend on the
enumeration. -/
theorem card_filter_equiv {α β : Type*} [Fintype α] [Fintype β] (σ : α ≃ β) (P : β → Prop)
    [DecidablePred P] : #{a | P (σ a)} = #{b | P b} := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fintype.sum_equiv σ _ _ fun _ ↦ rfl

end Morse

namespace Morse.Homology

variable {𝕜 : Type u} [Field 𝕜]

/-! ### Absolute homology and Betti numbers -/

section Absolute

variable (𝕜)

/-- The singular homology `H_i(X; 𝕜)` of a space `X` with coefficients in a field `𝕜`
(Mathlib's `AlgebraicTopology.singularHomologyFunctor`), as a `𝕜`-module. -/
abbrev spaceHomology (i : ℕ) (X : Type u) [TopologicalSpace X] : ModuleCat.{u} 𝕜 :=
  ((singularHomologyFunctor (ModuleCat.{u} 𝕜) i).obj (ModuleCat.of 𝕜 𝕜)).obj (TopCat.of X)

/-- **The `i`-th Betti number** `b_i(X) = dim_𝕜 H_i(X; 𝕜)` over a field `𝕜` (Milnor's
`R_i(X) = R_i(X, ∅)`, p. 28).  By the convention of `Module.finrank` it is `0` when
`H_i(X; 𝕜)` is infinite-dimensional; for the spaces considered here it is finite-dimensional
(`Morse.Homology.finiteDimensional_spaceHomology`). -/
def bettiNumber (X : Type u) [TopologicalSpace X] (i : ℕ) : ℕ :=
  finrank 𝕜 (spaceHomology 𝕜 i X)

end Absolute

/-- **Homeomorphic spaces have isomorphic homology** (functoriality of singular homology). -/
def spaceHomologyEquivOfHomeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (i : ℕ) : spaceHomology 𝕜 i X ≃ₗ[𝕜] spaceHomology 𝕜 i Y :=
  (((singularHomologyFunctor (ModuleCat.{u} 𝕜) i).obj (ModuleCat.of 𝕜 𝕜)).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) h)).toLinearEquiv

/-- **Homeomorphic spaces have the same Betti numbers.** -/
theorem bettiNumber_eq_of_homeomorph {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) (i : ℕ) : bettiNumber 𝕜 X i = bettiNumber 𝕜 Y i :=
  (spaceHomologyEquivOfHomeomorph h i).finrank_eq

/-- `H_i(E, ∅) ≅ H_i(E)`, for the pair of subsets `∅ ⊆ E` of a space `E`. -/
def subsetHomologyUnivEquiv (E : Type u) [TopologicalSpace E] (i : ℕ) :
    subsetHomology 𝕜 i (Set.empty_subset (univ : Set E)) ≃ₗ[𝕜] spaceHomology 𝕜 i E :=
  ((asIso (homologyMap (relπ (ModuleCat.of 𝕜 𝕜)
      (subsetPair (Set.empty_subset (univ : Set E)))) i)).symm ≪≫
    ((singularHomologyFunctor (ModuleCat.{u} 𝕜) i).obj (ModuleCat.of 𝕜 𝕜)).mapIso
      (TopCat.isoOfHomeo (X := TopCat.of (univ : Set E)) (Y := TopCat.of E)
        (Homeomorph.Set.univ E))).toLinearEquiv

/-- The homology of a pair of subsets `(B, A)` with `A = ∅` and `B = E` is that of `E`. -/
theorem finrank_subsetHomology_eq_bettiNumber {E : Type u} [TopologicalSpace E] {A B : Set E}
    (h : A ⊆ B) (hA : A = ∅) (hB : B = univ) (i : ℕ) :
    finrank 𝕜 (subsetHomology 𝕜 i h) = bettiNumber 𝕜 E i :=
  (finrank_subsetHomology_congr h (Set.empty_subset (univ : Set E)) hA hB i).trans
    (subsetHomologyUnivEquiv E i).finrank_eq

theorem finiteDimensional_spaceHomology_of_subsetHomology {E : Type u} [TopologicalSpace E]
    {A B : Set E} (h : A ⊆ B) (hA : A = ∅) (hB : B = univ) (i : ℕ)
    [FiniteDimensional 𝕜 (subsetHomology 𝕜 i h)] : FiniteDimensional 𝕜 (spaceHomology 𝕜 i E) :=
  have := finiteDimensional_subsetHomology_congr (𝕜 := 𝕜) h (Set.empty_subset (univ : Set E))
    hA hB i
  (subsetHomologyUnivEquiv E i).finiteDimensional

/-! ### The homology of cells attached to a closed set -/

variable (𝕜) in
/-- **The homology of finitely many cells attached to a closed set** (Milnor p. 29:
"`H_*(M^{c-ε} ∪ e^λ, M^{c-ε}) ≅ H_*(e^λ, ė^λ)` by excision", for several cells at once as in
Remark 3.3), as a property of the coefficient field `𝕜`, for spaces in the universe of `𝕜`.

Let `Y` be a closed subset of a Hausdorff space and `χ_j : D^{k_j} → T`, `j < m`, maps of
closed unit balls, continuous and injective on the ball, with pairwise disjoint images, such that
`χ_j(z) ∈ Y` exactly when `‖z‖ = 1` (the cells `e_j = χ_j(D^{k_j})` meet `Y` in their boundary
spheres).  Then `H_i(Y ∪ e_1 ∪ ⋯ ∪ e_m, Y; 𝕜)` is finite-dimensional, of dimension the number of
cells of dimension `i`. -/
def CellAttachHomology : Prop :=
  ∀ ⦃T : Type u⦄ [TopologicalSpace T] [T2Space T] ⦃m : ℕ⦄ ⦃k : Fin m → ℕ⦄
    ⦃χ : (j : Fin m) → EuclideanSpace ℝ (Fin (k j)) → T⦄ ⦃Y : Set T⦄, IsClosed Y →
    (∀ j, ContinuousOn (χ j) (Metric.closedBall 0 1) ∧ InjOn (χ j) (Metric.closedBall 0 1) ∧
      ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k j))) 1, χ j z ∈ Y ↔ ‖z‖ = 1) →
    Pairwise (fun j j' ↦ Disjoint (χ j '' Metric.closedBall 0 1) (χ j' '' Metric.closedBall 0 1)) →
    ∀ i, FiniteDimensional 𝕜 (subsetHomology 𝕜 i
        (subset_union_left (s := Y) (t := ⋃ j, χ j '' Metric.closedBall 0 1))) ∧
      finrank 𝕜 (subsetHomology 𝕜 i
        (subset_union_left (s := Y) (t := ⋃ j, χ j '' Metric.closedBall 0 1))) = #{j | k j = i}

section Retract

variable {E : Type u} [TopologicalSpace E]

/-- `H_i(B, A) ≅ H_i(X, A)` when `B ⊇ A` is a strong deformation retract of `X`
(`Morse.Homology.relHomologyIsoOfIsStrongDeformationRetract`). -/
def subsetHomologyEquivOfIsSDR {A B X : Set E} (hAB : A ⊆ B) (hBX : B ⊆ X)
    (h : IsStrongDeformationRetract ((↑) ⁻¹' B : Set X)) (i : ℕ) :
    subsetHomology 𝕜 i hAB ≃ₗ[𝕜] subsetHomology 𝕜 i (hAB.trans hBX) :=
  (relHomologyIsoOfIsStrongDeformationRetract (ModuleCat.of 𝕜 𝕜) hAB hBX h i).toLinearEquiv

/-- `H_i(B, A) = 0` when `A` is a strong deformation retract of `B`. -/
theorem subsingleton_subsetHomology_of_isSDR {A B : Set E} (hAB : A ⊆ B)
    (h : IsStrongDeformationRetract ((↑) ⁻¹' A : Set B)) (i : ℕ) :
    Subsingleton (subsetHomology 𝕜 i hAB) :=
  ModuleCat.isZero_iff_subsingleton.1
    (isZero_relHomology_of_isStrongDeformationRetract (ModuleCat.of 𝕜 𝕜) hAB h i)

/-- **Moving the bottom of a pair**: if `A ⊆ B ⊆ D` and `A` is a strong deformation retract of
`B`, then `H_i(D, A) ≅ H_i(D, B)`, by the exact sequence of the triple `(D, B, A)`, in which
`H_*(B, A) = 0`.  (The deformation of `B` onto `A` need not extend to `D`.) -/
def subsetHomologyEquivOfIsSDRBottom {A B D : Set E} (hAB : A ⊆ B) (hBD : B ⊆ D)
    (h : IsStrongDeformationRetract ((↑) ⁻¹' A : Set B)) (i : ℕ) :
    subsetHomology 𝕜 i (hAB.trans hBD) ≃ₗ[𝕜] subsetHomology 𝕜 i hBD :=
  (subsetTripleLongExactSeq 𝕜 hAB hBD).equivOfSubsingleton
    (fun j ↦ subsingleton_subsetHomology_of_isSDR hAB h j) i

/-- **The homology of a step of the Morse filtration, abstractly** (Milnor p. 29).  Let
`A ⊆ B ⊆ X' ⊆ X` be subsets of a Hausdorff space, `B` closed, and `e_j = χ_j(D^{k_j})`
pairwise disjoint cells attached to `B` (each meeting `B` in its boundary sphere) with
`B ∪ ⋃ e_j ⊆ X'`.  If `A` is a strong deformation retract of `B`, `B ∪ ⋃ e_j` one of `X'` and
`X'` one of `X`, then `H_i(X, A; 𝕜)` is finite-dimensional, of dimension the number of cells of
dimension `i`:
`H_i(X, A) ≅ H_i(X, B) ≅ H_i(X', B) ≅ H_i(B ∪ ⋃ e_j, B)`. -/
theorem finrank_subsetHomology_of_cells (hcell : CellAttachHomology 𝕜) [T2Space E]
    {A B X' X : Set E} {m : ℕ} {k : Fin m → ℕ}
    {χ : (j : Fin m) → EuclideanSpace ℝ (Fin (k j)) → E} (hB : IsClosed B)
    (hχ : ∀ j, ContinuousOn (χ j) (Metric.closedBall 0 1) ∧ InjOn (χ j) (Metric.closedBall 0 1) ∧
      ∀ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (k j))) 1, χ j z ∈ B ↔ ‖z‖ = 1)
    (hdisj : Pairwise fun j j' ↦
      Disjoint (χ j '' Metric.closedBall 0 1) (χ j' '' Metric.closedBall 0 1))
    (hAB : A ⊆ B) (hB'X' : B ∪ ⋃ j, χ j '' Metric.closedBall 0 1 ⊆ X') (hX'X : X' ⊆ X)
    (h₁ : IsStrongDeformationRetract ((↑) ⁻¹' A : Set B))
    (h₂ : IsStrongDeformationRetract
      ((↑) ⁻¹' (B ∪ ⋃ j, χ j '' Metric.closedBall 0 1) : Set X'))
    (h₃ : IsStrongDeformationRetract ((↑) ⁻¹' X' : Set X)) (hAX : A ⊆ X) (i : ℕ) :
    FiniteDimensional 𝕜 (subsetHomology 𝕜 i hAX) ∧
      finrank 𝕜 (subsetHomology 𝕜 i hAX) = #{j | k j = i} := by
  have hBB' : B ⊆ B ∪ ⋃ j, χ j '' Metric.closedBall 0 1 := subset_union_left
  -- `H_i(X, A) ≅ H_i(X, B)`
  have e₁ := subsetHomologyEquivOfIsSDRBottom (𝕜 := 𝕜) hAB ((hBB'.trans hB'X').trans hX'X) h₁ i
  -- `H_i(X', B) ≅ H_i(X, B)`
  have e₂ := subsetHomologyEquivOfIsSDR (𝕜 := 𝕜) (hBB'.trans hB'X') hX'X h₃ i
  -- `H_i(B ∪ ⋃ e_j, B) ≅ H_i(X', B)`
  have e₃ := subsetHomologyEquivOfIsSDR (𝕜 := 𝕜) hBB' hB'X' h₂ i
  have e : subsetHomology 𝕜 i hAX ≃ₗ[𝕜] subsetHomology 𝕜 i hBB' :=
    e₁.trans (e₂.symm.trans e₃.symm)
  obtain ⟨hfd, hfr⟩ := hcell hB hχ hdisj i
  exact ⟨e.symm.finiteDimensional, e.finrank_eq.trans hfr⟩

end Retract

end Morse.Homology
