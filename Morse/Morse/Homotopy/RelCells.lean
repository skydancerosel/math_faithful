import Mathlib
import Morse.Homotopy.Telescope
import Morse.Chapter10.RelativeCells

/-!
# Homotopy groups of relative cell complexes: the form of Milnor's Theorem 22.1

Milnor's Theorem 22.1 (and the proofs of both Bott periodicity theorems) concludes from the
fundamental theorem of Morse theory that the path space `Ω` has the homotopy type of a cell
complex obtained from a sublevel set `Ω^d` by attaching cells of dimension `≥ λ₀`, and deduces
that `π_i(Ω^d) → π_i(Ω)` is an isomorphism for `i ≤ λ₀ - 2` ("`π_i(Ω, Ω^d) = 0` for
`i < λ₀`"). This file gives that deduction, for the project's notion of "having the homotopy type
of a relative cell complex" (`Morse.IsRelCellComplexType`: `ι : A → X` is, up to homotopy
equivalence, the inclusion of `A` into `A` with cells attached).

## Main results

* `Morse.Homotopy.bijective_homotopyGroupMap_of_isHomotopyEquiv`: homotopy equivalences (in the
  sense of `Morse.IsHomotopyEquiv`) induce bijections on all homotopy groups.
* `Morse.Homotopy.bijective_homotopyGroupMap_of_isRelCellComplexType`,
  `…surjective…`: if `ι : A → X` has the homotopy type of the inclusion of `A` into `A` with
  finitely many cells of dimension `≥ λ₀` attached, then `ι_*` is a bijection on `π_i` for
  `i ≤ λ₀ - 2` and onto for `i = λ₀ - 1`, at every basepoint of `A`. The homotopy equivalences
  are transferred by `Morse.Homotopy.bijective_homotopyGroupMap_iff_of_square`, the cells by
  `Morse.Homotopy.bijective_homotopyGroupMap_of_isRelCellAttachment`.
* `Morse.Homotopy.bijective_homotopyGroupMap_of_seq`, `…surjective…`: **countably many cells**:
  if `B₀ ⊆ B₁ ⊆ ⋯ ⊆ X`, every compact subset of `X` lies in some `B n`, and each inclusion
  `B n → B (n + 1)` has the homotopy type of a relative cell complex with cells of dimension
  `≥ λ₀`, then `B₀ → X` is bijective on `π_i` for `i ≤ λ₀ - 2` and onto for `i = λ₀ - 1`.
* `Morse.Homotopy.bijective_homotopyGroupMap_sublevel`, `…surjective…`: the same for the sublevel
  sets `B n = {E ≤ a_n}` of a continuous `E : X → ℝ` with `a_n ↗ ∞` (every compact set lies in
  one of them): the setting of Theorem 22.1, with `E` the energy and `a₀ = d`.
* `Morse.Homotopy.bijective_homotopyGroupMap_of_telescope`, `…surjective…`: the same when `ι`
  is, up to homotopy equivalences and a homotopy-commutative square, the inclusion of the bottom
  stage of a countable cell complex (`Morse.CellTower`, mapping telescope) whose other cells have
  dimension `≥ λ₀`.
-/

open Set Function Topology Filter
open scoped unitInterval Topology.Homotopy

universe u

noncomputable section

namespace Morse.Homotopy

open Morse (IsRelCellComplexType IsHomotopyEquiv inclC sublevel sublevel_mono mem_sublevel)

variable {N : Type*} [Fintype N]

omit [Fintype N] in
/-- **A homotopy equivalence induces bijections on all homotopy groups** (`Morse.IsHomotopyEquiv`
form of `Morse.Homotopy.bijective_homotopyGroupMap_of_homotopyEquiv`). -/
theorem bijective_homotopyGroupMap_of_isHomotopyEquiv [Finite N] {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : C(X, Y)} (hf : IsHomotopyEquiv f) (x : X) :
    Bijective (homotopyGroupMap (N := N) f x) := by
  obtain ⟨e, rfl⟩ := hf.exists_homotopyEquiv
  exact bijective_homotopyGroupMap_of_homotopyEquiv e x

section Finite

variable {A X : Type u} [TopologicalSpace A] [TopologicalSpace X] {ι : C(A, X)}
  {cells : List ℕ}

/-- **Relative cell complexes, finitely many cells** (Milnor, Theorem 22.1, the step from cells to
homotopy groups): if `ι : A → X` has the homotopy type of the inclusion of `A` into `A` with cells
of dimensions `cells` attached (`Morse.IsRelCellComplexType`), all `≥ |N| + 2`, then `ι` induces a
bijection `π_N(A, a) → π_N(X, ι a)` for every `a ∈ A`. -/
theorem bijective_homotopyGroupMap_of_isRelCellComplexType (h : IsRelCellComplexType ι cells)
    (hcells : ∀ c ∈ cells, Fintype.card N + 2 ≤ c) (a : A) :
    Bijective (homotopyGroupMap (N := N) ι a) := by
  obtain ⟨K, j, hrel, e, he⟩ := h
  have hsq : (e.toFun.comp ι).Homotopic (j.hom.comp (ContinuousMap.HomotopyEquiv.refl A).toFun) :=
    he
  exact (bijective_homotopyGroupMap_iff_of_square (ContinuousMap.HomotopyEquiv.refl A) e hsq
    a).2 (bijective_homotopyGroupMap_of_isRelCellAttachment hrel hcells a)

/-- **Relative cell complexes, surjectivity**: if the cells all have dimension `> |N|`, `ι` is
onto on `π_N`. -/
theorem surjective_homotopyGroupMap_of_isRelCellComplexType (h : IsRelCellComplexType ι cells)
    (hcells : ∀ c ∈ cells, Fintype.card N < c) (a : A) :
    Surjective (homotopyGroupMap (N := N) ι a) := by
  obtain ⟨K, j, hrel, e, he⟩ := h
  have hsq : (e.toFun.comp ι).Homotopic (j.hom.comp (ContinuousMap.HomotopyEquiv.refl A).toFun) :=
    he
  exact (surjective_homotopyGroupMap_iff_of_square (ContinuousMap.HomotopyEquiv.refl A) e hsq
    a).2 (surjective_homotopyGroupMap_of_isRelCellAttachment hrel hcells a)

end Finite

section Countable

variable {X : Type u} [TopologicalSpace X] {B : ℕ → Set X} {cells : ℕ → List ℕ}

/-- **Relative cell complexes, countably many cells**: let `B₀ ⊆ B₁ ⊆ ⋯ ⊆ X` with every compact
subset of `X` in some `B n`, each inclusion `B n → B (n + 1)` having the homotopy type of a
relative cell complex with cells of dimension `≥ |N| + 2`. Then `B₀ → X` is bijective on `π_N`, at
every basepoint. -/
theorem bijective_homotopyGroupMap_of_seq (hB : Monotone B)
    (hK : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ B n)
    (hrel : ∀ n, IsRelCellComplexType (inclC (hB n.le_succ)) (cells n))
    (hcells : ∀ n, ∀ c ∈ cells n, Fintype.card N + 2 ≤ c) (x₀ : B 0) :
    Bijective (homotopyGroupMap (N := N) (valC (B 0)) x₀) :=
  bijective_homotopyGroupMap_valC_of_step hB hK
    (fun n x => bijective_homotopyGroupMap_of_isRelCellComplexType (hrel n) (hcells n) x) x₀

/-- **Countably many cells, surjectivity.** -/
theorem surjective_homotopyGroupMap_of_seq (hB : Monotone B)
    (hK : ∀ K : Set X, IsCompact K → ∃ n, K ⊆ B n)
    (hrel : ∀ n, IsRelCellComplexType (inclC (hB n.le_succ)) (cells n))
    (hcells : ∀ n, ∀ c ∈ cells n, Fintype.card N < c) (x₀ : B 0) :
    Surjective (homotopyGroupMap (N := N) (valC (B 0)) x₀) :=
  surjective_homotopyGroupMap_valC_of_step hB hK
    (fun n x => surjective_homotopyGroupMap_of_isRelCellComplexType (hrel n) (hcells n) x) x₀

omit [Fintype N] in
/-- Every compact set lies in some sublevel set `{E ≤ a_n}` when `a_n → ∞`. -/
theorem exists_subset_sublevel (E : C(X, ℝ)) {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {K : Set X} (hK : IsCompact K) : ∃ n, K ⊆ sublevel E (a n) := by
  obtain ⟨b, hb⟩ := hK.bddAbove_image E.continuous.continuousOn
  obtain ⟨n, hn⟩ := (ha.eventually_ge_atTop b).exists
  exact ⟨n, fun x hx => mem_sublevel.2 ((hb ⟨x, hx, rfl⟩).trans hn)⟩

/-- **The setting of Milnor's Theorem 22.1**: let `E : X → ℝ` be continuous and `a₀ ≤ a₁ ≤ ⋯`
tend to `∞`, and suppose that each inclusion `{E ≤ a_n} → {E ≤ a_{n+1}}` has the homotopy type of
a relative cell complex with cells of dimension `≥ |N| + 2`. Then `{E ≤ a₀} → X` is bijective on
`π_N` at every basepoint (Milnor: `π_i(Ω, Ω^d) = 0` for `i < λ₀`, with `E` the energy, `a₀ = d`
and all cells of dimension `≥ λ₀`). -/
theorem bijective_homotopyGroupMap_sublevel (E : C(X, ℝ)) {a : ℕ → ℝ} (ha : Monotone a)
    (ha' : Tendsto a atTop atTop)
    (hrel : ∀ n, IsRelCellComplexType (inclC (sublevel_mono E (ha n.le_succ))) (cells n))
    (hcells : ∀ n, ∀ c ∈ cells n, Fintype.card N + 2 ≤ c) (x₀ : sublevel E (a 0)) :
    Bijective (homotopyGroupMap (N := N) (valC (sublevel E (a 0))) x₀) :=
  bijective_homotopyGroupMap_of_seq (B := fun n => sublevel E (a n))
    (fun _ _ h => sublevel_mono E (ha h)) (fun _ hK => exists_subset_sublevel E ha' hK) hrel
    hcells x₀

/-- **Theorem 22.1 setting, surjectivity**: with cells of dimension `> |N|`, `{E ≤ a₀} → X` is
onto on `π_N`. -/
theorem surjective_homotopyGroupMap_sublevel (E : C(X, ℝ)) {a : ℕ → ℝ} (ha : Monotone a)
    (ha' : Tendsto a atTop atTop)
    (hrel : ∀ n, IsRelCellComplexType (inclC (sublevel_mono E (ha n.le_succ))) (cells n))
    (hcells : ∀ n, ∀ c ∈ cells n, Fintype.card N < c) (x₀ : sublevel E (a 0)) :
    Surjective (homotopyGroupMap (N := N) (valC (sublevel E (a 0))) x₀) :=
  surjective_homotopyGroupMap_of_seq (B := fun n => sublevel E (a n))
    (fun _ _ h => sublevel_mono E (ha h)) (fun _ hK => exists_subset_sublevel E ha' hK) hrel
    hcells x₀

/-- **Countable cell complexes up to homotopy**: let `T` be a cell tower (`Morse.CellTower`)
whose cells attached after the bottom stage `K₀` all have dimension `≥ |N| + 2`, and let
`ι : A → X` be, up to homotopy equivalences `A ≃ K₀` and `X ≃ Tel(K)` (homotopy-commutative
square), the inclusion of `K₀` into the countable complex. Then `ι` is bijective on `π_N`. -/
theorem bijective_homotopyGroupMap_of_telescope {A Z : Type*} [TopologicalSpace A]
    [TopologicalSpace Z] {ι : C(A, Z)} {cells : ℕ → List ℕ} (T : Morse.CellTower.{u} cells)
    (a : ContinuousMap.HomotopyEquiv A (T.K.obj 0))
    (e : ContinuousMap.HomotopyEquiv Z (Morse.MappingTelescope T.K))
    (hsq : (e.toFun.comp ι).Homotopic ((telescopeIncl T.K 0).comp a.toFun))
    (hcells : ∀ n, ∀ c ∈ cells (n + 1), Fintype.card N + 2 ≤ c) (x₀ : A) :
    Bijective (homotopyGroupMap (N := N) ι x₀) :=
  (bijective_homotopyGroupMap_iff_of_square a e hsq x₀).2
    (bijective_homotopyGroupMap_of_cellTower T hcells _)

/-- **Countable cell complexes up to homotopy, surjectivity.** -/
theorem surjective_homotopyGroupMap_of_telescope {A Z : Type*} [TopologicalSpace A]
    [TopologicalSpace Z] {ι : C(A, Z)} {cells : ℕ → List ℕ} (T : Morse.CellTower.{u} cells)
    (a : ContinuousMap.HomotopyEquiv A (T.K.obj 0))
    (e : ContinuousMap.HomotopyEquiv Z (Morse.MappingTelescope T.K))
    (hsq : (e.toFun.comp ι).Homotopic ((telescopeIncl T.K 0).comp a.toFun))
    (hcells : ∀ n, ∀ c ∈ cells (n + 1), Fintype.card N < c) (x₀ : A) :
    Surjective (homotopyGroupMap (N := N) ι x₀) :=
  (surjective_homotopyGroupMap_iff_of_square a e hsq x₀).2
    (surjective_homotopyGroupMap_of_cellTower T hcells _)

end Countable

end Morse.Homotopy
