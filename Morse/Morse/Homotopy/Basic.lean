import Mathlib

/-!
# Maps induced on homotopy groups, and compressions

Mathlib defines the homotopy groups `π_N(X, x) = HomotopyGroup N X x` as the classes of generalized
loops `I^N → X` (maps sending the boundary `∂I^N` to `x`) up to homotopy relative to `∂I^N`
(`Mathlib/Topology/Homotopy/HomotopyGroup.lean`), but not the maps they induce. This file defines
them and gives the criterion through which Milnor's Theorem 22.1 and the Bott periodicity theorems
use cell attachments.

## Induced maps

A continuous `f : X → Y` carries a generalized loop `γ` at `x` to `f ∘ γ`, a generalized loop at
`f x`, and homotopies relative to `∂I^N` to homotopies relative to `∂I^N`; so it induces
`f_* : π_N(X, x) → π_N(Y, f x)` (`Morse.Homotopy.homotopyGroupMap`), functorially
(`homotopyGroupMap_comp`, `homotopyGroupMap_id`).

## Compressions

Let `j : Y → X` be an embedding. Say that `j` **compresses** maps from `P`
(`Morse.Homotopy.Compresses j P`) if every map `f : P → X` is homotopic, relative to
`f⁻¹(j(Y))`, to a map into `j(Y)`. This is the conclusion of the push-off argument of cellular
approximation (Hatcher, Lemma 4.10), for `X = Y ∪ e^λ` and `P` of dimension `< λ`
(`Morse/Homotopy/CellAttach.lean`). It gives:

* `Morse.Homotopy.surjective_homotopyGroupMap_of_compresses`: if `j` compresses maps from the
  cube `I^N`, then `j_* : π_N(Y, y) → π_N(X, j y)` is onto. A generalized loop in `X` at `j y` is
  compressed relative to the preimage of `j(Y)`, which contains `∂I^N`, so relative to `∂I^N`,
  and the compressed loop factors through the embedding `j`.
* `Morse.Homotopy.injective_homotopyGroupMap_of_compresses`: if `j` compresses maps from
  `I × I^N`, then `j_*` is one-to-one. If `j ∘ α ≃ j ∘ α'` relative to `∂I^N`, the homotopy
  `I × I^N → X` maps `{0, 1} × I^N ∪ I × ∂I^N` into `j(Y)`; compressing it relative to the preimage
  of `j(Y)` gives a homotopy from `α` to `α'` in `Y`, relative to `∂I^N`.
-/

open Set Function Topology
open scoped unitInterval Topology.Homotopy

noncomputable section

namespace Morse.Homotopy

variable {N : Type*} {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-! ### Induced maps -/

/-- The image `f ∘ γ` of a generalized loop `γ` at `x` under `f : X → Y`, a generalized loop at
`f x`. -/
def genLoopMap (f : C(X, Y)) {x : X} (γ : Ω^ N X x) : Ω^ N Y (f x) :=
  ⟨f.comp γ.1, fun y hy => congrArg f (γ.2 y hy)⟩

@[simp]
theorem genLoopMap_apply (f : C(X, Y)) {x : X} (γ : Ω^ N X x) (y : I^N) :
    genLoopMap f γ y = f (γ y) :=
  rfl

theorem genLoopMap_homotopic (f : C(X, Y)) {x : X} {γ γ' : Ω^ N X x}
    (h : GenLoop.Homotopic γ γ') : GenLoop.Homotopic (genLoopMap f γ) (genLoopMap f γ') :=
  h.map fun H => H.compContinuousMap f

/-- **The map induced on homotopy groups**: `f_* : π_N(X, x) → π_N(Y, f x)`, `[γ] ↦ [f ∘ γ]`. -/
def homotopyGroupMap (f : C(X, Y)) (x : X) : HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map (genLoopMap f) fun _ _ h => genLoopMap_homotopic f h

@[simp]
theorem homotopyGroupMap_mk (f : C(X, Y)) {x : X} (γ : Ω^ N X x) :
    homotopyGroupMap f x ⟦γ⟧ = ⟦genLoopMap f γ⟧ :=
  rfl

theorem homotopyGroupMap_comp (g : C(Y, Z)) (f : C(X, Y)) (x : X) :
    homotopyGroupMap (N := N) (g.comp f) x = homotopyGroupMap g (f x) ∘ homotopyGroupMap f x := by
  funext c
  induction c using Quotient.inductionOn
  rfl

theorem homotopyGroupMap_id (x : X) :
    homotopyGroupMap (N := N) (ContinuousMap.id X) x = id := by
  funext c
  induction c using Quotient.inductionOn
  rfl

/-! ### Compressions -/

/-- A homotopy relative to `S` is a homotopy relative to any subset of `S`. -/
def homotopyRelMono {f₀ f₁ : C(X, Y)} {S T : Set X} (F : f₀.HomotopyRel f₁ S) (h : T ⊆ S) :
    f₀.HomotopyRel f₁ T where
  toHomotopy := F.toHomotopy
  prop' t x hx := F.prop t x (h hx)

/-- **`j` compresses maps from `P`**: every map `f : P → X` is homotopic, relative to the preimage
of the range of `j`, to a map into the range of `j`. -/
def Compresses (j : C(Y, X)) (P : Type*) [TopologicalSpace P] : Prop :=
  ∀ f : C(P, X), ∃ g : C(P, X), (∀ p, g p ∈ range j) ∧ f.HomotopicRel g (f ⁻¹' range j)

/-- A map into the range of an embedding factors through it. -/
theorem exists_lift_of_isEmbedding {P : Type*} [TopologicalSpace P] {j : C(Y, X)}
    (hj : IsEmbedding j) (g : C(P, X)) (hg : ∀ p, g p ∈ range j) :
    ∃ g' : C(P, Y), ∀ p, j (g' p) = g p := by
  choose g' hg' using hg
  refine ⟨⟨g', ?_⟩, hg'⟩
  rw [hj.isInducing.continuous_iff]
  exact g.continuous.congr fun p => (hg' p).symm

/-- **Compression gives surjectivity** on `π_N`: if the embedding `j : Y → X` compresses maps from
the cube `I^N`, then `j_* : π_N(Y, y) → π_N(X, j y)` is onto. -/
theorem surjective_homotopyGroupMap_of_compresses {j : C(Y, X)} (hj : IsEmbedding j)
    (hc : Compresses j (I^N)) (y : Y) : Surjective (homotopyGroupMap (N := N) j y) := by
  intro c
  induction c using Quotient.inductionOn with
  | h γ =>
  obtain ⟨g, hg, ⟨F⟩⟩ := hc γ.1
  obtain ⟨g', hg'⟩ := exists_lift_of_isEmbedding hj g hg
  have hbd : ∀ z ∈ Cube.boundary N, g' z = y := by
    intro z hz
    apply hj.injective
    have hz' : z ∈ γ.1 ⁻¹' range j := by
      change γ.1 z ∈ range j
      rw [show γ.1 z = j y from γ.2 z hz]
      exact mem_range_self y
    rw [hg', ← F.fst_eq_snd hz']
    exact γ.2 z hz
  refine ⟨⟦⟨g', hbd⟩⟧, Quotient.sound ?_⟩
  have hgg : (genLoopMap j (⟨g', hbd⟩ : Ω^ N Y y)).1 = g := ContinuousMap.ext hg'
  change (genLoopMap j (⟨g', hbd⟩ : Ω^ N Y y)).1.HomotopicRel γ.1 (Cube.boundary N)
  rw [hgg]
  refine ⟨homotopyRelMono F.symm fun z hz => ?_⟩
  change γ.1 z ∈ range j
  rw [show γ.1 z = j y from γ.2 z hz]
  exact mem_range_self y

/-- **Compression gives injectivity** on `π_N`: if the embedding `j : Y → X` compresses maps from
`I × I^N`, then `j_* : π_N(Y, y) → π_N(X, j y)` is one-to-one. -/
theorem injective_homotopyGroupMap_of_compresses {j : C(Y, X)} (hj : IsEmbedding j)
    (hc : Compresses j (I × I^N)) (y : Y) : Injective (homotopyGroupMap (N := N) j y) := by
  intro c c'
  induction c using Quotient.inductionOn with
  | h α =>
  induction c' using Quotient.inductionOn with
  | h α' =>
  intro hcc
  obtain ⟨F⟩ := Quotient.exact hcc
  obtain ⟨g, hg, ⟨G⟩⟩ := hc F.toContinuousMap
  obtain ⟨g', hg'⟩ := exists_lift_of_isEmbedding hj g hg
  -- `g` agrees with `F` wherever `F` lands in the range of `j`
  have hgF : ∀ q, F.toContinuousMap q ∈ range j → g q = F.toContinuousMap q := fun q hq =>
    (G.fst_eq_snd hq).symm
  have h0 : ∀ z, g' (0, z) = α z := fun z => hj.injective <| by
    rw [hg', hgF (0, z) ⟨α z, (F.apply_zero z).symm⟩]
    exact F.apply_zero z
  have h1 : ∀ z, g' (1, z) = α' z := fun z => hj.injective <| by
    rw [hg', hgF (1, z) ⟨α' z, (F.apply_one z).symm⟩]
    exact F.apply_one z
  have hb : ∀ t, ∀ z ∈ Cube.boundary N, g' (t, z) = α z := by
    intro t z hz
    apply hj.injective
    have hFz : F.toContinuousMap (t, z) = j (α z) := F.eq_fst t hz
    rw [hg', hgF (t, z) ⟨α z, hFz.symm⟩]
    exact hFz
  refine Quotient.sound ⟨?_⟩
  exact
    { toFun := g'
      continuous_toFun := g'.continuous
      map_zero_left := h0
      map_one_left := h1
      prop' := fun t z hz => hb t z hz }

end Morse.Homotopy
