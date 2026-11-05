import Mathlib

/-!
# A finite set in a connected space has "neighbouring" points of prescribed kinds

Let `X` be connected and locally connected, `N ⊆ X` finite, and for `x ∈ N` let `C x` be the
connected component of `x` in `X \ (N \ {x})`.  Assume every `x ∈ N` has a neighbourhood `J`
with `J ∩ N = {x}` and `J \ {x} ⊆ C x` (a "segment property", true in a manifold).  Then for
every partition `N = B ⊔ (N \ B)` into two nonempty parts there are `x ∈ B` and `z ∈ N \ B` with
`z ∈ closure (C x)`: some point of `B` has a "neighbour" in the other part.

Proof: otherwise `A = B ∪ ⋃_{x ∈ B} C x` is open (by the segment property), closed (each
`closure (C x) ⊆ C x ∪ (N \ {x})` misses `N \ B`) and neither empty nor everything.
-/

open Set Filter Topology

namespace Milnor

variable {X : Type*} [TopologicalSpace X]

/-- The connected component of `x` in the complement of the other points of `N`. -/
def compl' (N : Set X) (x : X) : Set X := connectedComponentIn (N \ {x})ᶜ x

theorem compl'_subset (N : Set X) (x : X) : compl' N x ⊆ (N \ {x})ᶜ :=
  connectedComponentIn_subset _ _

theorem mem_compl'_self {N : Set X} {x : X} : x ∈ compl' N x :=
  mem_connectedComponentIn (by simp)

theorem isOpen_compl' [LocallyConnectedSpace X] [T1Space X] {N : Set X} (hN : N.Finite) (x : X) :
    IsOpen (compl' N x) :=
  (hN.diff.isClosed).isOpen_compl.connectedComponentIn

/-- A connected component of an open set is relatively closed. -/
theorem closure_compl'_subset [LocallyConnectedSpace X] [T1Space X] {N : Set X} (hN : N.Finite)
    (x : X) : closure (compl' N x) ⊆ compl' N x ∪ (N \ {x}) := by
  intro y hy
  by_cases hyF : y ∈ (N \ {x})ᶜ
  · left
    have hF : IsOpen (N \ {x})ᶜ := (hN.diff.isClosed).isOpen_compl
    obtain ⟨V, hVF, hVo, hyV, hVc⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.1 inferInstance y _ (hF.mem_nhds hyF)
    -- `V` meets `compl' N x`
    obtain ⟨u, huV, huC⟩ := mem_closure_iff.1 hy V hVo hyV
    have hunion : IsPreconnected (V ∪ compl' N x) :=
      hVc.isPreconnected.union u huV huC (isPreconnected_connectedComponentIn)
    have hsub : V ∪ compl' N x ⊆ compl' N x :=
      hunion.subset_connectedComponentIn (Or.inr mem_compl'_self)
        (union_subset hVF (compl'_subset N x))
    exact hsub (Or.inl hyV)
  · right
    exact not_not.1 hyF

/-- **The neighbour lemma.** -/
theorem exists_neighbour [ConnectedSpace X] [LocallyConnectedSpace X] [T1Space X]
    {N : Set X} (hNf : N.Finite)
    (hseg : ∀ x ∈ N, ∃ J : Set X, IsOpen J ∧ x ∈ J ∧ J ∩ N ⊆ {x} ∧ J \ {x} ⊆ compl' N x)
    {B : Set X} (hBN : B ⊆ N) (hB : B.Nonempty) (hB' : (N \ B).Nonempty) :
    ∃ x ∈ B, ∃ z ∈ N \ B, z ∈ closure (compl' N x) := by
  by_contra hcon
  push Not at hcon
  set A : Set X := B ∪ ⋃ x ∈ B, compl' N x with hA
  have hBf : B.Finite := hNf.subset hBN
  -- `A` is open
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rcases hy with hyB | hyC
    · obtain ⟨J, hJo, hxJ, -, hJC⟩ := hseg y (hBN hyB)
      refine Filter.mem_of_superset (hJo.mem_nhds hxJ) ?_
      intro z hz
      by_cases hzy : z = y
      · rw [hzy]; exact Or.inl hyB
      · exact Or.inr (mem_iUnion₂.2 ⟨y, hyB, hJC ⟨hz, hzy⟩⟩)
    · obtain ⟨x, hxB, hyx⟩ := mem_iUnion₂.1 hyC
      refine Filter.mem_of_superset ((isOpen_compl' hNf x).mem_nhds hyx) ?_
      intro z hz
      exact Or.inr (mem_iUnion₂.2 ⟨x, hxB, hz⟩)
  -- `A` is closed
  have hAc : IsClosed A := by
    rw [← closure_subset_iff_isClosed, hA, closure_union, hBf.closure_biUnion]
    rintro y (hyB | hyC)
    · exact Or.inl (hBf.isClosed.closure_subset hyB)
    · obtain ⟨x, hxB, hyx⟩ := mem_iUnion₂.1 hyC
      rcases closure_compl'_subset hNf x hyx with h | h
      · exact Or.inr (mem_iUnion₂.2 ⟨x, hxB, h⟩)
      · -- `y ∈ N \ {x}`, and `y ∉ N \ B` by the contradiction hypothesis, so `y ∈ B`
        by_cases hyB' : y ∈ B
        · exact Or.inl hyB'
        · exact absurd hyx (hcon x hxB y ⟨h.1, hyB'⟩)
  -- `A` is neither empty nor everything
  have hAne : A.Nonempty := hB.mono subset_union_left
  obtain ⟨z, hzN, hzB⟩ := hB'
  have hzA : z ∉ A := by
    rintro (hzB' | hzC)
    · exact hzB hzB'
    · obtain ⟨x, hxB, hzx⟩ := mem_iUnion₂.1 hzC
      have hzx' : z ≠ x := fun h => hzB (h ▸ hxB)
      exact compl'_subset N x hzx ⟨hzN, hzx'⟩
  rcases isClopen_iff.1 ⟨hAc, hAo⟩ with h | h
  · exact hAne.ne_empty h
  · exact hzA (h ▸ mem_univ z)

end Milnor
