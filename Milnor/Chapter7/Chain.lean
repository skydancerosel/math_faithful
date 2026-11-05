import Milnor.Chapter7.Neighbour

/-!
# Chains of neighbouring points

For a finite set `N` in a connected, locally connected space, `adjN N u z` means `z` lies in the
closure of the component of `u` in the complement of the other points.  A *chain of length `k`
with interior in `A`* from `x` to `z` is a sequence `x = v₀, …, v_k = z` of consecutive
neighbours whose vertices `v₀, …, v_{k-1}` lie in `A`.  Two facts are proved:

* if a chain of minimal length ends at `w`, its earlier vertices avoid `w`
  (`chainRel_diff`), so the chain also has interior in `A \ {w}`;
* if `A ⊆ N` is closed under "the other endpoint of a neighbour" and misses a nonempty part of
  `N`, that part is reached by a chain (`exists_chainRel`, from the neighbour lemma).
-/

open Set Filter Topology

namespace Milnor

variable {X : Type*} [TopologicalSpace X]

/-- `z` is a neighbour of `u` (both in `N`). -/
def adjN (N : Set X) (u z : X) : Prop := u ∈ N ∧ z ∈ N ∧ z ∈ closure (compl' N u)

/-- Chains of length `k` from `x` to `z` with interior vertices in `A`. -/
inductive chainRel (N A : Set X) (x : X) : ℕ → X → Prop
  | zero : chainRel N A x 0 x
  | succ {k : ℕ} {u z : X} (h : chainRel N A x k u) (hu : u ∈ A) (hadj : adjN N u z) :
      chainRel N A x (k + 1) z

theorem chainRel.mono {N A A' : Set X} (hAA' : A ⊆ A') {x : X} {k : ℕ} {z : X}
    (h : chainRel N A x k z) : chainRel N A' x k z := by
  induction h with
  | zero => exact chainRel.zero
  | succ h hu hadj ih => exact chainRel.succ ih (hAA' hu) hadj

theorem chainRel.mem_of_pos {N A : Set X} {x : X} {k : ℕ} {z : X} (h : chainRel N A x k z)
    (hk : 0 < k) : z ∈ N := by
  cases h with
  | zero => exact absurd hk (lt_irrefl 0)
  | succ h hu hadj => exact hadj.2.1

/-- A chain to `u` avoiding `w` in the interior, when no shorter chain reaches `w`. -/
theorem chainRel_diff {N A : Set X} {x w : X} :
    ∀ {k : ℕ} {u : X}, chainRel N A x k u → (∀ j < k, ¬ chainRel N A x j w) →
      u = w ∨ chainRel N (A \ {w}) x k u := by
  intro k
  induction k with
  | zero =>
    intro u h _
    cases h
    by_cases hxw : x = w
    · exact Or.inl hxw
    · exact Or.inr chainRel.zero
  | succ k ih =>
    intro u h hmin
    cases h with
    | succ h' hu' hadj =>
      rename_i u'
      rcases ih h' (fun j hj => hmin j (Nat.lt_succ_of_lt hj)) with rfl | h''
      · exact absurd h' (hmin k (Nat.lt_succ_self k))
      · by_cases huw : u = w
        · exact Or.inl huw
        · have hu'w : u' ≠ w := by
            rintro rfl
            exact hmin k (Nat.lt_succ_self k) h'
          exact Or.inr (chainRel.succ h'' ⟨hu', hu'w⟩ hadj)

/-- A minimal chain to `w` has interior in `A \ {w}`. -/
theorem chainRel_diff' {N A : Set X} {x w : X} {k : ℕ} (h : chainRel N A x k w)
    (hmin : ∀ j < k, ¬ chainRel N A x j w) : chainRel N (A \ {w}) x k w := by
  cases h with
  | zero => exact chainRel.zero
  | succ h' hu' hadj =>
    rename_i k' u'
    rcases chainRel_diff h' (fun j hj => hmin j (Nat.lt_succ_of_lt hj)) with rfl | h''
    · exact absurd h' (hmin k' (Nat.lt_succ_self k'))
    · have hu'w : u' ≠ w := by
        rintro rfl
        exact hmin k' (Nat.lt_succ_self k') h'
      exact chainRel.succ h'' ⟨hu', hu'w⟩ hadj

/-- **Existence of a chain.** In a connected, locally connected space with the segment property,
if `B ⊆ N` and `N \ B` are nonempty, some point of `B` is joined to a point of `N \ B` by a chain
with interior in `B`. -/
theorem exists_chainRel [ConnectedSpace X] [LocallyConnectedSpace X] [T1Space X]
    {N : Set X} (hNf : N.Finite)
    (hseg : ∀ x ∈ N, ∃ J : Set X, IsOpen J ∧ x ∈ J ∧ J ∩ N ⊆ {x} ∧ J \ {x} ⊆ compl' N x)
    {B : Set X} (hBN : B ⊆ N) {x₀ : X} (hx₀ : x₀ ∈ B) (hB' : (N \ B).Nonempty) :
    ∃ k z, z ∈ N \ B ∧ chainRel N B x₀ k z := by
  by_contra hcon
  push Not at hcon
  -- the reachable set
  set R : Set X := {z | ∃ k, chainRel N B x₀ k z} with hR
  have hRN : R ⊆ N := by
    rintro z ⟨k, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · cases hk; exact hBN hx₀
    · exact hk.mem_of_pos hpos
  have hRB : R ⊆ B := by
    intro z hz
    by_contra hzB
    obtain ⟨k, hk⟩ := hz
    exact hcon k z ⟨hRN ⟨k, hk⟩, hzB⟩ hk
  have hx₀R : x₀ ∈ R := ⟨0, chainRel.zero⟩
  have hNR : (N \ R).Nonempty := hB'.mono (Set.sdiff_subset_sdiff_right hRB)
  obtain ⟨u, huR, z, hzR, hz⟩ := exists_neighbour hNf hseg (hRN) ⟨x₀, hx₀R⟩ hNR
  obtain ⟨k, hk⟩ := huR
  exact hzR.2 ⟨k + 1, chainRel.succ hk (hRB ⟨k, hk⟩) ⟨hRN ⟨k, hk⟩, hzR.1, hz⟩⟩

end Milnor
