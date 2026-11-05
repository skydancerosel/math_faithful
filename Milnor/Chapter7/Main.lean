import Milnor.Chapter7.CancelStep

/-!
# Framed `0`-manifolds with the same signed count are framed cobordant (Milnor §7, p. 51)

Induction on the total number of points.  If `F` (or `G`) has points of both signs, some point
has a neighbour of the opposite sign (the neighbour lemma) and the pair cancels (`cancel_step`).
Otherwise all points of `F` have one sign and all points of `G` have one sign; equal counts force
equal signs and equal numbers of points, and gathering (`gather`) finishes.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  {hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M} (hMc : IsCompact M) (hne : M.Nonempty)
  {oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m}

/-- If `F` has points of both signs, some point has a neighbour of the opposite sign. -/
theorem exists_opposite_neighbour (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    (F : FramedSub hM 0 m) {x y : M} (hx : x ∈ F.N) (hy : y ∈ F.N)
    (hxy : sgnAt oM F x ≠ sgnAt oM F y) :
    ∃ x₀ z, ∃ (hx₀ : x₀ ∈ F.N) (hz : z ∈ F.N), x₀ ≠ z ∧
      frameSign hM oM (fun i => F.v i ⟨z, hz⟩) z = -frameSign hM oM (fun i => F.v i ⟨x₀, hx₀⟩) x₀ ∧
      z ∈ closure (compl' F.N x₀) := by
  letI := hM.chartedSpace
  set B : Set M := {q | q ∈ F.N ∧ sgnAt oM F q = sgnAt oM F x}
  have hBN : B ⊆ F.N := fun q hq => hq.1
  obtain ⟨x₀, hx₀B, z, hzB, hnb⟩ := exists_neighbour_M (hM := hM) hconn F.finite_N hBN
    ⟨x, hx, rfl⟩ ⟨y, hy, fun h => hxy h.2.symm⟩
  have hx₀ : x₀ ∈ F.N := hx₀B.1
  have hz : z ∈ F.N := hzB.1
  have hzne : sgnAt oM F z ≠ sgnAt oM F x₀ := by
    intro h; exact hzB.2 ⟨hz, h.trans hx₀B.2⟩
  refine ⟨x₀, z, hx₀, hz, fun h => hzne (h ▸ rfl), ?_, hnb⟩
  rw [sgnAt_of_mem oM F hz, sgnAt_of_mem oM F hx₀] at hzne
  rcases frameSign_mem oM F hz with h1 | h1 <;> rcases frameSign_mem oM F hx₀ with h2 | h2 <;>
    omega

theorem count_of_empty {F : FramedSub hM 0 m} (h : F.N = ∅) : count hM oM F = 0 := by
  rw [count_eq_sum]
  have : F.finite_N.toFinset = ∅ := by
    rw [Set.Finite.toFinset_eq_empty]; exact h
  rw [this, Finset.sum_empty]

theorem card_of_remove_two {F F' : FramedSub hM 0 m} {x₀ z : M} (hx₀ : x₀ ∈ F.N) (hz : z ∈ F.N)
    (hxz : x₀ ≠ z) (hN : F'.N = F.N \ {x₀, z}) :
    F'.finite_N.toFinset.card + 2 = F.finite_N.toFinset.card := by
  have : F.finite_N.toFinset = insert x₀ (insert z F'.finite_N.toFinset) := by
    ext y
    simp only [Set.Finite.mem_toFinset, Finset.mem_insert, hN, Set.mem_sdiff, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · intro hy
      by_cases h1 : y = x₀
      · exact Or.inl h1
      · by_cases h2 : y = z
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr ⟨hy, fun h => h.elim h1 h2⟩)
    · rintro (rfl | rfl | ⟨hy, -⟩)
      · exact hx₀
      · exact hz
      · exact hy
  have hx₀n : x₀ ∉ insert z F'.finite_N.toFinset := by
    rw [Finset.mem_insert, Set.Finite.mem_toFinset, hN]
    rintro (h | ⟨-, h⟩)
    · exact hxz h
    · exact h (Or.inl rfl)
  have hzn : z ∉ F'.finite_N.toFinset := by
    rw [Set.Finite.mem_toFinset, hN]
    rintro ⟨-, h⟩
    exact h (Or.inr rfl)
  rw [this, Finset.card_insert_of_notMem hx₀n, Finset.card_insert_of_notMem hzn]

include hMc hne in
/-- **Equal signed counts give framed cobordant framed `0`-manifolds.** -/
theorem framedCobordant_of_count_eq (hm : 0 < m)
    (hconn : letI := hM.chartedSpace; ConnectedSpace M) :
    ∀ n : ℕ, ∀ F G : FramedSub hM 0 m,
      F.finite_N.toFinset.card + G.finite_N.toFinset.card = n →
      count hM oM F = count hM oM G → FramedCobordant hM F G := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F G hn hcount
  -- Case A: `F` has both signs
  by_cases hF : ∃ x ∈ F.N, ∃ y ∈ F.N, sgnAt oM F x ≠ sgnAt oM F y
  · obtain ⟨x, hx, y, hy, hxy⟩ := hF
    obtain ⟨x₀, z, hx₀, hz, hxz, hsign, hnb⟩ := exists_opposite_neighbour hconn F hx hy hxy
    obtain ⟨F'', hN'', hoff'', hcob⟩ := cancel_step hMc hne hm F hx₀ hz hxz hsign hnb
    have hc'' : count hM oM F'' = count hM oM F := by
      rw [count_of_remove_two hx₀ hz hxz hN'' hoff'', sgnAt_of_mem oM F hz, sgnAt_of_mem oM F hx₀,
        hsign]
      ring
    have hcard := card_of_remove_two hx₀ hz hxz hN''
    exact hcob.trans (ih (F''.finite_N.toFinset.card + G.finite_N.toFinset.card) (by omega)
      F'' G rfl (hc''.trans hcount))
  -- Case B: `G` has both signs
  by_cases hG : ∃ x ∈ G.N, ∃ y ∈ G.N, sgnAt oM G x ≠ sgnAt oM G y
  · obtain ⟨x, hx, y, hy, hxy⟩ := hG
    obtain ⟨x₀, z, hx₀, hz, hxz, hsign, hnb⟩ := exists_opposite_neighbour hconn G hx hy hxy
    obtain ⟨G'', hN'', hoff'', hcob⟩ := cancel_step hMc hne hm G hx₀ hz hxz hsign hnb
    have hc'' : count hM oM G'' = count hM oM G := by
      rw [count_of_remove_two hx₀ hz hxz hN'' hoff'', sgnAt_of_mem oM G hz, sgnAt_of_mem oM G hx₀,
        hsign]
      ring
    have hcard := card_of_remove_two hx₀ hz hxz hN''
    exact (ih (F.finite_N.toFinset.card + G''.finite_N.toFinset.card) (by omega)
      F G'' rfl (hcount.trans hc''.symm)).trans hcob.symm
  -- Case C: constant signs
  push Not at hF hG
  by_cases hFe : F.N = ∅
  · have hcF : count hM oM F = 0 := count_of_empty hFe
    by_cases hGe : G.N = ∅
    · have : F = G := FramedSub.ext' hM (hFe.trans hGe.symm) (fun i x hx _ => by
        rw [hFe] at hx; exact absurd hx (notMem_empty x))
      rw [this]; exact FramedCobordant.refl' hMc hne G
    · obtain ⟨y₀, hy₀⟩ := Set.nonempty_iff_ne_empty.2 hGe
      have hGs : ∀ x (hx : x ∈ G.N), frameSign hM oM (fun i => G.v i ⟨x, hx⟩) x =
          frameSign hM oM (fun i => G.v i ⟨y₀, hy₀⟩) y₀ := fun x hx => by
        have := hG x hx y₀ hy₀
        rwa [sgnAt_of_mem oM G hx, sgnAt_of_mem oM G hy₀] at this
      have hcG := count_of_const_sign oM G hGs
      have hpos : 0 < G.finite_N.toFinset.card := Finset.card_pos.2 ⟨y₀, G.finite_N.mem_toFinset.2 hy₀⟩
      rcases frameSign_mem oM G hy₀ with h1 | h1 <;>
      · rw [h1] at hcG
        rw [hcF, hcG] at hcount
        omega
  · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.2 hFe
    have hFs : ∀ x (hx : x ∈ F.N), frameSign hM oM (fun i => F.v i ⟨x, hx⟩) x =
        frameSign hM oM (fun i => F.v i ⟨x₀, hx₀⟩) x₀ := fun x hx => by
      have := hF x hx x₀ hx₀
      rwa [sgnAt_of_mem oM F hx, sgnAt_of_mem oM F hx₀] at this
    have hcF := count_of_const_sign oM F hFs
    have hposF : 0 < F.finite_N.toFinset.card :=
      Finset.card_pos.2 ⟨x₀, F.finite_N.mem_toFinset.2 hx₀⟩
    by_cases hGe : G.N = ∅
    · have hcG : count hM oM G = 0 := count_of_empty hGe
      rcases frameSign_mem oM F hx₀ with h1 | h1 <;>
      · rw [h1] at hcF
        rw [hcF, hcG] at hcount
        omega
    · obtain ⟨y₀, hy₀⟩ := Set.nonempty_iff_ne_empty.2 hGe
      have hGs : ∀ x (hx : x ∈ G.N), frameSign hM oM (fun i => G.v i ⟨x, hx⟩) x =
          frameSign hM oM (fun i => G.v i ⟨y₀, hy₀⟩) y₀ := fun x hx => by
        have := hG x hx y₀ hy₀
        rwa [sgnAt_of_mem oM G hx, sgnAt_of_mem oM G hy₀] at this
      have hcG := count_of_const_sign oM G hGs
      have hposG : 0 < G.finite_N.toFinset.card :=
        Finset.card_pos.2 ⟨y₀, G.finite_N.mem_toFinset.2 hy₀⟩
      -- equal signs and equal numbers of points
      have hss : frameSign hM oM (fun i => F.v i ⟨x₀, hx₀⟩) x₀ =
          frameSign hM oM (fun i => G.v i ⟨y₀, hy₀⟩) y₀ ∧
          F.finite_N.toFinset.card = G.finite_N.toFinset.card := by
        rw [hcF, hcG] at hcount
        rcases frameSign_mem oM F hx₀ with h1 | h1 <;> rcases frameSign_mem oM G hy₀ with h2 | h2 <;>
          rw [h1, h2] at hcount ⊢ <;> constructor <;> omega
      obtain ⟨F', hF', hcob'⟩ := exists_matched hMc hne hm (s := frameSign hM oM
        (fun i => G.v i ⟨y₀, hy₀⟩) y₀) hGs _ F (fun x hx => (hFs x hx).trans hss.1) hss.2 rfl
      exact hcob'.trans (gather hMc hne hm hconn hGs _ F' hF' rfl)

end Framed

end Milnor
