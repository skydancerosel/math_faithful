import Milnor.Chapter7.Reach
import Milnor.Chapter7.Chain

/-!
# Gathering: two framed `0`-manifolds with the same number of points of one sign are cobordant

Let `G` be a framed `0`-manifold all of whose points have sign `s`.  For `F` with all signs `s`,
the same number of points, and agreeing with `G` on common points, `F` is framed cobordant to
`G`: move the points of `F` one at a time onto the points of `G`, along chains of neighbouring
points (needed when `dim M = 1`, where points cannot pass each other).
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
  (oM : letI := hM.chartedSpace; Orient 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M m)

/-! ### The sign at a point and the count as a finite sum -/

/-- The sign of `F` at `x` (`0` off `F.N`). -/
def sgnAt (F : FramedSub hM 0 m) (x : M) : ℤ :=
  if hx : x ∈ F.N then frameSign hM oM (fun i => F.v i ⟨x, hx⟩) x else 0

theorem sgnAt_of_mem (F : FramedSub hM 0 m) {x : M} (hx : x ∈ F.N) :
    sgnAt oM F x = frameSign hM oM (fun i => F.v i ⟨x, hx⟩) x := dif_pos hx

theorem count_eq_sum (F : FramedSub hM 0 m) :
    count hM oM F = ∑ x ∈ F.finite_N.toFinset, sgnAt oM F x := by
  rw [count, ← finsum_mem_eq_finite_toFinset_sum _ F.finite_N,
    ← finsum_subtype_eq_finsum_cond (p := (· ∈ F.N))]
  apply finsum_congr
  intro x
  rw [sgnAt_of_mem oM F x.2]

theorem count_of_const_sign (F : FramedSub hM 0 m) {s : ℤ}
    (hs : ∀ x (hx : x ∈ F.N), frameSign hM oM (fun i => F.v i ⟨x, hx⟩) x = s) :
    count hM oM F = F.finite_N.toFinset.card * s := by
  rw [count_eq_sum, Finset.sum_congr rfl (fun x hx => by
    rw [sgnAt_of_mem oM F (F.finite_N.mem_toFinset.1 hx), hs]), Finset.sum_const, nsmul_eq_mul]

theorem frameSign_mem (F : FramedSub hM 0 m) {x : M} (hx : x ∈ F.N) :
    frameSign hM oM (fun i => F.v i ⟨x, hx⟩) x = 1 ∨
      frameSign hM oM (fun i => F.v i ⟨x, hx⟩) x = -1 := by
  letI := hM.chartedSpace
  exact orSign_eq_one_or_neg_one finrank_E finrank_E (stdOr m) (oM.or x)
    (basisCLM_bijective (linearIndependent_chartCoord hM (fun i => F.tangent i ⟨x, hx⟩)
      (F.indep ⟨x, hx⟩)))

/-! ### The invariants -/

/-- `F` has all signs `s`, as many points as `G`, and agrees with `G` on common points. -/
structure GInv (G : FramedSub hM 0 m) (s : ℤ) (F : FramedSub hM 0 m) : Prop where
  sign : ∀ x (hx : x ∈ F.N), frameSign hM oM (fun i => F.v i ⟨x, hx⟩) x = s
  card : F.finite_N.toFinset.card = G.finite_N.toFinset.card
  agree : ∀ x (hx : x ∈ F.N) (hx' : x ∈ G.N) (i : Fin m), F.v i ⟨x, hx⟩ = G.v i ⟨x, hx'⟩

/-- The unmatched points of `F`. -/
def unmatched (G F : FramedSub hM 0 m) : Finset M :=
  F.finite_N.toFinset \ G.finite_N.toFinset

theorem mem_unmatched {G F : FramedSub hM 0 m} {x : M} :
    x ∈ unmatched G F ↔ x ∈ F.N ∧ x ∉ G.N := by
  simp [unmatched]

variable {oM}

include hMc hne in
/-- One gathering move: `x ∈ F.N` moves onto a point `z ∈ G.N \ F.N` which is a neighbour of `x`
(relative to any `N ⊇ F.N`), taking the frame of `G`. -/
theorem gather_move (hm : 0 < m) {G : FramedSub hM 0 m} {s : ℤ}
    (hGs : ∀ z (hz : z ∈ G.N), frameSign hM oM (fun i => G.v i ⟨z, hz⟩) z = s)
    {F : FramedSub hM 0 m} (hF : GInv oM G s F) {N : Set M} (hFN : F.N ⊆ N) {x z : M}
    (hx : x ∈ F.N) (hz : z ∈ G.N) (hzF : z ∉ F.N) (hadj : adjN N x z) :
    ∃ F' : FramedSub hM 0 m, F'.N = (F.N \ {x}) ∪ {z} ∧ GInv oM G s F' ∧
      FramedCobordant hM F F' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI := locallyConnectedSpace_M (hM := hM)
  -- `z` lies in the component of `x` in `M \ (F.N \ {x})`
  have hzC : z ∈ compl' F.N x := by
    have h1 : compl' N x ⊆ compl' F.N x :=
      connectedComponentIn_mono _ (compl_subset_compl.2 (Set.sdiff_subset_sdiff_left hFN))
    have h2 : z ∈ closure (compl' F.N x) := closure_mono h1 hadj.2.2
    rcases closure_compl'_subset F.finite_N x h2 with h | h
    · exact h
    · exact absurd h.1 hzF
  obtain ⟨F', hN', hoff, hvz, hcob⟩ := exists_reach hMc hne hm oM F hx hzC
    (fun i => G.tangent i ⟨z, hz⟩) (G.indep ⟨z, hz⟩) (by rw [hGs z hz, hF.sign x hx])
  have hzx : z ≠ x := fun h => hzF (h ▸ hx)
  refine ⟨F', hN', ⟨?_, ?_, ?_⟩, hcob⟩
  · intro y hy
    by_cases hyz : y = z
    · subst hyz
      have : (fun i => F'.v i ⟨y, hy⟩) = fun i => G.v i ⟨y, hz⟩ := funext fun i => hvz i hy
      rw [this]; exact hGs y hz
    · have hy' : y ∈ F.N ∧ y ≠ x := by
        rw [hN'] at hy
        rcases hy with h | h
        · exact h
        · exact absurd h hyz
      have : (fun i => F'.v i ⟨y, hy⟩) = fun i => F.v i ⟨y, hy'.1⟩ :=
        funext fun i => hoff i y hy'.1 hy'.2 hy
      rw [this]; exact hF.sign y hy'.1
  · rw [← hF.card]
    have : F'.finite_N.toFinset = (F.finite_N.toFinset.erase x).cons z (by
        simp [Finset.mem_erase, hzF]) := by
      ext y
      simp only [Set.Finite.mem_toFinset, hN', mem_union, Set.mem_sdiff, mem_singleton_iff,
        Finset.mem_cons, Finset.mem_erase]
      tauto
    rw [this, Finset.card_cons, Finset.card_erase_of_mem (F.finite_N.mem_toFinset.2 hx)]
    have : 0 < F.finite_N.toFinset.card := Finset.card_pos.2 ⟨x, F.finite_N.mem_toFinset.2 hx⟩
    omega
  · intro y hy hy' i
    by_cases hyz : y = z
    · subst hyz
      exact hvz i hy
    · have hy'' : y ∈ F.N ∧ y ≠ x := by
        rw [hN'] at hy
        rcases hy with h | h
        · exact h
        · exact absurd h hyz
      rw [hoff i y hy''.1 hy''.2 hy, hF.agree y hy''.1 hy' i]

/-- The chain predicate: a chain of length `k` from an unmatched point of `F` to an unmatched
point of `G`, with interior in `F.N`. -/
def ChainP (G F : FramedSub hM 0 m) (N : Set M) (k : ℕ) : Prop :=
  ∃ x z, x ∈ F.N ∧ x ∉ G.N ∧ z ∈ G.N ∧ z ∉ F.N ∧ chainRel N F.N x k z

theorem card_unmatched_pos_iff {G F : FramedSub hM 0 m} :
    0 < (unmatched G F).card ↔ (unmatched G F).Nonempty := Finset.card_pos

include hMc hne in
/-- The gathering step: if some point of `F` is unmatched, one can decrease the number of
unmatched points by a framed cobordism (moving along a shortest chain). -/
theorem gather_step (hm : 0 < m) (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    {G : FramedSub hM 0 m} {s : ℤ}
    (hGs : ∀ z (hz : z ∈ G.N), frameSign hM oM (fun i => G.v i ⟨z, hz⟩) z = s) (N : Set M) :
    ∀ d : ℕ, ∀ F : FramedSub hM 0 m, GInv oM G s F → F.N ∪ G.N = N →
      (hex : ∃ j, ChainP G F N j) → Nat.find hex = d →
      ∃ F' : FramedSub hM 0 m, GInv oM G s F' ∧ FramedCobordant hM F F' ∧
        (unmatched G F').card < (unmatched G F).card := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro F hF hN hex hd
  have hspec := Nat.find_spec hex
  rw [hd] at hspec
  obtain ⟨x, z, hxF, hxG, hzG, hzF, hchain⟩ := hspec
  have hmin : ∀ j < d, ¬ ChainP G F N j := fun j hj => by
    have := Nat.find_min hex (hd ▸ hj)
    exact this
  cases hchain with
  | zero => exact absurd hxF hzF
  | succ h' hw hadj =>
    rename_i k w
    have hFN : F.N ⊆ N := hN ▸ subset_union_left
    by_cases hwG : w ∈ G.N
    · -- `w` is matched: move it onto `z` and continue along the shorter chain
      obtain ⟨F₁, hN₁, hF₁, hcob₁⟩ := gather_move hMc hne hm hGs hF hFN hw hzG hzF hadj
      have hwz : w ≠ z := fun h => hzF (h ▸ hw)
      have hxw : x ≠ w := fun h => hxG (h ▸ hwG)
      have hN₁' : F₁.N ∪ G.N = N := by
        rw [hN₁, ← hN]
        ext y
        simp only [mem_union, Set.mem_sdiff, mem_singleton_iff]
        constructor
        · rintro ((⟨h1, -⟩ | rfl) | h2)
          · exact Or.inl h1
          · exact Or.inr hzG
          · exact Or.inr h2
        · rintro (h1 | h2)
          · by_cases hyw : y = w
            · exact Or.inr (hyw ▸ hwG)
            · exact Or.inl (Or.inl ⟨h1, hyw⟩)
          · exact Or.inr h2
      -- the unmatched points are unchanged
      have hU : unmatched G F₁ = unmatched G F := by
        ext y
        simp only [mem_unmatched, hN₁, mem_union, Set.mem_sdiff, mem_singleton_iff]
        constructor
        · rintro ⟨(⟨h1, -⟩ | rfl), h2⟩
          · exact ⟨h1, h2⟩
          · exact absurd hzG h2
        · rintro ⟨h1, h2⟩
          exact ⟨Or.inl ⟨h1, fun h => h2 (h ▸ hwG)⟩, h2⟩
      -- the chain `x → w` has interior avoiding `w`, hence in `F₁.N`
      have hmin' : ∀ j < k, ¬ chainRel N F.N x j w := by
        intro j hj hc
        exact hmin (j + 1) (by omega) ⟨x, z, hxF, hxG, hzG, hzF, chainRel.succ hc hw hadj⟩
      have hc₁ : chainRel N F₁.N x k w :=
        (chainRel_diff' h' hmin').mono (by rw [hN₁]; exact fun y hy => Or.inl hy)
      have hxF₁ : x ∈ F₁.N := by rw [hN₁]; exact Or.inl ⟨hxF, hxw⟩
      have hwF₁ : w ∉ F₁.N := by
        rw [hN₁]
        rintro (⟨-, h⟩ | h)
        · exact h rfl
        · exact hwz h
      have hex₁ : ∃ j, ChainP G F₁ N j := ⟨k, x, w, hxF₁, hxG, hwG, hwF₁, hc₁⟩
      have hd₁ : Nat.find hex₁ < k + 1 := by
        have := Nat.find_min' hex₁ (⟨x, w, hxF₁, hxG, hwG, hwF₁, hc₁⟩ : ChainP G F₁ N k)
        omega
      obtain ⟨F₂, hF₂, hcob₂, hlt⟩ := ih _ hd₁ F₁ hF₁ hN₁' hex₁ rfl
      refine ⟨F₂, hF₂, hcob₁.trans hcob₂, ?_⟩
      rw [← hU]; exact hlt
    · -- `w` is unmatched: move it onto `z`
      obtain ⟨F₁, hN₁, hF₁, hcob₁⟩ := gather_move hMc hne hm hGs hF hFN hw hzG hzF hadj
      refine ⟨F₁, hF₁, hcob₁, ?_⟩
      have hwU : w ∈ unmatched G F := mem_unmatched.2 ⟨hw, hwG⟩
      have : unmatched G F₁ = (unmatched G F).erase w := by
        ext y
        simp only [mem_unmatched, hN₁, mem_union, Set.mem_sdiff, mem_singleton_iff,
          Finset.mem_erase]
        constructor
        · rintro ⟨(⟨h1, h2⟩ | rfl), h3⟩
          · exact ⟨h2, h1, h3⟩
          · exact absurd hzG h3
        · rintro ⟨h1, h2, h3⟩
          exact ⟨Or.inl ⟨h2, h1⟩, h3⟩
      rw [this]
      exact Finset.card_erase_lt_of_mem hwU

include hMc hne in
/-- **Gathering.** Under the invariants, `F` is framed cobordant to `G`. -/
theorem gather (hm : 0 < m) (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    {G : FramedSub hM 0 m} {s : ℤ}
    (hGs : ∀ z (hz : z ∈ G.N), frameSign hM oM (fun i => G.v i ⟨z, hz⟩) z = s) :
    ∀ n : ℕ, ∀ F : FramedSub hM 0 m, GInv oM G s F → (unmatched G F).card = n →
      FramedCobordant hM F G := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI := hconn
  haveI := locallyConnectedSpace_M (hM := hM)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F hF hn
  by_cases hU : (unmatched G F).card = 0
  · -- no unmatched points: `F = G`
    have hsub : F.finite_N.toFinset ⊆ G.finite_N.toFinset := by
      intro x hx
      by_contra hxG
      have : x ∈ unmatched G F := Finset.mem_sdiff.2 ⟨hx, hxG⟩
      rw [Finset.card_eq_zero] at hU
      rw [hU] at this
      exact Finset.notMem_empty x this
    have heq : F.finite_N.toFinset = G.finite_N.toFinset :=
      Finset.eq_of_subset_of_card_le hsub hF.card.ge
    have hNeq : F.N = G.N := by
      ext x
      rw [← F.finite_N.mem_toFinset, ← G.finite_N.mem_toFinset, heq]
    have : F = G := FramedSub.ext' hM hNeq (fun i x hx hx' => hF.agree x hx hx' i)
    rw [this]; exact FramedCobordant.refl' hMc hne G
  · -- a chain exists; take a gathering step
    obtain ⟨x₀, hx₀⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hU)
    rw [mem_unmatched] at hx₀
    have hNf : (F.N ∪ G.N).Finite := F.finite_N.union G.finite_N
    have hGF : ((F.N ∪ G.N) \ F.N).Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hcon
      have hsub : G.finite_N.toFinset ⊆ F.finite_N.toFinset := by
        intro y hy
        rw [Set.Finite.mem_toFinset] at hy ⊢
        exact hcon (Or.inr hy)
      have heq : G.finite_N.toFinset = F.finite_N.toFinset :=
        Finset.eq_of_subset_of_card_le hsub hF.card.le
      have : x₀ ∈ G.finite_N.toFinset := by
        rw [heq, Set.Finite.mem_toFinset]; exact hx₀.1
      rw [Set.Finite.mem_toFinset] at this
      exact hx₀.2 this
    obtain ⟨k, z, hz, hchain⟩ := exists_chainRel hNf
      (fun x _ => exists_segment_ball (hM := hM) hNf x) subset_union_left hx₀.1 hGF
    have hz' : z ∈ G.N ∧ z ∉ F.N := by
      rcases hz.1 with h | h
      · exact absurd h hz.2
      · exact ⟨h, hz.2⟩
    have hex : ∃ j, ChainP G F (F.N ∪ G.N) j := ⟨k, x₀, z, hx₀.1, hx₀.2, hz'.1, hz'.2, hchain⟩
    obtain ⟨F', hF', hcob, hlt⟩ :=
      gather_step hMc hne hm hconn hGs (F.N ∪ G.N) _ F hF rfl hex rfl
    exact hcob.trans (ih _ (hn ▸ hlt) F' hF' rfl)

/-- The common points at which the frames of `F` and `G` differ. -/
def badSet (G F : FramedSub hM 0 m) : Finset M :=
  (F.finite_N.toFinset ∩ G.finite_N.toFinset).filter
    (fun x => ¬ ∀ (hx : x ∈ F.N) (hx' : x ∈ G.N) (i : Fin m), F.v i ⟨x, hx⟩ = G.v i ⟨x, hx'⟩)

theorem mem_badSet {G F : FramedSub hM 0 m} {x : M} :
    x ∈ badSet G F ↔ x ∈ F.N ∧ x ∈ G.N ∧
      ¬ ∀ (hx : x ∈ F.N) (hx' : x ∈ G.N) (i : Fin m), F.v i ⟨x, hx⟩ = G.v i ⟨x, hx'⟩ := by
  simp [badSet, and_assoc]

include hMc hne in
/-- Frames at common points can be matched by frame changes. -/
theorem exists_matched (hm : 0 < m) {G : FramedSub hM 0 m} {s : ℤ}
    (hGs : ∀ z (hz : z ∈ G.N), frameSign hM oM (fun i => G.v i ⟨z, hz⟩) z = s) :
    ∀ n : ℕ, ∀ F : FramedSub hM 0 m,
      (∀ x (hx : x ∈ F.N), frameSign hM oM (fun i => F.v i ⟨x, hx⟩) x = s) →
      F.finite_N.toFinset.card = G.finite_N.toFinset.card → (badSet G F).card = n →
      ∃ F' : FramedSub hM 0 m, GInv oM G s F' ∧ FramedCobordant hM F F' := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  intro n
  induction n with
  | zero =>
    intro F hFs hcard hbad
    refine ⟨F, ⟨hFs, hcard, ?_⟩, FramedCobordant.refl' hMc hne F⟩
    intro x hx hx' i
    by_contra hcon
    have : x ∈ badSet G F := mem_badSet.2 ⟨hx, hx', fun h => hcon (h hx hx' i)⟩
    rw [Finset.card_eq_zero] at hbad
    rw [hbad] at this
    exact Finset.notMem_empty x this
  | succ n ih =>
    intro F hFs hcard hbad
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < (badSet G F).card)
    obtain ⟨hxF, hxG, -⟩ := mem_badSet.1 hx
    obtain ⟨F₁, hN₁, hoff, hvx, hcob⟩ := exists_reach hMc hne hm oM F hxF
      (mem_compl'_self (N := F.N) (x := x)) (fun i => G.tangent i ⟨x, hxG⟩) (G.indep ⟨x, hxG⟩)
      (by rw [hGs x hxG, hFs x hxF])
    have hN₁' : F₁.N = F.N := by
      rw [hN₁]
      ext y
      simp only [mem_union, Set.mem_sdiff, mem_singleton_iff]
      constructor
      · rintro (⟨h, -⟩ | rfl)
        · exact h
        · exact hxF
      · intro h
        by_cases hyx : y = x
        · exact Or.inr hyx
        · exact Or.inl ⟨h, hyx⟩
    have hFs₁ : ∀ y (hy : y ∈ F₁.N), frameSign hM oM (fun i => F₁.v i ⟨y, hy⟩) y = s := by
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        have : (fun i => F₁.v i ⟨y, hy⟩) = fun i => G.v i ⟨y, hxG⟩ := funext fun i => hvx i hy
        rw [this]; exact hGs y hxG
      · have hyF : y ∈ F.N := hN₁' ▸ hy
        have : (fun i => F₁.v i ⟨y, hy⟩) = fun i => F.v i ⟨y, hyF⟩ :=
          funext fun i => hoff i y hyF hyx hy
        rw [this]; exact hFs y hyF
    have hcard₁ : F₁.finite_N.toFinset.card = G.finite_N.toFinset.card := by
      rw [← hcard]
      congr 1
      ext y
      simp only [Set.Finite.mem_toFinset, hN₁']
    have hbad₁ : badSet G F₁ = (badSet G F).erase x := by
      ext y
      rw [mem_badSet, Finset.mem_erase, mem_badSet]
      have hmem : y ∈ F₁.N ↔ y ∈ F.N := by rw [hN₁']
      constructor
      · rintro ⟨hyF₁, hyG, hbad⟩
        have hyF : y ∈ F.N := hmem.1 hyF₁
        have hyx : y ≠ x := by
          rintro rfl
          exact hbad (fun hx₁ hx' i => hvx i hx₁)
        refine ⟨hyx, hyF, hyG, fun h => hbad ?_⟩
        intro hy₁ hy' i
        rw [hoff i y hyF hyx hy₁]
        exact h hyF hy' i
      · rintro ⟨hyx, hyF, hyG, hbad⟩
        have hyF₁ : y ∈ F₁.N := hmem.2 hyF
        refine ⟨hyF₁, hyG, fun h => hbad ?_⟩
        intro hy hy' i
        rw [← h hyF₁ hy' i, hoff i y hy hyx hyF₁]
    have hbadcard : (badSet G F₁).card = n := by
      rw [hbad₁, Finset.card_erase_of_mem hx]; omega
    obtain ⟨F₂, hF₂, hcob₂⟩ := ih F₁ hFs₁ hcard₁ hbadcard
    exact ⟨F₂, hF₂, hcob.trans hcob₂⟩

end Framed

end Milnor
