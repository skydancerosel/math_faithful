import Milnor.Chapter7.Reach
import Milnor.Chapter7.Equiv
import Milnor.Chapter7.Lemma1
import Milnor.Chapter7.Cobordism
import Milnor.Chapter7.ThmBsupp

/-!
# Operations on framed submanifolds (infrastructure for Milnor §8, Problem 17)

Problem 17 asks to make the set `Πᵖ(M)` of framed cobordism classes of codimension `p` into an
abelian group under disjoint union (for `p ≥ m/2 + 1`).  This file provides the basic
operations:

* `framedCobordant_refl`: framed cobordism is reflexive in every codimension (Theorem B and the
  constant homotopy), so it is an equivalence relation (`framedSetoid`) and we get the set of
  classes `FramedClass`;
* `isSliceSubmanifold_union`: the union of two disjoint compact submanifolds is a submanifold
  (near a point of one of them, the union coincides with that one);
* `FramedSub.union`: the disjoint union of two framed submanifolds; its tangent spaces are those
  of the pieces (`FramedOps.tangentN_eq_of_inter_eq`) and its framing is smooth because it is
  smooth on each piece, and the pieces are open in the union (`FramedOps.contMDiff_unionFun`);
* `FramedCob.union`, `framedCobordant_union`: the disjoint union of two framed cobordisms (with
  disjoint underlying sets, which are closed: `FramedCob.isClosed_S`) is a framed cobordism
  between the disjoint unions of the ends;
* `exists_framedCob_of_homotopy`, `exists_framedCob_of_det_pos`: Lemmas 3 and 1 of §7, with the
  underlying set of the cobordism exposed (to check disjointness later).

`FramedSub.union`, `FramedCob.union` and their lemmas live in `Milnor.Framed` (for dot notation);
the auxiliary lemmas live in `Milnor.Problems.FramedOps`.
-/

open Set Filter Topology Function Module TopologicalSpace
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Milnor

open Sphere

namespace Problems

open Framed

/-! ### Unions of slice submanifolds

The auxiliary declarations live in the namespace `Milnor.Problems.FramedOps`, to avoid clashes with
other files. -/

namespace FramedOps

section sets

theorem union_inter_compl_snd {α : Type*} (s t : Set α) : (s ∪ t) ∩ tᶜ = s ∩ tᶜ := by
  rw [union_inter_distrib_right, inter_compl_self, union_empty]

theorem union_inter_compl_fst {α : Type*} (s t : Set α) : (s ∪ t) ∩ sᶜ = t ∩ sᶜ := by
  rw [union_inter_distrib_right, inter_compl_self, empty_union]

open Classical in
/-- The function on `S ∪ T` given by `v` on `S` and by `w` on the rest. -/
def unionFun {X α : Type*} {S T : Set X} (v : S → α) (w : T → α) (q : ↥(S ∪ T)) : α :=
  if h : q.1 ∈ S then v ⟨q.1, h⟩ else w ⟨q.1, Or.resolve_left q.2 h⟩

open Classical in
theorem unionFun_of_mem_left {X α : Type*} {S T : Set X} (v : S → α) (w : T → α) (q : ↥(S ∪ T))
    (h : q.1 ∈ S) : unionFun v w q = v ⟨q.1, h⟩ :=
  dif_pos h

open Classical in
theorem unionFun_of_mem_right {X α : Type*} {S T : Set X} (hST : Disjoint S T) (v : S → α)
    (w : T → α) (q : ↥(S ∪ T)) (h : q.1 ∈ T) : unionFun v w q = w ⟨q.1, h⟩ :=
  dif_neg (Set.disjoint_right.1 hST h)

end sets

section general

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

omit [IsManifold I ∞ M] in
/-- A set which, near each of its points, coincides with a slice submanifold is a slice
submanifold: restrict the slice charts of the latter to the open sets of coincidence. -/
theorem isSliceSubmanifold_of_locally_eq {S : Set M}
    (h : ∀ x ∈ S, ∃ T U : Set M, IsSliceSubmanifold I Z W T ∧ IsOpen U ∧ x ∈ U ∧ S ∩ U = T ∩ U) :
    IsSliceSubmanifold I Z W S := by
  intro x hx
  obtain ⟨T, U, hT, hU, hxU, hSU⟩ := h x hx
  have hxT : x ∈ T := by
    have : x ∈ S ∩ U := ⟨hx, hxU⟩
    rw [hSU] at this
    exact this.1
  obtain ⟨σ, hxσ⟩ := hT x hxT
  refine ⟨{ φ := σ.φ.restrOpen U hU
            x₀ := x
            x₀_mem := hx
            x₀_source := ⟨hxσ, hxU⟩
            slice := fun r hr => ?_ }, ⟨hxσ, hxU⟩⟩
  rw [PartialDiffeomorph.restrOpen_apply, ← σ.slice r hr.1]
  constructor
  · intro hrS
    have : r ∈ S ∩ U := ⟨hrS, hr.2⟩
    rw [hSU] at this
    exact this.1
  · intro hrT
    have : r ∈ T ∩ U := ⟨hrT, hr.2⟩
    rw [← hSU] at this
    exact this.1

omit [IsManifold I ∞ M] in
/-- The union of two disjoint closed slice submanifolds is a slice submanifold. -/
theorem isSliceSubmanifold_union_of_isClosed {S T : Set M} (hS : IsSliceSubmanifold I Z W S)
    (hT : IsSliceSubmanifold I Z W T) (hSc : IsClosed S) (hTc : IsClosed T) (h : Disjoint S T) :
    IsSliceSubmanifold I Z W (S ∪ T) := by
  refine isSliceSubmanifold_of_locally_eq fun x hx => ?_
  rcases hx with hx | hx
  · exact ⟨S, Tᶜ, hS, hTc.isOpen_compl, Set.disjoint_left.1 h hx, union_inter_compl_snd S T⟩
  · exact ⟨T, Sᶜ, hT, hSc.isOpen_compl, Set.disjoint_right.1 h hx, union_inter_compl_fst S T⟩

/-- A function on a slice submanifold `S` which, on an open set `U`, factors through a smooth
function on a slice submanifold `T ⊇ S ∩ U` is smooth at the points of `U`. -/
theorem contMDiffAt_of_inter_subset {S T : Set M} (hS : IsSliceSubmanifold I Z W S)
    (hT : IsSliceSubmanifold I Z W T) {U : Set M} (hU : IsOpen U) (hST : S ∩ U ⊆ T)
    {v : S → E'} {w : T → E'} (hw : letI := hT.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E') ∞ w)
    (hvw : ∀ (x : S) (hx : x.1 ∈ U), v x = w ⟨x.1, hST ⟨x.2, hx⟩⟩) (x : S) (hx : x.1 ∈ U) :
    letI := hS.chartedSpace; ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, E') ∞ v x := by
  letI := hS.chartedSpace
  haveI := hS.isManifold
  letI := hT.chartedSpace
  haveI := hT.isManifold
  set US : Opens S := ⟨{r | r.1 ∈ U}, hU.preimage continuous_subtype_val⟩ with hUS
  have hmem : ∀ r : US, r.1.1 ∈ T := fun r => hST ⟨r.1.2, r.2⟩
  have hκ : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, Z) ∞ (fun r : US => (⟨r.1.1, hmem r⟩ : T)) :=
    hT.contMDiff_codRestrict (F := fun r : US => r.1.1)
      (hS.contMDiff_val.comp (contMDiff_subtype_val (I := 𝓘(ℝ, Z)))) hmem
  have heq : (fun r : US => v r.1) = w ∘ (fun r : US => (⟨r.1.1, hmem r⟩ : T)) := by
    funext r
    exact hvw r.1 r.2
  refine (contMDiffAt_subtype_iff (I := 𝓘(ℝ, Z)) (I' := 𝓘(ℝ, E')) (n := ∞) (U := US)
    (f := v) (x := ⟨x, hx⟩)).1 ?_
  rw [heq]
  exact (hw.comp hκ).contMDiffAt

/-- The function on a disjoint union of closed slice submanifolds given by smooth functions on
the pieces is smooth. -/
theorem contMDiff_unionFun {S T : Set M} (hS : IsSliceSubmanifold I Z W S)
    (hT : IsSliceSubmanifold I Z W T) (hSc : IsClosed S) (hTc : IsClosed T) (h : Disjoint S T)
    {v : S → E'} {w : T → E'} (hv : letI := hS.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E') ∞ v)
    (hw : letI := hT.chartedSpace; ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E') ∞ w) :
    letI := (isSliceSubmanifold_union_of_isClosed hS hT hSc hTc h).chartedSpace;
    ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E') ∞ (unionFun v w) := by
  have hU := isSliceSubmanifold_union_of_isClosed hS hT hSc hTc h
  intro q
  by_cases hq : q.1 ∈ S
  · exact contMDiffAt_of_inter_subset hU hS hTc.isOpen_compl
      (fun x hx => Or.resolve_right hx.1 hx.2) hv
      (fun x hx => unionFun_of_mem_left v w x _) q (Set.disjoint_left.1 h hq)
  · exact contMDiffAt_of_inter_subset hU hT hSc.isOpen_compl
      (fun x hx => Or.resolve_left hx.1 hx.2) hw
      (fun x hx => unionFun_of_mem_right h v w x _) q hq

end general

end FramedOps

open FramedOps

/-! ### The setting of Chapter 7 -/

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty) {n p : ℕ}

/-! ### Reflexivity and the set of classes -/

section classes

variable {hM} in
include hMc hne in
/-- **Framed cobordism is reflexive**, in every codimension: by Theorem B, `F` is the Pontryagin
manifold of some `k`, and the constant homotopy gives a framed cobordism from `F` to itself. -/
theorem framedCobordant_refl (F : FramedSub hM n p) : FramedCobordant hM F F := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  obtain ⟨k, hk, hkn, c, hc, hcb, hkF⟩ :=
    exists_map_of_framedSub hM hMc hne F _ (linearIndependent_single (m := p))
  have hH : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p))
      ∞ (fun q : M × ℝ => k q.1) :=
    hk.comp contMDiff_fst
  have h := framedCobordant_of_homotopy hM hMc hne F.dim (ε := 1 / 4) (by norm_num)
    (by norm_num) hH (isRegularValue_comp_fst hM hk hkn) (fun x t _ => rfl)
    (fun x t _ => rfl) hk hkn hk hkn _ hcb
  rw [hkF] at h
  exact h

include hMc hne in
/-- Framed cobordism as a setoid on the framed submanifolds of `M` of dimension `n` and
codimension `p`. -/
def framedSetoid (n p : ℕ) : Setoid (FramedSub hM n p) where
  r := FramedCobordant hM
  iseqv := ⟨framedCobordant_refl hMc hne, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **The set `Πᵖ(M)`** of framed cobordism classes of framed submanifolds of `M` of dimension
`n` and codimension `p` (with `n + p = m`). -/
def FramedClass (n p : ℕ) : Type := Quotient (framedSetoid hM hMc hne n p)

end classes

/-! ### Disjoint unions of framed submanifolds -/

section unionSub

/-- **The union of two disjoint compact slice submanifolds** of `M` is a slice submanifold: near
a point of `N` the union coincides with `N` (on the open set `N'ᶜ`), and symmetrically. -/
theorem isSliceSubmanifold_union {N N' : Set M}
    (hN : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin p)) N)
    (hN' : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin p)) N')
    (hc : IsCompact N) (hc' : IsCompact N') (h : Disjoint N N') :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin p)) (N ∪ N') := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  exact isSliceSubmanifold_union_of_isClosed hN hN' hc.isClosed hc'.isClosed h

namespace FramedOps

section local_

variable {N N' : Set M}
  (hN : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin p)) N)
  (hN' : letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin p)) N')

include hN hN' in
/-- If two submanifolds `N`, `N'` of `M` agree on an open set `U`, their tangent spaces agree at
points of `U` (one inclusion). -/
theorem tangentN_le_of_inter_eq {U : Set M} (hU : IsOpen U) (hNN' : N ∩ U = N' ∩ U)
    (x : N) (hx : x.1 ∈ U) (hxN' : x.1 ∈ N') :
    tangentN hM hN x ≤ tangentN hM hN' ⟨x.1, hxN'⟩ := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  letI := hN.chartedSpace
  haveI := hN.isManifold
  letI := hN'.chartedSpace
  haveI := hN'.isManifold
  set UN : Opens N := ⟨{r | r.1 ∈ U}, hU.preimage continuous_subtype_val⟩ with hUN
  have hmem : ∀ r : UN, r.1.1 ∈ N' := fun r => by
    have : r.1.1 ∈ N ∩ U := ⟨r.1.2, r.2⟩
    rw [hNN'] at this
    exact this.1
  set κ : UN → N' := fun r => ⟨r.1.1, hmem r⟩ with hκ
  have hκs : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ κ :=
    hN'.contMDiff_codRestrict (F := fun r : UN => r.1.1)
      (hN.contMDiff_val.comp (contMDiff_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))))) hmem
  set r : UN := ⟨x, hx⟩ with hr
  have hA : HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (fun s : N' => (s.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) (κ r)
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (fun s : N' => (s.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) (κ r)) :=
    hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))))
      ((hM.contMDiff_val.comp hN'.contMDiff_val).mdifferentiableAt (x := κ r) (by simp))
  have hB := hasMFDerivAt_mfd (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (hκs.mdifferentiableAt (x := r) (by simp))
  have h1 := hA.comp r hB
  have heq : ((fun s : N' => (s.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) ∘ κ) =
      (fun s : N => (s.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) ∘ (Subtype.val : UN → N) := by
    funext s; rfl
  rw [heq] at h1
  have h2 := HasMFDerivAt.mfd_eq h1
  have hmd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (fun s : N => (s.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) x :=
    (hM.contMDiff_val.comp hN.contMDiff_val).mdifferentiableAt (by simp)
  rw [mfd_comp_subtype_val (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) UN hmd] at h2
  have h2' : (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
      (fun s : N => (s.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) x) =
      (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1)))
        (fun s : N' => (s.1.1 : EuclideanSpace ℝ (Fin (K + 1)))) (κ r)).comp
        (mfd 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) κ r) := h2
  unfold tangentN
  show LinearMap.range _ ≤ LinearMap.range _
  have hκr : κ r = ⟨x.1, hxN'⟩ := rfl
  rw [← hκr, h2', ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp]
  exact LinearMap.map_le_range

include hN hN' in
/-- If two submanifolds `N`, `N'` of `M` agree on an open set `U`, their tangent spaces agree at
points of `U`. -/
theorem tangentN_eq_of_inter_eq {U : Set M} (hU : IsOpen U) (hNN' : N ∩ U = N' ∩ U)
    (x : N) (hx : x.1 ∈ U) (hxN' : x.1 ∈ N') :
    tangentN hM hN x = tangentN hM hN' ⟨x.1, hxN'⟩ :=
  le_antisymm (tangentN_le_of_inter_eq hM hN hN' hU hNN' x hx hxN')
    (tangentN_le_of_inter_eq hM hN' hN hU hNN'.symm ⟨x.1, hxN'⟩ hx x.2)

end local_

end FramedOps

variable {hM}

/-- **Disjoint union of framed submanifolds.** -/
def _root_.Milnor.Framed.FramedSub.union (F G : FramedSub hM n p) (h : Disjoint F.N G.N) :
    FramedSub hM n p where
  N := F.N ∪ G.N
  hN := isSliceSubmanifold_union hM F.hN G.hN F.compact G.compact h
  dim := F.dim
  compact := F.compact.union G.compact
  v i := unionFun (F.v i) (G.v i)
  smooth i := by
    letI := hM.chartedSpace
    haveI := hM.isManifold
    exact contMDiff_unionFun F.hN G.hN F.compact.isClosed G.compact.isClosed h (F.smooth i)
      (G.smooth i)
  tangent i q := by
    show unionFun (F.v i) (G.v i) q ∈ tangentM hM q.1
    by_cases hq : q.1 ∈ F.N
    · rw [unionFun_of_mem_left (F.v i) (G.v i) q hq]
      exact F.tangent i ⟨q.1, hq⟩
    · have hqG : q.1 ∈ G.N := Or.resolve_left q.2 hq
      rw [unionFun_of_mem_right h (F.v i) (G.v i) q hqG]
      exact G.tangent i ⟨q.1, hqG⟩
  normal i q w hw := by
    show ⟪unionFun (F.v i) (G.v i) q, w⟫ = 0
    by_cases hq : q.1 ∈ F.N
    · rw [unionFun_of_mem_left (F.v i) (G.v i) q hq]
      rw [tangentN_eq_of_inter_eq hM (isSliceSubmanifold_union hM F.hN G.hN F.compact G.compact h)
        F.hN G.compact.isClosed.isOpen_compl (union_inter_compl_snd F.N G.N) q
        (Set.disjoint_left.1 h hq) hq] at hw
      exact F.normal i ⟨q.1, hq⟩ w hw
    · have hqG : q.1 ∈ G.N := Or.resolve_left q.2 hq
      rw [unionFun_of_mem_right h (F.v i) (G.v i) q hqG]
      rw [tangentN_eq_of_inter_eq hM (isSliceSubmanifold_union hM F.hN G.hN F.compact G.compact h)
        G.hN F.compact.isClosed.isOpen_compl (union_inter_compl_fst F.N G.N) q hq hqG] at hw
      exact G.normal i ⟨q.1, hqG⟩ w hw
  indep q := by
    by_cases hq : q.1 ∈ F.N
    · have : (fun i => unionFun (F.v i) (G.v i) q) = fun i => F.v i ⟨q.1, hq⟩ :=
        funext fun i => unionFun_of_mem_left (F.v i) (G.v i) q hq
      show LinearIndependent ℝ (fun i => unionFun (F.v i) (G.v i) q)
      rw [this]
      exact F.indep _
    · have hqG : q.1 ∈ G.N := Or.resolve_left q.2 hq
      have : (fun i => unionFun (F.v i) (G.v i) q) = fun i => G.v i ⟨q.1, hqG⟩ :=
        funext fun i => unionFun_of_mem_right h (F.v i) (G.v i) q hqG
      show LinearIndependent ℝ (fun i => unionFun (F.v i) (G.v i) q)
      rw [this]
      exact G.indep _

variable {F G : FramedSub hM n p} {h : Disjoint F.N G.N}

@[simp] theorem _root_.Milnor.Framed.FramedSub.union_N : (F.union G h).N = F.N ∪ G.N := rfl

theorem _root_.Milnor.Framed.FramedSub.union_v_left (i : Fin p) (x : M) (hx : x ∈ F.N)
    (hx' : x ∈ (F.union G h).N) : (F.union G h).v i ⟨x, hx'⟩ = F.v i ⟨x, hx⟩ :=
  unionFun_of_mem_left (F.v i) (G.v i) ⟨x, hx'⟩ hx

theorem _root_.Milnor.Framed.FramedSub.union_v_right (i : Fin p) (x : M) (hx : x ∈ G.N)
    (hx' : x ∈ (F.union G h).N) : (F.union G h).v i ⟨x, hx'⟩ = G.v i ⟨x, hx⟩ :=
  unionFun_of_mem_right h (F.v i) (G.v i) ⟨x, hx'⟩ hx

end unionSub

/-! ### Disjoint unions of framed cobordisms -/

section unionCob

variable {hM}

/-- The underlying set of a framed cobordism is closed: it is the union of its compact part over
`[0, 1]` and of the closed product ends `N₀ × (-∞, 0]`, `N₁ × [1, ∞)`. -/
theorem _root_.Milnor.Framed.FramedCob.isClosed_S {F₀ F₁ : FramedSub hM n p}
    (X : FramedCob hM F₀ F₁) : IsClosed X.S := by
  have hset : X.S = {q ∈ X.S | 0 ≤ q.2 ∧ q.2 ≤ 1} ∪ (F₀.N ×ˢ Iic 0 ∪ F₁.N ×ˢ Ici 1) := by
    ext q
    constructor
    · intro hq
      by_cases h0 : 0 ≤ q.2
      · by_cases h1 : q.2 ≤ 1
        · exact Or.inl ⟨hq, h0, h1⟩
        · have h1' : 1 < q.2 := not_le.1 h1
          exact Or.inr (Or.inr ⟨(X.end1 q (by linarith [X.hε])).1 hq, h1'.le⟩)
      · have h0' : q.2 < 0 := not_le.1 h0
        exact Or.inr (Or.inl ⟨(X.end0 q (by linarith [X.hε])).1 hq, h0'.le⟩)
    · rintro (⟨hq, -⟩ | ⟨hq, hq2⟩ | ⟨hq, hq2⟩)
      · exact hq
      · have hq2' : q.2 ≤ 0 := hq2
        exact (X.end0 q (by linarith [X.hε])).2 hq
      · have hq2' : 1 ≤ q.2 := hq2
        exact (X.end1 q (by linarith [X.hε])).2 hq
  rw [hset]
  exact X.compact.isClosed.union ((F₀.compact.isClosed.prod isClosed_Iic).union
    (F₁.compact.isClosed.prod isClosed_Ici))

variable {F₀ F₁ G₀ G₁ : FramedSub hM n p}

/-- The union of the underlying sets of two disjoint framed cobordisms is a submanifold. -/
theorem FramedOps.isSliceSubmanifold_cobUnion (X : FramedCob hM F₀ F₁) (Y : FramedCob hM G₀ G₁)
    (hXY : Disjoint X.S Y.S) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    IsSliceSubmanifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin (n + 1))) (EuclideanSpace ℝ (Fin p)) (X.S ∪ Y.S) := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  exact isSliceSubmanifold_union_of_isClosed X.hS Y.hS X.isClosed_S Y.isClosed_S hXY

/-- **Disjoint union of framed cobordisms**: `X ∪ Y` is a framed cobordism between the disjoint
unions of the ends. -/
def _root_.Milnor.Framed.FramedCob.union (X : FramedCob hM F₀ F₁) (Y : FramedCob hM G₀ G₁)
    (hXY : Disjoint X.S Y.S) (h0 : Disjoint F₀.N G₀.N) (h1 : Disjoint F₁.N G₁.N) :
    FramedCob hM (F₀.union G₀ h0) (F₁.union G₁ h1) where
  S := X.S ∪ Y.S
  hS := isSliceSubmanifold_cobUnion X Y hXY
  ε := min X.ε Y.ε
  hε := lt_min X.hε Y.hε
  hε' := (min_le_left _ _).trans_lt X.hε'
  end0 q hq := by
    show q ∈ X.S ∪ Y.S ↔ q.1 ∈ F₀.N ∪ G₀.N
    rw [mem_union, mem_union, X.end0 q (hq.trans_le (min_le_left _ _)),
      Y.end0 q (hq.trans_le (min_le_right _ _))]
  end1 q hq := by
    show q ∈ X.S ∪ Y.S ↔ q.1 ∈ F₁.N ∪ G₁.N
    have hX : 1 - X.ε < q.2 := lt_of_le_of_lt (by linarith [min_le_left X.ε Y.ε]) hq
    have hY : 1 - Y.ε < q.2 := lt_of_le_of_lt (by linarith [min_le_right X.ε Y.ε]) hq
    rw [mem_union, mem_union, X.end1 q hX, Y.end1 q hY]
  compact := by
    show IsCompact {q ∈ X.S ∪ Y.S | 0 ≤ q.2 ∧ q.2 ≤ 1}
    have hset : {q ∈ X.S ∪ Y.S | 0 ≤ q.2 ∧ q.2 ≤ 1} =
        {q ∈ X.S | 0 ≤ q.2 ∧ q.2 ≤ 1} ∪ {q ∈ Y.S | 0 ≤ q.2 ∧ q.2 ≤ 1} := sep_union
    rw [hset]
    exact X.compact.union Y.compact
  u i := unionFun (X.u i) (Y.u i)
  smooth i := by
    letI := hM.chartedSpace
    haveI := hM.isManifold
    exact contMDiff_unionFun X.hS Y.hS X.isClosed_S Y.isClosed_S hXY (X.smooth i) (Y.smooth i)
  tangent i q := by
    show (unionFun (X.u i) (Y.u i) q).1 ∈ tangentM hM q.1.1
    by_cases hq : q.1 ∈ X.S
    · rw [unionFun_of_mem_left (X.u i) (Y.u i) q hq]
      exact X.tangent i ⟨q.1, hq⟩
    · have hqY : q.1 ∈ Y.S := Or.resolve_left q.2 hq
      rw [unionFun_of_mem_right hXY (X.u i) (Y.u i) q hqY]
      exact Y.tangent i ⟨q.1, hqY⟩
  normal i q w hw := by
    show ipXR (unionFun (X.u i) (Y.u i) q) w = 0
    by_cases hq : q.1 ∈ X.S
    · rw [unionFun_of_mem_left (X.u i) (Y.u i) q hq]
      rw [tangentS_eq_of_inter_eq hM (isSliceSubmanifold_cobUnion X Y hXY) X.hS
        Y.isClosed_S.isOpen_compl (union_inter_compl_snd X.S Y.S) q
        (Set.disjoint_left.1 hXY hq) hq] at hw
      exact X.normal i ⟨q.1, hq⟩ w hw
    · have hqY : q.1 ∈ Y.S := Or.resolve_left q.2 hq
      rw [unionFun_of_mem_right hXY (X.u i) (Y.u i) q hqY]
      rw [tangentS_eq_of_inter_eq hM (isSliceSubmanifold_cobUnion X Y hXY) Y.hS
        X.isClosed_S.isOpen_compl (union_inter_compl_fst X.S Y.S) q hq hqY] at hw
      exact Y.normal i ⟨q.1, hqY⟩ w hw
  indep q := by
    by_cases hq : q.1 ∈ X.S
    · have : (fun i => unionFun (X.u i) (Y.u i) q) = fun i => X.u i ⟨q.1, hq⟩ :=
        funext fun i => unionFun_of_mem_left (X.u i) (Y.u i) q hq
      show LinearIndependent ℝ (fun i => unionFun (X.u i) (Y.u i) q)
      rw [this]
      exact X.indep _
    · have hqY : q.1 ∈ Y.S := Or.resolve_left q.2 hq
      have : (fun i => unionFun (X.u i) (Y.u i) q) = fun i => Y.u i ⟨q.1, hqY⟩ :=
        funext fun i => unionFun_of_mem_right hXY (X.u i) (Y.u i) q hqY
      show LinearIndependent ℝ (fun i => unionFun (X.u i) (Y.u i) q)
      rw [this]
      exact Y.indep _
  u_end0 i q hq ht := by
    show unionFun (X.u i) (Y.u i) q = ((F₀.union G₀ h0).v i ⟨q.1.1, hq⟩, 0)
    have htX : q.1.2 < X.ε := ht.trans_le (min_le_left _ _)
    have htY : q.1.2 < Y.ε := ht.trans_le (min_le_right _ _)
    by_cases hqX : q.1 ∈ X.S
    · have hF : q.1.1 ∈ F₀.N := (X.end0 q.1 htX).1 hqX
      rw [unionFun_of_mem_left (X.u i) (Y.u i) q hqX, X.u_end0 i ⟨q.1, hqX⟩ hF htX,
        FramedSub.union_v_left i q.1.1 hF hq]
    · have hqY : q.1 ∈ Y.S := Or.resolve_left q.2 hqX
      have hG : q.1.1 ∈ G₀.N := (Y.end0 q.1 htY).1 hqY
      rw [unionFun_of_mem_right hXY (X.u i) (Y.u i) q hqY, Y.u_end0 i ⟨q.1, hqY⟩ hG htY,
        FramedSub.union_v_right i q.1.1 hG hq]
  u_end1 i q hq ht := by
    show unionFun (X.u i) (Y.u i) q = ((F₁.union G₁ h1).v i ⟨q.1.1, hq⟩, 0)
    have htX : 1 - X.ε < q.1.2 := lt_of_le_of_lt (by linarith [min_le_left X.ε Y.ε]) ht
    have htY : 1 - Y.ε < q.1.2 := lt_of_le_of_lt (by linarith [min_le_right X.ε Y.ε]) ht
    by_cases hqX : q.1 ∈ X.S
    · have hF : q.1.1 ∈ F₁.N := (X.end1 q.1 htX).1 hqX
      rw [unionFun_of_mem_left (X.u i) (Y.u i) q hqX, X.u_end1 i ⟨q.1, hqX⟩ hF htX,
        FramedSub.union_v_left i q.1.1 hF hq]
    · have hqY : q.1 ∈ Y.S := Or.resolve_left q.2 hqX
      have hG : q.1.1 ∈ G₁.N := (Y.end1 q.1 htY).1 hqY
      rw [unionFun_of_mem_right hXY (X.u i) (Y.u i) q hqY, Y.u_end1 i ⟨q.1, hqY⟩ hG htY,
        FramedSub.union_v_right i q.1.1 hG hq]

@[simp] theorem _root_.Milnor.Framed.FramedCob.union_S (X : FramedCob hM F₀ F₁)
    (Y : FramedCob hM G₀ G₁) (hXY : Disjoint X.S Y.S) (h0 : Disjoint F₀.N G₀.N)
    (h1 : Disjoint F₁.N G₁.N) : (X.union Y hXY h0 h1).S = X.S ∪ Y.S := rfl

/-- **Disjoint union of framed cobordisms.** -/
theorem framedCobordant_union (X : FramedCob hM F₀ F₁) (Y : FramedCob hM G₀ G₁)
    (hXY : Disjoint X.S Y.S) (h0 : Disjoint F₀.N G₀.N) (h1 : Disjoint F₁.N G₁.N) :
    FramedCobordant hM (F₀.union G₀ h0) (F₁.union G₁ h1) :=
  ⟨X.union Y hXY h0 h1⟩

end unionCob

/-! ### Lemmas 3 and 1 of §7 with the underlying set exposed -/

section homotopy

variable {f g : M → Sph p} {F' : M × ℝ → Sph p} {z : Sph p}

/-- **Lemma 3 of §7 with the underlying set exposed**: the framed cobordism between the
Pontryagin manifolds of `f` and `g` built from the homotopy `F'` is `F'⁻¹(z)`. -/
theorem exists_framedCob_of_homotopy (hnp : n + p = m) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hF' : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ F')
    (hz : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) F' z)
    (hF0 : ∀ x t, t ≤ ε → F' (x, t) = f x) (hF1 : ∀ x t, 1 - ε ≤ t → F' (x, t) = g x)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hzf : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f z)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g)
    (hzg : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g z)
    (b : Fin p → EuclideanSpace ℝ (Fin p)) (hb : LinearIndependent ℝ b) :
    ∃ X : FramedCob hM (pontryagin hM hMc hne hf hzf hnp b hb)
      (pontryagin hM hMc hne hg hzg hnp b hb), X.S = F' ⁻¹' {z} := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  refine ⟨{ S := F' ⁻¹' {z}
            hS := isSliceSubmanifold_levelXR hM hF' hz hnp
            ε := ε
            hε := hε
            hε' := hε'
            end0 := ?_
            end1 := ?_
            compact := ?_
            u := uh hM hMc hne F' z b
            smooth := fun i => contMDiff_uh hM hMc hne hF' hz hnp b i
            tangent := fun i q => uh_tangent hM hMc hne hF' b i q
            normal := fun i q w hw => uh_normal hM hMc hne hF' hz hnp b i q w hw
            indep := fun q => uh_indep hM hMc hne hF' hz hb q
            u_end0 := ?_
            u_end1 := ?_ }, rfl⟩
  · intro q hq
    show F' q = z ↔ f q.1 = z
    rw [← Prod.mk.eta (p := q), hF0 q.1 q.2 hq.le]
  · intro q hq
    show F' q = z ↔ g q.1 = z
    rw [← Prod.mk.eta (p := q), hF1 q.1 q.2 hq.le]
  · have hset : {q ∈ F' ⁻¹' {z} | 0 ≤ q.2 ∧ q.2 ≤ 1} =
        F' ⁻¹' {z} ∩ ({q : M × ℝ | 0 ≤ q.2} ∩ {q | q.2 ≤ 1}) := by
      ext q; simp
    rw [hset]
    refine (isCompact_univ.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset ?_ ?_
    · exact (isClosed_singleton.preimage hF'.continuous).inter
        ((isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd continuous_const))
    · rintro q ⟨-, h1, h2⟩
      exact ⟨mem_univ _, h1, h2⟩
  · intro i q hq ht
    exact uh_end hM hMc hne hF' hf isOpen_Iio (fun x t ht' => hF0 x t (le_of_lt ht')) b i q hq ht
  · intro i q hq ht
    exact uh_end hM hMc hne hF' hg isOpen_Ioi (fun x t ht' => hF1 x t (le_of_lt ht')) b i q hq ht

end homotopy

section detPos

variable {f : M → Sph p} {y : Sph p}

/-- **Lemma 1 of §7, general form, with the underlying set exposed**: the framed cobordism is
`f⁻¹(y) × ℝ`. -/
theorem exists_framedCob_of_det_pos' (hnp : n + p = m)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    {g : M → Sph p} {z : Sph p}
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ g)
    (hz : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) g z)
    {b c : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    (hc : LinearIndependent ℝ c) {A : Matrix (Fin p) (Fin p) ℝ} (hA : 0 < A.det)
    (hN : g ⁻¹' {z} = f ⁻¹' {y})
    (hv : ∀ i (x : M) (hx : x ∈ f ⁻¹' {y}) (hx' : x ∈ g ⁻¹' {z}),
      pontV hM hMc hne g z c i ⟨x, hx'⟩ = pontV hM hMc hne f y (GLp.mulTuple A b) i ⟨x, hx⟩) :
    ∃ X : FramedCob hM (pontryagin hM hMc hne hg hz hnp c hc) (pontryagin hM hMc hne hf hy hnp b hb),
      X.S = {q : M × ℝ | f q.1 = y} := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hε' : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨B, hBs, hB0, hB1, hBind⟩ := GLp.exists_basisPath hb hA hε hε'
  have hF' : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞
      (fun q : M × ℝ => f q.1) := hf.comp contMDiff_fst
  have hz' := isRegularValue_comp_fst hM hf hy
  refine ⟨{ S := (fun q : M × ℝ => f q.1) ⁻¹' {y}
            hS := isSliceSubmanifold_levelXR hM hF' hz' hnp
            ε := 1 / 4
            hε := hε
            hε' := hε'
            end0 := fun q _ => by
              show q.1 ∈ f ⁻¹' {y} ↔ q.1 ∈ g ⁻¹' {z}
              rw [hN]
            end1 := fun q _ => Iff.rfl
            compact := ?_
            u := uht hM hMc hne (fun q : M × ℝ => f q.1) y B
            smooth := fun i => contMDiff_uht hM hMc hne hF' hz' hnp B hBs i
            tangent := fun i q => uh_tangent hM hMc hne hF' (B q.1.2) i q
            normal := fun i q w hw => uh_normal hM hMc hne hF' hz' hnp (B q.1.2) i q w hw
            indep := fun q => uh_indep hM hMc hne hF' hz' (hBind q.1.2) q
            u_end0 := ?_
            u_end1 := ?_ }, rfl⟩
  · have hset : {q ∈ (fun q : M × ℝ => f q.1) ⁻¹' {y} | 0 ≤ q.2 ∧ q.2 ≤ 1} =
        (fun q : M × ℝ => f q.1) ⁻¹' {y} ∩ ({q : M × ℝ | 0 ≤ q.2} ∩ {q | q.2 ≤ 1}) := by
      ext q; simp
    rw [hset]
    refine (isCompact_univ.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset ?_ ?_
    · exact (isClosed_singleton.preimage hF'.continuous).inter
        ((isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd continuous_const))
    · rintro q ⟨-, h1, h2⟩
      exact ⟨mem_univ _, h1, h2⟩
  · intro i q hq ht
    have hq' : q.1.1 ∈ f ⁻¹' {y} := hN ▸ hq
    rw [uht_eq_uh, uh_end hM hMc hne hF' hf isOpen_Iio (fun _ _ _ => rfl) (B q.1.2) i q hq' ht]
    show (pontV hM hMc hne f y (B q.1.2) i ⟨q.1.1, hq'⟩, (0 : ℝ)) =
      (pontV hM hMc hne g z c i ⟨q.1.1, hq⟩, 0)
    rw [hv i q.1.1 hq' hq, hB0 q.1.2 ht.le]
  · intro i q hq ht
    rw [uht_eq_uh, uh_end hM hMc hne hF' hf isOpen_Ioi (fun _ _ _ => rfl) (B q.1.2) i q hq ht]
    show (pontV hM hMc hne f y (B q.1.2) i ⟨q.1.1, hq⟩, (0 : ℝ)) =
      (pontV hM hMc hne f y b i ⟨q.1.1, hq⟩, 0)
    rw [hB1 q.1.2 ht.le]

/-- **Lemma 1 of §7 (constant positive change of basis) with the underlying set exposed**: bases
related by a matrix of positive determinant give framed cobordant Pontryagin manifolds, through
the framed cobordism `f⁻¹(y) × ℝ`. -/
theorem exists_framedCob_of_det_pos (hnp : n + p = m)
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) ∞ f)
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin p)) f y)
    {b b' : Fin p → EuclideanSpace ℝ (Fin p)} (hb : LinearIndependent ℝ b)
    (hb' : LinearIndependent ℝ b') {A : Matrix (Fin p) (Fin p) ℝ} (hA : 0 < A.det)
    (hbA : GLp.mulTuple A b = b') :
    ∃ X : FramedCob hM (pontryagin hM hMc hne hf hy hnp b' hb') (pontryagin hM hMc hne hf hy hnp b hb),
      X.S = {q : M × ℝ | f q.1 = y} :=
  exists_framedCob_of_det_pos' hM hMc hne hnp hf hy hf hy hb hb' hA rfl
    (fun i x hx hx' => by rw [hbA])

end detPos

end Problems

end Milnor
