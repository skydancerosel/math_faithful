import Milnor.Chapter7.CancelFree
import Milnor.Chapter7.Main
import Milnor.Chapter4.Degree

/-!
# The count modulo `2` of a framed `0`-manifold (Milnor §7, p. 50)

**Stage 8 of `Exposition/PlanMod2.md`**, the mod `2` replacement for the signed count of
`Chapter7/Hopf0.lean` and for the classification theorem of `Chapter7/Main.lean`.  Milnor's remark at
the end of §7 (book p. 50) is that on a connected *non-orientable* manifold the signs of the frames
of a framed `0`-manifold are not defined, only their number modulo `2` is an invariant, and two
framed `0`-manifolds with the same number of points modulo `2` are framed cobordant.

Three things are proved.

* **The count** (`Milnor.Framed.countMod2`): the cardinality of the point set of a framed
  `0`-manifold, read in `ZMod 2`.  There is no orientation anywhere in the definition, in contrast
  with `Milnor.Framed.count`.

* **The classification** (`Milnor.Framed.framedCobordant_of_countMod2_eq`): two framed
  `0`-manifolds of a connected `M` with equal counts modulo `2` are framed cobordant.  The proof is
  strong induction on the sum of the two cardinalities: whenever one side has two or more points,
  Stage 7's `Milnor.Framed.exists_neighbour_pair` finds two of them that are neighbours and
  `Milnor.Framed.cancel_step_free` deletes both, which changes that cardinality by `2` and hence not
  the count modulo `2`; when both sides have at most one point the equal counts force equal
  cardinalities, and the two cases `0 = 0` and `1 = 1` are finished by
  `Milnor.Framed.FramedSub.ext'`, in the second case after Stage 6's
  `Milnor.Framed.exists_reach_free` has carried the single point of `F` onto the single point of `G`
  with `G`'s frame.

* **The degree bridge** (`Milnor.Framed.countMod2_pontryagin`): the count modulo `2` of the
  Pontryagin manifold of `f : M → Sᵐ` at a regular value `y` is `Milnor.degMod2` of `f`, the mod `2`
  degree of Chapter 4.  Both are the parity of `#f⁻¹(y)`, so this is bookkeeping: the point set of
  the Pontryagin manifold *is* `f⁻¹(y)`, and `Milnor.degMod2_eq` says that any regular value computes
  the degree.  Nothing about the framing enters, which is why the frame `e` is an arbitrary
  independent tuple rather than a positively oriented basis as in `Milnor.Framed.count_pontryagin`.

## The induction, and why dropping the signs does not break it

In the signed theorem `Milnor.Framed.framedCobordant_of_count_eq` (`Chapter7/Main.lean`) the
induction cancels a point of sign `+1` against a point of sign `-1`, so it can only run while *both*
signs occur; when they do not, the signed count itself pins down the number of points and their
common sign, and the remaining points are gathered together.  Here the cancellation
`Milnor.Framed.cancel_step_free` needs no signs, so the induction runs on the cruder condition "two
or more points", and there is no gathering step at all: it stops only when each side has at most one
point, and one point is carried onto one point.  That is the whole of Milnor's remark, and it goes
through exactly as the plan describes.

## Hypotheses

`0 < m`, `IsCompact M`, `M.Nonempty` and `ConnectedSpace M`, plus the reversing-loop hypothesis

```
hflip : ∀ P : Set M, P.Finite → ∀ x ∉ P, HasReversingBallLoop 𝓘(ℝ, Eᵐ) P x
```

carried in the shape of the plan, which Stage 9 discharges once from Stage 5's punctured dichotomy
`Milnor.hasReversingBallLoop_of_not_isOrientable`.  `2 ≤ m` does not appear here: it is needed only
to produce the loops.  The degree bridge needs no loop and no connectedness of `M`, only the
instances `CompactSpace M` (from `IsCompact M`) and `PreconnectedSpace (Sᵐ)` (from
`Milnor.Sphere.preconnectedSpace`); `T2Space M` and `SecondCountableTopology M` are automatic, `M`
being a subset of a Euclidean space.
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

local notation "Em" => EuclideanSpace ℝ (Fin m)
local notation "EK" => EuclideanSpace ℝ (Fin (K + 1))

/-! ### The count modulo `2` -/

/-- **The count modulo `2` of a framed `0`-manifold**: the number of its points, read in `ZMod 2`.
The unsigned, orientation-free substitute for `Milnor.Framed.count`. -/
def countMod2 (F : FramedSub hM 0 m) : ZMod 2 := (F.finite_N.toFinset.card : ZMod 2)

/-- The count modulo `2` unfolded. -/
theorem countMod2_eq_card (F : FramedSub hM 0 m) :
    countMod2 F = (F.finite_N.toFinset.card : ZMod 2) := rfl

/-- Deleting two points does not change the count modulo `2`. -/
theorem countMod2_of_remove_two {F F' : FramedSub hM 0 m} {x₀ z : M} (hx₀ : x₀ ∈ F.N)
    (hz : z ∈ F.N) (hxz : x₀ ≠ z) (hN : F'.N = F.N \ {x₀, z}) : countMod2 F' = countMod2 F := by
  have hcard := card_of_remove_two hx₀ hz hxz hN
  rw [countMod2_eq_card, countMod2_eq_card, ← hcard, Nat.cast_add, ZMod.natCast_self, add_zero]

/-- The count modulo `2` of a framed `0`-manifold without points is `0`. -/
theorem countMod2_of_empty {F : FramedSub hM 0 m} (h : F.N = ∅) : countMod2 F = 0 := by
  have h' : F.finite_N.toFinset = ∅ := by rw [Set.Finite.toFinset_eq_empty]; exact h
  rw [countMod2_eq_card, h', Finset.card_empty, Nat.cast_zero]

/-! ### Equal counts modulo `2` give framed cobordant framed `0`-manifolds -/

include hMc hne in
/-- **Two framed `0`-manifolds with the same count modulo `2` are framed cobordant** (Milnor's
remark, p. 50).  `M` is connected, and reversing ball loops are available at every point off every
finite set — for a connected non-orientable `M` of dimension at least two this is Stage 5's
punctured dichotomy, and no other hypothesis on `M` is needed.

Strong induction on the sum of the two cardinalities.  If `F` has at least two points, two of them
are neighbours (`Milnor.Framed.exists_neighbour_pair`) and both are cancelled
(`Milnor.Framed.cancel_step_free`); the cardinality drops by two, so the count modulo `2` is
unchanged and the induction hypothesis applies.  Symmetrically for `G`.  Otherwise each of `F` and
`G` has at most one point, and equality of the counts modulo `2` forces equality of the two
cardinalities: either both point sets are empty, and then `F = G` by
`Milnor.Framed.FramedSub.ext'`, or each is a single point, and Stage 6's
`Milnor.Framed.exists_reach_free` carries the point of `F` to the point of `G` — the whole of `M` is
available, the other points of `F` being none — endowed with the frame of `G` there, after which
`Milnor.Framed.FramedSub.ext'` again identifies the result with `G`. -/
theorem framedCobordant_of_countMod2_eq (hm : 0 < m)
    (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    (hflip : letI := hM.chartedSpace; haveI := hM.isManifold;
      ∀ P : Set M, P.Finite → ∀ x ∉ P, HasReversingBallLoop 𝓘(ℝ, Em) P x)
    (F G : FramedSub hM 0 m) (h : countMod2 F = countMod2 G) : FramedCobordant hM F G := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI := hconn
  suffices H : ∀ n : ℕ, ∀ F G : FramedSub hM 0 m,
      F.finite_N.toFinset.card + G.finite_N.toFinset.card = n →
      countMod2 F = countMod2 G → FramedCobordant hM F G by
    exact H _ F G rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F G hn hcount
  -- Case A: `F` has two distinct points
  by_cases hF2 : 1 < F.finite_N.toFinset.card
  · obtain ⟨x, hxF, y, hyF, hxy⟩ := Finset.one_lt_card.1 hF2
    obtain ⟨x₀, hx₀, z, hz, hxz, hnb⟩ := exists_neighbour_pair hconn F
      (F.finite_N.mem_toFinset.1 hxF) (F.finite_N.mem_toFinset.1 hyF) hxy
    obtain ⟨F'', hN'', -, hcob⟩ := cancel_step_free hMc hne hm F hx₀ hz hxz hnb hflip
    have hcard := card_of_remove_two hx₀ hz hxz hN''
    exact hcob.trans (ih (F''.finite_N.toFinset.card + G.finite_N.toFinset.card) (by omega)
      F'' G rfl ((countMod2_of_remove_two hx₀ hz hxz hN'').trans hcount))
  -- Case B: `G` has two distinct points
  by_cases hG2 : 1 < G.finite_N.toFinset.card
  · obtain ⟨x, hxG, y, hyG, hxy⟩ := Finset.one_lt_card.1 hG2
    obtain ⟨x₀, hx₀, z, hz, hxz, hnb⟩ := exists_neighbour_pair hconn G
      (G.finite_N.mem_toFinset.1 hxG) (G.finite_N.mem_toFinset.1 hyG) hxy
    obtain ⟨G'', hN'', -, hcob⟩ := cancel_step_free hMc hne hm G hx₀ hz hxz hnb hflip
    have hcard := card_of_remove_two hx₀ hz hxz hN''
    exact (ih (F.finite_N.toFinset.card + G''.finite_N.toFinset.card) (by omega)
      F G'' rfl (hcount.trans (countMod2_of_remove_two hx₀ hz hxz hN'').symm)).trans hcob.symm
  -- Case C: both have at most one point, hence the same number of points
  rw [not_lt] at hF2 hG2
  have hcard : F.finite_N.toFinset.card = G.finite_N.toFinset.card := by
    rw [countMod2_eq_card, countMod2_eq_card, ZMod.natCast_eq_natCast_iff'] at hcount
    omega
  by_cases hFe : F.N = ∅
  · -- both empty
    have hFc : F.finite_N.toFinset.card = 0 := by
      have h' : F.finite_N.toFinset = ∅ := by rw [Set.Finite.toFinset_eq_empty]; exact hFe
      rw [h', Finset.card_empty]
    have hGe : G.N = ∅ := by
      have h' : G.finite_N.toFinset = ∅ := Finset.card_eq_zero.1 (by omega)
      rwa [Set.Finite.toFinset_eq_empty] at h'
    have heq : F = G := FramedSub.ext' hM (hFe.trans hGe.symm) (fun i x hx _ => by
      rw [hFe] at hx; exact absurd hx (notMem_empty x))
    rw [heq]; exact FramedCobordant.refl' hMc hne G
  · -- one point each
    obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.2 hFe
    have hFpos : 0 < F.finite_N.toFinset.card :=
      Finset.card_pos.2 ⟨x₀, F.finite_N.mem_toFinset.2 hx₀⟩
    obtain ⟨y₀, hy₀⟩ : G.N.Nonempty := by
      obtain ⟨q, hq⟩ := Finset.card_pos.1 (show 0 < G.finite_N.toFinset.card by omega)
      exact ⟨q, G.finite_N.mem_toFinset.1 hq⟩
    -- the two point sets are singletons
    have hFN : F.N = {x₀} := Set.eq_singleton_iff_unique_mem.2 ⟨hx₀, fun q hq =>
      Finset.card_le_one.1 hF2 q (F.finite_N.mem_toFinset.2 hq) x₀
        (F.finite_N.mem_toFinset.2 hx₀)⟩
    have hGN : G.N = {y₀} := Set.eq_singleton_iff_unique_mem.2 ⟨hy₀, fun q hq =>
      Finset.card_le_one.1 hG2 q (G.finite_N.mem_toFinset.2 hq) y₀
        (G.finite_N.mem_toFinset.2 hy₀)⟩
    -- the component of `x₀` in the complement of the other points of `F.N` is all of `M`
    have hdiff : F.N \ {x₀} = ∅ := by rw [hFN]; ext q; simp
    have hcompl : compl' F.N x₀ = Set.univ := by
      simp only [compl', hdiff, Set.compl_empty, connectedComponentIn_univ]
      exact PreconnectedSpace.connectedComponent_eq_univ x₀
    -- carry the point of `F` onto the point of `G`, with `G`'s frame
    obtain ⟨F', hN', -, hv', hcob⟩ := exists_reach_free hMc hne hm F hx₀
      (hflip (F.N \ {x₀}) F.finite_N.sdiff x₀ (fun h => h.2 rfl))
      (y := y₀) (by rw [hcompl]; exact Set.mem_univ y₀)
      (fun i => G.tangent i ⟨y₀, hy₀⟩) (G.indep ⟨y₀, hy₀⟩)
    have hN'' : F'.N = G.N := by rw [hN', hdiff, hGN, Set.empty_union]
    have heq : F' = G := by
      refine FramedSub.ext' hM hN'' ?_
      intro i q hq hq'
      have hqy : q = y₀ := by
        rw [hN'', hGN] at hq; exact hq
      subst hqy
      exact hv' i hq
    rw [← heq]; exact hcob

/-! ### The count modulo `2` of a Pontryagin manifold is the mod `2` degree -/

include hMc hne in
/-- **The count modulo `2` of a Pontryagin manifold is Milnor's mod `2` degree of the map.**  For
`f : M → Sᵐ` smooth with regular value `y` and any independent tuple `e` of `ℝᵐ`, the framed
`0`-manifold `Milnor.Framed.pontryagin` of `f` at `y` framed by `e` has `Milnor.Framed.countMod2`
equal to `Milnor.degMod2 f`.

Both sides are the parity of the number of points of `f⁻¹(y)`: the point set of the Pontryagin
manifold is `f⁻¹(y)` by definition, `Milnor.degMod2_eq` evaluates the degree at the regular value `y`
as the parity of `Set.ncard (f ⁻¹' {y})`, and `Set.ncard_eq_toFinset_card` matches the two ways of
counting a finite set.  No orientation and no frame condition occur; contrast
`Milnor.Framed.count_pontryagin`, where the frame must be a positively oriented basis of the tangent
space of the sphere at `y`. -/
theorem countMod2_pontryagin (hm : 0 < m) {f : M → Sph m}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, Em) 𝓘(ℝ, Em) ∞ f)
    {y : Sph m}
    (hy : letI := hM.chartedSpace; haveI := hM.isManifold;
      IsRegularValue 𝓘(ℝ, Em) 𝓘(ℝ, Em) f y)
    (e : Fin m → EuclideanSpace ℝ (Fin m)) (he : LinearIndependent ℝ e) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    countMod2 (pontryagin hM hMc hne hf hy (zero_add m) e he) =
      degMod2 𝓘(ℝ, Em) 𝓘(ℝ, Em) f := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  haveI : PreconnectedSpace (Sph m) := preconnectedSpace hm
  have hcard : (pontryagin hM hMc hne hf hy (zero_add m) e he).finite_N.toFinset.card =
      (f ⁻¹' {y}).ncard :=
    (Set.ncard_eq_toFinset_card (f ⁻¹' {y})
      (pontryagin hM hMc hne hf hy (zero_add m) e he).finite_N).symm
  rw [countMod2_eq_card, degMod2_eq rfl hf hy, hcard]

end Framed

end Milnor
