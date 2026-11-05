import Milnor.Chapter7.CountMod2
import Milnor.Chapter7.OneManifoldOrientable
import Milnor.Chapter7.ThmAconv

/-!
# Milnor's mod `2` theorem at the end of §7 (book p. 50)

**Stage 9, the last, of `Exposition/PlanMod2.md`.**  Milnor closes §7 with a theorem he states
without proof: *if `M` is connected but non-orientable, then two smooth maps `M → Sᵐ` are smoothly
homotopic if and only if they have the same degree modulo `2`* (book p. 50).  The reason he gives is
one clause long — sliding a point around an orientation-reversing loop changes the sign of its frame,
so only the parity of the number of points of a framed `0`-manifold survives — and that clause is
Stages 1–8 of the plan.  Here the pieces are assembled.

Four statements.

* **Homotopy invariance** (`Milnor.degMod2_eq_of_smoothHomotopic`, and for maps to the sphere
  `Milnor.Framed.degMod2_eq_of_smoothHomotopic_sph`): smoothly homotopic maps have the same degree
  modulo `2`.  This is Theorem A of Chapter 4 (`Milnor.degMod2_eq_of_homotopy`), which is stated
  there for a raw smooth map `M × ℝ → N` and its two end slices, transcribed into the relation
  `Milnor.SmoothHomotopic` of `Chapter7/Homotopy.lean`.  **No orientability of any kind enters**, of
  `M` or of the sphere, and no dimension hypothesis beyond the ones `Milnor.degMod2` itself needs:
  `M` compact, the target connected — for the sphere `Sᵐ` that is `0 < m` — and the two dimensions
  equal.

* **Framed `0`-manifolds are classified by the parity of their number of points**
  (`Milnor.Framed.framedCobordant_of_card_parity`): on a compact connected non-orientable `M`, two
  framed `0`-manifolds whose numbers of points agree modulo `2` are framed cobordant.  This is Stage
  8's `Milnor.Framed.framedCobordant_of_countMod2_eq` with its reversing-loop hypothesis discharged,
  in one line, by Stage 5's punctured dichotomy `Milnor.hasReversingBallLoop_of_not_isOrientable`.

* **The converse half, which is Milnor's remark**
  (`Milnor.Framed.smoothHomotopic_of_degMod2_eq`): for a compact connected non-orientable `M` of
  dimension `m`, two smooth maps `M → Sᵐ` with the same degree modulo `2` are smoothly homotopic.
  The route is the skeleton of `Milnor.Framed.hopf_homotopic` with the signed count replaced by the
  count modulo `2` and with no orientation of `M` anywhere: a regular value for each map (Sard, via
  `Milnor.dense_regularValues`), a positively oriented basis of the sphere at each of them
  (`Milnor.Framed.exists_posBasis` — orientations of the *sphere* are still needed, and are the only
  orientations in the argument), the two Pontryagin manifolds, the bridge
  `Milnor.Framed.countMod2_pontryagin` turning equality of the degrees modulo `2` into equality of
  the counts modulo `2`, the classification above, and finally the converse half of Theorem B of §7,
  `Milnor.Framed.smoothHomotopic_of_framedCobordant`, which likewise needs orientations only on the
  sphere.

* **The theorem as Milnor states it** (`Milnor.Framed.hopf_homotopic_mod2`): for a closed connected
  non-orientable `M` of dimension `m`, two smooth maps `M → Sᵐ` are smoothly homotopic *if and only
  if* they have the same degree modulo `2`.  The two directions are the first and third statements
  above.

## No dimension hypothesis

Earlier versions of this file carried `2 ≤ m` in every statement that mentions non-orientability,
because `2 ≤ m` is what Stage 5's `Milnor.hasReversingBallLoop_of_not_isOrientable` wants (there it
keeps the complement of a finite set connected and lets an orientation be extended across the
punctures).  **The hypothesis was empty mathematics**: a connected `1`-manifold is diffeomorphic to
the circle or to an interval and all of those are orientable, so a connected non-orientable manifold
has dimension at least two, and `hnor` already implies `2 ≤ m`.

It is no longer assumed.  `Milnor/Chapter7/OneManifoldOrientable.lean` proves that a connected
`σ`-compact Hausdorff one-manifold is orientable — on top of the classification of one-manifolds,
`Milnor/Appendix/Smooth/Main.lean` — and deduces
`Milnor.two_le_of_not_isOrientable_slice`: a compact connected non-orientable slice submanifold of a
Euclidean space has dimension at least two.  Each theorem below that has `hnor` among its hypotheses
now derives `2 ≤ m` from it in one line.
-/

open Set Filter Topology Function Module Metric
open scoped ContDiff Manifold RealInnerProductSpace Classical

noncomputable section

namespace Milnor

/-! ### Homotopy invariance of the degree modulo `2` for the relation `SmoothHomotopic` -/

section Invariance

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

/-- **Smoothly homotopic maps have the same degree modulo `2`** (Milnor, Theorem A of §4, p. 21),
stated for the relation `Milnor.SmoothHomotopic` of `Chapter7/Homotopy.lean` rather than for a raw
map `M × ℝ → N` and its two end slices as in `Milnor.degMod2_eq_of_homotopy`.  A homotopy from `f` to
`g` *is* such a raw map whose slices at the times `0` and `1` are `f` and `g`, so this is only a
change of phrasing.

No orientation of `M` or of `N` occurs: the mod `2` degree is defined without any, which is the whole
point of Chapter 4 and the reason this half of Milnor's mod `2` theorem is free. -/
theorem degMod2_eq_of_smoothHomotopic [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [T2Space N] [PreconnectedSpace N] (hdim : finrank ℝ E = finrank ℝ F) {f g : M → N}
    (h : SmoothHomotopic I J f g) : degMod2 I J f = degMod2 I J g := by
  obtain ⟨Hm, hH, h0, h1⟩ := h
  have e0 : f = fun x => Hm (x, 0) := funext fun x => (h0 x).symm
  have e1 : g = fun x => Hm (x, 1) := funext fun x => (h1 x).symm
  rw [e0, e1]
  exact degMod2_eq_of_homotopy hdim hH

end Invariance

open Sphere

namespace Framed

variable {K m w : ℕ} {M : Set (EuclideanSpace ℝ (Fin (K + 1)))}
  (hM : IsSliceSubmanifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (K + 1))) (EuclideanSpace ℝ (Fin m))
    (EuclideanSpace ℝ (Fin w)) M) (hMc : IsCompact M) (hne : M.Nonempty)

local notation "Em" => EuclideanSpace ℝ (Fin m)

/-! ### The easy half: homotopic maps to the sphere have the same degree modulo `2` -/

include hMc in
/-- **Smoothly homotopic maps `M → Sᵐ` have the same degree modulo `2`**, for `M` a compact
`m`-dimensional submanifold of a Euclidean space and `0 < m`.

This is `Milnor.degMod2_eq_of_smoothHomotopic` read in the vocabulary of §7; the instances it wants
are `CompactSpace M`, from `IsCompact M`, and `PreconnectedSpace (Sᵐ)`, from
`Milnor.Sphere.preconnectedSpace`, which is where `0 < m` is spent — the `0`-sphere is two points and
has no connected target to offer.  `M` need be neither connected nor orientable, and `M.Nonempty` is
not used. -/
theorem degMod2_eq_of_smoothHomotopic_sph (hm : 0 < m) {f g : M → Sph m}
    (h : letI := hM.chartedSpace; haveI := hM.isManifold;
      SmoothHomotopic 𝓘(ℝ, Em) 𝓘(ℝ, Em) f g) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    degMod2 𝓘(ℝ, Em) 𝓘(ℝ, Em) f = degMod2 𝓘(ℝ, Em) 𝓘(ℝ, Em) g := by
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  haveI : PreconnectedSpace (Sph m) := preconnectedSpace hm
  exact degMod2_eq_of_smoothHomotopic rfl h

/-! ### Framed `0`-manifolds of a connected non-orientable manifold, classified by parity -/

include hMc hne in
/-- **Framed `0`-manifolds of a connected non-orientable manifold are classified by the parity of
the number of points** (Milnor, p. 50).  If `M` is compact, nonempty, connected and *not* orientable,
then two framed `0`-manifolds of `M` whose numbers of points agree in `ZMod 2` are framed cobordant.

This is Stage 8's `Milnor.Framed.framedCobordant_of_countMod2_eq`, whose hypothesis is the existence
of a reversing loop of chart balls at every point off every finite set, with that hypothesis
discharged by Stage 5's punctured dichotomy `Milnor.hasReversingBallLoop_of_not_isOrientable`: the
non-orientability of `M` is used for nothing else, here or downstream.

No dimension hypothesis is needed.  Stage 5 wants `2 ≤ m`, and that is supplied by
`Milnor.two_le_of_not_isOrientable_slice`, which derives it from `hnor` and `hconn` through the
classification of one-manifolds; see the module docstring. -/
theorem framedCobordant_of_card_parity
    (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    (hnor : letI := hM.chartedSpace; ¬ IsOrientable 𝓘(ℝ, Em) M m)
    (F G : FramedSub hM 0 m)
    (h : (F.finite_N.toFinset.card : ZMod 2) = (G.finite_N.toFinset.card : ZMod 2)) :
    FramedCobordant hM F G := by
  have hm2 : 2 ≤ m := two_le_of_not_isOrientable_slice hM hMc hconn hnor
  letI := hM.chartedSpace
  haveI := hM.isManifold
  haveI := hconn
  have hflip : ∀ P : Set M, P.Finite → ∀ x ∉ P, HasReversingBallLoop 𝓘(ℝ, Em) P x :=
    fun P hP x hx => hasReversingBallLoop_of_not_isOrientable finrank_E hm2 hnor hP hx
  exact framedCobordant_of_countMod2_eq hMc hne (by omega) hconn hflip F G h

/-! ### The converse half: equal degrees modulo `2` give a homotopy -/

include hMc hne in
/-- **Milnor's remark at the end of §7 (p. 50), the substantial half**: on a compact connected
*non-orientable* `M` of dimension `m`, two smooth maps `M → Sᵐ` with the same degree modulo `2` are
smoothly homotopic.

The proof is the skeleton of the oriented Hopf theorem `Milnor.Framed.hopf_homotopic` with the signed
count of `Chapter7/Hopf0.lean` replaced by the count modulo `2` of Stage 8 and with **no orientation
of `M` anywhere**.  Sard's theorem, in the form `Milnor.dense_regularValues`, gives a regular value
`y` of `f` and a regular value `y'` of `g`; `Milnor.Framed.exists_posBasis` gives bases of `ℝᵐ`
positively oriented for the orientation of the sphere at `y` and at `y'` — orientations of the
sphere, which both the Pontryagin construction and the converse of Theorem B require and which are
the only orientations occurring; `Milnor.Framed.countMod2_pontryagin` says that the count modulo `2`
of each Pontryagin manifold is the mod `2` degree of the corresponding map, so the hypothesis
`hdeg` says exactly that the two Pontryagin manifolds have the same count modulo `2`;
`Milnor.Framed.framedCobordant_of_card_parity` makes them framed cobordant; and
`Milnor.Framed.smoothHomotopic_of_framedCobordant` — Theorem B of §7 in the direction that needs no
orientation of `M` — turns the framed cobordism into a homotopy.

No dimension hypothesis is needed: `0 < m`, which the Pontryagin construction wants, comes from
`Milnor.two_le_of_not_isOrientable_slice`; see the module docstring. -/
theorem smoothHomotopic_of_degMod2_eq
    (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    (hnor : letI := hM.chartedSpace; ¬ IsOrientable 𝓘(ℝ, Em) M m)
    {f g : M → Sph m}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, Em) 𝓘(ℝ, Em) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, Em) 𝓘(ℝ, Em) ∞ g)
    (hdeg : letI := hM.chartedSpace; haveI := hM.isManifold;
      degMod2 𝓘(ℝ, Em) 𝓘(ℝ, Em) f = degMod2 𝓘(ℝ, Em) 𝓘(ℝ, Em) g) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    SmoothHomotopic 𝓘(ℝ, Em) 𝓘(ℝ, Em) f g := by
  have hm2 : 2 ≤ m := two_le_of_not_isOrientable_slice hM hMc hconn hnor
  letI := hM.chartedSpace
  haveI := hM.isManifold
  have hm : 0 < m := by omega
  obtain ⟨y, hy⟩ := (dense_regularValues hf).nonempty
  obtain ⟨y', hy'⟩ := (dense_regularValues hg).nonempty
  obtain ⟨e, he⟩ := exists_posBasis hm y
  obtain ⟨e', he'⟩ := exists_posBasis hm y'
  have h1 := countMod2_pontryagin (hM := hM) hMc hne hm hf hy e e.linearIndependent
  have h2 := countMod2_pontryagin (hM := hM) hMc hne hm hg hy' e' e'.linearIndependent
  have hcard : countMod2 (pontryagin hM hMc hne hf hy (zero_add m) e e.linearIndependent) =
      countMod2 (pontryagin hM hMc hne hg hy' (zero_add m) e' e'.linearIndependent) := by
    rw [h1, h2]; exact hdeg
  have hcob := framedCobordant_of_card_parity hM hMc hne hconn hnor
    (pontryagin hM hMc hne hf hy (zero_add m) e e.linearIndependent)
    (pontryagin hM hMc hne hg hy' (zero_add m) e' e'.linearIndependent) hcard
  exact smoothHomotopic_of_framedCobordant hM hMc hne (zero_add m) hm hf hg hy hy' e he e' he' hcob

/-! ### Milnor's theorem -/

include hMc hne in
/-- **Milnor's theorem at the end of §7 (book p. 50).**  Let `M` be a closed connected
*non-orientable* smooth `m`-dimensional submanifold of a Euclidean space.  Then two smooth maps
`f g : M → Sᵐ` are smoothly homotopic **if and only if** they have the same degree modulo `2`.

The forward direction is `Milnor.Framed.degMod2_eq_of_smoothHomotopic_sph`, Chapter 4's homotopy
invariance of the mod `2` degree, and uses neither the connectedness nor the non-orientability of `M`
beyond the `0 < m` they give.  The backward direction is
`Milnor.Framed.smoothHomotopic_of_degMod2_eq`, Milnor's remark, and uses all of them.

**No dimension hypothesis.**  Both directions want `0 < m`, and both get it from
`Milnor.two_le_of_not_isOrientable_slice`: a connected `1`-manifold is diffeomorphic to the circle or
to an interval, hence orientable, so a connected non-orientable manifold automatically has dimension
at least two.  That is proved in `Milnor/Chapter7/OneManifoldOrientable.lean` on top of the
classification of one-manifolds of `Milnor/Appendix/Smooth/Main.lean`; see the module docstring. -/
theorem hopf_homotopic_mod2
    (hconn : letI := hM.chartedSpace; ConnectedSpace M)
    (hnor : letI := hM.chartedSpace; ¬ IsOrientable 𝓘(ℝ, Em) M m)
    {f g : M → Sph m}
    (hf : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, Em) 𝓘(ℝ, Em) ∞ f)
    (hg : letI := hM.chartedSpace; haveI := hM.isManifold;
      ContMDiff 𝓘(ℝ, Em) 𝓘(ℝ, Em) ∞ g) :
    letI := hM.chartedSpace; haveI := hM.isManifold;
    SmoothHomotopic 𝓘(ℝ, Em) 𝓘(ℝ, Em) f g ↔
      degMod2 𝓘(ℝ, Em) 𝓘(ℝ, Em) f = degMod2 𝓘(ℝ, Em) 𝓘(ℝ, Em) g := by
  have hm2 : 2 ≤ m := two_le_of_not_isOrientable_slice hM hMc hconn hnor
  letI := hM.chartedSpace
  haveI := hM.isManifold
  exact ⟨fun h => degMod2_eq_of_smoothHomotopic_sph hM hMc (by omega) h,
    fun h => smoothHomotopic_of_degMod2_eq hM hMc hne hconn hnor hf hg h⟩

end Framed

end Milnor
