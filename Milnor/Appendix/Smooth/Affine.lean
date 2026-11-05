import Milnor.Appendix.Smooth.ArcLength
import Milnor.Appendix.TwoComponents

/-!
# Milnor's Appendix, smooth version: the transition of two unit-speed arcs is affine

Milnor, *Topology from the Differentiable Viewpoint*, Appendix (book p. 54), classifies the
connected one-manifolds.  This file is **Stage 5** of the plan `Exposition/PlanOneManifold.md`, and
it is the keystone of the design: it is the only stage that makes an *extension* of an arc a genuine
extension, which is what unlocks both the maximality argument of the non-compact case and the exact
period of the circle.

## Which part is Milnor's Lemma 1

Milnor's Appendix has one lemma, stated for arc-length parametrizations `f : U → M`, `g : V → M` of
a one-manifold: *the overlap `f⁻¹(g(V))` has at most two components, on each of which
`g⁻¹ ∘ f` is `s ↦ ±s + c`; and if there are two components, they reach opposite ends.*  The two
halves live in two files:

* the **topological half** -- at most two components, and opposite ends -- is
  `Milnor/Appendix/TwoComponents.lean` (Stage 2), which needs no smoothness at all;
* the **affine half** -- `s ↦ ±s + c` on each component -- is this file, `exists_affine_trans`.

`milnor_lemma_one` below is the two halves conjoined, and **that theorem is Milnor's Lemma 1 in
full**.  Nothing else in this file is part of his lemma; the extension theorem is his Step 2, which
his text carries out in words.

## What is proved

**The affine half of Lemma 1.**

* `abs_transDeriv_eq_one`: for two unit-speed arcs the derivative of the transition, taken *within*
  the (possibly half-open) target, has absolute value `1` at every parameter of the overlap,
  endpoints included.  One line from the cocycle rule of the length element: read in a unit-speed
  parameter the density is `1`, so `1 = 1 · |τ'|`.
* `exists_sign_transDeriv`: on a connected piece of the overlap the transition derivative is
  *constantly* `+1` or constantly `-1` -- it is continuous (Stage 3's `contDiffOn_transDeriv`) and
  omits `0`, so the intermediate value theorem forbids it from changing sign.
* `exists_affine_trans`: hence on each component the transition is `s ↦ ε s + k` with `ε = ±1`,
  by the mean value theorem in the form `sub_eq_mul_sub_of_hasDerivWithinAt`.
* `milnor_lemma_one`: **Milnor's Appendix Lemma 1**, the affine half joined to Stage 2's topological
  half.

**The extension theorem for unit-speed arcs**, the point of the whole design.

* `exists_extension_aux_unitSpeed` and `exists_extension_unitSpeed` re-prove the existing
  `Milnor.OneManifold.exists_extension_aux` and `Milnor.OneManifold.exists_extension` with three
  additions: the glued arc is a `SmoothArc`, it has unit speed, and -- the strong form that the
  affine glue makes true -- **it agrees with the first arc on the whole of the first arc's source**,
  so it genuinely extends it rather than merely containing its image up to reparametrization.

The gluing formula is the existing one: the new coordinate is `A.toFun` on `A.source` and
`c + (A'.toFun · - d)` beyond it.  What the affine half of Lemma 1 buys is that these two formulas
agree *on the whole overlap*, not just in the limit: `hFA'` below says the second formula is valid
on all of `A'.source`.  So the glued coordinate is a smooth function on each of two open sets, and
**there is no seam** -- the seventy lines of one-sided limits that the topological proof spends on
continuity at the junction disappear, and the smoothness obligations cost a few lines each.

## Why the extension is a genuine extension

The strong form is not a bonus; it is forced.  Because the transition between two unit-speed arcs is
`s ↦ ±s + k`, and because the normalization pins down both the direction (`+`) and the constant
(`k = c - d`, from `sSup` of the overlap seen from either side), the old parameter *is* the new
parameter on the old source.  A merely monotone transition would leave `k` and the shape of the
reparametrization free, the glued coordinate would differ from the old one past the junction,
and the poset of arcs ordered by restriction would have no useful chains.  This is the sharp
reason Milnor states his lemma for arc-length parametrizations, not for arbitrary charts.

## What had to be restated, and why

`Milnor.OneManifold.exists_extension_aux` concludes with an *existential* over topological arcs, and
its conclusion records only `A.source ⊆ Ã.source`, not `Ã.toFun = A.toFun` on `A.source`, and not
`Ã.source = A.source ∪ A'.source`.  Neither missing fact can be recovered from the statement: a
topological arc containing `A` may reparametrize it by any increasing homeomorphism.  So the two
theorems are restated here rather than applied.  Everything *below* them is reused verbatim from
`Milnor/Appendix/OneManifold.lean` -- `overlap_ordConnected`, `end_left`, `end_right`,
`trans_zero_eq_sInf_or_sSup`, the hull API, the monotonicity dichotomy -- and the restated proofs
follow the original line for line down to the junction, where the affine half of Lemma 1 replaces
the limit arguments.

## Hypotheses

The affine half needs: a manifold `M` charted on a model with corners `I : ModelWithCorners ℝ E H`
over a real normed space `E`, two `C^∞` smooth arcs, a length element `L`, and unit speed for both.
**No dimension hypothesis, no Hausdorffness, no compactness, no boundarylessness.**  (A length
element exists when `M` is Hausdorff and σ-compact and `finrank ℝ E = 1`, by Stage 3, but that is
the only place those hypotheses are used, and here `L` is an argument.)

`milnor_lemma_one` and the two extension theorems add `T2Space M`, because the topological half of
Lemma 1 and the `overlap`/`trans` API of the existing file are stated for Hausdorff spaces.  The
extension theorems also inherit the existing normalization hypotheses: the first arc starts at a
boundary point with coordinate `0` and target `Ico 0 c`.

## References

* Milnor, *Topology from the Differentiable Viewpoint*, Appendix, p. 54 (Lemma 1 and its use).
* `Exposition/PlanOneManifold.md`, Stage 5 and §4.
-/

open Set Filter Topology

open scoped ContDiff Manifold

noncomputable section

namespace Milnor.OneManifold.Smooth

/-! ## A function with constant derivative on an interval is affine

The mean value theorem in the only form this file needs.  The derivative is taken *within* the
interval, which may be half-open, so the statement applies at an endpoint of an arc's target.
-/

/-- **A real function whose derivative within an order-connected set is the constant `ε` has
increments `ε · (t - s)`** -- that is, it is affine with slope `ε` there.

The derivative is a `derivWithin`, so the two endpoints of the set are allowed and the one-sided
derivative is what is assumed.  The proof restricts to the compact subinterval `Icc s t` --
contained in the set because the set is order-connected -- where `uniqueDiffOn_Icc` makes
`derivWithin` unambiguous and Mathlib's `constant_of_derivWithin_zero` applies to
`u ↦ f u - ε u`. -/
theorem sub_eq_mul_sub_of_hasDerivWithinAt {f : ℝ → ℝ} {C : Set ℝ} {ε : ℝ} (hC : C.OrdConnected)
    (hd : ∀ u ∈ C, HasDerivWithinAt f ε C u) {s t : ℝ} (hs : s ∈ C) (ht : t ∈ C) :
    f t - f s = ε * (t - s) := by
  have key : ∀ a ∈ C, ∀ b ∈ C, a ≤ b → f b - f a = ε * (b - a) := by
    intro a ha b hb hab
    have hIcc : Icc a b ⊆ C := hC.out ha hb
    have hgd : ∀ u ∈ Icc a b, HasDerivWithinAt (fun v : ℝ => f v - ε * v) 0 (Icc a b) u := by
      intro u hu
      have h1 : HasDerivWithinAt f ε (Icc a b) u := (hd u (hIcc hu)).mono hIcc
      have h2 : HasDerivWithinAt (fun v : ℝ => ε * v) ε (Icc a b) u := by
        simpa using HasDerivWithinAt.const_mul ε (hasDerivWithinAt_id u (Icc a b))
      have h3 : HasDerivWithinAt (fun v : ℝ => f v - ε * v) (ε - ε) (Icc a b) u := h1.sub h2
      rw [sub_self] at h3
      exact h3
    have hdiff : DifferentiableOn ℝ (fun v : ℝ => f v - ε * v) (Icc a b) := fun u hu =>
      (hgd u hu).differentiableWithinAt
    have hzero : ∀ u ∈ Ico a b, derivWithin (fun v : ℝ => f v - ε * v) (Icc a b) u = 0 := by
      intro u hu
      have hab' : a < b := hu.1.trans_lt hu.2
      exact (hgd u (Ico_subset_Icc_self hu)).derivWithin
        (uniqueDiffOn_Icc hab' u (Ico_subset_Icc_self hu))
    have hconst := constant_of_derivWithin_zero hdiff hzero b (right_mem_Icc.2 hab)
    linear_combination hconst
  rcases le_total s t with h | h
  · exact key s hs t ht h
  · have := key t ht s hs h
    linarith

/-! ## The affine half of Milnor's Lemma 1 -/

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The transition between two unit-speed arcs has derivative of absolute value `1`.**

At a parameter `u` of the first arc whose point also lies in the source of the second, the cocycle
rule of the length element reads `ρ u = ρ' (τ u) · |τ' u|` with `ρ` and `ρ'` the density in the two
parameters; unit speed makes both densities `1`, so `|τ' u| = 1`.

The derivative is taken within the first arc's target, which may be half-open, and `u` may be an
endpoint of it; it is unambiguous there because an arc target is convex with nonempty interior.

Hypotheses: two `C^∞` smooth arcs and a length element for which both have unit speed.  No dimension
hypothesis, no Hausdorffness, no compactness. -/
theorem abs_transDeriv_eq_one {L : LengthElement I ∞ M} {A A' : SmoothArc I ∞ M}
    (hA : UnitSpeed L A) (hA' : UnitSpeed L A') {u : ℝ} (hu : u ∈ A.target)
    (hx : A.invFun u ∈ A'.source) :
    |transDeriv A.toRealChart A'.toRealChart u| = 1 := by
  have hone : L.fn A'.toRealChart (A'.toFun (A.invFun u)) = 1 := hA' _ (A'.map_source hx)
  have hcoc := L.cocycle A.toRealChart A'.toRealChart u hu hx
  simp only [SmoothArc.toRealChart_toFun, SmoothArc.toRealChart_invFun] at hcoc
  rw [hA u hu, hone] at hcoc
  simpa using hcoc.symm

/-- **The transition derivative of two unit-speed arcs is `+1` or `-1`** at every parameter of the
overlap.  Immediate from `abs_transDeriv_eq_one`. -/
theorem transDeriv_eq_one_or_eq_neg_one {L : LengthElement I ∞ M} {A A' : SmoothArc I ∞ M}
    (hA : UnitSpeed L A) (hA' : UnitSpeed L A') {u : ℝ} (hu : u ∈ A.target)
    (hx : A.invFun u ∈ A'.source) :
    transDeriv A.toRealChart A'.toRealChart u = 1 ∨
      transDeriv A.toRealChart A'.toRealChart u = -1 :=
  abs_eq (zero_le_one' ℝ) |>.1 (abs_transDeriv_eq_one hA hA' hu hx)

/-- **The transition derivative is continuous on the overlap**, endpoints of a half-open target
included: Stage 3's `contDiffOn_transDeriv` at order `0`. -/
theorem continuousOn_transDeriv (A A' : SmoothArc I ∞ M) :
    ContinuousOn (transDeriv A.toRealChart A'.toRealChart)
      (A.target ∩ A.invFun ⁻¹' A'.source) :=
  (contDiffOn_transDeriv (n := ∞) (by simp) (m := 0) (by norm_num)
    A.toRealChart A'.toRealChart).continuousOn

/-- **On a connected piece of the overlap the sign of the transition derivative is constant.**

The derivative is continuous and takes only the values `±1`; if it took both on an order-connected
set, the intermediate value theorem would give a parameter at which it is `0`, contradicting
`abs_transDeriv_eq_one`.

`C` is any order-connected subset of the overlap -- in the application it is a component, i.e. a
`hull` of the overlap. -/
theorem exists_sign_transDeriv {L : LengthElement I ∞ M} {A A' : SmoothArc I ∞ M}
    (hA : UnitSpeed L A) (hA' : UnitSpeed L A') {C : Set ℝ}
    (hCsub : C ⊆ A.target ∩ A.invFun ⁻¹' A'.source) (hCoc : C.OrdConnected) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ s ∈ C, transDeriv A.toRealChart A'.toRealChart s = ε := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨1, Or.inl rfl, by simp⟩
  refine ⟨transDeriv A.toRealChart A'.toRealChart s₀,
    transDeriv_eq_one_or_eq_neg_one hA hA' (hCsub hs₀).1 (hCsub hs₀).2, fun t ht => ?_⟩
  by_contra hne
  -- the derivative takes the two values `1` and `-1` at `t` and `s₀`, hence `0` in between
  have hcont : ContinuousOn (transDeriv A.toRealChart A'.toRealChart) (uIcc t s₀) :=
    (continuousOn_transDeriv A A').mono ((hCoc.uIcc_subset ht hs₀).trans hCsub)
  have hzero : (0 : ℝ) ∈ transDeriv A.toRealChart A'.toRealChart '' uIcc t s₀ := by
    refine intermediate_value_uIcc hcont ?_
    rcases transDeriv_eq_one_or_eq_neg_one hA hA' (hCsub ht).1 (hCsub ht).2 with h | h <;>
      rcases transDeriv_eq_one_or_eq_neg_one hA hA' (hCsub hs₀).1 (hCsub hs₀).2 with h' | h'
    · exact absurd (h.trans h'.symm) hne
    · rw [h, h']; norm_num [Set.mem_uIcc]
    · rw [h, h']; norm_num [Set.mem_uIcc]
    · exact absurd (h.trans h'.symm) hne
  obtain ⟨v, hv, hv0⟩ := hzero
  have hvC : v ∈ C := hCoc.uIcc_subset ht hs₀ hv
  have habs := abs_transDeriv_eq_one hA hA' (hCsub hvC).1 (hCsub hvC).2
  rw [hv0] at habs
  simp at habs

/-- **The affine half of Milnor's Appendix Lemma 1: on each connected piece of the overlap the
transition between two unit-speed arcs is `s ↦ ε s + k` with `ε = ±1`.**

The derivative is constantly `ε = ±1` there by `exists_sign_transDeriv`, and a function with
constant derivative within an order-connected set is affine by `sub_eq_mul_sub_of_hasDerivWithinAt`.
Both statements are valid at an endpoint of a half-open target, so the conclusion holds on a closed
end of the overlap as well.

`C` is any order-connected subset of the overlap; taking `C` to be a component of the overlap and
combining with Stage 2 gives `milnor_lemma_one`.

Hypotheses: two `C^∞` smooth arcs and a length element for which both have unit speed.  No dimension
hypothesis, no Hausdorffness, no compactness. -/
theorem exists_affine_trans {L : LengthElement I ∞ M} {A A' : SmoothArc I ∞ M}
    (hA : UnitSpeed L A) (hA' : UnitSpeed L A') {C : Set ℝ}
    (hCsub : C ⊆ A.target ∩ A.invFun ⁻¹' A'.source) (hCoc : C.OrdConnected) :
    ∃ ε k : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ s ∈ C, A'.toFun (A.invFun s) = ε * s + k := by
  obtain ⟨ε, hε, hsign⟩ := exists_sign_transDeriv hA hA' hCsub hCoc
  rcases C.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨ε, 0, hε, by simp⟩
  refine ⟨ε, A'.toFun (A.invFun s₀) - ε * s₀, hε, fun t ht => ?_⟩
  have hd : ∀ u ∈ C, HasDerivWithinAt (fun s => A'.toFun (A.invFun s)) ε C u := by
    intro u hu
    have h := hasDerivWithinAt_trans (n := ∞) (by simp) A.toRealChart A'.toRealChart
      (hCsub hu).1 (hCsub hu).2
    rw [hsign u hu] at h
    exact h.mono (hCsub.trans inter_subset_left)
  have hkey := sub_eq_mul_sub_of_hasDerivWithinAt hCoc hd hs₀ ht
  linear_combination hkey

/-- **Unit speed survives reversal of the parameter.**  The transition from `A.neg` to `A` is
`s ↦ -s`, whose derivative is `-1`, so the cocycle rule turns the density `1` of `A` into the
density `1` of `A.neg`.  This is what lets the extension theorem remove the normalization by
negating the second arc's coordinate. -/
theorem UnitSpeed.neg {L : LengthElement I ∞ M} {A : SmoothArc I ∞ M} (hA : UnitSpeed L A) :
    UnitSpeed L A.neg := by
  intro u hu
  have hut : -u ∈ A.target := by simpa using hu
  have hval : A.toFun (A.neg.invFun u) = -u := A.right_inv hut
  have hsrc : A.neg.invFun u ∈ A.source := A.map_target hut
  -- the transition is `s ↦ -s` on `A.neg.target`, so its derivative within that target is `-1`
  have hderiv : transDeriv A.neg.toRealChart A.toRealChart u = -1 := by
    have hid : HasDerivWithinAt (fun s : ℝ => A.toFun (A.neg.invFun s)) (-1) A.neg.target u := by
      refine ((hasDerivWithinAt_id u A.neg.target).neg).congr (fun s hs => ?_) ?_
      · change A.toFun (A.invFun (-s)) = -(id s)
        simpa using A.right_inv (show -s ∈ A.target by simpa using hs)
      · change A.toFun (A.invFun (-u)) = -(id u)
        simpa using hval
    exact hid.derivWithin (A.neg.toRealChart.uniqueDiffWithinAt_target hu)
  have hcoc := L.cocycle A.neg.toRealChart A.toRealChart u hu hsrc
  simp only [SmoothArc.toRealChart_toFun, SmoothArc.toRealChart_invFun] at hcoc
  rw [hderiv, hval, hA _ hut] at hcoc
  simpa using hcoc

end Affine

/-! ## Milnor's Appendix Lemma 1, in full -/

section LemmaOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

/-- The overlap of two arcs, as the topological half of Lemma 1 uses it, is the domain of the
transition, as the affine half uses it: `A.toFun '' (A.source ∩ A'.source)` equals
`A.target ∩ A.invFun ⁻¹' A'.source`.  Both descriptions are already in the library; this is the
bridge between them. -/
theorem overlap_eq_inter_preimage (A A' : Arc M (I.boundary M)) :
    overlap A A' = A.target ∩ A.invFun ⁻¹' A'.source :=
  (transSource_eq_overlap A A').symm.trans (transSource_def A A')

/-- **Milnor's Appendix Lemma 1 (book p. 54), in full.**

Let `A` and `A'` be two unit-speed smooth arcs of a one-manifold and let `S = overlap A A'` be the
set of `A`-parameters whose point also lies in `A'`.  Then:

1. **(the affine half, this file)** on each component `hull S t₀` of `S` the transition
   `s ↦ A'.toFun (A.invFun s)` is `s ↦ ε s + k` for a constant `k` and a sign `ε = ±1`;
2. **(the topological half, Stage 2)** `S` has at most two components;
3. **(the topological half, Stage 2)** two different components reach *opposite* ends of `A.target`
   -- one runs down to `sInf A.target` while the other runs up to `sSup A.target`.

Part 1 is `exists_affine_trans`; parts 2 and 3 are `Milnor.OneManifold.encard_hulls_le_two` and
`Milnor.OneManifold.sInf_eq_and_sSup_eq_of_hull_ne`, which use no smoothness whatever.

Hypotheses: `M` Hausdorff and charted on a model with corners over a real normed space; two `C^∞`
smooth arcs; a length element `L` for which both have unit speed.  No dimension hypothesis, no
compactness, no boundarylessness, and no hypothesis on where either arc starts. -/
theorem milnor_appendix_lemma_one {L : LengthElement I ∞ M} {A A' : SmoothArc I ∞ M}
    (hA : UnitSpeed L A) (hA' : UnitSpeed L A') :
    (∀ t₀ ∈ overlap A.toArc A'.toArc, ∃ ε k : ℝ, (ε = 1 ∨ ε = -1) ∧
        ∀ s ∈ hull (overlap A.toArc A'.toArc) t₀,
          OneManifold.trans A.toArc A'.toArc s = ε * s + k) ∧
      ((fun t => hull (overlap A.toArc A'.toArc) t) ''
        overlap A.toArc A'.toArc).encard ≤ 2 ∧
      (∀ t₁ ∈ overlap A.toArc A'.toArc, ∀ t₂ ∈ overlap A.toArc A'.toArc,
        hull (overlap A.toArc A'.toArc) t₁ ≠ hull (overlap A.toArc A'.toArc) t₂ →
        (sInf (hull (overlap A.toArc A'.toArc) t₁) = sInf A.target ∧
            sSup (hull (overlap A.toArc A'.toArc) t₂) = sSup A.target) ∨
          (sSup (hull (overlap A.toArc A'.toArc) t₁) = sSup A.target ∧
            sInf (hull (overlap A.toArc A'.toArc) t₂) = sInf A.target)) := by
  refine ⟨fun t₀ _ => ?_, encard_hulls_le_two A.toArc A'.toArc,
    fun t₁ h₁ t₂ h₂ hne => sInf_eq_and_sSup_eq_of_hull_ne A.toArc A'.toArc h₁ h₂ hne⟩
  have hsub : hull (overlap A.toArc A'.toArc) t₀ ⊆ A.target ∩ A.invFun ⁻¹' A'.source := by
    rw [← overlap_eq_inter_preimage]
    exact hull_subset _ _
  obtain ⟨ε, k, hε, haff⟩ :=
    exists_affine_trans hA hA' hsub (hull_ordConnected (overlap A.toArc A'.toArc) t₀)
  refine ⟨ε, k, hε, fun s hs => ?_⟩
  change A'.toFun (A.invFun s) = ε * s + k
  exact haff s hs

end LemmaOne

/-! ## The extension theorem for unit-speed arcs -/

section Extension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

/-- **The extension of a unit-speed arc across a second one, in the normalized position**: the
smooth, unit-speed, genuinely-extending refinement of
`Milnor.OneManifold.exists_extension_aux`.

`A` is a unit-speed arc starting at a boundary point `p` with coordinate `0` and target `Ico 0 c`;
`A'` is any unit-speed arc; `x ∈ A'.source` lies outside `A.source`; and the normalization says that
all `A'`-coordinates of the overlap lie *below* `d = A'.toFun x` and accumulate at it.  The
conclusion is a unit-speed smooth arc whose source is exactly `A.source ∪ A'.source` and whose
coordinate **agrees with `A.toFun` on all of `A.source`**.

The construction is the existing one: coordinate `A.toFun` on `A.source` and `c + (A'.toFun · - d)`
beyond it; inverse `A.invFun` below `c` and `A'.invFun (d + (· - c))` above.  What unit speed
contributes is `hFA'`: by the affine half of Lemma 1 the transition on the overlap is exactly
`s ↦ d + (s - c)` -- slope `+1` because the transition is increasing there, and constant `c - d`
because the overlap has supremum `c` seen from `A` and `d` seen from `A'` -- so the second
formula is valid on *all* of `A'.source`.  Hence the two branches are one function near the
junction, and continuity, smoothness and unit speed are local statements on two open (or
relatively open) pieces.

Hypotheses: `T2Space M`; the two arcs `C^∞` and of unit speed for a common length element; and the
normalization hypotheses of the existing theorem.  No dimension hypothesis, no compactness. -/
theorem exists_extension_aux_unitSpeed (L : LengthElement I ∞ M) (A A' : SmoothArc I ∞ M)
    (hA : UnitSpeed L A) (hA' : UnitSpeed L A') {p x : M} {c : ℝ} (hc : 0 < c)
    (hpA : p ∈ A.source) (hp0 : A.toFun p = 0) (hAt : A.target = Ico 0 c) (hx' : x ∈ A'.source)
    (hxA : x ∉ A.source) (hlt : ∀ t ∈ overlap A'.toArc A.toArc, t < A'.toFun x)
    (happ : ∀ ε > 0, ∃ t ∈ overlap A'.toArc A.toArc, A'.toFun x - ε < t) :
    ∃ Ã : SmoothArc I ∞ M, UnitSpeed L Ã ∧ Ã.source = A.source ∪ A'.source ∧
      (∀ y ∈ A.source, Ã.toFun y = A.toFun y) ∧ p ∈ Ã.source ∧ Ã.toFun p = 0 ∧
      (0 : ℝ) ∈ Ã.target ∧ Ã.target ⊆ Ici 0 ∧ A.source ⊆ Ã.source ∧ A'.source ⊆ Ã.source := by
  classical
  -- ### The topological preliminaries, exactly as in `exists_extension_aux`
  set S := overlap A.toArc A'.toArc with hS
  set S' := overlap A'.toArc A.toArc with hS'
  set d := A'.toFun x with hd
  set τ := trans A.toArc A'.toArc with hτ
  set σ := trans A'.toArc A.toArc with hσ
  have hSo : S.OrdConnected := overlap_ordConnected A.toArc A'.toArc hc hpA hp0 hAt
  have hSc : S ⊆ Ico 0 c := fun t ht => hAt ▸ overlap_subset A.toArc A'.toArc ht
  have hS'T : S' ⊆ A'.target := overlap_subset A'.toArc A.toArc
  have hdT : d ∈ A'.target := A'.map_source hx'
  have hdS' : d ∉ S' := by
    rintro ⟨z, hz, hzx⟩
    exact hxA (A'.injOn hz.1 hx' hzx ▸ hz.2)
  have hστ : ∀ s ∈ S, σ (τ s) = s := fun s hs => by
    have h1 := invFun_eq_of_mem_overlap A.toArc A'.toArc hs
    change A.toFun (A'.invFun (trans A.toArc A'.toArc s)) = s
    rw [h1, A.right_inv (overlap_subset A.toArc A'.toArc hs)]
  have hτσ : ∀ t ∈ S', τ (σ t) = t := fun t ht => by
    have h1 := invFun_eq_of_mem_overlap A'.toArc A.toArc ht
    change A'.toFun (A.invFun (trans A'.toArc A.toArc t)) = t
    rw [h1, A'.right_inv (overlap_subset A'.toArc A.toArc ht)]
  have hτS : τ '' S = S' := by
    ext t; constructor
    · rintro ⟨s, hs, rfl⟩; exact trans_mem_overlap A.toArc A'.toArc hs
    · intro ht; exact ⟨σ t, trans_mem_overlap A'.toArc A.toArc ht, hτσ t ht⟩
  have hσS' : σ '' S' = S := by
    ext s; constructor
    · rintro ⟨t, ht, rfl⟩; exact trans_mem_overlap A'.toArc A.toArc ht
    · intro hs; exact ⟨τ s, trans_mem_overlap A.toArc A'.toArc hs, hστ s hs⟩
  obtain ⟨t₁, ht₁, -⟩ := happ 1 one_pos
  have hS'ne : S'.Nonempty := ⟨t₁, ht₁⟩
  have hSne : S.Nonempty := ⟨σ t₁, trans_mem_overlap A'.toArc A.toArc ht₁⟩
  have hhull : ∀ t ∈ S, hull S t = S := fun t ht => by
    ext u; exact ⟨fun hu => hull_subset S t hu, fun hu => hSo.uIcc_subset hu ht⟩
  have hSn : S.Nontrivial := by
    obtain ⟨s, hs⟩ := hSne
    have := hull_nontrivial A.toArc A'.toArc hc hAt hs
    rwa [hhull s hs] at this
  have hS'o : S'.OrdConnected := by
    rw [← hτS]; exact ordConnected_image_trans A.toArc A'.toArc subset_rfl hSo
  have hhull' : ∀ t ∈ S', hull S' t = S' := fun t ht => by
    ext u; exact ⟨fun hu => hull_subset S' t hu, fun hu => hS'o.uIcc_subset hu ht⟩
  have hS'n : S'.Nontrivial := by
    obtain ⟨a, ha, b, hb, hab⟩ := hSn
    exact ⟨τ a, trans_mem_overlap A.toArc A'.toArc ha, τ b,
      trans_mem_overlap A.toArc A'.toArc hb,
      fun h => hab (trans_injOn A.toArc A'.toArc ha hb h)⟩
  have hsupS' : sSup S' = d := by
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hS'ne (fun t ht => (hlt t ht).le)
      fun w hw => ?_
    obtain ⟨t, ht, hwt⟩ := happ (d - w) (by linarith)
    exact ⟨t, ht, by linarith⟩
  have hS'lt : S' ⊆ Iio d := fun t ht => hlt t ht
  have hS'b : BddAbove S' := A'.bddAbove_target.mono hS'T
  have hSb : BddAbove S := A.bddAbove_target.mono (overlap_subset A.toArc A'.toArc)
  have hSbb : BddBelow S := A.bddBelow_target.mono (overlap_subset A.toArc A'.toArc)
  have hS'bb : BddBelow S' := A'.bddBelow_target.mono hS'T
  have hinfS : 0 ≤ sInf S := le_csInf hSne fun t ht => (hSc ht).1
  -- `σ` is increasing on `S'`, and `sSup S = c`
  have hσmono : StrictMonoOn σ S' := by
    rcases strictMonoOn_or_strictAntiOn_of_ordConnected hS'o hS'n
      (trans_continuousOn A'.toArc A.toArc) (trans_injOn A'.toArc A.toArc) with h | h
    · exact h
    · exfalso
      have hR := end_right A'.toArc A.toArc ht₁ (by rw [hhull' t₁ ht₁]; exact hS'b)
        (by rw [hhull' t₁ ht₁, hsupS']; exact hdT)
        (by rw [hhull' t₁ ht₁, hsupS']; exact hdS')
      rw [hhull' t₁ ht₁, hσS'] at hR
      have := hR.2 h 0 (by rw [hAt]; exact ⟨le_rfl, hc⟩)
      exact lt_irrefl _ (hinfS.trans_lt this)
  have hsupS : sSup S = c := by
    have hR := end_right A'.toArc A.toArc ht₁ (by rw [hhull' t₁ ht₁]; exact hS'b)
      (by rw [hhull' t₁ ht₁, hsupS']; exact hdT)
      (by rw [hhull' t₁ ht₁, hsupS']; exact hdS')
    rw [hhull' t₁ ht₁, hσS'] at hR
    have h1 := hR.1 hσmono
    apply le_antisymm (csSup_le hSne fun t ht => (hSc ht).2.le)
    refine le_of_forall_lt fun t htc => ?_
    rcases lt_or_ge t 0 with h | h
    · exact h.trans_le (le_csSup_of_le hSb hSne.some_mem (hSc hSne.some_mem).1)
    · exact h1 t (by rw [hAt]; exact ⟨h, htc⟩)
  have hτmono : StrictMonoOn τ S := by
    intro s₁ hs₁ s₂ hs₂ hlt'
    by_contra h; push Not at h
    have := hσmono.monotoneOn (trans_mem_overlap A.toArc A'.toArc hs₂)
      (trans_mem_overlap A.toArc A'.toArc hs₁) h
    rw [hστ s₁ hs₁, hστ s₂ hs₂] at this
    exact absurd hlt' (not_lt.2 this)
  have hSlt : S ⊆ Iio c := fun t ht => (hSc ht).2
  have hinfSlt : sInf S < c := (csInf_le hSbb hSne.some_mem).trans_lt (hSc hSne.some_mem).2
  -- everything in `A'.target` below `d` is in the overlap
  have hbelow : ∀ t ∈ A'.target, t < d → t ∈ S' := by
    intro t ht htd
    by_cases hinf : sInf S ∈ S
    · have h0 : sInf S = 0 := by
        by_contra hne
        have hpos : 0 < sInf S := lt_of_le_of_ne hinfS (Ne.symm hne)
        have hh := sInf_hull_notMem A.toArc A'.toArc hc hAt hinf (by rwa [hhull _ hinf])
        rw [hhull _ hinf] at hh
        exact hh hinf
      rw [h0] at hinf
      have hτ0 : τ 0 ∈ S' := trans_mem_overlap A.toArc A'.toArc hinf
      have hmin : τ 0 = sInf A'.target := by
        rcases trans_zero_eq_sInf_or_sSup A.toArc A'.toArc hpA hp0 hAt hinf with h | h
        · rw [← hτ] at h; exact h
        · exfalso
          rw [← hτ] at h
          obtain ⟨a, ha, b, hb, hab⟩ := hSn
          have hpos : ∃ s ∈ S, 0 < s := by
            rcases eq_or_ne a 0 with rfl | ha0
            · exact ⟨b, hb, lt_of_le_of_ne (hSc hb).1 hab⟩
            · exact ⟨a, ha, lt_of_le_of_ne (hSc ha).1 (Ne.symm ha0)⟩
          obtain ⟨s, hs, hs0⟩ := hpos
          have h1 : τ 0 < τ s := hτmono hinf hs hs0
          have h2 : τ s < d := hlt _ (trans_mem_overlap A.toArc A'.toArc hs)
          have h3 : d ≤ sSup A'.target := le_csSup A'.bddAbove_target hdT
          rw [h] at h1; linarith
      have h1 : τ 0 ≤ t := by rw [hmin]; exact csInf_le A'.bddBelow_target ht
      obtain ⟨b, hb, htb⟩ := exists_lt_of_lt_csSup hS'ne (by rw [hsupS']; exact htd)
      exact hS'o.out hτ0 hb ⟨h1, htb.le⟩
    · have hL := end_left A.toArc A'.toArc hSne.some_mem
        (by rw [hhull _ hSne.some_mem]; exact hSbb)
        (by rw [hhull _ hSne.some_mem, hAt]; exact ⟨hinfS, hinfSlt⟩)
        (by rw [hhull _ hSne.some_mem]; exact hinf)
      rw [hhull _ hSne.some_mem, hτS] at hL
      have h1 := hL.1 hτmono t ht
      obtain ⟨a, ha, hat⟩ := exists_lt_of_csInf_lt hS'ne h1
      obtain ⟨b, hb, htb⟩ := exists_lt_of_lt_csSup hS'ne (by rw [hsupS']; exact htd)
      exact hS'o.out ha hb ⟨hat.le, htb.le⟩
  have hF2 : ∀ y ∈ A.source, y ∈ A'.source → A'.toFun y < d := fun y hy hy' =>
    hlt _ ⟨y, ⟨hy', hy⟩, rfl⟩
  have hF1 : ∀ y ∈ A'.source, y ∉ A.source → d ≤ A'.toFun y := by
    intro y hy hyA
    by_contra h; push Not at h
    obtain ⟨z, hz, hzy⟩ := hbelow _ (A'.map_source hy) h
    exact hyA (A'.injOn hz.1 hy hzy ▸ hz.2)
  have hF3 : ∀ t ∈ A'.target, d ≤ t → A'.invFun t ∉ A.source := by
    intro t ht hdt hmem
    have : t ∈ S' := ⟨A'.invFun t, ⟨A'.map_target ht, hmem⟩, A'.right_inv ht⟩
    exact lt_irrefl _ ((hlt t this).trans_le hdt)
  -- ### The affine half of Lemma 1 pins the transition down to `s ↦ d + (s - c)`
  have hσeq : ∀ t, σ t = A.toFun (A'.invFun t) := fun _ => rfl
  have hS'sub : S' ⊆ A'.target ∩ A'.invFun ⁻¹' A.source := fun t ht =>
    ⟨hS'T ht, (invFun_mem_of_mem_overlap A'.toArc A.toArc ht).2⟩
  obtain ⟨e, k, he, haff⟩ := exists_affine_trans hA' hA hS'sub hS'o
  -- the slope is `+1`, because the transition `σ` is increasing on `S'`
  have he1 : e = 1 := by
    obtain ⟨a, ha, b, hb, hab⟩ := hS'n
    rcases he with h1 | h1
    · exact h1
    · exfalso
      rcases lt_or_gt_of_ne hab with hab' | hab'
      · have hm := hσmono ha hb hab'
        rw [hσeq a, hσeq b, haff a ha, haff b hb, h1] at hm
        linarith
      · have hm := hσmono hb ha hab'
        rw [hσeq a, hσeq b, haff a ha, haff b hb, h1] at hm
        linarith
  -- the constant is `c - d`, because `sSup S = c` and `sSup S' = d`
  have hk : k = c - d := by
    have h1 : c ≤ d + k := by
      rw [← hsupS]
      refine csSup_le hSne fun s hs => ?_
      rw [← hσS'] at hs
      obtain ⟨t, ht, hts⟩ := hs
      have hval : s = t + k := by rw [← hts, hσeq t, haff t ht, he1]; ring
      have := hlt t ht
      linarith
    have h2 : d + k ≤ c := by
      by_contra hcon
      push Not at hcon
      obtain ⟨t, ht, htlt⟩ := happ (d + k - c) (by linarith)
      have hmem : σ t ∈ S := by rw [← hσS']; exact ⟨t, ht, rfl⟩
      have hle : σ t ≤ c := by rw [← hsupS]; exact le_csSup hSb hmem
      have hval : σ t = t + k := by rw [hσeq t, haff t ht, he1]; ring
      linarith
    linarith
  have hσaff : ∀ t ∈ S', A.toFun (A'.invFun t) = c + (t - d) := by
    intro t ht
    rw [haff t ht, he1, hk]; ring
  have hτaff : ∀ s ∈ S, A'.toFun (A.invFun s) = d + (s - c) := by
    intro s hs
    have hmem := invFun_mem_of_mem_overlap A.toArc A'.toArc hs
    have hts : A'.toFun (A.invFun s) ∈ S' := ⟨A.invFun s, hmem.symm, rfl⟩
    have h := hσaff _ hts
    rw [A'.left_inv hmem.2, A.right_inv (overlap_subset A.toArc A'.toArc hs)] at h
    linarith
  -- ### The glued arc: the same formulas as in the topological proof
  set F : M → ℝ := fun y => if y ∈ A.source then A.toFun y else c + (A'.toFun y - d) with hF
  set G : ℝ → M := fun t => if t < c then A.invFun t else A'.invFun (d + (t - c)) with hG
  set T : Set ℝ := {t | 0 ≤ t ∧ (t < c ∨ d + (t - c) ∈ A'.target)} with hT
  set c'' : ℝ := c + (sSup A'.target - d) with hc''
  have hcc'' : c ≤ c'' := by
    have := le_csSup A'.bddAbove_target hdT; rw [hc'']; linarith
  have hF_A : ∀ y ∈ A.source, F y = A.toFun y := fun y hy => by simp [hF, hy]
  have hF_notA : ∀ y, y ∉ A.source → F y = c + (A'.toFun y - d) := fun y hy => by
    simp [hF, hy]
  have hG_lt : ∀ t, t < c → G t = A.invFun t := fun t ht => by simp [hG, ht]
  have hG_ge : ∀ t, c ≤ t → G t = A'.invFun (d + (t - c)) := fun t ht => by
    simp [hG, not_lt.2 ht]
  have hTlt : ∀ t, 0 ≤ t → t < c → t ∈ T := fun t h0 hc' => ⟨h0, Or.inl hc'⟩
  have hTge : ∀ t ∈ T, c ≤ t → d + (t - c) ∈ A'.target := fun t ht hct => by
    rcases ht.2 with h | h
    · exact absurd h (not_lt.2 hct)
    · exact h
  have hTof : ∀ t, c ≤ t → d + (t - c) ∈ A'.target → t ∈ T := fun t hct h =>
    ⟨hc.le.trans hct, Or.inr h⟩
  have hIoo : Ioo 0 c'' ⊆ T := by
    intro t ht
    rcases lt_or_ge t c with h | h
    · exact hTlt t ht.1.le h
    · refine hTof t h ?_
      rcases eq_or_lt_of_le h with h' | h'
      · rw [← h']; simpa using hdT
      · have h1 : d < d + (t - c) := by linarith
        have h2 : d + (t - c) < sSup A'.target := by rw [hc''] at ht; linarith [ht.2]
        obtain ⟨b, hb, hb'⟩ := exists_lt_of_lt_csSup A'.nontrivial_target.nonempty h2
        exact A'.ordConnected_target.out hdT hb ⟨h1.le, hb'.le⟩
  have hIcc : T ⊆ Icc 0 c'' := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    rcases ht.2 with h | h
    · exact h.le.trans hcc''
    · have := le_csSup A'.bddAbove_target h; rw [hc'']; linarith
  have hTo : T.OrdConnected := by
    refine ⟨fun a ha b hb t ht => ⟨ha.1.trans ht.1, ?_⟩⟩
    rcases lt_or_ge t c with h | h
    · exact Or.inl h
    · right
      have hbc : c ≤ b := h.trans ht.2
      have hb' := hTge b hb hbc
      exact A'.ordConnected_target.out hdT hb' ⟨by linarith, by linarith [ht.2]⟩
  have hTn : T.Nontrivial := ⟨0, hTlt 0 le_rfl hc, c / 2, hTlt _ (by positivity) (by linarith),
    by linarith⟩
  have hint : interior T = Ioo 0 c'' := by
    apply Subset.antisymm
    · calc interior T ⊆ interior (Icc 0 c'') := interior_mono hIcc
        _ = Ioo 0 c'' := interior_Icc
    · exact interior_maximal hIoo isOpen_Ioo
  -- **the junction is not a junction**: the second formula is valid on all of `A'.source`
  have hF_A' : ∀ y ∈ A'.source, F y = c + (A'.toFun y - d) := by
    intro y hy
    by_cases hyA : y ∈ A.source
    · rw [hF_A y hyA]
      have hs : A.toFun y ∈ S := ⟨y, ⟨hyA, hy⟩, rfl⟩
      have h := hτaff (A.toFun y) hs
      rw [A.left_inv hyA] at h
      linarith
    · exact hF_notA y hyA
  -- ### Two relatively open pieces of the new target, on each of which the inverse is one formula
  have hTIio : T ∩ Iio c = A.target := by
    rw [hAt]
    exact Subset.antisymm (fun t ht => ⟨ht.1.1, ht.2⟩) fun t ht => ⟨hTlt t ht.1 ht.2, ht.2⟩
  have hSlow : Ioo (sInf S) c ⊆ S := by
    intro t ht
    obtain ⟨a, ha, hat⟩ := exists_lt_of_csInf_lt hSne ht.1
    obtain ⟨b, hb, htb⟩ := exists_lt_of_lt_csSup hSne (by rw [hsupS]; exact ht.2)
    exact hSo.out ha hb ⟨hat.le, htb.le⟩
  have hTaff : ∀ t ∈ T, sInf S < t → d + (t - c) ∈ A'.target := by
    intro t ht hlow
    rcases lt_or_ge t c with h | h
    · have hts : t ∈ S := hSlow ⟨hlow, h⟩
      rw [← hτaff t hts]
      exact A'.map_source (invFun_mem_of_mem_overlap A.toArc A'.toArc hts).2
    · exact hTge t ht h
  have hGaff : ∀ t ∈ T, sInf S < t → G t = A'.invFun (d + (t - c)) := by
    intro t ht hlow
    rcases lt_or_ge t c with h | h
    · have hts : t ∈ S := hSlow ⟨hlow, h⟩
      have hmem := invFun_mem_of_mem_overlap A.toArc A'.toArc hts
      rw [hG_lt t h, ← hτaff t hts, A'.left_inv hmem.2]
    · rw [hG_ge t h]
  -- ### Smoothness of the new coordinate: two open sets, one formula on each
  have haff1 : ContDiff ℝ ∞ fun u : ℝ => c + (u - d) := by fun_prop
  have haff2 : ContDiff ℝ ∞ fun u : ℝ => d + (u - c) := by fun_prop
  have hFsm : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F (A.source ∪ A'.source) := by
    intro y hy
    rcases hy with hyA | hyA'
    · have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ A.toFun y :=
        A.contMDiffOn_toFun.contMDiffAt (A.open_source.mem_nhds hyA)
      refine (h1.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [A.open_source.mem_nhds hyA] with z hz using hF_A z hz
    · have h0 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ A'.toFun y :=
        A'.contMDiffOn_toFun.contMDiffAt (A'.open_source.mem_nhds hyA')
      have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ ((fun u : ℝ => c + (u - d)) ∘ A'.toFun) y :=
        ContMDiffAt.comp y haff1.contMDiff.contMDiffAt h0
      refine (h1.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [A'.open_source.mem_nhds hyA'] with z hz using hF_A' z hz
  -- ### Smoothness of the new parametrization: two relatively open pieces of the target
  have hGsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ G T := by
    intro t ht
    rcases lt_or_ge (sInf S) t with hlow | hhigh
    · have hnb : T ∩ Ioi (sInf S) ∈ 𝓝[T] t :=
        inter_mem_nhdsWithin _ (isOpen_Ioi.mem_nhds hlow)
      refine ContMDiffWithinAt.mono_of_mem_nhdsWithin ?_ hnb
      have hmaps : MapsTo (fun u : ℝ => d + (u - c)) (T ∩ Ioi (sInf S)) A'.target :=
        fun u hu => hTaff u hu.1 hu.2
      have h1 : ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ (fun u : ℝ => A'.invFun (d + (u - c)))
          (T ∩ Ioi (sInf S)) t :=
        ContMDiffWithinAt.comp t (A'.contMDiffOn_invFun _ (hmaps ⟨ht, hlow⟩))
          haff2.contMDiff.contMDiffAt.contMDiffWithinAt hmaps
      exact h1.congr (fun u hu => hGaff u hu.1 hu.2) (hGaff t ht hlow)
    · have htc : t < c := hhigh.trans_lt hinfSlt
      have hnb : T ∩ Iio c ∈ 𝓝[T] t := inter_mem_nhdsWithin _ (isOpen_Iio.mem_nhds htc)
      refine ContMDiffWithinAt.mono_of_mem_nhdsWithin ?_ hnb
      have h1 : ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ A.invFun (T ∩ Iio c) t := by
        rw [hTIio]
        exact A.contMDiffOn_invFun t (by rw [hAt]; exact ⟨ht.1, htc⟩)
      exact h1.congr (fun u hu => hG_lt u hu.2) (hG_lt t htc)
  -- ### The remaining obligations, exactly as in `exists_extension_aux`
  have hms : ∀ y ∈ A.source ∪ A'.source, F y ∈ T := by
    intro y hy
    by_cases hyA : y ∈ A.source
    · rw [hF_A y hyA]
      have := A.map_source hyA; rw [hAt] at this
      exact hTlt _ this.1 this.2
    · have hy' : y ∈ A'.source := hy.resolve_left hyA
      rw [hF_notA y hyA]
      have h1 := hF1 y hy' hyA
      refine hTof _ (by linarith) ?_
      have : d + (c + (A'.toFun y - d) - c) = A'.toFun y := by ring
      rw [this]; exact A'.map_source hy'
  have hmt : ∀ t ∈ T, G t ∈ A.source ∪ A'.source := by
    intro t ht
    rcases lt_or_ge t c with h | h
    · rw [hG_lt t h]; exact Or.inl (A.map_target (by rw [hAt]; exact ⟨ht.1, h⟩))
    · rw [hG_ge t h]; exact Or.inr (A'.map_target (hTge t ht h))
  have hli : ∀ y ∈ A.source ∪ A'.source, G (F y) = y := by
    intro y hy
    by_cases hyA : y ∈ A.source
    · have hlt' : F y < c := by
        rw [hF_A y hyA]; have := A.map_source hyA; rw [hAt] at this; exact this.2
      rw [hG_lt _ hlt', hF_A y hyA, A.left_inv hyA]
    · have hy' : y ∈ A'.source := hy.resolve_left hyA
      have hge : c ≤ F y := by rw [hF_notA y hyA]; linarith [hF1 y hy' hyA]
      rw [hG_ge _ hge, hF_notA y hyA]
      have : d + (c + (A'.toFun y - d) - c) = A'.toFun y := by ring
      rw [this]; exact A'.left_inv hy'
  have hri : ∀ t ∈ T, F (G t) = t := by
    intro t ht
    rcases lt_or_ge t c with h | h
    · have hmem : A.invFun t ∈ A.source := A.map_target (by rw [hAt]; exact ⟨ht.1, h⟩)
      rw [hG_lt t h, hF_A _ hmem, A.right_inv (by rw [hAt]; exact ⟨ht.1, h⟩)]
    · have hmem := hTge t ht h
      have hnot : A'.invFun (d + (t - c)) ∉ A.source := hF3 _ hmem (by linarith)
      rw [hG_ge t h, hF_notA _ hnot, A'.right_inv hmem]; ring
  have hbd : ∀ y ∈ A.source ∪ A'.source, y ∈ I.boundary M ↔ F y ∉ interior T := by
    intro y hy
    rw [hint]
    by_cases hyA : y ∈ A.source
    · rw [hF_A y hyA, A.bdry y hyA, hAt, interior_Ico]
      have := A.map_source hyA; rw [hAt] at this
      constructor
      · intro h1 h2; exact h1 ⟨h2.1, this.2⟩
      · intro h1 h2; exact h1 ⟨h2.1, h2.2.trans_le hcc''⟩
    · have hy' : y ∈ A'.source := hy.resolve_left hyA
      rw [hF_notA y hyA, A'.bdry y hy', A'.interior_target]
      have h1 := hF1 y hy' hyA
      have h2 : sInf A'.target < A'.toFun y :=
        (csInf_le A'.bddBelow_target (hS'T ht₁)).trans_lt ((hlt t₁ ht₁).trans_le h1)
      constructor
      · intro h3 h4
        apply h3
        refine ⟨h2, ?_⟩
        rw [hc''] at h4; linarith [h4.2]
      · intro h3 h4
        apply h3
        refine ⟨by linarith, ?_⟩
        rw [hc'']; linarith [h4.2]
  -- ### The glued smooth arc
  obtain ⟨Ã, hÃf, hÃg, hÃs, hÃt⟩ :
      ∃ Ã : SmoothArc I ∞ M, Ã.toFun = F ∧ Ã.invFun = G ∧
        Ã.source = A.source ∪ A'.source ∧ Ã.target = T :=
    ⟨{ toFun := F
       invFun := G
       source := A.source ∪ A'.source
       target := T
       map_source' := hms
       map_target' := hmt
       left_inv' := hli
       right_inv' := hri
       open_source := A.open_source.union A'.open_source
       ordConnected_target := hTo
       nontrivial_target := hTn
       bddAbove_target := ⟨c'', fun t ht => (hIcc ht).2⟩
       bddBelow_target := ⟨0, fun t ht => (hIcc ht).1⟩
       continuousOn_toFun := hFsm.continuousOn
       continuousOn_invFun := hGsm.continuousOn
       bdry := hbd
       contMDiffOn_toFun := hFsm
       contMDiffOn_invFun := hGsm }, rfl, rfl, rfl, rfl⟩
  -- ### Unit speed of the glued arc, from the cocycle rule on the two pieces
  have hUS : UnitSpeed L Ã := by
    intro u hu
    have huA : u ∈ Ã.target := hu
    rw [hÃt] at hu
    rcases lt_or_ge (sInf S) u with hlow | hhigh
    · -- beyond `sInf S` the new parametrization is `A'.invFun (d + (· - c))`
      have hnb : T ∩ Ioi (sInf S) ∈ 𝓝[T] u :=
        inter_mem_nhdsWithin _ (isOpen_Ioi.mem_nhds hlow)
      have hGu : Ã.invFun u = A'.invFun (d + (u - c)) := by rw [hÃg]; exact hGaff u hu hlow
      have hmem : Ã.invFun u ∈ A'.source := by
        rw [hGu]; exact A'.map_target (hTaff u hu hlow)
      have hval : A'.toFun (Ã.invFun u) = d + (u - c) := by
        rw [hGu]; exact A'.right_inv (hTaff u hu hlow)
      have hloc : ∀ s ∈ T ∩ Ioi (sInf S), A'.toFun (Ã.invFun s) = d + (s - c) := by
        intro s hs
        rw [hÃg, hGaff s hs.1 hs.2, A'.right_inv (hTaff s hs.1 hs.2)]
      have hdd : transDeriv Ã.toRealChart A'.toRealChart u = 1 := by
        have h0 : HasDerivWithinAt (fun s : ℝ => d + (s - c)) 1 (T ∩ Ioi (sInf S)) u := by
          simpa using HasDerivWithinAt.const_add d
            ((hasDerivWithinAt_id u (T ∩ Ioi (sInf S))).sub_const c)
        have hdw : HasDerivWithinAt (fun s => A'.toFun (Ã.invFun s)) 1 Ã.target u := by
          rw [hÃt]
          exact (h0.congr hloc (hloc u ⟨hu, hlow⟩)).mono_of_mem_nhdsWithin hnb
        exact hdw.derivWithin (Ã.toRealChart.uniqueDiffWithinAt_target huA)
      have hcoc := L.cocycle Ã.toRealChart A'.toRealChart u huA hmem
      simp only [SmoothArc.toRealChart_toFun, SmoothArc.toRealChart_invFun] at hcoc
      rw [hdd, hval, hA' _ (hTaff u hu hlow)] at hcoc
      simpa using hcoc
    · -- below `sInf S` the new parametrization is `A.invFun`, and the transition is the identity
      have huc : u < c := hhigh.trans_lt hinfSlt
      have huAt : u ∈ A.target := by rw [hAt]; exact ⟨hu.1, huc⟩
      have hGu : Ã.invFun u = A.invFun u := by rw [hÃg]; exact hG_lt u huc
      have hmem : Ã.invFun u ∈ A.source := by rw [hGu]; exact A.map_target huAt
      have hval : A.toFun (Ã.invFun u) = u := by rw [hGu]; exact A.right_inv huAt
      have hnb : T ∩ Iio c ∈ 𝓝[T] u := inter_mem_nhdsWithin _ (isOpen_Iio.mem_nhds huc)
      have hloc : ∀ s ∈ T ∩ Iio c, A.toFun (Ã.invFun s) = s := by
        intro s hs
        rw [hÃg, hG_lt s hs.2]
        exact A.right_inv (by rw [hAt]; exact ⟨hs.1.1, hs.2⟩)
      have hdd : transDeriv Ã.toRealChart A.toRealChart u = 1 := by
        have hdw : HasDerivWithinAt (fun s => A.toFun (Ã.invFun s)) 1 Ã.target u := by
          rw [hÃt]
          refine ((hasDerivWithinAt_id u (T ∩ Iio c)).congr (fun s hs => ?_)
            ?_).mono_of_mem_nhdsWithin hnb
          · exact hloc s hs
          · exact hloc u ⟨hu, huc⟩
        exact hdw.derivWithin (Ã.toRealChart.uniqueDiffWithinAt_target huA)
      have hcoc := L.cocycle Ã.toRealChart A.toRealChart u huA hmem
      simp only [SmoothArc.toRealChart_toFun, SmoothArc.toRealChart_invFun] at hcoc
      rw [hdd, hval, hA u huAt] at hcoc
      simpa using hcoc
  refine ⟨Ã, hUS, hÃs, fun y hy => by rw [hÃf]; exact hF_A y hy, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hÃs]; exact Or.inl hpA
  · rw [hÃf, hF_A p hpA]; exact hp0
  · rw [hÃt]; exact hTlt 0 le_rfl hc
  · rw [hÃt]; exact fun t ht => ht.1
  · rw [hÃs]; exact subset_union_left
  · rw [hÃs]; exact subset_union_right

/-- **The extension theorem for unit-speed arcs**: the smooth, unit-speed, genuinely-extending
refinement of `Milnor.OneManifold.exists_extension`, and the point of Stage 5.

Let `A` be a unit-speed smooth arc starting at a boundary point `p` with coordinate `0` and target
`Ico 0 c`, let `A'` be any unit-speed smooth arc, and let `x ∈ A'.source` be a point outside
`A.source` but in its closure -- so `A'` reaches past the far end of `A`.  Then there is a
**unit-speed smooth arc `Ã` whose source is `A.source ∪ A'.source`, which starts at `p` with
coordinate `0`, whose target lies in `Ici 0`, and whose coordinate agrees with `A.toFun` at every
point of `A.source`.**

That last clause is the whole point: `Ã` *extends* `A`, it does not merely contain a
reparametrization of it.  It is what makes the set of unit-speed arcs from `p` a poset under
restriction with useful chains -- the input to the maximality argument for the non-compact case --
and it is what fixes the period in the circle case.

The normalization of `exists_extension_aux_unitSpeed` is removed exactly as in the existing proof:
the overlap seen from `A'` lies entirely on one side of `d = A'.toFun x`, and in the second case the
coordinate of `A'` is negated, which preserves unit speed by `UnitSpeed.neg`.

Hypotheses: `T2Space M`; `A`, `A'` of class `C^∞` and of unit speed for a common length element `L`;
`0 < c`; `p ∈ A.source` with `A.toFun p = 0` and `A.target = Ico 0 c`; and
`x ∈ A'.source \ A.source` with `x ∈ closure A.source`.  No dimension hypothesis, no compactness,
no boundarylessness.  (Note that `A.target = Ico 0 c` forces `p` to be a boundary point of `M`; that
is where the one-sided normalization comes from, exactly as in the topological original.) -/
theorem exists_extension_unitSpeed (L : LengthElement I ∞ M) (A A' : SmoothArc I ∞ M)
    (hA : UnitSpeed L A) (hA' : UnitSpeed L A') {p x : M} {c : ℝ} (hc : 0 < c)
    (hpA : p ∈ A.source) (hp0 : A.toFun p = 0) (hAt : A.target = Ico 0 c) (hx' : x ∈ A'.source)
    (hxA : x ∉ A.source) (hxcl : x ∈ closure A.source) :
    ∃ Ã : SmoothArc I ∞ M, UnitSpeed L Ã ∧ Ã.source = A.source ∪ A'.source ∧
      (∀ y ∈ A.source, Ã.toFun y = A.toFun y) ∧ p ∈ Ã.source ∧ Ã.toFun p = 0 ∧
      (0 : ℝ) ∈ Ã.target ∧ Ã.target ⊆ Ici 0 ∧ A.source ⊆ Ã.source ∧ A'.source ⊆ Ã.source := by
  set S' := overlap A'.toArc A.toArc with hS'
  set d := A'.toFun x with hd
  have hdS' : d ∉ S' := by
    rintro ⟨z, hz, hzx⟩
    exact hxA (A'.injOn hz.1 hx' hzx ▸ hz.2)
  have hxcl' : x ∈ closure (A'.source ∩ A.source) := by
    rw [mem_closure_iff_nhds] at hxcl ⊢
    intro N hN
    obtain ⟨z, hz⟩ := hxcl (N ∩ A'.source) (inter_mem hN (A'.open_source.mem_nhds hx'))
    exact ⟨z, hz.1.1, hz.1.2, hz.2⟩
  have hdcl : d ∈ closure S' :=
    ((A'.continuousOn_toFun x hx').mono inter_subset_left).mem_closure_image hxcl'
  have hS'ne : S'.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hdcl
    exact hdcl
  have hS'o : S'.OrdConnected := by
    have hSo := overlap_ordConnected A.toArc A'.toArc hc hpA hp0 hAt
    have hτS : OneManifold.trans A.toArc A'.toArc '' overlap A.toArc A'.toArc = S' := by
      ext t
      constructor
      · rintro ⟨s, hs, rfl⟩; exact trans_mem_overlap A.toArc A'.toArc hs
      · intro ht
        refine ⟨OneManifold.trans A'.toArc A.toArc t, trans_mem_overlap A'.toArc A.toArc ht, ?_⟩
        have h1 := invFun_eq_of_mem_overlap A'.toArc A.toArc ht
        change A'.toFun (A.invFun (OneManifold.trans A'.toArc A.toArc t)) = t
        rw [h1, A'.right_inv (overlap_subset A'.toArc A.toArc ht)]
    rw [← hτS]
    exact ordConnected_image_trans A.toArc A'.toArc subset_rfl hSo
  have happ : ∀ ε > 0, ∃ t ∈ S', |t - d| < ε := fun ε hε => by
    obtain ⟨t, ht, hlt⟩ := Metric.mem_closure_iff.1 hdcl ε hε
    exact ⟨t, ht, by rwa [Real.dist_eq, abs_sub_comm] at hlt⟩
  have hdich : (∀ t ∈ S', t < d) ∨ (∀ t ∈ S', d < t) := by
    by_contra h
    push Not at h
    obtain ⟨⟨a, ha, hda⟩, b, hb, hbd⟩ := h
    exact hdS' (hS'o.out hb ha ⟨hbd, hda⟩)
  rcases hdich with hlow | hhigh
  · exact exists_extension_aux_unitSpeed L A A' hA hA' hc hpA hp0 hAt hx' hxA hlow
      fun ε hε => by
        obtain ⟨t, ht, h⟩ := happ ε hε
        exact ⟨t, ht, by rw [abs_lt] at h; linarith [h.1]⟩
  · have hnegov : overlap A'.neg.toArc A.toArc = -overlap A'.toArc A.toArc := by
      rw [SmoothArc.neg_toArc]
      exact overlap_neg_left A.toArc A'.toArc
    have hneg := exists_extension_aux_unitSpeed L A A'.neg hA hA'.neg hc hpA hp0 hAt hx' hxA
      (by
        rw [hnegov]
        intro t ht
        rw [Set.mem_neg] at ht
        have := hhigh _ ht
        change t < -A'.toFun x
        linarith)
      (by
        rw [hnegov]
        intro ε hε
        obtain ⟨t, ht, h⟩ := happ ε hε
        refine ⟨-t, by rw [Set.mem_neg, neg_neg]; exact ht, ?_⟩
        change -A'.toFun x - ε < -t
        rw [abs_lt] at h
        linarith [h.2])
    obtain ⟨Ã, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hneg
    exact ⟨Ã, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end Extension

end Milnor.OneManifold.Smooth
