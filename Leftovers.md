# The leftovers: what the book states and the formalization did not prove

Status file, started 2026-09-28. The comparison edition (`Exposition/Comparison.md`, rows G.1 to
G.6) lists what the book states and the formalization does not prove. This file records the plan to
close those rows, with what each one needs and where it stands.

Estimates are lines of Lean. Anything marked *in progress* has an agent working on it.

## 0. The vacuous hypothesis is gone (2026-09-28, last)

`Milnor/Chapter7/OneManifoldOrientable.lean`, 564 lines, and a four-line edit to
`Chapter7/HopfMod2.lean`. **Milnor's theorem of p. 50 now carries no dimension hypothesis at all**:
for a closed connected non-orientable smooth `m`-manifold in a Euclidean space, two smooth maps to
`Sᵐ` are smoothly homotopic if and only if they have the same degree modulo 2. The `2 ≤ m` that the
punctured stage needs is now *derived* from non-orientability, by way of the classification of
one-manifolds: every connected σ-compact smooth one-manifold over a boundaryless model is
orientable, and every 0-manifold is, so a connected non-orientable manifold has dimension at least
two. Chapter 7's side hypotheses come free — its manifolds are compact subsets of a Euclidean space,
hence Hausdorff and σ-compact, and their model is boundaryless.

On the way: the pullback of an orientation along an invertible linear map, and its uniqueness;
orientability transported along any smooth map with everywhere-invertible derivative, which needs
the *source* model boundaryless and nothing else, so in particular along a diffeomorphism; and all
four models of the classification oriented. Two things worth recording. Mathlib's interval `[0, 1]`
has **two** charts whose transition reverses orientation, so a constant family is not an orientation
there and the reflection has to be computed; and the circle was oriented not through its own charts
but through the sphere `S¹ ⊆ ℝ²`, which Chapter 8 already orients as the boundary of the disk, the
classification then supplying the diffeomorphism. Transport *into* a manifold whose model has a
boundary is not proved, is not needed, and is the one place this file stops short.

## 1. Lemma 2 of §2, second clause (book p. 11)

The derivative carries the orthogonal complement of the tangent space of the level set
isomorphically onto the tangent space of the target. The kernel clause is
`Milnor.mem_range_mfderiv_val_iff` (Chapter2/LevelSet.lean); this is a splitting argument on top of
it, and needs an inner product on the ambient model space, which Milnor has because his manifolds
sit in Euclidean space.

**Done** 2026-09-28: `Milnor/Chapter2/Normal.lean`, 142 lines. `mfderiv_injOn_tangent_orthogonal`,
`mfderiv_surjOn_tangent_orthogonal`, and the bundled isomorphism `normalEquiv`. The one addition to
Milnor's hypotheses is an inner product on the model space of the source, which he has for free
because his manifolds sit in Euclidean space.

## 2. The index of a non-degenerate zero (Lemma 4 of §6, book p. 36)

The index at a zero where the derivative is non-singular is the sign of its determinant. The
pointwise sign of a linear field is `Milnor.Sphere.signAt_nv0_linear` (Chapter6/Radial.lean), so
what is new is the linearization of the field near the zero, by a straight-line homotopy on a small
sphere, and turning a constant sign into a degree.

**Done** 2026-09-28: `Milnor/Chapter6/Nondegenerate.lean`, 262 lines. `Sphere.index_eq_sgn_det`:
for `n ≥ 1`, a smooth field with `v z = 0` and `dv_z` bijective has `index v z = sgn (det dv_z)`;
`Sphere.index_nondegenerate` is Milnor's ±1 form. Two things he leaves implicit: one uniform
estimate that makes the zero isolated and the straight-line homotopy zero-free at once, and the
step from a constant pointwise sign to a degree (`deg_nv0_linear`, new).

## 3. Hadamard's lemma, and Lemma 2 of §6 (book p. 33)

An orientation-preserving diffeomorphism of ℝᵐ is smoothly isotopic to the identity. Milnor's
isotopy is `F(x, t) = f(tx)/t`, which is smooth at `t = 0` only through a factorization
`f(x) = L(x)·x` with `L` smooth. Mathlib has the integral form of Taylor's theorem but no theorem
saying that an integral over a fixed interval depends smoothly on a parameter, so that lemma comes
first; the template is Mathlib's convolution file. The last step of Milnor's proof, that `GL⁺` is
connected by smooth paths, is already `Milnor.GLp.exists_glPath` (Chapter7/GLplus.lean).

**Hadamard done** 2026-09-28: `Milnor/Chapter6/Hadamard.lean`, 199 lines.
`contDiff_intervalIntegral` and `contDiff_intervalIntegral_infty` say that an integral over a fixed
interval depends smoothly on a parameter, which Mathlib does not have; the proof differentiates
under the integral sign and dominates on a tube around the compact segment, so it needs neither
finite dimension nor local compactness. Then `exists_hadamard`: for smooth `f` with `f 0 = 0` there
is a smooth `L` with `f x = L x x` and `L 0 = df₀`; and `exists_contDiff_extension`, the smooth
extension of `t⁻¹ f (t x)` to `t = 0`. The only hypothesis Milnor would not state is completeness of
the target. **Lemma 2 of §6 done** 2026-09-28: `Milnor/Chapter7/Isotopy.lean`, 474 lines, in Chapter 7
because Milnor's last step is the GL⁺ path proved there. `lemma2_of_sec6`: a diffeomorphism of
ℝᵐ whose Jacobian determinant is positive at one point is smoothly isotopic to the identity,
with every time slice a diffeomorphism, as in the project's notion of isotopy. Stated for any
finite-dimensional real normed space; positivity of the dimension is not needed. Three things
Milnor passes over: transitivity of isotopy, which needs the two isotopies made constant near
the join before gluing; that the slices at negative times are diffeomorphisms too, since the
definition asks for every real time; and invertibility of the derivative at the origin, which
comes from the chain rule on the two-sided inverse. Nothing in the development depends on this
lemma: the formalization of §6 replaced it by a sign computation.

## 4. The chart definition of the index, and its agreement with ours (book pp. 33 and 37)

Milnor defines the index of a zero on a manifold through a parametrization, and his Lemma 5
identifies it with the intrinsic one at a non-degenerate zero. Our index is defined through the
field extended to a tubular neighbourhood (V6.8). Independence of the chart is already
`Milnor.Sphere.index_eq_of_diffeo` (Chapter6/Invariance.lean, Milnor's Lemma 1). At a
non-degenerate zero the agreement reduces to the determinant formula of item 2, since the extended
field is the original one on the tangent directions and the identity on the normal ones.

**Done** 2026-09-28: `Milnor/Chapter6/ChartIndex.lean`, 929 lines. Milnor's Lemma 5 in two forms,
ambient and intrinsic; the derivative of the retraction at a point of the submanifold is proved to
be the orthogonal projection onto the tangent space, so the derivative of the extended field is
`dv ∘ P + (id − P)` and its determinant is the determinant of `dv` restricted to the tangent
space; the chart definition of the index, with independence of the parametrization and of the
extension; and the agreement of the two definitions at a non-degenerate zero, both being the sign
of that determinant. Two things Milnor leaves implicit: what "the derivative of a field on a
submanifold" means, and his own proof of Lemma 5 uses the smoothness of the coefficient field,
which is avoided here by differentiating the identity `(id − dr)(v ∘ r) = 0` instead. The general
agreement, for an arbitrary isolated zero, is **not** proved and cannot be with what the project
has: the two numbers are degrees of maps of spheres of different dimensions, so it needs a
suspension formula for the degree, which Milnor does not prove either. The chart index carries
`n ≥ 2` and the ambient one `K ≥ 1`, because both are degrees on spheres.

## 5. The Euler number of the sphere, and the small remarks of §6 (book pp. 32, 33, 39)

With item 4 in hand, the index sum of an explicit field on `Sⁿ` gives the integer of
Poincaré–Hopf: the field `x ↦ e − ⟪e, x⟫ x` has two non-degenerate zeros, so the integer is
`1 + (−1)ⁿ`. The identification of that integer with the Euler characteristic is **not** planned:
Mathlib has no Euler characteristic of a space, no Betti numbers and no cellular homology, so it
would mean building that theory first.

**Done** 2026-09-28: `Milnor/Chapter6/EulerSphere.lean`, 699 lines. For `n ≥ 1`, every smooth
tangent field on `Sⁿ` with finitely many zeros has index sum `1 + (−1)ⁿ`, and that integer is
pinned down, not merely bounded: any integer with the Poincaré–Hopf property equals it. The field
is Milnor's, the gradient of the height function, whose two zeros are the poles with derivatives
minus the identity and the identity on the tangent space. The odd case is cross-checked
independently: for odd `n` the sphere carries a nowhere-zero field, so the index sum is empty and
the integer is `0`, and a third theorem derives `1 + (−1)ⁿ = 0` from both results. Three things
had to be added: the sphere presented as a level set with a one-dimensional complement model, so
that §6's tubular machinery applies; its tangent space as the orthogonal complement of the
position vector, for that structure; and the derivative through the retraction of a field that
comes from the ambient space. The identification of this integer with the Euler characteristic is
not formalized and cannot be, so the statement `χ(Sⁿ) = 1 + (−1)ⁿ` cannot even be written down.

*A cleanup this exposed:* the project has no lemma comparing two slice-submanifold structures on
the same set, so Milnor's odd-dimensional field had to be rebuilt as an ambient linear map, about
forty duplicated lines. A general "two slice structures, same smooth maps" lemma would remove it.

## 6. The mod 2 theorem of §7 (book p. 50)

For a connected non-orientable manifold, two maps to `Sᵐ` are homotopic if and only if they have
the same degree modulo 2. The survey of chapter 7 found that the framed machinery is almost
entirely orientation-free: `FramedSub`, `FramedCob`, `FramedCobordant`, `pontV`, `pontryagin` and
Theorem C take no orientation at all, and the converse of Theorem B needs an orientation only on
the sphere. Orientation enters in exactly one definition, `frameSign` (Chapter7/Hopf0.lean), and in
the endgame that cancels a plus against a minus (`cancel_step`, `exists_opposite_neighbour`,
`gather`).

So the work is in two parts.

**6a. Orientability of a manifold.** Neither Mathlib nor this project has it in any form. Stages:
**Stage one done** 2026-09-28: `Chapter7/OrientTransport.lean`, 494 lines. Transport of an
orientation across a chart and its uniqueness, orientations as transport sections, hops and
chains, and chain-connectedness of a connected manifold. A step has to record *which* chart it
travels through: the naive relation is not symmetric, and the symmetric repair is wrong, because
two charts can disagree on a disconnected overlap. No boundarylessness is needed.
**Stage two done** 2026-09-28: `Chapter7/Orientable.lean`, 364 lines, verified: the
dichotomy, that a connected manifold with no reversing chain-loop is orientable, and conversely
for the stronger notion of a chart-coherent orientation; also that a connected orientable
manifold has exactly two orientations. The converse is **false** for a bare
`Orient`: on `ℝ` with the atlas made of the identity chart and a chart that is `x` on `(−1, 0)`
and `3 − x` on `(1, 2)`, the orientation that is standard except reversed on `(1, 2)` satisfies
the `Orient` condition, and the loop out through the second chart and back through the first
reverses. **Stage three done** 2026-09-28: `Chapter7/OrientBall.lean`, 643 lines. Chart balls and their
connectedness; ball hops and ball chains, with all the transport algebra inherited from the chart
level; the key lemma that the transport sign is constant on a ball, so that **every** orientation
is ball-coherent, which is false for a chart domain and is exactly what the counterexample above
shows; and the **exact dichotomy**, with no extra hypothesis: a connected manifold is orientable
if and only if no loop of balls reverses an orientation, and a connected non-orientable manifold
carries a reversing loop of balls at every point. Boundarylessness is needed by 24 of the 61
declarations, for two reasons, both because a chart target has to be open. So item 6a is closed.

**6b. The mod 2 endgame.** The count modulo 2 of a framed 0-submanifold is its cardinality, so
`countMod2 (pontryagin …) = degMod2 f` should be almost immediate. What has to be reproved is the
cancellation: with a reversing loop, any two points can be brought to opposite frames, so pairs
cancel without signs, and the parity is a complete invariant. Then Milnor's statement follows with
the converse of Theorem B, which is orientation-free.

The staged plan is `Exposition/PlanMod2.md`, nine stages, revised estimate about 2,600 lines. State
of play, 2026-09-28:

* **Stage 1 done**: `Chapter7/ChartSign.lean`, 548 lines. The chart sign, the self sign and the
  Jacobian sign, with the cocycle formula relating them, and the bridge
  `frameSign = orEps · selfSign`: the sign of a frame against an orientation of the manifold is the
  determinant sign of the frame read in one chart, times a factor depending only on the point. The
  factor mentions no frame and the sign mentions no orientation, which is what lets the local
  machinery run on a non-orientable manifold. Also frames of either sign at every point, and a frame
  transported to another point of the same chart with the same sign. The self sign needs no
  chart-membership hypothesis, which the plan did not notice and which makes it the better primitive
  for the clopen arguments later.
* **Stages 2 and 3 done**: the same restatement applied to the existing local lemmas, in the seven
  files `MoveAux`, `MoveH`, `CancelH`, `Move`, `Cancel`, `AddPoint`, `Reach`, which go from 1,808
  to 1,939 lines. `MoveH` and `CancelH` no longer mention an orientation at all: six theorems lost
  two hypotheses each, and the lemma asserting that a chart derivative is bijective, whose
  hypothesis "the chart preserves orientation" was spurious, is deleted in favour of the general
  one. Moving a point, cancelling two points, adding a point and the good-ball lemma are now
  orientation-free, and the sign of the frame at a zero of the cancelling map is flatly the sign
  of the signed distance, where before it carried a factor depending on the orientation. The
  proof of "frames of both signs at a point" collapses from 65 lines to one.
  *Where the plan was wrong:* four declarations cannot be restated in place, because
  `CancelStep.lean` and `Hopf.lean` call them in their oriented form; the sign-free statement now
  carries the proof and the oriented one is a short corollary beside it, so no proof is
  duplicated. The plan's predicted net saving of 60 lines is therefore a net cost of 131.
  The oriented Hopf theorem is untouched and still checks.
* **Stage 4 done**: `Chapter7/BallChainSign.lean`, 780 lines (the ball hops and the exact
  dichotomy were already done as stage three of 6a above). The sign dictionary: transport across
  a chart, along a hop, and along a chain is multiplication by a sign, the sign of a composite is
  the product, the sign of a reverse is the same, and a loop reverses exactly when its sign is
  `−1`. It all works for arbitrary chart chains, not only ball ones, at no extra cost. The
  transition cocycle lemma: neither Jacobian sign is continuous in the point, because each reads
  a fixed chart through the moving chart, but in the product the moving chart cancels and what is
  left is the determinant sign of a fixed smooth transition, hence locally constant. And ball
  chains that avoid a set, with two hypotheses weaker than the plan asked: the avoided set need
  not be closed, only disjoint from the region, and the region need only be preconnected. One
  hypothesis had to be added, and the later stages must supply it: the plan phrases avoidance
  through the topological closure of each ball, which is not available in this generality, since
  on a non-Hausdorff manifold the closure of a chart ball need not lie in its chart. The file
  works with closed chart balls instead and gives the closure form under `[T2Space M]`, which is
  free in Chapter 7, where the manifolds are subsets of a Euclidean space.
  *To add when the halves are joined:* the one-line bridge identifying the concrete
  `Milnor.Framed.jacSign` of Stage 1 with the abstract `Milnor.jacSign` of this file.
* **Stage 5, first half done**: `Chapter7/Puncture.lean`, 412 lines. A punctured chart ball is path
  connected, the complement of a finite set in a connected manifold is connected, the complement of
  the other points of a finite set is that connected complement, and a nonempty open set is
  infinite. The hypothesis `2 ≤ m` is **sharp** for the two connectedness statements, not merely
  convenient: for `m = 1` a punctured ball is an interval minus an interior point, and `ℝ` minus a
  point is a disconnected complement of a finite set in a connected 1-manifold. So the dimension
  restriction the final theorem will carry comes from exactly here. No separation hypothesis is
  needed anywhere: charts give `T1` for free.
* **Stage 5, second half done**, so the risky stage is closed: `Chapter7/Puncture.lean` is now 722
  lines, and the plan's primary route worked, with no recourse to the fallback. A ball-coherent
  family of orientations on the complement of a finite set extends to an orientation of the whole
  manifold: the value at a puncture is the value at a nearby point transported back, well defined
  because that assignment is locally constant on a punctured ball, which is where the cocycle
  lemma earns its keep, and because a punctured ball is connected. Two things came out cleaner
  than the plan expected: well-definedness holds at every point, not only at the punctures, so the
  extension is one total function with no case split, and the transport-section condition is then
  checked at every point at once in three lines. Hence the punctured dichotomy: a connected
  non-orientable manifold of dimension at least two has, at any point outside a given finite set,
  a reversing loop of balls avoiding that set. One small lemma had to be added, that no point of a
  manifold of positive dimension is isolated. A locally constant function on a connected set is
  constant had to be proved by hand: Mathlib's version wants a discrete target, and the two
  orientations of a vector space carry no topology.
* **Stage 6 done**: `Chapter7/Slide.lean`, 561 lines, and the flip works: given a reversing loop
  of balls at a point of a framed 0-manifold avoiding the others, the manifold is framed cobordant
  to one with the same points, the same frames elsewhere, and the sign at that point reversed.
  With it, the frame at a point may be replaced by any tangent independent frame, and a point may
  be moved anywhere in its component with any frame, which is the oriented reach lemma with the
  orientation and its sign hypothesis simply deleted. No orientation, no connectedness, no
  `2 ≤ m` and no Hausdorffness appear in the file; the only dimension hypothesis is `0 < m`.
  *Where the plan was wrong:* one ball hop cannot be performed by one move, because a move needs
  its two points inside a quarter-radius ball whose closed ball fits in the chart, while a hop's
  endpoints can be almost a full diameter apart, and the chart target need not contain a ball four
  times as large. So each hop is subdivided, and the sign must be shown not to notice the
  subdivision: that needed an open-set form of the cocycle lemma and a change-of-hub lemma, which
  is where the invariant carried across a hop turns out to be the chart sign at the hop's own hub.
  *An improvement on the plan:* the sign-free reach lemma needs the reversing loop only at the
  starting point, not at the target.
* **Stages 7 and 8 done**: `Chapter7/CancelFree.lean`, 265 lines, and `Chapter7/CountMod2.lean`,
  242 lines. Frames at two points may be changed to anything at all, with no condition relating
  them; the cancel step loses its opposite-sign hypothesis outright; and two framed 0-manifolds of
  a connected manifold with the same count modulo 2 are framed cobordant, the count modulo 2 of a
  Pontryagin manifold being Milnor's mod 2 degree for any independent frame.
  *Where the plan was wrong, and this is the point of the remark:* it prescribed choosing an
  arrival frame of the opposite sign and replacing the old case split by a new one. Neither is
  needed. The cancellation lemma supplies its own two frames, of chart signs `+1` and `−1`, and
  "frames are free at two points" connects any configuration to that one, so the arriving frame
  may be arbitrary and the case split disappears rather than being replaced. The sign-free cancel
  step is therefore *shorter* than the signed one. The induction is simpler too: the signed proof
  can only cancel while both signs occur and needs a separate gathering argument when they do not,
  whereas here there is no gathering step at all and the stopping condition is just "each side has
  at most one point". Stage 6's improvement is used exactly there: the loop is needed only at the
  point that moves.
* **Stage 9 done, so item 6 is closed**: `Chapter7/HopfMod2.lean`, 259 lines, of which 45 are
  tactics. **Milnor's theorem of p. 50 is proved:** for a closed connected non-orientable
  manifold `M` of dimension `m`, presented as a compact nonempty slice submanifold of a Euclidean
  space and with `2 ≤ m`, two smooth maps `M → Sᵐ` are smoothly homotopic if and only if they have
  the same degree modulo 2. The easy half holds with no orientation anywhere and no hypothesis on
  `M` beyond compactness, and needs `0 < m` only because `degMod2` wants a connected target. The
  substantial half runs through Sard, positively oriented bases on the sphere, the two Pontryagin
  manifolds, the parity bridge, the parity classification and the converse of Theorem B. The only
  orientations in the whole argument are orientations of the **target sphere**; the source carries
  none, and is assumed not to have one.
  The hypothesis `2 ≤ m` is empty mathematics, since a connected 1-manifold is the circle or an
  interval and both are orientable, and it enters at exactly one point, the appeal to Stage 5. It
  can be deleted from all four statements in one line once item 7 below is formalized.
* Remaining, if wanted: the plan's optional Stage 10, the framed converse, which would make the
  parity classification an equivalence on the framed side as well.

## 7. The classification of one-manifolds (Appendix, book p. 54)

Every smooth connected one-manifold is diffeomorphic to the circle or to an interval. The Appendix
in this project is topological and proves the consequence the book uses, that a compact
one-manifold has an even number of boundary points, in a stronger form. Milnor's proof runs through
arc-length parametrization, which needs a Riemannian metric; the alternative is to use that
transitions between one-dimensional charts are strictly monotone diffeomorphisms and to glue a
maximal chain of charts. Mathlib has smooth partitions of unity and smooth bump functions, path
length and integral curves, but no metric-existence theorem and no classification.

A design pass is written up in `Exposition/PlanOneManifold.md`, which revises the estimate to
about 4,000 lines in nine stages and recommends Milnor's own route, built on top of the existing
topological Appendix rather than beside it: the hard, topological half of his Lemma 1 is already
proved there, and the existing 370-line gluing construction already glues with an affine change
of coordinate, which is exactly what unit-speed arcs produce. Three findings worth recording.
Mathlib's arc-length file is of no use here: its unit speed is metric variation, not derivatives,
and its reparametrization is a set-theoretic inverse with no smoothness. Existence of a
Riemannian metric is the one piece of general theory needed and Mathlib does not have it, though
the right engine for it does exist. And the classification is false without a countability
hypothesis, the long line being a connected smooth 1-manifold that is neither the circle nor an
interval, so the non-compact case must assume σ-compactness; Milnor's manifolds sit in Euclidean
space and get it for free. Two cheap spin-offs: in the smooth setting the Appendix's
`BoundaryCompatible` hypothesis becomes a theorem, and Milnor's Appendix Lemma 1 can be stated in
general, without the assumption that the arc starts at a boundary point.

State of play, 2026-09-28:

* **Stage 2 done**: `Appendix/TwoComponents.lean`, 463 lines. Milnor's Appendix Lemma 1, the
  topological half, in full: the overlap of two arcs has at most two components, and if it has two
  they reach opposite ends of the first arc, which is the circle case, now counted rather than
  excluded. The idea the existing file lacked is to single out the *inner* component, the one with
  both ends interior: it runs off both ends of the other arc at once, so its image is that arc's
  whole target, and injectivity then makes it the only component. The old file's normalisation, an
  arc starting at a boundary point, turns out to have been doing nothing essential. Two byproducts:
  the inner case is exactly the case where one arc sits inside the other, and an inner component
  forces the other arc to have no boundary point at all.
* **Stage 0 done**: `Appendix/Smooth/Setup.lean`, 820 lines. The one-dimensional model classified
  into three shapes, the line, a closed half-line, and a compact interval, which is a one-manifold
  *with corners* and is kept alive throughout; a real coordinate on every chart, with the fact
  that a chart's coordinate image is an open set cut by the model range; unique differentiability
  along the model range, so `derivWithin` is unambiguous at an endpoint; the chart-independence of
  boundary points, from Mathlib's `C¹` theorem; and the two normalised local models. **The
  Appendix's `BoundaryCompatible` hypothesis is now discharged** for a smooth one-manifold with a
  half-line model, with no extra hypothesis at all, so the existing counting theorem applies to
  smooth one-manifolds with no side condition. `C¹` suffices everywhere. Three risks the plan
  flagged were all handled: the compact-interval case stays live, interior charts are shrunk away
  from the model's own endpoints, and the sign of the identification with `ℝ` is normalised both
  globally and at an endpoint, the local sign mattering because it keeps the far endpoint out of a
  normalised chart.
* **Stage 1 done**: `Appendix/Smooth/SmoothArc.lean`, 630 lines. A smooth arc extends the
  topological one with smoothness both ways, so the whole existing API is inherited; the
  transition between two smooth arcs is smooth with nowhere-vanishing derivative, the two
  transition derivatives multiplying to one; a smooth arc is an immersion; and every point lies in
  the source of one, with target `[0, ε)` at a boundary point and `(−ε, ε)` elsewhere. The
  half-open smoothness that the plan flagged as the technical heart cost nothing: Mathlib's
  `ContMDiffOn` is already relative to the given set, so at an endpoint it *is* the one-sided
  condition. The one real wrinkle was that a transition is defined only on a relatively open piece
  of the target, so a derivative is computed there and then transported to the whole target.
* **Stages 3 and 4 done**, and the riskiest stage came through in full generality, with neither of
  the plan's fallbacks: `Appendix/Smooth/LengthElement.lean`, 595 lines, and `ArcLength.lean`, 720
  lines. A length element is a density indexed not by charts but by *local real parameters*, which
  covers both a chart read in Stage 0's coordinate and a smooth arc, so that it can be evaluated
  along an arc with no intermediate layer. Its engine is the transition-derivative calculus on
  possibly half-open sets: the chain rule at an endpoint, non-vanishing, smoothness. Existence
  needs exactly four things: dimension one, `C^∞` (Mathlib's partitions of unity are built from
  smooth bumps, and a transition derivative loses a degree), Hausdorff and σ-compact — the last
  two only here, in the whole of stages 3 and 4. No boundarylessness, and all three model shapes
  stay alive.
  Unit-speed arcs exist at every point, with targets `[0, ε)` and `(−ε, ε)`. The plan's "second
  soft spot", the one-sided smooth inverse, was proved rather than dodged: Mathlib has only the
  two-sided inverse function rule, which says nothing at an endpoint, so the one-sided rule is
  proved from the elementary identity relating the two slopes, and smoothness of the inverse then
  follows by bootstrapping on the order. Two devices made the endpoints painless: all the analysis
  happens on a compact interval inside the target, where Mathlib's fundamental theorem of calculus
  is available at the endpoints and compactness gives continuity of the inverse; and the window is
  chosen in the *new* parameter, since arc length need not be symmetric about the base point.
* **Stage 5 done**: `Appendix/Smooth/Affine.lean`, 929 lines. The transition between two unit-speed
  arcs has derivative of absolute value one, hence constant sign on each component of the overlap,
  hence is `s ↦ ±s + k` there; with Stage 2 that is **Milnor's Appendix Lemma 1 in full**, and it
  needs no dimension hypothesis, no manifold instance and no compactness — only Hausdorffness,
  where the existing overlap API demands it. And the extension theorem, in the strong form the
  whole design was for: the extended arc's coordinate *equals* the old one on the whole of the old
  source, and its source is the union of the two.
  *Where the plan was wrong, and it matters for the later stages:* the existing topological
  extension theorem cannot be reused with smoothness added. Its conclusion is an existential that
  forgets the witness's coordinate, and from the statement alone one can recover only that the
  transition is an increasing homeomorphism fixing `0` — it could be `s ↦ s²`. So the theorem was
  restated for smooth arcs, reusing the topological apparatus beneath it and transcribing the
  parts of its proof that carry over. About 75 lines of the original then *disappear*: both
  one-sided limit computations at the junction and the trichotomy proofs of continuity there, and
  they disappear because with unit-speed arcs the two branches are the same affine function on the
  whole overlap, not merely near the seam, so there is no junction to be continuous at.
* **Stage 6 done, and the first of Milnor's four cases is proved**: `Appendix/Smooth/Compact.lean`,
  421 lines. A compact Hausdorff preconnected smooth one-manifold with a boundary point is
  diffeomorphic to `[0, 1]`, and its boundary is exactly two points, `p` and the far end of the
  exhausting arc — which identifies them, where the existing theorem only counted them modulo two.
  The diffeomorphism is the arc itself, rescaled by its total length, and the conversion through
  Mathlib's two `Icc` bridges cost about twenty lines, the cheapest part rather than the dearest.
  Three things worth recording. Connectedness is needed nowhere in the exhaustion: the honest
  conclusion is about the component of `p`, which is the form the assembly will want. Compactness
  is used three times, and only one of those uses is really σ-compactness in disguise, which is
  why the compact case needs no countability hypothesis. And the existing finite-cover induction
  had to be restated for a third reason the plan did not foresee: it demands a homeomorphism of
  the model space with the half-line, which does not exist when the model range is a compact
  interval — a shape Stage 0 deliberately admits.
* **Stage 7 done, and the second of Milnor's four cases is proved**: `Appendix/Smooth/Circle.lean`,
  1,712 lines. A compact Hausdorff connected nonempty boundaryless smooth one-manifold is
  diffeomorphic to `Circle`, and on the way: such a manifold *is* a closed geodesic — there are a
  length element, a least period `T` and a unit-speed map of the line onto it which identifies two
  times exactly when they differ by a multiple of `T`.
  *Where the plan was wrong, and this is the substantive correction of the whole programme:* the
  exhaustion by arcs does not exist in the boundaryless case. Every arc of a manifold with empty
  boundary has an **open** target, while the extension theorem needs the first arc's target to be
  half-open, i.e. to start at a boundary point. So Stage 6's induction has no boundaryless
  analogue in the shape the plan assumed. The replacement is to drop injectivity: a *unit-speed
  curve* is a map of the line agreeing near each time with the arc-length parametrisation of an
  arc, and the engine is a **propagation lemma** — two unit-speed curves agreeing near one time
  agree on the whole interval — proved by a connectedness argument run in the parameter of one arc
  rather than in the time, because the set of times of local agreement need not be closed, and the
  obstruction is exactly that an overlap can have two components. With curves, continuation needs
  no gluing of injective arcs and no two-component bookkeeping at all.
  Two more things fell out. The geometric fact the plan singled out as the one part of Milnor's
  Step 5 with no counterpart in the existing file — that two times with the same value have
  matching directions — is proved by excluding a reflection through local injectivity. And Stage 2
  turns out **not** to be used here: what Stage 7 needs from the topological file is the relative
  openness of hulls and Stage 5's affine half, not the counting of components. Stage 2 remains the
  right statement of Milnor's lemma; the plan's dependency claim was wrong.
  One friction worth recording: Mathlib's tangent spaces carry no norm, so "a nonzero linear map
  between one-dimensional spaces is invertible" had to be stated for topological modules with the
  inverse supplied as data, which a left inverse built from the circle's two coordinate functions
  provides.
* **Stage 8 done, so all four of Milnor's cases are proved**: `Appendix/Smooth/NonCompact.lean`,
  2,202 lines. A connected Hausdorff σ-compact non-compact smooth one-manifold is diffeomorphic to
  `ℝ` when its boundary is empty and to `Ici 0` when it has a boundary point, which is then its
  only one. σ-compactness is used **once**, to build the length element, and that is exactly where
  the long line fails: a manifold carrying a Riemannian metric is metrizable, so the long line
  carries none and arc length has nothing to start from. Milnor gets the hypothesis for free by
  sitting in Euclidean space, and uses it silently when he restricts the Euclidean metric.
  No inverse function theorem is used anywhere in the file: the four shapes of open interval and
  the two of half-line are parametrized explicitly, with their logarithmic or rational inverses
  written down. `Ici 0` had to be given its manifold structure, since Mathlib has only `Icc`; it
  is a one-chart manifold with boundary, its chart being a homeomorphism onto the whole model
  half-space.
  *Corrections to my own sketch, both instructive:* a repeated value gives a period only once the
  curve is known to run on the whole line, which here it need not, so injectivity is proved
  instead from the fact that a repeated value makes the image of one compact interval of times
  both compact and open, hence everything; and a unit-speed curve cannot take a boundary value at
  all, so it cannot run on a closed half-line of times — the boundary point has to be adjoined by
  hand, and showing that no *second* boundary point appears in the closure is the long step, and
  the only place non-compactness is used in that case.
* **Stage 9 done, so item 7 is closed and Milnor's Appendix theorem is proved**:
  `Appendix/Smooth/Main.lean`, 784 lines. A connected Hausdorff σ-compact smooth one-manifold is
  diffeomorphic to **exactly one** of the circle, `[0, 1]`, `[0, ∞)` and `ℝ`, keyed to whether it
  is compact and whether its boundary is empty. All six exclusions are proved: compactness settles
  four, and the number of boundary points — a diffeomorphism invariant, by Mathlib's theorem that
  a diffeomorphism carries boundary onto boundary, stated for two different models with corners —
  settles the remaining one in each compactness class.
  The slice form is the one the book uses: for a compact one-manifold with boundary in Chapter 2's
  sense, every component is the circle or `[0, 1]`, the components with a boundary point are
  exactly the `[0, 1]`s, each contributes exactly two boundary points, and the boundary is finite
  of even cardinality — **derived from the classification**, with the pairing realised by the two
  ends of one arc-length parametrization, rather than by the old parity argument. The old theorem
  is left untouched and is still what Chapters 2 and 4 use.
  Three bridges had to be built, and the project will want all three: connected components of a
  smooth one-manifold are **open**, hence manifolds in their own right, which is what lets the
  classification apply to a disconnected manifold and is the piece the plan never mentions; the
  boundary of the half-line model is a single point, which Mathlib could not supply since it has
  no half-line manifold; and the boundary count for a possibly disconnected compact one-manifold,
  whose *finiteness* is the harder half and could not reuse the existing theorem, because that one
  wants a compatibility hypothesis available only when the model range is a half-line.
  Two things the plan got right paid off: stating Stage 6's exhaustion for the *component* of a
  boundary point made the disconnected case cheap, and giving each model its own model with
  corners cost nothing.


## Not planned

The identification of the index sum with the Euler characteristic (item 5 above), for the reason
given there.

## Registration and checks

Every finished file is imported by `Milnor.lean` and its main results are listed in
`Milnor/Test.lean`, which now checks **175** theorems; `lake build` passes (8,883 jobs) and every
one of the 175 depends only on propext, Classical.choice and Quot.sound.
