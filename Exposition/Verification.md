# Milnor, verified: the machine-checked edition

*A companion to the entertaining edition of Milnor's "Topology from the Differentiable Viewpoint".
That edition is written to be read; this one is written to be checked. It records, chapter by
chapter, exactly which statements of the book have been verified by the Lean 4 proof assistant
against the Mathlib library, what each verified statement says when read back in ordinary
language, which hypotheses the book left silent, where the formal proof departs from the book's,
and what remains unverified and why. Nothing here needs to be read in Lean; every checked
statement is restated in prose, and the Lean names are given only so that the claims can be
audited.*

---

## 0. Summary

| Chapter | Content | Status | Lean lines |
|:-----|:----------------------------------------------------------------|:------------|:------|
| 1 | Manifolds, tangent spaces, inverse function theorem, regular values, local constancy of the count, the counting principle, the fundamental theorem of algebra | **verified** | 1,304 |
| 2 | Regular values in unequal dimensions, level sets are manifolds (Lemma 1, both clauses of Lemma 2), manifolds with boundary (Lemma 3), level sets in manifolds with boundary (Lemma 4), the disk | **verified** | 1,685 |
| 2 | No retraction of the disk (Lemma 5), the smooth retraction (Lemma 6), Brouwer's fixed point theorem for smooth and for continuous maps | **verified** | 562 |
| 3 | Sard's theorem, with Milnor's proof; Brown's theorem | **verified** | 1,112 |
| 4 | Lemma 4 for the cylinder, the Homotopy Lemma, the Homogeneity Lemma, the Theorem (both assertions) and the degree modulo 2, surjectivity of maps of nonzero degree | **verified** | 894 |
| 5 | Orientations, the sign of a derivative, Lemmas 1 and 2, Theorems A and B, the Brouwer degree, the degree of the antipodal map, the hairy ball theorem | **verified** | 3,096 |
| 6 | The index of a vector field, the region lemma, Hopf's lemma, invariance of the index under diffeomorphisms (Lemma 1), Lemma 2 by way of Hadamard's lemma, the index of a non-degenerate zero (Lemma 4), the chart definition of the index and Lemma 5, the $\varepsilon$-neighbourhood theorem, the Poincaré–Hopf theorem for compact submanifolds of Euclidean space, the Euler number of the sphere | **verified** | 7,153 |
| 7 | Framed submanifolds and framed cobordism, the Pontryagin manifold, Lemmas 1–4, Theorem A, Theorem B in both directions, the Product Neighborhood Theorem, Theorem C, framed cobordism as an equivalence relation, the Hopf theorem, orientability of a manifold and the orientability dichotomy, the orientability of every connected one-manifold, the mod 2 theorem of p. 50 with no dimension hypothesis | **verified** | 19,823 |
| 8 | Milnor's seventeen problems: degree of a composition, polynomials, maps between spheres, smoothing, products, graphs, tangent and normal bundles, the retraction, linking numbers, the Hopf invariant and the Hopf fibration, transversality, the intersection product and the group of framed cobordism classes | **verified** | 16,166 |
| Appendix | Milnor's Appendix Lemma 1 in full, the length element and unit-speed arcs, the classification of the connected one-manifolds as exactly one of the circle, $[0,1]$, $[0,\infty)$ and $\mathbb R$, and the boundary count of a compact 1-manifold with boundary, proved twice over — for topological 1-manifolds and again from the classification | **verified**, in full and in a stronger form | 11,054 |

Total: 62,849 lines of Lean in 176 files (each row counts the lines of that chapter's directory of
Lean files, as `wc -l` gives them; a few results sit in another chapter's files and are counted
there, such as the strengthened V1.4, written for Chapter 5 and kept in Chapter 1, Milnor's Lemma 2
of §6 (V6.12), whose last step is Chapter 7's $GL^+$ path and which therefore lives in Chapter 7's
directory, and the orientability of one-manifolds (V7.27), which rests on the Appendix and is kept
in Chapter 7 with the mod 2 theory it was written for; the Appendix row now counts all twelve of
its files, the two that prove V.A and V.A′ and the ten of the classification), no `sorry`, every
verified theorem depending only on the three standard axioms of Lean's Mathlib (`propext`,
`Classical.choice`, `Quot.sound`). Toolchain: Lean
4.33.1, Mathlib as of September 2026. To reproduce: in the project directory run `lake build`,
then `lake env lean Milnor/Test.lean`, which prints the axioms of the 175 main theorems.

The dividing line is exact. Everything the book proves in §1–§6 and in the Appendix is checked,
including Brouwer's fixed point theorem, both degrees, the hairy ball theorem and its converse,
the $\varepsilon$-neighbourhood theorem of §8, and the Poincaré–Hopf theorem for compact
submanifolds of Euclidean space; the Appendix is checked both as Milnor states it, his four cases
proved mutually exclusive, and in a form stronger than he states it, the boundary count holding for
topological 1-manifolds. Two things in §6 are done differently from the book and are flagged as such (V6.5, V6.8):
Milnor's Lemma 2 is replaced by a direct sign computation, and the index of a field on a
submanifold is *defined* through Milnor's extension to a tubular neighbourhood rather than
through charts. Both detours are now also bridged: Lemma 2 itself is proved (V6.12, by way of
Hadamard's lemma, V6.11) although nothing uses it, and Milnor's chart definition of the index is
formalized and shown to agree with the definition used here at a non-degenerate zero (V6.13,
V6.14, his Lemmas 5 and 4). Everything through §8 is checked: all of Chapter 7 including the Hopf
theorem and the mod 2 theorem of p. 50 for a non-orientable manifold (V7.26), which now carries no
dimension hypothesis at all, that hypothesis having been derived from non-orientability itself
(V7.27, V7.28), and all seventeen
problems of Chapter 8 (§9). One value in the problems is not what the book's conventions give: the
Hopf fibration has Hopf invariant $-1$ (V8.15). Milnor's Appendix theorem is checked too (§10,
V.J): a connected Hausdorff $\sigma$-compact smooth one-manifold is diffeomorphic to **exactly
one** of the circle, $[0,1]$, $[0,\infty)$ and $\mathbb R$. What remains unverified — the
identification of the Poincaré–Hopf integer with the Euler characteristic, and the agreement of
the two index definitions at an arbitrary isolated zero — is listed in
§11.

---

## 1. How to read a verified statement

**The manifolds are abstract, the book's are embedded.** Milnor's manifolds are subsets of
$\mathbb R^k$. Mathlib's are abstract spaces with an atlas of charts, and every theorem here is
stated for those. Every Milnor manifold is a Mathlib manifold, so nothing is lost; but an abstract
manifold need not be Hausdorff or second countable, so where the book uses those properties
silently, the formal statement carries them as explicit hypotheses. The prose restatements below
list them.

**The statements are the contract.** A machine-checked proof guarantees that the *stated* theorem
follows from Mathlib's axioms. It guarantees nothing about whether the statement is the one you
wanted. So the reader's job, and the only mathematical judgement this document asks of them, is to
read each prose restatement and confirm that it says what Milnor means. Where the restatement is
weaker or stronger than the book, or uses a different but equivalent definition, this is flagged
with **Deviation**.

**What "smooth" means.** Throughout, smooth means $C^\infty$ (`ContMDiff I J ∞ f`). One subtlety
recurs: Mathlib's "smooth at a point" means "$C^n$ on some neighbourhood, for every $n$", with the
neighbourhood allowed to shrink with $n$. This does not give a single neighbourhood on which the
map is $C^\infty$. Theorems that need such a neighbourhood therefore assume smoothness on a
neighbourhood rather than at a point. For the book's maps, which are smooth everywhere, nothing
changes.

**Two formal conventions.** First, wherever a statement below assumes a manifold or a set to be
*connected*, the formal statement assumes only that it is *preconnected* (Mathlib's
`PreconnectedSpace`, `IsPreconnected`): it is not the union of two disjoint nonempty open pieces.
The only difference is that the empty set is preconnected, so the formal statements are slightly
more general than the prose, which keeps the word "connected". Second, several statements (Sard's
and Brown's theorems, and results of later chapters that rest on them, such as those of Chapters 4
and 5) require the model vector spaces of source and target to lie in the same universe of Lean's
type theory (in V8.5, the lowest one). This is a formality of the type theory with no mathematical content: every space in
the book is a finite-dimensional real vector space, and these all live in the lowest universe.

---

## 2. Chapter 1 (Milnor §1): verified

**V1.1 (the inverse function theorem on manifolds; `Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv`).**
Let $M$ and $N$ be smooth manifolds without boundary modelled on finite-dimensional real vector
spaces of the same dimension, $f : M \to N$ smooth on a neighbourhood of $x$, and suppose the
derivative $df_x$ is an invertible linear map. Then $f$ is a local diffeomorphism at $x$: there are
open sets $U \ni x$ and $V \ni f(x)$ such that $f$ restricts to a diffeomorphism $U \to V$.
*Hidden hypotheses:* none beyond the smoothness-on-a-neighbourhood convention.
*Deviation (stronger):* the formal statement allows real or complex scalars, maps of class $C^n$
for any $n \ge 1$ (including $C^\infty$ and analytic maps; the local inverse is then of the same
class), and a model space of $M$ that is only required to be complete, not finite-dimensional.
*Note:* Mathlib listed this theorem as an open TODO; it was proved here from the Euclidean inverse
function theorem by the chart argument of the entertaining edition, Chapter 1, Theorem 4.1.

**V1.2 (regular values; `Milnor.IsRegularPoint`, `Milnor.IsRegularValue`).** A point $x$ is a
regular point of $f$ if $df_x$ is surjective; $y$ is a regular value if every point of $f^{-1}(y)$
is regular. *Deviation:* Milnor defines regular points in §1 by invertibility and in §2 by
surjectivity; the formal definition is the §2 one, and `Milnor.IsRegularPoint.isInvertible_mfderiv`
proves that for equal dimensions the two agree. A point not in the image is a regular value
(`Milnor.IsRegularValue.of_notMem_range`).

**V1.3 (finiteness; `Milnor.IsRegularValue.finite_preimage`).** Let $M$ and $N$ be manifolds
without boundary. If $M$ is compact, points of $N$
are closed, $\dim M = \dim N$, and $y$ is a regular value of the smooth $f : M \to N$, then
$f^{-1}(y)$ is finite. *Hidden hypothesis:* points of $N$ closed (true when $N$ is Hausdorff).

**V1.4 (local constancy; `Milnor.IsRegularValue.eventually_ncard_preimage_eq`).** If moreover
$M$ and $N$ are Hausdorff, then for every $y'$ in some neighbourhood of $y$, $\#f^{-1}(y') =
\#f^{-1}(y)$. *Deviation (stronger):* the parenthesis on p. 8 in which Milnor introduces
the count speaks of regular values, but the sentence that follows it produces a neighbourhood $V$
of $y$ and asserts the equality for every $y' \in V$ without restriction, which is what the formal
statement proves.

**V1.5 (the counting principle; `Milnor.subset_range_of_isPreconnected`,
`Milnor.surjective_of_isPreconnected_regularValues`).** With $M$, $N$ without boundary, $M$
compact, $M$, $N$ Hausdorff, $\dim M = \dim N$: if $R \subseteq N$ is a connected set of regular
values containing a point of the image of $f$, then $R$ is contained in the image. If the set of all regular values is connected
and meets the image, $f$ is onto.

**V1.6 (the fundamental theorem of algebra; `Milnor.fundamental_theorem_of_algebra`).** Every
complex polynomial of positive degree has a root. The statement is exactly `∀ P : Polynomial ℂ,
0 < P.degree → ∃ z, P.IsRoot z`. *Deviation (route, not content):* the compact surface is the
Riemann sphere $\mathbb C \cup \{\infty\}$ with the two charts $z$ and $1/z$
(`Milnor.RiemannSphere`), not the unit sphere with stereographic projection; the two are
diffeomorphic (a standard fact, not formalized here and not needed). The point $\infty$ is put
into the bad set rather than shown to be regular. The
intermediate facts are checked as separate statements: the polynomial map is smooth
(`contMDiff_polyMap`), its critical values are finite (`critVals_finite`), the complement of a
finite set in the plane is connected (`isPreconnected_compl_critVals`), the image is infinite
(`infinite_range_eval`).

*Not formalized in Chapter 1:* the bridge between Milnor's definition of tangent space (image of
the derivative of a parametrization) and Mathlib's (a copy of the model space); the two-link arm.

---

## 3. Chapter 2 (Milnor §2): verified

**V2.1 (slice submanifolds; `Milnor.SliceChart`, `Milnor.IsSliceSubmanifold`).** Mathlib has no
notion of an embedded submanifold of an abstract manifold. This project defines one: a *slice
chart* for $S \subseteq M$ is a diffeomorphism from an open subset of $M$ onto an open subset of
$Z \times W$ under which $S$ corresponds to $Z \times \{0\}$; $S$ is a slice submanifold if it is
covered by slice charts. Verified: such an $S$ carries a smooth manifold structure modelled on
$Z$ (`IsSliceSubmanifold.isManifold`) and the inclusion $S \to M$ is smooth (`contMDiff_val`).

**V2.2 (Lemma 1; `Milnor.isSliceSubmanifold_preimage`).** Let $f : M \to N$ be smooth between
manifolds without boundary modelled on $E$ and $F$, with $\dim Z + \dim F = \dim E$, and $y$ a
regular value. Then $f^{-1}(y)$ is a slice submanifold of $M$ modelled on $Z$, hence a smooth
manifold of dimension $\dim M - \dim N$. *Hidden hypothesis:* the dimension bookkeeping is carried by the space $Z$.

**V2.3 (Lemma 2; `Milnor.mem_range_mfderiv_val_iff`).** In that situation, for $p \in f^{-1}(y)$
and $v$ a tangent vector of $M$ at $p$: $v$ is the image of a tangent vector of $f^{-1}(y)$ under
the inclusion if and only if $df_p(v) = 0$. That is, the tangent space of the level set is the
kernel of $df_p$. *Deviation (form):* stated elementwise rather than as an equality of subspaces,
to avoid coercions between tangent spaces of different manifolds.

**V2.4 (manifolds with boundary; `Milnor.HalfSpace`, `Milnor.halfSpaceModel`,
`Milnor.HalfSliceChart`, `Milnor.IsHalfSliceSubmanifold`).** A *half-slice chart* for $X$ with
boundary $B$ is a diffeomorphism from an open subset of $M$ onto an open subset of $\mathbb R
\times Z$ under which $X$ corresponds to $\{t \ge 0\}$ and $B$ to $\{t = 0\}$. Verified: a set
covered by half-slice charts is a smooth manifold with boundary in Mathlib's sense, modelled on
the half-space $\{(t,z) : t \ge 0\}$ (`isManifold`), and Mathlib's boundary of it is exactly
$X \cap B$ (`boundary_eq`); this is $B$ whenever $B \subseteq X$, as in every use. *Deviation:*
Milnor's "it is not hard to show that $\partial X$ is well defined" is not proved as a separate
theorem; the definition requires every chart to send exactly $B$ to
$\{t = 0\}$, and the manifolds with boundary that occur in the book are constructed with such
charts. The entertaining edition, Chapter 2, Claim 3.1, gives the prose proof of well-definedness
for the reader who wants it; it is not needed for anything downstream.

**V2.5 (Lemma 3; `Milnor.isHalfSliceSubmanifold_of_regularValue`).** Let $M$ be a manifold
without boundary modelled on $E$, $\dim Z + 1 = \dim E$, $g : M \to \mathbb R$ smooth with $0$ a
regular value. Then $\{g \ge 0\}$ is a half-slice submanifold with boundary $\{g = 0\}$.

**V2.6 (Lemma 4; `Milnor.isHalfSliceSubmanifold_levelSet`).** Let $M$ and $N$ be manifolds
without boundary modelled on $E$ and $F$, and let $Z$, $Z'$ be spaces with $\dim Z + \dim F =
\dim E$ and $\dim Z' + 1 = \dim Z$ (the dimension bookkeeping, as in V2.2). Let $f : M \to N$ be
smooth, $y$ a regular value of $f$ on all of $M$, $g : M \to \mathbb R$ smooth, and suppose the
transversality condition: for every $x$ with $f(x) = y$ and $g(x) = 0$ there is a tangent vector
$v$ with $df_x(v) = 0$ and $dg_x(v) \ne 0$. Then inside the manifold $f^{-1}(y)$ (with the
structure of V2.2, modelled on $Z$), the sets $\{g \ge 0\}$ and $\{g = 0\}$ form a half-slice
submanifold modelled on the half-space over $Z'$: $f^{-1}(y) \cap \{g \ge 0\}$ is a manifold with
boundary $f^{-1}(y) \cap \{g = 0\}$. *Deviation (form):* Milnor's hypothesis "$y$ is a regular
value of $f|_{\partial X}$" is replaced by the transversality condition displayed, which is what
that hypothesis is used for in his proof (the dimension count in the entertaining edition,
Chapter 2, Lemma 4.1). The manifold with boundary is presented as $\{g \ge 0\}$ inside a manifold
without boundary; this suffices for every application in the formal text (V2.10, V4.1 and V5.3
use it), but not for Milnor's statement for an arbitrary manifold with boundary. *Deviation
(hypothesis):* $y$ must be a regular value of $f$ on the whole of $M$, not only on $\{g \ge 0\}$
as in Milnor; this holds in every application.

**V2.7 (the disk; `Milnor.isHalfSliceSubmanifold_unitDisk`).** For every $m \ge 0$, the closed
unit ball of $\mathbb R^{m+1}$ is a half-slice submanifold, modelled on the half-space over
$\mathbb R^m$, with boundary the unit sphere $S^m$, via $g(x) = 1 - \|x\|^2$. (The ambient space
has positive dimension; for $\mathbb R^0$ the ball is a point and the statement would be false.)

**V2.8 (corestriction; `Milnor.IsSliceSubmanifold.contMDiff_codRestrict`).** A smooth map into
$M$ whose values lie in a slice submanifold $S$ is smooth as a map into $S$. Milnor uses this
silently whenever he treats a map into $\partial X \subseteq X$ as a map into the manifold
$\partial X$.

**V2.9 (Lemma 6, the retraction formula; `Milnor.Retraction.norm_retr`, `retr_eq_self`,
`closedBall_subset_good`, `contDiffOn_retr`).** For $P : E \to E$ and $u = (x - Px)/\|x - Px\|$,
$t = -\langle x,u\rangle + \sqrt{1 - \|x\|^2 + \langle x,u\rangle^2}$, $f(x) = x + t\,u$: on the
set where $x \ne Px$ and the radicand is positive, $\|f(x)\| = 1$; this set is open when $P$ is
continuous (`isOpen_good`), and $f$ is smooth on it when $P$ is smooth (`contDiffOn_retr`); if
moreover $\|x\| = 1$ and $\|Px\| \le 1$ then $f(x) = x$; and if $P$ maps the closed unit ball into
itself without fixed points, the ball lies in that set. This is Milnor's "it is easy to
verify", done: the positivity of the radicand on the sphere uses $\langle x, Px\rangle = 1$,
$\|x\| = 1$, $\|Px\| \le 1 \Rightarrow Px = x$.

**V2.10 (Lemma 5 for the disk, and the smooth fixed point theorem;
`Milnor.exists_fixedPoint_of_contDiff`).** Let $E$ be a finite-dimensional real inner product
space with closed unit ball $D$. Every map $P : E \to E$ which is smooth on all of $E$ and maps $D$
into itself has a fixed point in $D$. *Proof as in the book:* if not, the
retraction $f$ of V2.9, extended to all of $E$ by a smooth cutoff and corestricted to the sphere by
V2.8, has a regular value $y$ on the sphere by Brown (V3.3); the transversality condition of V2.6
holds at $y$ because $f$ is the identity on the sphere, which is checked through V2.3 and the chain
rule; so by V2.6 the level set $f^{-1}(y) \cap D$ is a compact 1-manifold with boundary
$\{y\}$, contradicting V.A′. *Deviation (form):* Milnor's Lemma 5 is stated for any compact
manifold with boundary; only the disk is needed and only the disk is proved. Milnor's Lemma 6
concerns a smooth map of the disk to itself; here $P$ is assumed smooth on all of $E$ (nothing is
lost for the book, since V2.11 covers every continuous self-map of the ball). The domain of the
retraction is all of $E$ rather than the disk, which is why no manifolds with boundary appear as
domains; the cutoff makes this possible.

**V2.11 (Brouwer's fixed point theorem; `Milnor.exists_fixedPoint`).** Every map $G$ that is
continuous on the closed unit ball of a finite-dimensional real inner product space and maps it
into itself has a fixed point. *Proof as in the book*, with one substitution: the polynomial
approximation is replaced by an approximation by smooth maps, obtained from the Stone–Weierstrass
theorem applied to the subalgebra of continuous functions on the ball that extend to smooth
functions on $E$ (`smoothSubalgebra`, `exists_contDiff_approx`); the rescaling by $1 + \mu/2$ and
the final estimate are Milnor's. *Hidden hypothesis:* none; the statement is for a general
finite-dimensional inner product space, of which $\mathbb R^n$ is the case in the book.

**V2.12 (Lemma 2, second clause; `Milnor.tangentSubspace`,
`Milnor.mfderiv_injOn_tangent_orthogonal`, `Milnor.mfderiv_surjOn_tangent_orthogonal`,
`Milnor.normalEquiv`).** In the situation of V2.2 and V2.3, write $T \subseteq E$ for the tangent
space of the level set at $p \in f^{-1}(y)$, realised inside the model space $E \cong T_pM$ as the
range of the derivative of the inclusion (`tangentSubspace`). Then $df_p$ is injective on the
orthogonal complement $T^\perp$ and carries it onto $TN_y$, so it restricts to a linear
isomorphism $T^\perp \to TN_y$ (`normalEquiv`, whose underlying map is $df_p$ itself). This is the
second sentence of Milnor's Lemma 2 (p. 11), the one that follows "therefore" from the description
of the kernel. *Hidden hypothesis:* an inner product on the model space $E$
of the source, in place of the bare norm of V2.2 and V2.3; the orthogonal complement is taken in
$E$. Milnor has this for nothing, his manifolds being subsets of $\mathbb R^k$; the target $N$
needs no inner product, and $M$, $N$ and the boundaryless model are otherwise as general as in
V2.3. *Proof as in the book:* the dimension count Milnor leaves to the reader. Since $y$ is a
regular value, $T = \ker df_p$ has dimension $\dim E - \dim F$, so $\dim T^\perp = \dim F$;
injectivity on $T^\perp$ is the first clause (V2.3) together with $T \cap T^\perp = 0$, and
surjectivity follows because an injective map between spaces of equal finite dimension is onto.

*Not formalized in Chapter 2:* the general Lemma 5 (for a compact manifold with boundary other
than the disk) and Claim 3.1 of the entertaining edition (well-definedness of the boundary),
neither of which anything in the book uses.

---

## 4. Chapter 3 (Milnor §3): verified

**V3.1 (Sard's theorem; `Milnor.sard`).** Let $E$, $F$ be finite-dimensional real normed spaces,
$U \subseteq E$ open, $f : U \to F$ smooth. Let $C$ be the set of points of $U$ where $df$ is not
surjective. Then $f(C)$ has measure zero for every Haar measure on $F$. *Deviation (stronger):*
stated for abstract finite-dimensional spaces and arbitrary Haar measures rather than for
$\mathbb R^n \to \mathbb R^p$ with Lebesgue measure. This was a necessity, not a flourish: the proof
is an induction on $\dim E$ that passes to hyperplanes, which are not literally $\mathbb R^{n-1}$.

**V3.2 (dense regular values; `Milnor.dense_compl_image_critSet`).** In the same setting, the
complement of $f(C)$ is dense in $F$.

**V3.3 (Brown's theorem on manifolds; `Milnor.dense_regularValues`).** Let $M$ be a second
countable smooth manifold, $N$ a smooth manifold, both without boundary, $f : M \to N$ smooth.
Then the regular values of $f$ are dense in $N$. *Hidden hypothesis:* $M$ second countable, which
is Milnor's "covered by countably many neighbourhoods" and is automatic for subsets of
$\mathbb R^k$. The target $N$ carries no measure; the proof uses one on the model space of its
charts.

**How the formal proof follows the book, and where it does not.** The proof is Milnor's three
steps, with his coordinate change $h(x) = (w(x), x_2, \dots, x_n)$ formalized as a structure
(`Milnor.Sard.Straightening`, `exists_straightening`) built on V1.1. Step 1 (`step1_local`) uses
Fubini exactly as the book does, with the block-matrix remark proved as a separate claim. Step 2
(`step2_local`) is the book's. Step 3 (`measure_image_vanishSet_inter_eq_zero`) replaces Milnor's
cube-counting by the statement that a Hölder map of exponent $k+1$ sends a set of Hausdorff
dimension $n$ to a set of dimension at most $n/(k+1)$, which Mathlib has; the Taylor estimate
behind it (`norm_sub_le_of_iteratedFDeriv_eq_zero`) is proved by induction from the mean value
inequality. Two degenerate cases the book does not mention are handled separately in
`sardStatement`. For $p = 0$ every linear map onto the zero space is surjective, so there are no
critical points and the theorem holds trivially (`critSet_eq_empty_of_subsingleton`); the case must
nevertheless be split off, because the steps of the proof use that points have measure zero, and a
Haar measure on a zero-dimensional space is a point mass. For $n = 0$, and a target of positive
dimension (the other case having been split off), the set $f(C)$ has at most one point, which has
measure zero.

---

## 5. Chapter 4 (Milnor §4): verified

Milnor's §4 has two lemmas and one theorem. The Homotopy Lemma is Lemma 4 applied to the
cylinder plus the Appendix; the Homogeneity Lemma is proved in the book by a flow, and here by an
explicit diffeomorphism instead (see V4.4 for why). The Theorem, which Milnor does not letter,
makes two assertions: the parity of $\#f^{-1}(y)$ is the same at all regular values $y$ (V4.6),
and this residue class, the mod 2 degree, depends only on the smooth homotopy class of $f$ (V4.8);
both follow as in the book. (The project's Lean docstrings call these two assertions "Theorem B"
and "Theorem A"; those letters are not Milnor's.)

**Convention: what a smooth homotopy is.** Milnor's homotopy is a smooth map on $M \times [0,1]$.
Mathlib does have smooth structures on the interval $[0,1]$ and on products
(`instIccChartedSpace`, `instIsManifoldIcc`, `IsManifold.prod`), so $M \times [0,1]$ is a smooth
manifold with boundary in Mathlib's sense. The formal proofs nevertheless use $M \times \mathbb R$,
because it has no boundary, so that Lemma 4 (V2.6, in the form V4.1) and Brown's theorem (V3.3)
apply to it directly (`homotopy_lemma_of_isRegularValue`, `homotopy_lemma`). Accordingly a
*smooth homotopy* is taken here to be a smooth map $F : M \times \mathbb R \to N$, and its two ends
are $F(\cdot, 0)$ and $F(\cdot, 1)$. Every homotopy in Milnor's sense extends to one in this sense
after reparametrizing $t$ by the smooth transition function (this is the reparametrization already
used in the entertaining edition, Chapter 4, §1), and conversely a map on $M \times \mathbb R$
restricts to one on $M \times [0,1]$; so the two notions of "smoothly homotopic" agree. *This is a deviation of form only, but the reader should confirm it once, since
every statement of the chapter is phrased through it.*

**V4.1 (Lemma 4 for the cylinder; `Milnor.isHalfSliceSubmanifold_levelSet_two`).** Let $M$ and
$N$ be smooth manifolds without boundary, with model spaces $Z$, $Z'$ for the dimension bookkeeping
as in V2.6: $\dim Z + \dim N = \dim M$ and $\dim Z' + 1 = \dim Z$ (so $\dim M > \dim N$). Let
$g_0, g_1 : M \to \mathbb R$ and $f : M \to N$ be smooth, and let $y$ be a regular value of $f$
such that at every point of $f^{-1}(y)$ at most one of $g_0, g_1$ vanishes, and at each point of
$f^{-1}(y) \cap \{g_i = 0\}$ there is a tangent vector killed by $df$ but not by $dg_i$. Then
$f^{-1}(y) \cap \{g_0 \ge 0, g_1 \ge 0\}$ is a manifold with boundary
$f^{-1}(y) \cap (\{g_0 = 0\} \cup \{g_1 = 0\})$, in the sense of V2.4 (a half-slice submanifold of
the manifold $f^{-1}(y)$ of V2.2, as in V2.6). The cylinder is the case $g_0 = t$, $g_1 = 1 - t$
on $M \times \mathbb R$. *Proof:* V2.6 applied on the open set
$\{g_1 > 0\}$ with the function $g_0$, and on $\{g_0 > 0\}$ with $g_1$, then glued by a lemma
(`IsHalfSliceSubmanifold.of_local`) saying that being a manifold with boundary is a local property.

**V4.2 (the transversality condition at the ends; `Milnor.cylinder_transversality`).** Let $M$
and $N$ be manifolds without boundary of the same dimension. If $y$ is a regular value of the
homotopy $F : M \times \mathbb R \to N$ and of the end map $F(\cdot, c)$, then at each point $(x, c)$ of $F^{-1}(y)$ there is a vector $v = (v_1, v_2)$ with $dF_{(x,c)} v = 0$ and
$v_2 \ne 0$. Milnor's proof (p. 21) passes over this: it says only "suppose that $y$ is
also a regular value for $F$" and then treats $F^{-1}(y)$ as a compact 1-manifold whose boundary
is $f^{-1}(y) \times 0 \cup g^{-1}(y) \times 1$, which needs the transversality at the ends. Here
it is proved: the kernel of $dF$ at $(x, c)$ is nontrivial by dimension count, and cannot lie in
$T_xM \times 0$ because $dF(\cdot, c)_x$ is injective. *Redundant hypothesis:* regularity of $y$
for $F$ is assumed but never used; the proof needs only the end map.

**V4.3 (the Homotopy Lemma; `Milnor.homotopy_lemma`).** Let $M$ be a compact Hausdorff second
countable smooth manifold without boundary, $N$ a Hausdorff smooth manifold without boundary of the
same dimension, $F : M \times \mathbb R \to N$ smooth, $f = F(\cdot, 0)$, $g = F(\cdot, 1)$. If $y$
is a regular value of both $f$ and $g$ then $\#f^{-1}(y) + \#g^{-1}(y)$ is even. *Proof as in the
book.* Case 1 ($y$ also regular for $F$; `homotopy_lemma_of_isRegularValue`): by V4.1 and V4.2
the set $F^{-1}(y) \cap (M \times [0,1])$ is a compact 1-manifold with boundary
$f^{-1}(y) \times \{0\} \cup g^{-1}(y) \times \{1\}$, so V.A′ gives the parity. Case 2: by V1.4 in
its strengthened form (`eventually_isRegularValue_and_ncard`: regular values near a regular
value are regular with the same count) there is a neighbourhood of $y$ on which both counts are
constant, and by V3.3 it contains a regular value of $F$. *Hidden hypotheses:* Hausdorff and
second countable, as in V1.4 and V3.3.

**V4.4 (the Homogeneity Lemma; `Milnor.isotopic_of_preconnected`).** Let $N$ be a connected
Hausdorff smooth manifold without boundary. For any $y, z \in N$ there is a diffeomorphism
$h : N \to N$ with $h(y) = z$ and a smooth map $H : N \times \mathbb R \to N$ with
$H(\cdot, 0) = \mathrm{id}$ and $H(\cdot, 1) = h$, every stage $H(\cdot, t)$ being a
diffeomorphism of $N$: a smooth isotopy from the identity to $h$, which is Milnor's conclusion
(the relation `Milnor.Isotopic`). *Deviation (proof, not statement):* Milnor
moves $y$ by the time-one flow of a compactly supported vector field, and isotopes by the flow.
Mathlib has no smooth dependence of flows on initial conditions, so the flow is replaced by the
explicit map $u \mapsto u + \varphi(u)\,c$ of the model space, $\varphi$ a bump function equal to
$1$ at the chart image of $y$ and $c$ the small displacement to the chart image of $z$
(`Milnor.Bump.shift`). This map is injective by the mean value inequality
($\|\varphi\|_{\mathrm{Lip}}\,\|c\| < 1$; `shift_injective`), surjective by the contraction
principle applied to $u \mapsto w - \varphi(u)c$ (`shift_surjective`), and its inverse is smooth by
the inverse function theorem, since $d(u + \varphi c) = 1 + d\varphi \otimes c$ is a perturbation
of the identity of norm less than one (`shift_symm_contDiff`). Transported through the chart and
extended by the identity it is a diffeomorphism of $N$ (`Milnor.transport`,
`contMDiff_transport`), and $u + \sigma(t)\varphi(u)c$ with $\sigma$ the smooth transition
function is the isotopy (`contMDiff_transport_shift`); each of its stages is again a transported
bump shift, hence a diffeomorphism. The relation "isotopic" is reflexive, transitive (compose the
isotopies at each time), and symmetric (apply $h^{-1}$ to the reversed isotopy); it holds on a neighbourhood of each point by the construction just described
(`eventually_isotopic`); so its classes are open, and a connected space has one class. *Hidden
hypothesis:* Hausdorff, used once, to see that the chart image of a closed ball is closed in $N$.
That every stage is a diffeomorphism is not needed in this chapter, but it is used in V5.5.

**V4.5 (diffeomorphisms preserve regular values; `Milnor.IsRegularValue.diffeomorph_comp`,
`surjective_mfderiv_diffeomorph`).** If $y$ is a regular value of $f$ and $h$ is a diffeomorphism
of $N$ then $h(y)$ is a regular value of $h \circ f$, with the same preimage. The derivative of a
diffeomorphism is surjective because it has a left inverse (the chain rule on
$h^{-1} \circ h = \mathrm{id}$) and the tangent spaces have equal dimension.

**V4.6 (the Theorem of §4, first assertion; `Milnor.even_ncard_add_ncard_of_isRegularValue`).**
Let $M$ be a compact Hausdorff second countable smooth manifold without boundary, $N$ a connected
Hausdorff smooth manifold without boundary of the same dimension, $f : M \to N$ smooth. If $y$ and $z$ are regular
values of $f$ then $\#f^{-1}(y) + \#f^{-1}(z)$ is even. *Proof as in the book:* V4.4 gives $h$
isotopic to the identity with $h(y) = z$; $z$ is a regular value of $h \circ f$ by V4.5, with
$(h \circ f)^{-1}(z) = f^{-1}(y)$; the map $(x, t) \mapsto H(f(x), t)$ is a smooth homotopy from
$f$ to $h \circ f$; V4.3 applies.

**V4.7 (the degree modulo 2; `Milnor.degMod2`, `degMod2_eq`).** For $f$ as in V4.6,
$\deg_2 f \in \mathbb Z/2$ is defined as the parity of $\#f^{-1}(y)$ for a chosen regular value
$y$ (chosen by the axiom of choice among the regular values; there is one by V3.3 whenever $N$ is
nonempty; if there is none, $\deg_2 f = 0$). The theorem `degMod2_eq` says that for *every*
regular value $y$, $\deg_2 f = \#f^{-1}(y) \bmod 2$.

**V4.8 (the Theorem of §4, second assertion; `Milnor.degMod2_eq_of_homotopy`).** For $M$, $N$ as
in V4.6 and $F : M \times \mathbb R \to N$ smooth, $\deg_2 F(\cdot, 0) = \deg_2 F(\cdot, 1)$. *Proof as in the
book:* the two end maps have a common regular value (the regular values of the first form an
open set by V1.4, nonempty by V3.3, and the regular values of the second are dense by V3.3), and
V4.3 gives the parity. The case $N$ empty is handled separately (both degrees are $0$).

**V4.9 (maps of nonzero degree are onto; `Milnor.surjective_of_degMod2_ne_zero`,
`degMod2_eq_zero_of_notMem_range`).** For $f$ as in V4.6, if $\deg_2 f \ne 0$ then $f$ is
surjective: a point outside the range is a regular value with empty preimage.

*Not formalized in Chapter 4:* Milnor's example that a map homotopic to a constant has even
counts and his remark on $\mathbb{RP}^n$ (both are immediate from V4.8 and are examples, not
theorems).

**Size.** 894 lines in the five files of Chapter 4: 97 for V4.1, 215 for V4.2–V4.3, 137 for the
bump diffeomorphism of the model space, 272 for the transport and the Homogeneity Lemma (including
the isotopy through diffeomorphisms that V5.5 uses), 173 for V4.5–V4.9, that is, the Theorem and
the degree. The strengthened V1.4 (about 80 lines) was written for this chapter but sits in
Chapter 1's `RegularValue.lean` and is counted there. The estimate of 1,500 lines given in the
previous edition of §8 was too high, mainly because the inverse function theorem in Mathlib
already delivers the smoothness of the inverse of the bump shift.

---

## 6. Chapter 5 (Milnor §5): verified

Mathlib has orientations of vector spaces but no orientations of manifolds, no sign of a
derivative, and no degree. All three are built here. The reader's main job in this chapter is to
confirm the definition of an oriented manifold (V5.0), because everything else is stated through
it. Milnor's §5 has two lemmas and two theorems: Lemma 1, a map on the boundary of a compact
oriented manifold that extends over the manifold has signed count $0$ (V5.3); Lemma 2, homotopic
maps have the same signed count at a common regular value (V5.4);
Theorem A, the signed count does not depend on the regular value (V5.6); and Theorem B, smoothly
homotopic maps have the same degree (V5.7). The project's Lean docstrings use an older lettering in
which the two theorems are interchanged ("Theorem A" for homotopy invariance, "Theorem B" for the
independence of the regular value).

**V5.0 (orientations; `Milnor.orSign`, `Milnor.Orient`, `Milnor.signAt`, `Milnor.orProd`,
`Orient.prodReal`).** For finite-dimensional real spaces $E$, $F$ of the same dimension $n$
with orientations $a$, $b$ (Mathlib's `Orientation`, a ray of alternating $n$-forms) and a
linear map $T : E \to F$, the *sign* $\operatorname{sgn}(a, b, T) \in \{1, -1, 0\}$ is defined by
pulling a representative form of $b$ back along $T$ and comparing with a representative of
$a$: the pullback is a multiple $c\,\omega$, and the sign is the sign of $c$. It is $0$ exactly
when $T$ is singular, multiplicative under composition, and $1$ for the identity. An
*orientation of a manifold* $M$ modelled on $E$ is a choice of orientation $o_x$ of $E = T_xM$
for each $x$ such that, for each $x$, the derivative at nearby points $y$ of the chart at $x$
carries $o_y$ to $o_x$ (sign $1$). The sign of $f : M \to N$ at $x$ is
$\operatorname{sgn}(o_x, o_{f(x)}, df_x)$. The product $M \times \mathbb R$ is oriented by
declaring a positive basis of $E$ followed by $(0,1)$ positive. *Deviation (definition):* Milnor
defines an orientation as a locally consistent choice of orientations of tangent spaces; the
formal definition makes "locally consistent" precise through the derivatives of the preferred
charts. The reader should confirm that this is the intended notion; nothing in the chapter
depends on the choice of charts, since every statement is chart-independent, but the
*definition* is phrased through them.

**V5.1 (local constancy of the sign; `Milnor.eventually_signAt_eq`).** If $x_0$ is a regular
point of a smooth map $f : M \to N$ between oriented manifolds of the same dimension, then
$\operatorname{sign} df_x = \operatorname{sign} df_{x_0}$ for $x$ near $x_0$. This is the
continuity statement Milnor uses without comment on p. 27; its proof is the chain rule in charts
together with the continuity of a determinant.

**V5.2 (the signed count and its local constancy; `Milnor.degAt`,
`IsRegularValue.eventually_degAt_eq`).** For $M$ compact and $y$ a regular value,
$\deg(f; y) = \sum_{x \in f^{-1}(y)} \operatorname{sign} df_x$; if $M$ and $N$ are Hausdorff, it
is constant on a neighbourhood of $y$ (as a function of all $y'$ near $y$, not only regular ones,
as in V1.4).

**V5.3 (Lemma 1, ambient form; `Milnor.lemmaOne_ambient`).** Let $M'$ be an oriented
$(n{+}1)$-manifold without boundary, $N$ an oriented $n$-manifold without boundary, $g : M' \to
\mathbb R$ smooth with $X = \{g \ge 0\}$ (more precisely $f^{-1}(y) \cap X$) compact, $f : M' \to
N$ smooth, $y$ a regular value of $f$ such that at each point of $f^{-1}(y) \cap \{g = 0\}$ some
vector in the kernel of $df$ is not in the kernel of $dg$ (this is "$y$ is a regular value of
$f|\partial X$"). Then
$$\sum_{x \in f^{-1}(y) \cap \{g = 0\}} \operatorname{sign}\, d(f, g)_x = 0,$$
the signs of the pair map $(f, g) : M' \to N \times \mathbb R$ being taken for the orientation of
$M'$ and the product orientation of $N \times \mathbb R$. *Deviation (form):* Milnor's Lemma 1
is stated for an abstract compact oriented manifold $X$ with boundary $M = \partial X$ and says
$\deg(f|M; y) = 0$ for the boundary orientation of $M$. Here $X$ is presented inside a
boundaryless $M'$ as $\{g \ge 0\}$, and the sign at a boundary point is expressed through the
ambient pair map $(f, g)$ instead of through the boundary orientation of $\{g = 0\}$; with
Milnor's convention "outward normal first" the two agree up to the global sign $(-1)^{n+1}$
(`Milnor.signAt_levelOrient_eq'`, proved in Chapter 6 and used in V6.1), which does not affect
the statement. The manifolds with boundary that occur in the book (the cylinder, regions in
$\mathbb R^m$) are all of this form. *Deviation (division of labour):* the formal statement asks
that $y$ be a regular value of $f$ on all of $M'$, which is Milnor's first case; his last
paragraph, which reduces a regular value of $f|\partial X$ to that case by moving $y$ slightly,
is carried out inside V5.4 instead, where a nearby regular value of the homotopy is chosen. *Proof as in the book*, with the sentence "we leave the
details to the reader" carried out: $f^{-1}(y) \cap X$ is a compact 1-manifold with boundary
(V2.6); the arc lemmas of the Appendix (`OneManifold.exists_closed_arc`,
`OneManifold.finite_boundary`, §10) pair its boundary points by arcs; along an arc, for any local
coordinate $c$ of the arc, the quantity $\operatorname{sign} d(f,c) \cdot
(\text{direction of } c \text{ along the arc})$ is independent of $c$ (a two-by-two block
computation), locally constant, hence constant; at the two ends the coordinate $c = g$ points
into the arc at one end and out of it at the other, so the two signs are opposite
(`Milnor.bdrySign_end_eq_neg`). *Hidden hypotheses:* $M'$ and $N$ Hausdorff (the formal statement
carries both; the proof uses only the first).

**V5.4 (Lemma 2 of §5, homotopy invariance at a common regular value;
`Milnor.degAt_eq_of_homotopy`).** Let $M$ be a compact Hausdorff second countable oriented
manifold without boundary, $N$ a Hausdorff oriented manifold without boundary
of the same dimension, $F : M \times \mathbb R \to N$ smooth, $f = F(\cdot,0)$, $g = F(\cdot,1)$,
$y$ a regular value of both. Then $\deg(f; y) = \deg(g; y)$. *Proof as in the book:* V5.3 for the
cylinder $X = \{t(1-t) \ge 0\} = M \times [0,1]$ in $M' = M \times \mathbb R$, the sign of
$(F, t(1-t))$ at $(x, 0)$ being $\operatorname{sign} df_x$ and at $(x, 1)$ being
$-\operatorname{sign} dg_x$ (the block formula of V5.0); then the reduction to a regular value of
$F$ by V5.2 and Brown, as in V4.3. This is Milnor's Lemma 2 of §5; his Theorem B follows from it
once the degree is defined (V5.7).

**V5.5 (isotopies preserve orientation; `Milnor.exists_isotopy_signAt_eq_one`).** The
isotopy $H$ of V4.4 has every stage $H(\cdot, t)$ a diffeomorphism (this is Milnor's notion of
isotopy, and the bump-function construction gives it for free). For such an isotopy from the
identity to $h$, $\operatorname{sign} dh = 1$ everywhere: the sign of $H(\cdot, t)$ at $x$ is
nonzero for all $t$, locally constant in $(x, t)$ by V5.1 applied to $(x, t) \mapsto (H(x,t), t)$,
hence constant in $t$, hence equal to its value $1$ at $t = 0$.

**V5.6 (Theorem A of §5; `Milnor.degAt_eq_of_isRegularValue`).** For $M$ compact Hausdorff second
countable, $N$ connected Hausdorff, both oriented without boundary, of the same dimension, and
$f : M \to N$ smooth, $\deg(f; y) = \deg(f; z)$ for any two regular values. *Proof as in the
book:* V4.4 and V5.5 give an orientation-preserving $h$ isotopic to the identity with $h(y) =
z$; $\deg(h \circ f; z) = \deg(f; y)$ because the signs multiply (`Milnor.signAt_comp`); and
$\deg(h \circ f; z) = \deg(f; z)$ by V5.4 along the homotopy $(x, t) \mapsto H(f(x), t)$.

**V5.7 (the Brouwer degree and Theorem B of §5; `Milnor.deg`, `deg_eq`, `deg_eq_of_homotopy`,
`surjective_of_deg_ne_zero`, `deg_id`).** For $M$, $N$ as in V5.6, $\deg f \in \mathbb Z$ is
defined as $\deg(f; y)$ for a regular value $y$ chosen by the axiom of choice ($0$ if there is
none, which happens only for $N$ empty); `deg_eq` says $\deg f = \deg(f; y)$ for every regular
value $y$. Smoothly homotopic maps have the same degree (`deg_eq_of_homotopy`, Milnor's Theorem
B, from V5.4 at a common regular value); a map of nonzero degree is surjective; the identity has
degree $1$.

**V5.8 (the induced orientation of a level set; `Milnor.levelOrient`, `contractOr`).** Let $E$
be an oriented space of dimension $n + 1$, $g : E \to \mathbb R$ smooth with $0$ a regular value,
$S = g^{-1}(0)$ (a submanifold by V2.2). Orient $T_qS$ by declaring a basis $z$ positive when
$(\text{outward}(q), z)$ is a positive basis of $E$, where $\text{outward}(q) = -\sum_i
dg_q(e_i)\,e_i$ for a basis $e$ of $E$ fixed once by the axiom of choice
(`finBasisOfFinrankEq`), a vector with $dg_q(\text{outward}(q)) < 0$. Any other vector $w$ with
$dg_q(w) < 0$ gives the same orientation, since $w$ is a positive multiple of $\text{outward}(q)$
plus a vector tangent to $S$ (`Milnor.contractForm_eq_smul`, proved in Chapter 6); and the
choice of the top form representing the orientation of $E$ does not matter either
(`rayOfNeZero_contractForm`). This is an orientation of $S$ in the sense of V5.0. This is
Milnor's boundary orientation of $\partial X$ for $X = \{g \ge 0\} \subseteq E$ ("outward normal
first"). *Deviation (generality):* only for
level sets in a vector space $E$, not in an arbitrary oriented manifold; this covers the spheres
and the regions of $\mathbb R^m$ used in the book. The proof is the continuity of the
contracted form in the chart, a determinant computation.

**V5.9 (the antipodal map; `Milnor.Sphere.deg_antip`, `signAt_antip`).** On the unit sphere
$S^n \subseteq \mathbb R^{n+1}$, presented as the level set of $\langle x, x\rangle -
1$ with the orientation of V5.8 (called `sphOr`), the antipodal map $x \mapsto -x$ has sign
$(-1)^{n+1}$ at every point, for every $n \ge 0$, and degree $(-1)^{n+1}$ for $n \ge 1$, the
degree of §5 needing a connected target. Milnor computes this as a composite of
$n + 1$ reflections; here it is read off directly from the contracted form, since $-1$ reverses
the outward vector and each of the $n$ tangent vectors. *Flag (the orientation of the sphere):*
`sphOr` is the level-set orientation of V5.8 for the orientation of $\mathbb R^{n+1}$ given by
the basis chosen by the axiom of choice, not by the standard basis. Moreover the region
$\{\langle x,x\rangle \ge 1\}$ is the *exterior* of the ball, so the "outward" vector of V5.8
points into the ball and `sphOr` is the boundary orientation of the exterior: for the standard
orientation of $\mathbb R^{n+1}$ this rule would give the opposite of Milnor's orientation of
$S^n$ as the boundary of the disk. Since the chosen basis may have either orientation, `sphOr` is
Milnor's orientation or its opposite, and the formal text does not decide which. The degree of
the antipodal map does not depend on this
(the same orientation is used on both sides), and neither do the other uses of `sphOr` in
Chapters 5–7 (the introduction to Chapter 6 explains the one place where the convention is
visible); where Milnor's orientation matters (linking numbers and the Hopf invariant), Chapter 8
uses it explicitly (V8.0 (iii)).

**V5.10 (the hairy ball theorem; `Milnor.Sphere.hairy_ball`).** For $n$ even and positive, every
smooth tangent vector field on $S^n$ (a smooth $v : S^n \to \mathbb R^{n+1}$ with
$\langle x, v(x)\rangle = 0$) vanishes somewhere. *Proof as in the book:* otherwise
$(x, t) \mapsto \cos(\pi t)\,x + \sin(\pi t)\,v(x)/|v(x)|$ is a smooth homotopy in $S^n$ from the
identity to the antipodal map, so by V5.7 their degrees $1$ and $(-1)^{n+1} = -1$ agree.
*Hidden hypotheses:* none beyond smoothness of $v$ (Milnor's statement is for smooth fields;
the continuous case follows by approximation and is not formalized). *The converse*
(`Milnor.Sphere.exists_nonvanishing_field`): for $n$ odd, write $n + 1 = 2(k + 1)$ and
$x = (a, b)$ with $a, b \in \mathbb R^{k+1}$ the first and second halves of the coordinates; the
field $(a, b) \mapsto (b, -a)$ is a smooth tangent field on $S^n$ without zeros; verified, so
Milnor's "if and only if" is complete. (Milnor's field $(x_2, -x_1, x_4, -x_3, \dots)$ pairs
adjacent coordinates instead; the two differ by a permutation of coordinates.)

*Not formalized in Chapter 5:* Lemma 1 in Milnor's boundary-orientation form for an abstract
compact manifold with boundary (see V5.3; the boundary-orientation form for regions
$\{g \ge 0\}$ is V6.1); Milnor's remarks on the degree of a constant map and on
$\mathbb{RP}^n$.

**Size.** 3,096 lines in the thirteen files of Chapter 5: 508 for the sign of a linear map and
the product orientation, 248 for oriented manifolds and V5.1, 46 for V5.2, 1,089 for V5.3 (chart
functions 231, the real-analysis of the monotonicity sign 204, the transition between chart
functions 254, the sign along an arc 256, the pairing 144), 177 for V5.4, 204 for V5.5–V5.7, 354
for V5.8, 394 for V5.9–V5.10, and 76 for algebraic properties of the sign added later for
Chapters 7 and 8 (`OrSignAlg.lean`). The signed strengthening of V1.4 (about 90 lines, in
Chapter 1's `RegularValue.lean`) and the isotopy through diffeomorphisms (in Chapter 4's
`Homogeneity.lean`) were written for this chapter and are counted with their files. The estimate
of 3,000 lines in the previous edition was accurate. Lemma 1 is the expensive item, as predicted:
Milnor's "details left to the reader" are a third of the chapter.

---

## 7. Chapter 6 (Milnor §6): verified

Milnor's §6 defines the index of a zero of a vector field, proves that it is invariant under
diffeomorphisms (Lemma 1, using Lemma 2: every orientation-preserving diffeomorphism of
$\mathbb R^m$ is smoothly isotopic to the identity), proves Hopf's lemma on the index sum over a
region (Lemma 3), and deduces the Poincaré–Hopf theorem for a compact manifold
$N \subseteq \mathbb R^k$ by extending a tangent field to a tubular neighbourhood $N_\varepsilon$,
quoting the $\varepsilon$-neighbourhood theorem of §8. All of this is verified below, for compact
submanifolds of Euclidean space, with the two changes of route described in V6.5 and V6.8.
Throughout, $E = \mathbb R^{n+1}$ with $n \ge 1$ (so that $S^n$ is connected and the degree is
defined) and $S^n$ carries the orientation `sphOr` of V5.9. That orientation is the level-set
orientation of $|x|^2 - 1$ ("outward vector $-\nabla g$ first"), which is the boundary orientation
of the *complement* of the ball, the opposite of Milnor's convention for the same orientation of
$\mathbb R^{n+1}$ (V5.9). Since every degree below is between two such "complement" orientations,
or between two "ball" orientations, the numbers are Milnor's; the reader will see the convention only in the
statement of V6.3 and V6.4, where the boundary $\partial X = G^{-1}(0)$ is written with the
orientation of $\{G \ge 0\}$ reversed (`Orient.neg`).

**V6.0 (the index; `Milnor.Sphere.indexAt`, `Milnor.Sphere.index`, `Milnor.Sphere.IsolatedZero`).**
For a smooth vector field $v : \mathbb R^{n+1} \to \mathbb R^{n+1}$ with $v(z) = 0$ and no other
zero in the closed ball of radius $r$ about $z$, and any $0 < \varepsilon \le r$, the map
$u \mapsto v(z + \varepsilon u)/|v(z + \varepsilon u)|$ of $S^n$ to itself is smooth, and its
degree is the *index* of $v$ at $z$. It does not depend on $\varepsilon$
(`indexAt_eq_of_radii`), it is unchanged by a smooth homotopy of $v$ with no zeros on the
$\varepsilon$-sphere (`indexAt_eq_of_homotopy`, Milnor p. 33 bottom), and it depends only on
the germ of $v$ at $z$ (`index_eq_of_eventuallyEq`). *Deviation (form of the statement):* $v$ is
a field on all of $\mathbb R^{n+1}$. A field on an open set agrees near any compact subset with
a global field (`Milnor.exists_extension`, a cut-off), and the index depends only on the germ,
so nothing is lost; V6.5 and V6.9 use this.

**V6.1 (the level-set orientation in a manifold; `Milnor.levelOrientM`,
`Milnor.signAt_levelOrientM_eq'`, `Milnor.degAt_level_eq_zero_of_opens`).** V5.8 is extended
from vector spaces to any oriented manifold $M$ with charts in $E$ (in particular to open
subsets of $E$): for $g : M \to \mathbb R$ smooth with $0$ a regular value, $g^{-1}(0)$ is
oriented by "an outward vector $w$ with $dg(w) < 0$, then a positive basis of $T g^{-1}(0)$",
and this is chart-continuous. The bridge lemma between the two ways of counting signs holds in
this setting (`signAt_levelOrientM_eq'`; for level sets in a vector space it is
`Milnor.signAt_levelOrient_eq'`): at a point of $g^{-1}(0)$, the sign of $f|g^{-1}(0)$ for the
level-set orientation is $(-1)^{n+1}$ times the sign of the pair map $(f, g)$ of V5.3, where
$\dim M = n + 1$. So does Lemma 1 of §5 in boundary form: let $N$ be an oriented $n$-manifold
without boundary, $M$ and $N$ Hausdorff, $f : M \to N$ smooth on an open set
$U \supseteq g^{-1}(0)$, $y$ a regular value of $f|U$ satisfying the transversality condition of
V2.6 at the points of $f^{-1}(y) \cap g^{-1}(0)$, and $f^{-1}(y) \cap \{g \ge 0\} \cap U$
compact; then $f^{-1}(y) \cap g^{-1}(0)$ is finite and
$\deg(f|g^{-1}(0); y) = 0$. Given that $y$ is regular for $f|U$, the transversality condition is
equivalent to $y$ being a regular value of $f|g^{-1}(0)$; the formal statement assumes the
transversality condition, and the implication from regularity of $f|g^{-1}(0)$ to it is proved
separately (`Milnor.exists_mfd_eq_zero_of_isRegularPoint_level`), which is the direction the
applications need. *Why the open set:* in V6.3 the map is $v/|v|$, which is smooth only where
$v \ne 0$.

**V6.2 (the sign of a map between level sets; `Milnor.signAt_levelOrientM_map'`).** Let
$\Phi : M \to M'$ be smooth along $G^{-1}(0)$ and carry $G^{-1}(0)$ into $G'^{-1}(0)$, and
suppose $dG'_{\Phi(q)} \circ d\Phi_q = c \cdot dG_q$ with $c \ne 0$. Then the sign at $q$ of the
restricted map $G^{-1}(0) \to G'^{-1}(0)$, for the two level-set orientations, is
$\operatorname{sgn}(c)$ times the sign of $\Phi$ at $q$ for the ambient orientations. *This
lemma has no counterpart in the book*; it is the tool that lets every degree computation of
the chapter be done by transporting along explicit maps (the inclusion of a component, the
affine map $u \mapsto z + \varepsilon u$, a diffeomorphism $f$, the radial map of V6.5) instead
of by an isotopy argument. Its proof is the contracted-form calculus of V5.8: the pullback of
the outward vector decomposes as a positive multiple of the outward vector plus a tangent
vector, and the tangent part contributes nothing to the top form.

**V6.3 (the region lemma; `Milnor.Sphere.sum_indexAt_eq_deg`).** Let $X = \{G \ge 0\}$ be
compact with $0$ a regular value of $G : \mathbb R^{n+1} \to \mathbb R$, let the closed
$\varepsilon$-balls about $z_1, \dots, z_k$ be pairwise disjoint and contained in $\{G > 0\}$,
and let every zero of $v$ in $X$ be one of the $z_i$ (an inclusion: the $z_i$ are not required
to be zeros). Then
$$\sum_i \operatorname{index}_{z_i}(v) = \deg\big(v/|v| : \partial X \to S^n\big),$$
$\partial X = G^{-1}(0)$ carrying the orientation of V6.1 reversed (see the convention above).
*Proof as in the book (p. 34):* apply V6.1 on the open set $\{v \ne 0\}$ to the region
$X' = X \setminus \bigcup \operatorname{int} B_\varepsilon(z_i)$, presented as
$\{g \ge 0\}$ with $g = G \cdot \prod_i \big(|x - z_i|^2/\varepsilon^2 - 1\big)$; the degree over
$\partial X'$ vanishes, splits by V6.2 (with $\Phi$ the identity, $c$ the product of the other
factors) into the degree over $\partial X$ plus the degrees over the spheres, and each sphere
term is the index by V6.2 with $\Phi(u) = z_i + \varepsilon u$ ($c = 1$). *Hidden hypotheses:*
the common regular value of $v/|v|$ on $\{v \ne 0\}$, on $\partial X$ and on the $k$ spheres
exists because regular values of a map with compact domain form an open dense set
(`Milnor.isOpen_regularValues`, a variant for oriented manifolds of
`Milnor.isOpen_isRegularValue` of Chapter 4, used in V4.8; density is V3.3) and $S^n$ is a Baire
space.

**V6.4 (Hopf's lemma; `Milnor.Sphere.hopf_lemma`).** Under the hypotheses of V6.3, if $v$ points
outward along $\partial X$ (that is, $dG(v) < 0$ on $G^{-1}(0)$), then
$\sum_i \operatorname{index}_{z_i}(v)$ equals the degree of the Gauss map
$x \mapsto -\nabla G(x)/|\nabla G(x)|$ of $\partial X$, a number depending only on $X$. *Proof as
in the book (Lemma 3, p. 35):* the straight-line homotopy from $v$ to $-\nabla G$ stays away from
zero on $\partial X$, reparametrized by a smooth transition function so that it is defined for
all times; V5.7.

**V6.5 (invariance of the index under diffeomorphisms; Milnor's Lemma 1;
`Milnor.Sphere.index_eq_of_diffeo`).** Let $f : U \to U'$ be a diffeomorphism between open
subsets of $\mathbb R^{n+1}$ (smooth $f$, $g$ with $g \circ f = \mathrm{id}$ on $U$ and
$f \circ g = \mathrm{id}$ on $U'$), let $v$ be a smooth field with an isolated zero at $z$, the
closed $r$-ball about $z$ lying in $U$, and let $w$ be a smooth field equal to
$df \circ v \circ f^{-1}$ on $f(\bar B_r(z))$. Then $\operatorname{index}_{f(z)}(w) =
\operatorname{index}_z(v)$. *Deviation (route of proof):* Milnor proves this by his Lemma 2,
that every orientation-preserving diffeomorphism of $\mathbb R^m$ is smoothly isotopic to the
identity (first to its derivative at a fixed point, by $F(x, t) = f(tx)/t$, then through
$GL^+$ to the identity). Lemma 2 is now proved as well (V6.12), but it is not used here, and this
proof does not go through it. Instead: (i) by V6.3 applied to the
region $f(\bar B_r(z)) = \{G' \ge 0\}$ (with $G' = r^2 - |g(y) - z|^2$ near it, made global by a cut-off,
`Milnor.exists_region_fun`), the index of $w$ at $f(z)$ is the degree of $w/|w|$ over
$f(S_r(z))$; (ii) by V6.2 with $\Phi = f$ (here $c = -r^2$), that degree is
$-\sigma$ times the degree of $u \mapsto df_u(v(u))/|\cdot|$ over $S_r(z)$, where
$\sigma = \operatorname{sgn}\det df$ is constant on the ball by the intermediate value theorem
(`Milnor.sgn_det_fderiv_eq`); (iii) the homotopy $df_{z + t(u - z)} \to df_z$ ($t$ from $1$ to
$0$) and V5.7 reduce this to $u \mapsto A\,v(u)/|A\,v(u)|$ with $A = df_z$; (iv) this is
$h \circ (v/|v|)$ with $h(u) = Au/|Au|$, and the sign of $h$ at every point of $S^n$ is
$\operatorname{sgn}\det A = \sigma$ (`Milnor.Sphere.signAt_nv0_linear`); so the two factors
$\sigma$ cancel. Step (iv) is where Lemma 2 is replaced: $h$ is the restriction to $S^n$ of
$\Theta(x) = (|x|/|Ax|)\,Ax$, which preserves $|x|^2 - 1$, so by V6.2 the sign of $h$ is
$\operatorname{sgn}\det d\Theta$, and $d\Theta_u = (\lambda\,\mathrm{id} + (d\lambda_u \circ A^{-1})
\otimes Au) \circ A$ with $\lambda = |x|/|Ax|$ homogeneous of degree $0$, whose determinant is
$\lambda^{n+1}\det A$ by the matrix determinant lemma (`Milnor.det_id_add_smulRight`).

**V6.6 (the $\varepsilon$-neighbourhood theorem; `Milnor.Tub.tubular`).** Let
$N \subseteq \mathbb R^k$ be a compact submanifold (given by slice charts with model
$\mathbb R^n$, as in V2.2). There are $\varepsilon > 0$ and a map $r : \mathbb R^k \to N$ with
$|x - r(x)| = \operatorname{dist}(x, N)$ for every $x$ (a nearest point, chosen for every $x$),
such that every $x$ with $\operatorname{dist}(x, N) < \varepsilon$ has $r(x)$ as its *unique*
nearest point in $N$; the map $r$ is smooth on this neighbourhood, is the identity on $N$,
satisfies $x - r(x) \perp T_{r(x)}N$ there, and $dr_x$ takes values in $T_{r(x)}N$; and for
$x \in N$ and $v \perp T_xN$ one has $r(x + sv) = x$ for all sufficiently small $s$ (this last
conclusion is used in Chapter 7, for the Pontryagin framing and the framed cobordism of a
homotopy). *This is the theorem Milnor sets as Problems 11 and 12 of §8 (p. 52) and quotes in the proof of Poincaré–Hopf; it
is proved here directly.* *Route of
proof (different from Milnor's normal-bundle argument):* in a local parametrization $\varphi$ of
$N$, a nearest point $\varphi(z)$ of $x$ satisfies the nearest-point equation
$(d\varphi_z)^{*}(x - \varphi(z)) = 0$ (Fermat's condition, `Milnor.Tub.Fn_eq_zero_of_nearest`);
the map $(z, x) \mapsto ((d\varphi_z)^*(x - \varphi(z)), x)$ has invertible derivative at
$(z_0, \varphi(z_0))$, so by the inverse function theorem the equation has, for $x$ near
$\varphi(z_0)$, a unique solution $z = U(x)$ near $z_0$, smooth in $x$
(`Milnor.Tub.exists_contDiffOn_U`, which also shows that invertibility of the derivative is an
open condition); a compactness argument on sequences shows that all nearest points of all $x$
close enough to $N$ are captured by these local solutions, which gives uniqueness and
smoothness of $r$. *Hidden hypotheses:* $N$ nonempty; the slice charts of $N$ have Euclidean
model and complement, so that adjoints make sense.

**V6.7 (the region $N_{\varepsilon/2}$ and the extended field; `Milnor.Tub.exists_G`,
`Milnor.Tub.isRegularValue_G`, `Milnor.Tub.w₀_eq_zero`, `Milnor.Tub.fderiv_G₀_w₀`).** With $r$
and $\varepsilon$ as in V6.6, $X = \{\operatorname{dist}(\cdot, N) \le \varepsilon/2\}$ is
compact, equals $\{G \ge 0\}$ for a smooth $G$ with $G = (\varepsilon/2)^2 - |x - r(x)|^2$ near
$X$, and $0$ is a regular value of $G$. For a smooth tangent field $v$ on $N$, the field
$w(x) = v(r(x)) + (x - r(x))$ is smooth near $X$, its zeros in $X$ are exactly the zeros of $v$,
and it points outward along $\partial X$ ($dG(w) = -2|x - r(x)|^2 < 0$ there). *Proof as in the
book (p. 38):* the two summands of $w$ are orthogonal by V6.6.

**V6.8 (the index of a tangent field on a submanifold; `Milnor.Tub.indexN`,
`Milnor.Tub.indexN_eq`).** For a compact $N \subseteq \mathbb R^{K+1}$ and a smooth tangent
field $v$ on $N$, the index of $v$ at $q \in N$ is *defined* as the index at $q$ of (a global
smooth extension of) the field $w$ of V6.7; by V6.0 it depends only on the germ of $w$ at $q$,
hence only on $v$, $N$ and the nearest-point retraction, which is canonical. *Deviation
(definition):* Milnor defines the index on an abstract manifold through a chart, uses his Lemma
1 for well-definedness, and then remarks on p. 38 that this index equals the index of $w$. Here
the second quantity is the definition. The chart definition is formalized too, and the two are
proved equal at a non-degenerate zero (V6.14); the agreement at an arbitrary isolated zero is not
proved, and what it would need is recorded there and in §11. For the theorem below this makes no
difference, since its content is the independence of the index sum from $v$.

**V6.9 (the Poincaré–Hopf theorem; `Milnor.Tub.poincare_hopf`).** Let $N \subseteq
\mathbb R^{K+1}$, $K \ge 1$, be a compact submanifold. There is an integer $\chi(N)$ such that,
for every smooth tangent vector field $v$ on $N$ whose zeros are finitely many points
$z_1, \dots, z_j$,
$$\sum_i \operatorname{index}_{z_i}(v) = \chi(N).$$
In the proof $\chi(N)$ is the degree of the Gauss map of $\partial N_{\varepsilon/2}$.
*Deviation (stronger):* Milnor's Theorem 1 (p. 38) is stated for fields with nondegenerate zeros
only; the formal statement asks for finitely many zeros, of any kind. The price is the definition
of the index used here (V6.8, the index of the extended field); Milnor's Lemma 5 (p. 37), which
identifies that index with the intrinsic one at a nondegenerate zero, is V6.13 and V6.14.
*Proof
as in the book (p. 38):* V6.7 puts $w$ in the situation of V6.4, with small balls about the
$z_i$; the right-hand side of V6.4 does not involve $v$. Since the index is defined through the
extended field (V6.8), the proof does not use V6.5. *Hidden hypotheses:* $N$ nonempty (as in
V6.6; for empty $N$ the statement is trivial); "isolated zeros" is taken as "finitely many
zeros", which on a compact $N$ is the same thing; the ambient dimension is at least $2$; the zeros
are indexed injectively. *Not formalized:* the
identification of $\chi(N)$ with the Euler characteristic (Milnor refers to Hopf's theorem and
to the literature; no Euler characteristic exists in Mathlib), and Poincaré–Hopf for a manifold
not given as a submanifold of Euclidean space (Whitney's embedding theorem is not formalized;
Milnor also works with $N \subseteq \mathbb R^k$).

**V6.10 (Lemma 4, the index of a non-degenerate zero; `Milnor.Sphere.index_eq_sgn_det`,
`Milnor.Sphere.index_nondegenerate`, `Milnor.Sphere.deg_nv0_linear`).** Let $n \ge 1$ and let $v$
be a smooth field on $\mathbb R^{n+1}$ with $v(z) = 0$ and $dv_z$ bijective. Then
$$\operatorname{index}_z(v) = \operatorname{sgn}\det dv_z,$$
so the index is $+1$ or $-1$ according as $\det dv_z$ is positive or negative, which is Milnor's
Lemma 4 of §6 (p. 36, `index_nondegenerate` in his own form). *Hidden hypothesis:* $n \ge 1$, as
everywhere in this chapter, the index being a degree on $S^n$. No isolatedness of the zero is
assumed: it is proved. *Proof as in the book*, with two steps Milnor leaves implicit. First, one
uniform estimate does two jobs at once: writing $A = dv_z$, a bijective linear map is bounded
below, $\|Ay\| \ge c\|y\|$ (`exists_lower_bound_of_bijective`), and $v(x) = A(x - z) +
o(|x - z|)$, so there is a radius $r > 0$ on which no combination $A(x - z) + b\,(v(x) - A(x - z))$
with $0 \le b \le 1$ vanishes off $z$ (`exists_radius_of_nondegenerate`); the case $b = 1$ says
that $z$ is an isolated zero, and the whole range says that the straight-line homotopy from $v$ to
its linear part keeps the $r$-sphere free of zeros, so V6.0 replaces $v$ by $x \mapsto A(x - z)$.
Secondly, the sphere map of the linear field is $u \mapsto Au/|Au|$, whose sign at every point is
$\operatorname{sgn}\det A$ (V6.5's `signAt_nv0_linear`, which is what stands in this development
for Milnor's appeal to Lemma 2); the passage from a constant pointwise sign to a degree is
`deg_nv0_linear`, new here: the map is a bijection of $S^n$, so every point is a regular value
with exactly one preimage.

**V6.11 (Hadamard's lemma, and smoothness of a parametric integral;
`Milnor.contDiff_intervalIntegral`, `Milnor.contDiff_intervalIntegral_infty`,
`Milnor.exists_hadamard`, `Milnor.exists_contDiff_extension`,
`Milnor.contDiff_ite_smul_inv`).** Milnor's isotopy of Lemma 2 of §6 is
$F(x, t) = f(tx)/t$, and the whole difficulty is that it is smooth at $t = 0$. Let $E$ and $F$ be
real normed spaces, $F$ complete. Verified: (i) if
$h : E \times \mathbb R \to F$ is $C^n$ (resp. $C^\infty$) then so is
$x \mapsto \int_0^1 h(x, t)\,dt$ — *Mathlib has no such theorem*, and it is proved here by
induction on $n$, differentiating under the integral sign and dominating on a tube around the
compact segment $\{x\} \times [0,1]$, so that neither finite dimension nor local compactness is
needed; (ii) **Hadamard's lemma:** a smooth $f$ with $f(0) = 0$ factors as $f(x) = L(x)\,x$ with
$L(x) = \int_0^1 df_{tx}\,dt$ smooth and $L(0) = df_0$; (iii) consequently $t^{-1} f(tx)$ extends
to a smooth map of $E \times \mathbb R$ with value $df_0(x)$ at $t = 0$, both as an existence
statement and for the explicit `if t = 0 then … else …` formula in which the isotopy is written.
*Hidden hypothesis:* completeness of the target $F$, so that the Bochner integrals exist — the one
hypothesis Milnor would not state, his spaces being $\mathbb R^m$. *Deviation (stronger):* stated
for smooth maps between real normed spaces, not for $\mathbb R^m$.

**V6.12 (Lemma 2 of §6; `Milnor.lemma2_of_sec6`, `Milnor.smoothIsotopicMap_id`,
`Milnor.SmoothIsotopicMap`, `Milnor.IsDiffeoSelf`).** Every orientation-preserving diffeomorphism
$f$ of $\mathbb R^m$ — and more generally of a finite-dimensional real normed space $E$ — is
smoothly isotopic to the identity (Milnor's Lemma 2 of §6, p. 33). A
diffeomorphism is given unbundled, as a smooth map with a smooth two-sided inverse, as in V6.5; an
isotopy is a smooth $H : E \times \mathbb R \to E$ with $H(\cdot, 0) = f$, $H(\cdot, 1) =
\mathrm{id}$ and *every* time slice a diffeomorphism, the shape already used in V4.4;
"orientation-preserving" is positivity of the Jacobian determinant at one point, equivalently at
every point. *Deviation (stronger):* stated for any finite-dimensional real normed space, with
positivity of the dimension not needed. *Proof as in the book*, in three steps: $f$ is isotopic to
$x \mapsto f(x) - f(0)$ by translation; a diffeomorphism fixing the origin is isotopic to its
derivative there by $F(x, t) = f(tx)/t$, which is smooth by V6.11; and a linear automorphism of
positive determinant is isotopic to the identity along the $GL^+$ path of V7.3. Three things
Milnor passes over: transitivity of isotopy, which needs the two isotopies made constant near the
join before gluing; that the slices at *negative* times are diffeomorphisms too, since the
definition asks for every real time; and invertibility of the derivative, which comes from the
chain rule applied to the two-sided inverse. *Placement:* the Lean file is
`Milnor/Chapter7/Isotopy.lean`, because its last step is the $GL^+$ path of Chapter 7 and
Chapter 6 may not import Chapter 7. **Nothing in the development depends on this lemma**: §6
replaced Milnor's appeal to it by the sign computation of V6.5, and it is formalized only because
it is a theorem of the book.

**V6.13 (Lemma 5, and the derivative of the retraction; `Milnor.Tub.dret`,
`Milnor.Tub.dret_apply_of_mem_tanN`, `Milnor.Tub.ker_dret`, `Milnor.Tub.dvr_mem_tanN`,
`Milnor.Tub.mfd_mem_tanN`, `Milnor.Tub.det_fderiv_w₀`, `Milnor.Tub.bijective_fderiv_w₀_iff`).**
Let $N \subseteq \mathbb R^{K+1}$ be a compact nonempty submanifold of dimension $n$ and $r$ the
nearest-point retraction of V6.6. (i) At $q \in N$ the derivative $dr_q$ is the **orthogonal
projection** of $\mathbb R^{K+1}$ onto $T_qN$: it is the identity on $T_qN$, its image is $T_qN$,
it is idempotent, and its kernel is exactly $(T_qN)^\perp$. (ii) **Milnor's Lemma 5** (p. 37): if
$v$ is a smooth tangent field on $N$ with $v(q) = 0$, then the derivative of $v$ at $q$ carries
$T_qN$ into itself, both in the ambient reading (the derivative at $q$ of $x \mapsto v(r(x))$) and
in the intrinsic one (the derivative of $v : N \to \mathbb R^{K+1}$ on the image of the derivative
of the inclusion). (iii) Hence, at a zero of $v$, the derivative of the extended field
$w = v \circ r + (\mathrm{id} - r)$ of V6.7 is $dv_q \circ dr_q + (\mathrm{id} - dr_q)$, and in the
splitting $\mathbb R^{K+1} = T_qN \oplus (T_qN)^\perp$ it is $dv_q$ on the tangent part and the
identity on the normal part, so $\det dw_q$ is the determinant of the restriction of $dv_q$ to
$T_qN$, and $dw_q$ is invertible exactly when that restriction is. *Hidden hypotheses:* $N$
compact and nonempty, because the retraction of V6.6 is available only then; Milnor's Lemma 5
itself needs no compactness. The hypothesis $v(q) = 0$ is essential in (ii) and is Milnor's:
without it the derivative of $v$ at $q$ has no invariant meaning as an endomorphism of $T_qN$.
*Deviation (route of proof):* Milnor's own proof of Lemma 5 differentiates the field written in a
coefficient basis, which presumes the smoothness of the coefficients; here the identity
$(\mathrm{id} - dr)(v \circ r) = 0$ is differentiated instead, which avoids the point. *What
Milnor leaves implicit:* what "the derivative of a field on a submanifold" means at all; the two
readings above, and their agreement, are stated as theorems.

**V6.14 (the chart definition of the index, and its agreement with V6.8;
`Milnor.Tub.chartField`, `Milnor.Tub.chartIndexN`, `Milnor.Tub.index_eq_chartIndexN`,
`Milnor.Tub.indexN_eq_sgn_det`, `Milnor.Tub.chartIndexN_eq_sgn_det`,
`Milnor.Tub.chartIndexN_eq_indexN`).** Milnor defines the index of a zero of a field on a manifold
through a parametrization (p. 33): a local parametrization $\psi : \Omega \to N$, $\Omega \subseteq
\mathbb R^n$ open, $\psi(u_0) = q$, pulls $v$ back to a field on $\Omega$, and the index of $v$ at
$q$ is the index of the pull-back at $u_0$. Verified: (i) the pull-back through a slice-chart
parametrization is smooth, and its index at the parameter point is `chartIndexN`, Milnor's index;
(ii) *it depends neither on the parametrization nor on the extension* — for **any** smooth local
parametrization $\psi$ of $N$ at $q$ with a smooth ambient left inverse $\chi$ and with
$d\psi_u$ spanning the tangent space, and **any** globally smooth field on $\mathbb R^n$ agreeing
near $u_0$ with the pull-back and having an isolated zero there, the index is the same number
(this is Milnor's Lemma 1, V6.5, applied to the transition $\chi_q \circ \psi$); (iii) at a
non-degenerate zero both definitions are the sign of the same determinant — the index of the
extended field is $\operatorname{sgn}\det(dv_q|T_qN)$ by V6.13(iii) and V6.10, and so is the chart
index, because $d\varphi_q$ conjugates the derivative of the pulled-back field into that
restriction — hence **the chart definition agrees with V6.8 at every non-degenerate zero**
(Milnor, pp. 33 and 37). *Hidden hypotheses:* the dimension conditions, and they are two, because
both indices are degrees on spheres of *different* dimensions: the ambient index needs $K \ge 1$
and the chart index needs $n \ge 2$ (the index of a field on $\mathbb R^n$ is a degree on
$S^{n-1}$). Also $N$ compact and nonempty, as in V6.13. *Not formalized:* the agreement at an
arbitrary isolated zero. It is not a matter of effort: the two numbers are degrees of maps of
spheres of different dimensions, $S^K$ and $S^{n-1}$, so no invariance-under-diffeomorphism
argument compares them, and one would first need a suspension formula — that the index of a field
of the shape $(u, y) \mapsto (\tilde v(u), y)$ on $\mathbb R^n \times \mathbb R^{K+1-n}$ is the
index of $\tilde v$ — which this development does not have and which Milnor does not prove either.

**V6.15 (the Euler number of $S^n$; `Milnor.Sphere.indexSum_sph`,
`Milnor.Sphere.poincare_hopf_sph`, `Milnor.Sphere.eq_of_indexSum_sph`,
`Milnor.Sphere.indexSum_sph_even`, `Milnor.Sphere.indexSum_sph_odd`,
`Milnor.Sphere.indexSum_sph_of_nonvanishing`, `Milnor.Sphere.indexSum_sph_odd_agree`).** For
$n \ge 1$ and *every* smooth tangent field $v$ on $S^n$ whose zeros are finitely many distinct
points $z_1, \dots, z_j$,
$$\sum_i \operatorname{index}_{z_i}(v) = 1 + (-1)^n,$$
which is $2$ for $n$ even and $0$ for $n$ odd. This is Milnor's example on p. 39 (with pp. 32–33),
and the integer is pinned down, not merely bounded: any integer with the property V6.9 asserts of
$\chi(N)$ equals $1 + (-1)^n$ (`eq_of_indexSum_sph`). *Proof as in the book:* the field is
Milnor's, $v(x) = e - \langle e, x\rangle x$, the gradient on $S^n$ of the height function, whose
zeros are exactly $e$ and $-e$; by V6.13 the derivative on the tangent space is minus the identity
at $e$, of determinant $(-1)^n$, and the identity at $-e$, of determinant $1$, so V6.10 and V6.14
give the indices $(-1)^n$ and $1$, and V6.9 transfers their sum to every field. *A second,
independent computation of the odd case:* for $n$ odd the sphere carries a nowhere-zero field
(V5.10, converse), so the index sum is an empty sum and the integer is $0$; a third theorem derives
$1 + (-1)^n = 0$ from both computations, as it must. *Hidden hypotheses:* $n \ge 1$, from V6.9;
tangency is the condition $\langle q, v(q)\rangle = 0$, which for the sphere is what V6.9 asks; the
zeros are indexed injectively, as in V6.9. *What had to be added:* $S^n$ presented again as a slice
submanifold, because §6's tubular machinery is written for slice charts whose *complement* model is
a Euclidean space $\mathbb R^m$, whereas §5 presents $S^n$ as the level set of a real-valued
function and so with complement model the line itself; the two are isomorphic but not the same
model, so the presentation had to be redone with complement model $\mathbb R^1$, together with the
tangent space at $q$ as $q^\perp$ for that structure and the derivative through the retraction of a
field coming from the ambient space. For the same reason Milnor's odd-dimensional field of §5 had to
be rebuilt here as an ambient linear map, some forty duplicated lines: the project has no lemma
comparing two slice-submanifold structures on the same set, and a general "two slice structures,
same smooth maps" lemma would remove the duplication.
*Not formalized:* that this integer is the **Euler characteristic** of $S^n$. This is not a gap in
effort but in vocabulary: Mathlib has no Euler characteristic of a space, no Betti numbers and no
cellular homology, so the sentence $\chi(S^n) = 1 + (-1)^n$ cannot be written down at all. Every
statement here is about index sums of vector fields.

*Not formalized in Chapter 6:* the agreement of the two definitions of the index at an arbitrary
isolated zero (V6.14), and the identification of the Poincaré–Hopf integer with the Euler
characteristic (V6.9, V6.15). Both are described in §11.

**Size.** V6.0–V6.9 took 5,064 lines in 22 files: 208 for V6.0 (and 51 for the extension by a cut-off), 1,270
for V6.1 (the level-set orientation on manifolds 410, the bridge lemmas 441, the boundary form of
Lemma 1 and the product rule 239, open-subset bookkeeping 90, regular values 90), 146 for general
sign lemmas (among them the independence of the outward vector used in V5.8), 345 for V6.2 (with
the bijection-degree lemmas, and 66 more in `Compose.lean`), 639 for V6.3, 128 for V6.4, 976 for
V6.5 (the matrix determinant lemma and the radial map 230, the sign of the Jacobian 70, the
helper lemmas 202, the main proof 474), 1,020 for V6.6 and V6.7 (local parametrizations 170, the
nearest-point equation and the inverse function theorem 293, the nearest-point retraction 259,
the region and the extended field 298), 215 for V6.8–V6.9 (with the germ statement of V6.0). The
estimate of 2,000 lines in the previous edition was too low by a factor of two and a half; the
$\varepsilon$-neighbourhood theorem, which Milnor takes from §8, and the replacement of Lemma 2
account for most of the excess.

The items added since then bring Chapter 6's directory to **7,153 lines in 26 files**: 262 for
V6.10, 199 for V6.11 (of which about half is the parametric integral Mathlib lacks), 929 for
V6.13 and V6.14 together, and 699 for V6.15. V6.12, Milnor's Lemma 2, is a further 474 lines and
is counted with Chapter 7, where its file sits. The estimate of 800 lines in the previous edition
for Lemma 2 and the chart definition together was again too low, by a factor of two: 1,602 lines
for V6.11–V6.14. Two things account for the excess. The chart definition needed the derivative of
the retraction identified as the orthogonal projection onto the tangent space, which Milnor
assumes; and Lemma 2 needed a theorem Mathlib does not have, that an integral over a fixed interval
depends smoothly on a parameter. The Euler number of the sphere was not estimated at all, and its
699 lines are mostly the re-presentation of $S^n$ as a level set with a one-dimensional complement
model, so that §6's own tubular machinery applies to it.

---

## 8. Chapter 7 (Milnor §7): verified

Milnor's §7 introduces framed submanifolds and framed cobordism, associates to a smooth map
$f : M \to S^p$ and a regular value $y$ the *Pontryagin manifold* $f^{-1}(y)$ with the framing
pulled back from a positive basis of $T_y S^p$, and proves three theorems. *Theorem A:* the
framed cobordism class of the Pontryagin manifold does not depend on the regular value or on the
positive basis; the proof goes through Lemma 1 (the basis does not matter), Lemma 2 (a nearby
regular value gives a framed cobordant manifold) and Lemma 3 (smoothly homotopic maps with a
common regular value have framed cobordant Pontryagin manifolds). *Theorem C:* every compact
framed submanifold is a Pontryagin manifold; the proof uses the unlettered Product Neighborhood
Theorem. *Theorem B:* two maps are smoothly homotopic if and only if their Pontryagin manifolds
are framed cobordant; the converse direction uses Lemma 4 (maps with the same Pontryagin manifold
are smoothly homotopic). Milnor then deduces the Hopf theorem. All of this is verified below, for
$M$ a compact nonempty submanifold of $\mathbb R^{K+1}$ of dimension $m = n + p$ (with the
manifold structure of Chapter 2) and $S^p$ the unit sphere with the orientation `sphOr` of V5.9.
The V-labels follow the order of the formal development. In Milnor's names: V7.3 is Lemma 1;
V7.5 is Theorem A, and its proof contains Lemma 2; V7.6 is the first half of Theorem B, and
Lemma 3 is its special case of a common regular value; V7.2 is the construction of a framed
cobordism from a homotopy that Milnor uses inside his proofs of Lemmas 2 and 3; V7.7 is the
Product Neighborhood Theorem; V7.9 is Theorem C; V7.10 contains Lemma 4; V7.11 is the second half
of Theorem B. The project's Lean file names and docstrings use an older lettering (`ThmA.lean`
and `ThmAconv.lean` contain the two halves of Milnor's Theorem B, `ThmB.lean` and `ThmBsupp.lean`
his Theorem C, `Lemma2.lean` his Theorem A, and `Cobordism.lean` calls the construction of V7.2
"Lemma 3"). The chapter is now the largest of the formalization (19,823 lines in 68 files, having
passed Chapter 8 with the mod 2 theory of V7.18–V7.28), because Milnor's arguments quote several
facts without proof: that framed cobordism is an equivalence relation, that regular values form an
open set, that the group $GL^+$ is connected, and the Product Neighborhood Theorem, whose proof he
sketches — and, for the last theorem of the chapter, the characterization of non-orientability by a
reversing loop, which neither Milnor nor Mathlib supplies. Of those 19,823 lines, 5,438 are the
additions V7.18–V7.28, in the eleven files from `OrientTransport.lean` to
`OneManifoldOrientable.lean`, and 474 more are Milnor's Lemma 2 of §6 (V6.12), whose file sits here for
the reason given there; the older files of the chapter changed too, because the local lemmas behind
V7.13–V7.15 were restated without an orientation (V7.20). Three conventions are fixed once and for
all.

* *Tangent spaces are subspaces of the ambient space.* $T_x M \subseteq \mathbb R^{K+1}$ is the
  range of the derivative of the inclusion (`Milnor.Framed.tangentM`), and likewise for
  $N \subseteq M$ and for $S \subseteq M \times \mathbb R$ (`tangentN`, `tangentS`, the latter
  in $\mathbb R^{K+1} \times \mathbb R$ with the product inner product `ipXR`).
* *A basis at $y \in S^p$ is a basis of the model space.* The derivative of a map in Lean is a
  map between model spaces (V5.1), so "a positive basis of $T_y S^p$" is a basis $b$ of
  $\mathbb R^p$ whose orientation equals the orientation `(sphOr p).or y` of the sphere read in
  the chart at $y$. Every statement below about bases is in these terms.
* *Cobordisms live in $M \times \mathbb R$ without boundary.* Instead of a manifold with boundary
  $X \subseteq M \times [0,1]$, a framed cobordism is an $(n+1)$-dimensional submanifold
  $S \subseteq M \times \mathbb R$ which is the product $N_0 \times (-\infty, \varepsilon)$ for
  $t < \varepsilon$ and $N_1 \times (1 - \varepsilon, \infty)$ for $t > 1 - \varepsilon$, for some
  $0 < \varepsilon < \tfrac12$, with $S \cap (M \times [0,1])$ compact and a framing of $S$
  restricting to the given framings at the ends. Milnor's cobordism is $S \cap (M \times [0,1])$;
  the product structure near the ends is part of Milnor's definition of a cobordism, and is built
  into this one.

**V7.0 (framed submanifolds and framed cobordism; `Milnor.Framed.FramedSub`,
`Milnor.Framed.FramedCob`, `Milnor.Framed.FramedCobordant`).** A framed submanifold of
codimension $p$ is a compact submanifold $N \subseteq M$ of dimension $n$ together with $p$
smooth vector fields $v_1, \dots, v_p$ along $N$, tangent to $M$, orthogonal to $N$ and linearly
independent at every point (Milnor's framing of the normal bundle of $N$ in $M$, p. 41). Two
framed submanifolds are framed cobordant if a framed cobordism in the sense above exists.

**V7.1 (the Pontryagin manifold; `Milnor.Framed.pontryagin`, `Milnor.Framed.At_pontV`).** For
$f : M \to S^p$ smooth, $y$ a regular value and $b$ a basis of $\mathbb R^p$, the framed
submanifold $(f^{-1}(y), f^* b)$ is built as follows. Let $\tilde F = c_y \circ f \circ r$ be the
extension of $f$ to the $\varepsilon$-neighbourhood of $M$ (V6.6), read in the chart $c_y$ at
$y$, and $A_x = d\tilde F_x$. Then $v_i(x) = A_x^*(A_x A_x^*)^{-1} b_i$ is tangent to $M$,
orthogonal to $f^{-1}(y)$, smooth in $x$, and $A_x v_i(x) = b_i$; the $v_i$ are independent.
*Deviation (form of the framing):* Milnor takes $v_i(x)$ to be the unique normal vector with
$df_x(v_i(x)) = b_i$; this is the same vector (V7.8 proves the characterisation), written with
the pseudo-inverse so that its smoothness is a formula.

**V7.2 (the framed cobordism of a homotopy, the construction inside Milnor's proofs of Lemmas 2
and 3; `Milnor.Framed.framedCobordant_of_homotopy`, `Milnor.Framed.exists_reparam`).** Let
$0 < \varepsilon < \tfrac12$. If $F : M \times \mathbb R \to S^p$ is smooth, equal to $f$
for $t \le \varepsilon$ and to $g$ for $t \ge 1 - \varepsilon$, and $z$ is a regular value of
$F$, $f$ and $g$, then the Pontryagin manifolds of $f$ and $g$ at $z$ (same basis) are framed
cobordant; the cobordism is $F^{-1}(z)$ with the framing pulled back through the extension of
$F$ to $\mathbb R^{K+1} \times \mathbb R$. Any smooth homotopy can be reparametrized to be
constant near the ends without losing a regular value (`exists_reparam`, using a smooth
transition function $\rho$ with $\rho = 0$ for $t \le \varepsilon$, $\rho = 1$ for
$t \ge 1 - \varepsilon$ and $\rho' > 0$ in between, `Milnor.exists_timeTransition`, built from
Mathlib's smooth transition function).

**V7.3 (Lemma 1, the basis does not matter; `Milnor.Framed.framedCobordant_of_det_pos'`,
`Milnor.Framed.framedCobordant_of_orientation_eq`, `Milnor.GLp.exists_glPath`).** If $b$ and
$b'$ determine the same orientation of $\mathbb R^p$, the Pontryagin manifolds of $f$ at $y$
for $b$ and for $b'$ are framed cobordant. The cobordism is $f^{-1}(y) \times \mathbb R$ with a
framing that interpolates between the two, along a smooth path in $GL^+(p, \mathbb R)$ from the
change-of-basis matrix to the identity. *That such a path exists is the connectedness of
$GL^+(p, \mathbb R)$*, which Milnor asserts without proof in his proof of Lemma 1 (and uses again
at the end of the proof of Lemma 2 of §6); it is proved here: every matrix of positive
determinant is joined to the identity by a smooth path of matrices of positive determinant,
built from transvections (Gaussian elimination), planar rotations by $\pi$ that flip pairs of
negative diagonal entries, and a scaling of the diagonal. The general form of Lemma 1 proved here
(`framedCobordant_of_det_pos'`) allows the two maps to differ, as long as the level sets and the
framings agree; this is what the proof of V7.5 uses, through the composition rule
`Milnor.Framed.framedCobordant_comp`, for a map and its composite with a rotation.

**V7.4 (framed cobordism is an equivalence relation; `Milnor.Framed.FramedCobordant.symm`,
`Milnor.Framed.FramedCobordant.trans`, `Milnor.Framed.FramedCobordant.refl'`,
`Milnor.Problems.framedCobordant_refl`).** Chapter 7 proves symmetry and transitivity in general.
Symmetry reverses time, $(x, t) \mapsto (x, 1 - t)$, and negates the $t$-component of the
framing; transitivity shifts the second cobordism by $1$, glues along the common product end
$N_1 \times (1 - \varepsilon_1, 1 + \varepsilon_2)$, and rescales time by $\tfrac12$, scaling the
$t$-component of the framing by $2$. Reflexivity is proved in Chapter 7 only for framed
$0$-manifolds (`FramedCobordant.refl'`), which is all the Hopf theorem needs, and in every
codimension in Chapter 8 (`framedCobordant_refl`), where the classes $\Pi^p(M)$ are formed; both
proofs realise $F$ as the Pontryagin manifold of a map (Theorem C, V7.9) and apply V7.2 to the
constant homotopy. *That framed cobordism is an equivalence relation is asserted without proof on
p. 43.* The proof of symmetry and transitivity needs three facts about submanifolds of
$M \times \mathbb R$ that are not in Mathlib: the preimage of a slice submanifold under a
diffeomorphism is a slice submanifold, the tangent space at a point depends only on the
submanifold near that point, and two submanifolds that agree on an open strip glue to a
submanifold (`Milnor/Chapter7/Transport.lean`).

**V7.5 (Theorem A of §7, the regular value does not matter;
`Milnor.Framed.framedCobordant_of_regularValues`).**
For $p \ge 1$, if $y$ and $z$ are regular values of $f$ with positive bases $b$ at $y$ and $b'$
at $z$, the Pontryagin manifolds $(f^{-1}(y), f^*b)$ and $(f^{-1}(z), f^*b')$ are framed
cobordant. (The hypothesis $p \ge 1$ is part of the formal statement; it serves the proof, which
rotates one regular value to the other.) Milnor's proof is followed: a planar rotation $r_\theta$
of $S^p$ carries $y$ to $z$; if every point of the arc $r_\theta(y)$, $0 \le \theta \le \theta_0$,
is a regular value, then $z$ is a regular value of the homotopy $r_{\theta \rho(t)} \circ f$ and
V7.2 gives $f^{-1}(z) \sim (r \circ f)^{-1}(z)$, while $(r \circ f)^{-1}(z) = f^{-1}(y)$ with the
framing pulled back through $dr_y$, which preserves orientation, so Lemma 1 finishes (this is
Milnor's Lemma 2). For general $y, z$ one chooses (Sard, and the fact that *the regular values of
a map from a compact manifold form an open set*, `Milnor.Framed.isOpen_regularValues_sph`) a value
$z'$ near $z$ which is at once a regular value of the homotopy, of $f$ and of $r \circ f$, with
$y' = r^{-1}(z')$ near $y$, and chains four cobordisms using V7.4.
*A step the book omits:* Milnor's proof of Theorem A (p. 45) compares the two
Pontryagin manifolds without invoking Lemma 1, although the positive bases $b$ at $y$ and $b'$ at
$z$ are different and the rotated framing is $dr^{-1}b'$, not $b$. The formal proof closes this
with the composition rule (`Milnor.Framed.pontV_comp`) and the general form of Lemma 1.
Three tools were built for this: rotations of the sphere as smooth families with
$\operatorname{sign}(dr_\theta) = 1$ everywhere (`Milnor.Sphere.rotS`, `signAt_rotS`, via
V6.5's sign formula for linear maps), the composition rule for Pontryagin manifolds
(`Milnor.Framed.pontV_comp`: $(r \circ f)^*b = f^*(dr_y^{-1} b)$), and the fact that a map
with sign $1$ carries orientations (`Milnor.orientation_map_of_orSign_eq_one`).

**V7.6 (Theorem B of §7, first half, with Lemma 3; `Milnor.Framed.framedCobordant_of_homotopic`).**
For $p \ge 1$, if $f$ and $g$ are smoothly homotopic, $y$ is a regular value of $f$ and $z$ one of
$g$ (positive bases), then their Pontryagin manifolds are framed cobordant. For $y = z$ this is
Milnor's Lemma 3. (Choose a common regular value of the homotopy and of both ends,
reparametrize, apply V7.2, then V7.5 twice.)

**V7.7 (the Product Neighborhood Theorem; `Milnor.PN.exists_injOn`,
`Milnor.PN.isOpen_image_tube`, `Milnor.PN.contMDiffAt_Ginv`, `Milnor.Framed.exists_tubeData`).**
For a framed submanifold $(N, v)$ of $M$ there is $\varepsilon > 0$ such that
$G(x, s) = r\bigl(x + \sum_i s_i v_i(x)\bigr)$, $r$ the nearest-point retraction of V6.6, is a
smooth map $N \times B_\varepsilon \to M$, injective, with open image and smooth inverse, with
$G(x, 0) = x$ and $dG_{(x,0)}(a, s) = a + \sum_i s_i v_i(x)$. The abstract part is proved in a
general setting and reused for the cobordism $S \subseteq M \times \mathbb R$ in V7.10: let $N$
be a first countable manifold modelled on $\mathbb R^n$, $X$ a Hausdorff manifold without boundary
modelled on a finite-dimensional space, $G : N \times \mathbb R^p \to X$ smooth and injective on
$N \times \{0\}$, and $K \subseteq N$ compact such that $dG$ is bijective along $K \times \{0\}$
and $G$ is already known to be injective on the pairs of points of $N \times B_{\varepsilon_0}$
with first coordinate outside $K$; then $G$ is injective on some $N \times B_\varepsilon$ (the
inverse function theorem in charts and a compactness argument over $K$; $N$ itself need not be
compact, which is what the cobordism case requires). If $dG$ is bijective on
$N \times B_\varepsilon$, the image is open, and for $N$ nonempty the inverse is smooth on it.
*Deviation (form):* Milnor's diffeomorphism $N \times \mathbb R^p \to V$ is here the map $G$ on a
ball, with a smooth clamp $\lambda$ of $\mathbb R^p$ applied to $s$ so that $G$ is defined and
smooth everywhere; the inverse is a function on $M$ that is smooth on
$V = G(N \times B_\varepsilon)$.

**V7.8 (identification of the framing; `Milnor.Framed.ker_At_eq`, `Milnor.Framed.pontV_eq_of`,
`Milnor.Framed.pontryagin_eq_of_collapse`).** At $x \in f^{-1}(y)$ the kernel of
$A_x = d\tilde F_x$ is $T_x N \oplus (T_x M)^\perp$ (a dimension count), so a vector tangent to
$M$, orthogonal to $N$, with $A_x v = b_i$ is the framing vector $f^*b_i(x)$. Consequently, if
$k : M \to S^p$ has $k^{-1}(\mathrm{north}) = N$ and along each framing line
$k(r(x + s v_i(x))) = \pi(c\,A(s e_i))$ for $|s| < \varepsilon'$ (some $\varepsilon' > 0$ and
$c > 0$), where $\pi$ is the fixed map of V7.9 and $A = (d\pi_0)^{-1}B$ with $B e_i = b_i$ (the
collapse map adapted to $b$), then the north pole is a regular value of $k$ and the Pontryagin
manifold of $k$ at the north pole with basis $c\,b$ is exactly $(N, v)$.

**V7.9 (Theorem C of §7; `Milnor.Framed.exists_map_of_framedSub`, `Milnor.Sphere.stdMap`,
`Milnor.Sphere.collapse`).** Every framed submanifold $(N, v)$ of $M$ is the Pontryagin
manifold of some smooth $f : M \to S^p$ at the north pole: for any basis $b$ of $\mathbb R^p$
there are $c > 0$ and $f$ with $(f^{-1}(\mathrm{north}), f^*(c\,b)) = (N, v)$. The map is
$f(G(x, s)) = \pi(c A s)$ on the product neighbourhood and the south pole elsewhere, where
$\pi : \mathbb R^p \to S^p$ is a fixed smooth map with $\pi^{-1}(\mathrm{north}) = \{0\}$,
$d\pi_0$ invertible and $\pi = \mathrm{south}$ outside the ball of radius $\tfrac12$, and $A$
is chosen so that $d(c_{\mathrm{north}} \circ \pi \circ A)_0 = b$ up to the scalar $c$.
*Deviation (the scalar $c$):* with a fixed collapse map the derivative along the framing comes
out as $c\,b$, not $b$; since the framing is what matters and $c$ only rescales the basis, this
is harmless (V7.10 and V7.11 carry it along; Lemma 1 absorbs it).

**V7.10 (Lemma 4 and the map of a cobordism; `Milnor.Framed.exists_deform`,
`Milnor.Framed.smoothHomotopic_of_pontryagin_eq`, `Milnor.Framed.exists_cobMap`).** (a) Let
$N$ be nonempty and let the product neighbourhood $G$ of $(N, v)$ (V7.7) be given. If
$k : M \to S^p$ has $k^{-1}(y) = N$ and derivative $c\,b_i$, with $c > 0$, on the framing
vectors of $(N, v)$ (read in the chart $c_y$ at $y$), then $k$ is smoothly homotopic to a map $k'$
which near $N$ is the standard map $G(x, s) \mapsto c_y^{-1}\bigl(c_y(y) + \sum s_i b_i\bigr)$
and does not take the value $y$ off $N$. The homotopy is the bump-function interpolation, in the
chart at $y$, between the chart representative $\Phi$ of $k \circ G$ and its linearisation
$L s = \sum s_i b_i$; that $k'$ takes the value $y$ only on $N$ follows from
$|\Phi(x, s) - c L s| \le \kappa |s|$ uniformly (a uniform first-order estimate on a tube,
`Milnor.exists_uniform_taylor`, from joint continuity of the fibre derivative and the mean value
inequality). The formal statement records this for the end map $k'$ only; Milnor's remark that
the deformation creates no new preimages of $y$ at intermediate times is not part of it, and is
not needed. (b) Two maps with the same Pontryagin manifold at $y$, for bases $b$ and $c\,b$ with
$c > 0$ (Milnor: the same basis), are smoothly homotopic: deform both to the standard form, then
join them by the straight-line homotopy in stereographic coordinates from $y$
(`Milnor.Sphere.exists_homotopy_of_eqOn`: maps agreeing on an open set and avoiding $y$
outside it are smoothly homotopic relative to that set). This is Milnor's Lemma 4 (p. 47).
(c) For a framed cobordism $S$ between $F_0$ and $F_1$ there is a smooth
$H : M \times \mathbb R \to S^p$ whose restrictions to $t = 0$ and $t = 1$ have Pontryagin
manifolds $F_0$ and $F_1$ at the north pole (with a common basis $c\,b$). The construction is
V7.9 applied to $S \cap (M \times (-3, 4))$, using the product structure of the ends to obtain
the injectivity radius outside a compact piece. The resulting map $H_0$ is defined on all of
$M \times \mathbb R$ but is smooth only on $M \times (-2, 3)$; so the time variable is clamped,
$H(x, t) = H_0(x, \rho(t))$ with $\rho$ smooth, equal to the identity near $[0, 1]$ and with
values in $(-2, 3)$, which makes $H$ smooth on all of $M \times \mathbb R$.

**V7.11 (Theorem B of §7, second half; `Milnor.Framed.smoothHomotopic_of_framedCobordant`,
`Milnor.SmoothHomotopic`).** For $p \ge 1$, if the Pontryagin manifolds of $f$ at $y$ and of
$g$ at $y'$ (positive bases) are framed cobordant, then $f$ and $g$ are smoothly homotopic.
Smooth homotopy, defined by a smooth map $M \times \mathbb R \to S^p$ restricting to the two
maps at $t = 0, 1$, is an equivalence relation (`SmoothHomotopic.refl/symm/trans`; transitivity
glues two homotopies made constant near their ends). The proof rotates both regular values to
the north pole (a homotopy through rotations that changes the Pontryagin manifold only by the
rotated basis, V7.5), uses V7.3 to make the two bases equal, builds the map $H$ of V7.10(c) for
the cobordism, and applies V7.10(b) at both ends.

**V7.12 (framed $0$-manifolds and the signed count; `Milnor.Framed.frameSign`,
`Milnor.Framed.count`, `Milnor.Framed.count_pontryagin`).** For $n = 0$ and $p = m$ a framed
submanifold is a finite set of points (finiteness is proved: a compact $0$-dimensional slice
submanifold is finite), each carrying $m$ tangent vectors forming a basis of $T_x M$. Relative to
an orientation of $M$ (V5.0) each point has a sign $\pm 1$, the sign of the basis of chart
coordinates of the frame against $o_x$, and the *signed count* is the sum of the signs. **For
$m \ge 1$ and the Pontryagin manifold of $f : M \to S^m$ at a regular value $y$ with a positive
basis, the sign of $x \in f^{-1}(y)$ is the sign of $df_x$, so the signed count is the degree of
$f$** (V5.7). This is, in formal form, Milnor's statement (p. 50) that the sum of the signs is
the degree of the associated map; his next statement, that the framed cobordism class of the
$0$-manifold is determined by this integer, is V7.16.

**V7.13 (moving a framed point; `Milnor.Framed.exists_move`,
`Milnor.Framed.exists_reach`).** Let $m \ge 1$, let $\varphi$ be the chart at a point $x_c$ of
$M$, let $R > 0$ be such that the closed ball of radius $R$ about $\varphi(x_c)$ lies in the chart
image and $\varphi$ preserves orientation on the corresponding chart ball $U$, and suppose that no
point of $N$ other than $x_0$ lies in the closure of $U$. If $x_0 \in N$ and $x_1$ lie in the
chart ball of radius $R/4$ about $\varphi(x_c)$, and $x_1$ carries a frame $v_1$ of the same sign
as $v_0$, then $(N, v)$ is framed cobordant to $(N, v)$ with $(x_0, v_0)$ replaced by
$(x_1, v_1)$. The cobordism is the Pontryagin manifold of a homotopy: the Theorem-C map of
$(N, v)$ (V7.9, with its support kept away from the frontier of $U$) is replaced on $U$ by a
collapse map whose centre moves from $\varphi(x_0)$ to $\varphi(x_1)$ and whose linear part moves
along a path in $GL^+$ or $GL^-$ (V7.3) from the matrix producing $v_0$ to the one producing
$v_1$; V7.2 gives the cobordism, and the framings at both ends are identified as in V7.8.
Consequently ($m \ge 1$, $M$ oriented) every point of the connected component of $x_0$ in
$M \setminus (N \setminus \{x_0\})$ can be reached, with any frame of the right sign (the set of
reachable points is open and closed in the component).
*Deviation (proof):* Milnor moves points along paths; here the moves are homotopies of maps
inside chart balls, and paths are replaced by the open-closed argument.

**V7.14 (cancelling a pair; `Milnor.Framed.exists_cancel`,
`Milnor.Framed.cancel_step`).** Let $m \ge 1$, and let $\varphi$, $x_c$, $R$ and $U$ be as in
V7.13 (closed $R$-ball in the chart image, $\varphi$ orientation-preserving on $U$), with no point
of $N$ other than $x_1, x_2$ in the closure of $U$. If $x_1, x_2 \in N$ are the points
$\varphi^{-1}(c_0 \pm a w)$ with $w$ a unit vector, $|c_0 - \varphi(x_c)| < R/8$ and
$0 < 8a \le R$, then $(N, v)$, with the frames at $x_1, x_2$ replaced by the *standard* ones, is
framed cobordant to $(N, v)$ with $x_1, x_2$ removed; the standard frames have signs $\varepsilon$ and $-\varepsilon$, where
$\varepsilon = \pm 1$ depends only on the chart (it is the sign of the identity of $\mathbb R^m$
from $o_{x_c}$ to the standard orientation), so a pair of arbitrary frames of opposite signs is
cancelled after two frame changes (V7.13, with $w$ or $-w$ according to which point has sign
$\varepsilon$). The homotopy is the collapse map composed with
$s \mapsto (\langle s, w\rangle^2 - a^2\rho(t))\, w + (s - \langle s, w\rangle w)$, whose zero
set at time $t$ is $\{\lambda w : \lambda^2 = a^2 \rho(t)\}$ with $\rho$ going from $1$ to $-1$;
at the moment the two zeros merge the time derivative makes the north pole a regular value of the
homotopy, as V7.2 requires. Combined with the neighbour lemma (V7.15): if $x_0$ has a
neighbour $z$ of the opposite sign, $x_0$ is first moved next to $z$ (V7.13) and the pair
cancelled (`cancel_step`, which finds a suitable chart ball about $z$).

**V7.15 (the neighbour lemma and chains; `Milnor.exists_neighbour`,
`Milnor.Framed.exists_neighbour_M`, `Milnor.exists_chainRel`).** In a connected, locally
connected $T_1$ space, let $N$ be finite and, for $x \in N$, let $C(x)$ be the connected component
of $x$ in the complement of $N \setminus \{x\}$; assume every $x \in N$ has a neighbourhood meeting
$N$ only in $x$ and contained in $C(x) \cup \{x\}$ (true for chart balls, by joining points to
the centre along segments). Then for every partition of $N$ into two nonempty parts some point
of one part lies in the closure of $C(x)$ for a point $x$ of the other part ("$x$ has a
neighbour in the other part"). Proof: otherwise one part together with its components is open,
closed, nonempty and not everything. The same argument gives chains of consecutive neighbours
from one part to the other. *This is the formal content of the connectedness of $M$ in Milnor's
"it is not difficult to see" (the Hopf theorem, end of §7).* It is needed in this form because
for $m = 1$ points cannot pass each other, so that a point of $F$ may have to be moved onto a
point of $G$ along a chain through points that are already in place, which are moved one step
each.

**V7.16 (framed cobordism classes of framed $0$-manifolds;
`Milnor.Framed.framedCobordant_of_count_eq`).** Two framed $0$-manifolds of a compact
connected oriented $M$ ($m \ge 1$) with the same signed count are framed cobordant.
Induction on the total number of points: if one of them has points of both signs, V7.15 gives
a neighbouring pair of opposite signs and V7.14 removes it without changing the count; if all
points of $F$ have one sign and all points of $G$ have one sign, equal counts force the same
sign and the same number of points; the frames at common points are matched by frame changes,
and then the points of $F$ are moved onto the points of $G$ one at a time along shortest chains
of neighbours (`gather`).

**V7.17 (the Hopf theorem; `Milnor.Framed.hopf_homotopic`, `Milnor.Framed.exists_map_of_deg`).**
Let $M \subseteq \mathbb R^{K+1}$ be a compact connected oriented submanifold of dimension
$m \ge 1$. Two smooth maps $M \to S^m$ with the same degree are smoothly homotopic (the
converse is Theorem B of §5, V5.7), and every integer is the degree of a smooth map
$M \to S^m$ (for this second statement $M$ need not be connected). Proof of the first: choose
regular values and positive bases; the signed counts of the two Pontryagin manifolds are the two
degrees (V7.12), so the Pontryagin manifolds are framed cobordant (V7.16) and the maps are
homotopic (V7.11). Proof of the second: starting from
the empty framed $0$-manifold, add $|d|$ points of the required sign one at a time (a point
outside a finite set exists because chart balls are infinite; the new point is added by gluing
a stationary collapse map onto the Theorem-C map, `exists_add_point`), then apply Theorem C
(V7.9) and V7.12. *Deviations:* homotopy means smooth homotopy (V4, convention), and $M$ is a
submanifold of Euclidean space, as in all of §6–§7. Milnor's remark that for non-orientable
$M$ the maps are classified by the degree modulo $2$ is V7.26, at the end of this section.

The eleven items that follow prove that remark. Milnor gives it a single clause of justification — a
framed point carried around an orientation-reversing loop comes back with its frame reversed, so
only the parity of the number of points of a framed $0$-manifold survives — and the clause
presupposes what an orientation-reversing loop is and that a non-orientable manifold has one.
An orientation of a manifold is V5.0, Milnor's own; **orientability as a property, and its
characterization by reversing loops, existed neither in Mathlib nor anywhere in this project, and
the book does not prove it either**. So the work is in two halves: orientability and the loop
(V7.18, V7.19, V7.22), and the removal of the signs from the framed machinery (V7.20, V7.21,
V7.23–V7.25), ending in the theorem itself (V7.26); two further items (V7.27, V7.28), written after
the Appendix was finished, then remove the one hypothesis that route left behind. The survey behind them found that the framed
theory is almost entirely orientation-free already: V7.0, V7.1 and V7.9 take no orientation of $M$
at all and V7.11 needs one only on the sphere, so what had to be redone is one definition, the sign
of a frame (V7.12), and the endgame that cancels a plus against a minus (V7.14, V7.16).

**V7.18 (orientability, transport of an orientation, and the chart-level dichotomy;
`Milnor.IsOrientable`, `Milnor.orTransport`, `Milnor.ChartHop`, `Milnor.ChartChain`,
`Milnor.Orient.isTransportSection`, `Milnor.Orient.ofTransportSection`,
`Milnor.ChartChain.Reverses`, `Milnor.isOrientable_of_forall_not_reverses`,
`Milnor.IsChartCoherent`, `Milnor.exists_isChartCoherent_iff_forall_not_reverses`,
`Milnor.exists_reverses_of_not_isOrientable`, `Milnor.Orient.or_eq_or_eq_neg`).** Let $M$ be a
manifold modelled on a finite-dimensional $E$ with $\dim E = m$. (i) $M$ is *orientable* if it
carries an orientation in the sense of V5.0. (ii) The derivative at $y$ of the chart centred at $x$
is a linear isomorphism, so exactly one orientation of the model space at $y$ is carried by it to a
given orientation at $x$: this is the *transport* $o \mapsto \operatorname{tr}_{x \to y} o$
through that chart, an involution which anticommutes with reversal. An orientation of $M$ is
exactly a family of orientations which near every point is the transport of its value at that
point. (iii) A *hop* from $x$ to $y$ is a single chart whose source contains both; a *chain* is a
finite sequence of hops; chains compose and reverse, transport along a composite is the composite
of the transports, and transport along the reverse undoes the chain. In a connected manifold any
two points are joined by a chain (the reachable set is open and closed). (iv) A chain-loop
*reverses* if its transport carries some orientation at the base point to the opposite one; which
of the two is tested is immaterial. (v) **Half of the dichotomy:** if no chain-loop at a point of a
connected $M$ reverses, then $M$ is orientable — transport a fixed orientation from the base point,
the answer being unambiguous because two chains differ by a loop. Contrapositively, a connected
non-orientable manifold carries at every point a chain-loop that reverses *every* orientation
there. (vi) A connected orientable manifold has exactly two orientations, a given one and its
pointwise reverse. *Deviation, and a warning:* the converse of (v) is **false** for an orientation
in the sense of V5.0, whose compatibility is a condition only *near* each point. It holds for the
stronger notion of an orientation coherent with every chart on the *whole* of that chart's source,
and for connected $M$ the absence of reversing chain-loops is equivalent to the existence of such a
chart-coherent orientation. The counterexample is recorded in the Lean file: on $\mathbb R$ take
the atlas consisting of the identity together with the chart that is $x$ on $(-1, 0)$ and $3 - x$
on $(1, 2)$; this is a smooth structure on $\mathbb R$, which is orientable, and yet the
orientation that is standard except reversed on $(1, 2)$ satisfies the condition of V5.0 while the
loop out through the second chart and back through the identity chart reverses. The culprit is
that a chart source may be disconnected, and V7.19 removes the defect. *A step the design did not
foresee:* a hop must record *which* chart it travels through. The naive relation "some chart
contains both points" is not symmetric in the transport it induces, and the obvious symmetric
repair is wrong, precisely because two charts can disagree on a disconnected overlap.
*Hidden hypotheses:* none — no boundarylessness, no Hausdorffness, no second countability, and
$M$ may be empty; connectedness only where it is stated.

**V7.19 (chart balls and the exact dichotomy; `Milnor.chartBall`,
`Milnor.isPreconnected_chartBall`, `Milnor.BallHop`, `Milnor.ChartChain.IsBall`,
`Milnor.BallHop.transport_or`, `Milnor.ballReachable_of_preconnectedSpace`,
`Milnor.isOrientable_iff_forall_not_reverses_isBall`,
`Milnor.exists_isBall_reverses_of_not_isOrientable`).** A *chart ball* is the preimage under the
chart centred at $c$ of a round ball about the chart image of $c$; when that ball lies in the
target of the chart, the chart ball is connected, which is the one property a chart source lacks.
A *ball hop* is a hop through such a ball containing both its endpoints, a *ball chain* a chain all
of whose hops are of that kind; the entire transport algebra of V7.18 applies verbatim, only the
predicate having to be shown closed under the constructions. **The key lemma:** every orientation
of $M$ is *ball-coherent* — transport along a ball hop carries the orientation at one end to the
orientation at the other. (On a chart ball about $c$ the function
$z \mapsto \operatorname{sgn}(o_z \text{ against } o_c \text{ through } d\varphi_c)$ takes only the
values $\pm 1$, is locally constant by the continuity field of V5.0, equals $1$ at $c$, and a
locally constant function on a connected set is constant. For a chart source the conclusion is
false, which is exactly the counterexample of V7.18.) Hence **the exact dichotomy:** for connected
$M$ and any base point, $M$ is orientable *if and only if* no ball-chain-loop at that point
reverses; and a connected non-orientable $M$ carries at every point a ball-chain-loop reversing
every orientation there. *Why this matters:* unlike V7.18(v) the converse now holds with no
auxiliary notion, so a reversing ball loop is a genuine obstruction to orientability rather than a
symptom of a badly chosen atlas — and the loops run through round balls, which is what the moving
machinery of V7.13 can follow. *Hidden hypothesis:* the model boundaryless, on 24 of the 61
declarations and for two independent reasons, both of which are that a chart target must be open:
a ball inside the chart target has to exist at all (hence for every statement that *produces* a
ball hop, including the converse half), and the sign of a chart derivative has to be locally
constant (hence for the key lemma and the forward half). Everything about a chart ball that is
*given* needs it not. Hausdorffness, second countability and positivity of the dimension are
nowhere needed.

**V7.20 (the chart sign of a frame; `Milnor.Framed.chartSign`, `Milnor.Framed.selfSign`,
`Milnor.Framed.jacSign`, `Milnor.Framed.chartSign_eq_jacSign_mul_selfSign`,
`Milnor.Framed.frameSign_eq_orEps_mul_selfSign`, `Milnor.Framed.exists_frame_of_selfSign`,
`Milnor.Framed.exists_frame_transport`).** The sign of V7.12 is defined against an orientation of
$M$, which a non-orientable $M$ does not have, so the local lemmas must be restated with a sign
that mentions none. The *chart sign* of a frame $v$ at $x$ relative to a centre $x_c$ is the
determinant sign of $v$ read in the chart at $x_c$; the *self sign* is the case $x_c = x$; the
*Jacobian sign* is the determinant sign of the derivative at $x$ of the chart at $x_c$. All three
are $\pm 1$ for a tangent independent frame at a point of the chart's source, none mentions an
orientation, and $\text{chart sign} = \text{Jacobian sign} \cdot \text{self sign}$, with Jacobian
sign $1$ at the centre. **The bridge to the oriented theory:** the sign of V7.12 satisfies
$$\operatorname{frameSign}(v, x) = \varepsilon(x)\cdot \text{self sign}(v, x),$$
where $\varepsilon(x)$ depends only on the point and not on the frame. *The sign of a frame against
an orientation of the manifold is thus the determinant sign of the frame read in one chart, times a
factor depending only on the point* — and that is what lets the local machinery run without an
orientation, since every local proof compares a product of two such signs, in which the factor
cancels. At the level of a chart ball the same holds with the hub's factor, so equality of frame
signs at two points of a ball is exactly equality of their chart signs relative to the hub. Also:
frames of both chart signs exist at *every* point, with no case split on a global reference sign,
and a frame at $x$ may be transported to any other point of the same chart's source as the same
frame read in that chart, hence with the same chart sign. *Consequences for the earlier items:*
V7.13–V7.15 are restated in these terms (`MoveH` and `CancelH` no longer mention an orientation at
all; six theorems lost two hypotheses each, and a lemma whose hypothesis "the chart preserves
orientation" was spurious is deleted in favour of the general one), and the oriented statements are
short corollaries beside the sign-free ones, so that no proof is duplicated. The sign of the frame
at a zero of the cancelling map is now flatly the sign of the signed distance, where before it
carried a factor depending on the orientation. *A better primitive than expected:* the self sign
needs no chart-membership hypothesis at all, which is what makes it usable in the clopen arguments
of V7.23.

**V7.21 (the sign dictionary, the transition cocycle, and chains avoiding a set;
`Milnor.jacSign`, `Milnor.hopSign`, `Milnor.chainSign`, `Milnor.chainSign_comp`,
`Milnor.chainSign_reverse`, `Milnor.ChartChain.transport_eq_signAct`,
`Milnor.ChartChain.reverses_iff_chainSign`, `Milnor.eventually_jacSign_mul_jacSign_eq`,
`Milnor.ChartChain.IsBallIn`, `Milnor.exists_isBallIn`,
`Milnor.exists_isBallIn_avoiding`).** (i) *The dictionary.* Transport across a chart is
multiplication by the Jacobian sign; the sign of a hop is the product of the two Jacobian signs of
its chart at the two endpoints; the sign of a chain is the product of the signs of its hops. The
sign of a composite is the product, a chain and its reverse have the same sign, transport along a
chain is multiplication by its sign, and **a loop reverses exactly when its sign is $-1$**, so the
dichotomy of V7.19 becomes arithmetic. All of this holds for arbitrary chart chains, not only ball
ones, at no extra cost. (ii) *The transition cocycle lemma.* For two chart centres $p$, $q$ and a
point $y$ in both their sources, the product of the two Jacobian signs at $z$ is *locally constant*
in $z$ near $y$. Neither factor is, because each reads a fixed chart through the moving chart at
$z$; but in the product the moving chart cancels and what is left is the determinant sign of the
fixed smooth transition
$\varphi_p \circ \varphi_q^{-1}$, which is continuous and invertible, hence of locally constant
sign. This is the technical key, used in V7.22 and again in V7.23. (iii) *Avoidance.* A hop *runs
inside* a set $C$ if the closed chart ball of its radius lies in $C$; for $C$ open and
preconnected any two of its points are joined by a chain of hops running inside $C$, and such a
chain automatically avoids every set disjoint from $C$ — indeed each of its closed chart balls
does. *Two hypotheses weaker than expected:* the avoided set need not be closed, only disjoint
from the region, and the region need only be preconnected. *One hypothesis that had to be added:*
avoidance is phrased through the *closed chart ball* rather than the topological closure of the
ball, because on a non-Hausdorff manifold the closure of a chart ball need not lie in its chart —
on the line with two origins the closure of an interval about one origin contains the other. The
closure form is given separately under Hausdorffness, which is free in this chapter, where the
manifolds are subsets of a Euclidean space.

**V7.22 (punctures, and the punctured dichotomy;
`Milnor.isConnected_chartBall_diff_singleton`, `Milnor.isConnected_compl_finite`,
`Milnor.infinite_of_isOpen`, `Milnor.IsBallCoherentOn`, `Milnor.extend_ballCoherent`,
`Milnor.HasReversingBallLoop`, `Milnor.hasReversingBallLoop_of_not_isOrientable`).** The loops of
V7.19 must avoid the other points of a framed $0$-manifold, so the dichotomy has to be run on the
complement of a finite set. Verified, for $2 \le m$: a punctured chart ball is path connected; the
complement of a finite set in a connected $M$ is connected, and nonempty as soon as $0 < m$ (a
nonempty open subset of a manifold of positive dimension is infinite); a family of orientations of
the tangent spaces that is ball-coherent on the complement of a finite set $P$ agrees off $P$ with
an orientation of the whole of $M$; and hence **the punctured dichotomy:** a connected
non-orientable manifold of dimension at least two has, at every point outside a given finite set, a
loop of chart balls at that point missing the set and of chain sign $-1$. The extension lemma is
where the cocycle lemma of V7.21 earns its keep: the value at a puncture $p$ is the value at a
nearby point transported back to $p$, well defined because that assignment is locally constant on a
punctured ball about $p$ — the two Jacobian signs being separately discontinuous and jointly
locally constant — and because the punctured ball is connected. *Hidden hypothesis:* $2 \le m$, and
it is **sharp**, not a convenience: for $m = 1$ a punctured ball is an interval minus an interior
point, and $\mathbb R \setminus \{0\}$ is a disconnected complement of a finite set in a connected
$1$-manifold; for $m = 0$ a punctured ball is empty. This item therefore keeps $2 \le m$, and
keeps it sharply; but it is no longer a restriction on anything downstream, because it is now
*derivable* where it is used. It was the sole source of the dimension restriction in V7.26, and
V7.28 derives $2 \le m$ from non-orientability by way of the classification of one-manifolds (§10),
so the theorems that appeal to this item supply the hypothesis instead of assuming it.
*Deviations from the expected route, both simplifications:* well-definedness
of the extension holds at *every* point, not only at the punctures, so the extension is one total
function with no case split and the transport-section condition is checked at every point at once;
and no separation hypothesis is needed anywhere, charts giving $T_1$ for free. *What had to be
added:* that no point of a manifold of positive dimension is isolated, and that a locally constant
function on a connected set is constant — Mathlib's version wants a discrete target, and the two
orientations of a vector space carry no topology.

**V7.23 (the slide and the flip; `Milnor.Framed.exists_slide`,
`Milnor.Framed.exists_reach_any`, `Milnor.Framed.exists_flip`,
`Milnor.Framed.exists_frame_free`, `Milnor.Framed.exists_reach_free`).** Let $m \ge 1$ and let
$(N, v)$ be a framed $0$-manifold of a compact nonempty $M$. (i) *The slide:* given a chain of
chart balls from a point $x_0$ of $N$ to $y$, none of whose balls meets any other point of $N$,
$(N, v)$ is framed cobordant to a framed $0$-manifold with point set
$(N \setminus \{x_0\}) \cup \{y\}$, the same frames elsewhere, and self sign at $y$ equal to the
chain sign (V7.21) times the self sign at $x_0$. (ii) *The flip:* if the chain is a *loop* at
$x_0$ of chain sign $-1$, the point set and all the other frames are literally unchanged and the
self sign at $x_0$ is reversed. **This is Milnor's clause.** (iii) Consequently, with a reversing
loop available, the frame at a point may be replaced by *any* tangent independent frame, and the
point may be moved anywhere in its component of $M \setminus (N \setminus \{x_0\})$ with any frame:
this is V7.13 with the orientation and its sign hypothesis simply deleted. *Hidden hypotheses:*
$0 < m$, $M$ compact and nonempty, which the Theorem-B machinery behind V7.13 needs. No
orientation, no connectedness, no $2 \le m$ and no Hausdorffness occur; the reversing loop is a
hypothesis here, in exactly the form V7.22 produces it, so the two halves join with no glue.
*Where the plan was wrong:* one ball hop cannot be performed by one application of V7.13, because a
move needs its two points inside a quarter-radius ball whose closed ball fits in the chart, while a
hop's endpoints can be almost a full diameter apart and the chart target need not contain a ball
four times as large. So each hop is subdivided, and the sign must be shown not to notice the
subdivision; that needs an open-set form of the cocycle lemma of V7.21 and a change-of-hub lemma,
and the invariant carried across a hop turns out to be the chart sign at the hop's own hub. *An
improvement:* the sign-free reach lemma needs the reversing loop only at the starting point, not at
the target.

**V7.24 (sign-free cancellation; `Milnor.Framed.framedCobordant_of_frames_free`,
`Milnor.Framed.cancel_step_free`, `Milnor.Framed.exists_neighbour_pair`).** Let $(N, v)$ be a
framed $0$-manifold of $M$, as in V7.23, and let reversing ball loops be available off every finite
set. (i) Two framed $0$-manifolds with the same point set and the
same frames away from two distinct points are framed cobordant, with **no** condition relating the
frames at those two points; (ii) *any* two distinct points of $N$, one in the closure of the
component of the other, can be cancelled — V7.14 with its opposite-sign hypothesis deleted
outright; (iii) if $N$ has two distinct points and $M$ is connected, some two of them are
neighbours in that sense, which is V7.15 with the signs deleted, the partition handed to the
neighbour lemma being $\{x\} \sqcup (N \setminus \{x\})$ instead of a partition by sign. *Hidden
hypotheses:* $0 < m$, $M$ compact and nonempty; no orientation and no $2 \le m$. *Where the plan
was wrong, and this is the point of the remark:* it prescribed choosing an arrival frame of the
opposite sign and replacing the old case split by a new one. Neither is needed. The cancellation
lemma supplies its own two frames, of chart signs $+1$ and $-1$, and "frames are free at two
points" connects any configuration to that one, so the arriving frame may be arbitrary and the case
split *disappears* rather than being replaced. The sign-free cancel step is therefore **shorter**
than the signed one.

**V7.25 (the count modulo 2, and the parity classification; `Milnor.Framed.countMod2`,
`Milnor.Framed.framedCobordant_of_countMod2_eq`, `Milnor.Framed.countMod2_pontryagin`).** The
*count modulo 2* of a framed $0$-manifold is the cardinality of its point set read in
$\mathbb Z/2$; no orientation occurs in the definition, in contrast with V7.12. Verified: (i) two
framed $0$-manifolds of a connected $M$ with the same count modulo $2$ are framed cobordant,
given reversing ball loops off every finite set; (ii) the count modulo $2$ of the Pontryagin
manifold of $f : M \to S^m$ at a regular value is the mod 2 degree of $f$ (V4.8) — both are the
parity of $\#f^{-1}(y)$, and, unlike V7.12, this needs nothing of the framing, so the frame may be
any independent tuple rather than a positive basis. This is Milnor's statement on p. 50 that the
framed cobordism class is determined by the number of points modulo $2$, and it is V7.16 with the
signed count replaced by the parity. *Hidden hypotheses:* $0 < m$, $M$ compact, nonempty and
connected; $2 \le m$ does not appear, being needed only to produce the loops — and since V7.27 the
loops are available on a connected non-orientable $M$ with no dimension hypothesis whatever, so the
non-orientable form of (i), `Milnor.Framed.framedCobordant_of_card_parity`, which is where the
reversing loops are actually discharged and which is stated with V7.26, carries none either.
*Deviation (route of
proof):* the signed induction of V7.16 can cancel only while both signs occur and needs a separate
gathering argument when they do not; here the induction runs on the cruder condition "two or more
points", there is no gathering step at all, and it stops when each side has at most one point,
which is then carried onto the other by V7.23.

**V7.26 (Milnor's theorem of p. 50; `Milnor.Framed.hopf_homotopic_mod2`,
`Milnor.Framed.smoothHomotopic_of_degMod2_eq`, `Milnor.Framed.framedCobordant_of_card_parity`,
`Milnor.Framed.degMod2_eq_of_smoothHomotopic_sph`, `Milnor.degMod2_eq_of_smoothHomotopic`).** Let
$M \subseteq \mathbb R^{K+1}$ be a closed connected **non-orientable** submanifold of dimension
$m$ (compact, nonempty, in the sense of V7.0 and with the manifold structure of
Chapter 2, and non-orientable in the sense of V7.18). Then two smooth maps $M \to S^m$ are
smoothly homotopic **if and only if** they have the same degree modulo $2$. This is Milnor's
theorem at the end of §7, the counterpart for non-orientable $M$ of the Hopf theorem V7.17.
*The easy half* is the homotopy invariance of the mod 2 degree (V4.8, the second assertion of the
Theorem of §4) transcribed into the homotopy relation of this chapter:
it needs no orientation of any kind, no connectedness and nothing of the dimension beyond $0 < m$,
which is only what the mod 2 degree needs of its target. *The substantial half* is Milnor's remark,
and runs through Sard (V3.3) for a regular value of each map, a positively oriented basis of the
sphere at each — orientations of the **target sphere**, which the Pontryagin construction and the
converse of Theorem B require and which are the only orientations in the whole argument; the source
carries none and is assumed not to have one — the two Pontryagin manifolds (V7.1), the parity bridge
and the parity classification (V7.25), and the converse half of Theorem B (V7.11), which is itself
orientation-free. *No hidden hypothesis of dimension:* the theorem as stated has **none at all**.
Each half wants $0 < m$, which is all the mod 2 degree needs of its target, and each half gets it
from non-orientability along with everything else, so the dimension does not appear among the
hypotheses of the two-way statement. Earlier editions of this statement assumed $2 \le m$, which is
**mathematically vacuous**: a connected $1$-manifold is diffeomorphic to the circle or to an
interval and all of those are orientable, so a connected non-orientable manifold has dimension at
least two and non-orientability already implies it. It was carried only because the classification
of one-manifolds was not formalized in this project. It now is (§10), the deduction is V7.28, and
since the hypothesis enters at exactly one point, the appeal to V7.22, each of the three statements
here that mentions non-orientability derives it there in one line instead of assuming it.
*Deviations:* homotopy means smooth homotopy (V4, convention), and $M$ is a submanifold of
Euclidean space, as in all of §6–§7.

**V7.27 (orientations pulled back, the four models of the Appendix oriented, and the orientability
of every connected one-manifold; `Milnor.orPull`, `Milnor.orSign_orPull`, `Milnor.eq_orPull`,
`Milnor.Orient.ofConst`, `Milnor.Orient.ofZero`,
`Milnor.eventually_orSign_eq_one_of_pullback`, `Milnor.Orient.comap`, `Milnor.IsOrientable.comap`,
`Milnor.IsOrientable.of_diffeomorph`, `Milnor.orientReal`, `Milnor.orientIci`, `Milnor.orientIcc`,
`Milnor.mfd_extChartAt_Icc_top`, `Milnor.isOrientable_circle`,
`Milnor.isOrientable_of_finrank_eq_one`).** Five statements, whose only purpose is the next item.
(i) *Pullback.* For an invertible continuous linear map $T : E \to F$ between spaces of dimension
$n$ and an orientation $b$ of $F$, exactly one orientation of $E$ is carried by $T$ to $b$. (ii)
*Two cheap orientations.* If all the charts of $M$ are the *same* partial homeomorphism, every
transition is the identity and a constant family of orientations is an orientation in the sense of
V5.0; and every $0$-dimensional manifold is orientable whatever its charts, because in dimension
$0$ every linear map preserves every orientation — the only tuple to test is the empty one. (iii)
*Transport along a map with invertible derivative.* Let $\Phi : M \to N$ be smooth between
manifolds of the same dimension $n$, let $N$ carry an orientation, and let every $d\Phi_x$ be
invertible. Then $x \mapsto \operatorname{orPull}(o_N(\Phi x), d\Phi_x)$ is an orientation of $M$;
$\Phi$ need be neither injective nor surjective nor a local diffeomorphism, so in particular
orientability travels backwards along a diffeomorphism. (iv) *The four models of V.J are
orientable.* The line and the closed half-line by constant families, through (ii). The unit
interval **not** by a constant family: Mathlib's manifold structure on $[0,1]$ has two charts,
$z \mapsto z$ on $[0,1)$ and $z \mapsto 1 - z$ on $(0,1]$, whose transition reverses orientation,
so the family has to flip at the right-hand endpoint, and that one transition derivative has to be
computed. And the circle not through its own charts but through the unit circle
$S^1 \subseteq \mathbb R^2$, which Chapter 8 already orients as the boundary of the disk (V8.0's
`sphOrStd`): $S^1$ is a nonempty compact Hausdorff connected boundaryless smooth one-manifold, so
V.H hands over a diffeomorphism $S^1 \to$ `Circle` and (iii) carries the orientation across. (v)
Hence **every connected Hausdorff $\sigma$-compact smooth one-manifold over a boundaryless model is
orientable**: the classification V.J makes it the circle if it is compact and $\mathbb R$ if it is
not — the two interval models are excluded because the boundary of such an $M$ is empty — and
orientability travels back along the diffeomorphism by (iii). *Hidden hypothesis:* every transport
statement, hence (iii), (iv) and (v), assumes the model of the **source** boundaryless. It is used
in exactly one way: a chart target of the source has to be open in the model space, so that the map
read in charts is defined on an open set and has a genuine derivative there, continuous in the
point. For a model with boundary the argument would have to be rerun with `fderivWithin` along the
model range, and it is not. So (v) is available for boundaryless models only, even though all four
models of (iv), the two with boundary included, are oriented; nothing in the project needs more,
the manifolds of Chapters 7 and 8 being compact slice submanifolds of a Euclidean space, whose
model is boundaryless. *Deviation (route of proof):* (iii) is V5.1's local constancy of the sign
read backwards. Writing $\Phi$ in the charts at $x_0$ and $\Phi x_0$ as $g$, the transition of $N$
at $\Phi x$ composed with $d\Phi_x$ equals $dg$ composed with the transition of $M$ at $x$; the
left side has sign $1$ by the definition of the pulled-back family and the compatibility of the
orientation of $N$, and the right side splits as the sign of $dg$ — locally constant, and $1$ at
$x_0$, where $dg = d\Phi_{x_0}$ — times the sign of the transition of $M$, which is therefore $1$.

**V7.28 (the dimension of a connected non-orientable manifold, and the removal of the hypothesis;
`Milnor.two_le_of_not_isOrientable`, `Milnor.two_le_of_not_isOrientable_slice`).** Let $M$ be a
connected Hausdorff $\sigma$-compact smooth manifold of dimension $m$ over a boundaryless model. If
$M$ is **not** orientable, then $2 \le m$. Dimension $0$ is excluded by the second clause of V7.27
and dimension $1$ by the last. The second form is the same statement in the vocabulary of
Chapters 7 and 8 — $M$ a compact connected slice submanifold of a Euclidean space, charted on
$\mathbb R^m$ — and there every side hypothesis comes free: $M$ is Hausdorff as a subspace of a
metric space, $\sigma$-compact because it is compact, and its model $\mathbb R^m$ is boundaryless.
This is the item that deletes $2 \le m$ from V7.26. The three statements there that assume
non-orientability now derive the dimension bound from it, in one line each, at the single point
where V7.22 wants it; V7.22 itself keeps the hypothesis, sharply, as a statement about punctured
balls. *Hidden hypotheses:* the ones listed, which are exactly those of V7.27(v). *Deviation:*
none from Milnor, who states his theorem of p. 50 with no dimension condition at all; this item is
what makes the formal statement match his.

## 9. Chapter 8 (Milnor §8, the seventeen problems): verified

Milnor ends the book with seventeen problems "for the reader". All seventeen are verified; the
statements below are the formal versions. Throughout, "smooth homotopic" is the notion of V4 (a
smooth map on $X \times \mathbb R$), and a compact manifold $M \subseteq \mathbb R^{K+1}$ is a compact
submanifold of Euclidean space with the manifold structure of Chapter 2, as in §6–§7. Hidden
hypotheses are flagged where they occur: $k > 0$ for linking numbers (V8.13), positive dimensions
for linking numbers in the sphere (V8.13′), $p \ge 2$ for the Hopf invariant (V8.14); the formal
intersection product carries the hypotheses $p \ge 1$ and, for the product itself, $q \ge 1$, which
serve the proof, and $p + q \le m$ (V8.17). One value stated in the book is not what its
conventions give: the Hopf invariant of the Hopf fibration is $-1$, not $1$ (V8.15). For one
natural generalization of Problem 14 a) the formal statement carries an extra hypothesis, and
the reason is explained informally (V8.14).

**V8.0 (tools built for the chapter).** Several general facts that Mathlib lacks were proved once
and used throughout. *(i) Local zero sets:* let $M$ be a manifold without boundary modelled on a
finite-dimensional space $E$. A subset of $M$ which near each of its points is the zero set of a
map to a space $F$, smooth on an open neighbourhood and with surjective derivative at the points
of the subset, is a submanifold modelled on any $Z$ with $\dim Z + \dim F = \dim E$
(`Milnor.IsSliceSubmanifold.of_locally_preimage`), and its tangent space at a point is the kernel
of the derivative of any such local defining map
(`Milnor.IsSliceSubmanifold.range_mfderiv_val_eq_ker`,
`Milnor.IsSliceSubmanifold.mem_range_mfderiv_val_iff_of_local`). *(ii) Product
orientations:* the orientation of $M \times N$ given by a positive basis of $TM$ followed by one of
$TN$, the sign of a product of maps, and the sign $(-1)^{mn}$ of the swap
(`Milnor.Orient.prod`, `Milnor.signAt_prodMap`, `Milnor.signAt_swap`).
*(iii) Frame orientations:* a submanifold of Euclidean space with a continuous complementary frame
is oriented by "frame first, then tangent vectors"; in particular the sphere $S^n$ is oriented as the
boundary of the disk, outward normal first (`Milnor.Sphere.sphOrStd`), and preimages of regular
values in spheres are oriented as in §5 (`Milnor.Problems.preimOr`; frame first differs from §5's
tangent vectors first by $(-1)^{dp}$, which is $+1$ in the case $p = d + 1$ used below). The
orientation `sphOr` of V5.9 was built from a basis chosen by the axiom of choice, and is the
boundary orientation of the exterior of the ball relative to that basis; for $n \ge 1$ it agrees
with Milnor's orientation `sphOrStd` up to a global sign (`Milnor.Sphere.sphOrStd_eq_or_neg`).
Linking numbers and the Hopf invariant use Milnor's. *(iv) Local degrees for maps with compact
preimages:* for $M$ and $N$ Hausdorff, if some neighbourhood $V$ of a regular value $y$ has compact
preimage $f^{-1}(V)$, then nearby values are regular and the local degree is constant near $y$
(`Milnor.IsRegularValue.eventually_degAt_eq_of_isCompact`); if moreover $M$ is second countable,
$F$ is a smooth homotopy, $y$ is a regular value of both end maps and
$\{(x, t) : F(x, t) \in V,\ 0 \le t \le 1\}$ is compact for some neighbourhood $V$ of $y$, the two
end maps have the same local degree at $y$ (`Milnor.degAt_eq_of_homotopy_of_isCompact`).
*(v) Genericity:* the image of a second countable manifold of smaller dimension has dense
complement, and is meagre; the complement of the diagonal in $S^p \times S^p$ is connected
($p \ge 1$); a function locally constant near every point on a dense subset of a connected set is
constant (`Milnor.Problems.dense_compl_range_of_finrank_lt`,
`Milnor.Problems.isConnected_offDiag_sph`, `Milnor.Problems.eq_of_locallyConst_on_dense`). As in
Chapters 4 and 5, the statements of (iv), and those of (v) about images, require the model spaces
of source and target to lie in a common universe (§1).

**V8.1 (Problem 1, the degree of a composition; `Milnor.Problems.deg_comp`).** Let
$f : M \to N$ and $g : N \to P$ be smooth maps between oriented boundaryless manifolds of the same
dimension $n$, with $M$ and $N$ compact (Hausdorff, second countable), $P$ Hausdorff, and $N$,
$P$ connected (and the model spaces in a common universe, §1). Then
$\deg(g \circ f) = \deg g \cdot \deg f$. *Proof as in the solutions:* a point $z$ which is a
regular value of both $g$ and $g \circ f$ exists (regular values of $g$ are open and dense, those of
$g \circ f$ dense); every $y \in g^{-1}(z)$ is then a regular value of $f$
(`isRegularValue_of_isRegularValue_comp`); the sum over $(g \circ f)^{-1}(z)$ splits over the fibres
of $f$ and the signs multiply. *Hidden hypothesis:* $N$ compact (so that $\deg g$ is defined).

**V8.2 (Problem 2, polynomials; `Milnor.Problems.riemannOr`, `Milnor.Problems.deg_polyMap`).** The
Riemann sphere carries the orientation given by the standard orientation of $\mathbb C = \mathbb R^2$
in both charts $z$ and $1/z$ (well defined: the chart change has complex derivative $w \ne 0$,
whose real determinant is $|w|^2 > 0$, `orSign_complexMul`). For a complex polynomial $P$ of degree
$n \ge 1$, the induced smooth map of the Riemann sphere has degree $n$. *Proof:* at a regular value
$y \in \mathbb C$ outside the finite set of critical values, the preimages are the $n$ distinct simple
roots of $P - y$, each with derivative multiplication by $P'(z) \ne 0$, of sign $+1$.
*Deviation:* the Riemann sphere replaces the Gauss sphere $S^2$, as in V1.6.

**V8.3 (Problem 3; `Milnor.Problems.homotopic_of_norm_sub_lt_two`,
`Milnor.Problems.smoothHomotopic_of_norm_sub_lt_two`).** If $f, g : X \to S^p$ satisfy
$\|f(x) - g(x)\| < 2$ for all $x$, then $f$ and $g$ are homotopic ($X$ any topological space,
continuous maps); if $X$ is a manifold and $f, g$ are smooth, they are smoothly homotopic. The
homotopy is the normalized chord $((1-t)f + tg)/\|(1-t)f + tg\|$.

**V8.4 (Problem 4; `Milnor.Problems.exists_contDiff_approx_of_isCompact`,
`Milnor.Problems.exists_smooth_approx`, `Milnor.Problems.smoothHomotopic_of_homotopic`).** For a
compact manifold $X \subseteq \mathbb R^{K+1}$: every continuous map $X \to S^p$ is a uniform limit of
smooth maps, and two smooth maps $X \to S^p$ which are continuously homotopic are smoothly
homotopic. The approximation theorem underneath is proved for any compact subset of a
finite-dimensional space (Stone–Weierstrass for restrictions of smooth functions).

**V8.5 (Problem 5; `Milnor.Problems.exists_smoothHomotopic_const_of_lt`,
`Milnor.Problems.exists_homotopic_const_of_lt`).** If $m < p$, every smooth map from a second
countable boundaryless $m$-manifold to $S^p$ is smoothly homotopic to a constant, and every
continuous map from a compact $m$-manifold $M \subseteq \mathbb R^{K+1}$ to $S^p$ is homotopic to a
constant. *Proof:* by Brown's theorem a smooth map misses a point $y$ (a regular value cannot be
attained when $m < p$); stereographic projection from $y$ contracts; the continuous case follows
by V8.4 and V8.3. *Formal note:* because Brown's theorem is applied with the sphere as target,
the model space of the $m$-manifold is required to lie in the lowest universe (§1).

**V8.6 (Problem 6, Brouwer for spheres; `Milnor.Problems.exists_fixedPoint_of_deg_ne`).** A smooth
map $f : S^n \to S^n$ ($n \ge 1$) with $\deg f \ne (-1)^{n+1}$ has a fixed point. *Deviation:* stated
for smooth maps, for which the degree is defined in the formalization.

**V8.7 (Problem 7; `Milnor.Problems.exists_antipodal_of_odd_deg`,
`Milnor.Problems.even_deg_of_even_map`).** A smooth map $f : S^n \to S^n$ ($n \ge 1$) of odd degree
satisfies $f(-x) = -f(x)$ for some $x$. The key lemma: a smooth map with $h(-x) = h(x)$ has even
degree (preimages of a regular value come in antipodal pairs).

**V8.8 (Problem 8, products; `Milnor.Problems.isSliceSubmanifold_prod`,
`Milnor.Problems.range_mfd_val_prod`, `Milnor.Problems.IsSliceSubmanifold.finrank_add`).** If
$M \subseteq \mathbb R^k$ and $N \subseteq \mathbb R^l$ are smooth manifolds, then
$M \times N \subseteq \mathbb R^k \times \mathbb R^l$ is a smooth manifold of dimension $m + n$, and at
every point its tangent space is $T(M \times N)_{(x,y)} = TM_x \times TN_y$. *Proof:* near $(x, y)$
the set $M \times N$ is the common zero set of the normal coordinates of slice charts of $M$ and of
$N$, a map with surjective derivative; a set which is locally the zero set of such a map is a
manifold whose tangent space is the kernel of the derivative (a general criterion proved once for
the chapter, `Milnor.IsSliceSubmanifold.of_locally_preimage`). *Formal setting:* the
ambient spaces may be any finite-dimensional real spaces.

**V8.9 (Problem 9, graphs; `Milnor.Problems.graph`, `Milnor.Problems.isSliceSubmanifold_graph`,
`Milnor.Problems.range_mfd_val_graph`).** For a smooth map $f : M \to N$, the graph
$\Gamma = \{(x, f(x))\} \subseteq \mathbb R^k \times \mathbb R^l$ is a smooth manifold of the dimension
of $M$, and its tangent space at $(x, f(x))$ is $\{(v, df_x v) : v \in TM_x\}$, the graph of $df_x$.
*Proof:* near a point, $\Gamma$ is the zero set of $(a, b) \mapsto (\text{normal coordinates of } a,\ b - \tilde f(a))$,
where $\tilde f$ is a smooth extension of $f$ to an open subset of $\mathbb R^k$; this map has
surjective derivative, and its kernel is the graph of $df_x$.

**V8.10 (Problem 10, the tangent bundle; `Milnor.Problems.tangentBundleSet`,
`Milnor.Problems.isSliceSubmanifold_tangentBundle`, `Milnor.Problems.tangentMap`,
`Milnor.Problems.contMDiff_tangentMap`, `Milnor.Problems.tangentMap_id`,
`Milnor.Problems.tangentMap_comp`).** For a smooth manifold $M \subseteq \mathbb R^k$ of dimension $m$,
the tangent bundle space $TM = \{(x, v) \in M \times \mathbb R^k : v \in TM_x\}$ is a smooth manifold of
dimension $2m$. A smooth map $f : M \to N$ induces $df : TM \to TN$, $(x, v) \mapsto (f(x), df_x(v))$,
which is smooth, with $d(\mathrm{identity}) = \mathrm{identity}$ and $d(g \circ f) = dg \circ df$.
*Proof:* near a point, $TM$ is the zero set of $(a, w) \mapsto (\text{normal coordinates of } a,\
\text{normal part of } d\varphi_a(w))$ for a slice chart $\varphi$, a map with surjective derivative;
$df$ is smooth because $f$ has a smooth local extension to an open subset of $\mathbb R^k$; the
composition rule is the chain rule. *Formal setting:* the ambient spaces may be any
finite-dimensional real spaces; the identity rule needs no smoothness hypothesis.

**V8.11 (Problem 11, the normal bundle; `Milnor.Problems.normalBundleSet`,
`Milnor.Problems.isSliceSubmanifold_normalBundle`, `Milnor.Problems.normalε`,
`Milnor.Problems.exists_diffeomorph_normalε`, `Milnor.Problems.exists_normalTube_diffeomorph`).** For
a smooth manifold $M \subseteq \mathbb R^k$ of dimension $m$, the normal bundle space
$E = \{(x, v) \in M \times \mathbb R^k : v \perp TM_x\}$ is a smooth manifold of dimension $k$. If $M$
is compact and nonempty, there is $\varepsilon > 0$ such that $(x, v) \mapsto x + v$ maps
$\{(x, v) \in E : \|v\| < \varepsilon\}$ diffeomorphically onto the $\varepsilon$-neighbourhood
$N_\varepsilon = \{y : \operatorname{dist}(y, M) < \varepsilon\}$. *Proof:* near a point, $E$ is the zero
set of $(a, v) \mapsto (\text{normal coordinates of } a,\ \text{tangential components of } v)$, a map with
surjective derivative. The sum map has invertible derivative along the zero section, it is
injective on a uniformly thin tube because $M$ is compact (finitely many balls on which it is a
local diffeomorphism), and its inverse is $y \mapsto (r(y), y - r(y))$ with $r$ the nearest-point
retraction of V6.6. *Hidden hypothesis:* $M$ nonempty. *Formal setting:* the first part is proved
for $M \subseteq \mathbb R^k$ given by slice charts with model $\mathbb R^m$ and complement
$\mathbb R^w$, $m + w = k$; the second part is stated for $\mathbb R^{K+1}$, that is for
$k \ge 1$, as in §6–§7.

**V8.12 (Problem 12, the retraction; `Milnor.Problems.normalRetraction_nearest`,
`Milnor.Problems.exists_smooth_approx_mfld`, `Milnor.Problems.smoothHomotopic_of_homotopic_mfld`).**
With $\varepsilon$ as in V8.11 and $r : N_\varepsilon \to M$ the retraction: for $(x, v) \in E$ with
$\|v\| < \varepsilon$ we have $r(x + v) = x$, and $x$ is strictly closer to $x + v$ than any other point
of $M$. The analogue of Problem 4 with $S^p$ replaced by $M$: for compact manifolds
$X \subseteq \mathbb R^{L+1}$ and $M \subseteq \mathbb R^{K+1}$, $M$ nonempty, every continuous map
$X \to M$ is a uniform limit of smooth maps, and two smooth maps $X \to M$ which are continuously
homotopic are smoothly homotopic. *Proof:* approximate by a smooth map into $\mathbb R^{K+1}$ and
compose with $r$; smooth maps $X \to M$ closer than the tubular radius of V6.6 (which is at least
$\varepsilon$; for this step $X$ need not be compact) are joined by $r((1-s)f + sg)$
(`Milnor.Problems.smoothHomotopic_of_dist_lt_mfld`); a continuous homotopy is approximated on
$X \times [0, 1]$ and retracted.

**V8.13 (Problem 13, linking numbers; `Milnor.Problems.linkMap`, `Milnor.Problems.linkingNumber`,
`Milnor.Problems.linkingNumber_symm`, `Milnor.Problems.linkingNumber_eq_zero_of_bounds`).** Let
$A^a$ and $B^b$ be compact oriented boundaryless manifolds and $\alpha : A \to \mathbb R^{k+1}$,
$\beta : B \to \mathbb R^{k+1}$ smooth maps with disjoint images, $k = a + b$. The linking map
$\lambda(x, y) = (\alpha(x) - \beta(y))/\|\alpha(x) - \beta(y)\|$ is smooth, and the linking number
$l(\alpha, \beta)$ is its degree, for the product orientation of $A \times B$ and the orientation of
$S^k$ as the boundary of the disk. (Milnor's disjoint $M, N \subseteq \mathbb R^{k+1}$ are the case
where $\alpha$ and $\beta$ are inclusions.)

- *Symmetry.* If $k > 0$, then $l(\beta, \alpha) = (-1)^{(a+1)(b+1)}\, l(\alpha, \beta)$. *Proof:*
  $\lambda_{\beta,\alpha}$ is the antipodal map composed with $\lambda_{\alpha,\beta}$ composed with the
  swap of factors; the swap has sign $(-1)^{ab}$ everywhere and the antipodal map has degree
  $(-1)^{k+1}$.
- *Bounding.* Suppose $A$ is the boundary $\{g = 0\}$ of a compact region $X = \{g \ge 0\}$ in an
  oriented $(a+1)$-manifold $W$ ($0$ a regular value of $g$, $A$ with the boundary orientation),
  and $\alpha$ extends to a smooth $\bar\alpha : W \to \mathbb R^{k+1}$ with $\bar\alpha(X)$ disjoint from
  $\beta(B)$. Then $l(\alpha, \beta) = 0$. *Proof:* the linking map extends over $X \times B$, and the
  boundary orientation of $A \times B$ inside $W \times B$ is the product orientation; a map which
  extends over a compact region has degree $0$ on its boundary (V6.1).

*Hidden hypotheses:* $k > 0$ (for $k = 0$ the target $S^0$ is not connected and the degree is not
defined); $A$ and $B$ Hausdorff and second countable for the symmetry, and $B$ and $W$ Hausdorff
and second countable for the bounding statement. *Formal setting:* "$M$ bounds an oriented
manifold $X$ disjoint from $N$" is taken in the ambient form above, as manifolds with boundary are
throughout.

**V8.13′ (Problem 13, linking numbers in the sphere; `Milnor.Problems.linkingNumberSph`,
`Milnor.Problems.exists_admissible_rotation`, `Milnor.Problems.linkingNumberSph_eq`).** For smooth
maps $\alpha : A \to S^{k+1}$ and $\beta : B \to S^{k+1}$ with disjoint images, $k = a + b$: choose a
rotation $R$ of $\mathbb R^{k+2}$ (a linear isometry of positive determinant) such that the north pole
avoids $R\alpha(A) \cup R\beta(B)$, project stereographically from the north pole to $\mathbb R^{k+1}$,
and take the linking number of V8.13. Such rotations exist when $A$ and $B$ are second countable
(`exists_admissible_rotation`: the images are meagre; the formal statement also assumes
$a, b \ge 1$, which its proof does not use). If $a, b \ge 1$ and $A$, $B$ are Hausdorff and second
countable, the result does not depend on the choice (`linkingNumberSph_eq`). *Proof:* a rotation
fixing the north pole acts on $\mathbb R^{k+1}$ by a linear map of positive determinant, which does
not change linking numbers; a smooth family of rotations that keeps the north pole off both images
does not change it either (homotopy invariance of the degree);
two admissible rotations are joined by such families along two great-circle arcs through a common
point, chosen outside the "bad midpoints", which form a meagre set (images of manifolds of
dimensions $a + 1$ and $b + 1$, both less than $k + 1$; Brown's theorem and Baire's theorem).
*Hidden hypothesis:* $a, b \ge 1$ for the independence. *Remark (informal, not a formal result):*
the hypothesis cannot simply be dropped; for a point and a great sphere ($a = 0$) the answer
depends on the side of the sphere on which the projection point lies. This example is not
formalized.

**V8.14 (Problem 14, the Hopf invariant; `Milnor.Problems.linkPre`,
`Milnor.Problems.linkPre_self_eventually_eq`, `Milnor.Problems.linkPre_eq_of_norm_lt`,
`Milnor.Problems.hopfInvariant`, `Milnor.Problems.linkPre_eq_hopfInvariant`,
`Milnor.Problems.hopfInvariant_eq_of_smoothHomotopic`).** Let $p \ge 2$ and let
$f, g : S^{2p-1} \to S^p$ be smooth. For a regular value $y$ of $g$ and a regular value $z$ of $f$
with disjoint preimages, $l(g^{-1}(y), f^{-1}(z))$ denotes the linking number in the sphere
(V8.13′) of the preimages, oriented as in §5.

- *a)* For $y \ne z$ regular values of $f$, $l(f^{-1}(y), f^{-1}(z))$ is locally constant in $y$ (and
  in $z$).
- *b)* If $y \ne z$ are regular values of $f$ and of $g$ and $\|f(x) - g(x)\| < \|y - z\|$ for all $x$,
  then $l(f^{-1}(y), f^{-1}(z)) = l(g^{-1}(y), f^{-1}(z)) = l(g^{-1}(y), g^{-1}(z))$.
- *c)* $l(f^{-1}(y), f^{-1}(z))$ does not depend on the choice of regular values $y \ne z$; this
  integer is the Hopf invariant $H(f)$; smoothly homotopic maps have the same Hopf invariant.

*Proof.* The engine is a description of the linking number as a local degree
(`Milnor.Problems.degAt_phiR_eq_linkingNumberRot`): after a rotation $R$ that keeps the north pole
off both preimages, $l(g^{-1}(y), f^{-1}(z))$ is the local degree at $((y, z), e)$ of
$\Phi(x, x') = ((g(x), f(x')), \lambda(x, x'))$ on the open set of pairs of distinct points of
$S^{2p-1}$ away from $R^{-1}(\text{north})$, where $\lambda$ is the direction between the stereographic
images and $e$ is a regular value of the linking map. (At a preimage point the sign of $\Phi$ is the
sign of the linking map; the comparison is a block determinant in which the sign $(-1)^{(p-1)p} = 1$
appears.) Local degrees do not change under homotopies whose preimages stay in a compact part of
the domain, so the linking number does not change under homotopies of $g$ and $f$ during which the
preimages of $y$ and $z$ stay disjoint and away from $R^{-1}(\text{north})$, with $y$ and $z$ regular
only at the two ends (`Milnor.Problems.linkingNumberRot_eq_of_homotopy`). Moving $y$ along a short
arc by rotations of the target is such a homotopy (a); so is the normalized chord from $f$ to $g$,
because a chord point is no farther from $f(x)$ than $g(x)$ is (b); so is a smooth homotopy from $f$
to $g$ once $y$ and $z$ are chosen off the curve traced by one base point (c). The independence
of $(y, z)$ is not derived from a) but proved directly (`Milnor.Problems.linkPre_eq_linkPre_of_ne`):
the pairs of distinct points of $S^p$ form a connected set in which pairs of regular values are
dense, and near any pair $(y_0, z_0)$ two pairs of regular values are joined by moving both values
at once along short rotation arcs (`Milnor.Problems.linkPre_move`) that avoid $f(q)$, for a base
point $q$ with $f(q) \notin \{y_0, z_0\}$; for a constant map all these linking numbers vanish.

*Remark on a natural generalization (informal, not a formal result).* For two different maps one
should not expect $l(g^{-1}(y), f^{-1}(z))$ to be locally constant in $y$ under the sole assumption
$y \ne z$: moving $y$ can push $g^{-1}(y)$ through $f^{-1}(z)$, and the linking number can then
jump. No counterexample is formalized; the formal mixed statement
(`Milnor.Problems.linkPre_eventually_eq`) simply assumes the preimages disjoint. Milnor's
statement, with a single map $f$, needs nothing more than $y \ne z$.
*Hidden hypothesis:* $p \ge 2$ (for $p = 1$ the preimages are finite sets in $S^1$ and V8.13′ does
not apply). *Deviation:* smooth maps and smooth homotopies (V4 convention).

**V8.15 (Problem 15; `Milnor.Problems.hopfInvariant_eq_zero_of_odd`,
`Milnor.Problems.hopfInvariant_comp`, `Milnor.Problems.hopfMap`, `Milnor.Problems.hopfMap_eq_milnor`,
`Milnor.Problems.isRegularValue_hopfMap`, `Milnor.Problems.linkingNumberRot_hopfMap`,
`Milnor.Problems.hopfInvariant_hopfMap`).** Let $p \ge 2$.

- If $p$ is odd, $H(f) = 0$ for every smooth $f : S^{2p-1} \to S^p$.
- For smooth $f : S^{2p-1} \to S^p$ and $g : S^p \to S^p$, $H(g \circ f) = (\deg g)^2 H(f)$.
- *The Hopf fibration.* With $z_1 = x_1 + i x_2$ and $z_2 = x_3 + i x_4$, the map
  $\pi(z_1, z_2) = (2 z_1 \bar z_2,\ |z_1|^2 - |z_2|^2)$ is a smooth map $S^3 \to S^2$; it equals
  $h^{-1}(z_1/z_2)$ wherever $z_2 \ne 0$ ($h$ the stereographic projection from $(0,0,1)$) and
  $(0,0,1)$ where $z_2 = 0$; every point of $S^2$ is a regular value; and $H(\pi) = -1$.

*Proof.* Odd $p$: $l(N, M) = (-1)^{p^2} l(M, N) = -l(M, N)$ by V8.13, and both are $H(f)$ by V8.14.
Composition: choose regular values $y \ne z$ of $g$ and of $g \circ f$ and one admissible rotation;
the map $\Phi$ of $g \circ f$ is $(g \times g \times \mathrm{id})$ composed with the $\Phi$ of $f$; the local
degree of a composition is the sum over the fibre of the sign of the outer map times the local
degree of the inner one; here the signs are $\operatorname{sign}_g(y_i)\operatorname{sign}_g(z_j)$ and the
local degrees are $l(f^{-1}(y_i), f^{-1}(z_j)) = H(f)$, so the double sum is
$\deg g \cdot \deg g \cdot H(f)$. The Hopf fibration: the fibres over $y = (1,0,0)$ and
$z = (-1,0,0)$ are the great circles $z_1 = z_2$ and $z_1 = -z_2$. After stereographic projection
from $(0,0,0,1)$, exactly one pair of points, $a = (0,-1,0,-1)/\sqrt2$ on the first fibre and
$a' = (0,1,0,-1)/\sqrt2$ on the second, has direction $e = (0,-1,0)$. Lifting positive bases of
$T_yS^2$ and $T_zS^2$ to $u_1 = (1,0,-1,0)$, $u_2 = (0,-1,0,1)$ at $a$ and $w_1 = (0,1,0,1)$,
$w_2 = (1,0,1,0)$ at $a'$, the fibre directions $t = (1,0,1,0)/\sqrt2$ and $t' = (-1,0,1,0)/\sqrt2$
are both negatively oriented as preimages, since $\det(a, u_1, u_2, t) = \det(a', w_1, w_2, t') = -2$;
the derivative of the direction map sends $t$ and $t'$ to $\tfrac12(1,0,1)$ and $\tfrac12(1,0,-1)$, a
negatively oriented basis at $e$. The linking number is the product of the three signs, $-1$.

**A finding: the sign of $H(\pi)$.** Milnor states $H(\pi) = 1$. With his conventions taken
literally (spheres oriented as boundaries of disks, preimages oriented as in §5, $A \times B$
oriented as a product, $\lambda(x, y) = (x - y)/\|x - y\|$), the value is $-1$. This value was
checked by hand, numerically, and in Lean (`hopfInvariant_hopfMap`). The comparison with other
conventions that follows is an informal consequence of the formal sign lemmas (the degree of the
antipodal map, the sign of the swap, the symmetry of linking numbers, the composition formula
above); it is not itself a formal theorem. The sign flips under any one of three equally natural
changes: $\lambda(x, y) = (y - x)/\|y - x\|$, which composes $\lambda$ with the antipodal map of
$S^2$; ordering the product as $B \times A$, whose swap has sign $(-1)^{(p-1)^2} = -1$ for
$p = 2$; or orienting the target sphere $S^2$ of the linking map $\lambda$ the other way. Changing
the orientation of $S^3$, or of the target $S^2$ of $\pi$, reverses the orientations of both
preimages at once and leaves $H$ unchanged. Putting the lifts before the tangent vectors in the
preimage orientation changes nothing at all here, since the two orders differ by
$(-1)^{dp} = +1$ for $d = 1$, $p = 2$ (V8.0 (iii)). So the book's value corresponds to one of the
three changes above; the formal statement keeps the book's own conventions and records $-1$.

**V8.16 (Problem 16, transversality; `Milnor.Problems.Transverse`,
`Milnor.Problems.inter_eq_empty_of_transverse`, `Milnor.Problems.isSliceSubmanifold_inter`,
`Milnor.Problems.tangentN_inter`, `Milnor.Problems.exists_transverse_deformation`).** Submanifolds
$N^n, N'^{n'}$ of $M^m$ intersect transversally if $TN_x + TN'_x = TM_x$ at every common point. If
$n + n' < m$, transverse submanifolds are disjoint. The intersection of transverse submanifolds of
codimensions $p$ and $p'$, with $p + p' \le m$, is a submanifold of codimension $p + p'$, with
tangent space $TN_x \cap TN'_x$. A framed submanifold $N$ can be deformed slightly so as to meet a
given $N'$ transversally: if $G : N \times B_\varepsilon \to M$ is a product neighbourhood (the
Product Neighborhood Theorem, V7.7), then for arbitrarily small $u \in \mathbb R^p$ the translate
$N_u = G(N \times \{u\})$ is a submanifold, carried injectively onto by $x \mapsto G(x, u)$, lying
within any prescribed $\delta$ of $N$, and transverse to $N'$. *Proof:* with $\pi$ the second coordinate of the product
neighbourhood, $N_u = \pi^{-1}(u)$, and $N_u$ meets $N'$ transversally exactly when $u$ is a regular
value of $\pi$ restricted to $N'$ inside the neighbourhood; by Sard's theorem such $u$ exist
arbitrarily close to $0$. The intersection is locally the common zero set of defining maps of $N$
and $N'$, whose joint derivative is surjective by transversality. *Setting:* $M$ is a submanifold
of Euclidean space, as in §7; the statements about intersections need no compactness of $M$, and
the deformation, which uses the product neighbourhood, needs $M$ compact and nonempty.

**V8.17 (Problem 17, the intersection product; `Milnor.Problems.FramedClass`,
`Milnor.Framed.FramedSub.inter`, `Milnor.Problems.exists_transverse_rep`,
`Milnor.Problems.exists_intersection_product`, `Milnor.Problems.intersection_product_unique`).**
$\Pi^p(M)$ is the set of framed cobordism classes of framed submanifolds of codimension $p$ of the
compact nonempty manifold $M \subseteq \mathbb R^{K+1}$ (formally the set is indexed by the
dimension $n$ and the codimension $p$ of the submanifolds, and is empty unless $n + p = m$). If
framed submanifolds $F$ (codimension $p$, framing $v$) and $G$ (codimension $q$, framing $v'$)
intersect transversally and $p + q \le m$, their intersection is framed as follows: at $x$, let
$\alpha_F(x) : \mathbb R^{K+1} \to \mathbb R^p$ be the linear map with $\alpha_F(v_i) = e_i$
vanishing on the vectors orthogonal to all $v_i$, similarly $\alpha_G$, and $A = (\alpha_F,
\alpha_G)$, which is surjective at the points of the intersection by transversality; the framing
vectors of the intersection are $w_k = A^*(AA^*)^{-1} e_k$, so that $(\alpha_F w_k, \alpha_G w_k)$
is the $k$-th standard basis vector of $\mathbb R^p \times \mathbb R^q$. (Informally, $w_k$ is the
unique vector in the span of $v$ and $v'$ with these values; this description is not part of the
formal statement.) For $p \ge 1$, every pair of classes has transverse representatives; for
$p, q \ge 1$ and $p + q \le m$ there is a map $\Pi^p(M) \times \Pi^q(M) \to \Pi^{p+q}(M)$ sending
the classes of transverse $F, G$ to the class of the framed intersection, and for $p \ge 1$ it is
unique. *Proof:* let $f, g$ be maps with Pontryagin manifolds $F, G$ at the north pole (Theorem C
of §7, V7.9) and $\mu : S^p \times S^q \to S^{p+q}$ a smooth map with
$\mu^{-1}(\text{north}) = \{(\text{north},\text{north})\}$ and invertible derivative there. The
Pontryagin manifold of $\mu \circ (f, g)$ at the north pole is exactly the framed intersection, up to a positive rescaling of the framing (Lemma 1). Framed
cobordisms of $F$ and of $G$ give homotopies of $f$ and $g$ (second half of Theorem B, V7.11),
hence of $\mu \circ (f, g)$, hence a framed cobordism of the intersections (first half of
Theorem B, V7.6). Transverse representatives: replace $F$ by the Pontryagin manifold of $f$ at a
common regular value of $f$ and of $f$ restricted to $G$ (Brown's theorem; Theorem A of §7, V7.5,
and Lemma 1). *Formal hypotheses:* $p \ge 1$, and $q \ge 1$ for the existence of the product; they
come from the use of V7.5, V7.6 and V7.11, whose proofs rotate regular values, and are not claimed
to be necessary.

**V8.17′ (Problem 17, the group; `Milnor.Problems.exists_disjoint_rep`,
`Milnor.Problems.framedCobordant_union_of_framedCobordant`, `Milnor.Problems.cohomotopyAdd_mk`,
`Milnor.Problems.cohomotopyAdd_negFirst`, `Milnor.Problems.cohomotopyGroup`,
`Milnor.Problems.cohomotopyGroup_add`, `Milnor.Problems.cohomotopyGroup_zero`,
`Milnor.Problems.cohomotopyGroup_neg`).** Let $p \ge \tfrac12 m + 1$, i.e. $m + 2 \le 2p$. Then
any two classes in $\Pi^p(M)$ have disjoint representatives; if $F \sim F_1$ and $G \sim G_1$ with
$F, G$ disjoint and $F_1, G_1$ disjoint, then $F \sqcup G \sim F_1 \sqcup G_1$; and the disjoint union
makes $\Pi^p(M)$ an abelian group, with zero the class of the empty manifold and $-[F]$ the class
of $F$ with its first framing vector reversed. *Proof:* the dimension condition gives
$2n + 2 \le m$, so an $n$-manifold, and even an $(n+1)$-manifold swept out by a cobordism, has
image of empty interior in $S^p$; this lets one choose regular values (Brown's theorem) whose
Pontryagin manifolds avoid a given disjoint piece, and move one component at a time, keeping every
cobordism away from the other component: by rotation arcs (as in the proof of Theorem A of §7,
V7.5), by the cobordism $H^{-1}(z)$ of a homotopy $H$ between the two maps (the second half of
Theorem B, V7.11, gives $H$; V7.2 the cobordism), and by Lemma 1. Commutativity, associativity
and the zero are identities of framed submanifolds. For the inverse, the
cancellation homotopy of §7 (the family $s_1^2 - a^2\rho(t)$), transported into a product
neighbourhood of $F$, is a cobordism from two parallel copies of $F$, one with the first framing
vector reversed, to the empty manifold; translating each copy back to $F$ identifies the two
classes. *Formal note:* the group is stated on the set of classes $\Pi^p(M)$ with the addition,
zero and negation above; $n + p = m$ is needed for the empty manifold to be a framed submanifold.
The formal group structure also takes $p \ge 1$ as a hypothesis, which is redundant, since
$m + 2 \le 2p$ implies it.

**Size.** 16,166 lines in 31 files. Tools of V8.0: 1,763 (local zero sets 196, local degrees with
compact preimages 449, product orientations 403, frame orientations 452, genericity 263). Problems:
1: 117; 2: 203; 3: 116; 4–5: 392; 6–7: 143; 8–9: 445; 10: 412; 11: 578; 12: 371; 13: 1,452 (linking
numbers 579, definitions in the sphere 166, independence of the rotation 707); 14: 3,126 (preimage
orientations 641, the block determinants 508, linking numbers as local degrees 707, the invariant
1,270); 15: 2,266 (the explicit fibration 752, its sign 868, the composition formula 433, assembly
213); 16: 633; 17: 4,149 (framed classes and unions 675, the product 1,503, the group 1,971). The
estimate given before the chapter was about 1,500 lines for Problems 1–7 and 12 (actual 1,342) and
8,000–12,000 for Problems 13–17 (actual 11,626).

---

## 10. The Appendix (Milnor pp. 54–56): verified — the classification of one-manifolds, and the boundary count in a stronger form

Milnor's Appendix proves one theorem, that every smooth connected one-manifold is diffeomorphic to
the circle or to an interval, and draws from it the one corollary the book uses, that a compact
one-manifold with boundary has an even number of boundary points. This section has two halves,
written in that order historically and set out in that order here. The first (V.A, V.A′) is the
corollary alone, proved for a merely *topological* one-manifold with boundary, which is stronger
than the book in the hypothesis and weaker in the conclusion. The second (V.B–V.J) is Milnor's
theorem itself, in nine stages, and it ends by proving the corollary a second time, as he does,
*from* the classification: the classification also fixes the diffeomorphism type of every component,
identifies which components have boundary, and pairs the boundary points off explicitly. The old
proof is left in place untouched, because Chapters 2 and 4 cite it; the new one is not used by
anything in the book, and is here because the book states it.

**The first half: the boundary count for a topological one-manifold.**

**V.A (`Milnor.OneManifold.even_ncard_boundary`).** Let $M$ be a compact Hausdorff topological
space with a charted-space structure modelled on a space $H$ homeomorphic to the half-line
$[0,\infty)$, and let $B \subseteq M$ be a set such that every chart of the atlas sends exactly the
points of $B$ in its domain to coordinate $0$. Then $B$ is finite and has an even number of
points.

**V.A′ (`Milnor.IsHalfSliceSubmanifold.even_ncard_boundary`).** In the language of Chapter 2: let
$M$ be a Hausdorff smooth manifold (over any model with corners; its model space need not be
finite-dimensional). If $X \subseteq M$ is a compact half-slice submanifold with boundary
$B \subseteq X$, modelled on the half-space over a zero-dimensional $Z$ (that is, a compact
1-manifold with boundary), then $B$ is finite with an even number of points.

**What is stronger than the book.** Milnor proves the classification of smooth 1-manifolds and
deduces the boundary count. The formal theorem assumes only a *topological* 1-manifold with
boundary: charts are homeomorphisms, no smooth structure, no arc length. This is strictly more
general and is what the book actually uses (nothing downstream needs the diffeomorphism type).

**What is weaker than the book.** These two theorems do not state the classification. What is proved
on the way is that a component containing a boundary point is homeomorphic to a closed interval
(`exists_closed_arc`: an arc from a boundary point extends until its coordinate interval is closed,
and then its domain is the whole component). The circle case never arises, because the
parametrization is always started at a boundary point, and for the boundary count a component
without boundary points contributes zero whatever it is. The classification itself, "every compact
connected 1-manifold is $S^1$ or $[0,1]$", is V.J below, and V.J also draws the boundary count from
it; but that is a statement about *smooth* one-manifolds, so it neither subsumes V.A nor is
subsumed by it.

**How the formal proof differs from Milnor's, and why.** Three changes, each made to remove
infrastructure the proof would otherwise need. (1) Arc-length parametrizations are replaced by
*arcs*: homeomorphisms from open subsets onto intervals of $\mathbb R$ under which the boundary
corresponds to the endpoints (`Milnor.OneManifold.Arc`). Milnor's "the derivative of $g^{-1}
\circ f$ is $\pm 1$" becomes "a continuous injective map of an interval is strictly monotone",
which is in Mathlib. (2) Milnor's Lemma (the overlap of two parametrizations has at most two
components, and two components force a circle) is replaced by: the overlap of an arc *from a
boundary point* with any arc is a single interval (`overlap_ordConnected`). The proof is the
book's four-edges count, in the form "each end of a component of the overlap tends to an
unattained endpoint of the other arc's interval, and two components cannot share one"
(`end_lemma`, `clash_upper`, `clash_lower`), with the boundary point ruling out the extra
components. (3) The maximal parametrization is obtained not by Zorn's lemma but by a finite
induction: a finite cover by chart arcs exists by compactness, and each extension step
(`exists_extension`) absorbs at least one more chart. The parity of the count is then read off
from a fixed-point-free involution on the boundary, "the other end of my component"
(`exists_partner`, `even_ncard_of_involution`).

**Hidden hypotheses made explicit.** That every chart, not only the chart at the point, sends the
boundary to $0$ (the `BoundaryCompatible` hypothesis; for the manifolds built in Chapter 2 this
holds by construction; the proof applies it only to the preferred chart at each point, so it
could be weakened accordingly; and for a *smooth* one-manifold with a half-line model it is not a
hypothesis at all but a theorem, V.C, so V.A applies to smooth one-manifolds with no side condition
whatever). Hausdorffness of $M$, used in the end lemma, to identify two
limits, and again to see that the domain of an arc whose coordinate interval is closed, being
compact, is closed in $M$, hence (being also open) the whole component
(`IsFrom.source_eq_of_mem`). Compactness of $M$, used three times: to see that the boundary is
finite (it is closed, hence compact, and each boundary point has an arc neighbourhood containing
no other boundary point, `finite_boundary`); for the finite cover by chart arcs; and to show that
an arc whose coordinate interval is half-open, $[0, c)$, does not yet exhaust the component of its
initial point (a component is closed, hence compact, and its image in the coordinate would then
contain its supremum).

**Size.** 1,778 lines for the two theorems above: 1,704 for the topological theorem, 74 for the
specialization. The
extension step alone (`exists_extension_aux`, the gluing of two arcs with continuity checked at
the seam) is 380 lines; it is the honest content of Milnor's sentence "$f$ and $g \circ L$ piece
together to yield the required extension".

**The second half: the classification of smooth one-manifolds.**

Throughout this half, $M$ is a smooth manifold charted on a model with corners $I$ over a real
normed space $E$ which is **one-dimensional**, $\operatorname{finrank}_{\mathbb R} E = 1$, and
"boundary" means Mathlib's boundary of $M$ relative to $I$ — which V.C shows is the set of points
whose coordinate in *any* chart lies on the frontier of the model's range, so that it is the
boundary in the naive sense and needs no compatibility hypothesis. The model itself is **not**
assumed boundaryless: V.C classifies its range into three shapes, the line, a closed half-line and
a nondegenerate compact interval, and all three stay alive throughout, the third making $M$ a
one-manifold *with corners*. Smooth means $C^\infty$ except where $C^1$ is noted. The nine items follow the nine stages of the
development, in the order in which they are used rather than in the order they were written; the
Lean names all live in the namespace `Milnor.OneManifold.Smooth` unless another is given, and the
files are `Milnor/Appendix/TwoComponents.lean` and `Milnor/Appendix/Smooth/`.

**V.B (Milnor's Appendix Lemma 1, the topological half; `Milnor.OneManifold.IsInnerHull`,
`Milnor.OneManifold.image_trans_hull_eq_of_isInnerHull`,
`Milnor.OneManifold.hull_eq_of_isInnerHull`,
`Milnor.OneManifold.ordConnected_overlap_of_isInnerHull`,
`Milnor.OneManifold.sInf_eq_or_sSup_eq_of_not_isInnerHull`,
`Milnor.OneManifold.encard_hulls_le_two`,
`Milnor.OneManifold.sInf_eq_and_sSup_eq_of_hull_ne`).** Let $A$ and $A'$ be arcs of a Hausdorff
space $M$ relative to a set $B$, in the sense of V.A's `Arc` — homeomorphisms of open subsets of $M$
onto bounded nontrivial intervals of $\mathbb R$ under which $B$ corresponds to the endpoints — and
let $S$ be the set of $A$-coordinates of the points lying in both sources. Its *components* are its
hulls, the maximal intervals it contains, which V.A's file already shows to cover $S$, to be
pairwise equal or disjoint and to be relatively open in $A$'s interval. Verified: (i) if both ends
of one component are interior to $A$'s interval — an *inner* component — then the transition carries
it onto the whole of $A'$'s interval, and it is the *only* component, so $S$ is a single interval;
(ii) any other component reaches an end of $A$'s interval; (iii) hence there are **at most two**
components, the two ends not being available twice; and (iv) two distinct components reach
*opposite* ends of $A$'s interval. This is the general form of Milnor's Appendix Lemma 1 with its
affine clause removed, and it is his picture: the two-component case, which V.A excludes by fiat by
always starting an arc at a boundary point, is here *counted*, and it is the circle. *Deviation
(route of proof):* the idea V.A's file lacks is to single out the inner component. It runs off both
ends of $A'$'s interval at once, so its transition image is all of that interval and injectivity
leaves no room for a second component; the two "clash" lemmas of V.A are therefore not needed here,
and V.A's normalization — an arc starting at a boundary point — turns out to have been doing nothing
essential. *Byproducts:* an inner component occurs exactly when $A'$ sits inside $A$ (then $A'$'s
interval is open and $A'.\mathrm{source} \subseteq A.\mathrm{source}$), and an inner component
forces $A'$ to contain no point of $B$ at all. *Hypotheses:* $M$ Hausdorff, which V.A's end lemma
already needs for uniqueness of limits, and the two arcs' own data. No charts, no smoothness, no
compactness, no dimension, no `BoundaryCompatible`.

**V.C (the one-dimensional model, the real coordinate of a chart, and `BoundaryCompatible`
discharged; `closed_convex_cases`, `modelCoord`, `modelRange_cases`, `uniqueDiffOn_modelRange`,
`chartCoord`, `mem_boundary_iff_chartCoord_mem_frontier`, `boundaryCompatible`,
`exists_boundaryModel`, `exists_interiorModel`).** Verified, for $M$ as above and $C^1$ at least.
(i) *The three shapes.* A closed convex subset of $\mathbb R$ with nonempty interior is the line, a
closed half-line either way, or a nondegenerate compact interval; and there is a linear
identification $E \cong \mathbb R$, normalised so that the model range $\operatorname{range} I$ is
the line, a half-line $[a, \infty)$, or a nondegenerate $[a, b]$ — never $(-\infty, a]$. The third
shape is a one-manifold *with corners*, and it is admitted throughout: no statement of this half
excludes it. (ii) *Derivatives along the range are unique*, so `derivWithin` is unambiguous even at
an endpoint of it. (iii) *The real coordinate* `chartCoord` of an arbitrary chart, whose image is
an open set cut by the model range. (iv) *The boundary is chart-independent:* a point in the source
of **any** chart of the atlas is a boundary point exactly when its real coordinate lies on the
frontier of the model range — Mathlib's $C^1$ theorem, transported to the coordinate. (v) Hence
**V.A's `BoundaryCompatible` hypothesis is a theorem**, with no extra hypothesis at all, for a
smooth one-manifold whose model range is a half-line and with the boundary taken to be Mathlib's;
this is the "cheap spin-off" the design predicted, and it is what makes V.A apply to smooth
one-manifolds unconditionally. (vi) *The two normalised local models:* every boundary point has a
chart-derived partial homeomorphism onto $[0, \varepsilon)$ sending it to $0$, smooth both ways, and
every interior point one onto $(-\varepsilon, \varepsilon)$.
*Hypotheses:* $\operatorname{finrank}_{\mathbb R} E = 1$ and $C^1$; **not** Hausdorff, **not**
compact, **not** boundaryless. *Deviations
(all restrictions of shape, and flagged in the Lean docstrings):* only (v) and the half-line
identification are restricted to the half-line shape — V.A's datum, a homeomorphism of $H$ with
$[0,\infty)$, simply does not exist for a compact-interval model range. *Three things the design
warned of, all handled:* the compact-interval case stays live; charts at interior points are shrunk
away from the model's own endpoints before $\varepsilon$ is chosen; and the sign of the
identification with $\mathbb R$ is normalised twice, globally and again at an endpoint, the local
sign mattering because it is what keeps the far endpoint out of a normalised chart.

**V.D (smooth arcs; `SmoothArc`, `uniqueDiffOn_target`, `transSource`, `SmoothArc.contDiffOn_trans`,
`SmoothArc.derivWithin_trans_mul_derivWithin_trans`, `SmoothArc.derivWithin_trans_ne_zero`,
`SmoothArc.derivWithin_ne_zero`, `exists_smoothArc_of_mem_boundary`,
`exists_smoothArc_of_notMem_boundary`).** A *smooth arc* is an arc of V.A whose coordinate is $C^n$
on its source as a map of manifolds into $\mathbb R$ and whose parametrization is $C^n$ on its
interval as a map from $\mathbb R$ into $M$ — so the whole `Arc` API of V.A is inherited. Verified:
the interval of any arc is convex with nonempty interior, so `derivWithin` is unambiguous at its
endpoints; the transition between two smooth arcs is $C^n$ on the relatively open piece of the
interval where it is defined, and that piece is V.A's `overlap`; the two transition derivatives
multiply to $1$, so **neither vanishes**; **a smooth arc is an immersion**, its parametrization
having nowhere-vanishing derivative read in any chart of the maximal atlas, endpoints included; and
**smooth arcs exist around every point**, with interval $[0, \varepsilon)$ at a boundary point and
$(-\varepsilon, \varepsilon)$ elsewhere, built from V.C's two local models. *Hypotheses:* the
structure itself and the transition statements assume nothing of the dimension; the chart and
immersion statements and the two existence theorems need $\operatorname{finrank}_{\mathbb R} E = 1$
and $C^1$; only the identification with `overlap` needs $M$ Hausdorff, and only in order to be able
to mention it. All three shapes of V.C stay alive. *Deviation (what was expected to be hard and was
not):* the design flagged one-sided ($C^\infty$ on a half-open interval, Whitney style) smoothness
as the technical heart of the stage, and it cost nothing — Mathlib's `ContMDiffOn` is already
relative to the given set, so at an endpoint it *is* the one-sided condition. The one real wrinkle
was that a transition is defined only on a relatively open piece of the interval, so a derivative is
computed there and then transported to the whole of it.

**V.E (the length element, and unit-speed arcs; `RealChart`, `transDeriv`, `transDeriv_comp`,
`transDeriv_ne_zero`, `contDiffOn_transDeriv`, `LengthElement`, `nonempty_lengthElement`,
`continuousOn_leftInvOn_of_isCompact`, `hasDerivWithinAt_of_leftInvOn`, `arcParam`, `arcParamInv`,
`contDiffOn_arcParam`, `UnitSpeed`, `exists_reparam`, `exists_unitSpeed`).** Milnor reparametrizes
by arc length, which presupposes a Riemannian metric; his manifolds sit in $\mathbb R^k$ and he uses
the Euclidean one without comment. In dimension one a Riemannian metric is a **length element**: a
positive smooth density transforming by the absolute value of the derivative of a transition. That
is the one piece of general theory the classification needs and Mathlib does not have, and it is
built here. Verified: (i) a density is indexed not by charts but by *local real parameters* — a
`RealChart`, a partial homeomorphism of an open subset of $M$ onto a subset of $\mathbb R$ with
unique derivatives, $C^n$ both ways — of which both a chart read in V.C's coordinate and a smooth
arc of V.D are instances, which is what lets a length element be evaluated along an arc with no
intermediate layer; (ii) the transition derivatives of real charts form a **cocycle** and therefore
never vanish, and a transition derivative is itself $C^m$ where the charts are $C^{m+1}$ — the chain
rule on a possibly half-open set, which is the engine of the whole stage; (iii) **a $C^\infty$
one-manifold which is Hausdorff and $\sigma$-compact carries a $C^\infty$ length element**, namely
$\rho_c(u) = \sum_i \lambda_i(c^{-1}u)\,|\tau'_{c \to \kappa_i}(u)|$ for a smooth partition of unity
$\lambda$ subordinate to the chart sources and $\kappa_i$ the real coordinate of the chart at $i$;
(iv) the **one-sided inverse function rule** — if $g$ inverts $f$ on $t$, is continuous there, and
$f$ has nonzero derivative *within* $s$ at $g v$, then $g$ has derivative $1/f'$ within $t$ at $v$,
both derivatives allowed to be one-sided; (v) arc length $\sigma(v) = \int_c^v \rho$ on a compact
interval is $C^\infty$, strictly increasing, and has a $C^\infty$ inverse with derivative $1/\rho$,
at the endpoints included; and (vi) **Milnor's Lemma 1.1** — his "by a straightforward change of
variables" — that **every point lies on a unit-speed arc** sending it to $0$, with interval
$[0, \varepsilon)$ at a boundary point and $(-\varepsilon, \varepsilon)$ elsewhere, where
*unit-speed* means the length element read in the arc's own parameter is identically $1$. *Hidden
hypotheses:* existence of the length element, (iii), needs exactly four things —
$\operatorname{finrank}_{\mathbb R} E = 1$, $C^\infty$ (Mathlib's partitions of unity are built from
smooth bumps, and a transition derivative loses a degree, so a $C^n$ manifold would give only a
$C^{n-1}$ element), $M$ Hausdorff and $M$ $\sigma$-compact, these last two being the hypotheses of
Mathlib's subordinate partition of unity. **Those two are used nowhere else in this stage or the
next**, and $\sigma$-compactness is used nowhere else in the whole classification: see V.I. No
boundarylessness, and all three shapes of V.C stay alive. *Deviations (two soft spots of the design,
both met head-on rather than dodged):* the full $\sigma$-compact generality of (iii) was achieved,
so the fallback to a finite cover was not needed; and the one-sided smooth inverse was *proved*, not
avoided — Mathlib has only the two-sided rule, which says nothing at an endpoint, so (iv) is proved
from the elementary identity relating the two slopes, and smoothness of the inverse then follows by
bootstrapping on the order. Two devices made the endpoints painless: all the analysis is done on a
compact interval inside the arc's interval, where Mathlib's fundamental theorem of calculus holds at
the endpoints and compactness gives continuity of the inverse for free, and only at the end is the
arc restricted to a relatively open window; and the window is chosen in the *new* parameter, since
arc length need not be symmetric about the base point.

**V.F (Milnor's Appendix Lemma 1 in full, and the extension theorem; `abs_transDeriv_eq_one`,
`exists_sign_transDeriv`, `exists_affine_trans`, `milnor_appendix_lemma_one`,
`exists_extension_aux_unitSpeed`, `exists_extension_unitSpeed`).** Verified. (i) *The affine half of
Lemma 1.* For two unit-speed arcs the derivative of the transition, taken within the possibly
half-open interval, has absolute value $1$ at every parameter of the overlap, endpoints included —
one line from the cocycle rule, the density being $1$ in a unit-speed parameter; being continuous
and omitting $0$ it is *constantly* $+1$ or constantly $-1$ on each component of the overlap; and so
the transition is $s \mapsto \varepsilon s + k$ there, with $\varepsilon = \pm 1$. (ii) Joined to
V.B, **that is Milnor's Appendix Lemma 1 in full**: the overlap has at most two components, on each
of which the transition is $s \mapsto \pm s + k$, and if there are two they reach opposite ends.
(iii) *The extension theorem*, in the strong form the whole design is for: the arc glued from two
unit-speed arcs is again a unit-speed smooth arc, its source is the **union** of the two sources,
and its coordinate **equals** the old one on the whole of the first source. *Hypotheses:* the affine
half needs a length element and unit speed and nothing else — no dimension, no Hausdorffness, no
compactness, no boundarylessness; Lemma 1 and the two extension theorems add $M$ Hausdorff, because
V.B and V.A's `overlap` API are stated for Hausdorff spaces, and the extension theorems inherit
V.A's normalization, that the first arc starts at a boundary point with coordinate $0$ and interval
$[0, c)$. *Deviation, and it is the one that matters for V.G–V.I:* V.A's topological extension
theorem **cannot be reused with smoothness added**. Its conclusion is an existential that forgets
the witness's coordinate, and from the statement alone one can recover only that the transition is
an increasing homeomorphism fixing $0$ — it could be $s \mapsto s^2$. So the theorem is restated for
smooth arcs, reusing the apparatus beneath it verbatim and transcribing the parts of its proof that
carry over. About 75 lines of the original then *disappear*: both one-sided limit computations at
the junction and the trichotomy proofs of continuity there, and they disappear because with
unit-speed arcs the two branches are the same affine function on the whole overlap, not merely near
the seam, so there is no junction to be continuous at. The strong form is not a bonus but forced:
the transition being $s \mapsto \pm s + k$, and the normalization pinning down both the sign and the
constant, the old parameter *is* the new parameter on the old source. This is the sharp reason
Milnor states his lemma for arc-length parametrizations and not for arbitrary charts.

**V.G (Milnor's first case: a compact one-manifold with boundary is $[0,1]$;
`exists_closed_unitSpeedArc`, `exists_unitSpeedArc_component`, `exists_unitSpeedArc_of_preconnected`,
`SmoothArc.equivIcc`, `SmoothArc.diffeomorphIcc`, `nonempty_diffeomorphIcc`, `boundary_eq_pair`,
`ncard_boundary_eq_two`).** Let $M$ be a compact Hausdorff smooth one-manifold with a boundary point
$p$. Verified: the finite-cover induction of Milnor's Step 2, run with *unit-speed* arcs, produces a
unit-speed smooth arc from $p$ with coordinate $0$ and interval $[0, \ell]$, $\ell > 0$, whose source
is **the whole connected component of $p$** and which identifies the boundary inside that component
as $\{p, A^{-1}(\ell)\}$; if $M$ is moreover connected, its source is all of $M$, the arc rescaled by
$1/\ell$ is a **diffeomorphism $M \to [0,1]$** in Mathlib's sense over the model $\mathbb R^1_\partial$,
and the boundary of $M$ is exactly the two points $p$ and $A^{-1}(\ell)$, of cardinality $2$. The
last conclusion is **Milnor's own corollary**, and where V.A counts the boundary points modulo two it
*identifies* them. *Hypotheses:* $\operatorname{finrank}_{\mathbb R} E = 1$, $C^\infty$, $M$ Hausdorff
(used twice, by V.E for the length element and by V.F's extension theorem), and $M$ compact. *Three
things worth recording.* Compactness is used three times and **$\sigma$-compactness would not do for
two of them** — to extract a *finite* subcover by sources of unit-speed arcs, which is what makes the
induction terminate, and to know that the component of $p$ is compact, which is what forbids a proper
open sub-arc from exhausting it; only the third use, feeding V.E, is $\sigma$-compactness in disguise.
This is why the compact cases need no countability hypothesis. Connectedness is needed nowhere in the
exhaustion: the honest conclusion is about the component of $p$, which is the form V.J wants. And the
conversion to Mathlib's `Diffeomorph` through its two `Icc` bridges cost about twenty lines, the
cheapest part of the stage rather than the dearest. *Deviation:* V.A's finite-cover induction is
restated rather than reused, for three independent reasons — its conclusion is a topological arc and
the induction feeds its own output back in; its extension step is V.A's, which does not record that
the coordinate is preserved, so V.F's is the one the loop calls; and its hypothesis
`BoundaryCompatible` demands a homeomorphism of the model space with a half-line, which does not
exist when the model range is a compact interval, a shape V.C deliberately admits. Nothing in V.A's
file is edited.

**V.H (Milnor's second case: a compact boundaryless one-manifold is the circle; `IsUnitSpeedCurveOn`,
`trans_eq_add_of_two_points`, `eqOn_of_eventuallyEq`, `periodic_of_eq`, `exists_period`,
`exists_minimal_period`, `surjective_of_periodic`, `exists_periodic_parametrisation`,
`isInvertible_of_finrank_one`, `isLocalDiffeomorph_circleParam`, `nonempty_diffeomorphCircle`).** Let
$M$ be a nonempty compact Hausdorff connected smooth one-manifold with **empty boundary**. Verified:
there are a length element, a period $T > 0$ and a map $\gamma : \mathbb R \to M$ which is an
arc-length parametrization near every time, is $T$-periodic and onto, is injective on $[0, T)$, has
$T$ as its *least* period, and satisfies $\gamma s = \gamma t$ exactly when $s - t$ is an integer
multiple of $T$ — in words, such an $M$ **is a closed geodesic of length $T$** (Milnor's Step 5). And
$M$ is $C^\infty$-diffeomorphic to Mathlib's `Circle` over the model $\mathbb R^1$, in both
directions. *Hypotheses:* $\operatorname{finrank}_{\mathbb R} E = 1$, $C^\infty$, $M$ Hausdorff (used
three times: V.E, V.F, and essentially in the propagation lemma, for uniqueness of limits), $M$
compact (used twice, and **$\sigma$-compactness would not do for either** — to make the curve
accumulate as its time approaches the end of its interval, which is what lets it be continued, and to
make it accumulate at $+\infty$, which is what forces it to return and produces the period),
preconnected (only for surjectivity) and nonempty (only to choose a base point). No second
countability, no orientability, no `BoundarylessManifold` instance; emptiness of the boundary is about
$M$, not about the model, so the model range may still be a half-line or a compact interval.
*Deviation, and this is the substantive correction of the whole programme:* **the exhaustion by arcs
does not exist in the boundaryless case.** Every arc of a manifold with empty boundary has an *open*
interval, while V.F's extension theorem needs the first arc's interval to be half-open, that is, to
start at a boundary point; so V.G's induction has no boundaryless analogue in the shape the design
assumed. The replacement is to drop injectivity: a *unit-speed curve* is a map of the line agreeing
near each time with the arc-length parametrization of a unit-speed arc, and the engine is a
**propagation lemma** — two unit-speed curves agreeing near one time agree at every time — proved by
a connectedness argument run in the parameter of one arc rather than in the time, because the set of
times of local agreement need not be closed, and the obstruction is exactly that an overlap can have
two components. With curves, continuation needs no gluing of injective arcs and no two-component
bookkeeping at all. *Two more things fell out.* The geometric fact singled out as the one part of
Milnor's Step 5 with no counterpart in V.A's file — that two times with the same value have matching
directions — is proved by excluding a reflection through local injectivity. And **V.B turns out not
to be used here**: what V.H needs from V.A's file is the relative openness of hulls and V.F's affine
half, not the counting of components; V.B remains the right statement of Milnor's lemma, but the
design's claim that V.H depends on it was wrong. *Two further deviations of route.* Mathlib has no
quotient-manifold theory, so $\mathbb R / T\mathbb Z$ is not available and the descent goes through
local inverses of $t \mapsto \exp(2\pi i t / T)$, whose local diffeomorphism property is obtained
without computing a chart of the circle: the two coordinate functions $z \mapsto \operatorname{re} z$,
$z \mapsto \operatorname{im} z$ pull back to $\cos$ and $\sin$, which cannot both have vanishing
derivative, and rescaling whichever does not gives a smooth left inverse of the derivative. And
Mathlib's tangent spaces carry no norm, so "a nonzero linear map between one-dimensional spaces is
invertible" had to be stated for topological modules with the inverse supplied as data — which that
left inverse provides.

**V.I (Milnor's third and fourth cases: the non-compact ones are $[0,\infty)$ and $\mathbb R$;
`IsUnitSpeedCurveOn.notMem_boundary`, `eqOn_add_of_eq`, `isCompact_isOpen_image_Icc_of_eq`,
`mem_image_dom_of_mem_closure`, `SmoothArc.shrink`, `exists_parametrisation_of_boundary_eq_empty`,
`exists_ray_of_mem_boundary`, `exists_param_of_isOpen_ordConnected`, `exists_param_halfline`,
`iciHomeomorph`, `instIciChartedSpace`, `instIciIsManifold`, `nonempty_diffeomorphReal`,
`nonempty_diffeomorphIci`, `boundary_eq_singleton`).** Let $M$ be a connected Hausdorff
$\sigma$-compact smooth one-manifold which is **not compact**. Verified: if its boundary is empty, $M$
is $C^\infty$-diffeomorphic to $\mathbb R$ over the model $\mathbb R$; if it has a boundary point $p$,
$M$ is $C^\infty$-diffeomorphic to $[0, \infty)$ over the model $\mathbb R^1_\partial$, and then $p$
is its **only** boundary point. On the way: such an $M$ is parametrized by an *open interval* of
times in the boundaryless case — the honest form, since without compactness the interval need not be
the whole line, as $(0,1)$ shows — and by a half-open one in the other; every nonempty open interval
of the line is diffeomorphic to the line and every $[0, b)$ or $[0, \infty)$ to $[0,\infty)$, by
explicit elementary formulas with their explicit logarithmic or rational inverses, so **no inverse
function theorem is used anywhere in this stage**; and no value of a unit-speed curve is a boundary
point, the single fact that organises the whole argument. *What had to be built:* $[0,\infty)$ as a
one-chart $C^\infty$ manifold with boundary over $\mathbb R^1_\partial$ — Mathlib has $[a,b]$ only,
and there through two charts — with the two bridges, inclusion into $\mathbb R$ and projection from
it, that make a map into or out of it smooth exactly when its real expression is; and `SmoothArc.shrink`,
the restriction of a smooth arc to an open subinterval with the parameter shifted, which is what turns
the half-open arc issuing from a boundary point into the centred arc with symmetric open interval that
V.H's curve machinery accepts. *Hidden hypothesis, and where it bites:* **$\sigma$-compactness is used
once and only once, to build the length element of V.E.** Everything after that — the arcs, the
curves, the propagation lemma, the maximality of the interval of reached times, the continuation step
and both classifications — uses only Hausdorffness, connectedness and the failure of compactness. And
that one use is exactly where the hypothesis is *necessary*: see the note after V.J. Milnor's
manifolds sit in Euclidean space and get it for free, and he uses it silently, the metric he restricts
to $M$ being a Riemannian metric. *Deviations from the expected route, both instructive:* a repeated
value gives a period only once the curve is known to run on the whole line, which here it need not, so
injectivity is instead proved from the fact that a repeated value makes the image of one compact
interval of times both compact and open, hence all of a preconnected $M$, hence $M$ compact; and a
unit-speed curve cannot take a boundary value at all, so it cannot run on a closed half-line of times
— the boundary point has to be adjoined by hand, and showing that no *second* boundary point appears
in the closure is the long step, and the only place non-compactness is used in that case. (If a second
one did appear, $M$ would be covered by three compact pieces, which is V.G.)

**V.J (Milnor's Appendix theorem, its exclusivity, and the slice form;
`models_pairwise_not_diffeomorph`, `nonempty_diffeomorph_cases`, `nonempty_diffeomorph_or`,
`isOpen_connectedComponent_of_oneManifold`, `componentOpens`, `boundary_Ici`,
`boundary_inter_component_eq_pair`, `finite_boundary_of_compact`, `even_ncard_boundary_of_compact`,
`component_diffeomorph`, `nonempty_diffeomorphIcc_component_iff`,
`nonempty_diffeomorphCircle_component_iff`, `Milnor.IsHalfSliceSubmanifold.component_diffeomorph`,
`Milnor.IsHalfSliceSubmanifold.nonempty_diffeomorphIcc_component_iff`,
`Milnor.IsHalfSliceSubmanifold.ncard_boundary_inter_component`,
`Milnor.IsHalfSliceSubmanifold.exists_boundary_partner`,
`Milnor.IsHalfSliceSubmanifold.even_ncard_boundary_of_classification`).** **Milnor's Appendix
theorem.** Let $M$ be a connected Hausdorff $\sigma$-compact nonempty $C^\infty$ one-manifold. Then
$M$ is $C^\infty$-diffeomorphic to **exactly one** of

| | boundary empty | boundary nonempty |
|:--|:--|:--|
| compact | the circle (V.H) | $[0, 1]$ (V.G) |
| not compact | $\mathbb R$ (V.I) | $[0, \infty)$ (V.I) |

each model carrying its own model with corners — $\mathbb R^1$ on the circle, $\mathbb R^1_\partial$
on the two half-line-type intervals, $\mathbb R$ on the line — and the case being read off from
whether $M$ is compact and whether its boundary is empty. Nothing is assumed about the boundary,
about orientability or about second countability, and no compatibility hypothesis is assumed, V.C
having proved chart-independence of the boundary. **Exclusivity** is a statement about the four
models alone and is proved separately, all six exclusions: *compactness* separates
$\{$circle, $[0,1]\}$ from $\{[0,\infty), \mathbb R\}$, which settles four of them, a diffeomorphism
being in particular a homeomorphism; and *the number of boundary points* settles the remaining one
in each compactness class, by Mathlib's theorem that a diffeomorphism carries boundary onto boundary
— stated for two different models with corners — which makes that number a diffeomorphism invariant,
its values on the four models being $0$, $2$, $1$, $0$.

**The slice form, and the boundary count a second time.** In Chapter 2's language: let $X$ be a
compact half-slice submanifold with boundary $B$ of a Hausdorff ambient manifold, modelled on the
half-space over a one-point $Z$ — that is, a compact one-manifold with boundary in the sense of V.A′.
Then **every connected component of $X$ is diffeomorphic to the circle or to $[0,1]$; the components
carrying a boundary point are exactly those of the second kind; each of those meets $B$ in exactly
two points; and $B$ is finite of even cardinality.** The last conclusion is V.A′ again, and the point
of this item is that it now follows **from the classification**, as in the book, the pairing being
realised by the two ends of a single arc-length parametrization of a component rather than by an
abstract parity argument. V.A′ is not cited and is left untouched; what is reused from V.A's file is
only the pure combinatorics, that a fixed-point-free involution of a finite set has even cardinality.
*What had to be built, three bridges the project will want again.* (1) **The connected components of
a one-manifold are open**, hence are manifolds in their own right, which is what lets a theorem
needing connectedness be applied to a disconnected manifold, and which the design never mentions; it
needs nothing but $\operatorname{finrank}_{\mathbb R} E = 1$ and smoothness, since V.D gives every
point a neighbourhood which is the source of an arc and the source of an arc is preconnected. (2) The
boundary of the model half-line is a single point, which Mathlib could not supply, having no half-line
manifold. (3) The boundary count for a possibly **disconnected** compact one-manifold, whose
*finiteness* is the harder half and could not reuse V.A, because V.A wants a compatibility hypothesis
available only when the model range is a half-line. No bridge between the project's half-slice charts
and Mathlib's boundary had to be built, Chapter 2 having proved it, nor any ambient/intrinsic
translation; the transport of the counting statement follows V.A′'s file line for line. *Two things
the design got right paid off:* stating V.G's exhaustion for the *component* of a boundary point made
the disconnected case cheap, and giving each model its own model with corners cost nothing.

**$\sigma$-compactness is necessary.** The classification is **false** without a countability
hypothesis. The long line — two copies of the closed long ray $\omega_1 \times [0,1)$ with the
lexicographic order topology, glued along their least elements — is a connected Hausdorff smooth
one-manifold without boundary which is neither compact nor $\sigma$-compact, and it is diffeomorphic,
indeed not even homeomorphic, to none of the four models, since it is not second countable and all
four are. So the two non-compact cases must assume $\sigma$-compactness, and they do. In the compact
cases nothing extra is needed: compact plus Hausdorff plus a finite-dimensional model gives second
countability by Mathlib's own theorem. And the failure is located exactly: it is **the length element**
that does not exist, since a manifold carrying a Riemannian metric is metrizable, so the long line
carries none and Milnor's arc-length reparametrization has nothing to start from. Milnor's manifolds
sit in $\mathbb R^k$, hence are second countable, and he uses this silently.

**Size of the classification.** 9,276 lines for the nine stages: 463 for V.B, and 8,813 in the nine files of
`Milnor/Appendix/Smooth/` for V.C–V.J — 820 (V.C), 630 (V.D), 595 and 720 (V.E), 929 (V.F), 421
(V.G), 1,712 (V.H), 2,202 (V.I), 784 (V.J). The two largest files are the two whose route had to be
invented rather than transcribed, V.H and V.I. With V.A and V.A′ the Appendix is 11,054 lines in
twelve files. The design pass estimated the classification at about 4,000 lines in nine stages; it
took nine stages and rather more than twice the lines. See §11 for the comparison.

---

## 11. What is not verified, and what each part would need

**Two items remain, and both are in §6.** Everything else this section has ever listed is now
checked: Milnor's Lemma 2 of §6, the chart definition of the index, the mod 2 remark of §7, and — as
of this revision — Milnor's Appendix theorem. What is left is one sentence of §6 that cannot yet be
*written down*, because the definition it needs is not in Mathlib, and one statement of §6 that
Milnor does not prove either.

The habit of this section is to record the estimate against the outcome, because the estimates have
been wrong every time, and always in the same direction. Lemma 2 and the chart definition were
together estimated at 800 lines and cost 1,602 (V6.11–V6.14), low by a factor of two. The mod 2
remark was estimated at 800 lines, on the grounds that "the same proof applies with the mod 2 count
in place of the signed count", and cost 4,874 (V7.18–V7.26), low by a factor of six, and 5,438
counting the two items that afterwards removed its one superfluous hypothesis (V7.27, V7.28) — the
estimate overlooked that the remark presupposes the notion of an orientable manifold and of an
orientation-reversing loop, neither of which existed in Mathlib, in this project, or in the book.
The classification of one-manifolds was estimated, after a full design pass, at **about 4,000 lines
in nine stages**; it took nine stages — the plan's stage boundaries held, which no previous estimate
managed — and **about 8,800 lines**, 8,813 in the nine files of `Appendix/Smooth/` and 9,276 counting
the topological stage V.B. Low by a factor of more than two, and the excess is concentrated in the
two stages whose route the plan got wrong: the circle (V.H, 1,712 lines), where the exhaustion by
arcs turns out not to exist in the boundaryless case and had to be replaced by unit-speed curves and
a propagation lemma, and the non-compact cases (V.I, 2,202 lines), where a boundary point has to be
adjoined by hand because no unit-speed curve can take a boundary value. The pattern across all three
estimates is the same: what a designed plan measures well is the *shape* of the work, and what it
measures badly is the cost of the steps the source passes over in a sentence.

**Chapter 6.** Verified (§7), including Lemma 2 (V6.12), Lemma 4 and the index of a non-degenerate
zero (V6.10), Lemma 5 and the chart definition of the index (V6.13, V6.14), and the Euler number
$1 + (-1)^n$ of $S^n$ (V6.15). Two things remain.

*The identification of the Poincaré–Hopf integer with the Euler characteristic* (V6.9, V6.15). The
integer $\chi(N)$ of V6.9 exists, is independent of the field, and for $S^n$ is computed to be
$1 + (-1)^n$; what is missing is that it is the Euler characteristic. This is not a gap that an
estimate in lines would measure, because the statement cannot be *written down*: Mathlib has no
Euler characteristic of a topological space, no Betti numbers and no singular or cellular homology
of a space with ranks to alternate. Supplying that would mean building a homology theory and its
computation for manifolds — the work of a library, not of a chapter — and Milnor himself does not
prove it, referring to Hopf's theorem and to the literature. It is therefore **not planned**, and
it is the one place where this edition is honestly further from the book than a page count
suggests. Related and equally out of reach: Poincaré–Hopf for a manifold not presented as a
submanifold of Euclidean space, which needs Whitney's embedding theorem (Milnor also works with
$N \subseteq \mathbb R^k$).

*The agreement of the two definitions of the index at an arbitrary isolated zero* (V6.14). At a
non-degenerate zero the two are proved equal, which is what Milnor's Lemma 5 gives and what the
book uses. In general they are degrees of maps of spheres of *different* dimensions, $S^K$ for the
extended field and $S^{n-1}$ for the field read in a parametrization, so no appeal to invariance
under diffeomorphisms can compare them. What is needed first is a suspension formula: that the
index of a field of the shape $(u, y) \mapsto (\tilde v(u), y)$ on
$\mathbb R^n \times \mathbb R^{K+1-n}$ is the index of $\tilde v$. That is a statement about
degrees of joins of maps of spheres and would cost, at a guess, 600 to 1,000 lines on top of the
machinery of §5; the guess is worth little, the three previous ones having been low by factors of
two, six, and more than two. Milnor does not prove it either.

**Chapter 7.** Verified (§8), including the Hopf theorem for oriented $M$ (V7.17) and Milnor's mod
2 theorem for non-orientable $M$ (V7.26). Nothing of §7 is unverified, and — since this revision —
no hypothesis is carried that mathematics does not require. The dimension condition $2 \le m$ that
the previous edition flagged as vacuous has been **removed**, in the way that edition said was the
only way to remove it: through the classification of one-manifolds, which is now proved (§10,
V.B–V.J). Every connected $\sigma$-compact one-manifold is orientable (V7.27), so a connected
non-orientable manifold has dimension at least two (V7.28), and V7.26 assumes nothing about the
dimension beyond the $0 < m$ its target sphere needs. V7.22 still states its own $2 \le m$, and
should, because for punctured balls the hypothesis is sharp and not vacuous; it is simply no longer
an assumption of anything that uses it.

**The Appendix, and the hypothesis it removed.** The Appendix is verified twice over (§10): the
boundary count for *topological* 1-manifolds (V.A, V.A′), which is stronger than the book in its
hypothesis, and Milnor's classification itself (V.B–V.J), which is the theorem he states, with the
four cases proved mutually exclusive and the boundary count drawn from it a second time as he draws
it. Nothing in the book's own arguments needs the classification — the boundary count is what they
use, and Chapters 2 and 4 still cite the old proof — so it is here because the book states it, and
because it was the one route to deleting $2 \le m$ from Chapter 7. Three findings from the work are
worth keeping on the record. Mathlib's arc-length file is of no use for this: its unit speed is
metric variation, not a derivative, and its reparametrization is a set-theoretic inverse with no
smoothness, so the length element had to be built from scratch (V.E). The existence of a Riemannian
metric was the one piece of general theory needed and Mathlib does not have it; in dimension one the
length element *is* that metric, and it is the only place in the classification where Hausdorffness
and $\sigma$-compactness are used at all. And the classification is **false** without a countability
hypothesis — the long line is a connected smooth 1-manifold which is neither the circle nor an
interval — so the non-compact cases assume $\sigma$-compactness, and the failure is located exactly
at the length element, a manifold carrying a Riemannian metric being metrizable. Milnor's manifolds
sit in Euclidean space and get all of this for free, and he uses it silently.

**Chapter 8.** Verified (§9): all seventeen problems.

In total, what separates this edition from a fully checked book is one sentence of §6: that the
Poincaré–Hopf integer is the Euler characteristic. Everything the book proves in §1–§8 and in the
Appendix is now checked, apart from that sentence, the general agreement of the two index
definitions (a few hundred lines, and not something Milnor proves), and the small items
recorded at the ends of §2–§6, none of which anything downstream needs. The first is a missing
definition rather than a missing proof, and Mathlib is where it would have to appear.

---

## 12. Sign-off

The statements below are the ones the reader is asked to confirm say what Milnor means. Each
corresponds to one verified theorem above. They are summaries: the standing hypotheses stated with
each V-item (manifolds without boundary unless a boundary is named, Hausdorff and second
countable where the V-item says so, and the two formal conventions of §1) are not repeated.

1. (V1.1) A smooth map between manifolds of equal dimension with invertible derivative at a point
   is a diffeomorphism near that point.
2. (V1.3) At a regular value of a smooth map from a compact manifold to a manifold with closed
   points, of equal dimensions, the preimage is finite.
3. (V1.4) With both manifolds Hausdorff, the number of preimages is constant on a neighbourhood
   of a regular value.
4. (V1.5) On a connected set of regular values, if one point is hit then all are.
5. (V1.6) Every nonconstant complex polynomial has a root.
6. (V2.2) The preimage of a regular value is a submanifold of the complementary dimension.
7. (V2.3) Its tangent space is the kernel of the derivative.
8. (V2.5) $\{g \ge 0\}$ is a manifold with boundary $\{g = 0\}$ when $0$ is a regular value of $g$.
9. (V2.6) For a regular value of a map defined on the whole ambient manifold, the preimage inside
   such a manifold with boundary, under the transversality condition, is a manifold with boundary
   equal to the preimage in the boundary.
10. (V2.7) The closed unit ball of $\mathbb R^{m+1}$ is a manifold with boundary the unit sphere
    $S^m$.
11. (V3.1) The critical values of a smooth map between open subsets of finite-dimensional spaces
    have measure zero.
12. (V3.3) The regular values of a smooth map from a second countable manifold are dense.
13. (V.A) A compact topological 1-manifold with boundary has an even, finite number of boundary
    points.
14. (V.A′) The same for the compact 1-manifolds with boundary produced by Lemma 4.
15. (V2.9) For smooth $P$, Milnor's formula $x + t(x)u(x)$ is a smooth map of norm one wherever
    it makes sense, and fixes the points $x$ of the sphere with $\|Px\| \le 1$; it makes sense on
    the whole disk when $P$ maps the disk into itself without fixed points.
16. (V2.10) Every smooth map of the whole space that maps the closed unit ball into itself has a
    fixed point in the ball.
17. (V2.11) Every continuous self-map of the closed unit ball has a fixed point.
18. (Convention) A smooth homotopy is a smooth map on $M \times \mathbb R$ with the given maps at
    $t = 0$ and $t = 1$; this is equivalent to Milnor's notion.
19. (V4.3) If two smoothly homotopic maps from a compact manifold have a common regular value,
    the two preimage counts have the same parity.
20. (V4.4) On a connected manifold, any point can be carried to any other by a diffeomorphism
    joined to the identity by a smooth isotopy $N \times \mathbb R \to N$ all of whose stages are
    diffeomorphisms.
21. (V4.6) The parity of the preimage count of a map from a compact manifold to a connected one
    is the same at all regular values.
22. (V4.8) Smoothly homotopic maps have the same degree modulo 2.
23. (V4.9) A map of nonzero degree modulo 2 is surjective.
24. (V5.0) An orientation of a manifold is an orientation of each tangent space, carried to the
    orientation at $x$ by the derivative of the chart at $x$ for all nearby points; the sign of
    a linear map between oriented spaces is the sign of the pullback of a positive top form.
25. (V5.1) The sign of the derivative is locally constant near a regular point.
26. (V5.3) For $X = \{g \ge 0\}$ compact in a boundaryless oriented $M'$ and $y$ regular for $f$
    and for $f|\{g = 0\}$, the signs of the pair map $(f, g)$ over $f^{-1}(y) \cap \{g = 0\}$
    sum to zero; this is Lemma 1 up to the identification of the boundary orientation.
27. (V5.4) Smoothly homotopic maps have the same signed count at a common regular value.
28. (V5.5) A diffeomorphism reached from the identity by an isotopy through diffeomorphisms
    preserves orientation.
29. (V5.6) The signed count is the same at all regular values ($N$ connected).
30. (V5.7) The Brouwer degree is well defined, homotopy invariant, and nonzero only for
    surjective maps.
31. (V5.8) The level set $g^{-1}(0)$ in an oriented vector space is oriented by "outward vector
    first".
32. (V5.9) The antipodal map of $S^n$ has sign $(-1)^{n+1}$ at every point, and, for $n \ge 1$,
    degree $(-1)^{n+1}$.
33. (V5.10) For even $n \ge 2$, every smooth tangent vector field on $S^n$ has a zero.
34. (V5.10, converse) For odd $n$ there is a smooth tangent vector field on $S^n$ without zeros.
35. (V6.0) The index of an isolated zero $z$ of a smooth field on $\mathbb R^{n+1}$ is the degree
    of $u \mapsto v(z + \varepsilon u)/|v(z + \varepsilon u)|$ on $S^n$; it is independent of
    $\varepsilon$, homotopy invariant, and depends only on the germ of $v$ at $z$.
36. (V6.1) A regular level set $g^{-1}(0)$ in an oriented manifold with Euclidean charts is
    oriented by "outward vector first", and $\deg(f|g^{-1}(0); y) = 0$, the preimage being finite,
    when $f$ is smooth on an open set containing the level set, $y$ is regular for $f$ there and
    satisfies the transversality condition at the points of $f^{-1}(y) \cap g^{-1}(0)$ (which,
    given the first, is equivalent to $y$ being regular for $f|g^{-1}(0)$), and
    $f^{-1}(y) \cap \{g \ge 0\}$ is compact there.
37. (V6.2) If $\Phi$ carries $G^{-1}(0)$ into $G'^{-1}(0)$ and $dG' \circ d\Phi = c\, dG$ at $q$
    with $c \ne 0$, the sign of the restricted map at $q$ is $\operatorname{sgn}(c)$ times the
    ambient sign of $\Phi$.
38. (V6.3) For a compact region $X = \{G \ge 0\}$ in which every zero of $v$ is one of the centres
    of disjoint small balls inside $\{G > 0\}$, the index sum over the centres is the degree of
    $v/|v|$ on $\partial X$.
39. (V6.4) If moreover $v$ points outward along $\partial X$, the index sum is the degree of the
    Gauss map of $\partial X$.
40. (V6.5) The index of an isolated zero is invariant under diffeomorphisms of open subsets of
    $\mathbb R^{n+1}$ (Milnor's Lemma 1), proved without Lemma 2.
41. (V6.6) A compact nonempty submanifold $N$ of $\mathbb R^k$ has an $\varepsilon$-neighbourhood
    on which the nearest point $r(x)$ is unique and depends smoothly on $x$, with $x - r(x)$ normal
    to $N$; moreover $r(x + sv) = x$ for $x \in N$, $v$ normal to $N$ at $x$ and $s$ small. The
    formal statement adds three conclusions: the distance to $N$ is attained, at $r(x)$, for every
    $x$ of $\mathbb R^k$; $r$ is the identity on $N$; and $dr_x$ takes values in $T_{r(x)}N$.
42. (V6.7) $N_{\varepsilon/2}$ is a compact region with smooth boundary, and
    $w = v \circ r + (\mathrm{id} - r)$ extends a tangent field $v$ with the same zeros and points
    outward.
43. (V6.8) The index of a tangent field on a compact $N \subseteq \mathbb R^{K+1}$ at a point is
    *defined* as the index of $w$ there; it depends only on the germ of $w$.
44. (V6.9) For a compact nonempty submanifold $N \subseteq \mathbb R^{K+1}$, $K \ge 1$, there is an
    integer $\chi(N)$ equal to the index sum of every smooth tangent field with finitely many
    zeros.

45. (V7.0) A framed submanifold of $M$ of codimension $p$ is a compact submanifold with $p$
    smooth, independent normal fields tangent to $M$; a framed cobordism is a submanifold of
    $M \times \mathbb R$ which is a product for $t < \varepsilon$ and for $t > 1 - \varepsilon$
    (some $0 < \varepsilon < \tfrac12$), compact over $[0,1]$, framed compatibly with the ends.
46. (V7.1) The Pontryagin manifold of $f$ at a regular value $y$ for a basis $b$ is $f^{-1}(y)$
    with the framing $v_i(x) = A_x^*(A_x A_x^*)^{-1} b_i$, $A_x$ the derivative of the extension
    $c_y \circ f \circ r$; it satisfies $A_x v_i(x) = b_i$.
47. (V7.2) A homotopy constant near the ends, with a common regular value $z$ of the homotopy
    and of both ends, gives a framed cobordism between the two Pontryagin manifolds at $z$.
48. (V7.3) Pontryagin manifolds of the same map at the same regular value for two bases of the
    same orientation are framed cobordant; $GL^+(p, \mathbb R)$ is connected by smooth paths.
49. (V7.4) Framed cobordism is symmetric and transitive; it is reflexive for framed
    $0$-manifolds (Chapter 7) and in every codimension (Chapter 8), hence an equivalence relation.
50. (V7.5) For $p \ge 1$, Pontryagin manifolds of the same map at two regular values, with
    positive bases, are framed cobordant.
51. (V7.6) For $p \ge 1$, smoothly homotopic maps have framed cobordant Pontryagin manifolds
    (at any regular values, positive bases).
52. (V7.7) A framed submanifold has a product neighbourhood: $G(x, s) = r(x + \sum s_i v_i(x))$
    is injective on $N \times B_\varepsilon$ with open image and smooth inverse, and
    $dG_{(x,0)}(a, s) = a + \sum s_i v_i(x)$.
53. (V7.8) At $x \in f^{-1}(y)$, $\ker A_x = T_x N \oplus (T_x M)^\perp$, so a tangent vector of
    $M$ orthogonal to $N$ with $A_x v = b_i$ is the framing vector.
54. (V7.9) Every framed submanifold is the Pontryagin manifold of some map at the north pole,
    for the basis $c\,b$ with some $c > 0$, $b$ any given basis.
55. (V7.10) Two maps with the same Pontryagin manifold at $y$ (bases $b$ and $c\,b$, $c > 0$) are
    smoothly homotopic; a framed cobordism between $F_0$ and $F_1$ is realised by a smooth
    $H : M \times \mathbb R \to S^p$ with Pontryagin manifolds $F_0$ at $t = 0$ and $F_1$ at $t = 1$.
56. (V7.11) For $p \ge 1$, if the Pontryagin manifolds of $f$ and $g$ (positive bases, any
    regular values) are framed cobordant, then $f$ and $g$ are smoothly homotopic.

57. (V7.12) A framed $0$-manifold is a finite set of points with a basis of $T_x M$ at each;
    the sign of a point is the sign of that basis; for $m \ge 1$ and the Pontryagin manifold of
    $f$ at a regular value with a positive basis, the sign at $x$ is the sign of $df_x$, and the
    signed count is $\deg f$.
58. (V7.13) For $m \ge 1$, let $U$ be a chart ball whose closed ball lies in the chart image, on
    which the chart preserves orientation, and whose closure contains no other point of the framed
    $0$-manifold. A framed point in the concentric ball of a quarter the radius can be moved to any
    point of that smaller ball, with any frame of the same sign, by a framed cobordism; hence to
    any point of its component in the complement of the other points.
59. (V7.14) For $m \ge 1$, in such a chart ball $U$ of radius $R$, two points at
    $\varphi^{-1}(c_0 \pm a w)$ with $|c_0 - \varphi(x_c)| < R/8$ and $8a \le R$, and no other point
    in the closure of $U$, carrying the standard frames (which have opposite signs), can be
    cancelled by a framed cobordism.
60. (V7.15) In a connected, locally connected $T_1$ space with the segment property, for a finite
    set partitioned into two nonempty parts, some point of one part has a neighbour in the other.
61. (V7.16) On a compact connected oriented $M$ ($m \ge 1$), framed $0$-manifolds with the
    same signed count are framed cobordant.
62. (V7.17) On such $M$, smooth maps $M \to S^m$ of the same degree are smoothly homotopic,
    and every integer is a degree (for the latter, $M$ need not be connected).

63. (V8.0) The sphere is oriented as the boundary of the disk (outward normal first); the preimage
    of a regular value is oriented as in §5 (tangent vectors of the preimage, then lifts of a
    positive basis); a product $A \times B$ is oriented by a positive basis of $A$ followed by one of $B$.
64. (V8.1) For smooth maps $f : M \to N$ and $g : N \to P$ between compact oriented boundaryless
    manifolds of the same dimension, with $N$ and $P$ connected, $\deg(g \circ f) = \deg g \cdot \deg f$.
65. (V8.2) A complex polynomial of degree $n \ge 1$ induces a smooth map of the Riemann sphere of
    degree $n$.
66. (V8.3) Maps $f, g : X \to S^p$ with $\|f(x) - g(x)\| < 2$ for all $x$ are homotopic, and smoothly
    homotopic when they are smooth maps of a manifold.
67. (V8.4) Every continuous map from a compact manifold $X \subseteq \mathbb R^{K+1}$ to $S^p$ is a uniform
    limit of smooth maps, and continuously homotopic smooth maps $X \to S^p$ are smoothly homotopic.
68. (V8.5) If $m < p$, every smooth map from a boundaryless $m$-manifold to $S^p$ is smoothly
    homotopic to a constant, and every continuous map from a compact $m$-manifold in Euclidean
    space to $S^p$ is homotopic to a constant.
69. (V8.6) A smooth map $S^n \to S^n$ ($n \ge 1$) whose degree is not $(-1)^{n+1}$ has a fixed point.
70. (V8.7) A smooth map $S^n \to S^n$ ($n \ge 1$) of odd degree satisfies $f(-x) = -f(x)$ for some $x$.
71. (V8.8) For manifolds $M \subseteq \mathbb R^k$, $N \subseteq \mathbb R^l$, the product $M \times N$ is a
    manifold of dimension $m + n$ with tangent space $TM_x \times TN_y$.
72. (V8.9) The graph of a smooth $f : M \to N$ is a manifold of dimension $m$ whose tangent space at
    $(x, f(x))$ is the graph of $df_x$.
73. (V8.10) The tangent bundle space $TM$ is a manifold of dimension $2m$; a smooth $f$ induces a
    smooth $df : TM \to TN$, with $d(\mathrm{identity}) = \mathrm{identity}$ and $d(g \circ f) = dg \circ df$.
74. (V8.11) The normal bundle space $E$ of $M \subseteq \mathbb R^k$ is a manifold of dimension $k$; for
    compact nonempty $M$ there is $\varepsilon > 0$ such that $(x, v) \mapsto x + v$ maps
    $\{(x, v) \in E : \|v\| < \varepsilon\}$ diffeomorphically onto the $\varepsilon$-neighbourhood of $M$.
75. (V8.12) For such $\varepsilon$, $r(x + v) = x$ is strictly closer to $x + v$ than any other point of
    $M$; continuous maps from a compact manifold $X$ into $M$ are uniform limits of smooth maps, and
    continuously homotopic smooth maps $X \to M$ are smoothly homotopic.
76. (V8.13) For disjoint compact oriented $a$- and $b$-manifolds mapped into $\mathbb R^{k+1}$,
    $k = a + b > 0$: $l(\beta, \alpha) = (-1)^{(a+1)(b+1)} l(\alpha, \beta)$, and $l(\alpha, \beta) = 0$
    when the first is the boundary of a compact region whose image misses the second.
77. (V8.13′) For $a, b \ge 1$, the linking number in $S^{k+1}$, computed after any rotation that
    keeps the north pole off both images, does not depend on the rotation.
78. (V8.14 a, b) For $p \ge 2$ and smooth $f, g : S^{2p-1} \to S^p$ with regular values $y \ne z$:
    $l(f^{-1}(y), f^{-1}(z))$ is locally constant in $y$; and if $\|f(x) - g(x)\| < \|y - z\|$ for all
    $x$, then $l(f^{-1}(y), f^{-1}(z)) = l(g^{-1}(y), f^{-1}(z)) = l(g^{-1}(y), g^{-1}(z))$.
79. (V8.14 c) $l(f^{-1}(y), f^{-1}(z))$ does not depend on the regular values $y \ne z$, and smoothly
    homotopic maps have the same Hopf invariant.
80. (V8.15) For odd $p$, $H(f) = 0$; $H(g \circ f) = (\deg g)^2 H(f)$; the Hopf fibration
    $(z_1, z_2) \mapsto (2 z_1 \bar z_2, |z_1|^2 - |z_2|^2)$ agrees with Milnor's formula and, with the
    book's conventions (item 63 and $\lambda(x, y) = (x - y)/\|x - y\|$), has $H(\pi) = -1$.
81. (V8.16) Transverse submanifolds with $n + n' < m$ are disjoint; the intersection of transverse
    submanifolds of codimensions $p, p'$ is a submanifold of codimension $p + p'$ whose tangent space
    is the intersection of the tangent spaces; a framed submanifold can be moved arbitrarily little
    within its product neighbourhood so as to meet a given submanifold transversally.
82. (V8.17) For $p, q \ge 1$ with $p + q \le m$, every pair of classes in
    $\Pi^p(M) \times \Pi^q(M)$ has transverse representatives, and the framed intersection of
    transverse representatives defines a unique map $\Pi^p(M) \times \Pi^q(M) \to \Pi^{p+q}(M)$.
83. (V8.17′) If $2p \ge m + 2$, disjoint union makes $\Pi^p(M)$ an abelian group; its zero is the
    class of the empty manifold, and $-[F]$ is the class of $F$ with its first framing vector
    reversed.

84. (V2.12) For a regular value $y$ of a smooth $f : M \to N$ and $p \in f^{-1}(y)$, with the model
    space of $M$ carrying an inner product, $df_p$ maps the orthogonal complement of the tangent
    space of $f^{-1}(y)$ at $p$ isomorphically onto $T N_y$.
85. (V6.10) For $n \ge 1$, if a smooth field $v$ on $\mathbb R^{n+1}$ has $v(z) = 0$ with $dv_z$
    non-singular, then $z$ is an isolated zero and
    $\operatorname{index}_z(v) = \operatorname{sgn} \det dv_z$, that is $+1$ or $-1$ according as
    the determinant is positive or negative.
86. (V6.11) An integral over a fixed interval depends smoothly on a parameter: for $h$ of class
    $C^n$ on $E \times \mathbb R$, with $E$ a real normed space and the target complete,
    $x \mapsto \int_0^1 h(x, t)\,dt$ is $C^n$. Hence Hadamard's lemma: a smooth $f$ with $f(0) = 0$
    factors as $f(x) = L(x)\,x$ with $L$ smooth and $L(0) = df_0$, so $t^{-1} f(tx)$ extends
    smoothly over $t = 0$ with value $df_0(x)$.
87. (V6.12) Every diffeomorphism of a finite-dimensional real normed space whose Jacobian
    determinant is positive at one point, equivalently at every point, is smoothly isotopic to the
    identity, by an isotopy every one of whose time slices is a diffeomorphism.
88. (V6.13) For a compact nonempty submanifold $N \subseteq \mathbb R^{K+1}$, the derivative at a
    point $q$ of $N$ of the nearest-point retraction is the orthogonal projection onto $T_qN$; at a
    zero $q$ of a smooth tangent field $v$ on $N$ the derivative of $v$ carries $T_qN$ into itself;
    and the derivative there of the extended field $w = v \circ r + (\mathrm{id} - r)$ is $dv_q$ on
    $T_qN$ and the identity on $(T_qN)^\perp$, so its determinant is the determinant of $dv_q$
    restricted to $T_qN$.
89. (V6.14) For a compact nonempty $N \subseteq \mathbb R^{K+1}$ of dimension $n \ge 2$, Milnor's
    index of a smooth tangent field $v$ at $q$, computed in a local parametrization of $N$, depends
    neither on the parametrization nor on the extension of the pulled-back field; and at a zero $q$
    where the restriction of $dv_q$ to $T_qN$ is invertible it equals the index of the extended
    field ($K \ge 1$), both being the sign of the determinant of that restriction.
90. (V6.15) For $n \ge 1$, every smooth tangent field on $S^n$ with finitely many zeros has index
    sum $1 + (-1)^n$, and any integer having that property for all such fields equals $1 + (-1)^n$;
    for $n$ odd the value $0$ also follows from the existence of a nowhere-zero field.
91. (V7.18) A manifold is orientable if it carries an orientation in the sense of item 24. The
    derivative of a chart transports orientations from one point of its source to another; a chain
    of such charts transports along its hops, composites and reverses behaving as they should; a
    chain-loop reverses if its transport reverses an orientation at the base point. On a connected
    manifold with no reversing chain-loop an orientation exists, and a connected non-orientable
    manifold has a reversing chain-loop at every point; a connected orientable manifold has exactly
    two orientations. The converse — that an orientable manifold has no reversing chain-loop —
    fails for orientations in the sense of item 24 and holds for those coherent with each chart on
    the whole of its source.
92. (V7.19) Transport along a hop through a *round* chart ball carries any orientation of the
    manifold at one end to its value at the other. Hence, for a connected boundaryless manifold and
    any base point, the manifold is orientable **if and only if** no loop of chart balls at that
    point reverses; and a connected non-orientable manifold carries a reversing loop of chart balls
    at every point.
93. (V7.20) The chart sign of a frame at a point — the determinant sign of the frame read in a
    chart — mentions no orientation, is $\pm 1$ for a tangent independent frame, and factors as the
    Jacobian sign of the chart times the self sign. The sign of a frame against an orientation of
    the manifold (item 57) is the self sign times a factor depending only on the point; frames of
    both chart signs exist at every point; and a frame may be carried to another point of the same
    chart with the same chart sign.
94. (V7.21) Transport along a chain of charts is multiplication by a sign, the product over the
    hops of the two Jacobian signs of each hop's chart at its endpoints; the sign of a composite is
    the product, a chain and its reverse have the same sign, and a loop reverses exactly when its
    sign is $-1$. For two fixed charts the product of their Jacobian signs is locally constant in
    the point, although neither factor is. For a boundaryless model, any two points of an open
    preconnected set are joined by a chain of balls whose closed chart balls lie in that set, hence
    avoiding every set disjoint from it.
95. (V7.22) For $m \ge 2$: a punctured chart ball is connected, and so is the complement of a
    finite set in a connected $m$-manifold; a family of orientations of the tangent spaces which is
    coherent along the ball hops of that complement agrees off the finite set with an orientation of
    the whole manifold; and consequently a connected non-orientable $m$-manifold has, at every
    point outside a given finite set, a loop of chart balls at that point avoiding the set and of
    chain sign $-1$. The hypothesis $m \ge 2$ is sharp.
96. (V7.23) For $m \ge 1$, sliding a point of a framed $0$-manifold along a chain of chart balls
    that avoids the other points yields a framed cobordant framed $0$-manifold with that point
    moved to the far end, the other frames unchanged, and self sign there multiplied by the chain
    sign. Around a loop of chain sign $-1$ the point returns to itself with its frame's sign
    reversed. With such a loop available the frame at a point may be replaced by any tangent
    independent frame, and the point moved anywhere in its component of the complement of the
    others.
97. (V7.24) For $m \ge 1$ and with reversing loops available off every finite set: two framed
    $0$-manifolds with the same points and the same frames away from two of them are framed
    cobordant, with no condition on the frames at those two; any two distinct points, one in the
    closure of the component of the other, can be cancelled; and if the point set has two points
    and $M$ is connected, some two of them are such a pair.
98. (V7.25) For $m \ge 1$ and $M$ compact connected, with reversing loops available off every
    finite set, two framed $0$-manifolds whose numbers of points agree modulo $2$ are framed
    cobordant; and the number of points modulo $2$ of the Pontryagin manifold of $f : M \to S^m$ at
    a regular value is the degree of $f$ modulo $2$, for any independent frame.
99. (V7.26) Let $M \subseteq \mathbb R^{K+1}$ be a compact nonempty connected non-orientable
    submanifold of dimension $m$. Two smooth maps $M \to S^m$ are smoothly homotopic
    if and only if they have the same degree modulo $2$. **No hypothesis on $m$ is assumed.** Each
    half of the proof wants $m \ge 1$, and $m \ge 2$ is what item 95 wants; both follow from
    non-orientability, by item 110.
100. (V.B) Let $A$ and $A'$ be arcs of a Hausdorff space relative to a set $B$ — homeomorphisms of
     open subsets onto bounded intervals of $\mathbb R$ with at least two points, carrying exactly
     the points of $B$ to the endpoints of those intervals. Then the set of $A$-parameters of the
     points lying in both sources has at most two maximal subintervals; if it has two, they reach
     opposite ends of $A$'s interval; and if one of them has both its ends interior to $A$'s interval
     then it is the only one, so the set is a single interval. This is Milnor's Appendix Lemma 1
     without its affine clause, the two-interval case being his circle. No smoothness, no charts, no
     compactness, no dimension hypothesis.
101. (V.C) Let $M$ be a $C^1$ manifold charted on a model with corners whose model vector space is
     one-dimensional. Then the model's range is the whole line, a closed half-line, or a
     nondegenerate compact interval; derivatives along that range are unique, so one-sided
     derivatives at an endpoint of it are unambiguous; a point in the source of **any** chart of the
     atlas is a boundary point exactly when its real coordinate lies on the frontier of the range, so
     the boundary does not depend on the chart; consequently, when the range is a half-line, every
     chart carries exactly the boundary points of its source to the endpoint of the range — which is
     the hypothesis item 13 has to assume, and it is here a theorem; and every boundary point has a
     chart-derived real coordinate onto $[0, \varepsilon)$ sending it to $0$, every interior point one
     onto $(-\varepsilon, \varepsilon)$, smooth in both directions.
102. (V.D) Let $M$ be a $C^n$ manifold, $n \ge 1$, with one-dimensional model vector space, and call
     an arc *smooth* when its coordinate and its parametrization are both $C^n$, the latter on a
     possibly half-open interval. Then the transition between two smooth arcs is $C^n$ where it is
     defined, the two transition derivatives are reciprocal so neither vanishes, a smooth arc is an
     immersion, and every point of $M$ lies in the source of a smooth arc sending it to $0$, with
     interval $[0, \varepsilon)$ if it is a boundary point and $(-\varepsilon, \varepsilon)$ if not.
     Neither Hausdorffness nor compactness is assumed.
103. (V.E) Let $M$ be a Hausdorff $\sigma$-compact $C^\infty$ manifold with one-dimensional model
     vector space. Then $M$ carries a **length element**: an assignment to each local real parameter
     of a positive $C^\infty$ density, transforming by the absolute value of the derivative of the
     transition — which in dimension one is what a Riemannian metric is. Hence every point of $M$
     lies in the source of a **unit-speed** smooth arc sending it to $0$, one in whose parameter the
     density is identically $1$, with interval $[0, \varepsilon)$ at a boundary point and
     $(-\varepsilon, \varepsilon)$ elsewhere. This is Milnor's "by a straightforward change of
     variables". Hausdorffness and $\sigma$-compactness are used for the length element and for
     nothing else. Two supporting statements of real analysis: the one-sided inverse function rule,
     and the fact that arc length on a compact interval and its inverse are $C^\infty$ at the
     endpoints included.
104. (V.F) Let $M$ be a Hausdorff one-manifold with a length element. The transition between two
     unit-speed smooth arcs has derivative of absolute value $1$ at every parameter of the overlap,
     endpoints included, hence constant sign on each maximal subinterval of the overlap, hence is
     $s \mapsto \pm s + k$ there; with item 100 this is **Milnor's Appendix Lemma 1 in full**. And if
     the first of two unit-speed smooth arcs starts at a boundary point with coordinate $0$, the two
     glue to a unit-speed smooth arc whose source is the union of the two sources and whose
     coordinate *equals* the first arc's on the whole of the first source.
105. (V.G) A compact Hausdorff connected $C^\infty$ one-manifold with a boundary point $p$ is
     $C^\infty$-diffeomorphic to $[0, 1]$, and its boundary is exactly two points, $p$ and the far end
     of the arc-length parametrization that exhausts it. Without connectedness, that parametrization
     exhausts the connected component of $p$ and identifies the two boundary points inside it. No
     countability hypothesis is needed: compactness supplies what is wanted.
106. (V.H) A nonempty compact Hausdorff connected $C^\infty$ one-manifold with **empty boundary** is
     $C^\infty$-diffeomorphic to the circle. On the way it is a closed geodesic: there are a length
     element, a least period $T > 0$ and a unit-speed map of the line onto the manifold which
     identifies two times exactly when they differ by an integer multiple of $T$.
107. (V.I) A connected Hausdorff $\sigma$-compact **non-compact** $C^\infty$ one-manifold is
     $C^\infty$-diffeomorphic to $\mathbb R$ if its boundary is empty, and to $[0, \infty)$ if it has
     a boundary point — which is then its only boundary point. $\sigma$-compactness is used once and
     once only, to build the length element of item 103.
108. (V.J) **Milnor's Appendix theorem.** A connected Hausdorff $\sigma$-compact nonempty $C^\infty$
     one-manifold is $C^\infty$-diffeomorphic to **exactly one** of the circle, $[0, 1]$,
     $[0, \infty)$ and $\mathbb R$, according as it is compact or not and its boundary is empty or
     not; and the four are pairwise non-diffeomorphic, compactness settling four of the six
     exclusions and the number of boundary points — $0$, $2$, $1$, $0$, a diffeomorphism invariant —
     the other two. In Chapter 2's language: for a compact one-manifold with boundary $B$, every
     connected component is diffeomorphic to the circle or to $[0, 1]$, the components meeting $B$ are
     exactly those of the second kind, each of those meets $B$ in exactly two points, and $B$ is
     finite of even cardinality — this last **derived from the classification**, as Milnor derives it,
     and not from the involution argument of items 13 and 14, which is left in place and is still what
     Chapters 2 and 4 use. $\sigma$-compactness cannot be dropped: the long line is a connected
     Hausdorff smooth one-manifold without boundary diffeomorphic to none of the four.
109. (V7.27) An invertible linear map between spaces of the same finite dimension carries exactly one
     orientation of its source to a given orientation of its target. A smooth map between manifolds of
     the same dimension whose derivative is everywhere invertible pulls an orientation of the target
     back to an orientation of the source, provided the model of the **source** is boundaryless; it
     need be neither injective nor surjective. Every $0$-dimensional manifold is orientable, and each
     of the circle, $[0, 1]$, $[0, \infty)$ and $\mathbb R$ is orientable — the unit interval not by a
     constant family of orientations, its two charts having an orientation-reversing transition.
     Hence **every connected Hausdorff $\sigma$-compact smooth one-manifold over a boundaryless model
     is orientable.**
110. (V7.28) A connected Hausdorff $\sigma$-compact smooth manifold of dimension $m$ over a
     boundaryless model which is **not** orientable has $m \ge 2$; in particular a compact connected
     non-orientable submanifold of a Euclidean space has dimension at least two, where every side
     hypothesis is automatic. This is what deletes the dimension hypothesis from item 99, and it is
     what makes the formal statement of Milnor's theorem of p. 50 match his own, which carries no
     dimension condition.

Items 1–12 were signed off in the first session, items 13–17 in the second, 18–23 in the third,
24–33 in the fourth, 34–44 in the fifth; items 45–62 (Chapter 7) and 63–83 (Chapter 8) were new two
revisions ago, and items 84–99 in the previous revision: 84 belongs to Chapter 2, 85–90
to Chapter 6 and 91–99 to Chapter 7. The wording of the previously signed items 9, 10, 15, 16, 20,
36, 38, 41 and 44 was changed in the previous revision to match corrected statements, so these
need to be signed again; items 45, 49, 55, 57, 58, 59, 60, 62 and 82 were also reworded before
their first signature. In the present revision items 100–110 are new: 100–108 belong to the Appendix
and 109–110 to Chapter 7. One previously signed item was reworded, item 99, which lost the dimension
hypothesis it used to carry and to describe as vacuous, so it needs to be signed again. Nothing was
renumbered.
