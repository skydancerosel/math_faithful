# Morse Theory, verified: the machine-checked edition

*A companion to "Morse Theory, Rewritten", the expanded edition of J. Milnor's* Morse Theory
*(Princeton, 1963). That edition is written to be read; this one is written to be checked. It
records, chapter by chapter, exactly which statements of the book have been verified by the Lean 4
proof assistant against the Mathlib library and the formalization of Milnor's* Topology from the
Differentiable Viewpoint *(the companion project), what each verified statement says when read back
in ordinary language, which hypotheses the book left silent, where the formal statement or proof
departs from the book's, and what remains unverified and why. Nothing here needs to be read in
Lean; every checked statement is restated in prose, and the Lean names are given only so that the
claims can be audited.*

**Where to start.** The project has three parts:

- *Morse Theory, Rewritten*, the book for reading;
- *Morse Theory, Checked*, the Lean formalization and the reports on it;
- *Morse Theory, the Shortest Path*, the main theorems and exactly what their formal proofs use.

This edition is the way into the second part. Its four reports each answer one question:

- **What is proved?** This edition: every checked result in plain language, with all its
  hypotheses, and the list of statements to sign off.
- **How is it proved?** *Morse Theory, proof by proof* (`Exposition/ProofByProof.md`): the formal
  proofs retold as mathematics, with a trace tag on each step naming the Lean declaration that
  carries it.
- **How does it differ from Milnor?** *Morse Theory beside Lean*, the comparison
  (`Exposition/morse-beside-lean.html`): each result of the book beside the checked statement, with
  a verdict (the same, restated, hypotheses made explicit, stronger, narrower) and the differences.
- **Are the comparison's verdicts right?** The round-trip audit (`RoundTrip/REPORT.md`): Milnor's
  statements are formalized blind, without sight of the project's Lean, and proved equivalent, or
  not, to the checked ones; the definitions under the main theorems are checked against blind
  textbook definitions in the same way.

A result has the same number, V2.8 say, in this edition, the comparison, the rewritten book's notes
and the shortest path.

---

## 0. Summary

| Chapter | Milnor | Content | Status | Lean lines |
|:--|:--|:--|:--|--:|
| Chapter 1 | §§1–2 | critical points, Hessian and index, the Morse lemma, flows (Lemma 2.4) | **partly verified** | 4,572 |
| Chapter 2 | §3 | Theorems 3.1, 3.2, 3.5, Lemmas 3.6–3.7, Remarks 3.3–3.4 | **partly verified** | 6,359 |
| Chapter 3 | §§4–5 | Reeb's theorem, the torus, the Morse inequalities in singular homology, the Euler characteristic | **partly verified** | 13,353 |
| Chapter 4 | §6 | focal points, existence and density of Morse functions, compact abstract manifolds | **partly verified** | 3,720 |
| Chapter 5 | §7 | the index bound behind the Lefschetz theorem | **partly verified** | 2,804 |
| Chapter 6 | §§8–9 | connections, parallel transport and curvature, for submanifolds of $\mathbb R^K$ | **partly verified** | 3,346 |
| Chapter 7 | §10 | geodesics, the exponential map, the Gauss lemma, the Hopf–Rinow theorem | **partly verified** | 5,962 |
| Chapter 8 | §§11–13 | the path space, the energy, the first and second variation formulas | **partly verified** | 4,064 |
| Chapter 9 | §§14–15 | Jacobi fields and the index theorem | **partly verified** | 5,288 |
| Chapter 10 | §§16–17 | the finite-dimensional approximation, the full path space | **partly verified** | 13,564 |
| Chapter 11 | §§18–19 | non-conjugate points, topology and curvature | **partly verified** | 4,322 |
| Chapter 12 | §§20–21 | bi-invariant metrics, matrix groups, their geodesics and curvature | **partly verified** | 3,922 |
| Chapter 13 | §22 | manifolds of minimal geodesics, Freudenthal's theorem | **partly verified** | 3,048 |
| Chapter 14 | §23 | Bott periodicity for the unitary group | **partly verified** | 2,106 |
| Chapter 15 | §24 | Bott periodicity for the orthogonal group | **partly verified** | 9,682 |
| Appendix | Appendix | the homotopy type of a monotone union | **partly verified** | 2,720 |

Total: 88,832 lines of Lean in 216 files under `Morse/` (`wc -l`, excluding unfinished `WIP_` files), on top of the companion project. Toolchain: Lean 4.33.1, Mathlib 4.33.1. To reproduce: `lake build`, then `lake env lean -DmaxSynthPendingDepth=3 Morse/Test.lean`, which prints the axioms of every main theorem. Edition of 5 November 2026.

---

## 1. How to read a verified statement

**The statements are the contract.** A machine-checked proof guarantees that the *stated* theorem
follows from Lean's axioms. It guarantees nothing about whether the statement is the one Milnor
meant. The reader's job, and the only mathematical judgement this document asks for, is to read
each prose restatement and confirm that it says what the book means. Where the restatement is
weaker or stronger than the book, or uses a different but equivalent definition, this is flagged as
a **Deviation**.

**Three settings.** Mathlib's manifolds are abstract spaces with atlases. The results of §2 are
proved for abstract manifolds. Most of Part I is proved for submanifolds of a Euclidean space in the
sense of the companion project (subsets with slice charts), and carried to abstract *compact*
manifolds through Mathlib's Whitney embedding theorem; non-compact abstract manifolds would need a
Whitney embedding that Mathlib does not have. Part II, and Part III as far as it is verified
(§§11–19), are verified for submanifolds of $\mathbb R^K$ with the induced metric (every
Riemannian manifold is such a submanifold by Nash's theorem, which is quoted, not proved); Part IV
(§§20–24) for compact groups of matrices and the spaces $\Omega_k(n)$ of §24, as submanifolds of a
space of matrices, and in its algebraic cores; the Appendix for arbitrary topological spaces.
Homology is Mathlib's singular homology, extended here by relative homology, the exact sequences of
pairs and triples, and excision (Chapter 3).

**What "smooth" means.** Smooth means $C^\infty$. Hausdorffness and second countability, which
Milnor uses silently, are explicit hypotheses wherever they are needed; submanifolds of a Euclidean
space have both automatically.

**Axioms.** Every verified theorem depends only on the three standard axioms of Lean's Mathlib
(`propext`, `Classical.choice`, `Quot.sound`), as `Morse/Test.lean` prints; there is no `sorry`.

---

## 2. Chapter 1 (Milnor §§1–2): partly verified

Milnor's §1 introduces the subject through the height function on a torus standing on a plane; §2
defines critical points, the Hessian, the index and the nullity, proves Hadamard's lemma (Lemma 2.1)
and the Morse lemma (Lemma 2.2), states that non-degenerate critical points are isolated (Corollary
2.3), lists examples of degenerate critical points, and proves that a compactly supported vector
field generates a one-parameter group of diffeomorphisms (Lemma 2.4). All of §2 is verified except
the remark of p. 4 that regular sublevel sets are manifolds with boundary, the vector-field form of
the Hessian, example (b), Lemma 2.4 on a manifold that is not a vector space, and the closing remark
of p. 11. The definitions, Corollary 2.3 and the Morse lemma are verified in two settings: on a real
normed space $E$ (finite-dimensional wherever dimensions are counted), which is Milnor's situation
after a choice of coordinates, and on an abstract smooth manifold without boundary modelled on such
an $E$, with no Hausdorff or countability hypothesis. For a function $F|N$ on a slice submanifold
$N$ of a Euclidean space, in the sense of the companion project, they are computed in slice
parametrizations (V1.6); this is the setting of most of Chapter 2. Lemma 2.4 is verified on a
complete real normed space, together with the smooth dependence of solutions on the initial point,
which Milnor quotes. Of §1, the critical points of the torus, their indices, and Milnor's cases (1)
and (5) are verified for an explicit torus of revolution; the identification of the intermediate
sublevel sets and the cell attachments are not.

**V1.1 (the torus of §1; `Morse.torus`, `Morse.Torus.isCriticalPointM_height_iff`,
`Morse.Torus.pointP_spec`, `Morse.Torus.pointQ_spec`, `Morse.Torus.pointR_spec`,
`Morse.Torus.pointS_spec`, `Morse.Torus.sublevel_height_eq_empty`,
`Morse.Torus.sublevel_height_eq_univ`, `Morse.theorem_3_1_torus`).** Let $0 < \rho < R$ and let
$T \subseteq \mathbb R^3$ be the torus $(\sqrt{x_1^2 + x_2^2} - R)^2 + x_3^2 = \rho^2$, whose axis
of revolution is the $x_3$-axis; it is a compact slice submanifold of dimension $2$ (V1.6). Let
$f(x) = x_1 + R + \rho$, the height above the plane $x_1 = -(R + \rho)$, which touches $T$ at
$p = (-(R + \rho), 0, 0)$. Then $f|T$ has exactly four critical points, $p$,
$q = (-(R - \rho), 0, 0)$, $r = (R - \rho, 0, 0)$ and $s = (R + \rho, 0, 0)$, at the heights $0$,
$2\rho$, $2R$ and $2R + 2\rho$; all four are non-degenerate (V1.4), of indices $0$, $1$, $1$, $2$;
$T^a = \emptyset$ for $a < 0$ and $T^a = T$ for $a \ge 2R + 2\rho$; and if $a \le b$ and $[a, b]$
contains none of the four heights, a $C^\infty$ diffeomorphism of $T$ carries $T^a$ onto $T^b$,
$T^a$ is a strong deformation retract of $T^b$ (V2.1), and the inclusion $T^a \to T^b$ is a homotopy
equivalence. *Book:* pp. 1–3: for the torus of Diagram 1, tangent to the plane $V$, with $f$ the
height above $V$, the sublevel set $M^a$ is successively empty, a 2-cell, a cylinder, a compact
genus-one surface bounded by a circle, and all of $M$ as $a$ passes the values of $f$ at $p$, $q$,
$r$, $s$; these four points are the critical points, with normal forms $x^2 + y^2$ at $p$, const
$+ x^2 - y^2$ at $q$ and $r$, const $- x^2 - y^2$ at $s$. *Hidden hypotheses:* the torus must stand
on the plane with its axis parallel to it, and $\rho < R$; lying flat, its height function has two
circles of degenerate critical points. *Deviation (value differs):* case (1) reads $a < 0 < f(p)$ in
the scan, whereas $f(p) = 0$; the hypothesis is $a < 0$. *Deviation (narrower):* cases (2)–(4) and
the cell attachments are not verified; between critical heights only Theorem 3.1 (V2.3) is applied.
The Lean file is `Morse/Chapter3/Torus.lean`, since its proofs use Theorem 3.1 on submanifolds. The details, with their own sign-off items, are V3.22–V3.25 in Chapter 3.

**V1.2 (attaching a cell; `Morse.AttachCell`, `Morse.cellDesc`).** For a topological space $X$, an
integer $n \ge 0$ and a continuous map $\varphi : S^{n-1} \to X$, the space $X \cup_\varphi e^n$ is
the pushout, in the category of topological spaces, of $\varphi$ and the inclusion of the unit
sphere $S^{n-1}$ in the closed unit ball $D^n$ of $\mathbb R^n$: the quotient of the disjoint union
$X \sqcup D^n$ by the identification of each $u \in S^{n-1}$ with $\varphi(u)$, so that a map out of
it is a pair of maps on $X$ and on $D^n$ which agree along $\varphi$. For $n = 0$ the sphere is
empty and $D^0$ is a point. The disk and the sphere are Mathlib's, those of its CW complexes.
*Book:* pp. 2–3, the same definition (the topological sum of $Y$ and $e^k$ with each $x \in S^{k-1}$
identified with $g(x)$), with the same convention for $k = 0$. *Hidden hypotheses:* none.

**V1.3 (critical points, Hessian, index and nullity in coordinates; `Morse.IsCriticalPoint`,
`Morse.hessian`, `Morse.hessian_symm`, `Morse.nullSpace`, `Morse.nullity`, `Morse.index`,
`Morse.index_isGreatest`, `Morse.IsNondegenerate`, `Morse.isNondegenerate_iff_nullity_eq_zero`,
`Morse.IsNondegenerateCriticalPoint`, `Morse.isNondegenerate_hessian_iff_det_ne_zero`).** Let $E$ be
a real normed space and $f : E \to \mathbb R$. A point $p$ is a *critical point* of $f$ if $f$ is
differentiable at $p$ with derivative $0$. The *Hessian* of $f$ at $p$ is the second derivative
$d^2 f_p$, a continuous bilinear form on $E$, symmetric when $f$ is $C^2$ at $p$; it is defined at
every point but only used at critical points. For a continuous bilinear form $H$ on $E$, the *null
space* is $\{v : H(v, w) = 0 \text{ for all } w\}$, the *nullity* is its dimension, $H$ is
*non-degenerate* if its null space is $0$, and the *index* of $H$ is the negative index of inertia
of the quadratic form $v \mapsto H(v, v)$, which for finite-dimensional $E$ is the largest dimension
of a subspace on which $H(v, v) < 0$ for all $v \ne 0$. A *non-degenerate critical point* is a
critical point at which $d^2 f_p$ is non-degenerate. For finite-dimensional $E$, non-degenerate
means nullity $0$; for $E = \mathbb R^n$ and $f$ of class $C^2$ at $p$, it means that the matrix
$(\partial^2 f/\partial x^i\partial x^j(p))$ is non-singular. *Book:* pp. 4–5: critical points
($f_* = 0$, restated in local coordinates; the display is lost in the scan), non-degeneracy (the
matrix of second partial derivatives is non-singular), the index and nullity of a bilinear
functional, and the remark that a critical point is non-degenerate exactly when the nullity is $0$.
*Hidden hypotheses:* none. *Deviation (restated):* the index is defined as Mathlib's negative index
of inertia (`sigNeg`), and Milnor's definition as a maximum is a theorem (`Morse.index_isGreatest`);
non-degeneracy is defined by a zero null space, and Milnor's matrix definition is a theorem.

**V1.4 (the same on a manifold, and Morse functions; `Morse.IsCriticalPointM`, `Morse.hessianM`,
`Morse.indexM`, `Morse.nullityM`, `Morse.IsNondegenerateCriticalPointM`, `Morse.IsMorseFunction`,
`Morse.isCriticalPointM_iff_milnor`).** Let $M$ be a smooth manifold without boundary modelled on a
real normed space $E$, with no Hausdorff or countability hypothesis, $f : M \to \mathbb R$ and
$p \in M$. The point $p$ is a *critical point* of $f$ if the derivative $df_p : T_pM \to \mathbb R$
is $0$; equivalently, $df_p$ is not surjective, which is the companion project's definition. The
*Hessian* $f_{**}$ at $p$ is the second derivative at $\kappa(p)$ of $f\circ\kappa^{-1}$, where
$\kappa$ is the preferred chart at $p$: a bilinear form on $E$, which Mathlib identifies with $T_pM$
through the same chart. The index and the nullity of $f$ at $p$ are those of $f_{**}$, and $p$ is a
non-degenerate critical point if it is critical and $f_{**}$ is non-degenerate (V1.3). A *Morse
function* is a $C^\infty$ function on $M$ all of whose critical points are non-degenerate. *Book:*
pp. 4–5; the Morse functions are the differentiable functions with no degenerate critical points of
Theorem 3.5 (p. 20). *Hidden hypotheses:* none. *Deviation (restated):* Milnor defines
$f_{**}(v, w) = \tilde v_p(\tilde w(f))$ for vector fields $\tilde v$, $\tilde w$ extending $v$,
$w$, and checks that this is symmetric and independent of the extensions. That formula is not
formalized: the formal definition is his coordinate expression (the matrix of second partial
derivatives, p. 5, which is his formula for extensions with constant coefficients), and its
independence of the extensions is replaced by its independence of the chart (V1.5). Mathlib's
derivative is $0$ at a point where $f$ is not differentiable, so such a point counts as critical;
for smooth $f$ this never matters.

**V1.5 (independence of the coordinate system; `Morse.hessian_comp`, `Morse.IsSmoothCoord`,
`Morse.isSmoothCoord_iff_mem_maximalAtlas`, `Morse.IsSmoothCoord.isCriticalPointM_iff`,
`Morse.IsSmoothCoord.isCriticalPointM_iff_forall_partial`, `Morse.IsSmoothCoord.hessian_comp_symm`,
`Morse.IsSmoothCoord.isNondegenerate_iff`, `Morse.IsSmoothCoord.index_eq`,
`Morse.IsSmoothCoord.nullity_eq`, `Morse.IsSmoothCoord.isNondegenerate_iff_det_ne_zero`).** On
normed spaces: if $\psi$ is $C^2$ at $q$, $f$ is $C^2$ at $\psi(q)$ and $df_{\psi(q)} = 0$, then
$d^2(f\circ\psi)_q(v, w) = d^2 f_{\psi(q)}(d\psi_q v, d\psi_q w)$. On $M$ as in V1.4: a *smooth
coordinate system* is a homeomorphism $y$ of an open subset of $M$ onto an open subset of a real
normed space $E'$ which is $C^\infty$ with $C^\infty$ inverse (for $E' = E$ these are exactly the
charts of the maximal atlas). Let $p$ lie in the domain of $y$. If $f$ is differentiable at $p$,
then $p$ is critical if and only if $y(p)$ is a critical point of $f\circ y^{-1}$, that is, for
$E' = \mathbb R^n$, if and only if all the partial derivatives $\partial f/\partial y^i(p)$ vanish.
If $f$ is $C^2$ at $p$ and $p$ is critical, the Hessian of $f\circ y^{-1}$ at $y(p)$ is $f_{**}$
composed in both arguments with the derivative of $y^{-1}$ at $y(p)$ (the matrix
$(\partial^2 f/\partial y^i\partial y^j(p))$ represents $f_{**}$ in the basis
$\partial/\partial y^i|_p$); hence non-degeneracy, index and nullity are those of $f\circ y^{-1}$ at
$y(p)$, and for $E' = \mathbb R^n$, $p$ is non-degenerate if and only if
$\det(\partial^2 f/\partial y^i\partial y^j(p)) \ne 0$. *Book:* p. 4, non-degeneracy "can be checked
directly" not to depend on the coordinate system; p. 5, the matrix of second partial derivatives
represents $f_{**}$. *Hidden hypotheses:* none. *Deviation (stronger):* $f$ need only be $C^2$ at
$p$, and the coordinates may take values in any normed space. Criticality is used exactly once, to
kill the first-order term $df(d^2\psi)$ of the chain rule.

**V1.6 (functions on a slice submanifold; `Milnor.IsSliceSubmanifold`, `Morse.sliceParam`,
`Morse.tangentSubspace`, `Morse.tangentSubspace_eq_range_fderiv_sliceParam`,
`Morse.isCriticalPointM_comp_val_iff_sliceParam`,
`Morse.isCriticalPointM_comp_val_iff_forall_tangent`,
`Morse.isCriticalPointM_comp_val_iff_gradient_mem_orthogonal`, `Morse.hessian_comp_sliceParam`,
`Morse.index_hessian_comp_sliceParam`, `Morse.nullity_hessian_comp_sliceParam`,
`Morse.isNondegenerateCriticalPointM_comp_val_iff_sliceParam`,
`Morse.isCriticalPointM_normSq_sub_iff`, `Morse.hessian_normSq_sub_comp`,
`Morse.indexM_normSq_sub_eq`, `Morse.nullityM_normSq_sub_eq`).** This is the setting of every later
statement about a submanifold of Euclidean space. $V$ is a real normed space (Milnor's
$\mathbb R^K$) and $N \subseteq V$ is a slice submanifold modelled on $Z$ in the sense of the
companion project: every point of $N$ lies in the domain of a slice chart, a $C^\infty$
diffeomorphism $\sigma$ of an open subset of $V$ onto an open subset of $Z \times W$ which carries
the points of $N$ in its domain exactly onto $Z \times \{0\}$. $N$ need not be closed; it is a
smooth manifold modelled on $Z$, with the charts $q \mapsto \sigma(q)_1$ and the parametrizations
$x(z) = \sigma^{-1}(z, 0)$. Let $T_qN \subseteq V$ be the range of the derivative of the inclusion
$N \to V$ at $q$; it is the range of $dx$. Let $F : V \to \mathbb R$ and let $q \in N$ lie in the
domain of $\sigma$. If $F$ is differentiable at $q$, then $q$ is a critical point of $F|N$ if and
only if $\sigma(q)_1$ is a critical point of $F\circ x$, if and only if $dF_q$ vanishes on $T_qN$,
and, when $V$ is a complete inner product space, if and only if $\nabla F(q) \perp T_qN$. If $F$ is
$C^2$ at $q$ and $q$ is critical for $F|N$, the Hessian of $F\circ x$ at $\sigma(q)_1$ is $f_{**}$
composed with the derivative of the parametrization, so non-degeneracy, index and nullity of $F|N$
at $q$ are those of $F\circ x$. For $V$ an inner product space and $L_p(y) = \|y - p\|^2$: $q$ is a
critical point of $L_p|N$ if and only if $q - p \perp T_qN$; for any $x$ of class $C^2$ at $u$, the
second derivative of $L_p\circ x$ at $u$ is $2(\langle \partial x/\partial v, \partial x/\partial
w\rangle + \langle \partial^2 x/\partial v\,\partial w, x(u) - p\rangle)$; and at a critical point
$q$ the index and the nullity of $L_p|N$ are those of this form at $u = \sigma(q)_1$. *Book:* §2 is
written for abstract manifolds, and the reduction to a parametrization is used without comment
later; the statements on $L_p$ are Milnor's criterion of p. 35 and his formula of p. 36 (§6), proved
in this chapter's files. *Hidden hypotheses:* none. *Deviation (not in the book):* the
identifications themselves. The Hessian of $F\circ x$ is not the restriction of the ambient Hessian
of $F$: the chain rule adds $dF_q(\partial^2 x/\partial v\,\partial w)$, which does not vanish at a
critical point of $F|N$ and which, for $L_p$, is the second-fundamental-form term of Milnor's
formula.

**V1.7 (Lemma 2.1, Hadamard's lemma; `Morse.exists_hadamard_coord`, `Morse.exists_hadamard_on`,
`Morse.exists_hadamard_two_on`, `Morse.contDiffOn_intervalIntegral`).** Let
$V \subseteq \mathbb R^n$ be open and convex with $0 \in V$, and $f$ smooth on $V$ with $f(0) = 0$.
Then $f(x) = \sum_i x_i g_i(x)$ on $V$ for some functions $g_i$ smooth on $V$ with
$g_i(0) = \partial f/\partial x_i(0)$. More generally, let $V$ be open and star-shaped about $0$ in
a real normed space $E$ and $f$ smooth on $V$, with values in a complete normed space and
$f(0) = 0$. Then $f(x) = L(x)\,x$ on $V$ for a family of linear maps $L$ smooth on $V$ with
$L(0) = df_0$; and if moreover $df_0 = 0$, then $f(x) = B(x)(x, x)$ on $V$ for a family of bilinear
maps $B$ smooth on $V$, with $B(x)$ symmetric for each $x \in V$ and $B(0) = \tfrac12 d^2 f_0$. (The
proofs take $L(x) = \int_0^1 df_{tx}\,dt$ and $B(x) = \int_0^1 (1 - t)\, d^2 f_{tx}\,dt$.) *Book:*
p. 5, Lemma 2.1, for $f$ smooth in a convex neighbourhood $V$ of $0$ in $\mathbb R^n$; on p. 7
Milnor applies it twice, symmetrizes, and asserts without proof that the coefficients at $0$ are
$\tfrac12\,\partial^2 f/\partial x^i\partial x^j(0)$, which is the second-order form. *Hidden
hypotheses:* $V$ open; and the smoothness of the $g_i$, which the book does not argue, is
differentiation under the integral sign on an open set (`Morse.contDiffOn_intervalIntegral`: if $h$
is $C^n$ on an open $U \subseteq E \times \mathbb R$ containing $V \times [0, 1]$, $V$ open, then
$x \mapsto \int_0^1 h(x, t)\,dt$ is $C^n$ on $V$). *Deviation (stronger):* star-shaped instead of
convex, any normed source and any complete target. *Proof:* the second-order form is Taylor's
formula with integral remainder rather than two applications of Lemma 2.1, which makes the value
$B(0) = \tfrac12 d^2 f_0$ immediate.

**V1.8 (Lemma 2.2, the Morse lemma; `Morse.morse_lemma`, `Morse.exists_morse_chart`,
`Morse.morse_lemmaM`, `Morse.exists_morse_chartM`).** Let $E$ be a finite-dimensional real normed
space, $n = \dim E$, $f$ smooth on an open set $U \ni p$, and $p$ a critical point at which
$d^2 f_p$ is non-degenerate, of index $\lambda$. Then there is a homeomorphism $y$ of an open
neighbourhood $U' \subseteq U$ of $p$ onto an open subset of $\mathbb R^n$, $C^\infty$ with
$C^\infty$ inverse, such that $y(p) = 0$ and $f = f(p) - (y^1)^2 - \dots - (y^\lambda)^2 +
(y^{\lambda+1})^2 + \dots + (y^n)^2$ throughout $U'$. In coordinate-free form, there is such a
$\varphi$ onto an open subset of $E$ with $\varphi(p) = 0$, $d\varphi_p = \mathrm{id}$ and
$f = f(p) + \tfrac12 d^2 f_p(\varphi, \varphi)$ on its domain. On a smooth manifold $M$ without
boundary modelled on $E$, with no Hausdorff hypothesis, for $f$ smooth on an open $U \ni p$ and $p$
a non-degenerate critical point of index $\lambda$ (V1.4): there is a smooth coordinate system $y$
of $M$ (V1.5) with values in $\mathbb R^n$, domain an open neighbourhood of $p$ inside $U$,
$y(p) = 0$, and the same normal form on its domain; and there is a chart $\varphi$ of the maximal
atlas, with domain an open neighbourhood of $p$ inside $U$, $\varphi(p) = 0$ and
$f = f(p) + \tfrac12 f_{**}(\varphi, \varphi)$ on its domain. *Book:* p. 6, Lemma 2.2. *Hidden
hypotheses:* none. *Deviation (stronger):* $f$ need only be smooth near $p$. *Proof:* not Milnor's
induction, which completes one square at a time and does not justify the linear change of the
remaining coordinates making $H_{rr}(0) \ne 0$, but one application of the inverse function theorem:
with $f(p + x) - f(p) = B(x)(x, x)$ and $B_0 = \tfrac12 d^2 f_p$ (V1.7), the map $T \mapsto
B_0(T\cdot, T\cdot) + B_0(T\cdot, \cdot) - B_0(\cdot, T\cdot)$ on linear maps of $E$ has invertible
derivative $H \mapsto 2B_0(H\cdot, \cdot)$ at the identity, which yields linear maps $C(x)$, smooth
in $x$, with $C(0) = \mathrm{id}$ and $B(x)(v, v) = B_0(C(x)v, C(x)v)$ (`Morse.exists_sqrt_family`),
so that $\varphi(p + x) = C(x)x$. Sylvester's law of inertia, from Mathlib, then diagonalizes $B_0$
with the negative squares first (`Morse.exists_linearEquiv_diagForm`).

**V1.9 (the index is forced by the normal form; `Morse.index_eq_of_morse_chart`,
`Morse.isNondegenerateCriticalPointM_of_morse_chart`, `Morse.indexM_eq_of_morse_chart`).** On a real
normed space $E$, $n = \dim E$: if $f$ is $C^2$ at a critical point $p$ and $z$ is a homeomorphism
of an open neighbourhood of $p$ onto an open subset of $\mathbb R^n$, $C^\infty$ with $C^\infty$
inverse, with $z(p) = 0$ and $f = f(p) - \sum_{i \le k}(z^i)^2 + \sum_{i > k}(z^i)^2$ on its domain,
$k \le n$, then $k$ is the index of $f$ at $p$. On $M$ as in V1.4, with no hypothesis on $f$: if $z$
is a smooth coordinate system around $p$ with values in $\mathbb R^n$, $z(p) = 0$, $k \le n$, and
$f$ has this form on its domain, then $p$ is a non-degenerate critical point of $f$ of index $k$.
*Book:* p. 6, the first paragraph of the proof of Lemma 2.2. *Hidden hypotheses:* none. *Deviation
(stronger):* on $M$, smoothness, criticality and non-degeneracy are conclusions, not hypotheses. The
proof is Milnor's, with the independence of coordinates (V1.5) that he uses without comment.

**V1.10 (Corollary 2.3; `Morse.IsNondegenerateCriticalPoint.exists_nhds_isCriticalPoint_eq`,
`Morse.IsNondegenerateCriticalPointM.exists_nhds_isCriticalPointM_eq`).** Let $E$ be
finite-dimensional. If $f : E \to \mathbb R$ is $C^2$ at $p$ and $p$ is a non-degenerate critical
point, then $p$ has a neighbourhood in which it is the only critical point of $f$. The same holds on
a manifold $M$ without boundary modelled on $E$, for $f$ of class $C^2$ at $p$. *Book:* p. 8,
Corollary 2.3, stated after Lemma 2.2 without proof. *Hidden hypotheses:* none. *Deviation
(stronger):* only $C^2$ at $p$. *Proof:* not through the Morse lemma: $x \mapsto df_x$ has the
injective derivative $d^2 f_p$ at $p$, so it does not vanish at the points $x \ne p$ near $p$.

**V1.11 (finitely many critical points; `Morse.isClosed_setOf_isCriticalPointM`,
`Morse.isDiscrete_inter_setOf_isCriticalPointM`, `Morse.finite_inter_setOf_isCriticalPointM`,
`Morse.IsMorseFunction.finite_setOf_isCriticalPointM`).** Let $M$ be as in V1.4. The critical set of
a $C^1$ function on $M$ is closed. If $E$ is finite-dimensional and $f$ is $C^2$ with all its
critical points non-degenerate, the critical points of $f$ form a discrete set and every compact set
contains only finitely many of them; in particular a Morse function on a compact $M$ has finitely
many critical points. *Book:* not stated; Milnor uses it on p. 23, where the critical values have no
cluster point because each $M^a$ is compact. *Hidden hypotheses:* none; Hausdorffness is not needed.
*Deviation (not in the book):* a consequence of V1.10 that the book uses silently.

**V1.12 (degenerate critical points, pp. 8–9; `Morse.Examples.cube_degenerate`,
`Morse.Examples.isCriticalPoint_cube_iff`, `Morse.Examples.hessian_cube`,
`Morse.Examples.monkey_degenerate`, `Morse.Examples.isCriticalPoint_monkey_iff`,
`Morse.Examples.hessian_monkey`, `Morse.Examples.isCriticalPoint_sqFst_iff`,
`Morse.Examples.not_isNondegenerate_sqFst`, `Morse.Examples.isCriticalPoint_sqMul_iff`,
`Morse.Examples.not_isNondegenerate_sqMul`, `Morse.not_isNondegenerate_of_frequently`).** (a) The
only critical point of $x^3$ on $\mathbb R$ is $0$, where the Hessian is $0$, so it is degenerate.
(c) The only critical point of $x^3 - 3xy^2$ on $\mathbb R^2$ is the origin, where the Hessian is
$0$. (d) The critical points of $x^2$ on $\mathbb R^2$ are the points of the line $x = 0$, and all
are degenerate. (e) The critical points of $x^2y^2$ are the points of the two coordinate axes, and
all are degenerate. In (d) and (e) degeneracy is the contrapositive of V1.10: a critical point that
is a limit of other critical points, of a function $C^2$ there, is degenerate. *Book:* pp. 8–9,
examples (a), (c), (d), (e). *Hidden hypotheses:* none. *Deviation (stronger):* in (a) and (c) the
origin is also the only critical point. *Deviation (value differs):* in (d) the book says the
critical set is the $x$ axis; since $\partial f/\partial x = 2x$ and $\partial f/\partial y = 0$, it
is the $y$ axis. The formalization noticed this.

**V1.13 (one-parameter groups; `Morse.IsOneParameterGroup`, `Morse.Generates`,
`Morse.IsOneParameterGroup.zero`, `Morse.IsOneParameterGroup.isIntegralCurve`).** On a real normed
space $E$, a *one-parameter group of diffeomorphisms* is a map $\varphi : \mathbb R \times E \to E$,
$C^\infty$ in $(t, x)$, such that each $\varphi_t$ is a $C^\infty$ diffeomorphism of $E$ and
$\varphi_{t+s} = \varphi_t\circ\varphi_s$ for all $t$, $s$. A vector field $X : E \to E$ *generates*
$\varphi$ if for every $x$ the curve $h \mapsto \varphi_h(x)$ has derivative $X(x)$ at $h = 0$. Then
$\varphi_0 = \mathrm{id}$, and if $\varphi$ is generated by $X$, every orbit
$t \mapsto \varphi_t(x)$ is an integral curve of $X$. *Book:* pp. 9–10, on a manifold; the orbit
computation is on p. 10. *Hidden hypotheses:* none. *Deviation (narrower):* only for $M = E$, where
a tangent vector is a vector and Milnor's $X_q(f) = \lim_{h \to 0}(f(\varphi_h(q)) - f(q))/h$
becomes the derivative of $h \mapsto \varphi_h(q)$. That $\varphi_0 = \mathrm{id}$, used implicitly
on p. 10, follows from the group law because $\varphi_0$ is injective.

**V1.14 (global flows, and smooth dependence on the initial point; `Morse.IsBddLipschitz`,
`Morse.flow`, `Morse.IsBddLipschitz.isIntegralCurve_flow`, `Morse.IsBddLipschitz.eq_flow`,
`Morse.IsBddLipschitz.flow_add`, `Morse.IsBddLipschitz.continuous_flow`,
`Morse.IsBddLipschitz.flowHomeomorph`, `Morse.IsBddLipschitz.of_contDiff`, `Morse.contDiff_flow`,
`Morse.contDiff_flow_uncurry`, `Morse.flowDiffeomorph`).** Let $E$ be a complete real normed space
and $X : E \to E$ bounded and globally Lipschitz, for instance $C^1$ with compact support. Through
every point there is an integral curve of $X$ defined on all of $\mathbb R$, every integral curve is
a flow line, and the flow satisfies $\varphi_0 = \mathrm{id}$ and
$\varphi_{s+t} = \varphi_s\circ\varphi_t$, is jointly continuous in $(t, x)$, and each $\varphi_t$
is a homeomorphism with inverse $\varphi_{-t}$. If $X$ is $C^n$, $1 \le n \le \infty$, with compact
support, then $(t, x) \mapsto \varphi_t(x)$ is $C^n$ on $\mathbb R \times E$ and each $\varphi_t$ is
a $C^n$ diffeomorphism. *Book:* p. 10, quoted as well known (citing Graves): locally the equation
has a unique solution depending smoothly on the initial conditions; p. 11, "not difficult to verify"
that the $\varphi_t$ obtained by iteration are well defined, smooth, and form a group. *Hidden
hypotheses:* none. *Deviation (restated):* Milnor quotes the local theory and iterates it; the
formal statements are global, for bounded Lipschitz or compactly supported fields on a vector space,
and the smooth dependence, which Mathlib lacks, is proved rather than quoted. *Proof:* on $[0, 1]$
the flow line through $x$ solves $\Psi(\gamma) = x$ with
$\Psi(\gamma) = \gamma - \int_0^{\cdot} X(\gamma)$ in the Banach space $C([0, 1], E)$; for a
Lipschitz constant below $1$, $\Psi$ is a homeomorphism with everywhere invertible derivative
(Neumann series) and $\gamma \mapsto X\circ\gamma$ is as smooth as $X$, so the time-one map is $C^n$
(`Morse.Flow.voltHomeomorph`, `Morse.Flow.contDiff_voltHomeomorph_symm`, `Morse.Flow.contDiff_nem`).
General times come from $\varphi_t = (\varphi_{t/N})^N$ and joint smoothness from the flow of
$(x, \tau) \mapsto (\rho(\tau)X(x), 0)$ on $E \times \mathbb R$; Milnor's iteration of
$\varphi_{\epsilon_0/2}$ is replaced by Picard–Lindelöf on intervals of any length, which a bounded
field allows.

**V1.15 (Lemma 2.4; `Morse.lemma_2_4`).** Let $E$ be a complete real normed space and $X : E \to E$
a $C^\infty$ vector field which vanishes outside a compact set. Then there is exactly one
one-parameter group of diffeomorphisms of $E$ (V1.13) generated by $X$, namely its flow (V1.14).
*Book:* p. 10, Lemma 2.4, for a manifold $M$. *Hidden hypotheses:* none on $E$; on a manifold, the
uniqueness of integral curves needs $M$ Hausdorff. *Deviation (narrower):* only for $M = E$; if $E$
is infinite-dimensional the hypothesis forces $X = 0$, so the content is the case $E = \mathbb R^n$.
The uniqueness, implicit in the book, holds among all one-parameter groups generated by $X$, because
uniqueness of integral curves is global in time.

### What is not verified in this chapter

- §1: the identification of the sublevel sets of the torus in cases (2)–(4) (a 2-cell, a cylinder,
  a genus-one surface bounded by a circle) and the cell attachments of p. 2. Theorem 3.2 on
  submanifolds (V2.8) has not been applied to the torus. The normal forms at $p$, $q$, $r$, $s$
  follow from V1.1 and V1.8 but are not restated.
- p. 4: that $M^a$ is a smooth manifold with boundary $f^{-1}(a)$ when $a$ is not a critical
  value. Not restated; it is the companion project's Lemma 3
  (`Milnor.isHalfSliceSubmanifold_of_regularValue`) applied to $a - f$.
- pp. 4–5: Milnor's intrinsic definition of the Hessian through extending vector fields, and its
  independence of the extensions; his coordinate formula is used instead (V1.4).
- p. 8, example (b), $e^{-1/x^2}\sin^2(1/x)$: its smoothness at $0$ needs the flatness of
  $e^{-1/x^2}$ against the growth of the derivatives of $\sin^2(1/x)$; not done. Nor are the
  (non-)submanifold claims of (d) and (e).
- p. 10: Lemma 2.4 on a manifold other than a vector space. The smooth dependence of V1.14 is
  proved on vector spaces only (Mathlib has no smooth dependence on initial conditions); for
  submanifolds of $\mathbb R^K$, Chapter 2 uses instead the ambient flow of a field tangent to $N$
  (V2.3).
- p. 11: the Remark that compact support cannot be dropped ($d/dt$ on $(0, 1)$); not formalized.

---

## 3. Chapter 2 (Milnor §3): partly verified

Milnor's §3 proves that the homotopy type of $M^a$ changes only at critical values (Theorem 3.1);
that passing a non-degenerate critical point of index $\lambda$ attaches a $\lambda$-cell (Theorem
3.2, with Remark 3.3 for several critical points on one level and Remark 3.4 for the critical level
itself); two lemmas on attaching cells (Lemmas 3.6 and 3.7); and that a manifold carrying a function
with only non-degenerate critical points and compact sublevel sets has the homotopy type of a
CW-complex with one $\lambda$-cell for each critical point of index $\lambda$ (Theorem 3.5). Theorem
3.1 is verified in three settings: on a finite-dimensional real inner product space (Milnor's
$\mathbb R^n$ with a Riemannian metric); for $f = F|N$ on a slice submanifold
$N \subseteq \mathbb R^K$ in the sense of the companion project (V1.6), closed or not, with $F$
smooth on $\mathbb R^K$; and on an abstract compact Hausdorff manifold, through Mathlib's Whitney
embedding. The unnumbered Remark after it is verified on an explicit example. Theorem 3.2 is
verified on $\mathbb R^n$ and on slice submanifolds, both as a strong deformation retraction onto
$M^{c-\epsilon}$ with an embedded cell and as a homotopy equivalence with Milnor's adjunction space;
Remark 3.3 on slice submanifolds; Remark 3.4 on $\mathbb R^n$; Lemmas 3.6 and 3.7 for arbitrary
spaces. Theorem 3.5 is verified for compact slice submanifolds, with "CW-complex" replaced by an
iterated adjunction space with exactly $C_\lambda$ cells of dimension $\lambda$, because Mathlib has
no cellular approximation theorem. Not verified: Theorems 3.2 and 3.5 and Remarks 3.3 and 3.4 on
abstract manifolds, the non-compact case of Theorem 3.5, and the CW structure.

**V2.1 (sublevel sets and strong deformation retracts; `Morse.sublevel`,
`Morse.IsStrongDeformationRetract`, `Morse.IsStrongDeformationRetract.exists_homotopyEquiv`).** For
a real function $f$ on a set and $c \in \mathbb R$, $M^c = \{x : f(x) \le c\}$. A subset $A$ of a
topological space $X$ is a *strong deformation retract* of $X$ if there are a continuous map
$r : X \to X$ with values in $A$ and a homotopy $(t, x) \mapsto r_t(x)$, $0 \le t \le 1$, from
$r_0 = \mathrm{id}_X$ to $r_1 = r$ with $r_t(a) = a$ for all $t$ and all $a \in A$. If
$A \subseteq B$ are subsets of a space and $A$ is a strong deformation retract of $B$, the inclusion
$A \to B$ is a homotopy equivalence (the proof takes $r_1$ as its homotopy inverse). *Book:* p. 12
($M^a$); p. 13, the deformation $r_t$ in the proof of Theorem 3.1, and the passage from deformation
retract to homotopy equivalence. *Hidden hypotheses:* none. *Deviation (stronger):* Milnor uses
"deformation retract" without a definition; every deformation he constructs fixes the smaller set at
all times, and every formal statement asserts this strong form, which implies the weaker ones.

**V2.2 (Theorem 3.1 on a Euclidean space; `Morse.theorem_3_1`,
`Morse.exists_diffeomorph_image_sublevel_eq`).** Let $E$ be a finite-dimensional real inner product
space, $f : E \to \mathbb R$ of class $C^\infty$, $a \le b$, and suppose that $f^{-1}[a, b]$ is
compact and contains no critical point of $f$. Then there is a $C^\infty$ diffeomorphism $\Phi$ of
$E$ with $\Phi(M^a) = M^b$; $M^a$ is a strong deformation retract of $M^b$; the inclusion
$M^a \to M^b$ is a homotopy equivalence; and $M^a$ and $M^b$ are homeomorphic. *Book:* p. 12,
Theorem 3.1, for a smooth function on a manifold and $a < b$. *Hidden hypotheses:* none; the inner
product is Milnor's Riemannian metric. *Deviation (restated):* "$M^a$ is diffeomorphic to $M^b$" is
formalized as what the proof gives, a diffeomorphism of the whole space carrying $M^a$ onto $M^b$
(Milnor's $\varphi_{b-a}$); $a = b$ is allowed. *Proof:* Milnor's. The cut-off $\rho$, smooth with
compact support and equal to $1/\|\nabla f\|^2$ on $f^{-1}[a, b]$, is constructed
(`Morse.exists_cutoff`), and the flow of $\rho\nabla f$ is V1.14; everything after
$\frac{d}{dt} f(\varphi_t(q)) = 1$ is proved for any continuous flow on a topological space along
which a continuous function has derivative $1$ while its value lies in $[a, b]$ (`Morse.IsSlabFlow`,
`Morse.IsSlabFlow.image_sublevel`, `Morse.IsSlabFlow.isStrongDeformationRetract`): each trajectory
crosses the slab once, at unit speed, which is what Milnor's "clearly" needs, and his two-case $r_t$
is the single continuous formula $r_t(q) = \varphi_{t\min(0,\, a - f(q))}(q)$.

**V2.3 (Theorem 3.1 on a submanifold of Euclidean space; `Morse.theorem_3_1_submanifold`,
`Morse.theorem_3_1_submanifold_of_isCompact`).** Let $V$ be a finite-dimensional real normed space,
$N \subseteq V$ a slice submanifold modelled on a finite-dimensional $Z$ (V1.6; $N$ need not be
closed), $F : V \to \mathbb R$ of class $C^\infty$ and $f = F|N$. Let $a \le b$, and suppose that
$f^{-1}[a, b] \subseteq N$ is compact and contains no critical point of $f$, as a function on the
manifold $N$. Then there is a $C^\infty$ diffeomorphism $\Phi$ of $N$ with $\Phi(N^a) = N^b$, $N^a$
is a strong deformation retract of $N^b$, and the inclusion $N^a \to N^b$ is a homotopy equivalence.
When $N$ is compact, the compactness of $f^{-1}[a, b]$ need not be assumed. *Book:* p. 12, Theorem
3.1. *Hidden hypotheses:* none; $N$ is Hausdorff and second countable as a subset of $V$. *Deviation
(narrower):* $f$ must be the restriction of a smooth function on $V$. *Proof:* no Riemannian metric
is used. Slice charts and bump functions give a smooth field $Y$ on $V$, tangent to $N$ along $N$,
with $dF(Y) > 0$ on $f^{-1}[a, b]$; the field $\rho Y$, with $\rho\,dF(Y) = 1$ there, replaces
$\rho\,\mathrm{grad} f$, its flow on $V$ preserves $N$ (`Morse.flow_mem_of_tangent`), and the
slab-flow argument of V2.2 runs on $N$.

**V2.4 (Theorem 3.1 on a compact manifold; `Morse.theorem_3_1_of_compactSpace`).** Let $M$ be a
compact Hausdorff smooth manifold without boundary modelled on a finite-dimensional real normed
space, $f : M \to \mathbb R$ of class $C^\infty$, $a \le b$, and suppose that $f^{-1}[a, b]$
contains no critical point of $f$. Then a $C^\infty$ diffeomorphism of $M$ carries $M^a$ onto $M^b$,
$M^a$ is a strong deformation retract of $M^b$, and the inclusion $M^a \to M^b$ is a homotopy
equivalence. *Book:* p. 12, Theorem 3.1. *Hidden hypotheses:* Hausdorff. *Deviation (narrower):* $M$
compact. *Proof:* Mathlib's Whitney embedding for compact manifolds makes $M$ diffeomorphic to a
compact slice submanifold $N \subseteq \mathbb R^{K+1}$
(`Morse.exists_diffeomorph_sliceSubmanifold`); $f$ read on $N$ is the restriction of a smooth
function on $\mathbb R^{K+1}$ (`Morse.exists_contDiff_comp_val_eq`), so V2.3 applies, and its
conclusions are carried back to $M$.

**V2.5 (the Remark on p. 13: compactness cannot be omitted; `Morse.RemarkP13.remark_p13`,
`Morse.RemarkP13.remark_p13_not_isStrongDeformationRetract`,
`Morse.RemarkP13.remark_p13_not_homeomorph`, `Morse.RemarkP13.remark_p13_not_isCompact`,
`Morse.RemarkP13.remark_p13_not_isCriticalPoint`, `Morse.RemarkP13.remark_p13_plane`).** Let
$M = \mathbb C \setminus \{i\}$, $f(z) = |z|^2$ on $M$, $a = \tfrac14$ and $b = 4$. No
$z \in \mathbb C$ with $\tfrac14 \le |z|^2 \le 4$ is a critical point of $|z|^2$, but
$f^{-1}[\tfrac14, 4] \subseteq M$ is not compact; $M^{1/4}$ (the closed disc of radius $\tfrac12$)
and $M^4$ (the closed disc of radius $2$ without $i$) are not homotopy equivalent, so $M^{1/4}$ is
not a strong deformation retract of $M^4$, and the two are not homeomorphic. With $i$ put back,
Theorem 3.1 (V2.2) applies: in $\mathbb C$ the disc of radius $\tfrac12$ is a strong deformation
retract of the disc of radius $2$. *Book:* p. 13, the Remark after Theorem 3.1, with Diagram 3 (p.
14): a surface from which a point $p$ between the levels $a$ and $b$ has been removed, for which
$M^a$ is "clearly" not a deformation retract of $M^b$. The Remark is unnumbered (Milnor's Remark 3.3
is the statement of p. 19, V2.9). *Hidden hypotheses:* none. *Deviation (restated):* the pictured surface is replaced
by the punctured plane, and the conclusion is the stronger one that the two sublevel sets are not
even homotopy equivalent; $M$ is open in $\mathbb C$, so the critical points of $f$ are those of
$|z|^2$. *Proof:* the "clearly" is the non-contractibility of the punctured disc, proved by lifting
a null-homotopy of $z \mapsto z - i$ through the covering
$\exp : \mathbb C \to \mathbb C \setminus \{0\}$ (`Morse.RemarkP13.not_contractibleSpace`).

**V2.6 (Theorem 3.2 on a Euclidean space; `Morse.theorem_3_2`, `Morse.theorem_3_2_homotopyEquiv`,
`Morse.theorem_3_2_attach`).** Let $E$ be a finite-dimensional real inner product space,
$f : E \to \mathbb R$ of class $C^\infty$, $p$ a critical point at which $d^2 f_p$ is
non-degenerate, $\lambda$ its index (V1.3) and $c = f(p)$, and suppose that for some
$\epsilon_0 > 0$ the set $f^{-1}[c - \epsilon_0, c + \epsilon_0]$ is compact and contains no
critical point other than $p$. Then there is $\epsilon_1 > 0$ such that for every $\epsilon$ with
$0 < \epsilon \le \epsilon_1$ there is a map $\chi$ from the closed unit ball $D^\lambda$ of
$\mathbb R^\lambda$ to $E$, continuous and injective on $D^\lambda$, with
$\chi(z) \in M^{c-\epsilon}$ exactly when $|z| = 1$ and $\chi(D^\lambda) \subseteq M^{c+\epsilon}$,
such that $M^{c-\epsilon} \cup \chi(D^\lambda)$ is a strong deformation retract of $M^{c+\epsilon}$.
Hence the inclusion of $M^{c-\epsilon} \cup \chi(D^\lambda)$ in $M^{c+\epsilon}$ is a homotopy
equivalence, and there is an injective continuous $\varphi : S^{\lambda-1} \to M^{c-\epsilon}$ such
that $M^{c+\epsilon}$ is homotopy equivalent to $M^{c-\epsilon} \cup_\varphi e^\lambda$ (V1.2).
*Book:* p. 14, Theorem 3.2: for all sufficiently small $\epsilon$, $M^{c+\epsilon}$ has the homotopy
type of $M^{c-\epsilon}$ with a $\lambda$-cell attached (the scan prints "a k-cell" and renders the
index as "A"; both are read as $\lambda$, as the proof requires). *Hidden hypotheses:* none on $E$
(on a manifold, Hausdorff: V2.8). *Deviation (stronger):* the conclusion is a strong deformation
retraction onto $M^{c-\epsilon}$ with an embedded cell, which is what the proof produces; "for all
sufficiently small $\epsilon$" is read as "for all $\epsilon$ in some $(0, \epsilon_1]$". *Proof:*
Milnor's, through his four Assertions (`Morse.sublevel_milnorF_add`,
`Morse.isCriticalPoint_milnorF_iff`, `Morse.isStrongDeformationRetract_milnorF`,
`Morse.isStrongDeformationRetract_handle`), with these additions. His $\mu$ ($C^\infty$,
$\mu(0) > \epsilon$, $\mu = 0$ on $[2\epsilon, \infty)$, $-1 < \mu' \le 0$), whose existence he does
not show, is $\mu(r) = \tfrac34\int_r^{2\epsilon}\beta$ for a smooth plateau $\beta$
(`Morse.milnorMu`, `Morse.isMilnorMu_milnorMu`); Assertion 2 uses $\partial F/\partial\eta \ge 1$,
where the scan shows $> 1$, which fails where $\mu' = 0$; and the three cases of $r_t$ in Assertion
4 are one formula $(x, y) \mapsto (x, \sigma_t(x, y)\,y)$, continuous on the whole patch, which
pastes with the identity because it moves only points of the compact ellipsoid
$\xi + 2\eta \le 2\epsilon$ and keeps them there (`Morse.CellModel.retractModel`,
`Morse.CellModel.continuous_retractModel`).

**V2.7 (a cell meeting a closed set in its boundary sphere is attached to it;
`Morse.isPushout_of_cell`, `Morse.exists_isPushout_union_cell`,
`Morse.exists_isPushout_union_cell_of_t2`, `Morse.exists_homotopyEquiv_pushout_of_cell`).** Let $A$
be a closed subset of a Hausdorff space $M$ and $\chi : \mathbb R^n \to M$ continuous and injective
on $D^n$, with $\chi(z) \in A$ exactly when $|z| = 1$, for $z \in D^n$. Then the subspace
$A \cup \chi(D^n)$ of $M$ is the pushout of $\varphi = \chi|S^{n-1} : S^{n-1} \to A$ and
$S^{n-1} \to D^n$, that is, $A \cup_\varphi e^n$ (V1.2), and $\varphi$ is injective. Consequently,
if $f : M \to \mathbb R$ is continuous, $a \le b$, $\chi$ is as above for $A = M^a$,
$\chi(D^n) \subseteq M^b$, and $M^a \cup \chi(D^n)$ is a strong deformation retract of $M^b$, then
$M^b$ is homotopy equivalent to $M^a \cup_\varphi e^n$. *Book:* p. 16:
$e^\lambda \cap M^{c-\epsilon}$ is the boundary $\dot e^\lambda$, "so that" $e^\lambda$ is attached
to $M^{c-\epsilon}$ as required. *Hidden hypotheses:* $M$ Hausdorff and $A$ closed, so that the cell
is closed and $\chi$ is a homeomorphism onto it. *Deviation (not in the book):* the identification
of the subspace with the adjunction space is a lemma that Milnor does not state (Lemma D of the
exposition). *Proof:* the universal property of the pushout is checked directly, by the pasting
lemma for the closed cover of $A \cup \chi(D^n)$ by $A$ and $\chi(D^n)$.

**V2.8 (Theorem 3.2 in a Morse patch, and on a submanifold; `Morse.IsMorsePatch`,
`Morse.IsMilnorMu`, `Morse.patch_theorem_3_2`, `Morse.theorem_3_2_submanifold`,
`Morse.theorem_3_2_attach_submanifold`).** (i) The topological half, in any Hausdorff space $M$. Let
$X$, $Y$ be finite-dimensional real inner product spaces with $\dim X = \lambda$,
$f : M \to \mathbb R$, $p \in M$, and $\varphi$ a homeomorphism of an open neighbourhood of $p$ onto
an open subset of $X \times Y$ with $\varphi(p) = 0$, $f = f(p) - |x|^2 + |y|^2$ on its domain, and
image containing the ball $|x|^2 + |y|^2 \le 2\epsilon$, $\epsilon > 0$. Let $\mu$ satisfy Milnor's
four conditions (V2.6), and let $F = f - \mu(|x|^2 + 2|y|^2)$ on the domain of $\varphi$ and $F = f$
elsewhere. If $F^{-1}(-\infty, f(p) - \epsilon]$ is a strong deformation retract of
$M^{f(p)+\epsilon}$ (Assertion 3), then the conclusion of V2.6 about the cell holds in $M$ for this
$\epsilon$. (ii) Let $V$, $Z$ be finite-dimensional, $N \subseteq V$ a slice submanifold modelled on
$Z$, $F : V \to \mathbb R$ of class $C^\infty$, $f = F|N$, $p \in N$ a non-degenerate critical point
of $f$ of index $\lambda$ (V1.4), $c = f(p)$, and suppose that for some $\epsilon_0 > 0$ the set
$f^{-1}[c - \epsilon_0, c + \epsilon_0]$ is compact and contains no critical point of $f$ other than
$p$. Then the conclusions of V2.6 hold in $N$: there is $\epsilon_1 > 0$ such that for every
$\epsilon \in (0, \epsilon_1]$ there is a $\lambda$-cell $\chi(D^\lambda) \subseteq N^{c+\epsilon}$,
$\chi$ continuous and injective on $D^\lambda$, meeting $N^{c-\epsilon}$ exactly in
$\chi(S^{\lambda-1})$, such that $N^{c-\epsilon} \cup \chi(D^\lambda)$ is a strong deformation
retract of $N^{c+\epsilon}$; and $N^{c+\epsilon}$ is homotopy equivalent to
$N^{c-\epsilon} \cup_\varphi e^\lambda$ for an injective $\varphi$. *Book:* p. 14, Theorem 3.2.
*Hidden hypotheses:* Hausdorff, used for the ellipsoid $\xi + 2\eta \le 2\epsilon$ to be closed in
$M$ (for the smoothness of $F$ and the continuity of $r_t$) and in V2.7; automatic for
$N \subseteq V$. *Deviation (narrower):* in (ii), $f$ is the restriction of an ambient smooth
function. *Proof:* in (ii) the Morse coordinates are V1.8 on the manifold $N$, taken inside one
slice chart; Assertion 3 is V2.3 applied to $F$, which requires extending $F$ to a smooth function
on $V$ (`Morse.exists_contDiff_comp_val_eq_of_chart`), a step that Milnor's intrinsic Theorem 3.1
does not need.

**V2.9 (Remark 3.3, several critical points on one level; `Morse.remark_3_3_submanifold`).** Let
$V$, $Z$, $N$, $F$ and $f = F|N$ be as in V2.8 (ii), $S$ a finite set of non-degenerate critical
points of $f$, all with value $c$, and suppose that for some $\epsilon_0 > 0$ the set
$f^{-1}[c - \epsilon_0, c + \epsilon_0]$ is compact and all its critical points lie in $S$. Then
there is $\epsilon_1 > 0$ such that for every $\epsilon \in (0, \epsilon_1]$ there are cells
$e_p = \chi_p(D^{\lambda_p})$, $p \in S$, $\lambda_p$ the index of $p$, each $\chi_p$ continuous and
injective on $D^{\lambda_p}$, meeting $N^{c-\epsilon}$ exactly in $\chi_p(S^{\lambda_p-1})$ and
contained in $N^{c+\epsilon}$, the cells pairwise disjoint, such that
$N^{c-\epsilon} \cup \bigcup_{p \in S} e_p$ is a strong deformation retract of $N^{c+\epsilon}$.
*Book:* p. 19, Remark 3.3: for $k$ non-degenerate critical points in $f^{-1}(c)$, "a similar proof"
shows that $M^{c+\epsilon}$ has the homotopy type of
$M^{c-\epsilon} \cup e^{\lambda_1} \cup \dots \cup e^{\lambda_k}$. *Hidden hypotheses:* as for
Theorem 3.2, a compact $f^{-1}[c - \epsilon_0, c + \epsilon_0]$ with no other critical points; and
Morse charts with pairwise disjoint domains, which needs Hausdorffness. *Deviation (narrower):* only
on slice submanifolds. That the union is $N^{c-\epsilon}$ with the cells attached one at a time is
part of V2.12 (`Morse.isFiniteCellComplexType_union_cells`).

**V2.10 (Remark 3.4, the critical level; `Morse.remark_3_4`,
`Morse.IsStrongDeformationRetract.of_retract`).** Under the hypotheses of V2.6 ($E$ a
finite-dimensional real inner product space), there is $\epsilon_1 > 0$ such that for every
$\epsilon \in (0, \epsilon_1]$: $M^c$ is a strong deformation retract of $M^{c+\epsilon}$; and there
is a map $\chi$ from $D^\lambda$ to $E$, continuous and injective on $D^\lambda$, with
$\chi(z) \in M^{c-\epsilon}$ exactly when $|z| = 1$, such that the part of
$M^{c-\epsilon} \cup \chi(D^\lambda)$ lying in $M^c$ is a strong deformation retract of $M^c$. (The
whole cell lies in $M^c$, since $f = c - \epsilon|z|^2$ on it; the proof uses this, but the formal
statement does not record it.) *Book:* p. 20, the remark printed "Remark 2.4" in the scan and cited
as Remark 3.4 on p. 24: a simple modification of the proof of 3.2 shows that $M^c$ is a deformation
retract of $M^{c+\epsilon}$, and combining this with 3.2 one sees "easily" that
$M^{c-\epsilon} \cup e^\lambda$ is one of $M^c$. *Hidden hypotheses:* none. *Deviation (narrower):*
only on $E$, not on submanifolds. *Proof:* the second half uses a lemma that Milnor does not state:
if $A \subseteq B \subseteq C$ and both $A$ and $B$ are strong deformation retracts of $C$, then $A$
is a strong deformation retract of $B$ (only the retraction of $C$ onto $B$ is used).

**V2.11 (iterated adjunction spaces, in place of CW-complexes; `Morse.IsCellAttachment`,
`Morse.IsFiniteCellComplexType`).** A space $K$ is an *iterated adjunction space with cells*
$(\lambda_1, \dots, \lambda_k)$ if it is obtained from the empty space by attaching a
$\lambda_1$-cell, then a $\lambda_2$-cell, and so on, each along an arbitrary continuous map of its
boundary sphere into the space built so far (V1.2). A space $X$ *has the homotopy type of a finite
cell complex with cells* $(\lambda_1, \dots, \lambda_k)$ if it is homotopy equivalent to such a $K$.
*Book:* p. 20, the "CW-complex" of Theorem 3.5, for which Milnor refers to J. H. C. Whitehead.
*Hidden hypotheses:* none. *Deviation (narrower):* this is weaker than a CW-complex with these
cells: the attaching maps need not be cellular, and the cells are attached in the listed order
rather than by dimension. Milnor makes the attaching maps cellular by the cellular approximation
theorem (p. 23), which Mathlib does not have; with it and Lemma 3.6 such a space is homotopy
equivalent to a CW-complex with the same number of cells in each dimension, a step that is not
formalized.

**V2.12 (Theorem 3.5 for a compact submanifold of Euclidean space; `Morse.theorem_3_5'`,
`Morse.theorem_3_5_count'`, `Morse.theorem_3_5`, `Morse.theorem_3_5_count`).** Let $V$ be a
finite-dimensional real normed space, $N \subseteq V$ a compact slice submanifold modelled on a
finite-dimensional $Z$, $F : V \to \mathbb R$ of class $C^\infty$, and suppose that every critical
point of $f = F|N$ is non-degenerate. Then the critical points of $f$ can be listed without
repetition as $p_1, \dots, p_k$, with $f(p_1) \le \dots \le f(p_k)$, so that $N$ has the homotopy
type of a finite cell complex with cells $(\lambda(p_1), \dots, \lambda(p_k))$ in the sense of
V2.11, $\lambda(p)$ the index of $p$. In particular $N$ has the homotopy type of such a complex
whose number of cells of dimension $\lambda$ is, for every $\lambda$, the number $C_\lambda$ of
critical points of index $\lambda$. If the critical values are distinct, the list is strictly
increasing (`Morse.theorem_3_5`, `Morse.theorem_3_5_count`). *Book:* p. 20, Theorem 3.5: if $f$ has
no degenerate critical points and every $M^a$ is compact, $M$ has the homotopy type of a CW-complex
with one cell of dimension $\lambda$ for each critical point of index $\lambda$; proof pp. 23–24.
*Hidden hypotheses:* that $M^a$ is empty below the first critical value (p. 23) needs a global
minimum to be a critical point (`Morse.isCriticalPointM_of_forall_le`); that the critical values do
not accumulate is V1.11. *Deviation (narrower):* $N$ compact and $f$ the restriction of an ambient
function; the non-compact case (infinitely many critical points, Whitehead's theorem) is not done;
and the conclusion is an iterated adjunction space, not a CW-complex (V2.11). *Proof:* Milnor's
induction over regular values: Theorem 3.1 between critical levels (V2.3), Theorem 3.2 or Remark 3.3
at each level (V2.8, V2.9), V2.7 to attach disjoint cells one at a time
(`Morse.isFiniteCellComplexType_union_cells`), and Lemma 3.7 (V2.14) to carry the cells along
homotopy equivalences; Lemma 3.6 is not needed, since the attaching maps are not made cellular.

**V2.13 (Lemma 3.6; `Morse.lemma_3_6`).** Let $X$ be a topological space, $n \ge 0$, and
$\varphi_0, \varphi_1 : S^{n-1} \to X$ homotopic maps. Then there is a homotopy equivalence
$k : X \cup_{\varphi_0} e^n \to X \cup_{\varphi_1} e^n$ which is the identity on $X$. *Book:* p. 20,
Lemma 3.6 (Whitehead). *Hidden hypotheses:* none. *Proof:* Milnor's formulas for $k$ and $\ell$; his
"not difficult to verify" that $k\ell$ and $\ell k$ are homotopic to the identities is an explicit
homotopy (`Morse.lemma36Homotopy`). Homotopies on an adjunction space are built through the
exponential law for the locally compact $[0, 1]$ (`Morse.cellHomotopy`), which is the fact, used
silently by Milnor, that $[0, 1] \times$ (a quotient map) is a quotient map.

**V2.14 (Lemma 3.7, and the Assertion of p. 22; `Morse.lemma_3_7`,
`Morse.homotopic_of_leftInv_rightInv`).** Let $X$, $Y$ be topological spaces,
$\varphi : S^{n-1} \to X$ continuous and $f : X \to Y$ a homotopy equivalence. Then the map
$F : X \cup_\varphi e^n \to Y \cup_{f\varphi} e^n$ equal to $f$ on $X$ and to the identity on the
cell is a homotopy equivalence. And for maps $F$, $L$, $R$: if $LF \simeq \mathrm{id}$ and
$FR \simeq \mathrm{id}$, then $RF \simeq \mathrm{id}$. *Book:* p. 21, Lemma 3.7 (after Hilton): any
homotopy equivalence $f$ extends to a homotopy equivalence $F$; p. 22, the Assertion that a map with
a left and a right homotopy inverse is a homotopy equivalence, with $R$ (or $L$) a two-sided
homotopy inverse. *Hidden hypotheses:* none. *Deviation (stronger):* the extension is named, as in
Milnor's proof. *Proof:* Milnor's; it uses the formula for $k$ from the proof of Lemma 3.6, not only
its statement.

**V2.15 (the Remark on p. 24, at regular values; `Morse.isFiniteCellComplexType_sublevel'`,
`Morse.isFiniteCellComplexType_sublevel`).** Let $V$, $Z$, $N$, $F$ and $f = F|N$ be as in V2.12,
and let $a$ be a real number which is not a critical value of $f$. Then the critical points $p$ with
$f(p) < a$ can be listed without repetition as $p_1, \dots, p_j$, with
$f(p_1) \le \dots \le f(p_j)$, so that $N^a$ has the homotopy type of a finite cell complex with
cells $(\lambda(p_1), \dots, \lambda(p_j))$ (V2.11). *Book:* p. 24, the unnumbered Remark at the end
of §3: each $M^a$ has the homotopy type of a finite CW-complex with one cell of dimension $\lambda$
for each critical point of index $\lambda$ in $M^a$, even when $a$ is a critical value. *Hidden
hypotheses:* none. *Deviation (narrower):* only for $a$ not a critical value (a critical value would
need Remark 3.4 on submanifolds), and with the iterated adjunction space of V2.11.

### What is not verified in this chapter

- Theorem 3.1 on a non-compact abstract manifold (with $f^{-1}[a, b]$ compact): the transfer
  through Whitney's theorem needs a closed embedding of a non-compact manifold into Euclidean
  space, which Mathlib does not have. On submanifolds of $\mathbb R^K$, closed or not, it is V2.3.
- Theorems 3.2 and 3.5 and Remarks 3.3 and 3.4 on abstract manifolds, compact or not: not
  transferred through the Whitney embedding, as Theorem 3.1 is (V2.4).
- Remark 3.4 on submanifolds, and with it the Remark of p. 24 at a critical value.
- The CW structure in Theorem 3.5 and in the Remark of p. 24: Mathlib has no cellular approximation
  theorem (V2.11).
- Theorem 3.5 for non-compact $M$ with compact sublevel sets: with finitely many critical points it
  needs a deformation of $M$ onto some $M^a$ obtained by patching flows; with infinitely many it
  needs Whitehead's theorem and the fact that a manifold has the homotopy type of a CW-complex,
  neither of which is in Mathlib.
- The Remark of p. 17 (Smale's handles: $M^{c-\epsilon} \cup H$ is diffeomorphic to
  $M^{c+\epsilon}$): it is Theorem 3.1 applied to $F$, but the diffeomorphism is not recorded.

---

## 4. Chapter 3 (Milnor §§4–5): partly verified

Milnor's §4 proves Reeb's theorem (Theorem 4.1, p. 25) from Theorem 3.1 and the lemma of Morse, adds
two remarks, and sketches two examples: a manifold carrying a function with three critical points,
and $\mathbb CP^n$ (pp. 26–27). His §5 (pp. 28–31) defines subadditive functions and proves Lemma
5.1, the weak Morse inequalities (Theorem 5.2), Lemma 5.3, the strong inequalities $(4_\lambda)$ and
Corollary 5.4, for a compact manifold and singular homology over a field. Verified: Reeb's theorem
for a compact submanifold of a finite-dimensional real normed space, with every step of Milnor's
short proof made explicit (V3.1–V3.6; for an abstract compact manifold it is V4.24); the whole
algebra of §5, for an abstract "homology of a filtration" that records exactly the finiteness and
the exact sequences of triples that Milnor uses (V3.7–V3.15); formula (3) of Theorem 5.2 by the
route of §6, Application 2 (p. 36), without homology: on a compact submanifold $N$ of
$\mathbb R^{K+1}$, $K \ge 1$, of positive dimension, $\sum_\lambda (-1)^\lambda C_\lambda$ is the
same integer for every Morse function, namely the integer $\chi(N)$ of the Poincaré–Hopf theorem of
the Milnor project (V3.16–V3.21); and **§5 in singular homology, with no hypothesis left**
(V3.26–V3.40). For the last, the homology Milnor quotes is built first, Mathlib having only absolute
singular homology: relative singular homology with the exact sequences of pairs and triples,
homotopy invariance for pairs, excision, the Mayer–Vietoris sequence, and the homology of disks,
spheres and attached cells (V3.26–V3.31). Singular homology over any field is then an instance of
the abstract structure (V3.32); the homology of each slab between regular values is computed from
Theorems 3.1 and 3.2 (V3.33–V3.34); and Theorem 5.2, $(4_\lambda)$, Corollary 5.4 and the lacunary
principle hold for the Betti numbers over every field of every compact submanifold of a Euclidean
space and, through the Whitney embedding, of every compact Hausdorff manifold (V3.35–V3.37, V3.39).
The Poincaré–Hopf integer $\chi(N)$, and the Euler number of an abstract compact manifold (V4.18),
**are identified with the homological Euler characteristic** $\sum_i (-1)^i \dim H_i(N; F)$, the
same for every field $F$ (V3.38). The setting is that of slice submanifolds (the Milnor project's
`Milnor.IsSliceSubmanifold`: subsets covered by slice charts, with the manifold structure those
charts give), which are automatically Hausdorff and second countable. Also verified is the example
of $\mathbb CP^n$ (V3.41–V3.43): it is the submanifold of rank-one Hermitian projections, Milnor's
coordinates are slice coordinates on it, his function has the $n + 1$ critical points and the
indices he states, and the cells and the homology over every field follow
(`Morse/Chapter3/ProjectiveSpace.lean`, 450 lines; `ProjectiveMorse.lean`, 431). Not verified:
Milnor's two remarks on Reeb's theorem, the example with three critical points, integral homology,
and non-compact manifolds (the list at the end). The torus of §1 (pp. 1–3) belongs to the book pages
of Chapter 1, but its Lean files (`Morse/Chapter3/TorusSurface.lean`, `Morse/Chapter3/Torus.lean`)
live with this chapter and use V3.20, so it is verified here (V3.22–V3.25, with its homology in
V3.40). Lean: `Morse/Chapter3/` and `Morse/Homology/`.

**V3.1 (extrema of a function; `Morse.isCriticalPointM_of_isLocalMin`,
`Morse.isCriticalPointM_of_isLocalMax`, `Morse.indexM_eq_zero_of_isLocalMin`,
`Morse.indexM_eq_finrank_of_isLocalMax`).** Let $M$ be a manifold modelled on a real normed space
$E$ and $f : M \to \mathbb R$. A local minimum or local maximum $p$ of $f$ is a critical point (for
every $f$: in the formal definition of Chapter 1 a point where $f$ is not differentiable counts as
critical). If moreover $M$ is a smooth manifold without boundary, $E$ is finite-dimensional with
$n = \dim E$, $f$ is smooth on an open set containing $p$, and $p$ is a non-degenerate critical
point, then the index of $f$ at $p$ is $0$ if $p$ is a local minimum and $n$ if $p$ is a local
maximum. *Book:* used without comment in the proof of Theorem 4.1 (p. 25), where the small sublevel
sets at the minimum and the maximum are said to be closed $n$-cells "by 2.2". *Hidden hypotheses:*
none. *Deviation (not in the book):* Milnor never states it. *Proof:* in a Morse chart
(`Morse.morse_lemmaM`), $f$ decreases along an axis carrying a minus sign, so a minimum has none,
and increases along an axis carrying a plus sign, so a maximum has only minus signs.

**V3.2 (Morse charts at the extrema; small sublevel sets are closed balls;
`Morse.exists_morse_chart_of_isLocalMin`, `Morse.exists_morse_chart_of_isLocalMax`,
`Morse.exists_image_closedBall_eq_sublevel`).** (i) In the setting of the second half of V3.1, if
$p$ is a non-degenerate local minimum (maximum) of $f$, $f$ smooth on an open $U \ni p$, there are
smooth coordinates $y$ on an open subset of $U$ containing $p$, with values in $\mathbb R^n$ with
its Euclidean norm, such that $y(p) = 0$ and $f = f(p) + \|y\|^2$ (resp. $f = f(p) - \|y\|^2$) on
the domain of $y$. (ii) Let $X$ be a compact topological space, $f : X \to \mathbb R$ continuous
with a strict global minimum at $p$ ($f(p) < f(x)$ for all $x \ne p$), and $y$ a homeomorphism from
an open neighbourhood of $p$ onto an open subset of a real normed space $F$, with $y(p) = 0$ and
$f = f(p) + \|y\|^2$ on its domain. Then there is $\delta > 0$ such that for every $0 < \varepsilon
< \delta$ the map $v \mapsto y^{-1}(\sqrt\varepsilon\, v)$ is continuous and injective on the closed
unit ball of $F$, maps it onto $\{f \le f(p) + \varepsilon\}$, and maps the unit sphere onto the
level set $\{f = f(p) + \varepsilon\}$. (Applied to $-f$, the same holds at a strict maximum.)
*Book:* p. 25: if $\varepsilon$ is small enough, $f^{-1}[0, \varepsilon]$ and $f^{-1}[1 -
\varepsilon, 1]$ are closed $n$-cells by Lemma 2.2. *Hidden hypotheses:* the lemma of Morse
describes $f$ only near $p$; that the whole sublevel set lies in the Morse chart needs compactness
and the uniqueness of the minimum (off a small coordinate ball $f \ge f(p) + \eta$ for some $\eta >
0$); the gluing at the end of the proof needs the boundary sphere of the cell to be carried onto the
level set, which "closed $n$-cell" does not say. *Deviation (restated):* the closed cell is produced
as the image of the closed unit ball under a continuous injective map, with its boundary sphere
going onto the level set.

**V3.3 (the two critical points are the minimum and the maximum;
`Morse.exists_min_max_of_ncard_eq_two`).** Let $M$ be a compact smooth manifold without boundary
modelled on a finite-dimensional real normed space $E$ with $n = \dim E \ge 1$, and $f : M \to
\mathbb R$ smooth with exactly two critical points, both non-degenerate. Then there are points $p,
q$ with $f(p) < f(q)$ such that the critical points are exactly $p$ and $q$, $f(p) < f(x)$ for every
$x \ne p$, $f(x) < f(q)$ for every $x \ne q$, the index of $f$ is $0$ at $p$ and $n$ at $q$. *Book:*
p. 25: the two critical points must be the minimum and the maximum. *Hidden hypotheses:* $n \ge 1$
(in dimension $0$ every point is critical and $f$ may be constant); non-degeneracy, to see that $f$
is not constant (a constant $f$ would make its minimum point also a maximum, of index $n \ne 0$);
that no other point takes an extreme value, which V3.2(ii) needs. Hausdorffness is not needed.

**V3.4 (Theorem 3.1 also carries the boundary level;
`Morse.exists_diffeomorph_image_sublevel_level`, `Morse.IsSlabFlow.image_level`).** Let $N$ be a
slice submanifold of a finite-dimensional real normed space $V$, modelled on a finite-dimensional
space $Z$, let $F : V \to \mathbb R$ be smooth and $f = F|_N$, and let $a \le b$ with $f^{-1}[a, b]$
compact and containing no critical point of $f$. Then there is a smooth diffeomorphism $\Phi$ of $N$
with $\Phi(N^a) = N^b$ and $\Phi(f^{-1}(a)) = f^{-1}(b)$, where $N^c = \{f \le c\}$. *Book:* p. 25:
$M^\varepsilon$ is homeomorphic to $M^{1-\varepsilon}$ by Theorem 3.1. *Hidden hypotheses:* the
gluing needs a homeomorphism that also carries the level $f^{-1}(\varepsilon)$ onto $f^{-1}(1 -
\varepsilon)$; the statement of Theorem 3.1 does not give this, its proof does (the flow moves the
levels of the slab at unit speed). *Deviation (stronger):* the second conclusion is added; $\Phi$ is
the time-$(b - a)$ map of the flow used for Theorem 3.1 on submanifolds
(`Morse.theorem_3_1_submanifold`).

**V3.5 (two closed balls glued along their boundary spheres form a sphere;
`Morse.alexanderConeHomeomorph`, `Morse.nonempty_homeomorph_sphere_of_union_closedBall`).** (i)
Alexander's trick: if $g$ is a homeomorphism of the unit sphere of a real normed space $E$, the cone
$x \mapsto \|x\|\, g(x/\|x\|)$, $0 \mapsto 0$, is a homeomorphism of $E$ that preserves norms and
extends $g$. (ii) Let $X$ be a Hausdorff space, $n \ge 0$, $D^n$ and $S^{n-1}$ the closed unit ball
and unit sphere of $\mathbb R^n$, and $h_1, h_2 : D^n \to X$ continuous and injective, with
$h_1(D^n) \cup h_2(D^n) = X$, $h_1(D^n) \cap h_2(D^n) = h_1(S^{n-1})$ and $h_2(S^{n-1}) =
h_1(S^{n-1})$. Then $X$ is homeomorphic to the unit sphere $S^n \subseteq \mathbb R^{n+1}$. *Book:*
p. 25: $M$ is the union of two closed $n$-cells matched along their common boundary, and a
homeomorphism with $S^n$ is "now easy to construct"; none is constructed. *Hidden hypotheses:* the
identification $h_2^{-1} \circ h_1$ of the boundary spheres is in general not the identity and must
be extended over a ball (Alexander's trick); the inverse is continuous because a continuous
bijection from a compact space onto a Hausdorff space is a homeomorphism. *Deviation (not in the
book):* Milnor's "easy" step, made explicit. The cone is in general not differentiable at $0$, which
is where smoothness is lost (compare Milnor's Remark 2).

**V3.6 (Theorem 4.1, Reeb's theorem; `Morse.reeb`, `Morse.reeb_of_finrank_pos`,
`Morse.reeb_of_finrank_eq_zero`, `Morse.reeb_of_contMDiff`).** Let $N$ be a compact slice
submanifold of a finite-dimensional real normed space $V$, modelled on a finite-dimensional space of
dimension $n$, and $f = F|_N$ with $F : V \to \mathbb R$ smooth. If $f$ has exactly two critical
points, both non-degenerate, then $N$ is homeomorphic to the unit sphere $S^n \subseteq \mathbb
R^{n+1}$. For a compact $N \subseteq \mathbb R^{K+1}$ modelled on $\mathbb R^n$, $n \ge 1$, the same
holds for every smooth $f : N \to \mathbb R$ (`Morse.reeb_of_contMDiff`; such an $f$ is the
restriction of a smooth function on $\mathbb R^{K+1}$, V3.20). *Book:* Theorem 4.1 (p. 25): a
compact manifold carrying a differentiable function with only two critical points, both
non-degenerate, is homeomorphic to a sphere. *Hidden hypotheses:* "only two" is read as exactly two
(on a nonempty compact manifold of positive dimension the extrema already give two); the sphere is
$S^n$ with $n = \dim N$; $N$ has no boundary. In dimension $0$ Milnor's proof does not apply ($f$
may be constant), but every point is critical, so $N$ has two points
(`Morse.reeb_of_finrank_eq_zero`). *Deviation (narrower):* $N$ is a submanifold of a vector space;
the abstract compact (Hausdorff) case is V4.24. The conclusion is a homeomorphism, as in Milnor.
*Proof:* Milnor's, made complete: V3.3 gives the minimum $p$ and the maximum $q$; V3.2 gives the
closed cells $\{f \le f(p) + \varepsilon\}$ and $\{f \ge f(q) - \varepsilon\}$ for small
$\varepsilon$; V3.4 on $[f(p) + \varepsilon, f(q) - \varepsilon]$ carries the first onto $\{f \le
f(q) - \varepsilon\}$ and its boundary onto $\{f = f(q) - \varepsilon\}$; V3.5 glues the two cells.
The normalization $f(p) = 0$, $f(q) = 1$ is not needed.

**V3.7 (subadditive and additive functions; `Morse.IsSubadditive`, `Morse.IsAdditive`).** Spaces are
replaced by the elements of a preordered set $\iota$, $a \le b$ standing for $X_a \subseteq X_b$. A
function on pairs is an integer-valued function $S(a, b)$ of two indices, used only for $a \le b$,
where $S(a, b)$ stands for Milnor's $S(X_b, X_a)$ (the smaller space is written first). $S$ is
subadditive if $S(a, c) \le S(a, b) + S(b, c)$ whenever $a \le b \le c$, and additive if equality
always holds. *Book:* p. 28: $S$ is an integer-valued function on certain pairs of spaces,
subadditive if $S(X, Z) \le S(X, Y) + S(Y, Z)$ whenever $X \supset Y \supset Z$, additive if
equality holds. *Hidden hypotheses:* the class of pairs on which $S$ is defined must be closed under
the passage from $(X, Y), (Y, Z)$ to $(X, Z)$; Milnor does not say which pairs. Here every pair $a
\le b$ of the index set is allowed. *Deviation (restated):* indices of a preorder in place of
spaces, and the reversed argument order.

**V3.8 (Lemma 5.1; `Morse.IsSubadditive.le_sum`, `Morse.IsAdditive.eq_sum`,
`Morse.le_sum_of_chain`).** If $S$ is subadditive and $X_0 \le X_1 \le \dots \le X_n$ with $n \ge
1$, then $S(X_0, X_n) \le \sum_{k=0}^{n-1} S(X_k, X_{k+1})$, that is, in Milnor's notation, $S(X_n,
X_0) \le \sum_{i=1}^n S(X_i, X_{i-1})$; if $S$ is additive, equality holds. `Morse.le_sum_of_chain`
assumes subadditivity only on the triples $X_0 \le X_m \le X_{m+1}$, which is all the induction
uses. *Book:* Lemma 5.1 (p. 28), by induction on $n$; with $X_0 = \emptyset$ it gives inequality
(1). *Hidden hypotheses:* $n \ge 1$: for $n = 0$ the statement would be $S(X_0, X_0) \le 0$, which
subadditivity does not give (it gives $S(X, X) \ge 0$).

**V3.9 (the homology of a filtration and its Morse numbers; `Morse.LongExactSeq`,
`Morse.FiltrationHomology`, `Morse.morseNumber`, `Morse.altSum`,
`Morse.FiltrationHomology.ofSteps`).** This is the structure in which §5 is verified. Fix a field
$F$ and a preordered set $\iota$. A *homology of a filtration* assigns to every degree $i \ge 0$ and
indices $a, b$ a vector space $H_i(a, b)$ over $F$, to be read as $H_i(X_b, X_a; F)$ (only $a \le b$
is ever used), such that $H_i(a, b)$ is finite-dimensional for $a \le b$, and assigns to every
triple $a \le b \le c$ a long exact sequence of $F$-linear maps
$$\cdots \to H_i(a,b) \to H_i(a,c) \to H_i(b,c) \xrightarrow{\ \partial\ } H_{i-1}(a,b) \to \cdots
\to H_0(a,b) \to H_0(a,c) \to H_0(b,c) \to 0,$$
exact at every term, the last condition being the surjectivity of $H_0(a, c) \to H_0(b, c)$. Nothing
else is assumed: no functoriality, no compatibility between the sequences of different triples, no
vanishing of $H_*(a, a)$, no excision. For a chain $X_0 \le X_1 \le \dots \le X_n$ the Betti numbers
are $R_i = \dim H_i(X_0, X_n)$ (Milnor's $R_i(M)$ when $X_0 = \emptyset$, $X_n = M$), and the Morse
numbers are $C_i = \sum_{k<n} \dim H_i(X_k, X_{k+1})$. The truncated alternating sum of a sequence
$d$ is $S_\lambda(d) = d_\lambda - d_{\lambda - 1} + \dots \pm d_0$. On a chain indexed by $\mathbb
N$, `Morse.FiltrationHomology.ofSteps` builds the structure from the exact sequences and the
finiteness of the slabs $H_i(k, k+1)$ and of the $H_i(k, k)$ alone, so that the finiteness of
$H_*(M; F)$ is a consequence rather than an assumption. *Book:* pp. 28–30: singular homology with
coefficients in a field $F$, the exact sequence of a triple $X \supset Y \supset Z$, and
$R_\lambda(X, Y) = \dim H_\lambda(X, Y; F)$ for the pairs where it is finite. *Hidden hypotheses:*
that the sequence of a triple ends with $\to 0$ (Milnor's exact sequence "$\dots \to D \to 0$",
p. 29) is the surjectivity of $H_0(X, Z) \to H_0(X, Y)$. *Deviation (restated):* this is an
abstract structure, not singular homology. Every statement V3.10–V3.15 is a theorem about every
such structure; singular homology over a field is an instance (V3.32), and the slab computation of
p. 29 that applies it to a manifold is V3.33–V3.34.

**V3.10 ($R_\lambda$ is subadditive and $\chi$ is additive; `Morse.LongExactSeq.finrank_le`,
`Morse.LongExactSeq.finiteDimensional_middle`, `Morse.FiltrationHomology.isSubadditive_finrank`,
`Morse.altSum_finrank_eq_zero_of_exact`, `Morse.LongExactSeq.altSum_eq_of_finrank_eq_zero`,
`Morse.FiltrationHomology.isAdditive_eulerChar`).** For a homology of a filtration: (i) for every
$\lambda$, $(a, b) \mapsto \dim H_\lambda(a, b)$ is subadditive; and in the segment $H_\lambda(a, b)
\to H_\lambda(a, c) \to H_\lambda(b, c)$ of a long exact sequence, the middle term is
finite-dimensional when the outer two are. (ii) The alternating sum of the dimensions in a finite
exact sequence $0 \to V_n \to \dots \to V_0 \to 0$ of finite-dimensional spaces is $0$. (iii) If
$H_{N+1}(a, b) = 0$ for all $a \le b$, the truncated Euler characteristic $\chi_N(a, b) = \sum_{i
\le N} (-1)^i \dim H_i(a, b)$ is additive. *Book:* p. 28: $R_\lambda$ is subadditive, "as is easily
seen" from the exact segment $H_\lambda(Y, Z) \to H_\lambda(X, Z) \to H_\lambda(X, Y)$; the Euler
characteristic $\chi(X, Y) = \sum (-1)^\lambda R_\lambda(X, Y)$ is additive, asserted without
argument. *Hidden hypotheses:* the closedness of the class of pairs with finite-dimensional homology
under triples (the second half of (i)); additivity of $\chi$ needs the total homology to be finite,
here replaced by truncation at $N$ with vanishing in degree $N + 1$. *Deviation (restated):* $\chi$
is truncated at a degree $N$; it is Milnor's $\chi$ when the homology vanishes above $N$.

**V3.11 (Theorem 5.2, the weak Morse inequalities;
`Morse.FiltrationHomology.finrank_le_morseNumber`,
`Morse.FiltrationHomology.sum_neg_one_pow_finrank_eq`, `Morse.morseNumber_eq_card`,
`Morse.morseNumber_eq_card_of_single`, `Morse.FiltrationHomology.weak_morse_inequality`).** For a
homology of a filtration and a chain $X_0 \le \dots \le X_n$ with $n \ge 1$: (2) $R_\lambda \le
C_\lambda$ for every $\lambda$; (3) if no slab $H_{N+1}(X_k, X_{k+1})$ is nonzero, then $\sum_{i \le
N} (-1)^i R_i = \sum_{i \le N} (-1)^i C_i$. In terms of critical points: let $P$ be a finite set
(the critical points), each $p \in P$ carrying an index $\operatorname{ind}(p)$ and a step
$\operatorname{step}(p) < n$ (the slab containing it), and assume the *cell hypothesis* $\dim
H_i(X_k, X_{k+1}) = \#\{p \in P : \operatorname{step}(p) = k,\ \operatorname{ind}(p) = i\}$ for all
$k < n$ and all $i$. Then $C_i = \#\{p \in P : \operatorname{ind}(p) = i\}$ and (2) reads $R_\lambda
\le \#\{p \in P : \operatorname{ind}(p) = \lambda\}$; with one critical point per slab this is
Milnor's count. *Book:* Theorem 5.2 (p. 29): on the compact manifold $M$, $R_\lambda(M) \le
C_\lambda$ and $\sum (-1)^\lambda R_\lambda(M) = \sum (-1)^\lambda C_\lambda$, $C_\lambda$ the
number of critical points of index $\lambda$; just before, $H_*(M^{a_i}, M^{a_{i-1}})$ is computed
as the coefficient group in dimension $\lambda_i$ and $0$ otherwise, "by excision". *Hidden
hypotheses:* Milnor's choice of $a_1 < \dots < a_k$ with exactly $i$ critical points in $M^{a_i}$
needs distinct critical values (the cell hypothesis allows any number of critical points per slab);
his chain starts at $\emptyset = M^{a_0}$ with $a_0$ never introduced (here $X_0$ is arbitrary and
$R_i$ is the homology of the pair); the slab identification is not literally an excision (one
thickens first). *Deviation (narrower):* the topological input, the slab computation of p. 29
(Theorems 3.1 and 3.2, homotopy invariance, excision and $H_*(D^\lambda, S^{\lambda-1})$), is the
cell hypothesis, not a theorem; and $R_\lambda$ is a dimension in the abstract structure of V3.9,
not a Betti number of a manifold. Both are supplied for singular homology in V3.32–V3.35.

**V3.12 (Lemma 5.3; `Morse.finrank_range_eq_altSum`, `Morse.LongExactSeq.altSum_le`,
`Morse.FiltrationHomology.isSubadditive_altSum`).** (i) If $V_{n+1} \xrightarrow{h} V_n \to \dots
\to V_0 \to 0$ is exact at $V_0, \dots, V_n$ and all $V_k$ are finite-dimensional, then
$\operatorname{rank} h = \dim V_n - \dim V_{n-1} + \dots \pm \dim V_0$. (ii) For the sequence of a
triple $a \le b \le c$, $S_\lambda(a, c) \le S_\lambda(a, b) + S_\lambda(b, c)$, where $S_\lambda =
R_\lambda - R_{\lambda-1} + \dots \pm R_0$ of the pair; the proof is Milnor's, through the identity
$\operatorname{rank}(\partial : H_{\lambda+1}(b, c) \to H_\lambda(a, b)) = S_\lambda(a, b) -
S_\lambda(a, c) + S_\lambda(b, c)$, which is proved as a lemma of its own. (iii) Hence $S_\lambda$
is subadditive. *Book:* Lemma 5.3 (pp. 29–30), with Milnor's computation of $\operatorname{rank} h$
and of $\operatorname{rank} \partial$. *Hidden hypotheses:* finite dimensions, for rank–nullity.

**V3.13 (the Morse inequalities $(4_\lambda)$; `Morse.FiltrationHomology.altSum_le_morseNumber`,
`Morse.FiltrationHomology.morse_inequality`).** For a homology of a filtration and a chain with $n
\ge 1$: $R_\lambda - R_{\lambda-1} + \dots \pm R_0 \le C_\lambda - C_{\lambda-1} + \dots \pm C_0$
for every $\lambda$; under the cell hypothesis of V3.11, with $C_i = \#\{p \in P :
\operatorname{ind}(p) = i\}$. *Book:* p. 30, inequality $(4_\lambda)$, from Lemma 5.1 for
$S_\lambda$ on $\emptyset \subset M^{a_1} \subset \dots \subset M^{a_k}$. *Hidden hypotheses:* as in
V3.11. *Deviation (narrower):* as in V3.11.

**V3.14 (consequences of $(4_\lambda)$; `Morse.le_of_altSum_le`, `Morse.altSum_eq_of_altSum_le`,
`Morse.sum_neg_one_pow_eq_of_altSum_le`, `Morse.FiltrationHomology.finrank_eq_zero_of_forall_ne`,
`Morse.FiltrationHomology.euler_characteristic_eq`).** Let $b, c$ be integer sequences with
$(4_\lambda)$, $S_\lambda(b) \le S_\lambda(c)$, for every $\lambda$. Then $b_\lambda \le c_\lambda$
for every $\lambda$; if $c_{\lambda+1} = 0$ and $b_{\lambda+1} \ge 0$, then $S_\lambda(b) =
S_\lambda(c)$; if $b \ge 0$ and $c_{N+1} = 0$, then $\sum_{i \le N} (-1)^i b_i = \sum_{i \le N}
(-1)^i c_i$. For a filtration with the cell hypothesis, $R_l = 0$ if no critical point has index
$l$, and, if every index is at most $N$, $\sum_{i \le N} (-1)^i R_i = \sum_{p \in P}
(-1)^{\operatorname{ind}(p)}$, the left side being the whole alternating sum. *Book:* p. 30: adding
$(4_\lambda)$ and $(4_{\lambda-1})$ gives $(2_\lambda)$; comparing $(4_\lambda)$ with
$(4_{\lambda-1})$ for $\lambda > n$ gives (3); if $C_{\lambda+1} = 0$ then $R_{\lambda+1} = 0$ and
$(4_\lambda)$ is an equality. *Hidden hypotheses:* only $\lambda = n + 1$ matters in the comparison
for $\lambda > n$, and it uses $C_{n+1} = 0$ and $R_{n+1} \ge 0$; that the left side of (3) is the
whole alternating sum uses $R_i = 0$ for $i > n$, which is (2). Milnor's intermediate step
$R_{\lambda+1} = 0$ is not needed: $R_{\lambda+1} \ge 0$ suffices.

**V3.15 (Corollary 5.4 and the lacunary principle; `Morse.eq_of_altSum_le_succ`,
`Morse.eq_of_altSum_le_zero`, `Morse.FiltrationHomology.finrank_eq_morseNumber_of_succ`,
`Morse.FiltrationHomology.finrank_eq_morseNumber_of_zero`, `Morse.eq_of_altSum_le_of_lacunary`,
`Morse.lacunary_of_odd`, `Morse.FiltrationHomology.finrank_eq_morseNumber_of_lacunary`).** For
sequences $b \ge 0$ and $c$ satisfying every $(4_\lambda)$, and so for the Betti and Morse numbers
of a chain: if $\lambda \ge 1$ and $c_{\lambda+1} = c_{\lambda-1} = 0$, then $b_\lambda = c_\lambda$
and $b_{\lambda+1} = b_{\lambda-1} = 0$; if $c_1 = 0$, then $b_0 = c_0$ and $b_1 = 0$; and if no two
consecutive $c_i$ are nonzero (for instance, if every odd $c_i$ vanishes), then $b_i = c_i$ for
every $i$. *Book:* Corollary 5.4 (p. 31): if $C_{\lambda+1} = C_{\lambda-1} = 0$ then $R_\lambda =
C_\lambda$ and $R_{\lambda+1} = R_{\lambda-1} = 0$; Milnor adds that this gives the homology of
complex projective space (§4) without Theorem 3.5. *Hidden hypotheses:* for $\lambda = 0$ the
condition $C_{\lambda-1} = 0$ is empty. *Deviation (not in the book):* the lacunary form. Corollary
5.4 yields Betti numbers over a field, not integral homology groups. For the Betti numbers of a
compact manifold it is V3.37 and V3.39; $\mathbb CP^n$ is not constructed (see the list at the
end).

**V3.16 (the numbers $C_\lambda$ of a function; `Morse.critCount`,
`Morse.finsum_neg_one_pow_indexM_eq_sum_critCount`).** For $f : M \to \mathbb R$ on a manifold
modelled on a real normed space $E$, $C_\lambda(f)$ is the number of critical points of $f$ of index
$\lambda$, set to $0$ if there are infinitely many. If $E$ is finite-dimensional and $f$ has
finitely many critical points, $\sum_{p \text{ critical}} (-1)^{\operatorname{index}_p f} =
\sum_{\lambda=0}^{\dim E} (-1)^\lambda C_\lambda(f)$. *Book:* p. 29: $C_\lambda$ is the number of
critical points of index $\lambda$. *Hidden hypotheses:* finiteness, which holds for a Morse
function on a compact manifold (non-degenerate critical points are isolated,
`Morse.IsMorseFunction.finite_setOf_isCriticalPointM`); $C_\lambda = 0$ for $\lambda > \dim M$,
which is why Milnor's sum stops at $\pm C_n$ with $n = \dim M$. *Deviation (restated):* the
convention for infinitely many critical points never applies in the theorems below.

**V3.17 (the Poincaré–Hopf integer; `Morse.IsEulerNumber`, `Morse.exists_isEulerNumber`).** Let $N
\subseteq \mathbb R^{K+1}$ be a compact nonempty slice submanifold modelled on $\mathbb R^{d+1}$. An
integer $\chi$ is an *Euler number* of $N$ if for every smooth tangent vector field $v$ on $N$ whose
zeros are finitely many distinct points $z_1, \dots, z_j$, $\sum_i \operatorname{index}_{z_i}(v) =
\chi$, the index being that of the Milnor project (`Milnor.Tub.indexN`, its V6.8: the index at $z_i$
of the extension $x \mapsto v(r(x)) + (x - r(x))$ of $v$ to a tubular neighbourhood, $r$ the
nearest-point retraction). For $K \ge 1$ an Euler number exists: this is the Poincaré–Hopf theorem
of the Milnor project (`Milnor.Tub.poincare_hopf`, its V6.9), where it is the degree of the Gauss
map of the boundary of a tubular neighbourhood. It is unique: by V3.20 every Euler number equals the
alternating count of the critical points of any Morse function, and $N$ carries one (V4.13). Below
it is written $\chi(N)$. *Book:* Milnor's $\chi$ is the Euler characteristic $\sum (-1)^\lambda
R_\lambda$ (p. 28); in Application 2 (pp. 36–37) he uses that the index sum of a vector field is a
topological invariant (citing Steenrod, §39.7). *Hidden hypotheses:* $N$ compact and nonempty; $K
\ge 1$, i.e. ambient dimension at least $2$; the zeros indexed without repetition. *Deviation
(restated):* $\chi(N)$ is defined through vector fields; its identification with $\sum_i (-1)^i
\dim H_i(N; F)$ is V3.38.

**V3.18 ($\operatorname{sgn}\det = (-1)^{\mathrm{index}}$; `Morse.index_eq_ncard_eigenvalues_neg`,
`Morse.isNondegenerate_iff_bijective`, `Morse.sgn_det_eq_neg_one_pow_index`,
`Morse.sgn_det_eq_neg_one_pow_index_of_symm`).** Let $H$ be a symmetric bilinear form on a
finite-dimensional real inner product space and $A$ the operator with $H(v, w) = \langle Av,
w\rangle$. The index of $H$ (the largest dimension of a subspace on which $H$ is negative definite)
is the number of negative eigenvalues of $A$; $H$ is non-degenerate iff $A$ is bijective; and if $H$
is non-degenerate, $\operatorname{sgn}\det A = (-1)^{\operatorname{index} H}$. The right side does
not involve the inner product, so the sign is the same for the operators representing $H$ with
respect to any two inner products. *Book:* used without comment in Application 2 (p. 36), in the
claim that $(-1)^\lambda$ is the index of $\operatorname{grad} f$. *Hidden hypotheses:* none.
*Deviation (not in the book).* *Proof:* the spectral theorem and Sylvester's law of inertia, from
Mathlib.

**V3.19 (the index of the gradient field is $(-1)^\lambda$; `Morse.tangentialGradient`,
`Morse.inner_tangentialGradient`, `Morse.tangentialGradient_eq_zero_iff`,
`Morse.dret_eq_starProjection`, `Morse.contMDiff_tangentialGradient`, `Morse.index_hessT`,
`Morse.isNondegenerate_hessT_iff`, `Morse.bijective_dvT_tangentialGradient`,
`Morse.indexN_tangentialGradient`).** Let $N \subseteq \mathbb R^{K+1}$, $K \ge 1$, be a compact
nonempty slice submanifold modelled on $\mathbb R^{d+1}$, and $F : \mathbb R^{K+1} \to \mathbb R$
smooth, $f = F|_N$. The tangential gradient $v(q) = P_q \nabla F(q)$, $P_q$ the orthogonal
projection onto $T_qN$, is the gradient of $f$ for the metric induced from $\mathbb R^{K+1}$
($\langle v(q), t\rangle = dF_q(t)$ for $t \in T_qN$); its zeros are exactly the critical points of
$f$; it is a smooth tangent field. If $q$ is a non-degenerate critical point of $f$ of index
$\lambda$, the derivative of $v$ at $q$ is an invertible endomorphism of $T_qN$ whose determinant
has sign $(-1)^\lambda$, and the index of $v$ at $q$ is $(-1)^\lambda$. *Book:* Application 2 (p.
36): $(-1)^\lambda$ is the index of $\operatorname{grad} f$ at a point where $f$ has index
$\lambda$, asserted without proof. *Hidden hypotheses:* a metric must be chosen (here the induced
one); the Hessian of $F|_N$ is not the restriction of the Hessian of $F$, since at a critical point
$\nabla F(q)$ is normal to $N$, not zero; the derivative of $v$ at $q$ is an endomorphism of $T_qN$
only because $v(q) = 0$ (proved in the Milnor project, its V6.13; `Milnor.Tub.dvT`). *Deviation (not
in the book):* Milnor gives no proof. *Proof:* $F$ is replaced by $F \circ r$, $r$ the nearest-point
retraction, whose derivative at a point of $N$ is $P_q$: $F \circ r$ agrees with $F$ on $N$ and is
critical at $q$ as a function on $\mathbb R^{K+1}$, $v = \nabla(F \circ r)$ on $N$, and the Hessian
of $f$ in a slice parametrization is the Hessian of $F \circ r$ restricted to $T_qN$; then V3.18,
and the index of a non-degenerate zero (`Milnor.Tub.indexN_eq_sgn_det`, the Milnor project's V6.14).

**V3.20 (formula (3) without homology; `Morse.IsEulerNumber.finsum_eq_of_ambient`,
`Morse.exists_contDiff_comp_val_eq`, `Morse.IsEulerNumber.finsum_eq`,
`Morse.IsEulerNumber.sum_critCount_eq`, `Morse.exists_eulerNumber_eq_sum_critCount`,
`Morse.sum_critCount_eq_of_isMorseFunction`, `Morse.IsEulerNumber.eq_sum_critCount`).** Let $N
\subseteq \mathbb R^{K+1}$, $K \ge 1$, be a compact nonempty slice submanifold of dimension $d + 1
\ge 1$. There is an integer $\chi(N)$, an Euler number of $N$ in the sense of V3.17, such that every
Morse function $f$ on $N$ (smooth, with only non-degenerate critical points) satisfies
$$\sum_{\lambda=0}^{d+1} (-1)^\lambda C_\lambda(f) = \sum_{q \text{ critical}}
(-1)^{\operatorname{index}_q f} = \chi(N).$$
Consequently the alternating count is the same for all Morse functions on $N$, and every Euler
number of $N$ equals the alternating count of any one Morse function. Every smooth $f : N \to
\mathbb R$ is the restriction of a smooth function on $\mathbb R^{K+1}$
(`Morse.exists_contDiff_comp_val_eq`). *Book:* p. 29: for a compact $M$ and a function with
isolated, non-degenerate critical points, $\chi(M) = C_0 - C_1 + C_2 - \dots \pm C_n$, recorded as
formula (3) of Theorem 5.2; Application 2 (pp. 36–37). *Hidden hypotheses:* "isolated" is redundant
for non-degenerate critical points; $\pm C_n$ takes $n = \dim M$; distinct critical values are not
needed; in Application 2, "any differentiable function" must be one with only non-degenerate
critical points, and "the critical points of $X$" are the zeros of $X$; $\dim N \ge 1$ and $K \ge 1$
(the Milnor project computes the index of a non-degenerate zero only in positive dimension, and its
Poincaré–Hopf theorem needs $K \ge 1$). *Deviation (restated):* $\chi(N)$ is the Poincaré–Hopf
integer; what is verified here is the topological invariance of $\sum (-1)^\lambda C_\lambda$. Its
equality with $\sum (-1)^i R_i(N)$, formula (3) as Milnor states it, is V3.35, and the
identification of $\chi(N)$ with the homological Euler characteristic is V3.38. $N$ is a
submanifold of Euclidean space; for an abstract compact manifold see V4.19. *Proof:* Application 2
run in the direction that needs no homology: the gradient field of $f$ (V3.19) has index sum $\sum
(-1)^\lambda C_\lambda(f)$, and every tangent field has the index sum $\chi(N)$.

**V3.21 (the sphere; `Morse.isEulerNumber_sph`, `Morse.sum_critCount_sph`, `Morse.heightFun`,
`Morse.isCriticalPointM_heightFun_iff`, `Morse.hessT_heightFun`, `Morse.indexM_heightFun_pos`,
`Morse.indexM_heightFun_neg`, `Morse.isMorseFunction_heightFun`, `Morse.critCount_heightFun`,
`Morse.sum_critCount_heightFun`, `Morse.IsEulerNumber.eq_sph`).** Let $S^n \subseteq \mathbb
R^{n+1}$, $n \ge 1$, be the unit sphere, as the slice submanifold `Milnor.Sphere.sphSub` of the
Milnor project. Its Euler number is $1 + (-1)^n$ (from `Milnor.Sphere.indexSum_sph`), so every Morse
function on $S^n$ has $\sum_\lambda (-1)^\lambda C_\lambda = 1 + (-1)^n$. For a unit vector $e$, the
height function $h(x) = \langle e, x\rangle$ on $S^n$ has exactly the critical points $\pm e$; its
Hessian on $T_qS^n = q^\perp$ is $-\langle e, q\rangle\langle \cdot, \cdot\rangle$; it is a Morse
function of index $n$ at $e$ and $0$ at $-e$, so $C_0 = C_n = 1$ and all other $C_\lambda = 0$; and
every Euler number of $S^n$ equals $1 + (-1)^n$, recomputed from $h$ by V3.20. *Book:* not in the
book. *Hidden hypotheses:* $n \ge 1$. *Deviation (not in the book):* a check of V3.20 on $S^n$
against the Milnor project's direct computation of the index sum; $h$ also satisfies the hypotheses
of Reeb's theorem (V3.6).

The next four items are Milnor's opening example (§1, pp. 1–3), from the book pages of Chapter 1.
They are verified here because their Lean files live with this chapter and use V3.20.

**V3.22 (the torus of Diagram 1 is a compact surface; `Morse.torus`, `Morse.Torus.poly`,
`Morse.Torus.mem_torus_iff`, `Morse.Torus.dpoly_ne_zero`, `Morse.Torus.isRegularValue_poly1`,
`Morse.isSliceSubmanifold_torus`, `Morse.isCompact_torus`, `Morse.nonempty_torus`,
`Morse.Torus.mem_tangentSubspace_torus_iff`, `Morse.Torus.finrank_tangentSubspace_torus`).** For $0
< \rho < R$ let $T = \{x \in \mathbb R^3 : (\sqrt{x_1^2 + x_2^2} - R)^2 + x_3^2 = \rho^2\}$, the
torus of revolution about the $x_3$-axis with core radius $R$ and tube radius $\rho$. $T$ is the
zero set of $g(x) = (\|x\|^2 + R^2 - \rho^2)^2 - 4R^2(x_1^2 + x_2^2)$, and $dg$ does not vanish on
$T$; hence $T$ is a $2$-dimensional slice submanifold of $\mathbb R^3$, compact and nonempty, and
its tangent plane at $q$ is $\ker dg_q$, of dimension $2$. *Book:* p. 1: a torus $M$ tangent to a
plane $V$, drawn standing upright (Diagram 1); no equations are given, and nothing is said about why
$M$ is a smooth compact surface. *Hidden hypotheses:* $\rho < R$ (a ring torus, which is smooth; it
also makes the four critical values of V3.23 distinct, which (3) and (4) of p. 1 presuppose).
*Deviation (restated):* the surface is fixed as the torus of revolution.

**V3.23 (the height function: four critical points, of indices $0, 1, 1, 2$; `Morse.Torus.height`,
`Morse.Torus.isCriticalPointM_height_iff`, `Morse.Torus.criticalValues_height`,
`Morse.Torus.onAxis_spec`, `Morse.Torus.pointP_spec`, `Morse.Torus.pointQ_spec`,
`Morse.Torus.pointR_spec`, `Morse.Torus.pointS_spec`, `Morse.Torus.isMorseFunction_height`,
`Morse.Torus.critCount_height`, `Morse.hessian_comp_sliceParam_of_fderiv_eq_zero`,
`Morse.isNondegenerate_and_index_of_diag`).** Let $f = x_1 + R + \rho$ on $T$, the height above the
plane $V = \{x_1 = -(R + \rho)\}$, which touches $T$ at $p = (-(R + \rho), 0, 0)$; the axis of
revolution is parallel to $V$, so the torus stands upright. The critical points of $f$ are exactly
$p$, $q = (-(R - \rho), 0, 0)$, $r = (R - \rho, 0, 0)$ and $s = (R + \rho, 0, 0)$, with critical
values $0, 2\rho, 2R, 2R + 2\rho$. All four are non-degenerate, of indices $0, 1, 1, 2$; $f$ is a
Morse function on $T$, with $C_0 = 1$, $C_1 = 2$, $C_2 = 1$ and $C_\lambda = 0$ for $\lambda \ge 3$.
*Book:* p. 3: the points $p, q, r, s$ at which the homotopy type of $M^a$ changes are the critical
points of $f$; in suitable coordinates $f = x^2 + y^2$ at $p$, $f = \text{const} + x^2 - y^2$ at $q$
and $r$, $f = \text{const} - x^2 - y^2$ at $s$. *Hidden hypotheses:* the upright position (lying
flat, the height function has degenerate critical circles); the critical points and the normal forms
are asserted without verification. *Deviation (restated):* the normal forms are not restated for the
torus; they follow from the lemma of Morse (`Morse.morse_lemmaM`) with the indices computed here.
*Proof:* Lagrange's rule. At a point $(a, 0, 0)$ of $T$, $dg = \kappa\, dx_1$ with $\kappa \ne 0$,
so $G = f - \kappa^{-1} g$ agrees with $f$ on $T$ and is critical at the point as a function on
$\mathbb R^3$; the Hessian of $f|_T$ is then $d^2G$ restricted to the tangent plane, a diagonal form
whose entries are, up to sign, the principal curvatures.

**V3.24 (Milnor's (1) and (5), and Theorem 3.1 on the torus; `Morse.Torus.sublevel_height_eq_empty`,
`Morse.Torus.sublevel_height_eq_univ`, `Morse.theorem_3_1_torus`).** $T^a = \emptyset$ for $a < 0$,
and $T^a = T$ for $a \ge 2R + 2\rho = f(s)$. If $a \le b$ and $[a, b]$ contains none of the critical
values $0, 2\rho, 2R, 2R + 2\rho$, then a smooth diffeomorphism of $T$ carries $T^a$ onto $T^b$,
$T^a$ is a strong deformation retract of $T^b$, and the inclusion $T^a \to T^b$ is a homotopy
equivalence; in particular the $T^a$ with $a$ in any one of $(0, 2\rho)$, $(2\rho, 2R)$, $(2R, 2R +
2\rho)$ are diffeomorphic to one another. *Book:* p. 1: (1) $M^a$ is vacuous if $a < 0 < f(p)$ (as
printed in the scan); (5) $M^a$ is the full torus if $f(s) < a$; (2)–(4) $M^a$ is a $2$-cell, a
cylinder, a compact genus-one surface bounded by a circle. *Hidden hypotheses:* $f(p) = 0$ because
$V$ touches $M$ at $p$, so the hypothesis of (1) must be read as $a < 0 = f(p)$; (5) holds for $a =
f(s)$ as well. *Deviation (narrower):* of (2)–(4) only what Theorem 3.1 gives is verified; the
homeomorphism types are not.

**V3.25 (the Euler number of the torus is $0$; `Morse.isEulerNumber_torus`,
`Morse.IsEulerNumber.eq_torus`, `Morse.sum_critCount_torus`,
`Morse.IsEulerNumber.eq_torus_of_rotation`).** $0$ is an Euler number of $T$ (V3.17), and every
Euler number of $T$ is $0$: by V3.20 from $C_0 - C_1 + C_2 = 1 - 2 + 1$, and independently of Morse
theory, because the rotation field $(-x_2, x_1, 0)$ is a smooth tangent field on $T$ without zeros.
Hence every Morse function on $T$ has $C_0 - C_1 + C_2 = 0$. *Book:* not in the book; p. 2 describes
the passage from (1) to (5) as attaching a $0$-cell, two $1$-cells and a $2$-cell, which gives the
same count. *Hidden hypotheses:* none. *Deviation (not in the book):* the value is the Poincaré–Hopf
integer; by V3.38 it is also the homological Euler characteristic of $T$ (V3.40).

The next six items build the homology that Milnor quotes in §5 (Mathlib, v4.33.1, has the singular
chain complex, absolute singular homology and its homotopy invariance, but no relative homology).
Below, $\Bbbk$ denotes a field (Milnor's $F$; the letter $F$ is kept for ambient functions), and the
spaces whose homology is taken lie in the universe of the coefficients, a formality of the type
theory.

**V3.26 (relative singular homology and the exact sequence of a pair; `Morse.Homology.relChains`,
`Morse.Homology.relHomology`, `Morse.Homology.relShortComplex_shortExact`, `Morse.Homology.relδ`,
`Morse.Homology.relHomology_exact₁`, `Morse.Homology.relHomology_exact₂`,
`Morse.Homology.relHomology_exact₃`, `Morse.Homology.epi_homologyMap_relπ_zero`,
`Morse.Homology.relδ_naturality`, `Morse.Homology.relHomologyInclIso`,
`Morse.Homology.isZero_relHomology_diag`, `Morse.Homology.isIso_relHomology_map`,
`Morse.Homology.relHomology_map_eq_of_homotopy`,
`Morse.Homology.isIso_relHomology_map_of_isStrongDeformationRetract`,
`Morse.Homology.isZero_relHomology_of_isStrongDeformationRetract`,
`Morse.Homology.singularHomologyPretheory`).** Coefficients are an object $R$ of an abelian category
with coproducts (for instance a field, or any commutative ring); pairs $(X, A)$ are embeddings
$A \hookrightarrow X$ (Mathlib's `TopPair`). The relative chain complex $C(X, A)$ is the cokernel of
the chain map $C(A) \to C(X)$ of singular chains, which is injective, so that $0 \to C(A) \to C(X)
\to C(X, A) \to 0$ is exact; $H_n(X, A)$ is its homology, and both are functorial in maps of pairs.
The sequence
$$\cdots \to H_{n+1}(X, A) \xrightarrow{\ \partial\ } H_n(A) \to H_n(X) \to H_n(X, A)
\xrightarrow{\ \partial\ } H_{n-1}(A) \to \cdots \to H_0(X) \to H_0(X, A) \to 0$$
is exact at every place, and $\partial$ is natural in maps of pairs. $H_n(X, \emptyset) \cong H_n(X)$
naturally, and $H_n(X, X) = 0$. A map of pairs inducing isomorphisms in the homology of both spaces
induces isomorphisms in relative homology (the five lemma). Maps of pairs that are homotopic through
maps of pairs induce the same maps in relative homology. If $A \subseteq B \subseteq X$ are subsets
of a space and $B$ is a strong deformation retract of $X$, then $H_n(B, A) \to H_n(X, A)$ is an
isomorphism and $H_n(X, B) = 0$. With these data singular homology is a homotopy-invariant homology
pretheory in the sense of Mathlib's formulation of the Eilenberg–Steenrod axioms. *Book:* p. 28:
homology of pairs with coefficients in a field and its exact sequences; p. 29: pairs replaced by
homotopy equivalent ones; all quoted as standard. *Hidden hypotheses:* the first equality of p. 29
needs homotopy equivalences of pairs, here strong deformation retracts. *Deviation (not in the
book):* built here, since Mathlib has no relative singular homology. *Proof:* homotopy invariance
for pairs from the absolute one, through the cylinder $(X \times I, A \times I)$ and the five lemma.

**V3.27 (the exact sequence of a triple; `Morse.Homology.TopTriple`, `Morse.Homology.TopTriple.ofSubsets`,
`Morse.Homology.cokernel_comp_shortExact`, `Morse.Homology.TopTriple.shortComplex_shortExact`,
`Morse.Homology.TopTriple.δ`, `Morse.Homology.TopTriple.exact₁`, `Morse.Homology.TopTriple.exact₂`,
`Morse.Homology.TopTriple.exact₃`, `Morse.Homology.TopTriple.epi_map₂_zero`,
`Morse.Homology.TopTriple.δ_eq`).** For a triple $Z \subseteq Y \subseteq X$ (two composable
embeddings, for instance subsets $A \subseteq B \subseteq D$ of a space), the inclusions of pairs
give a short exact sequence $0 \to C(Y, Z) \to C(X, Z) \to C(X, Y) \to 0$, hence the sequence
$$\cdots \to H_{n+1}(X, Y) \xrightarrow{\ \partial\ } H_n(Y, Z) \to H_n(X, Z) \to H_n(X, Y)
\xrightarrow{\ \partial\ } H_{n-1}(Y, Z) \to \cdots \to H_0(X, Z) \to H_0(X, Y) \to 0,$$
exact at every place, whose $\partial$ is the boundary of the pair $(X, Y)$ followed by $H_n(Y) \to
H_n(Y, Z)$. *Book:* p. 28, the segment $H_\lambda(Y, Z) \to H_\lambda(X, Z) \to H_\lambda(X, Y)$;
p. 30, "the homology exact sequence of a triple $X \supset Y \supset Z$", used with its final
"$\to 0$" (p. 29). *Hidden hypotheses:* none. *Deviation (not in the book):* quoted by Milnor, built
here. *Proof:* the third isomorphism theorem $(C(X)/C(Z))/(C(Y)/C(Z)) \cong C(X)/C(Y)$, in any
abelian category.

**V3.28 (excision; `Morse.Homology.smallChainsHomotopyEquiv`, `Morse.Homology.excision_of_union`,
`Morse.Homology.excision`, `Morse.Homology.excision_of_closure_subset_interior`).** (i) If the
interiors of a family of subsets of a space $X$ cover $X$, the inclusion of the chains made of
simplices each lying in one member of the family into all singular chains is a chain homotopy
equivalence (any ring of coefficients). With coefficients in a commutative ring $R$, for subsets of
a space $E$, interiors and closures taken in $X$: (ii) if $A, B \subseteq X$ have interiors covering
$X$, then $(B, A \cap B) \to (X, A)$ induces isomorphisms $H_n(B, A \cap B) \cong H_n(X, A)$ for all
$n$; (iii) if $Z \subseteq A \subseteq X$ and the closure of $Z$ lies in the interior of $A$, then
$(X \setminus Z, A \setminus Z) \to (X, A)$ induces isomorphisms in all degrees; the same holds with
closure and interior taken in $E$. *Book:* p. 29, "by excision", quoted. *Hidden hypotheses:* the
step Milnor calls excision is not literally an instance of (iii) (V3.31). *Deviation (not in the
book):* proved here (Hatcher, *Algebraic Topology*, Proposition 2.21 and Theorem 2.20), by
barycentric subdivision with the diameter bound $(n/(n+1))^k$.

**V3.29 (the Mayer–Vietoris sequence; `Morse.Homology.mvShortComplex_shortExact`,
`Morse.Homology.mvMap₁`, `Morse.Homology.mvMap₂`, `Morse.Homology.mvδ`, `Morse.Homology.mv_exact₁`,
`Morse.Homology.mv_exact₂`, `Morse.Homology.mv_exact₃`).** With coefficients in a commutative ring
$R$: if $A, B \subseteq X$ have interiors covering $X$, then
$$\cdots \to H_{n+1}(X) \xrightarrow{\ \partial\ } H_n(A \cap B) \xrightarrow{(i_*, -i'_*)} H_n(A)
\oplus H_n(B) \xrightarrow{j_* + j'_*} H_n(X) \xrightarrow{\ \partial\ } H_{n-1}(A \cap B) \to
\cdots,$$
$i, i', j, j'$ the inclusions, is exact at every place. *Book:* not used in §5. *Hidden
hypotheses:* none. *Deviation (not in the book):* part of the infrastructure; the naturality of
$\partial$ is not proved. *Proof:* the short exact sequence $0 \to C(A \cap B) \to C(A) \oplus C(B)
\to C^{\{A, B\}}(X) \to 0$ and (i) of V3.28.

**V3.30 (the homology of disks, spheres and cells; `Morse.Homology.relHomologyDiskPairIso`,
`Morse.Homology.isZero_relHomology_diskPair`, `Morse.Homology.finrank_relHomology_diskPair`,
`Morse.Homology.sphereHomologyZeroIso`, `Morse.Homology.sphereHomologyTopIso`,
`Morse.Homology.sphereHomologyZeroIsoBiprod`, `Morse.Homology.isZero_sphereHomology`,
`Morse.Homology.finrank_sphereHomology`, `Morse.Homology.cellPair`, `Morse.Homology.cellPairIso`,
`Morse.Homology.isZero_relHomology_cellPair`, `Morse.Homology.finrank_homology_imageSphere`,
`Morse.Homology.relHomologyTopDiskPairIso`).** Coefficients in a commutative ring $R$; $D^n$ and
$S^{n-1}$ are the closed unit ball and the unit sphere of $\mathbb R^n$ ($S^{-1} = \emptyset$).
$H_i(D^n, S^{n-1}) \cong R$ for $i = n$, and $H_i(D^n, S^{n-1}) = 0$ for $i \ne n$. For $n \ge 1$,
$H_0(S^n) \cong R$, $H_n(S^n) \cong R$ and $H_i(S^n) = 0$ for $i \ne 0, n$; $H_0(S^0) \cong R \oplus
R$. Over a field, $\dim H_i(D^n, S^{n-1}) = [i = n]$ and $\dim H_i(S^n) = [i = 0] + [i = n]$. More
generally, if $E$ is Hausdorff and $\chi : \mathbb R^k \to E$ is continuous and injective on $D^k$,
the pair $(\chi(D^k), \chi(S^{k-1}))$ has the homology of $(D^k, S^{k-1})$; an image of $S^n$ under
a map continuous and injective on it has the homology of $S^n$; and so has Mathlib's disk pair, in
every universe. *Book:* p. 29: $H_*(e^\lambda, \dot e^\lambda)$ is the coefficient group in
dimension $\lambda$ and $0$ otherwise, quoted. *Hidden hypotheses:* none. *Deviation (not in the
book):* computed here. *Proof:* induction on $k$, through the boundary of the triple
$\{q\} \subseteq \chi(S^k) \subseteq \chi(D^{k+1})$, $q$ a point onto which the cell contracts, and
excision for the upper hemisphere of $S^k$ attached to the lower one (V3.31).

**V3.31 (attaching cells to a closed set; `Morse.Homology.isIso_relHomology_map_cellPair`,
`Morse.Homology.relHomology_cellAttach_iso`, `Morse.Homology.relHomologyCellAttachTopIso`,
`Morse.Homology.isZero_relHomology_cellAttach`, `Morse.Homology.finrank_relHomology_cellAttach`,
`Morse.Homology.finrank_relHomology_cellsAttach`, `Morse.Homology.relHomology_cellsAttach_iso`,
`Morse.Homology.isZero_relHomology_cellsAttach`).** Let $E$ be a Hausdorff space, $Y \subseteq X
\subseteq E$ with $Y$ closed, and $\chi_j : \mathbb R^{k_j} \to E$, $j = 1, \dots, m$, maps
continuous and injective on the closed unit balls $D^{k_j}$, whose cells $e_j = \chi_j(D^{k_j})$ are
pairwise disjoint, such that $\chi_j(z) \in Y$ exactly when $\|z\| = 1$, and $X = Y \cup e_1 \cup
\dots \cup e_m$. Coefficients in a commutative ring $R$. For one cell of dimension $k$, the
inclusion $(e_1, \chi_1(S^{k-1})) \to (X, Y)$ and the characteristic map $(D^k, S^{k-1}) \to (X, Y)$
induce isomorphisms in all degrees: $H_k(X, Y) \cong R$ and $H_i(X, Y) = 0$ for $i \ne k$ (the
first statement holds for the unit ball of any finite-dimensional normed space). For several cells,
$H_i(X, Y) \cong R^{c_i}$, $c_i$ the number of cells of dimension $i$, so $H_i(X, Y) = 0$ when no
cell has dimension $i$, and over a field $\dim H_i(X, Y) = c_i$. *Book:* p. 29: $H_*(M^{a_{i-1}}
\cup e^{\lambda_i}, M^{a_{i-1}}) = H_*(e^{\lambda_i}, \dot e^{\lambda_i})$ "by excision". *Hidden
hypotheses:* this is not literally excision: the closure of the set to be excised is not inside the
interior of $M^{a_{i-1}}$. One first deforms $X$ minus the centre of the cell onto $Y$ (pushing the
punctured cell radially onto its boundary), then excises; $Y$ must be closed. With several cells
on one level (Remark 3.3) the exact sequence of a triple gives only an inequality of dimensions;
additivity uses the disjointness of the cells. *Deviation (stronger):* any number of disjoint cells,
and any commutative ring of coefficients; this is the exposition's Lemma E.

The remaining items are Milnor's statements, in singular homology over a field.

**V3.32 (the Morse inequalities for any filtration of a space; `Morse.Homology.TopTriple.longExactSeq`,
`Morse.Homology.subsetHomology`, `Morse.Homology.filtrationHomology`,
`Morse.Homology.singularMorseNumber`, `Morse.Homology.finiteDimensional_subsetHomology_of_steps`,
`Morse.Homology.singular_weak_morse_inequality`, `Morse.Homology.singular_morse_inequality`,
`Morse.Homology.singular_euler_characteristic`, `Morse.Homology.singularMorseNumber_eq_card`,
`Morse.Homology.singular_weak_morse_inequality_of_cells`,
`Morse.Homology.singular_morse_inequality_of_cells`,
`Morse.Homology.singular_euler_characteristic_of_cells`).** Let $X_0 \subseteq X_1 \subseteq \cdots$
be subsets of a space $E$. With $H_i(a, b) = H_i(X_b, X_a; \Bbbk)$ for $a \le b$ and the exact
sequences of triples of V3.27, singular homology is a homology of a filtration in the sense of V3.9,
provided every step $(X_{k+1}, X_k)$ has finite-dimensional homology. Consequently, for $n \ge 1$, if
the steps $k < n$ have finite-dimensional homology, so has $(X_n, X_0)$, and with $b_i = \dim
H_i(X_n, X_0; \Bbbk)$ and $C_i = \sum_{k < n} \dim H_i(X_{k+1}, X_k; \Bbbk)$: $b_l \le C_l$;
$b_l - b_{l-1} + \dots \pm b_0 \le C_l - C_{l-1} + \dots \pm C_0$ for every $l$; and $\sum_{i \le N}
(-1)^i b_i = \sum_{i \le N} (-1)^i C_i$ if no step has homology in degree $N + 1$. Under the cell
hypothesis of V3.11 ($\dim H_i(X_{k+1}, X_k; \Bbbk)$ is the number of points of a finite set $P$ of
critical points that lie in step $k$ and have index $i$), $C_i$ is the number of points of $P$ of
index $i$, the three statements hold with these $C_i$, and the alternating sum is $\sum_{p \in P}
(-1)^{\operatorname{ind} p}$ when every index is at most $N$. *Book:* pp. 28–30: Lemma 5.1 and
Lemma 5.3 applied to $\emptyset = M^{a_0} \subset \dots \subset M^{a_k} = M$, giving Theorem 5.2
and $(4_\lambda)$. *Hidden hypotheses:* as in V3.10–V3.11; finiteness of $H_*(X_n, X_0)$ is a
consequence, not an assumption. *Deviation (restated):* the instance of V3.9 that V3.9–V3.15 lacked;
it applies to any filtration of any space.

**V3.33 (Betti numbers, and the homology of a slab in the abstract; `Morse.Homology.spaceHomology`,
`Morse.Homology.bettiNumber`, `Morse.Homology.bettiNumber_eq_of_homeomorph`,
`Morse.Homology.finrank_subsetHomology_eq_bettiNumber`, `Morse.Homology.subsetHomologyEquivOfIsSDRBottom`,
`Morse.Homology.CellAttachHomology`, `Morse.Homology.cellAttachHomology`,
`Morse.Homology.finrank_subsetHomology_of_cells`).** For a space $X$, $b_i(X) = \dim_\Bbbk H_i(X;
\Bbbk)$ (Mathlib's singular homology), Milnor's $R_i(X)$; it is $0$ by convention if $H_i(X; \Bbbk)$
is infinite-dimensional, which never happens for the spaces below. Homeomorphic spaces have the same
Betti numbers, and $H_i(E, \emptyset) = H_i(E)$. If $A \subseteq B \subseteq D$ and $A$ is a strong
deformation retract of $B$, then $H_i(D, A) \cong H_i(D, B)$, by the sequence of the triple, in
which $H_*(B, A) = 0$ (the deformation of $B$ onto $A$ need not extend to $D$). The cell computation
of V3.31 (several disjoint cells attached to a closed subset of a Hausdorff space give relative
homology of dimension the number of cells in each degree) holds over every field. The slab lemma:
let $A \subseteq B \subseteq X' \subseteq X$ be subsets of a Hausdorff space, $B$ closed, and $e_1,
\dots, e_m$ pairwise disjoint cells attached to $B$ as in V3.31, with $B \cup e_1 \cup \dots \cup e_m
\subseteq X'$; if $A$ is a strong deformation retract of $B$, $B \cup e_1 \cup \dots \cup e_m$ one of
$X'$, and $X'$ one of $X$, then $H_i(X, A; \Bbbk)$ is finite-dimensional, of dimension the number of
cells of dimension $i$. *Book:* p. 28, $R_\lambda$; p. 29: $H_*(M^{a_i}, M^{a_{i-1}}) =
H_*(M^{a_{i-1}} \cup e^{\lambda_i}, M^{a_{i-1}}) = H_*(e^{\lambda_i}, \dot e^{\lambda_i})$.
*Hidden hypotheses:* the first equality is about pairs, not spaces: the top of a pair moves along
deformations that fix the bottom, but the bottom moves only through the sequence of a triple; this
needs strong deformation retracts, whereas Milnor states Theorem 3.2 only up to homotopy type.
*Deviation (restated):* for $A = M^{a_{i-1}}$, $B = M^{c - \varepsilon}$, $X' = M^{c + \varepsilon}$,
$X = M^{a_i}$, $c$ the critical value, this is the slab computation; V3.34 supplies the hypotheses.

**V3.34 (the Morse filtration of a compact submanifold; `Morse.exists_separating_seq`,
`Morse.isCriticalPointM_of_forall_ge`, `Morse.Homology.sublevel_step_critical`,
`Morse.Homology.sublevel_step`, `Morse.Homology.exists_morse_filtration`,
`Morse.Homology.exists_morse_filtration'`, `Morse.Homology.exists_cells_filtration`,
`Morse.Homology.critCount_eq_card`, `Morse.Homology.finiteDimensional_spaceHomology`).** Let $N$ be a
compact slice submanifold of a finite-dimensional real normed space $V$, modelled on a
finite-dimensional space, and $F : V \to \mathbb R$ smooth such that every critical point of $f =
F|_N$ is non-degenerate. (i) If $a' \le a$ are not critical values and all critical values in
$(a', a)$ are equal, then $H_i(N^a, N^{a'}; \Bbbk)$ is finite-dimensional, of dimension the number of
critical points of index $i$ in $f^{-1}(a', a)$. (ii) There are $n \ge 1$ and non-critical values
$a_0 \le a_1 \le \dots$ with $N^{a_0} = \emptyset$, $N^{a_n} = N$ and at most one critical value in
each $(a_k, a_{k+1})$; by (i), each step $(N^{a_{k+1}}, N^{a_k})$ has finite-dimensional homology
over every field, of dimension the number of critical points of index $i$ in $f^{-1}(a_k,
a_{k+1})$. (iii) Hence $H_i(N; \Bbbk)$ is finite-dimensional for every $i$. These statements are
made for every space homeomorphic to $N$, homology being carried along the homeomorphism (for use in
V3.39), and for $N$ itself. *Book:* p. 29: for compact $M$ and $f$ with isolated, non-degenerate
critical points, $a_1 < \dots < a_k$ are chosen so that $M^{a_i}$ contains exactly $i$ critical
points and $M^{a_k} = M$, and $H_*(M^{a_i}, M^{a_{i-1}})$ is the coefficient group in dimension
$\lambda_i$ and $0$ otherwise. *Hidden hypotheses:* Milnor's choice of the $a_i$ needs distinct
critical values; here each slab contains at most one critical value, with any number of critical
points on it (Remark 3.3); $M^{a_0} = \emptyset$ and $M^{a_k} = M$ rest on the minimum and the
maximum of $f$ being critical values; the finiteness of $R_\lambda(M)$ is a consequence; "isolated"
is redundant (V3.16). *Proof:* in (i), with no critical value in $(a', a)$, $N^{a'}$ is a strong
deformation retract of $N^a$ (`Morse.theorem_3_1_submanifold`); otherwise the slab lemma of V3.33,
with Remark 3.3 at the critical value $c$ (`Morse.remark_3_3_submanifold`) and Theorem 3.1 on
$[a', c - \varepsilon]$ and $[c + \varepsilon, a]$.

**V3.35 (Theorem 5.2 in singular homology; `Morse.Homology.bettiNumber_le_critCount`,
`Morse.Homology.bettiNumber_le_critCount'`, `Morse.Homology.sum_bettiNumber_eq_sum_critCount`,
`Morse.Homology.sum_bettiNumber_eq_sum_critCount'`, `Morse.Homology.bettiNumber_eq_zero_of_finrank_lt`,
`Morse.Homology.subsingleton_spaceHomology_of_finrank_lt`).** In the setting of V3.34, with $n =
\dim N$, $b_i = \dim H_i(N; \Bbbk)$ for any field $\Bbbk$, and $C_\lambda = C_\lambda(f)$ (V3.16):
(2) $b_\lambda \le C_\lambda$ for every $\lambda$; (3) $\sum_{i=0}^n (-1)^i b_i =
\sum_{\lambda=0}^n (-1)^\lambda C_\lambda$; and $H_i(N; \Bbbk) = 0$ for $i > n$, so that the left
side of (3) is the whole alternating sum. The same holds for every space homeomorphic to $N$.
*Book:* p. 29, Theorem 5.2 (2) and (3), on a compact manifold $M$, $C_\lambda$ the number of
critical points of index $\lambda$. *Hidden hypotheses:* as in V3.34; $R_\lambda(M) = 0$ for
$\lambda > n$, which makes $\sum (-1)^\lambda R_\lambda(M)$ a finite sum, follows from (2).
*Deviation (narrower):* $M$ is a compact submanifold of a Euclidean space and $f$ the restriction of
a smooth function on the ambient space; abstract compact manifolds are V3.39. *Proof:* V3.32
applied to the filtration of V3.34.

**V3.36 (the inequalities $(4_\lambda)$ in singular homology; `Morse.Homology.altSum_bettiNumber_le`,
`Morse.Homology.altSum_bettiNumber_le'`).** In the setting of V3.35, $b_\lambda - b_{\lambda-1} +
\dots \pm b_0 \le C_\lambda - C_{\lambda-1} + \dots \pm C_0$ for every $\lambda$. *Book:* p. 30,
$(4_\lambda)$. *Hidden hypotheses:* as in V3.34. *Deviation (narrower):* as in V3.35.

**V3.37 (Corollary 5.4 and the lacunary principle in singular homology;
`Morse.Homology.bettiNumber_eq_critCount_of_succ`, `Morse.Homology.bettiNumber_eq_critCount_of_zero`,
`Morse.Homology.bettiNumber_eq_critCount_of_lacunary`).** In the setting of V3.35: if $\lambda \ge 1$
and $C_{\lambda+1} = C_{\lambda-1} = 0$, then $b_\lambda = C_\lambda$ and $b_{\lambda+1} =
b_{\lambda-1} = 0$; if $C_1 = 0$, then $b_0 = C_0$ and $b_1 = 0$; and if no two consecutive $C_i$
are nonzero, then $b_i = C_i$ for every $i$. *Book:* p. 31, Corollary 5.4, with the remark that it
gives the homology groups of $\mathbb CP^n$ (§4) without Theorem 3.5. *Hidden hypotheses:* for
$\lambda = 0$ the condition $C_{\lambda-1} = 0$ is empty. *Deviation (not in the book):* the
lacunary form. Over every field; integral homology groups are not derived, and $\mathbb CP^n$ is not
constructed.

**V3.38 ($\chi$ is the homological Euler characteristic; `Morse.IsEulerNumber.eq_sum_bettiNumber`,
`Morse.Homology.eulerNumberM_eq_sum_bettiNumber`).** (i) Let $N \subseteq \mathbb R^{K+1}$, $K \ge
1$, be a compact nonempty slice submanifold of dimension $d + 1 \ge 1$. Every Euler number $\chi$ of
$N$ (V3.17, the Poincaré–Hopf integer) satisfies $\chi = \sum_{i=0}^{d+1} (-1)^i \dim H_i(N;
\Bbbk)$ for every field $\Bbbk$; the same holds for every space homeomorphic to $N$. (ii) For a
compact Hausdorff smooth manifold $M$ without boundary, modelled on a finite-dimensional real normed
space, the integer $\chi(M)$ of V4.18 ($\sum_\lambda (-1)^\lambda C_\lambda$ for any Morse
function) equals $\sum_{i=0}^{\dim M} (-1)^i \dim H_i(M; \Bbbk)$ for every field $\Bbbk$. In
particular this alternating sum does not depend on the field. *Book:* p. 28, $\chi(X, Y) = \sum
(-1)^\lambda R_\lambda(X, Y)$; p. 29, formula (3), $\chi(M) = C_0 - C_1 + \dots \pm C_n$;
Application 2 (pp. 36–37): $\chi(M)$ is the index sum of every vector field. *Hidden hypotheses:*
that $\chi(M)$ is the same over every field, never stated; passing from $M$ to an embedded copy uses
the invariance of homology under homeomorphisms. *Deviation (restated):* the three descriptions of
$\chi$ (by homology, by critical points, by index sums of vector fields) are identified, which closes
the circle left open in V3.20 and V4.19. *Proof:* (3) of V3.35 for a Morse function $L_p = \|\cdot -
p\|^2$ (Theorem 6.6, V4.12), compared with V3.20, resp. V4.19, through a Whitney embedding (V4.16).

**V3.39 (the Morse inequalities on a compact manifold;
`Morse.Homology.finiteDimensional_spaceHomology_of_isCompact`,
`Morse.Homology.bettiNumber_eq_zero_of_isCompact`, `Morse.Homology.exists_whitney_normSq`,
`Morse.Homology.exists_ambient_of_isMorseFunction`,
`Morse.Homology.finiteDimensional_spaceHomology_of_compactSpace`,
`Morse.Homology.bettiNumber_eq_zero_of_compactSpace`,
`Morse.Homology.bettiNumber_le_critCount_of_compactSpace`,
`Morse.Homology.altSum_bettiNumber_le_of_compactSpace`,
`Morse.Homology.sum_bettiNumber_eq_sum_critCount_of_compactSpace`,
`Morse.Homology.bettiNumber_eq_critCount_of_lacunary_of_compactSpace`).** The homology over any field
of a compact $k$-dimensional slice submanifold of $\mathbb R^n$, or of a space homeomorphic to one,
is finite-dimensional and vanishes above degree $k$. Let $M$ be a compact Hausdorff smooth manifold
without boundary, modelled on a finite-dimensional real normed space, of dimension $n$. Then
$H_i(M; \Bbbk)$ is finite-dimensional and is $0$ for $i > n$, and for every Morse function $g$ on
$M$, with $b_i = \dim H_i(M; \Bbbk)$ and $C_\lambda = C_\lambda(g)$: $b_\lambda \le C_\lambda$;
$(4_\lambda)$; $\sum_{i \le n} (-1)^i b_i = \sum_{\lambda \le n} (-1)^\lambda C_\lambda$; and $b_i
= C_i$ for every $i$ if no two consecutive $C_i$ are nonzero. *Book:* §5 is stated for compact
manifolds; p. 36 quotes Whitney's embedding theorem. *Hidden hypotheses:* Hausdorff, for the
embedding; homology is invariant under homeomorphisms, which carries the results from the embedded
copy. *Deviation (restated):* proved through a Whitney embedding $M \cong N \subseteq \mathbb
R^{K+1}$ (V4.16), on which $g$ becomes the restriction of a smooth ambient function (V3.20) with
the same numbers $C_\lambda$ (V4.15); in dimension $0$ directly from (3).

**V3.40 (examples: two critical points, the torus, the spheres;
`Morse.Homology.bettiNumber_of_ncard_eq_two`, `Morse.Homology.torus_bettiNumber`,
`Morse.Homology.sphere_sum_bettiNumber`, `Morse.Homology.sphere_bettiNumber`,
`Morse.Homology.circle_bettiNumber`).** Over any field: (i) if a compact Hausdorff manifold $M$ of
dimension $n \ge 2$ carries a smooth function with exactly two critical points, both
non-degenerate, then $b_0 = b_n = 1$ and $b_i = 0$ otherwise; (ii) the torus of V3.22 has $b_0 \le
1$, $b_1 \le 2$, $b_2 \le 1$, $b_i = 0$ for $i \ge 3$, and $b_0 - b_1 + b_2 = 0$; (iii)
$\sum_i (-1)^i b_i(S^n) = 1 + (-1)^n$ for $n \ge 1$, and for $n \ge 2$, $b_0(S^n) = b_n(S^n) = 1$
and $b_i(S^n) = 0$ otherwise; (iv) the circle has $b_0 = b_1 \le 1$. *Book:* Reeb's situation (p.
25) and the torus of §1 (pp. 1–3), with §5; the spheres are not discussed in §5. *Hidden
hypotheses:* $n \ge 2$ in (i) and (iii), where the lacunary principle applies ($C_0 = C_n = 1$);
for the circle it does not ($C_0 = C_1 = 1$). *Deviation (not in the book):* checks of
V3.35–V3.39; (iii) agrees with the direct computation of V3.30, which also gives $b_0 = b_1 = 1$
for the circle. For the torus only the bounds and the Euler characteristic follow; its Betti
numbers $1, 2, 1$ are not derived.

**V3.41 ($\mathbb CP^n$ as a compact submanifold, with Milnor's coordinates;
`Morse.CP.exists_vec_of_mem`, `Morse.CP.Model`, `Morse.CP.param`, `Morse.CP.coord`,
`Morse.CP.coord_param`, `Morse.CP.nsq_coord_lt_and_param_coord`, `Morse.CP.exists_re_diag_pos`,
`Morse.CP.isSliceSubmanifold`, `Morse.CP.exists_sliceChart`, `Morse.CP.isCompact`).** Here
$\mathbb CP^n$ is the set of Hermitian projections of trace $1$ in the space $M_{n+1}(\mathbb C)$ of
complex matrices (the Grassmannian of V14.16 with $m = 1$). Every point of it is $P = zz^*$, that is
$P_{ab} = z_a\bar z_b$, for a unit vector $z \in \mathbb C^{n+1}$. For $0 \le k \le n$ let $U_k$ be
the set of $P$ with $\operatorname{Re}P_{kk} > 0$; every point of $\mathbb CP^n$ lies in some $U_k$.
On $\mathbb R^{2n} = \mathbb C^n$, with coordinates $z_j = x_j + iy_j$ ($j \neq k$), put
$\operatorname{param}_k(z) = vv^*$, where $v_k = \sqrt{1 - |z|^2}$ and $v_j = z_j$ for $j \neq k$;
and for a matrix $P$ put
$\operatorname{coord}_k(P) = (P_{jk}/\sqrt{\operatorname{Re}P_{kk}})_{j \neq k}$. Then
$\operatorname{coord}_k(\operatorname{param}_k(z)) = z$ for $|z| < 1$, and for
$P \in \mathbb CP^n \cap U_k$, $|\operatorname{coord}_k(P)| < 1$ and
$\operatorname{param}_k(\operatorname{coord}_k(P)) = P$. $\mathbb CP^n$ is a compact slice
submanifold of $M_{n+1}(\mathbb C)$ of dimension $2n$, and at every $x \in \mathbb CP^n \cap U_k$ it
has a slice chart whose parametrization is
$z \mapsto \operatorname{param}_k(\operatorname{coord}_k(x) + z)$ near $0$. *Book:* p. 26:
$\mathbb CP_n$ as the equivalence classes of $(n + 1)$-tuples $(z_0, \dots, z_n)$ with
$\sum|z_j|^2 = 1$; on the set $U_0$ where $z_0 \neq 0$, $|z_0|\,z_j/z_0 = x_j + iy_j$, and
$x_1, y_1, \dots, x_n, y_n$ "are the required coordinate functions, mapping $U_0$ diffeomorphically
onto the open unit ball in $\mathbb R^{2n}$". *Hidden hypotheses:* "diffeomorphically" presupposes a
smooth structure on $\mathbb CP_n$. *Deviation (restated):* $\mathbb CP^n$ is the submanifold of
rank-one projections, with the smooth structure induced from the space of matrices; Milnor's
coordinates are then entries of $P$, visibly independent of the representative $z$, and they are the
coordinates of slice charts.

**V3.42 (Milnor's function on $\mathbb CP^n$, its critical points and their indices;
`Morse.CP.height`, `Morse.CP.height_param`, `Morse.CP.isCriticalPointM_height_iff`,
`Morse.CP.isNondegenerate_indexM_height`, `Morse.CP.isNondegenerate_of_isCriticalPointM`,
`Morse.CP.bijective_rank`, `Morse.CP.critCount_height`).** For real numbers $c_0, \dots, c_n$ let
$f(P) = \sum_j c_j\operatorname{Re}P_{jj}$ on $\mathbb CP^n$, so that $f(zz^*) = \sum_j c_j|z_j|^2$.
In the coordinates of V3.41,
$f(\operatorname{param}_k(z)) = c_k + \sum_{j \neq k}(c_j - c_k)(x_j^2 + y_j^2)$ for $|z| \le 1$.
Suppose the $c_j$ are distinct. Then the critical points of $f$ are exactly the $n + 1$ points
$p_k = \operatorname{param}_k(0)$ (the projections onto the coordinate axes); $p_k$ is
non-degenerate, of index $2\,\#\{j : c_j < c_k\}$; so $f$ is a Morse function. The map
$k \mapsto \#\{j : c_j < c_k\}$ is a bijection of $\{0, \dots, n\}$, and so the number $C_\lambda$
of critical points of index $\lambda$ is $1$ for $\lambda = 0, 2, \dots, 2n$ and $0$ for every other
$\lambda$. *Book:* pp. 26–27: $f(z_0 : z_1 : \dots : z_n) = \sum c_j|z_j|^2$ with distinct real
constants $c_j$; $f = c_0 + \sum_{j=1}^n(c_j - c_0)(x_j^2 + y_j^2)$ on $U_0$, so the only critical
point of $f$ within $U_0$ is the centre $p_0$, non-degenerate, of index twice the number of $j$ with
$c_j < c_0$; similarly at $p_1, \dots, p_n$; "every possible even index between $0$ and $2n$ occurs
exactly once". *Hidden hypotheses:* the scan of p. 26 prints the definition as $f = c_j|z_j|$; the
display that follows shows that $\sum c_j|z_j|^2$ is meant. That every even index occurs once is the
bijectivity of $k \mapsto \#\{j : c_j < c_k\}$, Milnor's tacit renumbering $c_0 < \dots < c_n$.
*Deviation:* none in substance; the critical points, their non-degeneracy and their indices are read
in the slice parametrizations of V3.41 (V1.6).

**V3.43 (the cells and the homology of $\mathbb CP^n$; `Morse.CP.exists_cells`,
`Morse.CP.bettiNumber_eq`, `Morse.bettiNumber_complexProjectiveSpace`).** $\mathbb CP^n$ has the
homotopy type of a space built from the empty set by attaching cells one after another (V2.12),
exactly one of each dimension $0, 2, \dots, 2n$. For every field $\mathbb k$,
$\dim H_\lambda(\mathbb CP^n; \mathbb k) = 1$ if $\lambda$ is even and $\lambda \le 2n$, and $0$
otherwise. *Book:* p. 27: by Theorem 3.5, $\mathbb CP_n$ has the homotopy type of a CW-complex of
the form $e^0 \cup e^2 \cup e^4 \cup \dots \cup e^{2n}$; it follows that the integral homology
groups are $\mathbb Z$ for $i = 0, 2, 4, \dots, 2n$ and $0$ for other values of $i$. *Hidden
hypotheses:* none. *Deviation (narrower):* an iterated adjunction space rather than a CW-complex
(V2.12); the homology over fields, by the lacunary principle (V3.37, V3.39), not the integral
groups.

### What is not verified in this chapter

- **Remark 1** (p. 25, Reeb's theorem with degenerate critical points): Milnor cites two papers. A
  proof needs M. Brown's monotone union theorem, which is not in Mathlib (a proof by that route is
  in `Exposition/Chapter3.md`, §1).
- **Remark 2** (pp. 25–26, a non-standard smooth $7$-sphere): out of scope (characteristic classes,
  the signature theorem). V3.5 shows where smoothness is lost.
- **Three critical points** (p. 26: indices $0, n/2, n$ by Poincaré duality, and the homotopy type
  of an $n/2$-sphere with an $n$-cell attached): not formalized. Singular homology with its exact
  sequences is now available (V3.26–V3.31), but Poincaré duality (mod 2), which the argument needs,
  is not.
- **$\mathbb CP^n$** (pp. 26–27): verified in V3.41–V3.43, except for the integral homology (next
  item) and for the CW-complex in the strict sense, which is an iterated adjunction space here
  (V2.12).
- **Integral homology**: §5 works over a field, and so do V3.32–V3.40. The integral groups
  $H_i(\mathbb CP^n; \mathbb Z)$ of p. 27, and more generally the exposition's Proposition G (in the
  lacunary case $H_\lambda(M; \mathbb Z)$ is free of rank $C_\lambda$), are not derived, although
  relative homology and the cell computations are available with integer coefficients (V3.26–V3.31).
- **Non-compact manifolds**: everything above is for compact $N$ or $M$, as in Milnor's §5; the
  inequalities for the compact sublevel sets of a function on a non-compact manifold are not stated,
  and abstract non-compact manifolds would need a Whitney embedding that Mathlib does not have.
- **The torus, (2)–(4) of p. 1 and the cell attachments of p. 2**: the sublevel sets are not shown
  to be a disk, a cylinder and a torus with an open disk removed, and the attachments are not
  derived; Theorem 3.2 on submanifolds is proved in Chapter 2 but has not been applied to the torus,
  and the homeomorphism types would need explicit homeomorphisms. Its Betti numbers $1, 2, 1$ are
  not derived either: Morse theory with the height function gives only $b_0 \le 1$, $b_1 \le 2$,
  $b_2 \le 1$ and $b_0 - b_1 + b_2 = 0$ (V3.40).

---

## 5. Chapter 4 (Milnor §6): partly verified

Milnor's §6 (pp. 32–38) takes a manifold $M$ of dimension $k$ in $\mathbb R^n$, its normal bundle
$N$ and the endpoint map $E(q, v) = q + v$, and defines focal points (p. 32). He quotes Sard's
theorem (Theorem 6.1) to get Corollary 6.2 (almost no point is focal), introduces the fundamental
forms and the principal curvatures, locates the focal points on a normal line (Lemma 6.3, through
Assertion 6.4), relates them to the squared distance functions $L_p(q) = \|q - p\|^2$ (Lemma 6.5),
and proves that $L_p$ is a Morse function for almost every $p$ (Theorem 6.6). Corollary 6.7 (every
manifold has a Morse function with compact sublevel sets, via Whitney's embedding), Applications 1
and 2, Corollary 6.8 (approximation by Morse functions) and Lemma 6.9 (the index of $L_p$) follow.
The numbering, checked against the scan of pp. 32–38, is: 6.1 Sard's theorem, 6.2 the corollary on
focal points, 6.3 the lemma on focal points along a normal line (principal curvatures), 6.4 an
assertion inside its proof, 6.5 the lemma on degenerate critical points of $L_p$, 6.6 the theorem,
6.7 and 6.8 corollaries, 6.9 the index lemma. Verified: every numbered statement of pp. 32–38 for a
slice submanifold $M \subseteq \mathbb R^n$ modelled on $\mathbb R^k$ with complement $\mathbb R^w$
(the Milnor project's `Milnor.IsSliceSubmanifold`; $M$ need not be closed or compact, except that
Corollary 6.7 needs $M$ closed, and $k = n$ is allowed), with Sard's theorem for smooth maps into a
vector space (V4.1–V4.13, V4.20, V4.21, V4.23; Application 2 for a compact submanifold of $\mathbb
R^{K+1}$ is V3.20, its Lean files being those of Chapter 3); and, through Mathlib's Whitney
embedding of compact manifolds, Corollary 6.7, Application 2 and Corollary 6.8 for an abstract
compact Hausdorff manifold without boundary modelled on a finite-dimensional real normed space
(V4.14–V4.19, V4.22), together with two results of earlier chapters whose Lean files live here,
Reeb's theorem and Theorem 3.1 for such manifolds (V4.24, V4.25). Corollary 6.8 is proved **without
Milnor's hypothesis that $f$ be bounded**. In Application 2 and throughout, $\chi$ is the
Poincaré–Hopf integer of the Milnor project (V3.17); its identification with the homological Euler
characteristic is in Chapter 3 (V3.38). Not verified: Corollary 6.7 for non-compact abstract
manifolds, Application 1, and the items listed at the end.

**V4.1 (the normal bundle and the endpoint map; `Milnor.Problems.normalBundleSet`,
`Milnor.Problems.isSliceSubmanifold_normalBundle`, `Milnor.Problems.normalSum`,
`Morse.mem_normalBundleSet_iff`, `Morse.slice_dim_add_eq_of_nonempty`, `Morse.normalEnd`,
`Morse.normalEnd_id`).** Throughout, $M \subseteq \mathbb R^n$ is a slice submanifold modelled on
$\mathbb R^k$ with complement $\mathbb R^w$; if $M$ is nonempty, $k + w = n$. The normal bundle is
$N = \{(q, v) \in M \times \mathbb R^n : v \perp T_qM\}$; when $k + w = n$ it is a slice submanifold
of $\mathbb R^n \times \mathbb R^n$ of dimension $n$ (the Milnor project's V8.11). The endpoint map
is $E(q, v) = q + v$; more generally, for a map $\Gamma : \mathbb R^n \to \mathbb R^n$, $E_\Gamma(q,
v) = \Gamma(q) + v$, smooth over every open set on which $\Gamma$ is smooth, with $E_{\mathrm{id}} =
E$. *Book:* p. 32: $M \subset \mathbb R^n$ a manifold of dimension $k < n$, differentiably embedded;
$N$ is an $n$-dimensional manifold ("not difficult to show"); $E(q, v) = q + v$. *Hidden
hypotheses:* "differentiably embedded" must mean a submanifold (an injectively immersed manifold
need not be one, V4.14); for slice charts, $k + w = n$ needs $M \ne \emptyset$. *Deviation
(stronger):* $k = n$ is allowed and $M$ need not be closed or compact; $E_\Gamma$ is not in the book
and serves V4.20.

**V4.2 (focal points and their multiplicity; `Morse.endpointNullity`, `Morse.IsFocalPointMult`,
`Morse.IsFocalPoint`, `Morse.focalSet`, `Morse.endpointNullity_pos_iff`, `Morse.isFocalPoint_iff`,
`Morse.focalSet_eq_image_critPoints`).** Assume $k + w = n$. The nullity of $E$ at $x \in N$ is the
dimension of the kernel of $dE_x$, the tangent space of $N$ at $x$ being identified with $\mathbb
R^n$ by the chart of $N$ at $x$. A point $e \in \mathbb R^n$ is a focal point of $(M, q)$ with
multiplicity $\mu$ if $(q, e - q) \in N$ and the nullity of $E$ at $(q, e - q)$ is $\mu > 0$; a
focal point of $(M, q)$ if this holds for some $\mu$; a focal point of $M$ if it is a focal point of
$(M, q)$ for some $q \in M$. The nullity is positive exactly at the critical points of $E$ (the
points where $dE$ is not onto); so $e$ is a focal point of $(M, q)$ iff $(q, e - q) \in N$ is a
critical point of $E$, and the set of focal points of $M$ is the set of critical values of $E$.
*Book:* p. 32 (the definition, with $e = q + v$ and $(q, v) \in N$); p. 33 (the proof of Corollary
6.2). *Hidden hypotheses:* the nullity does not depend on the chart (two charts differ by an
isomorphism of $\mathbb R^n$).

**V4.3 (Theorem 6.1, Sard's theorem on a manifold; `Morse.measure_image_inter_critPoints_eq_zero`,
`Morse.measure_image_critPoints_eq_zero`).** Let $M$ be a second countable smooth manifold without
boundary modelled on a finite-dimensional real normed space $E$, $F$ a finite-dimensional real
normed space with a Haar measure $\mu$, $U \subseteq M$ open and $f : M \to F$ smooth on $U$. Then
the image under $f$ of the points of $U$ where $df$ is not onto is $\mu$-null; in particular, for
$f$ smooth on $M$, the set of critical values is null. $E$ and $F$ are required to lie in the same
universe of Lean's type theory, a formality with no mathematical content (as in the Milnor project).
*Book:* Theorem 6.1 (p. 33): for a $C^1$ map between manifolds of the same dimension with countable
bases, the image of the set of critical points (where the Jacobian is singular) has measure $0$;
Milnor refers to de Rham and gives no proof. *Hidden hypotheses:* "measure $0$" in the target needs
a measure class; only $\mathbb R^n$ is used, where all Haar measures have the same null sets.
*Deviation (narrower):* $f$ is smooth, not merely $C^1$, and the target is a vector space; on the
other hand the dimensions are arbitrary. Every use in §6 is for a smooth map into $\mathbb R^n$.
*Proof:* countably many charts and the Euclidean Sard theorem of the Milnor project (`Milnor.sard`).

**V4.4 (Corollary 6.2; `Morse.measure_focalSet_eq_zero`).** If $k + w = n$, the set of focal points
of $M$ is null for every Haar measure on $\mathbb R^n$. *Book:* Corollary 6.2 (p. 33): for almost
all $x \in \mathbb R^n$, $x$ is not a focal point of $M$. *Hidden hypotheses:* $N$ has a countable
basis, automatic for a subset of $\mathbb R^{2n}$.

**V4.5 (the fundamental forms; `Morse.xParam`, `Morse.uParam`, `Morse.dParam`, `Morse.d2Param`,
`Morse.firstFF`, `Morse.secondFF`, `Morse.normalForm`).** For $q \in M$, Milnor's coordinates $u
\mapsto x(u)$ are the inverse of the slice chart of $M$ chosen at $q$, with $x(u_q) = q$; $dx$ and
$d^2x$ are its first and second derivatives at $u_q$ (Milnor's $\partial x/\partial u^i$ and
$\partial^2 x/\partial u^i \partial u^j$). The first fundamental form is the bilinear form $g(\xi,
\eta) = \langle dx\,\xi, dx\,\eta\rangle$ on $\mathbb R^k$; the second fundamental form in a
direction $v \in \mathbb R^n$ is $\ell_v(\xi, \eta) = \langle v, d^2x(\xi, \eta)\rangle$; and for a
linear map $T$ of $\mathbb R^n$ the form $(\xi, \eta) \mapsto \langle T\,dx\,\xi, dx\,\eta\rangle -
\ell_v(\xi, \eta)$ is the one attached to $E_\Gamma$ with $T = d\Gamma_q$ (V4.8), equal to $g -
\ell_v$ for $T = \mathrm{id}$. *Book:* pp. 33–34: $g_{ij} = \partial x/\partial u^i \cdot \partial
x/\partial u^j$; $\ell_{ij}$ is the normal component of $\partial^2 x/\partial u^i \partial u^j$,
and for a unit normal $v$ the matrix $(v \cdot \ell_{ij})$ is the second fundamental form in the
direction $v$. *Hidden hypotheses:* none. *Deviation (restated):* $\ell_v$ is defined for every $v$
by the inner product with $d^2x$; for $v$ normal at $q$ it is Milnor's $(v \cdot \ell_{ij})$, the
tangential part of $d^2x$ being orthogonal to $v$. The coordinates are those of the chosen slice
chart; Milnor allows any coordinates.

**V4.6 (principal curvatures; `Morse.tanSpace`, `Morse.shapeOp`, `Morse.isSymmetric_shapeOp`,
`Morse.principalCurvatures`, `Morse.finrank_eigenspace_shapeOp`).** The shape operator $S_v$ of $M$
at $q$ in the direction $v$ is the endomorphism of the tangent space $T_qM = \operatorname{range}
dx$ with $\langle S_v a, b\rangle = \ell_v(dx^{-1}a, dx^{-1}b)$; it is self-adjoint. The principal
curvatures of $M$ at $q$ in the direction $v$ are its $k$ eigenvalues, with multiplicity, in
decreasing order; the multiplicity of $K$ is the dimension of the eigenspace of $K$. *Book:* p. 34:
with coordinates chosen so that $(g_{ij})$ is the identity at $q$, the eigenvalues of $(v \cdot
\ell_{ij})$ are the principal curvatures, and the reciprocals of the nonzero ones the principal
radii of curvature. *Hidden hypotheses:* that coordinates with $g_{ij}(q) = \delta_{ij}$ exist, and
that the eigenvalues do not depend on them. *Deviation (restated):* no normalization: the
eigenvalues of $S_v$ are those of $g^{-1}(v \cdot \ell)$, which are Milnor's $K_i$ when $g$ is the
identity. That $S_v$ does not depend on the parametrization is not proved, and nothing uses it. The
scan lists the curvatures as $K_1, \dots, K_n$; there are $k$ of them, and Lemma 6.3 itself uses $1
\le i \le k$.

**V4.7 (Lemma 6.3; `Morse.focalMult`, `Morse.focalMult_add_smul`, `Morse.isFocalPoint_add_smul_iff`,
`Morse.focalMult_add_inv_smul`, `Morse.sum_focalMult_add_smul_le`).** Assume $k + w = n$, and let
$\operatorname{mult}_q(e)$ be the multiplicity of $e$ as a focal point of $(M, q)$, $0$ if it is not
one. For $q \in M$, $v \perp T_qM$ and $t \in \mathbb R$: $\operatorname{mult}_q(q + tv) = 0$ if
$t = 0$, and otherwise it is the multiplicity of $1/t$ as an eigenvalue of $S_v$. Hence $q + tv$ is
a focal point of $(M, q)$ iff $t = K^{-1}$ for a nonzero principal curvature $K$ in the direction
$v$, the multiplicity of $q + K^{-1}v$ is that of $K$, and for any finitely many values of $t$ the
multiplicities of the points $q + tv$ add up to at most $k$. *Book:* Lemma 6.3 (p. 34), for a unit
normal $v$: the focal points of $(M, q)$ on the normal line $\{q + tv\}$ are exactly the points $q +
K_i^{-1}v$ with $K_i \ne 0$, so there are at most $k$ of them, each counted with its multiplicity.
*Hidden hypotheses:* $t = 0$ must be set aside in "$1/t$ is an eigenvalue" ($q$ is never a focal
point of $(M, q)$, V4.9); the multiplicity of an eigenvalue of a symmetric matrix as a root of the
characteristic polynomial equals the dimension of its eigenspace, which is what the proof produces.
*Deviation (stronger):* $v$ is any normal vector, not necessarily a unit vector. In place of
Milnor's normalized coordinates, for $t \ne 0$ the map $dx$ carries the null space of $g - t\ell_v$
onto the eigenspace of $S_v$ for $1/t$ (`Morse.map_nullSpace_firstFF_sub_eq_eigenspace`).

**V4.8 (the Jacobian of the endpoint map; `Morse.mem_range_mfd_val_normalBundle_iff`,
`Morse.hasMFDerivAt_normalEnd`, `Morse.finrank_ker_mfd_normalEnd`,
`Morse.endpointNullity_eq_nullity`).** Assume $k + w = n$ and let $(q, v) \in N$. A pair $(a, b) \in
\mathbb R^n \times \mathbb R^n$ is tangent to $N$ at $(q, v)$ iff $a = dx\,\xi$ for some $\xi \in
\mathbb R^k$ and $\langle b, dx\,\eta \rangle + \langle v, d^2x(\xi, \eta)\rangle = 0$ for every
$\eta \in \mathbb R^k$. For $\Gamma$ differentiable at $q$, the derivative of $E_\Gamma$ at $(q, v)$
is $(a, b) \mapsto d\Gamma_q(a) + b$ on this tangent space, and its nullity equals the nullity of
the form $(\xi, \eta) \mapsto \langle d\Gamma_q\,dx\,\xi, dx\,\eta\rangle - \langle v, d^2x(\xi,
\eta)\rangle$ on $\mathbb R^k$. For $\Gamma = \mathrm{id}$: the nullity of $E$ at $(q, v)$ is the
nullity of $g - \ell_v$. *Book:* pp. 34–35, in the proof of Lemma 6.3: coordinates $(u, t)$ on $N$
built from orthonormal normal fields $w_\alpha$, and an $n \times n$ matrix whose upper left block
is $(g_{ij} - \sum_\alpha t^\alpha w_\alpha \cdot \ell_{ij})$. *Hidden hypotheses:* the fields
$w_\alpha$ exist only locally, and Milnor does not say why they exist; his sentence that the rank of
the matrix equals the rank of the upper left block (p. 35) does not hold as written, the two ranks differing by
$n - k$; what holds, and is needed, is that the nullities agree. *Deviation (restated):* no normal
frame is used. *Proof:* the tangent space of $N$ is the kernel of the derivative of the local
defining function of $N$ used by the Milnor project; its second condition is the derivative of
Milnor's identity $w_\alpha \cdot \partial x/\partial u^j = 0$.

**V4.9 (Assertion 6.4; `Morse.isFocalPointMult_add_smul_iff`, `Morse.not_isFocalPoint_self`).**
Assume $k + w = n$. For $q \in M$, $v \perp T_qM$, $t \in \mathbb R$ and $\mu \in \mathbb N$: $q +
tv$ is a focal point of $(M, q)$ with multiplicity $\mu$ iff the form $g - t\ell_v$ (in the
coordinates of V4.5) has nullity $\mu > 0$. In particular $q$ is never a focal point of $(M, q)$,
$g$ being non-degenerate. *Book:* Assertion 6.4 (p. 35), for a unit normal $v$: $q + tv$ is a focal
point of $(M, q)$ with multiplicity $\mu$ iff the matrix $(g_{ij} - t\,v \cdot \ell_{ij})$ is
singular with nullity $\mu$. *Hidden hypotheses:* the case $t = 0$, left implicit. *Deviation
(stronger):* $v$ need not be a unit vector.

**V4.10 (the critical points and the Hessian of $L_p$;
`Morse.isCriticalPointM_normSq_sub_iff_mem_normalBundleSet`, `Morse.hessian_normSq_sub_xParam`).**
For $p \in \mathbb R^n$ let $L_p(q) = \|q - p\|^2$ on $M$. Then $q$ is a critical point of $L_p$ iff
$p - q \perp T_qM$, that is, iff $(q, p - q) \in N$; and at every $q \in M$ the Hessian of $L_p
\circ x$ at $u_q$ is $2(g - \ell_{p - q})$. *Book:* p. 35: $L_p$ has a critical point at $q$ iff
$q - p$ is normal to $M$ at $q$; p. 36: at a critical point the second derivatives are $2(\partial
x/\partial u^i \cdot \partial x/\partial u^j + \partial^2 x/\partial u^i \partial u^j \cdot (x -
p))$, which on setting $p = x + tv$ becomes $2(g_{ij} - t\,v \cdot \ell_{ij})$ (the second display
is cut off in the scan; the value is the one used on p. 38). *Hidden hypotheses:* setting $p = q +
tv$ with $v$ a unit normal presupposes that $p - q$ is normal (i.e. that $q$ is critical) and that
$p \ne q$. *Deviation (stronger):* the formula holds at every point, in the direction $p - q$
itself, so no unit vector and no case $p = q$ are needed.

**V4.11 (Lemma 6.5; `Morse.nullityM_normSq_sub_eq_endpointNullity`, `Morse.isFocalPointMult_iff`,
`Morse.isDegenerate_normSq_sub_iff_isFocalPoint`).** Assume $k + w = n$, and let $p \in \mathbb
R^n$, $q \in M$. If $q$ is a critical point of $L_p$, the nullity of $L_p$ at $q$ (the nullity of
its Hessian) equals the nullity of $E$ at $(q, p - q)$. Hence $p$ is a focal point of $(M, q)$ with
multiplicity $\mu$ iff $q$ is a critical point of $L_p$ of nullity $\mu > 0$, and $q$ is a
degenerate critical point of $L_p$ iff $p$ is a focal point of $(M, q)$. *Book:* Lemma 6.5 (p. 36):
$q$ is a degenerate critical point of $L_p$ iff $p$ is a focal point of $(M, q)$, and the nullity of
$q$ is the multiplicity of $p$. *Hidden hypotheses:* the case of a non-critical $q$ (then $p - q$ is
not normal at $q$ and $p$ is not a focal point of $(M, q)$) is left implicit.

**V4.12 (Theorem 6.6; `Morse.mem_focalSet_of_not_isMorseFunction`,
`Morse.ae_isMorseFunction_normSq_sub`, `Morse.ae_volume_isMorseFunction_normSq_sub`,
`Morse.exists_mem_isMorseFunction_normSq_sub`, `Morse.exists_isMorseFunction_normSq_sub`).** For
every slice submanifold $M \subseteq \mathbb R^n$ and every Haar measure $\mu$ on $\mathbb R^n$ (in
particular Lebesgue measure), for $\mu$-almost every $p$ the function $L_p$ is a Morse function on
$M$ (smooth, with only non-degenerate critical points). If $L_p$ is not a Morse function, $p$ is a
focal point of $M$. Every nonempty open subset of $\mathbb R^n$ contains a $p$ for which $L_p$ is a
Morse function. *Book:* Theorem 6.6 (p. 36): for almost all $p \in \mathbb R^n$, $L_p$ has no
degenerate critical points. *Hidden hypotheses:* none; $M = \emptyset$ is trivial, and is the only
case in which $k + w = n$ may fail. *Deviation (stronger):* $M$ need not be closed or compact, $k =
n$ is allowed, and any Haar measure may be used.

**V4.13 (Corollary 6.7 for submanifolds of $\mathbb R^n$; `Morse.isCompact_sublevel_normSq_sub`,
`Morse.ae_isMorseFunction_normSq_sub_and_isCompact_sublevel`,
`Morse.exists_isMorseFunction_isCompact_sublevel`,
`Morse.exists_isMorseFunction_finite_critPoints_sublevel`,
`Morse.ae_isMorseFunction_normSq_sub_finite_critPoints`,
`Morse.exists_isMorseFunction_finite_critPoints`).** If the slice submanifold $M \subseteq \mathbb
R^n$ is a closed subset, then for every $p$ and every $a$ the sublevel set $\{q \in M : L_p(q) \le
a\}$ is compact; so for almost every $p$, $L_p$ is a Morse function on $M$ with compact sublevel
sets, and $M$ carries a Morse function $f$ each of whose sublevel sets $M^a$ is compact and contains
only finitely many critical points. If $M$ is compact, for almost every $p$, $L_p$ is a Morse
function with finitely many critical points. *Book:* Corollary 6.7 (p. 36): on any manifold $M$
there is a differentiable function with no degenerate critical points for which each $M^a$ is
compact; the proof combines Theorem 6.6 with an embedding of $M$ as a closed subset of $\mathbb
R^{2n+1}$ (Whitney). *Hidden hypotheses:* the embedding must be closed (for the open interval in
$\mathbb R$, every $L_p$ has a non-compact sublevel set); "any manifold" must be read as Hausdorff
with a countable basis (on the long line every continuous real function is eventually constant, so
some sublevel set is not compact). *Deviation (narrower):* closed submanifolds of $\mathbb R^n$;
abstract compact manifolds are V4.17; non-compact abstract manifolds are not covered.

**V4.14 (the image of an embedding is a submanifold; `Morse.exists_continuousLinearEquiv_coprod`,
`Morse.exists_sliceChart_range`, `Morse.isSliceSubmanifold_range`,
`Morse.contMDiff_ofInjective_symm`, `Morse.diffeomorphRange`, `Morse.exists_diffeomorph_range`).**
Let $M$ be a smooth manifold without boundary modelled on a finite-dimensional real normed space
$E$, $F$ a finite-dimensional real normed space, and $e : M \to F$ smooth, a topological embedding
(a homeomorphism onto its image), with injective derivative at every point. For finite-dimensional
$Z, W$ with $\dim Z = \dim E$ and $\dim Z + \dim W = \dim F$, the image $e(M)$ is a slice
submanifold of $F$ modelled on $Z$ with complement $W$, and $e : M \to e(M)$ is a smooth
diffeomorphism. *Book:* not stated; taken for granted in the proof of Corollary 6.7 (p. 36), where
Theorem 6.6 is applied to the image of Whitney's embedding. *Hidden hypotheses:* $e$ must be a
homeomorphism onto its image (the figure eight, an injectively immersed line, is not a submanifold);
the inverse of $e$ is smooth because of the slice charts, not merely because $e$ is a smooth
bijection ($x \mapsto x^3$ on $\mathbb R$). *Deviation (not in the book).* *Proof:* the local
immersion theorem, from the inverse function theorem on manifolds of the Milnor project
(`Milnor.isLocalDiffeomorphAt_of_isInvertible_mfderiv`) applied to $(z, w) \mapsto
e(\varphi^{-1}(Tz)) + Lw$, $\varphi$ a chart of $M$, $T : Z \cong E$, and $L$ completing $de_x$ to
an isomorphism.

**V4.15 (the Morse notions are invariant under diffeomorphisms;
`Morse.isCriticalPointM_comp_symm_iff`, `Morse.setOf_isCriticalPointM_comp_symm`,
`Morse.hessianM_comp_symm_apply`, `Morse.isNondegenerate_hessianM_comp_symm_iff`,
`Morse.indexM_comp_symm`, `Morse.nullityM_comp_symm`, `Morse.IsMorseFunction.comp_diffeomorph_symm`,
`Morse.isMorseFunction_comp_symm_iff`, `Morse.critCount_comp_symm`,
`Morse.ncard_setOf_isCriticalPointM_comp_symm`).** Let $g : M \to M'$ be a smooth diffeomorphism of
smooth manifolds without boundary modelled on real normed spaces $E, E'$, and $f : M \to \mathbb R$.
For every $f$, $q$ is a critical point of $f \circ g^{-1}$ iff $g^{-1}(q)$ is a critical point of
$f$, and the numbers of critical points agree. If $f$ is $C^2$ at a critical point $g^{-1}(q)$, the
Hessian of $f \circ g^{-1}$ at $q$ is the Hessian of $f$ at $g^{-1}(q)$ pulled back by
$d(g^{-1})_q$, so non-degeneracy, index and nullity agree there. $f$ is a Morse function iff $f
\circ g^{-1}$ is, and for $f$ of class $C^2$ the numbers $C_\lambda$ (V3.16) of $f$ and $f \circ
g^{-1}$ agree. *Book:* not stated; used without comment wherever a manifold is replaced by its image
under an embedding (p. 36). *Hidden hypotheses:* none. *Deviation (not in the book).*

**V4.16 (every compact manifold is a compact submanifold of Euclidean space;
`Morse.exists_isSliceSubmanifold_whitney`, `Morse.exists_embedding_euclidean`,
`Morse.exists_diffeomorph_sliceSubmanifold`).** Let $M$ be a compact Hausdorff smooth manifold
without boundary modelled on a finite-dimensional real normed space $E$, $n = \dim E$. Then $M$ has
a smooth closed embedding with injective derivative into some $\mathbb R^m$ (Mathlib's Whitney
embedding, `exists_embedding_euclidean_of_compact`), whose image is a slice submanifold modelled on
$E$; such an embedding exists into $\mathbb R^{K+1}$ with $K \ge 1$ and $K + 1$ as large as desired;
and $M$ is diffeomorphic to a compact, closed slice submanifold $N \subseteq \mathbb R^{K+1}$, $K
\ge 1$, modelled on $\mathbb R^n$. *Book:* p. 36, in the proof of Corollary 6.7: an $n$-dimensional
manifold can be embedded differentiably as a closed subset of $\mathbb R^{2n+1}$ (Whitney,
*Geometric Integration Theory*, p. 113). *Hidden hypotheses:* Hausdorff. *Deviation (narrower):*
compact manifolds only; the ambient dimension is not $2n + 1$, which plays no role ($K \ge 1$ is
arranged by two extra zero coordinates, for the Poincaré–Hopf theorem).

**V4.17 (Corollary 6.7 for a compact manifold; `Morse.exists_isMorseFunction_of_compactSpace`).**
Every compact Hausdorff smooth manifold without boundary, modelled on a finite-dimensional real
normed space, carries a Morse function, and it has finitely many critical points. *Book:* Theorem
6.6 and Corollary 6.7 (p. 36). *Hidden hypotheses:* Hausdorff, for the embedding; for compact $M$
every $M^a$ is compact. *Deviation (narrower):* compact $M$ only; the function is $L_p$ on an
embedded copy (V4.16, V4.13), pulled back by the diffeomorphism (V4.15).

**V4.18 (the Euler number of an abstract manifold; `Morse.eulerNumberM`).** For a manifold $M$
modelled on $E$, $\chi(M) = \sum_{\lambda=0}^{\dim E} (-1)^\lambda C_\lambda(f)$ for one Morse
function $f$ on $M$ chosen once and for all, and $\chi(M) = 0$ if $M$ has no Morse function. *Book:*
p. 29: $\chi(M) = C_0 - C_1 + C_2 - \dots \pm C_n$, where $\chi$ is the Euler characteristic of
p. 28. *Hidden hypotheses:* the value must not depend on the choice; that is V4.19, for compact
Hausdorff $M$. *Deviation (restated):* defined through critical points, not homology; for compact
Hausdorff $M$ it equals $\sum_i (-1)^i \dim H_i(M; F)$ for every field $F$ (V3.38).

**V4.19 (formula (3) and Application 2 on a compact manifold;
`Morse.sum_critCount_eq_of_isMorseFunction_of_compactSpace`, `Morse.sum_critCount_eq_eulerNumberM`,
`Morse.exists_eulerNumber_of_compactSpace`, `Morse.sum_critCount_of_finrank_eq_zero`,
`Morse.IsEulerNumber.eq_eulerNumberM`, `Morse.eulerNumberM_eq_of_diffeomorph`,
`Morse.exists_isEulerNumber_eulerNumberM`).** Let $M$ be a compact Hausdorff smooth manifold without
boundary modelled on a finite-dimensional real normed space. (i) Every Morse function $f$ on $M$ has
$\sum_{\lambda=0}^{\dim M} (-1)^\lambda C_\lambda(f) = \chi(M)$; in dimension $0$ both sides are the
number of points of $M$. (ii) If $\dim M = d + 1 \ge 1$ and $N \subseteq \mathbb R^{K+1}$, $K \ge
1$, is a compact nonempty slice submanifold modelled on $\mathbb R^{d+1}$ and diffeomorphic to $M$
(for instance the image of any embedding, V4.14), every Euler number of $N$ (V3.17) equals
$\chi(M)$; so the Poincaré–Hopf integer does not depend on the embedding. (iii) $\chi$ is invariant
under diffeomorphisms between compact Hausdorff manifolds. (iv) If $M$ is nonempty of dimension $d +
1$, it is diffeomorphic to a compact $N \subseteq \mathbb R^{K+1}$ on which every smooth tangent
field with finitely many zeros has index sum $\chi(M)$. *Book:* p. 29, formula (3); Application 2
(pp. 36–37): on a compact $M$ the index sum of $\operatorname{grad} f$ is $\chi(M)$, and the index
sum of any vector field is $\chi(M)$, the index sum being a topological invariant (Steenrod, §39.7).
*Hidden hypotheses:* Hausdorff; in Application 2 "any differentiable function" must be a Morse
function. *Deviation (restated):* $\chi(M)$ is the integer of V4.18, which equals the Poincaré–Hopf
integer of every embedded copy and, by V3.38, the homological Euler characteristic;
vector fields and their indices are defined in the Milnor project only for submanifolds of Euclidean
space, so Application 2 is stated on an embedded copy; the topological invariance that Milnor quotes
from Steenrod is replaced by the Poincaré–Hopf theorem and invariance under diffeomorphisms.

**V4.20 (the generic perturbation behind Corollary 6.8; `Morse.negGrad`,
`Morse.exists_local_extension_of_contMDiff`, `Morse.mem_image_critPoints_of_not_isNondegenerate`,
`Morse.ae_isMorseFunction_add_inner`, `Morse.exists_mem_isMorseFunction_add_inner`).** For every
slice submanifold $M \subseteq \mathbb R^n$, every smooth $f : M \to \mathbb R$ and every Haar
measure on $\mathbb R^n$: for almost every $a \in \mathbb R^n$, $f + \langle a, \cdot\rangle$ is a
Morse function on $M$, and such $a$ exist in every nonempty open set. *Book:* not in this form;
Milnor's proof of Corollary 6.8 (p. 37) uses $L_p$ on an embedding whose first coordinate is $f$.
For $f = \frac12\|x\|^2$ the statement is Theorem 6.6, since $\frac12\|x\|^2 + \langle a, x\rangle =
\frac12 L_{-a}(x) - \frac12\|a\|^2$. *Hidden hypotheses:* none; no boundedness, compactness or
closedness. *Deviation (not in the book):* the standard linear perturbation, used in place of
Milnor's construction. *Proof:* that of Theorem 6.6 with $L_p$ replaced by $f + \langle a,
\cdot\rangle$ and $E$ by $E_\Gamma$, $\Gamma = -\nabla F$ for a local extension $F$ of $f$ (constant
along the slices of a slice chart): a degenerate critical point $q$ makes $(q, a + \nabla F(q))$ a
critical point of $E_\Gamma$ with value $a$ (V4.8), and Sard's theorem (V4.3) on countably many
pieces of $N$ finishes.

**V4.21 (Corollary 6.8 on a submanifold of $\mathbb R^n$; `Morse.exists_isMorseFunction_approx`,
`Morse.ballDiffeo`, `Morse.isSliceSubmanifold_ballImage`, `Morse.isMorseFunction_of_ballImage`,
`Morse.ae_isMorseFunction_add_inner_ballDiffeo`, `Morse.exists_isMorseFunction_approx_uniform`).**
Let $M \subseteq \mathbb R^n$ be any slice submanifold, $f : M \to \mathbb R$ smooth (bounded or
not), $\varepsilon > 0$, $r \in \mathbb N$, and finitely many smooth coordinate systems $y_j$ on
open subsets of $M$, with values in $\mathbb R^k$, with compact sets $K_j$ inside their ranges.
There is a Morse function $g$ on $M$ with $|g - f| < \varepsilon$ on all of $M$ and $\|D^i((g - f)
\circ y_j^{-1})(u)\| < \varepsilon$ for every $j$, every $i \le r$ and every $u \in K_j$. One can
take $g = f + \langle a, \beta(\cdot)\rangle$ with $a$ small, where $\beta(y) = y/\sqrt{1 +
\|y\|^2}$ is the diffeomorphism of $\mathbb R^n$ onto its open unit ball; for compact $M$ also $g =
f + \langle a, \cdot\rangle$ (`Morse.exists_isMorseFunction_approx`). *Book:* Corollary 6.8 (p. 37):
any bounded smooth $f : M \to \mathbb R$ can be uniformly approximated by a smooth $g$ without
degenerate critical points, and $g$ can be chosen so that its $i$-th derivatives on a given compact
$K \subset M$ uniformly approximate those of $f$, for $i \le k$. *Hidden hypotheses:* derivatives on
a manifold exist only in coordinates, so the approximation on $K$ must be read in fixed coordinate
systems covering $K$ (finitely many suffice); Milnor's embedding $h$ with bounded image and first
coordinate $f$ is not constructed (one can take $h = (f, \beta \circ h')$ for any embedding $h'$).
*Deviation (stronger):* **no boundedness hypothesis on $f$**: the perturbation $\langle a,
\beta(\cdot)\rangle$ is bounded by $\|a\|$; and $M$ need not be compact. $M$ is a submanifold of
$\mathbb R^n$; abstract compact $M$ is V4.22. *Proof:* V4.20 applied to the slice submanifold
$\beta(M)$ and $f \circ \beta^{-1}$, and the Morse property carried back along $\beta$.

**V4.22 (Corollary 6.8 on a compact manifold; `Morse.ae_isMorseFunction_add_inner_comp`,
`Morse.exists_isMorseFunction_approx_of_compactSpace`).** (i) Let $M$ be a smooth manifold without
boundary modelled on a finite-dimensional real normed space, $e : M \to \mathbb R^n$ smooth, a
topological embedding with injective derivative, and $f : M \to \mathbb R$ smooth. Then $f + \langle
a, e(\cdot)\rangle$ is a Morse function for almost every $a$ (any Haar measure). (ii) If $M$ is
compact and Hausdorff, then for every smooth $f$, $\varepsilon > 0$, $r \in \mathbb N$, and finitely
many smooth coordinate systems $y_j$ (with values in a real normed space) with compact sets $K_j$
inside their ranges, there is a Morse function $g$ with $|g - f| < \varepsilon$ on $M$ and every
derivative of order $\le r$ of $(g - f) \circ y_j^{-1}$ of norm $< \varepsilon$ on $K_j$; one can
take $g = f + \langle a, e(\cdot)\rangle$, $e$ Mathlib's Whitney embedding. *Book:* Corollary 6.8
(p. 37). *Hidden hypotheses:* Hausdorff; Milnor's boundedness of $f$ is automatic for compact $M$.
*Deviation (narrower):* (ii) for compact $M$ only; the perturbation is not Milnor's.

**V4.23 (Lemma 6.9, the index of $L_p$; `Morse.index_firstFF_sub_secondFF`,
`Morse.indexM_normSq_sub_eq_card`, `Morse.indexM_normSq_sub_eq_finsum_focalMult`).** (i) The index
of $g - \ell_v$ is the number of principal curvatures in the direction $v$, counted with
multiplicity, that are greater than $1$. (ii) At a critical point $q$ of $L_p$, the index of $L_p$
is the number of principal curvatures of $M$ at $q$ in the direction $p - q$ that are greater than
$1$. (iii) If $k + w = n$ and $q$ is a non-degenerate critical point of $L_p$, the index of $L_p$ at
$q$ is $\sum_{t \in [0, 1]} \operatorname{mult}_q(q + t(p - q))$ (all but finitely many terms
vanish): the number of focal points of $(M, q)$ on the segment from $q$ to $p$, each counted with
its multiplicity. *Book:* Lemma 6.9 (p. 37), proved on p. 38: the index of $2(g_{ij} - t\,v \cdot
\ell_{ij})$ is its number of negative eigenvalues, which for $(g_{ij})$ the identity is the number
of eigenvalues of $(v \cdot \ell_{ij})$ that are $\ge 1/t$; compare with Lemma 6.3. *Hidden
hypotheses:* the eigenvalues to count are those $> 1/t$, not $\ge 1/t$: equality would make $p$ a
focal point of $(M, q)$, i.e. $q$ degenerate (V4.11), and this is where non-degeneracy enters; the
case $p = q$ (index $0$, and the segment $\{q\}$ holds no focal point). *Deviation (restated):* the
direction $p - q$ is not normalized: if $p - q = tv$ with $\|v\| = 1$, the curvatures in the
direction $p - q$ are $t$ times those in the direction $v$, so "greater than $1$" is Milnor's
"greater than $1/t$". *Proof:* Sylvester's law of inertia in an orthonormal eigenbasis of $S_v$, in
which $g - \ell_v$ is $\sum_i (1 - \kappa_i)c_i^2$.

**V4.24 (Reeb's theorem on a compact manifold; `Morse.reeb_of_compactSpace`).** Let $M$ be a compact
Hausdorff smooth manifold without boundary modelled on a real normed space of finite dimension $n$,
and $f : M \to \mathbb R$ smooth with exactly two critical points, both non-degenerate. Then $M$ is
homeomorphic to the unit sphere $S^n \subseteq \mathbb R^{n+1}$. This is Theorem 4.1 of Chapter 3,
placed here because its Lean file is `Morse/Chapter4/Whitney.lean`. *Book:* Theorem 4.1 (p. 25), in
Milnor's own setting of an abstract compact manifold. *Hidden hypotheses:* Hausdorff; the others as
in V3.6. *Proof:* V3.6 on an embedded copy (V4.16), the critical points and their non-degeneracy
carried over by V4.15.

**V4.25 (Theorem 3.1 on a compact manifold).** This is V2.4 in Chapter 2, where it belongs in book order; it is proved through the Whitney embedding of this chapter (V4.14–V4.16).

### What is not verified in this chapter

- **Theorem 6.1 in Milnor's generality** ($C^1$ maps between manifolds of the same dimension): only
  smooth maps into a vector space are treated, which is every use Milnor makes of it; the Milnor
  project proves Sard's theorem for smooth maps only.
- **Corollary 6.7 for a non-compact abstract manifold**, and with it the abstract forms of V4.17 and
  V4.22 for non-compact $M$: Mathlib's Whitney embedding is for compact manifolds only, so a
  non-compact manifold has no closed embedding into Euclidean space here. The submanifold forms
  (V4.13, V4.21) need the embedding as input.
- **Application 1** (p. 36: a differentiable manifold has the homotopy type of a CW-complex):
  Theorem 3.5 is proved only for compact submanifolds of Euclidean space and only as an iterated
  adjunction space, since Mathlib has no cellular approximation (Chapter 2); Theorems 3.2 and 3.5
  are not transferred to abstract manifolds; the non-compact case needs Whitehead's theorem.
- **Application 2 as Milnor argues it**: $\chi$ enters as the Poincaré–Hopf integer (V3.17, V4.18),
  identified with $\sum_i (-1)^i \dim H_i(M; F)$ only afterwards (V3.38); the topological invariance
  quoted from Steenrod is not formalized; vector fields on an abstract manifold are not treated,
  only on an embedded copy.
- **Independence of the principal curvatures from the parametrization**: not proved, and not needed
  (V4.6).
- **Milnor's own proof of Corollary 6.8**, through $L_p$ on an embedding with first coordinate $f$:
  not formalized; replaced by V4.20–V4.22.

---

## 6. Chapter 5 (Milnor §7): partly verified

Milnor's §7 (pp. 39–42) applies Part I to complex submanifolds of $\mathbb C^n$. A closed complex
submanifold of complex dimension $k$ has the homotopy type of a CW-complex of dimension at most $k$
(Theorem 7.2), so a non-singular affine variety of real dimension $2k$ has no homology above
dimension $k$ (Theorem 7.1), and Lefschetz's theorems on hyperplane sections follow (Corollary 7.3,
Theorem 7.4). The only new mathematics in the section is algebraic: at a critical point $q$ of
$L_p = \|\cdot - p\|^2$ on a complex submanifold, the Hessian has index at most $k$. That algebraic
core is verified, in a stronger form than Milnor's (at every point of a holomorphic chart, critical
or not, degenerate or not), together with Assertions 1 and 2, read as statements about quadratic
forms and about Hessians in a holomorphic chart. The setting is linear algebra: a finite-dimensional
complex vector space $V$ (Milnor's $\mathbb C^k$, the domain of a holomorphic chart), a complex
inner product space $F$ (Milnor's $\mathbb C^n$), and a map $w : V \to F$ holomorphic near a point
(Milnor's inclusion $M \to \mathbb C^n$ read in holomorphic coordinates). The topological statements
of §7 are verified as well (V5.13–V5.19), for submanifolds of $\mathbb R^{2n}$ whose tangent spaces
are complex subspaces: the index bound for $L_p$ on such a submanifold, at every critical point;
Theorem 7.2, as a countable cell complex with cells of dimension at most $k$; Theorem 7.1, over a
field; and, under the hypothesis that a neighbourhood of the hyperplane section deforms into it
(which Milnor draws from the triangulability of algebraic varieties), Corollary 7.3 over a field and
Theorem 7.4, for a closed subset of $\mathbb CP^n$ whose affine part is such a submanifold. Focal
points of complex submanifolds are never used. Not verified: integral coefficients, the passage from
algebraic varieties to these hypotheses, and the deformation hypothesis itself (the list at the
end). Lean: `Morse/Chapter5/IndexBound.lean` (545 lines), on the definitions of §2 in
`Morse/Chapter1/Nondegenerate.lean`, for V5.1–V5.12; `ComplexIndex.lean` (230), `Lefschetz.lean`
(351), `LefschetzSlab.lean` (364), `HyperplaneSection.lean` (423), `ProjectiveSection.lean` (310)
and `LefschetzHomotopy.lean` (581) for V5.13–V5.19.

**Conventions.** A complex vector space is also regarded as a real one (restriction of scalars), and
"bilinear form" means a continuous real-bilinear form. Mathlib's Hermitian product
$\langle a, b\rangle$ is conjugate-linear in the first slot, Milnor's
$\sum_\alpha a_\alpha\bar b_\alpha$ in the second; their real parts agree, and only real parts occur
below. A *complex structure* on a real vector space is a real-linear $J$ with $J^2 = -1$; on a
complex vector space, $J = i\cdot$.

**V5.1 (Hessian, index, nullity; `Morse.hessian`, `Morse.index`, `Morse.index_isGreatest`,
`Morse.nullSpace`, `Morse.nullity`).** For $f : E \to \mathbb R$ on a real normed space $E$ and
$q \in E$, the Hessian $d^2f_q$ is the second Fréchet derivative, the bilinear form
$(v, w) \mapsto d(x \mapsto df_x(w))_q(v)$; it is defined at every point (it is $0$ at a point where
$x \mapsto df_x$ is not differentiable). For a bilinear form $H$, the null space is
$\{v : H(v, w) = 0 \text{ for all } w\}$ and the nullity is its dimension; the index is Mathlib's
negative index of inertia (`sigNeg`) of $v \mapsto H(v, v)$, and on a finite-dimensional space
`Morse.index_isGreatest` proves it is the largest dimension of a subspace on which $H(v, v) < 0$ for
$v \neq 0$. *Book:* p. 5: the index of a bilinear functional is the maximal dimension of a subspace
on which it is negative definite, the nullity is the dimension of its null space; the Hessian
$f_{**}$ is defined at a critical point (p. 4) and is the matrix of second partial derivatives in
local coordinates (p. 5). *Hidden hypotheses:* none. *Deviation (restated):* the formal Hessian
exists at every point; at a critical point it is the matrix of $f_{**}$ in the given linear
coordinates. The nullity is a Mathlib `finrank`, which is $0$ for an infinite-dimensional null
space; the statements below that compare nullities hold as stated in any dimension and are
meaningful in finite dimension.

**V5.2 (Milnor's form $Q'$ and the orthogonal map $J$; `Morse.reBilin`, `Morse.reBilin_apply`,
`Morse.reBilin_I_smul`, `Morse.reInner`, `Morse.reInner_I_smul`, `Morse.realMulI`,
`Morse.complexStructureEquiv`).** For a complex vector space $V$ and a continuous complex-bilinear
$B : V \times V \to \mathbb C$, $\operatorname{Re}B$ is a real bilinear form; for
$B(z, z') = \sum b_{hj}z^hz'^j$ on $\mathbb C^k$ its quadratic form is Milnor's $Q'$. Multiplication
by $i$ is a real-linear isomorphism $J$ with $J^2 = -1$ (inverse $-J$), and
$\operatorname{Re}B(iv, iw) = -\operatorname{Re}B(v, w)$ for all $v, w$. On a complex inner product
space the real inner product $\operatorname{Re}\langle v, w\rangle$ (the Euclidean inner product of
$\mathbb R^{2k}$ when $V = \mathbb C^k$) satisfies
$\operatorname{Re}\langle iv, iw\rangle = \operatorname{Re}\langle v, w\rangle$: $J$ is orthogonal.
*Book:* p. 39: substituting $x^h + iy^h$ for $z^h$ in $Q(z) = \sum b_{hj}z^hz^j$ and taking real
parts gives a real quadratic form $Q'$ in $2k$ variables; the identity $Q(iz) = -Q(z)$ shows that an
orthogonal change of variables carries $Q'$ into $-Q'$. *Hidden hypotheses:* none. *Deviation
(stronger):* the sign change is proved for the bilinear form, not only for the quadratic form.

**V5.3 (Assertion 1; `Morse.nullity_reBilin_sub_smul_reInner_eq`,
`Morse.eigenspace_eq_nullSpace_sub_smul_reInner`, `Morse.finrank_eigenspace_neg_eq`).** Let $V$ be a
complex inner product space, $B$ a continuous complex-bilinear form on $V$ and $e \in \mathbb R$.
Then $\operatorname{Re}B - e\operatorname{Re}\langle\cdot,\cdot\rangle$ and
$\operatorname{Re}B + e\operatorname{Re}\langle\cdot,\cdot\rangle$ have the same nullity. If $A$ is
a real-linear operator on $V$ with
$\operatorname{Re}\langle Au, w\rangle = \operatorname{Re}B(u, w)$ for all $u, w$ (the matrix of
$Q'$ in orthonormal real coordinates), then the $e$-eigenspace of $A$ is the null space of
$\operatorname{Re}B - e\operatorname{Re}\langle\cdot,\cdot\rangle$, and the $e$- and
$(-e)$-eigenspaces of $A$ have the same dimension. *Book:* p. 39, Assertion 1: if $e$ is an
eigenvalue of $Q'$ with multiplicity $\mu$, then so is $-e$; after the orthogonal change of
variables of V5.2, Assertion 1 "clearly follows". *Hidden hypotheses:* none. *Proof:* as in the
book; the step left implicit is that $J$, orthogonal with
$\operatorname{Re}B(Ju, Jw) = -\operatorname{Re}B(u, w)$, carries
$\operatorname{Re}B - e\operatorname{Re}\langle\cdot,\cdot\rangle$ into
$-(\operatorname{Re}B + e\operatorname{Re}\langle\cdot,\cdot\rangle)$, and a linear change of
variables does not change the nullity.

**V5.4 (Assertion 1 relative to an invariant form; `Morse.nullity_sub_smul_eq_nullity_add_smul`,
`Morse.nullity_sub_smul_eq_nullity_add_smul'`).** Let $E$ be a real normed space, $J$ a continuous
real-linear map with $J^2 = -1$, $G$ a bilinear form with $G(Jv, Jw) = G(v, w)$ and $L$ a bilinear
form with $L(Jv, Jw) = -L(v, w)$, for all $v, w$. Then for every real $t$ the forms $G - tL$ and
$G + tL$ have the same nullity, and for every real $e$ the forms $L - eG$ and $L + eG$ have the same
nullity. *Book:* not stated. On p. 40 Milnor passes from Assertion 1 (eigenvalues for the coordinate
inner product of $\mathbb R^{2k}$) to focal points, which are governed by the second fundamental
form relative to the first fundamental form $(g_{ij})$ (Assertion 6.4, p. 35). *Deviation (not in
the book):* this is the form of Assertion 1 that Assertion 2 needs (Assertion 1a of the exposition).
With $G = (g_{ij})$, which is $J$-invariant by the Cauchy–Riemann equations, and $L$ the second
fundamental form in a normal direction $v$, the two nullities $G \mp tL$ are the multiplicities of
$q \pm tv$ as focal points; V5.3 gives the same conclusion only when the real coordinates are
orthonormal at $q$, an assumption Milnor makes in §6 (p. 34) but not on p. 40.

**V5.5 (real orthogonality to a complex subspace; `Morse.inner_eq_zero_of_re_inner_eq_zero`).** Let
$T$ be a complex linear subspace of a complex inner product space and $v$ a vector with
$\operatorname{Re}\langle a, v\rangle = 0$ for every $a \in T$. Then $\langle a, v\rangle = 0$ for
every $a \in T$. *Book:* p. 40, the parenthesis that the linear terms of
$\sum_\alpha w_\alpha(z)\bar v_\alpha$ vanish since $v$ is orthogonal to $M$. *Hidden hypotheses:*
the tangent space $TM_q$ is a complex subspace, and orthogonality is meant in the real sense; the
lemma is what turns real orthogonality into the vanishing of the Hermitian products. *Deviation (not
in the book):* stated and proved, but not used by V5.6–V5.11, which avoid power series.

**V5.6 (the Hessian of $L_p$ in holomorphic coordinates; `Morse.hessian_normSq_sub_holomorphic`).**
Let $V$ be a complex normed space, $F$ a complex inner product space, $w : V \to F$ complex $C^2$ on
a neighbourhood of $q$ (in particular holomorphic there), and $p \in F$. Then the real Hessian at
$q$ of $z \mapsto \|w(z) - p\|^2$ is
$$(\xi, \xi') \longmapsto 2\Big(\operatorname{Re}\langle dw_q\xi,\, dw_q\xi'\rangle +
\operatorname{Re}\big\langle w(q) - p,\ d^2w_q(\xi, \xi')\big\rangle\Big),$$
where $dw_q$ and $d^2w_q$ are the complex first and second derivatives. The first term is unchanged
by $(\xi, \xi') \mapsto (i\xi, i\xi')$ (it is the first fundamental form of $w$), the second changes
sign (it is the real part of a complex bilinear form). *Book:* p. 40: in holomorphic coordinates the
real inner product $w \cdot v$ is a constant plus $Q'(x, y)$ plus higher terms, and "clearly" the
quadratic terms $Q'$ determine the second fundamental form in the normal direction $v$. *Hidden
hypotheses:* none. *Deviation (restated):* Milnor's remark is replaced by an explicit formula for
the whole Hessian of $L_p$ in the chart. For $p = w(q) + tv$, $v$ a unit normal, the second inner
product is $-2t\,Q'(\xi)$ on the diagonal, $Q$ being Milnor's quadratic part of
$\sum_\alpha w_\alpha\bar v_\alpha$.

**V5.7 (Assertion 2, in a holomorphic chart; `Morse.nullity_hessian_normSq_sub_add_eq_sub`).** With
$V$, $F$, $w$, $q$ as in V5.6, for every $n \in F$ and every real $t$, the Hessians at $q$ of
$\|w(\cdot) - (w(q) + tn)\|^2$ and of $\|w(\cdot) - (w(q) - tn)\|^2$ have the same nullity. *Book:*
p. 40, Assertion 2: the focal points of $(M, q)$ along any normal line occur in pairs symmetric
about $q$; if $q + tv$ is a focal point, then $q - tv$ is a focal point with the same multiplicity.
*Hidden hypotheses:* none for the formal statement ($n$ need be neither normal nor a unit vector,
and $q$ need not be critical). *Deviation (restated):* the statement concerns Hessians in a
holomorphic chart, not focal points. For a unit normal $n$ these nullities are the multiplicities of
$w(q) \pm tn$ as focal points, by Assertion 6.4 and Milnor's p. 36 formula for the Hessian of $L_p$;
those are formalized for real slice submanifolds of $\mathbb R^n$ (Chapter 4,
`Morse.isFocalPointMult_add_smul_iff`), but a holomorphic chart of a complex submanifold is not
identified with a chart of that real submanifold, so the passage to focal points is not verified.
*Proof:* $J = i\cdot$ carries one Hessian into the other (V5.6), as in V5.4. Milnor's route through
the eigenvalues of $Q'$ (V5.3) is not used.

**V5.8 (the Andreotti–Frankel identity; `Morse.apply_J_apply_J_eq`,
`Morse.apply_I_smul_apply_I_smul_eq`, `Morse.apply_I_smul_apply_I_smul_eq_two_mul_norm_sq_sub`).**
Let $G$, $L$, $H$ be bilinear forms on a real normed space and $J$ any map of it such that, for all
$v$, $H(v, v) = G(v, v) - L(v, v)$, $G(Jv, Jv) = G(v, v)$ and $L(Jv, Jv) = -L(v, v)$. Then
$H(Jv, Jv) = 2G(v, v) - H(v, v)$. On a complex vector space with $J = i\cdot$ and
$L = \operatorname{Re}B$, $B$ complex bilinear, the condition on $L$ is automatic; on a complex
inner product space with $G(v, v) = \|v\|^2$ this reads $H(iv, iv) = 2\|v\|^2 - H(v, v)$. *Book:*
not in Milnor's text; it replaces the count of focal points on p. 41 (Milnor attributes the proof of
§7 to Andreotti and Frankel, p. 39). *Deviation (not in the book).*

**V5.9 (the index bound; `Morse.two_mul_index_le_finrank`, `Morse.index_le_finrank_complex`).** Let
$E$ be a finite-dimensional real normed space, $H$ a bilinear form and $J$ an injective real-linear
map of $E$ with $H(v, v) + H(Jv, Jv) \ge 0$ for all $v$. Then
$2\cdot\operatorname{index}H \le \dim_{\mathbb R}E$. On a finite-dimensional complex vector space
$V$, if $H(v, v) + H(iv, iv) \ge 0$ for all $v$, then $\operatorname{index}H \le \dim_{\mathbb C}V$.
*Book:* not stated; it is the abstract form of the conclusion on p. 41 that the index of $L_p$ at
$q$ is at most $k$. *Deviation (not in the book).* *Proof:* if $H$ is negative definite on $W$, then
$W \cap JW = 0$, since a non-zero $Jw \in W$ would make both $H(w, w)$ and $H(Jw, Jw)$ negative; so
$2\dim W \le \dim E$.

**V5.10 (the index bound for forms of Milnor's shape; `Morse.index_le_finrank_of_eq_sub_re`,
`Morse.index_le_finrank_of_hermitian`, `Morse.index_hessian_le_finrank_complex`).** Let $V$ be a
complex vector space of finite dimension $k$, $G$ a bilinear form with $G(v, v) \ge 0$ and
$G(iv, iv) = G(v, v)$, $B$ a continuous complex-bilinear form, and $H$ a bilinear form with
$H(v, v) = G(v, v) - \operatorname{Re}B(v, v)$ for all $v$. Then $\operatorname{index}H \le k$. In
particular: on a complex inner product space, every form with quadratic form
$\|v\|^2 - \operatorname{Re}B(v, v)$ has index at most $k$; and for any $f : V \to \mathbb R$ and
$q \in V$ whose Hessian (V5.1) has, on the diagonal, the form $G - \operatorname{Re}B$, the Hessian
has index at most $k$. *Book:* p. 41: the index of $L_p$ at a critical point $q$ is at most $k$.
*Hidden hypotheses:* none. *Deviation (stronger):* neither criticality, nor non-degeneracy, nor any
smoothness of $f$ is assumed; only the shape of the Hessian matters. *Proof:* V5.8 and V5.9: if
$H(v, v) < 0$ then $H(iv, iv) = 2G(v, v) - H(v, v) > 0$. Milnor's count of focal points (Lemmas 6.3
and 6.9 with Assertion 2) is not used.

**V5.11 (the index of $L_p$ is at most $k$, in a holomorphic chart;
`Morse.index_hessian_normSq_sub_holomorphic_le`).** Let $V$ be a complex vector space of finite
dimension $k$, $F$ a complex inner product space, $w : V \to F$ complex $C^2$ on a neighbourhood of
$q$, and $p \in F$. Then the Hessian at $q$ of $z \mapsto \|w(z) - p\|^2$ has index at most $k$.
*Book:* p. 41: the index of $L_p$ at a critical point $q$ of $L_p : M \to \mathbb R$ is at most $k$,
$M$ a complex submanifold of complex dimension $k$ and $L_p$ without degenerate critical points.
*Hidden hypotheses:* none. *Deviation (stronger):* $q$ need not be a critical point, the Hessian
need not be non-degenerate, and $dw_q$ need not be injective. *Deviation (restated):* the statement
is about the Hessian in a holomorphic chart. When $w$ parametrizes $M$ near a critical point $w(q)$
of $L_p|M$, this Hessian is that of $L_p|M$ in the real coordinates $(x, y)$, and its index is the
index of $L_p$ at $w(q)$ by the chart independence of §2; that identification needs $M$ as a real
slice submanifold with $w^{-1}$ among its charts, which is not formalized. *Proof:* by V5.6 the
Hessian $H$ satisfies $H(\xi, \xi) + H(i\xi, i\xi) = 4\|dw_q\xi\|^2 \ge 0$; then V5.9.

**V5.12 (no negative semidefinite Hessian; `Morse.exists_pos_apply_of_eq_sub_re`).** If, in V5.10,
$G$ is moreover positive definite ($G(v, v) > 0$ for $v \neq 0$) and $V \neq 0$, then $H(v, v) > 0$
for some $v$. *Book:* not in Milnor's text. *Deviation (not in the book):* with
$G(\xi, \xi) = 2\|dw_q\xi\|^2$ (V5.6) it says that, where $dw_q$ is injective, the Hessian of $L_p$
in a holomorphic chart of positive dimension is never negative semidefinite; the consequence drawn
in the exposition (Chapter 5, §4), that $L_p$ has no local maximum on a complex submanifold of
positive dimension, is not formalized.

**V5.13 (complex submanifolds, and the index bound at every critical point of $L_p$;
`Morse.IsOrthComplexStructure`, `Morse.IsComplexSubmanifold`, `Morse.two_mul_indexM_normSq_sub_le`,
`Morse.indexM_normSq_sub_le`).** Let $V$ be a finite-dimensional real inner product space and $J$ an
orthogonal linear map of $V$ with $J^2 = -1$ (for $V = \mathbb C^m = \mathbb R^{2m}$: multiplication
by $i$). A slice submanifold $N \subseteq V$ is called a *complex submanifold* (for $J$) if $J$ maps
every tangent space $T_xN$ into itself. For such an $N$, every $p \in V$ and every critical point
$q$ of $L_p = \|\cdot - p\|^2$ on $N$, degenerate or not, twice the index of $L_p$ at $q$ is at most
$\dim_{\mathbb R}N$; so if $\dim_{\mathbb R}N = 2k$, the index is at most $k$. *Book:* pp. 39–41:
for a complex manifold $M$ of complex dimension $k$ bianalytically embedded in $\mathbb C^n$, the
index of $L_p$ at a non-degenerate critical point is $\le k$, by the focal points (Assertions 1 and
2, Lemmas 6.3 and 6.9). *Hidden hypotheses:* none. *Deviation (restated):* "complex" is the
invariance of the tangent spaces under $J$, which a bianalytically embedded complex manifold has;
nothing else about it is used. This is the bridge that V5.7 and V5.11 lacked: the bound is for the
Hessian of $L_p$ on the real submanifold, computed in a slice chart, where the complex structure
read in the chart satisfies the identity of V5.8. *Deviation (stronger):* every critical point,
without non-degeneracy; no focal points.

**V5.14 (the homology of a slab without critical points of a given index; `Morse.critValuesIn`,
`Morse.subsingleton_subsetHomology_sublevel`, `Morse.subsingleton_subsetHomology_slab`,
`Morse.exists_regular_levels`).** Let $N$ be a slice submanifold of a finite-dimensional real inner
product space, $F$ a smooth function on the ambient space, $f = F|N$, and $\mathbb k$ a field. Let
$a \le b \le a_0$ be such that $f^{-1}(-\infty, a_0]$ is compact (or only the slab
$f^{-1}[\ell, a_0]$, for some $\ell \le a$), every critical point of $f$ in it is non-degenerate,
and $a$ and $b$ are not critical values. If no critical point $q$ with $a < f(q) < b$ has index $j$,
then $H_j(N^b, N^a; \mathbb k) = 0$, where $N^c = f^{-1}(-\infty, c]$. A Morse function on $N$ which
is bounded below by $0$ and has compact sublevel sets has regular values
$a_0 < 0 \le a_1 \le a_2 \le \dots$ tending to infinity. *Book:* §3 and §5 (Theorems 3.1, 3.2,
Remark 3.3; the exact sequences), as §7 uses them for $L_p$ (p. 39) and for $1/L_p$ (p. 42). *Hidden
hypotheses:* for $-L_p$ and $1/L_p$ the sublevel sets are not compact; Theorems 3.1 and 3.2 only
need the compactness of the slab $f^{-1}[a, b]$. *Deviation (not in the book as a statement):* the
form in which Chapter 3's computation (V3.33–V3.34) is used in §7, by induction on the number of
critical values in the slab.

**V5.15 (Theorem 7.2; `Morse.theorem_7_2`).** Let $M \subseteq \mathbb R^n$ be a slice submanifold
of dimension $2k$ which is closed in $\mathbb R^n$ and complex for an orthogonal $J$ with $J^2 = -1$
(V5.13). Then $M$ has the homotopy type of a countable cell complex (VA.18) all of whose cells have
dimension at most $k$. *Book:* p. 39, Theorem 7.2: a complex manifold of complex dimension $k$,
bianalytically embedded as a closed subset of $\mathbb C^n$, has the homotopy type of a
$k$-dimensional CW-complex. *Hidden hypotheses:* "$k$-dimensional" means of dimension at most $k$
($\mathbb C$ is contractible). *Deviation (restated):* a closed submanifold with complex tangent
spaces, of pure dimension $2k$; a countable cell complex in the sense of VA.18, with cells attached
along arbitrary maps. *Proof:* for almost every $p$, $L_p$ is a Morse function on $M$ (V4.12), with
compact sublevel sets because $M$ is closed; its critical points have index $\le k$ (V5.13); the
sublevel sets between regular values are obtained by attaching cells, and the tower of these
attachments has the homotopy type of $M$ (V10.20, VA.19).

**V5.16 (Theorem 7.1, over a field; `Morse.theorem_7_1`).** Under the hypotheses of V5.15,
$H_i(M; \mathbb k) = 0$ for every field $\mathbb k$ and every $i > k$. *Book:* p. 39, Theorem 7.1
(Andreotti and Frankel): a non-singular affine algebraic variety $M \subset \mathbb C^n$ of real
dimension $2k$ has $H_i(M; \mathbb Z) = 0$ for $i > k$. *Hidden hypotheses:* that such a variety is
a closed complex submanifold of pure dimension. *Deviation (narrower):* coefficients in a field;
"non-singular affine algebraic variety" is replaced by the hypotheses of V5.15. *Proof:* from the
filtration by sublevel sets (V5.14, assembled as in V10.25), not from cellular chains.

**V5.17 (hyperplane sections, for an abstract pair; `Morse.HypothesisN`,
`Morse.le_indexM_neg_normSq_sub`, `Morse.subsingleton_subsetHomology_univ_of_section`,
`Morse.corollary_7_3_of_section`).** Let $X$ be a compact space, $A \subseteq X$ closed, $M$ as in
V5.15, and $e$ a homeomorphism of $M$ onto $X \setminus A$ such that $\|e^{-1}(y)\| \to \infty$ as
$y \to A$. *Hypothesis (N)* for $A$ in $X$: there are an open $U \supseteq A$ and a homotopy
$H : [0, 1] \times U \to X$ with $H_0$ the inclusion, $H_1(U) \subseteq A$, and $H_t(a) = a$ for all
$t$ and all $a \in A$. Under Hypothesis (N), for every field $\mathbb k$: $H_r(X, A; \mathbb k) = 0$
for $r < k$; hence the map $H_r(A; \mathbb k) \to H_r(X; \mathbb k)$ induced by the inclusion is
bijective for $r + 1 < k$ and surjective for $r < k$. On the way: at a non-degenerate critical point
of $L_p$ on $M$, the function $-L_p$ has index at least $k$. *Book:* pp. 41–42: for Corollary 7.3
the exact sequence of the pair and Lefschetz duality, with Theorem 7.1 for $V - (V \cap P)$; for
Theorem 7.4 "the hypothesis that some neighborhood $U$ of $V \cap P$ can be deformed into $V \cap P$
within $V$". *Hidden hypotheses:* the deformation must keep $V \cap P$ pointwise fixed; Lefschetz
duality has hypotheses that are not stated. *Deviation (restated):* an abstract pair $(X, A)$ with
$X \setminus A$ a closed complex submanifold of $\mathbb C^n$ going to infinity at $A$; no duality:
with $V_R = A \cup e\{L_p \ge R\}$ inside $U$, the map $H_r(V_R, A) \to H_r(X, A)$ is zero by (N),
and $H_r(X, V_R) \cong H_r(M, \{L_p \ge R\})$ vanishes for $r < k$ by excision and V5.14 for $-L_p$
on the compact slab $\{L_p \le R\}$; then the exact sequence of the triple. *Deviation (narrower):*
field coefficients; (N) is a hypothesis.

**V5.18 (Corollary 7.3, Lefschetz, over a field; `Morse.CP.affinePart`,
`Morse.CP.hyperplaneSection`, `Morse.CP.affineHomeomorph`,
`Morse.CP.tendsto_norm_affineHomeomorph_symm`, `Morse.corollary_7_3`).** Let
$V \subseteq \mathbb CP^n$ (V3.41) be closed and $P$ the hyperplane $z_0 = 0$, the set of
projections $Q$ with $Q_{00} = 0$. The *affine part* of $V$ is the set of
$u \in \mathbb C^n = \mathbb R^{2n}$ for which the projection onto the line of $(1, u)$ belongs to
$V$; it is homeomorphic to $V \setminus P$, and its points go to infinity as their images approach
$V \cap P$. Suppose the affine part is a slice submanifold of $\mathbb R^{2n}$ of dimension $2k$,
complex for multiplication by $i$, and suppose Hypothesis (N) for $V \cap P$ in $V$ (V5.17). Then
for every field $\mathbb k$ the map $H_r(V \cap P; \mathbb k) \to H_r(V; \mathbb k)$ induced by the
inclusion is bijective for $r < k - 1$ and surjective for $r = k - 1$. *Book:* p. 41, Corollary 7.3
(Lefschetz): for an algebraic variety $V$ of complex dimension $k$ in $\mathbb CP_n$ and a
hyperplane $P$ containing the singular points of $V$, the inclusion $V \cap P \to V$ induces
isomorphisms of homology groups in dimensions less than $k - 1$, and is onto in dimension $k - 1$.
*Hidden hypotheses:* $V$ must have pure dimension $k$ (the exposition gives a counterexample
otherwise); and (N). *Deviation (narrower):* field coefficients; (N) assumed; the hyperplane
$z_0 = 0$ only (another hyperplane is brought there by a unitary change of coordinates, which is not
formalized); "algebraic variety with its singular points in $P$" is replaced by the hypothesis on
the affine part.

**V5.19 (Theorem 7.4, Lefschetz; `Morse.theorem_7_4_of_section`, `Morse.theorem_7_4`,
`Morse.theorem_7_4_of_embedding`, `Morse.theorem_7_4_bijective`, `Morse.theorem_7_4_surjective`).**
Under the hypotheses of V5.18: for $r < k$, every continuous map $h : I^r \to V$ is homotopic,
relative to $h^{-1}(V \cap P)$, to a map into $V \cap P$; the same holds for maps from any compact
space that admits a continuous injection into a real vector space of dimension $< k$, and for the
abstract pair $(X, A)$ of V5.17. Consequently, for every $x \in V \cap P$, the map
$\pi_i(V \cap P, x) \to \pi_i(V, x)$ induced by the inclusion is bijective for $i + 1 < k$ and
surjective for $i < k$. *Book:* pp. 41–42, Theorem 7.4 (Lefschetz): under the same hypotheses the
relative homotopy group $\pi_r(V, V \cap P)$ is zero for $r < k$. The proof uses the function $f$
equal to $0$ on $V \cap P$ and to $1/L_p$ elsewhere, whose critical points have index
$\ge 2k - k = k$, and the hypothesis that a neighbourhood $U$ of $V \cap P$ can be deformed into
$V \cap P$ within $V$, which "can be proved, for example, using the theorem that algebraic varieties
can be triangulated". *Hidden hypotheses:* as in V5.17; and $1/L_p$ is infinite at $p$ when
$p \in V$. *Deviation (restated):* relative homotopy groups are not in Mathlib; the statement is the
criterion for their vanishing, in the relative form above, with $r = 0$ included. Milnor's $1/L_p$
is replaced by $1/(1 + L_p)$. *Proof:* the pushing lemma of Chapter 13 (V13.13) for $-L_p$ on a
compact slab pushes every map into a small neighbourhood $V_R$ of $A$, after localizing to the part
of the map that lies outside it; (N) pushes $V_R$ into $A$.

### What is not verified in this chapter

- **Integral coefficients** in Theorem 7.1 and Corollary 7.3 (pp. 39, 41): the homology of the
  sublevel filtrations is computed over a field (V5.16–V5.18).
- **Algebraic varieties:** that a non-singular affine variety, or the affine part of a projective
  variety of pure dimension whose singular points lie in $P$, is a closed submanifold with complex
  tangent spaces, and that a bianalytically embedded complex manifold is one. These are the
  hypotheses of V5.13–V5.19; and Theorem 7.2 gives a countable cell complex with cells attached
  along arbitrary maps (VA.18), not a CW-complex in the strict sense.
- **Assertion 2 as a statement about focal points** (p. 40), and **Milnor's count on p. 41** (at
  most $2k$ focal points on the normal line, symmetric about $q$, hence at most $k$ between $p$ and
  $q$, via Lemmas 6.3 and 6.9): replaced by V5.8–V5.11 and V5.13, which need neither.
- **Hypothesis (N)** (p. 42): the deformation of a neighbourhood of $V \cap P$ into $V \cap P$,
  which Milnor obtains from the triangulability of algebraic varieties (quoted). It is a hypothesis
  of V5.17–V5.19, in the form that keeps $V \cap P$ fixed. **Lefschetz duality**, which Milnor's
  proof of Corollary 7.3 quotes, is neither formalized nor needed (V5.17).
- **Relative homotopy groups** as objects (pp. 41–42): Theorem 7.4 is stated as the criterion for
  the vanishing of $\pi_r(V, V \cap P)$ (V5.19). **Hyperplanes other than $z_0 = 0$** need a unitary
  change of coordinates, which is not formalized.

---

## 7. Chapter 6 (Milnor §§8–9): partly verified

Milnor's §§8–9 (pp. 43–54) are a rapid course on connections for an abstract Riemannian manifold:
affine connections and Christoffel symbols, covariant derivatives along curves (Lemma 8.1), parallel
transport (Lemma 8.2), compatibility with the metric (Lemma 8.3, Corollary 8.4), symmetric
connections and the fundamental Lemma 8.6, parametrized surfaces (Lemma 8.7), the curvature tensor
and its tensor property (Lemma 9.1), Lemma 9.2, and the four symmetries of Lemma 9.3; the sectional
curvature is defined later, on p. 100. Mathlib (as used here) has covariant derivatives on vector
bundles, their torsion and metric compatibility, but no curvature tensor, no Christoffel symbols, no
covariant derivative along curves, no parallel transport and no Levi-Civita connection. The chapter
is therefore verified in three layers. (1) On an abstract manifold, with Mathlib's
`CovariantDerivative`: Milnor's rules, his symmetric and compatible connections identified with
Mathlib's torsion-free and metric ones, the sign of his curvature (the negative of the
Kobayashi–Nomizu $R$), and the uniqueness half of Lemma 8.6. (2) For a submanifold $N$ of a
Euclidean space with the induced metric: the substance of §§8–9 — the Levi-Civita connection with
rules (1)–(4), Lemma 8.6 (existence and uniqueness), Lemmas 8.1–8.3 and 8.7, Corollary 8.4, parallel
transport as a linear isometry, the curvature tensor, Lemmas 9.1–9.3 — plus the Gauss equation and
the curvature of the round sphere. Every Riemannian manifold is isometric to such an $N$ by Nash's
embedding theorem, which is quoted in the Lean files but neither proved nor used, so these results
are statements about embedded manifolds with the induced metric. (3) At one point, for any trilinear
map on an inner product space satisfying Lemma 9.3 (1)–(3): Lemma 9.3 (4) by Milnor's octahedron,
and the theory of sectional curvature. What is not verified is listed at the end. Lean:
`Morse/Chapter6/` — `Connection.lean` (248 lines), `CurvatureAlgebra.lean` (499), `Projection.lean`
(756), `Submanifold.lean` (780), `LinearODE.lean` (232), `Parallel.lean` (461), `Surface.lean`
(239), `SphereCurvature.lean` (131).

**The embedded setting** (layer 2). $V$ is a finite-dimensional real inner product space (Milnor's
$\mathbb R^K$) and $N \subseteq V$ a slice submanifold in the sense of the companion project
(`Milnor.IsSliceSubmanifold`): every point of $N$ lies in the domain of a diffeomorphism $\sigma$
from an open subset of $V$ onto an open subset of $Z \times W$ that carries $N$ onto
$Z \times \{0\}$, and the maps $q \mapsto (\sigma q)_1$ make $N$ a smooth manifold modelled on $Z$.
$Z$ is assumed finite-dimensional throughout, and $W$ in the results that use the symmetry of the
second fundamental form; when $N$ is non-empty both hold automatically, $Z \times W$ being linearly
isomorphic to $V$. $N$ carries the induced metric: tangent vectors at $q$ are vectors of $V$, with
the inner product of $V$. A map $F : N \to E$ into a normed space is smooth, or differentiable at
$q$, as a map of manifolds; a curve $c : \mathbb R \to N$ or a surface $s : \mathbb R^2 \to N$ is
smooth when it is smooth as a map into $V$. No closedness or compactness of $N$ is assumed anywhere.

**V6.1 (tangent spaces, the projection $P_q$, derivatives along $N$, vector fields;
`Morse.tangentSubspace`, `Morse.tanProj`, `Morse.dN`, `Morse.dN_eq_fderiv`,
`Morse.IsTangentField`).** $T_qN \subseteq V$ is the range of the derivative at $q$ of the inclusion
$N \to V$, and $P_q$ is the orthogonal projection of $V$ onto $T_qN$. For $F : N \to E$, the linear
map $dN\,F\,q : V \to E$ is the derivative of $F$ at $q$ read on ambient vectors: on $v \in T_qN$ it
is $dF_q(v)$ (its values off $T_qN$ depend on a chart and are never used). If $F = G$ on $N$ near
$q$ for some $G : V \to E$ differentiable at $q$, then $dN\,F\,q\,v = dG_q(v)$ for $v \in T_qN$. A
vector field is a map $X : N \to V$ with $X(q) \in T_qN$ for every $q$; it is smooth if it is smooth
as a map $N \to V$. *Book:* Milnor works on an abstract manifold with tangent spaces $TM_p$, vector
fields and directional derivatives $X_pf$ (pp. 43–44). *Hidden hypotheses:* none. *Deviation
(narrower):* the embedded setting.

**V6.2 (the projection is smooth, and tangent vectors extend to fields; `Morse.contMDiff_tanProj`,
`Morse.tanProj_eq_gramProj`, `Morse.contDiffAt_gramProj`, `Morse.projField`,
`Morse.contMDiff_projField`, `Morse.projField_apply_of_mem`).** The map $q \mapsto P_q$ from $N$ to
the operators on $V$ is smooth. Hence for each $u \in V$ the field $q \mapsto P_qu$ is a smooth
vector field on $N$, equal to $u$ at every $q$ with $u \in T_qN$: every tangent vector extends to a
smooth vector field on all of $N$. *Book:* not stated; Milnor checks the smoothness of what he
builds chart by chart (condition (1), p. 44). *Deviation (not in the book).* *Proof:* in a slice
chart with parametrization $x$, $P_{x(u)} = A(A^{\mathsf T}A)^{-1}A^{\mathsf T}$ with $A = dx_u$,
which is injective, and this expression is smooth in $A$ near an injective operator.

**V6.3 (affine connections on an abstract manifold; `Morse.cov_smul_left`, `Morse.cov_add_right`,
`Morse.cov_smul_right`).** Let $M$ be a smooth manifold in Mathlib's sense (modelled on a real
normed space) and $\nabla$ a Mathlib covariant derivative on its tangent bundle, $X_p \vdash Y$
being the value at $X_p$ of the linear map $\nabla Y(p) : T_pM \to T_pM$. Then Milnor's (3),
$(fX) \vdash Y = f\,(X \vdash Y)$, holds at every point; (2), additivity in $Y$, holds at every
point where both summands are differentiable; and (4), $X \vdash (fY) = (Xf)\,Y + f\,(X \vdash Y)$,
holds at every point where $f$ and $Y$ are differentiable. Dependence on $X_p$ only, and linearity
in $X_p$, are part of the definition. *Book:* pp. 43–44: an affine connection at $p$ assigns to
$X_p$ and $Y$ a vector $X_p \vdash Y$, bilinear, with the Leibniz rule; a global one satisfies the
smoothness condition (1), and conditions (1)–(4) "can be taken as the definition". *Hidden
hypotheses:* differentiability of $f$ and $Y$ at the point, in (2) and (4). *Deviation (restated):*
Milnor's connection is Mathlib's `CovariantDerivative`, his condition (1) the separate class
`ContMDiffCovariantDerivative`; Mathlib's object is defined on all sections and is unconstrained on
sections not differentiable at the point.

**V6.4 (the connection of the induced metric and Milnor's rules (1)–(4); `Morse.covAt`,
`Morse.leviCivita`, `Morse.contMDiff_leviCivita`, `Morse.leviCivita_add_left`,
`Morse.leviCivita_add_right`, `Morse.leviCivita_smul_left`, `Morse.leviCivita_smul_right`).** In the
embedded setting put $v \vdash Y = P_q(dY_q(v))$ for $v \in T_qN$ and $Y : N \to V$, and
$(X \vdash Y)(q) = P_q(dY_q(X(q)))$. Then $X \vdash Y$ is tangent to $N$ at every point, and: (1)
$X \vdash Y$ is smooth when $X$ is a smooth vector field and $Y$ is smooth; (2) it is additive in
$X$, and additive in $Y$ at every point where both summands are differentiable; (3)
$(fX) \vdash Y = f\,(X \vdash Y)$ for every function $f$; (4) at $q$,
$X \vdash (fY) = (Xf)\,Y + f\,(X \vdash Y)$ with $Xf = df_q(X(q))$, when $f$ and $Y$ are
differentiable at $q$ and $X(q)$, $Y(q)$ are tangent. *Book:* p. 44, conditions (1)–(4). *Hidden
hypotheses:* differentiability in (2) and (4). *Deviation (narrower):* the embedded setting; the
connection is a global formula, with no Christoffel symbols.

**V6.5 (covariant derivative along a curve; `Morse.velocity`, `Morse.IsFieldAlong`,
`Morse.covDeriv`, `Morse.deriv_mem_tangentSubspace`, `Morse.covDeriv_add`, `Morse.covDeriv_smul`,
`Morse.covDeriv_comp`).** For a curve $c : \mathbb R \to N$, a vector field along $c$ is a map
$X : \mathbb R \to V$ with $X(t) \in T_{c(t)}N$ for all $t$; the velocity $c'(t)$ is tangent when
$c$ is smooth; and $DX/dt\,(t) = P_{c(t)}(X'(t))$. Milnor's axioms hold: (a)
$D(X + Y)/dt = DX/dt + DY/dt$ at $t$ when $X$, $Y$ are differentiable at $t$; (b)
$D(fX)/dt = f'X + f\,DX/dt$ at $t$ when $f$, $X$ are differentiable at $t$ and $X(t)$ is tangent;
(c) if $c$ is smooth and $Y : N \to V$ is differentiable at $c(t)$, then
$D(Y \circ c)/dt\,(t) = c'(t) \vdash Y$. *Book:* pp. 45–46: parametrized curves, vector fields along
a curve, the velocity field, and the axioms (a), (b), (c). *Hidden hypotheses:* differentiability at
$t$ (Milnor's fields along curves are smooth by definition). *Deviation (narrower):* the embedded
setting.

**V6.6 (Lemma 8.1; `Morse.IsCovDerivAlong`, `Morse.isCovDerivAlong_covDeriv`,
`Morse.IsCovDerivAlong.eq_covDeriv`).** Let $c$ be a smooth curve in $N$. Call an operation $D$ on
maps $\mathbb R \to V$ admissible if it satisfies (a) for smooth fields along $c$, (b) for smooth
$f$ and smooth fields along $c$, and (c) for smooth vector fields $Y$ on $N$. Then $X \mapsto P(X')$
of V6.5 is admissible, and every admissible $D$ agrees with it on every smooth field along $c$.
*Book:* p. 46, Lemma 8.1 (the scan prints it as "Lemma 0.1"): there is one and only one operation
$V \mapsto DV/dt$ satisfying (a), (b), (c). *Hidden hypotheses:* none beyond the smoothness
conventions. *Deviation (narrower):* the embedded setting. *Proof:* instead of a chart, a field
along $c$ is expanded as $X = \sum_i \langle e_i, X\rangle\,(E_i \circ c)$ in the smooth fields
$E_i(q) = P_qe_i$ of V6.2 ($e_i$ an orthonormal basis of $V$), and (a)–(c) determine $DX/dt$. This
avoids what Milnor's coordinate proof leaves implicit: locality in $t$ and the extension of the
coordinate fields to all of $M$.

**V6.7 (global solutions of linear equations; `Morse.linearODE_eqOn`, `Morse.linearODE_eq`,
`Morse.exists_skewLinearODE`).** Let $A : \mathbb R \to \operatorname{End}(E)$ be continuous. (i) On
a real normed space $E$, two solutions of $x' = A(t)x$ on an open interval (or on $\mathbb R$) that
agree at one time agree everywhere. (ii) If $E$ is a complete real inner product space and
$\langle A(t)x, x\rangle = 0$ for all $t$ and $x$, then for every $t_0$ and $x_0$ there is a
solution on all of $\mathbb R$ with $x(t_0) = x_0$. *Book:* p. 47, proof of Lemma 8.2: the equations
are linear, so the solutions are determined by their initial values and "can be defined for all
relevant values of $t$" (Milnor cites Graves). *Hidden hypotheses:* a global existence theorem for
linear equations; Mathlib has local existence (Picard–Lindelöf) and Grönwall uniqueness only.
*Deviation (narrower):* global existence is proved only for skew-adjoint coefficients, the case
needed in V6.8. *Proof:* solutions of the skew equation have constant norm, so the equation may be
truncated outside a ball and solved by Picard–Lindelöf on any compact interval; solutions on nested
intervals are glued by (i).

**V6.8 (Lemma 8.2; `Morse.IsParallel`, `Morse.exists_unique_isParallel`,
`Morse.IsParallel.contDiff`).** A field $X$ along $c$ is parallel if it is differentiable and
$DX/dt = 0$ at every $t$. For a smooth curve $c$, every $t_0 \in \mathbb R$ and every
$v \in T_{c(t_0)}N$ there is exactly one parallel field $X$ along $c$ with $X(t_0) = v$; it is
defined on all of $\mathbb R$, and it is smooth. *Book:* p. 47, Lemma 8.2, with initial time $0$ and
smooth fields. *Hidden hypotheses:* none. *Deviation (stronger):* any initial time, and uniqueness
among differentiable fields, not only smooth ones. *Deviation (narrower):* the embedded setting.
*Proof:* a tangent field is parallel iff $X' = P'X$, where $P(t) = P_{c(t)}$, and uniqueness is V6.7
(i) for this equation. It has no a priori bound, so existence solves instead $X' = (P'P - PP')X$,
whose coefficient is skew-adjoint (V6.7 (ii)); since $PP'P = 0$, the normal part $U = X - PX$
satisfies $U' = -P'U$, so a solution that starts tangent stays tangent (V6.7 (i) again) and is then
parallel. On an abstract manifold Milnor's coordinate equations would also have to be patched from
chart to chart along the curve; here there is one equation in $V$.

**V6.9 (parallel translation is a linear isometry; `Morse.IsParallel.inner_eq`,
`Morse.parallelTransport`, `Morse.inner_parallelTransport`, `Morse.parallelTransport_self`,
`Morse.parallelTransport_trans`).** For parallel fields $X$, $Y$ along any curve $c$ in $N$,
$\langle X(t), Y(t)\rangle$ does not depend on $t$: the induced connection is compatible with the
metric in Milnor's sense. For a smooth curve $c$ and times $t_0$, $t_1$, the map sending
$v \in T_{c(t_0)}N$ to the value at $t_1$ of the parallel field through $v$ at $t_0$ is a linear
isometry of $T_{c(t_0)}N$ onto $T_{c(t_1)}N$; it is the identity when $t_1 = t_0$, and translating
from $t_0$ to $t_1$ and then to $t_2$ is translating from $t_0$ to $t_2$. *Book:* p. 47: $V_t$ is
obtained from $V_0$ by parallel translation; a connection is compatible with the metric if parallel
translation preserves inner products. *Hidden hypotheses:* none. *Deviation (stronger):* linearity,
surjectivity and transitivity of parallel translation are stated; Milnor uses them without comment.
*Deviation (narrower):* compatibility is proved for the induced connection, not assumed.

**V6.10 (Lemma 8.3; `Morse.hasDerivAt_inner_covDeriv`).** For any curve $c$ in $N$ and fields $X$,
$Y$ along $c$ differentiable at $t$, the derivative of $\langle X, Y\rangle$ at $t$ is
$\langle DX/dt, Y\rangle + \langle X, DY/dt\rangle$. *Book:* p. 47, Lemma 8.3, for a connection
compatible with the metric; the proof expands $V$ and $W$ in a parallel orthonormal frame. *Hidden
hypotheses:* none in the statement; Milnor's proof needs Lemma 8.2 for $n$ initial vectors and the
smoothness of the coefficients $\langle V, P_i\rangle$. *Deviation (narrower):* the induced
connection. *Proof:* the product rule in $V$ and $\langle PX', Y\rangle = \langle X', Y\rangle$ for
tangent $Y$; no parallel transport is used, so here Lemma 8.3 comes before Lemma 8.2.

**V6.11 (Corollary 8.4; `Morse.dN_inner_eq_covAt`, `Morse.IsCompatible`,
`Morse.isCompatible_iff_isMetricCompatible`).** *Embedded:* if $Y$, $Y'$ are differentiable at $q$
with $Y(q)$, $Y'(q)$ tangent, and $v \in T_qN$, then
$v\langle Y, Y'\rangle = \langle v \vdash Y, Y'(q)\rangle + \langle Y(q), v \vdash Y'\rangle$.
*Abstract:* on a manifold whose tangent bundle carries a Riemannian metric (Mathlib's
`RiemannianBundle`), a covariant derivative is called compatible (`Morse.IsCompatible`) if Milnor's
identity holds at every point for all vector fields differentiable there; for a finite-dimensional
model space and a $C^1$ metric this is Mathlib's `IsMetricCompatible`. *Book:* p. 48, Corollary 8.4,
deduced from Lemma 8.3 with a curve whose velocity at $0$ is $X_p$. *Hidden hypotheses:*
differentiability at the point. *Deviation (restated, abstract):* Milnor's definition of
compatibility (parallel translation preserves inner products, p. 47) cannot be stated for Mathlib's
connections, which have no parallel transport; Corollary 8.4 is taken as the definition instead.

**V6.12 (the second fundamental form; `Morse.secondFundForm`, `Morse.secondFundForm_eq_sub_tanProj`,
`Morse.sub_tanProj_dN_eq_of_eq`, `Morse.secondFundForm_mem_orthogonal`,
`Morse.dN_tanProj_mem_of_mem_orthogonal`, `Morse.inner_secondFundForm_comm`,
`Morse.secondFundForm_comm`).** For $v \in T_qN$ let $D_v$ be the derivative of $q \mapsto P_q$ in
the direction $v$, and $\mathrm{II}_q(v, w) = D_vw$. For every vector field $W$ differentiable at
$q$, $\mathrm{II}_q(v, W(q)) = dW_q(v) - P_q(dW_q(v))$, the normal part of $dW_q(v)$, which
therefore depends only on $v$ and $W(q)$. For $v, w \in T_qN$, $\mathrm{II}_q(v, w)$ is normal to
$N$ and $\mathrm{II}_q(v, w) = \mathrm{II}_q(w, v)$; and
$\langle\mathrm{II}_q(v, x), y\rangle = \langle x, \mathrm{II}_q(v, y)\rangle$ for all $x, y \in V$
($D_v$ is self-adjoint; it maps $T_qN$ to normal vectors and normal vectors to $T_qN$). *Book:* not
in §§8–9; Milnor meets the second fundamental form in §6 (p. 34). *Deviation (not in the book):* it
is the tool for symmetry and curvature below. *Proof of the symmetry:* in a slice chart $\sigma$,
$T_xN$ is the kernel of $d(\sigma_2)_x$ for $x \in N$, so $d(\sigma_2)_x \circ P_x = 0$ on $N$;
differentiating along $N$ gives $d(\sigma_2)_q(\mathrm{II}(v, w)) = -d^2(\sigma_2)_q(v, w)$, which
is symmetric in $v, w$, so $\mathrm{II}(v, w) - \mathrm{II}(w, v)$ is tangent as well as normal.

**V6.13 (Definition 8.5, symmetric connections; `Morse.IsSymmetric`,
`Morse.isSymmetric_iff_torsion_eq_zero`, `Morse.bracket`, `Morse.bracket_mem`, `Morse.dN_bracket`,
`Morse.leviCivita_sub_leviCivita`).** *Abstract:* a covariant derivative is symmetric
(`Morse.IsSymmetric`) if $X \vdash Y - Y \vdash X = [X, Y]$ at every point where $X$ and $Y$ are
differentiable, $[X, Y]$ being Mathlib's Lie bracket of vector fields (which has Milnor's sign,
$[X, Y]f = X(Yf) - Y(Xf)$); for a finite-dimensional model space this is "the torsion is zero".
*Embedded:* the bracket of two maps $X, Y : N \to V$ is $[X, Y](q) = dY_q(X(q)) - dX_q(Y(q))$. For
vector fields differentiable at $q$ it is tangent to $N$ at $q$; for smooth $f$ and smooth vector
fields, $X(Yf) - Y(Xf) = [X, Y]f$, where $Xf = df(X)$; and the induced connection is symmetric:
$X \vdash Y - Y \vdash X = [X, Y]$ at $q$ for vector fields differentiable at $q$. *Book:* p. 48,
Definition 8.5, with $[X, Y]$ the Poisson bracket $[X, Y]f = X(Yf) - Y(Xf)$. *Hidden hypotheses:*
differentiability at the point; in the embedded setting, that the ambient formula for the bracket is
tangent and acts on functions as Milnor's bracket, neither of which is automatic. *Proof:* tangency
of the bracket is the symmetry of $\mathrm{II}$ (V6.12): the normal part of $[X, Y]$ is
$\mathrm{II}(X, Y) - \mathrm{II}(Y, X)$; the action on functions uses the symmetry of second
derivatives.

**V6.14 (Lemma 8.6, the fundamental lemma; `Morse.IsSymmCompat`, `Morse.isSymmCompat_leviCivita`,
`Morse.IsSymmCompat.two_mul_inner`, `Morse.IsSymmCompat.eq_leviCivita`, `Morse.koszul`,
`Morse.two_mul_inner_cov_eq_koszul`, `Morse.cov_eq_of_isSymmetric_of_isCompatible`,
`Morse.cov_eq_of_torsion_eq_zero_of_isMetricCompatible`).** *Embedded:* call an operation $D$ on
maps $N \to V$ symmetric and compatible if, on smooth vector fields, $D(X, Y)$ is tangent,
$D(X, Y) - D(Y, X) = [X, Y]$, and
$X\langle Y, Y'\rangle = \langle D(X, Y), Y'\rangle + \langle Y, D(X, Y')\rangle$. The induced
connection $P(dY(X))$ is such an operation (existence), every such operation satisfies the Koszul
formula
$$2\langle D(X, Y), Z\rangle = X\langle Y, Z\rangle + Y\langle X, Z\rangle - Z\langle X, Y\rangle +
\langle[X, Y], Z\rangle - \langle[X, Z], Y\rangle - \langle[Y, Z], X\rangle$$
on smooth vector fields, and every such operation agrees with $P(dY(X))$ on smooth vector fields at
every point (uniqueness). *Abstract:* for a manifold with a Riemannian metric on its tangent bundle,
two covariant derivatives that are both symmetric and compatible (V6.11, V6.13) satisfy the Koszul
formula and agree on every vector field differentiable at the point; with Mathlib's predicates, two
torsion-free metric connections agree on such fields (finite-dimensional model space, $C^1$ metric).
*Book:* p. 48, Lemma 8.6: a Riemannian manifold possesses one and only one symmetric connection
compatible with its metric; uniqueness by the Christoffel identities (p. 49), and "one can verify"
the converse. *Hidden hypotheses:* the existence half needs a converse of Lemma 8.3, which Milnor
does not state, and a patching of the local connections. *Deviation (stronger):* the embedded
uniqueness assumes no linearity or tensoriality of $D$, only the three properties on smooth fields.
*Deviation (narrower):* existence is proved only in the embedded setting; on an abstract manifold
only uniqueness, and only on sections differentiable at the point (a Mathlib covariant derivative is
unconstrained elsewhere). *Proof:* the Koszul formula, the coordinate-free form of Milnor's first
Christoffel identity, replaces his linear system on p. 49 (whose list of three unknowns contains
$\langle\partial_i \vdash \partial_j, \partial_k\rangle$ twice, by the symmetry he quotes, a
misprint); uniqueness applies it with $Z$ the field $x \mapsto P_x(D(X, Y)(q) - (X \vdash Y)(q))$ of
V6.2.

**V6.15 (Lemma 8.7; `Morse.velX`, `Morse.velY`, `Morse.covDerivX`, `Morse.covDerivY`,
`Morse.covDerivX_eq`, `Morse.covDerivX_velY`).** For a smooth surface $s : \mathbb R^2 \to N$ the
velocity fields $\partial s/\partial x$, $\partial s/\partial y$ are tangent, and $DW/\partial x$ is
defined, as in Milnor, as the covariant derivative of $x \mapsto W(x, y_0)$ along the curve
$x \mapsto s(x, y_0)$ (similarly $DW/\partial y$); at a point $p$ where $W$ is differentiable it
equals $P_{s(p)}(\partial W/\partial x\,(p))$. Then
$\frac{D}{\partial x}\frac{\partial s}{\partial y} = \frac{D}{\partial y}\frac{\partial s}{\partial x}$
at every point. *Book:* p. 50, Lemma 8.7, for a symmetric connection; the proof is to express both
sides in local coordinates and compute. *Hidden hypotheses:* joint smoothness of $DW/\partial x$ in
$(x, y)$, which Milnor defines one curve at a time; here it is visible from the formula. *Deviation
(narrower):* the induced connection, which is symmetric (V6.13). *Proof:* both sides are
$P(\partial^2s/\partial x\partial y)$.

**V6.16 (the curvature tensor and its sign; `Morse.milnorCurvature`, `Morse.nomizuCurvature`,
`Morse.milnorCurvature_eq_neg`, `Morse.milnorCurvature_swap`, `Morse.curvature`).** For a covariant
derivative on an abstract manifold, Milnor's curvature of vector fields is
$R(X, Y)Z = -X \vdash (Y \vdash Z) + Y \vdash (X \vdash Z) + [X, Y] \vdash Z$; it is the negative of
Nomizu's (and Kobayashi–Nomizu's) $\nabla_X\nabla_YZ - \nabla_Y\nabla_XZ - \nabla_{[X, Y]}Z$, and
$R(Y, X)Z = -R(X, Y)Z$. In the embedded setting the same formula, with the induced connection and
the bracket of V6.13, defines $R(X, Y)Z$ for maps $N \to V$. *Book:* p. 51, the definition, with the
footnote that Nomizu gives $R$ the opposite sign. *Hidden hypotheses:* none. Mathlib defines no
curvature, so there is no Mathlib sign to compare with.

**V6.17 (Lemma 9.1, made explicit; `Morse.curvOp`, `Morse.curvature_eq`, `Morse.curvTensor`,
`Morse.curvature_eq_curvTensor`, `Morse.curvature_congr`).** In the embedded setting, for smooth
vector fields $X, Y, Z$ and every $q$,
$$R(X, Y)Z\,(q) = \mathrm{II}_q\big(Y_q, \mathrm{II}_q(X_q, Z_q)\big) - \mathrm{II}_q\big(X_q,
\mathrm{II}_q(Y_q, Z_q)\big),$$
that is, $R(X, Y) = D_YD_X - D_XD_Y$ on $T_qN$. Consequently $R(X, Y)Z$ at $q$ depends only on
$X_q$, $Y_q$, $Z_q$, and it is the value of a trilinear map $T_qN \times T_qN \times T_qN \to T_qN$,
the curvature tensor of $N$ at $q$. *Book:* p. 51, Lemma 9.1: the value of $R(X, Y)Z$ at $p$ depends
only on $X_p, Y_p, Z_p$, and the correspondence is trilinear. *Hidden hypotheses:* none. *Deviation
(stronger):* an explicit formula. *Deviation (narrower):* the embedded setting. *Proof:* with a
smooth ambient representative $G$ of $Z$, $Y \vdash (X \vdash Z)$ at $q$ is $D_YD_XZ$ plus terms
that cancel by the symmetry of $d^2G$ and against $[X, Y] \vdash Z$. Milnor treats $X$ explicitly
and says the identities for $Y$ and $Z$ "are easily obtained by similar computations"; for $Z$ the
computation is a different one.

**V6.18 (the Gauss equation; `Morse.inner_curvOp`, `Morse.gauss_equation`).** For all
$x, y, z, w \in V$,
$$\langle D_yD_xz - D_xD_yz, w\rangle = \langle\mathrm{II}(x, z), \mathrm{II}(y, w)\rangle -
\langle\mathrm{II}(x, w), \mathrm{II}(y, z)\rangle$$
at $q$; hence, for smooth vector fields $X, Y, Z$ and any $W : N \to V$,
$$\langle R(X, Y)Z, W\rangle = \langle\mathrm{II}(X, Z), \mathrm{II}(Y, W)\rangle -
\langle\mathrm{II}(X, W), \mathrm{II}(Y, Z)\rangle$$
at every point, with Milnor's sign of $R$. With $Z = X$, $W = Y$ and the symmetry of $\mathrm{II}$
(V6.12) this gives
$\langle R(X, Y)X, Y\rangle = \langle\mathrm{II}(X, X), \mathrm{II}(Y, Y)\rangle - \|\mathrm{II}(X, Y)\|^2$,
Gauss's curvature for a surface in $\mathbb R^3$. *Book:* not in Milnor's text. *Deviation (not in
the book).*

**V6.19 (Lemma 9.2; `Morse.covDerivY_covDerivX_sub`).** For a smooth surface $s : \mathbb R^2 \to N$
and a smooth map $W : \mathbb R^2 \to V$ with $W(p) \in T_{s(p)}N$ for all $p$,
$$\frac{D}{\partial y}\frac{D}{\partial x}W - \frac{D}{\partial x}\frac{D}{\partial y}W =
R\Big(\frac{\partial s}{\partial x}, \frac{\partial s}{\partial y}\Big)W$$
at every point, with $R(x, y) = D_yD_x - D_xD_y$ the curvature of V6.17. *Book:* p. 52, Lemma 9.2,
again proved by a computation in local coordinates. *Hidden hypotheses:* joint smoothness of
$DW/\partial x$ (as in V6.15). *Deviation (narrower):* the embedded setting. *Proof:* from $W = PW$,
$PD_vP = 0$, and the fact that $D_v$ maps normal vectors to tangent ones; no symmetry of the
connection is used.

**V6.20 (Lemma 9.3 (1)–(3); `Morse.IsCurvatureTensor`, `Morse.inner_add_inner_eq_zero_iff`,
`Morse.isCurvatureTensor_curvTensor`, `Morse.curvature_add_swap`, `Morse.curvature_bianchi`,
`Morse.inner_curvature_add_inner`).** A trilinear map $R$ on a real inner product space is called a
curvature tensor (`Morse.IsCurvatureTensor`) if it satisfies (1) $R(X, Y)Z + R(Y, X)Z = 0$, (2)
$R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0$, (3)
$\langle R(X, Y)Z, W\rangle + \langle R(X, Y)W, Z\rangle = 0$. For a linear map $T$,
$\langle TZ, W\rangle$ is skew in $Z, W$ iff $\langle TZ, Z\rangle = 0$ for all $Z$. The curvature
tensor of $N$ at each point (V6.17) satisfies (1)–(3). For maps $X, Y, Z$ of $N$ into $V$, (1) holds
with no hypothesis; for smooth vector fields, (2) and (3) hold at every point. *Book:* p. 53, Lemma
9.3 (1)–(3), and "clearly equivalent" for the reduction of (3) to $\langle R(X, Y)Z, Z\rangle = 0$.
*Hidden hypotheses:* Milnor proves (2) and (3) for extensions with vanishing brackets, which must be
constructed (coordinate fields cut off by a bump function). *Deviation (narrower):* the embedded
setting. *Proof:* no extensions are needed; (2) is the symmetry of $\mathrm{II}$ and (3) the
self-adjointness of $D_v$ (V6.12).

**V6.21 (Lemma 9.3 (4), the octahedron; `Morse.octahedron`,
`Morse.IsCurvatureTensor.inner_comm_pairs`, `Morse.inner_curvature_comm_pairs`).** Let
$T(X, Y, Z, W)$ be any real function of four arguments that is skew in $(X, Y)$, skew in $(Z, W)$
and satisfies $T(X, Y, Z, W) + T(Y, Z, X, W) + T(Z, X, Y, W) = 0$. Then
$T(X, Y, Z, W) = T(Z, W, X, Y)$. Hence every curvature tensor (V6.20) satisfies (4)
$\langle R(X, Y)Z, W\rangle = \langle R(Z, W)X, Y\rangle$, and so does $R$ on smooth vector fields
of $N$. *Book:* p. 54: (4) from (1), (2), (3) by the octahedron, the four shaded faces being
instances of (2), "making use of (1) and (3)". *Hidden hypotheses:* none. *Deviation (stronger):* no
linearity of $T$ is used. *Proof:* Milnor's; the four face identities, whose signs he leaves to the
reader, are written out.

**V6.22 (sectional curvature; `Morse.sectionalCurvature`,
`Morse.IsCurvatureTensor.sectionalCurvature_smul_add`, `Morse.IsCurvatureTensor.neg`,
`Morse.IsCurvatureTensor.inner_neg_apply_swap`).** For a trilinear map $R$ and vectors $X, Y$, put
$K(X, Y) = \langle R(X, Y)X, Y\rangle / (\|X\|^2\|Y\|^2 - \langle X, Y\rangle^2)$ (Lean's convention
gives $0$ when $X, Y$ are dependent); for an orthonormal pair this is Milnor's
$\langle R(A, B)A, B\rangle$. If $R$ satisfies (1)–(3), $K$ depends only on the plane:
$K(aX + bY, cX + dY) = K(X, Y)$ whenever $ad - bc \neq 0$. With the standard sign, $-R$ also
satisfies (1)–(3), and $\langle(-R)(X, Y)Y, X\rangle = \langle R(X, Y)X, Y\rangle$: the sectional
curvature is the same number in both conventions. *Book:* p. 100, remark after Lemma 19.1: for
orthogonal unit vectors $A, B$ at $p$, $\langle R(A, B)A, B\rangle$ is the sectional curvature
determined by $A$ and $B$. *Hidden hypotheses:* that this number depends only on the plane spanned
by $A$ and $B$ is not stated in the book. *Deviation (stronger):* defined for any independent pair,
and shown to depend only on the plane.

**V6.23 (the sectional curvatures determine $R$; `Morse.IsCurvatureTensor.polarization`,
`Morse.IsCurvatureTensor.ext`, `Morse.IsCurvatureTensor.ext_of_sectionalCurvature`,
`Morse.IsCurvatureTensor.ext_of_orthonormal`).** For a curvature tensor $R$,
$6\langle R(X, Y)Z, W\rangle$ is an explicit combination of the values
$k(A, B) = \langle R(A, B)A, B\rangle$ at sums of $X, Y, Z, W$ (polarization). Hence two curvature
tensors are equal as soon as they have the same $\langle R(X, Y)X, Y\rangle$ for all $X, Y$, or the
same sectional curvature on all independent pairs, or the same $\langle R(A, B)A, B\rangle$ on all
orthonormal pairs (Milnor's definition). *Book:* not stated. *Deviation (not in the book):* Lemma
7.2 of the exposition.

**V6.24 (constant curvature; `Morse.curvatureOne`, `Morse.isCurvatureTensor_curvatureOne`,
`Morse.sectionalCurvature_smul_curvatureOne`,
`Morse.IsCurvatureTensor.eq_smul_curvatureOne_of_orthonormal`,
`Morse.IsCurvatureTensor.apply_eq_of_sectionalCurvature_eq`, `Morse.neg_smul_curvatureOne_apply`).**
$R_1(X, Y)Z = \langle X, Z\rangle Y - \langle Y, Z\rangle X$ is a curvature tensor, and $\kappa R_1$
has sectional curvature $\kappa$ on every independent pair. Conversely, if a curvature tensor $R$
has $\langle R(A, B)A, B\rangle = \kappa$ for all orthonormal $A, B$, or $K(X, Y) = \kappa$ for all
independent $X, Y$, then $R(X, Y)Z = \kappa(\langle X, Z\rangle Y - \langle Y, Z\rangle X)$; with
the standard sign this is $\kappa(\langle Y, Z\rangle X - \langle X, Z\rangle Y)$. *Book:* not
stated in §§8–9 or on p. 100. *Deviation (not in the book):* Corollary 7.3 of the exposition.

**V6.25 (the round sphere; `Milnor.Sphere.Sph`, `Milnor.Sphere.sphSub`, `Morse.tanProj_sph`,
`Morse.secondFundForm_sph`, `Morse.curvOp_sph`, `Morse.curvTensor_sph`,
`Morse.sectionalCurvature_sph`, `Morse.inner_curvTensor_sph_orthonormal`).** For the unit sphere
$S^n \subseteq \mathbb R^{n+1}$ (a slice submanifold, from the companion project) with the induced
metric: $P_qv = v - \langle q, v\rangle q$; $\mathrm{II}_q(v, w) = -\langle v, w\rangle q$ for
tangent $v, w$; the curvature tensor is $R(x, y)z = \langle x, z\rangle y - \langle y, z\rangle x$
with Milnor's sign; so $S^n$ has sectional curvature $1$, both as $K(x, y) = 1$ for independent
tangent $x, y$ and as $\langle R(A, B)A, B\rangle = 1$ for orthonormal $A, B$. *Book:* not in §§8–9;
the computation is the application in §8 of the exposition. *Deviation (not in the book).* *Proof:*
coordinate-free, from the Gauss equation (V6.18).

### What is not verified in this chapter

- **§§8–9 on an abstract Riemannian manifold**, beyond V6.3, V6.11, V6.13, V6.14 (uniqueness) and
  V6.16: the existence of the Levi-Civita connection, Christoffel symbols and formulas (5), (6), the
  coordinate formula for $DV/dt$, Lemmas 8.1–8.3 and 8.7, the tensor property of $R$ (Lemma 9.1),
  Lemma 9.2, and (2)–(4) of Lemma 9.3 for vector fields. Mathlib has no curvature, Christoffel
  symbols, covariant derivative along curves, parallel transport or Levi-Civita connection; the
  embedded results reach an arbitrary Riemannian manifold only through Nash's embedding theorem,
  which is neither in Mathlib nor proved here.
- **The bridge between the two settings:** the induced connection of $N$ as a Mathlib
  `CovariantDerivative` on the tangent bundle of $N$, with the induced metric as a Riemannian
  bundle, is not constructed. The embedded existence (V6.14) and the abstract uniqueness (V6.14) are
  parallel results, not one theorem.
- **Milnor's side remarks:** the converse "if $\Gamma^k_{ij} = \Gamma^k_{ji}$ then the connection is
  symmetric" (p. 48), the footnote on the covariant second derivative (p. 48), and the construction
  of parallel fields along a surface when $R = 0$ (pp. 52–53).
- **The geometric meaning of sectional curvature** (p. 100: the Gaussian curvature of the surface
  swept out by geodesics tangent to the plane): it needs geodesics and the exponential map (§10,
  Chapter 7 of this edition), not used here.

---

## 8. Chapter 7 (Milnor §10): partly verified

Milnor's §10 (pp. 55–66) defines geodesics on a connected Riemannian manifold and notes that their
speed is constant (p. 55), quotes the existence and uniqueness theorem for ordinary differential
equations (Theorem 10.1), obtains geodesics on a fixed time interval for small initial velocities
(Lemma 10.2), defines the exponential map and geodesic completeness (pp. 57–58), builds uniformly
normal neighbourhoods (Lemma 10.3), and proves that short geodesics are shortest (Theorem 10.4, from
the Gauss lemma 10.5 and Lemma 10.6) and that shortest paths parametrized by arc length are
geodesics (Corollary 10.7). He then defines the distance $\rho$, proves Corollary 10.8, the
Hopf–Rinow theorem (Theorem 10.9) and Corollary 10.10, states its converse, and ends with examples
(pp. 65–66). Verified: every numbered statement from Theorem 10.1 through Corollary 10.10 (Lemma
10.6 in a one-sided form), and the converse of Corollary 10.10, with the definitions they need
(geodesics, the exponential map, piecewise smooth paths and their lengths, the distance, minimal
geodesics, metric and geodesic completeness), for a submanifold $N$ of a Euclidean space with the
induced metric, in the embedded setting of Chapter 6; Theorem 10.1 itself for a finite-dimensional
normed space. Every Riemannian manifold is isometric to such an $N$ by Nash's embedding theorem,
which is quoted in the Lean files but neither proved nor used, so these results are statements
about embedded manifolds with the induced metric. In this setting the Hausdorff property that
Milnor uses silently is automatic, and his standing assumption that $M$ is connected is made only
where it is needed (finiteness of $\rho$, Theorem 10.9 for all pairs of points, Corollary 10.10,
the Hopf–Rinow equivalence); elsewhere $\rho$ may take the value $\infty$. Proved more sharply than
in the book: **the equality case of Theorem 10.4** (a path of the same length is a monotone
reparametrization of the geodesic, V7.16), which Corollary 10.7 needs; the uniqueness of geodesics
in the large (V7.5), the smooth dependence in Lemma 10.2 (V7.6) and the Gauss lemma in every
direction (V7.12); and **Theorem 10.9 with completeness at a single point** (V7.26), which yields
the four-way Hopf–Rinow equivalence (V7.29). Supplied where the book is silent or refers
elsewhere: the continuity of $\rho$ (V7.21), the continuity of $\exp$ on its whole domain
(V7.23), the converse of Corollary 10.10 (V7.28); and, not in the book, the completeness of closed
submanifolds, among them the sphere (V7.30). The smoothness of $\exp$ on its whole domain, and the
extension of a geodesic on $[0, 1]$ past its ends, are proved later (Chapters 9 and 11; V7.7 and
the list at the end). **Not verified:** maximal geodesics, the convexity remark after Lemma 10.3,
the remarks on minimal geodesics of p. 62 and the examples of pp. 65–66 (the list at the end). Lean: `Morse/Chapter7/` —
`ODE.lean` (235 lines), `Geodesic.lean` (368), `GeodesicLocal.lean` (447), `Exp.lean` (337),
`NormalNbhd.lean` (764), `GaussLemma.lean` (419), `Path.lean` (394), `Shortest.lean` (542),
`Minimal.lean` (329), `Distance.lean` (386), `Metric.lean` (309), `GeodesicFlow.lean` (766),
`HopfRinow.lean` (664).

**The embedded setting.** As in Chapter 6: $V$ is a finite-dimensional real inner product space
(Milnor's $\mathbb R^K$) and $N \subseteq V$ a slice submanifold modelled on $Z$ with complement $W$
(V1.6), $Z$ and $W$ finite-dimensional (automatic when $N$ is non-empty), with the induced metric.
$T_qN \subseteq V$ is the tangent space at $q$, $P_q$ the orthogonal projection onto it (V6.1),
$\mathrm{II}$ the second fundamental form (V6.12) and $D/dt = P \circ d/dt$ the covariant derivative
along curves (V6.5). Curves are maps $\mathbb R \to V$, of which only the values on the interval
considered matter. A map defined on a subset of $V$, $V \times V$ or $V \times V \times \mathbb R$ is
called smooth there if it is the restriction of a map that is smooth on an open set containing the
subset (or, where so stated, near each of its points); this is Milnor's notion of smoothness for
subsets of Euclidean space. $N$ need not be closed, compact or connected.

**V7.1 (geodesics; `Morse.IsGeodesicOn`, `Morse.hasDerivAt_mem_tangentSubspace`,
`Morse.IsGeodesicOn.deriv_mem`, `Morse.IsGeodesicOn.tanProj_deriv_deriv`,
`Morse.isGeodesicOn_univ_iff_covDeriv`, `Morse.isGeodesicOn_const`).** Let $s \subseteq \mathbb R$ be
open, in practice an open interval. A curve $\gamma$ is a geodesic on $s$ if it is $C^\infty$ on $s$,
$\gamma(t) \in N$ for $t \in s$, and the acceleration $\gamma''(t)$ is orthogonal to $T_{\gamma(t)}N$
for every $t \in s$. The velocity at $t$ of a curve that lies in $N$ near $t$ and is differentiable
at $t$ is tangent to $N$; so for a geodesic $\gamma'(t) \in T_{\gamma(t)}N$, and the condition on
$\gamma''$ reads $P_{\gamma(t)}\gamma''(t) = 0$, Milnor's $\frac{D}{dt}\frac{d\gamma}{dt} = 0$ with
$D/dt$ of V6.5. Formally: a smooth curve $c : \mathbb R \to N$ is a geodesic on $\mathbb R$ iff
$\frac{D}{dt}\frac{dc}{dt}(t) = 0$ for all $t$ (V6.5 defines $D/dt$ for curves on all of
$\mathbb R$). Constant curves at points of $N$ are geodesics. *Book:* p. 55: on a connected
Riemannian manifold $M$, a parametrized path $\gamma : I \to M$, $I$ any interval, is a geodesic if
its acceleration $\frac{D}{dt}\frac{d\gamma}{dt}$ vanishes identically, i.e. its velocity field is
parallel along $\gamma$. *Hidden hypotheses:* none. *Deviation (narrower):* the embedded setting,
where a geodesic is a curve whose acceleration in $V$ is normal to $N$; geodesics live on open sets,
so a geodesic on a closed interval is represented by one on a slightly larger open interval (V7.7).

**V7.2 (constant speed and homogeneity; `Morse.IsGeodesicOn.hasDerivAt_norm_sq`,
`Morse.IsGeodesicOn.norm_deriv_eq`, `Morse.IsGeodesicOn.pathLength_eq`,
`Morse.IsGeodesicOn.comp_mul_add`).** For a geodesic $\gamma$ on $s$,
$\frac{d}{dt}\|\gamma'\|^2 = 2\langle\gamma'', \gamma'\rangle = 0$ on $s$. If $s$ is an open
interval (more generally, preconnected), the speed $\|\gamma'\|$ is constant on $s$, and the length
of $\gamma$ on any $[a, b] \subseteq s$ (V7.11) is $\|\gamma'(t_0)\|\,(b - a)$ for every $t_0 \in s$.
For all real $a$, $b$ the curve $t \mapsto \gamma(at + b)$ is a geodesic on $\{t : at + b \in s\}$.
*Book:* p. 55: $\frac{d}{dt}\langle\frac{d\gamma}{dt}, \frac{d\gamma}{dt}\rangle =
2\langle\frac{D}{dt}\frac{d\gamma}{dt}, \frac{d\gamma}{dt}\rangle = 0$, so the speed is constant and
the parameter is a linear function of arc length; p. 57 (homogeneity): if $t \mapsto \gamma(t)$ is a
geodesic, so is $t \mapsto \gamma(ct)$ for every constant $c$. *Hidden hypotheses:* none.
*Deviation (stronger):* all affine changes of parameter $t \mapsto at + b$ ($a = 0$ gives a constant
curve).

**V7.3 (the geodesic equation; `Morse.IsGeodesicOn.deriv_deriv_eq`,
`Morse.isGeodesicOn_of_deriv_deriv_eq`, `Morse.geodesicSpray`,
`Morse.IsGeodesicOn.mem_tangentBundleSet`, `Morse.isGeodesicOn_iff_hasDerivAt_geodesicSpray`,
`Morse.pinvL`, `Morse.chartAcc`, `Morse.chartSpray`, `Morse.contDiffOn_chartSpray`,
`Morse.isGeodesicOn_chart`).** Let $\gamma$ be $C^\infty$ on an open set $s$ with
$\gamma(s) \subseteq N$. Then $\gamma$ is a geodesic on $s$ iff
$\gamma'' = \mathrm{II}_\gamma(\gamma', \gamma')$ on $s$, iff the lift
$t \mapsto (\gamma(t), \gamma'(t))$, which then lies in
$TN = \{(x, v) : x \in N,\ v \in T_xN\}$, is an integral curve on $s$ of the geodesic spray
$(x, v) \mapsto (v, \mathrm{II}_x(v, v))$. In a slice chart with parametrization $x$ (V1.6) on the
open set $T \subseteq Z$, put $A^+ = (A^{\mathsf T}A)^{-1}A^{\mathsf T}$ for injective $A$ and
$\Gamma(u)(w, w) = (dx_u)^+\big(d^2x_u(w, w)\big)$. The field $(u, w) \mapsto (w, -\Gamma(u)(w, w))$
is smooth on $T \times Z$, and if $(u, w)$ is a $C^\infty$ solution of $u' = w$,
$w' = -\Gamma(u)(w, w)$ on an open set $s$ with $u(s) \subseteq T$, then $x \circ u$ is a geodesic on
$s$. *Book:* p. 55: in local coordinates the geodesic condition becomes the system
$\frac{d^2u^k}{dt^2} + \sum_{i,j}\Gamma^k_{ij}\frac{du^i}{dt}\frac{du^j}{dt} = 0$, so the existence of
geodesics rests on a system of second-order equations (the scan shows only the $\Gamma$-term of this
display, a defect of the scan, not a misprint). *Hidden hypotheses:* none. *Deviation (restated):*
$(dx_u)^+d^2x_u(w, w)$ is the coordinate vector, in the basis $\partial x/\partial u^k$, of the
tangential part of $d^2x_u(w, w)$, that is $\big(\sum_{i,j}\Gamma^k_{ij}w^iw^j\big)_k$ for the
Christoffel symbols of the induced metric; the Lean files define no Christoffel symbols, so this
identification is a remark, not a theorem. In the chart only the direction "solutions are
geodesics" is stated, which is what existence needs (V7.6); uniqueness uses the global form (V7.5).

**V7.4 (Theorem 10.1; `Morse.exists_localFlow`, `Morse.theorem_10_1`, `Morse.ode_eventuallyEq`,
`Morse.ode_eqOn`, `Morse.eqOn_of_eventuallyEq`, `Morse.theorem_10_1_unique`).** *Existence and
smooth dependence.* Let $E$ be a finite-dimensional real normed space (Milnor's $\mathbb R^n$),
$U \subseteq E \times E$ open, $F : E \times E \to E$ smooth on $U$, and $z_1 \in U$. There are a
neighbourhood $W$ of $z_1$, an $\varepsilon > 0$ and a map $(z, t) \mapsto u_z(t)$, smooth on
$W \times (-\varepsilon, \varepsilon)$, such that for every $z = (u_0, v_0) \in W$: $u_z(0) = u_0$,
$u_z'(0) = v_0$, and $(u_z(t), u_z'(t)) \in U$ and $u_z''(t) = F(u_z(t), u_z'(t))$ for
$|t| < \varepsilon$. In first-order form: for $G$ smooth on an open set $U \ni x_1$ of $E$ there are
a smooth $\varphi : \mathbb R \times E \to E$ and $r, \tau > 0$ such that for $\|x - x_1\| < r$ the
curve $t \mapsto \varphi(t, x)$ solves $x' = G(x)$ in $U$ for $|t| < \tau$, with $\varphi(0, x) = x$.
*Uniqueness.* Let $E$ be any real normed space and $G$ of class $C^1$ on an open set
$U \subseteq E$. Two solutions of $x' = G(x)$ with values in $U$ that agree at one time agree near
it, and, if both are defined on the same open interval (more generally, open preconnected set), on
all of it. In particular, if $F$ is $C^1$ on $U \subseteq E \times E$, two pairs $(u_i, v_i)$ with
$u_i' = v_i$, $v_i' = F(u_i, v_i)$ and $(u_i, v_i) \in U$ on an open interval $s$, with the same
position and velocity at one time of $s$, have $u_1 = u_2$ on $s$. *Book:* p. 56, Theorem 10.1, for
an $n$-tuple $F$ of $C^\infty$ functions near $(u_1, v_1) \in \mathbb R^{2n}$: a neighbourhood $W$ and
an $\varepsilon > 0$ such that for $(u_0, v_0) \in W$ the equation has a unique solution for
$|t| < \varepsilon$ with the given initial conditions, and $(u_0, v_0, t) \mapsto u(t)$ is
$C^\infty$ on $W \times (-\varepsilon, \varepsilon)$; the proof passes to the first-order system
$du/dt = v$, $dv/dt = F(u, v)$ and quotes Graves (the scan shows only part of the displayed
equation). *Hidden hypotheses:* none. *Deviation (stronger):* uniqueness on every common interval of
definition, for $C^1$ equations on any normed space. *Proof:* proved, not quoted: $G$ times a bump
function equal to $1$ near $x_1$ is a compactly supported smooth field whose global flow is smooth in
$(t, x)$ (V1.14), and its bounded speed keeps the flow lines from points near $x_1$, for a uniform
time, where the bump function is $1$; uniqueness is Grönwall's inequality (Mathlib) near each time,
spread over the interval by connectedness.

**V7.5 (uniqueness of geodesics; `Morse.projRep`, `Morse.IsGeodesicOn.eventuallyEq`,
`Morse.IsGeodesicOn.eqOn`).** Two geodesics on open sets $s_1$, $s_2$ containing $t_0$, with the
same position and the same velocity at $t_0$, agree near $t_0$. Two geodesics on the same open
interval (more generally, open preconnected set) $s$, with the same position and velocity at one
time of $s$, agree on all of $s$. *Book:* Theorem 10.1 gives uniqueness for small times in one
coordinate system (p. 56); Lemmas 10.2 and 10.3 assert uniqueness of geodesics on whole intervals,
and p. 58 says that $\exp_q(v)$, if defined at all, is uniquely defined. *Hidden hypotheses:*
uniqueness in the large, by a connectedness argument; on an abstract manifold it also needs the
Hausdorff property, automatic here. *Deviation (not in the book):* the statement, which is the
exposition's Lemma A. *Proof:* near $t_0$ both lifts $(\gamma_i, \gamma_i')$ solve
$(x, v)' = (v, dQ_x(v)\,v)$, where $Q$ is the smooth extension of $x \mapsto P_x$ to an open set of
$V$ given by a slice chart at $\gamma_1(t_0)$ (V6.2); this field is smooth, so V7.4 applies.

**V7.6 (Lemma 10.2; `Morse.LocalSpray`, `Morse.nonempty_localSpray`, `Morse.LocalSpray.geo`,
`Morse.LocalSpray.isGeodesicOn_geo`, `Morse.LocalSpray.contDiffOn_geo`, `Morse.lemma_10_2`).** For
every $q_0 \in N$ there are an open set $U \ni q_0$ of $V$, an $\varepsilon > 0$ and a map
$\Gamma : V \times V \times \mathbb R \to V$, smooth on
$U \times \{v : \|v\| < \varepsilon\} \times (-2, 2)$, such that for every $p \in N \cap U$ and every
$v \in T_pN$ with $\|v\| < \varepsilon$, the curve $\gamma_v = \Gamma(p, v, \cdot)$ is a geodesic on
$(-2, 2)$ with $\gamma_v(0) = p$ and $\gamma_v'(0) = v$, and every geodesic on $(-2, 2)$ with this
position and velocity at $0$ equals $\gamma_v$ on $(-2, 2)$. *Book:* p. 56, Lemma 10.2: for $p$ in a
neighbourhood $U$ of $p_0$ and $v \in TM_p$ of length $< \varepsilon$ there is a unique geodesic
$\gamma_v : (-2, 2) \to M$ with $\gamma_v(0) = p$ and $\frac{d\gamma_v}{dt}(0) = v$; the proof
(pp. 56–57) gets $\varepsilon_1$, $\varepsilon_2$ from Theorem 10.1 in a coordinate system and puts
$\gamma_v(t) = \gamma_{v/\varepsilon_2}(\varepsilon_2t)$ for
$\|v\| < \varepsilon < \varepsilon_1\varepsilon_2$. *Hidden hypotheses:* the step from the
coordinate neighbourhood $W$ of Theorem 10.1 to the condition "$p \in U$, $\|v\| < \varepsilon_1$"
needs a bound for the coordinates of $v$ by $\|v\|$, uniform for $p$ near $p_0$; uniqueness on
$(-2, 2)$ is V7.5. *Deviation (stronger):* $\gamma_v(t)$ depends smoothly on $(p, v, t)$, which
Milnor does not state here but uses on p. 58 (V7.8). *Proof:* Milnor's, with Theorem 10.1 (V7.4)
applied to the chart equation of V7.3 near $(u_0, 0)$ and the rescaling by half the time of
existence; the coordinates of $v$ are $(d\sigma_p v)_1$, $\sigma$ the slice chart, and
$\|d\sigma_p v\| \le \|d\sigma_p\|\,\|v\|$ with $\|d\sigma_p\|$ bounded near $q_0$.

**V7.7 (the exponential map; `Morse.IsGeodesicFrom`, `Morse.expDom`, `Morse.exp`,
`Morse.IsGeodesicFrom.mem`, `Morse.isGeodesicFrom_of_isGeodesicOn`, `Morse.IsGeodesicFrom.eqOn`,
`Morse.IsGeodesicFrom.exp_eq`, `Morse.exp_zero`, `Morse.zero_mem_expDom`,
`Morse.IsGeodesicFrom.exp_smul`, `Morse.IsGeodesicFrom.isGeodesicOn_exp_smul`).** For $q, v \in V$,
a geodesic from $q$ with initial velocity $v$ is a geodesic $\gamma$ on an open interval
$(-\delta, 1 + \delta)$, $\delta > 0$, with $\gamma(0) = q$ and $\gamma'(0) = v$ (then $q \in N$, and
$v \in T_qN$ by V7.1); a geodesic on an open interval containing $0$ and $1$ is one, from
$\gamma(0)$ with initial velocity $\gamma'(0)$. The domain of $\exp$ is the set of pairs $(q, v)$ for
which such a geodesic exists, and $\exp_q(v) = \gamma(1)$ (off the domain $\exp_q(v)$ is defined to
be $q$, a placeholder). Two geodesics from $q$ with initial velocity $v$ agree on an open interval
containing $[0, 1]$, so $\exp_q(v) = \gamma(1)$ for every such $\gamma$. For $q \in N$, $(q, 0)$ is
in the domain and $\exp_q(0) = q$. If $\gamma$ is a geodesic from $q$ with initial velocity $v$,
there is $\delta > 0$ such that $\gamma$ is a geodesic on $(-\delta, 1 + \delta)$ and, for each $t$
in this interval, $s \mapsto \gamma(ts)$ is a geodesic from $q$ with initial velocity $tv$ and
$\exp_q(tv) = \gamma(t)$; so $t \mapsto \exp_q(tv)$ is a geodesic near $[0, 1]$, equal to $\gamma$. *Book:* p. 57: for $v \in TM_q$ and a geodesic
$\gamma : [0, 1] \to M$ with $\gamma(0) = q$ and $\frac{d\gamma}{dt}(0) = v$, $\exp_q(v) = \gamma(1)$,
and $\gamma(t) = \exp_q(tv)$; p. 58: $\exp_q(v)$ is defined for small $\|v\|$, in general not for
large $v$, but uniquely defined whenever defined. *Hidden hypotheses:* well-definedness is the
uniqueness in the large of V7.5; $\gamma(t) = \exp_q(tv)$ uses homogeneity (V7.2) together with
V7.5. *Deviation (restated):* Milnor's geodesic on the closed interval $[0, 1]$ (with one-sided
derivatives at the ends) is replaced by one on an open interval containing $[0, 1]$. Restricting to
$[0, 1]$ gives a geodesic in Milnor's sense with the same value $\gamma(1)$, and both domains contain
every $(q, v) \in TN$ with $v$ small enough (V7.8). Conversely, a geodesic on $[0, 1]$ in Milnor's
sense (a curve in $N$, $C^\infty$ on $[0, 1]$ with one-sided derivatives at the ends, and a geodesic
on $(0, 1)$) agrees on $[0, 1]$ with $t \mapsto \exp_{\gamma(0)}(t\gamma'(0))$, which is a geodesic
on an open interval containing $[0, 1]$ (V9.9 (ii), `Morse.exists_initial_ray`), so that
$(\gamma(0), \gamma'(0))$ is in the formal domain (V11.1 (iii), `Morse.mem_expDom_of_isGeodesicOn`):
the two domains coincide. This is proved in Chapters 9 and 11, not in `Morse/Chapter7/`.

**V7.8 (the tangent manifold, $\exp$ near the zero section, and $d(\exp_q)_0$;
`Milnor.Problems.tangentBundleSet`, `Milnor.Problems.isSliceSubmanifold_tangentBundle`,
`Morse.exists_exp_eq`, `Morse.exists_isOpen_exp`, `Morse.contMDiffOn_exp`,
`Morse.hasFDerivAt_exp_zero`).** $TN = \{(q, v) \in V \times V : q \in N,\ v \in T_qN\}$ is a slice
submanifold of $V \times V$ modelled on $Z \times Z$ (the companion project). (i) For every
$q_0 \in N$ there are an open set $U \ni q_0$ of $V$, an $\varepsilon > 0$ and a map
$F : V \times V \to V$, smooth on $U \times \{v : \|v\| < \varepsilon\}$, such that for
$p \in N \cap U$ and $v \in T_pN$ with $\|v\| < \varepsilon$, $(p, v)$ is in the domain of $\exp$
and $\exp_p(v) = F(p, v)$. (ii) There is an open set $O \subseteq V \times V$ containing $(q, 0)$ for
every $q \in N$ such that every point of $TN \cap O$ is in the domain of $\exp$, and $\exp$ is smooth
on $TN \cap O$: near each point of $TN \cap O$ it is the restriction of a smooth map on an open set
of $V \times V$, and $(q, v) \mapsto \exp_q(v)$ is smooth on the open subset $TN \cap O$ of the
manifold $TN$. (iii) For each $q \in N$, $\exp_q$, as a map on the vector space $T_qN$, has
derivative at $0$ the inclusion $T_qN \to V$. *Book:* p. 58: $TM$ is given a $C^\infty$ structure by
the coordinates $(u^1, \dots, u^n, t^1, \dots, t^n)$; by Lemma 10.2, $(q, v) \mapsto \exp_q(v)$ is
defined and differentiable throughout a neighbourhood of $(p, 0)$ in $TM$; in the Jacobian of
$(q, v) \mapsto (q, \exp_q(v))$ at $(p, 0)$, the formula
$F_*(\partial/\partial t^j) = \partial/\partial u_2^j$ amounts to $d(\exp_p)_0 = \mathrm{id}$.
*Hidden hypotheses:* the smooth dependence in Lemma 10.2 (V7.6). *Deviation (restated):* Milnor's
tangent manifold is the embedded $TN \subseteq V \times V$. *Deviation (stronger):* one open
neighbourhood of the whole zero section.

**V7.9 (normal radius; `Morse.NormalCoord`, `Morse.IsNormalRadius`, `Morse.expToN`,
`Morse.NormalCoord.expDiffeo`).** For $q \in N$ and $\varepsilon > 0$ let
$B_\varepsilon(q) = \{v \in T_qN : \|v\| < \varepsilon\}$. $\varepsilon$ is a normal radius at $q$ if
there are open sets $O, U \subseteq V$ and maps $F$ smooth on $O$ and $G$ smooth on $U$ such that:
$B_\varepsilon(q) \subseteq O$, $B_\varepsilon(q)$ lies in the domain of $\exp_q$, and
$\exp_q = F$ on $B_\varepsilon(q)$; $\exp_q$ maps $B_\varepsilon(q)$ into $U$, with
$G(\exp_q v) = v$ for $v \in B_\varepsilon(q)$; and $G$ maps $U_q = N \cap U$ into
$B_\varepsilon(q)$, with $\exp_q(G(y)) = y$ for $y \in U_q$. Thus $\exp_q$ is a bijection of
$B_\varepsilon(q)$ onto the open subset $U_q$ of $N$, and it and its inverse are restrictions of
smooth maps on open sets of $V$. A normal radius yields a diffeomorphism in Mathlib's sense: $\exp_q$,
as a map from the vector space $T_qN$ to the manifold $N$, restricts to a `PartialDiffeomorph` of the
open $\varepsilon$-ball onto $U_q$. *Book:* p. 59, Lemma 10.3 (3): $\exp_q$ maps the open
$\varepsilon$-ball in $TM_q$ diffeomorphically onto an open set $U_q$. *Hidden hypotheses:* none.
*Deviation (restated):* the name is the exposition's; "diffeomorphically" is made precise in
Milnor's sense for subsets of Euclidean space, and Mathlib's sense follows.

**V7.10 (Lemma 10.3; `Morse.LocalSpray.chartExp`, `Morse.LocalSpray.exp_eq_chartExp`,
`Morse.LocalSpray.chartF`, `Morse.LocalSpray.jacobian`, `Morse.LocalSpray.hasFDerivAt_chartF`,
`Morse.lemma_10_3`, `Morse.lemma_10_3_geodesic`, `Morse.exists_isNormalRadius`,
`Morse.exists_expDiffeo`).** For each $p \in N$ there are an open set $O \ni p$ of $V$ and an
$\varepsilon > 0$ such that, with $W = N \cap O$: (1) for all $q_1, q_2 \in W$ there is exactly one
$v \in T_{q_1}N$ with $\|v\| < \varepsilon$ and $\exp_{q_1}(v) = q_2$; and if $\gamma$ is a geodesic
from $q_1$ (V7.7) with initial velocity $v$, $\|v\| < \varepsilon$, and $\gamma(1) = q_2$, then $v$
is this vector, so $\gamma(t) = \exp_{q_1}(tv)$ on $[0, 1]$; (2) there are an open set
$O_2 \subseteq V \times V$ containing $W \times W$ and a map $G$ smooth on $O_2$ such that
$G(q_1, q_2)$ is the vector of (1) for all $q_1, q_2 \in W$; (3) $\varepsilon$ is a normal radius
(V7.9) at every $q \in W$, and $U_q \supseteq W$ by (1). In particular every point of $N$ has a
normal radius, and $\exp_q$ restricts to a `PartialDiffeomorph` of an open ball of $T_qN$ onto an
open neighbourhood of $q$ in $N$. *Book:* p. 59, Lemma 10.3: a neighbourhood $W$ of $p$ and an
$\varepsilon > 0$ such that (1) any two points of $W$ are joined by a unique geodesic of length
$< \varepsilon$, (2) it depends smoothly on them, in that $(q_1, v) \in TM$ depends differentiably on
$(q_1, q_2)$, and (3) for $q \in W$, $\exp_q$ maps the open $\varepsilon$-ball diffeomorphically onto
an open set $U_q \supseteq W$; proved on pp. 58–59 from the nonsingular Jacobian of
$F(q, v) = (q, \exp_q v)$ at $(p, 0)$ by the "implicit function theorem". *Hidden hypotheses:* the
theorem used is the inverse function theorem; taking the neighbourhood $V'$ of $(p, 0)$ of the form
$\{(q, v) : q \in U', \|v\| < \varepsilon\}$ needs such sets to form a neighbourhood base of $(p, 0)$
in $TM$, that is a comparison between $\|v\|$ and the coordinates of $v$, uniform near $p$;
uniqueness in (1) among geodesics of length $< \varepsilon$ uses that the initial vector of such a
geodesic has norm equal to its length (V7.2). *Deviation (restated):* in (1), "unique geodesic of
length $< \varepsilon$" becomes the unique initial vector $v$, $\|v\| < \varepsilon$, the geodesic
$t \mapsto \exp_{q_1}(tv)$ on $[0, 1]$ having length $\|v\|$ (V7.15). *Proof:* Milnor's, in the
slice chart at $p$: $E(u, w) = \sigma_1(\exp(x(u), dx_u w))$, $x$ the parametrization, is given by the
flow of the chart equation of V7.3, hence smooth (V7.4), and $(u, w) \mapsto (u, E(u, w))$ has
derivative $(a, b) \mapsto (a, a + b)$ at $(u_0, 0)$ (Milnor's matrix
$\begin{pmatrix} I & I \\ 0 & I \end{pmatrix}$ has the images of $\partial/\partial u^i$ and
$\partial/\partial t^j$ as rows); the companion project's inverse function theorem
(`Milnor.ContMDiff.isLocalDiffeomorphAt_of_isInvertible_mfderiv`) gives the local inverse from which
$W$, $\varepsilon$, $G$ and the inverses in (3) are read off.

**V7.11 (piecewise smooth paths and their lengths; `Morse.pathLength`, `Morse.IsPiecewiseSmooth`,
`Morse.IsAdmissible`, `Morse.IsPiecewiseSmooth.isAdmissible`, `Morse.IsAdmissible.integral_deriv`,
`Morse.IsAdmissible.norm_sub_le_pathLength`, `Morse.IsAdmissible.pathLength_add`,
`Morse.IsAdmissible.eq_of_pathLength_eq_zero`, `Morse.pathLength_eq_of_norm_deriv`,
`Morse.IsPiecewiseSmooth.mono`, `Morse.IsPiecewiseSmooth.concat`, `Morse.pathLength_concat`,
`Morse.IsPiecewiseSmooth.reverse`, `Morse.pathLength_reverse`, `Morse.IsPiecewiseSmooth.translate`,
`Morse.pathLength_translate`).** Let $c$ be a curve in a real normed space (complete, for the
statements involving $\int c'$) and $a \le b$. The length of $c$ on $[a, b]$ is
$L(c|[a, b]) = \int_a^b \|c'(t)\|\,dt$ ($c'$ is taken to be $0$ where $c$ is not differentiable,
which for the paths below happens only on a null set). $c$ is piecewise smooth on $[a, b]$ if it is
continuous on $[a, b]$ and there is a finite set $B$ of break points such that $c$ is $C^\infty$, with
one-sided derivatives at the ends, on every $[s, t] \subseteq [a, b]$, $s < t$, with no point of $B$
in $(s, t)$. $c$ is admissible on $[a, b]$ if it is continuous on $[a, b]$, differentiable at all but
countably many points of $(a, b)$, and $\|c'\|$ is integrable on $[a, b]$. A path in $N$ is one with
$c([a, b]) \subseteq N$. Piecewise smooth paths are admissible. For admissible paths
$\int_a^b c' = c(b) - c(a)$, so $\|c(b) - c(a)\| \le L(c|[a, b])$; length is additive under
subdivision; a path of length $0$ is constant; a path with $\|c'\| = k$ wherever it is
differentiable has length $k(b - a)$. Restriction to a subinterval, concatenation of two paths
with a common endpoint, reversal $t \mapsto c(a + b - t)$ and translation of the parameter preserve
piecewise smoothness; under concatenation lengths add, and under reversal and translation they are
unchanged. *Book:* p. 67 (§11): a piecewise smooth path is a map $\omega : [0, 1] \to M$ with a
subdivision $0 = t_0 < \dots < t_k = 1$ such that each $\omega|[t_{i-1}, t_i]$ is $C^\infty$; from
Theorem 10.4 on (p. 59) such paths on intervals $[a, b]$ and their lengths
$\int\|d\omega/dt\|\,dt$ are used without comment. *Hidden hypotheses:* integrability of
$\|d\omega/dt\|$; additivity and invariance of length under subdivision, concatenation, reversal and
translation. *Deviation (restated):* the subdivision is given as a finite set of break points.
*Deviation (stronger):* the lower bounds for lengths (V7.13–V7.16) are proved for admissible paths,
a class that contains the piecewise smooth paths and is closed under restriction.

**V7.12 (Lemma 10.5, the Gauss lemma; `Morse.NormalCoord.norm_fderiv_F_apply`,
`Morse.NormalCoord.inner_fderiv_F`, `Morse.NormalCoord.fderiv_G_fderiv_F`,
`Morse.NormalCoord.injective_fderiv_F`, `Morse.gauss_lemma`, `Morse.gauss_lemma_orthogonal`).** Let
$\varepsilon$ be a normal radius at $q \in N$ and regard $\exp_q$ as a map on the vector space
$T_qN$. For $w, x \in T_qN$ with $\|w\| < \varepsilon$,
$$\langle d(\exp_q)_w(w),\ d(\exp_q)_w(x)\rangle = \langle w, x\rangle;$$
in particular, if $x \perp w$, the radial velocity $d(\exp_q)_w(w)$ is orthogonal to
$d(\exp_q)_w(x)$. Moreover $d(\exp_q)_w$ is injective on $T_qN$, and
$\|d(\exp_q)_{rw}(w)\| = \|w\|$ for $0 \le r \le 1$ (these two are stated for the smooth extension
$F$ of V7.9, whose derivative on $T_qN$ is that of $\exp_q$). *Book:* p. 60, Lemma 10.5: in $U_q$
the geodesics through $q$ are the orthogonal trajectories of the hypersurfaces
$\{\exp_q(v) : \|v\| = \text{constant}\}$; proof with the surface $f(r, t) = \exp_q(rv(t))$,
$\|v(t)\| = 1$. *Hidden hypotheses:* that these sets are hypersurfaces whose tangent vectors are the
$\frac{d}{dt}\exp_q(r_0v(t))$ uses that $\exp_q$ is a diffeomorphism on the ball (V7.9).
*Deviation (stronger):* the identity holds for every $x \in T_qN$, not only for $x \perp w$, and
needs no curve $v(t)$; Milnor's orthogonality of trajectories is its case $x \perp w$, the vectors
$x \perp w$ forming the tangent space at $w$ of the sphere $\{\|v\| = \|w\|\}$. *Proof:* Milnor's,
with $f(r, s) = \exp_q(r(w + sx))$ and $g(r) = \langle\partial f/\partial r, \partial f/\partial
s\rangle$ at $s = 0$: in $V$, $\langle\partial^2 f/\partial r^2, \partial f/\partial s\rangle = 0$
because the acceleration of the radial geodesic is normal and $\partial f/\partial s$ is tangent,
and $\langle\partial f/\partial r, \partial^2 f/\partial s\,\partial r\rangle =
\frac12\frac{\partial}{\partial s}\|w + sx\|^2 = \langle w, x\rangle$ by constant speed, the
symmetry of second derivatives in $V$ replacing Lemma 8.7; so $g' = \langle w, x\rangle$, $g(0) = 0$,
and $g(1) = \langle w, x\rangle$ by the mean value theorem.

**V7.13 (Lemma 10.6; `Morse.NormalCoord.hasDerivAt_radius`,
`Morse.NormalCoord.radius_sub_le_pathLength`, `Morse.NormalCoord.direction_eq_of_pathLength_eq`).**
Let $\varepsilon$ be a normal radius at $q$, with $U_q$ and $G = \exp_q^{-1}$ as in V7.9. Let $c$ be
admissible on $[a, b]$ with $c(t) \in U_q$ and $c(t) \neq q$ for $t \in [a, b]$, and write
$c(t) = \exp_q(r(t)v(t))$ with $r(t) = \|G(c(t))\| \in (0, \varepsilon)$ and $v(t) = G(c(t))/r(t)$, a
unit vector. Then $L(c|[a, b]) \ge r(b) - r(a)$, and if equality holds, $v$ is constant on
$[a, b]$. Pointwise: at each $t \in (a, b)$ where $c$ is differentiable, $r$ is differentiable with
$|r'(t)| \le \|c'(t)\|$, and $r'(t) = \|c'(t)\|$ implies $v'(t) = 0$. *Book:* p. 60, Lemma 10.6, for
a piecewise smooth $\omega : [a, b] \to U_q - \{q\}$: $\int_a^b\|d\omega/dt\|\,dt \ge |r(b) - r(a)|$,
with equality only if $r$ is monotone and $v$ constant; the proof (p. 61) splits
$d\omega/dt = \frac{\partial f}{\partial r}r'(t) + \frac{\partial f}{\partial t}$ into orthogonal
parts. *Hidden hypotheses:* the step from $\partial f/\partial t = 0$ to $dv/dt = 0$ needs
$d(\exp_q)_{rv}$ injective (V7.12) and $r > 0$. *Deviation (narrower):* the bound is one-sided,
$r(b) - r(a)$ rather than $|r(b) - r(a)|$, which is the case Theorem 10.4 uses, and the equality
clause gives only that $v$ is constant; the monotone parametrization appears in V7.16.
*Deviation (stronger):* admissible paths. *Proof:* without the orthogonal splitting: with
$w = G \circ c$, the Gauss lemma gives $\langle d(\exp_q)_w(w), c'\rangle = \langle w, w'\rangle =
rr'$, and the Cauchy–Schwarz inequality with $\|d(\exp_q)_w(w)\| = \|w\|$ gives $|r'| \le \|c'\|$,
equality forcing $w'$ to be a multiple of $w$; the integrated forms use the fundamental theorem of
calculus off a countable set.

**V7.14 (paths leaving a normal ball; `Morse.NormalCoord.ballSet`,
`Morse.NormalCoord.closedBallSet`, `Morse.NormalCoord.isCompact_closedBallSet`,
`Morse.NormalCoord.mem_closedBallSet`, `Morse.NormalCoord.exists_crossing`).** Let $\varepsilon$ be a
normal radius at $q$ and $0 < s < \varepsilon$. The open normal ball
$\exp_q\{v \in T_qN : \|v\| < s\}$ is the intersection of $N$ with an open set of $V$; the closed
normal ball $\exp_q\{v \in T_qN : \|v\| \le s\}$ is compact, hence closed in $V$, and consists of the
points $y \in U_q$ with $\|G(y)\| \le s$. If $c$ is an admissible path in $N$ on $[a, b]$ with
$c(a) = q$ and $c(b)$ outside the open normal ball of radius $s$, there are $a \le t_1 < t_2 \le b$
with $c(t_1) = q$, $c(t) \in U_q \setminus \{q\}$ for $t_1 < t \le t_2$, $c(t)$ in the open normal
ball for $t_1 \le t < t_2$, $\|G(c(t_2))\| = s$, and $L(c|[t_1, t_2]) \ge s$. ($t_2$ is the first
exit from the open ball and $t_1$ the last visit of $q$ before it; after $t_2$ the path may leave
$U_q$.) *Book:* p. 61, proof of Theorem 10.4: for every $\delta > 0$ a path from $q$ to a point of
the shell of radius $r$ contains a segment that joins the shells of radii $\delta$ and $r$ and lies
between them, of length $\ge r - \delta$; then $\delta \to 0$. *Hidden hypotheses:* a
competing path may leave $U_q$ and come back; the segment exists because closed normal balls are
closed in $M$ (compact in a Hausdorff space), which puts the first exit point on the shell.
*Deviation (restated):* the shells of radius $\delta \to 0$ are replaced by the last visit of $q$,
the limit being taken inside the proof; this is the exposition's Lemma C for paths starting at $q$.

**V7.15 (Theorem 10.4; `Morse.NormalCoord.radial`, `Morse.NormalCoord.pathLength_exp_smul`,
`Morse.NormalCoord.norm_le_pathLength`, `Morse.theorem_10_4`).** (i) If $\varepsilon$ is a normal
radius at $q$ and $v \in T_qN$, $\|v\| < \varepsilon$, then $t \mapsto \exp_q(tv)$ is a geodesic near
$[0, 1]$ with initial velocity $v$ and length $\|v\|$ on $[0, 1]$, and every admissible path in $N$,
on any $[a, b]$, from $q$ to $\exp_q(v)$ has length $\ge \|v\|$, whether or not it stays in $U_q$.
(ii) For each $p \in N$ there are an open set $O \ni p$ of $V$ and an $\varepsilon > 0$ such that for
any $q_1, q_2 \in N \cap O$ there is $v \in T_{q_1}N$ with $\|v\| < \varepsilon$ and
$\exp_{q_1}(v) = q_2$, the geodesic $\gamma(t) = \exp_{q_1}(tv)$, $0 \le t \le 1$, has length $\|v\|$,
and every piecewise smooth path $c$ in $N$ on any $[a, b]$ from $q_1$ to $q_2$ satisfies
$L(c|[a, b]) \ge \|v\|$, with equality only if $c([a, b]) = \gamma([0, 1])$. *Book:* p. 59, Theorem
10.4: for $W$, $\varepsilon$ as in Lemma 10.3, $\gamma : [0, 1] \to M$ the geodesic of length
$< \varepsilon$ joining two points of $W$, and any other piecewise smooth path
$\omega : [0, 1] \to M$ joining them, $\int_0^1\|d\gamma/dt\|\,dt \le \int_0^1\|d\omega/dt\|\,dt$,
with equality only if the point sets $\omega([0, 1])$ and $\gamma([0, 1])$ coincide; proof on p. 61.
*Hidden hypotheses:* the shell-crossing step (V7.14). *Deviation (stronger):* paths on any parameter
interval, and in (i) admissible paths. *Proof:* (ii) takes $O$ and $\varepsilon$ from Lemma 10.3
(V7.10), so $v$ is the vector of its item (1) and $\varepsilon$ a normal radius at $q_1$; the
inequality is (i), which is V7.14 with $s = \|v\|$; the equality clause is V7.16 (for $v = 0$ the
path has length $0$ and is constant).

**V7.16 (the equality case of Theorem 10.4, sharp form; `Morse.NormalCoord.eq_exp_of_pathLength_eq`,
`Morse.IsAdmissible.continuousOn_pathLength`, `Morse.IsAdmissible.monotoneOn_pathLength`,
`Morse.NormalCoord.image_eq_of_pathLength_eq`).** Let $\varepsilon$ be a normal radius at $q$,
$v \in T_qN$ with $0 < \|v\| < \varepsilon$, and $c$ an admissible path in $N$ on $[a, b]$ from $q$ to
$\exp_q(v)$ of length exactly $\|v\|$. Then
$$c(t) = \exp_q(\rho(t)v),\qquad \rho(t) = \frac{L(c|[a, t])}{\|v\|},\qquad a \le t \le b,$$
where $\rho$ is continuous and nondecreasing with $\rho(a) = 0$ and $\rho(b) = 1$: $c = \gamma \circ
\rho$ is a monotone reparametrization of the geodesic $\gamma(t) = \exp_q(tv)$, $0 \le t \le 1$.
Milnor's conclusion $c([a, b]) = \gamma([0, 1])$ follows. *Book:* p. 59, the equality clause of
Theorem 10.4 (the point sets coincide); p. 61: if the images differ, a strict inequality is "easily"
obtained. *Hidden hypotheses:* the equality analysis, left to the reader. *Deviation (stronger):* a
monotone reparametrization instead of equal images. Equal images are too weak for Corollary 10.7
(V7.17), whose proof needs this form. *Proof:* with $t_1$, $t_2$ from V7.14, the lengths on
$[a, t_1]$ and $[t_2, b]$ vanish, so $c$ is constant there; for $t_1 < t \le t_2$, (i) of V7.15 on
$[t_1, t]$ and Lemma 10.6 on $[t, t_2]$ force $L(c|[t_1, t]) = r(t)$ and equality in Lemma 10.6 on
$[t, t_2]$, so the direction of $G(c(t))$ is that of $v$.

**V7.17 (Corollary 10.7; `Morse.isGeodesicOn_of_locally`, `Morse.minimal_segment`,
`Morse.corollary_10_7`, `Morse.corollary_10_7_extend`).** Let $c$ be a piecewise smooth path in $N$
on $[0, \ell]$, parametrized by arc length ($\|c'(t)\| = 1$ at every $t \in (0, \ell)$ where $c$ is
differentiable), whose length is at most that of every piecewise smooth path in $N$, on any
parameter interval, from $c(0)$ to $c(\ell)$. Then $c$ is a geodesic on $(0, \ell)$, in particular
smooth there, also at its break points; and $c$ agrees on $[0, \ell]$ with a geodesic defined on an
open interval $(-\delta, \ell + \delta)$. On the way: being a geodesic is a local property, and if $c$
maps $[\alpha, \beta]$ into a set $W$ as in Lemma 10.3 (V7.10), it agrees on $[\alpha, \beta]$ with a
geodesic defined on an open set containing $[\alpha, \beta]$. *Book:* p. 61, Corollary 10.7, for a
path $\omega : [0, \ell] \to M$ parametrized by arc length whose length is at most that of any other
path from $\omega(0)$ to $\omega(\ell)$; the proof applies Theorem 10.4 to each segment of $\omega$
that lies in a set $W$ of Lemma 10.3 and has length $< \varepsilon$. *Hidden hypotheses:* the
equality clause of Theorem 10.4 as stated (equal images) does not make such a segment a geodesic, a
path running along $\gamma$ at varying speed having the same image; the proof needs V7.16 together
with the unit speed, which makes $\rho$ affine. Also needed: each segment is minimal between its
endpoints (replacing it by the geodesic of Lemma 10.3 gives a competitor, by concatenation, V7.11),
the segments must contain the break points in their interiors, and being a geodesic is local.
*Deviation (stronger):* the extension to an open interval containing $[0, \ell]$.

**V7.18 (the distance; `Morse.pathLengths`, `Morse.riemDist`, `Morse.riemDist_le_pathLength`,
`Morse.riemDist_self`, `Morse.riemDist_eq_top_of_notMem`, `Morse.riemDist_comm`,
`Morse.riemDist_triangle`, `Morse.NormalCoord.ofReal_le_riemDist`, `Morse.eq_of_riemDist_eq_zero`).**
For $p, q \in V$, $\rho(p, q) \in [0, \infty]$ is the infimum of the lengths of the piecewise smooth
paths $c$ in $N$, on any $[a, b]$, with $c(a) = p$ and $c(b) = q$ ($\infty$ if there is none, as when
$q \notin N$). Then $\rho(p, q) \le L(c|[a, b])$ for every such path; $\rho(p, p) = 0$ for $p \in N$;
$\rho(p, q) = \rho(q, p)$; $\rho(p, r) \le \rho(p, q) + \rho(q, r)$; if $\varepsilon$ is a normal
radius at $p$ and $0 < s < \varepsilon$, every point outside the open normal ball of radius $s$
about $p$ is at distance $\ge s$ from $p$; and for $p, q \in N$, $\rho(p, q) = 0$ implies $p = q$. So
$\rho$ is a metric on $N$ with values in $[0, \infty]$. *Book:* p. 62: $\rho(p, q)$ is the greatest
lower bound of the arc-lengths of the piecewise smooth paths joining $p$ and $q$, and this "clearly"
makes $M$ a metric space. *Hidden hypotheses:* finiteness needs $M$ connected (Milnor's standing
assumption, p. 55); positivity is not clear, since a path from $p$ to $q$ may leave every normal
neighbourhood of $p$: the lower bound needs the shell-crossing lemma (V7.14). *Deviation
(restated):* $\rho$ is $\infty$ between points that no path joins, and $N$ need not be connected.

**V7.19 (metric balls and the topology; `Morse.NormalCoord.riemDist_exp_le`,
`Morse.NormalCoord.riemDist_exp`, `Morse.NormalCoord.riemDist_lt_iff`,
`Morse.hasBasis_nhdsWithin_riemDist`).** Let $\varepsilon$ be a normal radius at $p \in N$. For
$v \in T_pN$ with $\|v\| < \varepsilon$, $\rho(p, \exp_p v) = \|v\|$. For $0 < r \le \varepsilon$,
$\rho(p, y) < r$ iff $y$ lies in the normal ball $\exp_p\{v \in T_pN : \|v\| < r\}$. Consequently,
for every $p \in N$, the metric balls $\{y : \rho(p, y) < r\}$, $r > 0$, form a basis of the
neighbourhoods of $p$ in $N$ (with the topology of a subspace of $V$): the topology defined by $\rho$
is the topology of $N$. *Book:* p. 62: compatibility of the metric with the topology of $M$ follows
"easily" from Theorem 10.4. *Hidden hypotheses:* that small metric balls are normal balls (V7.14
again), and that normal balls of small radius lie in any given neighbourhood of $p$ (continuity of
$\exp_p$ at $0$). *Deviation (restated):* compatibility is stated as the neighbourhood-basis property
at each point; the metric-space structure on $N$ that it yields is V7.21.

**V7.20 (Corollary 10.8; `Morse.IsShortJoin`, `Morse.exists_isShortJoin`, `Morse.corollary_10_8`).**
Let $K \subseteq N$ be compact. There is $\delta > 0$ such that for all $y, z \in K$ with
$\rho(y, z) < \delta$: there is $v \in T_yN$ with $\|v\| < \delta$ and $\exp_y(v) = z$, the initial
vector of the geodesic $t \mapsto \exp_y(tv)$, $0 \le t \le 1$, of length $\|v\|$, from $y$ to $z$;
this geodesic is minimal, $\rho(y, z) = \|v\|$; $v$ is the only $w \in T_yN$ with $\|w\| < \delta$ and
$\exp_y(w) = z$; and $v$ depends smoothly on the endpoints: there are an open set $O_2 \ni (y, z)$
of $V \times V$ and a map $G$ smooth on $O_2$ with $G(y, z) = v$ such that for all $y', z' \in N$ with
$(y', z') \in O_2$ and $\rho(y', z') < \delta$, $G(y', z') \in T_{y'}N$, $\|G(y', z')\| < \delta$ and
$\exp_{y'}(G(y', z')) = z'$. *Book:* p. 62, Corollary 10.8: any two points of $K$ at distance less
than $\delta$ are joined by a unique geodesic of length less than $\delta$, which is minimal and
depends differentiably on its endpoints; proof: cover $K$ by sets $W$ as in Lemma 10.3 and take
$\delta$ so small that any two points of $K$ at distance $< \delta$ lie in a common $W$. *Hidden
hypotheses:* the choice of $\delta$ is a Lebesgue-number argument with a finite subcover; uniqueness
among geodesics of length $< \delta$ needs $\delta$ at most the $\varepsilon$ of each set of the
cover, else Lemma 10.3 (1) does not apply; minimality is Theorem 10.4, through
$\rho(y, z) = \|v\|$ (V7.19). *Deviation (restated):* uniqueness is stated for initial vectors (a
geodesic from $y$ with initial velocity $w$, defined near $[0, 1]$ and ending at $z$, has length
$\|w\|$ and $\exp_y(w) = z$, by V7.2 and V7.7); "depends differentiably" means that near each pair
the initial vector is the restriction of a smooth map on an open set of $V \times V$, on the pairs at
distance $< \delta$. *Proof:* each $x \in K$ is the centre of a normal ball of radius $s_x$, with
$2s_x$ at most the $\varepsilon$ of Lemma 10.3 at $x$ and the radius of a metric ball about $x$ inside
its set $W$; finitely many of these balls cover $K$, $\delta$ is the least of their $s_x$, and the
triangle inequality puts $y$ and $z$ in one $W$.

**V7.21 (continuity and finiteness of $\rho$; the metric space $(N, \rho)$;
`Morse.ofReal_norm_sub_le_riemDist`, `Morse.eventually_riemDist_lt`, `Morse.continuousOn_riemDist`,
`Morse.continuousOn_riemDist_left`, `Morse.continuous_riemDist`, `Morse.riemDist_ne_top`,
`Morse.riemEMetricSpace`, `Morse.riemMetricSpace`, `Morse.riemMetricSpace_dist`,
`Morse.riemMetricSpace_topology`).** For all $p, q \in V$, $\|q - p\| \le \rho(p, q)$. For
$p \in N$ and every $r > 0$, all points of $N$ near $p$ are at distance $< r$ from $p$. The function
$(x, y) \mapsto \rho(x, y)$, with values in $[0, \infty]$, is continuous on $N \times N$ (with the
topology of a subspace of $V \times V$); in particular $y \mapsto \rho(y, q)$ is continuous on $N$
for every $q$. If $N$ is connected, $\rho(p, q) < \infty$ for all $p, q \in N$. Hence $\rho$ makes
$N$ an extended metric space whose topology is the topology of $N$ (by V7.19), and, for connected
$N$, a metric space with distance $\rho$ and the topology of $N$.
*Book:* p. 62: $\rho$ "clearly" makes $M$ a metric space, compatible with its topology by Theorem
10.4; finiteness rests on the standing assumption that $M$ is connected (p. 55); the continuity of
$\rho$ is used without comment in the proof of Theorem 10.9 (p. 63: a point of the compact shell $S$
at minimum distance from $q$, and the equality at the supremum $t_0$ "by continuity"). *Hidden
hypotheses:* connectedness, for finiteness; the continuity of $\rho$, which the book never states.
*Deviation (restated):* the two metric spaces are structures on $N$ given by name, not instances,
since $N$, a subset of $V$, already carries the metric of $V$. "Connected" is preconnected in the
formal statements here and below, which also admits $N = \emptyset$. *Proof:* the points at finite
distance from $p$ form a subset of $N$ that is open and closed, metric balls being neighbourhoods
(V7.19); continuity follows from $|\rho(x, y) - \rho(x', y')| \le \rho(x, x') + \rho(y, y')$ and
V7.19.

**V7.22 (metric and geodesic completeness; `Morse.IsRiemComplete`,
`Morse.isRiemComplete_iff_completeSpace`, `Morse.IsRiemBounded`, `Morse.IsGeodesicallyComplete`,
`Morse.isGeodesicOn_univ_exp_smul`, `Morse.isGeodesicallyComplete_iff`).** $(N, \rho)$ is
*complete* if every sequence of points $x_n \in N$ that is Cauchy for $\rho$ (for every
$\varepsilon > 0$, $\rho(x_m, x_n) < \varepsilon$ for all large $m, n$) converges for $\rho$ to some
$y \in N$, i.e. $\rho(x_n, y) \to 0$; for connected $N$ this is the completeness of the metric space
of V7.21. A set $X \subseteq V$ is *bounded* if $\rho(x, y) \le d$ for all $x, y \in X$ and some real
$d$ (a nonempty bounded set lies in $N$, since $\rho(x, x) = \infty$ for $x \notin N$). $N$ is
*geodesically complete* if $\exp_q(v)$ is defined (V7.7) for every $q \in N$ and every
$v \in T_qN$. If $\exp_q$ is defined on all of $T_qN$, then $t \mapsto \exp_q(tv)$ is a geodesic on
$\mathbb R$ for every $v \in T_qN$; and $N$ is geodesically complete iff every geodesic on an open
interval is the restriction of a geodesic on $\mathbb R$. *Book:* p. 58: the definition, "clearly
equivalent" to the requirement that every geodesic segment $\gamma_0 : [a, b] \to M$ extends to a
geodesic $\gamma : \mathbb R \to M$, the form recalled on p. 62; p. 64: bounded subsets, and $M$
complete as a metric space (every Cauchy sequence converges). *Hidden hypotheses:* the equivalence
glues geodesics, which needs their uniqueness in the large (V7.5). *Deviation (restated):* Milnor's
segments on closed intervals are replaced by geodesics on open intervals, as in V7.7.

**V7.23 (the geodesic flow, and the continuity of $\exp$; `Morse.IsGeodesicOn.exp_smul_eq`,
`Morse.geoFlow`, `Morse.exists_localFlow_exp`, `Morse.isGeodesicOn_exp_smul_union`,
`Morse.eventually_mem_expDom_and_continuousWithinAt_exp`, `Morse.continuousOn_exp`).** (i) If
$\gamma$ is a geodesic on an open interval containing $0$, then $\gamma(t) = \exp_{\gamma(0)}(t\,
\gamma'(0))$ for every $t$ in the interval. So the curves $t \mapsto \exp_y(tw)$ are all the
geodesics, and the geodesic flow is read off from $\exp$: it sends $(y, w)$ and $t$ to the position
and velocity at time $t$ of $s \mapsto \exp_y(sw)$. (ii) For $x_0 \in N$ and $R > 0$ there are an
open set $U \ni x_0$ of $V$, a time $\tau > 0$ and a map $\Phi$, continuous on
$U \times \{w : \|w\| < R\} \times (-\tau, \tau)$, such that for $y \in N \cap U$ and $w \in T_yN$
with $\|w\| < R$ the curve $t \mapsto \exp_y(tw)$ is a geodesic on $(-\tau, \tau)$ with velocity $w$
at $0$, whose position and velocity at time $t$ are $\Phi(y, w, t)$. (iii) If $t \mapsto \exp_y(tw)$
is a geodesic on an open interval $I \ni 0$, $s \in I$, $(y', w')$ is its position and velocity at
time $s$, and $t \mapsto \exp_{y'}(tw')$ is a geodesic on an open interval $J \ni 0$, then
$t \mapsto \exp_y(tw)$ is a geodesic on $I \cup (s + J)$, and its position and velocity at time
$s + t$, $t \in J$, are those of $t \mapsto \exp_{y'}(tw')$ at time $t$. (iv) The domain of $\exp$
is open in $TN$ (V7.8) and $\exp$ is continuous on it: if $(p, v)$ is in the domain, so is every
$(q, w) \in TN$ near $(p, v)$, and $\exp$, as a function on $TN$, is continuous at $(p, v)$. In
particular, if $\exp_p$ is defined on all of $T_pN$, it is continuous there. *Book:* p. 57,
$\gamma(t) = \exp_q(tv)$; the extension of geodesics (pp. 58, 62); Corollary 10.10 (p. 64) uses
that $\exp_p$ maps the disk of radius $d$ in $TM_p$ onto a compact set, which needs (iv). *Hidden
hypotheses:* (iv), the global dependence of geodesics on their initial data: Lemma 10.2 concerns
small vectors only. *Deviation (narrower):* continuity of $\exp$ on its domain, not the smoothness
asserted in the exposition's Lemma B; maximal geodesics are not constructed, geodesics being glued
by (iii) instead. *Proof:* (ii) is Lemma 10.2 with smooth dependence (V7.6), rescaled by
homogeneity; for (iv) the compact arc $\gamma([0, 1])$ is covered by finitely many sets $U$ of (ii)
with a uniform time $2\tau_0$, and the geodesics with initial data near $(p, v)$ are continued by
(iii) in steps of length $\tau_0$, their position and velocity being at each step a composition of
continuous maps.

**V7.24 (minimal geodesics; `Morse.IsMinimalGeodesic`, `Morse.exp_mem_of_mem_expDom`,
`Morse.isMinimalGeodesic_exp_smul`).** A curve $\gamma$ is a minimal geodesic on $[a, b]$,
$a \le b$, if it is a geodesic on some open set containing $[a, b]$ and $L(\gamma|[a, b]) \le
L(c|[a', b'])$ for every piecewise smooth path $c$ in $N$, on any $[a', b']$, with $c(a') =
\gamma(a)$ and $c(b') = \gamma(b)$. Where $\exp_q(v)$ is defined, it lies in $N$. If $v \in T_pN$,
$t \mapsto \exp_p(tv)$ is a geodesic on $\mathbb R$ and $\rho(p, \exp_p v) = \|v\|$, then
$t \mapsto \exp_p(tv)$ is a minimal geodesic on $[0, 1]$, of length $\|v\|$. *Book:* pp. 61–62: a
geodesic $\gamma : [a, b] \to M$ is minimal if its length is at most that of any other piecewise
smooth path joining its endpoints. *Hidden hypotheses:* none. *Deviation (restated):* a geodesic on
an open set containing $[a, b]$ in place of one on $[a, b]$, as in V7.7.

**V7.25 (the two steps of Milnor's proof of Theorem 10.9; `Morse.NormalCoord.exists_riemDist_eq_add`,
`Morse.broken_geodesic_eq`).** (i) Let $\varepsilon$ be a normal radius at $p \in N$ (V7.9),
$0 < \delta < \varepsilon$, and $q$ with $\delta < \rho(p, q) < \infty$. There is $w \in T_pN$ with
$\|w\| = \delta$ and $\rho(p, q) = \delta + \rho(\exp_p w, q)$: the point $p_0 = \exp_p w$ of the
sphere of radius $\delta$ about $p$ is a point of that sphere nearest to $q$. (ii) Let $\gamma$ be a
geodesic on $\mathbb R$ with $\|\gamma'(0)\| = 1$ (so of unit speed), $0 < t_0 < t_1$, and $\sigma$
a geodesic on an open interval containing $[t_0, t_1]$ with $\|\sigma'(t_0)\| = 1$ and $\sigma(t_0)
= \gamma(t_0)$. If $\rho(\gamma(0), \sigma(t_1)) \ge t_1$, that is, if the broken path ($\gamma$ on
$[0, t_0]$, then $\sigma$), of length $t_1$, is minimal, then $\sigma(t_1) = \gamma(t_1)$. *Book:*
p. 63: since every path from $p$ to $q$ passes through the shell $S$, $\rho(p, q) = \min_{s \in S}
(\rho(p, s) + \rho(s, q)) = \delta + \rho(p_0, q)$; pp. 63–64: the broken geodesic has minimal
length, so it is an unbroken geodesic by Corollary 10.7, "and hence coincides with $\gamma$".
*Hidden hypotheses:* in (i), $\delta < \rho(p, q)$, not only $\delta < \varepsilon$ (otherwise $q$
lies inside the shell and paths from $p$ to $q$ need not meet it); that every path crosses the shell
is V7.14; the minimum exists because the shell is compact and nonempty and $\rho(\cdot, q)$ is
continuous (V7.21). In (ii), unit speed on both pieces, for Corollary 10.7 (V7.17), and the
uniqueness of geodesics in the large (V7.5) from a time before the break, carried to $t_1$ by
continuity.

**V7.26 (Theorem 10.9, Hopf–Rinow; `Morse.theorem_10_9`, `Morse.theorem_10_9'`).** (i) Let
$p \in N$ be such that $\exp_p$ is defined on all of $T_pN$. Every $q \in N$ with $\rho(p, q) <
\infty$ is $\exp_p(v)$ for some $v \in T_pN$ with $\|v\| = \rho(p, q)$, and $t \mapsto \exp_p(tv)$
is a minimal geodesic on $[0, 1]$ (V7.24) from $p$ to $q$. (ii) If $N$ is connected and
geodesically complete, any two points $p, q \in N$ are joined by a minimal geodesic $\gamma$ on
$[0, 1]$, $\gamma(0) = p$, $\gamma(1) = q$, whose length is $\rho(p, q)$. *Book:* p. 62, Theorem
10.9: if $M$ is geodesically complete, any two points can be joined by a minimal geodesic; proof
pp. 62–64, with Diagram 10. *Hidden hypotheses:* those of V7.25, and $\delta' < r - t_0$ in the
inductive step (otherwise the new time $t_0 + \delta'$ overshoots $r = \rho(p, q)$); the supremum
argument is a continuous induction on the set of $t \in [\delta, r]$ with $\rho(\gamma(t), q) = r -
t$, closed by the continuity of $\rho$ (V7.21); connectedness, for $\rho(p, q) < \infty$.
*Deviation (stronger):* (i) uses completeness only at $p$, as the exposition remarks after the
proof. *Proof:* Milnor's, with V7.25 (i) at $p$ and at $\gamma(t_0)$, and V7.25 (ii) for the broken
geodesic.

**V7.27 (Corollary 10.10; `Morse.isCompact_closure_of_isRiemBounded`,
`Morse.isRiemComplete_of_forall_isCompact_closure`, `Morse.corollary_10_10`).** (i) If $N$ is
connected and $\exp_p$ is defined on all of $T_pN$ for some $p \in N$, every bounded set
$X \subseteq V$ (V7.22) has compact closure, contained in $N$. (ii) If every bounded set has compact
closure contained in $N$, then $(N, \rho)$ is complete. (iii) Hence, if $N$ is connected and
geodesically complete, every bounded set has compact closure in $N$, and $(N, \rho)$ is complete.
*Book:* p. 64, Corollary 10.10: if $M$ is geodesically complete, every bounded subset of $M$ has
compact closure; consequently $M$ is complete as a metric space; proof: for $X$ of diameter $d$ and
$p \in X$, $\exp_p$ maps the disk of radius $d$ in $TM_p$ onto a compact set which contains $X$, by
Theorem 10.9. *Hidden hypotheses:* the continuity of $\exp_p$ on the whole disk (V7.23 (iv));
connectedness, so that distances are finite and Theorem 10.9 applies to all of $X$; for
completeness, that a Cauchy sequence is bounded and converges when a subsequence does. *Deviation
(stronger):* (i) needs completeness at one point only. The closure is taken in $V$; as it lies in
$N$, it is also the closure in $N$.

**V7.28 (the converse of Corollary 10.10; `Morse.isGeodesicallyComplete_of_isRiemComplete`).** If
$(N, \rho)$ is complete, then $N$ is geodesically complete. *Book:* p. 64: conversely, if $M$ is
complete as a metric space, it is "not difficult, using Lemma 10.3" to prove that $M$ is
geodesically complete; the details are left to Hopf and Rinow. *Hidden hypotheses:* none;
connectedness is not needed. *Deviation (not in the book):* the proof, the exposition's, which uses
the uniform local existence of Lemma 10.2 (V7.23 (ii)) rather than Lemma 10.3. *Proof:* if the
geodesic $\gamma(t) = \exp_q(tv)$ existed only up to a time $T_0$, then $\rho(\gamma(t), \gamma(t'))
\le \|v\|\,|t - t'|$ would make $\gamma(t_n)$, $t_n \uparrow T_0$, a Cauchy sequence; it converges
to some $x \in N$, near which all geodesics of speed $\|v\|$ exist for a uniform time, so $\gamma$
continues past $T_0$ (V7.23 (iii)).

**V7.29 (the Hopf–Rinow theorem; `Morse.hopf_rinow`, `Morse.hopf_rinow_of_isRiemComplete`,
`Morse.isCompact_of_isClosed_of_isRiemBounded`).** For a connected nonempty $N$ the following are
equivalent: (1) $(N, \rho)$ is complete; (2) $N$ is geodesically complete; (3) $\exp_p$ is defined
on all of $T_pN$ for some $p \in N$; (4) every bounded set has compact closure, contained in $N$. If
$N$ is connected and $(N, \rho)$ is complete, then $N$ is geodesically complete, every geodesic on
an open interval is the restriction of a geodesic on $\mathbb R$, any two points of $N$ are joined
by a minimal geodesic on $[0, 1]$ whose length is their distance, and every bounded subset of $N$
that is closed in $N$ is compact (which follows from (4) alone). *Book:* p. 64: after Corollary
10.10 and its converse, geodesic and metric completeness are no longer distinguished, and $M$ is
called a complete Riemannian manifold. *Hidden hypotheses:* connectedness. *Deviation (stronger):*
condition (3), the exposition's remark that completeness at one point suffices, and the compactness
of closed bounded sets are not in the book. *Proof:* (2) ⇒ (3) as $N \ne \emptyset$, (3) ⇒ (4) is
V7.27 (i), (4) ⇒ (1) is V7.27 (ii), (1) ⇒ (2) is V7.28; the second statement adds V7.22 and V7.26.

**V7.30 (closed and compact submanifolds; the sphere; `Morse.tendsto_riemDist_of_tendsto`,
`Morse.isRiemComplete_of_isClosed`, `Morse.hopf_rinow_of_isClosed`, `Morse.hopf_rinow_of_isCompact`,
`Morse.sphere_hopf_rinow`).** Convergence in $N$ implies convergence for $\rho$. If $N$ is closed in
$V$, then $(N, \rho)$ is complete. Hence a connected $N$ that is closed in $V$, in particular a
connected compact one, has all the properties listed in the second statement of V7.29. The unit
sphere $S^n \subseteq \mathbb R^{n+1}$, $n \ge 1$ (the companion project's slice submanifold
`Milnor.Sphere.sphSub`), is geodesically complete, and any two of its points are joined by a minimal
geodesic on $[0, 1]$ whose length is their distance. *Book:* not stated; p. 65 shows that the
geodesics of $S^n$ are the great circles and discusses which arcs are minimal; the exposition
(Chapter 7, §5) notes that compact Riemannian manifolds are complete. *Hidden hypotheses:* none.
*Deviation (not in the book):* in the embedded setting this is the source of complete manifolds,
among them compact matrix groups. The great circles are not identified as the geodesics of $S^n$.
*Proof:* a $\rho$-Cauchy sequence is Cauchy in $V$, by $\|x - y\| \le \rho(x, y)$ (V7.21), so it
converges in $V$; its limit lies in the closed set $N$, and convergence in $N$ gives convergence for
$\rho$.

### What is not verified in this chapter

- **Maximal geodesics** (the exposition's Lemma B): the domain of $\exp$ is shown to be open in $TN$
  and $\exp$ continuous on it (V7.23), which is all that Corollary 10.10 needs; the maximal geodesic
  through each point is not formalized, geodesics being glued instead. The smoothness of $\exp$ on
  its whole domain, not only near the zero section (V7.8), is proved in Chapter 11 (V11.1:
  `Morse.exists_contDiffOn_exp`, `Morse.contMDiffOn_exp_expDom`), and the extension of a geodesic
  on $[0, 1]$ to an open interval, which makes Milnor's domain of $\exp$ equal to the formal one,
  in Chapters 9 and 11 (V7.7).
- **The remark after Lemma 10.3** (p. 59): $W$ can be chosen so that the geodesic joining any two of
  its points lies in $W$ (after J. H. C. Whitehead). Not formalized in this chapter; it is proved in
  Chapter 10, in the form the modified proof of Theorem 17.1 needs (V10.17: `Morse.IsGoodBall`,
  `Morse.exists_isGoodBall_ball`): the part of $N$ in a small ball of the ambient space contains the
  short geodesic joining any two of its points.
- **The remarks on minimal geodesics** (p. 62): sufficiently small segments of a geodesic are
  minimal, long geodesics need not be, and minimal geodesics need not be unique. Minimal geodesics
  are defined (V7.24) and produced by Theorem 10.9 (V7.26), but these remarks are not formalized.
- **The examples** of pp. 65–66 (straight lines in $\mathbb R^n$ and inscribed polygons, great
  circles on $S^n$ and the geodesics joining two points of $S^n$, meridians of surfaces of
  revolution, the cylinder) and the footnote on $U(n)$ (p. 57): not formalized in this chapter,
  except that $S^n$ is complete and has minimal geodesics between any two points (V7.30). Later
  chapters prove that the geodesics of $S^n$ are the great circles, with the list of those joining
  two points (V10.23), that the geodesics of an open subset of a Euclidean space are the straight
  segments (V10.27), and that the exponential map of a group of matrices such as $U(n)$ is the
  matrix exponential (V12.15). Inscribed polygons, the continuum of minimal geodesics between
  antipodal points, surfaces of revolution and the cylinder are not formalized.
- **Lemma 10.6 as stated:** the two-sided bound $|r(b) - r(a)|$ and the monotonicity of $r$ in the
  equality case (V7.13); Theorem 10.4 uses only the one-sided form, and its equality case is V7.16.
- **§10 on an abstract Riemannian manifold:** Mathlib has no Levi-Civita connection, geodesics or
  exponential map, and the Christoffel-symbol form of the geodesic equation is not formalized
  (V7.3); the embedded results reach an arbitrary Riemannian manifold only through Nash's embedding
  theorem, which is neither in Mathlib nor proved here.

---

## 9. Chapter 8 (Milnor §§11–13): partly verified

Milnor's §11 (pp. 67–69) introduces the space $\Omega = \Omega(M; p, q)$ of piecewise smooth paths
from $p$ to $q$, its "tangent spaces" $T\Omega_\omega$ (an analogy: $\Omega$ is given no topology
before §16), variations and their variation fields, and critical paths of a function on $\Omega$.
§12 (pp. 70–73) defines the energy $E$, compares it with the length by Schwarz's inequality, proves
Lemma 12.1 (on a complete manifold $E$ takes its minimum $d^2$ exactly at the minimal geodesics),
the first variation formula (Theorem 12.2) and Corollary 12.3 (the critical paths of $E$ are the
geodesics). §13 (pp. 74–76) defines the Hessian $E_{**}$ at a geodesic through 2-parameter
variations and proves the second variation formula (Theorem 13.1), Corollary 13.4 ($E_{**}$ is a
well-defined symmetric bilinear form), Remark 13.5 and Lemma 13.6 (at a minimal geodesic $E_{**}$ is
positive semi-definite). Verified, for a submanifold $N$ of a Euclidean space with the induced
metric, in the embedded setting of Chapters 6–7: every numbered statement of §§11–13 except Lemma
12.1, of which only the inequality $E(\gamma) \le E(\omega)$ at a minimal geodesic is checked
(V8.6); the definitions they need; and the exposition's Lemma 11.A (every finite family of fields
along a path is the family of variation fields of one variation, without completeness), Lemma 12.A,
formula (12.2′) and Proposition 13.A. Every Riemannian manifold is such an $N$ by Nash's embedding
theorem, which is quoted, not proved. As in the book, $\Omega$ is given no manifold structure; how
$T\Omega_\omega$ and $E_{**}$ are formalized is explained below. Proved more sharply than in the
book: the first variation at every value of the parameter (V8.9); Theorem 13.1 with the existence
of the second derivative as part of the conclusion (V8.13); the symmetry of $E_{**}$ without
assuming $E \circ \bar\alpha$ of class $C^2$ (V8.16); and Lemma 13.6 from minimality alone (V8.18).
Theorem 14.1 (the null space of $E_{**}$ consists of the Jacobi fields vanishing at the ends) is
also proved, in `Morse/Chapter8/Jacobi.lean`, and is reported with Chapter 9 (§14). **Not
verified:** Lemma 12.1 in full, Milnor's motivating constructions $F_*$ and $f_{**}$ and the example
of p. 69, the index of $E_{**}$ as a number, and the exposition's Lemma 13.B (the list at the end).
Lean: `Morse/Chapter8/` — `Piecewise.lean` (448 lines), `Energy.lean` (576), `FirstVariation.lean`
(572), `Critical.lean` (590), `SecondVariation.lean` (575), `Hessian.lean` (595); the directory also
holds `Jacobi.lean` (704), which belongs to Chapter 9.

**The embedded setting.** As in Chapters 6 and 7: $V$ is a finite-dimensional real inner product
space (Milnor's $\mathbb R^K$) and $N \subseteq V$ a slice submanifold modelled on $Z$ with
complement $W$, both finite-dimensional, with the induced metric. $T_qN \subseteq V$ is the tangent
space and $P_q$ the orthogonal projection onto it (V6.1), extended by $P_x = 0$ for $x \notin N$, so
that $P_{\omega(t)}$ makes sense for every $t$; $D/dt = P \circ d/dt$ along curves (V6.5); $R$ is
Milnor's curvature tensor, with his sign (V6.16–V6.17). Paths, fields and variations are maps defined
on all of $\mathbb R$ (in the time variable), of which only the values for $t \in [0, 1]$ matter.
$c'(t)$ is the derivative of $c$ at $t$, taken to be $0$ where $c$ is not differentiable, which for
the paths below happens at finitely many points only. Piecewise smooth is V7.11's notion: continuous
on the interval, and $C^\infty$, with one-sided derivatives at the ends, on every closed piece
between consecutive points of a finite set of break points. $N$ need not be closed, compact or
connected.

**How $\Omega$, $T\Omega_\omega$ and $E_{**}$ are formalized.** As in the book, $\Omega$ carries no
topology or manifold structure. $T\Omega_\omega$ is *defined* as a vector space of fields along
$\omega$ (V8.1), related to $\Omega$ only through variations: the variation field of every variation
lies in it (V8.2), and every finite family of its elements is the family of variation fields of one
variation (V8.3). Every derivative "on $\Omega$" is a derivative of a function $u \mapsto
E(\bar\alpha(u))$ of finitely many real variables. $E_{**}$ is *defined* as the bilinear form on
$T\Omega_\gamma$ given by the right side of Milnor's second variation formula (V8.14); Theorem 13.1
(V8.13) and Lemma 11.A (V8.3) then show that Milnor's definition through 2-parameter variations is
well defined and agrees with it.

**V8.1 (the path space and its "tangent spaces"; `Morse.pathSpace`, `Morse.prj`,
`Morse.prj_eq_self_iff`, `Morse.pathTangent`, `Morse.mem_pathTangent`,
`Morse.mem_pathTangent_congr`).** For $p, q \in V$, $\Omega(N; p, q)$ is the set of maps $\omega$
that are piecewise smooth on $[0, 1]$, with $\omega(t) \in N$ for $t \in [0, 1]$, $\omega(0) = p$ and
$\omega(1) = q$. For a map $\omega$, $T\Omega_\omega$ is the real vector space of maps $W$ that are
piecewise smooth on $[0, 1]$ and tangent along $\omega$ ($P_{\omega(t)}W(t) = W(t)$ for $t \in [0,
1]$, that is $W(t) \in T_{\omega(t)}N$ when $\omega(t) \in N$), with $W(0) = 0$ and $W(1) = 0$; it
depends only on $\omega$ on $[0, 1]$. *Book:* p. 67: $\Omega(M; p, q)$ is the set of piecewise smooth paths $\omega : [0, 1] \to
M$ from $p$ to $q$ (each $\omega|[t_{i-1}, t_i]$ of class $C^\infty$ for some subdivision), thought of
as "something like an infinite dimensional manifold", to be topologized in §16; $T\Omega_\omega$ is
the vector space of piecewise smooth vector fields $W$ along $\omega$ with $W(0) = 0$ and $W(1) = 0$.
*Hidden hypotheses:* smoothness on a closed piece means one-sided derivatives at its ends.
*Deviation (restated):* paths and fields are maps on $\mathbb R$ considered on $[0, 1]$, and the
subdivision is a finite set of break points (V7.11); a field's break points need not be those of
$\omega$.

**V8.2 (variations and variation fields; `Morse.IsVariation`, `Morse.IsVariation.isPiecewiseSmooth`,
`Morse.IsVariation.mem_pathSpace`, `Morse.IsVariation.comp`, `Morse.varField`,
`Morse.hasFDerivWithinAt_mem_tangentSubspace`, `Morse.IsVariation.prj_varDeriv`,
`Morse.IsVariation.varField_mem`).** Let $P$ be a real normed space (Milnor's $\mathbb R$ or
$\mathbb R^n$) and $U \ni 0$ an open subset of $P$. A map $\alpha(u, t)$, $u \in P$, $t \in \mathbb R$,
is a variation with break points $B$ (a finite set) if $\alpha(u, t) \in N$ for $u \in U$ and $t \in
[0, 1]$; $\alpha(u, 0)$ and $\alpha(u, 1)$ do not depend on $u \in U$; and $\alpha$ is $C^\infty$ on
every closed strip $U \times [s, t]$, $0 \le s < t \le 1$, with no point of $B$ in $(s, t)$. It is a
variation of $\omega = \alpha(0, \cdot)$, and every $\alpha(u, \cdot)$, $u \in U$, lies in
$\Omega(N; \omega(0), \omega(1))$; composed with a smooth map into $P$ that sends $0$ into $U$ it is
again a variation (for instance a slice $u_2 \mapsto \alpha(u_1, u_2, \cdot)$). For $P = \mathbb R$
the variation field is $W_t = \frac{\partial\alpha}{\partial u}(0, t)$; every
$\frac{\partial\alpha}{\partial u}(u, t)$ is tangent to $N$ at $\alpha(u, t)$, and $W \in
T\Omega_\omega$. Derivatives within a set (for instance one-sided derivatives along the edge of a
strip) of maps into $N$ are tangent to $N$. *Book:* p. 68: a variation of $\omega$ keeping the end
points fixed is a map $\bar\alpha : (-\varepsilon, \varepsilon) \to \Omega$ with $\bar\alpha(0) =
\omega$ and a subdivision such that $\alpha(u, t) = \bar\alpha(u)(t)$ is $C^\infty$ on each strip
$(-\varepsilon, \varepsilon) \times [t_{i-1}, t_i]$; an $n$-parameter variation replaces
$(-\varepsilon, \varepsilon)$ by a neighbourhood of $0$ in $\mathbb R^n$; $W_t =
\frac{\partial\alpha}{\partial u}(0, t)$, and "clearly" $W \in T\Omega_\omega$. *Hidden
hypotheses:* behind "clearly": $W$ is continuous at a break point $t_i$ because both adjacent strips
compute the velocity of the same curve $u \mapsto \alpha(u, t_i)$, tangent because that curve lies
in $N$, and zero at the ends because they are fixed. *Deviation (stronger):* any open parameter set
containing $0$, in any normed space.

**V8.3 (Lemma 11.A: every family of tangent fields comes from one variation;
`Morse.exists_variation`, `Morse.exists_variation_one`, `Morse.exists_variation_two`).** Let
$\omega \in \Omega(N; p, q)$, $P$ a real normed space, and $\Lambda$ a family, piecewise smooth on
$[0, 1]$, of continuous linear maps $\Lambda(t) : P \to V$ with values in $T_{\omega(t)}N$ and
$\Lambda(0) = \Lambda(1) = 0$. There are $\varepsilon > 0$ and a finite set $B$ such that
$\alpha(u, t) = \exp_{\omega(t)}(\Lambda(t)u)$ is a variation with break points $B$ on the ball
$\|u\| < \varepsilon$ (V8.2), with $\alpha(0, t) = \omega(t)$ and derivative $\Lambda(t)$ in $u$ at
$u = 0$, for $t \in [0, 1]$. In particular every $W \in T\Omega_\omega$ is the variation field of
$\alpha(u, t) = \exp_{\omega(t)}(uW_t)$, $|u| < \varepsilon$; and for $W_1, W_2 \in T\Omega_\omega$,
$\alpha(u_1, u_2, t) = \exp_{\omega(t)}(u_1W_1(t) + u_2W_2(t))$ is a 2-parameter variation of
$\omega$ with $\frac{\partial\alpha}{\partial u_i}(0, 0, t) = W_i(t)$. *Book:* p. 68: given $W \in
T\Omega_\omega$ there is a variation with $\bar\alpha(0) = \omega$ and $\frac{d\bar\alpha}{du}(0) =
W$; "in fact one can set" $\bar\alpha(u)(t) = \exp_{\omega(t)}(uW_t)$; p. 74: 2-parameter variations
with given fields are chosen without comment. *Hidden hypotheses:* $\exp$ is defined only near the
zero section (Lemma 10.2), so $\varepsilon$ must be chosen uniformly along $\omega$, by the
compactness of $\omega([0, 1])$ and a bound for $\|\Lambda\|$; completeness of $N$ is not needed.
*Deviation (stronger):* any number of parameters (the exposition's Lemma 11.A). *Proof:* $\exp$ is
defined and smooth on an open neighbourhood of the zero section of $TN$ (V7.8), and the derivative
in $u$ at $0$ is $\Lambda(t)$ because $d(\exp_q)_0$ is the inclusion of $T_qN$.

**V8.4 (critical paths of the energy; `Morse.IsCriticalPath`).** A map $\omega$ is a critical path
of the energy $E$ (V8.5) if for every 1-parameter variation $\alpha$ with $\alpha(0, t) =
\omega(t)$ for $t \in [0, 1]$, the function $u \mapsto E(\alpha(u, \cdot))$ is differentiable at $0$
with derivative $0$. *Book:* p. 69: $\omega$ is a critical path of $F : \Omega \to \mathbb R$ iff
$\frac{dF(\bar\alpha(u))}{du}\big|_{u=0}$ is zero for every variation $\bar\alpha$ of $\omega$.
*Hidden hypotheses:* that the derivative exists (for $E$ it always does, V8.9). *Deviation
(narrower):* only for $F = E$, the case of Corollary 12.3.

**V8.5 (energy and length, Lemma 12.A; `Morse.energy`, `Morse.pathLength_sq_le_energy`,
`Morse.pathLength_sq_eq_energy_iff`, `Morse.energy_eq_of_norm_deriv`).** For a map $c$ into a real
normed space and $a \le b$, $E_a^b(c) = \int_a^b \|c'(t)\|^2\,dt$, $E = E_0^1$, and $L_a^b(c) =
\int_a^b \|c'(t)\|\,dt$ is the length of V7.11. If $c$ is piecewise smooth on $[a, b]$, then
$(L_a^b(c))^2 \le (b - a)E_a^b(c)$, with equality iff $\|c'\|$ takes one and the same value at all
points of $(a, b)$ where $c$ is differentiable. An admissible path (V7.11) of constant speed $k$
there has $E_a^b = k^2(b - a)$. *Book:* p. 70: $E_a^b(\omega) = \int_a^b \|d\omega/dt\|^2\,dt$, $E =
E_0^1$, $L_a^b$, and by Schwarz's inequality $(L_a^b)^2 \le (b - a)E_a^b$, with equality iff
$\|d\omega/dt\|$ is constant, i.e. iff the parameter is proportional to arc length. *Hidden
hypotheses:* for a speed that is only piecewise continuous, "constant" can only mean constant off
the break points. *Deviation (stronger):* any $a \le b$ (Milnor: $0 \le a < b \le 1$) and any normed
target. *Proof:* the variance identity $(b - a)\int_a^b (g - \bar g)^2 = (b - a)E_a^b - (L_a^b)^2$,
$g = \|c'\|$ with mean $\bar g$ (the exposition's Lemma 12.A).

**V8.6 (the inequality of Lemma 12.1; `Morse.IsMinimalPath`, `Morse.energy_le_of_isMinimalPath`).**
A path $\gamma \in \Omega(N; p, q)$ is minimal if $L(\gamma) \le L(\omega)$ for every $\omega \in
\Omega(N; p, q)$. If $\gamma$ is minimal and a geodesic (V8.10), then $E(\gamma) \le E(\omega)$ for
every $\omega \in \Omega(N; p, q)$. *Book:* p. 70, Lemma 12.1: if $M$ is complete and $p, q$ are at
distance $d$, then $E : \Omega(M; p, q) \to \mathbb R$ takes its minimum $d^2$ precisely on the set
of minimal geodesics from $p$ to $q$; the proof is the chain $E(\gamma) = L(\gamma)^2 \le
L(\omega)^2 \le E(\omega)$. *Hidden hypotheses:* completeness serves only to make a minimal geodesic
exist (V7.26); the inequality holds on any $N$. *Deviation (narrower):* only the inequality; neither
the value $d^2$ of the minimum nor the converse (a path of energy $d^2$ is a minimal geodesic, which
needs the equality cases of V8.5 and Corollary 10.7) is formalized. Minimality is among the paths of
$\Omega$, parametrized on $[0, 1]$; by affine reparametrization this is Milnor's notion (V7.24), an
equivalence not stated formally. *Proof:* Milnor's chain, with the constant speed of a geodesic
(V7.2) and V8.5.

**V8.7 (velocity jumps, acceleration and the first variation; `Morse.jump`, `Morse.jump_eq_zero`,
`Morse.covD`, `Morse.covD_eq_covDeriv`, `Morse.accel`, `Morse.firstVariation`,
`Morse.finsum_jump_eq_sum`, `Morse.firstVariation_congr_field`).** For a map $f$ into $V$, the jump
of its derivative at $t$ is $\Delta_tf' = f'(t^+) - f'(t^-)$, the difference of the right and the
left derivative of $f$ at $t$; it vanishes where $f$ is differentiable. Along a path $\omega$,
$\frac{DX}{dt}(t) = P_{\omega(t)}X'(t)$
(for $\omega$ in $N$, $D/dt$ of V6.5), $V = \omega'$ and $A = \frac{D}{dt}V$. The first variation of
$\omega$ in the direction $W$ is
$$-\sum_{0 < t < 1}\langle W_t, \Delta_tV\rangle - \int_0^1 \langle W_t, A_t\rangle\,dt,$$
the sum being finite: for $\omega$ differentiable off a finite set $B$, it is the sum over the points
of $B$ in $(0, 1)$. It depends only on $W$ on $[0, 1]$. *Book:* p. 71: $V_t = d\omega/dt$, $A_t =
\frac{D}{dt}\frac{d\omega}{dt}$, $\Delta_tV = V_{t^+} - V_{t^-}$, which is $0$ for all but finitely
many $t \in (0, 1)$. *Hidden hypotheses:* none. *Deviation (restated):* the sum is written over all
of $(0, 1)$, its terms vanishing off the break points.

**V8.8 (calculus on closed strips; `Morse.pdU`, `Morse.pdT`, `Morse.hasDerivWithinAt_pdT`,
`Morse.pdU_pdT`, `Morse.hasDerivAt_integral_strip`, `Morse.piecewise_induction`,
`Morse.integral_eq_of_piecewise`, `Morse.hasDerivAt_integral_of_piecewise`).** For $F$ smooth on a
closed strip $U \times [a, b]$, $U \subseteq \mathbb R$ open, $a < b$: the partial derivatives
$\partial F/\partial u$ and $\partial F/\partial t$ computed within the strip are smooth on it, are
the one-sided $t$-derivatives on the edges $t = a$, $t = b$, and the mixed partials agree on the
whole closed strip, edges included. If $F$ and $F'$ are continuous on the strip and $F'$ is the
$u$-derivative of $F$ at its interior points, then $u \mapsto \int_a^b F(u, t)\,dt$ has derivative
$\int_a^b F'(u_0, t)\,dt$ at every $u_0 \in U$; the same holds for an integrand that on each piece
of a finite subdivision agrees, inside the piece, with a function of class $C^1$ on the closed
strip. If $\int_s^t g = F^-(t) - F^+(s)$ on every piece $[s, t]$ of $[a, b]$ with break points $B$,
then $\int_a^b g = F^-(b) - F^+(a) - \sum_{x \in B \cap (a, b)} (F^+(x) - F^-(x))$; and properties of
intervals that hold on pieces and glue at break points hold on every interval. *Book:* used without
comment in the proofs of Theorems 12.2 and 13.1 (pp. 71–72, 74–76): differentiation under the
integral sign, integration by parts on each $[t_{i-1}, t_i]$, and adding up. *Hidden hypotheses:*
smoothness on the closed strips; compactness, for the domination bound; the symmetry of second
derivatives on the edges of the strips, where the $t$-derivatives are one-sided. *Deviation (not in
the book).*

**V8.9 (Theorem 12.2 and formula (12.2′); `Morse.IsVariation.hasDerivAt_energy`,
`Morse.first_variation`).** Let $\alpha$ be a 1-parameter variation (V8.2), with parameter set $U
\subseteq \mathbb R$. For every $u_0 \in U$, $u \mapsto E(\alpha(u, \cdot))$ is differentiable at
$u_0$, and
$$\frac12\frac{d}{du}E(\alpha(u, \cdot))\Big|_{u = u_0} = -\sum_t\Big\langle\frac{\partial\alpha}
{\partial u}, \Delta_t\frac{\partial\alpha}{\partial t}\Big\rangle - \int_0^1\Big\langle\frac{\partial
\alpha}{\partial u}, \frac{D}{\partial t}\frac{\partial\alpha}{\partial t}\Big\rangle\,dt,$$
everything at $(u_0, t)$: the first variation (V8.7) of $\alpha(u_0, \cdot)$ in the direction
$\frac{\partial\alpha}{\partial u}(u_0, \cdot)$. In particular, if $\alpha(0, t) = \omega(t)$ on
$[0, 1]$ and $W$ is the variation field, $\frac12\frac{dE(\bar\alpha(u))}{du}(0) = -\sum_t\langle
W_t, \Delta_tV\rangle - \int_0^1\langle W_t, A_t\rangle\,dt$. *Book:* p. 71, Theorem 12.2, at
$u = 0$ (the scan loses the leading minus sign of the displayed statement; the end of the proof, p.
72, has it); the proof differentiates under the integral sign, uses Lemma 8.3 and "Lemma 8.5" to
replace $\frac{D}{\partial u}\frac{\partial\alpha}{\partial t}$ by $\frac{D}{\partial t}
\frac{\partial\alpha}{\partial u}$, integrates by parts on each $[t_{i-1}, t_i]$ and adds up.
*Hidden hypotheses:* the reference should be to Lemma 8.7 (8.5 is the definition of a symmetric
connection); differentiation under the integral sign and the symmetry of mixed partials on the closed
strips (V8.8); the boundary terms telescope into the jump terms because $\partial\alpha/\partial u$
is continuous in $t$. *Deviation (stronger):* the formula at every $u$, formula (12.2′) of the
exposition, which §13 differentiates.

**V8.10 (geodesics of $\Omega$; criticality through the first variation; `Morse.IsUnbrokenGeodesic`,
`Morse.isCriticalPath_iff`, `Morse.IsUnbrokenGeodesic.firstVariation_eq_zero`).** A map $\omega$ is
an (unbroken) geodesic if it is $C^\infty$ on $[0, 1]$, with one-sided derivatives at the ends, and a
geodesic on $(0, 1)$ in the sense of V7.1, so that $A = 0$ there. For $\omega \in \Omega(N; p, q)$:
$\omega$ is a critical path (V8.4) iff its first variation (V8.7) vanishes in every direction $W \in
T\Omega_\omega$. For a geodesic, the first variation vanishes in every direction. *Book:* p. 73: the
path $\omega \in \Omega$ is a geodesic iff $\omega$ is $C^\infty$ on the whole interval $[0, 1]$ and
its acceleration $\frac{D}{dt}\frac{d\omega}{dt}$ is identically zero; "clearly a geodesic is a
critical point". *Hidden hypotheses:* the converse direction of the "iff" needs Lemma 11.A (V8.3).
*Deviation (restated):* the acceleration is required to vanish on $(0, 1)$; at the ends it then
vanishes by continuity. *Proof:* Theorem 12.2 (V8.9) and Lemma 11.A (V8.3).

**V8.11 (Corollary 12.3; `Morse.accel_eq_zero_of_critical`, `Morse.prj_jump`,
`Morse.jump_eq_zero_of_critical`, `Morse.exists_isGeodesicOn_through`, `Morse.isGeodesicOn_of_glue`,
`Morse.corollary_12_3`).** A path $\omega \in \Omega(N; p, q)$ is a critical path of $E$ iff it is a
geodesic (V8.10). The steps, for $\omega$ critical and smooth on the pieces of a finite set $B$: the
acceleration vanishes at every $t \in (0, 1) \setminus B$; the one-sided velocities, hence the jumps
$\Delta_tV$, are tangent to $N$, and every jump $\Delta_tV$, $0 < t < 1$, vanishes; through every
$q \in N$ with any velocity $v \in T_qN$ at any time $x$ there is a geodesic on an interval around
$x$; and a path which is a geodesic on both sides of $x$, smooth up to $x$ from each side, and
differentiable at $x$, is a geodesic near $x$. *Book:* p. 73, Corollary 12.3; proof: a variation
with $W(t) = f(t)A(t)$, $f$ positive except at the $t_i$, gives $A = 0$ on each piece; one with
$W(t_i) = \Delta_{t_i}V$ gives $\Delta_{t_i}V = 0$, so $\omega$ is $C^1$; then $\omega$ is $C^\infty$
"from the uniqueness theorem for differential equations". *Hidden hypotheses:* the test variations
exist only by Lemma 11.A (V8.3); $W = fA$ must be continuous at the $t_i$, where the one-sided
accelerations differ; a field with the prescribed values $\Delta_{t_i}V$ must be constructed; the
last step needs the lift $(\omega, \omega')$ to solve the geodesic equation at the former break
point itself (a derivative-extension argument) before uniqueness applies. *Proof:* test fields $W =
\varphi A$ and $W = \varphi P(\Delta_xV)$, with $\varphi \ge 0$ a bump function at one point $x$,
supported where $\omega$ is smooth, give $A(x) = 0$ and $\|\Delta_xV\|^2 = 0$; then uniqueness for
the first-order geodesic system (V7.3, V7.4) identifies $\omega$ near $x$ with the geodesic through
$(\omega(x), \omega'(x))$.

**V8.12 (the curvature identity (13.3), and jumps under differentiation; `Morse.curvR`,
`Morse.curvR_of_mem`, `Morse.curvature_identity`, `Morse.IsVariation.hasDerivAt_jump`).** $R(a, b)c$
at $x \in N$ is Milnor's curvature tensor of $N$ at $x$ (V6.17, with his sign), and $0$ for $x \notin
N$. (i) For a map $F(u, t)$, smooth on an open subset $O$ of $\mathbb R^2$ with values in $N$, at
every point of $O$
$$\frac{D}{\partial u}\frac{D}{\partial t}\frac{\partial F}{\partial t} = \frac{D}{\partial t}
\frac{D}{\partial t}\frac{\partial F}{\partial u} + R\Big(\frac{\partial F}{\partial t},
\frac{\partial F}{\partial u}\Big)\frac{\partial F}{\partial t},$$
with $\frac{D}{\partial u}X = P(\partial X/\partial u)$ and $\frac{D}{\partial t}X = P(\partial
X/\partial t)$. (ii) For a 1-parameter variation $\alpha$, $u_0 \in U$ and $0 < x < 1$, the jump
$\Delta_x\frac{\partial\alpha}{\partial t}(u, \cdot)$ is differentiable in $u$ at $u_0$, with
derivative $\Delta_x\frac{\partial}{\partial t}\frac{\partial\alpha}{\partial u}(u_0, \cdot)$.
*Book:* pp. 75–76: the curvature formula $\frac{D}{\partial u_1}\frac{D}{\partial t}V -
\frac{D}{\partial t}\frac{D}{\partial u_1}V = R(V, W_1)V$ (Lemma 9.2) and $\frac{D}{\partial u_1}V
= \frac{D}{\partial t}W_1$ (Lemma 8.7) give (13.3), $\frac{D}{\partial u_1}\frac{D}{\partial t}V =
\frac{D^2W_1}{dt^2} + R(V, W_1)V$; on p. 75, "rearranging the second term" of the differentiated
first variation formula. *Hidden hypotheses:* Lemmas 8.7 and 9.2 are applied to a surface defined
only on the strips, near an interior point (Chapter 6 states them for surfaces on all of $\mathbb
R^2$, V6.15, V6.19); differentiating a one-sided $t$-derivative in $u$ needs the symmetry of mixed
partials on the edges of the strips (V8.8). *Deviation (restated):* (i) is (13.3) for a surface,
with $x = t$, $y = u$ in Lemma 9.2.

**V8.13 (Theorem 13.1, the second variation formula; `Morse.secondVariation`, `Morse.second_variation`,
`Morse.second_variation_eq`).** For a path $\gamma$ with velocity $V = \gamma'$ and fields $W_1,
W_2$ along it, let
$$\Phi(W_1, W_2) = -\sum_{0 < t < 1}\Big\langle W_2(t), \Delta_t\frac{DW_1}{dt}\Big\rangle -
\int_0^1\Big\langle W_2, \frac{D^2W_1}{dt^2} + R(V, W_1)V\Big\rangle\,dt,$$
where $\Delta_t\frac{DW_1}{dt} = P_{\gamma(t)}(\Delta_tW_1)$ is the jump of $\frac{DW_1}{dt} =
PW_1'$. Let $\gamma$ be a geodesic (V8.10) and $\alpha(u_1, u_2, t)$ a 2-parameter variation of
$\gamma$ (parameter set $U \subseteq \mathbb R^2$, $\alpha(0, 0, t) = \gamma(t)$ on $[0, 1]$) with
variation fields $W_i = \frac{\partial\alpha}{\partial u_i}(0, 0, \cdot)$. Then $u_1 \mapsto
\frac{\partial}{\partial u_2}E(\alpha(u_1, u_2, \cdot))\big|_{u_2 = 0}$ is differentiable at $u_1 =
0$, and its derivative, Milnor's $\frac{\partial^2E}{\partial u_1\partial u_2}(0, 0)$, equals
$2\Phi(W_1, W_2)$. Two 2-parameter variations of $\gamma$ whose variation fields agree on $[0, 1]$
have the same $\frac{\partial^2E}{\partial u_1\partial u_2}(0, 0)$. *Book:* p. 75, Theorem 13.1:
$\frac12\frac{\partial^2E}{\partial u_1\partial u_2}(0, 0) = \Phi(W_1, W_2)$ (the scan drops the
$-\sum_t$ in front of the first term of the displayed statement; (13.2) on the same page has it),
introduced on p. 74 to show that $E_{**}$ is well defined; proof pp. 75–76, from 12.2, the vanishing
of $\Delta_tV$ and $\frac{D}{dt}V$ along a geodesic, (13.2) and (13.3). *Hidden hypotheses:* (12.2′)
at every $(u_1, 0)$ (V8.9); differentiating the jump and integral terms in $u_1$ (V8.8, V8.12);
the curvature identity on the strips (V8.12). *Deviation (restated):* the mixed second derivative is
the iterated derivative $\partial/\partial u_1$ of $\partial E/\partial u_2$ along $u_2 = 0$, which is
what Milnor's proof computes; its existence is part of the conclusion, and $E \circ \bar\alpha$ is
not assumed to be of class $C^2$.

**V8.14 (the Hessian $E_{**}$; `Morse.energyHessian`, `Morse.energyHessian_apply`,
`Morse.IsVariation.partial₁_mem`, `Morse.IsVariation.partial₂_mem`, `Morse.hasDerivAt_energyHessian`,
`Morse.secondVariation_congr`).** For $\gamma \in \Omega(N; p, q)$, $E_{**}(W_1, W_2) = 2\Phi(W_1,
W_2)$ (V8.13) is a bilinear form on the vector space $T\Omega_\gamma$ (V8.1; bilinearity is V8.15–
V8.16), depending only on the values of the fields on $[0, 1]$. The variation fields of a
2-parameter variation of $\gamma$ lie in $T\Omega_\gamma$. If $\gamma$ is a geodesic, then for every
2-parameter variation of $\gamma$ with variation fields $W_1, W_2$, Milnor's $\frac{\partial^2E}
{\partial u_1\partial u_2}(0, 0)$ (as in V8.13) exists and equals $E_{**}(W_1, W_2)$; and by Lemma
11.A (V8.3) every pair $W_1, W_2 \in T\Omega_\gamma$ is the pair of variation fields of such a
variation. So Milnor's definition is well defined and agrees with $E_{**}$. *Book:* p. 74: for a
geodesic $\gamma$, $E_{**} : T\Omega_\gamma \times T\Omega_\gamma \to \mathbb R$, the Hessian of $E$
at $\gamma$, is defined by analogy with the Hessian $f_{**}$ of a function on a manifold: choose a
2-parameter variation with fields $W_1, W_2$ and put $E_{**}(W_1, W_2) = \frac{\partial^2E(\bar
\alpha(u_1, u_2))}{\partial u_1\partial u_2}(0, 0)$. *Hidden hypotheses:* that such variations
exist (Lemma 11.A); well-definedness is Theorem 13.1. *Deviation (restated):* $\Omega$ has no
manifold structure, here as in the book; $E_{**}$ is defined by Milnor's formula and identified with
his definition by the statements above. It is defined for every $\gamma \in \Omega$; only at a
geodesic is it the second derivative of $E$.

**V8.15 (Proposition 13.A, the Hessian as an integral; `Morse.hessForm`,
`Morse.secondVariation_eq_hessForm`, `Morse.energyHessian_eq_integral`).** For $\gamma \in
\Omega(N; p, q)$ and $W_1, W_2 \in T\Omega_\gamma$,
$$\tfrac12E_{**}(W_1, W_2) = \int_0^1\Big(\Big\langle\frac{DW_1}{dt}, \frac{DW_2}{dt}\Big\rangle -
\langle R(V, W_1)V, W_2\rangle\Big)\,dt.$$
*Book:* not in the book. *Hidden hypotheses:* none; $\gamma$ need not be a geodesic. *Deviation (not
in the book):* the exposition's Proposition 13.A. *Proof:* one integration by parts on each piece
(Lemma 8.3, V6.10), the boundary terms telescoping into the jump terms, $W_2$ vanishing at the ends.

**V8.16 (Corollary 13.4; `Morse.inner_curvR_comm`, `Morse.hessForm_comm`, `Morse.hessForm_add_right`,
`Morse.hessForm_smul_right`, `Morse.energyHessian_isSymm`).** For $\gamma \in \Omega(N; p, q)$,
$E_{**}$ is a symmetric bilinear form on $T\Omega_\gamma$. For tangent vectors $v, w_1, w_2$ at $x
\in N$, $\langle R(v, w_1)v, w_2\rangle = \langle R(v, w_2)v, w_1\rangle$. *Book:* p. 76, Corollary
13.4: $E_{**}(W_1, W_2) = \frac{\partial^2E}{\partial u_1\partial u_2}(0, 0)$ is a well defined,
symmetric, bilinear function of $W_1, W_2$; well defined and bilinear by the second variation
formula, symmetric by $\frac{\partial^2E}{\partial u_1\partial u_2} = \frac{\partial^2E}{\partial
u_2\partial u_1}$. *Hidden hypotheses:* that symmetry of mixed partials needs $E \circ \bar\alpha$ of
class $C^2$ near $(0, 0)$, which the book does not address; bilinearity in $W_1$ needs the linearity
of $W \mapsto \Delta_t\frac{DW}{dt}$ and $W \mapsto \frac{D^2W}{dt^2}$ on piecewise smooth fields.
*Deviation (restated):* well-definedness is V8.13–V8.14; symmetry and bilinearity come from the
integral form (V8.15) and the symmetry of the curvature term (Lemma 9.3 (4), here from the Gauss
equation, V6.18), not from second derivatives.

**V8.17 (Remark 13.5; `Morse.remark_13_5`, `Morse.hasDerivAt_deriv_energy`).** Let $\gamma \in
\Omega(N; p, q)$ be a geodesic and $\alpha$ a 1-parameter variation of $\gamma$ with variation
field $W$. Then $u \mapsto \frac{d}{du}E(\alpha(u, \cdot))$ is differentiable at $0$, and
$\frac{d^2E(\bar\alpha(u))}{du^2}(0) = E_{**}(W, W)$. *Book:* p. 76, Remark 13.5, through the
2-parameter variation $\beta(u_1, u_2) = \bar\alpha(u_1 + u_2)$. *Hidden hypotheses:* that $\beta$
is a 2-parameter variation with both variation fields equal to $W$. *Proof:* Milnor's, V8.13 for
$\beta$.

**V8.18 (Lemma 13.6; `Morse.lemma_13_6`).** If $\gamma \in \Omega(N; p, q)$ is a geodesic and is
minimal in the sense of V8.6, then $E_{**}(W, W) \ge 0$ for every $W \in T\Omega_\gamma$. *Book:*
p. 76, Lemma 13.6: if $\gamma$ is a minimal geodesic from $p$ to $q$, then $E_{**}$ is positive
semi-definite, hence its index $\lambda$ is zero; proof: $E(\bar\alpha(u)) \ge E(\gamma) =
E(\bar\alpha(0))$ forces $\frac{d^2E(\bar\alpha(u))}{du^2}(0) \ge 0$. *Hidden hypotheses:* only
minimality is used, not completeness; the energy inequality is V8.6; that a minimum forces a
nonnegative second derivative needs an argument when only the second derivative at $0$ is known to
exist (if it were negative, $0$ would also be a local maximum, so the function would be locally
constant and its second derivative $0$). *Deviation (narrower):* the index of $E_{**}$ (the largest
dimension of a subspace on which it is negative definite) is not defined formally; index $0$ is the
positive semi-definiteness proved. *Proof:* for $W \in T\Omega_\gamma$, Lemma 11.A gives a variation
with field $W$; $u \mapsto E(\bar\alpha(u))$ has a minimum at $0$ (V8.6) and second derivative
$E_{**}(W, W)$ there (V8.17).

### What is not verified in this chapter

- **Lemma 12.1 in full** (p. 70): that the minimum of $E$ on $\Omega$ is $d^2$ and is attained
  exactly at the minimal geodesics. Only $E(\gamma) \le E(\omega)$ at a minimal geodesic is
  formalized (V8.6); the existence of a minimal geodesic on a complete $N$ is V7.26, but the equality
  cases (V8.5 and Corollary 10.7) are not assembled into the converse.
- **Milnor's motivating constructions** (pp. 67–69, 74): the induced map $F_*$ of a function on
  $\Omega$, the Hessian $f_{**}$ of a function on a finite-dimensional manifold and its independence
  of the chosen map, and the example of p. 69 (a minimum of $F$ at which all the derivatives
  $dF(\bar\alpha(u))/du$ exist is a critical path). Critical paths are defined for $E$ only (V8.4).
- **The index of $E_{**}$** (p. 76: "hence the index $\lambda$ of $E_{**}$ is zero"): not defined
  (V8.18); it belongs with the index theorem (§15).
- **A topology or manifold structure on $\Omega$**: none, as in §§11–15 of the book; Palais's
  Hilbert manifold of $H^1$ paths is not formalized.
- **The exposition's Lemma 13.B** (rescaling the Hessian of a geodesic on $[0, \tau]$, used in
  Chapter 9): not formalized.
- **§§11–13 on an abstract Riemannian manifold**: as in Chapters 6–7, only for submanifolds of a
  Euclidean space with the induced metric; Nash's embedding theorem is quoted, not proved.

---

## 10. Chapter 9 (Milnor §§14–15): partly verified

Milnor's §14 (pp. 77–82) defines Jacobi fields along a geodesic, conjugate points and their
multiplicity, and the null space and nullity of $E_{**}$. It proves that the null space consists of
the Jacobi fields vanishing at both ends (Theorem 14.1) and that the nullity is less than $n$
(Remark 14.2), treats flat manifolds and the antipodal points of $S^n$ (Examples 1–2), shows that
the Jacobi fields are exactly the variation fields of variations through geodesics (Lemmas
14.3–14.4), and adds two remarks on short segments (Remarks 14.5–14.6). §15 (pp. 83–87) proves the
Morse index theorem (Theorem 15.1, with Corollary 15.2): the index of $E_{**}$ is the number of
interior conjugate points, counted with multiplicity. The proof splits $T\Omega_\gamma$ into the
broken Jacobi fields of a fine subdivision and the fields vanishing at its points (Lemma 15.3),
reduces the index to the finite-dimensional first summand (Lemma 15.4), and follows the index
$\lambda(\tau)$ of $\gamma|[0, \tau]$ through Assertions (1)–(4). Verified, for a submanifold $N$ of a
Euclidean space with the induced metric, in the embedded setting of Chapters 6–8: every numbered
statement of §§14–15 except Examples 1 and 2 and part of Remark 14.6 (negative parameters, and the
absence of cluster points along an entire geodesic), Remark 14.5 being restated for the
neighbourhoods of Lemma 10.3; the definitions they need (Jacobi fields, conjugate parameters and
their multiplicity, the null space and nullity of $E_{**}$, the index of a bilinear form, fine
subdivisions, broken Jacobi fields, $\lambda(\tau)$); Milnor's parenthetical remark on p. 81 (V9.10);
and the exposition's Lemma 14.A, Corollary 14.B and Lemmas 15.A–15.C. Every Riemannian manifold is
such an $N$ by Nash's embedding theorem, which is quoted, not proved. Proved more sharply than in
the book: the solution theory of the Jacobi equation, Remark 14.6 and the index identity along any
smooth curve in $N$, not only along geodesics (V9.2, V9.12, V9.24); Remark 14.2 also for the
constant geodesic (V9.7); and the lower bound of Assertion (4) for every $\tau' > \tau$ (V9.23). The
proofs depart from Milnor's in three places. **Lemma 14.4 is proved from initial data**, with the
variation $\alpha(u, t) = \exp_{c(u)}(t\,w(u))$, so that neither minimal geodesics nor a short
initial segment are needed (V9.9). **Positivity on $T'$ comes from a Poincaré estimate**, which also
gives the two properties of a fine subdivision and Assertion (2), without minimal geodesics (V9.16,
V9.18, V9.20). **$\lambda(\tau)$ is the index of $E_{**}$ on the fields supported in $[0, \tau]$**,
so that no Hessian along $\gamma|[0, \tau]$ on its own parameter interval is needed (V9.17, V9.20).
**Not verified:** Examples 1 and 2, the rest of Remark 14.6, and the exposition's Lemma 14.C and §5
(the list at the end). Lean: `Morse/Chapter8/Jacobi.lean` (704 lines; Theorem 14.1) and
`Morse/Chapter9/` — `FormIndex.lean` (379), `JacobiODE.lean` (256), `JacobiSystem.lean` (570),
`JacobiSpace.lean` (507), `IndexForm.lean` (458), `BrokenJacobi.lean` (466), `IndexReduction.lean`
(437), `IndexContinuity.lean` (450), `IndexAssertions.lean` (419), `IndexTheorem.lean` (286),
`JacobiVariation.lean` (386), `GeodesicVariation.lean` (674).

**The embedded setting.** As in Chapter 8: $V$ is a finite-dimensional real inner product space
and $N \subseteq V$ a slice submanifold modelled on $Z$ with complement $W$, with the induced metric;
every tangent space $T_xN$, $x \in N$, has dimension $n = \dim Z$ (`Morse.finrank_tanAt`); $P_x$ is
the orthogonal projection onto $T_xN$ ($P_x = 0$ for $x \notin N$), $D/dt = P \circ d/dt$, and $R$ is
Milnor's curvature tensor, with his sign (V6.16–V6.17, V8.12). $\Omega = \Omega(N; p, q)$,
$T\Omega_\gamma$, the geodesics of $\Omega$, the form $\Phi$ of the second variation formula and
$E_{**} = 2\Phi$ are those of V8.1, V8.10, V8.13 and V8.14. A *smooth curve in $N$ on $[0, 1]$*
(`Morse.IsSmoothCurveIn`) is a map $\gamma : \mathbb R \to V$ that is $C^\infty$ on $[0, 1]$, with
one-sided derivatives at the ends, and has values in $N$ there; every geodesic of $\Omega$ is one
(`Morse.IsUnbrokenGeodesic.isSmoothCurveIn`), and every such curve lies in
$\Omega(N; \gamma(0), \gamma(1))$ (`Morse.IsSmoothCurveIn.mem_pathSpace`). Along it the velocity
$V(t)$, the derivative $P'(t)$ of $t \mapsto P(t) = P_{\gamma(t)}$, and $\frac{DX}{dt}(t) =
P(t)X'(t)$ are computed within $[0, 1]$, so one-sided at the ends (`Morse.velAlong`,
`Morse.dpAlong`, `Morse.covAlong`). Curves and fields are maps on $\mathbb R$ of which only the
values on $[0, 1]$ matter; where a space of fields is to be finite-dimensional, its elements are
normalized to be constant off $[0, 1]$. $N$ need not be closed, compact or connected.

**How the index, the nullity and $\lambda(\tau)$ are formalized.** $T\Omega_\gamma$ is
infinite-dimensional, and its elements (V8.1) are maps on $\mathbb R$ whose values off $[0, 1]$
play no role. Hence three conventions. The index of a bilinear form is a supremum in
$\{0, 1, 2, \dots\} \cup \{\infty\}$ (V9.13); that it is finite for $E_{**}$ is part of Theorem 15.1,
as in the book. The null space of $E_{**}$ is read on $[0, 1]$ (V9.6), since the literal kernel of
the formal $E_{**}$ contains every field vanishing on $[0, 1]$. And Milnor's $\lambda(\tau)$, the
index of the Hessian $(E_0^\tau)_{**}$ of $\gamma_\tau = \gamma|[0, \tau]$, is the index of $E_{**}$
(of $\gamma$ on $[0, 1]$) restricted to the fields of $T\Omega_\gamma$ vanishing outside $[0, \tau]$
(V9.17, V9.20). These are Milnor's fields along $\gamma_\tau$ vanishing at $0$ and $\tau$, extended by
zero as in his proof of Assertion (1), and on them $\frac12E_{**}(W_1, W_2) = \int_0^\tau(\langle
\frac{DW_1}{dt}, \frac{DW_2}{dt}\rangle - \langle R(V, W_1)V, W_2\rangle)\,dt$ (V8.15), the integral
that represents $\frac12(E_0^\tau)_{**}$ (Proposition 13.A on $[0, \tau]$). The Hessian on
$[0, \tau]$ itself is not formalized, and the proof does not need it.

**V9.1 (linear equations: global solutions, the exposition's Lemma 14.A; `Morse.exists_linearODE`,
`Morse.linSol`, `Morse.linSol_add`, `Morse.linSol_smul`, `Morse.eqOn_Icc_linSol`,
`Morse.contDiffOn_Icc_of_hasDerivAt`).** Let $E$ be a complete real normed space and $t \mapsto A(t)$
a continuous map from $\mathbb R$ to the continuous linear maps $E \to E$. (i) For every
$t_0 \in \mathbb R$ and $x_0 \in E$ there is a solution of $x' = A(t)x$ on all of $\mathbb R$ with
$x(t_0) = x_0$; the solution with value $\xi$ at $s$ depends linearly on $\xi$. (ii) If $a < b$ and
$f$ is continuous on $[a, b]$ and solves the equation on $(a, b)$, then for every $s \in [a, b]$,
end points included, $f$ agrees on $[a, b]$ with the solution whose value at $s$ is $f(s)$.
(iii) If $A$ is $C^\infty$ on $[a, b]$ (one-sided derivatives at the ends) and $f'(t) = A(t)f(t)$ at
every $t \in [a, b]$, then $f$ is $C^\infty$ on $[a, b]$. *Book:* p. 77: the Jacobi equation, a
linear second-order equation, has $2n$ linearly independent solutions, each "defined throughout
$\gamma$", all of class $C^\infty$, and a Jacobi field is determined by $J(0)$ and
$\frac{DJ}{dt}(0)$; no proof. *Hidden hypotheses:* a global existence theorem for linear equations;
the local theorem gives solutions on intervals of length about $1/\sup\|A\|$ only. *Deviation
(stronger):* any continuous coefficients on any complete space, extending V6.7 (ii), where they had
to be skew-adjoint. *Proof:* the equation is truncated radially outside a ball and solved on compact
intervals by Picard–Lindelöf; Grönwall's inequality, forward and backward in time, bounds the
solution so that the truncation is never active (the exposition uses Picard iteration on the whole
interval); (iii) is a bootstrap.

**V9.2 (Jacobi fields and the Jacobi system; `Morse.jacobiExpr`, `Morse.IsJacobiField`,
`Morse.curvAlong`, `Morse.jacS`, `Morse.jacSys`, `Morse.IsSmoothCurveIn.contDiffOn_jacSys`,
`Morse.IsSmoothCurveIn.continuous_jacA`, `Morse.jacSol`, `Morse.jacSol_mem_tanAt`, `Morse.isJacobiField_jacSol`,
`Morse.IsJacobiField.eqOn_jacSol`, `Morse.IsJacobiField.eqOn_zero`).** For maps $\gamma$ and $J$ the
Jacobi operator is $\frac{D^2J}{dt^2} + R(V, J)V$, $V = \gamma'$, with $D/dt$ of V8.7. $J$ is a
*Jacobi field along $\gamma$* if it is $C^\infty$ on $[0, 1]$ (one-sided derivatives at the ends),
tangent along $\gamma$ ($J(t) \in T_{\gamma(t)}N$ for $t \in [0, 1]$), and
$$\frac{D^2J}{dt^2} + R(V, J)V = 0 \quad\text{on } (0, 1).$$
Let $\gamma$ be a smooth curve in $N$ on $[0, 1]$, $S = P'P - PP'$ and $K(t)v = R(V, P(t)v)V$. The
Jacobi system is the first-order linear system $J' = SJ + Y$, $Y' = SY - KJ$ for $(J, Y)$ in
$V \times V$; its coefficients are smooth on $[0, 1]$, and extended to $\mathbb R$ as constants they
are continuous, so its solution with any value $\zeta$ at any time $s$ exists on $\mathbb R$ (V9.1).
If $s \in [0, 1]$ and $\zeta = (x, y)$ with $x, y \in T_{\gamma(s)}N$, both components of this
solution stay tangent on $[0, 1]$, the first is a Jacobi field and the second is its covariant
derivative there. Conversely, for every Jacobi field $J$ and every $s \in [0, 1]$, $(J,
\frac{DJ}{dt})$ agrees on $[0, 1]$ with the solution whose value at $s$ is $(J(s),
\frac{DJ}{dt}(s))$; in particular a Jacobi field with $J(s) = 0$ and $\frac{DJ}{dt}(s) = 0$ vanishes
on $[0, 1]$. *Book:* p. 77: a vector field $J$ along a geodesic $\gamma$ is a Jacobi field if it
satisfies the Jacobi equation; in orthonormal parallel fields $P_1, \dots, P_n$ along $\gamma$,
$J = \sum f^iP_i$, it becomes a linear system with coefficients $\langle R(V, P_j)V, P_i\rangle$; a
Jacobi field is completely determined by its initial conditions $J(0)$, $\frac{DJ}{dt}(0)$.
*Hidden hypotheses:* the global solution theory (V9.1); parallel frames along $\gamma$ (Lemma 8.2),
which V6.8 provides only for curves defined on all of $\mathbb R$. *Deviation (restated):* no frame:
the unknown is $(J, \frac{DJ}{dt})$ in $V \times V$, and the term $S$ (the device of V6.8) keeps
solutions with tangent initial values tangent, their normal parts $(1 - P)J$, $(1 - P)Y$ solving a
homogeneous linear system and vanishing at $s$. *Deviation (stronger):* along any smooth curve in
$N$, not only along a geodesic, and with initial values at any $s \in [0, 1]$.

**V9.3 (the space of Jacobi fields, the exposition's Corollary 14.B; `Morse.jacobiSpace`,
`Morse.IsJacobiField.comp_projIcc_mem`, `Morse.jacobiSpace_eq_zero`, `Morse.jacEval`,
`Morse.jacEval_bijective`, `Morse.jacEquiv`, `Morse.finrank_jacobiSpace`, `Morse.exists_jacobi`).**
Let $\gamma$ be a smooth curve in $N$ on $[0, 1]$. $\mathcal J(\gamma)$ is the vector space of the
Jacobi fields along $\gamma$ that are constant off $[0, 1]$ ($J(t) = J(0)$ for $t < 0$ and
$J(t) = J(1)$ for $t > 1$); every Jacobi field agrees on $[0, 1]$ with one of them, and an element of
$\mathcal J(\gamma)$ vanishing on $[0, 1]$ is $0$. For every $s \in [0, 1]$, $J \mapsto (J(s),
\frac{DJ}{dt}(s))$ is a linear isomorphism $\mathcal J(\gamma) \to T_{\gamma(s)}N \times
T_{\gamma(s)}N$: every pair of tangent vectors at $\gamma(s)$ is the value and covariant derivative
at $s$ of exactly one field of $\mathcal J(\gamma)$, and $\dim\mathcal J(\gamma) = 2n$. *Book:* p.
77: "$2n$ linearly independent solutions", determined by $J(0)$ and $\frac{DJ}{dt}(0)$. *Hidden
hypotheses:* that every pair of initial values occurs (global existence, V9.1). *Deviation
(stronger):* the isomorphism at every $s \in [0, 1]$, along any smooth curve in $N$.

**V9.4 (conjugate parameters and their multiplicity; `Morse.IsConjugate`, `Morse.conjSpace`,
`Morse.conjMultiplicity`, `Morse.isConjugate_iff`).** Let $\gamma$ be a smooth curve in $N$ on
$[0, 1]$. Parameters $a$ and $b$ are *conjugate along $\gamma$* if $a, b \in [0, 1]$, $a \ne b$, and
some Jacobi field along $\gamma$ vanishes at $a$ and at $b$ without vanishing identically on
$[0, 1]$. Their *multiplicity* is the dimension of the space of fields of $\mathcal J(\gamma)$
vanishing at $a$ and $b$ (finite, by V9.3); for $a \ne b$ in $[0, 1]$ they are conjugate iff the
multiplicity is positive. Below, $\nu(t)$ is the multiplicity of $0$ and $t$, which is $0$ for
$t \in (0, 1]$ not conjugate to $0$. *Book:* p. 77: for $a \ne b$, $p = \gamma(a)$ and
$q = \gamma(b)$ are conjugate along $\gamma$ if a non-zero Jacobi field vanishes for $t = a$ and
$t = b$, and the multiplicity is the dimension of the vector space of all such fields; footnote: if
$\gamma$ has self-intersections, one should say that the parameter values $a$ and $b$ are
conjugate. *Hidden hypotheses:* none. *Deviation (restated):* conjugacy is a relation between
parameter values, as the footnote advises; in §15 "the conjugate points $\gamma(t)$" are read as the
conjugate parameters $t$.

**V9.5 (Theorem 14.1: the null vectors of $E_{**}$ are the Jacobi fields;
`Morse.IsJacobiField.mem_pathTangent`, `Morse.IsJacobiField.secondVariation_eq_zero`,
`Morse.jacobiExpr_eq_zero_of_null`, `Morse.jump_eq_prj_jump`, `Morse.jump_eq_zero_of_null`,
`Morse.deriv_deriv_eq_of_jacobiExpr`, `Morse.smooth_near_of_null`, `Morse.theorem_14_1`).** Let
$\gamma \in \Omega(N; p, q)$ be a geodesic (V8.10) and $W_1 \in T\Omega_\gamma$. Then
$E_{**}(W_1, W_2) = 0$ for every $W_2 \in T\Omega_\gamma$ iff $W_1$ is a Jacobi field along $\gamma$;
in particular such a $W_1$ is $C^\infty$ on all of $[0, 1]$. The steps: a Jacobi field vanishing at
$0$ and $1$ lies in $T\Omega_\gamma$, and for a Jacobi field $J$ (along any curve) $\Phi(J, Y) = 0$
for every field $Y$ (V8.13); for a null vector $W_1$, the Jacobi operator of $W_1$ vanishes off its
break points, and at every $t \in (0, 1)$ the jump of $W_1'$ is tangent and vanishes; for a smooth
tangent field the Jacobi equation gives the second-order equation $W'' = -P(P'W') - R(V, W)V +
(1 - P)(P''W + 2P'W')$ in $V$; and $W_1$ is $C^\infty$ near every point of $(0, 1)$. *Book:* p. 78,
Theorem 14.1 (first sentence); proof pp. 78–79: a Jacobi field vanishing at the ends lies in the
null space by the second variation formula; conversely, testing against $W_2 = f(t)(\frac{D^2W_1}
{dt^2} + R(V, W_1)V)$, $f$ vanishing exactly at the break points, makes $W_1$ a Jacobi field on each
piece, testing against a field $W_2'$ with $W_2'(t_i) = \Delta_{t_i}\frac{DW_1}{dt}$ shows that
$\frac{DW_1}{dt}$ has no jumps, and the pieces "fit together" since a solution is determined by
$W_1(t_i)$ and $\frac{DW_1}{dt}(t_i)$. *Hidden hypotheses:* the field $W_2'$ with prescribed values
at the break points has to be constructed; fitting the pieces together needs Jacobi fields along all
of $\gamma$ with given initial values (V9.2), stated in the book without proof. *Deviation
(restated):* in $V$, the absence of jumps of $\frac{DW_1}{dt} = PW_1'$ makes $W_1$ of class $C^1$ only
because the normal parts of the two one-sided derivatives agree (both are $\mathrm{II}(V, W_1)$).
*Proof:* the test fields are bump functions, supported inside one piece or centred at one break
point, times $\frac{D^2W_1}{dt^2} + R(V, W_1)V$ or times the tangent projection of the jump; the
pieces are joined by a local argument instead of the uniqueness of Jacobi fields: the second-order
equation above holds on both sides of a former break point $x$, with a right side continuous across
$x$, so $W_1'$ is differentiable at $x$, and a solution of a smooth second-order equation is
$C^\infty$ (a bootstrap).

**V9.6 (Theorem 14.1: the null space and the nullity; `Morse.restrictIcc`, `Morse.hessNullSpace`,
`Morse.hessNullity`, `Morse.hessNullSpace_eq`, `Morse.theorem_14_1_nullity`,
`Morse.hessNullity_pos_iff`).** For $\gamma \in \Omega(N; p, q)$, the *null space* of $E_{**}$ is the
space of the restrictions to $[0, 1]$, extended as constants, of the $W_1 \in T\Omega_\gamma$ with
$E_{**}(W_1, W_2) = 0$ for all $W_2 \in T\Omega_\gamma$, and the *nullity* $\nu$ is its dimension. If
$\gamma$ is a geodesic, the null space is the space of fields of $\mathcal J(\gamma)$ vanishing at
$0$ and $1$; so $\nu$ is the multiplicity of $0$ and $1$ (V9.4), in particular finite, and $\nu > 0$
($E_{**}$ is degenerate) iff $0$ and $1$ are conjugate along $\gamma$. *Book:* pp. 77–78: the null
space of $E_{**}$ is the space of the $W_1 \in T\Omega_\gamma$ with $E_{**}(W_1, W_2) = 0$ for all
$W_2$, the nullity $\nu$ is its dimension, and $E_{**}$ is degenerate if $\nu > 0$; p. 78, Theorem
14.1: hence $E_{**}$ is degenerate iff $p$ and $q$ are conjugate along $\gamma$, and the nullity is
their multiplicity; p. 79: the nullity is always finite. *Hidden hypotheses:* finiteness needs the
identification with a subspace of the $2n$-dimensional $\mathcal J(\gamma)$ (V9.3). *Deviation
(restated):* the fields of $T\Omega_\gamma$ (V8.1) are maps on $\mathbb R$ whose values off $[0, 1]$
play no role, so the literal kernel of the formal $E_{**}$ contains every field vanishing on
$[0, 1]$ and is infinite-dimensional; the null space is therefore taken modulo the values off
$[0, 1]$. "$p$ and $q$ conjugate" reads "$0$ and $1$ conjugate" (V9.4).

**V9.7 (Remark 14.2; `Morse.finrank_jacobiSpace_zero`, `Morse.isJacobiField_smul_vel`,
`Morse.eq_const_of_velAlong_one_eq_zero`, `Morse.isJacobiField_const_curve`, `Morse.remark_14_2`).**
Along a smooth curve $\gamma$ in $N$ on $[0, 1]$, the fields of $\mathcal J(\gamma)$ vanishing at $0$
form a space of dimension $n$. If $\gamma$ is moreover a geodesic on $(0, 1)$, then $t \mapsto tV(t)$
is a Jacobi field, and $\gamma$ is constant on $[0, 1]$ if $V(1) = 0$; along a constant curve,
$t \mapsto ty$ is a Jacobi field for every tangent vector $y$. Hence, for a geodesic
$\gamma \in \Omega(N; p, q)$ and $n \ge 1$, the nullity of $E_{**}$ (V9.6) satisfies $\nu < n$.
*Book:* p. 79, Remark 14.2: $0 \le \nu < n$; the Jacobi fields vanishing at $t = 0$ form a space of
dimension precisely $n$, and $J_t = tV_t$ is a Jacobi field vanishing at $0$ but not at $1$.
*Hidden hypotheses:* $J_1 = V_1 \ne 0$ requires $\gamma$ to be non-constant, and $\nu < n$ requires
$n \ge 1$ (for $n = 0$, $\nu = 0 = n$). *Deviation (stronger):* the constant geodesic ($p = q$) is
included, with $ty$, $y \ne 0$, in place of $tV$.

**V9.8 (Lemma 14.3; `Morse.IsJacobiField.congr_curve`, `Morse.lemma_14_3`).** Let $\varepsilon > 0$
and let $\alpha(u, t)$ be $C^\infty$ on $(-\varepsilon, \varepsilon) \times [0, 1]$ (one-sided
derivatives along the edges $t = 0, 1$), with values in $N$ there, such that each
$t \mapsto \alpha(u, t)$, $|u| < \varepsilon$, is a geodesic on $(0, 1)$ (V7.1). Then
$W(t) = \frac{\partial\alpha}{\partial u}(0, t)$ is a Jacobi field along $\alpha(0, \cdot)$. Being a
Jacobi field along $\gamma$ depends only on $\gamma$ on $[0, 1]$. *Book:* p. 79: a variation of
$\gamma$ through geodesics, not necessarily keeping the end points fixed, is a $C^\infty$ map
$\alpha : (-\varepsilon, \varepsilon) \times [0, 1] \to M$ with $\alpha(0, t) = \gamma(t)$ and each
$\bar\alpha(u)$ a geodesic; p. 80, Lemma 14.3: its variation field is a Jacobi field; proof: apply
$\frac{D}{\partial u}$ to $\frac{D}{\partial t}\frac{\partial\alpha}{\partial t} = 0$ and use Lemmas
9.2 and 8.7. *Hidden hypotheses:* Lemmas 9.2 and 8.7 are applied to a map defined on a strip and
smooth up to its edges (V8.12). *Proof:* Milnor's, with the identity (13.3) of V8.12 on the open
strip $(-\varepsilon, \varepsilon) \times (0, 1)$; the smoothness of $W$ up to $t = 0, 1$ comes from
that of $\alpha$ on the closed strip.

**V9.9 (Lemma 14.4; `Morse.exists_smooth_ray`, `Morse.exists_initial_ray`, `Morse.RaysGood`,
`Morse.raysGood_of_isGeodesicOn`, `Morse.lemma_14_4`).** (i) For $x_1 \in N$ and $R > 0$ there are
an open set $U \ni x_1$ of $V$, an $h > 0$ and a map $\Phi(y, w, t)$, $C^\infty$ on
$U \times \{\|w\| < R\} \times (-h, h)$, such that for $y \in N \cap U$ and $w \in T_yN$ with
$\|w\| < R$, $t \mapsto \exp_y(tw)$ is a geodesic on $(-h, h)$, equal to $\Phi(y, w, t)$ there.
(ii) A smooth curve $\gamma$ in $N$ on $[0, 1]$ that is a geodesic on $(0, 1)$ agrees on $[0, 1]$
with $t \mapsto \exp_{\gamma(0)}(tV(0))$, which is a geodesic on an open interval containing
$[0, 1]$; this is the extension of a geodesic segment past its end points that V7.7 leaves
unformalized. (iii) Let $c, w$ be $C^\infty$ on an open set $U_0 \ni 0$ of $\mathbb R$, with
$c(u) \in N$ and $w(u) \in T_{c(u)}N$. If $t \mapsto \exp_{c(0)}(tw(0))$ is a geodesic on
$(-\delta, B + \delta)$, $B \ge 0$, $\delta > 0$, there are $\varepsilon, \eta > 0$ such that every
$t \mapsto \exp_{c(u)}(tw(u))$, $|u| < \varepsilon$, is a geodesic on $(-\eta, B + \eta)$ and
$(u, t) \mapsto \exp_{c(u)}(tw(u))$ is $C^\infty$ on $(-\varepsilon, \varepsilon) \times (-\eta,
B + \eta)$. (iv) **Lemma 14.4:** let $\gamma$ be a smooth curve in $N$ on $[0, 1]$ that is a geodesic
on $(0, 1)$, and $J$ a Jacobi field along $\gamma$. There are $\varepsilon > 0$ and a map $\alpha$
satisfying the hypotheses of Lemma 14.3 (V9.8) on $(-\varepsilon, \varepsilon) \times [0, 1]$, with
$\alpha(0, t) = \gamma(t)$ and $\frac{\partial\alpha}{\partial u}(0, t) = J(t)$ for $t \in [0, 1]$.
*Book:* p. 81, Lemma 14.4: every Jacobi field along a geodesic $\gamma : [0, 1] \to M$ may be
obtained by a variation of $\gamma$ through geodesics. Proof: take a neighbourhood $U$ of
$\gamma(0)$ in which any two points are joined by a unique minimal geodesic depending
differentiably on the end points, and $\delta$ with $\gamma(t) \in U$ for $0 \le t \le \delta$;
minimal geodesics between the points of curves $a(u)$, $b(u)$ give Jacobi fields along
$\gamma|[0, \delta]$ with arbitrary values at $0$ and $\delta$, so $J \mapsto (J(0), J(\delta))$ is
onto, hence an isomorphism (both spaces have dimension $2n$); "using the compactness of $[0, 1]$",
the geodesics extend over $[0, 1]$ for small $u$. *Hidden hypotheses:* the construction returns
$\bar\alpha(0) = \gamma|[0, \delta]$ only if $\gamma|[0, \delta]$ is *the* minimal geodesic from
$\gamma(0)$ to $\gamma(\delta)$, which $\gamma([0, \delta]) \subseteq U$ does not say; for Milnor's
$U$ it is true, by an argument the book omits (the exposition supplies it after its Lemma 14.4, and
ensures it directly by a bound on the length of $\gamma|[0, \delta]$); the compactness step is the
smooth dependence of geodesics on their initial data over a compact interval, (iii), with the
openness of the domain of $\exp$, neither among the statements of §10; and that the extended
variation still has $J$ as variation field needs the uniqueness of Jacobi fields (V9.2). *Proof:*
departs from Milnor's. The variation is built from initial data: $\alpha(u, t) = \exp_{c(u)}(t\,
w(u))$ with $c(u) = \exp_{\gamma(0)}(uJ(0))$ and $w(u) = P_{c(u)}(V(0) + u\frac{DJ}{dt}(0))$. It is
defined and smooth on $(-\varepsilon, \varepsilon) \times [0, 1]$ by (i)–(iii); its variation field
is a Jacobi field (V9.8) with value $J(0)$ and covariant derivative $\frac{DJ}{dt}(0)$ at $t = 0$
(by the symmetry of the mixed partials and $PP'P = 0$), hence equals $J$ (V9.2). No minimal
geodesic, restriction to $[0, \delta]$ or dimension count is used: the formal statement has no
minimality hypothesis, and the minimality of $\gamma|[0, \delta]$ is neither assumed nor proved.

**V9.10 (Jacobi fields at two non-conjugate parameters; `Morse.jacEvalEnds`,
`Morse.jacEvalEnds_bijective_of_not_isConjugate`).** Let $\gamma$ be a smooth curve in $N$ on
$[0, 1]$, and $a \ne b$ in $[0, 1]$ parameters that are not conjugate along $\gamma$ (V9.4). Then
$J \mapsto (J(a), J(b))$ is a linear isomorphism $\mathcal J(\gamma) \to T_{\gamma(a)}N \times
T_{\gamma(b)}N$: a Jacobi field is determined by its values at $a$ and $b$, and these values can be
prescribed. *Book:* p. 81, in the proof of Lemma 14.4: more generally a Jacobi field is determined
by its values at any two non-conjugate points (in parentheses, without proof). *Hidden hypotheses:*
none; injectivity is the definition of non-conjugacy. *Deviation (stronger):* the values can be
prescribed, by the dimension count (V9.3).

**V9.11 (Remark 14.5; `Morse.IsNormalRadius.isSmoothCurveIn_ray`,
`Morse.remark_14_5_of_isNormalRadius`, `Morse.remark_14_5_bijective`, `Morse.remark_14_5`).**
(i) Let $\varepsilon$ be a normal radius at $q \in N$ (V7.9), $v \in T_qN$ and $\|v\| < \varepsilon$.
Then $\sigma(t) = \exp_q(tv)$ is a smooth curve in $N$ on $[0, 1]$; a Jacobi field along $\sigma$
vanishing at $t = 0$ and $t = 1$ vanishes on $[0, 1]$; and $J \mapsto (J(0), J(1))$ is a linear
isomorphism $\mathcal J(\sigma) \to T_qN \times T_{\sigma(1)}N$. (ii) Every $p \in N$ has an open
neighbourhood $O$ in $V$, with an $\varepsilon > 0$, such that for all $q_1, q_2 \in N \cap O$ there
is $v \in T_{q_1}N$ with $\|v\| < \varepsilon$ and $\exp_{q_1}(v) = q_2$, $\varepsilon$ is a normal
radius at $q_1$, and a Jacobi field along $t \mapsto \exp_{q_1}(tv)$ vanishing at both ends vanishes
on $[0, 1]$. *Book:* pp. 81–82, Remark 14.5: the argument of Lemma 14.4 shows that in any such
neighbourhood $U$ the Jacobi fields along a geodesic segment in $U$ are uniquely determined by their
values at the end points. *Hidden hypotheses:* that argument applies to a segment that is the
minimal geodesic between its end points (V9.9). *Deviation (restated):* Milnor's $U$ is replaced by
the neighbourhoods $N \cap O$ of Lemma 10.3 (V7.10), and "a geodesic segment in $U$" by
$t \mapsto \exp_{q_1}(tv)$, $\|v\| < \varepsilon$, the geodesic of V7.15 (ii), which is shortest
among all paths from $q_1$ to $q_2$. *Deviation (stronger):* the end values can be prescribed.
*Proof:* injectivity from the local inverse of $\exp_q$: the Jacobi field with $J(0) = 0$ and
$\frac{DJ}{dt}(0) = w$ is the variation field $t \mapsto d(\exp_q)_{tv}(tw)$ of the variation
$\exp_q(t(v + uw))$ through geodesics (V9.8 and V9.2), and $d(\exp_q)_v$ is injective on $T_qN$
because $\exp_q$ has a smooth inverse near $\exp_q(v)$; surjectivity by the dimension count (V9.3).
Milnor goes the other way: surjectivity from the end-point construction of Lemma 14.4, then the
dimension count.

**V9.12 (Remark 14.6; `Morse.remark_14_6`).** For every smooth curve $\gamma$ in $N$ on $[0, 1]$
there is $\delta > 0$ such that no $t \in (0, \delta)$ is conjugate to $0$ along $\gamma$. *Book:* p. 82, Remark 14.6: the proof also shows
that there is a neighbourhood $(-\delta, \delta)$ of $0$ such that $\gamma(t)$ is not conjugate to
$\gamma(0)$ for $t \in (-\delta, \delta)$; and (by 15.2) the conjugate points of $\gamma(0)$ along
the entire geodesic have no cluster points. *Hidden hypotheses:* in Milnor's argument, as in V9.9,
that $\gamma|[0, t]$ is the minimal geodesic between its end points. *Deviation (narrower):* only
$t > 0$, $\gamma$ being given on $[0, 1]$; the last sentence is not formalized. *Deviation
(stronger):* along any smooth curve in $N$. *Proof:* $\delta = \min(h_0, 1)$, since no two
parameters at distance at most $h_0$ are conjugate (V9.16 (ii)); Milnor's neighbourhood $U$ is not
used.

**V9.13 (the index and the nullity of a bilinear form; `Morse.IsNegDefOn`, `Morse.IsPosDefOn`,
`Morse.formIndex`, `Morse.le_formIndex`, `Morse.exists_isNegDefOn_of_formIndex_eq`,
`Morse.formIndex_le_of_map`, `Morse.formIndex_eq_of_equiv`, `Morse.formIndex_eq_sigNeg`).** Let $B$
be a bilinear form on a real vector space $X$. $B$ is negative (positive) definite on a subspace $S$
if $B(x, x) < 0$ ($> 0$) for every $x \ne 0$ in $S$. The *index* of $B$ is the supremum, in
$\{0, 1, 2, \dots\} \cup \{\infty\}$, of the dimensions of the finite-dimensional subspaces on which
$B$ is negative definite; a finite index is the dimension of such a subspace. A linear map $L$ with
$B'(Lx, Ly) = B(x, y)$ does not decrease the index (it is injective on every negative definite
subspace), so a linear isomorphism carrying $B$ to $B'$ preserves it; on a finite-dimensional space
the index is Mathlib's negative index of inertia (`sigNeg`) of $x \mapsto B(x, x)$, as in V1.3. The
*nullity* of $B$ is the dimension of its null space $\{x : B(x, y) = 0 \text{ for all } y\}$; for
$E_{**}$ the null space is read on $[0, 1]$ (V9.6). *Book:* p. 83: the index $\lambda$ of $E_{**}$
is the maximum dimension of a subspace of $T\Omega_\gamma$ on which $E_{**}$ is negative definite;
p. 5: the index and the nullity of a bilinear functional on a vector space. *Hidden hypotheses:*
that the maximum exists, i.e. is finite; for $E_{**}$ this is part of Theorem 15.1 (V9.19, V9.24).
*Deviation (restated):* a supremum over finite-dimensional subspaces, possibly $\infty$; a negative
definite subspace of infinite dimension contains finite-dimensional ones of every dimension, and so
also gives $\infty$.

**V9.14 (linear algebra, the exposition's Lemmas 15.A and 15.B; `Morse.finrank_add_finrank_le`,
`Morse.exists_isPosDefOn_add`, `Morse.eventually_isNegDefOn`, `Morse.eventually_isPosDefOn`,
`Morse.formIndex_eq_restrict_of_isCompl`, `Morse.ker_eq_map_ker_restrict`,
`Morse.le_formIndex_of_compound`).** Let $B$ be a bilinear form on a real vector space $X$. (1) If
$\dim X = m < \infty$, a negative definite and a positive definite subspace have dimensions adding
up to at most $m$. (2) (Sylvester) If $\dim X = m < \infty$ and $B$ is symmetric, with index
$\lambda$ and nullity $\nu$, then $B$ is positive definite on a subspace of dimension
$m - \lambda - \nu$. (3) If $(B_\tau)$ is a family of bilinear forms on $X$ indexed by a topological
space, $S \subseteq X$ is a finite-dimensional subspace, $\tau \mapsto B_\tau(x, y)$ is continuous at
$\tau_0$ for all $x, y \in S$, and $B_{\tau_0}$ is negative (positive) definite on $S$, then so is
$B_\tau$ for all $\tau$ near $\tau_0$. (4) (Lemma 15.B) If $X = A \oplus C$, $B(a, c) = B(c, a) = 0$
for all $a \in A$, $c \in C$, and $B$ is positive definite on $C$, then $B$ and its restriction to
$A$ have the same index, and the null space of $B$ is that of its restriction to $A$. (5) (Milnor's
compound matrix) If $B$ is symmetric, $U : \mathbb R^\lambda \to X$ is linear with $B(Ua, Ua) < 0$
for $a \ne 0$, and $J, Y : \mathbb R^\nu \to X$ are linear with $B(Jb, Ua) = 0$, $B(Jb, Jb') = 0$ and
$B(Jb, Yb') = 2\langle b, b'\rangle$ for all $a, b, b'$, then the index of $B$ is at least
$\lambda + \nu$. *Book:* used without proof on pp. 85–87: Lemma 15.4 ("the proof is
straightforward"), the persistence of definiteness for $H_{\tau'}$ near $H_\tau$ in Assertions (3)
and (4), a positive definite subspace of dimension $ni - \lambda(\tau) - \nu$, and the compound
matrix, "certainly negative definite" for small $c$. *Hidden hypotheses:* in (5), that a negative
definite Gram matrix makes the $\lambda + \nu$ fields linearly independent. *Deviation (not in the
book):* stated and proved as lemmas. *Proof:* (3) by the compactness of the unit sphere of $S$;
(5) by (3): for small $c \ne 0$, $B$ is negative definite on the image of $(a, b) \mapsto
Ua + c^{-1}Jb - cYb$, whose Gram matrix is a perturbation of the block-diagonal one with blocks
$(B(Ua_i, Ua_j))$ and $-4I$.

**V9.15 (the second variation formula for piecewise Jacobi fields; `Morse.jacobiExpr_congr`,
`Morse.isJacobiField_zero`, `Morse.energyHessian_eq_jumps`).** Let $\gamma \in \Omega(N; p, q)$,
$X, Y \in T\Omega_\gamma$, and $B$ a finite set such that near every $t \in (0, 1) \setminus B$ the
field $X$ agrees with some Jacobi field along $\gamma$ (the zero field is one). Then
$$E_{**}(X, Y) = -2\sum_{b \in B \cap (0, 1)}\Big\langle Y(b), \Delta_b\frac{DX}{dt}\Big\rangle,$$
$\Delta_b\frac{DX}{dt} = P_{\gamma(b)}(\Delta_bX')$ being the jump of $\frac{DX}{dt}$ (V8.13).
$\gamma$ need not be a geodesic. *Book:* p. 84, in the proof of Lemma 15.3: for a broken Jacobi field
$W_1$ and $W_2 \in T'$ the second variation formula reduces to its jump terms; p. 87: by the second
variation formula one sees "easily" the values of $E_{**}(J_h, \cdot)$. *Hidden hypotheses:* none.
*Proof:* the formula of V8.13, whose integrand vanishes off the finite set $B \cup \{1\}$.

**V9.16 (positivity near zeros, and fine subdivisions; `Morse.jacBound`, `Morse.fineMesh`,
`Morse.fineMesh_pos`, `Morse.integrand_ge`, `Morse.integral_norm_sq_le`, `Morse.hessForm_ge`,
`Morse.eqOn_zero_of_hessForm`, `Morse.eq_zero_of_short`, `Morse.jacEvalEnds_bijective`,
`Morse.IsFine`, `Morse.exists_isFine`).** Let $\gamma$ be a smooth curve in $N$ on $[0, 1]$, $C \ge 0$
a bound for $\|P'(t)\|^2 + \|K(t)\|$ on $[0, 1]$ ($K$ as in V9.2), and $h_0 = 1/(C + 1) > 0$.
(i) *A Poincaré estimate.* If $X \in T\Omega_\gamma$ and every $t \in [0, 1]$ has a zero $s \in
[0, t]$ of $X$ with $t - s \le h_0$, then
$$\int_0^1\|X\|^2\,dt \le \int_0^1\Big(\Big\|\frac{DX}{dt}\Big\|^2 - \langle R(V, X)V, X\rangle\Big)
\,dt = \tfrac12E_{**}(X, X)$$
(the equality is V8.15); so $E_{**}(X, X) \le 0$ forces $X = 0$ on $[0, 1]$. (ii) If
$0 \le a < b \le 1$ and $b - a \le h_0$, a field of $\mathcal J(\gamma)$ vanishing at $a$ and $b$ is
$0$, and $J \mapsto (J(a), J(b))$ is a linear isomorphism $\mathcal J(\gamma) \to T_{\gamma(a)}N
\times T_{\gamma(b)}N$; in particular no two parameters at distance at most $h_0$ are conjugate.
(iii) For $\tau > 0$, a finite set $B \subseteq (0, \tau)$ of division points is *fine for
$[0, \tau]$* if consecutive points of $\{0\} \cup B \cup \{\tau\}$ are at most $h_0$ apart; for every
$\tau > 0$ there is one whose last point is within $h_0/2$ of $\tau$. *Book:* p. 83: each
$\gamma(t)$ lies in an open set $U$ in which any two points are joined by a unique minimal geodesic
depending differentiably on the end points (§10), and the subdivision is chosen "sufficiently fine"
that each $\gamma|[t_{i-1}, t_i]$ lies in such a $U$ and is minimal. Milnor uses two consequences:
along each segment the Jacobi fields are determined by their end values, which can be prescribed
(Remark 14.5); and each segment has smaller energy than any other path between its end points
(p. 84). *Hidden hypotheses:* that such subdivisions exist (a Lebesgue number of a finite cover, and
a length bound for minimality, Theorem 10.4). *Deviation (restated):* "sufficiently fine" becomes
the explicit mesh $h_0$, which depends only on bounds for $P'$ and the curvature along $\gamma$;
$\gamma$ need not be a geodesic, and neither $\exp$ nor minimality enters. *Proof:* on a piece
$[s, t]$ starting at a zero, $\|X(t)\|^2 \le L_s^t(X)^2 \le (t - s)E_s^t(X)$ (V7.11, V8.5), whence
$\int_0^1\|X\|^2 \le h_0\int_0^1\|X'\|^2$; and the integrand is at least $\|X'\|^2 - C\|X\|^2$,
since $\|\frac{DX}{dt}\|^2 \ge \|X'\|^2 - \|P'\|^2\|X\|^2$ for a tangent field and
$\langle R(V, X)V, X\rangle \le \|K\|\,\|X\|^2$. For (ii), the field equal to $J$ on $[a, b]$ and to
$0$ elsewhere has $E_{**} = 0$ by V9.15 (its only break points $a$, $b$ are zeros), so it vanishes by
(i); $J$ then vanishes near the midpoint of $[a, b]$, hence everywhere (V9.2).

**V9.17 (fields along $\gamma|[0, \tau]$, broken Jacobi fields, and $T'$; `Morse.fieldsUpTo`,
`Morse.fieldsUpTo_apply_self`, `Morse.IsBrokenJacobi`, `Morse.brokenSpace`, `Morse.nodeZero`,
`Morse.exists_isBrokenJacobi`, `Morse.IsBrokenJacobi.eqOn_zero`, `Morse.exists_brokenSpace_eq`,
`Morse.nodeSpace`, `Morse.nodeEval_bijective`).** Let $\gamma$ be a smooth curve in $N$ on $[0, 1]$.
For $\tau \in \mathbb R$, the *fields along $\gamma|[0, \tau]$* are the fields of $T\Omega_\gamma$
vanishing outside $[0, \tau]$; for $0 \le \tau \le 1$ they vanish at $\tau$. Let $0 < \tau \le 1$ and
$B$ be fine for $[0, \tau]$ (V9.16). A map is a *broken Jacobi field* on $[0, \tau]$ for $B$ if on
each piece between consecutive points of $\{0\} \cup B \cup \{\tau\}$ it agrees with a field of
$\mathcal J(\gamma)$. Milnor's $T\Omega_\gamma(t_0, \dots, t_k)$ is the space of fields along
$\gamma|[0, \tau]$ that are broken Jacobi fields, and his $T'$ the space of fields along
$\gamma|[0, \tau]$ vanishing at the points of $B$. Broken Jacobi fields with arbitrary tangent values
at $0$, $\tau$ and the points of $B$ exist, and one vanishing at all these points vanishes on
$[0, \tau]$; so $W \mapsto (W(b))_{b \in B}$ is a linear isomorphism from the broken Jacobi fields
along $\gamma|[0, \tau]$ onto $\Sigma = \bigoplus_{b \in B}T_{\gamma(b)}N$. *Book:* p. 83:
$T\Omega_\gamma(t_0, \dots, t_k)$, the fields $W$ along $\gamma$ vanishing at $0$ and $1$ with
$W|[t_{i-1}, t_i]$ a Jacobi field along $\gamma|[t_{i-1}, t_i]$ for each $i$, a finite-dimensional
space of broken Jacobi fields; p. 84: $T'$, the fields with $W(t_0) = W(t_1) = \dots = W(t_k) = 0$,
and "it follows from §14.5" that the broken Jacobi field with given values at the $t_i$ exists and is
unique; p. 86: along $\gamma_\tau$, for $0 < t_1 < \dots < t_i < \tau$, the broken Jacobi fields form
a space isomorphic to $\Sigma$, since a broken Jacobi field is determined by its values at the break
points. *Hidden hypotheses:* Remark 14.5 on each segment, and the gluing of the pieces.
*Deviation (restated):* everything is along $\gamma|[0, \tau]$ for every $\tau \in (0, 1]$, as fields
on $[0, 1]$ vanishing outside $[0, \tau]$ (Milnor uses $\tau = 1$ here and $\gamma_\tau$ on p. 86); a
piece is the restriction of a Jacobi field along all of $\gamma$, which is equivalent to being a
Jacobi field along $\gamma|[t_{i-1}, t_i]$ by V9.1–V9.2, an equivalence not stated formally.
*Proof:* existence by induction over the division points, gluing segment by segment with V9.16 (ii);
uniqueness from V9.16 (ii) on each piece.

**V9.18 (Lemma 15.3; `Morse.energyHessian_broken_eq`, `Morse.isCompl_broken_nodeZero`,
`Morse.energyHessian_broken_nodeZero`, `Morse.energyHessian_nodeZero_pos`).** Let $\gamma$ be a
smooth curve in $N$ on $[0, 1]$, $0 < \tau \le 1$ and $B$ fine for $[0, \tau]$. (i) The fields along
$\gamma|[0, \tau]$ are the direct sum of the broken Jacobi fields and $T'$ (V9.17). (ii) For a broken
Jacobi field $W_1$ along $\gamma|[0, \tau]$ and every field $Y$ along $\gamma|[0, \tau]$,
$E_{**}(W_1, Y) = -2\sum_{b \in B}\langle Y(b), \Delta_b\frac{DW_1}{dt}\rangle$; in particular
$E_{**}(W_1, W_2) = 0$ for $W_2 \in T'$. (iii) $E_{**}(W, W) > 0$ for every $W \ne 0$ in $T'$.
*Book:* p. 84, Lemma 15.3: $T\Omega_\gamma = T\Omega_\gamma(t_0, \dots, t_k) \oplus T'$, the two
subspaces are mutually perpendicular with respect to $E_{**}$, and $E_{**}$ restricted to $T'$ is
positive definite; proof pp. 84–85: $W = W_1 + (W - W_1)$; perpendicularity from the second
variation formula; $E_{**}(W, W) \ge 0$ on $T'$ because each $\gamma|[t_{i-1}, t_i]$ is minimal, and
$E_{**}(W, W) = 0$ puts $W$ in the null space, so $W$ is a Jacobi field, and $T'$ contains no Jacobi
field other than $0$. *Hidden hypotheses:* the existence and uniqueness of $W_1$ (V9.17); that $T'$
contains no non-zero Jacobi field needs the uniqueness of Jacobi fields on short segments.
*Deviation (restated):* along $\gamma|[0, \tau]$ for every $\tau \in (0, 1]$ (Milnor's lemma is
$\tau = 1$), for fine subdivisions in the sense of V9.16. *Proof:* (ii) is V9.15; (iii) departs from
Milnor's: a field of $T'$ has a zero within $h_0$ before every point, so V9.16 (i) gives
$E_{**}(W, W) > 0$ directly, without minimal geodesics, variations or Theorem 14.1.

**V9.19 (Lemma 15.4; `Morse.lemma_15_4`, `Morse.lemma_15_4_ker`, `Morse.eq_jacobi_of_jumps_zero`,
`Morse.finrank_ker_broken`, `Morse.finiteDimensional_brokenSpace`, `Morse.indexUpTo_le_finrank`,
`Morse.indexUpTo_lt_top`).** Let $\gamma$,
$\tau$ and $B$ be as in V9.18. The index (V9.13) of $E_{**}$ on the fields along $\gamma|[0, \tau]$
equals its index on the broken Jacobi fields; the null space of $E_{**}$ on the fields along
$\gamma|[0, \tau]$ is the null space of its restriction to the broken Jacobi fields, and the latter
has dimension $\nu(\tau)$ (V9.4), because a broken Jacobi field whose jumps
$\Delta_b\frac{DW}{dt}$ all vanish agrees on $[0, \tau]$ with a single field of $\mathcal J(\gamma)$.
In particular the index is at most the (finite) dimension of the broken Jacobi fields, so it is
finite for every $\tau \in (0, 1]$. *Book:* p. 85, Lemma 15.4: the index (or the nullity) of
$E_{**}$ equals the index (or the nullity) of $E_{**}$ restricted to the broken Jacobi fields; in
particular the index $\lambda$ is always finite; "the proof is straightforward". *Hidden
hypotheses:* the proof is the abstract Lemma 15.B (V9.14 (4)), applied to Lemma 15.3. *Deviation
(restated):* along $\gamma|[0, \tau]$ (Milnor states $\tau = 1$ and applies it to $\gamma_\tau$ on p.
86), and for subdivisions fine in the sense of V9.16 rather than Milnor's; the theorem needs only one
fine subdivision. *Deviation (stronger):* the nullity on the broken Jacobi fields is identified with
$\nu(\tau)$ directly; Milnor gets this on p. 86 from Theorem 14.1 for $\gamma_\tau$.

**V9.20 ($\lambda(\tau)$, Assertions (1) and (2); `Morse.indexUpTo`, `Morse.indexUpTo_one`,
`Morse.indexUpTo_mono`, `Morse.indexUpTo_eq_zero`).** For a smooth curve $\gamma$ in $N$ on
$[0, 1]$ and $\tau \in \mathbb R$, $\lambda(\tau)$ is the index of $E_{**}$ restricted to the fields
along $\gamma|[0, \tau]$ (V9.17); $\lambda(1)$ is the index of $E_{**}$ on all of $T\Omega_\gamma$.
(1) $\lambda(\tau) \le \lambda(\tau')$ for $\tau \le \tau'$. (2) $\lambda(\tau) = 0$ for
$0 < \tau \le h_0$ (V9.16). *Book:* p. 85: $\gamma_\tau = \gamma|[0, \tau]$, a geodesic from
$\gamma(0)$ to $\gamma(\tau)$, and $\lambda(\tau)$ the index of the associated Hessian
$(E_0^\tau)_{**}$, so that $\lambda(1)$ is the index sought; Assertion (1): $\lambda$ is monotone,
because a field along $\gamma_\tau$ vanishing at both ends extends by zero to one along
$\gamma_{\tau'}$; Assertion (2): $\lambda(\tau) = 0$ for small $\tau$, because $\gamma_\tau$ is then a
minimal geodesic (Lemma 13.6). *Hidden hypotheses:* (1) needs the extension by zero to preserve the
Hessian (the integral form, V8.15); (2) needs short geodesics to be minimal (Theorem 10.4).
*Deviation (restated):* $\lambda(\tau)$ is the index of a restriction of $E_{**}$, not of a Hessian
along $\gamma_\tau$ on its own interval (see "How the index, the nullity and $\lambda(\tau)$ are
formalized" above); with this definition (1) is immediate, and no rescaling of $\gamma_\tau$ to
$[0, 1]$ (the exposition's Lemma 13.B) is needed. *Proof:* (2) from V9.16 (i): a field along
$\gamma|[0, \tau]$ with $\tau \le h_0$ has a zero within $h_0$ before every point, so $E_{**}$ is
positive definite on these fields; minimality and Lemma 13.6 are not used.

**V9.21 (the forms $H_\tau$ and their continuity, the exposition's Lemma 15.C; `Morse.validFor`,
`Morse.Hform`, `Morse.Hform_isSymm`, `Morse.formIndex_Hform`, `Morse.finrank_ker_Hform`,
`Morse.brokenOf_eqOn`, `Morse.continuous_linFlow`, `Morse.continuousWithinAt_of_injective`,
`Morse.continuousWithinAt_Hform`, `Morse.mem_validFor_of_near`).** Let $\gamma$ be a smooth curve in
$N$ on $[0, 1]$ and $B$ a finite set; $\tau$ is *valid* for $B$ if $0 < \tau \le 1$ and $B$ is fine
for $[0, \tau]$. For valid $\tau$, $H_\tau$ is the symmetric bilinear form on
$\Sigma = \bigoplus_{b \in B}T_{\gamma(b)}N$ given by $E_{**}$ on the broken Jacobi fields along
$\gamma|[0, \tau]$ with these values at the points of $B$ (V9.17); $H_\tau = 0$ for other $\tau$. For
valid $\tau$, the index of $H_\tau$ is $\lambda(\tau)$ and its nullity is $\nu(\tau)$. For
$x, y \in \Sigma$, $\tau \mapsto H_\tau(x, y)$ is continuous on the set of valid $\tau$. If $B$ is
fine for $[0, \tau]$ and the last point $m$ of $\{0\} \cup B$ is within $h_0/2$ of $\tau$, every
$\tau' \in (m, \tau + h_0/2)$ with $\tau' \le 1$ is valid. *Book:* p. 86: with the subdivision chosen
so that $t_i < \tau < t_{i+1}$, $\lambda(\tau)$ is the index of a quadratic form $H_\tau$ on the
broken Jacobi fields along $\gamma_\tau$ for $0 < t_1 < \dots < t_i < \tau$, a space isomorphic to
$\Sigma = TM_{\gamma(t_1)} \oplus \dots \oplus TM_{\gamma(t_i)}$, which is independent of $\tau$;
"evidently" $H_\tau$ varies continuously with $\tau$. *Hidden hypotheses:* that the subdivision stays
fine for $\tau'$ near $\tau$; and, for the continuity, that $t_i$ and $\tau$ are not conjugate (so
that the Jacobi field with value $x_i$ at $t_i$ and $0$ at $\tau$ exists), the linear dependence of
Jacobi fields on their initial values, and the continuity of the solution of an injective linear
system. *Proof:* by V9.18 (ii), $H_\tau(x, y) = -2\sum_b\langle y_b, \Delta_b\frac{DW_x}{dt}\rangle$;
the broken Jacobi fields for different valid $\tau$ agree up to the last division point $m$, so only
$\frac{DY^\tau}{dt}(m)$ depends on $\tau$, where $Y^\tau$ is the Jacobi field with $Y^\tau(m) = x_m$
and $Y^\tau(\tau) = 0$; its initial vector solves $L(\tau)z = c(\tau)$, with $L$ and $c$ continuous
(propagators of V9.1) and $L(\tau_0)$ injective because $m$ and $\tau_0$ are closer than $h_0$ (V9.16
(ii)), and the solution of such a system is continuous at $\tau_0$. This replaces Cramer's rule in
the exposition's proof.

**V9.22 (Assertion (3); `Morse.assertion_3`).** For a smooth curve $\gamma$ in $N$ on $[0, 1]$ and
$0 < \tau \le 1$: $\lambda(\tau') = \lambda(\tau)$ for all $\tau' < \tau$ close enough to $\tau$.
*Book:* p. 85, Assertion (3): $\lambda(\tau - \varepsilon) = \lambda(\tau)$ for all sufficiently small
$\varepsilon > 0$; proof p. 86: $H_\tau$ is negative definite on a subspace of $\Sigma$ of dimension
$\lambda(\tau)$, hence so is $H_{\tau'}$ for $\tau'$ near $\tau$, giving $\lambda(\tau') \ge
\lambda(\tau)$, and Assertion (1) gives the reverse inequality for $\tau' < \tau$. *Hidden
hypotheses:* that $\lambda(\tau)$ is finite and attained (V9.13, V9.19). *Proof:* Milnor's, with
V9.21 and V9.14 (3).

**V9.23 (Assertion (4); `Morse.assertion_4_le`, `Morse.energyHessian_cut`, `Morse.exists_dual`,
`Morse.assertion_4_ge`, `Morse.assertion_4`).** Let $\gamma$ be a smooth curve in $N$ on $[0, 1]$ and
$0 < \tau < 1$. (i) $\lambda(\tau') \le \lambda(\tau) + \nu(\tau)$ for all $\tau' > \tau$ close enough
to $\tau$. (ii) If $J \in \mathcal J(\gamma)$ vanishes at $0$ and $\tau$, and $\hat J$ equals $J$ on
$[0, \tau]$ and $0$ elsewhere, then $E_{**}(\hat J, Z) = 2\langle Z(\tau), \frac{DJ}{dt}(\tau)
\rangle$ for every $Z \in T\Omega_\gamma$. (iii) Linearly independent tangent vectors
$d_1, \dots, d_\nu$ at a point of $N$ have tangent vectors $x_1, \dots, x_\nu$ there with
$\langle d_h, x_k\rangle = \delta_{hk}$. (iv) $\lambda(\tau') \ge \lambda(\tau) + \nu(\tau)$ for every
$\tau' \in (\tau, 1]$. Hence $\lambda(\tau') = \lambda(\tau) + \nu(\tau)$ for all $\tau' > \tau$ close
enough to $\tau$. *Book:* p. 86, Assertion (4): if $\nu$ is the nullity of $(E_0^\tau)_{**}$, then
$\lambda(\tau + \varepsilon) = \lambda(\tau) + \nu$ for all sufficiently small $\varepsilon > 0$.
Proof of $\le$ (p. 86): $H_\tau$ is positive definite on a subspace of dimension
$ni - \lambda(\tau) - \nu$, hence so is $H_{\tau'}$ for $\tau'$ near $\tau$. Proof of $\ge$
(pp. 86–87): with $W_1, \dots, W_\lambda$ spanning a space on which $(E_0^\tau)_{**}$ is
negative definite, $J_1, \dots, J_\nu$ independent Jacobi fields vanishing at $0$ and $\tau$, and
fields $X_k$ with $\langle\frac{DJ_h}{dt}(\tau), X_k(\tau)\rangle = \delta_{hk}$, all extended by
$0$ beyond $\tau$,
the fields $W_i$, $c^{-1}J_h - cX_h$ span a $(\lambda + \nu)$-dimensional space on which
$(E_0^{\tau+\varepsilon})_{**}$ is negative definite, for small $c$. *Hidden hypotheses:* for $\le$,
Sylvester's law of inertia and the fact that the nullity of $H_\tau$ is $\nu(\tau)$ (Lemma 15.4 and
Theorem 14.1 for $\gamma_\tau$); for $\ge$, the linear independence of the $\frac{DJ_h}{dt}(\tau)$
(uniqueness, V9.2), the construction of the $X_k$, and the linear independence of the
$\lambda + \nu$ fields (V9.14 (5)). *Deviation (restated):* $\nu$ is $\nu(\tau)$, the multiplicity of
$0$ and $\tau$ (V9.4), which is the nullity of $E_{**}$ along $\gamma|[0, \tau]$ by V9.19 and V9.21.
*Deviation (stronger):* (iv) holds for every $\tau' \in (\tau, 1]$, not only for $\tau'$ near $\tau$.
*Proof:* Milnor's, with V9.14 (1)–(3) and (5); (ii) is V9.15, and the fields $X_k$ are a bump
function times the vectors of (iii).

**V9.24 (Theorem 15.1, the Morse index theorem; `Morse.eq_finsum_of_jumps`,
`Morse.indexUpTo_one_eq`, `Morse.theorem_15_1`).** (i) Let $\ell, \nu : \mathbb R \to
\{0, 1, 2, \dots\}$ and $h_0 > 0$, with $\ell$ non-decreasing on $(0, 1]$, $\ell = 0$ on
$(0, h_0]$, $\ell(\tau') = \ell(\tau)$ for $\tau' < \tau$ near $\tau$ (for $0 < \tau \le 1$), and
$\ell(\tau') = \ell(\tau) + \nu(\tau)$ for $\tau' > \tau$ near $\tau$ (for $0 < \tau < 1$). Then
$\nu(t) \ne 0$ for only finitely many $t \in (0, 1)$, and $\ell(1) = \sum_{0 < t < 1}\nu(t)$.
(ii) For every smooth curve $\gamma$ in $N$ on $[0, 1]$, $\nu(t) \ne 0$ for only finitely many
$t \in (0, 1)$, and $\lambda(1) = \sum_{0 < t < 1}\nu(t)$. (iii) **Theorem 15.1:** let
$\gamma \in \Omega(N; p, q)$ be a geodesic (V8.10). The parameters $t \in (0, 1)$ conjugate to $0$
along $\gamma$ form a finite set, and the index of $E_{**}$ on $T\Omega_\gamma$ (V9.13) is
$$\lambda = \sum_{0 < t < 1}\nu(t),$$
the number of these parameters, each counted with its multiplicity (V9.4); in particular $\lambda$
is finite. *Book:* p. 83, Theorem 15.1 (Morse): the index $\lambda$ of $E_{**}$ is equal to the
number of points $\gamma(t)$, $0 < t < 1$, conjugate to $\gamma(0)$ along $\gamma$, each counted with
its multiplicity, and is always finite; p. 87: the theorem "clearly follows" from Assertions (2), (3)
and (4). *Hidden hypotheses:* the finiteness of the set of conjugate parameters has to be proved
first (from Assertions (1) and (4) and the finiteness of $\lambda(1)$), before the jumps can be
added up; then $\lambda(\tau) - \sum_{t < \tau}\nu(t)$ is locally constant on $(0, 1]$, hence
constant, and it vanishes for small $\tau$, where Assertion (4) also excludes conjugate parameters.
*Deviation (restated):* parameters for points (V9.4). *Deviation (stronger):* (ii) holds along any
smooth curve in $N$; when $\gamma$ is not a geodesic, $E_{**}$ is the form of V8.14, not the
Hessian of the energy. *Proof:* (i) applied to $\ell = \lambda$ and $\nu$, by Assertions (1)–(4)
(V9.20, V9.22, V9.23); $\lambda(1)$ is the index on all of $T\Omega_\gamma$ (V9.20).

**V9.25 (Corollary 15.2; `Morse.corollary_15_2`).** For a geodesic $\gamma \in \Omega(N; p, q)$,
the set of parameters conjugate to $0$ along $\gamma$ is finite. *Book:* p. 83, Corollary 15.2, "an
immediate consequence": a geodesic segment $\gamma : [0, 1] \to M$ contains only finitely many points
conjugate to $\gamma(0)$ along $\gamma$. *Hidden hypotheses:* none. *Deviation (restated):*
parameters for points (V9.4). *Proof:* V9.24, plus the parameter $t = 1$.

### What is not verified in this chapter

- **Examples 1 and 2** (pp. 79–80): along a flat manifold no two points are conjugate; on $S^n$,
  antipodal points are conjugate along a great semicircle with multiplicity $n - 1$, an upper bound
  that needs Remark 14.2. Not formalized in this chapter. Chapter 10 proves Example 2, for every
  great circle and every parameter (V10.23: `Morse.isJacobiField_sin_smul`,
  `Morse.conjMultiplicity_greatCircle`), and Example 1 for the open subsets of a Euclidean space
  (V10.27: `Morse.not_isConjugate_of_top`); a flat manifold embedded with positive codimension is
  not covered.
- **Remark 14.6 for $t < 0$, and its last sentence** (p. 82): the conjugate points of $\gamma(0)$
  along an entire geodesic have no cluster points. The geodesics of $\Omega$ are given on $[0, 1]$,
  and the reparametrization of a geodesic to $[0, 1]$ (the exposition's Lemma 14.C) is not
  formalized.
- **Milnor's subdivisions** (p. 83): Lemmas 15.3–15.4 are proved for subdivisions of mesh at most
  $h_0$ (V9.16), not for his subdivisions into minimal segments inside neighbourhoods $U$; the
  theorem needs only one fine subdivision.
- **$\lambda(\tau)$ as the index of the Hessian of $\gamma_\tau$ on $[0, \tau]$**: no Hessian on
  $[0, \tau]$ is formalized, nor the exposition's Lemma 13.B; $\lambda(\tau)$ is defined by
  restriction (V9.20).
- **The index of $E_{**}$ at a minimal geodesic** (p. 76, Lemma 13.6, "hence the index $\lambda$ of
  $E_{**}$ is zero"): positive semi-definiteness is V8.18, and the index is now defined (V9.13), but
  the vanishing of the index is not stated formally.
- **The exposition's §5** (the index of every great-circle route on $S^n$, the explicit matrix on
  $S^2$, the optics remark) and its interactive figure: not formalized in this chapter; the index
  $k(n - 1)$ of the geodesics joining two non-antipodal points of $S^n$ is V10.23.
- **§§14–15 on an abstract Riemannian manifold**: only for submanifolds of a Euclidean space with the
  induced metric; Nash's embedding theorem is quoted, not proved.

---

## 11. Chapter 10 (Milnor §§16–17): partly verified

Milnor's §16 (pp. 88–92) topologizes the path space $\Omega = \Omega(M; p, q)$ of a connected
Riemannian manifold by a metric $d$ for which the energy $E$ is continuous and, for complete $M$,
replaces the paths of energy less than $c$ by the finite-dimensional manifold $B$ of broken
geodesics with fixed break times (Lemma 16.1). The energy $E' = E|B$ is smooth, its sublevel sets
$B^a$, $a < c$, are compact deformation retracts of the sets $\Omega^a$, and its critical points are
the geodesics, with the index and nullity of $E_{**}$ (Theorem 16.2); so $\Omega^a$ has the homotopy
type of a finite CW-complex with one $\lambda$-cell for each geodesic in $\Omega^a$ of index
$\lambda$ (Theorem 16.3), and a minimum of $E'$ is a minimal geodesic (the Remark on p. 92). §17
(pp. 93–97) shows that the inclusion of $\Omega$ into the space $\Omega^*$ of continuous paths is a
homotopy equivalence (Theorem 17.1), so that $\Omega$ has the homotopy type of a CW-complex
(Corollary 17.2); proves the fundamental theorem (Theorem 17.3: for complete $M$ and $p, q$ not
conjugate along any geodesic, $\Omega$ has the homotopy type of a countable CW-complex with one
$\lambda$-cell for each geodesic from $p$ to $q$ of index $\lambda$); finds the cells of the loop
space of $S^n$ (Corollary 17.4) and its homology for $n > 2$; and concludes that two non-conjugate
points of a manifold of the homotopy type of $S^n$, $n > 2$, are joined by infinitely many geodesics
(Corollary 17.5), with a Remark citing Serre. Verified, for a submanifold $N$ of a Euclidean space
with the induced metric, in the embedded setting of Chapters 6–9: Milnor's metric, a pseudometric on
paths given as maps on $\mathbb R$, with the exposition's Lemmas 16.A and 16.B; Lemma 16.1; all of
Theorem 16.2, with the continuity of Milnor's deformation $r_u$ (the exposition's Lemma 16.C);
Theorem 16.3, for a level $a$ that is not the energy of a geodesic; the Remark on p. 92 for the
energy; Theorem 17.1, for every $N$; Theorem 17.3 for $\Omega$, with $N$ closed in the Euclidean
space; Corollary 17.4 for the path space $\Omega(S^n; p, q)$, $q \ne \pm p$, $n \ge 2$, and its
homology over every field for $n \ge 3$; and the example $\mathbb R^{n+1} \setminus \{0\}$, which
shows that Corollary 17.5 needs the completeness Milnor omits. Every Riemannian manifold is such an
$N$ by Nash's embedding theorem, which is quoted, not proved. As in Part I and the Appendix, a
"CW-complex" is an iterated adjunction space, or a mapping telescope of such spaces, whose attaching
maps need not be cellular (V2.11, VA.18). Proved more sharply than in the book: Lemma 16.1 without
Milnor's hypothesis $\Omega^c \ne \emptyset$ (V10.4). **One step of the printed proof of Theorem 17.1 does
not hold as we read it:** Milnor's "Clearly $h$ is continuous" (p. 94) fails for the metric $d$ of
$\Omega$; the theorem is true, and it is verified with the exposition's modified proof (V10.19). The
proofs depart from Milnor's in three further places. **Lemma 15.4 is proved anew for the subdivision
of §16**, which need not be fine in the sense of §15 (V10.10). **Theorem 16.3 applies Theorem 3.5 to
a compact sublevel set** of a smooth extension of $E'$ (V10.12). **Theorem 17.3 takes Milnor's
second route**, Theorem A of the Appendix, with a tower that commutes only up to homotopy, so that
neither Corollary 17.2, Whitehead's theorem nor nested subdivisions are needed (V10.20, V10.22).
Corollary 17.2, for $N$ closed in $V$, and the loop-space form of Corollary 17.4, with the homology
of the loop space of $S^n$ for $n \ge 3$, are obtained by moving the end point to a non-conjugate
one (V10.28–V10.30). **Not verified:** Milnor's own route to Corollary 17.2, Theorem 17.3 for
$\Omega^*$, the homology of the path spaces of $S^2$ and integral homology, Corollary 17.5 itself,
and Serre's remark (the list at the end). Lean: `Morse/Chapter10/`, 30 files of 13,564 lines in all
— for §16 `Product.lean` (220 lines), `Broken.lean` (806), `BrokenPaths.lean` (248),
`BrokenEnergy.lean` (246), `BrokenVariation.lean` (357), `BrokenSplitting.lean` (707),
`BrokenIndex.lean` (424), `SublevelCW.lean` (319), `Finite.lean` (340), `PathMetric.lean` (400),
`Retraction.lean` (528), `RetractionCont.lean` (320), `RetractionConv.lean` (510),
`Deformation.lean` (302), `Omega.lean` (228); for §17 `FullPathSpace.lean` (471), `GoodBalls.lean`
(630), `FullPathDeform.lean` (502), `GoodJoin.lean` (194), `FullPathOmega.lean` (879),
`FullPathTheorem.lean` (113), `RelativeCells.lean` (583), `FundamentalTheorem.lean` (561),
`SublevelHomology.lean` (534), `PathHomology.lean` (553), `SphereGeodesics.lean` (881),
`SpherePaths.lean` (107), `Incomplete.lean` (591), `CWType.lean` (199).

**The embedded setting.** As in Chapters 8 and 9: $V$ is a finite-dimensional real inner product
space and $N \subseteq V$ a slice submanifold modelled on $Z$ with complement $W$ (V1.6), with the
induced metric and its distance $\rho$ (V7.18), which satisfies $\|x - y\| \le \rho(x, y)$ (V7.21);
$p, q \in V$. $\Omega = \Omega(N; p, q)$ is the set of maps that are piecewise smooth on $[0, 1]$,
with values in $N$ there, from $p$ to $q$ (V8.1); $E(\omega) = E_0^1(\omega)$ is the energy (V8.5),
$\Omega^a = \{\omega \in \Omega : E(\omega) \le a\}$ and $\operatorname{Int}\Omega^c = \{\omega \in
\Omega : E(\omega) < c\}$. A *geodesic* of $\Omega$ is an unbroken geodesic (V8.10); it has constant
speed, so $E = L^2$ for it, and Milnor's "length $\le \sqrt a$" reads "energy $\le a$". $E_{**}$, its
index and its nullity are those of V8.14, V9.13 and V9.6; at a geodesic the nullity is $0$ iff $0$
and $1$ are not conjugate along it (Theorem 14.1, V9.6). Milnor's completeness of $M$ enters only
through the compactness of the balls $\{x \in N : \rho(p, x) \le r\}$, which holds when $N$ is
closed in $V$ (then $N$ is complete, V7.30), or when $N$ is connected and complete (V7.22). $N$ need
not be compact or connected unless this is stated.

**How the path space is formalized.** The elements of $\Omega$ are maps $\mathbb R \to V$ whose values
off $[0, 1]$ play no role, and Milnor's metric $d$ sees only $[0, 1]$, so it is a pseudometric:
distinct maps that agree on $[0, 1]$ are at distance $0$ (V10.1). Three conventions follow.
Identities between paths hold on $[0, 1]$, unless a map is completed off $[0, 1]$ to make them exact
(V10.7). Milnor's homeomorphisms between sets of paths and sets of break points become homotopy
equivalences whose composites are the identity up to paths at distance $0$ (V10.5). And geodesics
are counted by their values on $[0, 1]$: "one cell for each geodesic" means one cell for each class
of geodesics that agree on $[0, 1]$. The manifold $B$ of broken geodesics is represented by its set
$U$ of break points, an open subset of $N \times \dots \times N$ (V10.4).

**V10.1 (Milnor's metric on $\Omega$; `Morse.PathSp`, `Morse.PathSp.speed`, `Morse.PathSp.supDist`,
`Morse.PathSp.l2Dist`, `Morse.PathSp.instPseudoEMetricSpace`, `Morse.PathSp.edist_def`,
`Morse.PathSp.edist_eq_zero_of_eqOn`).** For $\omega, \eta \in \Omega$, with speeds
$\dot s_\omega(t) = \|\frac{d\omega}{dt}(t)\|$ and $\dot s_\eta(t)$,
$$d(\omega, \eta) = \sup_{0 \le t \le 1}\rho(\omega(t), \eta(t)) + \Big(\int_0^1(\dot s_\omega -
\dot s_\eta)^2\,dt\Big)^{1/2}.$$
This is an extended pseudometric on $\Omega$ (formally with values in $[0, \infty]$; symmetric, with
the triangle inequality), and two paths that agree on $[0, 1]$ are at distance $0$. From now on
$\Omega$ and its subsets carry the topology of $d$. *Book:* p. 88: $\Omega$ can be topologized by
the distance $d(\omega, \omega') = \max_t\rho(\omega(t), \omega'(t)) + [\int_0^1(\frac{ds}{dt} -
\frac{ds'}{dt})^2dt]^{1/2}$, with $s$, $s'$ the arc lengths. *Hidden hypotheses:* the triangle
inequality for the second term is Minkowski's inequality in $L^2$; $\frac{ds}{dt}$ exists except at
finitely many points. *Deviation (restated):* on maps $\mathbb R \to V$, $d$ is a pseudometric, not a
metric; on paths $[0, 1] \to N$ it is Milnor's metric.

**V10.2 (Lemmas 16.A and 16.B of the exposition: the energy is continuous;
`Morse.PathSp.abs_sqrt_energy_sub_le`, `Morse.PathSp.lipschitzWith_sqrt_energy`,
`Morse.PathSp.continuous_energy`, `Morse.PathSp.isClosed_sublevel`,
`Morse.PathSp.isOpen_sublevel_lt`, `Morse.PathSp.exists_energy_lt_of_tendsto`).** (i) For
$\omega, \eta \in \Omega$ and $0 \le a \le b \le 1$, $|\sqrt{E_a^b(\omega)} - \sqrt{E_a^b(\eta)}| \le
(\int_0^1(\dot s_\omega - \dot s_\eta)^2dt)^{1/2}$; hence $\sqrt{E_a^b}$ is $1$-Lipschitz for $d$,
$E_a^b$ is continuous on $\Omega$, $\Omega^c$ is closed and $\operatorname{Int}\Omega^c$ is open.
(ii) (Lemma 16.B) If $\omega_n \to \omega$ in $\Omega$, then for every $\epsilon > 0$ there is
$\delta > 0$ with $E_a^b(\omega_n) < \epsilon$ for all $n$ and all $0 \le a \le b \le 1$ with
$b - a < \delta$. *Book:* p. 88: the last term of $d$ is added so that $E_a^b(\omega) =
\int_a^b(\frac{ds}{dt})^2dt$ is a continuous function on $\Omega$; $\Omega^c = E^{-1}([0, c])$ is
closed and $\operatorname{Int}\Omega^c = E^{-1}([0, c))$ is open. *Hidden hypotheses:*
$\sqrt{E_a^b} = \|\dot s\|_{L^2[a, b]}$ and Minkowski's inequality on $[a, b]$; with the uniform term
alone the energy is not continuous. *Deviation (not in the book):* (ii), used for the continuity of
$r_u$ (V10.7).

**V10.3 (the ball $S$, subdivisions, and Milnor's choices; `Morse.closedRiemBall`,
`Morse.mem_closedRiemBall_of_energy_le`, `Morse.isCompact_closedRiemBall_of_isClosed`,
`Morse.isCompact_closedRiemBall_of_isRiemComplete`, `Morse.corollary_10_8'`, `Morse.Subdivision`,
`Morse.BrokenSetup`, `Morse.exists_brokenSetup`, `Morse.exists_brokenSetup_uniform`,
`Morse.BrokenSetup.IsBroken`, `Morse.BrokenSetup.brokenPaths`).** Let $c > 0$ and
$S = \{x \in N : \rho(p, x) \le \sqrt c\}$. (i) Every $\omega \in \Omega$ with $E(\omega) \le c$ maps
$[0, 1]$ into $S$. (ii) $S$ is compact if $N$ is closed in $V$, or if $N$ is connected and complete.
(iii) For every compact $K \subseteq N$ there is $\delta > 0$ such that any $y, z \in K$ with
$\rho(y, z) < \delta$ are joined as in Corollary 10.8 (V7.20) at the scale $\delta$, and $\delta$ is
at most a normal radius (V7.9) at every point of $K$. (iv) A *subdivision* is $0 = t_0 < t_1 <
\dots < t_{m+1} = 1$, with $m$ interior points (Milnor's $k = m + 1$). *Milnor's data* consist of
$p, q \in N$, $c > 0$ with $S$ compact, a $\delta$ as in (iii) for $K = S$ (Milnor's $\varepsilon$),
and a subdivision with $c\,(t_{i+1} - t_i) < \delta^2$ for every $i$. If $p, q \in N$ and $S$ is
compact, there is $\eta > 0$ such that every subdivision with all $t_{i+1} - t_i < \eta$ is part of
such data, and some subdivision into equal parts is. (v) For Milnor's data,
$B = \operatorname{Int}\Omega(t_0, \dots, t_k)^c$ is the set of $\omega \in \Omega$ with
$E(\omega) < c$ that are geodesics on each open interval $(t_i, t_{i+1})$, and
$B^a = \{\omega \in B : E(\omega) \le a\}$. *Book:* p. 88: $\Omega(t_0, \dots, t_k)$, the paths
$\omega$ with $\omega|[t_{i-1}, t_i]$ a geodesic for each $i$, and $\operatorname{Int}\Omega(t_0,
\dots, t_k)^c = (\operatorname{Int}\Omega^c) \cap \Omega(t_0, \dots, t_k)$; p. 89: every
$\omega \in \Omega^c$ lies in the ball $S$, by $L^2 \le E \le c$; $S$ is compact since $M$ is
complete; by 10.8 there is $\varepsilon > 0$ such that two points of $S$ at distance less than
$\varepsilon$ are joined by a unique geodesic of length less than $\varepsilon$, depending
differentiably on them; and each $t_i - t_{i-1} < \varepsilon^2/c$. *Hidden hypotheses:* the
compactness of $S$ is the Hopf–Rinow theorem (Corollary 10.10, V7.27). *Deviation (restated):*
completeness enters only as the compactness of $S$; $\delta$ is also asked to be at most a normal
radius on $S$, which (iii) provides at no cost and which keeps the ends of each segment
non-conjugate (V10.10).

**V10.4 (Lemma 16.1; `Morse.BrokenSetup.energy'`, `Morse.BrokenSetup.nodes`,
`Morse.BrokenSetup.joinVec`, `Morse.BrokenSetup.path`, `Morse.BrokenSetup.nodeVal`,
`Morse.contDiffOn_Icc_of_isGeodesicOn`, `Morse.BrokenSetup.exists_segVec`,
`Morse.BrokenSetup.energy_path`, `Morse.BrokenSetup.lemma_16_1`, `Morse.BrokenSetup.exists_isOpen_nodes`,
`Morse.isSliceSubmanifold_pi_inter`, `Morse.tangentSubspace_pi_inter`).** Fix Milnor's data. For
$y = (y_1, \dots, y_m) \in V^m$ put $x_0 = p$, $x_j = y_j$ ($1 \le j \le m$), $x_{m+1} = q$, and
$$E'(y) = \sum_{i=0}^{m}\frac{\rho(x_i, x_{i+1})^2}{t_{i+1} - t_i};$$
let $U$ be the set of $y \in N^m$ with every $\rho(x_i, x_{i+1})$ finite and $E'(y) < c$. (i)
$U = N^m \cap O$ for an open $O \subseteq V^m$; for every open $O \subseteq V^m$, $N^m \cap O$ is a
slice submanifold of $V^m$ modelled on $Z^m$, with tangent space $T_{y_1}N \times \dots \times
T_{y_m}N$ at $y$. (ii) For $y \in U$, the broken geodesic $\omega_y$, equal on $[t_i, t_{i+1}]$ to
$t \mapsto \exp_{x_i}(\frac{t - t_i}{t_{i+1} - t_i}\,v(x_i, x_{i+1}))$, where $v(x, x')$ is the
initial vector of the short geodesic from $x$ to $x'$ (V7.20), lies in $B$, has break points
$(\omega_y(t_1), \dots, \omega_y(t_m)) = y$, and $E(\omega_y) = E'(y)$ (the exposition's formula
$(\ast)$). (iii) For $\omega \in B$ and each $i$ there is $w \in T_{\omega(t_i)}N$ with
$\|w\| < \delta$, $\omega(t) = \exp_{\omega(t_i)}(\frac{t - t_i}{t_{i+1} - t_i}\,w)$ for
$t_i \le t \le t_{i+1}$, and $E_{t_i}^{t_{i+1}}(\omega) = \|w\|^2/(t_{i+1} - t_i)$; the break points
$y$ of $\omega$ lie in $U$, and $\omega_y$ agrees with $\omega$ on $[0, 1]$. So $y \mapsto \omega_y$
and $\omega \mapsto (\omega(t_1), \dots, \omega(t_m))$ are inverse bijections between $U$ and $B$,
paths being compared on $[0, 1]$. *Book:* p. 88, Lemma 16.1: for $M$ complete and $c > 0$ with
$\Omega^c \ne \emptyset$, for all sufficiently fine subdivisions $\operatorname{Int}\Omega(t_0,
\dots, t_k)^c$ can be given the structure of a smooth finite dimensional manifold "in a natural
way"; proof, p. 89: for a broken geodesic, $(L_{t_{i-1}}^{t_i}\omega)^2 = (t_i -
t_{i-1})E_{t_{i-1}}^{t_i}\omega < \varepsilon^2$, so each segment is determined by its end points,
and $\omega$ by $(\omega(t_1), \dots, \omega(t_{k-1})) \in M \times \dots \times M$; this
correspondence is a homeomorphism onto an open subset of the product, whose differentiable structure
is taken over. *Hidden hypotheses:* that the image is the open set $U$: the vertices of a point of
$U$ lie in $S$ by the Cauchy–Schwarz inequality, $\rho(p, x_i) \le \sum_j\rho(x_j, x_{j+1}) \le
(\sum_j(t_{j+1} - t_j))^{1/2}E'(y)^{1/2} < \sqrt c$, and consecutive ones are at distance less than
$\delta$; that a geodesic segment is the radial geodesic of its initial vector (V9.9 (ii)) and,
that vector being shorter than $\delta$, the short geodesic (uniqueness in Corollary 10.8); that a
broken geodesic is smooth up to the ends of its segments. *Deviation (stronger):* $\Omega^c \ne
\emptyset$ is not needed. *Deviation (restated):* the manifold is $U$, an open subset of $N^m$,
rather than a structure transported to $B$; the topologies are compared in V10.5.

**V10.5 (the correspondence is a homeomorphism up to paths at distance $0$;
`Morse.BrokenSetup.continuous_pathP`, `Morse.BrokenSetup.continuous_nodeVal`,
`Morse.BrokenSetup.homotopyEquivNodes`).** For Milnor's data, $y \mapsto \omega_y$ is continuous from
$U$ (with the topology of $V^m$) to $\Omega$, and $\omega \mapsto (\omega(t_1), \dots, \omega(t_m))$
is continuous from $\Omega$ to $V^m$. For every $a \in \mathbb R$ they restrict to continuous maps
between $B^a \subseteq \Omega$ and $\{y \in U : E'(y) \le a\}$, inverse to each other up to paths
at distance $0$; so the two sets are homotopy equivalent (for $a \ge c$, $B$ and $U$). *Book:*
p. 89: "Evidently" $\omega \mapsto (\omega(t_1), \dots, \omega(t_{k-1}))$ defines a homeomorphism
between $\operatorname{Int}\Omega(t_0, \dots, t_k)^c$ and an open subset of $M \times \dots \times
M$. *Hidden hypotheses:* the continuity of $\omega \mapsto \omega(t_i)$ uses $\|x - y\| \le
\rho(x, y)$; that of $y \mapsto \omega_y$ for $d$ needs, for the uniform term, the continuity of
the short geodesics in their end points (Corollary 10.8 and the continuity of $\exp$, V7.23), and,
for the $L^2$ term, that of the speeds $\rho(x_i, x_{i+1})/(t_{i+1} - t_i)$. *Deviation (restated):*
a homotopy equivalence, indeed a homeomorphism up to the identification of paths at distance $0$,
in place of a homeomorphism, since paths are maps on $\mathbb R$.

**V10.6 (Theorem 16.2: $E'$ is smooth and $B^a$ is compact; `Morse.contMDiffAt_of_locally_eq`,
`Morse.BrokenSetup.exists_smooth_energy'`, `Morse.BrokenSetup.contMDiff_energy'`,
`Morse.BrokenSetup.continuousOn_energy'`, `Morse.BrokenSetup.isCompact_sublevel`).** For Milnor's
data: (i) every $y_0 \in U$ has an open neighbourhood $O$ in $V^m$ with a function smooth on $O$
that equals $E'$ on $U \cap O$; hence $E'$ is continuous on $U$, and smooth on the manifold
$N^m \cap O$ for every open $O \subseteq V^m$ with $N^m \cap O \subseteq U$ (a function on a slice
submanifold which near a point is the restriction of a smooth function on an open set of the
ambient space is smooth there). (ii) For $a < c$, $\{y \in U : E'(y) \le a\}$ is compact. *Book:*
p. 90, Theorem 16.2: $E' : B \to \mathbb R$ is smooth, and for each $a < c$ the set $B^a =
(E')^{-1}[0, a]$ is compact; p. 90: $E'$ depends smoothly on the break points, by the explicit
formula $E'(\omega) = \sum_i\rho(\omega(t_{i-1}), \omega(t_i))^2/(t_i - t_{i-1})$; p. 91: $B^a$ is
homeomorphic to a set of $(k - 1)$-tuples in $S \times \dots \times S$, closed in a compact set.
*Hidden hypotheses:* $\rho$ is not smooth on the diagonal; $E'$ is smooth because $\rho(x, x')^2 =
\|v(x, x')\|^2$ with $v$ smooth (Corollary 10.8); the set of tuples is closed only because the
distances are finite. *Deviation (restated):* as reproduced in the scan, the condition defining the
tuples reads $\rho(p_{i-1}, p_i)^c/(t_i - t_{i-1}) \le a$, with exponent $c$ and no summation sign;
the formal condition is $E'(p_1, \dots, p_{k-1}) \le a$, the sum with exponent $2$ (see
`Exposition/Findings.md`). Compactness is stated for the set of break points.

**V10.7 (Milnor's deformation $r_u$, and the exposition's Lemma 16.C; `Morse.BrokenSetup.retr`,
`Morse.BrokenSetup.retr_mem_pathSpace`, `Morse.BrokenSetup.energy_retr_le`,
`Morse.BrokenSetup.retr_zero`, `Morse.BrokenSetup.retr_one`,
`Morse.BrokenSetup.retr_of_mem_brokenPaths`, `Morse.BrokenSetup.retrSeg_eq_retr`,
`Morse.BrokenSetup.deform`, `Morse.BrokenSetup.continuousOn_deform`).** For Milnor's data,
$\omega \in \Omega$ with $E(\omega) < c$ and $t_i \le u \le t_{i+1}$, $r_u(\omega)$ is the broken
geodesic $\omega_y$ of the break points $y$ of $\omega$ on $[0, t_i]$, the short geodesic from
$\omega(t_i)$ to $\omega(u)$, run at constant speed, on $[t_i, u]$, and $\omega$ on $[u, 1]$; at
$u = t_{i+1}$ the formulas of the two neighbouring segments agree. On $[0, 1]$: $r_u(\omega) \in
\Omega$, $E(r_u(\omega)) \le E(\omega)$, $r_0(\omega) = \omega$, $r_1(\omega) = \omega_y$, and
$r_u(\omega) = \omega$ for $\omega \in B$. Completed by $\omega$ off $[0, 1]$, and set equal to
$\omega$ when $u \notin [0, 1]$ or $E(\omega) \ge c$, $(u, \omega) \mapsto r_u(\omega)$ is a map
$\mathbb R \times \Omega \to \Omega$, and (Lemma 16.C) it is continuous on $[0, 1] \times
\operatorname{Int}\Omega^c$. *Book:* p. 91: the retraction $r : \operatorname{Int}\Omega^c \to B$,
$r(\omega)$ being on each $[t_{i-1}, t_i]$ the geodesic of length less than $\varepsilon$ from
$\omega(t_{i-1})$ to $\omega(t_i)$; "Clearly" $E(r(\omega)) \le E(\omega) < c$; for
$t_{i-1} \le u \le t_i$, $r_u(\omega)$ is $r(\omega)$ on $[0, t_{i-1}]$, the minimal geodesic from
$\omega(t_{i-1})$ to $\omega(u)$ on $[t_{i-1}, u]$, and $\omega$ on $[u, 1]$; $r_0$ is the identity,
$r_1 = r$, and "it is easily verified" that $r_u(\omega)$ is continuous in both variables. *Hidden
hypotheses:* the short geodesic exists since $\rho(\omega(t_i), \omega(u))^2 \le (u - t_i)E(\omega)
< \delta^2$; the formulas must agree where neighbouring intervals meet; $r_u$ fixes $B$ because a
sub-arc of a short geodesic is the short geodesic between its ends (uniqueness in Corollary 10.8);
$E(r_u(\omega)) \le E(\omega)$ holds segment by segment, by Schwarz's inequality $\rho^2 \le
(b - a)E_a^b$; for the continuity, the uniform term needs the continuity of short geodesics in
their end points and the equicontinuity of the paths of energy less than $c$, and the $L^2$ term,
for $u$ near $t_i$, the bound $\rho(\omega(t_i), \omega(u))^2/(u - t_i) \le E_{t_i}^u(\omega)$ with
Lemma 16.B (V10.2). *Deviation (restated):* Milnor's minimal geodesic is the short geodesic of
V7.20, which is minimal.

**V10.8 (Theorem 16.2: $B^a$ is a strong deformation retract of $\Omega^a$;
`Morse.BrokenSetup.deform_zero`, `Morse.BrokenSetup.energy_deform_le`,
`Morse.BrokenSetup.deform_one_mem_brokenPaths`, `Morse.BrokenSetup.deform_of_mem_brokenPaths`,
`Morse.BrokenSetup.theorem_16_2_deformationRetract`, `Morse.BrokenSetup.homotopyEquivBroken`).** For
Milnor's data and $a < c$, the deformation of V10.7 is continuous on $[0, 1] \times \Omega^a$, does
not increase the energy (so every $r_u$ maps $\Omega^a$ into itself), starts at the identity, ends
in $B^a$ ($r_1(\omega) \in B$ for every $\omega \in \operatorname{Int}\Omega^c$), and fixes every
point of $B$ for $0 \le u \le 1$. So $B^a$ is a strong deformation retract of $\Omega^a$, and the
inclusion $B^a \subseteq \Omega^a$ is a homotopy equivalence; by V10.7, $B$ is likewise a strong
deformation retract of $\operatorname{Int}\Omega^c$. *Book:* p. 90, Theorem 16.2: $B^a$ is a
deformation retract of $\Omega^a$, with the footnote that $B$ itself is similarly a deformation
retract of $\operatorname{Int}\Omega^c$; p. 91: since $E(r_u(\omega)) \le E(\omega)$, "it is clear"
that each $B^a$ is a deformation retract of $\Omega^a$. *Hidden hypotheses:* those of V10.7.
*Deviation (restated):* the strong deformation retraction is stated through these properties of
$(u, \omega) \mapsto r_u(\omega)$, which hold exactly, not only on $[0, 1]$, thanks to the completion
of V10.7.

**V10.9 (Theorem 16.2: the critical points of $E'$; `Morse.exists_curve_of_mem_tangentSubspace`,
`Morse.BrokenSetup.exists_variation_path`, `Morse.BrokenSetup.varField_path_node`,
`Morse.BrokenSetup.firstVariation_path`, `Morse.BrokenSetup.fderiv_eq_jumps`,
`Morse.BrokenSetup.isCriticalPointM_iff`,
`Morse.BrokenSetup.eqOn_path_nodeVal_of_isUnbrokenGeodesic`).** Fix Milnor's data. (i) Every
tangent vector of a slice submanifold at a point is the velocity at $0$ of a smooth curve in it. If
$u \mapsto y(u)$ is a smooth curve in $U$ near $0$, then $(u, t) \mapsto \omega_{y(u)}(t)$ is, for
$|u| < \varepsilon$, a variation (V8.2) through broken geodesics, smooth on each strip
$(-\varepsilon, \varepsilon) \times [t_i, t_{i+1}]$, whose variation field takes the value
$y'(0)_j$ at $t_j$. (ii) At $\gamma = \omega_y$, $y \in U$, the first variation (V8.7) in the
direction $X$ is $-\sum_j\langle X(t_j), \Delta_{t_j}\gamma'\rangle$. (iii) Let $O \subseteq V^m$ be
open with $N^m \cap O \subseteq U$, and $F$ smooth on $V^m$ with $F = E'$ on $N^m \cap O$. For
$y \in N^m \cap O$ and $w \in T_{y_1}N \times \dots \times T_{y_m}N$, $dF_y(w) =
-2\sum_j\langle w_j, \Delta_{t_j}\omega_y'\rangle$; and $y$ is a critical point (V1.4) of
$E' = F|(N^m \cap O)$ iff $\omega_y$ is an unbroken geodesic. (iv) For every geodesic
$\gamma \in \Omega$ with $E(\gamma) < c$, the break points $y$ of $\gamma$ lie in $U$, $\omega_y$
agrees with $\gamma$ on $[0, 1]$ and is an unbroken geodesic, and $E'(y) = E(\gamma)$. *Book:*
p. 90, Theorem 16.2: the critical points of $E'$ are precisely the critical points of $E$ in
$\operatorname{Int}\Omega^c$, namely the unbroken geodesics from $p$ to $q$ of length less than
$\sqrt c$; p. 91: every geodesic is a broken geodesic, so every critical point of $E$ in
$\operatorname{Int}\Omega^c$ lies in $B$, and with the first variation formula (§12.2) "it is
clear" that the critical points of $E'$ are the unbroken geodesics. *Hidden hypotheses:* that every
tangent vector of $B$ at $\gamma$ is the variation field of a variation through broken geodesics,
smooth on the strips, which needs the smooth dependence of a geodesic segment on its end points
over the whole segment (V9.9 (iii)); testing one break point at a time, with the tangent vector
$\Delta_{t_j}\gamma'$; a broken geodesic without velocity jumps is unbroken (Corollary 12.3, V8.11).
*Deviation (restated):* the critical points of $E$ are the unbroken geodesics by Corollary 12.3;
$E'$ is read through a smooth ambient extension $F$, as functions on submanifolds are in Part I
(V1.6), and the statement holds for every such $F$ and $O$.

**V10.10 (broken Jacobi fields for the subdivision of §16, and Lemma 15.4 for it;
`Morse.IsJacobiField.comp_affine`, `Morse.nonneg_of_isLocalMin_of_hasDerivAt`,
`Morse.BrokenSetup.energy'_nodeVal_le`, `Morse.BrokenSetup.not_isConjugate_seg`,
`Morse.BrokenSetup.exists_brokenSpace_node`, `Morse.BrokenSetup.brokenSpace_eq_zero`,
`Morse.BrokenSetup.brokenNodeMap_bijective`, `Morse.BrokenSetup.energyHessian_nodeZero_nonneg`,
`Morse.BrokenSetup.energyHessian_nodeZero_pos`, `Morse.BrokenSetup.isCompl_brokenSpace_nodeZero`,
`Morse.BrokenSetup.formIndex_brokenSpace`, `Morse.BrokenSetup.finrank_ker_brokenSpace`).** Fix
Milnor's data and $y \in U$ with $\gamma = \omega_y$ an unbroken geodesic. (i) A Jacobi field along
$\gamma$, restricted to a segment and reparametrized affinely, is a Jacobi field along the
reparametrized segment. (ii) For every $i$, $t_i$ and $t_{i+1}$ are not conjugate along $\gamma$
(V9.4). (iii) The broken Jacobi fields along $\gamma$ for the break points $t_1, \dots, t_m$ (V9.17,
with $\tau = 1$) with arbitrary tangent values at the $t_j$ exist and are unique: $W \mapsto
(W(t_1), \dots, W(t_m))$ is a linear isomorphism onto $T_{y_1}N \times \dots \times T_{y_m}N$. (iv)
For every $\omega \in \Omega$, $E'(\omega(t_1), \dots, \omega(t_m)) \le E(\omega)$; hence
$E_{**}(W, W) \ge 0$ for every $W \in T\Omega_\gamma$ vanishing at the $t_j$, and
$E_{**}(W, W) > 0$ if moreover $W \ne 0$ and $W$ vanishes off $[0, 1]$. (v) The fields of
$T\Omega_\gamma$ vanishing off $[0, 1]$ are the direct sum of the broken Jacobi fields and of those
vanishing at the $t_j$; the index of $E_{**}$ is the index of its restriction to the broken Jacobi
fields, and the nullity of this restriction is the nullity of $E_{**}$. *Book:* pp. 91–92: $TB_\gamma$
is identified with the space $T\Omega_\gamma(t_0, \dots, t_k)$ of broken Jacobi fields of §15;
p. 92: the equality of the indices and nullities "is an immediate consequence of Lemma 15.4".
*Hidden hypotheses:* Lemma 15.4 (V9.19) is proved for a subdivision chosen in §15, fine in the sense
of V9.16, which the subdivision of §16 need not be; its proof needs (a) Jacobi fields on each
segment with arbitrary end values, and unique, and (b) $E_{**}$ positive definite on the fields
vanishing at the break points. For §16, (a) holds because each segment is the radial geodesic of a
vector shorter than a normal radius (V9.11 (i)), and (b) because the broken geodesic minimizes the
energy among the paths through its break points, (a) excluding null vectors. *Deviation (not in the
book):* (iv)–(v) are Lemma 15.4 proved anew for this subdivision. *Proof:* (iv) from Schwarz's
inequality on each segment, Remark 13.5 (V8.17) and the fact that a minimum has a nonnegative second
derivative; a null vector vanishing at the $t_j$ would be a Jacobi field on each segment vanishing at
both ends, hence $0$ by (ii).

**V10.11 (Theorem 16.2: the index and the nullity of $E'$; `Morse.hasDerivAt_deriv_line`,
`Morse.BrokenSetup.chartBrokenEquiv`, `Morse.BrokenSetup.hessian_apply_self`,
`Morse.BrokenSetup.hessian_eq_energyHessian`, `Morse.BrokenSetup.theorem_16_2_index`).** Let $O$ and
$F$ be as in V10.9 (iii), and $y \in N^m \cap O$ with $\gamma = \omega_y$ an unbroken geodesic; let
$\kappa$ be the slice chart of $N^m \cap O$ at $y$, $x$ its parametrization and $z_0 = \kappa(y)$.
For $z$ in the model space $Z^m$ let $\Lambda z$ be the broken Jacobi field (V10.10 (iii)) with the
values $dx_{z_0}(z)$ at the break points; $\Lambda$ is a linear isomorphism onto the broken Jacobi
fields. (i) For $G$ of class $C^2$ near $z_0$, the second derivative at $0$ of
$u \mapsto G(z_0 + uz)$ is $G_{**}(z, z)$. (ii) The Hessian of $F \circ x$ at $z_0$ is $E_{**}$ on
the broken Jacobi fields: $(F \circ x)_{**}(z, z') = E_{**}(\Lambda z, \Lambda z')$. (iii)
**Theorem 16.2:** the index of $E'$ at $y$ (V1.4) equals the index of $E_{**}$ at $\gamma$ (V9.13),
and the nullity of $E'$ at $y$ equals the nullity of $E_{**}$ at $\gamma$ (V9.6). *Book:* p. 90,
Theorem 16.2: the index [or the nullity] of the Hessian $E'_{**}$ at each critical point $\gamma$ is
equal to the index [or the nullity] of $E_{**}$ at $\gamma$; p. 92: for a variation
$\bar\alpha : (-\varepsilon, \varepsilon) \to B$ of $\gamma$ through broken geodesics the variation
field is "clearly a broken Jacobi field" (compare §14.3); then Lemma 15.4. *Hidden hypotheses:* the
variation field of a variation through broken geodesics is, on each segment, a Jacobi field along
the segment reparametrized to $[0, 1]$ (Lemma 14.3, V9.8, with V10.10 (i)); that it is the broken
Jacobi field with the same values at the break points needs their uniqueness (V10.10 (ii)); the
Hessians are compared first as quadratic forms, then polarized. *Proof:* $F(x(z_0 + uz)) =
E(\omega_{x(z_0 + uz)})$ for a variation through broken geodesics (V10.9 (i)), so by Remark 13.5
(V8.17) the second derivative is $E_{**}(W, W)$, $W$ its variation field, which is $\Lambda z$; then
V10.10 (v).

**V10.12 (Theorem 16.3 in the model; `Morse.exists_contDiff_eq_of_locally`,
`Morse.isFiniteCellComplexType_sublevel_of_isCompact`, `Morse.BrokenSetup.exists_contDiff_eq_energy'`,
`Morse.BrokenSetup.geodIndex`, `Morse.BrokenSetup.theorem_16_3`, `Morse.BrokenSetup.theorem_16_3_count`,
`Morse.BrokenSetup.theorem_16_3_nonconj`).** (i) If $K \subseteq S'$ are subsets of a
finite-dimensional normed space, $K$ compact, and $f$ agrees on $S'$ near each point of $K$ with a
function smooth on an open set, then $f$ agrees on $K$ with a function smooth everywhere. (ii)
(Theorem 3.5 for a compact sublevel set) Let $N$ be a slice submanifold, $F$ smooth on $V$,
$f = F|N$, and $a_0$ a real number that is not a critical value of $f$, with
$N^{a_0} = f^{-1}(-\infty, a_0]$ compact and all critical points of $f$ in $N^{a_0}$ non-degenerate.
Then the critical points of $f$ in $N^{a_0}$, listed by non-decreasing value, are finitely many, and
$N^{a_0}$ has the homotopy type of an iterated adjunction space (V2.11) with one cell of dimension
the index for each of them. (iii) **Theorem 16.3 in the model:** for Milnor's data and $a < c$,
suppose $E'(y) \ne a$ for every $y \in U$ with $\omega_y$ a geodesic, and $E_{**}$ has nullity $0$
at every such $\omega_y$ with $E'(y) \le a$ (equivalently, $0$ and $1$ are not conjugate along it).
Then the $y \in U$ with $\omega_y$ a geodesic and $E'(y) \le a$ are finitely many, and
$\{y \in U : E'(y) \le a\}$ has the homotopy type of an iterated adjunction space with one cell of
dimension the index of $E_{**}$ at $\omega_y$ for each of them, attached in order of non-decreasing
energy; the number of cells of dimension $\lambda$ is the number of these geodesics of index
$\lambda$. *Book:* p. 90, Theorem 16.3 (V10.13); proof: "This follows from 16.2 together with
§3.5". *Hidden hypotheses:* Theorem 3.5 (V2.12) concerns a function on a manifold with compact
sublevel sets and no degenerate critical point, while $B$ is not compact and only the critical
points in $B^a$ are assumed non-degenerate; and $a$ must not be a critical value of $E'$ (Milnor's
hypothesis does not exclude a geodesic of energy exactly $a$, and then $B^a$ is a critical sublevel
set). *Deviation (narrower):* $a$ is not the energy of a geodesic; a cell complex in the sense of
V2.11. *Proof:* departs from the exposition's, which reparametrizes $E'$ on $\{E' < a'\}$ for a level
$a' > a$ below the next critical value: $E'$ is extended by (i) from the compact
$\{E' \le (a + c)/2\}$ to a smooth function on $V^m$, and (ii) is applied on the manifold
$\{y \in U : E'(y) < (a + c)/2\}$, with V10.9 for the critical points and V10.11 for their indices.

**V10.13 (Theorem 16.3 for $\Omega^a$; `Morse.BrokenSetup.theorem_16_3_Omega`,
`Morse.BrokenSetup.theorem_16_3_Omega_count`).** Let Milnor's data be given with $c > a$ (by V10.3
they exist for every $c > 0$ when $N$ is closed in $V$, or connected and complete), and suppose that
no geodesic $\gamma \in \Omega$ has $E(\gamma) = a$ and that $E_{**}$ has nullity $0$ at every
geodesic $\gamma \in \Omega$ with $E(\gamma) \le a$. Then the geodesics in $\Omega^a$ are finitely
many, and $\Omega^a$, with the metric $d$, has the homotopy type of an iterated adjunction space with
one cell of dimension $\lambda$ for each geodesic in $\Omega^a$ of index $\lambda$, attached in order
of non-decreasing energy. *Book:* p. 90, Theorem 16.3: if $M$ is complete and $p, q$ are not
conjugate along any geodesic of length $\le \sqrt a$, then $\Omega^a$ has the homotopy type of a
finite CW-complex with one cell of dimension $\lambda$ for each geodesic in $\Omega^a$ at which
$E_{**}$ has index $\lambda$; in particular $\Omega^a$ contains only finitely many geodesics.
*Hidden hypotheses:* as in V10.12; and the homotopy equivalences $\Omega^a \simeq B^a$ (Theorem 16.2)
and between $B^a$ and its break points (V10.5). *Deviation (narrower):* $a$ is not the energy of a
geodesic; non-conjugacy is stated as nullity $0$, equivalent by Theorem 14.1 (V9.6); the
CW-complex is a cell complex in the sense of V2.11. *Proof:* V10.12 (iii), transported along V10.5
and V10.8; every geodesic of $\Omega^a$ is some $\omega_y$ on $[0, 1]$ (V10.9 (iv)).

**V10.14 (the Remark on p. 92: a minimum of $E'$; `Morse.BrokenSetup.nodeVal_mem_nodes_of_energy_lt`,
`Morse.BrokenSetup.exists_energy_minimizing`).** For Milnor's data, every $\omega \in \Omega$ with
$E(\omega) < c$ has its break points $y$ in $U$, with $E'(y) \le E(\omega)$; and if some
$\omega_0 \in \Omega$ has $E(\omega_0) < c$, there is $y \in U$ such that $\omega_y$ is an unbroken
geodesic and $E(\omega_y) \le E(\omega)$ for every $\omega \in \Omega$. *Book:* p. 92, Remark: an
alternative proof of the existence of a minimal geodesic joining two points of a complete manifold:
if $\Omega^a$ is non-vacuous, $B^a$ is compact and non-vacuous, $E'$ takes its minimum on $B^a$ at
some $\gamma$, and this $\gamma$ "will be the required minimal geodesic". *Hidden hypotheses:* that
$\gamma$ minimizes $E$ on all of $\Omega$ needs $E(\omega) \ge E'(\omega(t_1), \dots, \omega(t_m))$
for every $\omega$ (Schwarz's inequality); that it is a geodesic, that a minimum is a critical point
(V10.9); that it is shortest, a reparametrization of paths by arc length. *Deviation (narrower):*
minimality is proved for the energy; that $\omega_y$ is a minimal geodesic in the sense of V7.24 is
not stated.

**V10.15 ($\Omega^*$ and the inclusion $i$; `Morse.pathCSet`, `Morse.PathC`, `Morse.PathSp.toPathC`,
`Morse.PathSp.edist_toPathC_le`, `Morse.PathSp.continuous_toPathC`, `Morse.pathIncl`).**
$\Omega^* = \Omega^*(N; p, q)$ is the set of continuous maps $\omega : [0, 1] \to V$ with values in
$N$, $\omega(0) = p$ and $\omega(1) = q$, as a subspace of the space of continuous maps
$[0, 1] \to V$ with the uniform distance $d^*(\omega, \eta) = \max_t\|\omega(t) - \eta(t)\|$, whose
topology is the compact-open topology. The map $i : \Omega \to \Omega^*$ restricts a path to
$[0, 1]$; $d^*(i\omega, i\eta) \le d(\omega, \eta)$, so $i$ is continuous. *Book:* p. 93: $\Omega^*$,
the space of all continuous paths $\omega : [0, 1] \to M$ from $p$ to $q$ with the compact-open
topology, which is also induced by $d^*(\omega, \omega') = \max_t\rho(\omega(t), \omega'(t))$; since
$d \ge d^*$, the natural map $i : \Omega \to \Omega^*$ is continuous. *Hidden hypotheses:* none.
*Deviation (restated):* $d^*$ is measured with the norm of $V$ rather than with $\rho$; on $N$ the two
distances define the same topology (V7.21), so both give the compact-open topology, and
$\|x - y\| \le \rho(x, y)$ gives the inequality.

**V10.16 (convergence in $\Omega$ controls the velocities;
`Morse.PathSp.tendsto_integral_norm_deriv_sub_sq`, `Morse.PathSp.tendsto_of_tendsto_apply_of_integral`,
`Morse.tendsto_integral_deriv_comp_sub_sq`).** (i) If $\omega_j \to \omega$ in $\Omega$ (along any
filter), then $\int_0^1\|\omega_j' - \omega'\|^2dt \to 0$, although $d$ involves only the speeds.
(ii) Conversely, if $\omega_j(s) \to \omega(s)$ for every $s \in [0, 1]$ and
$\int_0^1\|\omega_j' - \omega'\|^2dt \to 0$, then $\omega_j \to \omega$ in $\Omega$. (iii) If $\Phi$
is of class $C^1$ on an open set containing the curve $F([a, b])$, $F_j \to F$ uniformly on
$[a, b]$, and the velocities $F_j'$ are bounded in $L^2$ and converge to $F'$ in $L^2$ (all curves
differentiable off finite sets), then $(\Phi \circ F_j)' \to (\Phi \circ F)'$ in $L^2$. *Book:* not
stated; it is what the continuity for $d$ of the maps in the proof of Theorem 17.1 needs (p. 94).
*Deviation (not in the book):* these are the analytic facts that make maps given pointwise by smooth
formulas, such as the deformation of V10.18, continuous for $d$. *Proof:* (i) the energies converge
(V10.2), and the velocities converge weakly in $L^2$ by integration by parts on the smooth pieces of
$\omega$ and uniform convergence.

**V10.17 (good balls, the exposition's Lemma 17.B; `Morse.IsMinJoin`, `Morse.minJoin`,
`Morse.minGeo`, `Morse.IsGoodBall`, `Morse.IsGoodBall.eq_minJoin`, `Morse.IsGoodBall.minGeo_minGeo`,
`Morse.IsGoodBall.exists_smooth_minGeo`, `Morse.exists_isGoodBall_ball`,
`Morse.exists_lebesgue_goodBall`, `Morse.exists_smooth_glue`, `Morse.exists_goodSet`,
`Morse.JoinSystem`, `Morse.goodJoin`).** For
$y, z \in V$ the *minimal join vector* $v(y, z)$ is the unique $v \in T_yN$ with $\exp_y(v) = z$
and $\rho(y, z) = \|v\|$ for which the conclusion of Corollary 10.8 holds at some scale
$\delta > \|v\|$ ($0$ if there is none), and $\sigma_{yz}(s) = \exp_y(s\,v(y, z))$. An open
$O \subseteq V$ is a *good ball* if, for one $\delta > 0$, any two points of $N \cap O$ are at
distance less than $\delta$ and joined as in Corollary 10.8 at the scale $\delta$, and
$\sigma_{yz}(s) \in N \cap O$ for $y, z \in N \cap O$ and $0 \le s \le 1$ (convexity). (i) For
$x \in N$, the balls $\{\|y - x\| < r\}$ of $V$ are good for all small $r > 0$. (ii) For compact
$K \subseteq N$ there is $\varepsilon > 0$ such that the ball of radius $\varepsilon$ about each point
of $K$ lies in a good ball. (iii) In a good ball, $\sigma_{yz}$ is the unique minimal geodesic from
$y$ to $z$, its sub-arcs are minimal geodesics, and near each pair the map $(y, z, s) \mapsto
\sigma_{yz}(s)$ is the restriction of a map smooth on an open set. (iv) Local smooth extensions are
glued, by a partition of unity, into one map of $(y, z, s)$, smooth for $-\varepsilon < s <
1 + \varepsilon$, that agrees with $\sigma$ on a given compact set of pairs. So the balls
$\{\|y - x\| < r\}$, $x \in N$, for which the concentric balls of radius up to $2r$ are good and
$N \cap \{\|y - x\| \le r\}$ is compact, with the joins $\sigma$, form a *join system*: open good
sets, convex for the joins, with $\sigma_{yz}(0) = y$, $\sigma_{yz}(1) = z$, $\sigma_{yy} = y$, one
smooth map of $(y, z, s)$ on each good set, and a Lebesgue number for every compact subset of $N$.
*Book:* p. 93: for a continuous $f : M \to [0, \infty)$ with compact sets $f^{-1}([0, r])$,
$\varepsilon_1(r)$ is the largest number such that any two points of $f^{-1}([0, r])$ at distance
less than $\varepsilon_1(r)$ are joined by a unique minimal geodesic which varies differentiably with
the end points. *Hidden hypotheses:* the modified proof of Theorem 17.1 needs regions that are convex
for these geodesics (J. H. C. Whitehead's convex balls), one smooth map of $(y, z, s)$ on each whole
region, and a uniform scale; Milnor's construction provides none of these. *Deviation (not in the
book):* the exposition's Lemma 17.B. *Deviation (restated):* good balls are balls of $V$ intersected
with $N$, not metric balls of $\rho$, and their convexity is proved with the ambient distance: along
a geodesic $\gamma$, $(\|\gamma - x\|^2)'' = 2\|\gamma'\|^2 + 2\langle\gamma - x,
\mathrm{II}(\gamma', \gamma')\rangle > 0$ while $\gamma$ stays near $x$, so no normal coordinates or
Gauss lemma are needed; smoothness in $(y, z, s)$ uses the smoothness of $\exp$ on its whole domain
(V11.1).

**V10.18 (the exposition's Lemma 17.C; `Morse.dy`, `Morse.JoinSystem.IsGood`,
`Morse.JoinSystem.YSet`, `Morse.JoinSystem.isOpen_YSet`, `Morse.JoinSystem.YSet_mono`,
`Morse.JoinSystem.exists_mem_YSet`, `Morse.JoinSystem.XSet`, `Morse.JoinSystem.XSet_eq_preimage`,
`Morse.JoinSystem.broken`, `Morse.JoinSystem.interp`, `Morse.JoinSystem.continuous_interp_star`,
`Morse.JoinSystem.continuous_brokenΩ`, `Morse.JoinSystem.continuous_interpΩ`,
`Morse.JoinSystem.isHomotopyEquiv_toY`).** Fix a join system (V10.17). For $k \ge 0$ let
$Y_k \subseteq \Omega^*$ be the set of paths each of whose dyadic pieces
$\omega([j2^{-k}, (j + 1)2^{-k}])$ lies in a good set, and $X_k = i^{-1}(Y_k) \subseteq \Omega$.
(i) The $Y_k$ are open, increasing, and cover $\Omega^*$. (ii) For $\omega \in Y_k$ let $b(\omega)$ be
the broken geodesic with vertices $\omega(j2^{-k})$, joined by the joins, and let
$H(\omega, u)(s) = \sigma_{\omega(s), b(\omega)(s)}(u)$ be the point at time $u$ of the join from
$\omega(s)$ to $b(\omega)(s)$; $H(\omega, 0) = \omega$ and $H(\omega, 1) = b(\omega)$. Then $H$ is
continuous from $Y_k \times [0, 1]$ to $Y_k$ for $d^*$ and from $X_k \times [0, 1]$ to $X_k$ for $d$,
and $b$ is continuous from $(Y_k, d^*)$ to $(X_k, d)$. (iii) Hence $i : X_k \to Y_k$ is a homotopy
equivalence with homotopy inverse $b$. *Book:* p. 94: $h(\omega)$, the broken geodesic agreeing
with $\omega$ at $t = 0, A(\omega), \dots, kA(\omega)$ and $1$; an argument similar to that in §16
shows $h \circ i \simeq \mathrm{id}$ and $i \circ h \simeq \mathrm{id}$. *Hidden hypotheses:* the
deformation must stay where the joins are defined (convexity, V10.17); continuity for $d$ of a map
given by a smooth formula needs the velocities, not only the speeds, to converge in $L^2$ (V10.16);
$d$ being only a pseudometric, $b \circ i \simeq \mathrm{id}$ holds up to paths at distance $0$,
which is harmless. *Deviation (not in the book):* the dyadic sets $Y_k$ and $X_k$, on each of which
the subdivision is fixed. *Deviation (restated):* the deformation moves every point $\omega(s)$ along
the join to $b(\omega)(s)$, instead of moving a break point along the path as Milnor's $r_u$ (and
the exposition's proof) does.

**V10.19 (Theorem 17.1; `Morse.isHomotopyDirectLimit_preimage`, `Morse.theoremA_general`,
`Morse.JoinSystem.isHomotopyEquiv_toPathC`, `Morse.theorem_17_1`).** (i) If $Y$ is paracompact and
Hausdorff, $B_0 \subseteq B_1 \subseteq \cdots$ are subsets of $Y$ such that every point lies in the
interior of some $B_n$, and $g : X \to Y$ is continuous, then $X$ is the homotopy direct limit
(VA.2) of the sets $g^{-1}(B_n)$. (ii) For every join system, $i : \Omega(N; p, q) \to
\Omega^*(N; p, q)$ is a homotopy equivalence (VA.1). (iii) **Theorem 17.1:** for every slice
submanifold $N$ of $V$, complete or not, and all $p, q$, the inclusion $i : \Omega \to \Omega^*$, with
Milnor's metric $d$ on $\Omega$ and the compact-open topology on $\Omega^*$, is a homotopy
equivalence. *Book:* p. 93, Theorem 17.1: the natural map $i$ is a homotopy equivalence between
$\Omega$ and $\Omega^*$. Proof, pp. 93–94: with $f$ and $\varepsilon_1$ as in V10.17, a continuous
$\varepsilon_2$ with $0 < \varepsilon_2 < \varepsilon_1$, $\varepsilon(\omega) =
\varepsilon_2(\max_tf(\omega(t)))$ and $F(\omega, \alpha) = (\alpha - 1)\varepsilon(\omega) +
\max_{|t - t'| \le \alpha}\rho(\omega(t), \omega(t'))$, the zero $\alpha = 2A(\omega)$ of
$F(\omega, \cdot)$ defines a continuous $A : \Omega^* \to (0, 1]$ such that points of $\omega$ at
times less than $2A(\omega)$ apart are joined by a unique minimal geodesic; $h(\omega)$ is the path
that agrees with $\omega$ at $t = 0, A(\omega), 2A(\omega), \dots, kA(\omega)$ ($k$ the largest
integer in $1/A(\omega)$) and at $t = 1$, and is a geodesic in between; "Clearly $h$ is continuous";
and an argument similar to that in §16 gives $h \circ i \simeq \mathrm{id}$ and
$i \circ h \simeq \mathrm{id}$. *A step that does not hold as we read it:* "Clearly $h$ is continuous" (p. 94) fails
for the metric $d$ of $\Omega$, the topology in which Theorem 17.1 is stated ($h$ is continuous
only for $d^*$). When $1/A(\omega)$ crosses an integer from below, $h(\omega)$ acquires a new last
segment of duration $\delta \to 0$ and length $\ell \to 0$, whose energy $\ell^2/\delta$ need not
tend to $0$; for a continuous path that is not Lipschitz near $t = 1$ it can tend to infinity, and
since $\sqrt E$ is $1$-Lipschitz for $d$ (V10.2), $h$ is then not continuous. The exposition's
example: $M = \mathbb R$, $p = q = 0$, $f(x) = |x|$, $\varepsilon_2 \equiv 1$ and
$\omega_\lambda(t) = \lambda((1 - t)^{1/3} - (1 - t))$; as $\lambda$ decreases to
$\lambda_* = \sqrt3/2$, $\omega_\lambda \to \omega_{\lambda_*}$ uniformly while
$E(h(\omega_\lambda)) \to \infty$. This counterexample is machine-checked (`Morse.milnor_h_not_continuous`,
`Morse.milnor_h_not_continuous'`): with Milnor's $A$ and $h$ defined exactly as on p. 94 for this
choice, $h$ is not continuous at $\omega_{\lambda_*}$ (it was first found by hand and
numerically: `Exposition/Chapter10.md`, §5; `Exposition/Findings.md`). The theorem is true, and what is verified is the theorem itself, by the exposition's
modified proof. (Also, $A$ takes its values in $(0, \frac12]$.) *Hidden hypotheses (of the modified
proof):* good balls convex for minimal geodesics, with one smooth join on each (V10.17); the $L^2$
control of velocities by $d$ (V10.16); $\Omega$ is not Hausdorff for $d$, so Example 1 of the
Appendix (paracompact Hausdorff spaces) is applied to $\Omega^*$ and pulled back by $i$; Theorem A
for open, not closed, pieces (VA.15). *Proof:* the exposition's, not Milnor's: the open sets $Y_k$
exhaust the metric, hence paracompact, space $\Omega^*$, which is therefore the homotopy direct
limit of the $Y_k$ (Example 1, VA.7), and $\Omega$ is that of the $X_k = i^{-1}(Y_k)$ by (i); $i$
carries each $X_k$ into $Y_k$ by a homotopy equivalence (V10.18); Theorem A with no closedness
hypothesis (VA.15) concludes. No completeness is used.

**V10.20 (relative cell complexes and the tower; `Morse.IsRelCellComplexType`,
`Morse.IsRelCellAttachment.transport`, `Morse.IsRelCellComplexType.of_square`,
`Morse.isRelCellComplexType_union_cells`, `Morse.isRelCellComplexType_sublevel_of_isCompact`,
`Morse.isCountableCellComplexType_of_rel`, `Morse.isCountableCellComplexType_of_relSublevel`).** (i)
A map $\iota : A \to X$ is, *up to homotopy, the inclusion of $A$ with cells
$(\lambda_1, \dots, \lambda_k)$ attached* if there are a space $K$ obtained from $A$ by attaching a
$\lambda_1$-cell, then a $\lambda_2$-cell, and so on (VA.18), with $j : A \to K$ the composite of
the inclusions, and a homotopy equivalence $e : X \to K$ with $e \circ \iota \simeq j$. (ii) (Lemma
3.7, relative and iterated) Such an attachment $L \to K$ and a homotopy equivalence $L \to L'$ give
an attachment $L' \to K'$ of the same cells and a homotopy equivalence $K \to K'$ extending
$L \to L'$; and the notion in (i) is invariant under homotopy-commutative squares of homotopy
equivalences. (iii) Disjoint embedded cells meeting a closed set exactly in their boundary spheres
are attached to it one at a time (the exposition's Lemma D, relative). (iv) (the relative Theorem
3.5) For $f = F|N$ on a slice submanifold, $F$ smooth, and levels $b \le a_0$, neither a critical
value, with $N^{a_0}$ compact and the critical points in $N^{a_0}$ non-degenerate, the inclusion
$N^b \to N^{a_0}$ is, up to homotopy, the inclusion of $N^b$ with one cell of dimension the index
for each critical point in $f^{-1}(b, a_0)$, attached in order of non-decreasing value. (v) (the
tower) If $E : X \to \mathbb R$ is continuous, $a_0 \le a_1 \le \cdots$ tend to $\infty$,
$X^{a_0} = \{E \le a_0\}$ has the homotopy type of a finite cell complex with cells
$\mathrm{cells}_0$ (V2.11), and each inclusion $X^{a_n} \to X^{a_{n+1}}$ is, up to homotopy, the
inclusion with cells $\mathrm{cells}_{n+1}$ attached, then $X$ has the homotopy type of the countable
cell complex with cells $\mathrm{cells}_0, \mathrm{cells}_1, \dots$ (VA.18). *Book:* p. 95: by 16.2
together with 3.3 and 3.7, each $\Omega^{a_i}$ has the homotopy type of $\Omega^{a_{i-1}}$ with
finitely many cells attached; "just as in the proof of 3.5", one constructs CW-complexes
$K_0 \subset K_1 \subset \cdots$ with cells of the required description and homotopy equivalences
$\Omega^{a_i} \to K_i$ forming a commutative diagram. *Hidden hypotheses:* "each extending the
previous one": Lemma 3.7 extends a homotopy equivalence over the new cells, but $\Omega^{a_{i+1}}$ is
only homotopy equivalent to $\Omega^{a_i}$ with cells attached, by retractions that move
$\Omega^{a_i}$, so the extension holds only up to homotopy (strict compatibility needs nested
subdivisions, the exposition's Lemma 17.E); and the step needs a relative form of Theorem 3.5, for
pairs of sublevel sets. *Deviation (restated):* the Appendix's comparison of telescopes needs only
homotopy-commutative squares (VA.16 (ii), VA.19), so the tower is built up to homotopy and no nested
subdivisions are needed.

**V10.21 (the step from $\Omega^a$ to $\Omega^b$; `Morse.PathSp.energyC`,
`Morse.BrokenSetup.isRelCellComplexType_nodes`, `Morse.BrokenSetup.omegaEquivNodes`,
`Morse.BrokenSetup.isRelCellComplexType_Omega`, `Morse.BrokenSetup.finite_geodesics`,
`Morse.finite_geodesicEnergies`, `Morse.geodesicIndex`, `Morse.geodesicIndex_eq`).** (i) For Milnor's
data and levels $a \le b < c$, if neither $a$ nor $b$ is $E'(y)$ for a $y \in U$ with $\omega_y$ a
geodesic, and every such $\omega_y$ with $E'(y) \le b$ has nullity $0$, then the inclusion
$\Omega^a \to \Omega^b$ is, up to homotopy (V10.20 (i)), the inclusion of $\Omega^a$ with one cell of
dimension the index of $E_{**}$ at $\omega_y$ for each such $y$ with $a < E'(y) < b$, attached in
order of non-decreasing energy; and likewise for the sublevel sets of $E'$ in $U$. The homotopy
equivalences $\Omega^t \simeq \{y \in U : E'(y) \le t\}$, $t < c$, are given by one formula,
$\omega \mapsto$ the break points of $r_1(\omega)$, so they commute with the inclusions. (ii) If
every $\omega_y$, $y \in U$, that is a geodesic with $E'(y) \le b < c$ has nullity $0$, there are
finitely many such $y$; if $N$ is closed in $V$, $p, q \in N$, and every
geodesic in $\Omega$ has nullity $0$, the energies at most $b$ of the geodesics in $\Omega$ are
finitely many, for every $b$. (iii) The index of a geodesic, as a natural number, equals the index
of $E_{**}$ at it (finite by Theorem 15.1, V9.24). *Book:* p. 95: by 16.2 together with 3.3 and
3.7, each $\Omega^{a_i}$ has the homotopy type of $\Omega^{a_{i-1}}$ with one $\lambda$-cell attached
for each geodesic of index $\lambda$ with energy in $(a_{i-1}, a_i)$. *Hidden hypotheses:* the
choice of levels needs the critical values of $E$ to be discrete, which follows from Theorem 16.3
(finitely many geodesics below each level); the homotopy equivalences with the models must commute
with the inclusions. *Deviation (restated):* each step uses its own manifold of broken geodesics,
with an energy bound $c > b$, and any finite number of critical values between $a$ and $b$.

**V10.22 (Theorem 17.3, the fundamental theorem of Morse theory; `Morse.theorem_17_3_of_levels`,
`Morse.theorem_17_3`, `Morse.theorem_17_3_nonconj`).** Let $N$ be closed in $V$ and $p, q \in N$.
(i) Suppose every geodesic in $\Omega$ has nullity $0$, and let $a_0 \le a_1 \le \cdots$ be levels
tending to $\infty$, with $a_0 < 0$, none of which is the energy of a geodesic. Then there are finite
lists $\mathrm{geo}_0 = \emptyset, \mathrm{geo}_1, \mathrm{geo}_2, \dots$ of geodesics in $\Omega$,
$\mathrm{geo}_{n+1}$ consisting of geodesics with energy in $(a_n, a_{n+1})$, containing one geodesic
that agrees on $[0, 1]$ with each geodesic of that energy and no two that agree on $[0, 1]$, ordered
by energy, such that $\Omega$, with Milnor's metric, has the homotopy type of the countable cell
complex (VA.18) with one cell of dimension the index of $E_{**}$ at $\gamma$ for each entry
$\gamma$. (ii) **Theorem 17.3:** if every geodesic in $\Omega$ has nullity $0$, there are finite lists
$\mathrm{geo}_0, \mathrm{geo}_1, \dots$ of geodesics from $p$ to $q$ such that every geodesic from
$p$ to $q$ agrees on $[0, 1]$ with exactly one entry of exactly one list, the energies increase
strictly from one list to the next and weakly within a list, and $\Omega(N; p, q)$, with Milnor's
metric, has the homotopy type of the countable cell complex with one cell of dimension $\lambda$ for
each entry of index $\lambda$: one $\lambda$-cell for each geodesic from $p$ to $q$ of index
$\lambda$, attached in order of increasing energy. (iii) The same holds if $q$ is not conjugate to
$p$ along any geodesic (V11.4), which makes every nullity $0$ (Theorem 14.1, V9.6). *Book:* p. 95,
Theorem 17.3: if $M$ is complete and $p, q$ are not conjugate along any geodesic, then
$\Omega(M; p, q)$ (or $\Omega^*(M; p, q)$) has the homotopy type of a countable CW-complex containing
one cell of dimension $\lambda$ for each geodesic from $p$ to $q$ of index $\lambda$. Proof, p. 95:
levels $a_0 < a_1 < \cdots$, not critical values, with "precisely one" critical value in each
interval and $\Omega^{a_0}$ empty; 16.2 with 3.3 and 3.7 at each step; the tower of CW-complexes
(V10.20); the direct limit map $\Omega \to K$ induces isomorphisms of homotopy groups, hence is a
homotopy equivalence by Whitehead's theorem, since $\Omega$ has the homotopy type of a CW-complex
(17.2); and a reference to a different proof, not using 17.1, on p. 149. *Hidden hypotheses:* the
$a_i$ must tend to infinity, or the $\Omega^{a_i}$ do not exhaust $\Omega$; "precisely one" critical
value in each interval is impossible when there are finitely many geodesics, and "at most one"
suffices; the compatibility of the tower (V10.20). *Deviation (narrower):* completeness is replaced
by the closedness of $N$ in $V$, which implies it (V7.30) and is used only through the compactness
of the balls $S$ (V10.3); the statement is for $\Omega$, not for $\Omega^*$; the "countable
CW-complex" is the mapping telescope of a tower of cell attachments (VA.18). *Deviation (restated):*
geodesics are counted by their values on $[0, 1]$; an interval between consecutive levels may
contain several critical values, whose cells are attached in order of energy. *Proof:* Milnor's
second route, Theorem A of the Appendix (VA.19), through V10.20 (v) and V10.21; neither Whitehead's
theorem nor Corollary 17.2 is used.

**V10.23 (the geodesics from $p$ to $q$ on $S^n$, and their indices; `Morse.greatCircle`,
`Morse.isGeodesicOn_greatCircle`, `Morse.energy_greatCircle`, `Morse.exists_eqOn_greatCircle`,
`Morse.isJacobiField_sin_smul`, `Morse.isJacobiField_smul_deriv_greatCircle`,
`Morse.conjMultiplicity_greatCircle`, `Morse.sphLen`, `Morse.sphGeod`, `Morse.mul_pi_lt_sphLen`,
`Morse.sphLen_lt`, `Morse.energy_sphGeod`, `Morse.exists_eqOn_sphGeod`, `Morse.notMem_conjLocus_sph`,
`Morse.formIndex_sphGeod`, `Morse.formIndex_eq_of_eqOn_sphGeod`,
`Morse.formIndex_energyHessian_congr`).** $S^n \subseteq \mathbb R^{n+1}$ is the unit sphere with the
induced metric (V6.25), $n \ge 1$. (i) For unit vectors $p \perp u$ and $L \in \mathbb R$,
$c(t) = \cos(Lt)\,p + \sin(Lt)\,u$ is a geodesic of $S^n$ on $\mathbb R$, with energy $L^2$ on
$[0, 1]$; every geodesic $\gamma \in \Omega(S^n; p, q)$ agrees on $[0, 1]$ with such a $c$, with
$L \ge 0$. (ii) For every $e \perp p, u$, $t \mapsto \sin(Lt)\,e$ is a Jacobi field along $c$, and so
is $t \mapsto t\,c'(t)$; for $L > 0$ and $0 < t \le 1$, the multiplicity of $0$ and $t$ as conjugate
parameters along $c$ (V9.4) is $n - 1$ if $Lt$ is a multiple of $\pi$, and $0$ otherwise. (iii) Let
$q \ne \pm p$, $\theta \in
(0, \pi)$ the angle between $p$ and $q$, and $u \perp p$ the unit vector with $q = \cos\theta\,p +
\sin\theta\,u$; let $\gamma_{2j}$ be the great circle along $u$ with $L_{2j} = \theta + 2\pi j$, and
$\gamma_{2j+1}$ the one along $-u$ with $L_{2j+1} = 2\pi(j + 1) - \theta$. These are geodesics in
$\Omega(S^n; p, q)$ with $E(\gamma_k) = L_k^2$ and $k\pi < L_k < (k + 1)\pi$; every geodesic in
$\Omega(S^n; p, q)$ agrees on $[0, 1]$ with some $\gamma_k$; $q$ is not conjugate to $p$ along any
geodesic (V11.4); and the index of $E_{**}$ at $\gamma_k$, and at every geodesic that agrees with
$\gamma_k$ on $[0, 1]$, is $k(n - 1)$. *Book:* pp. 95–96, the example of the path space of $S^n$:
for $q \ne p, p'$, $p'$ the antipode of $p$, the geodesics from $p$ to $q$ are $\gamma_0$, the short
great circle arc, $\gamma_1$, the long arc $pq'p'q$, $\gamma_2 = pqp'q'pq$, and so on; $k$ is the
number of times $p$ or $p'$ occurs in the interior of $\gamma_k$, and $\lambda(\gamma_k) = k(n - 1)$
since each of these points is conjugate to $p$ with multiplicity $n - 1$; p. 80 (Example 2 of §14):
antipodal points are conjugate along a great semicircle with multiplicity $n - 1$. *Hidden
hypotheses:* that $q \ne p, p'$ makes $p, q$ non-conjugate along every geodesic needs the conjugate
points along every great circle through $p$ and the list of all geodesics from $p$ to $q$; the
multiplicity is exactly $n - 1$ (Remark 14.2, V9.7) and no other interior point is conjugate to $p$;
that every geodesic is a great circle uses the uniqueness of geodesics after extending the segment
past $t = 0$ (V9.9 (ii)); "$k$ occurrences" is the inequality $k\pi < L_k < (k + 1)\pi$; the index
comes from Theorem 15.1 (V9.24). *Deviation (restated):* of Milnor's rephrasing of non-conjugacy as
$q \ne p, p'$, the direction Theorem 17.3 needs is proved; the index does not depend on the values
off $[0, 1]$. *Proof:* the Jacobi fields are checked directly with $R(x, y)z = \langle x, z\rangle y
- \langle y, z\rangle x$, not by rotations and Lemma 14.3; the fields $\sin(Lt)\,e$ and $t\,c'(t)$
span the $n$-dimensional space of Jacobi fields vanishing at $0$ (V9.7).

**V10.24 (Corollary 17.4 for $\Omega(S^n; p, q)$; `Morse.oneCellEach`, `Morse.omega_cells_of_unique`,
`Morse.strictMono_energy_sphGeod`, `Morse.tendsto_energy_sphGeod`, `Morse.corollary_17_4`).** (i) Let
$N$ be closed in $V$, $p, q \in N$, every geodesic in $\Omega$ of nullity $0$, and suppose that the
geodesics in $\Omega$ are, up to their values off $[0, 1]$, a sequence $g_0, g_1, \dots$ with
strictly increasing energies tending to $\infty$, every geodesic agreeing with $g_k$ on $[0, 1]$
having index $d_k$. Then $\Omega$ has the homotopy type of the countable cell complex (VA.18) with no
cell at stage $0$ and one cell of dimension $d_k$ at stage $k + 1$. (ii) **Corollary 17.4:** for
$n \ge 2$ and $p, q \in S^n$ with $q \ne \pm p$, $\Omega(S^n; p, q)$, with Milnor's metric, has the
homotopy type of the countable cell complex with one cell in each of the dimensions
$0, n - 1, 2(n - 1), \dots$, attached in this order. *Book:* p. 96, Corollary 17.4: the loop space
$\Omega(S^n)$ has the homotopy type of a CW-complex with one cell each in the dimensions
$0, n - 1, 2(n - 1), 3(n - 1), \dots$, derived from Theorem 17.3 and the example (V10.23), whose end
points are non-conjugate. *Hidden hypotheses:* in the loop space, $p$ is conjugate to itself along
every great circle; passing to loops needs that $\Omega^*(S^n; p, q)$ does not depend on $q$ up to
homotopy (the exposition's Lemma 17.D) and Theorem 17.1. *Deviation (narrower):* the path space
$\Omega(S^n; p, q)$, $q \ne \pm p$, which is what Milnor's argument gives, not the loop space;
$n \ge 2$ (the case $n = 1$, with every cell a point, is not stated); a countable cell complex in
the sense of VA.18. *Proof:* V10.22 (i) with levels halfway between consecutive energies, one
geodesic in each interval, and V10.23.

**V10.25 (the homology of a path space read off from its geodesics;
`Morse.Homology.subsingleton_subsetHomology_univ_of_exhaustion`,
`Morse.Homology.nonempty_linearEquiv_spaceHomology_of_exhaustion`, `Morse.Homology.bettiNumber_eq_of_steps`,
`Morse.Homology.exists_subset_sublevel_of_isCompact`, `Morse.Homology.sublevel_step_of_isCompact`,
`Morse.BrokenSetup.finrank_subsetHomology_Omega`, `Morse.windowLevels`, `Morse.finrank_window`,
`Morse.bettiNumber_omega_of_unique`).** Homology is singular homology with coefficients in a field
$\Bbbk$, and $b_i = \dim_\Bbbk H_i$ (V3.33). (i) Let $A_0 \subseteq A_1 \subseteq \cdots$ be subsets
of a space $X$ such that every compact subset of $X$ lies in some $A_k$ (for instance the sublevel
sets of a continuous function at levels unbounded above). If $H_j(A_k, A_{k_0}) = 0$ for all
$k \ge k_0$, then $H_j(X, A_{k_0}) = 0$; and if the steps $H_*(A_{k+1}, A_k)$ vanish in degrees $i$
and $i + 1$ for all $k \ge k_0$, then $b_i(X) = \dim H_i(A_{k_0})$. (ii) The homology of a slab
(V3.33–V3.34) is computed in the same way for a slice submanifold that need not be compact, below a
level whose sublevel set is compact. (iii) For Milnor's data and levels $a \le b < c$, neither the
energy of a geodesic, with at most one energy of a geodesic in $(a, b)$ and every geodesic of energy
at most $b$ of nullity $0$, $H_j(\Omega^b, \Omega^a)$ is finite-dimensional, of dimension the number
of geodesics with energy in $(a, b)$ and index $j$. (iv) In the situation of V10.24 (i), with levels
halfway between consecutive energies, $H_j(\Omega^{a_{k+1}}, \Omega^{a_k})$ is $\Bbbk$ for $j = d_k$
and $0$ otherwise; and if $d_k = kr$ with $r \ge 2$, then $b_i(\Omega) = 1$ when $r$ divides $i$ and
$0$ otherwise. *Book:* p. 96: for $n > 2$ the homology of $\Omega(S^n)$ "can be computed immediately"
from the cells of Corollary 17.4. *Hidden hypotheses:* reading the homology off the cells is cellular
homology, which needs cellular attaching maps; that the homology of $\Omega$ is the limit of that of
the $\Omega^a$ needs every compact subset of $\Omega$ to have bounded energy, true for $d$ since $E$
is continuous (V10.2), false for $d^*$; the vanishing is needed in degrees $i$ and $i + 1$.
*Deviation (restated):* the homology is computed from the filtration of $\Omega$ by the sets
$\Omega^a$, with the lacunary principle (Corollary 5.4, V3.15) on the finite stages, rather than from
a cellular chain complex; the coefficients form a field.

**V10.26 (the homology of $\Omega(S^n; p, q)$; `Morse.bettiNumber_sphere_paths`).** For $n \ge 3$,
$p, q \in S^n$ with $q \ne \pm p$, and every field $\Bbbk$, $\dim_\Bbbk H_i(\Omega(S^n; p, q); \Bbbk)$
is $1$ if $n - 1$ divides $i$ and $0$ otherwise. *Book:* p. 96: for $n > 2$ the homology of
$\Omega(S^n)$ is computed from Corollary 17.4, and $\Omega(S^n)$ has non-trivial homology in
infinitely many dimensions. *Hidden hypotheses:* $n > 2$, so that no two cells have consecutive
dimensions; for loops, Lemma 17.D and Theorem 17.1 as in V10.24. *Deviation (narrower):* the path
space with $q \ne \pm p$; coefficients in a field, not the integers. *Proof:* V10.25 (iv) with
$r = n - 1$, and V10.23.

**V10.27 (Corollary 17.5 needs completeness; `Morse.isSliceSubmanifold_of_isOpen`,
`Morse.tangentSubspace_of_isOpen`, `Morse.curvR_eq_zero_of_top`,
`Morse.IsUnbrokenGeodesic.eqOn_segment_of_top`, `Morse.IsJacobiField.eqOn_affine_of_top`,
`Morse.not_isConjugate_of_top`, `Morse.formIndex_energyHessian_eq_zero_of_top`,
`Morse.hessNullity_eq_zero_of_top`, `Morse.unique_geodesic_of_top`, `Morse.puncturedSub`,
`Morse.not_isGeodesicallyComplete_puncturedSub`, `Morse.not_isClosed_punctured`,
`Morse.isPathConnected_punctured`, `Morse.puncturedHomotopyEquiv`, `Morse.remark_17_5_completeness`).**
(i) An open subset of $V$ is a slice submanifold of $V$ of codimension $0$, with every tangent space
equal to $V$. (ii) If every tangent space of $N$ is $V$, the induced metric is flat ($P = 1$,
$\mathrm{II} = 0$, $R = 0$); every geodesic in $\Omega(N; p, q)$ agrees on $[0, 1]$ with the segment
$t \mapsto p + t(q - p)$; Jacobi fields are affine, so no two parameters are conjugate along a curve
in $N$, and every geodesic has index $0$ and nullity $0$; and if the segment from $p$ to $q$ lies in
$N$, it is a geodesic in $\Omega(N; p, q)$ and every geodesic in $\Omega(N; p, q)$ agrees with it on
$[0, 1]$. (iii) For $n \ge 1$, $N = \mathbb R^{n+1} \setminus \{0\}$ with the induced (flat) metric
is homotopy equivalent to $S^n$ and path-connected; it is neither closed in $\mathbb R^{n+1}$ nor
geodesically complete ($\exp_q(-q)$ is undefined); no point of $N$ is conjugate to another along any
geodesic; and there are $p \ne q$ in $N$ joined by exactly one geodesic. *Book:* p. 96, Corollary
17.5: if $M$ has the homotopy type of $S^n$, $n > 2$, any two non-conjugate points of $M$ are joined
by infinitely many geodesics; completeness is not among its hypotheses, although the proof rests on
Theorem 17.3, which assumes it (the Remark on p. 97 assumes it). *Hidden hypotheses:* the
completeness of $M$. *Deviation (not in the book):* the example shows that this hypothesis cannot be
dropped: for $n \ge 3$, $N$ satisfies the hypotheses of Corollary 17.5 as printed and not its
conclusion. That $\Omega(N; p, q)$ is not homotopy equivalent to a point, which would contradict
Theorem 17.3 without completeness for every $n \ge 1$, is not formalized; what is proved is that $N$
satisfies every hypothesis of the formal Theorem 17.3 (V10.22 (iii)) except closedness in the
ambient space.

**V10.28 (moving the end point, the exposition's Lemma 17.D with Theorem 17.1;
`Morse.joined_of_riemDist_lt_top`, `Morse.exists_joined_notMem_conjLocus`,
`Morse.pathSpHomotopyEquiv`, `Morse.Homology.spaceHomologyEquivOfHomotopyEquiv`,
`Morse.Homology.bettiNumber_eq_of_homotopyEquiv`).** Let $N$ be a slice submanifold of $V$ and
$p, q \in N$. (i) Two points of $N$ at finite Riemannian distance are joined by a path in $N$, and
$q$ is joined by a path in $N$ to a point $q' \in N$ which is not conjugate to $p$ along any
geodesic. (ii) A path in $N$ from $q$ to $q'$ gives a homotopy equivalence
$\Omega(N; p, q) \simeq \Omega(N; p, q')$ of path spaces with Milnor's metric. (iii) Homotopy
equivalent spaces have isomorphic homology over a field, hence the same Betti numbers. *Book:* p.
96: the loop space of $S^n$ is treated through the paths from $p$ to a point $q \neq p, p'$, without
comment; p. 106: Theorem 19.6 is stated for all $p, q$ and proved for non-conjugate ones. *Hidden
hypotheses:* that the homotopy type of the path space does not depend on the end point within a path
component. *Deviation (not in the book):* (i) is the density of the non-conjugate points (V11.6) in
a small ball about $q$; (ii) composes Theorem 17.1 (V10.19), the homeomorphism of $\Omega^*$ with
Mathlib's space of paths, and composition of paths with the given one.

**V10.29 (Corollary 17.2; `Morse.corollary_17_2`, `Morse.corollary_17_2_pathC`).** Let $N$ be closed
in $V$ and $p, q \in N$. Then $\Omega(N; p, q)$, with Milnor's metric, has the homotopy type of a
countable cell complex (VA.18), and so does the space $\Omega^*(N; p, q)$ of continuous paths with
the compact-open topology. *Book:* p. 95: "It is known that the space $\Omega^*$ has the homotopy
type of a CW-complex" (Milnor, 1959); therefore (Corollary 17.2) $\Omega$ has the homotopy type of a
CW-complex. *Hidden hypotheses:* none. *Deviation (restated):* Milnor's theorem of 1959 is not used:
$q$ is moved to a point $q'$ not conjugate to $p$ (V10.28), and Theorem 17.3 (V10.22) gives a
countable cell complex for $\Omega(N; p, q')$. *Deviation (narrower):* $N$ closed in $V$, hence
complete, which Milnor's corollary does not assume; a countable cell complex in the sense of VA.18,
with cells attached along arbitrary maps.

**V10.30 (Corollary 17.4 for the loop space, and its homology;
`Morse.exists_loop_homotopyEquiv_sph`, `Morse.corollary_17_4_loop`,
`Morse.bettiNumber_sphere_loops`).** Let $n \ge 2$ and $p \in S^n$. The loop space
$\Omega(S^n; p, p)$ is homotopy equivalent to $\Omega(S^n; p, q)$ for some $q \neq \pm p$, and it
has the homotopy type of the countable cell complex with one cell in each of the dimensions
$0, n - 1, 2(n - 1), 3(n - 1), \dots$, attached in this order. For $n \ge 3$ and every field
$\mathbb k$, $\dim H_i(\Omega(S^n; p, p); \mathbb k)$ is $1$ if $n - 1$ divides $i$ and $0$
otherwise. *Book:* p. 96, Corollary 17.4: the loop space $\Omega(S^n)$ has the homotopy type of a
CW-complex with one cell each in the dimensions $0, n - 1, 2(n - 1), 3(n - 1), \dots$. *Hidden
hypotheses:* $p$ is conjugate to itself along every great circle, so Theorem 17.3 does not apply to
loops; the end point must be moved (V10.28). *Deviation (narrower):* $n \ge 2$ (and $n \ge 3$ for
the homology, over fields); a cell complex in the sense of VA.18. The path-space form is V10.24 and
V10.26.

### What is not verified in this chapter

- **Milnor's route to Corollary 17.2** (p. 95): his theorem that $\Omega^*$ has the homotopy type of
  a CW-complex (*On spaces having the homotopy type of a CW-complex*, 1959) is not in Mathlib. The
  corollary is proved for $N$ closed in $V$ by moving the end point (V10.29); for a manifold that is
  not complete it is not verified. Theorem 17.3 does not use it (V10.22).
- **Theorem 17.3 for $\Omega^*$** (p. 95): not stated; it would follow from V10.22 and Theorem 17.1
  (V10.19) by composing homotopy equivalences.
- **Corollary 17.4 for $n = 1$** (p. 96): not stated (V10.24). The loop-space form for $n \ge 2$ is
  V10.30.
- **The homology of the path spaces of $S^2$, and integral homology**: for $n = 2$ there is a cell in
  every dimension and the lacunary principle does not apply; $H_j(\Omega S^2) \cong \mathbb Z$ for all
  $j$ (through the Hopf fibration, quoted in the exposition) is not formalized. For $n \ge 3$ the
  homology is computed over fields only, not over $\mathbb Z$ (V10.26).
- **Corollary 17.5 itself** (p. 96): that two non-conjugate points of a complete $M$ of the homotopy
  type of $S^n$, $n > 2$, are joined by infinitely many geodesics needs the homotopy invariance of
  $\Omega^*$ (the loop spaces of homotopy equivalent spaces are weakly equivalent, and have the same
  homology) and the homology of the countable cell complex of Theorem 17.3; only the counterexample
  without completeness is verified (V10.27).
- **Serre's remark** (p. 97): Serre's theorem on the homology of loop spaces (the spectral sequence
  of the path fibration) and the passage to the universal cover are not formalized. The Freudenthal
  suspension theorem, to which the remark is applied, is verified in Chapter 13 by the route of §22
  (V13.9).
- **Milnor's construction in the proof of Theorem 17.1** (pp. 93–94) in general: $\varepsilon_1$,
  $\varepsilon_2$, $A(\omega)$ and $h$ (the exposition's Lemma 17.A) are formalized only for
  $M = \mathbb R$ with $\varepsilon_2 \equiv 1$, where they serve the machine-checked counterexample to
  the continuity of $h$ (V10.19).
- **Theorem 16.3 at a critical level** (p. 90): when $a$ is the energy of a geodesic; the formal
  statements assume it is not (V10.12–V10.13).
- **The Remark on p. 92 for the length**: that the geodesic minimizing the energy is shortest is not
  stated (V10.14).
- **CW-complexes**: cellular approximation is not in Mathlib, so cells are attached along arbitrary
  maps (V2.11, VA.18); the exposition's Lemma 17.E (a strictly compatible tower from nested
  subdivisions) is neither formalized nor needed (V10.20).
- **The exposition's interactive figure (§4) and its §7** (seismic surface waves on the round Earth):
  not formalized.
- **§§16–17 on an abstract Riemannian manifold**: only for submanifolds of a Euclidean space with the
  induced metric; Nash's embedding theorem is quoted, not proved.

---

## 12. Chapter 11 (Milnor §§18–19): partly verified

Milnor's §18 (pp. 98–99) shows that $\exp_p(v)$ is conjugate to $p$ along $t \mapsto \exp_p(tv)$
exactly when $\exp_p$ is critical at $v$ (Theorem 18.1), so that by Sard's theorem almost every $q$
is conjugate to $p$ along no geodesic (Corollary 18.2); this justifies the hypothesis of Theorem
17.3. §19 (pp. 100–107) relates curvature and topology. If $\langle R(A, B)A, B\rangle \le 0$, no
two points are conjugate along any geodesic (Lemma 19.1); with §17 this makes a simply connected
complete such manifold diffeomorphic to $\mathbb R^n$ by $\exp_p$ (Theorem 19.2, Cartan) and gives
Corollary 19.3 on homotopy groups. If the Ricci curvature is at least $(n - 1)/r^2$, every geodesic
longer than $\pi r$ contains conjugate points and is not minimal (Theorem 19.4, Myers), a complete
such manifold is compact of diameter at most $\pi r$ (Corollary 19.5), and on a compact manifold
with positive definite Ricci tensor $\Omega(M; p, q)$ has the homotopy type of a CW-complex with
finitely many cells in each dimension (Theorem 19.6). Verified, for a submanifold $N$ of a Euclidean
space with the induced metric, in the embedded setting of Chapters 6–9: the smoothness of $\exp$ on
its whole domain, which Milnor uses and §10 does not provide (V11.1); Theorem 18.1 with the
multiplicity, and Corollary 18.2, without completeness; the density of non-conjugate points; Lemma
19.1, with the steps of the proof of 19.2 that need only the index theorem and 18.1 (index $0$,
$E_{**}$ positive definite, $\exp_p$ non-critical); the Ricci tensor, its symmetry and Milnor's
Assertion; Theorem 19.4 and Corollary 19.5, for $n \ge 2$, a hypothesis the book leaves silent; the
example of the unit sphere; and the index estimate in the proof of Theorem 19.6 (a geodesic longer
than $k\pi r$ has index at least $k$). With §17 (Chapter 10) and the covering $\exp_p$: Theorem
19.2 (Cartan–Hadamard) and Milnor's description of the path space in curvature $\le 0$, the
statement that each homotopy class of paths contains one geodesic, and the first half of Corollary
19.3 (V11.17–V11.21); and Theorem 19.6, for all end points, with the finiteness of the homology of
the path space (V11.22–V11.24). Every Riemannian manifold is such an $N$ by Nash's embedding
theorem, which is quoted, not proved. **Not verified:** the second half of Corollary 19.3 (no
torsion in $\pi_1$); the finiteness of $\pi_1$ under a positive Ricci bound; the optics paragraph,
the examples and the remarks of §19; and the sectional curvature as a Gaussian curvature (the list
at the end). Lean: `Morse/Chapter11/` — `ExpSmooth.lean` (695 lines), `NonConjugate.lean` (242),
`Curvature.lean` (304), `Myers.lean` (619), `LongGeodesics.lean` (470), `ExpCovering.lean` (707),
`CartanHadamard.lean` (687), `PositiveRicci.lean` (266), `RicciHomology.lean` (252),
`PositiveRicciAll.lean` (73).

**The embedded setting.** As in Chapters 8 and 9: $V$ is a finite-dimensional real inner product
space and $N \subseteq V$ a slice submanifold modelled on $Z$ with complement $W$ (V1.6), with the
induced metric; every tangent space $T_qN$, $q \in N$, has dimension $n = \dim Z$; $R$ is Milnor's
curvature tensor, with his sign (V6.16–V6.17), and the sectional curvature is that of V6.22. The
exponential map, its domain and the tangent manifold $TN$ are those of V7.7–V7.8; $\Omega(N; p, q)$,
$T\Omega_\gamma$, the geodesics of $\Omega$ and $E_{**}$ those of V8.1, V8.10 and V8.14; smooth
curves in $N$ on $[0, 1]$, Jacobi fields, the space $\mathcal J(\gamma)$, conjugate parameters with
their multiplicity, and the index and nullity of $E_{**}$ those of V9.2–V9.4, V9.6 and V9.13. A
*geodesic from $p$* is a smooth curve $\gamma$ in $N$ on $[0, 1]$ with $\gamma(0) = p$ which is a
geodesic on $(0, 1)$; "$\gamma(t)$ is conjugate to $\gamma(0)$" reads "$t$ is conjugate to $0$"
(V9.4). $L(\gamma)$ is the length of $\gamma$ on $[0, 1]$ (V7.11), and $\rho$ the distance of V7.18.
$N$ need not be closed, compact, connected or complete unless this is stated.

**V11.1 ($\exp$ is smooth on its whole domain; `Morse.RaysGoodE`, `Morse.raysGoodE_of_isGeodesicOn`,
`Morse.exists_retraction`, `Morse.expDom_subset_tangentBundleSet`, `Morse.mem_expDom_of_isGeodesicOn`,
`Morse.exists_contDiffOn_exp`, `Morse.exists_isOpen_expDom`, `Morse.contMDiffOn_exp_expDom`).**
(i) Let $E$ be a real normed space, $U_0 \subseteq E$ open, $u_0 \in U_0$, and $c, w : E \to V$ of
class $C^\infty$ on $U_0$ with $c(u) \in N$ and $w(u) \in T_{c(u)}N$ for $u \in U_0$. If
$t \mapsto \exp_{c(u_0)}(t\,w(u_0))$ is a geodesic on $(-\delta, B + \delta)$, $B \ge 0$,
$\delta > 0$, there are $\varepsilon, \eta > 0$ such that the ball of radius $\varepsilon$ about
$u_0$ lies in $U_0$, every $t \mapsto \exp_{c(u)}(t\,w(u))$ with $u$ in this ball is a geodesic on
$(-\eta, B + \eta)$, and $(u, t) \mapsto \exp_{c(u)}(t\,w(u))$ is $C^\infty$ on the product of the
ball with $(-\eta, B + \eta)$. (ii) Every point of $N$ has an open neighbourhood $U$ in $V$ with a
map $r$, $C^\infty$ on $U$, with values in $N$ and fixing the points of $N \cap U$. (iii) The domain
of $\exp$ lies in $TN$; a point $(y, w)$ of $TN$ is in it as soon as $t \mapsto \exp_y(tw)$ is a
geodesic on an open interval containing $[0, 1]$; and near every point $(p, v)$ of the domain there
are an open set $O \subseteq V \times V$ and a map $F$, $C^\infty$ on $O$, such that every point of
$TN \cap O$ is in the domain and $\exp = F$ there. Hence the domain is $TN \cap O'$ for an open
$O' \subseteq V \times V$, and $(q, v) \mapsto \exp_q(v)$ is $C^\infty$ on it as a map on the
manifold $TN$. *Book:* p. 98: a critical point is defined for a smooth map between manifolds of the
same dimension and applied to $\exp = \exp_p : TM_p \to M$, so $\exp_p$ is treated as smooth on all
of $TM_p$; $M$ is assumed complete so that $\exp$ is everywhere defined, "although this assumption
could easily be eliminated". *Hidden hypotheses:* the smoothness of $\exp$ away from the zero
section, i.e. the smooth dependence of geodesics on their initial data over a compact time
interval: §10 (Lemma 10.2) gives it only near the zero section (V7.8), and V7.23 (iv) only the
continuity of $\exp$ on its domain. *Deviation (stronger):* the whole domain, without completeness.
*Proof:* (i) continues the geodesics step by step with the local smooth flow (V9.9 (i)), as in V9.9
(iii), now with parameters in any normed space; (ii) from a slice chart $\sigma$,
$r(y) = \sigma^{-1}(\sigma(y)_1, 0)$; (iii) is (i) with $E = V \times V$ and the data
$(y, w) \mapsto (r(y), P_{r(y)}w)$, which agree with $(y, w)$ on $TN$.

**V11.2 ($\exp_q$ and its derivative; `Morse.expDomAt`, `Morse.zero_mem_expDomAt`,
`Morse.smul_mem_expDomAt`, `Morse.exists_contDiffAt_expAt`, `Morse.isOpen_expDomAt`,
`Morse.contDiffOn_expAt`, `Morse.dExpAt`, `Morse.isGeodesicOn_ray`, `Morse.isSmoothCurveIn_ray`,
`Morse.expDomAt_eq_univ`).** For $q \in N$ let $\mathcal D_q \subseteq T_qN$ be the set of $v$ with
$(q, v)$ in the domain of $\exp$. It contains $0$, contains $tv$ for every $v \in \mathcal D_q$ and
$0 \le t \le 1$, is open in $T_qN$, and $\exp_q$ is $C^\infty$ on it, as a map from the vector space
$T_qN$ to $V$. For $v \in T_qN$, $d(\exp_q)_v : T_qN \to V$ is the derivative of this map at $v$,
and $\exp_q$ is *critical* at $v$ if $d(\exp_q)_v$ is not one-to-one. For $v \in \mathcal D_q$,
$\gamma_v(t) = \exp_q(tv)$ is a geodesic on an open interval containing $[0, 1]$ and a smooth curve
in $N$ on $[0, 1]$. If $N$ is geodesically complete (V7.22), $\mathcal D_q = T_qN$. *Book:* p. 98:
a smooth map $f$ between manifolds of the same dimension is critical at $x$ if
$f_* : TN_x \to TM_{f(x)}$ is not one-to-one; this is applied to $\exp_p : TM_p \to M$, with
$X \in T(TM_p)_v$ the tangent space at $v$ of $TM_p$ "considered as a manifold"; $\gamma_v$ is the
geodesic $t \mapsto \exp tv$ from $p$ to $\exp v$. *Hidden hypotheses:* without completeness, that
the domain of $\exp_p$ is open and star-shaped about $0$ (V11.1). *Deviation (restated):*
$T(TM_p)_v$ is identified with $T_qN$, as Milnor does on p. 99 (paths $v_i(u)$ in $TM_p$ with
$dv_i/du(0) = X_i$), and $d(\exp_q)_v$ takes values in $V$; whether it is one-to-one does not
depend on the target. *Deviation (stronger):* no completeness.

**V11.3 (Theorem 18.1; `Morse.expJacobi`, `Morse.expJacobi_zero`, `Morse.expJacobi_one`,
`Morse.isJacobiField_expJacobi`, `Morse.covAlong_expJacobi_zero`, `Morse.expJacobi_mem_jacobiSpace`,
`Morse.expJacobi_injective`, `Morse.eq_expJacobi`, `Morse.conjSpace_eq_map_ker`,
`Morse.theorem_18_1_multiplicity`, `Morse.theorem_18_1`).** Let $q \in N$ and $v \in \mathcal D_q$.
For $X \in T_qN$ let $W_X(t) = t\,d(\exp_q)_{tv}(X)$ for $t \in [0, 1]$, constant off $[0, 1]$.
(i) $X \mapsto W_X$ is linear; each $W_X$ is a Jacobi field along $\gamma_v$, in $\mathcal
J(\gamma_v)$ (V9.3), with $W_X(0) = 0$, $\frac{DW_X}{dt}(0) = X$ and $W_X(1) = d(\exp_q)_v(X)$.
(ii) $X \mapsto W_X$ is injective, and every field of $\mathcal J(\gamma_v)$ vanishing at $0$ is a
$W_X$. (iii) The fields of $\mathcal J(\gamma_v)$ vanishing at $0$ and $1$ are exactly the $W_X$
with $X \in \ker d(\exp_q)_v$; so the multiplicity of the conjugate parameters $0$ and $1$ along
$\gamma_v$ (V9.4) is $\dim\ker d(\exp_q)_v$. (iv) **Theorem 18.1:** $0$ and $1$ are conjugate along
$\gamma_v$ if and only if $\exp_q$ is critical at $v$. *Book:* p. 98, Theorem 18.1: the point
$\exp v$ is conjugate to $p$ along the geodesic $\gamma_v$ from $p$ to $\exp v$ iff the mapping
$\exp$ is critical at $v$. Proof (pp. 98–99): if $\exp_*X = 0$ with $X \ne 0$, a path $v(u)$ in
$TM_p$ with $v(0) = v$ and $\frac{dv}{du}(0) = X$ gives the variation $\alpha(u, t) = \exp tv(u)$
through geodesics, whose variation field $W$ is a Jacobi field with $W(0) = 0$,
$W(1) = \exp_*X = 0$ and $\frac{DW}{dt}(0) = \frac{D}{du}v(u)|_{u=0} \ne 0$; conversely, if $\exp_*$
is non-singular at $v$, independent $X_1, \dots, X_n$ give Jacobi fields $W_1, \dots, W_n$ vanishing
at $p$ whose values $\exp_*(X_i)$ at $\exp v$ are independent, and since $n$ is the dimension of the
space of Jacobi fields along $\gamma_v$ vanishing at $p$, "clearly" no non-trivial Jacobi field
vanishes at both $p$ and $\exp v$. *Hidden hypotheses:* the smoothness of $\exp_p$ on its domain
(V11.1); $\frac{DW}{dt}(0) = \frac{D}{du}v(u)$ needs the symmetry lemma 8.7 and the covariant
derivative along the constant curve $u \mapsto \alpha(u, 0) = p$; the dimension $n$ is that of
Remark 14.2 (V9.7). *Deviation (stronger):* the multiplicity equals $\dim\ker d(\exp_q)_v$, which
Milnor does not state (the exposition's form of 18.1); no completeness. *Deviation (restated):*
"$\exp v$ conjugate to $p$ along $\gamma_v$" is the conjugacy of the parameters $0$ and $1$.
*Proof:* Milnor's variation with the straight line $v(u) = v + uX$, whose variation field is $W_X$
(V9.8); $\frac{DW_X}{dt}(0) = d(\exp_q)_0(X) = X$ by $d(\exp_q)_0 = \mathrm{id}$ (V7.8 (iii)),
without the symmetry lemma; (ii) and (iii) use that a Jacobi field is determined by $J(0)$ and
$\frac{DJ}{dt}(0)$ (V9.3) in place of the dimension count.

**V11.4 (the conjugate locus is the set of critical values of $\exp_p$; `Morse.conjLocus`,
`Morse.IsConjugate.congr_curve`, `Morse.IsConjugate.congr_curve_iff`, `Morse.theorem_18_1_of_geodesic`,
`Morse.conjLocus_eq`, `Morse.conjLocus_eq_of_complete`).** For $p \in V$, the *conjugate locus*
$C(p)$ is the set of $q$ for which there is a geodesic $\gamma$ from $p$ with $\gamma(1) = q$ along
which $0$ and $1$ are conjugate; conjugacy depends only on $\gamma$ on $[0, 1]$. Let $p \in N$.
For every geodesic $\gamma$ from $p$, its one-sided initial velocity $v$ lies in $\mathcal D_p$,
$\exp_p(v) = \gamma(1)$, and $0$ and $1$ are conjugate along $\gamma$ iff $\exp_p$ is critical at
$v$. Hence $C(p) = \exp_p(\{v \in \mathcal D_p : \exp_p \text{ is critical at } v\})$, the set of
critical values of $\exp_p$; if $N$ is geodesically complete, $\mathcal D_p = T_pN$. *Book:* p. 99:
Corollary 18.2 "follows immediately from 18.1 together with Sard's theorem (6.1)". *Hidden
hypotheses:* every geodesic from $p$ is a radial geodesic $t \mapsto \exp_p(tv)$ (uniqueness of
geodesics, and the extension of a geodesic segment past its end points); without completeness, that
the domain of $\exp_p$ is open (V11.1). *Deviation (not in the book):* the conjugate locus is named
and identified as a set. *Proof:* $\gamma$ agrees on $[0, 1]$ with $t \mapsto \exp_p(tv)$ (V9.9
(ii)), and Theorem 18.1 (V11.3) applies.

**V11.5 (Corollary 18.2; `Morse.corollary_18_2`).** Let $p \in N$, let $\sigma$ be a slice chart of
$N$ (V1.6), and $\mu$ a Haar measure on $Z$. Then the image of $C(p) \cap \operatorname{dom}\sigma$
under the chart $y \mapsto \sigma(y)_1$ has $\mu$-measure $0$: $C(p)$ has measure zero in $N$.
*Book:* p. 99, Corollary 18.2: for $p \in M$ and almost all $q \in M$, $p$ is not conjugate to $q$
along any geodesic. *Hidden hypotheses:* "measure zero" in a manifold is not defined in the book
(Theorem 6.1, p. 33, uses the phrase for a manifold target); here it is read in charts. *Deviation
(restated):* "almost all $q$" is "outside a set of measure zero in every slice chart, for every Haar
measure on the model space". *Proof:* with $e : Z \to T_pN$ a linear isomorphism, the map
$z \mapsto \sigma(\exp_p(e(z)))_1$ is $C^\infty$ on an open subset of $Z$, and the chart image of
every point of $C(p) \cap \operatorname{dom}\sigma$ is a critical value of this map: a derivative
that is not one-to-one stays so after composing, and a linear map of $Z$ to itself is onto iff it is
one-to-one. Sard's theorem for smooth maps (the companion project's `Milnor.sard`) applies.

**V11.6 (non-conjugate points are dense, and non-degenerate; `Morse.dense_compl_conjLocus`,
`Morse.hessNullity_eq_zero_of_notMem_conjLocus`).** For $p \in N$, the points of $N$ outside $C(p)$
are dense in $N$. If $q \notin C(p)$, then at every geodesic $\gamma \in \Omega(N; p, q)$ the
nullity of $E_{**}$ is $0$. *Book:* p. 98: Theorem 17.3 describes $\Omega(M; p, q)$ when $p$ and $q$
are not conjugate along any geodesic, and "this section will justify this result by showing that
such non-conjugate points always exist". *Hidden hypotheses:* from measure zero to existence: a null
set has empty interior, since a non-empty open subset of $Z$ has positive Haar measure. *Deviation
(not in the book):* density, and the non-degeneracy that Theorems 16.3 and 17.3 use. *Proof:* V11.5
in the chart at a point of a given open set; Theorem 14.1 (V9.6).

**V11.7 (Lemma 19.1; `Morse.NonposCurvature`, `Morse.nonposCurvature_iff_sectionalCurvature`,
`Morse.hasDerivAt_inner_covAlong`, `Morse.continuousOn_covAlong`,
`Morse.IsJacobiField.eqOn_zero_of_nonpos`, `Morse.lemma_19_1`).** $N$ has *non-positive curvature*
if $\langle R(A, B)A, B\rangle \le 0$ for all $A, B \in T_qN$ and all $q \in N$; equivalently, every
sectional curvature of $N$ is $\le 0$. (i) For a smooth curve $\gamma$ in $N$ on $[0, 1]$ with
velocity $V$ and a Jacobi field $J$ along it,
$$\frac{d}{dt}\Big\langle\frac{DJ}{dt}, J\Big\rangle = \Big\|\frac{DJ}{dt}\Big\|^2 - \langle R(V, J)V,
J\rangle \quad\text{on } (0, 1).$$
(ii) If $N$ has non-positive curvature and $\gamma$ is a smooth curve in $N$ on $[0, 1]$ which is a
geodesic on $(0, 1)$, a Jacobi field along $\gamma$ vanishing at two parameters $a < b$ of $[0, 1]$ vanishes on $[0, 1]$; so no two
parameters are conjugate along $\gamma$. *Book:* p. 100, Lemma 19.1: if
$\langle R(A, B)A, B\rangle \le 0$ for every pair of vectors $A, B$ in $TM_p$ and every $p \in M$,
no two points of $M$ are conjugate along any geodesic; proof: $\langle\frac{D^2J}{dt^2}, J\rangle =
-\langle R(V, J)V, J\rangle \ge 0$, so $\langle\frac{DJ}{dt}, J\rangle$ is monotonically increasing,
strictly so where $\frac{DJ}{dt} \ne 0$; if $J(0) = J(t_0) = 0$ it vanishes on $[0, t_0]$, so
$J(0) = \frac{DJ}{dt}(0) = 0$ and $J \equiv 0$. *Hidden hypotheses:* $\frac{DJ}{dt}(0) = 0$ comes
from $\frac{DJ}{dt} = 0$ on $(0, t_0)$ by continuity. *Deviation (restated):* any two parameters
$a < b$ in $[0, 1]$ (Milnor: $0$ and $t_0$); conjugate parameters for points (V9.4). *Deviation
(stronger):* (i) along any smooth curve.

**V11.8 (non-positive curvature: index $0$, $E_{**}$ positive definite, $\exp_p$ non-critical;
`Morse.formIndex_eq_zero_of_nonpos`, `Morse.energyHessian_pos_of_nonpos`,
`Morse.injective_dExpAt_of_nonpos`).** Let $N$ have non-positive curvature. At every geodesic
$\gamma \in \Omega(N; p, q)$ the index and the nullity of $E_{**}$ are $0$, and $E_{**}(W, W) > 0$
for every $W \in T\Omega_\gamma$ that does not vanish identically on $[0, 1]$. For $p \in N$,
$\exp_p$ is critical at no point of $\mathcal D_p$. *Book:* p. 102, proof of Theorem 19.2: "since
there are no conjugate points, it follows from the index theorem that every geodesic from $p$ to
$q$ has index $\lambda = 0$"; p. 103: "it follows from 18.1 that $\exp_p$ is non-critical
everywhere". *Hidden hypotheses:* none. *Deviation (stronger):* positive definiteness of $E_{**}$,
not in the book; neither completeness nor simple connectivity. *Proof:* the index theorem (V9.24)
with Lemma 19.1; $E_{**} \ge 0$ from its integral form (V8.15), and a $W$ with $E_{**}(W, W) = 0$
is a null vector of the semi-definite form, hence a Jacobi field vanishing at $0$ and $1$ (V9.5),
hence $0$; the last statement is V11.3 with Lemma 19.1.

**V11.9 (the Ricci tensor and Milnor's Assertion; `Morse.ricci`, `Morse.ricci_eq_sum`,
`Morse.ricci_comm`, `Morse.curvOp_self`, `Morse.ricci_eq_sum_erase`).** For $q \in N$ and
$U_1, U_2 \in T_qN$, $K(U_1, U_2)$ is the trace of the linear map $W \mapsto R(U_1, W)U_2$ of
$T_qN$. For an orthonormal basis $E_1, \dots, E_n$ of $T_qN$,
$K(U_1, U_2) = \sum_i\langle R(U_1, E_i)U_2, E_i\rangle$, and $K(U_1, U_2) = K(U_2, U_1)$.
**Assertion:** for an orthonormal basis $U_1, \dots, U_n$ of $T_qN$, $K(U_n, U_n) = \sum_{i \ne
n}\langle R(U_n, U_i)U_n, U_i\rangle$, the sum of the sectional curvatures of the $n - 1$ planes
spanned by $U_n$ and $U_i$. *Book:* p. 104, Definition: the Ricci tensor at $p$ is the bilinear
pairing $K : TM_p \times TM_p \to \mathbb R$, $K(U_1, U_2)$ the trace of $W \mapsto R(U_1, W)U_2$;
"it follows easily from 9.3 that $K$ is symmetric"; Assertion: $K(U_n, U_n)$ is the sum of the
sectional curvatures $\langle R(U_n, U_i)U_n, U_i\rangle$, $i = 1, \dots, n - 1$, because the $n$-th
diagonal term of the matrix $(\langle R(U_n, U_i)U_n, U_j\rangle)$ is zero. *Hidden hypotheses:*
none. *Proof:* symmetry from the pair symmetry of Lemma 9.3 (4) (V6.21) in an orthonormal basis;
the Assertion as Milnor's, with $R(U_n, U_n) = 0$.

**V11.10 (a geodesic as a smooth curve with a parallel frame; `Morse.exists_smooth_clamp`,
`Morse.exists_smooth_extension`, `Morse.exists_parallel_frame`).** Let $\gamma \in \Omega(N; p, q)$
be a geodesic and $L = L(\gamma)$. (i) There are a $C^\infty$ curve $c : \mathbb R \to N$ equal to
$\gamma$ on $[0, 1]$ and a $C^\infty$ field $V$ along $c$, tangent to $N$, equal to $\gamma'$ on
$(0, 1)$, with $\|V(t)\| = L$ for all $t$ and $L^{-1}V$ parallel along $c$ (V6.8). (ii) If $L > 0$,
there are a $C^\infty$ curve $c : \mathbb R \to N$ equal to $\gamma$ on $[0, 1]$, a $C^\infty$ field
$V$ along $c$, tangent to $N$ and equal to $\gamma'$ on $(0, 1)$, and $n - 1$ parallel fields
$P_1, \dots, P_{n-1}$ along $c$ with $\|P_i(t)\| = 1$, such that, for every $r$ for which
$K(U, U) \ge (n - 1)/r^2$ for all unit vectors $U$ (V11.12), $\sum_{i=1}^{n-1}\langle R(V, P_i)V,
P_i\rangle \ge L^2(n - 1)/r^2$ at every $t$. *Book:* p. 104,
proof of Theorem 19.4: for a geodesic $\gamma : [0, 1] \to M$ of length $L$, choose parallel vector
fields $P_1, \dots, P_n$ along $\gamma$ which are orthonormal at one point, and hence everywhere,
with $P_n$ pointing along $\gamma$, so that $V = LP_n$ and $\frac{DP_i}{dt} = 0$. *Hidden
hypotheses:* parallel fields along $\gamma : [0, 1] \to M$ (Lemma 8.2 is formalized for curves on
$\mathbb R$, V6.8, so $\gamma$ is first extended past its ends); $V = LP_n$ needs the constant speed
$L$ of a geodesic on $[0, 1]$ and that $V$ itself is parallel; the frame must be orthonormal at
every $t$, parallel translation being an isometry (V6.9), for the Assertion (V11.9) to apply.
*Proof:* $c$ is the radial geodesic of $\gamma'(0)$, defined near $[0, 1]$ (V9.9 (ii)), composed
with a smooth map $\mathbb R \to (-\eta, 1 + \eta)$ that is the identity on $[0, 1]$; the $P_i$ are
the parallel translates of an orthonormal basis of $T_{\gamma(0)}N$ containing $V(0)/L$, and the sum
is $L^2K(V/L, V/L)$ by the Assertion.

**V11.11 (the test fields $\sin(\pi t)P(t)$; `Morse.integral_sin_sq_pi_mul`,
`Morse.integral_cos_sq_pi_mul`, `Morse.energyHessian_sin_parallel`, `Morse.continuous_inner_curvR`,
`Morse.exists_energyHessian_neg`).** (i) Let $\gamma \in \Omega(N; p, q)$ agree on $[0, 1]$ with a
$C^\infty$ curve $c : \mathbb R \to N$, $P$ a parallel field along $c$ with $\|P\| = 1$, and $V$ a
field equal to $\gamma'$ on $(0, 1)$. Then $W(t) = \sin(\pi t)P(t)$ lies in $T\Omega_\gamma$ and
$$\tfrac12E_{**}(W, W) = \int_0^1\big(\pi^2\cos^2(\pi t) - \sin^2(\pi t)\langle R(V, P)V,
P\rangle\big)\,dt.$$
(ii) If $n \ge 2$, $r > 0$, $K(U, U) \ge (n - 1)/r^2$ for every unit vector $U$, and $\gamma \in
\Omega(N; p, q)$ is a geodesic with $L(\gamma) > \pi r$, then $E_{**}(X, X) < 0$ for some $X \in
T\Omega_\gamma$. *Book:* p. 105: with $W_i(t) = \sin(\pi t)P_i(t)$,
$\frac12E_{**}(W_i, W_i) = -\int_0^1\langle W_i, \frac{D^2W_i}{dt^2} + R(V, W_i)V\rangle dt =
\int_0^1(\sin\pi t)^2(\pi^2 - L^2\langle R(P_n, P_i)P_n, P_i\rangle)dt$; summing over
$i = 1, \dots, n - 1$ gives $\int_0^1(\sin\pi t)^2((n - 1)\pi^2 - L^2K(P_n, P_n))dt$, which is
negative if $K(P_n, P_n) \ge (n - 1)/r^2$ and $L > \pi r$, so $E_{**}(W_i, W_i) < 0$ for some $i$
(the $\frac12$, $\sum$ and $\int$ missing from the scan's display of the sum are dropped glyphs,
`Exposition/Findings.md`).
*Hidden hypotheses:* $n \ge 2$, so that there is a field $P_i$ perpendicular to $\gamma$.
*Deviation (restated):* the integral form $\int(\|\frac{DW}{dt}\|^2 - \langle R(V, W)V, W\rangle)$
(V8.15) gives $\pi^2\cos^2(\pi t)$ in place of $\pi^2\sin^2(\pi t)$; both integrate to $\pi^2/2$.
*Proof:* $\frac{DW}{dt} = \pi\cos(\pi t)P$; with the frame of V11.10, $\sum_i\frac12E_{**}(W_i,
W_i) \le (n - 1)(\pi^2 - L^2/r^2)/2 < 0$.

**V11.12 (Theorem 19.4, Myers; `Morse.RicciLowerBound`, `Morse.theorem_19_4`).** Let $n \ge 2$,
$r > 0$, and suppose $K(U, U) \ge (n - 1)/r^2$ for every unit vector $U \in T_qN$ and every
$q \in N$. Then every geodesic $\gamma \in \Omega(N; p, q)$ with $L(\gamma) > \pi r$ has a parameter
$t \in (0, 1)$ conjugate to $0$, and is not minimal: some path of $\Omega(N; p, q)$ is shorter
(V8.6). *Book:* p. 104, Theorem 19.4 (Myers): if $K(U, U) \ge (n - 1)/r^2$ for every unit vector $U$
at every point of $M$, $r$ a positive constant, every geodesic on $M$ of length $> \pi r$ contains
conjugate points, and hence is not minimal; p. 105: $E_{**}(W_i, W_i) < 0$ makes the index of
$\gamma$ positive, and the index theorem gives conjugate points; a variation with field $W_i$
decreases the energy. *Hidden hypotheses:* $n \ge 2$: for $n = 1$ the Ricci tensor vanishes, the
hypothesis holds for every $r$, and a segment of a line longer than $\pi r$ has no conjugate points
and is minimal. *Deviation (restated):* "contains conjugate points" is "has a parameter in
$(0, 1)$ conjugate to $0$"; minimality is among the paths of $\Omega(N; p, q)$ (V8.6). *Proof:*
$E_{**}$ is negative definite on the line through the $X$ of V11.11, so the index (V9.13) is
positive, and the index theorem (V9.24) gives the conjugate parameter; Lemma 13.6 (V8.18) excludes
minimality.

**V11.13 (Corollary 19.5; `Morse.IsMinimalGeodesic.isMinimalPath`, `Morse.corollary_19_5`).** A
minimal geodesic on $[0, 1]$ in the sense of V7.24 is a geodesic of $\Omega(N; \gamma(0),
\gamma(1))$ that is minimal in the sense of V8.6. Let $N$ be connected, $(N, \rho)$ complete (V7.22),
$r > 0$ with $(n - 1)/r^2 > 0$, and $K(U, U) \ge (n - 1)/r^2$ for every unit vector $U$. Then
$\rho(p, q) \le \pi r$ for all $p, q \in N$, and $N$ is compact. *Book:* p. 105, Corollary 19.5: if
$M$ is complete and $K(U, U) \ge (n - 1)/r^2 > 0$ for all unit vectors $U$, then $M$ is compact with
diameter $\le \pi r$; proof: a minimal geodesic from $p$ to $q$ has length $\le \pi r$, and closed
bounded sets in a complete manifold are compact. *Hidden hypotheses:* connectedness (Milnor's
standing assumption), for minimal geodesics to exist; $n \ge 2$ is forced by $(n - 1)/r^2 > 0$.
*Proof:* Hopf–Rinow (V7.29) joins $p$ and $q$ by a minimal geodesic of length $\rho(p, q)$, which is
$\le \pi r$ by V11.12; $N$ is then bounded and closed in itself, hence compact (V7.29).

**V11.14 (the unit sphere; `Morse.ricci_sph`, `Morse.ricciLowerBound_sph`, `Morse.sphere_myers`).**
On the unit sphere $S^n \subseteq \mathbb R^{n+1}$ (V6.25), $K(U, U) = (n - 1)\|U\|^2$, so the
hypothesis of Theorem 19.4 holds with $r = 1$. For $n \ge 2$, every geodesic of $\Omega(S^n; p, q)$
of length $> \pi$ has a parameter in $(0, 1)$ conjugate to $0$ and is not minimal, and
$\rho(p, q) \le \pi$ for all $p, q \in S^n$. *Book:* p. 105, Example: on a sphere of radius $r$
every sectional curvature is $1/r^2$, so $K(U, U) = (n - 1)/r^2$, and by 19.4 every geodesic of
length $> \pi r$ contains conjugate points: "a best possible result". *Hidden hypotheses:* none.
*Deviation (narrower):* only the unit sphere, and not "best possible" (that a geodesic of length
$\pi$ has no interior conjugate point). *Proof:* on $S^n$, $R(U, X)U = \|U\|^2X - \langle X,
U\rangle U$ (V6.25), whose trace is $(n - 1)\|U\|^2$; then V11.12, and V11.13 with the completeness
of the closed set $S^n$ (V7.30).

**V11.15 (fields on disjoint pieces; `Morse.integral_eq_of_eqOn_pieces`, `Morse.integral_sin_sq_shift`,
`Morse.integral_cos_sq_shift`, `Morse.sinBump`, `Morse.sinBump_mem_pathTangent`,
`Morse.energyHessian_sinBump`, `Morse.energyHessian_sinBump_disjoint`, `Morse.exists_sinBump_neg`).**
Let $\gamma$, $c$, $V$ be as in V11.11 (i), with $V$ smooth and tangent along $c$, $P$ parallel along
$c$, and $0 \le a < b \le 1$. The field $X$ equal to $\sin(\kappa(t - a))P(t)$, $\kappa =
\pi/(b - a)$, on $[a, b]$ and to $0$ elsewhere lies in $T\Omega_\gamma$; if $\|P\| = 1$,
$$\tfrac12E_{**}(X, X) = \int_a^b\big(\kappa^2\cos^2(\kappa(t - a)) - \sin^2(\kappa(t - a))\langle
R(V, P)V, P\rangle\big)\,dt.$$
Two such fields on $[a, b]$ and $[a', b']$ with $b \le a'$ satisfy $E_{**}(X, X') = 0$. If $n \ge
2$, $r > 0$, the $P_i$ are unit parallel fields as in V11.10 (ii), and $L(\gamma)(b - a) > \pi r$,
the field built on $[a, b]$ from some $P_i$ has $E_{**}(X, X) < 0$. *Book:* p. 106, proof of
Theorem 19.6: for a geodesic of length $> k\pi r$, "a similar argument" gives, for each
$i = 1, \dots, k$, a vector field $X_i$ along $\gamma$ which vanishes outside the interval
$(\frac{i-1}k, \frac ik)$ with $E_{**}(X_i, X_i) < 0$, and "clearly" $E_{**}(X_i, X_j) = 0$ for
$i \ne j$. *Hidden hypotheses:* the construction of the $X_i$ (the computation of V11.11 on a piece
of length $1/k$) and $n \ge 2$. *Deviation (not in the book):* stated for any piece $[a, b]$.
*Proof:* the integrand of the integral form (V8.15) vanishes off $[a, b]$, and for two pieces off
their common end point; on $[a, b]$ the sum over the $P_i$ is at most
$(n - 1)(b - a)(\kappa^2 - L^2/r^2)/2 < 0$.

**V11.16 (Theorem 19.6, the index estimate; `Morse.theorem_19_6_index`,
`Morse.pathLength_le_of_formIndex_lt`, `Morse.le_finsum_conjMultiplicity_of_ricci`).** Let $n \ge 2$,
$r > 0$, $K(U, U) \ge (n - 1)/r^2$ for every unit vector $U$, $\gamma \in \Omega(N; p, q)$ a geodesic
and $k \ge 0$ an integer. If $L(\gamma) > k\pi r$, the index of $E_{**}$ at $\gamma$ is at least $k$,
and the parameters $t \in (0, 1)$ conjugate to $0$, counted with multiplicity, number at least $k$.
Equivalently, a geodesic of index $< k$ has length $\le k\pi r$. *Book:* p. 106, proof of Theorem
19.6: the continuous function $K(U, U) > 0$ takes on a minimum $(n - 1)/r^2 > 0$ on the compact
space of unit vectors; then every geodesic $\gamma \in \Omega(M; p, q)$ of length $> \pi r$ has
index $\lambda \ge 1$, and one of length $> k\pi r$ has index $\lambda \ge k$, since
$X_1, \dots, X_k$ span a $k$-dimensional subspace of $T\Omega_\gamma$ on which $E_{**}$ is negative
definite. *Hidden hypotheses:* $n \ge 2$; that the $X_i$ are linearly independent (they are
non-zero with disjoint supports). *Deviation (narrower):* the bound $(n - 1)/r^2$ is a hypothesis,
not derived from the compactness of $M$ and the positivity of the Ricci tensor (that step is
V11.22 (i)); the rest of Theorem 19.6 is V11.22–V11.24. *Proof:* on the pieces $[\frac ik, \frac{i+1}k]$, V11.15 gives fields
$X_0, \dots, X_{k-1}$ with $E_{**}(X_i, X_i) < 0$ and $E_{**}(X_i, X_j) = 0$ for $i \ne j$, so
$E_{**}(\sum c_iX_i, \sum c_iX_i) = \sum c_i^2E_{**}(X_i, X_i) < 0$ unless all $c_i = 0$; the count
of conjugate parameters is the index theorem (V9.24).

**V11.17 (Theorem 19.2, Cartan–Hadamard; `Morse.isGeodesicallyComplete_of_isClosed`,
`Morse.injective_dExpAt_of_nonpos'`, `Morse.exists_eqOn_ray`, `Morse.injective_expToN_of_simplyConnected`,
`Morse.surjective_expToN`, `Morse.expDiffeomorph`, `Morse.theorem_19_2`).** Let $N$ be geodesically
complete (V7.22; for instance closed in $V$), simply connected (as a topological space) and of
non-positive curvature (V11.7). Then any two points $p, q \in N$ are joined by a geodesic
$\gamma \in \Omega(N; p, q)$, and every geodesic of $\Omega(N; p, q)$ agrees with $\gamma$ on
$[0, 1]$; and $\exp_p : T_pN \to N$ is a diffeomorphism, so $N$ is diffeomorphic to $\mathbb R^n$,
$n = \dim N$, for its manifold structure as a slice submanifold. *Book:* p. 102, Theorem 19.2
(Cartan): a simply connected complete $M$ with $\langle R(A, B)A, B\rangle \le 0$ has a unique
geodesic between any two points and is diffeomorphic to $\mathbb R^n$; proof pp. 102–103: by 17.3
$\Omega(M; p, q)$ has the homotopy type of a connected $0$-dimensional complex, a point, so the
geodesic is unique, $\exp_p$ is one-one and onto, non-critical by 18.1, hence a diffeomorphism.
*Hidden hypotheses:* that a simply connected space is connected (needed for Hopf–Rinow); in Milnor's
route, that the components of $\Omega$ are the homotopy classes of paths (Theorem 17.1). *Deviation
(restated):* the order of the argument is reversed: $\exp_p$ is a covering (V11.19), injective
because $N$ is simply connected (the image of a segment of $T_pN$ with both ends over one point is
a null-homotopic loop, whose lift is closed), onto by Hopf–Rinow; uniqueness of geodesics follows.
Both routes rest on Lemma 19.1.

**V11.18 (the path space in non-positive curvature; `Morse.omega_cells_of_nonpos`,
`Morse.geodesic_iff_mem_fiber`, `Morse.nonempty_homotopyEquiv_pathC_fiber`,
`Morse.omega_homotopyEquiv_fiber`, `Morse.contractibleSpace_pathC`, `Morse.contractibleSpace_pathSp`,
`Morse.omega_single_cell`).** Let $N$ have non-positive curvature. (i) If $N$ is closed in $V$ and
$p, q \in N$, $\Omega(N; p, q)$ has the homotopy type of a countable cell complex (VA.18) all of
whose cells are $0$-cells, one for each geodesic from $p$ to $q$. (ii) If $N$ is geodesically
complete, the fibre of $\exp_p$ over $q$ is discrete and countable, its points $v$ correspond
bijectively (on $[0, 1]$) to the geodesics $t \mapsto \exp_p(tv)$ from $p$ to $q$, and
$\Omega(N; p, q)$ is homotopy equivalent to it. (iii) If moreover $N$ is simply connected,
$\Omega(N; p, q)$ is contractible, and (for $N$ closed) it has the homotopy type of a cell complex
with exactly one cell, a $0$-cell. *Book:* p. 102, proof of 19.2: by 17.3 $\Omega(M; p, q)$ has the
homotopy type of a $0$-dimensional CW-complex with one vertex for each geodesic, connected because
$M$ is simply connected, hence a point. *Hidden hypotheses:* Theorem 17.1 for the connectedness.
*Deviation (stronger):* (ii) for every complete $N$ of curvature $\le 0$, simply connected or not,
through the covering: lifting a path from $0 \in T_pN$ and taking the end point is a homotopy
equivalence of $\Omega^*$ with the fibre, and $\Omega \simeq \Omega^*$ (V10.19). That a countable cell
complex with only $0$-cells (a telescope, VA.18) is homotopy equivalent to a discrete space is not
formalized; (ii) reaches the discrete space directly.

**V11.19 ($\exp_p$ is a covering map; `Morse.gauss_lemma_expDomAt`,
`Morse.isLocalDiffeomorphAt_expToN`, `Morse.isLocalDiffeomorph_expToN`, `Morse.norm_expLift_le`,
`Morse.exists_expLift`, `Morse.expLift_unique`, `Morse.isCoveringMap_expToN`,
`Morse.isCoveringMap_expToN_of_nonpos`).** (i) The Gauss lemma holds on the whole domain of
$\exp_p$: $\langle d(\exp_p)_w(w), d(\exp_p)_w(x)\rangle = \langle w, x\rangle$ for
$w \in \mathcal D_p$, $x \in T_pN$. (ii) $\exp_p : T_pN \to N$ is a local diffeomorphism at every
point of its domain where $d(\exp_p)$ is one-to-one. Now let $N$ be geodesically complete and
$\exp_p$ nowhere critical. (iii) A lift $\Gamma$ through $\exp_p$ of a smooth curve of speed $\le L$
on $[0, T]$ satisfies $\|\Gamma(t)\| \le \|\Gamma(0)\| + 1 + Lt$. (iv) Smooth curves in $N$ lift
through $\exp_p$, uniquely, from any point over the initial point. (v) $\exp_p : T_pN \to N$ is a
covering map. In non-positive curvature (V11.8) all of this applies. *Book:* p. 103: by 18.1
$\exp_p$ is non-critical everywhere, "so that $\exp_p$ is locally a diffeomorphism"; for $M$ not
simply connected, Theorem 19.2 is applied to the universal covering $\tilde M$, which, "it is
clear", inherits a complete metric of curvature $\le 0$. *Hidden hypotheses:* the completeness of
the pulled-back metric (Milnor's "it is clear"), here (iii). *Deviation (not in the book):* the
universal covering is $\exp_p : T_pN \to N$ itself, so no abstract covering space or lifted metric is
needed; this is the standard proof of the Cartan–Hadamard theorem. The Gauss lemma is needed beyond
a normal neighbourhood (Milnor states it only there, Lemma 10.5).

**V11.20 (each homotopy class of paths contains exactly one geodesic; `Morse.pathOfMem`,
`Morse.homotopy_class_unique_geodesic`).** Let $N$ be geodesically complete and of non-positive
curvature, and $p, q \in N$. Every continuous path $c$ in $N$ from $p$ to $q$ is homotopic, relative
to its end points, to a geodesic $\gamma \in \Omega(N; p, q)$; and two geodesics of
$\Omega(N; p, q)$ both homotopic to $c$ agree on $[0, 1]$. *Book:* p. 103: for complete $M$ of
curvature $\le 0$, not simply connected, each homotopy class of paths from $p$ to $q$ contains
precisely one geodesic (19.2 applied to $\tilde M$). *Hidden hypotheses:* as in V11.19. *Proof:*
the geodesics from $p$ are the images of the segments from $0$ in $T_pN$, their lifts through the
covering $\exp_p$; homotopic paths have lifts from $0$ with the same end point.

**V11.21 (Corollary 19.3, first half; `Morse.contractibleSpace_cube`, `Morse.isPreconnected_cube_face`,
`Morse.genLoop_homotopic_const`, `Morse.corollary_19_3`).** If $N$ is geodesically complete and of
non-positive curvature, then $\pi_i(N, x) = 0$ for every $i > 1$ and every $x \in N$ (Mathlib's
homotopy groups); on the way, every map of the cube $I^i$, $i \ge 2$, sending the boundary to $x$ is
null-homotopic relative to the boundary. *Book:* p. 103, Corollary 19.3: for complete $M$ with
$\langle R(A, B)A, B\rangle \le 0$, $\pi_i(M) = 0$ for $i > 1$, and $\pi_1(M)$ has no element of
finite order other than the identity. *Hidden hypotheses:* "clearly $\pi_i(M) = \pi_i(\tilde M)$".
*Deviation (narrower):* only the first half; the torsion-freeness of $\pi_1$ (cohomology of groups and
of finite cyclic groups) is not formalized. *Proof:* a map of the cube lifts through the covering
$\exp_x$ (the cube is simply connected and locally path connected); the lift is $0$ on the boundary
because the fibre is discrete and the boundary is connected for $i \ge 2$; the straight-line
contraction of the lift projects to the null-homotopy.

**V11.22 (Theorem 19.6 for non-conjugate end points; `Morse.ricciMap`, `Morse.continuous_trace_ricciMap`,
`Morse.exists_ricciLowerBound`, `Morse.energy_le_of_geodesicIndex_le`,
`Morse.theorem_19_6_of_ricciLowerBound`, `Morse.theorem_19_6`).** (i) If $N$ is compact,
$n = \dim N \ge 2$ and the Ricci tensor is positive definite, there is $r > 0$ with
$K(U, U) \ge (n - 1)/r^2$ for every unit tangent vector $U$. (ii) Under such a bound, a geodesic of
index $\le d$ has energy $\le ((d + 1)\pi r)^2$. (iii) If $N$ is closed in $V$ with such a bound, or
compact with positive definite Ricci tensor, and $q$ is not conjugate to $p$ along any geodesic
($q \notin C(p)$, V11.4), then $\Omega(N; p, q)$ has the homotopy type of a countable cell complex
(VA.18) with only finitely many cells of each dimension. *Book:* p. 106, Theorem 19.6: for $M$
compact with positive definite Ricci tensor, $\Omega(M; p, q)$ has the homotopy type of a
CW-complex with only finitely many cells in each dimension; the proof treats $p, q$ not conjugate
along any geodesic, by 16.3 (finitely many geodesics of bounded length) and 17.3. *Hidden
hypotheses:* $n \ge 2$; the continuity of $K(U, U)$ on the unit tangent bundle. *Deviation
(restated):* "CW-complex" is a countable cell complex with arbitrary attaching maps (a telescope,
VA.18); the general $p, q$ are V11.24. *Proof:* the minimum of the continuous $K(U, U)$ on the
compact unit tangent bundle; V11.16 bounds the length of a geodesic of index $< k$; Theorem 16.3
(V10.13) gives finitely many geodesics below each energy, and Theorem 17.3 (V10.22) the complex.

**V11.23 (the homology of the path space in positive Ricci curvature; `Morse.slabEnergies`,
`Morse.slab_homology`, `Morse.finiteDimensional_spaceHomology_omega`,
`Morse.finiteDimensional_spaceHomology_omega_of_compact`).** Let $N$ be closed in $V$ and every
geodesic of $\Omega(N; p, q)$ of nullity $0$. For levels $a \le b$ that are not energies of
geodesics, $H_j(\Omega^b, \Omega^a; \Bbbk)$ is finite-dimensional, and zero if no geodesic with
energy in $(a, b)$ has index $j$. Hence, under a Ricci bound $K(U, U) \ge (n - 1)/r^2$, $n \ge 2$,
and for $q \notin C(p)$ — in particular under the hypotheses of V11.22 (iii) — $H_i(\Omega(N; p, q);
\Bbbk)$ is finite-dimensional for every $i$ and every field $\Bbbk$. *Book:* not stated; p. 106 with
the method of p. 96 (homology read off the cells). *Deviation (not in the book):* the homology is
computed from the energy filtration, since the cell complexes of VA.18 have no cellular homology:
above the energy $((i + 2)\pi r)^2$ every geodesic has index $\ge i + 2$.

**V11.24 (Theorem 19.6 for all end points; `Morse.exists_joined_notMem_conjLocus`,
`Morse.pathSpHomotopyEquiv`, `Morse.IsCountableCellComplexType.of_homotopyEquiv`,
`Morse.theorem_19_6_all`, `Morse.finiteDimensional_spaceHomology_omega_all`).** Let $N$ be compact,
$n = \dim N \ge 2$, with positive definite Ricci tensor. Then for all $p, q \in N$,
$\Omega(N; p, q)$ has the homotopy type of a countable cell complex (VA.18) with only finitely many
cells of each dimension, and $H_i(\Omega(N; p, q); \Bbbk)$ is finite-dimensional for every $i$ and
every field $\Bbbk$. On the way: $q$ is joined by a path in $N$ to a point $q'$ not conjugate to $p$
along any geodesic, and then $\Omega(N; p, q) \simeq \Omega(N; p, q')$. *Book:* p. 106, Theorem
19.6, stated for all $p, q$. *Hidden hypotheses:* Milnor's proof treats only non-conjugate end
points; the general case needs a nearby non-conjugate $q'$ (Corollary 18.2, V11.5–V11.6) and the
change of end point (the exposition's Lemma 17.D, through Theorem 17.1, V10.19). *Deviation
(restated):* as in V11.22; no connectedness of $N$ is needed, $q'$ being chosen in a small
Riemannian ball about $q$.

### What is not verified in this chapter

- **Corollary 19.3, second half** (p. 103): $\pi_1(M)$ has no non-trivial element of finite order.
  It needs the cohomology of groups ($H^k(M) \cong H^k(\pi_1M)$ for $M$ with contractible universal
  covering) and the cohomology of finite cyclic groups. The first half is V11.21.
- **That a complex with only $0$-cells is a discrete space up to homotopy** (p. 102): V11.18 (ii)
  reaches the discrete fibre of $\exp_p$ directly instead.
- **The finiteness of $\pi_1(M)$** (p. 105, after Corollary 19.5): the universal covering of a
  complete $M$ with $K(U, U) \ge (n - 1)/r^2 > 0$, with the lifted metric, is not formalized (in
  curvature $\le 0$ the covering $\exp_p$ of V11.19 plays its role).
- **The sectional curvature as a Gaussian curvature** (p. 100, the Remark after Lemma 19.1, citing
  Laugwitz): the Gaussian curvature of the surface $(u_1, u_2) \mapsto \exp_p(u_1A + u_2B)$ is not
  defined.
- **The optics paragraph and the examples** (pp. 101–102: apparent sizes and volumes, complete
  surfaces of curvature $\le 0$ in $\mathbb R^3$, the pseudo-sphere and Hilbert's theorem, compact
  surfaces of constant negative curvature), the sphere of radius $r \ne 1$ and "best possible"
  (p. 105), and the remarks of pp. 106–107 (complete non-compact $M$, $S^m \times S^k$, Synge's
  theorem): not formalized.
- **The exposition's application** (§6, shortest routes on the Earth) and its figure: not
  formalized.
- **§§18–19 on an abstract Riemannian manifold**: only for submanifolds of a Euclidean space with
  the induced metric; Nash's embedding theorem is quoted, not proved.

---

## 13. Chapter 12 (Milnor §§20–21): partly verified

Milnor's §20 (pp. 109–111) defines symmetric spaces, shows that they are complete and that their
curvature tensor is parallel (Lemma 20.1, Corollaries 20.2–20.4), and computes the conjugate points
along a geodesic of a locally symmetric space from the eigenvalues of $K_V(W) = R(V, W)V$ (Theorem
20.5). §21 (pp. 112–117) shows that a Lie group with a left- and right-invariant metric is a
symmetric space (Lemmas 21.1, 21.2), computes its curvature on left-invariant fields (Theorem 21.3,
Corollary 21.4), draws topological consequences (Corollaries 21.5, 21.6), and proves Bott's theorem
that the loop space of a compact simply connected Lie group has a CW structure with only
even-dimensional cells (Theorem 21.7). Everything in §21 that is a computation in the Lie algebra is
verified, for an abstract real Lie algebra $L$ (Milnor's $\mathfrak g$ of left-invariant fields)
with a bilinear form $B$ (Milnor's inner product on $\mathfrak g$), every hypothesis on $B$ —
symmetric, positive definite, ad-invariant — being an explicit hypothesis of the theorem that uses
it: Milnor's formula (d) and Theorem 21.3 (a)–(c) from the two geometric inputs of his proof, taken
as hypotheses; Corollary 21.4; the algebraic steps of Corollaries 21.5 and 21.6; and the pairing of
the eigenvalues of $K_V$ that drives the proof of Theorem 21.7. For a compact group of matrices —
a slice submanifold of the space of matrices, closed under products and adjoints, with a Lie algebra
of skew-Hermitian matrices (V12.14) — the geometry of §21 is verified as well, in the embedding
instead of through left-invariant fields: the one-parameter subgroups and their translates are the
geodesics and the group is complete (Lemma 21.2, V12.15), the reflection
$\sigma \mapsto \tau\sigma^{-1}\tau$ of Lemma 21.1 (V12.16), Theorem 21.3 (a)–(d) and Corollary 21.4
by the Gauss equation, which identifies the curvature with the algebraic one of V12.5 (V12.17), and
the Jacobi equation of Theorem 20.5 along a one-parameter subgroup (V12.18). Not verified: §20 for
general (locally) symmetric spaces, Lie groups not given as matrices, Myers's theorem in 21.5, the
splitting of the group in 21.6, and Theorem 21.7 itself. Lean: `Morse/Chapter12/BiInvariant.lean`
(557 lines), `MatrixInner.lean` (359), `MatrixGroups.lean` (793), `GroupGeodesics.lean` (593),
`GroupJacobi.lean` (276); `SUMinimal.lean`, `SUJacobi.lean` and `SUIndex.lean` serve §23 and are
reported in Chapter 14; one counting step of Theorem 21.7 (V12.13) sits in
`Morse/Chapter14/IndexCount.lean`.

**V12.1 (the algebraic model of a bi-invariant metric; `Morse.IsAdInvariant`,
`Morse.isAdInvariant_iff_lieInvariant`, `Morse.IsLeviCivita`).** $L$ is a real Lie algebra and
$B : L \times L \to \mathbb R$ a bilinear form. $B$ is *ad-invariant* if
$B([X, Y], Z) = B(X, [Y, Z])$ for all $X, Y, Z$; this is Mathlib's `lieInvariant`. A connection on
left-invariant fields is a bilinear map $D : L \times L \to L$, $D(X, Y)$ standing for $X \vdash Y$;
it is *Levi-Civita for $B$* (`Morse.IsLeviCivita`) if $D(X, Y) - D(Y, X) = [X, Y]$ (Milnor's 8.5)
and $B(D(X, Y), Z) + B(Y, D(X, Z)) = 0$ (Corollary 8.4 for fields whose inner products are
constant), for all $X, Y, Z$. *Book:* p. 113: the Lie algebra $\mathfrak g$ of left-invariant vector
fields with the bracket, on a Lie group with a left and right invariant metric; 21.3 (a) is the
identity $\langle[X, Y], Z\rangle = \langle X, [Y, Z]\rangle$. *Hidden hypotheses:* that
$X \vdash Y$ is left-invariant when $X$ and $Y$ are, so that the connection restricts to a map
$\mathfrak g \times \mathfrak g \to \mathfrak g$, which Milnor's computation of $R$ with (d) needs.
*Deviation (restated):* the Lie group, its left-invariant fields and its metric are replaced by an
abstract Lie algebra with a bilinear form; the geometric facts are hypotheses (V12.2, V12.3).

**V12.2 (Milnor's formula (d); `Morse.IsLeviCivita.conn_eq`).** Let $D$ be Levi-Civita for a
bilinear form $B$ (no condition on $B$), and suppose $D(X, X) = 0$ for every $X$. Then
$D(X, Y) = \tfrac12[X, Y]$ for all $X, Y$. *Book:* pp. 113–114: $X \vdash X = 0$ because the
integral curves of a left-invariant $X$ are left translates of one-parameter subgroups, hence
geodesics; expanding $(X + Y) \vdash (X + Y) = 0$ and adding $X \vdash Y - Y \vdash X = [X, Y]$
gives (d), $2X \vdash Y = [X, Y]$. *Hidden hypotheses:* $X \vdash X = 0$ rests on Lemma 21.2 and on
left translations being isometries. *Deviation (restated):* $X \vdash X = 0$ is a hypothesis.
*Proof:* as in the book; only the symmetry of $D$ is used.

**V12.3 (Theorem 21.3 (a); `Morse.IsLeviCivita.isAdInvariant`).** If $D$ is Levi-Civita for $B$ and
$D(X, X) = 0$ for every $X$, then $B$ is ad-invariant. *Book:* p. 113, Theorem 21.3 (a); proof on p.
114: $Y\langle X, Z\rangle = \langle Y \vdash X, Z\rangle + \langle X, Y \vdash Z\rangle$ (8.4), the
left side vanishes because $\langle X, Z\rangle$ is constant, and (d) is substituted. *Hidden
hypotheses:* the constancy of $\langle X, Z\rangle$ for left-invariant $X, Z$ (left invariance of
the metric), here built into the compatibility condition of V12.1. *Deviation (restated):* as in
V12.2. *Proof:* as in the book.

**V12.4 (the converse route: the Koszul formula; `Morse.IsLeviCivita.koszul`,
`Morse.IsLeviCivita.conn_eq_of_isAdInvariant`, `Morse.halfLie`, `Morse.halfLie_apply`,
`Morse.isLeviCivita_halfLie`).** If $B$ is symmetric and $D$ is Levi-Civita for $B$, then
$2B(D(X, Y), Z) = B([X, Y], Z) - B([Y, Z], X) + B([Z, X], Y)$. If moreover $B$ is ad-invariant and
non-degenerate, then $D(X, Y) = \tfrac12[X, Y]$. Conversely, for every ad-invariant $B$ the map
$D(X, Y) = \tfrac12[X, Y]$ is Levi-Civita for $B$. *Book:* not in Milnor's text. *Deviation (not in
the book):* this derives (d) from the ad-invariance of the metric instead of from $X \vdash X = 0$:
on left-invariant fields the Levi-Civita connection of a bi-invariant metric is forced to be
$\tfrac12[\,\cdot\,, \cdot\,]$, which is the uniqueness of Lemma 8.6 in this algebraic model.

**V12.5 (Theorem 21.3 (b); `Morse.curv`, `Morse.curv_halfLie`).** For a bilinear
$D : L \times L \to L$ put $R(X, Y)Z = -D(X, D(Y, Z)) + D(Y, D(X, Z)) + D([X, Y], Z)$, Milnor's
sign. In any real Lie algebra, with $D = \tfrac12[\,\cdot\,, \cdot\,]$,
$R(X, Y)Z = \tfrac14[[X, Y], Z]$. *Book:* p. 113, Theorem 21.3 (b); proof on p. 114, by substituting
(d) into the definition of $R$ and using the Jacobi identity. *Hidden hypotheses:* the left
invariance of $Y \vdash Z$ (V12.1). *Proof:* as in the book.

**V12.6 (Theorem 21.3 (c); `Morse.curv_inner`).** If $B$ is ad-invariant, then
$B(R(X, Y)Z, W) = \tfrac14B([X, Y], [Z, W])$ for $D = \tfrac12[\,\cdot\,, \cdot\,]$. *Book:* p. 113,
Theorem 21.3 (c), which "follows from (a) and (b)" (p. 114). *Hidden hypotheses:* none. *Proof:* as
in the book.

**V12.7 (Cartan's 3-form; `Morse.cartan_form_swap₁₂`, `Morse.cartan_form_swap₂₃`).** For every
bilinear $B$, $B([Y, X], Z) = -B([X, Y], Z)$; if $B$ is ad-invariant,
$B([X, Z], Y) = -B([X, Y], Z)$. So $(X, Y, Z) \mapsto B([X, Y], Z)$ is alternating. *Book:* footnote
on p. 114: this trilinear function is skew-symmetric in all three variables, giving a left-invariant
3-form, from which Cartan proved $H^3(G) \neq 0$ for a non-abelian compact connected Lie group.
*Hidden hypotheses:* none. *Deviation (narrower):* only the skew-symmetry; the differential form,
its de Rham class and Cartan's theorem are not formalized.

**V12.8 (Corollary 21.4; `Morse.sectional`, `Morse.sectional_nonneg`, `Morse.sectional_eq_zero_iff`,
`Morse.sectional_std`).** If $B$ is ad-invariant, then for $D = \tfrac12[\,\cdot\,, \cdot\,]$ and
all $X, Y$, $B(R(X, Y)X, Y) = \tfrac14B([X, Y], [X, Y])$; if $B$ is also positive definite, this is
$\ge 0$, with equality iff $[X, Y] = 0$. With the standard sign,
$B(-R(X, Y)Y, X) = \tfrac14B([X, Y], [X, Y])$. *Book:* p. 115, Corollary 21.4: the sectional
curvature $\langle R(X, Y)X, Y\rangle = \tfrac14\langle[X, Y], [X, Y]\rangle$ is always $\ge 0$,
with equality iff $[X, Y] = 0$. *Hidden hypotheses:* none (positive definiteness of $B$, needed for
the inequality, is part of "Riemannian metric"). *Deviation (stronger):* for all $X, Y$, not only
orthonormal pairs.

**V12.9 (Corollary 21.5, the algebraic step: Ricci curvature; `Morse.jacobiOp`,
`Morse.curv_halfLie_eq_jacobiOp`, `Morse.trace_jacobiOp`, `Morse.trace_eq_sum_of_isOrtho`,
`Morse.trace_jacobiOp_pos`, `Morse.killingForm_neg`).** Let $K_V = -\tfrac14\operatorname{ad}_V^2$;
then $K_V(W) = R(V, W)V$ for $D = \tfrac12[\,\cdot\,, \cdot\,]$, and in every real Lie algebra
$\operatorname{tr}K_V = -\tfrac14\kappa(V, V)$, $\kappa$ Mathlib's Killing form. If $L$ is
finite-dimensional, $B$ symmetric, positive definite and ad-invariant, and the centre of $L$ is
zero, then $\operatorname{tr}K_V > 0$ for every $V \neq 0$; equivalently $\kappa(V, V) < 0$. *Book:*
p. 115, Corollary 21.5 (trivial centre implies $G$ compact with finite fundamental group); in the
proof, the Ricci curvature $K(X_1, X_1) = \sum_i\langle R(X_1, X_i)X_1, X_i\rangle$, over an
orthonormal basis, is strictly positive since $[X_1, X_i] \neq 0$ for some $i$, and bounded away
from zero; Myers's theorem (Corollary 19.5) concludes. *Hidden hypotheses:* the termwise inequality
$\langle R(X_1, X_i)X_1, X_i\rangle \ge 0$ (V12.8), used without comment. *Deviation (narrower):*
only the positivity of the Ricci curvature; the uniform bound and Myers's theorem are not
formalized. *Deviation (not in the book):* the identification with the Killing form. *Proof:* the
trace is computed in a $B$-orthogonal basis, where its diagonal terms are
$B(K_Vb_i, b_i)/B(b_i, b_i) \ge 0$, one of them positive.

**V12.10 (Corollary 21.6, the algebraic step; `Morse.centerCompl`, `Morse.mem_centerCompl`,
`Morse.isCompl_center_centerCompl`, `Morse.eq_zero_of_mem_centerCompl`).** For ad-invariant $B$, the
set $\mathfrak g' = \{X : B(C, X) = 0 \text{ for every } C \text{ in the centre } \mathfrak c\}$ is
a Lie ideal of $L$. If $L$ is finite-dimensional and $B$ symmetric, positive definite and
ad-invariant, then $L = \mathfrak c \oplus \mathfrak g'$ as vector spaces, and $\mathfrak g'$ has
trivial centre: an element of $\mathfrak g'$ commuting with all of $\mathfrak g'$ is zero. *Book:*
pp. 115–116, Corollary 21.6: a simply connected Lie group with a bi-invariant metric splits as
$G' \times \mathbb R^k$ with $G'$ compact and the Lie algebra of $G'$ with trivial centre; in the
proof, the orthogonal complement $\mathfrak g'$ of $\mathfrak c$ is a subalgebra, since
$\langle[X, Y], C\rangle = \langle X, [Y, C]\rangle = 0$, and
$\mathfrak g = \mathfrak g' \oplus \mathfrak c$. *Hidden hypotheses:* none at this level. *Deviation
(stronger):* $\mathfrak g'$ is an ideal (for a complement of the centre this is the same as a
subalgebra, and it is what the splitting as Lie algebras uses). *Deviation (narrower):* the
splitting of the group and the compactness of $G'$ are not formalized.

**V12.11 (the operator $K_V$ in the proof of 21.7; `Morse.jacobiOp_apply`, `Morse.ad_skew`,
`Morse.jacobiOp_symm`, `Morse.jacobiOp_self`, `Morse.jacobiOp_self_nonneg`,
`Morse.jacobiOp_eq_zero_iff`, `Morse.eigenvalue_nonneg`, `Morse.ad_eigenvalue_eq_zero`).** Let $B$
be ad-invariant. Then $\operatorname{ad}_V$ is skew, $B([V, X], Y) = -B(X, [V, Y])$;
$K_V(W) = -\tfrac14[V, [V, W]]$ is self-adjoint for $B$, and
$B(K_VW, W) = \tfrac14B([V, W], [V, W])$. If $B$ is also positive definite: $K_V$ is positive
semidefinite, $K_VW = 0$ iff $[V, W] = 0$, every eigenvalue of $K_V$ is $\ge 0$, and the only real
eigenvalue of $\operatorname{ad}_V$ is $0$. *Book:* pp. 116–117:
$K_V(W) = R(V, W)V = \tfrac14[[V, W], V]$,
$K_V = -\tfrac14(\operatorname{Ad}V)\circ(\operatorname{Ad}V)$, and $\operatorname{Ad}V$ is
skew-symmetric by 21.3 (a). *Hidden hypotheses:* none (positive definiteness is part of "Riemannian
metric"). *Deviation (stronger):* the kernel of $K_V$ and the real spectrum of $\operatorname{ad}_V$
are stated.

**V12.12 (the non-zero eigenvalues of $K_V$ occur in pairs; `Morse.jacobiOp_of_lie_lie`,
`Morse.lie_lie_of_jacobiOp`, `Morse.lie_mem_eigenspace`, `Morse.eigenJ`, `Morse.eigenJ_comp_self`,
`Morse.eigenJ_isometry`, `Morse.even_finrank_of_comp_self_eq_neg_id`,
`Morse.even_finrank_eigenspace`).** $K_VW = \mu W$ iff $[V, [V, W]] = -4\mu W$, and
$\operatorname{ad}_V$ maps each eigenspace $E_\mu$ of $K_V$ into itself. For $\mu > 0$ the map
$J = (2\sqrt\mu)^{-1} \operatorname{ad}_V$ on $E_\mu$ satisfies $J^2 = -1$, and it preserves $B$
when $B$ is ad-invariant. A finite-dimensional real vector space with such a $J$ has even dimension.
Hence, for $L$ finite-dimensional and $B$ ad-invariant and positive definite, every eigenspace
$E_\mu$ of $K_V$ with $\mu \neq 0$ has even dimension. *Book:* p. 117: an orthonormal basis puts
$\operatorname{Ad}V$ in block form with blocks $\begin{pmatrix}0 & a_i\\ -a_i & 0\end{pmatrix}$, so
$(\operatorname{Ad}V)^2$ is diagonal with entries $-a_1^2, -a_1^2, -a_2^2, \dots$, and the non-zero
eigenvalues of $K_V$ are positive and occur in pairs. *Hidden hypotheses:* the normal form of a
skew-symmetric map is quoted without proof. *Deviation (restated):* the normal form is replaced by
the complex structure $J$ on each eigenspace, which is what "occur in pairs" needs.

**V12.13 (even index from paired eigenvalues; `Morse.even_spectralIndex`, `Morse.spectralIndex`,
`Morse.conjParams`).** Let $e_1, \dots, e_N$ be real numbers (a spectrum of $K_V$ with multiplicity)
and define the index of the spectrum as the sum over $t \in (0, 1)$ of the number of $i$ with
$e_i > 0$ and $t \in \pi\mathbb Z/\sqrt{e_i}$ — Theorems 20.5 and 15.1 written as a definition,
stated in full in Chapter 14 (V14.7, V14.8). If every positive value occurs among the $e_i$ an even
number of times, this index is even. *Book:* p. 117: by 20.5 the conjugate points occur in pairs,
every conjugate point has even multiplicity, and with the Index Theorem the index of every geodesic
from $p$ to $q$ is even. *Hidden hypotheses:* none. *Deviation (restated):* the index is the number
defined from the spectrum; Theorems 20.5 and 15.1 are not proved for a general bi-invariant metric
(for $SU(n)$ the index of a geodesic from $I$ to $-I$ is computed from them, V14.18–V14.19). The bridge from V12.12 (even
dimension of each eigenspace) to the hypothesis here (even multiplicity in a list of eigenvalues) is
the spectral theorem for the self-adjoint $K_V$, which is not formalized in this form, so the two
items are not joined into one theorem.

**Matrix groups.** From here on $\mathbb K = \mathbb R$ or $\mathbb C$, and $M_n(\mathbb K)$, the
$n \times n$ matrices indexed by a finite set, carries the real inner product
$\langle A, B\rangle = \operatorname{Re}\operatorname{tr}(A^*B)$ (Milnor's
$\operatorname{Re}\operatorname{tr}(AB^*)$ up to the order of the factors) and the Frobenius norm;
$\exp$ is the matrix exponential, and $[X, Y] = XY - YX$. The groups are slice submanifolds of
$M_n(\mathbb K)$ (V1.6) with the induced metric, so that geodesics (V7.1), the connection (V6.4),
the curvature (V6.17) and Jacobi fields (V9.2) are those of Chapters 6–9.

**V12.14 (matrix groups and their bi-invariant metric; `Morse.MatrixInner.innerProductSpace`,
`Morse.inner_def`, `Morse.inner_mul_left_of_unitary`, `Morse.inner_mul_right_of_unitary`,
`Morse.inner_eq_zero_of_hermitian_of_skew`, `Morse.contDiff_exp_matrix`,
`Morse.exp_conjTranspose_mul_exp_of_skew`, `Morse.skewHermitian`, `Morse.IsMatrixGroup`,
`Morse.IsMatrixGroup.tangentSubspace_eq`, `Morse.IsMatrixGroup.mem_tangentSubspace_iff`,
`Morse.IsMatrixGroup.mulLeftIso_image`, `Morse.IsMatrixGroup.mulRightIso_image`,
`Morse.frobForm`, `Morse.isAdInvariant_frobForm`, `Morse.frobForm_pos`).** Multiplication on either
side by a unitary matrix is a linear isometry of $M_n(\mathbb K)$; Hermitian and skew-Hermitian
matrices are orthogonal; $\exp$ is smooth and maps skew-Hermitian matrices to unitary ones. A
*matrix group* is a pair $(G, \mathfrak g)$ of a slice submanifold $G \subseteq M_n(\mathbb K)$ and
a real Lie subalgebra $\mathfrak g$ of $M_n(\mathbb K)$ such that every $g \in G$ is unitary, $G$ is
closed under products and $g \mapsto g^*$, every $X \in \mathfrak g$ is skew-Hermitian,
$g\mathfrak gg^* \subseteq \mathfrak g$ and $\exp\mathfrak g \subseteq G$, and
$\dim G = \dim\mathfrak g$. Then $T_gG = g\mathfrak g$ for every $g \in G$; left and right
translations by elements of $G$ are linear isometries of $M_n(\mathbb K)$ carrying $G$ onto $G$, so
the induced metric is bi-invariant; and the inner product restricted to $\mathfrak g$ is
ad-invariant and positive definite, so V12.1–V12.13 apply to it. *Book:* p. 112: a Lie group with
a metric invariant under left and right translations; for compact $G$ such a metric exists by
averaging with the Haar measure; p. 125 (in §23): the tangent space of $U(n)$ at $I$ is the space of
skew-Hermitian matrices. *Hidden hypotheses:* none at this level. *Deviation (narrower):* only groups
given as matrices, with the induced metric; Milnor's abstract Lie groups, left-invariant fields and
Haar averaging are not formalized. (Every compact Lie group is a matrix group by Peter–Weyl, which is
not needed for §§23–24.) *Proof:* $g\mathfrak g \subseteq T_gG$ through the curves
$t \mapsto g\exp(tX)$, and the dimensions agree.

**V12.15 (Lemma 21.2 for matrix groups, and completeness;
`Morse.IsMatrixGroup.isGeodesicOn_mul_exp_smul`, `Morse.IsMatrixGroup.isGeodesicOn_exp_smul`,
`Morse.IsMatrixGroup.eqOn_mul_exp_smul`, `Morse.IsMatrixGroup.lemma_21_2`,
`Morse.IsMatrixGroup.eq_exp_of_oneParam`, `Morse.IsMatrixGroup.isGeodesicOn_of_oneParam`,
`Morse.IsMatrixGroup.exp_eq`, `Morse.IsMatrixGroup.isGeodesicallyComplete`).** Let $(G, \mathfrak g)$
be a matrix group. For $g \in G$ and $X \in \mathfrak g$, $t \mapsto g\exp(tX)$ is a geodesic of $G$
on $\mathbb R$. Conversely a geodesic $\gamma$ of $G$ on a preconnected open set $s \ni t_0$ is
$\gamma(t) = \gamma(t_0)\exp((t - t_0)X)$ on $s$ with $X = \gamma(t_0)^*\gamma'(t_0) \in \mathfrak g$.
(i) A geodesic $\gamma : \mathbb R \to G$ with $\gamma(0) = I$ satisfies $\gamma'(0) \in \mathfrak g$,
$\gamma(t) = \exp(t\gamma'(0))$ and $\gamma(s + t) = \gamma(s)\gamma(t)$. (ii) A differentiable
$\theta : \mathbb R \to G$ with $\theta(0) = I$ and $\theta(s + t) = \theta(s)\theta(t)$ is a
geodesic. The Riemannian exponential at $g$ is $\exp_g(gX) = g\exp X$, and $G$ is geodesically
complete (V7.22). *Book:* p. 113, Lemma 21.2: the geodesics $\gamma$ with $\gamma(0) = e$ are
precisely the one-parameter subgroups; p. 110, Corollary 20.2 (a symmetric space is complete).
*Hidden hypotheses:* in Milnor's proof of (i), the passage from commensurable parameters to all of
$\mathbb R$ "by continuity" needs the continuity of multiplication. *Deviation (restated):* for
matrix groups; the proof does not go through Lemma 20.1. *Proof:* the acceleration
$g\exp(tX)X^2$ is normal, $X^2$ being Hermitian; uniqueness of geodesics (V7.5) gives the converse;
(ii) $\exp(-tX)\theta(t)$ has derivative $0$.

**V12.16 (Lemma 21.1 for matrix groups; `Morse.IsMatrixGroup.symmIso`,
`Morse.IsMatrixGroup.symmIso_mem`, `Morse.IsMatrixGroup.symmIso_self`,
`Morse.IsMatrixGroup.symmIso_mul_exp_smul`).** For a unitary $\tau$, $I_\tau(A) = \tau A^*\tau$ is
an involutive linear isometry of $M_n(\mathbb K)$; on $G$ it is $\sigma \mapsto \tau\sigma^{-1}\tau$.
For $\tau \in G$ it maps $G$ into $G$, fixes $\tau$, and reverses the geodesics through $\tau$:
$I_\tau(\tau\exp(tX)) = \tau\exp(-tX)$ for $X \in \mathfrak g$. *Book:* p. 112, Lemma 21.1: with a
bi-invariant metric, $I_\tau(\sigma) = \tau\sigma^{-1}\tau$ is an isometry fixing $\tau$ that reverses
geodesics through $\tau$, so $G$ is a symmetric space. *Hidden hypotheses:* "symmetric space"
includes connectedness, so the last clause needs $G$ connected. *Deviation (narrower):* the
definition of a symmetric space is not formalized, so "$G$ is a symmetric space" is not a statement;
by V12.15 every geodesic through $\tau$ is a $\tau\exp(tX)$, so all of them are reversed.

**V12.17 (Theorem 21.3 and Corollary 21.4 for matrix groups; `Morse.trace_gauss_identity`,
`Morse.inner_gauss_identity`, `Morse.inner_lie_left`, `Morse.algProj`, `Morse.algProj_mul`,
`Morse.IsMatrixGroup.tanProj_eq`, `Morse.IsMatrixGroup.secondFundForm_mul`,
`Morse.IsMatrixGroup.covAt_mul_right`, `Morse.IsMatrixGroup.curvOp_mul`,
`Morse.IsMatrixGroup.inner_curvOp_mul`, `Morse.IsMatrixGroup.sectional_mul`,
`Morse.IsMatrixGroup.sectional_mul_nonneg`, `Morse.IsMatrixGroup.curvOp_eq_curv_halfLie`,
`Morse.IsMatrixGroup.coe_curvTensor_eq_curv_halfLie`, `Morse.IsMatrixGroup.curvOp_eq_jacobiOp`).**
Let $(G, \mathfrak g)$ be a matrix group, $g \in G$, $X, Y, Z, W \in \mathfrak g$. (a)
$\langle[X, Y], Z\rangle = \langle X, [Y, Z]\rangle$. (d) The covariant derivative of the
left-invariant field $q \mapsto qY$ in the direction $gX$ is $g\cdot\tfrac12[X, Y]$. The orthogonal
projection onto $T_gG$ is $M \mapsto gP_{\mathfrak g}(g^*M)$, and the second fundamental form is
$\mathrm{II}_g(gX, gY) = \tfrac12g(XY + YX)$. (b) $R(gX, gY)gZ = \tfrac14g[[X, Y], Z]$, Milnor's sign;
this is $g$ times the algebraic curvature of V12.5 for $D = \tfrac12[\,\cdot\,, \cdot\,]$, also for the
trilinear tensor of Lemma 9.1, and $R(gA, gW)gA = g\,K_A(W)$ with $K_A$ of V12.9. (c)
$\langle R(gX, gY)gZ, gW\rangle = \tfrac14\langle[X, Y], [Z, W]\rangle$. Corollary 21.4:
$\langle R(gX, gY)gX, gY\rangle = \tfrac14\|[X, Y]\|^2 \ge 0$, with equality iff $XY = YX$.
*Book:* p. 113, Theorem 21.3 (a)–(c), with (d) inside the proof on p. 114; p. 115, Corollary 21.4.
*Hidden hypotheses:* the left invariance of $X \vdash Y$ and $X \vdash X = 0$ (V12.1–V12.3), here
theorems. *Deviation (restated):* for matrix groups, by the Gauss equation (V6.18) instead of
substituting (d) into the definition of $R$: the second fundamental form gives
$\tfrac14(\langle XZ + ZX, YW + WY\rangle - \langle XW + WX, YZ + ZY\rangle)$, which a trace identity
turns into $\tfrac14\langle[[X, Y], Z], W\rangle$. This removes, for matrix groups, the hypotheses
of V12.1–V12.3.

**V12.18 (Theorem 20.5 for matrix groups: the Jacobi equation along a one-parameter subgroup;
`Morse.halfExp`, `Morse.jacK`, `Morse.IsMatrixGroup.covD_conj`, `Morse.IsMatrixGroup.curvR_conj`,
`Morse.IsMatrixGroup.isJacobiField_conj`, `Morse.IsMatrixGroup.covAlong_conj_zero`).** Let
$(G, \mathfrak g)$ be a matrix group, $A \in \mathfrak g$, $\gamma(t) = \exp(tA)$ and
$h(t) = \exp(tA/2)$. For a differentiable $\mathfrak g$-valued $U$, the covariant derivative of
$t \mapsto h(t)U(t)h(t)$ along $\gamma$ is $hU'h$, and $R(\gamma', hMh)\gamma' = h\,K_A(M)\,h$ for
$M \in \mathfrak g$, $K_A(M) = \tfrac14[[A, M], A]$. Hence, if $U$ is a smooth $\mathfrak g$-valued
curve with $U'' + K_A(U) = 0$, then $J = hUh$ is a Jacobi field along $\gamma$, with
$\frac{DJ}{dt}(0) = U'(0)$. *Book:* p. 110, Theorem 20.5: in a locally symmetric space the conjugate
points along $\gamma$ are the $\gamma(\pi k/\sqrt{e_i})$, $e_i > 0$ an eigenvalue of
$K_V(W) = R(V, W)V$, with multiplicity the number of $e_i$ for which $t$ is a multiple of
$\pi/\sqrt{e_i}$; proof p. 111: in a parallel eigenframe the Jacobi equation becomes
$w_i'' + e_iw_i = 0$. *Hidden hypotheses:* that $K_V$ is self-adjoint, so that an orthonormal
eigenbasis exists (Lemma 9.3). *Deviation (narrower):* only along one-parameter subgroups of matrix
groups, and only the implication from the constant-coefficient equation to Jacobi fields; the
parallel frame is $U \mapsto hUh$, so no eigenbasis is chosen. The count of conjugate points with
their multiplicities is proved for $SU(n)$ only (V14.18).

### What is not verified in this chapter

- **§20 for general symmetric spaces** (pp. 109–111): the definition of a symmetric space, Lemma
  20.1, Corollaries 20.2–20.4, locally symmetric spaces, and Theorem 20.5 beyond one-parameter
  subgroups of matrix groups (V12.18) and $SU(n)$ (V14.18). The project's geodesics, curvature and
  Jacobi fields are those of submanifolds of a Euclidean space (Chapters 6–9); isometries of an
  abstract manifold and the parallel eigenframe of Milnor's proof are not formalized.
- **The passage from an abstract Lie group to its Lie algebra:** left-invariant fields, the
  existence of a bi-invariant metric on a compact group by averaging with Haar measure (p. 112),
  and Lemmas 21.1–21.2 and Theorem 21.3 for groups not given as matrices. For matrix groups they
  are V12.14–V12.17; for an abstract group the hypotheses of V12.1–V12.3 remain hypotheses.
- **The topology of Corollaries 21.5 and 21.6:** the application of Myers's theorem (Corollary
  19.5, V11.13) to $G$, the compactness and finite fundamental group of $G$; the splitting of a
  simply connected $G$ as $G' \times \mathbb R^k$. (For 21.5 the exposition also records that $G$
  must be connected.)
- **Theorem 21.7 and its Remarks** (pp. 116–117): the CW structure of $\Omega(G)$ with only even
  cells, finitely many in each dimension (it would combine Theorem 17.3, V10.22, with Theorem 20.5
  and the index theorem for a general compact simply connected $G$), Remark 1 (the homology of
  $\Omega S^3$) and Remark 2 (Iwasawa's theorem). Only the algebra of V12.11–V12.13 is checked.
- **The normal form of a skew-symmetric map** (p. 117), replaced by V12.12.

---

## 14. Chapter 13 (Milnor §22): partly verified

Milnor's §22 (pp. 118–123) shows that when every non-minimal geodesic from $p$ to $q$ has index at
least $\lambda_0$, the space $\Omega^d$ of minimal geodesics carries the homotopy groups of the path
space below $\lambda_0 - 1$ (Theorem 22.1), so that $\pi_i\Omega^d \cong \pi_{i+1}M$ for
$i \le \lambda_0 - 2$ (Corollary 22.2); for antipodal points of $S^{n+1}$ this is the Freudenthal
suspension theorem (Corollary 22.3). The proof perturbs a function whose minimum set is a manifold
without lowering the indices of its other critical points (Lemma 22.4), pushes maps past the
critical levels (Lemma 22.5), and runs this on the finite-dimensional model of Chapter 10.
Verified, for a slice submanifold $N$ of a finite-dimensional inner product space with the induced
metric and Milnor's path space $\Omega = \Omega(N; p, q)$ with his metric (V10.1): Theorem 22.1 in
a strong form (every map of a compact space of small dimension into $\Omega$ is homotopic, relative
to the part already in $\Omega^d$, to a map into $\Omega^d$), with **the hypothesis "$\Omega^d$ is a
topological manifold" replaced by "$\Omega^d$ is a retract of an open neighbourhood in $\Omega$"**,
which is what Milnor's proof uses of it through Hanner's theorem, not formalized; Milnor's corollary
on the inclusion $\Omega^d \to \Omega$, including $\pi_0$ and the surjectivity one degree higher;
Corollary 22.2 as a bijection and, for $i \ge 1$, as a group isomorphism, with the change of
basepoint it hides; Lemmas 22.4 and 22.5 and the exposition's Lemma D; the exposition's Lemmas A and
B for the sphere, the neighbourhood retraction written down there, and Corollary 22.3 with its
second half ($i = 2n - 1$, a surjection), as sets and as groups; and the variant of Theorem 22.1 for
an open and closed set of paths that §24 uses (p. 147). Not verified: Hanner's theorem, the
homological form of the corollary (relative Hurewicz), and the setting of an abstract Riemannian
manifold. Lean: `Morse/Chapter13/` — `Perturbation.lean` (364 lines), `Compression.lean` (358),
`ManifoldOfMinima.lean` (338), `MinimalDeform.lean` (210), `Theorem22.lean` (306),
`Corollaries.lean` (141), `CorollaryGroups.lean` (142), `SphereMinimal.lean` (389),
`Freudenthal.lean` (257), `Componentwise.lean` (385), `SUInstance.lean` (158, reported in Chapter
14); change of basepoint as a homomorphism in `Morse/Homotopy/ChangeOfBaseGroup.lean` (137).

**The setting.** $V$ is a finite-dimensional real inner product space and $N \subseteq V$ a slice
submanifold (V1.6) with the induced metric. $\Omega = \Omega(N; p, q)$ is the space of piecewise
smooth paths with Milnor's metric (V10.1); paths are functions on $\mathbb R$ whose values off
$[0, 1]$ play no role, so this metric is only a pseudometric, and two paths agreeing on $[0, 1]$ are
at distance $0$ (V10.5). $E$ is the energy (V8.5), a geodesic of $\Omega$ is an unbroken geodesic
(V8.10), and its index is the index of $E_{**}$ (V8.14, V9.13). $\rho$ is the Riemannian distance
(V7.18); "the closed balls about $p$ are compact" stands for Milnor's completeness (Hopf–Rinow,
V7.29). $\pi_i(X, x)$ is Mathlib's homotopy group, the classes of maps $I^i \to X$ sending
$\partial I^i$ to $x$ ($\pi_0$ a pointed set); a continuous map induces maps of homotopy groups
(`Morse.Homotopy.homotopyGroupMap`), which are homomorphisms for $i \ge 1$
(`Morse.Homotopy.homotopyGroupHom`). *Pushing maps* (V13.12) replaces relative homotopy groups:
"$\pi_r(X, A) = 0$" is read as "every map $(I^r, \partial I^r) \to (X, A)$ is homotopic relative to
$\partial I^r$ to a map into $A$", the exposition's (H1), and the theorems state this for every
compact space $P$ injected continuously into a real vector space of dimension less than the bound,
for instance $P = I^r$ or $P = I \times I^r$.

**V13.1 (the space $\Omega^d$; `Morse.minPaths`, `Morse.isUnbrokenGeodesic_of_minimal`).**
$\Omega^d$ is the set of paths $\gamma \in \Omega$ whose energy is at most that of every path of
$\Omega$. A path of least energy is an unbroken geodesic. *Book:* p. 118: $\Omega^d$ denotes the
space of minimal geodesics from $p$ to $q$, $d = \rho(p, q)^2$. *Hidden hypotheses:* that the
minimal geodesics, parametrized proportionally to arc length, are exactly the paths of least energy
$d$ (Lemma 12.1, V8.6); that one exists (Hopf–Rinow). *Deviation (restated):* $\Omega^d$ is defined
by least energy; $d$ is not named. *Proof:* a minimum of $E$ is a critical point (every variation
gives a function of $u$ with a minimum at $0$), and Corollary 12.3 (V8.11) applies.

**V13.2 (Theorem 22.1; `Morse.theorem_22_1`, `Morse.compresses_minPaths`, `Morse.minPathsIncl`).**
Let $p, q \in N$, let the closed Riemannian balls about $p$ be compact, and let $\lambda_0 \ge 0$ be
an integer such that every geodesic $\gamma \in \Omega$ which is not of least energy has index
$\ge \lambda_0$. Suppose $\Omega^d$ is a retract of an open neighbourhood: there are an open
$O \supseteq \Omega^d$ and a map $\rho : O \to \Omega^d$, continuous on $O$, equal to the identity on
$\Omega^d$. Let $P$ be a compact space with a continuous injection into a real vector space of
dimension $< \lambda_0$. Then every map $h : P \to \Omega$ is homotopic, relative to
$h^{-1}(\Omega^d)$, to a map into $\Omega^d$; equivalently, the inclusion $\Omega^d \to \Omega$
compresses maps from $P$. *Book:* p. 118, Theorem 22.1: if $\Omega^d$ is a topological manifold and
every non-minimal geodesic from $p$ to $q$ has index $\ge \lambda_0$, then $\pi_i(\Omega, \Omega^d)
= 0$ for $0 \le i < \lambda_0$; proof pp. 122–123. *Hidden hypotheses:* $M$ complete (the standing
assumption of §22); the meaning of $\pi_i(\Omega, \Omega^d) = 0$ for $i = 0, 1$, where these are
sets. *Deviation (narrower):* the manifold hypothesis is replaced by the neighbourhood retraction,
which is all the proof uses of it; for a manifold it follows from Hanner's theorem (in the
metrizable manifold $B$ of broken geodesics, composed with Milnor's $r_1$), which is not formalized.
For the sphere and for $SU(2m)$ the retraction is constructed (V13.8, V14.21). *Deviation
(stronger):* relative to the whole part of $P$ already mapped into $\Omega^d$, at all base points,
for every such $P$. *Proof:* Milnor's, through the finite-dimensional model (V10.4–V10.11): the
energy is bounded on the compact image; Milnor's deformation $r_u$ (V10.7) moves $h$ into the broken
geodesics, fixing $\Omega^d$, which consists of unbroken geodesics (V13.1); the manifold of break
points carries the energy as a smooth function with compact sublevel sets, whose critical points
off the minimum have index $\ge \lambda_0$ by Theorem 16.2 (V10.11); Lemma 22.5 below a level
(V13.14) with the neighbourhood of V13.15 pushes the map into the minimum; the result is moved back
to $\Omega$, corrected on paths at distance $0$. No reparametrization $F \circ E$ is needed, since
V13.14 needs only one compact sublevel set.

**V13.3 (the inclusion $\Omega^d \to \Omega$ on homotopy groups; `Morse.theorem_22_1_bijective`,
`Morse.theorem_22_1_surjective`).** Under the hypotheses of V13.2, at every $\gamma \in \Omega^d$
the inclusion induces a bijection $\pi_i(\Omega^d, \gamma) \to \pi_i(\Omega, \gamma)$ for
$i \le \lambda_0 - 2$ and a surjection for $i \le \lambda_0 - 1$, $\pi_0$ included. For $i \ge 1$
the induced map is a homomorphism, hence an isomorphism of groups. *Book:* p. 118: it follows that
the inclusion homomorphism $\pi_i\Omega^d \to \pi_i\Omega$ is an isomorphism for
$i \le \lambda_0 - 2$ (from the exact sequence of the pair), and onto for $i = \lambda_0 - 1$.
*Hidden hypotheses:* the exact sequence ends with pointed sets; $i = 0$ needs a direct argument
(exposition, §1). *Deviation (restated):* no exact sequence of the pair: compressing cubes gives
surjectivity and compressing cylinders $I \times I^i$ injectivity, uniformly in $i$.

**V13.4 (Corollary 22.2 as a bijection; `Morse.corollary_22_2`, `Morse.pathCHomeomorph`,
`Morse.contractLoop`, `Morse.contractPath`, `Morse.corollary_22_2_surjective`).** Under the
hypotheses of V13.2, for every $\gamma \in \Omega^d$ and $i + 2 \le \lambda_0$ there is a bijection
$\pi_i(\Omega^d, \gamma) \cong \pi_{i+1}(N, p)$; for $i + 1 \le \lambda_0$ there is a surjection
$\pi_i(\Omega^d, \gamma) \to \pi_{i+1}(N, p)$. *Book:* p. 118, Corollary 22.2: $\pi_i\Omega^d \cong
\pi_{i+1}M$ for $0 \le i \le \lambda_0 - 2$, since $\pi_i\Omega \cong \pi_{i+1}M$. *Hidden
hypotheses:* the base point: $\pi_i(\Omega, \gamma)$ is taken at a minimal geodesic, while
$\pi_i(\Omega M) \cong \pi_{i+1}M$ concerns the component of the constant loop; and Theorem 17.1
(V10.19) for $\Omega \simeq \Omega^*$. *Deviation (stronger):* no connectedness of $N$ is needed,
since $\gamma$ itself is used to pass from paths $p \to q$ to loops at $p$. *Proof:* six bijections:
V13.3; $\Omega \to \Omega^*$ (Theorem 17.1); $\Omega^*$ is homeomorphic to Mathlib's paths from $p$
to $q$ in $N$; $\delta \mapsto \delta \cdot \gamma^{-1}$, a homotopy equivalence onto the loops at
$p$, sending $\gamma$ to $\gamma \cdot \gamma^{-1}$; change of basepoint along the contraction
$s \mapsto \gamma|_{[0, s]} \cdot \gamma|_{[0, s]}^{-1}$ to the constant loop; and
$\pi_i(\Omega N) \cong \pi_{i+1}N$.

**V13.5 (change of basepoint is a homomorphism, and Corollary 22.2 as groups;
`Morse.Homotopy.changeBaseMap_mul`, `Morse.Homotopy.changeBaseMulEquiv`,
`Morse.Homotopy.evalZeroHomotopyEquiv`, `Morse.nonempty_mulEquiv_pathSp`,
`Morse.corollary_22_2_mulEquiv`, `Morse.corollary_22_2_surjective_hom`).** For a path $\omega$ from
$y_0$ to $y_1$ in any space $Y$ and $i \ge 1$, the change of basepoint
$\pi_i(Y, y_0) \to \pi_i(Y, y_1)$ along $\omega$ is a group isomorphism. Hence, for every
$\gamma \in \Omega$ and $j \ge 0$, $\pi_{j+1}(\Omega, \gamma) \cong \pi_{j+2}(N, p)$ as groups;
under the hypotheses of V13.2, $\pi_i(\Omega^d, \gamma) \cong \pi_{i+1}(N, p)$ as groups for
$1 \le i \le \lambda_0 - 2$, and there is a surjective homomorphism for $1 \le i \le \lambda_0 - 1$.
*Book:* p. 118, Corollary 22.2 (the isomorphisms are of groups for $i \ge 1$). *Hidden hypotheses:*
that the change of basepoint hidden in "$\pi_i\Omega \cong \pi_{i+1}M$" is a homomorphism.
*Deviation (not in the book):* the homomorphism property is proved, not quoted. *Proof:* on the
free path space $C(I, Y)$, evaluation at $1$ is homotopic to evaluation at $0$ along the tracks
$s \mapsto \omega(s)$, so $(\mathrm{ev}_1)_* = c_\omega \circ (\mathrm{ev}_0)_*$; $(\mathrm{ev}_0)_*$
is onto (it is a homotopy equivalence) and both are homomorphisms, so $c_\omega$ is one; the other
five steps of V13.4 are induced by maps or are Mathlib's loop-space isomorphism.

**V13.6 (the exposition's Lemma A: the geodesics from $p$ to $-p$ on $S^{n+1}$, and the minimal
ones; `Morse.exists_eqOn_greatCircle_antipode`, `Morse.greatCircle_mem_pathSpace_antipode`,
`Morse.pi_sq_le_energy_sph`, `Morse.equator`, `Morse.semicircle`, `Morse.semicircle_mem_minPaths`,
`Morse.exists_eqOn_semicircle`, `Morse.continuous_semicircle`, `Morse.sphMinPathsHomotopyEquiv`,
`Morse.sphMinPathsHomeomorph`).** On the unit sphere $S^{n+1} \subseteq \mathbb R^{n+2}$ (V6.25), for
$p \in S^{n+1}$: every geodesic from $p$ to $-p$ agrees on $[0, 1]$ with
$t \mapsto \cos(Lt)p + \sin(Lt)u$ for a unit $u \perp p$ and $L = (2m + 1)\pi$, $m \ge 0$, and each
of these is one; every path from $p$ to $-p$ has energy $\ge \pi^2$; the paths of least energy are,
on $[0, 1]$, the semicircles $\gamma_u(t) = \cos(\pi t)p + \sin(\pi t)u$, $u$ in the equator
$\{u : \|u\| = 1, u \perp p\}$; $u \mapsto \gamma_u$ is continuous for Milnor's metric and is a
homotopy equivalence from the equator to $\Omega^d$, with homotopy inverse $\gamma \mapsto
\gamma(\tfrac12)$, and a homeomorphism of the equator onto the separation quotient of $\Omega^d$
(paths at distance $0$ identified). *Book:* p. 119, proof of Corollary 22.3: the space $\Omega^{\pi^2}$
of minimal geodesics from $p$ to $-p$ "can be identified with" the equator $S^n$. *Hidden
hypotheses:* the list of geodesics from $p$ to $-p$, and that $d = \pi^2$ (a minimal geodesic
exists and is one of them). *Deviation (restated):* "homeomorphic" holds only up to the separation
quotient, because the pseudometric does not see values off $[0, 1]$; the homotopy equivalence is
what the homotopy groups need. *Proof:* the speeds of the semicircles are all $\pi$, so the $L^2$
part of Milnor's metric vanishes on them, and the uniform part is controlled by pointwise
convergence at bounded energy.

**V13.7 (the exposition's Lemma B: the indices; `Morse.formIndex_greatCircle_antipode`,
`Morse.le_formIndex_of_not_minimal_sph`).** The geodesic $t \mapsto \cos((2m + 1)\pi t)p +
\sin((2m + 1)\pi t)u$ from $p$ to $-p$ on $S^{n+1}$ has index $2mn$. Every geodesic from $p$ to $-p$
that is not of least energy has index $\ge 2n$. *Book:* p. 119: every non-minimal geodesic winds one
and a half times around $S^{n+1}$ and therefore has index $\ge 2n$ (two interior conjugate points of
multiplicity $n$). *Hidden hypotheses:* the conjugate points along a great circle and their
multiplicity $n$ (V10.23); the end point $t = 1$ is conjugate but does not count. *Proof:* the
index theorem (V9.24): the parameters $t = j/(2m + 1)$, $1 \le j \le 2m$, each of multiplicity $n$.

**V13.8 (the neighbourhood retraction for $S^{n+1}$; `Morse.eqComp`, `Morse.sphNbhd`,
`Morse.isOpen_sphNbhd`, `Morse.sphRetrPath`, `Morse.continuousOn_sphRetrPath`,
`Morse.exists_retraction_minPaths_sph`).** The set $O$ of paths $\omega \in \Omega(S^{n+1}; p, -p)$
with $\omega(\tfrac12) \ne \pm p$ is open and contains $\Omega^d$, and $\omega \mapsto$ the
semicircle through the normalized component of $\omega(\tfrac12)$ orthogonal to $p$, changed to the
identity on $\Omega^d$, is a retraction of $O$ onto $\Omega^d$, continuous on $O$. *Book:* p. 119:
"evidently the hypotheses of Theorem 22.1 are satisfied" ($\Omega^d \cong S^n$ is a manifold).
*Deviation (not in the book):* the retraction that Hanner's theorem would provide is written down,
so the hypothesis of V13.2 is proved, not assumed. *Proof:* on $\Omega^d$ the semicircle agrees
with the path on $[0, 1]$, at distance $0$, which keeps the modified map continuous.

**V13.9 (Corollary 22.3, Freudenthal; `Morse.equatorHomeomorph`, `Morse.hball_sph`,
`Morse.hidx_sph`, `Morse.corollary_22_3`, `Morse.corollary_22_3_surjective`,
`Morse.corollary_22_3_mulEquiv`, `Morse.corollary_22_3_surjective_hom`).** For all $x \in S^n$ and
$y \in S^{n+1}$: $\pi_i(S^n, x) \cong \pi_{i+1}(S^{n+1}, y)$ for $i \le 2n - 2$, as sets, and as
groups for $1 \le i \le 2n - 2$; and for $i \le 2n - 1$ there is a surjection
$\pi_i(S^n, x) \to \pi_{i+1}(S^{n+1}, y)$, a homomorphism for $i \ge 1$. *Book:* p. 119, Corollary
22.3: $\pi_iS^n \cong \pi_{i+1}S^{n+1}$ for $i \le 2n - 2$. *Hidden hypotheses:* the base points (the
pole $p = y$ is arbitrary, and every point of $S^n$ is the midpoint of a semicircle). *Deviation
(stronger):* the second half of Freudenthal's theorem, $i = 2n - 1$, which Milnor does not state in
22.3 (it follows from his remark on $\pi_{\lambda_0 - 1}$). Not formalized: that the isomorphism is
the suspension homomorphism (the exposition's remark). *Proof:* V13.4–V13.5 with $\lambda_0 = 2n$
(V13.7), the compact balls of the closed sphere, the retraction V13.8, V13.6, and the equator
$\cong S^n$ by an isometry of $p^\perp$ with $\mathbb R^{n+1}$.

**V13.10 (Lemma 22.4; `Morse.exists_negDef_margin`, `Morse.le_index_of_norm_sub_lt`,
`Morse.lemma_22_4`, `Morse.fderiv_hessian_add`, `Morse.lemma_22_4_add`).** Let $E$ be a
finite-dimensional real normed space, $U \subseteq E$ open, $K \subseteq U$ compact,
$f : E \to \mathbb R$ of class $C^2$ on $U$, and suppose every critical point of $f$ in $K$ has index
$\ge \lambda_0$ (critical points may be degenerate). Then there is $\varepsilon > 0$ such that for
every $g : E \to \mathbb R$ with $\|dg_x - df_x\| < \varepsilon$ and $\|d^2g_x - d^2f_x\| <
\varepsilon$ (operator norms) at every $x \in K$, every critical point of $g$ in $K$ has index
$\ge \lambda_0$. The same with $g = f + h$, $h$ of class $C^2$ on $U$ with its first two derivatives
smaller than $\varepsilon$ on $K$. On the way: a form negative definite on a subspace $W$ is
$\le -\mu\|v\|^2$ there for some $\mu > 0$, and every form within $\mu$ of it has index
$\ge \dim W$. *Book:* p. 119, Lemma 22.4, for $K \subseteq U \subseteq \mathbb R^n$, $f$, $g$
smooth, closeness of the first and second partial derivatives uniformly on $K$; proof pp. 120–121,
through the continuity of the $\lambda$-th eigenvalue and "a uniform continuity argument which will
be left to the reader". *Hidden hypotheses:* that $f$ may have degenerate critical points (needed
in V13.2: non-minimal geodesics may be degenerate). *Deviation (restated):* operator norms instead
of partial derivatives (equivalent up to constants); any finite-dimensional $E$; $f$ only $C^2$.
*Proof:* no eigenvalues: the index is the largest dimension of a negative definite subspace (V1.3,
`Morse.index_isGreatest`), negative definiteness on a fixed subspace survives small perturbations,
and a non-critical point stays non-critical for nearby $g$; compactness of $K$ gives one
$\varepsilon$ (Milnor's left-to-the-reader step).

**V13.11 (Lemma 22.4 on a submanifold; `Morse.exists_perturb_slice`,
`Morse.lemma_22_4_submanifold`).** Let $N \subseteq V$ be a slice submanifold, $F : V \to \mathbb R$
smooth and $K \subseteq N$ compact, and suppose every critical point of $F|N$ in $K$ has index
$\ge \lambda_0$. Then there is $\delta > 0$ such that for every linear form $a$ on $V$ with
$\|a\| < \delta$, every critical point of $(F + a)|N$ in $K$ has index $\ge \lambda_0$. *Book:*
p. 122, in the proof of Lemma 22.5: $g$ is chosen with derivatives so close to those of $f$ that 22.4
applies "in a coordinate neighbourhood" of each point of the compact set. *Deviation (narrower):*
only linear perturbations, the ones by which Corollary 6.8 (V4.22, `Morse.ae_isMorseFunction_add_inner_comp`)
produces Morse functions. *Proof:* V13.10 in each slice chart, the first two derivatives of the
parametrization being bounded on a closed ball; finitely many charts cover $K$.

**V13.12 (pushing maps, and pushing off cells; `Morse.PushesInto`, `Morse.pushesInto_self`,
`Morse.PushesInto.mono`, `Morse.PushesInto.trans`, `Morse.pushesInto_of_isStrongDeformationRetract`,
`Morse.pushesInto_union_cell`, `Morse.pushesInto_union_cells`).** For subsets $A, X$ of a space $T$
and a space $P$: *$A$ pushes maps from $P$ out of $X$* if every map $h : P \to T$ with values in
$X$ is homotopic in $T$, relative to $h^{-1}(A)$, to a map into $A$. This is transitive ($A \subseteq
B$, $A$ pushes out of $B$, $B$ out of $X$ give $A$ out of $X$) and monotone in $X$; a strong
deformation retract $A$ of $X$ pushes maps from every $P$ out of $X$. If $T$ is Hausdorff, $A$ closed,
$P$ compact with a continuous injection into a real vector space of dimension $d$, and
$\chi_1, \dots, \chi_k$ are continuous maps of closed unit balls of dimensions $n_i > d$, injective,
with pairwise disjoint images, each meeting $A$ exactly in the image of the boundary sphere, then
$A$ pushes maps from $P$ out of $A \cup \chi_1(D^{n_1}) \cup \dots \cup \chi_k(D^{n_k})$. *Book:*
p. 122: "since $r < \lambda_0$ it follows that $h$ is homotopic … to a map into
$g^{-1}(-\infty, 2\delta]$". *Hidden hypotheses:* the push-off lemma of cellular approximation
(Hatcher, Lemma 4.10), the exposition's (T5); deformations fixing the lower level. *Deviation (not in
the book):* the notion of pushing replaces $\pi_r(X, A) = 0$. *Proof:* one cell is the compression
lemma for attaching a cell (Part XII of the proof-by-proof edition); several cells by induction, the
partial union being closed.

**V13.13 (the exposition's Lemma D: passing critical levels of high index; `Morse.exists_gap_of_finite`,
`Morse.lemma_D`).** Let $N \subseteq V$ be a slice submanifold, $F : V \to \mathbb R$ smooth,
$f = F|N$, with $f^{-1}(-\infty, a_0]$ compact; let $a$ be a regular value of $f$, and suppose every
critical point $q$ with $a < f(q) \le a_0$ is non-degenerate of index $\ge \lambda_0$. Let $P$ be
compact with a continuous injection into a real vector space of dimension $< \lambda_0$. Then for
$a \le b < a_0$, $N^a = f^{-1}(-\infty, a]$ pushes maps from $P$ out of $N^b$. *Book:* p. 122:
$g^{-1}(-\infty, c + \delta]$ "has the homotopy type of" $g^{-1}(-\infty, 2\delta]$ with cells of
dimension $\ge \lambda_0$ attached. *Hidden hypotheses:* the critical points above $a$ are finitely
many (isolated in a compact set, and not accumulating at the regular level $a$); the deformations of
Theorem 3.1 and Remark 3.3 fix the lower level, which an abstract homotopy type would not provide.
*Deviation (restated):* the exposition's lemma, with $b$ not required to be regular. *Proof:*
induction on the number of critical points below $b$: Theorem 3.1 on a submanifold (V2.3,
`Morse.theorem_3_1_submanifold`) between critical levels, Remark 3.3 (V2.9, `Morse.remark_3_3_submanifold`)
at a critical level, V13.12 for the cells.

**V13.14 (Lemma 22.5; `Morse.pushesInto_of_deformation`, `Morse.criticalPoint_hessianM_congr`,
`Morse.lemma_22_5_sublevel`, `Morse.lemma_22_5`).** Let $N \subseteq V$ be a slice submanifold,
$F : V \to \mathbb R$ smooth, $f = F|N \ge d$, $M^0 = f^{-1}(d)$, and $P$ compact with a continuous
injection into a real vector space of dimension $< \lambda_0$. Suppose $M^0$ has an open
neighbourhood $U$ such that $M^0$ pushes maps from $P$ out of $U$ (for instance, $U$ deforms into
$M^0$ within $N$, fixing $M^0$). (i) If $f^{-1}(-\infty, a_0]$ is compact and every critical point
$q$ with $d < f(q) < a_0$ has index $\ge \lambda_0$, then $M^0$ pushes maps from $P$ out of
$f^{-1}(-\infty, b]$ for every $b < a_0$. (ii) If all sublevel sets are compact and every critical
point outside $M^0$ has index $\ge \lambda_0$, then $M^0$ pushes maps from $P$ out of $N$. *Book:*
p. 121, Lemma 22.5: for $f : M \to \mathbb R$ smooth with minimum $0$ and compact $M^c$, if $M^0$ is
a manifold and every critical point in $M - M^0$ has index $\ge \lambda_0$, then $\pi_r(M, M^0) = 0$
for $0 \le r < \lambda_0$; proof pp. 121–122. *Hidden hypotheses:* $M^0$ compact; the approximation
$g$ must live on an open set, where $f$ is bounded; regular levels. *Deviation (narrower):* the
conclusion of Milnor's first step (Hanner's theorem and short geodesics: a neighbourhood deforming
into $M^0$) is the hypothesis on $U$. *Deviation (stronger):* (i) needs only one compact sublevel
set, the form used in V13.2. *Proof:* $g = F + \rho\ell$, $\ell$ a small linear form making
$(F + \ell)|N$ a Morse function (Corollary 6.8) and $\rho$ a bump function equal to $1$ near the
compact $f^{-1}(-\infty, a_0]$, so that $|g - f|$ is small on all of $N$; Lemma 22.4 (V13.11) keeps
the indices; a regular level of $g$ just above $d$; Lemma D (V13.13) for $g$; then $U$.

**V13.15 (deforming a neighbourhood of the minima in the model; `Morse.BrokenSetup.mem_ball_of_mem_nodes`,
`Morse.BrokenSetup.joinVec_self`, `Morse.BrokenSetup.exists_pushesInto_nodes`).** In the
finite-dimensional model of Chapter 10 (a broken-geodesic setup with energy bound $c$, V10.3–V10.4),
let $N^m \cap O$ ($O$ open) consist of admissible break points and $d < c$. If $\{\gamma \in \Omega :
E(\gamma) \le d\}$ is a retract of an open set of $\Omega$ containing it, then
$\{y \in N^m \cap O : E'(y) \le d\}$ has an open neighbourhood in $N^m \cap O$ from which it pushes
maps from every $P$. *Book:* p. 121: "taking $U$ small, we may assume that each point of $U$ is
joined to its image under the retraction by a unique minimal geodesic; hence $U$ can be deformed into
$M^0$ within $M$". *Hidden hypotheses:* the deformation must stay in the open manifold $N^m \cap O$
(true near $M^0$ by the tube lemma); the retraction in $\Omega$ is transported to break points.
*Proof:* each break point is moved to the corresponding break point of the retracted path along the
short geodesic of Corollary 10.8 (V7.20); this fixes $M^0$.

**V13.16 (Theorem 22.1 for an open and closed set of paths, the exposition's Lemma 6.2 of Chapter
15; `Morse.PathSp.mem_of_edist_eq_zero`, `Morse.theorem_22_1_clopen`, `Morse.clopenIncl`,
`Morse.compresses_clopenIncl`, `Morse.theorem_22_1_clopen_bijective`,
`Morse.theorem_22_1_clopen_bijective_minPathsIncl`, `Morse.Homotopy.bijective_homotopyGroupMap_clopen`).**
In the setting of V13.2 (compact balls, neighbourhood retraction), let $\Omega' \subseteq \Omega$ be
open and closed, and suppose every geodesic *in $\Omega'$* that is not of least energy has index
$\ge \lambda_0$. Then every map $h : P \to \Omega'$ ($P$ as in V13.2) is homotopic, relative to
$h^{-1}(\Omega^d)$, to a map into $\Omega^d \cap \Omega'$. Hence the inclusion
$\Omega^d \cap \Omega' \to \Omega'$ is bijective on $\pi_i$ for $i \le \lambda_0 - 2$, $\pi_0$
included, and the inclusion $\Omega^d \to \Omega$ is bijective on $\pi_i$,
$1 \le i \le \lambda_0 - 2$, at every point of $\Omega^d \cap \Omega'$. On the way: the inclusion of
an open and closed set containing the base point is bijective on $\pi_i$, $i \ge 1$, in any space.
*Book:* p. 147 (§24, case $k \equiv 2 \pmod 4$): "a variant of Theorem 22.1 for the component
$\Omega^{(c)}$ of the path space"; the exposition states it as Lemma 6.2. *Hidden hypotheses:* where
the proof of 22.1 must see $\Omega'$ (the deformation $r_u$ keeps each path in its component, the
manifold of break points is cut down to the paths in $\Omega'$, and the last homotopy stays there);
$d$ is the least energy on all of $\Omega$, and $\Omega'$ need not contain a minimal geodesic.
*Deviation (stronger):* any open and closed set, not only a path component.

### What is not verified in this chapter

- **Hanner's theorem** (p. 121): a topological manifold is a neighbourhood retract. Theorem 22.1
  (V13.2) and Lemma 22.5 (V13.14) assume its conclusion; for the sphere and for $SU(2m)$ the
  retraction is constructed (V13.8, V14.21), so Corollary 22.3 and Theorem 23.3 are unconditional.
- **The homological form** (p. 118): $H_i(\Omega, \Omega^d) = 0$ for $i < \lambda_0$ and
  $H_i\Omega^d \cong H_i\Omega$ for $i \le \lambda_0 - 2$, by the relative Hurewicz theorem; and
  $H_i(\Omega S^{n+1}) \cong H_iS^n$ for $i \le 2n - 2$.
- **Relative homotopy groups and the exact sequence of the pair** $(\Omega, \Omega^d)$: replaced by
  pushing maps (V13.12) and compression (V13.3).
- **Milnor's eigenvalue argument** for Lemma 22.4 (continuity of the $\lambda$-th eigenvalue, his
  footnote's minimax): not needed (V13.10).
- **That the isomorphism of Corollary 22.3 is the suspension homomorphism** (exposition), and the
  exposition's application (§5: the stable stems, Toda's table). The first statement of that
  application, $\pi_jS^N = 0$ for $j < N$, is verified, though not by the induction through
  Corollary 22.3 given there: `Morse.Homotopy.subsingleton_pi_sphere`, by pushing maps off a point
  (see V14.25).
- **§22 on an abstract Riemannian manifold**: only for submanifolds of a Euclidean space with the
  induced metric (Nash's theorem quoted).

---

## 15. Chapter 14 (Milnor §23): partly verified

Milnor's §23 (pp. 124–132) proves Bott periodicity for the unitary group. He reviews $U(n)$, its
exponential and its bi-invariant metric
$\langle A, B\rangle = \operatorname{Re}\operatorname{tr}(AB^*)$ (pp. 124–126), finds the geodesics
from $I$ to $-I$ and the minimal ones (p. 127), identifies the minimal geodesics in $SU(2m)$ with
the Grassmannian $G_m(\mathbb C^{2m})$ (Lemma 23.1), shows that every other geodesic has index at
least $2m + 2$ (Lemma 23.2, proved on pp. 130–132), deduces from §22 that
$G_m(\mathbb C^{2m}) \to \Omega(SU(2m); I, -I)$ is an isomorphism on $\pi_i$ for $i \le 2m$ (Theorem
23.3), and with the fibrations of Lemma 23.4 obtains $\pi_{i-1}U \cong \pi_{i+1}U$ and the stable
homotopy groups of $U$ (Theorem 23.5). What is verified first is the computation on which Lemma 23.2
rests, for the diagonal velocity $A = \operatorname{diag}(i\pi k_1, \dots, i\pi k_n)$: the matrix
facts ($\exp A = -I$ exactly for odd $k_j$, the traces of $AA^*$ and of $A$, Lemma 23.1 as a
statement about projections, the entries of $K_A(W) = \tfrac14[[A, W], A]$, Milnor's eigenvectors
and the fact that they span), the count of conjugate points produced by an eigenvalue, the index
formula $\lambda = \sum_{k_i > k_j}(k_i - k_j - 2)$ from Milnor's spectrum, and Lemma 23.2 for that
formula; there Theorems 20.5 and 15.1 enter as definitions (V14.7, V14.8). Then the geometry and
the topology (V14.13–V14.30): $U(n)$ and $SU(n)$ as compact submanifolds of the space of matrices
with the induced bi-invariant metric; every geodesic from $I$ to $-I$ in $SU(n)$ is
$t \mapsto \exp(tA)$ with $A$ unitarily conjugate to Milnor's diagonal form; the distance from $I$ to
$-I$ in $SU(2m)$ and the minimal geodesics; Lemma 23.1 as a homeomorphism of the set of initial
velocities with the Grassmannian, and as a homotopy equivalence (a homeomorphism after identifying
paths that agree on $[0, 1]$) with the space $\Omega^d$ of minimal paths; Theorem 20.5 for $SU(n)$,
so that the index of every geodesic from $I$ to $-I$ is the formula above, by the project's Index
Theorem, and Lemma 23.2 for geodesics; the neighbourhood retraction that Theorem 22.1 (Chapter 13)
assumes; Theorem 23.3; the bundles of Lemma 23.4 on concrete Stiefel manifolds and Grassmannians,
with their exact sequences; Lemma 23.4; the periodicity theorem; and Theorem 23.5 — each as a
bijection of pointed sets and, where both sides are groups, as a group isomorphism. The stable
groups $\pi_iU$ are not defined as a limit: the statements are about $\pi_jU(m)$ in the stable
range, and the periodicity theorem is stated for $1 \le i \le 2m - 2$. Not verified: the linear
independence of Milnor's eigenvectors, the space form of Bott's theorem (the exposition's Corollary
23.6), and that $\sum k_j$ is constant on the components of the path space of $U(n)$. Lean:
`Morse/Chapter14/` — `SUMatrices.lean` (318 lines), `IndexCount.lean` (710; it also contains the
counts of §24, reported in Chapter 15, and the evenness step of Theorem 21.7, reported in Chapter
12), `MinimalPaths.lean` (311), `MinimalRetract.lean` (337), `Periodicity.lean` (198),
`PeriodicityGroups.lean` (139), `CircleGroup.lean` (93); `Morse/Chapter12/` — `MatrixInner.lean`,
`MatrixGroups.lean` (the groups), `SUMinimal.lean` (444), `SUJacobi.lean` (370), `SUIndex.lean`
(530); `Morse/Chapter13/SUInstance.lean` (158); `Morse/Homotopy/` — `Homogeneous.lean` (137),
`Stiefel.lean` (530), `Grassmannian.lean` (595), `BundleHomotopy.lean` (408),
`BundlesUnitary.lean` (595), on top of the homotopy groups, Serre fibrations and exact sequences
of Part XII of the proof-by-proof edition.

**Conventions.** Matrices are complex $n \times n$ matrices indexed by a finite set, $A^*$ is the
conjugate transpose, $\exp$ is Mathlib's matrix exponential, and $k = (k_1, \dots, k_n)$ is a family
of integers indexed by a finite set.

**V14.1 ($\exp A = -I$ for diagonal $A$; `Morse.exp_diagonal_eq_neg_one_iff`,
`Morse.exp_ofReal_mul_I_eq_neg_one_iff`).** For a real number $a$, $e^{ia} = -1$ iff $a = \pi k$
with $k$ an odd integer. Hence for real $a_1, \dots, a_n$,
$\exp\operatorname{diag}(ia_1, \dots, ia_n) = -I$ iff every $a_j$ is $\pi$ times an odd integer.
*Book:* p. 127: for diagonal $A = \operatorname{diag}(ia_1, \dots, ia_n)$,
$\exp A = \operatorname{diag}(e^{ia_1}, \dots, e^{ia_n})$, so $\exp A = -I$ iff
$A = \operatorname{diag}(k_1i\pi, \dots, k_ni\pi)$ with odd integers $k_j$. *Hidden hypotheses:*
none. *Deviation (narrower):* only diagonal $A$; the reduction of a general skew-Hermitian $A$ by
$\exp(TAT^{-1}) = T(\exp A)T^{-1}$ (pp. 126–127) is V14.14.

**V14.2 (length and trace of the velocity; `Morse.suDiag`, `Morse.trace_suDiag_mul_conjTranspose`,
`Morse.trace_suDiag`).** For integers $k_j$ and
$A = \operatorname{diag}(i\pi k_1, \dots, i\pi k_n)$, $\operatorname{tr}(AA^*) = \pi^2\sum_j k_j^2$
and $\operatorname{tr}A = i\pi\sum_j k_j$. *Book:* p. 127: the geodesic $t \mapsto \exp tA$,
$0 \le t \le 1$, has length $|A| = \sqrt{\operatorname{tr}AA^*} = \pi\sqrt{k_1^2 + \dots + k_n^2}$;
p. 130: $A$ in the Lie algebra of $SU(n)$ gives a geodesic from $I$ to $-I$ iff its eigenvalues are
$i\pi k_1, \dots, i\pi k_n$ with odd $k_j$ of sum zero. *Hidden hypotheses:* none. *Deviation
(restated):* only the trace identities; that $|A|$ is the length of the geodesic is V14.15.

**V14.3 (minimal geodesics, arithmetically; `Morse.card_le_sum_sq`, `Morse.sum_sq_eq_card_iff`,
`Morse.card_eq_of_minimal`).** For odd integers $k_1, \dots, k_n$, $\sum_j k_j^2 \ge n$, with
equality iff every $k_j = \pm1$. If $n = 2m$, every $k_j = \pm1$ and $\sum_j k_j = 0$, then exactly
$m$ of the $k_j$ equal $1$ and $m$ equal $-1$. *Book:* p. 127: $A$ determines a minimal geodesic iff
each $k_j = \pm1$, the length then being $\pi\sqrt n$; in $SU(2m)$ the condition
$\operatorname{tr}A = 0$ makes $\operatorname{Eigen}(i\pi)$ $m$-dimensional. *Hidden hypotheses:*
none. *Deviation (restated):* "minimal" is read through V14.2 as "of least $\sum k_j^2$"; that this
is minimality of the geodesic among all geodesics from $I$ to $-I$ (all of which are conjugate to
diagonal ones) is V14.15.

**V14.4 (Lemma 23.1 as a statement about projections; `Morse.sq_eq_neg_pi_sq_iff`,
`Morse.trace_pi_smul_projection`).** For a skew-Hermitian matrix $A$: $A^2 = -\pi^2I$ iff
$A = i\pi(2P - I)$ for some Hermitian projection $P$ ($P^* = P = P^2$). For every $P$,
$\operatorname{tr}\big(i\pi(2P - I)\big) = i\pi(2\operatorname{tr}P - n)$, so in $SU(n)$ the
condition $\operatorname{tr}A = 0$ reads $\operatorname{tr}P = n/2$. *Book:* p. 127: a minimal $A$
is completely determined by $\operatorname{Eigen}(i\pi)$, an arbitrary subspace of $\mathbb C^n$ (of
dimension $m$ in $SU(2m)$); p. 128, Lemma 23.1: the space of minimal geodesics from $I$ to $-I$ in
$SU(2m)$ is homeomorphic to $G_m(\mathbb C^{2m})$. *Hidden hypotheses:* "completely determined by
$\operatorname{Eigen}(i\pi)$" uses that a skew-Hermitian matrix is normal, so that its eigenspaces
are orthogonal; the formal proof produces the projection without the spectral theorem. *Deviation
(narrower):* a correspondence of sets of matrices only. Not formalized: that $P$ is the projection
onto $\operatorname{Eigen}(i\pi)$ (immediate from $A = i\pi(2P - I)$) and that $\operatorname{tr}P$
is the dimension of the range of $P$ (the Grassmannian is defined by the trace, V14.16). That
$A^2 = -\pi^2I$ is equivalent to minimality is V14.15, and the topology is V14.16–V14.17.

**V14.5 (the operator $K_A$ for diagonal $A$; `Morse.jacobiMat`, `Morse.commutator_diagonal_apply`,
`Morse.jacobiMat_suDiag_apply`).** Put $K_A(W) = \tfrac14[[A, W], A]$ for matrices $A, W$, with
$[A, W] = AW - WA$. For a diagonal matrix $\operatorname{diag}(d)$, the $(j, l)$ entry of
$[\operatorname{diag}(d), W]$ is $(d_j - d_l)w_{jl}$; for
$A = \operatorname{diag}(i\pi k_1, \dots, i\pi k_n)$ and every $W$, the $(j, l)$ entry of $K_A(W)$
is $\tfrac{\pi^2}{4}(k_j - k_l)^2w_{jl}$. *Book:* p. 130: by Theorem 20.5 the conjugate points are
determined by $K_A(W) = R(A, W)A = \tfrac14[[A, W], A]$; "a short computation" gives
$[A, W] = (i\pi(k_j - k_l)w_{jl})$, $[A, [A, W]] = (-\pi^2(k_j - k_l)^2w_{jl})$, and (p. 131)
$K_A(W) = (\tfrac{\pi^2}{4}(k_j - k_l)^2w_{jl})$. *Hidden hypotheses:* none. *Deviation (restated):*
$K_A$ is defined by the matrix formula. That it is $W \mapsto R(A, W)A$ for the bi-invariant metric
of $SU(n)$ is Theorem 21.3 (b) applied to the Lie algebra of skew-Hermitian matrices with the
commutator as bracket (p. 124); that application is V12.17 (for every matrix group).

**V14.6 (Milnor's eigenvectors, and that they span; `Morse.eReal`, `Morse.eImag`,
`Morse.jacobiMat_eReal`, `Morse.jacobiMat_eImag`, `Morse.jacobiMat_diagonal`,
`Morse.eReal_conjTranspose`, `Morse.eImag_conjTranspose`, `Morse.trace_eReal`, `Morse.trace_eImag`,
`Morse.eq_diagonal_add_sum_eReal_eImag`).** Let $E_{jl}$ have $+1$ at $(j, l)$ and $-1$ at $(l, j)$,
and $E'_{jl}$ have $i$ at both places. Both are skew-Hermitian, of trace $0$ when $j \neq l$, and
eigenvectors of $K_A$ (V14.5) with eigenvalue $\tfrac{\pi^2}{4}(k_j - k_l)^2$; every diagonal matrix
lies in the kernel of $K_A$. Every skew-Hermitian $W$ equals its diagonal part plus
$\sum_{j < l}\big(\operatorname{Re}w_{jl}\,E_{jl} + \operatorname{Im}w_{jl}\,E'_{jl}\big)$, for any
linear order of the index set. *Book:* p. 131: a basis of the Lie algebra of $SU(n)$ consisting of
eigenvectors of $K_A$: $E_{jl}$ and $E'_{jl}$ for $j < l$, with eigenvalue
$\tfrac{\pi^2}{4}(k_j - k_l)^2$, and the diagonal matrices of the Lie algebra, with eigenvalue $0$;
so the non-zero eigenvalues are the $\tfrac{\pi^2}{4}(k_j - k_l)^2$ with $k_j > k_l$, each counted
twice. *Hidden hypotheses:* Milnor does not say why these vectors span. *Deviation (narrower):*
spanning is proved, linear independence (the count $n(n-1) + (n-1) = \dim\mathfrak{su}(n)$) is not;
so "the spectrum of $K_A$ with multiplicity is Milnor's list" is not a formal theorem, and Milnor's
list is the input of V14.9. (The index computation of V14.18–V14.19 needs no eigenbasis.)

**V14.7 (conjugate parameters of an eigenvalue: Theorem 20.5 as a definition; `Morse.conjParams`,
`Morse.conjParams_finite`, `Morse.conjParams_sq`, `Morse.ncard_conjParams_sq`).** For a real number
$e$, the set of conjugate parameters of $e$ is
$\{t : 0 < t < 1,\ e > 0,\ t = \pi s/\sqrt e \text{ for some integer } s\}$, empty when $e \le 0$.
It is finite, and for $e = (\pi d)^2$ with $d \ge 1$ an integer it is
$\{1/d, 2/d, \dots, (d-1)/d\}$, with $d - 1$ elements. *Book:* p. 110, Theorem 20.5: the conjugate
points to $p$ along $\gamma$ are the $\gamma(\pi k/\sqrt{e_i})$, $k$ a non-zero integer and $e_i$ a
positive eigenvalue of $K_V$; p. 131: each eigenvalue $e > 0$ gives conjugate points at
$t = \pi/\sqrt e, 2\pi/\sqrt e, \dots$, here $t = 2/(k_j - k_l), 4/(k_j - k_l), \dots$, and the
number in $(0, 1)$ is "evidently" $(k_j - k_l)/2 - 1$. *Hidden hypotheses:* the count needs
$k_j - k_l$ even (both are odd), so that $\tfrac{\pi^2}{4}(k_j - k_l)^2 = (\pi d)^2$ with
$d = (k_j - k_l)/2$ an integer. *Deviation (restated):* Theorem 20.5 is not proved here; this set is its
conclusion, for a geodesic parametrized on $[0, 1]$, taken as a definition (for $SU(n)$ Theorem 20.5
is V14.18, which shows that this definition gives the multiplicities). The reader should
confirm that it says what 20.5 says.

**V14.8 (the index of a spectrum: Theorems 20.5 and 15.1 as a definition; `Morse.conjMult`,
`Morse.spectralIndex`, `Morse.spectralIndex_eq`, `Morse.spectralIndex_double`).** For a finite
family $e = (e_i)$ of real numbers (the eigenvalues of $K_V$ with multiplicity), the multiplicity of
$t$ is the number of $i$ such that $t$ is a conjugate parameter of $e_i$ (Theorem 20.5), and the
index of $e$ is the sum of these multiplicities over all $t$ (only $t \in (0, 1)$ contribute; the
Index Theorem 15.1). It equals $\sum_i \#\{\text{conjugate parameters of } e_i\}$. A family in which
every value is repeated twice has twice the index. *Book:* p. 110, Theorem 20.5: the multiplicity of
$\gamma(t)$ as a conjugate point is the number of $e_i$ such that $t$ is a multiple of
$\pi/\sqrt{e_i}$; p. 131: applying the Index Theorem and "adding over all $j, l$". *Hidden
hypotheses:* "adding over all $j, l$" exchanges the sum over conjugate points $t$ with the sum over
eigenvalues. *Deviation (restated):* a definition; that it is the Morse index of the energy at the
geodesic, through Theorems 15.1 and 20.5, is V14.19.

**V14.9 (the index formula; `Morse.bottIndex`, `Morse.pairSpectrum`, `Morse.suSpectrum`,
`Morse.two_mul_ncard_conjParams`, `Morse.two_mul_spectralIndex_pairSpectrum`,
`Morse.spectralIndex_suSpectrum`).** Put $\operatorname{bott}(k) = \sum (k_i - k_j - 2)$, the sum
over the ordered pairs $(i, j)$ with $k_i > k_j$. For odd integers $a > b$, the eigenvalue
$\tfrac{\pi^2}{4}(a - b)^2$ has $(a - b)/2 - 1$ conjugate parameters (V14.7). Hence, if all $k_j$
are odd, the index (V14.8) of Milnor's spectrum — the number $\tfrac{\pi^2}{4}(k_i - k_j)^2$ for
each pair with $k_i > k_j$, each counted twice — is $\operatorname{bott}(k)$; with each counted once
it is $\tfrac12\operatorname{bott}(k)$. *Book:* p. 131: each pair $k_j > k_l$ gives two copies of
$\tfrac{\pi^2}{4}(k_j - k_l)^2$ and contributes $2((k_j - k_l)/2 - 1)$, whence
$\lambda = \sum_{k_j > k_l}(k_j - k_l - 2)$. *Hidden hypotheses:* as in V14.7 and V14.8. *Deviation
(restated):* the conclusion concerns the index of Milnor's spectrum; that it is the Morse index of
the geodesic $t \mapsto \exp tA$ is V14.19.

**V14.10 (elementary properties of the formula; `Morse.bottIndex_nonneg`, `Morse.bottIndex_neg`,
`Morse.bottIndex_comp_equiv`, `Morse.bottIndex_eq_zero_of_minimal`).** If all $k_j$ are odd,
$\operatorname{bott}(k) \ge 0$ (every term is). For all $k$,
$\operatorname{bott}(-k) = \operatorname{bott}(k)$ and $\operatorname{bott}$ does not change when
the $k_j$ are reordered. If every $k_j = \pm1$, $\operatorname{bott}(k) = 0$. *Book:* pp. 131–132:
for a minimal geodesic all $k_j = \pm1$, hence $\lambda = 0$; the reordering is Milnor's
normalization $k_1 \ge \dots \ge k_n$ (p. 130), and the symmetry is his "(say) negative" (p. 132).
*Hidden hypotheses:* none.

**V14.11 (Lemma 23.2; `Morse.bottIndex_ge`, `Morse.exists_pos_neg_data`,
`Morse.sum_pos_neg_le_bottIndex`, `Morse.sum_pos_neg_eq`).** Let $k_1, \dots, k_{2m}$ be odd
integers with $\sum_j k_j = 0$, not all equal to $\pm1$. Then $\operatorname{bott}(k) \ge 2m + 2$.
*Book:* p. 128, Lemma 23.2: every non-minimal geodesic from $I$ to $-I$ in $SU(2m)$ has index
$\ge 2m + 2$; proof on p. 132: Case 1, at least $m + 1$ of the $k_j$ (say) negative, so some
positive $k_j \ge 3$ and $\lambda \ge 2(m + 1)$; Case 2, $m$ positive and $m$ negative, not all
$\pm1$, so one is $\ge 3$ and one $\le -3$, and $\lambda \ge 4m \ge 2(m + 1)$. *Hidden hypotheses:*
"(say) negative" needs the symmetry $k \mapsto -k$ (V14.10); the claims that some positive $k_j$ is
$\ge 3$ (Case 1) and that one $k_j$ is $\ge 3$ and one $\le -3$ (Case 2) use $\sum k_j = 0$, and
Case 2 also the equal numbers of each sign. *Deviation (restated):* a statement about the formula; for the index of a geodesic it is
V14.20. *Proof:* both
cases through the sum over the pairs (positive $k_i$, negative $k_j$), which equals
$N S_+ + P S_- - 2PN$ ($P$, $N$ the numbers of positive and negative $k_j$, $S_+$ and $S_-$ the sums
of the positive $k_j$ and of the $|k_j|$ with $k_j < 0$); this reproduces Milnor's bounds $2N$ and
$4m$.

**V14.12 (why not $U(n)$; `Morse.remarkK`, `Morse.bottIndex_remarkK`, `Morse.not_minimal_remarkK`,
`Morse.sum_remarkK`, `Morse.abs_sum_le_card_of_minimal`).** For
$k = (3, 1, \dots, 1) \in \mathbb Z^{n+1}$: $\operatorname{bott}(k) = 0$, not every $k_j$ is $\pm1$,
and $\sum_j k_j = (n + 1) + 2$; whereas every family of entries $\pm1$ has $|\sum_j k_j|$ at most
the number of entries. *Book:* p. 127: the space of minimal geodesics in $U(n)$ is "rather
inconvenient", having components of varying dimensions, which is why Milnor passes to $SU(2m)$.
*Deviation (not in the book):* the exposition's stronger reason: in $U(n + 1)$ the non-minimal
geodesic with $k = (3, 1, \dots, 1)$ has index $0$ (by V14.9's formula) and lies in a component of
the path space containing no minimal geodesic, so Theorem 22.1 cannot be applied to $U(n)$. That
$\sum k_j$, the degree of $\det$ along the geodesic, is constant on the components of the path space
is topology and is not formalized.

**The geometry and the topology.** From here on $U(n)$, $SU(n)$ are the matrix groups of Chapter 12
(V12.14) inside $M_n(\mathbb C)$ with the Frobenius inner product, $\Omega = \Omega(SU(n); I, -I)$ is
Milnor's path space with his metric (V10.1, Chapter 13), $\Omega^d$ its subset of paths of least
energy (V13.1), and homotopy groups and pushing maps are as in Chapter 13. A *Hermitian projection*
is a matrix $P$ with $P^* = P = P^2$; $G_m(\mathbb C^n)$ is the set of Hermitian projections of trace
$m$ with the subspace topology (the projections onto the $m$-dimensional subspaces). A *Stiefel
manifold* $V_k(\mathbb K^n)$ is the set of $n \times k$ matrices $F$ with $F^*F = I$ (orthonormal
$k$-frames), with the subspace topology. Locally trivial maps, Serre fibrations and their exact
homotopy sequences are those of Part XII of the proof-by-proof edition
(`Morse.Homotopy.IsLocallyTrivial`, `Morse.Homotopy.IsSerreFibration`).

**V14.13 ($U(n)$ and $SU(n)$; `Morse.unitaryMap`, `Morse.isRegularValue_unitaryMap`,
`Morse.isSliceSubmanifold_unitaryGroup`, `Morse.isMatrixGroup_unitaryGroup`,
`Morse.isCompact_unitaryGroup`, `Morse.specialSkewHermitian`, `Morse.suMap`,
`Morse.isRegularValue_suMap`, `Morse.isSliceSubmanifold_specialUnitaryGroup`,
`Morse.isMatrixGroup_specialUnitaryGroup`, `Morse.isCompact_specialUnitaryGroup`,
`Morse.fderiv_det_mul`, `Morse.det_exp_smul_of_trace_eq_zero`).** $U(n) = \{A : A^*A = I\}$ is a
compact slice submanifold of $M_n(\mathbb C)$ modelled on $\mathfrak u(n)$, the skew-Hermitian
matrices, and $(U(n), \mathfrak u(n))$ is a matrix group; for $n \ge 1$,
$SU(n) = \{A \in U(n) : \det A = 1\}$ is a compact slice submanifold modelled on $\mathfrak{su}(n)$,
the traceless skew-Hermitian matrices, and $(SU(n), \mathfrak{su}(n))$ is a matrix group. Jacobi's
formula $d(\det)_A(AX) = \det A \cdot \operatorname{tr}X$ holds, and $\det\exp(tX) = 1$ when
$\operatorname{tr}X = 0$. (The same file gives $O(n)$ and $SO(n)$, used in Chapter 15.) *Book:*
pp. 124–126: $U(n)$ is a compact smooth submanifold of $M_n(\mathbb C)$ and a Lie group, with tangent
space $\mathfrak u(n)$ at $I$ ((5), (6)), Lie bracket the commutator, the bi-invariant metric
$\operatorname{Re}\operatorname{tr}(AB^*)$; $\det\exp A = e^{\operatorname{tr}A}$, and $SU(n)$ with
Lie algebra $\mathfrak{su}(n)$. *Hidden hypotheses:* $n \ge 1$ for $SU(n)$. *Deviation (restated):*
$U(n)$ is a regular level set of $A \mapsto A^*A - I$ (Hermitian values) rather than a submanifold by
the chart $\exp$; $SU(n)$ is not a regular level set of $(A^*A - I, \det A - 1)$, and is obtained as
the open piece $\operatorname{Re}\det > 0$ of the regular level set
$\{A^*A = I, \operatorname{Im}\det A = 0\}$; only the traceless case of
$\det\exp A = e^{\operatorname{tr}A}$ is proved. The bracket of left-invariant fields is not used
(V12.17). Not formalized: that $\exp$ is onto and that $SU(n)$ is connected (not needed).

**V14.14 (every geodesic from $I$ to $-I$ in $SU(n)$ is of Milnor's form;
`Morse.eqOn_exp_smul_of_isUnbrokenGeodesic_su`, `Morse.exists_unitary_suDiag`,
`Morse.exp_conj_suDiag`, `Morse.conj_suDiag_mem`, `Morse.mem_pathSpace_exp`,
`Morse.isUnbrokenGeodesic_exp`).** Every geodesic $\gamma \in \Omega(SU(n); I, q)$ agrees on $[0, 1]$
with $t \mapsto \exp(tA)$ for some $A \in \mathfrak{su}(n)$. If $A \in \mathfrak{su}(n)$ and
$\exp A = -I$, there are a unitary $T$ and odd integers $k_j$ with $\sum k_j = 0$ and
$A = T\operatorname{diag}(i\pi k_1, \dots, i\pi k_n)T^*$; conversely every such $A$ lies in
$\mathfrak{su}(n)$ and has $\exp A = -I$, and then $t \mapsto \exp(tA)$ is a geodesic in
$\Omega(SU(n); I, -I)$. *Book:* pp. 126–127: after conjugation by a unitary matrix, a skew-Hermitian
$A$ is diagonal, $\exp A = -I$ iff $A$ has eigenvalues $i\pi k_j$ with $k_j$ odd; p. 130: in
$SU(n)$, moreover $\sum k_j = 0$. *Hidden hypotheses:* that the geodesics from $I$ are the
$\exp(tA)$ (Lemma 21.2, V12.15) and the spectral theorem. *Proof:* Mathlib's spectral theorem for the
Hermitian matrix $iA$, and V14.1.

**V14.15 (the distance from $I$ to $-I$ and the minimal geodesics; `Morse.norm_conj_suDiag_sq`,
`Morse.pathLength_exp_smul`, `Morse.pi_sqrt_card_le_norm`, `Morse.kHalf`,
`Morse.riemDist_one_neg_one`, `Morse.sq_conj_suDiag_iff`, `Morse.isMinimalGeodesic_exp_iff`).** For
skew-Hermitian $A$, the length of $t \mapsto \exp(tA)$ on $[0, 1]$ is $\|A\|$, and for
$A = T\operatorname{diag}(i\pi k_j)T^*$ this is $\pi(\sum k_j^2)^{1/2} \ge \pi\sqrt n$ (odd $k_j$).
In $SU(2m)$, $m \ge 1$, the distance $\rho(I, -I)$ is $\pi\sqrt{2m}$; for $A \in \mathfrak{su}(2m)$ with
$\exp A = -I$, the geodesic $t \mapsto \exp(tA)$ is minimal (V7.24) iff $A^2 = -\pi^2I$, iff all
$k_j = \pm1$. *Book:* p. 127: the geodesic has length $|A| = \pi(k_1^2 + \dots + k_n^2)^{1/2}$, and it
is minimal iff every $k_j = \pm1$. *Hidden hypotheses:* that a minimal geodesic exists (Hopf–Rinow,
V7.26, in the compact $SU(2m)$) and that every geodesic from $I$ is an $\exp(tA)$ (V12.15), without
which "length $\pi\sqrt n$" would not imply "minimal". *Deviation (narrower):* for $SU(2m)$, the case
used; $U(n)$ is not treated.

**V14.16 (Lemma 23.1 for the initial velocities; `Morse.minVel`, `Morse.grassmannian`,
`Morse.exp_eq_neg_one_of_sq`, `Morse.mem_minVel_iff`, `Morse.lemma_23_1`).** Let $|\iota| = 2m$ and
$\operatorname{minVel} = \{A \in \mathfrak{su}(2m) : A^2 = -\pi^2I\}$. Then $A \in \operatorname{minVel}$
iff $A \in \mathfrak{su}(2m)$, $\exp A = -I$ and $t \mapsto \exp(tA)$ is a minimal geodesic; and
$A \mapsto \tfrac12(I - \tfrac i\pi A)$ is a homeomorphism of $\operatorname{minVel}$ onto
$G_m(\mathbb C^{2m})$, with inverse $P \mapsto i\pi(2P - I)$. *Book:* p. 128, Lemma 23.1: the space of
minimal geodesics from $I$ to $-I$ in $SU(2m)$ is homeomorphic to $G_m(\mathbb C^{2m})$; p. 127: a
minimal $A$ is completely determined by $\operatorname{Eigen}(i\pi)$. *Hidden hypotheses:* the
topology (Milnor matches the spaces only as sets, `Exposition/Findings.md`). *Deviation (restated):*
the space of minimal geodesics is represented here by their initial velocities; the path space is
V14.17. $G_m$ is a set of projections.

**V14.17 (Lemma 23.1 in the path space; `Morse.exp_half_smul_of_mem_minVel`,
`Morse.pi_sq_le_energy`, `Morse.expPath`, `Morse.expPath_mem_minPaths`,
`Morse.exists_minVel_of_mem_minPaths`, `Morse.continuous_expPath`, `Morse.minVelToPaths`,
`Morse.pathsToMinVel`, `Morse.minPathsHomotopyEquiv`, `Morse.minVelHomeomorph`).** Let $|\iota| = 2m$.
Every path from $I$ to $-I$ in $SU(2m)$ has energy $\ge 2m\pi^2$; for $A \in \operatorname{minVel}$,
$t \mapsto \exp(tA)$ lies in $\Omega^d$ and $\exp(A/2) = A/\pi$; every $\gamma \in \Omega^d$ agrees on
$[0, 1]$ with such a path, with $A = \pi\gamma(\tfrac12)$. The map $A \mapsto (t \mapsto \exp tA)$ is
continuous for Milnor's metric, and it is a homotopy equivalence $\operatorname{minVel} \simeq
\Omega^d$, with homotopy inverse $\gamma \mapsto \pi\gamma(\tfrac12)$, and a homeomorphism of
$\operatorname{minVel}$ onto the separation quotient of $\Omega^d$. *Book:* p. 128, Lemma 23.1 (as
above). *Hidden hypotheses:* the continuity for Milnor's metric (the exposition's Lemma 2.3).
*Deviation (restated):* "homeomorphic" holds only after identifying paths that agree on $[0, 1]$, as
for the sphere (V13.6); the homotopy equivalence is what the homotopy groups use. With V14.16 this
is Milnor's $\Omega^d \cong G_m(\mathbb C^{2m})$.

**V14.18 (Theorem 20.5 for $SU(n)$; `Morse.jacSin`, `Morse.hadSin`, `Morse.diagI`,
`Morse.jacK_diagI_apply`, `Morse.suSol`, `Morse.suSol_ode`, `Morse.suJac`, `Morse.isJacobiField_suJac`,
`Morse.covAlong_suJac_zero`, `Morse.suJac_eq_zero_iff`, `Morse.hadKer`, `Morse.conjMultiplicity_su`,
`Morse.finrank_hadKer`).** Let $a \in \mathbb R^n$, $T$ unitary, $A = T\operatorname{diag}(ia_j)T^*
\in \mathfrak{su}(n)$, $s_b(t) = \sin(bt)/b$ ($= t$ for $b = 0$), and $S(t) \odot W$ the matrix with
entries $s_{(a_j - a_l)/2}(t)w_{jl}$. For $C \in \mathfrak{su}(n)$, $J_C(t) = e^{tA/2}\,T(S(t) \odot
T^*CT)T^*\,e^{tA/2}$ is a Jacobi field along $t \mapsto \exp(tA)$ with $J_C(0) = 0$ and
$\frac{DJ_C}{dt}(0) = C$. The multiplicity (V9.4) of $t_0 \in [0, 1]$ as a parameter conjugate to $0$
is $\dim\{W \in \mathfrak{su}(n) : S(t_0) \odot W = 0\}$; for $a = \pi k$, $k$ integers, and
$0 < t_0 < 1$ this dimension is the multiplicity of $t_0$ computed from Milnor's spectrum (V14.8,
V14.9): twice the number of pairs $k_j > k_l$ such that $t_0$ is a conjugate parameter of
$\tfrac{\pi^2}4(k_j - k_l)^2$. *Book:* p. 110, Theorem 20.5, applied on p. 130 to $K_A(W) =
\tfrac14[[A, W], A]$; p. 131, "adding over all $j, l$". *Hidden hypotheses:* the multiplicity of a
conjugate point is the dimension of a space of Jacobi fields, so all Jacobi fields vanishing at $0$
must be described; Milnor does so in a parallel eigenframe. *Deviation (restated):* for $SU(n)$
only, without an eigenbasis (V14.6): the Jacobi equation is solved entrywise in the frame of V12.18,
and the reduction to diagonal $A$ is replaced by carrying $T$ through the computation.

**V14.19 (the index formula in $SU(n)$; `Morse.formIndex_su_geodesic`,
`Morse.index_su_eq_bottIndex`).** For integers $k_j$ with $\sum k_j = 0$, $T$ unitary and
$A = T\operatorname{diag}(i\pi k_j)T^*$ such that $t \mapsto \exp(tA)$ is a path from $I$ to $-I$,
the index of $E_{**}$ at this geodesic is the index of Milnor's spectrum (V14.8). Hence every
geodesic $t \mapsto \exp(tA)$ from $I$ to $-I$ in $SU(n)$ has index
$\operatorname{bott}(k) = \sum_{k_i > k_j}(k_i - k_j - 2)$, for the odd $k_j$ of V14.14. *Book:*
p. 131: by the Index Theorem the index of $t \mapsto \exp tA$, $0 \le t \le 1$, is
$\sum_{k_j > k_l}(k_j - k_l - 2)$. *Hidden hypotheses:* as in V14.7–V14.9 and V14.18. *Proof:* the
Index Theorem (V9.24) and V14.18, with V14.9.

**V14.20 (Lemma 23.2 for the geodesics of $SU(2m)$; `Morse.lemma_23_2_index`,
`Morse.energy_exp_smul`, `Morse.le_formIndex_of_not_minimal_su`).** Let $|\iota| = 2m$. A geodesic
$t \mapsto \exp(tA)$ from $I$ to $-I$ in $SU(2m)$ has index $0$ if all $k_j = \pm1$ (a minimal
geodesic) and index $\ge 2m + 2$ otherwise. Every geodesic in $\Omega(SU(2m); I, -I)$ that is not of
least energy has index $\ge 2m + 2$: the index hypothesis of Theorem 22.1 (V13.2) with
$\lambda_0 = 2m + 2$. *Book:* p. 128, Lemma 23.2: every non-minimal geodesic from $I$ to $-I$ in
$SU(2m)$ has index $\ge 2m + 2$; proof pp. 130–132. *Hidden hypotheses:* "non-minimal" in Theorem
22.1 is "not of least energy"; a geodesic with all $k_j = \pm1$ has least energy
($E = \|A\|^2 = L^2 \le L(\omega)^2 \le E(\omega)$, V8.5). *Proof:* V14.11 applied to V14.19, with
V14.14 and V14.15.

**V14.21 (the neighbourhood retraction for $SU(2m)$, and Corollary 22.2 for $SU(2m)$;
`Morse.specProj`, `Morse.continuousOn_specProj`, `Morse.hermOf`, `Morse.minProj`, `Morse.minNbhd`,
`Morse.retrPath`, `Morse.exists_retraction_minPaths_su`, `Morse.corollary_22_2_su`,
`Morse.corollary_22_2_su'`, `Morse.corollary_22_2_su_mulEquiv`).** Let $|\iota| = 2m$. For Hermitian
$H$ let $Q(H)$ be the spectral projection onto the eigenvalues $> \tfrac12$; it depends continuously
on $H$ where $\tfrac12$ is not an eigenvalue. The set $O$ of paths $\omega \in \Omega$ such that
$\tfrac12$ is not an eigenvalue of $H(\omega)$, the Hermitian part of $\tfrac12(I - i\omega(\tfrac12))$,
and $|\operatorname{tr}Q(H(\omega)) - m| < \tfrac12$, is open and contains $\Omega^d$, and
$\omega \mapsto (t \mapsto \exp(t\,i\pi(2Q(H(\omega)) - I)))$, changed to the identity on $\Omega^d$, is
a retraction of $O$ onto $\Omega^d$. Hence (V13.4, V13.5, V14.20) for every $\gamma \in \Omega^d$,
$\pi_i(\Omega^d, \gamma) \cong \pi_{i+1}(SU(2m), I)$ for $i \le 2m$, as groups for $1 \le i \le 2m$.
*Book:* p. 128: by Lemma 23.1 $\Omega^d$ is a manifold, so Theorem 22.1 applies. *Deviation (not in
the book):* the retraction that Hanner's theorem would give is constructed, so the result does not
depend on the hypothesis of V13.2; the trace is locally constant on projections, which keeps the
rank $m$.

**V14.22 (Theorem 23.3; `Morse.theorem_23_3`, `Morse.theorem_23_3_mulEquiv`).** Let $|\iota| = 2m$.
For every $P \in G_m(\mathbb C^{2m})$ and $i \le 2m$ there is a bijection
$\pi_i(G_m(\mathbb C^{2m}), P) \cong \pi_{i+1}(SU(2m), I)$, a group isomorphism for $1 \le i \le 2m$.
*Book:* p. 128, Theorem 23.3 (Bott): the inclusion $G_m(\mathbb C^{2m}) \to \Omega(SU(2m); I, -I)$
induces isomorphisms of homotopy groups in dimensions $\le 2m$; hence $\pi_iG_m(\mathbb C^{2m}) \cong
\pi_{i+1}SU(2m)$ for $0 \le i \le 2m$. *Hidden hypotheses:* the base points (as in V13.4); $i = 0$
(pointed sets). *Deviation (restated):* the statement about the inclusion is V13.3 applied with
V14.20–V14.21 (for $\Omega^d$, identified with $G_m$ by V14.16–V14.17); the isomorphism is the
composite of V14.16, V14.17 and V14.21, a bijection, and a group isomorphism for $i \ge 1$.

**V14.23 (local triviality from orbit sections; the Stiefel bundles; `Morse.Homotopy.orbitTriv`,
`Morse.Homotopy.exists_triv_of_orbitSection`, `Morse.Homotopy.Stiefel`, `Morse.Homotopy.secMat`,
`Morse.Homotopy.secMat_mem_unitaryGroup`, `Morse.Homotopy.secMat_mul_baseFrame`,
`Morse.Homotopy.exists_unitary_smul_baseFrame`, `Morse.Homotopy.stiefelRestrict_locallyTrivial`,
`Morse.Homotopy.unitaryOrbit_locallyTrivial`, `Morse.Homotopy.stiefelSphere`,
`Morse.Homotopy.isLocallyTrivial_sphereOrbit`).** (i) If a topological group $G$ acts continuously
on $E$ and $B$, $p : E \to B$ is continuous and equivariant, $G$ acts transitively on $B$, and the
orbit map $g \mapsto gb_0$ has a continuous section over a neighbourhood of $b_0$, then $p$ is
locally trivial with fibre $p^{-1}(b_0)$. (ii) $U(n)$ acts transitively on $V_k(\mathbb K^n)$, and
near the base frame $F_0$ (the last $k$ standard vectors) an explicit unitary matrix $s(F)$ with
$s(F)F_0 = F$ depends continuously on $F$. (iii) Restricting a frame to its last vectors,
$V_{k + l}(\mathbb K^n) \to V_l(\mathbb K^n)$, is locally trivial with fibre $V_k(\mathbb K^{n - l})$,
and $g \mapsto gF_0$, $U(n) \to V_k(\mathbb K^n)$, is locally trivial with fibre $U(n - k)$, embedded
as $S \mapsto \operatorname{diag}(S, I)$. $V_1(\mathbb K^n)$ is the unit sphere, so $U(m + 1) \to
S^{2m+1}$ is locally trivial with fibre $U(m)$. *Book:* pp. 128–129: $U(m + 1)/U(m) \cong S^{2m+1}$,
the complex Stiefel manifold $U(2m)/U(m)$, and the fibrations $U(m) \to U(m + 1) \to S^{2m+1}$,
$U(m) \to U(2m) \to U(2m)/U(m)$, quoted from Steenrod. *Hidden hypotheses:* the bundle structure of
a coset map (local sections). *Deviation (restated):* concrete spaces of matrices instead of coset
spaces; the local section is written down.

**V14.24 (the Grassmannian bundle; `Morse.Homotopy.Grassmannian`,
`Morse.Homotopy.eq_of_mul_eq_of_trace_eq`, `Morse.Homotopy.frameSpan`,
`Morse.Homotopy.exists_frame_of_mem_grassmannian`, `Morse.Homotopy.gsFrame`,
`Morse.Homotopy.continuousAt_gsFrame`, `Morse.Homotopy.exists_unitary_smul_grassBase`,
`Morse.Homotopy.frameSpan_locallyTrivial`, `Morse.Homotopy.grassmannian_eq_Grassmannian`).** Every
$P \in G_m(\mathbb K^n)$ is $FF^*$ for an orthonormal $m$-frame $F$; $F \mapsto FF^*$,
$V_m(\mathbb K^n) \to G_m(\mathbb K^n)$, is continuous, equivariant under $U(n)$ acting on
$G_m$ by $P \mapsto gPg^*$, transitively, and locally trivial with fibre $U(m)$. Near the base point
the section is the Gram–Schmidt process applied to the columns of $PF_0$, which is continuous at
independent families. The Grassmannian of Lemma 23.1 (V14.16) is this one. *Book:* p. 129:
$G_m(\mathbb C^{2m})$ "can be identified with" $U(2m)/U(m) \times U(m)$, and there is a fibration
$U(m) \to U(2m)/U(m) \to G_m(\mathbb C^{2m})$. *Hidden hypotheses:* as in V14.23. *Deviation
(restated):* $G_m$ as projections, the bundle as the frame-to-span map. *Proof:* two Hermitian
projections with $PQ = Q$ and equal traces are equal.

**V14.25 (Lemma 23.4: connectivity of Stiefel manifolds and stability; `Morse.Homotopy.SphereConnected`,
`Morse.Homotopy.sphereConnected_complex`, `Morse.Homotopy.subsingleton_pi_stiefel`,
`Morse.Homotopy.subsingleton_pi_stiefel_complex`, `Morse.Homotopy.unitaryInclC`,
`Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl`,
`Morse.Homotopy.bijective_homotopyGroupMap_unitaryIncl_complex`,
`Morse.Homotopy.surjective_homotopyGroupMap_unitaryIncl_complex`).** $\pi_iS^{2n - 1} = 0$ for
$i < 2n - 1$, at every base point. Hence $\pi_iV_k(\mathbb C^n) = 0$ for $k \le n$ and
$i \le 2(n - k)$; and the inclusion $U(m) \to U(m + k)$, $S \mapsto \operatorname{diag}(S, I_k)$,
induces bijections on $\pi_i$ for $i < 2m$ and surjections for $i \le 2m$, at every base point. (The
same holds over $\mathbb R$ with the bounds of $S^{n-1}$, Chapter 15.) *Book:* pp. 128–129, Lemma 23.4
and its proof: $\pi_{i-1}U(m) \cong \pi_{i-1}U(m + 1) \cong \cdots$ for $i \le 2m$, by the
inclusions; $\pi_{2m}U(m) \to \pi_{2m}U(m + 1)$ is onto; $\pi_i(U(2m)/U(m)) = 0$ for $i \le 2m$.
*Hidden hypotheses:* $\pi_iS^N = 0$ for $i < N$ (Part XII, quoted by Milnor). *Deviation
(stronger):* every $V_k(\mathbb C^n)$, by induction on $k$ through the restriction bundles, instead
of Milnor's exact-sequence argument for $V_m(\mathbb C^{2m})$ alone.

**V14.26 (Lemma 23.4: $\pi_iG_m(\mathbb C^{2m}) \cong \pi_{i-1}U(m)$;
`Morse.Homotopy.grassmannianEquiv`, `Morse.Homotopy.grassmannianEquiv_complex`,
`Morse.Homotopy.nonempty_mulEquiv_grassmannian_complex`, `Morse.Homotopy.grassmannianPiEquiv`,
`Morse.Homotopy.nonempty_mulEquiv_grassmannianPi`, `Morse.Homotopy.minVelPiEquiv`,
`Morse.Homotopy.nonempty_mulEquiv_minVelPi`).** For $1 \le i \le 2m$ and every
$P \in G_m(\mathbb C^{2m})$ there is a bijection $\pi_i(G_m(\mathbb C^{2m}), P) \cong
\pi_{i-1}(U(m), I)$, a group isomorphism for $2 \le i \le 2m$; the same for the space
$\operatorname{minVel}$ of V14.16. *Book:* p. 129, Lemma 23.4: $\pi_iG_m(\mathbb C^{2m}) \cong
\pi_{i-1}U(m)$ for $1 \le i \le 2m$. *Hidden hypotheses:* base points; $\pi_0$ is not a group.
*Deviation (restated):* for $i = 1$ a bijection of pointed sets ($\pi_1G_m$ and $\pi_0U(m)$ are both
trivial, which is not separately stated). *Proof:* the boundary map of the exact sequence of
$U(m) \to V_m(\mathbb C^{2m}) \to G_m$, whose total space is $2m$-connected (V14.25), moved to any
$P$ by a unitary motion.

**V14.27 (Lemma 23.4: $SU(n)$ and $U(n)$; `Morse.Homotopy.detCircle`, `Morse.Homotopy.diagCircle`,
`Morse.Homotopy.unitaryProd`, `Morse.Homotopy.isLocallyTrivial_detCircle`,
`Morse.Homotopy.subsingleton_pi_circle`, `Morse.Homotopy.suInclC`,
`Morse.Homotopy.bijective_homotopyGroupMap_suInclC`).** $g \mapsto (\det g, gD(\det g)^{-1})$, with
$D(z) = \operatorname{diag}(z, 1, \dots, 1)$, is a homeomorphism $U(n) \cong S^1 \times SU(n)$;
$\pi_jS^1 = 0$ for $j \ge 2$; and the inclusion $SU(n) \to U(n)$ ($n \ge 1$) induces bijections on
$\pi_j$, $j \ge 2$, at every point of $SU(n)$. *Book:* p. 129, Lemma 23.4, last clause:
$\pi_jU(m) \cong \pi_jSU(m)$ for $j \ne 1$ (from $SU(m) \to U(m) \to S^1$). *Deviation
(narrower):* $j = 0$ (both groups connected) is not formalized; it is not used.

**V14.28 (Milnor's chain and the periodicity theorem; `Morse.nonempty_equiv_pi_unitary_two_mul`,
`Morse.periodicity_theorem`, `Morse.nonempty_mulEquiv_pi_unitary_two_mul`,
`Morse.periodicity_theorem_mulEquiv`).** For $1 \le i \le 2m$, $\pi_{i-1}(U(m), I) \cong
\pi_{i+1}(U(2m), I)$, as groups for $2 \le i \le 2m$. For $1 \le i \le 2m - 2$,
$\pi_{i-1}(U(m), I) \cong \pi_{i+1}(U(m), I)$, as groups for $2 \le i \le 2m - 2$. *Book:* p. 129:
$\pi_{i-1}U = \pi_{i-1}U(m) \cong \pi_iG_m(\mathbb C^{2m}) \cong \pi_{i+1}SU(2m) \cong
\pi_{i+1}U(2m) = \pi_{i+1}U$ (Lemma 23.4, Theorem 23.3, Lemma 23.4), the periodicity theorem
$\pi_{i-1}U \cong \pi_{i+1}U$. *Hidden hypotheses:* the stable groups $\pi_jU$ are the $\pi_jU(m)$
for $2m - 1 \ge j$ (the exposition's definition); the chain's base points. *Deviation (restated):*
no stable group $\pi_jU$ is defined; periodicity is stated inside one $U(m)$, which needs
$i + 1 < 2m$ for stability back from $U(2m)$, hence the range $i \le 2m - 2$; for $i = 1$ a bijection
of pointed sets. Every stable group is reached for $m$ large.

**V14.29 (Theorem 23.5; `Morse.Homotopy.zerothHomotopyEquivOfDiscrete`,
`Morse.Homotopy.nonempty_pi_one_circle_equiv_int`, `Morse.Homotopy.unitaryOneHomeomorph`,
`Morse.Homotopy.nonempty_pi_unitary_equiv_circle`, `Morse.theorem_23_5`).** For $j \le 2m - 1$:
$\pi_j(U(m), I)$ is trivial if $j$ is even, and in bijection with $\mathbb Z$ if $j$ is odd. On the
way: $\pi_1(S^1) \cong \mathbb Z$ as sets, by the boundary map of the covering
$\mathbb Z \to \mathbb R \to S^1$; $\det : U(1) \to S^1$ is a homeomorphism; and
$\pi_iU(m) \cong \pi_iS^1$ for $i \le 1$, $m \ge 1$. *Book:* p. 130, Theorem 23.5 (Bott): the stable
groups $\pi_0U \cong \pi_2U \cong \cdots$ are zero and $\pi_1U \cong \pi_3U \cong \cdots$ are infinite
cyclic. *Hidden hypotheses:* $\pi_1S^1 \cong \mathbb Z$ (quoted); the stable range as in V14.28.
*Deviation (restated):* in the stable range of $U(m)$, not for a limit group; for odd $j$ a
bijection here, a group isomorphism in V14.30.

**V14.30 (Theorem 23.5 as groups; `Morse.Homotopy.piOneCircleMulEquiv`,
`Morse.Homotopy.piMulEquivOfHomeomorph`, `Morse.Homotopy.nonempty_mulEquiv_pi_one_unitary_circle`,
`Morse.nonempty_mulEquiv_pi_unitary_odd`, `Morse.nonempty_mulEquiv_pi_unitary_even`,
`Morse.theorem_23_5_mulEquiv`).** $\pi_1(S^1, 1) \cong \mathbb Z$ as groups. For $2k + 2 \le 2m$,
$\pi_{2k+1}(U(m), I) \cong \mathbb Z$ as groups; in the stable range $\pi_jU(m) \cong \pi_1U(m)$ for
odd $j$ and $\pi_jU(m) \cong \pi_2U(m)$ for even $j \ge 2$, as groups. *Book:* p. 130, Theorem 23.5.
*Hidden hypotheses:* as in V14.29. *Deviation (not in the book):* $\pi_1S^1 \cong \mathbb Z$ is
proved, through Mathlib's covering-space theory (the monodromy of $t \mapsto e^{it}$, whose deck group
$2\pi\mathbb Z$ is abelian) and Mathlib's identification of $\pi_1$ with the fundamental group.

### What is not verified in this chapter

- **The reduction to diagonal form by an isometry** (pp. 126–127, 130): that conjugation by
  $T \in U(n)$ is an isometry preserving conjugate points and indices. Not needed: $T$ is carried
  through the computation (V14.14, V14.18).
- **The linear independence of Milnor's eigenvectors** (V14.6); the formal index computation needs no
  eigenbasis.
- **$U(n)$ beyond what $SU(2m)$ needs** (p. 127): the distance $\pi\sqrt n$ in $U(n)$, its minimal
  geodesics as all subspaces of $\mathbb C^n$, the surjectivity of $\exp$, the connectedness of
  $U(n)$ and $SU(n)$; and that $\sum k_j$ is constant on the components of $\Omega(U(n); I, -I)$
  (V14.12).
- **$\pi_0$ in Lemma 23.4**: $\pi_0U(m) \cong \pi_0SU(m)$ (both connected) and the identification of
  $\pi_1G_m$ and $\pi_0U(m)$ as trivial.
- **The stable groups $\pi_iU$ as homotopy groups of a limit**, and the space form of Bott's theorem
  ($\Omega SU \simeq BU$, $\Omega U \simeq \mathbb Z \times BU$, the exposition's Corollary 23.6):
  colimit topologies and CW homotopy types are not formalized.
- **Lemma 23.1 as a homeomorphism of path spaces on the nose** (V14.17): paths are functions on
  $\mathbb R$, so only the separation quotient is homeomorphic to $G_m(\mathbb C^{2m})$.
- **The exposition's application** (§5, complex vector bundles over spheres).

---

## 16. Chapter 15 (Milnor §24): partly verified

Milnor's §24 (pp. 133–148) proves Bott periodicity for the orthogonal group. Complex structures on
$\mathbb R^n$ form $\Omega_1(n)$, the space of minimal geodesics from $I$ to $-I$ in $O(n)$ (Lemma
24.1); other geodesics have index at least $2m - 2$ in $O(2m)$ (Lemma 24.2), so
$\pi_i\Omega_1(n) \cong \pi_{i+1}O(n)$ for $i \le n - 4$ (Theorem 24.3). Iterating with
anticommuting complex structures $J_1, J_2, \dots$ gives a chain
$\Omega_k(n) \subset \dots \subset \Omega_1(n) \subset O(n)$ of compact, totally geodesic
submanifolds, each the space of minimal geodesics of the previous one (Lemma 24.4); in the limit
$\Omega_{k+1} \to \Omega\Omega_k$ is a homotopy equivalence (Theorem 24.5), and the identification
of $\Omega_8(16r)$ with $O(r)$ (Lemma 24.6) gives $\pi_iO \cong \pi_{i+8}O$ (Theorem 24.7). The
proof of 24.5 rests on minimal Clifford modules and Lemma 24.8 (Bott–Shapiro), with the dimensions
$m_k$, and Milnor remarks that these yield vector fields on spheres. What is verified first
(V15.1–V15.20) is the algebra: complex structures; $\Omega_k(n)$ as sets, with their inclusions and
compactness; the algebraic parts of Lemma 24.4 (the reflection, the "if" halves of Assertions 1 and
2, the decomposition $J' = J_kA$ and the semicircle through $J'$); Milnor's imbedding
$\Omega_k(n) \to \Omega_k(n + n')$; explicit anticommuting complex structures on $\mathbb R^{16r}$;
every product identity Milnor uses on pp. 139–143; the odd steps of Lemma 24.6 as bijections with
involutions, and its dimensions; the dimensions $m_k$ and Lemma 24.8 for $k \le 8$ (uniqueness up to
linear isomorphism); the orthonormal vector fields on spheres; and the index counts of Lemma 24.2
and of the proof of Theorem 24.5, from Milnor's spectra. Then the geometry and the topology
(V15.21–V15.46), for each $n$: the strata of $\Omega_k(n)$ (the sets on which Milnor's tangent space
has a fixed dimension) as compact totally geodesic submanifolds of the space of matrices, with both
halves of Assertions 1 and 2; Lemma 24.1 and the second half of Lemma 24.4, that is, the distance
$\pi\sqrt n$ from $J_k$ to $-J_k$, the minimal geodesics as the semicircles through the points of
$\Omega_{k+1}(n)$, and a homotopy equivalence of $\Omega_{k+1}(n)$ with the space $\Omega^d$ of
minimal paths (a homeomorphism after identifying paths that agree on $[0, 1]$); the neighbourhood
retraction that Theorem 22.1 (Chapter 13) assumes; the index bounds for the geodesics themselves
(Lemma 24.2 and Milnor's Assertions of pp. 146 and 148), obtained from Killing fields and the
project's Index Theorem instead of the curvature of $\Omega_k(n)$; Theorem 24.3; Theorem 24.5 for
each $n$ and $k \le 7$, as bijections of homotopy groups in a range that grows with $n$, class by
class for $k = 2, 6$, where the winding number of $\det_{\mathbb C}$ is shown to be an integer; the
compatibility with Milnor's stabilization; $\Omega_8(16r) \cong O(r)$ (Lemma 24.6 (8)); the
eight-step chain; and Theorem 24.7 in the stable range, $\pi_iO(n) \cong \pi_{i+8}O(n')$ for
$n \ge i + 2$ and $n' \ge i + 10$. Every isomorphism of V15.21–V15.46 is a bijection of pointed
sets. Not verified: the limit spaces $\Omega_k$ and $O$ and the homotopy equivalences of Theorems
24.5 and 24.7; the group structure along the chain; the table of $\pi_iO$ and $\pi_iSp$; the
identifications of $\Omega_1, \dots, \Omega_7$ with coset spaces and Grassmannians; the
symmetric-space structure; and the exact index of a geodesic. Lean: `Morse/Chapter15/` — for
V15.1–V15.18, `Relations.lean` (189 lines), `ComplexStructure.lean` (455), `Clifford.lean` (372),
`CliffordModules.lean` (595), `MinimalModules.lean` (643); Lemma 24.2 and the counts of the proof of
24.5 (V15.3, V15.19, V15.20) are in `Morse/Chapter14/IndexCount.lean`; for V15.21–V15.46,
`TotallyGeodesic.lean` (344), `OmegaManifold.lean` (554), `OmegaMinimal.lean` (611),
`OmegaRetract.lean` (298), `OmegaKilling.lean` (272), `OmegaIntertwiners.lean` (298),
`InvariantSplitting.lean` (181), `SplittingClifford.lean` (527), `SplittingData.lean` (275),
`IndexBound.lean` (270), `FiniteStage.lean` (257), `Winding.lean` (396), `OmegaWinding.lean` (188),
`OmegaComponents.lean` (488), `SplittingTwo.lean` (283), `SplittingTwoData.lean` (295),
`KillingTwo.lean` (291), `IndexBoundTwo.lean` (360), `FiniteStageTwo.lean` (178),
`Stabilization.lean` (193), `EightCommutant.lean` (211), `OmegaEight.lean` (324), `BottChain.lean`
(146), `StablePeriodicity.lean` (182), on top of Theorem 22.1 (Chapter 13) and the homotopy groups
of Chapter 14.

**Conventions.** Matrices are real $n \times n$ matrices indexed by a finite set, $O(n)$ is
Mathlib's orthogonal group, and $J_1, J_2, \dots$ is a fixed sequence of matrices (the index $0$ is
unused). For the abstract statements (V15.10, V15.12–V15.17) $V$ is a real vector space,
finite-dimensional where dimensions are counted, and the $J_\alpha$ are linear maps of $V$; no inner
product is used there. From V15.21 on, $M_n(\mathbb R)$ carries the inner product
$\langle A, B\rangle = \operatorname{tr}(AB^{\mathsf T})$, whose norm $\|A\|$ is the Frobenius norm,
and a submanifold $N$ of $M_n(\mathbb R)$ carries the induced metric, as in Chapters 6–11 and 14;
$\Omega(N; p, q)$ is the space of piecewise smooth paths with Milnor's metric (Chapter 10),
$\Omega^d$ the set of its paths of least energy (V13.1), and the index of a geodesic is that of
$E_{**}$ (Chapter 9). "An anticommuting family $J_1, \dots, J_k$" is as in V15.4; in statements
about $\Omega_k(n)$ it includes the base point $J_k \in \Omega_k(n)$, whose existence is Milnor's
standing assumption (p. 136), and $J_0 = I$ is the base point of $\Omega_0(n) = O(n)$. Homotopy
groups are Mathlib's $\pi_i$, $i \ge 0$, of a pointed space, and a bijection between them is one of
sets.

**V15.1 (complex structures; `Morse.IsComplexStructure`, `Morse.isComplexStructure_iff`,
`Morse.IsComplexStructure.even_card`, `Morse.IsComplexStructure.trace_transpose_mul_self`).** A
complex structure on $\mathbb R^n$ is a matrix $J \in O(n)$ with $J^2 = -I$. Equivalently,
$J^{\mathsf T} = -J$ and $J^2 = -I$. A complex structure exists only if $n$ is even, and every
complex structure has $\operatorname{tr}(J^{\mathsf T}J) = n$. *Book:* p. 133: the definition, after
"Now suppose that $n$ is even"; pp. 134–135, in the proof of Lemma 24.1: a skew $A$ with $A^2 = -I$
is a complex structure, and $JJ^* = I$, $JJ = -I$ give $J^* = -J$. *Hidden hypotheses:* none.
*Deviation (stronger):* the parity of $n$ is derived rather than assumed.

**V15.2 (the geodesic $t \mapsto \exp(\pi tJ)$; `Morse.exp_smul_of_mul_self_eq_neg_one`,
`Morse.exp_pi_smul`).** If $J^2 = -I$, then $\exp(\theta J) = \cos\theta\,I + \sin\theta\,J$ for
every real $\theta$; in particular $\exp(\pi J) = -I$. *Book:* pp. 134–135, proof of Lemma 24.1: in
a suitable basis $\exp(\pi A)$ is block diagonal with rotation blocks, and for a complex structure
$J$, $\exp\pi J = -I$. *Hidden hypotheses:* none. *Deviation (narrower):* only this matrix identity;
that $t \mapsto \exp(\pi tJ)$ is a minimal geodesic of $O(n)$, and Lemma 24.1 itself, are
V15.24–V15.26.

**V15.3 (Lemma 24.2; `Morse.bottIndexO`, `Morse.oSpectrum`, `Morse.spectralIndex_oSpectrum`,
`Morse.bottIndexO_eq_zero`, `Morse.bottIndexO_ge`).** For integers $a_1, \dots, a_m$ put
$\lambda(a) = \sum_{i < j}(a_i + a_j - 2) + \sum_{a_i > a_j}(a_i - a_j - 2)$, the second sum over
ordered pairs. Let all $a_j$ be odd and positive. (i) The index, in the sense of Chapter 14 (V14.8),
of the spectrum consisting of $\tfrac{\pi^2}{4}(a_i + a_j)^2$ for $i < j$ and
$\tfrac{\pi^2}{4}(a_i - a_j)^2$ for $a_i > a_j$, each counted twice, is $\lambda(a)$. (ii) If all
$a_j = 1$, $\lambda(a) = 0$. (iii) If not all $a_j = 1$, $\lambda(a) \ge 2m - 2$. *Book:* p. 135,
Lemma 24.2: any non-minimal geodesic from $I$ to $-I$ in $O(2m)$ has index $\ge 2m - 2$; in the
proof the geodesic is $t \mapsto \exp(\pi tA)$ with $A$ block diagonal with blocks
$a_j\begin{pmatrix}0 & 1\\ -1 & 0\end{pmatrix}$, $a_1 \ge \dots \ge a_m > 0$ odd; the non-zero
eigenvalues of $K_A = -\tfrac14(\operatorname{Ad}A)^2$ are $(a_i + a_j)^2/4$ for $i < j$ and
$(a_i - a_j)^2/4$ for $i < j$ with $a_i \neq a_j$, each counted twice, whence the formula for
$\lambda$, which vanishes for the minimal geodesic and is $\ge \sum_{j=2}^m(3 + 1 - 2) = 2m - 2$
otherwise. *Hidden hypotheses:* the conjugate points of $t \mapsto \exp(\pi tA)$ are governed by the
eigenvalues of $K_{\pi A} = \pi^2K_A$, the velocity being $\pi A$; Milnor's formula is the right one
for them. *Deviation (restated):* Milnor's spectrum is the input; its computation for block-diagonal
$A$, the reduction of a geodesic to that form, and Theorem 20.5 for $O(n)$ are not formalized. The
bound of Lemma 24.2 for the geodesics themselves is V15.30, proved without the spectrum.

**V15.4 (the spaces $\Omega_k(n)$; `Morse.Omega`, `Morse.omega_succ_subset`, `Morse.isClosed_omega`,
`Morse.isCompact_omega`, `Morse.IsAnticommFamily`, `Morse.IsAnticommFamily.mem_omega`).**
$\Omega_0(n) = O(n)$, and for $k \ge 1$, $\Omega_k(n)$ is the set of complex structures $J$ with
$J_\alpha J = -JJ_\alpha$ for $1 \le \alpha \le k - 1$. For any fixed matrices $J_\alpha$,
$\Omega_{k+1}(n) \subseteq \Omega_k(n)$, and every $\Omega_k(n)$ is closed and compact.
$J_1, \dots, J_k$ form an anticommuting family if each is a complex structure and
$J_\alpha J_\beta = -J_\beta J_\alpha$ for $\alpha \neq \beta$; then $J_k \in \Omega_k(n)$ for
$k \ge 1$. *Book:* p. 136: with fixed anticommuting complex structures $J_1, \dots, J_{k-1}$,
$\Omega_k(n)$ is the set of complex structures anticommuting with them;
$\Omega_k(n) \subset \dots \subset \Omega_1(n) \subset O(n)$; "Clearly each $\Omega_k(n)$ is a
compact set"; $\Omega_0(n) = O(n)$. *Hidden hypotheses:* none. *Deviation (stronger):* the
inclusions and the compactness hold for any fixed matrices $J_\alpha$.

**V15.5 (Lemma 24.4, the reflection; `Morse.reflection_mem_omega`).** For $k \ge 1$ and
$P, J' \in \Omega_k(n)$, $-PJ'P \in \Omega_k(n)$. Since $J'^{-1} = -J'$ for a complex structure,
$-PJ'P = PJ'^{-1}P$ is the image of $J'$ under $\sigma \mapsto P\sigma^{-1}P$, the reflection of
$O(n)$ in $P$ (Lemma 21.1). *Book:* p. 136: each component of $\Omega_k(n)$ is a symmetric space,
because the isometric reflection of $O(n)$ in a point of $\Omega_k(n)$ carries $\Omega_k(n)$ to
itself. *Hidden hypotheses:* none. *Deviation (narrower):* only the algebraic invariance; that the
reflection is an isometry and that the components of $\Omega_k(n)$ are symmetric spaces are not
formalized (the manifold structure is V15.23).

**V15.6 (Assertions 1 and 2 in the proof of Lemma 24.4, "if" halves;
`Morse.isComplexStructure_mul_exp`, `Morse.anticomm_mul_exp`).** If $J$ is a complex structure and
$A$ is skew with $AJ = -JA$, then $J\exp A$ is a complex structure. If $J_\alpha J = -JJ_\alpha$ and
$A$ commutes with $J_\alpha$, then $J_\alpha$ anticommutes with $J\exp A$. *Book:* p. 137, Assertion
1: $J\exp A$ is a complex structure iff $A$ anticommutes with $J$; Assertion 2: $J\exp A$
anticommutes with $J_1, \dots, J_{k-1}$ iff $A$ commutes with them; here $A$ is small and skew.
*Hidden hypotheses:* the "only if" halves need $A$ small (Milnor uses "Since $A$ is small").
*Deviation (stronger):* the "if" halves hold for every skew $A$ (for Assertion 2, for every $A$).
The "only if" halves, which need the injectivity of $\exp$ near $0$, are V15.22, and their
consequence that $\Omega_k(n)$ is a smooth totally geodesic submanifold is V15.23.

**V15.7 (Lemma 24.4, the step from $\Omega_k$ to $\Omega_{k+1}$, algebraically, and the Remark;
`Morse.omega_succ_decomp`, `Morse.mul_mem_omega_succ`, `Morse.semicircle_mem_omega`,
`Morse.mul_exp_eq_semicircle`, `Morse.trace_transpose_mul_eq_zero`).** Let $J_1, \dots, J_k$
($k \ge 1$) be an anticommuting family. (i) If $J' \in \Omega_{k+1}(n)$, then $A = -J_kJ'$
($= J_k^{-1}J'$) is a complex structure that anticommutes with $J_k$ and commutes with
$J_1, \dots, J_{k-1}$, and $J' = J_kA$. (ii) Conversely, for every such $A$,
$J_kA \in \Omega_{k+1}(n)$. (iii) For $J' \in \Omega_{k+1}(n)$ and every real $t$,
$\cos t\,J_k + \sin t\,J' \in \Omega_k(n)$, and $J_k\exp(tA) = \cos t\,J_k + \sin t\,J'$ for
$A = -J_kJ'$: the curve $t \mapsto J_k\exp(tA)$ stays in $\Omega_k(n)$, passes through $J'$ at
$t = \pi/2$ and reaches $-J_k$ at $t = \pi$. (iv) A complex structure $J'$ anticommuting with a
matrix $J$ satisfies $\operatorname{tr}(J'^{\mathsf T}J) = 0$. *Book:* pp. 137–138: choosing
$J_k \in \Omega_k(n)$ and a complex structure $J = J_kA$ anticommuting with $J_1, \dots, J_k$, $A$
is a complex structure anticommuting with $J_k$ and commuting with $J_1, \dots, J_{k-1}$, so
$t \mapsto J_k\exp(\pi tA)$ is a minimal geodesic from $J_k$ to $-J_k$ in $\Omega_k(n)$, and
conversely; Remark, p. 138: $J_kA$ is the midpoint $\gamma(\tfrac12)$. *Hidden hypotheses:* Milnor's
point $J_k$ is, in his later use, the next member of the fixed anticommuting family, as here, and
the lemma needs $\Omega_{k+1}(n) \neq \emptyset$. *Deviation (narrower):* (iii) concerns the curve
(Milnor's, reparametrized by $\pi t$), not geodesics: that it is a minimal geodesic of
$\Omega_k(n)$, and that every minimal geodesic from $J_k$ to $-J_k$ in $\Omega_k(n)$ arises so (the
homeomorphism with $\Omega_{k+1}(n)$), are V15.25–V15.26. *Deviation (not in the book):* (iv), the
orthogonality of $J'$ and $J$ for the trace inner product.

**V15.8 (Milnor's imbedding $\Omega_k(n) \to \Omega_k(n + n')$; `Morse.IsAnticommFamily.fromBlocks`,
`Morse.fromBlocks_mem_omega`).** If $J_1, \dots, J_k$ and $J'_1, \dots, J'_k$ are anticommuting
families on $\mathbb R^n$ and $\mathbb R^{n'}$, the block matrices $J_\alpha \oplus J'_\alpha$ form
an anticommuting family on $\mathbb R^n \oplus \mathbb R^{n'}$. For any fixed matrices and every
$k$: if $P \in \Omega_k(n)$ for the $J_\alpha$ and $P' \in \Omega_k(n')$ for the $J'_\alpha$, then
$P \oplus P' \in \Omega_k(n + n')$ for the $J_\alpha \oplus J'_\alpha$. With $P' = J'_k$ (V15.4)
this is Milnor's map $J \mapsto J \oplus J'_k$. *Book:* p. 138: choose anticommuting complex
structures $J'_1, \dots, J'_k$ on $\mathbb R^{n'}$; each $J \in \Omega_k(n)$ determines
$J \oplus J'_k$, which anticommutes with $J_\alpha \oplus J'_\alpha$. *Hidden hypotheses:*
$\mathbb R^{n'}$ must carry $k$ anticommuting complex structures, which the choice presupposes
(V15.9 supplies them for $n' = 16r'$, $k \le 8$). *Deviation (narrower):* the direct limit
$\Omega_k$ and its topology are not formalized; the compatibility of the imbedding with $\varphi$ is
V15.41.

**V15.9 (explicit anticommuting complex structures; `Morse.bott4`, `Morse.bott8`, `Morse.bott16`,
`Morse.isAnticommFamily_bott2`, `Morse.isAnticommFamily_bott4`, `Morse.isAnticommFamily_bott8`,
`Morse.isAnticommFamily_bott16`, `Morse.IsAnticommFamily.blockDiagonal`,
`Morse.IsAnticommFamily.reindex`, `Morse.isAnticommFamily_bott16r`).** With
$\sigma = \begin{pmatrix}0 & -1\\ 1 & 0\end{pmatrix}$,
$\tau = \begin{pmatrix}1 & 0\\ 0 & -1\end{pmatrix}$,
$\kappa = \begin{pmatrix}0 & 1\\ 1 & 0\end{pmatrix}$, explicit Kronecker products give one complex
structure on $\mathbb R^2$ ($\sigma$), three anticommuting ones on $\mathbb R^4$
($1 \otimes \sigma$, $\sigma \otimes \tau$, $\sigma \otimes \kappa$), seven on $\mathbb R^8$, and
eight on $\mathbb R^{16}$ (the seven tensored with $\tau$, and
$1 \otimes 1 \otimes 1 \otimes \sigma$). Renaming the coordinates and repeating block-diagonally
($J_\alpha \oplus \dots \oplus J_\alpha$) preserve anticommuting families; so $\mathbb R^{16r}$
carries eight anticommuting complex structures for every $r$. *Book:* p. 136: assume that $n$ is
divisible by a high power of $2$, and let $J_1, \dots, J_{k-1}$ be fixed anticommuting complex
structures; p. 139: it is convenient to set $n = 16r$. Milnor never writes the structures down.
*Hidden hypotheses:* their existence. *Deviation (not in the book):* explicit structures, which make
the standing assumptions of §24 non-vacuous for $n = 16r$ and $k \le 8$.

**V15.10 (products of anticommuting complex structures; `Morse.IsClifford`,
`Morse.IsAnticommFamily.isClifford`, `Morse.θ₃_spec`, `Morse.θ₃_anticommute`, `Morse.θ₅_spec`,
`Morse.θ₆_spec`, `Morse.θ₇_spec`, `Morse.J₃J₄_spec`, `Morse.J₇J₈_spec`, `Morse.ω₇_spec`).** In any
ring, call $J_1, \dots, J_k$ Clifford if $J_\alpha^2 = -1$ and
$J_\alpha J_\beta = -J_\beta J_\alpha$ for $\alpha \neq \beta$ ($1 \le \alpha, \beta \le k$); an
anticommuting family of matrices is Clifford. Put $\theta_3 = J_1J_2J_3$, $\theta_5 = J_1J_4J_5$,
$\theta_6 = J_2J_4J_6$, $\theta_7 = J_1J_6J_7$ and $\omega_7 = J_1J_2\cdots J_7$. Then, whenever $k$
is large enough for the indices involved: $\theta_3^2 = 1$, $\theta_3$ commutes with $J_1, J_2, J_3$
and anticommutes with $J_\alpha$ for $4 \le \alpha \le k$; $J_3J_4$ anticommutes with $\theta_3$ and
commutes with $J_1, J_2$; $\theta_5^2 = 1$, $\theta_5$ commutes with $J_1, J_4, J_5, \theta_3$ and
anticommutes with $J_2, J_3$; $\theta_6^2 = 1$, $\theta_6$ commutes with
$J_2, J_4, J_6, \theta_3, \theta_5$ and anticommutes with $J_1, J_3, J_5$; $\theta_7^2 = 1$,
$\theta_7$ commutes with $J_1, J_6, J_7, \theta_3, \theta_5, \theta_6$ and anticommutes with
$J_2, \dots, J_5$; $J_7J_8$ commutes with $\theta_3, \theta_5, \theta_6$ and anticommutes with
$\theta_7$; $\omega_7 = -\theta_3\theta_5\theta_7$, and it commutes with $J_1, \dots, J_7$. *Book:*
pp. 139–143, the facts on which Lemma 24.6 and the discussion of Lemma 24.8 run: $J_1J_2J_3$ has
square $+I$ and commutes with $J_1, J_2$ (p. 139); $J_3J_4$ anticommutes with $J_1J_2J_3$ and
commutes with $J_1, J_2$ (pp. 139–140); the corresponding statements for $J_1J_4J_5$ (p. 140),
$J_2J_4J_6$ (pp. 140–141), $J_1J_6J_7$ and $J_7J_8$ (p. 141); and, for $k = 7$, the two minimal
spaces distinguished by $J_7 = \pm J_1\cdots J_6$ (p. 143). *Hidden hypotheses:* none; Milnor states
these without computation. *Deviation (stronger):* the complete commutation table, in any ring.

**V15.11 (Lemma 24.6, the odd steps; `Morse.theta_of_mem_omega`, `Morse.mem_omega_of_theta`,
`Morse.mul_theta_mul`).** Let $J_1, \dots, J_k$ be an anticommuting family and $1 \le a < b \le k$.
For $J' \in \Omega_{k+1}(n)$, $\theta = J_aJ_bJ'$ is symmetric with $\theta^2 = I$, commutes with
$J_a$ and $J_b$, and anticommutes with every other $J_c$, $c \le k$. Conversely, for every such
$\theta$, $J' = J_bJ_a\theta$ lies in $\Omega_{k+1}(n)$ and $J_aJ_bJ' = \theta$; and
$J_bJ_a(J_aJ_bJ') = J'$ for every $J'$. So $J' \mapsto J_aJ_bJ'$ is a bijection of $\Omega_{k+1}(n)$
onto the symmetric involutions with this commutation pattern. With
$(a, b, k) = (1, 2, 2), (1, 4, 4), (2, 4, 5), (1, 6, 6)$ it is the passage $J_3 \mapsto \theta_3$,
$J_5 \mapsto \theta_5$, $J_6 \mapsto \theta_6$, $J_7 \mapsto \theta_7$ of 24.6 (3), (5), (6), (7).
*Book:* pp. 139–141, Lemma 24.6 (3), (5), (6), (7): $\Omega_3(16r)$ is the quaternionic Grassmannian
of $\mathbb H^{4r}$, through the $+1$-eigenspace $V_1$ of $J_1J_2J_3$; $\Omega_5(16r)$ the subspaces
$W \subset V_1$ closed under $J_1$ with $V_1 = W \oplus J_2W$; $\Omega_6(16r)$ the real subspaces
$X \subset W$ with $W = X \oplus J_1X$; $\Omega_7(16r)$ the real Grassmannian of
$X \cong \mathbb R^{2r}$. For (3) Milnor writes $J_3$ back in terms of $V_1$; for (5), (6), (7) he
asserts without proof that the subspace determines $J_5$, $J_6$, $J_7$ uniquely. *Hidden
hypotheses:* none; the uniqueness claims are the inverse maps $\theta \mapsto J_bJ_a\theta$.
*Deviation (narrower):* a symmetric involution is the same as its $+1$-eigenspace, but the passage
from involutions of $\mathbb R^{16r}$ to Milnor's subspaces of $V_1$, $W$, $X$, and the
identification with Grassmann manifolds as spaces, are not formalized. Of the even steps, (4),
$\Omega_4(16r) \cong Sp(2r)$ through $J_3J_4$, is covered only by V15.7 (i)–(ii), not as an
identification with a group; (8), $\Omega_8(16r) \cong O(r)$ through $J_7J_8$, is V15.42.

**V15.12 (Lemma 24.6, the dimensions; `Morse.eigV₁`, `Morse.eigW`, `Morse.eigX`, `Morse.jointEigen`,
`Morse.finrank_eq_two_mul_of_anticomm`, `Morse.finrank_chain`, `Morse.finrank_eq_sixteen_mul`,
`Morse.finrank_jointEigen_bott16r`).** On a finite-dimensional real vector space $V$, if
$\theta^2 = 1$ and an injective $P$ anticommutes with $\theta$, then $\dim V = 2\dim\{\theta = 1\}$
($P$ exchanges the $\pm1$-eigenspaces of $\theta$). Hence, for Clifford $J_1, \dots, J_8$ on $V$,
with $V_1 = \{\theta_3 = 1\}$, $W = V_1 \cap \{\theta_5 = 1\}$, $X = W \cap \{\theta_6 = 1\}$ and
$X_1 = X \cap \{\theta_7 = 1\}$: $\dim V = 2\dim V_1 = 4\dim W = 8\dim X = 16\dim X_1$, the halvings
being effected by $J_4$, $J_2$, $J_1$ and $J_7J_8$. For $\mathbb R^{16r}$ with the structures of
V15.9, $\dim V_1 = 8r$, $\dim W = 4r$, $\dim X = 2r$ and $\dim X_1 = r$. *Book:* pp. 139–141: the
splittings $V_1 \oplus V_2$, $W \oplus J_2W$, $X \oplus J_1X$, $X_1 \oplus X_2$; Milnor restricts to
the component of $\Omega_3(16r)$ with $\dim_{\mathbb H}V_1 = \dim_{\mathbb H}V_2 = 2r$ (p. 139) and
to the component of $\Omega_7(16r)$ with $\dim X_1 = \dim X_2 = r$ (p. 141), and writes
$X \cong \mathbb R^{2r}$. *Hidden hypotheses:* that each involution splits the space into halves of
equal dimension needs an invertible map anticommuting with it ($J_4$, $J_2$, $J_1$, $J_7J_8$), which
Milnor uses without comment. *Deviation (stronger):* the equal dimensions are forced as soon as the
later structures exist ($J_4$ for $V_1$, $J_8$ for $X_1$), which Milnor's later steps presuppose;
the restriction to components is then automatic.

**V15.13 (minimal spaces and the numbers $m_k$; `Morse.IsMinimalCliffordModule`, `Morse.milnorM`).**
A real vector space $V$ with linear maps $J_1, J_2, \dots$ is minimal for $J_1, \dots, J_k$ if
$V \neq 0$ and every subspace closed under $J_1, \dots, J_k$ is $0$ or $V$. The numbers $m_k$ are
defined by the table $m_0, \dots, m_8 = 1, 2, 4, 4, 8, 8, 8, 8, 16$ and $m_{k+8} = 16m_k$. *Book:*
p. 143: $V$ is a minimal $(J_1, \dots, J_k)$-space if no proper non-trivial subspace is closed under
$J_1, \dots, J_k$; two minimal spaces are isomorphic if there is an isometry between them commuting
with the $J_\alpha$; $m_k$ is the dimension of a minimal space, with the table "from the above
discussion", and $m_k = 16m_{k-8}$ for $k > 8$ "can be shown". *Hidden hypotheses:* $V \neq 0$.
*Deviation (restated):* $m_k$ is defined by the table; that it is the dimension of every minimal
space is V15.16, for $k \le 8$. For $k > 8$ the recursion is only a definition.

**V15.14 ($m_k$ divides the dimension, and is the least one; `Morse.two_dvd_finrank_of_sq`,
`Morse.four_dvd_finrank_of_anticomm`, `Morse.eight_dvd_finrank`, `Morse.milnorM_dvd_finrank`,
`Morse.milnorM_dvd_card`, `Morse.exists_isAnticommFamily_fin`, `Morse.isLeast_milnorM`).** On a real
vector space: one $J$ with $J^2 = -1$ makes the dimension even ($V$ is a $\mathbb C$-module); two
anticommuting ones make it divisible by $4$ ($V$ is an $\mathbb H$-module, through Mathlib's
quaternion algebra); four Clifford maps on a finite-dimensional $V$ make it divisible by $8$; and
for $k \le 8$, Clifford $J_1, \dots, J_k$ on a finite-dimensional $V$ force $m_k \mid \dim V$. For
matrices: if $\mathbb R^n$ carries $k \le 8$ anticommuting complex structures then $m_k \mid n$, and
$\mathbb R^{m_k}$ carries $k$ of them; so $m_k$ is the least positive $n$ for which $\mathbb R^n$
carries $k$ anticommuting complex structures. *Book:* p. 143: the values $m_0, \dots, m_8$, from the
description of the minimal spaces as lines over $\mathbb R$, $\mathbb C$, $\mathbb H$, and as $H$,
$H \oplus H'$, $L$, $L \oplus L'$. *Hidden hypotheses:* the halving of V15.12. *Deviation
(stronger):* divisibility for every space, not only for minimal ones, and explicit existence on
$\mathbb R^{m_k}$.

**V15.15 (the Clifford algebra; `Morse.cliffQ`, `Morse.cliffordLift`, `Morse.cliffordLift_ι`,
`Morse.finrank_cliffordAlgebra`, `Morse.finrank_le_two_pow`).** Let $C_k$ be Mathlib's Clifford
algebra of the quadratic form $Q(x) = -\sum x_i^2$ on $\mathbb R^k$. Clifford elements
$J_1, \dots, J_k$ of a real algebra $A$ determine an algebra homomorphism $C_k \to A$ sending the
$i$-th basis vector to $J_i$; $\dim C_k = 2^k$; and a minimal $(J_1, \dots, J_k)$-space has
dimension at most $2^k$, being the image of $C_k$ under $c \mapsto c\cdot u$ for any $u \neq 0$.
*Book:* p. 136, footnote: these structures make $\mathbb R^n$ a module over a suitable Clifford
algebra; the Clifford algebras are suppressed in the presentation. *Hidden hypotheses:* none.
*Deviation (not in the book, beyond the footnote):* the bound $2^k$ is the tool of V15.16; given the
splitting of $\mathbb R^n$ into minimal summands (not formalized), it alone gives what the proof of
24.5 needs from $m_{k+1}$ — that the number of summands, at least $n/2^{k+1}$, tends to infinity
with $n$.

**V15.16 (Lemma 24.8, the dimensions; `Morse.finrank_eq_milnorM_of_isMinimal`,
`Morse.isMinimal_of_finrank_eq_milnorM`, `Morse.milnorM_le_finrank_le`,
`Morse.finrank_eq_milnorM_of_le_two`, `Morse.central_involution`, `Morse.minimal_three`,
`Morse.minimal_seven`).** Let $k \le 8$ and let $J_1, \dots, J_k$ be Clifford on a
finite-dimensional real $V$. If $V$ is minimal, $\dim V = m_k$; conversely, if $\dim V = m_k$, $V$
is minimal; a minimal $V$ has $m_k \le \dim V \le 2^k$. An involution commuting with all $J_\alpha$
acts on a minimal space as $1$ or as $-1$; hence a minimal space for $k = 3$ (resp. $7$) is minimal
for $J_1, J_2$ (resp. $J_1, \dots, J_6$), the involution being $J_1J_2J_3$ (resp. $J_1\cdots J_7$).
*Book:* p. 143: the proof of 24.8 "follows that of 24.6": a minimal space is a line over
$\mathbb R$, $\mathbb C$, $\mathbb H$ for $k \le 2$; for $k = 3$ a quaternionic line, with
$J_3 = \pm J_1J_2$; $H \oplus H'$ for $k = 4, 5, 6$; for $k = 7$, $J_7 = \pm J_1\cdots J_6$;
$L \oplus L'$ for $k = 8$; for $k > 8$ the situation repeats more or less periodically, and
$k \le 8$ suffices. *Hidden hypotheses:* that $J_1J_2J_3$ and $J_1\cdots J_7$ act as $\pm1$ on a
minimal space, because they commute with every $J_\alpha$ and square to $1$ (Milnor states
$J_3 = \pm J_1J_2$ directly). *Deviation (narrower):* $k \le 8$. *Deviation (stronger):* no inner
product, and only the Clifford relations. *Proof:* replaces "follows that of 24.6": a minimal space
is the image of $C_k$ under $c \mapsto c\cdot u$, $u \neq 0$ (V15.15); taking $u$ a joint
$+1$-eigenvector of the available involutions $\theta$, it is the image of the subspace of $C_k$
fixed by right multiplication by the $\theta$'s, which has dimension $m_k$ for $k = 4, 5, 6, 8$ by
the halving of V15.12 applied to $C_k$ (all of $C_k$ for $k \le 2$); with $m_k \mid \dim V$ (V15.14)
this forces $\dim V = m_k$.

**V15.17 (Lemma 24.8, uniqueness; `Morse.exists_iso_of_isMinimal`, `Morse.cyclicMap`,
`Morse.range_cyclicMap_eq_top`, `Morse.minimal_of_fixed`, `Morse.exists_iso_of_equiv`).** Let
$k \le 8$ with $k \not\equiv 3 \pmod 4$, and let $V$, $V'$ be finite-dimensional real spaces with
Clifford $J_1, \dots, J_k$ and $J'_1, \dots, J'_k$, both minimal. Then there is a linear isomorphism
$T : V \to V'$ with $T(J_\alpha v) = J'_\alpha(Tv)$ for all $\alpha \le k$ and $v \in V$. *Book:* p.
143, Lemma 24.8 (Bott and Shapiro): for $k \not\equiv 3 \pmod 4$ any two minimal
$(J_1, \dots, J_k)$-spaces are isomorphic, by an isometry commuting with the $J_\alpha$. *Hidden
hypotheses:* a cyclic-vector argument (a minimal space is generated by one joint eigenvector), which
"follows that of 24.6" does not supply. *Deviation (narrower):* a linear isomorphism rather than an
isometry (for orthogonal $J_\alpha$ an isometry would follow by polar decomposition, which is not
formalized), and $k \le 8$. *Deviation (stronger):* no inner product is needed. *Proof:* both spaces
are isomorphic to the same fixed subspace of $C_k$ by orbit maps (V15.16), hence to each other.

**V15.18 (vector fields on spheres; `Morse.IsAnticommFamily.dotProduct_mulVec`,
`Morse.IsComplexStructure.dotProduct_mulVec_self`, `Morse.bott16r_vectorFields`).** If
$J_1, \dots, J_k$ are anticommuting complex structures on $\mathbb R^n$, then for every $u$,
$\langle J_\alpha u, J_\beta u\rangle = \delta_{\alpha\beta}|u|^2$ and
$\langle J_\alpha u, u\rangle = 0$; so for $|u| = 1$ the $J_\alpha u$ are $k$ orthonormal vectors
tangent to the unit sphere at $u$. This is written out for the eight structures of V15.9 on
$\mathbb R^{16r}$ (eight fields on $S^{16r-1}$), and the general statement applies to the
block-diagonal families on $\mathbb R^{4r}$ and $\mathbb R^{8r}$ built from V15.9 (three and seven
fields). *Book:* pp. 143–144, Remark: for anticommuting $J_1, \dots, J_k$ on a space of dimension
$rm_k$, the vectors $J_1u, \dots, J_ku$ are perpendicular to each other and to $u$, giving $k$
linearly independent vector fields on the $(rm_k - 1)$-sphere: $3$ on $S^{4r-1}$, $7$ on $S^{8r-1}$,
$8$ on $S^{16r-1}$ (Hurwitz–Radon; Adams showed these are best possible). *Hidden hypotheses:* none.
*Deviation (narrower):* the identities only (the fields are linear in $u$, hence continuous); the
general Hurwitz–Radon count and Adams's theorem are not formalized.

**V15.19 (the proof of Theorem 24.5 for $k \not\equiv 2 \pmod 4$: the index bound;
`Morse.card_lt_le_spectralIndex`, `Morse.card_sub_one_le_spectralIndex`).** The index of a spectrum
(in the sense of Chapter 14, V14.8) is at least the number of its eigenvalues greater than $\pi^2$.
Hence, for integers $a_1, \dots, a_s \ge 1$ with some $a_{h_0} \ge 3$, the $s - 1$ eigenvalues
$\tfrac{\pi^2}{4}(a_{h_0} + a_j)^2$, $j \neq h_0$, already have index at least $s - 1$. *Book:* pp.
144–146: $K_A$ has at least $s - 1$ eigenvalues $\ge (3 + 1)^2/4 = 4$, namely $(a_h + a_j)^2/4$
(Assertion, p. 145); each eigenvalue $e^2$ of $K_A$ gives conjugate points at
$t = e^{-1}, 2e^{-1}, \dots$, so $e^2 \ge 4$ gives an interior conjugate point; hence the index of a
non-minimal geodesic from $J$ to $-J$ in $\Omega_k(n)$ is at least $n/m_{k+1} - 1$ (Assertion, p.
146). *Hidden hypotheses:* as in V15.3, the conjugate points of $t \mapsto J\exp(\pi tA)$ come from
$K_{\pi A} = \pi^2K_A$, whose eigenvalues $\pi^2e^2$ are the ones used here (Milnor's $t = e^{-1}$
is the count for them). *Deviation (restated):* the eigenvalues are input; the formula for $K_A$ on
the tangent space of the totally geodesic $\Omega_k(n)$ is not formalized. The splitting of
$\mathbb R^n$ into minimal summands $M_h$ and the isomorphisms $M_h \to \bar M_j$ given by Lemma
24.8 are V15.29, and the resulting bound for the index of a geodesic is V15.30, proved through
Killing fields instead of the eigenvectors $B$. *Deviation (stronger):* oddness of the $a_j$ is not
needed.

**V15.20 (the proof of Theorem 24.5 for $k \equiv 2 \pmod 4$: the index bound on a component;
`Morse.card_sub_abs_sum_le_two_mul_bottIndex`,
`Morse.card_sub_abs_sum_le_four_mul_spectralIndex`).** Let $a_1, \dots, a_r$ be odd integers, some
$|a_h| \ge 3$, and $c = \sum_h a_h$. Then $\sum_{a_h > a_j}(a_h - a_j - 2) \ge (r - |c|)/2$;
equivalently, the index (V14.8) of the spectrum with one eigenvalue $\tfrac{\pi^2}{4}(a_h - a_j)^2$
for each pair $a_h > a_j$ is at least $(r - |c|)/4$. *Book:* pp. 147–148: on a component of
$\Omega\Omega_k(n)$, where $\operatorname{tr}A = icm_k/2$ is fixed, the $a_h$ are odd with
$\sum a_h = c$ and $\max|a_h| \ge 3$; the pairs $a_h > a_j$ give eigenvalues $(a_h - a_j)^2/4$ and
$2\lambda \ge \sum_{a_h > a_j}(a_h - a_j - 2)$; Milnor then treats, "for example", the case of some
$a_h$ equal to $-3$: with $p$ and $-q$ the sums of the positive and of the negative $a_h$,
$p - q = c$, $p + q \ge r$, and the displayed chain
$2\lambda \ge \sum(a_h - a_j - 2) > \sum_{a_h > 0}(a_h - (-3) - 3) = p$ gives
$4\lambda \ge 2p \ge r + c$, with $r = n/m_k \to \infty$. *Hidden hypotheses:* Milnor treats only
the example of an $a_h$ equal to $-3$; the strict inequality of his chain fails when no $a_h$ is
positive (for $a = (-1, -3)$ both sides are $0$), although his final bound still holds then.
*Deviation (value differs):* the formal bound is $4\lambda \ge r - |c|$, whichever sign the large
$|a_h|$ has; Milnor's $4\lambda \ge r + c$ is for his example, and some $a_h \ge 3$ gives the bound
with $r - c$ instead. Since $c$ is fixed on a component and $r \to \infty$, either suffices.
*Deviation (restated):* as in V15.19, the eigenvalues are input; the bound for the geodesics
themselves is V15.38.

**V15.21 (totally geodesic sets of orthogonal matrices; `Morse.isSliceSubmanifold_of_param`,
`Morse.IsTotGeo`, `Morse.IsTotGeo.tangentSubspace_eq`, `Morse.IsTotGeo.isGeodesicOn_mul_exp_smul`,
`Morse.IsTotGeo.eqOn_of_isUnbrokenGeodesic`, `Morse.IsTotGeo.exp_eq`,
`Morse.IsTotGeo.isGeodesicallyComplete`).** Let $N \subseteq M_n(\mathbb R)$ be a slice submanifold
consisting of orthogonal matrices, and for each $x \in N$ let $T_x$ be a space of skew matrices with
$\dim T_x = \dim N$, such that $x\exp A \in N$ and $A \in T_{x\exp A}$ whenever $A \in T_x$. Then:
(i) the tangent space of $N$ at $x$ is $x\,T_x$; (ii) for $A \in T_x$ the curve
$t \mapsto x\exp(tA)$ is a geodesic of $N$ on all of $\mathbb R$; (iii) every unbroken geodesic
$\gamma \in \Omega(N; p, q)$ agrees on $[0, 1]$ with $s \mapsto p\exp(sV)$ for some $V \in T_p$;
(iv) the Riemannian exponential of $N$ is $\exp_x(xA) = x\exp A$ for $A \in T_x$, and $N$ is
geodesically complete. Also, as a tool for V15.23: let $S$ be a subset of a real normed space $V$
such that near each $x \in S$ there is a smooth $\Phi : Z \times W \to V$ ($Z$, $W$
finite-dimensional) with $\Phi(0) = x$ and invertible derivative at $0$, for which, near $0$, the
points $\Phi(z, 0)$ lie in $S$ and every point $\Phi(q) \in S$ equals $\Phi(g(q), 0)$ with
$g(q) \to 0$ as $q \to 0$; then $S$ is a slice submanifold modelled on $Z$. *Book:* p. 136,
footnote: a submanifold is totally geodesic if each of its geodesics is a geodesic of the larger
manifold; p. 137: the description of $\Omega_k(n)$ near $J$ "clearly implies" that it is a totally
geodesic submanifold of $O(n)$. *Hidden hypotheses:* "clearly" needs an argument (the exposition's
Lemma 2.2). *Deviation (restated):* "totally geodesic" is not used as a definition, and the
geodesics of $N$ are not compared with those of $O(n)$; what Milnor draws from it, the list
(ii)–(iii) of the geodesics of $N$, is proved directly. *Proof:* the acceleration of
$t \mapsto x\exp(tA)$ is $yA^2$, $y = x\exp(tA)$; $A^2$ is symmetric, hence $yA^2$ is orthogonal to
the tangent space $y\,T_y$, which consists of $y$ times skew matrices; so the curve is a geodesic of
the submanifold $N$, and (iii) follows by the uniqueness of geodesics.

**V15.22 (the space $\mathcal T_J$, and Assertions 1 and 2 in both directions; `Morse.tanAlg`,
`Morse.mem_tanAlg`, `Morse.tanAlg_zero`, `Morse.mul_exp_mem_omega`, `Morse.mem_tanAlg_mul_exp`,
`Morse.exists_exp_injective`, `Morse.mem_tanAlg_of_mul_exp_mem`, `Morse.exists_local_log`).** For a
matrix $x$ let $\mathcal T_x$ be the space of skew matrices $A$ with $Ax = -xA$ and
$AJ_\alpha = J_\alpha A$ for $1 \le \alpha \le k - 1$; for $k = 0$ the first condition is dropped,
so that $\mathcal T_x$ is the space $\mathfrak o(n)$ of all skew matrices, the same for every $x$.
(i) For any fixed matrices $J_\alpha$: if $x \in \Omega_k(n)$ and $A \in \mathcal T_x$, then
$x\exp A \in \Omega_k(n)$ and $A \in \mathcal T_{x\exp A}$. (ii) There is $\varepsilon > 0$ such
that $\exp$ is injective on the matrices of norm $< \varepsilon$. For every such $\varepsilon$,
every anticommuting family $J_1, \dots, J_k$, every $x \in \Omega_k(n)$ and every matrix $C$ with
$\|C\| < \varepsilon$: if $x\exp C \in \Omega_k(n)$, then $C \in \mathcal T_x$. (iii) Hence, for an
anticommuting family and $x \in \Omega_k(n)$, there is a map $L$ with $L(y) \to 0$ as $y \to x$,
such that every $y \in \Omega_k(n)$ near $x$ satisfies $L(y) \in \mathcal T_x$ and
$y = x\exp(L(y))$. *Book:* p. 137: Assertion 1 ($J\exp A$ is a complex structure if and only if $A$
anticommutes with $J$) and Assertion 2 ($J\exp A$ anticommutes with $J_1, \dots, J_{k-1}$ if and
only if $A$ commutes with them), for small skew $A$; hence "a neighborhood of $J$ in $\Omega_k(n)$
consists of all points $J\exp A$ where $A$ ranges over all small matrices in a linear subspace of
the Lie algebra". *Hidden hypotheses:* "small" must be measured by a norm invariant under
transposition and under conjugation by orthogonal matrices, since the "only if" halves apply the
injectivity of $\exp$ to $C^{\mathsf T}$, $x^{\mathsf T}Cx$ and $J_\alpha CJ_\alpha^{\mathsf T}$ as
well as to $\pm C$; the Frobenius norm is. *Deviation (stronger):* in (ii) $C$ is any small matrix;
that it is skew is part of the conclusion. The "if" halves are V15.6, here for all $k \ge 0$.

**V15.23 (Lemma 24.4, first half: the strata of $\Omega_k(n)$ are compact totally geodesic
submanifolds; `Morse.omegaStratum`, `Morse.finrank_tanAlg_mul_exp`,
`Morse.eventually_mem_omegaStratum`, `Morse.isClosed_omegaStratum`, `Morse.isCompact_omegaStratum`,
`Morse.isSliceSubmanifold_omegaStratum`, `Morse.isTotGeo_omegaStratum`,
`Morse.omegaStratum_zero`).** The *stratum* of $\Omega_k(n)$ through a matrix $p$ is the set of
$x \in \Omega_k(n)$ with $\dim\mathcal T_x = \dim\mathcal T_p$. (i)
$\dim\mathcal T_{x\exp A} = \dim\mathcal T_x$ for $A \in \mathcal T_x$. Let $J_1, \dots, J_k$ be an
anticommuting family. (ii) The stratum is open in $\Omega_k(n)$ (each of its points has a
neighbourhood in $M_n(\mathbb R)$ whose points in $\Omega_k(n)$ belong to it), closed in
$M_n(\mathbb R)$, and compact. (iii) It is a slice submanifold of $M_n(\mathbb R)$ modelled on
$\mathcal T_p$, and it satisfies the hypotheses of V15.21 with $T_x = \mathcal T_x$. Consequently
its tangent space at $x$ is $x\mathcal T_x$, its geodesics are the curves $t \mapsto x\exp(tA)$ with
$A \in \mathcal T_x$, and it is geodesically complete. For $k = 0$ the stratum through any $p$ is
$O(n)$. *Book:* p. 136, Lemma 24.4: each $\Omega_k(n)$ is a smooth, totally geodesic submanifold of
$O(n)$; p. 139: $\Omega_3(16r)$ "contains components of varying dimension" (and p. 141 for
$\Omega_7(16r)$). *Hidden hypotheses:* as the components of $\Omega_k(n)$ may have different
dimensions, the lemma must be read on each component separately. *Deviation (restated):* on the
stratum through $p$, which is open and closed in $\Omega_k(n)$, hence a union of components, among
them that of $p$ when $p \in \Omega_k(n)$; as a submanifold of $M_n(\mathbb R)$ rather than of
$O(n)$; and with "totally geodesic" in the sense of V15.21. *Proof:* near a point $x$ of the
stratum, $(a, w) \mapsto x(\exp a + w)$, $a \in \mathcal T_x$, $w \in \mathcal T_x^\perp$, is a
parametrization as in V15.21, by V15.22 (iii) and (i).

**V15.24 (Lemma 24.1, the length of a geodesic from $I$ to $-I$; `Morse.pi_sq_le_of_sq_mul`,
`Morse.pi_sq_mul_card_le_norm_sq`, `Morse.mul_self_eq_of_norm_sq_le`).** Let $V$ be a skew matrix
with $\exp V = -I$. If $E \neq 0$ is a matrix and $V^2E = -\lambda E$ for a real $\lambda$, then
$\lambda \ge \pi^2$. Hence $\|V\|^2 \ge \pi^2n$, and if $\|V\|^2 \le \pi^2n$ then $V^2 = -\pi^2I$.
*Book:* p. 134, proof of Lemma 24.1: for $A$ in the block form with blocks
$a_j\bigl(\begin{smallmatrix}0 & 1\\ -1 & 0\end{smallmatrix}\bigr)$, $\exp(\pi A) = -I$ if and only
if the $a_j$ are odd integers; $\langle A, A\rangle = 2(a_1^2 + \dots + a_m^2)$; so the geodesic
$t \mapsto \exp(\pi tA)$ is minimal if and only if $a_1 = \dots = a_m = 1$, and then $A^2 = -I$.
*Hidden hypotheses:* none. *Deviation (restated):* $V = \pi A$, and no normal form: the symmetric
matrix $V^{\mathsf T}V = -V^2$ is diagonalized by Mathlib's spectral theorem, and for an eigenvalue
$\lambda > 0$ the solution $\cos(\sqrt\lambda\,t)E + \lambda^{-1/2}\sin(\sqrt\lambda\,t)VE$ of
$c' = Vc$ must be $-E$ at $t = 1$, which forces $\sqrt\lambda \ge \pi$. That this bound describes
the minimal geodesics is V15.25.

**V15.25 (the distance from $p$ to $-p$, and the minimal geodesics; `Morse.minVelO`,
`Morse.omegaGeo`, `Morse.neg_mem_omegaStratum`, `Morse.riemDist_omegaStratum`,
`Morse.pi_sq_card_le_energy`, `Morse.omegaPath_mem_minPaths`,
`Morse.exists_minVelO_of_mem_minPaths`, `Morse.omegaGeo_half`).** Let $J_1, \dots, J_k$ be an
anticommuting family, $p \in \Omega_k(n)$, $N$ the stratum through $p$, and
$\mathcal C_p = \{A \in \mathcal T_p : A^2 = -I\}$; suppose $\mathcal C_p \neq \emptyset$. For
$A \in \mathcal C_p$ put $\gamma_A(t) = p\exp(\pi tA)$. Then: (i) $-p \in N$; (ii) the Riemannian
distance in $N$ is $\rho(p, -p) = \pi\sqrt n$, and every path in $\Omega(N; p, -p)$ has energy
$\ge \pi^2n$; (iii) every $\gamma_A$, $A \in \mathcal C_p$, is a path of least energy in
$\Omega(N; p, -p)$, and its midpoint is $\gamma_A(\tfrac12) = pA$; (iv) every path of least energy
agrees on $[0, 1]$ with $\gamma_A$ for some $A \in \mathcal C_p$. *Book:* pp. 137–138, proof of
Lemma 24.4: the geodesic $t \mapsto J_k\exp(\pi tA)$ "is minimal in $O(n)$", hence "certainly
minimal in $\Omega_k(n)$"; conversely a minimal geodesic from $J_k$ to $-J_k$ in $\Omega_k(n)$ is
$J_k\exp(\pi tA)$ with $A$ a complex structure (by 24.1) commuting with $J_1, \dots, J_{k-1}$ and
anticommuting with $J_k$ (by Assertions 1, 2); Remark, p. 138: $J_kA$ is the midpoint
$\gamma(\tfrac12)$. *Hidden hypotheses:* that a minimal geodesic exists; in the converse, that a
minimal geodesic of $\Omega_k(n)$ is minimal in $O(n)$, which needs the distance from $J_k$ to
$-J_k$ in $O(n)$. *Deviation (restated):* distances in $\Omega_k(n)$ and in $O(n)$ are not compared.
$N$ is complete (V15.23), so by the Hopf–Rinow theorem (V7.26) a shortest geodesic from $p$ to $-p$
exists; it is $t \mapsto p\exp(tV)$ with $V \in \mathcal T_p$ and $\exp V = -I$ (V15.23), of length
$\|V\| \ge \pi\sqrt n$ (V15.24). "Minimal" is read as "of least energy" (V13.1). *Deviation
(stronger):* any $p \in \Omega_k(n)$ with $\mathcal C_p \neq \emptyset$, not only $J_k$.

**V15.26 (Lemma 24.1, and Lemma 24.4, second half: the minimal geodesics and $\Omega_{k+1}(n)$;
`Morse.basePt`, `Morse.mem_minVelO_iff`, `Morse.minVelOHomeomorph`, `Morse.omegaGeo_eq_semicircle`,
`Morse.omegaMinPathsHomotopyEquiv`, `Morse.omegaMinPathsHomeomorph`, `Morse.omegaPhi`,
`Morse.omegaPhi_apply`, `Morse.isHomotopyEquiv_omegaPhi_minPaths`).** Let $J_1, \dots, J_k$ be an
anticommuting family, with base point $J_k$ ($J_0 = I$). (i) $A \in \mathcal C_{J_k}$ if and only if
$J_kA \in \Omega_{k+1}(n)$; $A \mapsto J_kA$ is a homeomorphism of $\mathcal C_{J_k}$ onto
$\Omega_{k+1}(n)$, with inverse $J' \mapsto J_k^{\mathsf T}J'$; and for $J' \in \Omega_{k+1}(n)$ and
$A = J_k^{\mathsf T}J'$, $\gamma_A(t) = \cos(\pi t)\,J_k + \sin(\pi t)\,J'$ for all $t$. (ii) In the
setting of V15.25, $A \mapsto \gamma_A$ is a homotopy equivalence of $\mathcal C_p$ with
$\Omega^d(N; p, -p)$, and a homeomorphism of $\mathcal C_p$ onto the quotient of $\Omega^d$ in which
paths at distance $0$ are identified. (iii) If $J_1, \dots, J_{k+1}$ is an anticommuting family and
$N$ is the stratum of $\Omega_k(n)$ through $J_k$, the map
$\varphi : \Omega_{k+1}(n) \to \Omega(N; J_k, -J_k)$,
$\varphi(J')(t) = \cos(\pi t)\,J_k + \sin(\pi t)\,J'$, is continuous, and it is the inclusion
$\Omega^d \to \Omega$ composed with a homotopy equivalence $\Omega_{k+1}(n) \to \Omega^d$. For
$k = 0$, $N = O(n)$ and $\Omega_1(n)$ is the set of all complex structures: this is Lemma 24.1.
*Book:* p. 133, Lemma 24.1: the space of minimal geodesics from $I$ to $-I$ in $O(n)$ is
homeomorphic to the space $\Omega_1(n)$ of complex structures; p. 136, Lemma 24.4: the space of
minimal geodesics from $J_\ell$ to $-J_\ell$ in $\Omega_\ell(n)$ is homeomorphic to
$\Omega_{\ell+1}(n)$, for $0 \le \ell < k$. *Hidden hypotheses:*
$\Omega_{\ell+1}(n) \neq \emptyset$, here the existence of $J_{k+1}$; the topology of the space of
minimal geodesics. *Deviation (narrower):* paths are functions on $\mathbb R$, and two paths at
distance $0$ are two that agree on $[0, 1]$; so $\Omega^d$ itself is only homotopy equivalent to
$\Omega_{k+1}(n)$, and homeomorphic to it after that identification (as for $SU(2m)$, V14.17).

**V15.27 (the neighbourhood retraction for $\Omega_k(n)$; `Morse.midDir`, `Morse.polarDir`,
`Morse.polarDir_mem`, `Morse.omegaNbhd`, `Morse.isOpen_omegaNbhd`,
`Morse.exists_retraction_minPaths_omega`).** In the setting of V15.25, $\Omega^d(N; p, -p)$ is a
retract of an open neighbourhood: there are an open $O \supseteq \Omega^d$ in $\Omega(N; p, -p)$ and
a map $\rho : O \to \Omega^d$, continuous on $O$ and equal to the identity on $\Omega^d$. Here, for
a matrix $Y$, let $Y_1$ be the orthogonal projection of $p^{\mathsf T}Y$ onto $\mathcal T_p$; if
$\det(Y_1^{\mathsf T}Y_1) \neq 0$, then $Y_1(Y_1^{\mathsf T}Y_1)^{-1/2} \in \mathcal C_p$. $O$ is
the set of paths $\omega$ whose midpoint $Y = \omega(\tfrac12)$ has
$\det(Y_1^{\mathsf T}Y_1) \neq 0$, an open set, and off $\Omega^d$ the retraction is
$\rho(\omega) = \gamma_A$ with $A = Y_1(Y_1^{\mathsf T}Y_1)^{-1/2}$. *Book:* p. 118, Theorem 22.1
assumes that $\Omega^d$ is a topological manifold; in §24 this is the statement that
$\Omega_{k+1}(n)$ is a manifold (pp. 135–136: "together with the statement that $\Omega_1(n)$ is a
manifold"). *Hidden hypotheses:* Hanner's theorem, which turns "manifold" into the retraction that
the proof of 22.1 uses (V13.2). *Deviation (not in the book):* an explicit retraction, the third of
the project (after V13.8 and V14.21): the nearest complex structure in $\mathcal T_p$ to the
midpoint, by projection and polar decomposition. It supplies the hypothesis of V13.2 for every
stratum.

**V15.28 (Killing fields are Jacobi fields, and a lower bound for the index; `Morse.isoAlg`,
`Morse.killing`, `Morse.isJacobiField_killing`, `Morse.finrank_le_conjMultiplicity`,
`Morse.sum_finrank_le_formIndex`).** Let $J_1, \dots, J_k$ be an anticommuting family,
$p \in \Omega_k(n)$, $N$ the stratum through $p$, and $V \in \mathcal T_p$. The *isotropy algebra*
of $p$ is the space of skew matrices commuting with $p$ and with $J_1, \dots, J_{k-1}$. (i) For $X$
in the isotropy algebra, $K(t) = X\gamma(t) - \gamma(t)X$ is a Jacobi field along
$\gamma(t) = p\exp(tV)$ in $N$. (ii) Let $\gamma \in \Omega(N; p, q)$ be an unbroken geodesic equal
to $t \mapsto p\exp(tV)$ on $[0, 1]$, let $\tau \in [0, 1]$, and let $\mathcal X$ be a subspace of
the isotropy algebra whose elements commute with $\exp(\tau V)$ and none of whose non-zero elements
commutes with $V$. Then $\gamma(\tau)$ is conjugate to $\gamma(0)$ along $\gamma$ with multiplicity
(V9.4) at least $\dim\mathcal X$. (iii) For a finite set $T \subset (0, 1)$ and such subspaces
$\mathcal X_\tau$, $\tau \in T$, the index of $\gamma$ is at least
$\sum_{\tau \in T}\dim\mathcal X_\tau$. *Book:* pp. 144, 146: since $\Omega_k(n)$ is totally
geodesic in $O(n)$, $K_A$ is computed by $K_AB = -\tfrac14[A, [A, B]]$ on the space $T$ of Milnor's
conditions 1)–3); each eigenvalue $e^2$ of $K_A$ gives conjugate points at
$t = e^{-1}, 2e^{-1}, \dots$ by 20.5; then the index theorem. *Hidden hypotheses:* that the
curvature of a totally geodesic submanifold is that of the ambient manifold, and Theorem 20.5 for
the components of $\Omega_k(n)$. *Deviation (restated):* neither is formalized, and neither is
needed for a lower bound, which only asks for Jacobi fields vanishing at $0$ and at $\tau$. These
come from the isometries $y \mapsto gyg^{-1}$, $g = \exp(uX)$, of $N$, which fix $p$: $K$ is the
variation field of the geodesics $t \mapsto g\,p\exp(tV)\,g^{-1}$ (Lemma 14.3, V9.8), and it
vanishes at $\tau$ when $X$ commutes with $\exp(\tau V)$. (iii) is the Index Theorem (V9.24).

**V15.29 (the splitting into minimal pieces, and Lemma 24.8 between two pieces; `Morse.IsInvar`,
`Morse.IsMinInvar`, `Morse.IsStarSigned`, `Morse.exists_minInvar_decomp`,
`Morse.IsMinInvar.exists_scalar`, `Morse.IsOmegaOps`, `Morse.omegaGens`,
`Morse.IsOmegaOps.exists_sq_eq`, `Morse.one_le_of_minInvar`, `Morse.IsOmegaOps.isClifford_cliffFam`,
`Morse.IsOmegaOps.isMinimal_cliffFam`, `Morse.IsOmegaOps.exists_inter`,
`Morse.IsOmegaOps.exists_piece_gt`, `Morse.IsOmegaOps.exists_omegaPieceData`).** Let $E$ be a
finite-dimensional real inner product space and $\mathcal G$ a set of operators on $E$, each
self-adjoint or skew-adjoint. A subspace is *minimal invariant* if it is non-zero, invariant under
$\mathcal G$, and contains no invariant subspace other than $0$ and itself. (i) Every invariant
subspace $U$ is spanned by a list of pairwise orthogonal minimal invariant subspaces of $U$ whose
dimensions add up to $\dim U$; and a self-adjoint operator that commutes with $\mathcal G$ and
preserves a minimal invariant $M$ is a scalar on $M$. (ii) Let $A$ be skew-adjoint, let
$J, J_1, \dots, J_{k-1}$ be skew-adjoint operators with square $-1$, anticommuting with one another,
and let $A$ anticommute with $J$ and commute with the $J_\alpha$ (for $k = 0$: $J = 1$ and there are
no $J_\alpha$); put $\mathcal G = \{A, J, J_1, \dots, J_{k-1}\}$. On each minimal invariant $M$,
$A^2 = -c$ for a real $c$; and for real $s$ with $s^2c = 1$ the restrictions of
$J_1, \dots, J_{k-1}, J, sJA$ to $M$ satisfy the Clifford relations (V15.10) and make $M$ a minimal
space for $k + 1$ structures (V15.13). For matrices: if $A$ is skew, $\exp(\pi A) = -I$, and
$A^2 = -c$ on a non-zero subspace of $\mathbb R^n$, then $c \ge 1$. (iii) If $k \le 7$,
$k \not\equiv 2 \pmod 4$, and $M_0$, $M_1$ are minimal invariant with $A^2 = -a_0^2$ on $M_0$ and
$A^2 = -b^2$ on $M_1$, $a_0, b > 0$, there is a linear isomorphism $T : M_0 \to M_1$ that commutes
with $J$ and the $J_\alpha$ and carries $a_0^{-1}JA$ to $-b^{-1}JA$. (iv) If moreover $c \ge 1$ on
every minimal invariant subspace and $A^2 \neq -1$, then in a splitting (i) of $E$ some piece $M_0$
has $c > 1$; and there are an integer $s$ with $(s + 1)m_{k+1} = \dim E$, reals $a_0 > 1$ and
$b_1, \dots, b_s \ge 1$, and operators $D_1, \dots, D_s$ on $E$ (each the projection onto $M_0$
followed by an isomorphism (iii) onto another piece) which commute with $J$ and the $J_\alpha$,
satisfy $b_jD_jA = -a_0AD_j$, $A^2D_j = -b_j^2D_j$ and $D_jA^2 = -a_0^2D_j$, and for which the
$AD_j$ are separated by projections (for $k = 0$ there are two for each $j$, $D_j$ and $D_jA$).
*Book:* pp. 144–145: $\mathbb R^n = M_1 \oplus \dots \oplus M_s$, mutually orthogonal subspaces
closed and minimal under $J_1, \dots, J_{k-1}$, $J$ and $A$; the eigenvalues of $A$ on $M_h$ are
"all equal, except for sign", $\pm ia_h$ with $a_h$ odd and positive; $J' = a_h^{-1}JA|M_h$ makes
$M_h$ a minimal $(J_1, \dots, J_{k-1}, J, J')$-space, so $\dim M_h = m_{k+1}$ and $s = n/m_{k+1}$;
for $h \neq j$ an isometry $M_h \to \bar M_j$ "exists by 24.8". *Hidden hypotheses:* that the
orthogonal complement of an invariant subspace is invariant (the operators are skew); $k + 1 \le 8$,
the range in which Lemma 24.8 is proved (V15.16–V15.17). *Deviation (restated):* $a_h = \sqrt c$;
that the $a_h$ are odd integers is not used, only $c \ge 1$. Milnor changes the sign of $J$ on
$M_j$; changing the sign of the last structure instead is equivalent, and keeps $T$ commuting with
$J$. *Deviation (narrower):* $T$ is a linear isomorphism, not an isometry (V15.17); this suffices,
because only the skew matrix $D - D^{\mathsf T}$ is used.

**V15.30 (the index of a non-minimal geodesic for $k \not\equiv 2 \pmod 4$, and Lemma 24.2 for
geodesics; `Morse.IsInterRel`, `Morse.IsInterRel.commute_exp`, `Morse.exists_killing_spaces`,
`Morse.exists_killing_spaces_omega`, `Morse.le_formIndex_of_not_minimal_omega`,
`Morse.omega_hidx`).** Let $J_1, \dots, J_k$ be an anticommuting family on $\mathbb R^n$ with
$\mathcal C_{J_k} \neq \emptyset$ (equivalently $\Omega_{k+1}(n) \neq \emptyset$, V15.26), let
$k \le 7$ and $k \not\equiv 2 \pmod 4$, and let $N$ be the stratum through $J_k$. If
$\gamma \in \Omega(N; J_k, -J_k)$ is an unbroken geodesic which is not of least energy, then
$m_{k+1}$ divides $n$ and the index of $\gamma$ is at least $n/m_{k+1} - 1$; for $k = 0$ it is at
least $2(n/2 - 1) = n - 2$. *Book:* p. 135, Lemma 24.2: any non-minimal geodesic from $I$ to $-I$ in
$O(2m)$ has index $\ge 2m - 2$; p. 146, Assertion: the index of a non-minimal geodesic from $J$ to
$-J$ in $\Omega_k(n)$ is $\ge n/m_{k+1} - 1$ (for $k \not\equiv 2 \pmod 4$), from the $s - 1$
eigenvalues $(a_h + a_j)^2/4 \ge 4$ of $K_A$ (p. 145). *Hidden hypotheses:* the linear independence
of the eigenvectors belonging to different pairs $(h, j)$; $k + 1 \le 8$. *Deviation (restated):* by
V15.23 and V15.25, $\gamma$ is $t \mapsto J_k\exp(\pi tA)$ on $[0, 1]$ with
$A \in \mathcal T_{J_k}$, $\exp(\pi A) = -I$ and $A^2 \neq -I$. With the pieces and the operators
$D_j$ of V15.29, $X_j = D_j - D_j^{\mathsf T}$ lies in the isotropy algebra of $J_k$ and commutes
with $\exp(\tau_j\pi A)$ for $\tau_j = 2/(a_0 + b_j) \in (0, 1)$, and the $[X_j, A]$ are linearly
independent; V15.28 (iii) gives the bound. Milnor's eigenvector $B$ is $[X_j, A]$ up to a factor.
For $k = 0$ each pair of pieces gives two fields, from $D_j$ and $D_jA$: Milnor's eigenvalues
"counted twice". "Non-minimal" is read as "not of least energy". *Deviation (narrower):* only the
lower bound; the formula of Lemma 24.2 for the index of a geodesic of $O(2m)$ is not proved for
geodesics (V15.3 derives it from Milnor's spectrum).

**V15.31 (Theorem 24.5 for each $n$, $k \not\equiv 2 \pmod 4$; `Morse.omega_theorem_22_1_bijective`,
`Morse.omegaPhi_bijective`, `Morse.stratumIn`, `Morse.isClopen_stratumIn`,
`Morse.nonempty_pi_stratum_equiv`, `Morse.omega_pi_equiv`).** Let $J_1, \dots, J_{k+1}$ be an
anticommuting family on $\mathbb R^n$, $k \le 7$, $k \not\equiv 2 \pmod 4$, let $N$ be the stratum
of $\Omega_k(n)$ through $J_k$, and let $i + 2 \le n/m_{k+1} - 1$ (for $k = 0$: $i + 2 \le n - 2$).
Then: (i) the inclusion $\Omega^d \to \Omega(N; J_k, -J_k)$ induces a bijection on $\pi_i$ at every
minimal path; (ii) for every $J' \in \Omega_{k+1}(n)$, the map $\varphi$ of V15.26 induces a
bijection $\pi_i(\Omega_{k+1}(n), J') \to \pi_i(\Omega(N; J_k, -J_k), \varphi(J'))$; (iii) for every
$J' \in \Omega_{k+1}(n)$ there is a bijection
$\pi_i(\Omega_{k+1}(n), J') \cong \pi_{i+1}(\Omega_k(n), J_k)$. On the way: $N$ is open and closed
in $\Omega_k(n)$, and $\pi_{j+1}(N, x) \cong \pi_{j+1}(\Omega_k(n), x)$ for $x \in N$ and $j \ge 0$.
*Book:* p. 146: the inclusion $\Omega_{k+1}(n) \to \Omega\Omega_k(n)$ induces isomorphisms of
homotopy groups in dimensions $\le n/m_{k+1} - 3$; p. 138, Theorem 24.5:
$\pi_hO \cong \pi_{h-1}\Omega_1 \cong \pi_{h-2}\Omega_2 \cong \dots \cong \pi_1\Omega_{h-1}$.
*Hidden hypotheses:* base points; $k + 1 \le 8$; the case $i = 0$. *Deviation (restated):*
V13.2–V13.4 for the stratum, with V15.27 and V15.30. Milnor's $\Omega\Omega_k(n)$ is here the space
of piecewise smooth paths from $J_k$ to $-J_k$ in $N$ with Milnor's metric; the passage to
continuous paths and loops is inside V13.4. Bijections of pointed sets, $\pi_0$ included, at every
base point $J'$. The quotient $n/m_{k+1}$ is exact, since $J_{k+1}$ exists (V15.14).

**V15.32 (Theorem 24.3; `Morse.theorem_24_3`).** Suppose $\mathbb R^n$ carries a complex structure
(so $n$ is even), and let $i + 4 \le n$. For every complex structure $J'$ on $\mathbb R^n$, the map
$\varphi : \Omega_1(n) \to \Omega(O(n); I, -I)$, $\varphi(J)(t) = \cos(\pi t)\,I + \sin(\pi t)\,J$,
induces a bijection on $\pi_i$ at $J'$, and there is a bijection
$\pi_i(\Omega_1(n), J') \cong \pi_{i+1}(O(n), I)$. *Book:* p. 136, Theorem 24.3 (Bott): the
inclusion map $\Omega_1(n) \to \Omega O(n)$ induces isomorphisms of homotopy groups in dimensions
$\le n - 4$; hence $\pi_i\Omega_1(n) \cong \pi_{i+1}O(n)$ for $i \le n - 4$. *Hidden hypotheses:*
base points. *Deviation (restated):* the case $k = 0$ of V15.31, where the stratum is $O(n)$;
bijections of pointed sets, at every $J'$.

**V15.33 (angles, and the sets of paths with a given end angle; `Morse.IsAngleLift`,
`Morse.IsAngleLift.unique`, `Morse.exists_isAngleLift`, `Morse.IsAngleLift.perturb`,
`Morse.windSet`, `Morse.isClopen_windSet`, `Morse.disjoint_windSet`).** Let $F$ be a complex-valued
function on a finite-dimensional real inner product space $V$ and $\omega : \mathbb R \to V$. An
*angle* of $F \circ \omega$ is a continuous $\theta : [0, 1] \to \mathbb R$ with $\theta(0) = 0$ and
$F(\omega(t)) = e^{i\theta(t)}$ for $t \in [0, 1]$. An angle is unique, and it exists whenever
$t \mapsto F(\omega(t))$ is continuous on $[0, 1]$, of modulus $1$, with $F(\omega(0)) = 1$. For
$N \subseteq V$, points $p$, $q$ and a real $w$, let $\Omega_w \subseteq \Omega(N; p, q)$ be the set
of paths $\omega$ for which $F \circ \omega$ has an angle with $\theta(1) = w$. If $F$ is continuous
and $|F| = 1$ on a compact set containing $N$, every $\Omega_w$ is open and closed in
$\Omega(N; p, q)$; and $\Omega_w$, $\Omega_{w'}$ are disjoint for $w \neq w'$. *Book:* p. 147: $f$
maps the geodesic into a closed loop on $S^1$ "which is completely determined by the trace of $A$",
and "this trace is invariant under homotopy of the geodesic within the path space"; p. 148:
"restrict attention to some fixed component of $\Omega\Omega_k(n)$". *Hidden hypotheses:* Theorem
22.1 is applied to one class of paths, which must then be open and closed in the path space
(V13.16). *Deviation (restated):* the classes $\Omega_w$ in place of components. *Proof:* paths that
are close in Milnor's metric are uniformly close on $[0, 1]$; then
$|F \circ \omega' - F \circ \omega| < 1$, the quotient $F \circ \omega'/F \circ \omega$ has positive
real part, and adding its argument to the angle of $\omega$ gives the angle of $\omega'$, with the
same end value.

**V15.34 ($\det_{\mathbb C}$ of a real matrix; `Morse.cplx`, `Morse.projP`, `Morse.projM`,
`Morse.cdet`, `Morse.cdet_mul`, `Morse.cdet_one`, `Morse.norm_cdet`, `Morse.cdet_exp`).** For real
$n \times n$ matrices $\mathbf i$ and $M$ put $\det_{\mathbb C}M = \det(M_{\mathbb C}P_+ + P_-)$, a
complex number, where $M_{\mathbb C}$ is $M$ read as a complex matrix and
$P_\pm = \tfrac12(1 \mp \sqrt{-1}\,\mathbf i_{\mathbb C})$. Then $\det_{\mathbb C}I = 1$, and, if
$\mathbf i^2 = -I$: $\det_{\mathbb C}(MN) = \det_{\mathbb C}M\,\det_{\mathbb C}N$ whenever $N$
commutes with $\mathbf i$; $|\det_{\mathbb C}M| = 1$ when $\mathbf i$ is skew and $M$ is orthogonal
and commutes with $\mathbf i$; and
$\det_{\mathbb C}\exp(tV) = e^{-\sqrt{-1}\,t\operatorname{tr}(V\mathbf i)/2}$ for every real $t$,
when $V$ commutes with $\mathbf i$ and $\operatorname{tr}V = 0$. *Book:* p. 146: $\mathbb R^n$ is
made a complex vector space by $iv = J_1J_2\cdots J_{k-1}v$, and a unitary complex linear
transformation "has a well defined complex determinant"; p. 147:
$f(J\exp(\pi tA)) = \det(\exp(\pi tA)) = e^{\pi t\operatorname{trace}A}$, the trace being the
complex one. *Hidden hypotheses:* none. *Deviation (restated):* no complex basis is chosen.
$M_{\mathbb C}P_+ + P_-$ is $M$ on the $\sqrt{-1}$-eigenspace of $\mathbf i_{\mathbb C}$, a copy of
the complex vector space $(\mathbb R^n, \mathbf i)$, and the identity on the other eigenspace; and
the complex trace of a real $V$ commuting with $\mathbf i$ is
$\tfrac12(\operatorname{tr}V - \sqrt{-1}\operatorname{tr}(V\mathbf i))$.

**V15.35 (Milnor's $i$ and $f$, and the sets $\Omega^{(c)}$; `Morse.IsCentralI`, `Morse.iWordM`,
`Morse.isCentralI_two`, `Morse.isCentralI_six`, `Morse.omegaF`, `Morse.norm_omegaF`,
`Morse.omegaF_self`, `Morse.omegaF_geo`, `Morse.omegaComp`, `Morse.isClopen_omegaComp`,
`Morse.disjoint_omegaComp`, `Morse.mem_omegaComp_geo_iff`).** Call a matrix $\mathbf i$ *central for
$k$* if $\mathbf i^2 = -I$, $\mathbf i^{\mathsf T} = -\mathbf i$, $\mathbf i$ commutes with
$J_1, \dots, J_{k-1}$ and with every matrix that commutes with all of them, and $\mathbf i$
anticommutes with every matrix that anticommutes with all of them. The product
$\mathbf i = J_1J_2\cdots J_{k-1}$ is central for $k = 2$ when $J_1$ is a complex structure, and for
$k = 6$ when $J_1, \dots, J_5$ is an anticommuting family. Let $\mathbf i$ be central for $k \ge 1$,
$p \in \Omega_k(n)$, and $f(X) = \det_{\mathbb C}(p^{\mathsf T}X)$ (V15.34 with this $\mathbf i$).
Then $|f| = 1$ on $\Omega_k(n)$, $f(p) = 1$, and
$f(p\exp(tV)) = e^{-\sqrt{-1}\,t\operatorname{tr}(V\mathbf i)/2}$ for $V \in \mathcal T_p$. Now let
$J_1, \dots, J_k$ be an anticommuting family, $k \ge 1$, $p = J_k$, $N$ the stratum through $J_k$,
and let $\Omega_w \subseteq \Omega(N; J_k, -J_k)$ be the set of paths whose $f$-angle ends at $w$
(V15.33). Each $\Omega_w$ is open and closed, different $w$ give disjoint sets, and a path that
agrees on $[0, 1]$ with $t \mapsto J_k\exp(tV)$, $V \in \mathcal T_{J_k}$, lies in $\Omega_w$ if and
only if $w = -\operatorname{tr}(V\mathbf i)/2$. For an integer $c$, $\Omega^{(c)}$ denotes
$\Omega_w$ with $w = \pi m_{k+1}c/2$. *Book:* pp. 146–148: $iv = J_1J_2\cdots J_{k-1}v$, where "the
condition $k \equiv 2 \pmod 4$ guarantees that $i^2 = -1$, and that $J_1, J_2, \dots, J_{k-1}$
commute with $i$"; $f(J') = \det_{\mathbb C}(J^{-1}J')$; a component of the path space is fixed by
$\operatorname{trace}A = icm_k/2$. *Hidden hypotheses:* that every $J' \in \Omega_k(n)$ anticommutes
with $i$ and every $A \in \mathcal T$ commutes with it, so that $J^{-1}J'$ and $A$ are complex
linear. *Deviation (restated):* the properties of $i$ that are used are taken as the definition of
"central" and proved for $k = 2$ and $k = 6$, the cases that occur for $k \le 7$. For these
$m_{k+1} = m_k$, and for the geodesic $J_k\exp(\pi tA)$ Milnor's $\operatorname{trace}A$ is
$-\tfrac{\sqrt{-1}}2\operatorname{tr}(A\mathbf i)$; so $\Omega^{(c)}$ contains exactly the geodesics
with $\operatorname{trace}A = icm_k/2$, as in the book.

**V15.36 (every path lies in exactly one $\Omega^{(c)}$; `Morse.existsUnique_mem_omegaComp`,
`Morse.exists_mem_omegaComp_two`, `Morse.exists_mem_omegaComp_six`, `Morse.pdet`,
`Morse.pdet_split`, `Morse.omegaF_eq_pow_four`).** Let $k = 2$ or $k = 6$, let $J_1, \dots, J_k$ be
an anticommuting family, $\mathbf i = J_1\cdots J_{k-1}$ and $N$ the stratum through $J_k$. Every
path in $\Omega(N; J_k, -J_k)$ lies in $\Omega^{(c)}$ for exactly one integer $c$. For $k = 6$ the
proof uses that $f = G^4$ on $\Omega_6(n)$, where
$G(X) = \det\bigl((J_6^{\mathsf T}X)_{\mathbb C}Q + 1 - Q\bigr)$ and $Q$ is the product of the
projections $P_+$ of V15.34 for $\mathbf i$, $J_1J_2$ and $J_3J_4$. *Book:* p. 148:
"$\operatorname{trace}A = icm_k/2$ where $c$ is some constant integer". *Hidden hypotheses:* that
the class of an arbitrary path, not only of a geodesic, is given by an integer $c$. The end angle is
a multiple of $2\pi$ because $f(-J_k) = \det_{\mathbb C}(-I) = 1$, which holds since $4$ divides $n$
(V15.14); this is Milnor's "closed loop" (p. 147). For $k = 2$ that is the claim, as
$\pi m_3/2 = 2\pi$. For $k = 6$ the normalization asks for multiples of $\pi m_7/2 = 4\pi$, which
needs $f$ to be the fourth power of a continuous function $G$ with $G(-J_6) = \pm1$. *Deviation (not
in the book):* the statement, and the fourth-power argument: the commutant of $J_1, \dots, J_5$ acts
on the $+\sqrt{-1}$-eigenspace of $\mathbf i$ as four copies of one representation, split off by
$J_1J_2$ and $J_3J_4$.

**V15.37 (the pieces for $k \equiv 2 \pmod 4$; `Morse.iWord`, `Morse.IsIOps`,
`Morse.IsOmegaOps.exists_eq_smul_iWord`, `Morse.exists_odd_of_mulVec`, `Morse.exists_decomp_two`,
`Morse.exists_inter_two`).** In the setting of V15.29 (ii) with $k \ge 1$, let
$\mathbf i = J_1\cdots J_{k-1}$ and suppose that $\mathbf i$ is skew-adjoint with
$\mathbf i^2 = -1$, commutes with $A$ and the $J_\alpha$, and anticommutes with $J$. (i) On each
minimal invariant $M$, $A = c\,\mathbf i$ for a real $c$. (ii) For matrices: if $\mathbf i$ is skew
with $\mathbf i^2 = -I$ and commutes with $A$, $\exp(\pi A) = -I$, and $Aw = c\,\mathbf iw$ for a
vector $w \neq 0$, then $c$ is an odd integer. (iii) If $k \le 7$ and the scalars $c$ of (i) are odd
integers, then there are pairwise orthogonal minimal invariant subspaces $M_1, \dots, M_\nu$ of $E$
with $A = a_h\mathbf i$ on $M_h$, $a_h$ an odd integer, $\nu m_{k+1} = \dim E$,
$\operatorname{tr}(A\mathbf i) = -m_{k+1}\sum_h a_h$, and $A^2 = -1$ if every $a_h = \pm1$. (iv) If
$k \le 8$, $k \not\equiv 3 \pmod 4$, and $M_0$, $M_1$ are minimal invariant with $A = c_0\mathbf i$
on $M_0$ and $A = c_1\mathbf i$ on $M_1$, $c_0, c_1 \neq 0$, there is a linear isomorphism
$M_0 \to M_1$ that commutes with the $J_\alpha$ and anticommutes with $J$. *Book:* p. 147: on $M_h$
the complex linear transformation $A|M_h$ "can have only one eigenvalue, say $ia_h$", so
$A|M_h = a_hJ_1J_2\cdots J_{k-1}|M_h$; $M_h$ is minimal under $J_1, \dots, J_{k-1}, J$, of complex
dimension $m_k/2$, so $\operatorname{trace}A = i(a_1 + \dots + a_r)m_k/2$; by 24.8 there is an
isometry $M_h \to M_j$ which commutes with $J_1, \dots, J_{k-1}$ and anticommutes with $J$. *Hidden
hypotheses:* why $A|M_h$ has only one eigenvalue. *Deviation (restated):* $A\mathbf i$ is
self-adjoint and commutes with $\mathcal G$, hence is a scalar on $M$ (V15.29 (i)); complex
eigenspaces are not used. The count is in terms of $m_{k+1}$, which is $m_k$ for $k = 2, 6$.
*Deviation (narrower):* a linear isomorphism, not an isometry, as in V15.29.

**V15.38 (the index bound on $\Omega^{(c)}$; `Morse.IsInterRelI`, `Morse.IsInterRelI.commute_exp`,
`Morse.exists_killing_spaces_two`, `Morse.le_formIndex_of_not_minimal_omega_two`,
`Morse.omega_hidx_two`).** Let $J_1, \dots, J_k$ be an anticommuting family on $\mathbb R^n$ with
$1 \le k \le 7$, $k \not\equiv 3 \pmod 4$, such that $\mathbf i = J_1\cdots J_{k-1}$ is central for
$k$ and $\mathcal C_{J_k} \neq \emptyset$, and let $c$ be an integer. If $\gamma \in \Omega^{(c)}$
is an unbroken geodesic which is not of least energy, then $n = \nu m_{k+1}$ for an integer $\nu$,
and the index of $\gamma$ is at least $\lfloor(\nu - |c|)/4\rfloor$ (at least $0$ if $|c| > \nu$).
*Book:* pp. 147–148: $2\lambda \ge \sum_{a_h > a_j}(a_h - a_j - 2)$; then, supposing "for example"
that some $a_h$ is $-3$, $4\lambda \ge 2p \ge r + c$, where $r = n/m_k$. *Hidden hypotheses:* as in
V15.20, and the linear independence of the eigenvectors of different pairs. *Deviation (value
differs):* $4\lambda \ge \nu - |c|$ up to rounding, whichever sign the large $|a_h|$ has (V15.20).
*Deviation (restated):* as in V15.30. The geodesic is $J_k\exp(\pi tA)$ with $A = a_h\mathbf i$ on
the pieces $M_h$ and $\sum_h a_h = c$ (V15.35, V15.37), and some $|a_{h_0}| \ge 3$. If
$a_{h_0} \ge 3$, the isomorphisms $T_j : M_{h_0} \to M_j$ of V15.37 (iv), for the $j$ with
$a_j < 0$, give operators $D_j$ and elements $X_j = D_j\mathbf i - (D_j\mathbf i)^{\mathsf T}$ of
the isotropy algebra which commute with $\exp(\tau\pi A)$ at the $(a_{h_0} - a_j)/2 - 1$ parameters
$\tau = 2s/(a_{h_0} - a_j)$ in $(0, 1)$; V15.28 (iii) and the count of V15.20 give the bound. If
$a_{h_0} \le -3$, the same is done for $-A$. Only the pairs $(h_0, j)$ with $a_j$ of the sign
opposite to $a_{h_0}$ are used.

**V15.39 (Theorem 24.5 for each $n$, $k = 2, 6$; `Morse.isCentralI_iWordM`,
`Morse.omegaPhi_mem_omegaComp`, `Morse.omega_minPaths_bijective_two`,
`Morse.omegaPhi_bijective_two`, `Morse.theorem_24_5_two_six`, `Morse.omega_pi_equiv_two`).** Let
$k = 2$ or $k = 6$, let $J_1, \dots, J_{k+1}$ be an anticommuting family on $\mathbb R^n$,
$\nu = n/m_{k+1}$, and $c$ an integer. (i) For $J' \in \Omega_{k+1}(n)$, $\varphi(J')$ lies in
$\Omega_w$ with $w = -\pi\operatorname{tr}(J_k^{\mathsf T}J'\mathbf i)/2$; so
$\varphi(J') \in \Omega^{(c)}$ exactly when
$-\operatorname{tr}(J_k^{\mathsf T}J'\mathbf i) = m_{k+1}c$. (ii) For
$j + 2 \le \lfloor(\nu - |c|)/4\rfloor$, the inclusion $\Omega^d \cap \Omega^{(c)} \to \Omega^{(c)}$
induces a bijection on $\pi_j$ at every point. (iii) For $j + 3 \le \lfloor(\nu - |c|)/4\rfloor$ and
$J' \in \Omega_{k+1}(n)$ with $\varphi(J') \in \Omega^{(c)}$, $\varphi$ induces a bijection on
$\pi_{j+1}$ at $J'$, and there is a bijection
$\pi_{j+1}(\Omega_{k+1}(n), J') \cong \pi_{j+2}(\Omega_k(n), J_k)$. *Book:* p. 148: "the component
of $\Omega\Omega_k(n)$ is approximated up to higher and higher dimensions by the corresponding
component of $\Omega_{k+1}(n)$, as $n \to \infty$". *Hidden hypotheses:* Theorem 22.1 for one class
of paths (V13.16); which part of $\Omega_{k+1}(n)$ corresponds to $\Omega^{(c)}$. *Deviation
(restated):* V13.16 with V15.27, V15.35 and V15.38, with explicit ranges; bijections of pointed
sets. (ii) includes $\pi_0$; (iii) is stated in degrees $\ge 1$, where the open and closed set
$\Omega^{(c)}$ has the homotopy groups of the whole path space. The path components are V15.40.

**V15.40 (Theorem 24.5 for each $n$, $k = 2, 6$: path components;
`Morse.theorem_24_5_pi0_two_six`).** In the setting of V15.39, let
$\lfloor(\nu - |c|)/4\rfloor \ge 2$. (i) Every path in $\Omega^{(c)}$ can be joined, by a path in
$\Omega(N; J_k, -J_k)$, to $\varphi(J')$ for some $J' \in \Omega_{k+1}(n)$. (ii) If
$\varphi(J') \in \Omega^{(c)}$, then for every $J'' \in \Omega_{k+1}(n)$: $J'$ and $J''$ can be
joined in $\Omega_{k+1}(n)$ if and only if $\varphi(J')$ and $\varphi(J'')$ can be joined in
$\Omega(N; J_k, -J_k)$. *Book:* p. 146: $\Omega\Omega_k(n)$ has infinitely many components, while
the approximating subspace $\Omega_{k+1}(n)$ has only finitely many; p. 148: passing to the direct
limit, "a homotopy equivalence on each component". *Hidden hypotheses:* that in the limit $\varphi$
is a bijection on path components. *Deviation (narrower):* for a fixed $n$ only the classes with
$|c| \le \nu - 8$ are controlled. With V15.36 (every path has a class) and V15.41 (the class is
stable) this is what the limit needs; the limit itself is not formed.

**V15.41 (the structures on $\mathbb R^{16r}$, and stabilization; `Morse.bottJ`,
`Morse.isAnticommFamily_bottJ`, `Morse.stabEquiv`, `Morse.stab`, `Morse.stab_mem_omega`,
`Morse.stab_basePt`, `Morse.omegaPhi_stab`, `Morse.omegaLabel_stab`,
`Morse.omegaPhi_bottJ_mem_omegaComp`).** On $\mathbb R^{16r} = \mathbb R^{16} \otimes \mathbb R^r$
let $J_\alpha = J'_\alpha \oplus \dots \oplus J'_\alpha$ ($r$ summands), where $J'_1, \dots, J'_8$
are the structures of V15.9 on $\mathbb R^{16}$; $J_1, \dots, J_8$ is an anticommuting family.
Identify $\mathbb R^{16r} \oplus \mathbb R^{16}$ with $\mathbb R^{16(r+1)}$, the new block last, and
put $s(X) = X \oplus J'_k$ (for $k = 0$: $X \oplus I_{16}$). Then: (i) for $k \le 8$, $s$ maps
$\Omega_k(16r)$ into $\Omega_k(16r + 16)$ and carries $J_k$ to $J_k$; (ii) for $k \le 7$ and
$J' \in \Omega_{k+1}(16r)$,
$\varphi(J' \oplus J'_{k+1})(t) = \varphi(J')(t) \oplus \bigl(\cos(\pi t)\,J'_k + \sin(\pi t)\,J'_{k+1}\bigr)$
for all $t$; (iii) for $k = 2, 6$ and every matrix $X$ on $\mathbb R^{16r}$,
$\operatorname{tr}\bigl(J_k^{\mathsf T}(X \oplus J'_{k+1})\,\mathbf i\bigr) = \operatorname{tr}(J_k^{\mathsf T}X\mathbf i)$,
the left side computed on $\mathbb R^{16(r+1)}$, so that by V15.39 (i) the class $c$ of
$\varphi(J')$ does not change under stabilization; (iv) for $k = 2, 6$,
$\varphi(J_{k+1}) \in \Omega^{(0)}$. *Book:* p. 138: $\Omega_k(n)$ is imbedded in $\Omega_k(n + n')$
by $J \mapsto J \oplus J'_k$; "It is not difficult to see that the inclusions
$\Omega_{k+1}(n) \to \Omega\Omega_k(n)$ give rise, in the limit, to inclusions
$\Omega_{k+1} \to \Omega\Omega_k$"; p. 139: $n = 16r$. *Hidden hypotheses:* the compatibility (ii)
of $\varphi$ with the imbeddings; for $k = 2, 6$, that the class is stable (iii). *Deviation
(narrower):* the direct limits $\Omega_k$, the limit map, and the naturality under stabilization of
the bijections of V15.31 and V15.39 are not formalized; V15.45 does not need them.

**V15.42 (Lemma 24.6 (8): $\Omega_8(16r)$ is homeomorphic to $O(r)$; `Morse.W16`,
`Morse.eq_of_commute_bott16`, `Morse.qOf`, `Morse.eq_qOf_of_commute`, `Morse.omegaEightHomeomorph`,
`Morse.omegaEightHomeomorph_basePt`).** (i) A $16 \times 16$ matrix that commutes with
$J'_1, \dots, J'_7$ is $b\,I + c\,W$ for real $b$, $c$, where
$W = 1 \otimes 1 \otimes 1 \otimes \tau$ in the notation of V15.9. (ii) With
$P_\pm = \tfrac12(1 \pm W)$ and $q(U, V) = P_+ \otimes U + P_- \otimes V$ for $r \times r$ matrices
$U$, $V$: every matrix on $\mathbb R^{16r}$ that commutes with $J_1, \dots, J_7$ (V15.41) is
$q(U, V)$ for some $U$, $V$. (iii) $\Omega_8(16r)$, for the structures of V15.41, is homeomorphic to
$O(r)$: $J$ corresponds to the $U$ with $-J_8J = q(U, U^{\mathsf T})$, and $U$ to
$J_8\,q(U, U^{\mathsf T})$; the base point $J_8$ corresponds to $I$. *Book:* pp. 141–142, Lemma 24.6
(8): $\Omega_8(16r)$ can be identified with the set of all real isometries from $X_1$ to $X_2$,
through $J_7J_8$; "Thus we see that $\Omega_8(16r)$ is diffeomorphic to the orthogonal group
$O(r)$". *Hidden hypotheses:* $\dim X_1 = \dim X_2 = r$ (V15.12), and that the isometry "determines
$J_8$ uniquely". *Deviation (restated):* Milnor's $X_1$, $X_2$ are replaced by the commutant of
$J_1, \dots, J_7$: for $J \in \Omega_8(16r)$, $-J_8J$ commutes with $J_1, \dots, J_7$, and the
conditions on $q(U, V)$ are that $U$ be orthogonal and $V = U^{\mathsf T}$. *Deviation (narrower):*
a homeomorphism, not a diffeomorphism, and for the explicit structures. The other parts of Lemma
24.6 remain as in V15.11–V15.12. *Proof of (i):* the $256$ Kronecker words in
$1, \sigma, \tau, \kappa$ form a basis of the $16 \times 16$ matrices, each word commutes or
anticommutes with each $J'_\alpha$, and a finite check shows that only $1$ and $W$ commute with all
seven.

**V15.43 (Bott's chain at $n = 16r$; `Morse.bott_chain`, `Morse.bott_chain_of_le`,
`Morse.bott_periodicity_finite`, `Morse.bott_periodicity_finite_of_le`).** For the structures of
V15.41, every $i \ge 0$ and every $r \ge 2i + 7$, there are bijections
$\pi_i(\Omega_8(16r), J_8) \cong \pi_{i+8}(O(16r), I)$ and
$\pi_i(O(r), I) \cong \pi_{i+8}(O(16r), I)$. *Book:* p. 138, Theorem 24.5:
$\pi_hO \cong \pi_{h-1}\Omega_1 \cong \pi_{h-2}\Omega_2 \cong \dots \cong \pi_1\Omega_{h-1}$; p.
142: "Combining this fact with Theorem 24.5", for $\Omega_8 \cong O$. *Hidden hypotheses:* the base
points along the chain; for $k = 2, 6$ the base point $J_{k+1}$ must lie in the class $c = 0$
(V15.41 (iv)). *Deviation (restated):* eight steps at the finite stage $n = 16r$, each at the base
points: V15.31 for $k = 7, 5, 4, 3, 1$; V15.39 with $c = 0$ for $k = 6$ and $k = 2$, used in degrees
$\ge 1$ only; V15.32 for $k = 0$; then V15.42. The ranges they need, $i + 2 \le r - 1$,
$i + 3 \le \lfloor r/2\rfloor$, $i + 6 \le 2r - 1$, $i + 7 \le r$, $i + 8 \le 4r - 1$ and
$i + 11 \le 16r$, all follow from $2i + 7 \le r$. Bijections of sets.

**V15.44 (stability of the homotopy groups of $O(n)$ and $U(n)$;
`Morse.Homotopy.sphereConnected_real`, `Morse.Homotopy.nonempty_pi_unitary_equiv_of_le`,
`Morse.Homotopy.nonempty_pi_unitary_equiv_stable`).** Let $\mathbb K = \mathbb R$ with $d = 1$, or
$\mathbb K = \mathbb C$ with $d = 2$, and let $U_{\mathbb K}(m)$ be $O(m)$, resp. $U(m)$. If
$i + 2 \le dm + d - 1$ and $i + 2 \le dm' + d - 1$, there is a bijection
$\pi_i(U_{\mathbb K}(m), I) \cong \pi_i(U_{\mathbb K}(m'), I)$. So $\pi_iO(n) \cong \pi_iO(n')$
whenever $i + 2 \le n$ and $i + 2 \le n'$, and $\pi_iU(n) \cong \pi_iU(n')$ whenever $i < 2n$ and
$i < 2n'$. *Book:* for $U$, pp. 128–129, proof of Lemma 23.4:
$\pi_{i-1}U(m) \cong \pi_{i-1}U(m + 1)$ for $i \le 2m$, from the fibration
$U(m) \to U(m + 1) \to S^{2m+1}$. For $O$ the book has no such statement: $\pi_iO$ is the homotopy
group of the direct limit (p. 138). *Hidden hypotheses:* for $O$, the fibration
$O(n) \to O(n + 1) \to S^n$ and $\pi_iS^n = 0$ for $i < n$. *Deviation (not in the book, for $O$):*
it is what allows Theorem 24.7 to be stated without the limit (V15.45). The proof is that of V14.25,
over $\mathbb R$ and $\mathbb C$ at once.

**V15.45 (Theorem 24.7 in the stable range; `Morse.theorem_24_7`).** For every $i \ge 0$,
$n \ge i + 2$ and $n' \ge i + 10$ there is a bijection $\pi_i(O(n), I) \cong \pi_{i+8}(O(n'), I)$.
*Book:* p. 142, Theorem 24.7 (Bott): the infinite orthogonal group $O$ has the same homotopy type as
its own 8-th loop space; hence $\pi_iO$ is isomorphic to $\pi_{i+8}O$ for $i \ge 0$. *Hidden
hypotheses:* for the homotopy equivalence, that $\Omega_{k+1}$ and $\Omega\Omega_k$ have the
homotopy type of a CW-complex (p. 146, "it can be shown"). *Deviation (narrower):* a bijection
between homotopy groups of finite orthogonal groups in the stable range, where $\pi_iO(n)$ does not
depend on $n \ge i + 2$ (V15.44) and is Milnor's $\pi_iO$. The limit group $O$, the homotopy
equivalence $O \simeq \Omega^8O$, the statement that the bijection is a group isomorphism, and the
table of $\pi_iO$ (p. 142) are not formalized. *Proof:* with $r = 2i + 7$,
$\pi_iO(n) \cong \pi_iO(r) \cong \pi_{i+8}O(16r) \cong \pi_{i+8}O(n')$, by V15.44, V15.43 and
V15.44.

**V15.46 (the periodicity theorem for the unitary group in the stable range;
`Morse.periodicity_theorem_stable`).** For $i < 2n$ and $i + 2 < 2n'$ there is a bijection
$\pi_i(U(n), I) \cong \pi_{i+2}(U(n'), I)$. *Book:* p. 129, the Periodicity Theorem of §23:
$\pi_{i-1}U \cong \pi_{i+1}U$ for $i \ge 1$, the stable groups being $\pi_{i-1}U = \pi_{i-1}U(m)$
for $i \le 2m$. *Hidden hypotheses:* none. *Deviation (restated):* V14.28 gives
$\pi_{i-1}U(m) \cong \pi_{i+1}U(2m)$ for $1 \le i \le 2m$; with the stability of V15.44 on both
sides the statement no longer refers to a single $m$, and holds between any two groups in the stable
range. A bijection of sets; the group isomorphisms of Chapter 14 are V14.28 and V14.30.

### What is not verified in this chapter

- **The limit spaces and the homotopy equivalences** (pp. 138, 142, 146): the direct limits
  $\Omega_k$ and $O$ with their topology; the limit maps $\Omega_{k+1} \to \Omega\Omega_k$; that
  these spaces have the homotopy type of CW-complexes; Whitehead's theorem (in Mathlib only in an
  abstract model-category form); hence Theorem 24.5 as a homotopy equivalence and Theorem 24.7 as
  $O \simeq \Omega^8O$. The naturality under stabilization of the bijections of V15.31 and V15.39 is
  not formalized either; Theorem 24.7 is obtained in the stable range instead (V15.45). - **Group
  structures:** the bijections of V15.31, V15.32, V15.39, V15.43 and V15.45 are not shown to be
  homomorphisms. - **The table** of $\pi_iO$ and $\pi_iSp$ (p. 142), which Milnor leaves to the
  reader, and the statements about $Sp$ on that page. - **Lemma 24.4 beyond V15.23, V15.25 and
  V15.26:** $\Omega_k(n)$ as a submanifold of $O(n)$ (each stratum is a submanifold of
  $M_n(\mathbb R)$); that the reflection is an isometry and the components are symmetric spaces
  (V15.5 is the algebraic part). Of Lemma 24.1: the block normal form of a skew matrix (p. 134),
  which is not needed, and the Remark $\Omega_1(n) \cong O(n)/U(n/2)$ (p. 133). - **The rest of
  Lemma 24.6** (pp. 139–142): the identifications of $\Omega_2(n)$ with $U(n/2)/Sp(n/4)$ and of
  $\Omega_3, \dots, \Omega_7(16r)$ with Grassmannians, $Sp(2r)$, $Sp(2r)/U(2r)$ and $U(2r)/O(2r)$,
  the Assertion on the largest component of $\Omega_7(16r)$, and the footnote
  $\Omega_k(16r) \cong \Omega_{k-8}(r)$ for $k > 8$ (p. 142). V15.11–V15.12 are their algebraic
  parts; (8) is V15.42. - **The exact index of a geodesic:** the eigenvalues of $K_A$ on
  $\Omega_k(n)$ (which need the curvature of a totally geodesic submanifold and Theorem 20.5 there)
  and the formula of Lemma 24.2 for the geodesics of $O(2m)$. For geodesics only the lower bounds
  V15.30 and V15.38 are proved; V15.3, V15.19 and V15.20 remain counts from Milnor's spectra. -
  **Theorem 24.5 for $k = 2, 6$ at a fixed $n$ beyond the classes $|c| \le n/m_{k+1} - 8$**
  (V15.40); and Milnor's remark that $\Omega_k(n)$ has an infinite cyclic fundamental group (p.
  146), which is not needed. - **Lemma 24.8 beyond V15.16–V15.17:** the two non-isomorphic classes
  for $k = 3$ and $k = 7$, the cases $k > 8$ and the relation $m_{k+8} = 16m_k$ as a theorem, and
  the isometric form of the isomorphism; the Hurwitz–Radon count and Adams's theorem (p. 144).

---

## 17. Appendix (Milnor pp. 149–153): partly verified

Milnor's Appendix gives an alternative final step for the proof of Theorem 17.3. For subspaces
$X_0 \subseteq X_1 \subseteq \cdots$ of a space $X$ it defines the telescope $X_\Sigma \subseteq X
\times \mathbb R$ and calls $X$ the homotopy direct limit of $\{X_i\}$ if the projection
$X_\Sigma \to X$ is a homotopy equivalence (p. 149). Examples 1–3 (pp. 149–150) give two sufficient
conditions (the interiors of the $X_i$ cover a paracompact $X$; the $X_i$ are subcomplexes of a
CW-complex) and a counterexample. Theorem A (p. 150) says that a map of homotopy direct limits that
carries each $X_i$ into $Y_i$ by a homotopy equivalence is a homotopy equivalence; it is proved by
reduction to the map of telescopes, in two cases (pp. 150–153), and gives the final step of 17.3.
The Corollary (p. 153) says that a homotopy direct limit of spaces of the homotopy type of
CW-complexes has that homotopy type. Verified, for arbitrary topological spaces: telescopes,
homotopy direct limits, and the facts Milnor uses about them without comment ((T1)–(T3) and Lemmas
2.1–2.2 of the exposition); Examples 1 and 3; Milnor's proof of Theorem A in both cases, with the
misprint $(4 - 3t)u$ corrected to $(4t - 3)u$; **Theorem A exactly as Milnor states it, with no
closedness hypothesis** (VA.15); the Corollary, with a mapping telescope in place of a CW-complex;
and the topological part of Theorem 17.3, for a space exhausted by sublevel sets of a continuous
function. The proof departs from Milnor's in one respect. **Milnor's maps are defined strip by
strip**, which makes them continuous only when the sets are closed (T3): Case 1 as written needs
the $X_i$ closed; Case 2 applies Case 1 only to truncations of telescopes, which are always closed,
and pastes only one map, $G$, on the telescope of the $Y_i$, so his proof of Theorem A needs only
the $Y_i$ closed (VA.12); and the same proof run on mapping
telescopes, where pasting is automatic, needs no closedness at all (VA.15). **Not verified:**
Example 2 (Whitehead's theorem), a counterexample for the Remark, and the CW structure of
mapping telescopes (cellular approximation), so that "CW-complex" becomes a mapping telescope of
iterated adjunction spaces (the list at the end). Lean: `Morse/Appendix/` — `Telescope.lean` (630
lines), `Examples.lean` (239), `TheoremA.lean` (765), `MappingTelescope.lean` (517),
`MonotoneUnion.lean` (569).

**Conventions.** Spaces are arbitrary topological spaces, with no separation axiom unless one is
stated; maps are continuous; subsets carry the subspace topology; $I = [0, 1]$. Sequences are
indexed from $0$. A sequence of subsets $X_0, X_1, \dots$ of $X$ is *monotone* if
$X_0 \subseteq X_1 \subseteq \cdots$; Milnor's sequences always are, and most statements below
assume it. Homotopies of maps into a subset take values in that subset.

**VA.1 (homotopy equivalences; `Morse.IsHomotopyEquiv`, `Morse.IsHomotopyEquiv.comp`,
`Morse.IsHomotopyEquiv.of_homotopic`, `Morse.IsHomotopyEquiv.of_inverse`,
`Morse.IsHomotopyEquiv.of_leftInv_rightInv`, `Morse.restrictTo`).** A map $f : X \to Y$ is a
*homotopy equivalence* if there is a map $g : Y \to X$ with $gf \simeq \mathrm{id}_X$ and
$fg \simeq \mathrm{id}_Y$. A composite of homotopy equivalences is one; a map homotopic to a
homotopy equivalence is one; a homotopy inverse is one; and a map with a left homotopy inverse and
a right homotopy inverse is a homotopy equivalence. If $f$ carries $A \subseteq X$ into
$B \subseteq Y$, $f|A : A \to B$ is its restriction. *Book:* p. 22, Assertion: if a map $F$ has a
left homotopy inverse $L$ and a right homotopy inverse $R$, then $F$ is a homotopy equivalence;
p. 153 refers to it ("compare page 22"). *Hidden hypotheses:* none. *Deviation (not in the
book):* the closure properties, used throughout without comment.

**VA.2 (the telescope and homotopy direct limits; `Morse.telescope`, `Morse.mem_telescope_iff`,
`Morse.mem_telescope_of_le`, `Morse.stripMap`, `Morse.telescopeProj`,
`Morse.IsHomotopyDirectLimit`).** For subsets $X_0, X_1, \dots$ of $X$, the *telescope* is
$X_\Sigma = \bigcup_n X_n \times [n, n + 1] \subseteq X \times \mathbb R$, with the subspace
topology; the $n$-th *strip* is the map $X_n \times [0, 1] \to X_\Sigma$, $(x, t) \mapsto
(x, n + t)$; $p : X_\Sigma \to X$ is $p(x, \tau) = x$; and $X$ is the *homotopy direct limit* of
$\{X_i\}$ if $p$ is a homotopy equivalence. **(T1)** For a monotone sequence, $(x, \tau) \in
X_\Sigma$ iff $x \in X_n$ for some integer $n \ge 0$ with $n \le \tau$; so $(x, \tau) \in X_\Sigma$
and $\tau' \ge \tau$ give $(x, \tau') \in X_\Sigma$. *Book:* p. 149: for subspaces $X_0 \subset X_1
\subset \cdots$, the infinite union $X_\Sigma = X_0 \times [0, 1] \cup X_1 \times [1, 2] \cup
\cdots$, "to be topologized as a subset of $X \times \mathbb R$"; Definition: $X$ is the homotopy
direct limit of $\{X_i\}$ if $p : X_\Sigma \to X$, $p(x, \tau) = x$, is a homotopy equivalence.
*Hidden hypotheses:* none. *Deviation (not in the book):* (T1), used without comment.

**VA.3 ((T3) pasting along the strips; `Morse.continuous_of_stripMap`, `Morse.telescopeLift`,
`Morse.telescopeDesc`, `Morse.telescopeHomotopy`).** If every $X_n$ is closed in $X$, then for every
space $P$ a function $F$ on $P \times X_\Sigma$ is continuous as soon as each $(p, x, t) \mapsto
F(p, (x, n + t))$ is continuous on $P \times X_n \times [0, 1]$. Hence, for a monotone sequence of
closed sets, maps $\Phi_n : P \times X_n \times [0, 1] \to Z$ with $\Phi_{n+1}(p, x, 0) =
\Phi_n(p, x, 1)$ define a continuous map $P \times X_\Sigma \to Z$, $(p, (x, n + t)) \mapsto
\Phi_n(p, x, t)$; in particular maps $X_\Sigma \to Z$, and homotopies between them, may be given
strip by strip. *Book:* every map and homotopy on a telescope in the proof of Theorem A
(pp. 151–153) is given strip by strip, by formulas in $(x, n + t)$, $0 \le t \le 1$. *Hidden
hypotheses:* closedness of the $X_n$, which Milnor never states; then the strips are closed in
$X_\Sigma$ and form a locally finite family. *Deviation (not in the book):* stated and proved as a
lemma.

**VA.4 (the map of telescopes, and "clearly sufficient"; `Morse.telescopeMap`,
`Morse.telescopeProj_comp_telescopeMap`, `Morse.IsHomotopyEquiv.of_telescopeMap`).** If $f : X \to Y$
carries each $X_n$ into $Y_n$, then $f_\Sigma(x, \tau) = (f(x), \tau)$ is a map $X_\Sigma \to
Y_\Sigma$ with $p_Yf_\Sigma = fp_X$. If $X$ and $Y$ are the homotopy direct limits of $\{X_i\}$ and
$\{Y_i\}$ and $f_\Sigma$ is a homotopy equivalence, then so is $f$. *Book:* p. 150: define
$f_\Sigma(x, t) = (f(x), t)$; "it is clearly sufficient to prove that $f_\Sigma$ is a homotopy
equivalence". *Hidden hypotheses:* none; neither closedness nor monotonicity is needed. *Proof:*
$f \simeq fp_Xs = p_Yf_\Sigma s$ for a homotopy inverse $s$ of $p_X$.

**VA.5 ((T2) truncations; `Morse.truncation`, `Morse.isClosed_truncation`,
`Morse.monotone_truncation`, `Morse.truncIncl`, `Morse.truncProj`, `Morse.isHomotopyEquiv_truncIncl`,
`Morse.isHomotopyEquiv_truncProj`, `Morse.level_le_of_stripMap`).** The truncation $X^n_\Sigma =
\{(x, \tau) \in X_\Sigma : \tau \le n\}$ is closed in $X_\Sigma$, and $X^0_\Sigma \subseteq
X^1_\Sigma \subseteq \cdots$, whatever the $X_i$. For a monotone sequence, $x \mapsto (x, n)$ is a
homotopy equivalence $X_n \to X^n_\Sigma$ with homotopy inverse $(x, \tau) \mapsto x$, the homotopy
raising $\tau$ to $n$; and a function $F$ on $X_\Sigma$ that sends the $n$-th strip to levels
$\le n + 1$ and $X_n \times \{n\}$ to levels $\le n$ sends each $X^m_\Sigma$ to levels $\le m$.
*Book:* p. 152: $X^n_\Sigma = X_0 \times [0, 1] \cup \dots \cup X_{n-1} \times [n - 1, n] \cup X_n
\times [n]$, which "contains $X_n \times [n]$ as deformation retract"; $Gf_\Sigma$ carries
$X^n_\Sigma$ into itself. *Hidden hypotheses:* none; no closedness. *Deviation (not in the book):*
proofs of the two facts Milnor states.

**VA.6 (Lemmas 2.1 and 2.2 of the exposition; `Morse.isHomotopyDirectLimit_of_level`,
`Morse.isHomotopyDirectLimit_truncation`).** (i) For a monotone sequence, if $f : X \to \mathbb R$
is continuous, $f \ge 0$, and $f(x) \ge n + 1$ whenever $x \notin X_n$, then $X$ is the homotopy
direct limit of $\{X_i\}$. (ii) For any sequence, $X_\Sigma$ is the homotopy direct limit of its
truncations $\{X^n_\Sigma\}$. *Book:* p. 149, in Example 1: $x \mapsto (x, f(x))$ maps $X$
homeomorphically onto a subset of $X_\Sigma$ "which is clearly a deformation retract"; (ii) is used
without mention at the end of Case 2 (p. 153). *Hidden hypotheses:* (ii), for Case 2 (VA.11).
*Deviation (not in the book):* (i) needs no paracompactness once $f$ is given. *Proof:* (i) the
homotopy $(x, (1 - s)f(x) + s\tau)$ stays in $X_\Sigma$ by (T1); (ii) is (i) with
$f(x, \tau) = \tau + 1$.

**VA.7 (Example 1, and sublevel sets; `Morse.example1`, `Morse.isHomotopyDirectLimit_sublevel`).**
(i) Let $X$ be paracompact and Hausdorff, and $X_0 \subseteq X_1 \subseteq \cdots$ with every point
of $X$ in the interior of some $X_i$. Then $X$ is the homotopy direct limit of $\{X_i\}$. (ii) Let
$E : X \to \mathbb R$ be continuous, on any space $X$, and $a_0 \le a_1 \le \cdots$ with
$a_i \to \infty$. Then $X$ is the homotopy direct limit of the sublevel sets
$\{x : E(x) \le a_i\}$. *Book:* p. 149, Example 1: if each point of $X$ lies in the interior of
some $X_i$ and $X$ is paracompact, a partition of unity gives $f : X \to \mathbb R$ with
$f(x) \ge i + 1$ for $x \notin X_i$ and $f \ge 0$, and $X$ is a homotopy direct limit. *Hidden
hypotheses:* Hausdorff: Mathlib's partitions of unity need a normal space, and Milnor's
"paracompact" is read with the Hausdorff axiom. *Deviation (stronger):* (ii) needs no
paracompactness; it covers the sublevel sets of the energy in Theorem 17.3, where Milnor uses
Example 1 and the paracompactness of a metric space. *Proof:* (i) $f = \sum_ii\,\varphi_i$ for a
partition of unity $\{\varphi_i\}$ subordinate to $\{\operatorname{int}X_i\}$, then VA.6 (i);
(ii) $f = \sum_j\min(1, \max(0, E - a_j + 1))$, locally a finite sum.

**VA.8 (Example 3; `Morse.example3Set`, `Morse.monotone_example3Set`, `Morse.isClosed_example3Set`,
`Morse.iUnion_example3Set`, `Morse.example3`).** Let $X_n = \{0\} \cup [\frac1{n+1}, 1] \subseteq
[0, 1]$. The $X_n$ are closed and increasing, with union $[0, 1]$, and $[0, 1]$ is not the homotopy
direct limit of $\{X_n\}$. *Book:* p. 150, Example 3: the unit interval $[0, 1]$ is not the
homotopy direct limit of the sequence of closed subsets $[0] \cup [1/i, 1]$; no proof. *Hidden
hypotheses:* none. *Deviation (restated):* indexed from $0$. *Proof:* $\{0\} \times [0, \infty)$ is
open and closed in $X_\Sigma$, so $X_\Sigma$ is not connected, while a homotopy inverse $s$ of $p$
would join $(0, 0)$ to $s(0)$, $s(0)$ to $s(1)$ and $s(1)$ to $(1, 0)$ by paths.

**VA.9 (Milnor's maps $h_1$ and their inverse $g$; `Morse.reparam`, `Morse.reparam_homotopic`,
`Morse.scaleMap`, `Morse.IsMilnorMap`, `Morse.IsMilnorMap.fix`, `Morse.milnorInv`,
`Morse.loopFun`, `Morse.milnorH`, `Morse.milnorK`, `Morse.isHomotopyEquiv_of_milnorMap`).** Let
$X_0 \subseteq X_1 \subseteq \cdots$ be closed in $X$. (i) For a map $\rho : I \to I$ with
$\rho(0) = 0$ and $\rho(1) = 1$, $(x, n + t) \mapsto (x, n + \rho(t))$ is homotopic to the
identity of $X_\Sigma$; in particular so is $R_c(x, n + t) = (x, n + \min(ct, 1))$, $c \ge 1$.
(ii) Let $\psi : X_\Sigma \to X_\Sigma$ be a map with $\psi(x, n + t) = (x, n + 2t)$ for
$t \le \frac12$ and $\psi(x, n + t)$ at level $n + 1$ for $t \ge \frac12$. Then $\psi$ fixes the
points at integer levels, and it is a homotopy equivalence, with homotopy inverse Milnor's $g$:
$g(x, n + t) = (x, n + 2t)$ for $t \le \frac12$ and $\psi(x, n + \frac32 - t)$ for
$t \ge \frac12$. *Book:* p. 151: any map $h_1$ with $h_1(x, n + t) = (x, n + 2t)$ for
$t \le \frac12$ and $h_1(x, n + t) \in X_{n+1} \times [n + 1]$ for $t \ge \frac12$ is a homotopy
equivalence, with homotopy inverse $g$, well defined since $h_1(x, n + \frac12) = h_1(x, n + 1) =
(x, n + 1)$; $h_1g \simeq \mathrm{id}$ by a homotopy $H_u$, $0 \le u \le \frac12$, ending at
$H_{1/2}(x, n + t) = (x, n + \min(4t, 1))$, "clearly" homotopic to the identity; p. 152:
$gh_1 \simeq \mathrm{id}$ "by a completely analogous argument". *Hidden hypotheses:* the $X_n$
closed (VA.3); the formula for $h_1g$ uses that $h_1$ fixes the integer levels. *Proof:* with $u$
rescaled to $[0, 1]$, Milnor's $H_u$ is the single formula $(x, n + 4t)$ for $t \le \frac14$ and
$\psi(x, n + \frac12 + \frac\mu2)$ for $t \ge \frac14$, $\mu = \min(4t - 1, 1 - u, 2 - 2t)$; the
analogous homotopy for $g\psi$ takes $\mu = \max(2 - 4t, 2t - 1, u)$; both end at $R_4$, homotopic to
the identity by (i).

**VA.10 (Case 1 of Theorem A; `Morse.case1Fun`, `Morse.case1Family`, `Morse.case1Map_zero`,
`Morse.case1Map_one`, `Morse.theoremA_case1`).** Let $X_0 \subseteq X_1 \subseteq \cdots$ be closed
in $X$, and $\varphi : X \to X$ a map carrying each $X_n$ into itself by a map $\varphi_n$
homotopic, in $X_n$, to the identity of $X_n$. Then $\varphi_\Sigma$ is a homotopy equivalence. The
steps: with homotopies $h^n_u$ from $\varphi_n$ to the identity, $h_u(x, n + t)$ is
$(h^n_u(x), n + 2t)$ for $t \le \frac12$, $(h^n_{(3-4t)u}(x), n + 1)$ for $\frac12 \le t \le \frac34$
and $(h^{n+1}_{(4t-3)u}(x), n + 1)$ for $\frac34 \le t \le 1$; $(u, z) \mapsto h_u(z)$ is
continuous; $h_0 = \varphi_\Sigma \circ R_2$; and $h_1$ is a map as in VA.9 (ii). *Book:*
pp. 150–152, Case 1: $X_i = Y_i$ and each $f_i : X_i \to Y_i$ homotopic to the identity; the third
line of $h_u$ is printed $h^{n+1}_{(4-3t)u}$; "taking $u = 0$ this defines a map $h_0$ which is
clearly homotopic to $f_\Sigma$". *Hidden hypotheses:* the $X_n$ closed, for the continuity of
$h_u$ and of $g$ (VA.3); without it Milnor's $g$ can be discontinuous (the exposition's example:
$X = [0, 1]$, $X_0 = (0, 1]$). This part does not use that $X$ is a homotopy direct limit.
*Deviation (value differs):* the third line is $h^{n+1}_{(4t-3)u}$; the printed $(4 - 3t)u$ is a
misprint, giving $h^{n+1}_{7u/4}$ at $t = \frac34$ where continuity needs $h^{n+1}_0$. *Proof:*
Milnor's, with $h_0 \simeq \varphi_\Sigma$ by VA.9 (i).

**VA.11 (Case 2: $f_\Sigma$ is a homotopy equivalence; `Morse.isHomotopyEquiv_of_truncation`,
`Morse.homotopic_square`, `Morse.case2Inv`, `Morse.case2Inv_level`, `Morse.theoremA_telescope`).**
(i) Let $X_0 \subseteq X_1 \subseteq \cdots$ be a monotone sequence, closed or not, and
$F : X_\Sigma \to X_\Sigma$ a map carrying each truncation $X^m_\Sigma$ into itself, with
$F(x, m) = (e_m(x), m)$ for maps $e_m : X_m \to X_m$ homotopic to the identity. Then $F$ is a
homotopy equivalence. (ii) Let $X_0 \subseteq X_1 \subseteq \cdots$ in $X$ and $Y_0 \subseteq Y_1
\subseteq \cdots$ in $Y$, the $Y_n$ closed, and let $f : X \to Y$ carry each $X_n$ into $Y_n$ by a
homotopy equivalence $f_n$. Then $f_\Sigma : X_\Sigma \to Y_\Sigma$ is a homotopy equivalence.
*Book:* pp. 152–153, Case 2: "now let $X$ and $Y$ be arbitrary"; with homotopy inverses $g_n$ of the
$f_n$, $i_ng_n \simeq g_{n+1}f_{n+1}i_ng_n = g_{n+1}j_nf_ng_n \simeq g_{n+1}j_n$; with a homotopy
$h^n_u$ from $i_ng_n$ to $g_{n+1}j_n$, $G(y, n + t) = (g_n(y), n + 2t)$ for $t \le \frac12$ and
$(h^n_{2t-1}(y), n + 1)$ for $t \ge \frac12$; $Gf_\Sigma$ carries $X^n_\Sigma$ into itself by a
map homotopic to the identity, so "we can apply Case 1 to the sequence $\{X^n_\Sigma\}$, and
conclude that $Gf_\Sigma$ is a homotopy equivalence"; similarly $f_\Sigma G$; so $f_\Sigma$ has a
left and a right homotopy inverse (VA.1). *Hidden hypotheses:* the $Y_n$ closed, for the continuity
of $G$ (VA.3); the return from Case 1, which is about the induced map of the telescope of
$\{X^n_\Sigma\}$, to $Gf_\Sigma$ itself needs $X_\Sigma$ to be the homotopy direct limit of its
truncations (VA.6 (ii)); that $Gf_\Sigma$ on $X^m_\Sigma$ is homotopic to the identity is the chain
$\varphi \simeq \varphi\iota r = \iota(g_mf_m)r \simeq \iota r \simeq \mathrm{id}$, with $\iota$, $r$
the maps of (T2) (VA.5). *Deviation (narrower):* the $Y_n$ closed, where Milnor's Case 2 has no
hypothesis. *Deviation (stronger):* no homotopy direct limit hypothesis, and no closedness of the
$X_n$: Case 1 is applied only to the truncations $X^m_\Sigma$ and $Y^m_\Sigma$, which are always
closed (VA.5).

**VA.12 (Theorem A, by Milnor's proof; `Morse.theoremA`).** Let $X$ be the homotopy direct limit of
$X_0 \subseteq X_1 \subseteq \cdots$ and $Y$ that of $Y_0 \subseteq Y_1 \subseteq \cdots$, the $Y_i$
closed in $Y$, and let $f : X \to Y$ carry each $X_i$ into $Y_i$ by a homotopy equivalence
$f_i = f|X_i : X_i \to Y_i$. Then $f$ is a homotopy equivalence. *Book:* p. 150, Theorem A, with no
closedness hypothesis. *Hidden hypotheses:* Milnor's proof needs the $Y_i$ closed (VA.11), and
only these. *Deviation (narrower):* the $Y_i$ closed; this is removed in VA.15. *Proof:* VA.11 (ii)
and VA.4.

**VA.13 (the mapping telescope; `Morse.MapTelRel`, `Morse.MappingTelescope`,
`Morse.MappingTelescope.mk`, `Morse.MappingTelescope.mk_one`, `Morse.MappingTelescope.desc`,
`Morse.MappingTelescope.lift`, `Morse.MappingTelescope.homotopy`, `Morse.MappingTelescope.level`,
`Morse.MappingTelescope.trunc`, `Morse.MappingTelescope.isClosed_trunc`,
`Morse.MappingTelescope.isHomotopyDirectLimit_trunc`, `Morse.MappingTelescope.push`,
`Morse.MappingTelescope.mk_zero_injective`, `Morse.MappingTelescope.isInducing_mk_zero`,
`Morse.MappingTelescope.levelIncl`, `Morse.MappingTelescope.levelRetract`,
`Morse.MappingTelescope.isHomotopyEquiv_levelIncl`).** For a
sequence of spaces and maps $K_0 \xrightarrow{c_0} K_1 \xrightarrow{c_1} \cdots$, the *mapping
telescope* $T$ is the quotient of the disjoint union of the blocks $K_n \times [0, 1]$ by
$(k, 1)_n \sim (c_n(k), 0)_{n+1}$, with the quotient topology; $(k, t)_n$ is at level $n + t$, a
continuous function on $T$. Maps out of $T$, and out of $P \times T$ for a locally compact $P$ (for
homotopies, $P = I$), may be given block by block, compatibly with the gluing, with no closedness
condition. The truncations $T_n = \{\text{level} \le n\}$ are closed and increasing, and $T$ is the
homotopy direct limit of $\{T_n\}$; $k \mapsto (k, 0)_n$ is an embedding $K_n \to T$ and a homotopy
equivalence $K_n \to T_n$. *Book:* not in the book; the exposition's proof of the Corollary uses it.
*Hidden hypotheses:* none. *Deviation (not in the book):* the device that removes the closedness
hypotheses (VA.15) and replaces a union of complexes that are not subspaces of one space (VA.16,
VA.17). *Proof:* the product of a quotient map with a locally compact space is a quotient map; the
homotopy inverse of $K_n \to T_n$ reads off the point reached by pushing each point of $T_n$ up to
level $n$ along the maps $c_m$, and is continuous because $K_n \to T$ is an embedding; $T$ is a
homotopy direct limit by VA.6 (i) with $f = \text{level} + 1$.

**VA.14 (the mapping telescope of the inclusions; `Morse.subspaceFunctor`,
`Morse.telescopeComparison`, `Morse.telescopeComparisonHomeomorph`,
`Morse.isHomotopyEquiv_telescopeComparison`, `Morse.telescopeProj'`,
`Morse.isHomotopyEquiv_telescopeProj'`).** Let $X_0 \subseteq X_1 \subseteq \cdots$ be subsets of
$X$, not necessarily closed, and $T$ the mapping telescope of the inclusions. The map $T \to
X_\Sigma$, $(x, t)_n \mapsto (x, n + t)$, is a homotopy equivalence, and a homeomorphism when the
$X_n$ are closed. If $X$ is the homotopy direct limit of $\{X_i\}$, the map $T \to X$,
$(x, t)_n \mapsto x$, is a homotopy equivalence. *Book:* not in the book. *Hidden hypotheses:*
none. *Deviation (not in the book).* *Proof:* the map carries $T_m$ into $X^m_\Sigma$ by a map
homotopic to the composite of the homotopy equivalences $T_m \to X_m \to X^m_\Sigma$ (VA.13,
VA.5), so VA.12 applies to the closed truncations, with VA.6 (ii) and VA.13; the inverse of the
homeomorphism is given strip by strip (VA.3).

**VA.15 (Theorem A with no closedness hypothesis; `Morse.mappingTelescopeMap`,
`Morse.mapsTo_mappingTelescopeMap`, `Morse.theoremA_general`).** Let $X$ be the homotopy direct
limit of $X_0 \subseteq X_1 \subseteq \cdots$ and $Y$ that of $Y_0 \subseteq Y_1 \subseteq \cdots$,
arbitrary subsets, and let $f : X \to Y$ carry each $X_i$ into $Y_i$ by a homotopy equivalence
$f_i = f|X_i : X_i \to Y_i$. Then $f$ is a homotopy equivalence. *Book:* p. 150, Theorem A: suppose
that $X$ is the homotopy direct limit of $\{X_i\}$ and $Y$ the homotopy direct limit of $\{Y_i\}$,
and let $f : X \to Y$ be a map which carries each $X_i$ into $Y_i$ by a homotopy equivalence; then
$f$ itself is a homotopy equivalence. *Hidden hypotheses:* none. *Proof:* departs from Milnor's in
the space on which his proof is run. The map $(x, t)_n \mapsto (f(x), t)_n$ of the mapping
telescopes of the inclusions carries the $m$-th truncation into the $m$-th by a map homotopic to
the composite of homotopy equivalences $T_m \to X_m \xrightarrow{f_m} Y_m \to T_m$ (VA.13), and
the truncations are closed, so VA.12 (Milnor's proof, Cases 1 and 2) makes it a homotopy
equivalence; the mapping telescopes are homotopy equivalent to $X$ and $Y$ by maps commuting with
$f$ (VA.14).

**VA.16 (monotone unions, and the final step of Theorem 17.3; `Morse.nonempty_homotopyEquiv_telescope`,
`Morse.homotopic_inverse_square`, `Morse.compareMap`, `Morse.compareMap_mapsTo`,
`Morse.isHomotopyEquiv_compareMap`, `Morse.nonempty_homotopyEquiv_mappingTelescope`).** (i) If $X$
is the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$, the $Y_i \subseteq Y$ are
closed and increasing, and $f : X \to Y$ carries each $X_i$ into $Y_i$ by a homotopy equivalence,
then $X$ is homotopy equivalent to the telescope $Y_\Sigma$. (ii) If $X$ is the homotopy direct
limit of $X_0 \subseteq X_1 \subseteq \cdots$ (closed or not), $K_0 \xrightarrow{c_0} K_1
\xrightarrow{c_1} \cdots$ is a sequence of spaces and maps, and $g_n : X_n \to K_n$ are homotopy
equivalences with $c_ng_n \simeq g_{n+1}$ on $X_n$, then $X$ is homotopy equivalent to the mapping
telescope of the $K_n$. *Book:* p. 150: in the proof of Theorem 17.3 homotopy equivalences
$\Omega^{a_i} \to K_i$ form a commutative diagram with $K_0 \subset K_1 \subset \cdots$; since
$\Omega = \bigcup\Omega^{a_i}$ and $K = \bigcup K_i$ are homotopy direct limits (Examples 1 and 2),
the limit mapping $\Omega \to K$ is a homotopy equivalence. *Hidden hypotheses:* the limit mapping
exists only because each map extends the previous one; $K$ is the homotopy direct limit of
$\{K_i\}$ by Example 2, which is not verified. *Deviation (restated):* the conclusion is a homotopy
equivalence with $Y_\Sigma$, or with the mapping telescope of the $K_n$, which stands for the union
$K$ with the weak topology; the two are homotopy equivalent by Example 2 (Whitehead's theorem).
*Deviation (stronger):* in (ii) the squares need only commute up to homotopy, and the $K_n$ need
not be subspaces of one space. *Proof:* (ii) Milnor's map $G$ of Case 2, built from homotopy
inverses of the $g_n$ and defined from the mapping telescope of the $K_n$ to $X_\Sigma$, where it is
continuous block by block, is a homotopy equivalence by VA.12 for the closed truncations.

**VA.17 (the Corollary; `Morse.corollary_appendix`, `Morse.corollary_cellComplex`).** (i) If $X$ is
the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ and the $X_n$ are homotopy
equivalent to spaces $K_n$, then there are maps $K_0 \to K_1 \to \cdots$ (in the proof
$e_{n+1}\iota_ne_n'$, with $e_n : X_n \to K_n$ a homotopy equivalence, $e_n'$ a homotopy inverse
and $\iota_n$ the inclusion) such that $X$ is homotopy equivalent to their mapping telescope.
(ii) If each $X_n$ has the homotopy type of a finite cell complex with cells $\mathrm{cells}_n$
(V2.11), $X$ is homotopy equivalent to the mapping telescope of a sequence of iterated adjunction
spaces $K_n$ with these cells. No closedness of the $X_n$ is assumed. *Book:* p. 153, Corollary: if
$X$ is the homotopy direct limit of $\{X_i\}$ and each $X_i$ has the homotopy type of a
CW-complex, then $X$ itself has the homotopy type of a CW-complex; "the proof is not difficult".
*Hidden hypotheses:* that a telescope of CW-complexes is a CW-complex needs cellular maps (cellular
approximation) and the CW structure of mapping telescopes. *Deviation (narrower):* the conclusion
is a mapping telescope of the $K_n$, not a CW-complex; for finite complexes, iterated adjunction
spaces (V2.11) replace CW-complexes. *Proof:* VA.16 (ii).

**VA.18 (countable cell complexes; `Morse.IsRelCellAttachment`, `Morse.IsCellAttachment.of_rel`,
`Morse.CellTower`, `Morse.CellTower.isCellAttachment`, `Morse.CellTower.ofSequence`,
`Morse.IsCountableCellComplexType`, `Morse.IsCountableCellComplexType.of_homotopyEquiv`).** A space
$K$ is obtained from $L$ by attaching cells of dimensions $(\lambda_1, \dots, \lambda_k)$ if it is
obtained by attaching a $\lambda_1$-cell to $L$, then a $\lambda_2$-cell, and so on, each along an
arbitrary map of its boundary sphere into the space built so far (V1.2); the map $L \to K$ is the
composite of the inclusions. A *cell tower* with cells $\mathrm{cells}_0, \mathrm{cells}_1, \dots$
(finite lists of dimensions) is a sequence $K_0 \to K_1 \to \cdots$ in which $K_0$ is an iterated
adjunction space with cells $\mathrm{cells}_0$ (V2.11) and $K_{n+1}$ is obtained from $K_n$ by
attaching the cells $\mathrm{cells}_{n+1}$, the map $K_n \to K_{n+1}$ being the inclusion; each
$K_n$ is then an iterated adjunction space with the cells $\mathrm{cells}_0, \dots,
\mathrm{cells}_n$. A space $X$ *has the homotopy type of a countable cell complex* with cells
$\mathrm{cells}_0, \mathrm{cells}_1, \dots$ if it is homotopy equivalent to the mapping telescope
(VA.13) of such a tower; this is invariant under homotopy equivalence. *Book:* p. 149: each
$\Omega^{a_i}$ has the homotopy type of "a certain CW-complex", and so should the union; p. 150:
$K = \bigcup K_i$. *Hidden hypotheses:* none. *Deviation (narrower):* weaker than a CW-complex: the
attaching maps need not be cellular (V2.11), and the mapping telescope of the tower stands for the
union of the $K_n$ with the weak topology, to which it is homotopy equivalent by Example 2, not
verified.

**VA.19 (the topological part of Theorem 17.3; `Morse.isCountableCellComplexType_of_tower`,
`Morse.isCountableCellComplexType_of_sublevel`, `Morse.isCountableCellComplexType_of_sublevel'`).**
(i) If $X$ is the homotopy direct limit of $X_0 \subseteq X_1 \subseteq \cdots$ and $g_n : X_n \to
K_n$ are homotopy equivalences to the stages of a cell tower with $c_ng_n \simeq g_{n+1}$ on $X_n$,
then $X$ has the homotopy type of the countable cell complex. (ii) Let $E : X \to \mathbb R$ be
continuous, $a_0 \le a_1 \le \cdots$ with $a_n \to \infty$, and $g_n : \{E \le a_n\} \to K_n$
homotopy equivalences to the stages of a cell tower (given as a tower, or by its stages $K_n$ and
the inclusions $c_n : K_n \to K_{n+1}$ attaching the cells $\mathrm{cells}_{n+1}$) with
$c_ng_n = g_{n+1}$ on $\{E \le a_n\}$. Then $X$ has the homotopy type of the countable cell complex
with cells $\mathrm{cells}_0, \mathrm{cells}_1, \dots$. *Book:* p. 150, the alternative final step
of Theorem 17.3 (VA.16). *Hidden hypotheses:* $a_i \to \infty$, so that the sublevel sets exhaust
$X$; each $g_{n+1}$ extends $g_n$, for the limit map. *Deviation (stronger):* no paracompactness
(VA.7 (ii)). *Deviation (restated):* "CW-complex" in the sense of VA.18. *Proof:* VA.16 (ii), with
VA.7 (ii) in (ii).

### What is not verified in this chapter

- **Example 2** (p. 149): a CW-complex is the homotopy direct limit of subcomplexes with union $X$.
  It needs Whitehead's theorem, the fact that compact subsets of a CW-complex lie in finite
  subcomplexes, and the CW topology of products (Lemma 2.3 and Facts (a)–(c) of the exposition),
  none of which is in Mathlib. Hence the mapping telescope of a cell tower is not compared with the
  union of its stages in the weak topology (VA.16, VA.18).
- **The Remark** (p. 150): that under the hypotheses of Case 1 $f_\Sigma$ need not be homotopic to
  the identity ("counterexamples can be given"). The exposition's phantom-map counterexample needs
  cellular cohomology and $\mathbb{CP}^\infty$; it is not formalized.
- **The CW structure of mapping telescopes**: the Corollary's conclusion that $X$ has the homotopy
  type of a CW-complex needs cellular approximation, to make the maps $K_n \to K_{n+1}$ cellular, and
  the CW structure of the mapping telescope of cellular maps; neither is in Mathlib, so the
  conclusion is a mapping telescope (VA.17).
- **The application to the path space** (p. 150) is not part of this chapter: the sublevel sets
  $\Omega^{a_i}$, Milnor's metric and the tower of complexes are verified in Chapter 10, where VA.19
  gives Theorem 17.3 (V10.20–V10.22) and the homology of $\Omega(S^n; p, q)$ is computed level by
  level (V10.25–V10.26).

---

## 18. Sign-off

The statements below are the ones the reader is asked to confirm say what Milnor means. Each is a summary of the V-item it names; the standing hypotheses of that item are not repeated.

1. (V1.2) $X \cup_\varphi e^n$ is the quotient of $X \sqcup D^n$ identifying each $u \in S^{n-1}$ with $\varphi(u)$, that is, the pushout of $X \leftarrow S^{n-1} \to D^n$.
2. (V1.3) In coordinates, a critical point is a zero of the derivative, the Hessian is the second derivative, the index is the largest dimension of a subspace on which the Hessian is negative definite, the nullity is the dimension of its null space, and non-degenerate means nullity $0$, equivalently a non-singular matrix of second partial derivatives.
3. (V1.4) On a manifold, with no Hausdorff hypothesis, the same notions are read in the preferred chart at $p$, critical points agree with those of the companion volume, and a Morse function is a smooth function all of whose critical points are non-degenerate.
4. (V1.5) At a critical point of a function $C^2$ there, criticality, the Hessian (transformed as a bilinear form by the derivative of the change of coordinates), non-degeneracy, index and nullity do not depend on the coordinate system.
5. (V1.6) For $f = F|N$ on a slice submanifold $N$ of $V$, a point $q$ is critical exactly when $dF_q$ vanishes on $T_qN$ (for an inner product, when $\nabla F(q) \perp T_qN$), the Hessian, index and nullity can be computed in any slice parametrization, and for $L_p$ Milnor's criterion and Hessian formula of pp. 35–36 hold.
6. (V1.7) A function smooth on an open convex neighbourhood $V$ of $0$ in $\mathbb R^n$ with $f(0) = 0$ is $\sum_i x_i g_i(x)$ with $g_i$ smooth on $V$ and $g_i(0) = \partial f/\partial x_i(0)$; on an open star-shaped $V$ in any normed space it is $L(x)x$ with $L$ smooth and $L(0) = df_0$, and if also $df_0 = 0$ it is $B(x)(x, x)$ with $B$ smooth and symmetric and $B(0) = \tfrac12 d^2 f_0$.
7. (V1.8) Near a non-degenerate critical point $p$ of index $\lambda$ of a function smooth near $p$, on $\mathbb R^n$ or on any smooth manifold, there are coordinates with $f = f(p) - \sum_{i \le \lambda}(y^i)^2 + \sum_{i > \lambda}(y^i)^2$.
8. (V1.9) If $f$ has such a normal form with $k$ minus signs in some coordinate system around $p$, then $p$ is a non-degenerate critical point of index $k$.
9. (V1.10) A non-degenerate critical point of a function $C^2$ at that point has a neighbourhood containing no other critical point.
10. (V1.11) A $C^2$ function whose critical points are all non-degenerate has only finitely many critical points in each compact set.
11. (V1.12) The origin is the only critical point of $x^3$ and of $x^3 - 3xy^2$, and is degenerate; the critical points of $x^2$ (the $y$ axis) and of $x^2y^2$ (the two axes) are all degenerate.
12. (V1.13) A one-parameter group of diffeomorphisms of $E$ is a jointly smooth $\varphi$ with each $\varphi_t$ a diffeomorphism and $\varphi_{t+s} = \varphi_t\circ\varphi_s$; $X$ generates it when $X(x)$ is the velocity of $t \mapsto \varphi_t(x)$ at $t = 0$, and then its orbits are integral curves of $X$.
13. (V1.14) A $C^n$ ($1 \le n \le \infty$) compactly supported vector field on a Banach space has a global flow, $C^n$ in $(t, x)$, each $\varphi_t$ being a $C^n$ diffeomorphism.
14. (V1.15) A smooth vector field on $E$ vanishing outside a compact set generates exactly one one-parameter group of diffeomorphisms of $E$.
15. (V2.1) $A$ is a strong deformation retract of $X$ if some homotopy from the identity of $X$ to a map into $A$ fixes $A$ at all times; the inclusion of such an $A$ is a homotopy equivalence.
16. (V2.2) On $\mathbb R^n$ with an inner product, if $f^{-1}[a, b]$ is compact and free of critical points, a diffeomorphism of $\mathbb R^n$ carries $M^a$ onto $M^b$, and $M^a$ is a strong deformation retract of $M^b$.
17. (V2.3) The same holds for $f = F|N$ on a slice submanifold $N \subseteq \mathbb R^K$, closed or not, with a diffeomorphism of $N$.
18. (V2.4) The same holds on a compact Hausdorff manifold, where $f^{-1}[a, b]$ need only be free of critical points.
19. (V2.5) On $\mathbb C \setminus \{i\}$ with $f = |z|^2$, the set $f^{-1}[\tfrac14, 4]$ contains no critical points but is not compact, and $M^{1/4}$ and $M^4$ are not homotopy equivalent.
20. (V2.6) On $\mathbb R^n$, under the hypotheses of Theorem 3.2 and for all small $\epsilon$, $M^{c+\epsilon}$ strongly deformation retracts onto $M^{c-\epsilon}$ together with an embedded $\lambda$-cell meeting $M^{c-\epsilon}$ in its boundary sphere, and so is homotopy equivalent to $M^{c-\epsilon}$ with a $\lambda$-cell attached.
21. (V2.7) In a Hausdorff space, a closed set $A$ together with an embedded closed disk meeting $A$ exactly in its boundary sphere is $A$ with a cell attached along the restriction of the embedding to the sphere.
22. (V2.8) Theorem 3.2 holds for $f = F|N$ on a slice submanifold $N \subseteq \mathbb R^K$, and its topological half (given Assertion 3) holds in any Morse coordinate patch of a Hausdorff space.
23. (V2.9) With finitely many non-degenerate critical points on the level $c$ and none other near it, $N^{c+\epsilon}$ strongly deformation retracts onto $N^{c-\epsilon}$ together with pairwise disjoint cells, one of dimension $\lambda_p$ for each critical point $p$.
24. (V2.10) On $\mathbb R^n$, $M^c$ is a strong deformation retract of $M^{c+\epsilon}$, and $M^{c-\epsilon} \cup e^\lambda$ is one of $M^c$.
25. (V2.11) An iterated adjunction space is built from the empty space by attaching cells one at a time along arbitrary continuous maps; it replaces Milnor's CW-complex, without the cellular condition.
26. (V2.12) A compact slice submanifold on which $F|N$ has only non-degenerate critical points has the homotopy type of an iterated adjunction space with exactly $C_\lambda$ cells of dimension $\lambda$, attached in order of critical value.
27. (V2.13) Attaching an $n$-cell along homotopic maps gives homotopy equivalent spaces, by a homotopy equivalence which is the identity on $X$.
28. (V2.14) A homotopy equivalence $f : X \to Y$, extended by the identity on the cell, is a homotopy equivalence $X \cup_\varphi e^n \to Y \cup_{f\varphi} e^n$.
29. (V2.15) For $a$ not a critical value, $N^a$ has the homotopy type of an iterated adjunction space with one $\lambda$-cell for each critical point of index $\lambda$ below $a$.
30. (V3.1) A local extremum is a critical point, and at a non-degenerate one the index is $0$ for a minimum and $\dim M$ for a maximum.
31. (V3.2) Near a non-degenerate minimum $f = f(p) + \|y\|^2$ in smooth coordinates, and when the minimum is strict and the space compact, each small sublevel set $\{f \le f(p) + \varepsilon\}$ is the image of the closed unit ball, with the unit sphere going onto the level set.
32. (V3.3) On a compact manifold of positive dimension, a smooth function with exactly two critical points, both non-degenerate, has them at its strict minimum and its strict maximum, of indices $0$ and $\dim M$.
33. (V3.4) If $f^{-1}[a, b]$ is compact and free of critical points, a diffeomorphism carries $N^a$ onto $N^b$ and the level $f^{-1}(a)$ onto $f^{-1}(b)$.
34. (V3.5) A Hausdorff space that is the union of two embedded closed $n$-balls meeting exactly in their common boundary sphere is homeomorphic to $S^n$.
35. (V3.6) A compact submanifold of a finite-dimensional space carrying a smooth function with exactly two critical points, both non-degenerate, is homeomorphic to $S^n$, $n$ its dimension.
36. (V3.7) A function $S$ on pairs $a \le b$ of a preordered set is subadditive if $S(a, c) \le S(a, b) + S(b, c)$ for $a \le b \le c$, additive if equality holds.
37. (V3.8) For subadditive $S$ and a chain $X_0 \le \dots \le X_n$ with $n \ge 1$, $S(X_0, X_n) \le \sum_k S(X_k, X_{k+1})$, with equality for additive $S$.
38. (V3.9) A homology of a filtration is a family of finite-dimensional vector spaces $H_i(a, b)$, $a \le b$, with a long exact sequence for every triple ending in $0$; nothing else is assumed.
39. (V3.10) For such a structure $\dim H_\lambda$ is subadditive, and the Euler characteristic truncated at $N$ is additive when $H_{N+1}$ vanishes.
40. (V3.11) For such a structure and a chain, $R_\lambda \le C_\lambda$, and the alternating sums of the $R_i$ and $C_i$ up to $N$ agree when the slabs have no homology in degree $N + 1$; under the cell hypothesis $C_\lambda$ is the number of critical points of index $\lambda$.
41. (V3.12) $S_\lambda = R_\lambda - R_{\lambda-1} + \dots \pm R_0$ is subadditive, by Milnor's rank computation.
42. (V3.13) $R_\lambda - R_{\lambda-1} + \dots \pm R_0 \le C_\lambda - C_{\lambda-1} + \dots \pm C_0$ for every $\lambda$.
43. (V3.14) The strong inequalities imply the weak ones, become equalities when $C_{\lambda+1} = 0$, and give $\sum (-1)^i R_i = \sum_p (-1)^{\operatorname{ind}(p)}$.
44. (V3.15) If $C_{\lambda+1} = C_{\lambda-1} = 0$ then $R_\lambda = C_\lambda$ and $R_{\lambda \pm 1} = 0$; if no two consecutive $C_i$ are nonzero, $R_i = C_i$ for all $i$.
45. (V3.16) $C_\lambda(f)$ is the number of critical points of $f$ of index $\lambda$, and the sum of $(-1)^{\operatorname{index}}$ over the critical points is $\sum_\lambda (-1)^\lambda C_\lambda(f)$.
46. (V3.17) An Euler number of a compact nonempty $N \subseteq \mathbb R^{K+1}$ is an integer equal to the index sum of every smooth tangent field with finitely many zeros; one exists for $K \ge 1$.
47. (V3.18) For a non-degenerate symmetric form $H(v, w) = \langle Av, w\rangle$, $\operatorname{sgn} \det A = (-1)^{\operatorname{index} H}$.
48. (V3.19) At a non-degenerate critical point of index $\lambda$ of $F|_N$, the gradient field of $F|_N$ for the induced metric has index $(-1)^\lambda$.
49. (V3.20) On a compact $N \subseteq \mathbb R^{K+1}$, $K \ge 1$, $\dim N \ge 1$, every Morse function has $\sum_\lambda (-1)^\lambda C_\lambda = \chi(N)$, the Poincaré–Hopf integer; so this sum does not depend on the Morse function.
50. (V3.21) Every Morse function on $S^n$, $n \ge 1$, has $\sum_\lambda (-1)^\lambda C_\lambda = 1 + (-1)^n$; the height function has exactly two critical points, of indices $0$ and $n$.
51. (V3.22) For $0 < \rho < R$ the torus of revolution is a compact smooth surface in $\mathbb R^3$, the regular zero set of a quartic polynomial.
52. (V3.23) The height of the upright torus above its tangent plane has exactly four critical points, all non-degenerate, of indices $0, 1, 1, 2$, at heights $0, 2\rho, 2R, 2R + 2\rho$.
53. (V3.24) $T^a$ is empty for $a < 0$ and all of $T$ for $a \ge 2R + 2\rho$, and between consecutive critical values Theorem 3.1 holds on $T$.
54. (V3.25) The Euler number of the torus is $0$, by Morse theory and by a nowhere-zero field, so every Morse function on it has $C_0 - C_1 + C_2 = 0$.
55. (V3.26) Relative singular homology $H_n(X, A)$ is functorial in pairs, has the exact sequence of a pair, is homotopy invariant, and $H_n(B, A) \cong H_n(X, A)$ when $B \supseteq A$ is a strong deformation retract of $X$.
56. (V3.27) A triple $Z \subseteq Y \subseteq X$ has an exact sequence $\cdots \to H_n(Y, Z) \to H_n(X, Z) \to H_n(X, Y) \to H_{n-1}(Y, Z) \to \cdots \to H_0(X, Y) \to 0$.
57. (V3.28) If the closure of $Z$ lies in the interior of $A$, then $(X \setminus Z, A \setminus Z) \to (X, A)$ induces isomorphisms in homology.
58. (V3.29) If the interiors of $A$ and $B$ cover $X$, the Mayer–Vietoris sequence of $A \cap B$, $A$ and $B$, and $X$ is exact.
59. (V3.30) $H_i(D^n, S^{n-1})$ is the coefficient ring for $i = n$ and $0$ otherwise, and $H_i(S^n)$, $n \ge 1$, is the coefficient ring for $i = 0$ and $i = n$ and $0$ otherwise.
60. (V3.31) Attaching disjoint cells to a closed subset $Y$ of a Hausdorff space gives $H_i(X, Y) \cong R^{c_i}$, $c_i$ the number of cells of dimension $i$.
61. (V3.32) For a filtration $X_0 \subseteq \dots \subseteq X_n$ whose steps have finite-dimensional homology, the Betti numbers of $(X_n, X_0)$ satisfy the weak and strong Morse inequalities and the Euler characteristic formula against the sums $C_i$ over the steps.
62. (V3.33) If $A$, $B \cup \bigcup_j e_j$ and $X'$ are strong deformation retracts of $B$, $X'$ and $X$ respectively, then $\dim H_i(X, A)$ is the number of cells $e_j$ of dimension $i$.
63. (V3.34) For a function with non-degenerate critical points on a compact submanifold, a slab between two non-critical levels containing one critical value has homology of dimension the number of critical points of each index in it; $H_*(N)$ is finite-dimensional.
64. (V3.35) For such a function on a compact $N$, over every field, $b_\lambda(N) \le C_\lambda$, $\sum (-1)^i b_i = \sum (-1)^\lambda C_\lambda$, and $b_i = 0$ above $\dim N$.
65. (V3.36) For such a function, $b_\lambda - b_{\lambda-1} + \dots \pm b_0 \le C_\lambda - C_{\lambda-1} + \dots \pm C_0$.
66. (V3.37) If $C_{\lambda+1} = C_{\lambda-1} = 0$, then $b_\lambda = C_\lambda$ and $b_{\lambda \pm 1} = 0$; if no two consecutive $C_i$ are nonzero, then $b_i = C_i$ for all $i$.
67. (V3.38) The Poincaré–Hopf integer of a compact submanifold, and $\chi(M)$ of a compact manifold, equal $\sum_i (-1)^i \dim H_i(\,\cdot\,; \Bbbk)$ for every field $\Bbbk$.
68. (V3.39) On every compact Hausdorff manifold and for every Morse function, the weak and strong inequalities, formula (3) and the lacunary principle hold for the Betti numbers over every field.
69. (V3.40) Over every field: a function with exactly two critical points, both non-degenerate, on $M^n$, $n \ge 2$, forces $b_0 = b_n = 1$ and $b_i = 0$ otherwise; $S^n$ has Euler characteristic $1 + (-1)^n$; the torus has $b_0 - b_1 + b_2 = 0$.
70. (V3.41) The Hermitian projections of trace $1$ in $M_{n+1}(\mathbb C)$ form a compact submanifold of dimension $2n$, which is $\mathbb CP^n$, and Milnor's functions $x_j, y_j$ on $U_k$ are coordinates on it.
71. (V3.42) For distinct $c_j$, $f = \sum c_j|z_j|^2$ on $\mathbb CP^n$ has exactly the $n + 1$ critical points $p_k$, all non-degenerate, $p_k$ of index $2\,\#\{j : c_j < c_k\}$; so there is one critical point of each index $0, 2, \dots, 2n$.
72. (V3.43) $\mathbb CP^n$ has the homotopy type of a space with one cell in each dimension $0, 2, \dots, 2n$, and over every field its Betti numbers are $1$ in those degrees and $0$ elsewhere.
73. (V4.1) For a $k$-dimensional submanifold $M \subseteq \mathbb R^n$, the normal bundle $N$ is an $n$-dimensional submanifold of $\mathbb R^n \times \mathbb R^n$, and $E(q, v) = q + v$.
74. (V4.2) $e$ is a focal point of $(M, q)$ of multiplicity $\mu$ iff $(q, e - q) \in N$ and $dE$ has nullity $\mu > 0$ there; the focal points of $M$ are the critical values of $E$.
75. (V4.3) For a smooth map from a second countable manifold into a finite-dimensional vector space, the image of the points where the derivative is not onto has measure zero.
76. (V4.4) Almost no point of $\mathbb R^n$ is a focal point of $M$.
77. (V4.5) In the slice-chart coordinates $x$ at $q$, $g = \langle dx\,\cdot, dx\,\cdot\rangle$ and $\ell_v = \langle v, d^2x(\cdot, \cdot)\rangle$ are Milnor's first and second fundamental forms.
78. (V4.6) The principal curvatures in a normal direction $v$ are the eigenvalues, with multiplicity, of the self-adjoint shape operator $S_v$ on $T_qM$.
79. (V4.7) The focal points of $(M, q)$ on the normal line $q + tv$ are the points $q + K^{-1}v$, $K \ne 0$ a principal curvature, with the multiplicity of $K$; at most $k$ of them counted with multiplicity.
80. (V4.8) The nullity of $dE$ at $(q, v) \in N$ equals the nullity of $g - \ell_v$.
81. (V4.9) $q + tv$ is a focal point of $(M, q)$ of multiplicity $\mu$ iff $g - t\ell_v$ has nullity $\mu > 0$; $q$ itself is never one.
82. (V4.10) $q$ is a critical point of $L_p$ iff $p - q$ is normal to $M$ at $q$, and the Hessian of $L_p$ in the coordinates $x$ is $2(g - \ell_{p-q})$.
83. (V4.11) $q$ is a degenerate critical point of $L_p$ iff $p$ is a focal point of $(M, q)$, the nullity being the multiplicity.
84. (V4.12) For almost every $p \in \mathbb R^n$, $L_p$ is a Morse function on $M$.
85. (V4.13) A closed submanifold of $\mathbb R^n$ carries a Morse function all of whose sublevel sets are compact.
86. (V4.14) The image of a smooth topological embedding with injective derivative is a submanifold, and the embedding is a diffeomorphism onto it.
87. (V4.15) Critical points, Hessians, non-degeneracy, index, nullity and the numbers $C_\lambda$ are preserved by diffeomorphisms.
88. (V4.16) Every compact Hausdorff manifold is diffeomorphic to a compact submanifold of some $\mathbb R^{K+1}$, $K \ge 1$.
89. (V4.17) Every compact Hausdorff manifold carries a Morse function.
90. (V4.18) $\chi(M)$ is defined as $\sum_\lambda (-1)^\lambda C_\lambda(f)$ for a chosen Morse function $f$.
91. (V4.19) On a compact Hausdorff manifold every Morse function gives the same $\sum_\lambda (-1)^\lambda C_\lambda = \chi(M)$, which is the index sum of every tangent field on every embedded copy.
92. (V4.20) For every smooth $f$ on a submanifold of $\mathbb R^n$, $f + \langle a, \cdot\rangle$ is a Morse function for almost every $a$.
93. (V4.21) Every smooth function on a submanifold of $\mathbb R^n$, bounded or not, is a uniform limit of Morse functions, with derivatives up to any order converging on compact pieces of coordinate charts.
94. (V4.22) The same holds on every compact Hausdorff manifold.
95. (V4.23) The index of $L_p$ at a non-degenerate critical point $q$ is the number of focal points of $(M, q)$ on the segment from $q$ to $p$, counted with multiplicity.
96. (V4.24) A compact Hausdorff manifold carrying a smooth function with exactly two critical points, both non-degenerate, is homeomorphic to $S^n$.
97. (V5.1) The Hessian is the second derivative, defined at every point; the index of a bilinear form is the largest dimension of a subspace on which it is negative definite, and the nullity is the dimension of its null space.
98. (V5.2) $\operatorname{Re}B$ of a complex bilinear form is Milnor's $Q'$, multiplication by $i$ is an orthogonal map with square $-1$, and it changes the sign of $\operatorname{Re}B$.
99. (V5.3) The eigenvalues of the matrix of $Q'$ come in pairs $\pm e$ of equal multiplicity.
100. (V5.4) If $G$ is $J$-invariant and $L$ is $J$-anti-invariant, then $G - tL$ and $G + tL$ have the same nullity, and so do $L - eG$ and $L + eG$.
101. (V5.5) A vector whose real inner product with every vector of a complex subspace vanishes is Hermitian-orthogonal to that subspace.
102. (V5.6) In holomorphic coordinates the Hessian of $\|w(\cdot) - p\|^2$ is twice the first fundamental form plus twice $\operatorname{Re}\langle w(q) - p, d^2w_q\rangle$.
103. (V5.7) In a holomorphic chart, the Hessians of $L_p$ for $p = w(q) \pm tn$ have the same nullity (Assertion 2, before the translation into focal points).
104. (V5.8) If $H = G - L$ on the diagonal with $G$ $J$-invariant and $L$ $J$-anti-invariant, then $H(Jv, Jv) = 2G(v, v) - H(v, v)$.
105. (V5.9) If $H(v, v) + H(Jv, Jv) \ge 0$ for an injective linear $J$, the index of $H$ is at most half the real dimension.
106. (V5.10) A real form $G - \operatorname{Re}B$ on $\mathbb C^k$, with $G \ge 0$ invariant under $v \mapsto iv$ and $B$ complex bilinear, has index at most $k$.
107. (V5.11) For $w$ holomorphic near $q$ on a $k$-dimensional complex space, the Hessian of $\|w(\cdot) - p\|^2$ at $q$ has index at most $k$, whether or not $q$ is critical or non-degenerate.
108. (V5.12) If moreover $G$ is positive definite and the space is non-zero, the form takes a positive value.
109. (V5.13) On a submanifold of $\mathbb R^{2m}$ whose tangent spaces are complex subspaces, of real dimension $2k$, every critical point of $L_p = \|\cdot - p\|^2$ has index at most $k$.
110. (V5.14) If no critical point between two regular levels $a < b$ has index $j$, and the slab between them is compact with non-degenerate critical points, then $H_j(N^b, N^a) = 0$ over a field.
111. (V5.15) Theorem 7.2: a closed submanifold of $\mathbb R^{2m}$ of dimension $2k$ with complex tangent spaces has the homotopy type of a countable cell complex with cells of dimension at most $k$.
112. (V5.16) Theorem 7.1 over a field: such a submanifold has no homology above degree $k$.
113. (V5.17) If $X$ is compact, $X \setminus A$ is such a submanifold going to infinity at $A$, and a neighbourhood of $A$ deforms into $A$ keeping $A$ fixed, then $H_r(X, A) = 0$ for $r < k$ over a field, and $H_r(A) \to H_r(X)$ is bijective for $r < k - 1$ and surjective for $r = k - 1$.
114. (V5.18) Corollary 7.3 over a field: this holds for a closed $V \subseteq \mathbb CP^n$ and the hyperplane $P = \{z_0 = 0\}$, when the affine part of $V$ is a complex submanifold of complex dimension $k$ and a neighbourhood of $V \cap P$ deforms into it.
115. (V5.19) Theorem 7.4: under the same hypotheses every map $I^r \to V$, $r < k$, deforms into $V \cap P$ relative to the part already there; so $\pi_i(V \cap P) \to \pi_i(V)$ is bijective for $i < k - 1$ and surjective for $i = k - 1$.
116. (V6.1) In the embedded setting, $T_qN$ is the range of the derivative of the inclusion, $P_q$ the orthogonal projection onto it, and a vector field is a map $N \to V$ with tangent values.
117. (V6.2) $q \mapsto P_q$ is smooth, so every tangent vector $u$ at a point extends to the smooth vector field $q \mapsto P_qu$.
118. (V6.3) A Mathlib covariant derivative satisfies Milnor's rules (2)–(4) at points where the sections involved are differentiable; his (1) is a separate smoothness class.
119. (V6.4) $X \vdash Y = P(dY(X))$ is tangent and satisfies Milnor's rules (1)–(4).
120. (V6.5) $DX/dt = P(X')$ satisfies Milnor's axioms (a), (b), (c).
121. (V6.6) Every operation satisfying (a), (b), (c) along a smooth curve equals $P(X')$ on smooth fields along the curve.
122. (V6.7) Linear equations $x' = A(t)x$ have unique solutions, and global ones when $A(t)$ is skew-adjoint.
123. (V6.8) Along a smooth curve, through every tangent vector at any time there is exactly one parallel field, defined for all $t$ and smooth.
124. (V6.9) Parallel fields have constant inner products, and parallel translation is a linear isometry between tangent spaces, the identity at equal times and transitive.
125. (V6.10) $\frac{d}{dt}\langle X, Y\rangle = \langle DX/dt, Y\rangle + \langle X, DY/dt\rangle$ for fields along any curve.
126. (V6.11) $v\langle Y, Y'\rangle = \langle v \vdash Y, Y'\rangle + \langle Y, v \vdash Y'\rangle$; on an abstract manifold this identity is the definition of compatibility, equal to Mathlib's.
127. (V6.12) $\mathrm{II}_q(v, w) = D_vw$ is the normal part of $dW_q(v)$ for any field $W$ with $W(q) = w$; it is normal, symmetric, and $D_v$ is self-adjoint.
128. (V6.13) The ambient bracket of tangent fields is tangent and is Milnor's Poisson bracket, and the induced connection is symmetric; on an abstract manifold symmetric means torsion-free.
129. (V6.14) $P(dY(X))$ is symmetric and compatible, and any symmetric compatible operation agrees with it on smooth fields; on an abstract manifold two symmetric compatible connections agree on differentiable fields.
130. (V6.15) $\frac{D}{\partial x}\frac{\partial s}{\partial y} = \frac{D}{\partial y}\frac{\partial s}{\partial x}$ for every smooth surface in $N$.
131. (V6.16) Milnor's $R(X, Y)Z = -X \vdash (Y \vdash Z) + Y \vdash (X \vdash Z) + [X, Y] \vdash Z$ is the negative of Nomizu's curvature.
132. (V6.17) For smooth vector fields on $N$, $R(X, Y)Z = \mathrm{II}(Y, \mathrm{II}(X, Z)) - \mathrm{II}(X, \mathrm{II}(Y, Z))$, so $R$ is a tensor.
133. (V6.18) $\langle R(X, Y)Z, W\rangle = \langle\mathrm{II}(X, Z), \mathrm{II}(Y, W)\rangle - \langle\mathrm{II}(X, W), \mathrm{II}(Y, Z)\rangle$, with Milnor's sign.
134. (V6.19) $\frac{D}{\partial y}\frac{D}{\partial x}W - \frac{D}{\partial x}\frac{D}{\partial y}W = R(\partial s/\partial x, \partial s/\partial y)W$ for every smooth tangent field along a smooth surface.
135. (V6.20) The curvature of $N$ satisfies Lemma 9.3 (1)–(3), pointwise and for smooth vector fields.
136. (V6.21) Skew-symmetry in each pair and the cyclic identity imply pair symmetry (Lemma 9.3 (4)).
137. (V6.22) The sectional curvature $K(X, Y)$ depends only on the plane, and is the same in Milnor's and in the standard sign convention.
138. (V6.23) A curvature tensor is determined by its sectional curvatures.
139. (V6.24) Constant sectional curvature $\kappa$ means $R(X, Y)Z = \kappa(\langle X, Z\rangle Y - \langle Y, Z\rangle X)$ in Milnor's sign.
140. (V6.25) The unit sphere has $\mathrm{II}_q(v, w) = -\langle v, w\rangle q$ and constant sectional curvature $1$.
141. (V7.1) A geodesic of $N$ on an open interval is a smooth curve in $N$ whose acceleration in $V$ is normal to $N$, that is, $\frac{D}{dt}\frac{d\gamma}{dt} = 0$.
142. (V7.2) A geodesic on an interval has constant speed, its length on $[a, b]$ is its speed times $b - a$, and $t \mapsto \gamma(at + b)$ is again a geodesic.
143. (V7.3) A smooth curve in $N$ is a geodesic iff $\gamma'' = \mathrm{II}(\gamma', \gamma')$, iff $(\gamma, \gamma')$ is an integral curve of the spray $(x, v) \mapsto (v, \mathrm{II}_x(v, v))$; solutions of the chart equation $u'' = -\Gamma(u)(u', u')$ are geodesics.
144. (V7.4) $u'' = F(u, u')$, $F$ smooth, has solutions for a uniform time, depending smoothly on $(u_0, v_0, t)$, and two solutions with the same initial data agree on every common interval.
145. (V7.5) Two geodesics on an interval with the same position and velocity at one time coincide.
146. (V7.6) Near each point there are $U$ and $\varepsilon$ such that every tangent vector $v$ at $p \in U$ with $\|v\| < \varepsilon$ is the initial velocity of a unique geodesic on $(-2, 2)$, depending smoothly on $(p, v, t)$.
147. (V7.7) $\exp_q(v) = \gamma(1)$ for the geodesic $\gamma$, defined near $[0, 1]$, with $\gamma(0) = q$ and $\gamma'(0) = v$; it is well defined, $\exp_q(0) = q$, and $\gamma(t) = \exp_q(tv)$.
148. (V7.8) $\exp$ is defined and smooth on a neighbourhood of the zero section of $TN$, and the derivative of $\exp_q$ at $0$ is the inclusion of $T_qN$.
149. (V7.9) $\varepsilon$ is a normal radius at $q$ when $\exp_q$ maps the open $\varepsilon$-ball of $T_qN$ diffeomorphically onto an open subset of $N$.
150. (V7.10) Every point has a neighbourhood $W$ and an $\varepsilon > 0$ such that for $q_1, q_2 \in W$ exactly one $v$ with $\|v\| < \varepsilon$ has $\exp_{q_1}(v) = q_2$, $v$ depends smoothly on $(q_1, q_2)$, and $\varepsilon$ is a normal radius at every point of $W$.
151. (V7.11) Lengths of piecewise smooth paths are additive, unchanged by reversal and translation, at least the distance in $V$ of the endpoints, and zero only for constant paths.
152. (V7.12) $\langle d(\exp_q)_w(w), d(\exp_q)_w(x)\rangle = \langle w, x\rangle$ inside a normal ball; in particular the radial geodesics are orthogonal to the images of the spheres.
153. (V7.13) Along a path in a punctured normal neighbourhood, the length is at least the increase of the radius $r$, and with equality the direction $v$ is constant.
154. (V7.14) A path from $q$ that leaves the open normal ball of radius $s$ has a segment, from its last visit of $q$ to its first arrival on the shell of radius $s$, of length at least $s$.
155. (V7.15) The geodesic $t \mapsto \exp_{q_1}(tv)$ of Lemma 10.3 is not longer than any piecewise smooth path in $N$ with the same endpoints, and equality forces the same image.
156. (V7.16) A path from $q$ to $\exp_q(v)$ of length $\|v\|$ is $t \mapsto \exp_q(\rho(t)v)$ with $\rho$ continuous and nondecreasing from $0$ to $1$.
157. (V7.17) A piecewise smooth path parametrized by arc length and not longer than any path with the same endpoints is a geodesic, smooth at its break points, and extends to a geodesic on an open interval.
158. (V7.18) The infimum $\rho$ of the lengths of joining paths is a metric on $N$ with values in $[0, \infty]$.
159. (V7.19) Within a normal radius, $\rho(p, \exp_p v) = \|v\|$ and the metric balls are the normal balls; the metric balls form neighbourhood bases of the topology of $N$.
160. (V7.20) For compact $K \subseteq N$ there is $\delta > 0$ such that points of $K$ at distance $< \delta$ are joined by a unique geodesic of length $< \delta$, which is minimal and depends smoothly on its endpoints.
161. (V7.21) $\rho$ is at least the distance in $V$, continuous on $N \times N$, finite when $N$ is connected, and makes $N$ a metric space with its own topology.
162. (V7.22) $(N, \rho)$ is complete if every $\rho$-Cauchy sequence converges in $N$; $N$ is geodesically complete if $\exp_q$ is defined on all of $T_qN$ for every $q$, which holds iff every geodesic on an open interval extends to a geodesic on $\mathbb R$.
163. (V7.23) Every geodesic is $t \mapsto \exp_q(tv)$; near each point geodesics of bounded speed exist for a uniform time and can be continued, and $\exp$ is continuous on its domain, which is open in $TN$.
164. (V7.24) A minimal geodesic on $[a, b]$ is a geodesic no longer than any piecewise smooth path in $N$ with the same endpoints; $t \mapsto \exp_p(tv)$ on $[0, 1]$ is one when $\rho(p, \exp_p v) = \|v\|$.
165. (V7.25) For $0 < \delta < \varepsilon$ and $\delta < \rho(p, q) < \infty$ some point $p_0$ of the sphere of radius $\delta$ about $p$ has $\rho(p, q) = \delta + \rho(p_0, q)$; a broken path made of two unit-speed geodesics and of minimal length is unbroken.
166. (V7.26) If $\exp_p$ is defined on all of $T_pN$, every point at finite distance from $p$ is joined to $p$ by a minimal geodesic of length $\rho(p, q)$; in a connected geodesically complete $N$ any two points are.
167. (V7.27) If $N$ is connected and $\exp_p$ is defined on all of $T_pN$ for one $p$, every bounded set has compact closure in $N$, and then $(N, \rho)$ is complete.
168. (V7.28) If $(N, \rho)$ is complete, $N$ is geodesically complete.
169. (V7.29) For connected nonempty $N$, metric completeness, geodesic completeness, completeness of $\exp_p$ at one point, and compactness of the closures of bounded sets are equivalent; then closed bounded sets are compact.
170. (V7.30) A connected submanifold that is closed in $V$, for instance a compact one, is complete in all these senses; any two points of $S^n$, $n \ge 1$, are joined by a minimal geodesic.
171. (V8.1) $\Omega(N; p, q)$ is the set of piecewise smooth paths in $N$ on $[0, 1]$ from $p$ to $q$, and $T\Omega_\omega$ the vector space of piecewise smooth tangent fields along $\omega$ vanishing at $0$ and $1$.
172. (V8.2) A variation is a map $\alpha(u, t)$, $u$ in an open set around $0$, with values in $N$ for $t \in [0, 1]$, fixed end points, and smooth on the closed strips of a subdivision; its variation field lies in $T\Omega_\omega$.
173. (V8.3) Every finite family of fields in $T\Omega_\omega$ is the family of variation fields of the variation $\exp_{\omega(t)}(\sum_j u_jW_j(t))$, $\|u\|$ small, without completeness.
174. (V8.4) $\omega$ is a critical path of $E$ if every variation of $\omega$ has $\frac{d}{du} E(\bar\alpha(u)) = 0$ at $u = 0$.
175. (V8.5) $E_a^b = \int_a^b \|c'\|^2$, and $(L_a^b)^2 \le (b - a)E_a^b$, with equality iff the speed is constant off the break points.
176. (V8.6) A geodesic that is no longer than any path of $\Omega$ has energy at most that of every path of $\Omega$.
177. (V8.7) The first variation of $\omega$ in the direction $W$ is $-\sum_t\langle W_t, \Delta_tV\rangle - \int_0^1\langle W_t, A_t\rangle\,dt$, $\Delta_tV$ the jump of the velocity and $A$ the acceleration.
178. (V8.8) On closed strips the mixed partials commute up to the edges, one may differentiate under the integral sign, and integration by parts over the pieces produces the jump terms.
179. (V8.9) For every variation and every $u$, $\frac12\frac{d}{du}E(\bar\alpha(u))$ is the first variation of $\bar\alpha(u)$ in the direction $\frac{\partial\alpha}{\partial u}(u, \cdot)$; at $u = 0$ this is Theorem 12.2.
180. (V8.10) A geodesic of $\Omega$ is a path smooth on $[0, 1]$ with zero acceleration; a path of $\Omega$ is critical iff its first variation vanishes on $T\Omega_\omega$.
181. (V8.11) A path of $\Omega$ is a critical path of the energy iff it is a geodesic.
182. (V8.12) $\frac{D}{\partial u}\frac{D}{\partial t}\frac{\partial F}{\partial t} = \frac{D}{\partial t}\frac{D}{\partial t}\frac{\partial F}{\partial u} + R(\frac{\partial F}{\partial t}, \frac{\partial F}{\partial u})\frac{\partial F}{\partial t}$ with Milnor's $R$, and the jumps of $\partial\alpha/\partial t$ can be differentiated in $u$.
183. (V8.13) For a 2-parameter variation of a geodesic, $\frac12\frac{\partial^2E}{\partial u_1 \partial u_2}(0, 0)$ exists and equals $-\sum_t\langle W_2, \Delta_t\frac{DW_1}{dt}\rangle - \int_0^1\langle W_2, \frac{D^2W_1}{dt^2} + R(V, W_1)V\rangle\,dt$.
184. (V8.14) $E_{**}$, defined on $T\Omega_\gamma$ by this formula, is Milnor's Hessian: at a geodesic every 2-parameter variation computes it, and every pair of fields comes from one.
185. (V8.15) $\frac12E_{**}(W_1, W_2) = \int_0^1(\langle\frac{DW_1}{dt}, \frac{DW_2}{dt}\rangle - \langle R(V, W_1)V, W_2\rangle)\,dt$.
186. (V8.16) $E_{**}$ is a symmetric bilinear form on $T\Omega_\gamma$.
187. (V8.17) For a 1-parameter variation of a geodesic with variation field $W$, $\frac{d^2E(\bar\alpha(u))}{du^2}(0) = E_{**}(W, W)$.
188. (V8.18) At a minimal geodesic, $E_{**}(W, W) \ge 0$ for every $W \in T\Omega_\gamma$.
189. (V9.1) Linear equations $x' = A(t)x$ with continuous coefficients have solutions on all of $\mathbb R$ through every initial value, unique on closed intervals and smooth where $A$ is.
190. (V9.2) A Jacobi field is a smooth tangent field with $\frac{D^2J}{dt^2} + R(V, J)V = 0$; one exists for all tangent initial values $(J(s), \frac{DJ}{dt}(s))$, and it is determined by them.
191. (V9.3) The Jacobi fields along $\gamma$ form a $2n$-dimensional space, isomorphic to $T_{\gamma(s)}N \times T_{\gamma(s)}N$ by $J \mapsto (J(s), \frac{DJ}{dt}(s))$ for every $s$.
192. (V9.4) Parameters $a \ne b$ are conjugate if a non-zero Jacobi field vanishes at both; the multiplicity is the dimension of the space of such fields.
193. (V9.5) At a geodesic, $W_1 \in T\Omega_\gamma$ is a null vector of $E_{**}$ iff it is a Jacobi field.
194. (V9.6) At a geodesic, the nullity of $E_{**}$ is the multiplicity of $0$ and $1$ as conjugate parameters, and $E_{**}$ is degenerate iff they are conjugate.
195. (V9.7) At a geodesic, the nullity of $E_{**}$ is less than $n = \dim N$ when $n \ge 1$.
196. (V9.8) The variation field of a smooth variation through geodesics is a Jacobi field.
197. (V9.9) Every Jacobi field along a geodesic $\gamma : [0, 1] \to N$ is the variation field of a smooth variation of $\gamma$ through geodesics.
198. (V9.10) At two non-conjugate parameters, the values of a Jacobi field determine it and can be prescribed.
199. (V9.11) Along the short geodesic joining two points of a neighbourhood of Lemma 10.3, Jacobi fields are determined by their end values, which can be prescribed.
200. (V9.12) Along any smooth curve, no parameter in some interval $(0, \delta)$ is conjugate to $0$.
201. (V9.13) The index of a bilinear form is the supremum of the dimensions of the finite-dimensional subspaces on which it is negative definite.
202. (V9.14) A perpendicular summand on which the form is positive definite changes neither the index nor the null space; definiteness on a finite-dimensional subspace persists under continuous perturbation; and Milnor's compound matrix gives index at least $\lambda + \nu$.
203. (V9.15) If $X$ is piecewise a Jacobi field, $E_{**}(X, Y)$ is $-2$ times the sum of the jumps of $\frac{DX}{dt}$ paired with the values of $Y$.
204. (V9.16) If a field has a zero within $h_0$ before every point, $\frac12E_{**}(X, X) \ge \int_0^1\|X\|^2$; hence parameters at most $h_0$ apart are never conjugate.
205. (V9.17) For a fine subdivision, broken Jacobi fields along $\gamma|[0, \tau]$ correspond bijectively to their values at the division points.
206. (V9.18) Lemma 15.3: the fields along $\gamma|[0, \tau]$ split into the broken Jacobi fields and $T'$, perpendicular for $E_{**}$, with $E_{**}$ positive definite on $T'$.
207. (V9.19) Lemma 15.4: the index and the null space of $E_{**}$ along $\gamma|[0, \tau]$ are those on the broken Jacobi fields; the index is finite and the nullity is $\nu(\tau)$.
208. (V9.20) $\lambda(\tau)$, the index of $E_{**}$ on the fields vanishing outside $[0, \tau]$, is non-decreasing and $0$ for small $\tau$, and $\lambda(1)$ is the index of $E_{**}$.
209. (V9.21) $\lambda(\tau)$ and $\nu(\tau)$ are the index and the nullity of a form $H_\tau$ on a fixed finite-dimensional space, continuous in $\tau$.
210. (V9.22) $\lambda$ is continuous from the left.
211. (V9.23) $\lambda$ jumps by $\nu(\tau)$ just after $\tau$, and $\lambda(\tau') \ge \lambda(\tau) + \nu(\tau)$ for every $\tau' > \tau$.
212. (V9.24) At a geodesic, the index of $E_{**}$ is the number of parameters in $(0, 1)$ conjugate to $0$, counted with multiplicity, and is finite.
213. (V9.25) A geodesic segment has only finitely many parameters conjugate to $0$.
214. (V10.1) Milnor's distance $d$, the largest distance of corresponding points plus the $L^2$ distance of the speeds, is a pseudometric on paths, vanishing for paths that agree on $[0, 1]$.
215. (V10.2) $\sqrt{E_a^b}$ is $1$-Lipschitz for $d$, so the energy is continuous, and a convergent sequence of paths has uniformly small energy on short intervals.
216. (V10.3) Paths of energy at most $c$ lie in the ball $S$ of radius $\sqrt c$ about $p$, which is compact when $N$ is closed (or connected and complete), and all subdivisions with $t_{i+1} - t_i < \delta^2/c$ are fine enough.
217. (V10.4) Lemma 16.1: the broken geodesics of energy less than $c$ correspond bijectively to their break points, which form an open subset $U$ of $N \times \dots \times N$, and their energy is $\sum_i\rho(x_i, x_{i+1})^2/(t_{i+1} - t_i)$.
218. (V10.5) This correspondence and its inverse are continuous, and identify each $B^a$ with its set of break points up to homotopy.
219. (V10.6) $E'$ is smooth on $U$, and its sublevel sets $B^a$, $a < c$, are compact.
220. (V10.7) Milnor's deformation $r_u$ does not increase the energy, runs from the identity to the retraction onto $B$, fixes $B$, and is continuous in both variables.
221. (V10.8) For $a < c$, $B^a$ is a strong deformation retract of $\Omega^a$.
222. (V10.9) The critical points of $E'$ are exactly the break points of the unbroken geodesics of energy less than $c$, and every such geodesic is a broken geodesic.
223. (V10.10) For the subdivision of §16, broken Jacobi fields take arbitrary values at the break points and are determined by them, $E_{**}$ is positive definite on the fields vanishing there, and Lemma 15.4 holds.
224. (V10.11) At a geodesic, the Hessian of $E'$ is $E_{**}$ on the broken Jacobi fields, so the two have the same index and the same nullity.
225. (V10.12) If $a < c$ is not the energy of a geodesic and the geodesics of energy at most $a$ are non-degenerate, they are finitely many, and $B^a$ has the homotopy type of a cell complex with one $\lambda$-cell for each of them of index $\lambda$.
226. (V10.13) Theorem 16.3: under the same hypotheses, $\Omega^a$ has that homotopy type and contains finitely many geodesics.
227. (V10.14) If some path has energy less than $c$, a minimum of $E'$ is a geodesic minimizing the energy on all of $\Omega$.
228. (V10.15) $\Omega^*$ is the space of continuous paths with the topology of uniform convergence, and the inclusion $\Omega \to \Omega^*$ is continuous since $d^* \le d$.
229. (V10.16) Convergence for $d$ implies $L^2$ convergence of the velocities, and, together with pointwise convergence, is implied by it.
230. (V10.17) Small ambient balls are good: two of their points are joined by a unique minimal geodesic, which stays in the ball and depends smoothly on its end points, and every compact set has a Lebesgue number for good balls.
231. (V10.18) On the open set $Y_k$ of paths whose dyadic pieces of level $k$ lie in good balls, the dyadic broken geodesic is a homotopy inverse of the inclusion of $X_k = Y_k \cap \Omega$.
232. (V10.19) Theorem 17.1: the inclusion of $\Omega$, with Milnor's metric, into $\Omega^*$ is a homotopy equivalence; Milnor's map $h$ is not continuous for $d$, and the proof verified is the exposition's modified proof.
233. (V10.20) Relative cell attachments carry over along homotopy equivalences, the relative Theorem 3.5 holds below a compact sublevel set, and a tower of relative cell attachments over sublevel sets that exhaust a space gives a countable cell complex.
234. (V10.21) Between two levels below $c$ that are not energies of geodesics, $\Omega^b$ is, up to homotopy, $\Omega^a$ with one $\lambda$-cell attached for each geodesic of index $\lambda$ with energy in between.
235. (V10.22) Theorem 17.3: for $N$ closed in $V$ and $q$ not conjugate to $p$ along any geodesic, $\Omega(N; p, q)$ has the homotopy type of a countable cell complex with one $\lambda$-cell for each geodesic from $p$ to $q$ of index $\lambda$.
236. (V10.23) For $q \ne \pm p$ on $S^n$, the geodesics from $p$ to $q$ are the great-circle arcs $\gamma_k$ with $k\pi < L(\gamma_k) < (k + 1)\pi$, $q$ is not conjugate to $p$ along any of them, and $\gamma_k$ has index $k(n - 1)$.
237. (V10.24) Corollary 17.4 for $\Omega(S^n; p, q)$, $q \ne \pm p$, $n \ge 2$: one cell in each of the dimensions $0, n - 1, 2(n - 1), \dots$.
238. (V10.25) A path space with one geodesic of index $kr$, $r \ge 2$, in the $k$-th energy window has Betti numbers $1$ in the degrees divisible by $r$ and $0$ in the others.
239. (V10.26) For $n \ge 3$ and $q \ne \pm p$, $H_i(\Omega(S^n; p, q))$ over a field has dimension $1$ if $n - 1$ divides $i$ and $0$ otherwise.
240. (V10.27) $\mathbb R^{n+1} \setminus \{0\}$ has the homotopy type of $S^n$, no conjugate points and two points joined by a single geodesic, so Corollary 17.5 needs completeness.
241. (V10.28) Every $q$ can be joined in $N$ to a point not conjugate to $p$, and a path from $q$ to $q'$ makes $\Omega(N; p, q)$ and $\Omega(N; p, q')$ homotopy equivalent.
242. (V10.29) Corollary 17.2: for $N$ closed in a Euclidean space, $\Omega(N; p, q)$ and $\Omega^*(N; p, q)$ have the homotopy type of a countable cell complex.
243. (V10.30) Corollary 17.4 for loops: for $n \ge 2$ the loop space of $S^n$ has the homotopy type of a cell complex with one cell in each dimension $k(n - 1)$; for $n \ge 3$ its Betti numbers over a field are $1$ in the degrees divisible by $n - 1$ and $0$ otherwise.
244. (V11.1) The exponential map is defined on an open subset of $TN$ and is smooth there, without completeness.
245. (V11.2) The domain of $\exp_q$ in $T_qN$ is open and star-shaped, $\exp_q$ is smooth on it, and $\exp_q$ is critical at $v$ when $d(\exp_q)_v$ is not one-to-one.
246. (V11.3) Theorem 18.1: $\exp_q(v)$ is conjugate to $q$ along $t \mapsto \exp_q(tv)$ iff $\exp_q$ is critical at $v$, the multiplicity being $\dim\ker d(\exp_q)_v$.
247. (V11.4) The points conjugate to $p$ along some geodesic are exactly the critical values of $\exp_p$.
248. (V11.5) Corollary 18.2: these points form a set of measure zero in every chart of $N$.
249. (V11.6) The points not conjugate to $p$ along any geodesic are dense, and every geodesic from $p$ to such a point has nullity $0$.
250. (V11.7) Lemma 19.1: with $\langle R(A, B)A, B\rangle \le 0$, no two parameters are conjugate along any geodesic.
251. (V11.8) With $\langle R(A, B)A, B\rangle \le 0$, every geodesic has index and nullity $0$, $E_{**}$ is positive definite, and $\exp_p$ is nowhere critical.
252. (V11.9) The Ricci tensor $K(U_1, U_2)$ is the trace of $W \mapsto R(U_1, W)U_2$; it is symmetric, and $K(U_n, U_n)$ is the sum of the sectional curvatures of the planes through $U_n$ and $U_i$.
253. (V11.10) A geodesic segment extends to a smooth curve on $\mathbb R$ along which its velocity is parallel, with parallel unit fields $P_1, \dots, P_{n-1}$ such that $\sum\langle R(V, P_i)V, P_i\rangle \ge L^2(n - 1)/r^2$ under the Ricci bound.
254. (V11.11) $\frac12E_{**}(\sin(\pi t)P, \sin(\pi t)P) = \int_0^1(\pi^2\cos^2\pi t - \sin^2\pi t\, \langle R(V, P)V, P\rangle)\,dt$, and under the Ricci bound a geodesic longer than $\pi r$ has a field with $E_{**}(X, X) < 0$.
255. (V11.12) Theorem 19.4: for $n \ge 2$ and $K(U, U) \ge (n - 1)/r^2$, a geodesic longer than $\pi r$ contains a conjugate point and is not minimal.
256. (V11.13) Corollary 19.5: if moreover $N$ is connected and complete, its diameter is at most $\pi r$ and $N$ is compact.
257. (V11.14) The unit sphere $S^n$ has $K(U, U) = (n - 1)\|U\|^2$, so for $n \ge 2$ its geodesics longer than $\pi$ are not minimal and its diameter is at most $\pi$.
258. (V11.15) Test fields supported in disjoint intervals are $E_{**}$-orthogonal, and on a piece $[a, b]$ with $L(b - a) > \pi r$ one of them has $E_{**}(X, X) < 0$.
259. (V11.16) Under the Ricci bound, a geodesic of length $> k\pi r$ has index at least $k$.
260. (V11.17) Theorem 19.2: a simply connected complete $N$ of curvature $\le 0$ has exactly one geodesic between any two points, and $\exp_p : T_pN \to N$ is a diffeomorphism.
261. (V11.18) In curvature $\le 0$, $\Omega(N; p, q)$ has the homotopy type of the discrete set of geodesics from $p$ to $q$, and is contractible when $N$ is simply connected.
262. (V11.19) For complete $N$ with $\exp_p$ nowhere critical (e.g. curvature $\le 0$), $\exp_p : T_pN \to N$ is a covering map.
263. (V11.20) In a complete $N$ of curvature $\le 0$, each homotopy class of paths from $p$ to $q$ contains exactly one geodesic.
264. (V11.21) Corollary 19.3, first half: in a complete $N$ of curvature $\le 0$, $\pi_i(N) = 0$ for $i > 1$.
265. (V11.22) For $N$ compact with positive definite Ricci tensor and $q$ not conjugate to $p$, $\Omega(N; p, q)$ has the homotopy type of a countable cell complex with finitely many cells in each dimension.
266. (V11.23) Under the same hypotheses its homology over any field is finite-dimensional in each degree.
267. (V11.24) Theorem 19.6 for all $p, q$: the same conclusions without the non-conjugacy hypothesis.
268. (V12.1) A bi-invariant metric is modelled by a bilinear form on a Lie algebra, and its Levi-Civita connection on left-invariant fields by a bilinear $D$ with $D(X, Y) - D(Y, X) = [X, Y]$ and $B(D(X, Y), Z) + B(Y, D(X, Z)) = 0$.
269. (V12.2) If moreover $D(X, X) = 0$ for all $X$, then $D(X, Y) = \tfrac12[X, Y]$.
270. (V12.3) Under the same hypotheses, $B([X, Y], Z) = B(X, [Y, Z])$.
271. (V12.4) For a symmetric, non-degenerate, ad-invariant $B$, the Levi-Civita connection on the Lie algebra must be $\tfrac12[\,\cdot\,, \cdot\,]$, and it is one.
272. (V12.5) With $D = \tfrac12[\,\cdot\,, \cdot\,]$, Milnor's curvature is $R(X, Y)Z = \tfrac14[[X, Y], Z]$.
273. (V12.6) For ad-invariant $B$, $B(R(X, Y)Z, W) = \tfrac14B([X, Y], [Z, W])$.
274. (V12.7) For ad-invariant $B$, $B([X, Y], Z)$ is alternating in $X, Y, Z$.
275. (V12.8) $B(R(X, Y)X, Y) = \tfrac14B([X, Y], [X, Y])$, which is $\ge 0$ and vanishes iff $[X, Y] = 0$ when $B$ is positive definite.
276. (V12.9) With trivial centre and a positive definite ad-invariant $B$, the Ricci curvature $\operatorname{tr}K_V$ is positive for $V \neq 0$; it equals $-\tfrac14$ of the Killing form.
277. (V12.10) The orthogonal complement of the centre is an ideal, complementary to the centre, with trivial centre.
278. (V12.11) $K_V = -\tfrac14\operatorname{ad}_V^2$ is self-adjoint and positive semidefinite, with kernel the centralizer of $V$.
279. (V12.12) Every eigenspace of $K_V$ for a non-zero eigenvalue carries a complex structure and so has even dimension.
280. (V12.13) A spectrum in which every positive eigenvalue has even multiplicity has even index, the index being defined by Theorems 20.5 and 15.1.
281. (V12.14) A matrix group $G$ with Lie algebra $\mathfrak g$ has $T_gG = g\mathfrak g$, its induced metric is bi-invariant, and the inner product on $\mathfrak g$ is ad-invariant.
282. (V12.15) The geodesics of a matrix group are the curves $t \mapsto g\exp(tX)$; those through $I$ are the one-parameter subgroups, and the group is complete.
283. (V12.16) $\sigma \mapsto \tau\sigma^{-1}\tau$ is an isometry of $G$ fixing $\tau$ and reversing the geodesics through $\tau$.
284. (V12.17) On a matrix group, $X \vdash Y = \tfrac12[X, Y]$, $R(X, Y)Z = \tfrac14[[X, Y], Z]$, and the sectional curvature is $\tfrac14\|[X, Y]\|^2 \ge 0$.
285. (V12.18) Along $\exp(tA)$, $\exp(tA/2)U(t)\exp(tA/2)$ is a Jacobi field whenever $U'' + \tfrac14[[A, U], A] = 0$ in $\mathfrak g$.
286. (V13.1) $\Omega^d$ is the set of paths of least energy, and these are geodesics.
287. (V13.2) Theorem 22.1: if the closed balls about $p$ are compact, every geodesic not of least energy has index $\ge \lambda_0$, and $\Omega^d$ is a retract of an open neighbourhood, then every map of a compact $P$ of dimension $< \lambda_0$ into $\Omega$ is homotopic, relative to the part already in $\Omega^d$, to a map into $\Omega^d$.
288. (V13.3) The inclusion $\Omega^d \to \Omega$ is bijective on $\pi_i$ for $i \le \lambda_0 - 2$ and onto for $i \le \lambda_0 - 1$, at every point of $\Omega^d$.
289. (V13.4) Corollary 22.2: $\pi_i(\Omega^d, \gamma) \cong \pi_{i+1}(N, p)$ for $i \le \lambda_0 - 2$ (bijection), onto for $i \le \lambda_0 - 1$.
290. (V13.5) Change of basepoint is a group isomorphism, and Corollary 22.2 holds as groups for $1 \le i \le \lambda_0 - 2$.
291. (V13.6) The geodesics from $p$ to $-p$ on $S^{n+1}$ are the great circles of length $(2m + 1)\pi$, the minimal ones are the semicircles, and these form a space homotopy equivalent to the equator, and homeomorphic to it after identifying paths that agree on $[0, 1]$.
292. (V13.7) The great circle of length $(2m + 1)\pi$ from $p$ to $-p$ has index $2mn$; the non-minimal ones have index $\ge 2n$.
293. (V13.8) $\Omega^d(S^{n+1}; p, -p)$ is a retract of the open set of paths whose midpoint is not $\pm p$.
294. (V13.9) Corollary 22.3: $\pi_iS^n \cong \pi_{i+1}S^{n+1}$ for $i \le 2n - 2$ (groups for $i \ge 1$), and onto for $i = 2n - 1$.
295. (V13.10) Lemma 22.4: a $C^2$-small perturbation of $f$ near a compact $K$ has no critical points in $K$ of index below $\lambda_0$ if $f$ has none.
296. (V13.11) On a submanifold, small linear perturbations keep the indices of critical points in a compact set $\ge \lambda_0$.
297. (V13.12) Pushing maps is transitive, holds for strong deformation retracts, and holds for a closed set with finitely many disjoint cells of dimension $> \dim P$ attached.
298. (V13.13) Lemma D: across critical levels whose critical points are non-degenerate of index $\ge \lambda_0$, $N^a$ pushes maps of dimension $< \lambda_0$ out of $N^b$.
299. (V13.14) Lemma 22.5: given a neighbourhood $U$ of the minimum set from which it pushes maps, and indices $\ge \lambda_0$ off the minimum, the minimum set pushes maps of dimension $< \lambda_0$ out of every compact sublevel set.
300. (V13.15) In the model of broken geodesics, a neighbourhood retraction of $\Omega^d$ gives a neighbourhood of the minimum that deforms into it.
301. (V13.16) Theorem 22.1 holds for an open and closed set $\Omega'$ of paths when the index bound holds for the geodesics in $\Omega'$.
302. (V14.1) $\exp\operatorname{diag}(ia_1, \dots, ia_n) = -I$ iff every $a_j$ is an odd multiple of $\pi$.
303. (V14.2) For $A = \operatorname{diag}(i\pi k_j)$, $\operatorname{tr}AA^* = \pi^2\sum k_j^2$ and $\operatorname{tr}A = i\pi\sum k_j$.
304. (V14.3) For odd $k_j$, $\sum k_j^2 \ge n$ with equality iff all $k_j = \pm1$; with $\sum k_j = 0$ and $n = 2m$, then $m$ are $+1$ and $m$ are $-1$.
305. (V14.4) A skew-Hermitian $A$ has $A^2 = -\pi^2I$ iff $A = i\pi(2P - I)$ for a Hermitian projection $P$, and then $\operatorname{tr}A = 0$ iff $\operatorname{tr}P = n/2$.
306. (V14.5) For diagonal $A = \operatorname{diag}(i\pi k_j)$, $\tfrac14[[A, W], A]$ multiplies the $(j, l)$ entry of $W$ by $\tfrac{\pi^2}{4}(k_j - k_l)^2$.
307. (V14.6) $E_{jl}$, $E'_{jl}$ are skew-Hermitian traceless eigenvectors with eigenvalue $\tfrac{\pi^2}{4}(k_j - k_l)^2$, diagonal matrices are in the kernel, and together they span the skew-Hermitian matrices.
308. (V14.7) The conjugate parameters of an eigenvalue $e$ are the $t \in (0, 1)$ in $\pi\mathbb Z/\sqrt e$, and for $e = (\pi d)^2$ there are $d - 1$ of them.
309. (V14.8) The index of a spectrum is the number of conjugate parameters in $(0, 1)$ counted with multiplicity, equivalently the sum over the eigenvalues of their numbers of conjugate parameters.
310. (V14.9) For odd $k_j$, Milnor's spectrum has index $\sum_{k_i > k_j}(k_i - k_j - 2)$.
311. (V14.10) The formula is non-negative, symmetric under $k \mapsto -k$, independent of the order, and zero when all $k_j = \pm1$.
312. (V14.11) For odd $k_1, \dots, k_{2m}$ with sum $0$, not all $\pm1$, the formula is at least $2m + 2$.
313. (V14.12) In $U(n + 1)$, $k = (3, 1, \dots, 1)$ gives index $0$ although it is not minimal, and its $\sum k_j$ is larger than that of any minimal geodesic.
314. (V14.13) $U(n)$ and $SU(n)$ are compact submanifolds of the space of matrices and matrix groups, with Lie algebras $\mathfrak u(n)$ and $\mathfrak{su}(n)$.
315. (V14.14) Every geodesic from $I$ to $-I$ in $SU(n)$ is $t \mapsto \exp(tA)$ with $A = T\operatorname{diag}(i\pi k_j)T^*$, $T$ unitary, $k_j$ odd, $\sum k_j = 0$.
316. (V14.15) In $SU(2m)$ the distance from $I$ to $-I$ is $\pi\sqrt{2m}$, and $\exp(tA)$ is minimal iff $A^2 = -\pi^2I$, iff all $k_j = \pm1$.
317. (V14.16) The initial velocities of the minimal geodesics form a space homeomorphic to $G_m(\mathbb C^{2m})$, by $A \mapsto \tfrac12(I - \tfrac i\pi A)$.
318. (V14.17) The space $\Omega^d$ of minimal paths is homotopy equivalent to that space of velocities, and homeomorphic to it after identifying paths that agree on $[0, 1]$.
319. (V14.18) Theorem 20.5 for $SU(n)$: the multiplicity of a conjugate parameter along $\exp(tA)$ is the dimension of an explicit kernel, which equals the count from Milnor's spectrum.
320. (V14.19) Every geodesic from $I$ to $-I$ in $SU(n)$ has index $\sum_{k_i > k_j}(k_i - k_j - 2)$.
321. (V14.20) In $SU(2m)$ every geodesic from $I$ to $-I$ not of least energy has index $\ge 2m + 2$.
322. (V14.21) $\Omega^d(SU(2m); I, -I)$ is a neighbourhood retract, so $\pi_i\Omega^d \cong \pi_{i+1}SU(2m)$ for $i \le 2m$ (groups for $i \ge 1$).
323. (V14.22) Theorem 23.3: $\pi_iG_m(\mathbb C^{2m}) \cong \pi_{i+1}SU(2m)$ for $i \le 2m$, at every point, as groups for $i \ge 1$.
324. (V14.23) An equivariant map onto a homogeneous space with a local section of the orbit map is locally trivial; restricting frames and $U(n) \to V_k(\mathbb K^n)$ are locally trivial.
325. (V14.24) The frame-to-span map $V_m(\mathbb K^n) \to G_m(\mathbb K^n)$ is locally trivial with fibre $U(m)$.
326. (V14.25) $V_k(\mathbb C^n)$ is $2(n - k)$-connected, and $U(m) \to U(m + k)$ is bijective on $\pi_i$ for $i < 2m$, onto for $i \le 2m$.
327. (V14.26) Lemma 23.4: $\pi_iG_m(\mathbb C^{2m}) \cong \pi_{i-1}U(m)$ for $1 \le i \le 2m$, as groups for $i \ge 2$.
328. (V14.27) $SU(n) \to U(n)$ is bijective on $\pi_j$ for $j \ge 2$.
329. (V14.28) $\pi_{i-1}U(m) \cong \pi_{i+1}U(2m)$ for $1 \le i \le 2m$, and periodicity $\pi_{i-1}U(m) \cong \pi_{i+1}U(m)$ for $1 \le i \le 2m - 2$ (groups for $i \ge 2$).
330. (V14.29) Theorem 23.5: for $j \le 2m - 1$, $\pi_jU(m)$ is trivial for even $j$ and in bijection with $\mathbb Z$ for odd $j$.
331. (V14.30) $\pi_1S^1 \cong \mathbb Z$ and $\pi_{2k+1}U(m) \cong \mathbb Z$ for $2k + 2 \le 2m$, as groups.
332. (V15.1) A complex structure is an orthogonal $J$ with $J^2 = -I$, equivalently a skew $J$ with $J^2 = -I$; it forces $n$ even.
333. (V15.2) If $J^2 = -I$ then $\exp(\theta J) = \cos\theta\,I + \sin\theta\,J$, so $\exp(\pi J) = -I$.
334. (V15.3) For odd positive $a_j$, Milnor's spectrum for $O(2m)$ has index $\sum_{i<j}(a_i + a_j - 2) + \sum_{a_i > a_j}(a_i - a_j - 2)$, which is $0$ when all $a_j = 1$ and at least $2m - 2$ otherwise.
335. (V15.4) $\Omega_k(n)$ is the set of complex structures anticommuting with $J_1, \dots, J_{k-1}$; these sets decrease with $k$ and are compact.
336. (V15.5) For $P, J' \in \Omega_k(n)$, the reflection $PJ'^{-1}P = -PJ'P$ lies in $\Omega_k(n)$.
337. (V15.6) For skew $A$ anticommuting with $J$, $J\exp A$ is a complex structure, and it anticommutes with every $J_\alpha$ that anticommutes with $J$ and commutes with $A$.
338. (V15.7) $J' \in \Omega_{k+1}(n)$ iff $J' = J_kA$ with $A$ a complex structure anticommuting with $J_k$ and commuting with $J_1, \dots, J_{k-1}$; then $J_k\exp(tA) = \cos t\,J_k + \sin t\,J'$ stays in $\Omega_k(n)$ and passes through $J'$ at $t = \pi/2$.
339. (V15.8) $P \oplus P'$ lies in $\Omega_k(n + n')$ for the structures $J_\alpha \oplus J'_\alpha$ whenever $P \in \Omega_k(n)$ and $P' \in \Omega_k(n')$.
340. (V15.9) Explicit matrices give $1$, $3$, $7$, $8$ anticommuting complex structures on $\mathbb R^2$, $\mathbb R^4$, $\mathbb R^8$, $\mathbb R^{16}$, and $8$ on every $\mathbb R^{16r}$.
341. (V15.10) The products $J_1J_2J_3$, $J_1J_4J_5$, $J_2J_4J_6$, $J_1J_6J_7$, $J_3J_4$, $J_7J_8$ and $J_1\cdots J_7$ have exactly the squares and commutation properties Milnor uses on pp. 139–143.
342. (V15.11) $J' \mapsto J_aJ_bJ'$ is a bijection of $\Omega_{k+1}(n)$ onto the symmetric involutions commuting with $J_a, J_b$ and anticommuting with the other $J_c$, $c \le k$.
343. (V15.12) With eight structures, $V_1 \supset W \supset X \supset X_1$ halve the dimension at each step, and in $\mathbb R^{16r}$ they have dimensions $8r$, $4r$, $2r$, $r$.
344. (V15.13) A minimal space is a non-zero space with no proper non-zero subspace closed under $J_1, \dots, J_k$; $m_k$ is Milnor's table.
345. (V15.14) For $k \le 8$, $m_k$ divides the dimension of every space with $k$ Clifford maps, and is the least positive dimension carrying $k$ anticommuting complex structures.
346. (V15.15) $k$ Clifford maps make a space a module over the Clifford algebra $C_k$ of dimension $2^k$, so a minimal space has dimension at most $2^k$.
347. (V15.16) For $k \le 8$ a space with $k$ Clifford maps is minimal iff its dimension is $m_k$.
348. (V15.17) For $k \le 8$, $k \not\equiv 3 \pmod 4$, any two minimal spaces are isomorphic by a linear isomorphism commuting with the $J_\alpha$.
349. (V15.18) For anticommuting complex structures, $J_1u, \dots, J_ku$ are orthonormal and orthogonal to a unit vector $u$.
350. (V15.19) Eigenvalues greater than $\pi^2$ each contribute at least one to the index; so $s - 1$ such eigenvalues give index at least $s - 1$.
351. (V15.20) For odd $a_h$ with some $|a_h| \ge 3$ and sum $c$, the pairs $a_h > a_j$ alone give $4\lambda \ge r - |c|$.
352. (V15.21) If $x\exp A \in N$ and $A \in T_{x\exp A}$ for $A \in T_x$, with $\dim T_x = \dim N$, then the geodesics of $N$ are exactly the curves $t \mapsto x\exp(tA)$, $A \in T_x$, and $N$ is complete.
353. (V15.22) Assertions 1 and 2: for $x \in \Omega_k(n)$ and $A \in \mathcal T_x$, $x\exp A \in \Omega_k(n)$; conversely, if $C$ is small and $x\exp C \in \Omega_k(n)$, then $C \in \mathcal T_x$.
354. (V15.23) The set of points of $\Omega_k(n)$ where $\mathcal T$ has a given dimension is open and closed in $\Omega_k(n)$, compact, a submanifold of $M_n(\mathbb R)$ with tangent spaces $x\mathcal T_x$, and its geodesics are the curves $x\exp(tA)$, $A \in \mathcal T_x$.
355. (V15.24) A skew $V$ with $\exp V = -I$ has $\|V\|^2 \ge \pi^2n$, with equality only if $V^2 = -\pi^2I$.
356. (V15.25) If some $A \in \mathcal T_p$ has $A^2 = -I$, the distance from $p$ to $-p$ in the stratum of $p$ is $\pi\sqrt n$, and the paths of least energy are, on $[0, 1]$, exactly the curves $p\exp(\pi tA)$ with $A \in \mathcal T_p$, $A^2 = -I$.
357. (V15.26) These $A$, for $p = J_k$, correspond homeomorphically to the points $J' = J_kA$ of $\Omega_{k+1}(n)$, the geodesic of $J'$ being $\cos(\pi t)J_k + \sin(\pi t)J'$; and $\Omega_{k+1}(n)$ is homotopy equivalent to the space of minimal paths from $J_k$ to $-J_k$ (homeomorphic after identifying paths that agree on $[0, 1]$).
358. (V15.27) The minimal paths from $p$ to $-p$ form a retract of an open neighbourhood in the path space.
359. (V15.28) For skew $X$ commuting with $p$ and $J_1, \dots, J_{k-1}$, $X\gamma - \gamma X$ is a Jacobi field along $\gamma(t) = p\exp(tV)$; spaces of such $X$ commuting with $\exp(\tau V)$ but not with $V$ bound the multiplicity of $\gamma(\tau)$, and so the index, from below.
360. (V15.29) $\mathbb R^n$ splits orthogonally into subspaces minimal under $A, J, J_1, \dots, J_{k-1}$; on each, $A^2$ is a scalar $-c$, with $c \ge 1$ if $\exp(\pi A) = -I$; each is a minimal space for $k + 1$ structures; and for $k \le 7$, $k \not\equiv 2 \pmod 4$, any two are related by an isomorphism as in Milnor's p. 145.
361. (V15.30) For $k \le 7$, $k \not\equiv 2 \pmod 4$, a geodesic from $J_k$ to $-J_k$ in $\Omega_k(n)$ that is not of least energy has index $\ge n/m_{k+1} - 1$, and $\ge n - 2$ in $O(n)$ ($k = 0$).
362. (V15.31) For $k \le 7$, $k \not\equiv 2 \pmod 4$ and $i \le n/m_{k+1} - 3$, the map $J' \mapsto (\cos(\pi t)J_k + \sin(\pi t)J')$ is bijective on $\pi_i$ at every point, and $\pi_i\Omega_{k+1}(n) \cong \pi_{i+1}\Omega_k(n)$.
363. (V15.32) Theorem 24.3: for $i \le n - 4$, $\Omega_1(n) \to \Omega(O(n); I, -I)$ is bijective on $\pi_i$, and $\pi_i\Omega_1(n) \cong \pi_{i+1}O(n)$.
364. (V15.33) For a continuous $F$ of modulus $1$, the set of paths along which the angle of $F$ ends at a given value is open and closed in the path space.
365. (V15.34) $\det_{\mathbb C}$, defined without a complex basis, is multiplicative, has modulus $1$ on orthogonal matrices commuting with $\mathbf i$, and $\det_{\mathbb C}\exp(tV) = e^{-\sqrt{-1}\,t\operatorname{tr}(V\mathbf i)/2}$.
366. (V15.35) $\mathbf i = J_1\cdots J_{k-1}$ has the properties Milnor uses for $k = 2, 6$; $f = \det_{\mathbb C}(J_k^{\mathsf T}\,\cdot\,)$ has modulus $1$ on $\Omega_k(n)$; and $\Omega^{(c)}$, the paths whose $f$-angle ends at $\pi m_{k+1}c/2$, is open and closed and contains the geodesic $J_k\exp(\pi tA)$ exactly when $-\operatorname{tr}(A\mathbf i) = m_{k+1}c$.
367. (V15.36) For $k = 2, 6$ every path from $J_k$ to $-J_k$ lies in exactly one $\Omega^{(c)}$, $c$ an integer.
368. (V15.37) For $k \equiv 2 \pmod 4$, on each minimal piece $A = a_h\mathbf i$ with $a_h$ an odd integer, and $\operatorname{tr}(A\mathbf i) = -m_{k+1}\sum a_h$.
369. (V15.38) For $k = 2, 6$, a geodesic in $\Omega^{(c)}$ that is not of least energy has index $\ge \lfloor(n/m_{k+1} - |c|)/4\rfloor$.
370. (V15.39) For $k = 2, 6$ and $j + 3 \le \lfloor(n/m_{k+1} - |c|)/4\rfloor$, at a point $J'$ whose semicircle lies in $\Omega^{(c)}$, the map of item 31 is bijective on $\pi_{j+1}$, and $\pi_{j+1}\Omega_{k+1}(n) \cong \pi_{j+2}\Omega_k(n)$.
371. (V15.40) For $k = 2, 6$ and $|c| \le n/m_{k+1} - 8$, the path components of $\Omega^{(c)}$ correspond bijectively to those of the part of $\Omega_{k+1}(n)$ mapped into it.
372. (V15.41) On $\mathbb R^{16r}$ with the explicit structures, $J \mapsto J \oplus J'_k$ maps $\Omega_k(16r)$ into $\Omega_k(16r + 16)$ compatibly with the maps of item 31, and for $k = 2, 6$ without changing $c$.
373. (V15.42) $\Omega_8(16r)$ is homeomorphic to $O(r)$, the base point $J_8$ corresponding to $I$.
374. (V15.43) For $r \ge 2i + 7$: $\pi_i\Omega_8(16r) \cong \pi_{i+8}O(16r)$ and $\pi_iO(r) \cong \pi_{i+8}O(16r)$, as sets.
375. (V15.44) $\pi_iO(n)$ does not depend on $n \ge i + 2$, and $\pi_iU(n)$ does not depend on $n > i/2$, up to bijection.
376. (V15.45) Theorem 24.7 in the stable range: $\pi_iO(n) \cong \pi_{i+8}O(n')$, as sets, for $n \ge i + 2$ and $n' \ge i + 10$.
377. (V15.46) $\pi_iU(n) \cong \pi_{i+2}U(n')$, as sets, for $i < 2n$ and $i + 2 < 2n'$.
378. (VA.1) A homotopy equivalence is a map with a two-sided homotopy inverse; a map with a left and a right homotopy inverse is one.
379. (VA.2) The telescope is $X_\Sigma = \bigcup_nX_n \times [n, n + 1] \subseteq X \times \mathbb R$, and $X$ is the homotopy direct limit of $\{X_i\}$ when $(x, \tau) \mapsto x$ is a homotopy equivalence; raising $\tau$ stays in $X_\Sigma$.
380. (VA.3) If the $X_n$ are closed, a map on $X_\Sigma$ (or $P \times X_\Sigma$) continuous on each strip is continuous.
381. (VA.4) If $f_\Sigma$ is a homotopy equivalence between homotopy direct limits, so is $f$.
382. (VA.5) $X_n \to X^n_\Sigma$, $x \mapsto (x, n)$, is a homotopy equivalence, with no closedness.
383. (VA.6) A function $f \ge 0$ with $f \ge n + 1$ off $X_n$ makes $X$ a homotopy direct limit, and $X_\Sigma$ is always the homotopy direct limit of its truncations.
384. (VA.7) Example 1 holds for paracompact Hausdorff $X$; sublevel sets $\{E \le a_i\}$ of a continuous $E$ with $a_i \to \infty$ need no paracompactness.
385. (VA.8) Example 3: $[0, 1]$ is not the homotopy direct limit of $\{0\} \cup [\frac1{n+1}, 1]$.
386. (VA.9) For closed $X_n$, Milnor's maps $h_1$ are homotopy equivalences with inverse $g$.
387. (VA.10) Case 1: for closed $X_n$ and $\varphi_n \simeq \mathrm{id}$, $\varphi_\Sigma$ is a homotopy equivalence; the third line of $h_u$ is $h^{n+1}_{(4t-3)u}$.
388. (VA.11) Case 2: if the $Y_n$ are closed and every $f_n$ is a homotopy equivalence, $f_\Sigma$ is a homotopy equivalence; the $X_n$ need not be closed.
389. (VA.12) Theorem A by Milnor's proof, with the $Y_i$ closed.
390. (VA.13) The mapping telescope of $K_0 \to K_1 \to \cdots$ is the homotopy direct limit of its closed truncations, each homotopy equivalent to the corresponding $K_n$.
391. (VA.14) The mapping telescope of the inclusions $X_n \subseteq X_{n+1}$ is homotopy equivalent to $X_\Sigma$, and to $X$ when $X$ is the homotopy direct limit.
392. (VA.15) Theorem A holds exactly as Milnor states it, with no closedness hypothesis.
393. (VA.16) A homotopy direct limit of the $X_n$ is homotopy equivalent to the mapping telescope of any sequence $K_n$ with compatible homotopy equivalences $X_n \to K_n$.
394. (VA.17) The Corollary, with the mapping telescope of the $K_n$ in place of a CW-complex.
395. (VA.18) A countable cell complex is the mapping telescope of a tower of cell attachments.
396. (VA.19) A space exhausted by sublevel sets homotopy equivalent to the compatible stages of a cell tower has the homotopy type of the countable cell complex.
